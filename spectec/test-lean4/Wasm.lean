/- Preamble -/
set_option linter.unusedVariables false

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
opaque min : forall (nat : Nat) (nat : Nat), Nat := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/0.2-aux.num.spectec:9.1-9.56 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.2-aux.num.spectec:9.1-9.56 -/
opaque sum : forall (_ : (List Nat)), Nat := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/0.2-aux.num.spectec:13.1-13.57 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.2-aux.num.spectec:13.1-13.57 -/
opaque prod : forall (_ : (List Nat)), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:7.1-7.44 -/
opaque opt_ : forall (X : Type) (_ : (List X)), (Option X) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:14.1-14.82 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:14.1-14.82 -/
opaque concat_ : forall (X : Type) (_ : (List (List X))), (List X) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:18.1-18.89 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:18.1-18.89 -/
opaque concatn_ : forall (X : Type) (_ : (List (List X))) (nat : Nat), (List X) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:22.1-22.58 -/
opaque concatopt_ : forall (X : Type) (_ : (List (Option X))), (List X) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:26.1-26.39 -/
opaque inv_concat_ : forall (X : Type) (_ : (List X)), (List (List X)) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:29.1-29.45 -/
opaque inv_concatn_ : forall (X : Type) (nat : Nat) (_ : (List X)), (List (List X)) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:35.1-35.78 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:35.1-35.78 -/
/- elided, builtin -/

/- Recursive Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:40.1-40.38 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:40.1-40.38 -/
opaque setminus1_ : forall (X : Type) (X : X) (_ : (List X)), (List X) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:39.1-39.56 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:39.1-39.56 -/
opaque setminus_ : forall (X : Type) (_ : (List X)) (_ : (List X)), (List X) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:51.1-51.46 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:51.1-51.46 -/
opaque setproduct2_ : forall (X : Type) (X : X) (_ : (List (List X))), (List (List X)) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:50.1-50.47 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:50.1-50.47 -/
opaque setproduct1_ : forall (X : Type) (_ : (List X)) (_ : (List (List X))), (List (List X)) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:49.1-49.84 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:49.1-49.84 -/
opaque setproduct_ : forall (X : Type) (_ : (List (List X))), (List (List X)) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/1.0-syntax.profiles.spectec:5.1-5.29 -/
opaque ND : Bool := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:7.1-7.37 -/
inductive bit : Type where
  |  (i : Nat) : bit
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:7.8-7.11 -/
inductive wf_bit : bit -> Prop where
  | bit_case_0 : forall (i : Nat), 
    ((i == 0) || (i == 1)) ->
    wf_bit (. i)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:8.1-8.50 -/
inductive byte : Type where
  |  (i : Nat) : byte
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:8.1-8.50 -/
opaque proj_byte_0 : forall (x : byte), Nat := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:8.8-8.12 -/
inductive wf_byte : byte -> Prop where
  | byte_case_0 : forall (i : Nat), 
    ((i >= 0) && (i <= 255)) ->
    wf_byte (. i)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:10.1-11.25 -/
inductive uN : Type where
  |  (i : Nat) : uN
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:10.1-11.25 -/
opaque proj_uN_0 : forall (x : uN), Nat := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:10.8-10.11 -/
inductive wf_uN : N -> uN -> Prop where
  | uN_case_0 : forall (N : N) (i : Nat), 
    ((i >= 0) && (i <= ((((2 ^ N) : Nat) - (1 : Nat)) : Nat))) ->
    wf_uN N (. i)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:12.1-13.50 -/
inductive sN : Type where
  |  (i : Nat) : sN
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:12.1-13.50 -/
opaque proj_sN_0 : forall (x : sN), Nat := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:12.8-12.11 -/
inductive wf_sN : N -> sN -> Prop where
  | sN_case_0 : forall (N : N) (i : Nat), 
    ((((i >= (0 - ((2 ^ (((N : Nat) - (1 : Nat)) : Nat)) : Nat))) && (i <= (0 - (1 : Nat)))) || (i == (0 : Nat))) || ((i >= ((1 : Nat))) && (i <= ((((2 ^ (((N : Nat) - (1 : Nat)) : Nat)) : Nat)) - (1 : Nat))))) ->
    wf_sN N (. i)

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

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:22.1-22.23 -/
abbrev u128 : Type := uN

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:23.1-23.21 -/
abbrev s33 : Type := sN

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:30.1-30.21 -/
opaque signif : forall (N : N), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:34.1-34.20 -/
opaque expon : forall (N : N), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:38.1-38.47 -/
opaque M : forall (N : N), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:41.1-41.47 -/
opaque E : forall (N : N), Nat := opaqueDef

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:48.1-48.47 -/
abbrev exp : Type := Nat

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:49.1-53.84 -/
inductive fNmag : Type where
  | NORM (m : m) (exp : exp) : fNmag
  | SUBNORM (m : m) : fNmag
  | INF : fNmag
  | NAN (m : m) : fNmag
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:49.8-49.14 -/
inductive wf_fNmag : N -> fNmag -> Prop where
  | fNmag_case_0 : forall (N : N) (m : m) (exp : exp), 
    ((m < (2 ^ (M N))) && ((((2 : Nat) - ((2 ^ ((((E N) : Nat) - (1 : Nat)) : Nat)) : Nat)) <= exp) && (exp <= (((2 ^ ((((E N) : Nat) - (1 : Nat)) : Nat)) : Nat) - (1 : Nat))))) ->
    wf_fNmag N (.NORM m exp)
  | fNmag_case_1 : forall (N : N) (m : m) (exp : exp), 
    ((m < (2 ^ (M N))) && (((2 : Nat) - ((2 ^ ((((E N) : Nat) - (1 : Nat)) : Nat)) : Nat)) == exp)) ->
    wf_fNmag N (.SUBNORM m)
  | fNmag_case_2 : forall (N : N), wf_fNmag N .INF
  | fNmag_case_3 : forall (N : N) (m : m), 
    ((1 <= m) && (m < (2 ^ (M N)))) ->
    wf_fNmag N (.NAN m)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:44.1-46.35 -/
inductive fN : Type where
  | POS (fNmag : fNmag) : fN
  | NEG (fNmag : fNmag) : fN
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:44.8-44.11 -/
inductive wf_fN : N -> fN -> Prop where
  | fN_case_0 : forall (N : N) (fNmag : fNmag), 
    (wf_fNmag N fNmag) ->
    wf_fN N (.POS fNmag)
  | fN_case_1 : forall (N : N) (fNmag : fNmag), 
    (wf_fNmag N fNmag) ->
    wf_fN N (.NEG fNmag)

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:55.1-55.21 -/
abbrev f32 : Type := fN

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:56.1-56.21 -/
abbrev f64 : Type := fN

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:58.1-58.39 -/
opaque fzero : forall (N : N), fN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:61.1-61.44 -/
opaque fnat : forall (N : N) (nat : Nat), fN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:64.1-64.39 -/
opaque fone : forall (N : N), fN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:67.1-67.21 -/
opaque canon_ : forall (N : N), Nat := opaqueDef

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:73.1-74.8 -/
abbrev vN : Type := uN

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:76.1-76.23 -/
abbrev v128 : Type := vN

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:82.1-82.49 -/
inductive list (X : Type 0) : Type where
  |  ((List.map (fun (X : X) => X) X*) : (List X)) : list X
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:82.1-82.49 -/
opaque proj_list_0 : forall (X : Type) (x : (list X)), (List X) := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:87.1-87.85 -/
inductive char : Type where
  |  (i : Nat) : char
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:87.1-87.85 -/
opaque proj_char_0 : forall (x : char), Nat := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:87.8-87.12 -/
inductive wf_char : char -> Prop where
  | char_case_0 : forall (i : Nat), 
    (((i >= 0) && (i <= 55295)) || ((i >= 57344) && (i <= 1114111))) ->
    wf_char (. i)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/5.1-binary.values.spectec:44.1-44.39 -/
opaque cont : forall (byte : byte), Nat := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:89.1-89.25 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:89.1-89.25 -/
opaque utf8 : forall (_ : (List char)), (List byte) := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:91.1-91.70 -/
inductive name : Type where
  |  ((List.map (fun (char : char) => char) char*) : (List char)) : name
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:91.1-91.70 -/
opaque proj_name_0 : forall (x : name), (List char) := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:91.8-91.12 -/
inductive wf_name : name -> Prop where
  | name_case_0 : forall (char* : (List char)), 
    Forall (fun (char : char) => (wf_char char)) char* ->
    ((List.length (utf8 (List.map (fun (char : char) => char) char*))) < (2 ^ 32)) ->
    wf_name (. (List.map (fun (char : char) => char) char*))

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:98.1-98.36 -/
abbrev idx : Type := u32

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:99.1-99.44 -/
abbrev laneidx : Type := u8

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:101.1-101.45 -/
abbrev typeidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:102.1-102.49 -/
abbrev funcidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:103.1-103.49 -/
abbrev globalidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:104.1-104.47 -/
abbrev tableidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:105.1-105.46 -/
abbrev memidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:106.1-106.43 -/
abbrev tagidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:107.1-107.45 -/
abbrev elemidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:108.1-108.45 -/
abbrev dataidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:109.1-109.47 -/
abbrev labelidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:110.1-110.47 -/
abbrev localidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:111.1-111.47 -/
abbrev fieldidx : Type := idx

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:113.1-114.79 -/
inductive externidx : Type where
  | FUNC (funcidx : funcidx) : externidx
  | GLOBAL (globalidx : globalidx) : externidx
  | TABLE (tableidx : tableidx) : externidx
  | MEM (memidx : memidx) : externidx
  | TAG (tagidx : tagidx) : externidx
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:113.8-113.17 -/
inductive wf_externidx : externidx -> Prop where
  | externidx_case_0 : forall (funcidx : funcidx), 
    (wf_uN 32 funcidx) ->
    wf_externidx (.FUNC funcidx)
  | externidx_case_1 : forall (globalidx : globalidx), 
    (wf_uN 32 globalidx) ->
    wf_externidx (.GLOBAL globalidx)
  | externidx_case_2 : forall (tableidx : tableidx), 
    (wf_uN 32 tableidx) ->
    wf_externidx (.TABLE tableidx)
  | externidx_case_3 : forall (memidx : memidx), 
    (wf_uN 32 memidx) ->
    wf_externidx (.MEM memidx)
  | externidx_case_4 : forall (tagidx : tagidx), 
    (wf_uN 32 tagidx) ->
    wf_externidx (.TAG tagidx)

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:127.1-127.86 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:127.1-127.86 -/
opaque funcsxx : forall (_ : (List externidx)), (List typeidx) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:128.1-128.88 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:128.1-128.88 -/
opaque globalsxx : forall (_ : (List externidx)), (List globalidx) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:129.1-129.87 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:129.1-129.87 -/
opaque tablesxx : forall (_ : (List externidx)), (List tableidx) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:130.1-130.85 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:130.1-130.85 -/
opaque memsxx : forall (_ : (List externidx)), (List memidx) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:131.1-131.85 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:131.1-131.85 -/
opaque tagsxx : forall (_ : (List externidx)), (List tagidx) := opaqueDef

/- Record Creation Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:156.1-166.4 -/
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



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:156.8-156.12 -/
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

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:169.1-169.28 -/
opaque free_opt : forall (_ : (Option free)), free := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:170.1-170.29 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:170.1-170.29 -/
opaque free_list : forall (_ : (List free)), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:179.1-179.34 -/
opaque free_typeidx : forall (typeidx : typeidx), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:180.1-180.34 -/
opaque free_funcidx : forall (funcidx : funcidx), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:181.1-181.38 -/
opaque free_globalidx : forall (globalidx : globalidx), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:182.1-182.36 -/
opaque free_tableidx : forall (tableidx : tableidx), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:183.1-183.32 -/
opaque free_memidx : forall (memidx : memidx), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:184.1-184.34 -/
opaque free_elemidx : forall (elemidx : elemidx), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:185.1-185.34 -/
opaque free_dataidx : forall (dataidx : dataidx), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:186.1-186.36 -/
opaque free_localidx : forall (localidx : localidx), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:187.1-187.36 -/
opaque free_labelidx : forall (labelidx : labelidx), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:188.1-188.38 -/
opaque free_externidx : forall (externidx : externidx), free := opaqueDef

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
opaque numtype_addrtype : forall (_ : addrtype), numtype := opaqueDef

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
opaque consttype_numtype : forall (_ : numtype), consttype := opaqueDef

/- Auxiliary Definition at:  -/
opaque consttype_vectype : forall (_ : vectype), consttype := opaqueDef

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
  | _IDX (typeidx : typeidx) : typeuse
  | _DEF (rectype : rectype) (n : n) : typeuse
  | REC (n : n) : typeuse
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
  | _IDX (typeidx : typeidx) : heaptype
  | REC (n : n) : heaptype
  | _DEF (rectype : rectype) (n : n) : heaptype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:51.1-52.14 -/
inductive valtype : Type where
  | I32 : valtype
  | I64 : valtype
  | F32 : valtype
  | F64 : valtype
  | V128 : valtype
  | REF ((Option.map (fun (null : null) => null) null?) : (Option null)) (heaptype : heaptype) : valtype
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
  | REF ((Option.map (fun (null : null) => null) null?) : (Option null)) (heaptype : heaptype) : storagetype
  | I8 : storagetype
  | I16 : storagetype
deriving Inhabited, BEq


/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:102.1-103.16 -/
abbrev resulttype : Type := (list valtype)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:112.1-112.61 -/
inductive fieldtype : Type where
  |  ((Option.map (fun (mut : «mut») => «mut») mut?) : (Option «mut»)) (storagetype : storagetype) : fieldtype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:114.1-117.34 -/
inductive comptype : Type where
  | STRUCT (list : (list fieldtype)) : comptype
  | ARRAY (fieldtype : fieldtype) : comptype
  | FUNC (resulttype : resulttype) (_ : resulttype) : comptype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:119.1-120.33 -/
inductive subtype : Type where
  | SUB ((Option.map (fun (final : final) => final) final?) : (Option final)) ((List.map (fun (typeuse : typeuse) => typeuse) typeuse*) : (List typeuse)) (comptype : comptype) : subtype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:122.1-123.22 -/
inductive rectype : Type where
  | REC (list : (list subtype)) : rectype
deriving Inhabited, BEq


end

/- Auxiliary Definition at:  -/
opaque heaptype_absheaptype : forall (_ : absheaptype), heaptype := opaqueDef

/- Auxiliary Definition at:  -/
opaque valtype_addrtype : forall (_ : addrtype), valtype := opaqueDef

/- Auxiliary Definition at:  -/
opaque storagetype_consttype : forall (_ : consttype), storagetype := opaqueDef

/- Auxiliary Definition at:  -/
opaque storagetype_numtype : forall (_ : numtype), storagetype := opaqueDef

/- Auxiliary Definition at:  -/
opaque valtype_numtype : forall (_ : numtype), valtype := opaqueDef

/- Auxiliary Definition at:  -/
opaque heaptype_typeuse : forall (_ : typeuse), heaptype := opaqueDef

/- Auxiliary Definition at:  -/
opaque storagetype_valtype : forall (_ : valtype), storagetype := opaqueDef

/- Auxiliary Definition at:  -/
opaque storagetype_vectype : forall (_ : vectype), storagetype := opaqueDef

/- Auxiliary Definition at:  -/
opaque valtype_vectype : forall (_ : vectype), valtype := opaqueDef

/- Recursive Definitions at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:37.1-123.22 -/
mutual
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:37.8-37.15 -/
inductive wf_typeuse : typeuse -> Prop where
  | typeuse_case_0 : forall (typeidx : typeidx), 
    (wf_uN 32 typeidx) ->
    wf_typeuse (._IDX typeidx)
  | typeuse_case_1 : forall (rectype : rectype) (n : n), wf_typeuse (._DEF rectype n)
  | typeuse_case_2 : forall (n : n), wf_typeuse (.REC n)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:43.8-43.16 -/
inductive wf_heaptype : heaptype -> Prop where
  | heaptype_case_0 : wf_heaptype .ANY
  | heaptype_case_1 : wf_heaptype .EQ
  | heaptype_case_2 : wf_heaptype .I31
  | heaptype_case_3 : wf_heaptype .STRUCT
  | heaptype_case_4 : wf_heaptype .ARRAY
  | heaptype_case_5 : wf_heaptype .NONE
  | heaptype_case_6 : wf_heaptype .FUNC
  | heaptype_case_7 : wf_heaptype .NOFUNC
  | heaptype_case_8 : wf_heaptype .EXN
  | heaptype_case_9 : wf_heaptype .NOEXN
  | heaptype_case_10 : wf_heaptype .EXTERN
  | heaptype_case_11 : wf_heaptype .NOEXTERN
  | heaptype_case_12 : wf_heaptype .BOT
  | heaptype_case_13 : forall (typeidx : typeidx), 
    (wf_uN 32 typeidx) ->
    wf_heaptype (._IDX typeidx)
  | heaptype_case_14 : forall (n : n), wf_heaptype (.REC n)
  | heaptype_case_15 : forall (rectype : rectype) (n : n), wf_heaptype (._DEF rectype n)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:51.8-51.15 -/
inductive wf_valtype : valtype -> Prop where
  | valtype_case_0 : wf_valtype .I32
  | valtype_case_1 : wf_valtype .I64
  | valtype_case_2 : wf_valtype .F32
  | valtype_case_3 : wf_valtype .F64
  | valtype_case_4 : wf_valtype .V128
  | valtype_case_5 : forall (null? : (Option null)) (heaptype : heaptype), 
    (wf_heaptype heaptype) ->
    wf_valtype (.REF (Option.map (fun (null : null) => null) null?) heaptype)
  | valtype_case_6 : wf_valtype .BOT

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:92.8-92.19 -/
inductive wf_storagetype : storagetype -> Prop where
  | storagetype_case_0 : wf_storagetype .BOT
  | storagetype_case_1 : wf_storagetype .I32
  | storagetype_case_2 : wf_storagetype .I64
  | storagetype_case_3 : wf_storagetype .F32
  | storagetype_case_4 : wf_storagetype .F64
  | storagetype_case_5 : wf_storagetype .V128
  | storagetype_case_6 : forall (null? : (Option null)) (heaptype : heaptype), 
    (wf_heaptype heaptype) ->
    wf_storagetype (.REF (Option.map (fun (null : null) => null) null?) heaptype)
  | storagetype_case_7 : wf_storagetype .I8
  | storagetype_case_8 : wf_storagetype .I16

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:112.8-112.17 -/
inductive wf_fieldtype : fieldtype -> Prop where
  | fieldtype_case_0 : forall (mut? : (Option «mut»)) (storagetype : storagetype), 
    (wf_storagetype storagetype) ->
    wf_fieldtype (. (Option.map (fun (mut : «mut») => «mut») mut?) storagetype)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:114.8-114.16 -/
inductive wf_comptype : comptype -> Prop where
  | comptype_case_0 : forall (list : (list fieldtype)), wf_comptype (.STRUCT list)
  | comptype_case_1 : forall (fieldtype : fieldtype), 
    (wf_fieldtype fieldtype) ->
    wf_comptype (.ARRAY fieldtype)
  | comptype_case_2 : forall (resulttype : resulttype) (var_0 : resulttype), wf_comptype (.FUNC resulttype var_0)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:119.8-119.15 -/
inductive wf_subtype : subtype -> Prop where
  | subtype_case_0 : forall (final? : (Option final)) (typeuse* : (List typeuse)) (comptype : comptype), 
    Forall (fun (typeuse : typeuse) => (wf_typeuse typeuse)) typeuse* ->
    (wf_comptype comptype) ->
    wf_subtype (.SUB (Option.map (fun (final : final) => final) final?) (List.map (fun (typeuse : typeuse) => typeuse) typeuse*) comptype)

end

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:32.1-33.34 -/
inductive deftype : Type where
  | _DEF (rectype : rectype) (n : n) : deftype
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
opaque heaptype_deftype : forall (_ : deftype), heaptype := opaqueDef

/- Auxiliary Definition at:  -/
opaque typeuse_deftype : forall (_ : deftype), typeuse := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:40.1-41.42 -/
inductive typevar : Type where
  | _IDX (typeidx : typeidx) : typevar
  | REC (n : n) : typevar
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
opaque heaptype_typevar : forall (_ : typevar), heaptype := opaqueDef

/- Auxiliary Definition at:  -/
opaque typeuse_typevar : forall (_ : typevar), typeuse := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:40.8-40.15 -/
inductive wf_typevar : typevar -> Prop where
  | typevar_case_0 : forall (typeidx : typeidx), 
    (wf_uN 32 typeidx) ->
    wf_typevar (._IDX typeidx)
  | typevar_case_1 : forall (n : n), wf_typevar (.REC n)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:46.1-47.23 -/
inductive reftype : Type where
  | REF ((Option.map (fun (null : null) => null) null?) : (Option null)) (heaptype : heaptype) : reftype
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
opaque storagetype_reftype : forall (_ : reftype), storagetype := opaqueDef

/- Auxiliary Definition at:  -/
opaque valtype_reftype : forall (_ : reftype), valtype := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:46.8-46.15 -/
inductive wf_reftype : reftype -> Prop where
  | reftype_case_0 : forall (null? : (Option null)) (heaptype : heaptype), 
    (wf_heaptype heaptype) ->
    wf_reftype (.REF (Option.map (fun (null : null) => null) null?) heaptype)

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:55.1-55.55 -/
abbrev Inn : Type := addrtype

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:56.1-56.56 -/
inductive Fnn : Type where
  | F32 : Fnn
  | F64 : Fnn
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
opaque numtype_Fnn : forall (_ : Fnn), numtype := opaqueDef

/- Auxiliary Definition at:  -/
opaque valtype_Fnn : forall (_ : Fnn), valtype := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:57.1-57.51 -/
inductive Vnn : Type where
  | V128 : Vnn
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
opaque valtype_Vnn : forall (_ : Vnn), valtype := opaqueDef

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
opaque storagetype_packtype : forall (_ : packtype), storagetype := opaqueDef

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
opaque lanetype_Fnn : forall (_ : Fnn), lanetype := opaqueDef

/- Auxiliary Definition at:  -/
opaque lanetype_addrtype : forall (_ : addrtype), lanetype := opaqueDef

/- Auxiliary Definition at:  -/
opaque storagetype_lanetype : forall (_ : lanetype), storagetype := opaqueDef

/- Auxiliary Definition at:  -/
opaque lanetype_numtype : forall (_ : numtype), lanetype := opaqueDef

/- Auxiliary Definition at:  -/
opaque lanetype_packtype : forall (_ : packtype), lanetype := opaqueDef

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
opaque lanetype_Jnn : forall (_ : Jnn), lanetype := opaqueDef

/- Auxiliary Definition at:  -/
opaque Jnn_addrtype : forall (_ : addrtype), Jnn := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:97.1-97.62 -/
inductive Lnn : Type where
  | I32 : Lnn
  | I64 : Lnn
  | F32 : Lnn
  | F64 : Lnn
  | I8 : Lnn
  | I16 : Lnn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:128.1-128.74 -/
inductive limits : Type where
  |  (u64 : u64) (_ : (Option u64)) : limits
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:128.8-128.14 -/
inductive wf_limits : limits -> Prop where
  | limits_case_0 : forall (u64 : u64) (var_0 : (Option u64)), 
    (wf_uN 64 u64) ->
    Forall (fun (var_0 : u64) => (wf_uN 64 var_0)) (Option.toList var_0) ->
    wf_limits (. u64 var_0)

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:130.1-130.47 -/
abbrev tagtype : Type := typeuse

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:131.1-131.58 -/
inductive globaltype : Type where
  |  ((Option.map (fun (mut : «mut») => «mut») mut?) : (Option «mut»)) (valtype : valtype) : globaltype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:131.8-131.18 -/
inductive wf_globaltype : globaltype -> Prop where
  | globaltype_case_0 : forall (mut? : (Option «mut»)) (valtype : valtype), 
    (wf_valtype valtype) ->
    wf_globaltype (. (Option.map (fun (mut : «mut») => «mut») mut?) valtype)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:132.1-132.63 -/
inductive memtype : Type where
  | PAGE (addrtype : addrtype) (limits : limits) : memtype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:132.8-132.15 -/
inductive wf_memtype : memtype -> Prop where
  | memtype_case_0 : forall (addrtype : addrtype) (limits : limits), 
    (wf_limits limits) ->
    wf_memtype (.PAGE addrtype limits)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:133.1-133.67 -/
inductive tabletype : Type where
  |  (addrtype : addrtype) (limits : limits) (reftype : reftype) : tabletype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:133.8-133.17 -/
inductive wf_tabletype : tabletype -> Prop where
  | tabletype_case_0 : forall (addrtype : addrtype) (limits : limits) (reftype : reftype), 
    (wf_limits limits) ->
    (wf_reftype reftype) ->
    wf_tabletype (. addrtype limits reftype)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:134.1-134.64 -/
inductive datatype : Type where
  | OK : datatype
deriving Inhabited, BEq


/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:135.1-135.52 -/
abbrev elemtype : Type := reftype

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:137.1-138.83 -/
inductive externtype : Type where
  | TAG (tagtype : tagtype) : externtype
  | GLOBAL (globaltype : globaltype) : externtype
  | MEM (memtype : memtype) : externtype
  | TABLE (tabletype : tabletype) : externtype
  | FUNC (typeuse : typeuse) : externtype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:137.8-137.18 -/
inductive wf_externtype : externtype -> Prop where
  | externtype_case_0 : forall (tagtype : tagtype), 
    (wf_typeuse tagtype) ->
    wf_externtype (.TAG tagtype)
  | externtype_case_1 : forall (globaltype : globaltype), 
    (wf_globaltype globaltype) ->
    wf_externtype (.GLOBAL globaltype)
  | externtype_case_2 : forall (memtype : memtype), 
    (wf_memtype memtype) ->
    wf_externtype (.MEM memtype)
  | externtype_case_3 : forall (tabletype : tabletype), 
    (wf_tabletype tabletype) ->
    wf_externtype (.TABLE tabletype)
  | externtype_case_4 : forall (typeuse : typeuse), 
    (wf_typeuse typeuse) ->
    wf_externtype (.FUNC typeuse)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:140.1-141.47 -/
inductive moduletype : Type where
  |  ((List.map (fun (externtype : externtype) => externtype) externtype*) : (List externtype)) (_ : (List externtype)) : moduletype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:140.8-140.18 -/
inductive wf_moduletype : moduletype -> Prop where
  | moduletype_case_0 : forall (externtype* : (List externtype)) (var_0 : (List externtype)), 
    Forall (fun (externtype : externtype) => (wf_externtype externtype)) externtype* ->
    Forall (fun (var_0 : externtype) => (wf_externtype var_0)) var_0 ->
    wf_moduletype (. (List.map (fun (externtype : externtype) => externtype) externtype*) var_0)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:179.1-179.51 -/
opaque IN : forall (N : N), Inn := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:183.1-183.51 -/
opaque FN : forall (N : N), Fnn := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:187.1-187.51 -/
opaque JN : forall (N : N), Jnn := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:196.1-196.46 -/
opaque size : forall (numtype : numtype), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:197.1-197.46 -/
opaque vsize : forall (vectype : vectype), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:198.1-198.46 -/
opaque psize : forall (packtype : packtype), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:199.1-199.46 -/
opaque lsize : forall (lanetype : lanetype), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:200.1-200.46 -/
opaque zsize : forall (storagetype : storagetype), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:201.1-201.71 -/
opaque isize : forall (Inn : Inn), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:202.1-202.71 -/
opaque jsize : forall (Jnn : Jnn), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:203.1-203.71 -/
opaque fsize : forall (Fnn : Fnn), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:226.1-226.40 -/
opaque inv_isize : forall (nat : Nat), (Option Inn) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:227.1-227.40 -/
opaque inv_jsize : forall (nat : Nat), (Option Jnn) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:228.1-228.40 -/
opaque inv_fsize : forall (nat : Nat), (Option Fnn) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:239.1-239.63 -/
opaque sizenn : forall (numtype : numtype), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:240.1-240.63 -/
opaque sizenn1 : forall (numtype : numtype), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:241.1-241.63 -/
opaque sizenn2 : forall (numtype : numtype), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:246.1-246.63 -/
opaque vsizenn : forall (vectype : vectype), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:249.1-249.63 -/
opaque psizenn : forall (packtype : packtype), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:252.1-252.63 -/
opaque lsizenn : forall (lanetype : lanetype), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:253.1-253.63 -/
opaque lsizenn1 : forall (lanetype : lanetype), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:254.1-254.63 -/
opaque lsizenn2 : forall (lanetype : lanetype), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:259.1-259.83 -/
opaque jsizenn : forall (Jnn : Jnn), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:262.1-262.42 -/
opaque inv_jsizenn : forall (nat : Nat), (Option Jnn) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:268.1-268.56 -/
opaque lunpack : forall (lanetype : lanetype), numtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:272.1-272.35 -/
opaque unpack : forall (storagetype : storagetype), valtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:276.1-276.73 -/
opaque nunpack : forall (storagetype : storagetype), (Option numtype) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:280.1-280.73 -/
opaque vunpack : forall (storagetype : storagetype), (Option vectype) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:283.1-283.74 -/
opaque cunpack : forall (storagetype : storagetype), (Option consttype) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:291.1-291.90 -/
opaque minat : forall (addrtype : addrtype) (addrtype : addrtype), addrtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:295.1-295.82 -/
opaque diffrt : forall (reftype : reftype) (reftype : reftype), reftype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:300.1-300.49 -/
opaque as_deftype : forall (typeuse : typeuse), deftype := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:308.1-308.87 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:308.1-308.87 -/
opaque tagsxt : forall (_ : (List externtype)), (List tagtype) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:309.1-309.90 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:309.1-309.90 -/
opaque globalsxt : forall (_ : (List externtype)), (List globaltype) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:310.1-310.87 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:310.1-310.87 -/
opaque memsxt : forall (_ : (List externtype)), (List memtype) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:311.1-311.89 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:311.1-311.89 -/
opaque tablesxt : forall (_ : (List externtype)), (List tabletype) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:312.1-312.88 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:312.1-312.88 -/
opaque funcsxt : forall (_ : (List externtype)), (List deftype) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:337.1-337.112 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:337.1-337.112 -/
opaque subst_typevar : forall (typevar : typevar) (_ : (List typevar)) (_ : (List typeuse)), typeuse := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:401.1-401.59 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:401.1-401.59 -/
opaque minus_recs : forall (_ : (List typevar)) (_ : (List typeuse)), (List typevar) × (List typeuse) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:347.1-347.112 -/
opaque subst_packtype : forall (packtype : packtype) (_ : (List typevar)) (_ : (List typeuse)), packtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:341.1-341.112 -/
opaque subst_numtype : forall (numtype : numtype) (_ : (List typevar)) (_ : (List typeuse)), numtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:342.1-342.112 -/
opaque subst_vectype : forall (vectype : vectype) (_ : (List typevar)) (_ : (List typeuse)), vectype := opaqueDef

/- Recursive Definitions at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:338.1-354.112 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:338.1-338.112 -/
opaque subst_typeuse : forall (typeuse : typeuse) (_ : (List typevar)) (_ : (List typeuse)), typeuse := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:343.1-343.112 -/
opaque subst_heaptype : forall (heaptype : heaptype) (_ : (List typevar)) (_ : (List typeuse)), heaptype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:344.1-344.112 -/
opaque subst_reftype : forall (reftype : reftype) (_ : (List typevar)) (_ : (List typeuse)), reftype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:345.1-345.112 -/
opaque subst_valtype : forall (valtype : valtype) (_ : (List typevar)) (_ : (List typeuse)), valtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:348.1-348.112 -/
opaque subst_storagetype : forall (storagetype : storagetype) (_ : (List typevar)) (_ : (List typeuse)), storagetype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:349.1-349.112 -/
opaque subst_fieldtype : forall (fieldtype : fieldtype) (_ : (List typevar)) (_ : (List typeuse)), fieldtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:351.1-351.112 -/
opaque subst_comptype : forall (comptype : comptype) (_ : (List typevar)) (_ : (List typeuse)), comptype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:352.1-352.112 -/
opaque subst_subtype : forall (subtype : subtype) (_ : (List typevar)) (_ : (List typeuse)), subtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:353.1-353.112 -/
opaque subst_rectype : forall (rectype : rectype) (_ : (List typevar)) (_ : (List typeuse)), rectype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:354.1-354.112 -/
opaque subst_deftype : forall (deftype : deftype) (_ : (List typevar)) (_ : (List typeuse)), deftype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:340.1-340.112 -/
opaque subst_addrtype : forall (addrtype : addrtype) (_ : (List typevar)) (_ : (List typeuse)), addrtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:356.1-356.112 -/
opaque subst_tagtype : forall (tagtype : tagtype) (_ : (List typevar)) (_ : (List typeuse)), tagtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:357.1-357.112 -/
opaque subst_globaltype : forall (globaltype : globaltype) (_ : (List typevar)) (_ : (List typeuse)), globaltype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:358.1-358.112 -/
opaque subst_memtype : forall (memtype : memtype) (_ : (List typevar)) (_ : (List typeuse)), memtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:359.1-359.112 -/
opaque subst_tabletype : forall (tabletype : tabletype) (_ : (List typevar)) (_ : (List typeuse)), tabletype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:361.1-361.112 -/
opaque subst_externtype : forall (externtype : externtype) (_ : (List typevar)) (_ : (List typeuse)), externtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:362.1-362.112 -/
opaque subst_moduletype : forall (moduletype : moduletype) (_ : (List typevar)) (_ : (List typeuse)), moduletype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:431.1-431.94 -/
opaque subst_all_valtype : forall (valtype : valtype) (_ : (List typeuse)), valtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:432.1-432.94 -/
opaque subst_all_reftype : forall (reftype : reftype) (_ : (List typeuse)), reftype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:433.1-433.94 -/
opaque subst_all_deftype : forall (deftype : deftype) (_ : (List typeuse)), deftype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:434.1-434.94 -/
opaque subst_all_tagtype : forall (tagtype : tagtype) (_ : (List typeuse)), tagtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:435.1-435.103 -/
opaque subst_all_globaltype : forall (globaltype : globaltype) (_ : (List typeuse)), globaltype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:436.1-436.94 -/
opaque subst_all_memtype : forall (memtype : memtype) (_ : (List typeuse)), memtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:437.1-437.100 -/
opaque subst_all_tabletype : forall (tabletype : tabletype) (_ : (List typeuse)), tabletype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:438.1-438.103 -/
opaque subst_all_externtype : forall (externtype : externtype) (_ : (List typeuse)), externtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:439.1-439.103 -/
opaque subst_all_moduletype : forall (moduletype : moduletype) (_ : (List typeuse)), moduletype := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:451.1-451.97 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:451.1-451.97 -/
opaque subst_all_deftypes : forall (_ : (List deftype)) (_ : (List typeuse)), (List deftype) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:458.1-458.88 -/
opaque rollrt : forall (typeidx : typeidx) (rectype : rectype), rectype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:459.1-459.90 -/
opaque unrollrt : forall (rectype : rectype), rectype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:460.1-460.90 -/
opaque rolldt : forall (typeidx : typeidx) (rectype : rectype), (List deftype) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:461.1-461.90 -/
opaque unrolldt : forall (deftype : deftype), subtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:462.1-462.90 -/
opaque expanddt : forall (deftype : deftype), comptype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:477.1-477.35 -/
opaque free_addrtype : forall (numtype : numtype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:478.1-478.34 -/
opaque free_numtype : forall (numtype : numtype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:479.1-479.36 -/
opaque free_packtype : forall (packtype : packtype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:480.1-480.36 -/
opaque free_lanetype : forall (lanetype : lanetype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:481.1-481.34 -/
opaque free_vectype : forall (vectype : vectype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:482.1-482.38 -/
opaque free_consttype : forall (consttype : consttype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:483.1-483.42 -/
opaque free_absheaptype : forall (absheaptype : absheaptype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:486.1-486.34 -/
opaque free_typevar : forall (typevar : typevar), free := opaqueDef

/- Recursive Definitions at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:484.1-523.34 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:484.1-484.36 -/
opaque free_heaptype : forall (heaptype : heaptype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:485.1-485.34 -/
opaque free_reftype : forall (reftype : reftype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:487.1-487.34 -/
opaque free_typeuse : forall (typeuse : typeuse), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:488.1-488.34 -/
opaque free_valtype : forall (valtype : valtype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:490.1-490.40 -/
opaque free_resulttype : forall (resulttype : resulttype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:491.1-491.42 -/
opaque free_storagetype : forall (storagetype : storagetype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:492.1-492.38 -/
opaque free_fieldtype : forall (fieldtype : fieldtype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:493.1-493.36 -/
opaque free_comptype : forall (comptype : comptype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:494.1-494.34 -/
opaque free_subtype : forall (subtype : subtype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:495.1-495.34 -/
opaque free_rectype : forall (rectype : rectype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:523.1-523.34 -/
opaque free_deftype : forall (deftype : deftype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:497.1-497.34 -/
opaque free_tagtype : forall (tagtype : tagtype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:498.1-498.40 -/
opaque free_globaltype : forall (globaltype : globaltype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:499.1-499.34 -/
opaque free_memtype : forall (memtype : memtype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:500.1-500.38 -/
opaque free_tabletype : forall (tabletype : tabletype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:501.1-501.36 -/
opaque free_datatype : forall (datatype : datatype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:502.1-502.36 -/
opaque free_elemtype : forall (elemtype : elemtype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:503.1-503.40 -/
opaque free_externtype : forall (externtype : externtype), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:504.1-504.40 -/
opaque free_moduletype : forall (moduletype : moduletype), free := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:7.1-7.21 -/
inductive num_ : Type where
  | mk_num__0 (Inn : Inn) (var_x : iN) : num_
  | mk_num__1 (Fnn : Fnn) (var_x : fN) : num_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:7.8-7.13 -/
inductive wf_num_ : numtype -> num_ -> Prop where
  | num__case_0 : forall (numtype : numtype) (Inn : Inn) (var_x : iN), 
    (wf_uN (size (numtype_addrtype Inn)) var_x) ->
    (numtype == (numtype_addrtype Inn)) ->
    wf_num_ numtype (.mk_num__0 Inn var_x)
  | num__case_1 : forall (numtype : numtype) (Fnn : Fnn) (var_x : fN), 
    (wf_fN (sizenn (numtype_Fnn Fnn)) var_x) ->
    (numtype == (numtype_Fnn Fnn)) ->
    wf_num_ numtype (.mk_num__1 Fnn var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:7.1-7.21 -/
opaque proj_num__0 : forall (Inn : Inn) (var_x : num_), (Option iN) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:7.1-7.21 -/
opaque proj_num__1 : forall (Fnn : Fnn) (var_x : num_), (Option fN) := opaqueDef

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:11.1-11.38 -/
abbrev pack_ : Type := iN

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:13.1-13.23 -/
inductive lane_ : Type where
  | mk_lane__0 (numtype : numtype) (var_x : num_) : lane_
  | mk_lane__1 (packtype : packtype) (var_x : pack_) : lane_
  | mk_lane__2 (Jnn : Jnn) (var_x : iN) : lane_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:13.8-13.14 -/
inductive wf_lane_ : lanetype -> lane_ -> Prop where
  | lane__case_0 : forall (lanetype : lanetype) (numtype : numtype) (var_x : num_), 
    (wf_num_ numtype var_x) ->
    (lanetype == (lanetype_numtype numtype)) ->
    wf_lane_ lanetype (.mk_lane__0 numtype var_x)
  | lane__case_1 : forall (lanetype : lanetype) (packtype : packtype) (var_x : pack_), 
    (wf_uN (psize packtype) var_x) ->
    (lanetype == (lanetype_packtype packtype)) ->
    wf_lane_ lanetype (.mk_lane__1 packtype var_x)
  | lane__case_2 : forall (lanetype : lanetype) (Jnn : Jnn) (var_x : iN), 
    (wf_uN (lsize (lanetype_Jnn Jnn)) var_x) ->
    (lanetype == (lanetype_Jnn Jnn)) ->
    wf_lane_ lanetype (.mk_lane__2 Jnn var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:13.1-13.23 -/
opaque proj_lane__0 : forall (numtype : numtype) (var_x : lane_), (Option num_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:13.1-13.23 -/
opaque proj_lane__1 : forall (packtype : packtype) (var_x : lane_), (Option pack_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:13.1-13.23 -/
opaque proj_lane__2 : forall (Jnn : Jnn) (var_x : lane_), (Option iN) := opaqueDef

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:18.1-18.35 -/
abbrev vec_ : Type := vN

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:20.1-20.25 -/
inductive lit_ : Type where
  | mk_lit__0 (numtype : numtype) (var_x : num_) : lit_
  | mk_lit__1 (vectype : vectype) (var_x : vec_) : lit_
  | mk_lit__2 (packtype : packtype) (var_x : pack_) : lit_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:20.8-20.13 -/
inductive wf_lit_ : storagetype -> lit_ -> Prop where
  | lit__case_0 : forall (storagetype : storagetype) (numtype : numtype) (var_x : num_), 
    (wf_num_ numtype var_x) ->
    (storagetype == (storagetype_numtype numtype)) ->
    wf_lit_ storagetype (.mk_lit__0 numtype var_x)
  | lit__case_1 : forall (storagetype : storagetype) (vectype : vectype) (var_x : vec_), 
    (wf_uN (vsize vectype) var_x) ->
    (storagetype == (storagetype_vectype vectype)) ->
    wf_lit_ storagetype (.mk_lit__1 vectype var_x)
  | lit__case_2 : forall (storagetype : storagetype) (packtype : packtype) (var_x : pack_), 
    (wf_uN (psize packtype) var_x) ->
    (storagetype == (storagetype_packtype packtype)) ->
    wf_lit_ storagetype (.mk_lit__2 packtype var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:20.1-20.25 -/
opaque proj_lit__0 : forall (numtype : numtype) (var_x : lit_), (Option num_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:20.1-20.25 -/
opaque proj_lit__1 : forall (vectype : vectype) (var_x : lit_), (Option vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:20.1-20.25 -/
opaque proj_lit__2 : forall (packtype : packtype) (var_x : lit_), (Option pack_) := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:28.1-28.56 -/
inductive sz : Type where
  |  (i : Nat) : sz
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:28.1-28.56 -/
opaque proj_sz_0 : forall (x : sz), Nat := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:28.8-28.10 -/
inductive wf_sz : sz -> Prop where
  | sz_case_0 : forall (i : Nat), 
    ((((i == 8) || (i == 16)) || (i == 32)) || (i == 64)) ->
    wf_sz (. i)

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
  | EXTEND (sz : sz) : unop_Inn
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.8-31.14 -/
inductive wf_unop_Inn : Inn -> unop_Inn -> Prop where
  | unop_Inn_case_0 : forall (Inn : Inn), wf_unop_Inn Inn .CLZ
  | unop_Inn_case_1 : forall (Inn : Inn), wf_unop_Inn Inn .CTZ
  | unop_Inn_case_2 : forall (Inn : Inn), wf_unop_Inn Inn .POPCNT
  | unop_Inn_case_3 : forall (Inn : Inn) (sz : sz), 
    (wf_sz sz) ->
    ((proj_sz_0 sz) < (sizenn (numtype_addrtype Inn))) ->
    wf_unop_Inn Inn (.EXTEND sz)

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
  | mk_unop__0 (Inn : Inn) (var_x : unop_Inn) : unop_
  | mk_unop__1 (Fnn : Fnn) (var_x : unop_Fnn) : unop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.8-31.14 -/
inductive wf_unop_ : numtype -> unop_ -> Prop where
  | unop__case_0 : forall (numtype : numtype) (Inn : Inn) (var_x : unop_Inn), 
    (wf_unop_Inn Inn var_x) ->
    (numtype == (numtype_addrtype Inn)) ->
    wf_unop_ numtype (.mk_unop__0 Inn var_x)
  | unop__case_1 : forall (numtype : numtype) (Fnn : Fnn) (var_x : unop_Fnn), 
    (numtype == (numtype_Fnn Fnn)) ->
    wf_unop_ numtype (.mk_unop__1 Fnn var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.1-31.22 -/
opaque proj_unop__0 : forall (Inn : Inn) (var_x : unop_), (Option unop_Inn) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.1-31.22 -/
opaque proj_unop__1 : forall (Fnn : Fnn) (var_x : unop_), (Option unop_Fnn) := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:35.1-35.23 -/
inductive binop_Inn : Type where
  | ADD : binop_Inn
  | SUB : binop_Inn
  | MUL : binop_Inn
  | DIV (sx : sx) : binop_Inn
  | REM (sx : sx) : binop_Inn
  | AND : binop_Inn
  | OR : binop_Inn
  | XOR : binop_Inn
  | SHL : binop_Inn
  | SHR (sx : sx) : binop_Inn
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
  | mk_binop__0 (Inn : Inn) (var_x : binop_Inn) : binop_
  | mk_binop__1 (Fnn : Fnn) (var_x : binop_Fnn) : binop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:35.8-35.15 -/
inductive wf_binop_ : numtype -> binop_ -> Prop where
  | binop__case_0 : forall (numtype : numtype) (Inn : Inn) (var_x : binop_Inn), 
    (numtype == (numtype_addrtype Inn)) ->
    wf_binop_ numtype (.mk_binop__0 Inn var_x)
  | binop__case_1 : forall (numtype : numtype) (Fnn : Fnn) (var_x : binop_Fnn), 
    (numtype == (numtype_Fnn Fnn)) ->
    wf_binop_ numtype (.mk_binop__1 Fnn var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:35.1-35.23 -/
opaque proj_binop__0 : forall (Inn : Inn) (var_x : binop_), (Option binop_Inn) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:35.1-35.23 -/
opaque proj_binop__1 : forall (Fnn : Fnn) (var_x : binop_), (Option binop_Fnn) := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:42.1-42.24 -/
inductive testop_Inn : Type where
  | EQZ : testop_Inn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:42.1-42.24 -/
inductive testop_ : Type where
  | mk_testop__0 (Inn : Inn) (var_x : testop_Inn) : testop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:42.8-42.16 -/
inductive wf_testop_ : numtype -> testop_ -> Prop where
  | testop__case_0 : forall (numtype : numtype) (Inn : Inn) (var_x : testop_Inn), 
    (numtype == (numtype_addrtype Inn)) ->
    wf_testop_ numtype (.mk_testop__0 Inn var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:42.1-42.24 -/
opaque proj_testop__0 : forall (Inn : Inn) (var_x : testop_), testop_Inn := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:46.1-46.23 -/
inductive relop_Inn : Type where
  | EQ : relop_Inn
  | NE : relop_Inn
  | LT (sx : sx) : relop_Inn
  | GT (sx : sx) : relop_Inn
  | LE (sx : sx) : relop_Inn
  | GE (sx : sx) : relop_Inn
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
  | mk_relop__0 (Inn : Inn) (var_x : relop_Inn) : relop_
  | mk_relop__1 (Fnn : Fnn) (var_x : relop_Fnn) : relop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:46.8-46.15 -/
inductive wf_relop_ : numtype -> relop_ -> Prop where
  | relop__case_0 : forall (numtype : numtype) (Inn : Inn) (var_x : relop_Inn), 
    (numtype == (numtype_addrtype Inn)) ->
    wf_relop_ numtype (.mk_relop__0 Inn var_x)
  | relop__case_1 : forall (numtype : numtype) (Fnn : Fnn) (var_x : relop_Fnn), 
    (numtype == (numtype_Fnn Fnn)) ->
    wf_relop_ numtype (.mk_relop__1 Fnn var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:46.1-46.23 -/
opaque proj_relop__0 : forall (Inn : Inn) (var_x : relop_), (Option relop_Inn) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:46.1-46.23 -/
opaque proj_relop__1 : forall (Fnn : Fnn) (var_x : relop_), (Option relop_Fnn) := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 -/
inductive cvtop__Inn_1_Inn_2 : Type where
  | EXTEND (sx : sx) : cvtop__Inn_1_Inn_2
  | WRAP : cvtop__Inn_1_Inn_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.8-55.16 -/
inductive wf_cvtop__Inn_1_Inn_2 : Inn -> Inn -> cvtop__Inn_1_Inn_2 -> Prop where
  | cvtop__Inn_1_Inn_2_case_0 : forall (Inn_1 : Inn) (Inn_2 : Inn) (sx : sx), 
    ((sizenn1 (numtype_addrtype Inn_1)) < (sizenn2 (numtype_addrtype Inn_2))) ->
    wf_cvtop__Inn_1_Inn_2 Inn_1 Inn_2 (.EXTEND sx)
  | cvtop__Inn_1_Inn_2_case_1 : forall (Inn_1 : Inn) (Inn_2 : Inn), 
    ((sizenn1 (numtype_addrtype Inn_1)) > (sizenn2 (numtype_addrtype Inn_2))) ->
    wf_cvtop__Inn_1_Inn_2 Inn_1 Inn_2 .WRAP

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 -/
inductive cvtop__Inn_1_Fnn_2 : Type where
  | CONVERT (sx : sx) : cvtop__Inn_1_Fnn_2
  | REINTERPRET : cvtop__Inn_1_Fnn_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.8-55.16 -/
inductive wf_cvtop__Inn_1_Fnn_2 : Inn -> Fnn -> cvtop__Inn_1_Fnn_2 -> Prop where
  | cvtop__Inn_1_Fnn_2_case_0 : forall (Inn_1 : Inn) (Fnn_2 : Fnn) (sx : sx), wf_cvtop__Inn_1_Fnn_2 Inn_1 Fnn_2 (.CONVERT sx)
  | cvtop__Inn_1_Fnn_2_case_1 : forall (Inn_1 : Inn) (Fnn_2 : Fnn), 
    ((sizenn1 (numtype_addrtype Inn_1)) == (sizenn2 (numtype_Fnn Fnn_2))) ->
    wf_cvtop__Inn_1_Fnn_2 Inn_1 Fnn_2 .REINTERPRET

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 -/
inductive cvtop__Fnn_1_Inn_2 : Type where
  | TRUNC (sx : sx) : cvtop__Fnn_1_Inn_2
  | TRUNC_SAT (sx : sx) : cvtop__Fnn_1_Inn_2
  | REINTERPRET : cvtop__Fnn_1_Inn_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.8-55.16 -/
inductive wf_cvtop__Fnn_1_Inn_2 : Fnn -> Inn -> cvtop__Fnn_1_Inn_2 -> Prop where
  | cvtop__Fnn_1_Inn_2_case_0 : forall (Fnn_1 : Fnn) (Inn_2 : Inn) (sx : sx), wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 (.TRUNC sx)
  | cvtop__Fnn_1_Inn_2_case_1 : forall (Fnn_1 : Fnn) (Inn_2 : Inn) (sx : sx), wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 (.TRUNC_SAT sx)
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
opaque proj_cvtop___0 : forall (Inn_1 : Inn) (Inn_2 : Inn) (var_x : cvtop__), (Option cvtop__Inn_1_Inn_2) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 -/
opaque proj_cvtop___1 : forall (Inn_1 : Inn) (Fnn_2 : Fnn) (var_x : cvtop__), (Option cvtop__Inn_1_Fnn_2) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 -/
opaque proj_cvtop___2 : forall (Fnn_1 : Fnn) (Inn_2 : Inn) (var_x : cvtop__), (Option cvtop__Fnn_1_Inn_2) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 -/
opaque proj_cvtop___3 : forall (Fnn_1 : Fnn) (Fnn_2 : Fnn) (var_x : cvtop__), (Option cvtop__Fnn_1_Fnn_2) := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:73.1-73.60 -/
inductive dim : Type where
  |  (i : Nat) : dim
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:73.1-73.60 -/
opaque proj_dim_0 : forall (x : dim), Nat := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:73.8-73.11 -/
inductive wf_dim : dim -> Prop where
  | dim_case_0 : forall (i : Nat), 
    (((((i == 1) || (i == 2)) || (i == 4)) || (i == 8)) || (i == 16)) ->
    wf_dim (. i)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:74.1-75.40 -/
inductive shape : Type where
  | X (lanetype : lanetype) (dim : dim) : shape
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:74.8-74.13 -/
inductive wf_shape : shape -> Prop where
  | shape_case_0 : forall (lanetype : lanetype) (dim : dim), 
    (wf_dim dim) ->
    (((lsize lanetype) * (proj_dim_0 dim)) == 128) ->
    wf_shape (.X lanetype dim)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:78.1-78.43 -/
opaque dim : forall (shape : shape), dim := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:81.1-81.58 -/
opaque lanetype : forall (shape : shape), lanetype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:84.1-84.57 -/
opaque unpackshape : forall (shape : shape), numtype := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:88.1-88.78 -/
inductive ishape : Type where
  |  (shape : shape) : ishape
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:88.1-88.78 -/
opaque proj_ishape_0 : forall (x : ishape), shape := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:88.8-88.14 -/
inductive wf_ishape : ishape -> Prop where
  | ishape_case_0 : forall (shape : shape) (Jnn : Jnn), 
    (wf_shape shape) ->
    ((lanetype shape) == (lanetype_Jnn Jnn)) ->
    wf_ishape (. shape)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:89.1-89.77 -/
inductive bshape : Type where
  |  (shape : shape) : bshape
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:89.1-89.77 -/
opaque proj_bshape_0 : forall (x : bshape), shape := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:89.8-89.14 -/
inductive wf_bshape : bshape -> Prop where
  | bshape_case_0 : forall (shape : shape), 
    (wf_shape shape) ->
    ((lanetype shape) == .I8) ->
    wf_bshape (. shape)

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
  | vunop_Jnn_M_case_0 : forall (Jnn : Jnn) (M : M), wf_vunop_Jnn_M Jnn M .ABS
  | vunop_Jnn_M_case_1 : forall (Jnn : Jnn) (M : M), wf_vunop_Jnn_M Jnn M .NEG
  | vunop_Jnn_M_case_2 : forall (Jnn : Jnn) (M : M), 
    ((lsizenn (lanetype_Jnn Jnn)) == 8) ->
    wf_vunop_Jnn_M Jnn M .POPCNT

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
  | mk_vunop__0 (Jnn : Jnn) (M : M) (var_x : vunop_Jnn_M) : vunop_
  | mk_vunop__1 (Fnn : Fnn) (M : M) (var_x : vunop_Fnn_M) : vunop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.8-102.15 -/
inductive wf_vunop_ : shape -> vunop_ -> Prop where
  | vunop__case_0 : forall (shape : shape) (Jnn : Jnn) (M : M) (var_x : vunop_Jnn_M), 
    (wf_vunop_Jnn_M Jnn M var_x) ->
    (shape == (.X (lanetype_Jnn Jnn) (. M))) ->
    wf_vunop_ shape (.mk_vunop__0 Jnn M var_x)
  | vunop__case_1 : forall (shape : shape) (Fnn : Fnn) (M : M) (var_x : vunop_Fnn_M), 
    (shape == (.X (lanetype_Fnn Fnn) (. M))) ->
    wf_vunop_ shape (.mk_vunop__1 Fnn M var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.1-102.42 -/
opaque proj_vunop__0 : forall (Jnn : Jnn) (M : M) (var_x : vunop_), (Option vunop_Jnn_M) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.1-102.42 -/
opaque proj_vunop__1 : forall (Fnn : Fnn) (M : M) (var_x : vunop_), (Option vunop_Fnn_M) := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:107.1-107.43 -/
inductive vbinop_Jnn_M : Type where
  | ADD : vbinop_Jnn_M
  | SUB : vbinop_Jnn_M
  | ADD_SAT (sx : sx) : vbinop_Jnn_M
  | SUB_SAT (sx : sx) : vbinop_Jnn_M
  | MUL : vbinop_Jnn_M
  | AVGRU : vbinop_Jnn_M
  | Q15MULR_SATS : vbinop_Jnn_M
  | RELAXED_Q15MULRS : vbinop_Jnn_M
  | MIN (sx : sx) : vbinop_Jnn_M
  | MAX (sx : sx) : vbinop_Jnn_M
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:107.8-107.16 -/
inductive wf_vbinop_Jnn_M : Jnn -> M -> vbinop_Jnn_M -> Prop where
  | vbinop_Jnn_M_case_0 : forall (Jnn : Jnn) (M : M), wf_vbinop_Jnn_M Jnn M .ADD
  | vbinop_Jnn_M_case_1 : forall (Jnn : Jnn) (M : M), wf_vbinop_Jnn_M Jnn M .SUB
  | vbinop_Jnn_M_case_2 : forall (Jnn : Jnn) (M : M) (sx : sx), 
    ((lsizenn (lanetype_Jnn Jnn)) <= 16) ->
    wf_vbinop_Jnn_M Jnn M (.ADD_SAT sx)
  | vbinop_Jnn_M_case_3 : forall (Jnn : Jnn) (M : M) (sx : sx), 
    ((lsizenn (lanetype_Jnn Jnn)) <= 16) ->
    wf_vbinop_Jnn_M Jnn M (.SUB_SAT sx)
  | vbinop_Jnn_M_case_4 : forall (Jnn : Jnn) (M : M), 
    ((lsizenn (lanetype_Jnn Jnn)) >= 16) ->
    wf_vbinop_Jnn_M Jnn M .MUL
  | vbinop_Jnn_M_case_5 : forall (Jnn : Jnn) (M : M), 
    ((lsizenn (lanetype_Jnn Jnn)) <= 16) ->
    wf_vbinop_Jnn_M Jnn M .AVGRU
  | vbinop_Jnn_M_case_6 : forall (Jnn : Jnn) (M : M), 
    ((lsizenn (lanetype_Jnn Jnn)) == 16) ->
    wf_vbinop_Jnn_M Jnn M .Q15MULR_SATS
  | vbinop_Jnn_M_case_7 : forall (Jnn : Jnn) (M : M), 
    ((lsizenn (lanetype_Jnn Jnn)) == 16) ->
    wf_vbinop_Jnn_M Jnn M .RELAXED_Q15MULRS
  | vbinop_Jnn_M_case_8 : forall (Jnn : Jnn) (M : M) (sx : sx), 
    ((lsizenn (lanetype_Jnn Jnn)) <= 32) ->
    wf_vbinop_Jnn_M Jnn M (.MIN sx)
  | vbinop_Jnn_M_case_9 : forall (Jnn : Jnn) (M : M) (sx : sx), 
    ((lsizenn (lanetype_Jnn Jnn)) <= 32) ->
    wf_vbinop_Jnn_M Jnn M (.MAX sx)

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
  | mk_vbinop__0 (Jnn : Jnn) (M : M) (var_x : vbinop_Jnn_M) : vbinop_
  | mk_vbinop__1 (Fnn : Fnn) (M : M) (var_x : vbinop_Fnn_M) : vbinop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:107.8-107.16 -/
inductive wf_vbinop_ : shape -> vbinop_ -> Prop where
  | vbinop__case_0 : forall (shape : shape) (Jnn : Jnn) (M : M) (var_x : vbinop_Jnn_M), 
    (wf_vbinop_Jnn_M Jnn M var_x) ->
    (shape == (.X (lanetype_Jnn Jnn) (. M))) ->
    wf_vbinop_ shape (.mk_vbinop__0 Jnn M var_x)
  | vbinop__case_1 : forall (shape : shape) (Fnn : Fnn) (M : M) (var_x : vbinop_Fnn_M), 
    (shape == (.X (lanetype_Fnn Fnn) (. M))) ->
    wf_vbinop_ shape (.mk_vbinop__1 Fnn M var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:107.1-107.43 -/
opaque proj_vbinop__0 : forall (Jnn : Jnn) (M : M) (var_x : vbinop_), (Option vbinop_Jnn_M) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:107.1-107.43 -/
opaque proj_vbinop__1 : forall (Fnn : Fnn) (M : M) (var_x : vbinop_), (Option vbinop_Fnn_M) := opaqueDef

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
  | mk_vternop__0 (Jnn : Jnn) (M : M) (var_x : vternop_Jnn_M) : vternop_
  | mk_vternop__1 (Fnn : Fnn) (M : M) (var_x : vternop_Fnn_M) : vternop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:122.8-122.17 -/
inductive wf_vternop_ : shape -> vternop_ -> Prop where
  | vternop__case_0 : forall (shape : shape) (Jnn : Jnn) (M : M) (var_x : vternop_Jnn_M), 
    (shape == (.X (lanetype_Jnn Jnn) (. M))) ->
    wf_vternop_ shape (.mk_vternop__0 Jnn M var_x)
  | vternop__case_1 : forall (shape : shape) (Fnn : Fnn) (M : M) (var_x : vternop_Fnn_M), 
    (shape == (.X (lanetype_Fnn Fnn) (. M))) ->
    wf_vternop_ shape (.mk_vternop__1 Fnn M var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:122.1-122.44 -/
opaque proj_vternop__0 : forall (Jnn : Jnn) (M : M) (var_x : vternop_), (Option vternop_Jnn_M) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:122.1-122.44 -/
opaque proj_vternop__1 : forall (Fnn : Fnn) (M : M) (var_x : vternop_), (Option vternop_Fnn_M) := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:126.1-126.44 -/
inductive vtestop_Jnn_M : Type where
  | ALL_TRUE : vtestop_Jnn_M
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:126.1-126.44 -/
inductive vtestop_ : Type where
  | mk_vtestop__0 (Jnn : Jnn) (M : M) (var_x : vtestop_Jnn_M) : vtestop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:126.8-126.17 -/
inductive wf_vtestop_ : shape -> vtestop_ -> Prop where
  | vtestop__case_0 : forall (shape : shape) (Jnn : Jnn) (M : M) (var_x : vtestop_Jnn_M), 
    (shape == (.X (lanetype_Jnn Jnn) (. M))) ->
    wf_vtestop_ shape (.mk_vtestop__0 Jnn M var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:126.1-126.44 -/
opaque proj_vtestop__0 : forall (Jnn : Jnn) (M : M) (var_x : vtestop_), vtestop_Jnn_M := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:130.1-130.43 -/
inductive vrelop_Jnn_M : Type where
  | EQ : vrelop_Jnn_M
  | NE : vrelop_Jnn_M
  | LT (sx : sx) : vrelop_Jnn_M
  | GT (sx : sx) : vrelop_Jnn_M
  | LE (sx : sx) : vrelop_Jnn_M
  | GE (sx : sx) : vrelop_Jnn_M
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:130.8-130.16 -/
inductive wf_vrelop_Jnn_M : Jnn -> M -> vrelop_Jnn_M -> Prop where
  | vrelop_Jnn_M_case_0 : forall (Jnn : Jnn) (M : M), wf_vrelop_Jnn_M Jnn M .EQ
  | vrelop_Jnn_M_case_1 : forall (Jnn : Jnn) (M : M), wf_vrelop_Jnn_M Jnn M .NE
  | vrelop_Jnn_M_case_2 : forall (Jnn : Jnn) (M : M) (sx : sx), 
    (((lsizenn (lanetype_Jnn Jnn)) != 64) || (sx == .S)) ->
    wf_vrelop_Jnn_M Jnn M (.LT sx)
  | vrelop_Jnn_M_case_3 : forall (Jnn : Jnn) (M : M) (sx : sx), 
    (((lsizenn (lanetype_Jnn Jnn)) != 64) || (sx == .S)) ->
    wf_vrelop_Jnn_M Jnn M (.GT sx)
  | vrelop_Jnn_M_case_4 : forall (Jnn : Jnn) (M : M) (sx : sx), 
    (((lsizenn (lanetype_Jnn Jnn)) != 64) || (sx == .S)) ->
    wf_vrelop_Jnn_M Jnn M (.LE sx)
  | vrelop_Jnn_M_case_5 : forall (Jnn : Jnn) (M : M) (sx : sx), 
    (((lsizenn (lanetype_Jnn Jnn)) != 64) || (sx == .S)) ->
    wf_vrelop_Jnn_M Jnn M (.GE sx)

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
  | mk_vrelop__0 (Jnn : Jnn) (M : M) (var_x : vrelop_Jnn_M) : vrelop_
  | mk_vrelop__1 (Fnn : Fnn) (M : M) (var_x : vrelop_Fnn_M) : vrelop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:130.8-130.16 -/
inductive wf_vrelop_ : shape -> vrelop_ -> Prop where
  | vrelop__case_0 : forall (shape : shape) (Jnn : Jnn) (M : M) (var_x : vrelop_Jnn_M), 
    (wf_vrelop_Jnn_M Jnn M var_x) ->
    (shape == (.X (lanetype_Jnn Jnn) (. M))) ->
    wf_vrelop_ shape (.mk_vrelop__0 Jnn M var_x)
  | vrelop__case_1 : forall (shape : shape) (Fnn : Fnn) (M : M) (var_x : vrelop_Fnn_M), 
    (shape == (.X (lanetype_Fnn Fnn) (. M))) ->
    wf_vrelop_ shape (.mk_vrelop__1 Fnn M var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:130.1-130.43 -/
opaque proj_vrelop__0 : forall (Jnn : Jnn) (M : M) (var_x : vrelop_), (Option vrelop_Jnn_M) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:130.1-130.43 -/
opaque proj_vrelop__1 : forall (Fnn : Fnn) (M : M) (var_x : vrelop_), (Option vrelop_Fnn_M) := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:138.1-138.46 -/
inductive vshiftop_Jnn_M : Type where
  | SHL : vshiftop_Jnn_M
  | SHR (sx : sx) : vshiftop_Jnn_M
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:138.1-138.46 -/
inductive vshiftop_ : Type where
  | mk_vshiftop__0 (Jnn : Jnn) (M : M) (var_x : vshiftop_Jnn_M) : vshiftop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:138.8-138.18 -/
inductive wf_vshiftop_ : ishape -> vshiftop_ -> Prop where
  | vshiftop__case_0 : forall (ishape : ishape) (Jnn : Jnn) (M : M) (var_x : vshiftop_Jnn_M), 
    (ishape == (. (.X (lanetype_Jnn Jnn) (. M)))) ->
    wf_vshiftop_ ishape (.mk_vshiftop__0 Jnn M var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:138.1-138.46 -/
opaque proj_vshiftop__0 : forall (Jnn : Jnn) (M : M) (var_x : vshiftop_), vshiftop_Jnn_M := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:141.1-141.47 -/
inductive vswizzlop_M : Type where
  | SWIZZLE : vswizzlop_M
  | RELAXED_SWIZZLE : vswizzlop_M
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:141.1-141.47 -/
inductive vswizzlop_ : Type where
  | mk_vswizzlop__0 (M : M) (var_x : vswizzlop_M) : vswizzlop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:141.8-141.19 -/
inductive wf_vswizzlop_ : bshape -> vswizzlop_ -> Prop where
  | vswizzlop__case_0 : forall (bshape : bshape) (M : M) (var_x : vswizzlop_M), 
    (bshape == (. (.X .I8 (. M)))) ->
    wf_vswizzlop_ bshape (.mk_vswizzlop__0 M var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:141.1-141.47 -/
opaque proj_vswizzlop__0 : forall (M : M) (var_x : vswizzlop_), vswizzlop_M := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:144.1-144.59 -/
inductive vextunop__Jnn_1_M_1_Jnn_2_M_2 : Type where
  | EXTADD_PAIRWISE (sx : sx) : vextunop__Jnn_1_M_1_Jnn_2_M_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:144.8-144.19 -/
inductive wf_vextunop__Jnn_1_M_1_Jnn_2_M_2 : Jnn -> M -> Jnn -> M -> vextunop__Jnn_1_M_1_Jnn_2_M_2 -> Prop where
  | vextunop__Jnn_1_M_1_Jnn_2_M_2_case_0 : forall (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (sx : sx), 
    ((16 <= (2 * (lsizenn1 (lanetype_Jnn Jnn_1)))) && (((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) == (lsizenn2 (lanetype_Jnn Jnn_2))) && ((lsizenn2 (lanetype_Jnn Jnn_2)) <= 32))) ->
    wf_vextunop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 (.EXTADD_PAIRWISE sx)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:144.1-144.59 -/
inductive vextunop__ : Type where
  | mk_vextunop___0 (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vextunop__Jnn_1_M_1_Jnn_2_M_2) : vextunop__
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:144.8-144.19 -/
inductive wf_vextunop__ : ishape -> ishape -> vextunop__ -> Prop where
  | vextunop___case_0 : forall (ishape_1 : ishape) (ishape_2 : ishape) (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vextunop__Jnn_1_M_1_Jnn_2_M_2), 
    (wf_vextunop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 var_x) ->
    (ishape_1 == (. (.X (lanetype_Jnn Jnn_1) (. M_1)))) ->
    (ishape_2 == (. (.X (lanetype_Jnn Jnn_2) (. M_2)))) ->
    wf_vextunop__ ishape_1 ishape_2 (.mk_vextunop___0 Jnn_1 M_1 Jnn_2 M_2 var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:144.1-144.59 -/
opaque proj_vextunop___0 : forall (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vextunop__), vextunop__Jnn_1_M_1_Jnn_2_M_2 := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:149.1-149.60 -/
inductive vextbinop__Jnn_1_M_1_Jnn_2_M_2 : Type where
  | EXTMUL (half : half) (sx : sx) : vextbinop__Jnn_1_M_1_Jnn_2_M_2
  | DOTS : vextbinop__Jnn_1_M_1_Jnn_2_M_2
  | RELAXED_DOTS : vextbinop__Jnn_1_M_1_Jnn_2_M_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:149.8-149.20 -/
inductive wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 : Jnn -> M -> Jnn -> M -> vextbinop__Jnn_1_M_1_Jnn_2_M_2 -> Prop where
  | vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_0 : forall (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (half : half) (sx : sx), 
    (((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) == (lsizenn2 (lanetype_Jnn Jnn_2))) && ((lsizenn2 (lanetype_Jnn Jnn_2)) >= 16)) ->
    wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 (.EXTMUL half sx)
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
    (ishape_1 == (. (.X (lanetype_Jnn Jnn_1) (. M_1)))) ->
    (ishape_2 == (. (.X (lanetype_Jnn Jnn_2) (. M_2)))) ->
    wf_vextbinop__ ishape_1 ishape_2 (.mk_vextbinop___0 Jnn_1 M_1 Jnn_2 M_2 var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:149.1-149.60 -/
opaque proj_vextbinop___0 : forall (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vextbinop__), vextbinop__Jnn_1_M_1_Jnn_2_M_2 := opaqueDef

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
    (ishape_1 == (. (.X (lanetype_Jnn Jnn_1) (. M_1)))) ->
    (ishape_2 == (. (.X (lanetype_Jnn Jnn_2) (. M_2)))) ->
    wf_vextternop__ ishape_1 ishape_2 (.mk_vextternop___0 Jnn_1 M_1 Jnn_2 M_2 var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:158.1-158.61 -/
opaque proj_vextternop___0 : forall (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vextternop__), vextternop__Jnn_1_M_1_Jnn_2_M_2 := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.1-163.55 -/
inductive vcvtop__Jnn_1_M_1_Jnn_2_M_2 : Type where
  | EXTEND (half : half) (sx : sx) : vcvtop__Jnn_1_M_1_Jnn_2_M_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.8-163.17 -/
inductive wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2 : Jnn -> M -> Jnn -> M -> vcvtop__Jnn_1_M_1_Jnn_2_M_2 -> Prop where
  | vcvtop__Jnn_1_M_1_Jnn_2_M_2_case_0 : forall (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (half : half) (sx : sx), 
    ((lsizenn2 (lanetype_Jnn Jnn_2)) == (2 * (lsizenn1 (lanetype_Jnn Jnn_1)))) ->
    wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 (.EXTEND half sx)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.1-163.55 -/
inductive vcvtop__Jnn_1_M_1_Fnn_2_M_2 : Type where
  | CONVERT ((Option.map (fun (half : half) => half) half?) : (Option half)) (sx : sx) : vcvtop__Jnn_1_M_1_Fnn_2_M_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.8-163.17 -/
inductive wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2 : Jnn -> M -> Fnn -> M -> vcvtop__Jnn_1_M_1_Fnn_2_M_2 -> Prop where
  | vcvtop__Jnn_1_M_1_Fnn_2_M_2_case_0 : forall (Jnn_1 : Jnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (half? : (Option half)) (sx : sx), 
    (((((sizenn2 (numtype_Fnn Fnn_2)) == (lsizenn1 (lanetype_Jnn Jnn_1))) && ((lsizenn1 (lanetype_Jnn Jnn_1)) == 32)) && ((Option.map (fun (half : half) => half) half?) == none)) || (((sizenn2 (numtype_Fnn Fnn_2)) == (2 * (lsizenn1 (lanetype_Jnn Jnn_1)))) && ((Option.map (fun (half : half) => half) half?) == (some .LOW)))) ->
    wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2 Jnn_1 M_1 Fnn_2 M_2 (.CONVERT (Option.map (fun (half : half) => half) half?) sx)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.1-163.55 -/
inductive vcvtop__Fnn_1_M_1_Jnn_2_M_2 : Type where
  | TRUNC_SAT (sx : sx) ((Option.map (fun (zero : zero) => zero) zero?) : (Option zero)) : vcvtop__Fnn_1_M_1_Jnn_2_M_2
  | RELAXED_TRUNC (sx : sx) ((Option.map (fun (zero : zero) => zero) zero?) : (Option zero)) : vcvtop__Fnn_1_M_1_Jnn_2_M_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.8-163.17 -/
inductive wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2 : Fnn -> M -> Jnn -> M -> vcvtop__Fnn_1_M_1_Jnn_2_M_2 -> Prop where
  | vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_0 : forall (Fnn_1 : Fnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (sx : sx) (zero? : (Option zero)), 
    (((((sizenn1 (numtype_Fnn Fnn_1)) == (lsizenn2 (lanetype_Jnn Jnn_2))) && ((lsizenn2 (lanetype_Jnn Jnn_2)) == 32)) && ((Option.map (fun (zero : zero) => zero) zero?) == none)) || (((sizenn1 (numtype_Fnn Fnn_1)) == (2 * (lsizenn2 (lanetype_Jnn Jnn_2)))) && ((Option.map (fun (zero : zero) => zero) zero?) == (some .ZERO)))) ->
    wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2 Fnn_1 M_1 Jnn_2 M_2 (.TRUNC_SAT sx (Option.map (fun (zero : zero) => zero) zero?))
  | vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_1 : forall (Fnn_1 : Fnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (sx : sx) (zero? : (Option zero)), 
    (((((sizenn1 (numtype_Fnn Fnn_1)) == (lsizenn2 (lanetype_Jnn Jnn_2))) && ((lsizenn2 (lanetype_Jnn Jnn_2)) == 32)) && ((Option.map (fun (zero : zero) => zero) zero?) == none)) || (((sizenn1 (numtype_Fnn Fnn_1)) == (2 * (lsizenn2 (lanetype_Jnn Jnn_2)))) && ((Option.map (fun (zero : zero) => zero) zero?) == (some .ZERO)))) ->
    wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2 Fnn_1 M_1 Jnn_2 M_2 (.RELAXED_TRUNC sx (Option.map (fun (zero : zero) => zero) zero?))

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.1-163.55 -/
inductive vcvtop__Fnn_1_M_1_Fnn_2_M_2 : Type where
  | DEMOTE (zero : zero) : vcvtop__Fnn_1_M_1_Fnn_2_M_2
  | PROMOTELOW : vcvtop__Fnn_1_M_1_Fnn_2_M_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.8-163.17 -/
inductive wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 : Fnn -> M -> Fnn -> M -> vcvtop__Fnn_1_M_1_Fnn_2_M_2 -> Prop where
  | vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0 : forall (Fnn_1 : Fnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (zero : zero), 
    ((sizenn1 (numtype_Fnn Fnn_1)) == (2 * (sizenn2 (numtype_Fnn Fnn_2)))) ->
    wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 Fnn_1 M_1 Fnn_2 M_2 (.DEMOTE zero)
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
    (shape_1 == (.X (lanetype_Jnn Jnn_1) (. M_1))) ->
    (shape_2 == (.X (lanetype_Jnn Jnn_2) (. M_2))) ->
    wf_vcvtop__ shape_1 shape_2 (.mk_vcvtop___0 Jnn_1 M_1 Jnn_2 M_2 var_x)
  | vcvtop___case_1 : forall (shape_1 : shape) (shape_2 : shape) (Jnn_1 : Jnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (var_x : vcvtop__Jnn_1_M_1_Fnn_2_M_2), 
    (wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2 Jnn_1 M_1 Fnn_2 M_2 var_x) ->
    (shape_1 == (.X (lanetype_Jnn Jnn_1) (. M_1))) ->
    (shape_2 == (.X (lanetype_Fnn Fnn_2) (. M_2))) ->
    wf_vcvtop__ shape_1 shape_2 (.mk_vcvtop___1 Jnn_1 M_1 Fnn_2 M_2 var_x)
  | vcvtop___case_2 : forall (shape_1 : shape) (shape_2 : shape) (Fnn_1 : Fnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vcvtop__Fnn_1_M_1_Jnn_2_M_2), 
    (wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2 Fnn_1 M_1 Jnn_2 M_2 var_x) ->
    (shape_1 == (.X (lanetype_Fnn Fnn_1) (. M_1))) ->
    (shape_2 == (.X (lanetype_Jnn Jnn_2) (. M_2))) ->
    wf_vcvtop__ shape_1 shape_2 (.mk_vcvtop___2 Fnn_1 M_1 Jnn_2 M_2 var_x)
  | vcvtop___case_3 : forall (shape_1 : shape) (shape_2 : shape) (Fnn_1 : Fnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (var_x : vcvtop__Fnn_1_M_1_Fnn_2_M_2), 
    (wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 Fnn_1 M_1 Fnn_2 M_2 var_x) ->
    (shape_1 == (.X (lanetype_Fnn Fnn_1) (. M_1))) ->
    (shape_2 == (.X (lanetype_Fnn Fnn_2) (. M_2))) ->
    wf_vcvtop__ shape_1 shape_2 (.mk_vcvtop___3 Fnn_1 M_1 Fnn_2 M_2 var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.1-163.55 -/
opaque proj_vcvtop___0 : forall (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vcvtop__), (Option vcvtop__Jnn_1_M_1_Jnn_2_M_2) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.1-163.55 -/
opaque proj_vcvtop___1 : forall (Jnn_1 : Jnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (var_x : vcvtop__), (Option vcvtop__Jnn_1_M_1_Fnn_2_M_2) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.1-163.55 -/
opaque proj_vcvtop___2 : forall (Fnn_1 : Fnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vcvtop__), (Option vcvtop__Fnn_1_M_1_Jnn_2_M_2) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.1-163.55 -/
opaque proj_vcvtop___3 : forall (Fnn_1 : Fnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (var_x : vcvtop__), (Option vcvtop__Fnn_1_M_1_Fnn_2_M_2) := opaqueDef

/- Record Creation Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:187.1-187.69 -/
structure memarg where MKmemarg ::
  ALIGN : u32
  OFFSET : u32
deriving Inhabited, BEq

def _append_memarg (arg1 arg2 : (memarg)) : memarg where
  ALIGN := arg1.ALIGN /- FIXME - Non-trivial append -/
  OFFSET := arg1.OFFSET /- FIXME - Non-trivial append -/
instance : Append memarg where
  append arg1 arg2 := _append_memarg arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:187.8-187.14 -/
inductive wf_memarg : memarg -> Prop where
  | memarg_case_ : forall (var_0 : u32) (var_1 : u32), 
    (wf_uN 32 var_0) ->
    (wf_uN 32 var_1) ->
    wf_memarg { ALIGN := var_0, OFFSET := var_1 }

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:191.1-191.24 -/
inductive loadop_Inn : Type where
  | _ (sz : sz) (sx : sx) : loadop_Inn
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:191.8-191.16 -/
inductive wf_loadop_Inn : Inn -> loadop_Inn -> Prop where
  | loadop_Inn_case_0 : forall (Inn : Inn) (sz : sz) (sx : sx), 
    (wf_sz sz) ->
    ((proj_sz_0 sz) < (sizenn (numtype_addrtype Inn))) ->
    wf_loadop_Inn Inn (._ sz sx)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:191.1-191.24 -/
inductive loadop_ : Type where
  | mk_loadop__0 (Inn : Inn) (var_x : loadop_Inn) : loadop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:191.8-191.16 -/
inductive wf_loadop_ : numtype -> loadop_ -> Prop where
  | loadop__case_0 : forall (numtype : numtype) (Inn : Inn) (var_x : loadop_Inn), 
    (wf_loadop_Inn Inn var_x) ->
    (numtype == (numtype_addrtype Inn)) ->
    wf_loadop_ numtype (.mk_loadop__0 Inn var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:191.1-191.24 -/
opaque proj_loadop__0 : forall (Inn : Inn) (var_x : loadop_), loadop_Inn := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:194.1-194.25 -/
inductive storeop_Inn : Type where
  |  (sz : sz) : storeop_Inn
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:194.8-194.17 -/
inductive wf_storeop_Inn : Inn -> storeop_Inn -> Prop where
  | storeop_Inn_case_0 : forall (Inn : Inn) (sz : sz), 
    (wf_sz sz) ->
    ((proj_sz_0 sz) < (sizenn (numtype_addrtype Inn))) ->
    wf_storeop_Inn Inn (. sz)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:194.1-194.25 -/
inductive storeop_ : Type where
  | mk_storeop__0 (Inn : Inn) (var_x : storeop_Inn) : storeop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:194.8-194.17 -/
inductive wf_storeop_ : numtype -> storeop_ -> Prop where
  | storeop__case_0 : forall (numtype : numtype) (Inn : Inn) (var_x : storeop_Inn), 
    (wf_storeop_Inn Inn var_x) ->
    (numtype == (numtype_addrtype Inn)) ->
    wf_storeop_ numtype (.mk_storeop__0 Inn var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:194.1-194.25 -/
opaque proj_storeop__0 : forall (Inn : Inn) (var_x : storeop_), storeop_Inn := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:197.1-200.59 -/
inductive vloadop_ : Type where
  | SHAPEX_ (sz : sz) (M : M) (sx : sx) : vloadop_
  | SPLAT (sz : sz) : vloadop_
  | ZERO (sz : sz) : vloadop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:197.8-197.17 -/
inductive wf_vloadop_ : vectype -> vloadop_ -> Prop where
  | vloadop__case_0 : forall (vectype : vectype) (sz : sz) (M : M) (sx : sx), 
    (wf_sz sz) ->
    ((((proj_sz_0 sz) * M) : Nat) == (((vsize vectype) : Nat) / (2 : Nat))) ->
    wf_vloadop_ vectype (.SHAPEX_ sz M sx)
  | vloadop__case_1 : forall (vectype : vectype) (sz : sz), 
    (wf_sz sz) ->
    wf_vloadop_ vectype (.SPLAT sz)
  | vloadop__case_2 : forall (vectype : vectype) (sz : sz), 
    (wf_sz sz) ->
    ((proj_sz_0 sz) >= 32) ->
    wf_vloadop_ vectype (.ZERO sz)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:205.1-207.17 -/
inductive blocktype : Type where
  | _RESULT ((Option.map (fun (valtype : valtype) => valtype) valtype?) : (Option valtype)) : blocktype
  | _IDX (funcidx : funcidx) : blocktype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:205.8-205.17 -/
inductive wf_blocktype : blocktype -> Prop where
  | blocktype_case_0 : forall (valtype? : (Option valtype)), 
    Forall (fun (valtype : valtype) => (wf_valtype valtype)) (Option.toList valtype?) ->
    wf_blocktype (._RESULT (Option.map (fun (valtype : valtype) => valtype) valtype?))
  | blocktype_case_1 : forall (funcidx : funcidx), 
    (wf_uN 32 funcidx) ->
    wf_blocktype (._IDX funcidx)

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
  | REF.I31_NUM (u31 : u31) : addrref
  | REF.STRUCT_ADDR (structaddr : structaddr) : addrref
  | REF.ARRAY_ADDR (arrayaddr : arrayaddr) : addrref
  | REF.FUNC_ADDR (funcaddr : funcaddr) : addrref
  | REF.EXN_ADDR (exnaddr : exnaddr) : addrref
  | REF.HOST_ADDR (hostaddr : hostaddr) : addrref
  | REF.EXTERN (addrref : addrref) : addrref
deriving Inhabited, BEq


/- Recursive Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:35.1-42.23 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:35.8-35.15 -/
inductive wf_addrref : addrref -> Prop where
  | addrref_case_0 : forall (u31 : u31), 
    (wf_uN 31 u31) ->
    wf_addrref (.REF.I31_NUM u31)
  | addrref_case_1 : forall (structaddr : structaddr), wf_addrref (.REF.STRUCT_ADDR structaddr)
  | addrref_case_2 : forall (arrayaddr : arrayaddr), wf_addrref (.REF.ARRAY_ADDR arrayaddr)
  | addrref_case_3 : forall (funcaddr : funcaddr), wf_addrref (.REF.FUNC_ADDR funcaddr)
  | addrref_case_4 : forall (exnaddr : exnaddr), wf_addrref (.REF.EXN_ADDR exnaddr)
  | addrref_case_5 : forall (hostaddr : hostaddr), wf_addrref (.REF.HOST_ADDR hostaddr)
  | addrref_case_6 : forall (addrref : addrref), wf_addrref (.REF.EXTERN addrref)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:255.1-259.27 -/
inductive «catch» : Type where
  | CATCH (tagidx : tagidx) (labelidx : labelidx) : «catch»
  | CATCH_REF (tagidx : tagidx) (labelidx : labelidx) : «catch»
  | CATCH_ALL (labelidx : labelidx) : «catch»
  | CATCH_ALL_REF (labelidx : labelidx) : «catch»
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:255.8-255.13 -/
inductive wf_catch : «catch» -> Prop where
  | catch_case_0 : forall (tagidx : tagidx) (labelidx : labelidx), 
    (wf_uN 32 tagidx) ->
    (wf_uN 32 labelidx) ->
    wf_catch (.CATCH tagidx labelidx)
  | catch_case_1 : forall (tagidx : tagidx) (labelidx : labelidx), 
    (wf_uN 32 tagidx) ->
    (wf_uN 32 labelidx) ->
    wf_catch (.CATCH_REF tagidx labelidx)
  | catch_case_2 : forall (labelidx : labelidx), 
    (wf_uN 32 labelidx) ->
    wf_catch (.CATCH_ALL labelidx)
  | catch_case_3 : forall (labelidx : labelidx), 
    (wf_uN 32 labelidx) ->
    wf_catch (.CATCH_ALL_REF labelidx)

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
  | TAG (tagaddr : tagaddr) : externaddr
  | GLOBAL (globaladdr : globaladdr) : externaddr
  | MEM (memaddr : memaddr) : externaddr
  | TABLE (tableaddr : tableaddr) : externaddr
  | FUNC (funcaddr : funcaddr) : externaddr
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
  | CONST (numtype : numtype) (num_ : num_) : val
  | VCONST (vectype : vectype) (vec_ : vec_) : val
  | REF.NULL (heaptype : heaptype) : val
  | REF.I31_NUM (u31 : u31) : val
  | REF.STRUCT_ADDR (structaddr : structaddr) : val
  | REF.ARRAY_ADDR (arrayaddr : arrayaddr) : val
  | REF.FUNC_ADDR (funcaddr : funcaddr) : val
  | REF.EXN_ADDR (exnaddr : exnaddr) : val
  | REF.HOST_ADDR (hostaddr : hostaddr) : val
  | REF.EXTERN (addrref : addrref) : val
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:48.8-48.11 -/
inductive wf_val : val -> Prop where
  | val_case_0 : forall (numtype : numtype) (num_ : num_), 
    (wf_num_ numtype num_) ->
    wf_val (.CONST numtype num_)
  | val_case_1 : forall (vectype : vectype) (vec_ : vec_), 
    (wf_uN (vsize vectype) vec_) ->
    wf_val (.VCONST vectype vec_)
  | val_case_2 : forall (heaptype : heaptype), 
    (wf_heaptype heaptype) ->
    wf_val (.REF.NULL heaptype)
  | val_case_3 : forall (u31 : u31), 
    (wf_uN 31 u31) ->
    wf_val (.REF.I31_NUM u31)
  | val_case_4 : forall (structaddr : structaddr), wf_val (.REF.STRUCT_ADDR structaddr)
  | val_case_5 : forall (arrayaddr : arrayaddr), wf_val (.REF.ARRAY_ADDR arrayaddr)
  | val_case_6 : forall (funcaddr : funcaddr), wf_val (.REF.FUNC_ADDR funcaddr)
  | val_case_7 : forall (exnaddr : exnaddr), wf_val (.REF.EXN_ADDR exnaddr)
  | val_case_8 : forall (hostaddr : hostaddr), wf_val (.REF.HOST_ADDR hostaddr)
  | val_case_9 : forall (addrref : addrref), 
    (wf_addrref addrref) ->
    wf_val (.REF.EXTERN addrref)

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
  | SELECT ((Option.map (fun (valtype* : (List valtype)) => (List.map (fun (valtype : valtype) => valtype) valtype*)) valtype*?) : (Option (List valtype))) : instr
  | BLOCK (blocktype : blocktype) ((List.map (fun (instr : instr) => instr) instr*) : (List instr)) : instr
  | LOOP (blocktype : blocktype) ((List.map (fun (instr : instr) => instr) instr*) : (List instr)) : instr
  | IFELSE (blocktype : blocktype) ((List.map (fun (instr : instr) => instr) instr*) : (List instr)) (_ : (List instr)) : instr
  | BR (labelidx : labelidx) : instr
  | BR_IF (labelidx : labelidx) : instr
  | BR_TABLE ((List.map (fun (labelidx : labelidx) => labelidx) labelidx*) : (List labelidx)) (_ : labelidx) : instr
  | BR_ON_NULL (labelidx : labelidx) : instr
  | BR_ON_NON_NULL (labelidx : labelidx) : instr
  | BR_ON_CAST (labelidx : labelidx) (reftype : reftype) (_ : reftype) : instr
  | BR_ON_CAST_FAIL (labelidx : labelidx) (reftype : reftype) (_ : reftype) : instr
  | CALL (funcidx : funcidx) : instr
  | CALL_REF (typeuse : typeuse) : instr
  | CALL_INDIRECT (tableidx : tableidx) (typeuse : typeuse) : instr
  | RETURN : instr
  | RETURN_CALL (funcidx : funcidx) : instr
  | RETURN_CALL_REF (typeuse : typeuse) : instr
  | RETURN_CALL_INDIRECT (tableidx : tableidx) (typeuse : typeuse) : instr
  | THROW (tagidx : tagidx) : instr
  | THROW_REF : instr
  | TRY_TABLE (blocktype : blocktype) (list : (list «catch»)) ((List.map (fun (instr : instr) => instr) instr*) : (List instr)) : instr
  | LOCAL.GET (localidx : localidx) : instr
  | LOCAL.SET (localidx : localidx) : instr
  | LOCAL.TEE (localidx : localidx) : instr
  | GLOBAL.GET (globalidx : globalidx) : instr
  | GLOBAL.SET (globalidx : globalidx) : instr
  | TABLE.GET (tableidx : tableidx) : instr
  | TABLE.SET (tableidx : tableidx) : instr
  | TABLE.SIZE (tableidx : tableidx) : instr
  | TABLE.GROW (tableidx : tableidx) : instr
  | TABLE.FILL (tableidx : tableidx) : instr
  | TABLE.COPY (tableidx : tableidx) (_ : tableidx) : instr
  | TABLE.INIT (tableidx : tableidx) (elemidx : elemidx) : instr
  | ELEM.DROP (elemidx : elemidx) : instr
  | LOAD (numtype : numtype) ((Option.map (fun (loadop_ : loadop_) => loadop_) loadop_?) : (Option loadop_)) (memidx : memidx) (memarg : memarg) : instr
  | STORE (numtype : numtype) ((Option.map (fun (storeop_ : storeop_) => storeop_) storeop_?) : (Option storeop_)) (memidx : memidx) (memarg : memarg) : instr
  | VLOAD (vectype : vectype) ((Option.map (fun (vloadop_ : vloadop_) => vloadop_) vloadop_?) : (Option vloadop_)) (memidx : memidx) (memarg : memarg) : instr
  | VLOAD_LANE (vectype : vectype) (sz : sz) (memidx : memidx) (memarg : memarg) (laneidx : laneidx) : instr
  | VSTORE (vectype : vectype) (memidx : memidx) (memarg : memarg) : instr
  | VSTORE_LANE (vectype : vectype) (sz : sz) (memidx : memidx) (memarg : memarg) (laneidx : laneidx) : instr
  | MEMORY.SIZE (memidx : memidx) : instr
  | MEMORY.GROW (memidx : memidx) : instr
  | MEMORY.FILL (memidx : memidx) : instr
  | MEMORY.COPY (memidx : memidx) (_ : memidx) : instr
  | MEMORY.INIT (memidx : memidx) (dataidx : dataidx) : instr
  | DATA.DROP (dataidx : dataidx) : instr
  | REF.NULL (heaptype : heaptype) : instr
  | REF.IS_NULL : instr
  | REF.AS_NON_NULL : instr
  | REF.EQ : instr
  | REF.TEST (reftype : reftype) : instr
  | REF.CAST (reftype : reftype) : instr
  | REF.FUNC (funcidx : funcidx) : instr
  | REF.I31 : instr
  | I31.GET (sx : sx) : instr
  | STRUCT.NEW (typeidx : typeidx) : instr
  | STRUCT.NEW_DEFAULT (typeidx : typeidx) : instr
  | STRUCT.GET ((Option.map (fun (sx : sx) => sx) sx?) : (Option sx)) (typeidx : typeidx) (u32 : u32) : instr
  | STRUCT.SET (typeidx : typeidx) (u32 : u32) : instr
  | ARRAY.NEW (typeidx : typeidx) : instr
  | ARRAY.NEW_DEFAULT (typeidx : typeidx) : instr
  | ARRAY.NEW_FIXED (typeidx : typeidx) (u32 : u32) : instr
  | ARRAY.NEW_DATA (typeidx : typeidx) (dataidx : dataidx) : instr
  | ARRAY.NEW_ELEM (typeidx : typeidx) (elemidx : elemidx) : instr
  | ARRAY.GET ((Option.map (fun (sx : sx) => sx) sx?) : (Option sx)) (typeidx : typeidx) : instr
  | ARRAY.SET (typeidx : typeidx) : instr
  | ARRAY.LEN : instr
  | ARRAY.FILL (typeidx : typeidx) : instr
  | ARRAY.COPY (typeidx : typeidx) (_ : typeidx) : instr
  | ARRAY.INIT_DATA (typeidx : typeidx) (dataidx : dataidx) : instr
  | ARRAY.INIT_ELEM (typeidx : typeidx) (elemidx : elemidx) : instr
  | EXTERN.CONVERT_ANY : instr
  | ANY.CONVERT_EXTERN : instr
  | CONST (numtype : numtype) (num_ : num_) : instr
  | UNOP (numtype : numtype) (unop_ : unop_) : instr
  | BINOP (numtype : numtype) (binop_ : binop_) : instr
  | TESTOP (numtype : numtype) (testop_ : testop_) : instr
  | RELOP (numtype : numtype) (relop_ : relop_) : instr
  | CVTOP (numtype_1 : numtype) (numtype_2 : numtype) (cvtop__ : cvtop__) : instr
  | VCONST (vectype : vectype) (vec_ : vec_) : instr
  | VVUNOP (vectype : vectype) (vvunop : vvunop) : instr
  | VVBINOP (vectype : vectype) (vvbinop : vvbinop) : instr
  | VVTERNOP (vectype : vectype) (vvternop : vvternop) : instr
  | VVTESTOP (vectype : vectype) (vvtestop : vvtestop) : instr
  | VUNOP (shape : shape) (vunop_ : vunop_) : instr
  | VBINOP (shape : shape) (vbinop_ : vbinop_) : instr
  | VTERNOP (shape : shape) (vternop_ : vternop_) : instr
  | VTESTOP (shape : shape) (vtestop_ : vtestop_) : instr
  | VRELOP (shape : shape) (vrelop_ : vrelop_) : instr
  | VSHIFTOP (ishape : ishape) (vshiftop_ : vshiftop_) : instr
  | VBITMASK (ishape : ishape) : instr
  | VSWIZZLOP (bshape : bshape) (vswizzlop_ : vswizzlop_) : instr
  | VSHUFFLE (bshape : bshape) ((List.map (fun (laneidx : laneidx) => laneidx) laneidx*) : (List laneidx)) : instr
  | VEXTUNOP (ishape_1 : ishape) (ishape_2 : ishape) (vextunop__ : vextunop__) : instr
  | VEXTBINOP (ishape_1 : ishape) (ishape_2 : ishape) (vextbinop__ : vextbinop__) : instr
  | VEXTTERNOP (ishape_1 : ishape) (ishape_2 : ishape) (vextternop__ : vextternop__) : instr
  | VNARROW (ishape_1 : ishape) (ishape_2 : ishape) (sx : sx) : instr
  | VCVTOP (shape_1 : shape) (shape_2 : shape) (vcvtop__ : vcvtop__) : instr
  | VSPLAT (shape : shape) : instr
  | VEXTRACT_LANE (shape : shape) ((Option.map (fun (sx : sx) => sx) sx?) : (Option sx)) (laneidx : laneidx) : instr
  | VREPLACE_LANE (shape : shape) (laneidx : laneidx) : instr
  | REF.I31_NUM (u31 : u31) : instr
  | REF.STRUCT_ADDR (structaddr : structaddr) : instr
  | REF.ARRAY_ADDR (arrayaddr : arrayaddr) : instr
  | REF.FUNC_ADDR (funcaddr : funcaddr) : instr
  | REF.EXN_ADDR (exnaddr : exnaddr) : instr
  | REF.HOST_ADDR (hostaddr : hostaddr) : instr
  | REF.EXTERN (addrref : addrref) : instr
  | LABEL_ (n : n) ((List.map (fun (instr : instr) => instr) instr*) : (List instr)) (_ : (List instr)) : instr
  | FRAME_ (n : n) (frame : frame) ((List.map (fun (instr : instr) => instr) instr*) : (List instr)) : instr
  | HANDLER_ (n : n) ((List.map (fun (catch : «catch») => «catch») catch*) : (List «catch»)) ((List.map (fun (instr : instr) => instr) instr*) : (List instr)) : instr
  | TRAP : instr
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
opaque instr_addrref : forall (_ : addrref), instr := opaqueDef

/- Auxiliary Definition at:  -/
opaque instr_val : forall (_ : val), instr := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:136.1-142.9 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:136.8-136.13 -/
inductive wf_instr : instr -> Prop where
  | instr_case_0 : wf_instr .NOP
  | instr_case_1 : wf_instr .UNREACHABLE
  | instr_case_2 : wf_instr .DROP
  | instr_case_3 : forall (valtype*? : (Option (List valtype))), 
    Forall (fun (valtype* : (List valtype)) => Forall (fun (valtype : valtype) => (wf_valtype valtype)) valtype*) (Option.toList valtype*?) ->
    wf_instr (.SELECT (Option.map (fun (valtype* : (List valtype)) => (List.map (fun (valtype : valtype) => valtype) valtype*)) valtype*?))
  | instr_case_4 : forall (blocktype : blocktype) (instr* : (List instr)), 
    (wf_blocktype blocktype) ->
    Forall (fun (instr : instr) => (wf_instr instr)) instr* ->
    wf_instr (.BLOCK blocktype (List.map (fun (instr : instr) => instr) instr*))
  | instr_case_5 : forall (blocktype : blocktype) (instr* : (List instr)), 
    (wf_blocktype blocktype) ->
    Forall (fun (instr : instr) => (wf_instr instr)) instr* ->
    wf_instr (.LOOP blocktype (List.map (fun (instr : instr) => instr) instr*))
  | instr_case_6 : forall (blocktype : blocktype) (instr* : (List instr)) (var_0 : (List instr)), 
    (wf_blocktype blocktype) ->
    Forall (fun (instr : instr) => (wf_instr instr)) instr* ->
    Forall (fun (var_0 : instr) => (wf_instr var_0)) var_0 ->
    wf_instr (.IFELSE blocktype (List.map (fun (instr : instr) => instr) instr*) var_0)
  | instr_case_7 : forall (labelidx : labelidx), 
    (wf_uN 32 labelidx) ->
    wf_instr (.BR labelidx)
  | instr_case_8 : forall (labelidx : labelidx), 
    (wf_uN 32 labelidx) ->
    wf_instr (.BR_IF labelidx)
  | instr_case_9 : forall (labelidx* : (List labelidx)) (var_0 : labelidx), 
    Forall (fun (labelidx : labelidx) => (wf_uN 32 labelidx)) labelidx* ->
    (wf_uN 32 var_0) ->
    wf_instr (.BR_TABLE (List.map (fun (labelidx : labelidx) => labelidx) labelidx*) var_0)
  | instr_case_10 : forall (labelidx : labelidx), 
    (wf_uN 32 labelidx) ->
    wf_instr (.BR_ON_NULL labelidx)
  | instr_case_11 : forall (labelidx : labelidx), 
    (wf_uN 32 labelidx) ->
    wf_instr (.BR_ON_NON_NULL labelidx)
  | instr_case_12 : forall (labelidx : labelidx) (reftype : reftype) (var_0 : reftype), 
    (wf_uN 32 labelidx) ->
    (wf_reftype reftype) ->
    (wf_reftype var_0) ->
    wf_instr (.BR_ON_CAST labelidx reftype var_0)
  | instr_case_13 : forall (labelidx : labelidx) (reftype : reftype) (var_0 : reftype), 
    (wf_uN 32 labelidx) ->
    (wf_reftype reftype) ->
    (wf_reftype var_0) ->
    wf_instr (.BR_ON_CAST_FAIL labelidx reftype var_0)
  | instr_case_14 : forall (funcidx : funcidx), 
    (wf_uN 32 funcidx) ->
    wf_instr (.CALL funcidx)
  | instr_case_15 : forall (typeuse : typeuse), 
    (wf_typeuse typeuse) ->
    wf_instr (.CALL_REF typeuse)
  | instr_case_16 : forall (tableidx : tableidx) (typeuse : typeuse), 
    (wf_uN 32 tableidx) ->
    (wf_typeuse typeuse) ->
    wf_instr (.CALL_INDIRECT tableidx typeuse)
  | instr_case_17 : wf_instr .RETURN
  | instr_case_18 : forall (funcidx : funcidx), 
    (wf_uN 32 funcidx) ->
    wf_instr (.RETURN_CALL funcidx)
  | instr_case_19 : forall (typeuse : typeuse), 
    (wf_typeuse typeuse) ->
    wf_instr (.RETURN_CALL_REF typeuse)
  | instr_case_20 : forall (tableidx : tableidx) (typeuse : typeuse), 
    (wf_uN 32 tableidx) ->
    (wf_typeuse typeuse) ->
    wf_instr (.RETURN_CALL_INDIRECT tableidx typeuse)
  | instr_case_21 : forall (tagidx : tagidx), 
    (wf_uN 32 tagidx) ->
    wf_instr (.THROW tagidx)
  | instr_case_22 : wf_instr .THROW_REF
  | instr_case_23 : forall (blocktype : blocktype) (list : (list «catch»)) (instr* : (List instr)), 
    (wf_blocktype blocktype) ->
    Forall (fun (instr : instr) => (wf_instr instr)) instr* ->
    wf_instr (.TRY_TABLE blocktype list (List.map (fun (instr : instr) => instr) instr*))
  | instr_case_24 : forall (localidx : localidx), 
    (wf_uN 32 localidx) ->
    wf_instr (.LOCAL.GET localidx)
  | instr_case_25 : forall (localidx : localidx), 
    (wf_uN 32 localidx) ->
    wf_instr (.LOCAL.SET localidx)
  | instr_case_26 : forall (localidx : localidx), 
    (wf_uN 32 localidx) ->
    wf_instr (.LOCAL.TEE localidx)
  | instr_case_27 : forall (globalidx : globalidx), 
    (wf_uN 32 globalidx) ->
    wf_instr (.GLOBAL.GET globalidx)
  | instr_case_28 : forall (globalidx : globalidx), 
    (wf_uN 32 globalidx) ->
    wf_instr (.GLOBAL.SET globalidx)
  | instr_case_29 : forall (tableidx : tableidx), 
    (wf_uN 32 tableidx) ->
    wf_instr (.TABLE.GET tableidx)
  | instr_case_30 : forall (tableidx : tableidx), 
    (wf_uN 32 tableidx) ->
    wf_instr (.TABLE.SET tableidx)
  | instr_case_31 : forall (tableidx : tableidx), 
    (wf_uN 32 tableidx) ->
    wf_instr (.TABLE.SIZE tableidx)
  | instr_case_32 : forall (tableidx : tableidx), 
    (wf_uN 32 tableidx) ->
    wf_instr (.TABLE.GROW tableidx)
  | instr_case_33 : forall (tableidx : tableidx), 
    (wf_uN 32 tableidx) ->
    wf_instr (.TABLE.FILL tableidx)
  | instr_case_34 : forall (tableidx : tableidx) (var_0 : tableidx), 
    (wf_uN 32 tableidx) ->
    (wf_uN 32 var_0) ->
    wf_instr (.TABLE.COPY tableidx var_0)
  | instr_case_35 : forall (tableidx : tableidx) (elemidx : elemidx), 
    (wf_uN 32 tableidx) ->
    (wf_uN 32 elemidx) ->
    wf_instr (.TABLE.INIT tableidx elemidx)
  | instr_case_36 : forall (elemidx : elemidx), 
    (wf_uN 32 elemidx) ->
    wf_instr (.ELEM.DROP elemidx)
  | instr_case_37 : forall (numtype : numtype) (loadop_? : (Option loadop_)) (memidx : memidx) (memarg : memarg), 
    Forall (fun (loadop_ : loadop_) => (wf_loadop_ numtype loadop_)) (Option.toList loadop_?) ->
    (wf_uN 32 memidx) ->
    (wf_memarg memarg) ->
    wf_instr (.LOAD numtype (Option.map (fun (loadop_ : loadop_) => loadop_) loadop_?) memidx memarg)
  | instr_case_38 : forall (numtype : numtype) (storeop_? : (Option storeop_)) (memidx : memidx) (memarg : memarg), 
    Forall (fun (storeop_ : storeop_) => (wf_storeop_ numtype storeop_)) (Option.toList storeop_?) ->
    (wf_uN 32 memidx) ->
    (wf_memarg memarg) ->
    wf_instr (.STORE numtype (Option.map (fun (storeop_ : storeop_) => storeop_) storeop_?) memidx memarg)
  | instr_case_39 : forall (vectype : vectype) (vloadop_? : (Option vloadop_)) (memidx : memidx) (memarg : memarg), 
    Forall (fun (vloadop_ : vloadop_) => (wf_vloadop_ vectype vloadop_)) (Option.toList vloadop_?) ->
    (wf_uN 32 memidx) ->
    (wf_memarg memarg) ->
    wf_instr (.VLOAD vectype (Option.map (fun (vloadop_ : vloadop_) => vloadop_) vloadop_?) memidx memarg)
  | instr_case_40 : forall (vectype : vectype) (sz : sz) (memidx : memidx) (memarg : memarg) (laneidx : laneidx), 
    (wf_sz sz) ->
    (wf_uN 32 memidx) ->
    (wf_memarg memarg) ->
    (wf_uN 8 laneidx) ->
    wf_instr (.VLOAD_LANE vectype sz memidx memarg laneidx)
  | instr_case_41 : forall (vectype : vectype) (memidx : memidx) (memarg : memarg), 
    (wf_uN 32 memidx) ->
    (wf_memarg memarg) ->
    wf_instr (.VSTORE vectype memidx memarg)
  | instr_case_42 : forall (vectype : vectype) (sz : sz) (memidx : memidx) (memarg : memarg) (laneidx : laneidx), 
    (wf_sz sz) ->
    (wf_uN 32 memidx) ->
    (wf_memarg memarg) ->
    (wf_uN 8 laneidx) ->
    wf_instr (.VSTORE_LANE vectype sz memidx memarg laneidx)
  | instr_case_43 : forall (memidx : memidx), 
    (wf_uN 32 memidx) ->
    wf_instr (.MEMORY.SIZE memidx)
  | instr_case_44 : forall (memidx : memidx), 
    (wf_uN 32 memidx) ->
    wf_instr (.MEMORY.GROW memidx)
  | instr_case_45 : forall (memidx : memidx), 
    (wf_uN 32 memidx) ->
    wf_instr (.MEMORY.FILL memidx)
  | instr_case_46 : forall (memidx : memidx) (var_0 : memidx), 
    (wf_uN 32 memidx) ->
    (wf_uN 32 var_0) ->
    wf_instr (.MEMORY.COPY memidx var_0)
  | instr_case_47 : forall (memidx : memidx) (dataidx : dataidx), 
    (wf_uN 32 memidx) ->
    (wf_uN 32 dataidx) ->
    wf_instr (.MEMORY.INIT memidx dataidx)
  | instr_case_48 : forall (dataidx : dataidx), 
    (wf_uN 32 dataidx) ->
    wf_instr (.DATA.DROP dataidx)
  | instr_case_49 : forall (heaptype : heaptype), 
    (wf_heaptype heaptype) ->
    wf_instr (.REF.NULL heaptype)
  | instr_case_50 : wf_instr .REF.IS_NULL
  | instr_case_51 : wf_instr .REF.AS_NON_NULL
  | instr_case_52 : wf_instr .REF.EQ
  | instr_case_53 : forall (reftype : reftype), 
    (wf_reftype reftype) ->
    wf_instr (.REF.TEST reftype)
  | instr_case_54 : forall (reftype : reftype), 
    (wf_reftype reftype) ->
    wf_instr (.REF.CAST reftype)
  | instr_case_55 : forall (funcidx : funcidx), 
    (wf_uN 32 funcidx) ->
    wf_instr (.REF.FUNC funcidx)
  | instr_case_56 : wf_instr .REF.I31
  | instr_case_57 : forall (sx : sx), wf_instr (.I31.GET sx)
  | instr_case_58 : forall (typeidx : typeidx), 
    (wf_uN 32 typeidx) ->
    wf_instr (.STRUCT.NEW typeidx)
  | instr_case_59 : forall (typeidx : typeidx), 
    (wf_uN 32 typeidx) ->
    wf_instr (.STRUCT.NEW_DEFAULT typeidx)
  | instr_case_60 : forall (sx? : (Option sx)) (typeidx : typeidx) (u32 : u32), 
    (wf_uN 32 typeidx) ->
    (wf_uN 32 u32) ->
    wf_instr (.STRUCT.GET (Option.map (fun (sx : sx) => sx) sx?) typeidx u32)
  | instr_case_61 : forall (typeidx : typeidx) (u32 : u32), 
    (wf_uN 32 typeidx) ->
    (wf_uN 32 u32) ->
    wf_instr (.STRUCT.SET typeidx u32)
  | instr_case_62 : forall (typeidx : typeidx), 
    (wf_uN 32 typeidx) ->
    wf_instr (.ARRAY.NEW typeidx)
  | instr_case_63 : forall (typeidx : typeidx), 
    (wf_uN 32 typeidx) ->
    wf_instr (.ARRAY.NEW_DEFAULT typeidx)
  | instr_case_64 : forall (typeidx : typeidx) (u32 : u32), 
    (wf_uN 32 typeidx) ->
    (wf_uN 32 u32) ->
    wf_instr (.ARRAY.NEW_FIXED typeidx u32)
  | instr_case_65 : forall (typeidx : typeidx) (dataidx : dataidx), 
    (wf_uN 32 typeidx) ->
    (wf_uN 32 dataidx) ->
    wf_instr (.ARRAY.NEW_DATA typeidx dataidx)
  | instr_case_66 : forall (typeidx : typeidx) (elemidx : elemidx), 
    (wf_uN 32 typeidx) ->
    (wf_uN 32 elemidx) ->
    wf_instr (.ARRAY.NEW_ELEM typeidx elemidx)
  | instr_case_67 : forall (sx? : (Option sx)) (typeidx : typeidx), 
    (wf_uN 32 typeidx) ->
    wf_instr (.ARRAY.GET (Option.map (fun (sx : sx) => sx) sx?) typeidx)
  | instr_case_68 : forall (typeidx : typeidx), 
    (wf_uN 32 typeidx) ->
    wf_instr (.ARRAY.SET typeidx)
  | instr_case_69 : wf_instr .ARRAY.LEN
  | instr_case_70 : forall (typeidx : typeidx), 
    (wf_uN 32 typeidx) ->
    wf_instr (.ARRAY.FILL typeidx)
  | instr_case_71 : forall (typeidx : typeidx) (var_0 : typeidx), 
    (wf_uN 32 typeidx) ->
    (wf_uN 32 var_0) ->
    wf_instr (.ARRAY.COPY typeidx var_0)
  | instr_case_72 : forall (typeidx : typeidx) (dataidx : dataidx), 
    (wf_uN 32 typeidx) ->
    (wf_uN 32 dataidx) ->
    wf_instr (.ARRAY.INIT_DATA typeidx dataidx)
  | instr_case_73 : forall (typeidx : typeidx) (elemidx : elemidx), 
    (wf_uN 32 typeidx) ->
    (wf_uN 32 elemidx) ->
    wf_instr (.ARRAY.INIT_ELEM typeidx elemidx)
  | instr_case_74 : wf_instr .EXTERN.CONVERT_ANY
  | instr_case_75 : wf_instr .ANY.CONVERT_EXTERN
  | instr_case_76 : forall (numtype : numtype) (num_ : num_), 
    (wf_num_ numtype num_) ->
    wf_instr (.CONST numtype num_)
  | instr_case_77 : forall (numtype : numtype) (unop_ : unop_), 
    (wf_unop_ numtype unop_) ->
    wf_instr (.UNOP numtype unop_)
  | instr_case_78 : forall (numtype : numtype) (binop_ : binop_), 
    (wf_binop_ numtype binop_) ->
    wf_instr (.BINOP numtype binop_)
  | instr_case_79 : forall (numtype : numtype) (testop_ : testop_), 
    (wf_testop_ numtype testop_) ->
    wf_instr (.TESTOP numtype testop_)
  | instr_case_80 : forall (numtype : numtype) (relop_ : relop_), 
    (wf_relop_ numtype relop_) ->
    wf_instr (.RELOP numtype relop_)
  | instr_case_81 : forall (numtype_1 : numtype) (numtype_2 : numtype) (cvtop__ : cvtop__), 
    (wf_cvtop__ numtype_2 numtype_1 cvtop__) ->
    wf_instr (.CVTOP numtype_1 numtype_2 cvtop__)
  | instr_case_82 : forall (vectype : vectype) (vec_ : vec_), 
    (wf_uN (vsize vectype) vec_) ->
    wf_instr (.VCONST vectype vec_)
  | instr_case_83 : forall (vectype : vectype) (vvunop : vvunop), wf_instr (.VVUNOP vectype vvunop)
  | instr_case_84 : forall (vectype : vectype) (vvbinop : vvbinop), wf_instr (.VVBINOP vectype vvbinop)
  | instr_case_85 : forall (vectype : vectype) (vvternop : vvternop), wf_instr (.VVTERNOP vectype vvternop)
  | instr_case_86 : forall (vectype : vectype) (vvtestop : vvtestop), wf_instr (.VVTESTOP vectype vvtestop)
  | instr_case_87 : forall (shape : shape) (vunop_ : vunop_), 
    (wf_shape shape) ->
    (wf_vunop_ shape vunop_) ->
    wf_instr (.VUNOP shape vunop_)
  | instr_case_88 : forall (shape : shape) (vbinop_ : vbinop_), 
    (wf_shape shape) ->
    (wf_vbinop_ shape vbinop_) ->
    wf_instr (.VBINOP shape vbinop_)
  | instr_case_89 : forall (shape : shape) (vternop_ : vternop_), 
    (wf_shape shape) ->
    (wf_vternop_ shape vternop_) ->
    wf_instr (.VTERNOP shape vternop_)
  | instr_case_90 : forall (shape : shape) (vtestop_ : vtestop_), 
    (wf_shape shape) ->
    (wf_vtestop_ shape vtestop_) ->
    wf_instr (.VTESTOP shape vtestop_)
  | instr_case_91 : forall (shape : shape) (vrelop_ : vrelop_), 
    (wf_shape shape) ->
    (wf_vrelop_ shape vrelop_) ->
    wf_instr (.VRELOP shape vrelop_)
  | instr_case_92 : forall (ishape : ishape) (vshiftop_ : vshiftop_), 
    (wf_ishape ishape) ->
    (wf_vshiftop_ ishape vshiftop_) ->
    wf_instr (.VSHIFTOP ishape vshiftop_)
  | instr_case_93 : forall (ishape : ishape), 
    (wf_ishape ishape) ->
    wf_instr (.VBITMASK ishape)
  | instr_case_94 : forall (bshape : bshape) (vswizzlop_ : vswizzlop_), 
    (wf_bshape bshape) ->
    (wf_vswizzlop_ bshape vswizzlop_) ->
    wf_instr (.VSWIZZLOP bshape vswizzlop_)
  | instr_case_95 : forall (bshape : bshape) (laneidx* : (List laneidx)), 
    (wf_bshape bshape) ->
    Forall (fun (laneidx : laneidx) => (wf_uN 8 laneidx)) laneidx* ->
    ((. (List.length (List.map (fun (laneidx : laneidx) => laneidx) laneidx*))) == (dim (proj_bshape_0 bshape))) ->
    wf_instr (.VSHUFFLE bshape (List.map (fun (laneidx : laneidx) => laneidx) laneidx*))
  | instr_case_96 : forall (ishape_1 : ishape) (ishape_2 : ishape) (vextunop__ : vextunop__), 
    (wf_ishape ishape_1) ->
    (wf_ishape ishape_2) ->
    (wf_vextunop__ ishape_2 ishape_1 vextunop__) ->
    wf_instr (.VEXTUNOP ishape_1 ishape_2 vextunop__)
  | instr_case_97 : forall (ishape_1 : ishape) (ishape_2 : ishape) (vextbinop__ : vextbinop__), 
    (wf_ishape ishape_1) ->
    (wf_ishape ishape_2) ->
    (wf_vextbinop__ ishape_2 ishape_1 vextbinop__) ->
    wf_instr (.VEXTBINOP ishape_1 ishape_2 vextbinop__)
  | instr_case_98 : forall (ishape_1 : ishape) (ishape_2 : ishape) (vextternop__ : vextternop__), 
    (wf_ishape ishape_1) ->
    (wf_ishape ishape_2) ->
    (wf_vextternop__ ishape_2 ishape_1 vextternop__) ->
    wf_instr (.VEXTTERNOP ishape_1 ishape_2 vextternop__)
  | instr_case_99 : forall (ishape_1 : ishape) (ishape_2 : ishape) (sx : sx), 
    (wf_ishape ishape_1) ->
    (wf_ishape ishape_2) ->
    (((lsize (lanetype (proj_ishape_0 ishape_2))) == (2 * (lsize (lanetype (proj_ishape_0 ishape_1))))) && ((2 * (lsize (lanetype (proj_ishape_0 ishape_1)))) <= 32)) ->
    wf_instr (.VNARROW ishape_1 ishape_2 sx)
  | instr_case_100 : forall (shape_1 : shape) (shape_2 : shape) (vcvtop__ : vcvtop__), 
    (wf_shape shape_1) ->
    (wf_shape shape_2) ->
    (wf_vcvtop__ shape_2 shape_1 vcvtop__) ->
    wf_instr (.VCVTOP shape_1 shape_2 vcvtop__)
  | instr_case_101 : forall (shape : shape), 
    (wf_shape shape) ->
    wf_instr (.VSPLAT shape)
  | instr_case_102 : forall (shape : shape) (sx? : (Option sx)) (laneidx : laneidx), 
    (wf_shape shape) ->
    (wf_uN 8 laneidx) ->
    (((Option.map (fun (sx : sx) => sx) sx?) == none) <-> (List.contains [.I32, .I64, .F32, .F64] (lanetype shape))) ->
    wf_instr (.VEXTRACT_LANE shape (Option.map (fun (sx : sx) => sx) sx?) laneidx)
  | instr_case_103 : forall (shape : shape) (laneidx : laneidx), 
    (wf_shape shape) ->
    (wf_uN 8 laneidx) ->
    wf_instr (.VREPLACE_LANE shape laneidx)
  | instr_case_104 : forall (u31 : u31), 
    (wf_uN 31 u31) ->
    wf_instr (.REF.I31_NUM u31)
  | instr_case_105 : forall (structaddr : structaddr), wf_instr (.REF.STRUCT_ADDR structaddr)
  | instr_case_106 : forall (arrayaddr : arrayaddr), wf_instr (.REF.ARRAY_ADDR arrayaddr)
  | instr_case_107 : forall (funcaddr : funcaddr), wf_instr (.REF.FUNC_ADDR funcaddr)
  | instr_case_108 : forall (exnaddr : exnaddr), wf_instr (.REF.EXN_ADDR exnaddr)
  | instr_case_109 : forall (hostaddr : hostaddr), wf_instr (.REF.HOST_ADDR hostaddr)
  | instr_case_110 : forall (addrref : addrref), 
    (wf_addrref addrref) ->
    wf_instr (.REF.EXTERN addrref)
  | instr_case_111 : forall (n : n) (instr* : (List instr)) (var_0 : (List instr)), 
    Forall (fun (instr : instr) => (wf_instr instr)) instr* ->
    Forall (fun (var_0 : instr) => (wf_instr var_0)) var_0 ->
    wf_instr (.LABEL_ n (List.map (fun (instr : instr) => instr) instr*) var_0)
  | instr_case_112 : forall (n : n) (frame : frame) (instr* : (List instr)), 
    (wf_frame frame) ->
    Forall (fun (instr : instr) => (wf_instr instr)) instr* ->
    wf_instr (.FRAME_ n frame (List.map (fun (instr : instr) => instr) instr*))
  | instr_case_113 : forall (n : n) (catch* : (List «catch»)) (instr* : (List instr)), 
    Forall (fun (catch : «catch») => (wf_catch «catch»)) catch* ->
    Forall (fun (instr : instr) => (wf_instr instr)) instr* ->
    wf_instr (.HANDLER_ n (List.map (fun (catch : «catch») => «catch») catch*) (List.map (fun (instr : instr) => instr) instr*))
  | instr_case_114 : wf_instr .TRAP

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:392.1-393.9 -/
abbrev expr : Type := (List instr)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:404.1-404.35 -/
def memarg0 : memarg := { ALIGN := (. 0), OFFSET := (. 0) }

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:407.1-407.69 -/
opaque const : forall (consttype : consttype) (lit_ : lit_), instr := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:414.1-414.30 -/
opaque free_shape : forall (shape : shape), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:415.1-415.38 -/
opaque free_blocktype : forall (blocktype : blocktype), free := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:572.1-572.44 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:572.1-572.44 -/
opaque shift_labelidxs : forall (_ : (List labelidx)), (List labelidx) := opaqueDef

/- Recursive Definitions at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:417.1-418.31 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:417.1-417.30 -/
opaque free_instr : forall (instr : instr), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:418.1-418.31 -/
opaque free_block : forall (_ : (List instr)), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:419.1-419.28 -/
opaque free_expr : forall (expr : expr), free := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:5.1-6.43 -/
inductive elemmode : Type where
  | ACTIVE (tableidx : tableidx) (expr : expr) : elemmode
  | PASSIVE : elemmode
  | DECLARE : elemmode
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:5.8-5.16 -/
inductive wf_elemmode : elemmode -> Prop where
  | elemmode_case_0 : forall (tableidx : tableidx) (expr : expr), 
    (wf_uN 32 tableidx) ->
    Forall (fun (expr : instr) => (wf_instr expr)) expr ->
    wf_elemmode (.ACTIVE tableidx expr)
  | elemmode_case_1 : wf_elemmode .PASSIVE
  | elemmode_case_2 : wf_elemmode .DECLARE

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:7.1-8.31 -/
inductive datamode : Type where
  | ACTIVE (memidx : memidx) (expr : expr) : datamode
  | PASSIVE : datamode
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:7.8-7.16 -/
inductive wf_datamode : datamode -> Prop where
  | datamode_case_0 : forall (memidx : memidx) (expr : expr), 
    (wf_uN 32 memidx) ->
    Forall (fun (expr : instr) => (wf_instr expr)) expr ->
    wf_datamode (.ACTIVE memidx expr)
  | datamode_case_1 : wf_datamode .PASSIVE

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:10.1-11.15 -/
inductive type : Type where
  | TYPE (rectype : rectype) : type
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:13.1-14.14 -/
inductive tag : Type where
  | TAG (tagtype : tagtype) : tag
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:13.8-13.11 -/
inductive wf_tag : tag -> Prop where
  | tag_case_0 : forall (tagtype : tagtype), 
    (wf_typeuse tagtype) ->
    wf_tag (.TAG tagtype)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:16.1-17.25 -/
inductive global : Type where
  | GLOBAL (globaltype : globaltype) (expr : expr) : global
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:16.8-16.14 -/
inductive wf_global : global -> Prop where
  | global_case_0 : forall (globaltype : globaltype) (expr : expr), 
    (wf_globaltype globaltype) ->
    Forall (fun (expr : instr) => (wf_instr expr)) expr ->
    wf_global (.GLOBAL globaltype expr)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:19.1-20.17 -/
inductive mem : Type where
  | MEMORY (memtype : memtype) : mem
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:19.8-19.11 -/
inductive wf_mem : mem -> Prop where
  | mem_case_0 : forall (memtype : memtype), 
    (wf_memtype memtype) ->
    wf_mem (.MEMORY memtype)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:22.1-23.23 -/
inductive table : Type where
  | TABLE (tabletype : tabletype) (expr : expr) : table
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:22.8-22.13 -/
inductive wf_table : table -> Prop where
  | table_case_0 : forall (tabletype : tabletype) (expr : expr), 
    (wf_tabletype tabletype) ->
    Forall (fun (expr : instr) => (wf_instr expr)) expr ->
    wf_table (.TABLE tabletype expr)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:25.1-26.22 -/
inductive data : Type where
  | DATA ((List.map (fun (byte : byte) => byte) byte*) : (List byte)) (datamode : datamode) : data
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:25.8-25.12 -/
inductive wf_data : data -> Prop where
  | data_case_0 : forall (byte* : (List byte)) (datamode : datamode), 
    Forall (fun (byte : byte) => (wf_byte byte)) byte* ->
    (wf_datamode datamode) ->
    wf_data (.DATA (List.map (fun (byte : byte) => byte) byte*) datamode)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:28.1-29.16 -/
inductive «local» : Type where
  | LOCAL (valtype : valtype) : «local»
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:28.8-28.13 -/
inductive wf_local : «local» -> Prop where
  | local_case_0 : forall (valtype : valtype), 
    (wf_valtype valtype) ->
    wf_local (.LOCAL valtype)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:31.1-32.27 -/
inductive func : Type where
  | FUNC (typeidx : typeidx) ((List.map (fun (local : «local») => «local») local*) : (List «local»)) (expr : expr) : func
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:31.8-31.12 -/
inductive wf_func : func -> Prop where
  | func_case_0 : forall (typeidx : typeidx) (local* : (List «local»)) (expr : expr), 
    (wf_uN 32 typeidx) ->
    Forall (fun (local : «local») => (wf_local «local»)) local* ->
    Forall (fun (expr : instr) => (wf_instr expr)) expr ->
    wf_func (.FUNC typeidx (List.map (fun (local : «local») => «local») local*) expr)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:34.1-35.30 -/
inductive elem : Type where
  | ELEM (reftype : reftype) ((List.map (fun (expr : expr) => expr) expr*) : (List expr)) (elemmode : elemmode) : elem
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:34.8-34.12 -/
inductive wf_elem : elem -> Prop where
  | elem_case_0 : forall (reftype : reftype) (expr* : (List expr)) (elemmode : elemmode), 
    (wf_reftype reftype) ->
    Forall (fun (expr : expr) => Forall (fun (expr : instr) => (wf_instr expr)) expr) expr* ->
    (wf_elemmode elemmode) ->
    wf_elem (.ELEM reftype (List.map (fun (expr : expr) => expr) expr*) elemmode)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:37.1-38.16 -/
inductive start : Type where
  | START (funcidx : funcidx) : start
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:37.8-37.13 -/
inductive wf_start : start -> Prop where
  | start_case_0 : forall (funcidx : funcidx), 
    (wf_uN 32 funcidx) ->
    wf_start (.START funcidx)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:40.1-41.30 -/
inductive «import» : Type where
  | IMPORT (name : name) (_ : name) (externtype : externtype) : «import»
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:40.8-40.14 -/
inductive wf_import : «import» -> Prop where
  | import_case_0 : forall (name : name) (externtype : externtype) (var_0 : name), 
    (wf_name name) ->
    (wf_externtype externtype) ->
    (wf_name var_0) ->
    wf_import (.IMPORT name var_0 externtype)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:43.1-44.24 -/
inductive «export» : Type where
  | EXPORT (name : name) (externidx : externidx) : «export»
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:43.8-43.14 -/
inductive wf_export : «export» -> Prop where
  | export_case_0 : forall (name : name) (externidx : externidx), 
    (wf_name name) ->
    (wf_externidx externidx) ->
    wf_export (.EXPORT name externidx)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:46.1-47.81 -/
inductive module : Type where
  | MODULE ((List.map (fun (type : type) => type) type*) : (List type)) ((List.map (fun (import : «import») => «import») import*) : (List «import»)) ((List.map (fun (tag : tag) => tag) tag*) : (List tag)) ((List.map (fun (global : global) => global) global*) : (List global)) ((List.map (fun (mem : mem) => mem) mem*) : (List mem)) ((List.map (fun (table : table) => table) table*) : (List table)) ((List.map (fun (func : func) => func) func*) : (List func)) ((List.map (fun (data : data) => data) data*) : (List data)) ((List.map (fun (elem : elem) => elem) elem*) : (List elem)) ((Option.map (fun (start : start) => start) start?) : (Option start)) ((List.map (fun (export : «export») => «export») export*) : (List «export»)) : module
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:46.8-46.14 -/
inductive wf_module : module -> Prop where
  | module_case_0 : forall (type* : (List type)) (import* : (List «import»)) (tag* : (List tag)) (global* : (List global)) (mem* : (List mem)) (table* : (List table)) (func* : (List func)) (data* : (List data)) (elem* : (List elem)) (start? : (Option start)) (export* : (List «export»)), 
    Forall (fun (import : «import») => (wf_import «import»)) import* ->
    Forall (fun (tag : tag) => (wf_tag tag)) tag* ->
    Forall (fun (global : global) => (wf_global global)) global* ->
    Forall (fun (mem : mem) => (wf_mem mem)) mem* ->
    Forall (fun (table : table) => (wf_table table)) table* ->
    Forall (fun (func : func) => (wf_func func)) func* ->
    Forall (fun (data : data) => (wf_data data)) data* ->
    Forall (fun (elem : elem) => (wf_elem elem)) elem* ->
    Forall (fun (start : start) => (wf_start start)) (Option.toList start?) ->
    Forall (fun (export : «export») => (wf_export «export»)) export* ->
    wf_module (.MODULE (List.map (fun (type : type) => type) type*) (List.map (fun (import : «import») => «import») import*) (List.map (fun (tag : tag) => tag) tag*) (List.map (fun (global : global) => global) global*) (List.map (fun (mem : mem) => mem) mem*) (List.map (fun (table : table) => table) table*) (List.map (fun (func : func) => func) func*) (List.map (fun (data : data) => data) data*) (List.map (fun (elem : elem) => elem) elem*) (Option.map (fun (start : start) => start) start?) (List.map (fun (export : «export») => «export») export*))

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:62.1-62.28 -/
opaque free_type : forall (type : type), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:63.1-63.26 -/
opaque free_tag : forall (tag : tag), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:64.1-64.32 -/
opaque free_global : forall (global : global), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:65.1-65.26 -/
opaque free_mem : forall (mem : mem), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:66.1-66.30 -/
opaque free_table : forall (table : table), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:67.1-67.30 -/
opaque free_local : forall (local : «local»), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:68.1-68.28 -/
opaque free_func : forall (func : func), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:71.1-71.36 -/
opaque free_datamode : forall (datamode : datamode), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:69.1-69.28 -/
opaque free_data : forall (data : data), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:72.1-72.36 -/
opaque free_elemmode : forall (elemmode : elemmode), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:70.1-70.28 -/
opaque free_elem : forall (elem : elem), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:73.1-73.30 -/
opaque free_start : forall (start : start), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:74.1-74.32 -/
opaque free_import : forall (import : «import»), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:75.1-75.32 -/
opaque free_export : forall (export : «export»), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:76.1-76.32 -/
opaque free_module : forall (module : module), free := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:130.1-130.89 -/
opaque funcidx_module : forall (module : module), (List funcidx) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:133.1-133.87 -/
opaque dataidx_funcs : forall (_ : (List func)), (List dataidx) := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:8.1-9.16 -/
inductive init : Type where
  | SET : init
  | UNSET : init
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:11.1-12.15 -/
inductive localtype : Type where
  |  (init : init) (valtype : valtype) : localtype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:11.8-11.17 -/
inductive wf_localtype : localtype -> Prop where
  | localtype_case_0 : forall (init : init) (valtype : valtype), 
    (wf_valtype valtype) ->
    wf_localtype (. init valtype)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:14.1-15.56 -/
inductive instrtype : Type where
  |  (resulttype : resulttype) ((List.map (fun (localidx : localidx) => localidx) localidx*) : (List localidx)) (_ : resulttype) : instrtype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:14.8-14.17 -/
inductive wf_instrtype : instrtype -> Prop where
  | instrtype_case_0 : forall (resulttype : resulttype) (localidx* : (List localidx)) (var_0 : resulttype), 
    Forall (fun (localidx : localidx) => (wf_uN 32 localidx)) localidx* ->
    wf_instrtype (. resulttype (List.map (fun (localidx : localidx) => localidx) localidx*) var_0)

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
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:46.1-46.144 -/
opaque with_locals : forall (context : context) (_ : (List localidx)) (_ : (List localtype)), context := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:59.1-59.94 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:59.1-59.94 -/
opaque clos_deftypes : forall (_ : (List deftype)), (List deftype) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:54.1-54.93 -/
opaque clos_valtype : forall (context : context) (valtype : valtype), valtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:55.1-55.93 -/
opaque clos_deftype : forall (context : context) (deftype : deftype), deftype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:56.1-56.93 -/
opaque clos_tagtype : forall (context : context) (tagtype : tagtype), tagtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:57.1-57.102 -/
opaque clos_externtype : forall (context : context) (externtype : externtype), externtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:58.1-58.102 -/
opaque clos_moduletype : forall (context : context) (moduletype : moduletype), moduletype := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:7.1-7.91 -/
inductive Numtype_ok : context -> numtype -> Prop where
  |  : forall (C : context) (numtype : numtype), 
    (wf_context C) ->
    Numtype_ok C numtype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:8.1-8.91 -/
inductive Vectype_ok : context -> vectype -> Prop where
  |  : forall (C : context) (vectype : vectype), 
    (wf_context C) ->
    Vectype_ok C vectype

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:79.1-80.85 -/
inductive oktypeidx : Type where
  | OK (typeidx : typeidx) : oktypeidx
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:79.8-79.17 -/
inductive wf_oktypeidx : oktypeidx -> Prop where
  | oktypeidx_case_0 : forall (typeidx : typeidx), 
    (wf_uN 32 typeidx) ->
    wf_oktypeidx (.OK typeidx)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:81.1-82.68 -/
inductive oktypeidxnat : Type where
  | OK (typeidx : typeidx) (nat : Nat) : oktypeidxnat
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:81.8-81.20 -/
inductive wf_oktypeidxnat : oktypeidxnat -> Prop where
  | oktypeidxnat_case_0 : forall (typeidx : typeidx) (nat : Nat), 
    (wf_uN 32 typeidx) ->
    wf_oktypeidxnat (.OK typeidx nat)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:84.1-84.103 -/
inductive Packtype_ok : context -> packtype -> Prop where
  |  : forall (C : context) (packtype : packtype), 
    (wf_context C) ->
    Packtype_ok C packtype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:133.1-133.116 -/
inductive Packtype_sub : context -> packtype -> packtype -> Prop where
  |  : forall (C : context) (packtype : packtype), 
    (wf_context C) ->
    Packtype_sub C packtype packtype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:7.1-7.103 -/
inductive Numtype_sub : context -> numtype -> numtype -> Prop where
  |  : forall (C : context) (numtype : numtype), 
    (wf_context C) ->
    Numtype_sub C numtype numtype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:65.1-66.70 -/
inductive Expand : deftype -> comptype -> Prop where
  |  : forall (deftype : deftype) (comptype : comptype), 
    (wf_comptype comptype) ->
    ((expanddt deftype) == comptype) ->
    Expand deftype comptype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:8.1-8.103 -/
inductive Vectype_sub : context -> vectype -> vectype -> Prop where
  |  : forall (C : context) (vectype : vectype), 
    (wf_context C) ->
    Vectype_sub C vectype vectype

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:151.1-151.85 -/
opaque before : forall (typeuse : typeuse) (typeidx : typeidx) (nat : Nat), Bool := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:156.1-156.69 -/
opaque unrollht : forall (context : context) (heaptype : heaptype), subtype := opaqueDef

/- Recursive Definitions at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:9.1-135.117 -/
mutual
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:9.1-9.92 -/
inductive Heaptype_ok : context -> heaptype -> Prop where
  | abs : forall (C : context) (absheaptype : absheaptype), 
    (wf_context C) ->
    Heaptype_ok C (heaptype_absheaptype absheaptype)
  | typeuse : forall (C : context) (typeuse : typeuse), 
    (wf_context C) ->
    (wf_typeuse typeuse) ->
    (Typeuse_ok C typeuse) ->
    Heaptype_ok C (heaptype_typeuse typeuse)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:10.1-10.91 -/
inductive Reftype_ok : context -> reftype -> Prop where
  |  : forall (C : context) (heaptype : heaptype), 
    (wf_context C) ->
    (wf_reftype (.REF (some .NULL) heaptype)) ->
    (Heaptype_ok C heaptype) ->
    Reftype_ok C (.REF (some .NULL) heaptype)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:11.1-11.91 -/
inductive Valtype_ok : context -> valtype -> Prop where
  | num : forall (C : context) (numtype : numtype), 
    (wf_context C) ->
    (Numtype_ok C numtype) ->
    Valtype_ok C (valtype_numtype numtype)
  | vec : forall (C : context) (vectype : vectype), 
    (wf_context C) ->
    (Vectype_ok C vectype) ->
    Valtype_ok C (valtype_vectype vectype)
  | ref : forall (C : context) (reftype : reftype), 
    (wf_context C) ->
    (wf_reftype reftype) ->
    (Reftype_ok C reftype) ->
    Valtype_ok C (valtype_reftype reftype)
  | bot : forall (C : context), 
    (wf_context C) ->
    (wf_valtype .BOT) ->
    Valtype_ok C .BOT

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:12.1-12.94 -/
inductive Typeuse_ok : context -> typeuse -> Prop where
  | typeidx : forall (C : context) (typeidx : typeidx) (dt : deftype), 
    (wf_context C) ->
    (wf_typeuse (._IDX typeidx)) ->
    ((proj_uN_0 typeidx) < (List.length (C.TYPES))) ->
    (((C.TYPES)[(proj_uN_0 typeidx)]!) == dt) ->
    Typeuse_ok C (._IDX typeidx)
  | rec : forall (C : context) (i : n) (st : subtype), 
    (wf_context C) ->
    (wf_subtype st) ->
    (wf_typeuse (.REC i)) ->
    (i < (List.length (C.RECS))) ->
    (((C.RECS)[i]!) == st) ->
    Typeuse_ok C (.REC i)
  | deftype : forall (C : context) (deftype : deftype), 
    (wf_context C) ->
    (Deftype_ok C deftype) ->
    Typeuse_ok C (typeuse_deftype deftype)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:49.1-49.100 -/
inductive Resulttype_ok : context -> resulttype -> Prop where
  |  : forall (C : context) (t* : (List valtype)), 
    (wf_context C) ->
    Forall (fun (t : valtype) => (wf_valtype t)) t* ->
    Forall (fun (t : valtype) => (Valtype_ok C t)) t* ->
    Resulttype_ok C (. (List.map (fun (t : valtype) => t) t*))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:85.1-85.104 -/
inductive Fieldtype_ok : context -> fieldtype -> Prop where
  |  : forall (C : context) (storagetype : storagetype), 
    (wf_context C) ->
    (wf_fieldtype (. (some .MUT) storagetype)) ->
    (Storagetype_ok C storagetype) ->
    Fieldtype_ok C (. (some .MUT) storagetype)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:86.1-86.106 -/
inductive Storagetype_ok : context -> storagetype -> Prop where
  | val : forall (C : context) (valtype : valtype), 
    (wf_context C) ->
    (wf_valtype valtype) ->
    (Valtype_ok C valtype) ->
    Storagetype_ok C (storagetype_valtype valtype)
  | pack : forall (C : context) (packtype : packtype), 
    (wf_context C) ->
    (Packtype_ok C packtype) ->
    Storagetype_ok C (storagetype_packtype packtype)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:87.1-87.103 -/
inductive Comptype_ok : context -> comptype -> Prop where
  | struct : forall (C : context) (fieldtype* : (List fieldtype)), 
    (wf_context C) ->
    (wf_comptype (.STRUCT (. (List.map (fun (fieldtype : fieldtype) => fieldtype) fieldtype*)))) ->
    Forall (fun (fieldtype : fieldtype) => (Fieldtype_ok C fieldtype)) fieldtype* ->
    Comptype_ok C (.STRUCT (. (List.map (fun (fieldtype : fieldtype) => fieldtype) fieldtype*)))
  | array : forall (C : context) (fieldtype : fieldtype), 
    (wf_context C) ->
    (wf_comptype (.ARRAY fieldtype)) ->
    (Fieldtype_ok C fieldtype) ->
    Comptype_ok C (.ARRAY fieldtype)
  | func : forall (C : context) (t_1* : (List valtype)) (t_2* : (List valtype)), 
    (wf_context C) ->
    (wf_comptype (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Resulttype_ok C (. (List.map (fun (t_1 : valtype) => t_1) t_1*))) ->
    (Resulttype_ok C (. (List.map (fun (t_2 : valtype) => t_2) t_2*))) ->
    Comptype_ok C (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:88.1-88.126 -/
inductive Subtype_ok : context -> subtype -> oktypeidx -> Prop where
  |  : forall (C : context) (x* : (List idx)) (comptype : comptype) (x_0 : idx) (x'** : (List (List idx))) (comptype'* : (List comptype)), 
    (wf_context C) ->
    (wf_subtype (.SUB (some .FINAL) (List.map (fun (x : idx) => (._IDX x)) x*) comptype)) ->
    (wf_oktypeidx (.OK x_0)) ->
    ((List.length comptype'*) == (List.length x'**)) ->
    Forall₂ (fun (comptype' : comptype) (x'* : (List typeidx)) => (wf_subtype (.SUB none (List.map (fun (x' : idx) => (._IDX x')) x'*) comptype'))) comptype'* x'** ->
    ((List.length (List.map (fun (x : idx) => x) x*)) <= 1) ->
    Forall (fun (x : idx) => ((proj_uN_0 x) < (proj_uN_0 x_0))) x* ->
    ((List.length comptype'*) == (List.length x*)) ->
    Forall (fun (x : idx) => ((proj_uN_0 x) < (List.length (C.TYPES)))) x* ->
    Forall₃ (fun (comptype' : comptype) (x : idx) (x'* : (List typeidx)) => ((unrolldt ((C.TYPES)[(proj_uN_0 x)]!)) == (.SUB none (List.map (fun (x' : idx) => (._IDX x')) x'*) comptype'))) comptype'* x* x'** ->
    (Comptype_ok C comptype) ->
    Forall (fun (comptype' : comptype) => (Comptype_sub C comptype comptype')) comptype'* ->
    Subtype_ok C (.SUB (some .FINAL) (List.map (fun (x : idx) => (._IDX x)) x*) comptype) (.OK x_0)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:89.1-89.126 -/
inductive Rectype_ok : context -> rectype -> oktypeidx -> Prop where
  | empty : forall (C : context) (x : idx), 
    (wf_context C) ->
    (wf_oktypeidx (.OK x)) ->
    Rectype_ok C (.REC (. [])) (.OK x)
  | cons : forall (C : context) (subtype_1 : subtype) (subtype* : (List subtype)) (x : idx), 
    (wf_context C) ->
    (wf_subtype subtype_1) ->
    Forall (fun (subtype : subtype) => (wf_subtype subtype)) subtype* ->
    (wf_oktypeidx (.OK x)) ->
    (wf_oktypeidx (.OK (. ((proj_uN_0 x) + 1)))) ->
    (Subtype_ok C subtype_1 (.OK x)) ->
    (Rectype_ok C (.REC (. (List.map (fun (subtype : subtype) => subtype) subtype*))) (.OK (. ((proj_uN_0 x) + 1)))) ->
    Rectype_ok C (.REC (. ([subtype_1] ++ (List.map (fun (subtype : subtype) => subtype) subtype*)))) (.OK x)
  | _rec2 : forall (C : context) (subtype* : (List subtype)) (x : idx), 
    (wf_context C) ->
    (wf_oktypeidx (.OK x)) ->
    (wf_context { TYPES := [], RECS := (List.map (fun (subtype : subtype) => subtype) subtype*), TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (wf_oktypeidxnat (.OK x 0)) ->
    (Rectype_ok2 ({ TYPES := [], RECS := (List.map (fun (subtype : subtype) => subtype) subtype*), TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } ++ C) (.REC (. (List.map (fun (subtype : subtype) => subtype) subtype*))) (.OK x 0)) ->
    Rectype_ok C (.REC (. (List.map (fun (subtype : subtype) => subtype) subtype*))) (.OK x)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:90.1-90.126 -/
inductive Subtype_ok2 : context -> subtype -> oktypeidxnat -> Prop where
  |  : forall (C : context) (typeuse* : (List typeuse)) (compttype : comptype) (x : idx) (i : Nat) (typeuse'** : (List (List typeuse))) (comptype'* : (List comptype)) (comptype : comptype), 
    (wf_context C) ->
    (wf_comptype comptype) ->
    (wf_subtype (.SUB (some .FINAL) (List.map (fun (typeuse : typeuse) => typeuse) typeuse*) compttype)) ->
    (wf_oktypeidxnat (.OK x i)) ->
    ((List.length comptype'*) == (List.length typeuse'**)) ->
    Forall₂ (fun (comptype' : comptype) (typeuse'* : (List typeuse)) => (wf_subtype (.SUB none (List.map (fun (typeuse' : typeuse) => typeuse') typeuse'*) comptype'))) comptype'* typeuse'** ->
    ((List.length (List.map (fun (typeuse : typeuse) => typeuse) typeuse*)) <= 1) ->
    Forall (fun (typeuse : typeuse) => (before typeuse x i)) typeuse* ->
    ((List.length comptype'*) == (List.length typeuse*)) ->
    Forall₃ (fun (comptype' : comptype) (typeuse : typeuse) (typeuse'* : (List typeuse)) => ((unrollht C (heaptype_typeuse typeuse)) == (.SUB none (List.map (fun (typeuse' : typeuse) => typeuse') typeuse'*) comptype'))) comptype'* typeuse* typeuse'** ->
    (Comptype_ok C comptype) ->
    Forall (fun (comptype' : comptype) => (Comptype_sub C comptype comptype')) comptype'* ->
    Subtype_ok2 C (.SUB (some .FINAL) (List.map (fun (typeuse : typeuse) => typeuse) typeuse*) compttype) (.OK x i)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:91.1-91.126 -/
inductive Rectype_ok2 : context -> rectype -> oktypeidxnat -> Prop where
  | empty : forall (C : context) (x : idx) (i : Nat), 
    (wf_context C) ->
    (wf_oktypeidxnat (.OK x i)) ->
    Rectype_ok2 C (.REC (. [])) (.OK x i)
  | cons : forall (C : context) (subtype_1 : subtype) (subtype* : (List subtype)) (x : idx) (i : Nat), 
    (wf_context C) ->
    (wf_subtype subtype_1) ->
    Forall (fun (subtype : subtype) => (wf_subtype subtype)) subtype* ->
    (wf_oktypeidxnat (.OK x i)) ->
    (wf_oktypeidxnat (.OK (. ((proj_uN_0 x) + 1)) (i + 1))) ->
    (Subtype_ok2 C subtype_1 (.OK x i)) ->
    (Rectype_ok2 C (.REC (. (List.map (fun (subtype : subtype) => subtype) subtype*))) (.OK (. ((proj_uN_0 x) + 1)) (i + 1))) ->
    Rectype_ok2 C (.REC (. ([subtype_1] ++ (List.map (fun (subtype : subtype) => subtype) subtype*)))) (.OK x i)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:92.1-92.102 -/
inductive Deftype_ok : context -> deftype -> Prop where
  |  : forall (C : context) (rectype : rectype) (i : n) (x : idx) (subtype* : (List subtype)) (n : n), 
    (wf_context C) ->
    Forall (fun (subtype : subtype) => (wf_subtype subtype)) subtype* ->
    (wf_oktypeidx (.OK x)) ->
    (Rectype_ok C rectype (.OK x)) ->
    ((List.length subtype*) == n) ->
    (rectype == (.REC (. (List.map (fun (subtype : subtype) => subtype) subtype*)))) ->
    (i < n) ->
    Deftype_ok C (._DEF rectype i)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:95.1-95.108 -/
inductive Comptype_sub : context -> comptype -> comptype -> Prop where
  | struct : forall (C : context) (ft_1* : (List fieldtype)) (ft'_1* : (List fieldtype)) (ft_2* : (List fieldtype)), 
    (wf_context C) ->
    (wf_comptype (.STRUCT (. ((List.map (fun (ft_1 : fieldtype) => ft_1) ft_1*) ++ (List.map (fun (ft'_1 : fieldtype) => ft'_1) ft'_1*))))) ->
    (wf_comptype (.STRUCT (. (List.map (fun (ft_2 : fieldtype) => ft_2) ft_2*)))) ->
    ((List.length ft_1*) == (List.length ft_2*)) ->
    Forall₂ (fun (ft_1 : fieldtype) (ft_2 : fieldtype) => (Fieldtype_sub C ft_1 ft_2)) ft_1* ft_2* ->
    Comptype_sub C (.STRUCT (. ((List.map (fun (ft_1 : fieldtype) => ft_1) ft_1*) ++ (List.map (fun (ft'_1 : fieldtype) => ft'_1) ft'_1*)))) (.STRUCT (. (List.map (fun (ft_2 : fieldtype) => ft_2) ft_2*)))
  | array : forall (C : context) (ft_1 : fieldtype) (ft_2 : fieldtype), 
    (wf_context C) ->
    (wf_comptype (.ARRAY ft_1)) ->
    (wf_comptype (.ARRAY ft_2)) ->
    (Fieldtype_sub C ft_1 ft_2) ->
    Comptype_sub C (.ARRAY ft_1) (.ARRAY ft_2)
  | func : forall (C : context) (t_11* : (List valtype)) (t_12* : (List valtype)) (t_21* : (List valtype)) (t_22* : (List valtype)), 
    (wf_context C) ->
    (wf_comptype (.FUNC (. (List.map (fun (t_11 : valtype) => t_11) t_11*)) (. (List.map (fun (t_12 : valtype) => t_12) t_12*)))) ->
    (wf_comptype (.FUNC (. (List.map (fun (t_21 : valtype) => t_21) t_21*)) (. (List.map (fun (t_22 : valtype) => t_22) t_22*)))) ->
    (Resulttype_sub C (. (List.map (fun (t_21 : valtype) => t_21) t_21*)) (. (List.map (fun (t_11 : valtype) => t_11) t_11*))) ->
    (Resulttype_sub C (. (List.map (fun (t_12 : valtype) => t_12) t_12*)) (. (List.map (fun (t_22 : valtype) => t_22) t_22*))) ->
    Comptype_sub C (.FUNC (. (List.map (fun (t_11 : valtype) => t_11) t_11*)) (. (List.map (fun (t_12 : valtype) => t_12) t_12*))) (.FUNC (. (List.map (fun (t_21 : valtype) => t_21) t_21*)) (. (List.map (fun (t_22 : valtype) => t_22) t_22*)))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:96.1-96.107 -/
inductive Deftype_sub : context -> deftype -> deftype -> Prop where
  | refl : forall (C : context) (deftype_1 : deftype) (deftype_2 : deftype), 
    (wf_context C) ->
    ((clos_deftype C deftype_1) == (clos_deftype C deftype_2)) ->
    Deftype_sub C deftype_1 deftype_2
  | super : forall (C : context) (deftype_1 : deftype) (deftype_2 : deftype) (final? : (Option final)) (typeuse* : (List typeuse)) (ct : comptype) (i : Nat), 
    (wf_context C) ->
    (wf_subtype (.SUB (Option.map (fun (final : final) => final) final?) (List.map (fun (typeuse : typeuse) => typeuse) typeuse*) ct)) ->
    ((unrolldt deftype_1) == (.SUB (Option.map (fun (final : final) => final) final?) (List.map (fun (typeuse : typeuse) => typeuse) typeuse*) ct)) ->
    (i < (List.length (List.map (fun (typeuse : typeuse) => typeuse) typeuse*))) ->
    (Heaptype_sub C (heaptype_typeuse ((List.map (fun (typeuse : typeuse) => typeuse) typeuse*)[i]!)) (heaptype_deftype deftype_2)) ->
    Deftype_sub C deftype_1 deftype_2

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:9.1-9.104 -/
inductive Heaptype_sub : context -> heaptype -> heaptype -> Prop where
  | refl : forall (C : context) (heaptype : heaptype), 
    (wf_context C) ->
    (wf_heaptype heaptype) ->
    Heaptype_sub C heaptype heaptype
  | trans : forall (C : context) (heaptype_1 : heaptype) (heaptype_2 : heaptype) (heaptype' : heaptype), 
    (wf_context C) ->
    (wf_heaptype heaptype_1) ->
    (wf_heaptype heaptype_2) ->
    (wf_heaptype heaptype') ->
    (Heaptype_ok C heaptype') ->
    (Heaptype_sub C heaptype_1 heaptype') ->
    (Heaptype_sub C heaptype' heaptype_2) ->
    Heaptype_sub C heaptype_1 heaptype_2
  | eq-any : forall (C : context), 
    (wf_context C) ->
    (wf_heaptype .EQ) ->
    (wf_heaptype .ANY) ->
    Heaptype_sub C .EQ .ANY
  | i31-eq : forall (C : context), 
    (wf_context C) ->
    (wf_heaptype .I31) ->
    (wf_heaptype .EQ) ->
    Heaptype_sub C .I31 .EQ
  | struct-eq : forall (C : context), 
    (wf_context C) ->
    (wf_heaptype .STRUCT) ->
    (wf_heaptype .EQ) ->
    Heaptype_sub C .STRUCT .EQ
  | array-eq : forall (C : context), 
    (wf_context C) ->
    (wf_heaptype .ARRAY) ->
    (wf_heaptype .EQ) ->
    Heaptype_sub C .ARRAY .EQ
  | struct : forall (C : context) (deftype : deftype) (fieldtype* : (List fieldtype)), 
    (wf_context C) ->
    (wf_heaptype .STRUCT) ->
    (wf_comptype (.STRUCT (. (List.map (fun (fieldtype : fieldtype) => fieldtype) fieldtype*)))) ->
    (Expand deftype (.STRUCT (. (List.map (fun (fieldtype : fieldtype) => fieldtype) fieldtype*)))) ->
    Heaptype_sub C (heaptype_deftype deftype) .STRUCT
  | array : forall (C : context) (deftype : deftype) (fieldtype : fieldtype), 
    (wf_context C) ->
    (wf_heaptype .ARRAY) ->
    (wf_comptype (.ARRAY fieldtype)) ->
    (Expand deftype (.ARRAY fieldtype)) ->
    Heaptype_sub C (heaptype_deftype deftype) .ARRAY
  | func : forall (C : context) (deftype : deftype) (t_1* : (List valtype)) (t_2* : (List valtype)), 
    (wf_context C) ->
    (wf_heaptype .FUNC) ->
    (wf_comptype (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Expand deftype (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Heaptype_sub C (heaptype_deftype deftype) .FUNC
  | def : forall (C : context) (deftype_1 : deftype) (deftype_2 : deftype), 
    (wf_context C) ->
    (Deftype_sub C deftype_1 deftype_2) ->
    Heaptype_sub C (heaptype_deftype deftype_1) (heaptype_deftype deftype_2)
  | typeidx-l : forall (C : context) (typeidx : typeidx) (heaptype : heaptype), 
    (wf_context C) ->
    (wf_heaptype heaptype) ->
    (wf_heaptype (._IDX typeidx)) ->
    ((proj_uN_0 typeidx) < (List.length (C.TYPES))) ->
    (Heaptype_sub C (heaptype_deftype ((C.TYPES)[(proj_uN_0 typeidx)]!)) heaptype) ->
    Heaptype_sub C (._IDX typeidx) heaptype
  | typeidx-r : forall (C : context) (heaptype : heaptype) (typeidx : typeidx), 
    (wf_context C) ->
    (wf_heaptype heaptype) ->
    (wf_heaptype (._IDX typeidx)) ->
    ((proj_uN_0 typeidx) < (List.length (C.TYPES))) ->
    (Heaptype_sub C heaptype (heaptype_deftype ((C.TYPES)[(proj_uN_0 typeidx)]!))) ->
    Heaptype_sub C heaptype (._IDX typeidx)
  | rec : forall (C : context) (i : n) (typeuse* : (List typeuse)) (j : Nat) (final? : (Option final)) (ct : comptype), 
    (j < (List.length (List.map (fun (typeuse : typeuse) => typeuse) typeuse*))) ->
    (wf_context C) ->
    (wf_heaptype (.REC i)) ->
    (wf_subtype (.SUB (Option.map (fun (final : final) => final) final?) (List.map (fun (typeuse : typeuse) => typeuse) typeuse*) ct)) ->
    (i < (List.length (C.RECS))) ->
    (((C.RECS)[i]!) == (.SUB (Option.map (fun (final : final) => final) final?) (List.map (fun (typeuse : typeuse) => typeuse) typeuse*) ct)) ->
    Heaptype_sub C (.REC i) (heaptype_typeuse ((List.map (fun (typeuse : typeuse) => typeuse) typeuse*)[j]!))
  | none : forall (C : context) (heaptype : heaptype), 
    (wf_context C) ->
    (wf_heaptype heaptype) ->
    (wf_heaptype .NONE) ->
    (wf_heaptype .ANY) ->
    (Heaptype_sub C heaptype .ANY) ->
    Heaptype_sub C .NONE heaptype
  | nofunc : forall (C : context) (heaptype : heaptype), 
    (wf_context C) ->
    (wf_heaptype heaptype) ->
    (wf_heaptype .NOFUNC) ->
    (wf_heaptype .FUNC) ->
    (Heaptype_sub C heaptype .FUNC) ->
    Heaptype_sub C .NOFUNC heaptype
  | noexn : forall (C : context) (heaptype : heaptype), 
    (wf_context C) ->
    (wf_heaptype heaptype) ->
    (wf_heaptype .NOEXN) ->
    (wf_heaptype .EXN) ->
    (Heaptype_sub C heaptype .EXN) ->
    Heaptype_sub C .NOEXN heaptype
  | noextern : forall (C : context) (heaptype : heaptype), 
    (wf_context C) ->
    (wf_heaptype heaptype) ->
    (wf_heaptype .NOEXTERN) ->
    (wf_heaptype .EXTERN) ->
    (Heaptype_sub C heaptype .EXTERN) ->
    Heaptype_sub C .NOEXTERN heaptype
  | bot : forall (C : context) (heaptype : heaptype), 
    (wf_context C) ->
    (wf_heaptype heaptype) ->
    (wf_heaptype .BOT) ->
    Heaptype_sub C .BOT heaptype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:10.1-10.103 -/
inductive Reftype_sub : context -> reftype -> reftype -> Prop where
  | nonnull : forall (C : context) (ht_1 : heaptype) (ht_2 : heaptype), 
    (wf_context C) ->
    (wf_reftype (.REF none ht_1)) ->
    (wf_reftype (.REF none ht_2)) ->
    (Heaptype_sub C ht_1 ht_2) ->
    Reftype_sub C (.REF none ht_1) (.REF none ht_2)
  | null : forall (C : context) (ht_1 : heaptype) (ht_2 : heaptype), 
    (wf_context C) ->
    (wf_reftype (.REF (some .NULL) ht_1)) ->
    (wf_reftype (.REF (some .NULL) ht_2)) ->
    (Heaptype_sub C ht_1 ht_2) ->
    Reftype_sub C (.REF (some .NULL) ht_1) (.REF (some .NULL) ht_2)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:11.1-11.103 -/
inductive Valtype_sub : context -> valtype -> valtype -> Prop where
  | num : forall (C : context) (numtype_1 : numtype) (numtype_2 : numtype), 
    (wf_context C) ->
    (Numtype_sub C numtype_1 numtype_2) ->
    Valtype_sub C (valtype_numtype numtype_1) (valtype_numtype numtype_2)
  | vec : forall (C : context) (vectype_1 : vectype) (vectype_2 : vectype), 
    (wf_context C) ->
    (Vectype_sub C vectype_1 vectype_2) ->
    Valtype_sub C (valtype_vectype vectype_1) (valtype_vectype vectype_2)
  | ref : forall (C : context) (reftype_1 : reftype) (reftype_2 : reftype), 
    (wf_context C) ->
    (wf_reftype reftype_1) ->
    (wf_reftype reftype_2) ->
    (Reftype_sub C reftype_1 reftype_2) ->
    Valtype_sub C (valtype_reftype reftype_1) (valtype_reftype reftype_2)
  | bot : forall (C : context) (valtype : valtype), 
    (wf_context C) ->
    (wf_valtype valtype) ->
    (wf_valtype .BOT) ->
    Valtype_sub C .BOT valtype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:116.1-116.115 -/
inductive Resulttype_sub : context -> resulttype -> resulttype -> Prop where
  |  : forall (C : context) (t_1* : (List valtype)) (t_2* : (List valtype)), 
    (wf_context C) ->
    Forall (fun (t_1 : valtype) => (wf_valtype t_1)) t_1* ->
    Forall (fun (t_2 : valtype) => (wf_valtype t_2)) t_2* ->
    ((List.length t_1*) == (List.length t_2*)) ->
    Forall₂ (fun (t_1 : valtype) (t_2 : valtype) => (Valtype_sub C t_1 t_2)) t_1* t_2* ->
    Resulttype_sub C (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:134.1-134.119 -/
inductive Storagetype_sub : context -> storagetype -> storagetype -> Prop where
  | val : forall (C : context) (valtype_1 : valtype) (valtype_2 : valtype), 
    (wf_context C) ->
    (wf_valtype valtype_1) ->
    (wf_valtype valtype_2) ->
    (Valtype_sub C valtype_1 valtype_2) ->
    Storagetype_sub C (storagetype_valtype valtype_1) (storagetype_valtype valtype_2)
  | pack : forall (C : context) (packtype_1 : packtype) (packtype_2 : packtype), 
    (wf_context C) ->
    (Packtype_sub C packtype_1 packtype_2) ->
    Storagetype_sub C (storagetype_packtype packtype_1) (storagetype_packtype packtype_2)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:135.1-135.117 -/
inductive Fieldtype_sub : context -> fieldtype -> fieldtype -> Prop where
  | const : forall (C : context) (zt_1 : storagetype) (zt_2 : storagetype), 
    (wf_context C) ->
    (wf_fieldtype (. none zt_1)) ->
    (wf_fieldtype (. none zt_2)) ->
    (Storagetype_sub C zt_1 zt_2) ->
    Fieldtype_sub C (. none zt_1) (. none zt_2)
  | var : forall (C : context) (zt_1 : storagetype) (zt_2 : storagetype), 
    (wf_context C) ->
    (wf_fieldtype (. (some .MUT) zt_1)) ->
    (wf_fieldtype (. (some .MUT) zt_2)) ->
    (Storagetype_sub C zt_1 zt_2) ->
    (Storagetype_sub C zt_2 zt_1) ->
    Fieldtype_sub C (. (some .MUT) zt_1) (. (some .MUT) zt_2)

end

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:50.1-50.99 -/
inductive Instrtype_ok : context -> instrtype -> Prop where
  |  : forall (C : context) (t_1* : (List valtype)) (x* : (List idx)) (t_2* : (List valtype)) (lct* : (List localtype)), 
    (wf_context C) ->
    Forall (fun (lct : localtype) => (wf_localtype lct)) lct* ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (List.map (fun (x : idx) => x) x*) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Resulttype_ok C (. (List.map (fun (t_1 : valtype) => t_1) t_1*))) ->
    (Resulttype_ok C (. (List.map (fun (t_2 : valtype) => t_2) t_2*))) ->
    ((List.length lct*) == (List.length x*)) ->
    Forall (fun (x : idx) => ((proj_uN_0 x) < (List.length (C.LOCALS)))) x* ->
    Forall₂ (fun (lct : localtype) (x : idx) => (((C.LOCALS)[(proj_uN_0 x)]!) == lct)) lct* x* ->
    Instrtype_ok C (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (List.map (fun (x : idx) => x) x*) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:68.1-69.70 -/
inductive Expand_use : typeuse -> context -> comptype -> Prop where
  | deftype : forall (deftype : deftype) (C : context) (comptype : comptype), 
    (wf_context C) ->
    (wf_comptype comptype) ->
    (Expand deftype comptype) ->
    Expand_use (typeuse_deftype deftype) C comptype
  | typeidx : forall (typeidx : typeidx) (C : context) (comptype : comptype), 
    (wf_context C) ->
    (wf_comptype comptype) ->
    (wf_typeuse (._IDX typeidx)) ->
    ((proj_uN_0 typeidx) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 typeidx)]!) comptype) ->
    Expand_use (._IDX typeidx) C comptype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:201.1-201.120 -/
inductive Limits_ok : context -> limits -> Nat -> Prop where
  |  : forall (C : context) (n : n) (m? : (Option m)) (k : Nat), 
    (wf_context C) ->
    (wf_limits (. (. n) (Option.map (fun (m : m) => (. m)) m?))) ->
    (n <= k) ->
    Forall (fun (m : Nat) => ((n <= m) && (m <= k))) (Option.toList m?) ->
    Limits_ok C (. (. n) (Option.map (fun (m : m) => (. m)) m?)) k

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:202.1-202.97 -/
inductive Tagtype_ok : context -> tagtype -> Prop where
  |  : forall (C : context) (typeuse : typeuse) (t_1* : (List valtype)) (t_2* : (List valtype)), 
    (wf_context C) ->
    (wf_typeuse typeuse) ->
    (wf_comptype (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Typeuse_ok C typeuse) ->
    (Expand_use typeuse C (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Tagtype_ok C typeuse

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:203.1-203.100 -/
inductive Globaltype_ok : context -> globaltype -> Prop where
  |  : forall (C : context) (t : valtype), 
    (wf_context C) ->
    (wf_globaltype (. (some .MUT) t)) ->
    (Valtype_ok C t) ->
    Globaltype_ok C (. (some .MUT) t)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:204.1-204.97 -/
inductive Memtype_ok : context -> memtype -> Prop where
  |  : forall (C : context) (addrtype : addrtype) (limits : limits), 
    (wf_context C) ->
    (wf_memtype (.PAGE addrtype limits)) ->
    (Limits_ok C limits (2 ^ 16)) ->
    Memtype_ok C (.PAGE addrtype limits)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:205.1-205.99 -/
inductive Tabletype_ok : context -> tabletype -> Prop where
  |  : forall (C : context) (addrtype : addrtype) (limits : limits) (reftype : reftype), 
    (wf_context C) ->
    (wf_tabletype (. addrtype limits reftype)) ->
    (Limits_ok C limits ((((2 ^ 32) : Nat) - (1 : Nat)) : Nat)) ->
    (Reftype_ok C reftype) ->
    Tabletype_ok C (. addrtype limits reftype)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:206.1-206.100 -/
inductive Externtype_ok : context -> externtype -> Prop where
  | tag : forall (C : context) (tagtype : tagtype), 
    (wf_context C) ->
    (wf_externtype (.TAG tagtype)) ->
    (Tagtype_ok C tagtype) ->
    Externtype_ok C (.TAG tagtype)
  | global : forall (C : context) (globaltype : globaltype), 
    (wf_context C) ->
    (wf_externtype (.GLOBAL globaltype)) ->
    (Globaltype_ok C globaltype) ->
    Externtype_ok C (.GLOBAL globaltype)
  | mem : forall (C : context) (memtype : memtype), 
    (wf_context C) ->
    (wf_externtype (.MEM memtype)) ->
    (Memtype_ok C memtype) ->
    Externtype_ok C (.MEM memtype)
  | table : forall (C : context) (tabletype : tabletype), 
    (wf_context C) ->
    (wf_externtype (.TABLE tabletype)) ->
    (Tabletype_ok C tabletype) ->
    Externtype_ok C (.TABLE tabletype)
  | func : forall (C : context) (typeuse : typeuse) (t_1* : (List valtype)) (t_2* : (List valtype)), 
    (wf_context C) ->
    (wf_externtype (.FUNC typeuse)) ->
    (wf_comptype (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Typeuse_ok C typeuse) ->
    (Expand_use typeuse C (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Externtype_ok C (.FUNC typeuse)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:117.1-117.114 -/
inductive Instrtype_sub : context -> instrtype -> instrtype -> Prop where
  |  : forall (C : context) (t_11* : (List valtype)) (x_1* : (List idx)) (t_12* : (List valtype)) (t_21* : (List valtype)) (x_2* : (List idx)) (t_22* : (List valtype)) (x* : (List idx)) (t* : (List valtype)), 
    (wf_context C) ->
    Forall (fun (x : idx) => (wf_uN 32 x)) x* ->
    (wf_instrtype (. (. (List.map (fun (t_11 : valtype) => t_11) t_11*)) (List.map (fun (x_1 : idx) => x_1) x_1*) (. (List.map (fun (t_12 : valtype) => t_12) t_12*)))) ->
    (wf_instrtype (. (. (List.map (fun (t_21 : valtype) => t_21) t_21*)) (List.map (fun (x_2 : idx) => x_2) x_2*) (. (List.map (fun (t_22 : valtype) => t_22) t_22*)))) ->
    Forall (fun (t : valtype) => (wf_localtype (. .SET t))) t* ->
    (Resulttype_sub C (. (List.map (fun (t_21 : valtype) => t_21) t_21*)) (. (List.map (fun (t_11 : valtype) => t_11) t_11*))) ->
    (Resulttype_sub C (. (List.map (fun (t_12 : valtype) => t_12) t_12*)) (. (List.map (fun (t_22 : valtype) => t_22) t_22*))) ->
    ((List.map (fun (x : idx) => x) x*) == (setminus_ localidx (List.map (fun (x_2 : idx) => x_2) x_2*) (List.map (fun (x_1 : idx) => x_1) x_1*))) ->
    ((List.length t*) == (List.length x*)) ->
    Forall (fun (x : idx) => ((proj_uN_0 x) < (List.length (C.LOCALS)))) x* ->
    Forall₂ (fun (t : valtype) (x : idx) => (((C.LOCALS)[(proj_uN_0 x)]!) == (. .SET t))) t* x* ->
    Instrtype_sub C (. (. (List.map (fun (t_11 : valtype) => t_11) t_11*)) (List.map (fun (x_1 : idx) => x_1) x_1*) (. (List.map (fun (t_12 : valtype) => t_12) t_12*))) (. (. (List.map (fun (t_21 : valtype) => t_21) t_21*)) (List.map (fun (x_2 : idx) => x_2) x_2*) (. (List.map (fun (t_22 : valtype) => t_22) t_22*)))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:191.1-191.110 -/
inductive Limits_sub : context -> limits -> limits -> Prop where
  |  : forall (C : context) (n_1 : n) (m_1 : m) (n_2 : n) (m_2 : m), 
    (wf_context C) ->
    (wf_limits (. (. n_1) (some (. m_1)))) ->
    (wf_limits (. (. n_2) (some (. m_2)))) ->
    (n_1 >= n_2) ->
    (m_1 <= m_2) ->
    Limits_sub C (. (. n_1) (some (. m_1))) (. (. n_2) (some (. m_2)))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:192.1-192.111 -/
inductive Tagtype_sub : context -> tagtype -> tagtype -> Prop where
  |  : forall (C : context) (deftype_1 : deftype) (deftype_2 : deftype), 
    (wf_context C) ->
    (Deftype_sub C deftype_1 deftype_2) ->
    (Deftype_sub C deftype_2 deftype_1) ->
    Tagtype_sub C (typeuse_deftype deftype_1) (typeuse_deftype deftype_2)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:193.1-193.114 -/
inductive Globaltype_sub : context -> globaltype -> globaltype -> Prop where
  | const : forall (C : context) (valtype_1 : valtype) (valtype_2 : valtype), 
    (wf_context C) ->
    (wf_globaltype (. none valtype_1)) ->
    (wf_globaltype (. none valtype_2)) ->
    (Valtype_sub C valtype_1 valtype_2) ->
    Globaltype_sub C (. none valtype_1) (. none valtype_2)
  | var : forall (C : context) (valtype_1 : valtype) (valtype_2 : valtype), 
    (wf_context C) ->
    (wf_globaltype (. (some .MUT) valtype_1)) ->
    (wf_globaltype (. (some .MUT) valtype_2)) ->
    (Valtype_sub C valtype_1 valtype_2) ->
    (Valtype_sub C valtype_2 valtype_1) ->
    Globaltype_sub C (. (some .MUT) valtype_1) (. (some .MUT) valtype_2)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:194.1-194.111 -/
inductive Memtype_sub : context -> memtype -> memtype -> Prop where
  |  : forall (C : context) (addrtype : addrtype) (limits_1 : limits) (limits_2 : limits), 
    (wf_context C) ->
    (wf_memtype (.PAGE addrtype limits_1)) ->
    (wf_memtype (.PAGE addrtype limits_2)) ->
    (Limits_sub C limits_1 limits_2) ->
    Memtype_sub C (.PAGE addrtype limits_1) (.PAGE addrtype limits_2)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:195.1-195.113 -/
inductive Tabletype_sub : context -> tabletype -> tabletype -> Prop where
  |  : forall (C : context) (addrtype : addrtype) (limits_1 : limits) (reftype_1 : reftype) (limits_2 : limits) (reftype_2 : reftype), 
    (wf_context C) ->
    (wf_tabletype (. addrtype limits_1 reftype_1)) ->
    (wf_tabletype (. addrtype limits_2 reftype_2)) ->
    (Limits_sub C limits_1 limits_2) ->
    (Reftype_sub C reftype_1 reftype_2) ->
    (Reftype_sub C reftype_2 reftype_1) ->
    Tabletype_sub C (. addrtype limits_1 reftype_1) (. addrtype limits_2 reftype_2)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:196.1-196.114 -/
inductive Externtype_sub : context -> externtype -> externtype -> Prop where
  | tag : forall (C : context) (tagtype_1 : tagtype) (tagtype_2 : tagtype), 
    (wf_context C) ->
    (wf_externtype (.TAG tagtype_1)) ->
    (wf_externtype (.TAG tagtype_2)) ->
    (Tagtype_sub C tagtype_1 tagtype_2) ->
    Externtype_sub C (.TAG tagtype_1) (.TAG tagtype_2)
  | global : forall (C : context) (globaltype_1 : globaltype) (globaltype_2 : globaltype), 
    (wf_context C) ->
    (wf_externtype (.GLOBAL globaltype_1)) ->
    (wf_externtype (.GLOBAL globaltype_2)) ->
    (Globaltype_sub C globaltype_1 globaltype_2) ->
    Externtype_sub C (.GLOBAL globaltype_1) (.GLOBAL globaltype_2)
  | mem : forall (C : context) (memtype_1 : memtype) (memtype_2 : memtype), 
    (wf_context C) ->
    (wf_externtype (.MEM memtype_1)) ->
    (wf_externtype (.MEM memtype_2)) ->
    (Memtype_sub C memtype_1 memtype_2) ->
    Externtype_sub C (.MEM memtype_1) (.MEM memtype_2)
  | table : forall (C : context) (tabletype_1 : tabletype) (tabletype_2 : tabletype), 
    (wf_context C) ->
    (wf_externtype (.TABLE tabletype_1)) ->
    (wf_externtype (.TABLE tabletype_2)) ->
    (Tabletype_sub C tabletype_1 tabletype_2) ->
    Externtype_sub C (.TABLE tabletype_1) (.TABLE tabletype_2)
  | func : forall (C : context) (deftype_1 : deftype) (deftype_2 : deftype), 
    (wf_context C) ->
    (wf_externtype (.FUNC (typeuse_deftype deftype_1))) ->
    (wf_externtype (.FUNC (typeuse_deftype deftype_2))) ->
    (Deftype_sub C deftype_1 deftype_2) ->
    Externtype_sub C (.FUNC (typeuse_deftype deftype_1)) (.FUNC (typeuse_deftype deftype_2))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:42.1-42.121 -/
inductive Blocktype_ok : context -> blocktype -> instrtype -> Prop where
  | valtype : forall (C : context) (valtype? : (Option valtype)), 
    (wf_context C) ->
    (wf_blocktype (._RESULT (Option.map (fun (valtype : valtype) => valtype) valtype?))) ->
    (wf_instrtype (. (. []) [] (. (Option.toList (Option.map (fun (valtype : valtype) => valtype) valtype?))))) ->
    Forall (fun (valtype : valtype) => (Valtype_ok C valtype)) (Option.toList valtype?) ->
    Blocktype_ok C (._RESULT (Option.map (fun (valtype : valtype) => valtype) valtype?)) (. (. []) [] (. (Option.toList (Option.map (fun (valtype : valtype) => valtype) valtype?))))
  | typeidx : forall (C : context) (typeidx : typeidx) (t_1* : (List valtype)) (t_2* : (List valtype)), 
    (wf_context C) ->
    (wf_blocktype (._IDX typeidx)) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_comptype (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    ((proj_uN_0 typeidx) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 typeidx)]!) (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Blocktype_ok C (._IDX typeidx) (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:164.1-164.77 -/
inductive Catch_ok : context -> «catch» -> Prop where
  | catch : forall (C : context) (x : idx) (l : labelidx) (t* : (List valtype)), 
    (wf_context C) ->
    (wf_catch (.CATCH x l)) ->
    (wf_comptype (.FUNC (. (List.map (fun (t : valtype) => t) t*)) (. []))) ->
    ((proj_uN_0 x) < (List.length (C.TAGS))) ->
    (Expand (as_deftype ((C.TAGS)[(proj_uN_0 x)]!)) (.FUNC (. (List.map (fun (t : valtype) => t) t*)) (. []))) ->
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    (Resulttype_sub C (. (List.map (fun (t : valtype) => t) t*)) ((C.LABELS)[(proj_uN_0 l)]!)) ->
    Catch_ok C (.CATCH x l)
  | catch_ref : forall (C : context) (x : idx) (l : labelidx) (t* : (List valtype)), 
    (wf_context C) ->
    (wf_catch (.CATCH_REF x l)) ->
    (wf_comptype (.FUNC (. (List.map (fun (t : valtype) => t) t*)) (. []))) ->
    ((proj_uN_0 x) < (List.length (C.TAGS))) ->
    (Expand (as_deftype ((C.TAGS)[(proj_uN_0 x)]!)) (.FUNC (. (List.map (fun (t : valtype) => t) t*)) (. []))) ->
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    (Resulttype_sub C (. ((List.map (fun (t : valtype) => t) t*) ++ [(.REF none .EXN)])) ((C.LABELS)[(proj_uN_0 l)]!)) ->
    Catch_ok C (.CATCH_REF x l)
  | catch_all : forall (C : context) (l : labelidx), 
    (wf_context C) ->
    (wf_catch (.CATCH_ALL l)) ->
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    (Resulttype_sub C (. []) ((C.LABELS)[(proj_uN_0 l)]!)) ->
    Catch_ok C (.CATCH_ALL l)
  | catch_all_ref : forall (C : context) (l : labelidx), 
    (wf_context C) ->
    (wf_catch (.CATCH_ALL_REF l)) ->
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    (Resulttype_sub C (. [(.REF none .EXN)]) ((C.LABELS)[(proj_uN_0 l)]!)) ->
    Catch_ok C (.CATCH_ALL_REF l)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.1-execution.values.spectec:7.1-7.30 -/
opaque default_ : forall (valtype : valtype), (Option val) := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:9.1-10.71 -/
inductive Defaultable : valtype -> Prop where
  |  : forall (t : valtype), 
    (wf_valtype t) ->
    ((default_ t) != none) ->
    Defaultable t

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:255.1-255.111 -/
opaque is_packtype : forall (storagetype : storagetype), Bool := opaqueDef

/- Recursive Definitions at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:5.1-6.96 -/
mutual
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:5.1-5.95 -/
inductive Instr_ok : context -> instr -> instrtype -> Prop where
  | nop : forall (C : context), 
    (wf_context C) ->
    (wf_instr .NOP) ->
    (wf_instrtype (. (. []) [] (. []))) ->
    Instr_ok C .NOP (. (. []) [] (. []))
  | unreachable : forall (C : context) (t_1* : (List valtype)) (t_2* : (List valtype)), 
    (wf_context C) ->
    (wf_instr .UNREACHABLE) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Instrtype_ok C (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Instr_ok C .UNREACHABLE (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))
  | drop : forall (C : context) (t : valtype), 
    (wf_context C) ->
    (wf_instr .DROP) ->
    (wf_instrtype (. (. [t]) [] (. []))) ->
    (Valtype_ok C t) ->
    Instr_ok C .DROP (. (. [t]) [] (. []))
  | select-expl : forall (C : context) (t : valtype), 
    (wf_context C) ->
    (wf_instr (.SELECT (some [t]))) ->
    (wf_instrtype (. (. [t, t, .I32]) [] (. [t]))) ->
    (Valtype_ok C t) ->
    Instr_ok C (.SELECT (some [t])) (. (. [t, t, .I32]) [] (. [t]))
  | select-impl : forall (C : context) (t : valtype) (t' : valtype) (numtype : numtype) (vectype : vectype), 
    (wf_context C) ->
    (wf_valtype t') ->
    (wf_instr (.SELECT none)) ->
    (wf_instrtype (. (. [t, t, .I32]) [] (. [t]))) ->
    (Valtype_ok C t) ->
    (Valtype_sub C t t') ->
    ((t' == (valtype_numtype numtype)) || (t' == (valtype_vectype vectype))) ->
    Instr_ok C (.SELECT none) (. (. [t, t, .I32]) [] (. [t]))
  | block : forall (C : context) (bt : blocktype) (instr* : (List instr)) (t_1* : (List valtype)) (t_2* : (List valtype)) (x* : (List idx)), 
    (wf_context C) ->
    (wf_instr (.BLOCK bt (List.map (fun (instr : instr) => instr) instr*))) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [(. (List.map (fun (t_2 : valtype) => t_2) t_2*))], RETURN := none, REFS := [] }) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (List.map (fun (x : idx) => x) x*) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Blocktype_ok C bt (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Instrs_ok ({ TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [(. (List.map (fun (t_2 : valtype) => t_2) t_2*))], RETURN := none, REFS := [] } ++ C) (List.map (fun (instr : instr) => instr) instr*) (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (List.map (fun (x : idx) => x) x*) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Instr_ok C (.BLOCK bt (List.map (fun (instr : instr) => instr) instr*)) (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))
  | loop : forall (C : context) (bt : blocktype) (instr* : (List instr)) (t_1* : (List valtype)) (t_2* : (List valtype)) (x* : (List idx)), 
    (wf_context C) ->
    (wf_instr (.LOOP bt (List.map (fun (instr : instr) => instr) instr*))) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [(. (List.map (fun (t_1 : valtype) => t_1) t_1*))], RETURN := none, REFS := [] }) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (List.map (fun (x : idx) => x) x*) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Blocktype_ok C bt (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Instrs_ok ({ TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [(. (List.map (fun (t_1 : valtype) => t_1) t_1*))], RETURN := none, REFS := [] } ++ C) (List.map (fun (instr : instr) => instr) instr*) (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (List.map (fun (x : idx) => x) x*) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Instr_ok C (.LOOP bt (List.map (fun (instr : instr) => instr) instr*)) (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))
  | if : forall (C : context) (bt : blocktype) (instr_1* : (List instr)) (instr_2* : (List instr)) (t_1* : (List valtype)) (t_2* : (List valtype)) (x_1* : (List idx)) (x_2* : (List idx)), 
    (wf_context C) ->
    (wf_instr (.IFELSE bt (List.map (fun (instr_1 : instr) => instr_1) instr_1*) (List.map (fun (instr_2 : instr) => instr_2) instr_2*))) ->
    (wf_instrtype (. (. ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ [.I32])) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [(. (List.map (fun (t_2 : valtype) => t_2) t_2*))], RETURN := none, REFS := [] }) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (List.map (fun (x_1 : idx) => x_1) x_1*) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (List.map (fun (x_2 : idx) => x_2) x_2*) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Blocktype_ok C bt (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Instrs_ok ({ TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [(. (List.map (fun (t_2 : valtype) => t_2) t_2*))], RETURN := none, REFS := [] } ++ C) (List.map (fun (instr_1 : instr) => instr_1) instr_1*) (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (List.map (fun (x_1 : idx) => x_1) x_1*) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Instrs_ok ({ TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [(. (List.map (fun (t_2 : valtype) => t_2) t_2*))], RETURN := none, REFS := [] } ++ C) (List.map (fun (instr_2 : instr) => instr_2) instr_2*) (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (List.map (fun (x_2 : idx) => x_2) x_2*) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Instr_ok C (.IFELSE bt (List.map (fun (instr_1 : instr) => instr_1) instr_1*) (List.map (fun (instr_2 : instr) => instr_2) instr_2*)) (. (. ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ [.I32])) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))
  | br : forall (C : context) (l : labelidx) (t_1* : (List valtype)) (t* : (List valtype)) (t_2* : (List valtype)), 
    (wf_context C) ->
    (wf_instr (.BR l)) ->
    (wf_instrtype (. (. ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ (List.map (fun (t : valtype) => t) t*))) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    ((proj_list_0 valtype ((C.LABELS)[(proj_uN_0 l)]!)) == (List.map (fun (t : valtype) => t) t*)) ->
    (Instrtype_ok C (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Instr_ok C (.BR l) (. (. ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ (List.map (fun (t : valtype) => t) t*))) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))
  | br_if : forall (C : context) (l : labelidx) (t* : (List valtype)), 
    (wf_context C) ->
    (wf_instr (.BR_IF l)) ->
    (wf_instrtype (. (. ((List.map (fun (t : valtype) => t) t*) ++ [.I32])) [] (. (List.map (fun (t : valtype) => t) t*)))) ->
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    ((proj_list_0 valtype ((C.LABELS)[(proj_uN_0 l)]!)) == (List.map (fun (t : valtype) => t) t*)) ->
    Instr_ok C (.BR_IF l) (. (. ((List.map (fun (t : valtype) => t) t*) ++ [.I32])) [] (. (List.map (fun (t : valtype) => t) t*)))
  | br_table : forall (C : context) (l* : (List labelidx)) (l' : labelidx) (t_1* : (List valtype)) (t* : (List valtype)) (t_2* : (List valtype)), 
    (wf_context C) ->
    (wf_instr (.BR_TABLE (List.map (fun (l : labelidx) => l) l*) l')) ->
    (wf_instrtype (. (. ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ ((List.map (fun (t : valtype) => t) t*) ++ [.I32]))) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Forall (fun (l : labelidx) => ((proj_uN_0 l) < (List.length (C.LABELS)))) l* ->
    Forall (fun (l : labelidx) => (Resulttype_sub C (. (List.map (fun (t : valtype) => t) t*)) ((C.LABELS)[(proj_uN_0 l)]!))) l* ->
    ((proj_uN_0 l') < (List.length (C.LABELS))) ->
    (Resulttype_sub C (. (List.map (fun (t : valtype) => t) t*)) ((C.LABELS)[(proj_uN_0 l')]!)) ->
    (Instrtype_ok C (. (. ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ ((List.map (fun (t : valtype) => t) t*) ++ [.I32]))) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Instr_ok C (.BR_TABLE (List.map (fun (l : labelidx) => l) l*) l') (. (. ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ ((List.map (fun (t : valtype) => t) t*) ++ [.I32]))) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))
  | br_on_null : forall (C : context) (l : labelidx) (t* : (List valtype)) (ht : heaptype), 
    (wf_context C) ->
    (wf_instr (.BR_ON_NULL l)) ->
    (wf_instrtype (. (. ((List.map (fun (t : valtype) => t) t*) ++ [(.REF (some .NULL) ht)])) [] (. ((List.map (fun (t : valtype) => t) t*) ++ [(.REF none ht)])))) ->
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    ((proj_list_0 valtype ((C.LABELS)[(proj_uN_0 l)]!)) == (List.map (fun (t : valtype) => t) t*)) ->
    (Heaptype_ok C ht) ->
    Instr_ok C (.BR_ON_NULL l) (. (. ((List.map (fun (t : valtype) => t) t*) ++ [(.REF (some .NULL) ht)])) [] (. ((List.map (fun (t : valtype) => t) t*) ++ [(.REF none ht)])))
  | br_on_non_null : forall (C : context) (l : labelidx) (t* : (List valtype)) (ht : heaptype), 
    (wf_context C) ->
    (wf_instr (.BR_ON_NON_NULL l)) ->
    (wf_instrtype (. (. ((List.map (fun (t : valtype) => t) t*) ++ [(.REF (some .NULL) ht)])) [] (. (List.map (fun (t : valtype) => t) t*)))) ->
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    (((C.LABELS)[(proj_uN_0 l)]!) == (. ((List.map (fun (t : valtype) => t) t*) ++ [(.REF (some .NULL) ht)]))) ->
    Instr_ok C (.BR_ON_NON_NULL l) (. (. ((List.map (fun (t : valtype) => t) t*) ++ [(.REF (some .NULL) ht)])) [] (. (List.map (fun (t : valtype) => t) t*)))
  | br_on_cast : forall (C : context) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype) (t* : (List valtype)) (rt : reftype), 
    (wf_context C) ->
    (wf_reftype rt) ->
    (wf_instr (.BR_ON_CAST l rt_1 rt_2)) ->
    (wf_instrtype (. (. ((List.map (fun (t : valtype) => t) t*) ++ [(valtype_reftype rt_1)])) [] (. ((List.map (fun (t : valtype) => t) t*) ++ [(valtype_reftype (diffrt rt_1 rt_2))])))) ->
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    (((C.LABELS)[(proj_uN_0 l)]!) == (. ((List.map (fun (t : valtype) => t) t*) ++ [(valtype_reftype rt)]))) ->
    (Reftype_ok C rt_1) ->
    (Reftype_ok C rt_2) ->
    (Reftype_sub C rt_2 rt_1) ->
    (Reftype_sub C rt_2 rt) ->
    Instr_ok C (.BR_ON_CAST l rt_1 rt_2) (. (. ((List.map (fun (t : valtype) => t) t*) ++ [(valtype_reftype rt_1)])) [] (. ((List.map (fun (t : valtype) => t) t*) ++ [(valtype_reftype (diffrt rt_1 rt_2))])))
  | br_on_cast_fail : forall (C : context) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype) (t* : (List valtype)) (rt : reftype), 
    (wf_context C) ->
    (wf_reftype rt) ->
    (wf_instr (.BR_ON_CAST_FAIL l rt_1 rt_2)) ->
    (wf_instrtype (. (. ((List.map (fun (t : valtype) => t) t*) ++ [(valtype_reftype rt_1)])) [] (. ((List.map (fun (t : valtype) => t) t*) ++ [(valtype_reftype rt_2)])))) ->
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    (((C.LABELS)[(proj_uN_0 l)]!) == (. ((List.map (fun (t : valtype) => t) t*) ++ [(valtype_reftype rt)]))) ->
    (Reftype_ok C rt_1) ->
    (Reftype_ok C rt_2) ->
    (Reftype_sub C rt_2 rt_1) ->
    (Reftype_sub C (diffrt rt_1 rt_2) rt) ->
    Instr_ok C (.BR_ON_CAST_FAIL l rt_1 rt_2) (. (. ((List.map (fun (t : valtype) => t) t*) ++ [(valtype_reftype rt_1)])) [] (. ((List.map (fun (t : valtype) => t) t*) ++ [(valtype_reftype rt_2)])))
  | call : forall (C : context) (x : idx) (t_1* : (List valtype)) (t_2* : (List valtype)), 
    (wf_context C) ->
    (wf_instr (.CALL x)) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_comptype (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    ((proj_uN_0 x) < (List.length (C.FUNCS))) ->
    (Expand ((C.FUNCS)[(proj_uN_0 x)]!) (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Instr_ok C (.CALL x) (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))
  | call_ref : forall (C : context) (x : idx) (t_1* : (List valtype)) (t_2* : (List valtype)), 
    (wf_context C) ->
    (wf_instr (.CALL_REF (._IDX x))) ->
    (wf_instrtype (. (. ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ [(.REF (some .NULL) (._IDX x))])) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_comptype (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Instr_ok C (.CALL_REF (._IDX x)) (. (. ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ [(.REF (some .NULL) (._IDX x))])) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))
  | call_indirect : forall (C : context) (x : idx) (y : idx) (t_1* : (List valtype)) (at : addrtype) (t_2* : (List valtype)) (lim : limits) (rt : reftype), 
    (wf_context C) ->
    (wf_instr (.CALL_INDIRECT x (._IDX y))) ->
    (wf_instrtype (. (. ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ [(valtype_addrtype at)])) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_tabletype (. at lim rt)) ->
    (wf_reftype (.REF (some .NULL) .FUNC)) ->
    (wf_comptype (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (. at lim rt)) ->
    (Reftype_sub C rt (.REF (some .NULL) .FUNC)) ->
    ((proj_uN_0 y) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 y)]!) (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Instr_ok C (.CALL_INDIRECT x (._IDX y)) (. (. ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ [(valtype_addrtype at)])) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))
  | return : forall (C : context) (t_1* : (List valtype)) (t* : (List valtype)) (t_2* : (List valtype)), 
    (wf_context C) ->
    (wf_instr .RETURN) ->
    (wf_instrtype (. (. ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ (List.map (fun (t : valtype) => t) t*))) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    ((C.RETURN) == (some (. (List.map (fun (t : valtype) => t) t*)))) ->
    (Instrtype_ok C (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Instr_ok C .RETURN (. (. ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ (List.map (fun (t : valtype) => t) t*))) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))
  | return_call : forall (C : context) (x : idx) (t_3* : (List valtype)) (t_1* : (List valtype)) (t_4* : (List valtype)) (t_2* : (List valtype)) (t'_2* : (List valtype)), 
    (wf_context C) ->
    Forall (fun (t'_2 : valtype) => (wf_valtype t'_2)) t'_2* ->
    (wf_instr (.RETURN_CALL x)) ->
    (wf_instrtype (. (. ((List.map (fun (t_3 : valtype) => t_3) t_3*) ++ (List.map (fun (t_1 : valtype) => t_1) t_1*))) [] (. (List.map (fun (t_4 : valtype) => t_4) t_4*)))) ->
    (wf_comptype (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_instrtype (. (. (List.map (fun (t_3 : valtype) => t_3) t_3*)) [] (. (List.map (fun (t_4 : valtype) => t_4) t_4*)))) ->
    ((proj_uN_0 x) < (List.length (C.FUNCS))) ->
    (Expand ((C.FUNCS)[(proj_uN_0 x)]!) (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    ((C.RETURN) == (some (. (List.map (fun (t'_2 : valtype) => t'_2) t'_2*)))) ->
    (Resulttype_sub C (. (List.map (fun (t_2 : valtype) => t_2) t_2*)) (. (List.map (fun (t'_2 : valtype) => t'_2) t'_2*))) ->
    (Instrtype_ok C (. (. (List.map (fun (t_3 : valtype) => t_3) t_3*)) [] (. (List.map (fun (t_4 : valtype) => t_4) t_4*)))) ->
    Instr_ok C (.RETURN_CALL x) (. (. ((List.map (fun (t_3 : valtype) => t_3) t_3*) ++ (List.map (fun (t_1 : valtype) => t_1) t_1*))) [] (. (List.map (fun (t_4 : valtype) => t_4) t_4*)))
  | return_call_ref : forall (C : context) (x : idx) (t_3* : (List valtype)) (t_1* : (List valtype)) (t_4* : (List valtype)) (t_2* : (List valtype)) (t'_2* : (List valtype)), 
    (wf_context C) ->
    Forall (fun (t'_2 : valtype) => (wf_valtype t'_2)) t'_2* ->
    (wf_instr (.RETURN_CALL_REF (._IDX x))) ->
    (wf_instrtype (. (. ((List.map (fun (t_3 : valtype) => t_3) t_3*) ++ ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ [(.REF (some .NULL) (._IDX x))]))) [] (. (List.map (fun (t_4 : valtype) => t_4) t_4*)))) ->
    (wf_comptype (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_instrtype (. (. (List.map (fun (t_3 : valtype) => t_3) t_3*)) [] (. (List.map (fun (t_4 : valtype) => t_4) t_4*)))) ->
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    ((C.RETURN) == (some (. (List.map (fun (t'_2 : valtype) => t'_2) t'_2*)))) ->
    (Resulttype_sub C (. (List.map (fun (t_2 : valtype) => t_2) t_2*)) (. (List.map (fun (t'_2 : valtype) => t'_2) t'_2*))) ->
    (Instrtype_ok C (. (. (List.map (fun (t_3 : valtype) => t_3) t_3*)) [] (. (List.map (fun (t_4 : valtype) => t_4) t_4*)))) ->
    Instr_ok C (.RETURN_CALL_REF (._IDX x)) (. (. ((List.map (fun (t_3 : valtype) => t_3) t_3*) ++ ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ [(.REF (some .NULL) (._IDX x))]))) [] (. (List.map (fun (t_4 : valtype) => t_4) t_4*)))
  | return_call_indirect : forall (C : context) (x : idx) (y : idx) (t_3* : (List valtype)) (t_1* : (List valtype)) (at : addrtype) (t_4* : (List valtype)) (lim : limits) (rt : reftype) (t_2* : (List valtype)) (t'_2* : (List valtype)), 
    (wf_context C) ->
    Forall (fun (t'_2 : valtype) => (wf_valtype t'_2)) t'_2* ->
    (wf_instr (.RETURN_CALL_INDIRECT x (._IDX y))) ->
    (wf_instrtype (. (. ((List.map (fun (t_3 : valtype) => t_3) t_3*) ++ ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ [(valtype_addrtype at)]))) [] (. (List.map (fun (t_4 : valtype) => t_4) t_4*)))) ->
    (wf_tabletype (. at lim rt)) ->
    (wf_reftype (.REF (some .NULL) .FUNC)) ->
    (wf_comptype (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_instrtype (. (. (List.map (fun (t_3 : valtype) => t_3) t_3*)) [] (. (List.map (fun (t_4 : valtype) => t_4) t_4*)))) ->
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (. at lim rt)) ->
    (Reftype_sub C rt (.REF (some .NULL) .FUNC)) ->
    ((proj_uN_0 y) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 y)]!) (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    ((C.RETURN) == (some (. (List.map (fun (t'_2 : valtype) => t'_2) t'_2*)))) ->
    (Resulttype_sub C (. (List.map (fun (t_2 : valtype) => t_2) t_2*)) (. (List.map (fun (t'_2 : valtype) => t'_2) t'_2*))) ->
    (Instrtype_ok C (. (. (List.map (fun (t_3 : valtype) => t_3) t_3*)) [] (. (List.map (fun (t_4 : valtype) => t_4) t_4*)))) ->
    Instr_ok C (.RETURN_CALL_INDIRECT x (._IDX y)) (. (. ((List.map (fun (t_3 : valtype) => t_3) t_3*) ++ ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ [(valtype_addrtype at)]))) [] (. (List.map (fun (t_4 : valtype) => t_4) t_4*)))
  | throw : forall (C : context) (x : idx) (t_1* : (List valtype)) (t* : (List valtype)) (t_2* : (List valtype)), 
    (wf_context C) ->
    (wf_instr (.THROW x)) ->
    (wf_instrtype (. (. ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ (List.map (fun (t : valtype) => t) t*))) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_comptype (.FUNC (. (List.map (fun (t : valtype) => t) t*)) (. []))) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    ((proj_uN_0 x) < (List.length (C.TAGS))) ->
    (Expand (as_deftype ((C.TAGS)[(proj_uN_0 x)]!)) (.FUNC (. (List.map (fun (t : valtype) => t) t*)) (. []))) ->
    (Instrtype_ok C (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Instr_ok C (.THROW x) (. (. ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ (List.map (fun (t : valtype) => t) t*))) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))
  | throw_ref : forall (C : context) (t_1* : (List valtype)) (t_2* : (List valtype)), 
    (wf_context C) ->
    (wf_instr .THROW_REF) ->
    (wf_instrtype (. (. ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ [(.REF (some .NULL) .EXN)])) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Instrtype_ok C (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Instr_ok C .THROW_REF (. (. ((List.map (fun (t_1 : valtype) => t_1) t_1*) ++ [(.REF (some .NULL) .EXN)])) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))
  | try_table : forall (C : context) (bt : blocktype) (catch* : (List «catch»)) (instr* : (List instr)) (t_1* : (List valtype)) (t_2* : (List valtype)) (x* : (List idx)), 
    (wf_context C) ->
    (wf_instr (.TRY_TABLE bt (. (List.map (fun (catch : «catch») => «catch») catch*)) (List.map (fun (instr : instr) => instr) instr*))) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [(. (List.map (fun (t_2 : valtype) => t_2) t_2*))], RETURN := none, REFS := [] }) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (List.map (fun (x : idx) => x) x*) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Blocktype_ok C bt (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Instrs_ok ({ TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [(. (List.map (fun (t_2 : valtype) => t_2) t_2*))], RETURN := none, REFS := [] } ++ C) (List.map (fun (instr : instr) => instr) instr*) (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (List.map (fun (x : idx) => x) x*) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Forall (fun (catch : «catch») => (Catch_ok C «catch»)) catch* ->
    Instr_ok C (.TRY_TABLE bt (. (List.map (fun (catch : «catch») => «catch») catch*)) (List.map (fun (instr : instr) => instr) instr*)) (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))
  | ref.null : forall (C : context) (ht : heaptype), 
    (wf_context C) ->
    (wf_instr (.REF.NULL ht)) ->
    (wf_instrtype (. (. []) [] (. [(.REF (some .NULL) ht)]))) ->
    (Heaptype_ok C ht) ->
    Instr_ok C (.REF.NULL ht) (. (. []) [] (. [(.REF (some .NULL) ht)]))
  | ref.func : forall (C : context) (x : idx) (dt : deftype), 
    (wf_context C) ->
    (wf_instr (.REF.FUNC x)) ->
    (wf_instrtype (. (. []) [] (. [(.REF none (heaptype_deftype dt))]))) ->
    ((proj_uN_0 x) < (List.length (C.FUNCS))) ->
    (((C.FUNCS)[(proj_uN_0 x)]!) == dt) ->
    ((List.length (C.REFS)) > 0) ->
    (List.contains (C.REFS) x) ->
    Instr_ok C (.REF.FUNC x) (. (. []) [] (. [(.REF none (heaptype_deftype dt))]))
  | ref.i31 : forall (C : context), 
    (wf_context C) ->
    (wf_instr .REF.I31) ->
    (wf_instrtype (. (. [.I32]) [] (. [(.REF none .I31)]))) ->
    Instr_ok C .REF.I31 (. (. [.I32]) [] (. [(.REF none .I31)]))
  | ref.is_null : forall (C : context) (ht : heaptype), 
    (wf_context C) ->
    (wf_instr .REF.IS_NULL) ->
    (wf_instrtype (. (. [(.REF (some .NULL) ht)]) [] (. [.I32]))) ->
    (Heaptype_ok C ht) ->
    Instr_ok C .REF.IS_NULL (. (. [(.REF (some .NULL) ht)]) [] (. [.I32]))
  | ref.as_non_null : forall (C : context) (ht : heaptype), 
    (wf_context C) ->
    (wf_instr .REF.AS_NON_NULL) ->
    (wf_instrtype (. (. [(.REF (some .NULL) ht)]) [] (. [(.REF none ht)]))) ->
    (Heaptype_ok C ht) ->
    Instr_ok C .REF.AS_NON_NULL (. (. [(.REF (some .NULL) ht)]) [] (. [(.REF none ht)]))
  | ref.eq : forall (C : context), 
    (wf_context C) ->
    (wf_instr .REF.EQ) ->
    (wf_instrtype (. (. [(.REF (some .NULL) .EQ), (.REF (some .NULL) .EQ)]) [] (. [.I32]))) ->
    Instr_ok C .REF.EQ (. (. [(.REF (some .NULL) .EQ), (.REF (some .NULL) .EQ)]) [] (. [.I32]))
  | ref.test : forall (C : context) (rt : reftype) (rt' : reftype), 
    (wf_context C) ->
    (wf_instr (.REF.TEST rt)) ->
    (wf_instrtype (. (. [(valtype_reftype rt')]) [] (. [.I32]))) ->
    (Reftype_ok C rt) ->
    (Reftype_ok C rt') ->
    (Reftype_sub C rt rt') ->
    Instr_ok C (.REF.TEST rt) (. (. [(valtype_reftype rt')]) [] (. [.I32]))
  | ref.cast : forall (C : context) (rt : reftype) (rt' : reftype), 
    (wf_context C) ->
    (wf_instr (.REF.CAST rt)) ->
    (wf_instrtype (. (. [(valtype_reftype rt')]) [] (. [(valtype_reftype rt)]))) ->
    (Reftype_ok C rt) ->
    (Reftype_ok C rt') ->
    (Reftype_sub C rt rt') ->
    Instr_ok C (.REF.CAST rt) (. (. [(valtype_reftype rt')]) [] (. [(valtype_reftype rt)]))
  | i31.get : forall (C : context) (sx : sx), 
    (wf_context C) ->
    (wf_instr (.I31.GET sx)) ->
    (wf_instrtype (. (. [(.REF (some .NULL) .I31)]) [] (. [.I32]))) ->
    Instr_ok C (.I31.GET sx) (. (. [(.REF (some .NULL) .I31)]) [] (. [.I32]))
  | struct.new : forall (C : context) (x : idx) (zt* : (List storagetype)) (mut?* : (List (Option «mut»))), 
    (wf_context C) ->
    (wf_instr (.STRUCT.NEW x)) ->
    (wf_instrtype (. (. (List.map (fun (zt : storagetype) => (unpack zt)) zt*)) [] (. [(.REF none (._IDX x))]))) ->
    ((List.length mut?*) == (List.length zt*)) ->
    (wf_comptype (.STRUCT (. (List.zipWith (fun (mut? : (Option «mut»)) (zt : storagetype) => (. (Option.map (fun (mut : «mut») => «mut») mut?) zt)) mut?* zt*)))) ->
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.STRUCT (. (List.zipWith (fun (mut? : (Option «mut»)) (zt : storagetype) => (. (Option.map (fun (mut : «mut») => «mut») mut?) zt)) mut?* zt*)))) ->
    Instr_ok C (.STRUCT.NEW x) (. (. (List.map (fun (zt : storagetype) => (unpack zt)) zt*)) [] (. [(.REF none (._IDX x))]))
  | struct.new_default : forall (C : context) (x : idx) (mut?* : (List (Option «mut»))) (zt* : (List storagetype)), 
    (wf_context C) ->
    (wf_instr (.STRUCT.NEW_DEFAULT x)) ->
    (wf_instrtype (. (. []) [] (. [(.REF none (._IDX x))]))) ->
    ((List.length mut?*) == (List.length zt*)) ->
    (wf_comptype (.STRUCT (. (List.zipWith (fun (mut? : (Option «mut»)) (zt : storagetype) => (. (Option.map (fun (mut : «mut») => «mut») mut?) zt)) mut?* zt*)))) ->
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.STRUCT (. (List.zipWith (fun (mut? : (Option «mut»)) (zt : storagetype) => (. (Option.map (fun (mut : «mut») => «mut») mut?) zt)) mut?* zt*)))) ->
    Forall (fun (zt : storagetype) => (Defaultable (unpack zt))) zt* ->
    Instr_ok C (.STRUCT.NEW_DEFAULT x) (. (. []) [] (. [(.REF none (._IDX x))]))
  | struct.get : forall (C : context) (sx? : (Option sx)) (x : idx) (i : u32) (zt : storagetype) (ft* : (List fieldtype)) (mut? : (Option «mut»)), 
    (wf_context C) ->
    (wf_instr (.STRUCT.GET (Option.map (fun (sx : sx) => sx) sx?) x i)) ->
    (wf_instrtype (. (. [(.REF (some .NULL) (._IDX x))]) [] (. [(unpack zt)]))) ->
    (wf_comptype (.STRUCT (. (List.map (fun (ft : fieldtype) => ft) ft*)))) ->
    (wf_fieldtype (. (Option.map (fun (mut : «mut») => «mut») mut?) zt)) ->
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.STRUCT (. (List.map (fun (ft : fieldtype) => ft) ft*)))) ->
    ((proj_uN_0 i) < (List.length (List.map (fun (ft : fieldtype) => ft) ft*))) ->
    (((List.map (fun (ft : fieldtype) => ft) ft*)[(proj_uN_0 i)]!) == (. (Option.map (fun (mut : «mut») => «mut») mut?) zt)) ->
    (((Option.map (fun (sx : sx) => sx) sx?) == none) <-> (is_packtype zt)) ->
    Instr_ok C (.STRUCT.GET (Option.map (fun (sx : sx) => sx) sx?) x i) (. (. [(.REF (some .NULL) (._IDX x))]) [] (. [(unpack zt)]))
  | struct.set : forall (C : context) (x : idx) (i : u32) (zt : storagetype) (ft* : (List fieldtype)), 
    (wf_context C) ->
    (wf_instr (.STRUCT.SET x i)) ->
    (wf_instrtype (. (. [(.REF (some .NULL) (._IDX x)), (unpack zt)]) [] (. []))) ->
    (wf_comptype (.STRUCT (. (List.map (fun (ft : fieldtype) => ft) ft*)))) ->
    (wf_fieldtype (. (some .MUT) zt)) ->
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.STRUCT (. (List.map (fun (ft : fieldtype) => ft) ft*)))) ->
    ((proj_uN_0 i) < (List.length (List.map (fun (ft : fieldtype) => ft) ft*))) ->
    (((List.map (fun (ft : fieldtype) => ft) ft*)[(proj_uN_0 i)]!) == (. (some .MUT) zt)) ->
    Instr_ok C (.STRUCT.SET x i) (. (. [(.REF (some .NULL) (._IDX x)), (unpack zt)]) [] (. []))
  | array.new : forall (C : context) (x : idx) (zt : storagetype) (mut? : (Option «mut»)), 
    (wf_context C) ->
    (wf_instr (.ARRAY.NEW x)) ->
    (wf_instrtype (. (. [(unpack zt), .I32]) [] (. [(.REF none (._IDX x))]))) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    Instr_ok C (.ARRAY.NEW x) (. (. [(unpack zt), .I32]) [] (. [(.REF none (._IDX x))]))
  | array.new_default : forall (C : context) (x : idx) (mut? : (Option «mut»)) (zt : storagetype), 
    (wf_context C) ->
    (wf_instr (.ARRAY.NEW_DEFAULT x)) ->
    (wf_instrtype (. (. [.I32]) [] (. [(.REF none (._IDX x))]))) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    (Defaultable (unpack zt)) ->
    Instr_ok C (.ARRAY.NEW_DEFAULT x) (. (. [.I32]) [] (. [(.REF none (._IDX x))]))
  | array.new_fixed : forall (C : context) (x : idx) (n : n) (zt : storagetype) (mut? : (Option «mut»)), 
    (wf_context C) ->
    (wf_instr (.ARRAY.NEW_FIXED x (. n))) ->
    (wf_instrtype (. (. (List.replicate n (unpack zt))) [] (. [(.REF none (._IDX x))]))) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    Instr_ok C (.ARRAY.NEW_FIXED x (. n)) (. (. (List.replicate n (unpack zt))) [] (. [(.REF none (._IDX x))]))
  | array.new_elem : forall (C : context) (x : idx) (y : idx) (mut? : (Option «mut»)) (rt : reftype), 
    (wf_context C) ->
    (wf_instr (.ARRAY.NEW_ELEM x y)) ->
    (wf_instrtype (. (. [.I32, .I32]) [] (. [(.REF none (._IDX x))]))) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) (storagetype_reftype rt)))) ->
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) (storagetype_reftype rt)))) ->
    ((proj_uN_0 y) < (List.length (C.ELEMS))) ->
    (Reftype_sub C ((C.ELEMS)[(proj_uN_0 y)]!) rt) ->
    Instr_ok C (.ARRAY.NEW_ELEM x y) (. (. [.I32, .I32]) [] (. [(.REF none (._IDX x))]))
  | array.new_data : forall (C : context) (x : idx) (y : idx) (mut? : (Option «mut»)) (zt : storagetype) (numtype : numtype) (vectype : vectype), 
    (wf_context C) ->
    (wf_instr (.ARRAY.NEW_DATA x y)) ->
    (wf_instrtype (. (. [.I32, .I32]) [] (. [(.REF none (._IDX x))]))) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    (((unpack zt) == (valtype_numtype numtype)) || ((unpack zt) == (valtype_vectype vectype))) ->
    ((proj_uN_0 y) < (List.length (C.DATAS))) ->
    (((C.DATAS)[(proj_uN_0 y)]!) == .OK) ->
    Instr_ok C (.ARRAY.NEW_DATA x y) (. (. [.I32, .I32]) [] (. [(.REF none (._IDX x))]))
  | array.get : forall (C : context) (sx? : (Option sx)) (x : idx) (zt : storagetype) (mut? : (Option «mut»)), 
    (wf_context C) ->
    (wf_instr (.ARRAY.GET (Option.map (fun (sx : sx) => sx) sx?) x)) ->
    (wf_instrtype (. (. [(.REF (some .NULL) (._IDX x)), .I32]) [] (. [(unpack zt)]))) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    (((Option.map (fun (sx : sx) => sx) sx?) == none) <-> (is_packtype zt)) ->
    Instr_ok C (.ARRAY.GET (Option.map (fun (sx : sx) => sx) sx?) x) (. (. [(.REF (some .NULL) (._IDX x)), .I32]) [] (. [(unpack zt)]))
  | array.set : forall (C : context) (x : idx) (zt : storagetype), 
    (wf_context C) ->
    (wf_instr (.ARRAY.SET x)) ->
    (wf_instrtype (. (. [(.REF (some .NULL) (._IDX x)), .I32, (unpack zt)]) [] (. []))) ->
    (wf_comptype (.ARRAY (. (some .MUT) zt))) ->
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (. (some .MUT) zt))) ->
    Instr_ok C (.ARRAY.SET x) (. (. [(.REF (some .NULL) (._IDX x)), .I32, (unpack zt)]) [] (. []))
  | array.len : forall (C : context), 
    (wf_context C) ->
    (wf_instr .ARRAY.LEN) ->
    (wf_instrtype (. (. [(.REF (some .NULL) .ARRAY)]) [] (. [.I32]))) ->
    Instr_ok C .ARRAY.LEN (. (. [(.REF (some .NULL) .ARRAY)]) [] (. [.I32]))
  | array.fill : forall (C : context) (x : idx) (zt : storagetype), 
    (wf_context C) ->
    (wf_instr (.ARRAY.FILL x)) ->
    (wf_instrtype (. (. [(.REF (some .NULL) (._IDX x)), .I32, (unpack zt), .I32]) [] (. []))) ->
    (wf_comptype (.ARRAY (. (some .MUT) zt))) ->
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (. (some .MUT) zt))) ->
    Instr_ok C (.ARRAY.FILL x) (. (. [(.REF (some .NULL) (._IDX x)), .I32, (unpack zt), .I32]) [] (. []))
  | array.copy : forall (C : context) (x_1 : idx) (x_2 : idx) (zt_1 : storagetype) (mut? : (Option «mut»)) (zt_2 : storagetype), 
    (wf_context C) ->
    (wf_instr (.ARRAY.COPY x_1 x_2)) ->
    (wf_instrtype (. (. [(.REF (some .NULL) (._IDX x_1)), .I32, (.REF (some .NULL) (._IDX x_2)), .I32, .I32]) [] (. []))) ->
    (wf_comptype (.ARRAY (. (some .MUT) zt_1))) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt_2))) ->
    ((proj_uN_0 x_1) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x_1)]!) (.ARRAY (. (some .MUT) zt_1))) ->
    ((proj_uN_0 x_2) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x_2)]!) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt_2))) ->
    (Storagetype_sub C zt_2 zt_1) ->
    Instr_ok C (.ARRAY.COPY x_1 x_2) (. (. [(.REF (some .NULL) (._IDX x_1)), .I32, (.REF (some .NULL) (._IDX x_2)), .I32, .I32]) [] (. []))
  | array.init_elem : forall (C : context) (x : idx) (y : idx) (zt : storagetype), 
    (wf_context C) ->
    (wf_instr (.ARRAY.INIT_ELEM x y)) ->
    (wf_instrtype (. (. [(.REF (some .NULL) (._IDX x)), .I32, .I32, .I32]) [] (. []))) ->
    (wf_comptype (.ARRAY (. (some .MUT) zt))) ->
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (. (some .MUT) zt))) ->
    ((proj_uN_0 y) < (List.length (C.ELEMS))) ->
    (Storagetype_sub C (storagetype_reftype ((C.ELEMS)[(proj_uN_0 y)]!)) zt) ->
    Instr_ok C (.ARRAY.INIT_ELEM x y) (. (. [(.REF (some .NULL) (._IDX x)), .I32, .I32, .I32]) [] (. []))
  | array.init_data : forall (C : context) (x : idx) (y : idx) (zt : storagetype) (numtype : numtype) (vectype : vectype), 
    (wf_context C) ->
    (wf_instr (.ARRAY.INIT_DATA x y)) ->
    (wf_instrtype (. (. [(.REF (some .NULL) (._IDX x)), .I32, .I32, .I32]) [] (. []))) ->
    (wf_comptype (.ARRAY (. (some .MUT) zt))) ->
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (. (some .MUT) zt))) ->
    (((unpack zt) == (valtype_numtype numtype)) || ((unpack zt) == (valtype_vectype vectype))) ->
    ((proj_uN_0 y) < (List.length (C.DATAS))) ->
    (((C.DATAS)[(proj_uN_0 y)]!) == .OK) ->
    Instr_ok C (.ARRAY.INIT_DATA x y) (. (. [(.REF (some .NULL) (._IDX x)), .I32, .I32, .I32]) [] (. []))
  | extern.convert_any : forall (C : context) (null_1? : (Option null)) (null_2? : (Option null)), 
    (wf_context C) ->
    (wf_instr .EXTERN.CONVERT_ANY) ->
    (wf_instrtype (. (. [(.REF (Option.map (fun (null_1 : null) => null_1) null_1?) .ANY)]) [] (. [(.REF (Option.map (fun (null_2 : null) => null_2) null_2?) .EXTERN)]))) ->
    ((Option.map (fun (null_1 : null) => null_1) null_1?) == (Option.map (fun (null_2 : null) => null_2) null_2?)) ->
    Instr_ok C .EXTERN.CONVERT_ANY (. (. [(.REF (Option.map (fun (null_1 : null) => null_1) null_1?) .ANY)]) [] (. [(.REF (Option.map (fun (null_2 : null) => null_2) null_2?) .EXTERN)]))
  | any.convert_extern : forall (C : context) (null_1? : (Option null)) (null_2? : (Option null)), 
    (wf_context C) ->
    (wf_instr .ANY.CONVERT_EXTERN) ->
    (wf_instrtype (. (. [(.REF (Option.map (fun (null_1 : null) => null_1) null_1?) .EXTERN)]) [] (. [(.REF (Option.map (fun (null_2 : null) => null_2) null_2?) .ANY)]))) ->
    ((Option.map (fun (null_1 : null) => null_1) null_1?) == (Option.map (fun (null_2 : null) => null_2) null_2?)) ->
    Instr_ok C .ANY.CONVERT_EXTERN (. (. [(.REF (Option.map (fun (null_1 : null) => null_1) null_1?) .EXTERN)]) [] (. [(.REF (Option.map (fun (null_2 : null) => null_2) null_2?) .ANY)]))
  | local.get : forall (C : context) (x : idx) (t : valtype), 
    (wf_context C) ->
    (wf_instr (.LOCAL.GET x)) ->
    (wf_instrtype (. (. []) [] (. [t]))) ->
    (wf_localtype (. .SET t)) ->
    ((proj_uN_0 x) < (List.length (C.LOCALS))) ->
    (((C.LOCALS)[(proj_uN_0 x)]!) == (. .SET t)) ->
    Instr_ok C (.LOCAL.GET x) (. (. []) [] (. [t]))
  | local.set : forall (C : context) (x : idx) (t : valtype) (init : init), 
    (wf_context C) ->
    (wf_instr (.LOCAL.SET x)) ->
    (wf_instrtype (. (. [t]) [x] (. []))) ->
    (wf_localtype (. init t)) ->
    ((proj_uN_0 x) < (List.length (C.LOCALS))) ->
    (((C.LOCALS)[(proj_uN_0 x)]!) == (. init t)) ->
    Instr_ok C (.LOCAL.SET x) (. (. [t]) [x] (. []))
  | local.tee : forall (C : context) (x : idx) (t : valtype) (init : init), 
    (wf_context C) ->
    (wf_instr (.LOCAL.TEE x)) ->
    (wf_instrtype (. (. [t]) [x] (. [t]))) ->
    (wf_localtype (. init t)) ->
    ((proj_uN_0 x) < (List.length (C.LOCALS))) ->
    (((C.LOCALS)[(proj_uN_0 x)]!) == (. init t)) ->
    Instr_ok C (.LOCAL.TEE x) (. (. [t]) [x] (. [t]))
  | global.get : forall (C : context) (x : idx) (t : valtype) (mut? : (Option «mut»)), 
    (wf_context C) ->
    (wf_instr (.GLOBAL.GET x)) ->
    (wf_instrtype (. (. []) [] (. [t]))) ->
    (wf_globaltype (. (Option.map (fun (mut : «mut») => «mut») mut?) t)) ->
    ((proj_uN_0 x) < (List.length (C.GLOBALS))) ->
    (((C.GLOBALS)[(proj_uN_0 x)]!) == (. (Option.map (fun (mut : «mut») => «mut») mut?) t)) ->
    Instr_ok C (.GLOBAL.GET x) (. (. []) [] (. [t]))
  | global.set : forall (C : context) (x : idx) (t : valtype), 
    (wf_context C) ->
    (wf_instr (.GLOBAL.SET x)) ->
    (wf_instrtype (. (. [t]) [] (. []))) ->
    (wf_globaltype (. (some .MUT) t)) ->
    ((proj_uN_0 x) < (List.length (C.GLOBALS))) ->
    (((C.GLOBALS)[(proj_uN_0 x)]!) == (. (some .MUT) t)) ->
    Instr_ok C (.GLOBAL.SET x) (. (. [t]) [] (. []))
  | table.get : forall (C : context) (x : idx) (at : addrtype) (rt : reftype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.TABLE.GET x)) ->
    (wf_instrtype (. (. [(valtype_addrtype at)]) [] (. [(valtype_reftype rt)]))) ->
    (wf_tabletype (. at lim rt)) ->
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (. at lim rt)) ->
    Instr_ok C (.TABLE.GET x) (. (. [(valtype_addrtype at)]) [] (. [(valtype_reftype rt)]))
  | table.set : forall (C : context) (x : idx) (at : addrtype) (rt : reftype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.TABLE.SET x)) ->
    (wf_instrtype (. (. [(valtype_addrtype at), (valtype_reftype rt)]) [] (. []))) ->
    (wf_tabletype (. at lim rt)) ->
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (. at lim rt)) ->
    Instr_ok C (.TABLE.SET x) (. (. [(valtype_addrtype at), (valtype_reftype rt)]) [] (. []))
  | table.size : forall (C : context) (x : idx) (at : addrtype) (lim : limits) (rt : reftype), 
    (wf_context C) ->
    (wf_instr (.TABLE.SIZE x)) ->
    (wf_instrtype (. (. []) [] (. [(valtype_addrtype at)]))) ->
    (wf_tabletype (. at lim rt)) ->
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (. at lim rt)) ->
    Instr_ok C (.TABLE.SIZE x) (. (. []) [] (. [(valtype_addrtype at)]))
  | table.grow : forall (C : context) (x : idx) (rt : reftype) (at : addrtype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.TABLE.GROW x)) ->
    (wf_instrtype (. (. [(valtype_reftype rt), (valtype_addrtype at)]) [] (. [.I32]))) ->
    (wf_tabletype (. at lim rt)) ->
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (. at lim rt)) ->
    Instr_ok C (.TABLE.GROW x) (. (. [(valtype_reftype rt), (valtype_addrtype at)]) [] (. [.I32]))
  | table.fill : forall (C : context) (x : idx) (at : addrtype) (rt : reftype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.TABLE.FILL x)) ->
    (wf_instrtype (. (. [(valtype_addrtype at), (valtype_reftype rt), (valtype_addrtype at)]) [] (. []))) ->
    (wf_tabletype (. at lim rt)) ->
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (. at lim rt)) ->
    Instr_ok C (.TABLE.FILL x) (. (. [(valtype_addrtype at), (valtype_reftype rt), (valtype_addrtype at)]) [] (. []))
  | table.copy : forall (C : context) (x_1 : idx) (x_2 : idx) (at_1 : addrtype) (at_2 : addrtype) (lim_1 : limits) (rt_1 : reftype) (lim_2 : limits) (rt_2 : reftype), 
    (wf_context C) ->
    (wf_instr (.TABLE.COPY x_1 x_2)) ->
    (wf_instrtype (. (. [(valtype_addrtype at_1), (valtype_addrtype at_2), (valtype_addrtype (minat at_1 at_2))]) [] (. []))) ->
    (wf_tabletype (. at_1 lim_1 rt_1)) ->
    (wf_tabletype (. at_2 lim_2 rt_2)) ->
    ((proj_uN_0 x_1) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x_1)]!) == (. at_1 lim_1 rt_1)) ->
    ((proj_uN_0 x_2) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x_2)]!) == (. at_2 lim_2 rt_2)) ->
    (Reftype_sub C rt_2 rt_1) ->
    Instr_ok C (.TABLE.COPY x_1 x_2) (. (. [(valtype_addrtype at_1), (valtype_addrtype at_2), (valtype_addrtype (minat at_1 at_2))]) [] (. []))
  | table.init : forall (C : context) (x : idx) (y : idx) (at : addrtype) (lim : limits) (rt_1 : reftype) (rt_2 : reftype), 
    (wf_context C) ->
    (wf_reftype rt_2) ->
    (wf_instr (.TABLE.INIT x y)) ->
    (wf_instrtype (. (. [(valtype_addrtype at), .I32, .I32]) [] (. []))) ->
    (wf_tabletype (. at lim rt_1)) ->
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (. at lim rt_1)) ->
    ((proj_uN_0 y) < (List.length (C.ELEMS))) ->
    (((C.ELEMS)[(proj_uN_0 y)]!) == rt_2) ->
    (Reftype_sub C rt_2 rt_1) ->
    Instr_ok C (.TABLE.INIT x y) (. (. [(valtype_addrtype at), .I32, .I32]) [] (. []))
  | elem.drop : forall (C : context) (x : idx) (rt : reftype), 
    (wf_context C) ->
    (wf_reftype rt) ->
    (wf_instr (.ELEM.DROP x)) ->
    (wf_instrtype (. (. []) [] (. []))) ->
    ((proj_uN_0 x) < (List.length (C.ELEMS))) ->
    (((C.ELEMS)[(proj_uN_0 x)]!) == rt) ->
    Instr_ok C (.ELEM.DROP x) (. (. []) [] (. []))
  | memory.size : forall (C : context) (x : idx) (at : addrtype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.MEMORY.SIZE x)) ->
    (wf_instrtype (. (. []) [] (. [(valtype_addrtype at)]))) ->
    (wf_memtype (.PAGE at lim)) ->
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE at lim)) ->
    Instr_ok C (.MEMORY.SIZE x) (. (. []) [] (. [(valtype_addrtype at)]))
  | memory.grow : forall (C : context) (x : idx) (at : addrtype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.MEMORY.GROW x)) ->
    (wf_instrtype (. (. [(valtype_addrtype at)]) [] (. [(valtype_addrtype at)]))) ->
    (wf_memtype (.PAGE at lim)) ->
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE at lim)) ->
    Instr_ok C (.MEMORY.GROW x) (. (. [(valtype_addrtype at)]) [] (. [(valtype_addrtype at)]))
  | memory.fill : forall (C : context) (x : idx) (at : addrtype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.MEMORY.FILL x)) ->
    (wf_instrtype (. (. [(valtype_addrtype at), .I32, (valtype_addrtype at)]) [] (. []))) ->
    (wf_memtype (.PAGE at lim)) ->
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE at lim)) ->
    Instr_ok C (.MEMORY.FILL x) (. (. [(valtype_addrtype at), .I32, (valtype_addrtype at)]) [] (. []))
  | memory.copy : forall (C : context) (x_1 : idx) (x_2 : idx) (at_1 : addrtype) (at_2 : addrtype) (lim_1 : limits) (lim_2 : limits), 
    (wf_context C) ->
    (wf_instr (.MEMORY.COPY x_1 x_2)) ->
    (wf_instrtype (. (. [(valtype_addrtype at_1), (valtype_addrtype at_2), (valtype_addrtype (minat at_1 at_2))]) [] (. []))) ->
    (wf_memtype (.PAGE at_1 lim_1)) ->
    (wf_memtype (.PAGE at_2 lim_2)) ->
    ((proj_uN_0 x_1) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x_1)]!) == (.PAGE at_1 lim_1)) ->
    ((proj_uN_0 x_2) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x_2)]!) == (.PAGE at_2 lim_2)) ->
    Instr_ok C (.MEMORY.COPY x_1 x_2) (. (. [(valtype_addrtype at_1), (valtype_addrtype at_2), (valtype_addrtype (minat at_1 at_2))]) [] (. []))
  | memory.init : forall (C : context) (x : idx) (y : idx) (at : addrtype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.MEMORY.INIT x y)) ->
    (wf_instrtype (. (. [(valtype_addrtype at), .I32, .I32]) [] (. []))) ->
    (wf_memtype (.PAGE at lim)) ->
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE at lim)) ->
    ((proj_uN_0 y) < (List.length (C.DATAS))) ->
    (((C.DATAS)[(proj_uN_0 y)]!) == .OK) ->
    Instr_ok C (.MEMORY.INIT x y) (. (. [(valtype_addrtype at), .I32, .I32]) [] (. []))
  | data.drop : forall (C : context) (x : idx), 
    (wf_context C) ->
    (wf_instr (.DATA.DROP x)) ->
    (wf_instrtype (. (. []) [] (. []))) ->
    ((proj_uN_0 x) < (List.length (C.DATAS))) ->
    (((C.DATAS)[(proj_uN_0 x)]!) == .OK) ->
    Instr_ok C (.DATA.DROP x) (. (. []) [] (. []))
  | load-val : forall (C : context) (nt : numtype) (x : idx) (memarg : memarg) (at : addrtype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.LOAD nt none x memarg)) ->
    (wf_instrtype (. (. [(valtype_addrtype at)]) [] (. [(valtype_numtype nt)]))) ->
    (wf_memtype (.PAGE at lim)) ->
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE at lim)) ->
    (((2 ^ (proj_uN_0 (memarg.ALIGN))) : Nat) <= (((size nt) : Nat) / (8 : Nat))) ->
    Instr_ok C (.LOAD nt none x memarg) (. (. [(valtype_addrtype at)]) [] (. [(valtype_numtype nt)]))
  | load-pack : forall (C : context) (Inn : Inn) (M : M) (sx : sx) (x : idx) (memarg : memarg) (at : addrtype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.LOAD (numtype_addrtype Inn) (some (.mk_loadop__0 Inn (._ (. M) sx))) x memarg)) ->
    (wf_instrtype (. (. [(valtype_addrtype at)]) [] (. [(valtype_addrtype Inn)]))) ->
    (wf_memtype (.PAGE at lim)) ->
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE at lim)) ->
    (((2 ^ (proj_uN_0 (memarg.ALIGN))) : Nat) <= ((M : Nat) / (8 : Nat))) ->
    Instr_ok C (.LOAD (numtype_addrtype Inn) (some (.mk_loadop__0 Inn (._ (. M) sx))) x memarg) (. (. [(valtype_addrtype at)]) [] (. [(valtype_addrtype Inn)]))
  | store-val : forall (C : context) (nt : numtype) (x : idx) (memarg : memarg) (at : addrtype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.STORE nt none x memarg)) ->
    (wf_instrtype (. (. [(valtype_addrtype at), (valtype_numtype nt)]) [] (. []))) ->
    (wf_memtype (.PAGE at lim)) ->
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE at lim)) ->
    (((2 ^ (proj_uN_0 (memarg.ALIGN))) : Nat) <= (((size nt) : Nat) / (8 : Nat))) ->
    Instr_ok C (.STORE nt none x memarg) (. (. [(valtype_addrtype at), (valtype_numtype nt)]) [] (. []))
  | store-pack : forall (C : context) (Inn : Inn) (M : M) (x : idx) (memarg : memarg) (at : addrtype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.STORE (numtype_addrtype Inn) (some (.mk_storeop__0 Inn (. (. M)))) x memarg)) ->
    (wf_instrtype (. (. [(valtype_addrtype at), (valtype_addrtype Inn)]) [] (. []))) ->
    (wf_memtype (.PAGE at lim)) ->
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE at lim)) ->
    (((2 ^ (proj_uN_0 (memarg.ALIGN))) : Nat) <= ((M : Nat) / (8 : Nat))) ->
    Instr_ok C (.STORE (numtype_addrtype Inn) (some (.mk_storeop__0 Inn (. (. M)))) x memarg) (. (. [(valtype_addrtype at), (valtype_addrtype Inn)]) [] (. []))
  | vload-val : forall (C : context) (x : idx) (memarg : memarg) (at : addrtype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.VLOAD .V128 none x memarg)) ->
    (wf_instrtype (. (. [(valtype_addrtype at)]) [] (. [.V128]))) ->
    (wf_memtype (.PAGE at lim)) ->
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE at lim)) ->
    (((2 ^ (proj_uN_0 (memarg.ALIGN))) : Nat) <= (((vsize .V128) : Nat) / (8 : Nat))) ->
    Instr_ok C (.VLOAD .V128 none x memarg) (. (. [(valtype_addrtype at)]) [] (. [.V128]))
  | vload-pack : forall (C : context) (M : M) (N : N) (sx : sx) (x : idx) (memarg : memarg) (at : addrtype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.VLOAD .V128 (some (.SHAPEX_ (. M) N sx)) x memarg)) ->
    (wf_instrtype (. (. [(valtype_addrtype at)]) [] (. [.V128]))) ->
    (wf_memtype (.PAGE at lim)) ->
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE at lim)) ->
    (((2 ^ (proj_uN_0 (memarg.ALIGN))) : Nat) <= (((M : Nat) / (8 : Nat)) * (N : Nat))) ->
    Instr_ok C (.VLOAD .V128 (some (.SHAPEX_ (. M) N sx)) x memarg) (. (. [(valtype_addrtype at)]) [] (. [.V128]))
  | vload-splat : forall (C : context) (N : N) (x : idx) (memarg : memarg) (at : addrtype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.VLOAD .V128 (some (.SPLAT (. N))) x memarg)) ->
    (wf_instrtype (. (. [(valtype_addrtype at)]) [] (. [.V128]))) ->
    (wf_memtype (.PAGE at lim)) ->
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE at lim)) ->
    (((2 ^ (proj_uN_0 (memarg.ALIGN))) : Nat) <= ((N : Nat) / (8 : Nat))) ->
    Instr_ok C (.VLOAD .V128 (some (.SPLAT (. N))) x memarg) (. (. [(valtype_addrtype at)]) [] (. [.V128]))
  | vload-zero : forall (C : context) (N : N) (x : idx) (memarg : memarg) (at : addrtype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.VLOAD .V128 (some (.ZERO (. N))) x memarg)) ->
    (wf_instrtype (. (. [(valtype_addrtype at)]) [] (. [.V128]))) ->
    (wf_memtype (.PAGE at lim)) ->
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE at lim)) ->
    (((2 ^ (proj_uN_0 (memarg.ALIGN))) : Nat) <= ((N : Nat) / (8 : Nat))) ->
    Instr_ok C (.VLOAD .V128 (some (.ZERO (. N))) x memarg) (. (. [(valtype_addrtype at)]) [] (. [.V128]))
  | vload_lane : forall (C : context) (N : N) (x : idx) (memarg : memarg) (i : laneidx) (at : addrtype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.VLOAD_LANE .V128 (. N) x memarg i)) ->
    (wf_instrtype (. (. [(valtype_addrtype at), .V128]) [] (. [.V128]))) ->
    (wf_memtype (.PAGE at lim)) ->
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE at lim)) ->
    (((2 ^ (proj_uN_0 (memarg.ALIGN))) : Nat) <= ((N : Nat) / (8 : Nat))) ->
    (((proj_uN_0 i) : Nat) < ((128 : Nat) / (N : Nat))) ->
    Instr_ok C (.VLOAD_LANE .V128 (. N) x memarg i) (. (. [(valtype_addrtype at), .V128]) [] (. [.V128]))
  | vstore : forall (C : context) (x : idx) (memarg : memarg) (at : addrtype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.VSTORE .V128 x memarg)) ->
    (wf_instrtype (. (. [(valtype_addrtype at), .V128]) [] (. []))) ->
    (wf_memtype (.PAGE at lim)) ->
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE at lim)) ->
    (((2 ^ (proj_uN_0 (memarg.ALIGN))) : Nat) <= (((vsize .V128) : Nat) / (8 : Nat))) ->
    Instr_ok C (.VSTORE .V128 x memarg) (. (. [(valtype_addrtype at), .V128]) [] (. []))
  | vstore_lane : forall (C : context) (N : N) (x : idx) (memarg : memarg) (i : laneidx) (at : addrtype) (lim : limits), 
    (wf_context C) ->
    (wf_instr (.VSTORE_LANE .V128 (. N) x memarg i)) ->
    (wf_instrtype (. (. [(valtype_addrtype at), .V128]) [] (. []))) ->
    (wf_memtype (.PAGE at lim)) ->
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE at lim)) ->
    (((2 ^ (proj_uN_0 (memarg.ALIGN))) : Nat) <= ((N : Nat) / (8 : Nat))) ->
    (((proj_uN_0 i) : Nat) < ((128 : Nat) / (N : Nat))) ->
    Instr_ok C (.VSTORE_LANE .V128 (. N) x memarg i) (. (. [(valtype_addrtype at), .V128]) [] (. []))
  | const : forall (C : context) (nt : numtype) (c_nt : num_), 
    (wf_context C) ->
    (wf_instr (.CONST nt c_nt)) ->
    (wf_instrtype (. (. []) [] (. [(valtype_numtype nt)]))) ->
    Instr_ok C (.CONST nt c_nt) (. (. []) [] (. [(valtype_numtype nt)]))
  | unop : forall (C : context) (nt : numtype) (unop_nt : unop_), 
    (wf_context C) ->
    (wf_instr (.UNOP nt unop_nt)) ->
    (wf_instrtype (. (. [(valtype_numtype nt)]) [] (. [(valtype_numtype nt)]))) ->
    Instr_ok C (.UNOP nt unop_nt) (. (. [(valtype_numtype nt)]) [] (. [(valtype_numtype nt)]))
  | binop : forall (C : context) (nt : numtype) (binop_nt : binop_), 
    (wf_context C) ->
    (wf_instr (.BINOP nt binop_nt)) ->
    (wf_instrtype (. (. [(valtype_numtype nt), (valtype_numtype nt)]) [] (. [(valtype_numtype nt)]))) ->
    Instr_ok C (.BINOP nt binop_nt) (. (. [(valtype_numtype nt), (valtype_numtype nt)]) [] (. [(valtype_numtype nt)]))
  | testop : forall (C : context) (nt : numtype) (testop_nt : testop_), 
    (wf_context C) ->
    (wf_instr (.TESTOP nt testop_nt)) ->
    (wf_instrtype (. (. [(valtype_numtype nt)]) [] (. [.I32]))) ->
    Instr_ok C (.TESTOP nt testop_nt) (. (. [(valtype_numtype nt)]) [] (. [.I32]))
  | relop : forall (C : context) (nt : numtype) (relop_nt : relop_), 
    (wf_context C) ->
    (wf_instr (.RELOP nt relop_nt)) ->
    (wf_instrtype (. (. [(valtype_numtype nt), (valtype_numtype nt)]) [] (. [.I32]))) ->
    Instr_ok C (.RELOP nt relop_nt) (. (. [(valtype_numtype nt), (valtype_numtype nt)]) [] (. [.I32]))
  | cvtop : forall (C : context) (nt_1 : numtype) (nt_2 : numtype) (cvtop : cvtop__), 
    (wf_context C) ->
    (wf_instr (.CVTOP nt_1 nt_2 cvtop)) ->
    (wf_instrtype (. (. [(valtype_numtype nt_2)]) [] (. [(valtype_numtype nt_1)]))) ->
    Instr_ok C (.CVTOP nt_1 nt_2 cvtop) (. (. [(valtype_numtype nt_2)]) [] (. [(valtype_numtype nt_1)]))
  | vconst : forall (C : context) (c : vec_), 
    (wf_context C) ->
    (wf_instr (.VCONST .V128 c)) ->
    (wf_instrtype (. (. []) [] (. [.V128]))) ->
    Instr_ok C (.VCONST .V128 c) (. (. []) [] (. [.V128]))
  | vvunop : forall (C : context) (vvunop : vvunop), 
    (wf_context C) ->
    (wf_instr (.VVUNOP .V128 vvunop)) ->
    (wf_instrtype (. (. [.V128]) [] (. [.V128]))) ->
    Instr_ok C (.VVUNOP .V128 vvunop) (. (. [.V128]) [] (. [.V128]))
  | vvbinop : forall (C : context) (vvbinop : vvbinop), 
    (wf_context C) ->
    (wf_instr (.VVBINOP .V128 vvbinop)) ->
    (wf_instrtype (. (. [.V128, .V128]) [] (. [.V128]))) ->
    Instr_ok C (.VVBINOP .V128 vvbinop) (. (. [.V128, .V128]) [] (. [.V128]))
  | vvternop : forall (C : context) (vvternop : vvternop), 
    (wf_context C) ->
    (wf_instr (.VVTERNOP .V128 vvternop)) ->
    (wf_instrtype (. (. [.V128, .V128, .V128]) [] (. [.V128]))) ->
    Instr_ok C (.VVTERNOP .V128 vvternop) (. (. [.V128, .V128, .V128]) [] (. [.V128]))
  | vvtestop : forall (C : context) (vvtestop : vvtestop), 
    (wf_context C) ->
    (wf_instr (.VVTESTOP .V128 vvtestop)) ->
    (wf_instrtype (. (. [.V128]) [] (. [.I32]))) ->
    Instr_ok C (.VVTESTOP .V128 vvtestop) (. (. [.V128]) [] (. [.I32]))
  | vunop : forall (C : context) (sh : shape) (vunop : vunop_), 
    (wf_context C) ->
    (wf_instr (.VUNOP sh vunop)) ->
    (wf_instrtype (. (. [.V128]) [] (. [.V128]))) ->
    Instr_ok C (.VUNOP sh vunop) (. (. [.V128]) [] (. [.V128]))
  | vbinop : forall (C : context) (sh : shape) (vbinop : vbinop_), 
    (wf_context C) ->
    (wf_instr (.VBINOP sh vbinop)) ->
    (wf_instrtype (. (. [.V128, .V128]) [] (. [.V128]))) ->
    Instr_ok C (.VBINOP sh vbinop) (. (. [.V128, .V128]) [] (. [.V128]))
  | vternop : forall (C : context) (sh : shape) (vternop : vternop_), 
    (wf_context C) ->
    (wf_instr (.VTERNOP sh vternop)) ->
    (wf_instrtype (. (. [.V128, .V128, .V128]) [] (. [.V128]))) ->
    Instr_ok C (.VTERNOP sh vternop) (. (. [.V128, .V128, .V128]) [] (. [.V128]))
  | vtestop : forall (C : context) (sh : shape) (vtestop : vtestop_), 
    (wf_context C) ->
    (wf_instr (.VTESTOP sh vtestop)) ->
    (wf_instrtype (. (. [.V128]) [] (. [.I32]))) ->
    Instr_ok C (.VTESTOP sh vtestop) (. (. [.V128]) [] (. [.I32]))
  | vrelop : forall (C : context) (sh : shape) (vrelop : vrelop_), 
    (wf_context C) ->
    (wf_instr (.VRELOP sh vrelop)) ->
    (wf_instrtype (. (. [.V128, .V128]) [] (. [.V128]))) ->
    Instr_ok C (.VRELOP sh vrelop) (. (. [.V128, .V128]) [] (. [.V128]))
  | vshiftop : forall (C : context) (sh : ishape) (vshiftop : vshiftop_), 
    (wf_context C) ->
    (wf_instr (.VSHIFTOP sh vshiftop)) ->
    (wf_instrtype (. (. [.V128, .I32]) [] (. [.V128]))) ->
    Instr_ok C (.VSHIFTOP sh vshiftop) (. (. [.V128, .I32]) [] (. [.V128]))
  | vbitmask : forall (C : context) (sh : ishape), 
    (wf_context C) ->
    (wf_instr (.VBITMASK sh)) ->
    (wf_instrtype (. (. [.V128]) [] (. [.I32]))) ->
    Instr_ok C (.VBITMASK sh) (. (. [.V128]) [] (. [.I32]))
  | vswizzlop : forall (C : context) (sh : bshape) (vswizzlop : vswizzlop_), 
    (wf_context C) ->
    (wf_instr (.VSWIZZLOP sh vswizzlop)) ->
    (wf_instrtype (. (. [.V128, .V128]) [] (. [.V128]))) ->
    Instr_ok C (.VSWIZZLOP sh vswizzlop) (. (. [.V128, .V128]) [] (. [.V128]))
  | vshuffle : forall (C : context) (sh : bshape) (i* : (List laneidx)), 
    (wf_context C) ->
    (wf_instr (.VSHUFFLE sh (List.map (fun (i : laneidx) => i) i*))) ->
    (wf_instrtype (. (. [.V128, .V128]) [] (. [.V128]))) ->
    Forall (fun (i : laneidx) => ((proj_uN_0 i) < (2 * (proj_dim_0 (dim (proj_bshape_0 sh)))))) i* ->
    Instr_ok C (.VSHUFFLE sh (List.map (fun (i : laneidx) => i) i*)) (. (. [.V128, .V128]) [] (. [.V128]))
  | vsplat : forall (C : context) (sh : shape), 
    (wf_context C) ->
    (wf_instr (.VSPLAT sh)) ->
    (wf_instrtype (. (. [(valtype_numtype (unpackshape sh))]) [] (. [.V128]))) ->
    Instr_ok C (.VSPLAT sh) (. (. [(valtype_numtype (unpackshape sh))]) [] (. [.V128]))
  | vextract_lane : forall (C : context) (sh : shape) (sx? : (Option sx)) (i : laneidx), 
    (wf_context C) ->
    (wf_instr (.VEXTRACT_LANE sh (Option.map (fun (sx : sx) => sx) sx?) i)) ->
    (wf_instrtype (. (. [.V128]) [] (. [(valtype_numtype (unpackshape sh))]))) ->
    ((proj_uN_0 i) < (proj_dim_0 (dim sh))) ->
    Instr_ok C (.VEXTRACT_LANE sh (Option.map (fun (sx : sx) => sx) sx?) i) (. (. [.V128]) [] (. [(valtype_numtype (unpackshape sh))]))
  | vreplace_lane : forall (C : context) (sh : shape) (i : laneidx), 
    (wf_context C) ->
    (wf_instr (.VREPLACE_LANE sh i)) ->
    (wf_instrtype (. (. [.V128, (valtype_numtype (unpackshape sh))]) [] (. [.V128]))) ->
    ((proj_uN_0 i) < (proj_dim_0 (dim sh))) ->
    Instr_ok C (.VREPLACE_LANE sh i) (. (. [.V128, (valtype_numtype (unpackshape sh))]) [] (. [.V128]))
  | vextunop : forall (C : context) (sh_1 : ishape) (sh_2 : ishape) (vextunop : vextunop__), 
    (wf_context C) ->
    (wf_instr (.VEXTUNOP sh_1 sh_2 vextunop)) ->
    (wf_instrtype (. (. [.V128]) [] (. [.V128]))) ->
    Instr_ok C (.VEXTUNOP sh_1 sh_2 vextunop) (. (. [.V128]) [] (. [.V128]))
  | vextbinop : forall (C : context) (sh_1 : ishape) (sh_2 : ishape) (vextbinop : vextbinop__), 
    (wf_context C) ->
    (wf_instr (.VEXTBINOP sh_1 sh_2 vextbinop)) ->
    (wf_instrtype (. (. [.V128, .V128]) [] (. [.V128]))) ->
    Instr_ok C (.VEXTBINOP sh_1 sh_2 vextbinop) (. (. [.V128, .V128]) [] (. [.V128]))
  | vextternop : forall (C : context) (sh_1 : ishape) (sh_2 : ishape) (vextternop : vextternop__), 
    (wf_context C) ->
    (wf_instr (.VEXTTERNOP sh_1 sh_2 vextternop)) ->
    (wf_instrtype (. (. [.V128, .V128, .V128]) [] (. [.V128]))) ->
    Instr_ok C (.VEXTTERNOP sh_1 sh_2 vextternop) (. (. [.V128, .V128, .V128]) [] (. [.V128]))
  | vnarrow : forall (C : context) (sh_1 : ishape) (sh_2 : ishape) (sx : sx), 
    (wf_context C) ->
    (wf_instr (.VNARROW sh_1 sh_2 sx)) ->
    (wf_instrtype (. (. [.V128, .V128]) [] (. [.V128]))) ->
    Instr_ok C (.VNARROW sh_1 sh_2 sx) (. (. [.V128, .V128]) [] (. [.V128]))
  | vcvtop : forall (C : context) (sh_1 : shape) (sh_2 : shape) (vcvtop : vcvtop__), 
    (wf_context C) ->
    (wf_instr (.VCVTOP sh_1 sh_2 vcvtop)) ->
    (wf_instrtype (. (. [.V128]) [] (. [.V128]))) ->
    Instr_ok C (.VCVTOP sh_1 sh_2 vcvtop) (. (. [.V128]) [] (. [.V128]))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:6.1-6.96 -/
inductive Instrs_ok : context -> (List instr) -> instrtype -> Prop where
  | empty : forall (C : context), 
    (wf_context C) ->
    (wf_instrtype (. (. []) [] (. []))) ->
    Instrs_ok C [] (. (. []) [] (. []))
  | seq : forall (C : context) (instr_1 : instr) (instr_2* : (List instr)) (t_1* : (List valtype)) (x_1* : (List idx)) (x_2* : (List idx)) (t_3* : (List valtype)) (t_2* : (List valtype)) (init* : (List init)) (t* : (List valtype)), 
    (wf_context C) ->
    (wf_instr instr_1) ->
    Forall (fun (instr_2 : instr) => (wf_instr instr_2)) instr_2* ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) ((List.map (fun (x_1 : idx) => x_1) x_1*) ++ (List.map (fun (x_2 : idx) => x_2) x_2*)) (. (List.map (fun (t_3 : valtype) => t_3) t_3*)))) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (List.map (fun (x_1 : idx) => x_1) x_1*) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    ((List.length init*) == (List.length t*)) ->
    Forall₂ (fun (init : init) (t : valtype) => (wf_localtype (. init t))) init* t* ->
    Forall (fun (t : valtype) => (wf_localtype (. .SET t))) t* ->
    (wf_instrtype (. (. (List.map (fun (t_2 : valtype) => t_2) t_2*)) (List.map (fun (x_2 : idx) => x_2) x_2*) (. (List.map (fun (t_3 : valtype) => t_3) t_3*)))) ->
    (Instr_ok C instr_1 (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (List.map (fun (x_1 : idx) => x_1) x_1*) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    ((List.length init*) == (List.length x_1*)) ->
    Forall (fun (x_1 : idx) => ((proj_uN_0 x_1) < (List.length (C.LOCALS)))) x_1* ->
    Forall₃ (fun (init : init) (t : valtype) (x_1 : idx) => (((C.LOCALS)[(proj_uN_0 x_1)]!) == (. init t))) init* t* x_1* ->
    (Instrs_ok (with_locals C (List.map (fun (x_1 : idx) => x_1) x_1*) (List.map (fun (t : valtype) => (. .SET t)) t*)) (List.map (fun (instr_2 : instr) => instr_2) instr_2*) (. (. (List.map (fun (t_2 : valtype) => t_2) t_2*)) (List.map (fun (x_2 : idx) => x_2) x_2*) (. (List.map (fun (t_3 : valtype) => t_3) t_3*)))) ->
    Instrs_ok C ([instr_1] ++ (List.map (fun (instr_2 : instr) => instr_2) instr_2*)) (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) ((List.map (fun (x_1 : idx) => x_1) x_1*) ++ (List.map (fun (x_2 : idx) => x_2) x_2*)) (. (List.map (fun (t_3 : valtype) => t_3) t_3*)))
  | sub : forall (C : context) (instr* : (List instr)) (it' : instrtype) (it : instrtype), 
    (wf_context C) ->
    Forall (fun (instr : instr) => (wf_instr instr)) instr* ->
    (wf_instrtype it') ->
    (wf_instrtype it) ->
    (Instrs_ok C (List.map (fun (instr : instr) => instr) instr*) it) ->
    (Instrtype_sub C it it') ->
    (Instrtype_ok C it') ->
    Instrs_ok C (List.map (fun (instr : instr) => instr) instr*) it'
  | frame : forall (C : context) (instr* : (List instr)) (t* : (List valtype)) (t_1* : (List valtype)) (x* : (List idx)) (t_2* : (List valtype)), 
    (wf_context C) ->
    Forall (fun (instr : instr) => (wf_instr instr)) instr* ->
    (wf_instrtype (. (. ((List.map (fun (t : valtype) => t) t*) ++ (List.map (fun (t_1 : valtype) => t_1) t_1*))) (List.map (fun (x : idx) => x) x*) (. ((List.map (fun (t : valtype) => t) t*) ++ (List.map (fun (t_2 : valtype) => t_2) t_2*))))) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (List.map (fun (x : idx) => x) x*) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Instrs_ok C (List.map (fun (instr : instr) => instr) instr*) (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (List.map (fun (x : idx) => x) x*) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (Resulttype_ok C (. (List.map (fun (t : valtype) => t) t*))) ->
    Instrs_ok C (List.map (fun (instr : instr) => instr) instr*) (. (. ((List.map (fun (t : valtype) => t) t*) ++ (List.map (fun (t_1 : valtype) => t_1) t_1*))) (List.map (fun (x : idx) => x) x*) (. ((List.map (fun (t : valtype) => t) t*) ++ (List.map (fun (t_2 : valtype) => t_2) t_2*))))

end

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:7.1-7.94 -/
inductive Expr_ok : context -> expr -> resulttype -> Prop where
  |  : forall (C : context) (instr* : (List instr)) (t* : (List valtype)), 
    (wf_context C) ->
    Forall (fun (instr : instr) => (wf_instr instr)) instr* ->
    (wf_instrtype (. (. []) [] (. (List.map (fun (t : valtype) => t) t*)))) ->
    (Instrs_ok C (List.map (fun (instr : instr) => instr) instr*) (. (. []) [] (. (List.map (fun (t : valtype) => t) t*)))) ->
    Expr_ok C (List.map (fun (instr : instr) => instr) instr*) (. (List.map (fun (t : valtype) => t) t*))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:12.1-13.75 -/
inductive Nondefaultable : valtype -> Prop where
  |  : forall (t : valtype), 
    (wf_valtype t) ->
    ((default_ t) == none) ->
    Nondefaultable t

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:637.1-637.104 -/
inductive Instr_const : context -> instr -> Prop where
  | const : forall (C : context) (nt : numtype) (c_nt : num_), 
    (wf_context C) ->
    (wf_instr (.CONST nt c_nt)) ->
    Instr_const C (.CONST nt c_nt)
  | vconst : forall (C : context) (vt : vectype) (c_vt : vec_), 
    (wf_context C) ->
    (wf_instr (.VCONST vt c_vt)) ->
    Instr_const C (.VCONST vt c_vt)
  | ref.null : forall (C : context) (ht : heaptype), 
    (wf_context C) ->
    (wf_instr (.REF.NULL ht)) ->
    Instr_const C (.REF.NULL ht)
  | ref.i31 : forall (C : context), 
    (wf_context C) ->
    (wf_instr .REF.I31) ->
    Instr_const C .REF.I31
  | ref.func : forall (C : context) (x : idx), 
    (wf_context C) ->
    (wf_instr (.REF.FUNC x)) ->
    Instr_const C (.REF.FUNC x)
  | struct.new : forall (C : context) (x : idx), 
    (wf_context C) ->
    (wf_instr (.STRUCT.NEW x)) ->
    Instr_const C (.STRUCT.NEW x)
  | struct.new_default : forall (C : context) (x : idx), 
    (wf_context C) ->
    (wf_instr (.STRUCT.NEW_DEFAULT x)) ->
    Instr_const C (.STRUCT.NEW_DEFAULT x)
  | array.new : forall (C : context) (x : idx), 
    (wf_context C) ->
    (wf_instr (.ARRAY.NEW x)) ->
    Instr_const C (.ARRAY.NEW x)
  | array.new_default : forall (C : context) (x : idx), 
    (wf_context C) ->
    (wf_instr (.ARRAY.NEW_DEFAULT x)) ->
    Instr_const C (.ARRAY.NEW_DEFAULT x)
  | array.new_fixed : forall (C : context) (x : idx) (n : n), 
    (wf_context C) ->
    (wf_instr (.ARRAY.NEW_FIXED x (. n))) ->
    Instr_const C (.ARRAY.NEW_FIXED x (. n))
  | any.convert_extern : forall (C : context), 
    (wf_context C) ->
    (wf_instr .ANY.CONVERT_EXTERN) ->
    Instr_const C .ANY.CONVERT_EXTERN
  | extern.convert_any : forall (C : context), 
    (wf_context C) ->
    (wf_instr .EXTERN.CONVERT_ANY) ->
    Instr_const C .EXTERN.CONVERT_ANY
  | global.get : forall (C : context) (x : idx) (t : valtype), 
    (wf_context C) ->
    (wf_instr (.GLOBAL.GET x)) ->
    (wf_globaltype (. none t)) ->
    ((proj_uN_0 x) < (List.length (C.GLOBALS))) ->
    (((C.GLOBALS)[(proj_uN_0 x)]!) == (. none t)) ->
    Instr_const C (.GLOBAL.GET x)
  | binop : forall (C : context) (Inn : Inn) (binop : binop_), 
    (wf_context C) ->
    (wf_instr (.BINOP (numtype_addrtype Inn) binop)) ->
    (wf_binop_ (numtype_addrtype Inn) (.mk_binop__0 Inn .ADD)) ->
    (wf_binop_ (numtype_addrtype Inn) (.mk_binop__0 Inn .SUB)) ->
    (wf_binop_ (numtype_addrtype Inn) (.mk_binop__0 Inn .MUL)) ->
    (List.contains [.I32, .I64] Inn) ->
    (List.contains [(.mk_binop__0 Inn .ADD), (.mk_binop__0 Inn .SUB), (.mk_binop__0 Inn .MUL)] binop) ->
    Instr_const C (.BINOP (numtype_addrtype Inn) binop)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:638.1-638.103 -/
inductive Expr_const : context -> expr -> Prop where
  |  : forall (C : context) (instr* : (List instr)), 
    (wf_context C) ->
    Forall (fun (instr : instr) => (wf_instr instr)) instr* ->
    Forall (fun (instr : instr) => (Instr_const C instr)) instr* ->
    Expr_const C (List.map (fun (instr : instr) => instr) instr*)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:639.1-639.105 -/
inductive Expr_ok_const : context -> expr -> valtype -> Prop where
  |  : forall (C : context) (expr : expr) (t : valtype), 
    (wf_context C) ->
    Forall (fun (expr : instr) => (wf_instr expr)) expr ->
    (wf_valtype t) ->
    (Expr_ok C expr (. [t])) ->
    (Expr_const C expr) ->
    Expr_ok_const C expr t

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:7.1-7.97 -/
inductive Type_ok : context -> type -> (List deftype) -> Prop where
  |  : forall (C : context) (rectype : rectype) (dt* : (List deftype)) (x : idx), 
    (wf_context C) ->
    (wf_context { TYPES := (List.map (fun (dt : deftype) => dt) dt*), RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (wf_oktypeidx (.OK x)) ->
    ((proj_uN_0 x) == (List.length (C.TYPES))) ->
    ((List.map (fun (dt : deftype) => dt) dt*) == (rolldt x rectype)) ->
    (Rectype_ok (C ++ { TYPES := (List.map (fun (dt : deftype) => dt) dt*), RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) rectype (.OK x)) ->
    Type_ok C (.TYPE rectype) (List.map (fun (dt : deftype) => dt) dt*)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:8.1-8.96 -/
inductive Tag_ok : context -> tag -> tagtype -> Prop where
  |  : forall (C : context) (tagtype : tagtype), 
    (wf_context C) ->
    (wf_tag (.TAG tagtype)) ->
    (Tagtype_ok C tagtype) ->
    Tag_ok C (.TAG tagtype) (clos_tagtype C tagtype)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:9.1-9.99 -/
inductive Global_ok : context -> global -> globaltype -> Prop where
  |  : forall (C : context) (globaltype : globaltype) (expr : expr) (t : valtype), 
    (wf_context C) ->
    (wf_global (.GLOBAL globaltype expr)) ->
    (wf_globaltype (. (some .MUT) t)) ->
    (Globaltype_ok C globaltype) ->
    (globaltype == (. (some .MUT) t)) ->
    (Expr_ok_const C expr t) ->
    Global_ok C (.GLOBAL globaltype expr) globaltype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:10.1-10.96 -/
inductive Mem_ok : context -> mem -> memtype -> Prop where
  |  : forall (C : context) (memtype : memtype), 
    (wf_context C) ->
    (wf_mem (.MEMORY memtype)) ->
    (Memtype_ok C memtype) ->
    Mem_ok C (.MEMORY memtype) memtype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:11.1-11.98 -/
inductive Table_ok : context -> table -> tabletype -> Prop where
  |  : forall (C : context) (tabletype : tabletype) (expr : expr) (at : addrtype) (lim : limits) (rt : reftype), 
    (wf_context C) ->
    (wf_table (.TABLE tabletype expr)) ->
    (wf_tabletype (. at lim rt)) ->
    (Tabletype_ok C tabletype) ->
    (tabletype == (. at lim rt)) ->
    (Expr_ok_const C expr (valtype_reftype rt)) ->
    Table_ok C (.TABLE tabletype expr) tabletype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:18.1-18.98 -/
inductive Local_ok : context -> «local» -> localtype -> Prop where
  | set : forall (C : context) (t : valtype), 
    (wf_context C) ->
    (wf_local (.LOCAL t)) ->
    (wf_localtype (. .SET t)) ->
    (Defaultable t) ->
    Local_ok C (.LOCAL t) (. .SET t)
  | unset : forall (C : context) (t : valtype), 
    (wf_context C) ->
    (wf_local (.LOCAL t)) ->
    (wf_localtype (. .UNSET t)) ->
    (Nondefaultable t) ->
    Local_ok C (.LOCAL t) (. .UNSET t)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:12.1-12.97 -/
inductive Func_ok : context -> func -> deftype -> Prop where
  |  : forall (C : context) (x : idx) (local* : (List «local»)) (expr : expr) (t_1* : (List valtype)) (t_2* : (List valtype)) (lct* : (List localtype)), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (wf_context C) ->
    (wf_func (.FUNC x (List.map (fun (local : «local») => «local») local*) expr)) ->
    (wf_comptype (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := ((List.map (fun (t_1 : valtype) => (. .SET t_1)) t_1*) ++ (List.map (fun (lct : localtype) => lct) lct*)), LABELS := [(. (List.map (fun (t_2 : valtype) => t_2) t_2*))], RETURN := (some (. (List.map (fun (t_2 : valtype) => t_2) t_2*))), REFS := [] }) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    ((List.length lct*) == (List.length local*)) ->
    Forall₂ (fun (lct : localtype) (local : «local») => (Local_ok C «local» lct)) lct* local* ->
    (Expr_ok (C ++ { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := ((List.map (fun (t_1 : valtype) => (. .SET t_1)) t_1*) ++ (List.map (fun (lct : localtype) => lct) lct*)), LABELS := [(. (List.map (fun (t_2 : valtype) => t_2) t_2*))], RETURN := (some (. (List.map (fun (t_2 : valtype) => t_2) t_2*))), REFS := [] }) expr (. (List.map (fun (t_2 : valtype) => t_2) t_2*))) ->
    Func_ok C (.FUNC x (List.map (fun (local : «local») => «local») local*) expr) ((C.TYPES)[(proj_uN_0 x)]!)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:15.1-15.118 -/
inductive Datamode_ok : context -> datamode -> datatype -> Prop where
  | passive : forall (C : context), 
    (wf_context C) ->
    (wf_datamode .PASSIVE) ->
    Datamode_ok C .PASSIVE .OK
  | active : forall (C : context) (x : idx) (expr : expr) (at : addrtype) (lim : limits), 
    (wf_context C) ->
    (wf_datamode (.ACTIVE x expr)) ->
    (wf_memtype (.PAGE at lim)) ->
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE at lim)) ->
    (Expr_ok_const C expr (valtype_addrtype at)) ->
    Datamode_ok C (.ACTIVE x expr) .OK

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:13.1-13.115 -/
inductive Data_ok : context -> data -> datatype -> Prop where
  |  : forall (C : context) (b* : (List byte)) (datamode : datamode), 
    (wf_context C) ->
    (wf_data (.DATA (List.map (fun (b : byte) => b) b*) datamode)) ->
    (Datamode_ok C datamode .OK) ->
    Data_ok C (.DATA (List.map (fun (b : byte) => b) b*) datamode) .OK

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:16.1-16.101 -/
inductive Elemmode_ok : context -> elemmode -> elemtype -> Prop where
  | passive : forall (C : context) (rt : reftype), 
    (wf_context C) ->
    (wf_reftype rt) ->
    (wf_elemmode .PASSIVE) ->
    Elemmode_ok C .PASSIVE rt
  | declare : forall (C : context) (rt : reftype), 
    (wf_context C) ->
    (wf_reftype rt) ->
    (wf_elemmode .DECLARE) ->
    Elemmode_ok C .DECLARE rt
  | active : forall (C : context) (x : idx) (expr : expr) (rt : reftype) (at : addrtype) (lim : limits) (rt' : reftype), 
    (wf_context C) ->
    (wf_reftype rt) ->
    (wf_elemmode (.ACTIVE x expr)) ->
    (wf_tabletype (. at lim rt')) ->
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (. at lim rt')) ->
    (Reftype_sub C rt rt') ->
    (Expr_ok_const C expr (valtype_addrtype at)) ->
    Elemmode_ok C (.ACTIVE x expr) rt

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:14.1-14.97 -/
inductive Elem_ok : context -> elem -> elemtype -> Prop where
  |  : forall (C : context) (elemtype : elemtype) (expr* : (List expr)) (elemmode : elemmode), 
    (wf_context C) ->
    (wf_elem (.ELEM elemtype (List.map (fun (expr : expr) => expr) expr*) elemmode)) ->
    (Reftype_ok C elemtype) ->
    Forall (fun (expr : expr) => (Expr_ok_const C expr (valtype_reftype elemtype))) expr* ->
    (Elemmode_ok C elemmode elemtype) ->
    Elem_ok C (.ELEM elemtype (List.map (fun (expr : expr) => expr) expr*) elemmode) elemtype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:17.1-17.98 -/
inductive Start_ok : context -> start -> Prop where
  |  : forall (C : context) (x : idx), 
    (wf_context C) ->
    (wf_start (.START x)) ->
    (wf_comptype (.FUNC (. []) (. []))) ->
    ((proj_uN_0 x) < (List.length (C.FUNCS))) ->
    (Expand ((C.FUNCS)[(proj_uN_0 x)]!) (.FUNC (. []) (. []))) ->
    Start_ok C (.START x)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:98.1-98.105 -/
inductive Import_ok : context -> «import» -> externtype -> Prop where
  |  : forall (C : context) (name_1 : name) (name_2 : name) (xt : externtype), 
    (wf_context C) ->
    (wf_import (.IMPORT name_1 name_2 xt)) ->
    (Externtype_ok C xt) ->
    Import_ok C (.IMPORT name_1 name_2 xt) (clos_externtype C xt)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:100.1-100.108 -/
inductive Externidx_ok : context -> externidx -> externtype -> Prop where
  | tag : forall (C : context) (x : idx) (jt : tagtype), 
    (wf_context C) ->
    (wf_externidx (.TAG x)) ->
    (wf_externtype (.TAG jt)) ->
    ((proj_uN_0 x) < (List.length (C.TAGS))) ->
    (((C.TAGS)[(proj_uN_0 x)]!) == jt) ->
    Externidx_ok C (.TAG x) (.TAG jt)
  | global : forall (C : context) (x : idx) (gt : globaltype), 
    (wf_context C) ->
    (wf_externidx (.GLOBAL x)) ->
    (wf_externtype (.GLOBAL gt)) ->
    ((proj_uN_0 x) < (List.length (C.GLOBALS))) ->
    (((C.GLOBALS)[(proj_uN_0 x)]!) == gt) ->
    Externidx_ok C (.GLOBAL x) (.GLOBAL gt)
  | mem : forall (C : context) (x : idx) (mt : memtype), 
    (wf_context C) ->
    (wf_externidx (.MEM x)) ->
    (wf_externtype (.MEM mt)) ->
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == mt) ->
    Externidx_ok C (.MEM x) (.MEM mt)
  | table : forall (C : context) (x : idx) (tt : tabletype), 
    (wf_context C) ->
    (wf_externidx (.TABLE x)) ->
    (wf_externtype (.TABLE tt)) ->
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == tt) ->
    Externidx_ok C (.TABLE x) (.TABLE tt)
  | func : forall (C : context) (x : idx) (dt : deftype), 
    (wf_context C) ->
    (wf_externidx (.FUNC x)) ->
    (wf_externtype (.FUNC (typeuse_deftype dt))) ->
    ((proj_uN_0 x) < (List.length (C.FUNCS))) ->
    (((C.FUNCS)[(proj_uN_0 x)]!) == dt) ->
    Externidx_ok C (.FUNC x) (.FUNC (typeuse_deftype dt))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:99.1-99.105 -/
inductive Export_ok : context -> «export» -> name -> externtype -> Prop where
  |  : forall (C : context) (name : name) (externidx : externidx) (xt : externtype), 
    (wf_context C) ->
    (wf_externtype xt) ->
    (wf_export (.EXPORT name externidx)) ->
    (Externidx_ok C externidx xt) ->
    Export_ok C (.EXPORT name externidx) name xt

/- Recursive Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:136.1-136.100 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:136.1-136.100 -/
inductive Globals_ok : context -> (List global) -> (List globaltype) -> Prop where
  | empty : forall (C : context), 
    (wf_context C) ->
    Globals_ok C [] []
  | cons : forall (C : context) (global_1 : global) (global* : (List global)) (gt_1 : globaltype) (gt* : (List globaltype)), 
    (wf_context C) ->
    (wf_global global_1) ->
    Forall (fun (global : global) => (wf_global global)) global* ->
    Forall (fun (gt : globaltype) => (wf_globaltype gt)) gt* ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [gt_1], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (Global_ok C global_1 gt_1) ->
    (Globals_ok (C ++ { TYPES := [], RECS := [], TAGS := [], GLOBALS := [gt_1], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) (List.map (fun (global : global) => global) global*) (List.map (fun (gt : globaltype) => gt) gt*)) ->
    Globals_ok C ([global_1] ++ (List.map (fun (global : global) => global) global*)) ([gt_1] ++ (List.map (fun (gt : globaltype) => gt) gt*))

/- Recursive Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:135.1-135.98 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:135.1-135.98 -/
inductive Types_ok : context -> (List type) -> (List deftype) -> Prop where
  | empty : forall (C : context), 
    (wf_context C) ->
    Types_ok C [] []
  | cons : forall (C : context) (type_1 : type) (type* : (List type)) (dt_1* : (List deftype)) (dt* : (List deftype)), 
    (wf_context C) ->
    (wf_context { TYPES := (List.map (fun (dt_1 : deftype) => dt_1) dt_1*), RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (Type_ok C type_1 (List.map (fun (dt_1 : deftype) => dt_1) dt_1*)) ->
    (Types_ok (C ++ { TYPES := (List.map (fun (dt_1 : deftype) => dt_1) dt_1*), RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) (List.map (fun (type : type) => type) type*) (List.map (fun (dt : deftype) => dt) dt*)) ->
    Types_ok C ([type_1] ++ (List.map (fun (type : type) => type) type*)) ((List.map (fun (dt_1 : deftype) => dt_1) dt_1*) ++ (List.map (fun (dt : deftype) => dt) dt*))

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:139.1-139.44 -/
inductive nonfuncs : Type where
  |  ((List.map (fun (global : global) => global) global*) : (List global)) ((List.map (fun (mem : mem) => mem) mem*) : (List mem)) ((List.map (fun (table : table) => table) table*) : (List table)) ((List.map (fun (elem : elem) => elem) elem*) : (List elem)) : nonfuncs
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:139.8-139.16 -/
inductive wf_nonfuncs : nonfuncs -> Prop where
  | nonfuncs_case_0 : forall (global* : (List global)) (mem* : (List mem)) (table* : (List table)) (elem* : (List elem)), 
    Forall (fun (global : global) => (wf_global global)) global* ->
    Forall (fun (mem : mem) => (wf_mem mem)) mem* ->
    Forall (fun (table : table) => (wf_table table)) table* ->
    Forall (fun (elem : elem) => (wf_elem elem)) elem* ->
    wf_nonfuncs (. (List.map (fun (global : global) => global) global*) (List.map (fun (mem : mem) => mem) mem*) (List.map (fun (table : table) => table) table*) (List.map (fun (elem : elem) => elem) elem*))

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:140.1-140.93 -/
opaque funcidx_nonfuncs : forall (nonfuncs : nonfuncs), (List funcidx) := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:134.1-134.99 -/
inductive Module_ok : module -> moduletype -> Prop where
  |  : forall (type* : (List type)) (import* : (List «import»)) (tag* : (List tag)) (global* : (List global)) (mem* : (List mem)) (table* : (List table)) (func* : (List func)) (data* : (List data)) (elem* : (List elem)) (start? : (Option start)) (export* : (List «export»)) (C : context) (xt_I* : (List externtype)) (xt_E* : (List externtype)) (dt'* : (List deftype)) (C' : context) (jt* : (List tagtype)) (gt* : (List globaltype)) (mt* : (List memtype)) (tt* : (List tabletype)) (dt* : (List deftype)) (ok* : (List datatype)) (rt* : (List reftype)) (nm* : (List name)) (jt_I* : (List tagtype)) (mt_I* : (List memtype)) (tt_I* : (List tabletype)) (gt_I* : (List globaltype)) (dt_I* : (List deftype)) (x* : (List idx)), 
    (wf_context C) ->
    (wf_context C') ->
    Forall (fun (nm : name) => (wf_name nm)) nm* ->
    (wf_module (.MODULE (List.map (fun (type : type) => type) type*) (List.map (fun (import : «import») => «import») import*) (List.map (fun (tag : tag) => tag) tag*) (List.map (fun (global : global) => global) global*) (List.map (fun (mem : mem) => mem) mem*) (List.map (fun (table : table) => table) table*) (List.map (fun (func : func) => func) func*) (List.map (fun (data : data) => data) data*) (List.map (fun (elem : elem) => elem) elem*) (Option.map (fun (start : start) => start) start?) (List.map (fun (export : «export») => «export») export*))) ->
    (wf_moduletype (. (List.map (fun (xt_I : externtype) => xt_I) xt_I*) (List.map (fun (xt_E : externtype) => xt_E) xt_E*))) ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (wf_context { TYPES := (List.map (fun (dt' : deftype) => dt') dt'*), RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (wf_context { TYPES := [], RECS := [], TAGS := ((List.map (fun (jt_I : tagtype) => jt_I) jt_I*) ++ (List.map (fun (jt : tagtype) => jt) jt*)), GLOBALS := (List.map (fun (gt : globaltype) => gt) gt*), MEMS := ((List.map (fun (mt_I : memtype) => mt_I) mt_I*) ++ (List.map (fun (mt : memtype) => mt) mt*)), TABLES := ((List.map (fun (tt_I : tabletype) => tt_I) tt_I*) ++ (List.map (fun (tt : tabletype) => tt) tt*)), FUNCS := [], DATAS := (List.map (fun (ok : datatype) => ok) ok*), ELEMS := (List.map (fun (rt : reftype) => rt) rt*), LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (wf_context { TYPES := (List.map (fun (dt' : deftype) => dt') dt'*), RECS := [], TAGS := [], GLOBALS := (List.map (fun (gt_I : globaltype) => gt_I) gt_I*), MEMS := [], TABLES := [], FUNCS := ((List.map (fun (dt_I : deftype) => dt_I) dt_I*) ++ (List.map (fun (dt : deftype) => dt) dt*)), DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := (List.map (fun (x : idx) => x) x*) }) ->
    (wf_nonfuncs (. (List.map (fun (global : global) => global) global*) (List.map (fun (mem : mem) => mem) mem*) (List.map (fun (table : table) => table) table*) (List.map (fun (elem : elem) => elem) elem*))) ->
    (Types_ok { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } (List.map (fun (type : type) => type) type*) (List.map (fun (dt' : deftype) => dt') dt'*)) ->
    ((List.length import*) == (List.length xt_I*)) ->
    Forall₂ (fun (import : «import») (xt_I : externtype) => (Import_ok { TYPES := (List.map (fun (dt' : deftype) => dt') dt'*), RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } «import» xt_I)) import* xt_I* ->
    ((List.length jt*) == (List.length tag*)) ->
    Forall₂ (fun (jt : tagtype) (tag : tag) => (Tag_ok C' tag jt)) jt* tag* ->
    (Globals_ok C' (List.map (fun (global : global) => global) global*) (List.map (fun (gt : globaltype) => gt) gt*)) ->
    ((List.length mem*) == (List.length mt*)) ->
    Forall₂ (fun (mem : mem) (mt : memtype) => (Mem_ok C' mem mt)) mem* mt* ->
    ((List.length table*) == (List.length tt*)) ->
    Forall₂ (fun (table : table) (tt : tabletype) => (Table_ok C' table tt)) table* tt* ->
    ((List.length dt*) == (List.length func*)) ->
    Forall₂ (fun (dt : deftype) (func : func) => (Func_ok C func dt)) dt* func* ->
    ((List.length data*) == (List.length ok*)) ->
    Forall₂ (fun (data : data) (ok : datatype) => (Data_ok C data ok)) data* ok* ->
    ((List.length elem*) == (List.length rt*)) ->
    Forall₂ (fun (elem : elem) (rt : elemtype) => (Elem_ok C elem rt)) elem* rt* ->
    Forall (fun (start : start) => (Start_ok C start)) (Option.toList start?) ->
    ((List.length export*) == (List.length nm*)) ->
    ((List.length export*) == (List.length xt_E*)) ->
    Forall₃ (fun (export : «export») (nm : name) (xt_E : externtype) => (Export_ok C «export» nm xt_E)) export* nm* xt_E* ->
    (disjoint_ name (List.map (fun (nm : name) => nm) nm*)) ->
    (C == (C' ++ { TYPES := [], RECS := [], TAGS := ((List.map (fun (jt_I : tagtype) => jt_I) jt_I*) ++ (List.map (fun (jt : tagtype) => jt) jt*)), GLOBALS := (List.map (fun (gt : globaltype) => gt) gt*), MEMS := ((List.map (fun (mt_I : memtype) => mt_I) mt_I*) ++ (List.map (fun (mt : memtype) => mt) mt*)), TABLES := ((List.map (fun (tt_I : tabletype) => tt_I) tt_I*) ++ (List.map (fun (tt : tabletype) => tt) tt*)), FUNCS := [], DATAS := (List.map (fun (ok : datatype) => ok) ok*), ELEMS := (List.map (fun (rt : reftype) => rt) rt*), LOCALS := [], LABELS := [], RETURN := none, REFS := [] })) ->
    (C' == { TYPES := (List.map (fun (dt' : deftype) => dt') dt'*), RECS := [], TAGS := [], GLOBALS := (List.map (fun (gt_I : globaltype) => gt_I) gt_I*), MEMS := [], TABLES := [], FUNCS := ((List.map (fun (dt_I : deftype) => dt_I) dt_I*) ++ (List.map (fun (dt : deftype) => dt) dt*)), DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := (List.map (fun (x : idx) => x) x*) }) ->
    ((List.map (fun (x : idx) => x) x*) == (funcidx_nonfuncs (. (List.map (fun (global : global) => global) global*) (List.map (fun (mem : mem) => mem) mem*) (List.map (fun (table : table) => table) table*) (List.map (fun (elem : elem) => elem) elem*)))) ->
    ((List.map (fun (jt_I : tagtype) => jt_I) jt_I*) == (tagsxt (List.map (fun (xt_I : externtype) => xt_I) xt_I*))) ->
    ((List.map (fun (gt_I : globaltype) => gt_I) gt_I*) == (globalsxt (List.map (fun (xt_I : externtype) => xt_I) xt_I*))) ->
    ((List.map (fun (mt_I : memtype) => mt_I) mt_I*) == (memsxt (List.map (fun (xt_I : externtype) => xt_I) xt_I*))) ->
    ((List.map (fun (tt_I : tabletype) => tt_I) tt_I*) == (tablesxt (List.map (fun (xt_I : externtype) => xt_I) xt_I*))) ->
    ((List.map (fun (dt_I : deftype) => dt_I) dt_I*) == (funcsxt (List.map (fun (xt_I : externtype) => xt_I) xt_I*))) ->
    Module_ok (.MODULE (List.map (fun (type : type) => type) type*) (List.map (fun (import : «import») => «import») import*) (List.map (fun (tag : tag) => tag) tag*) (List.map (fun (global : global) => global) global*) (List.map (fun (mem : mem) => mem) mem*) (List.map (fun (table : table) => table) table*) (List.map (fun (func : func) => func) func*) (List.map (fun (data : data) => data) data*) (List.map (fun (elem : elem) => elem) elem*) (Option.map (fun (start : start) => start) start?) (List.map (fun (export : «export») => «export») export*)) (clos_moduletype C (. (List.map (fun (xt_I : externtype) => xt_I) xt_I*) (List.map (fun (xt_E : externtype) => xt_E) xt_E*)))

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:5.1-5.24 -/
inductive relaxed2 : Type where
  |  (i : Nat) : relaxed2
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:5.1-5.24 -/
opaque proj_relaxed2_0 : forall (x : relaxed2), Nat := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:5.8-5.16 -/
inductive wf_relaxed2 : relaxed2 -> Prop where
  | relaxed2_case_0 : forall (i : Nat), 
    ((i == 0) || (i == 1)) ->
    wf_relaxed2 (. i)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:6.1-6.32 -/
inductive relaxed4 : Type where
  |  (i : Nat) : relaxed4
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:6.1-6.32 -/
opaque proj_relaxed4_0 : forall (x : relaxed4), Nat := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:6.8-6.16 -/
inductive wf_relaxed4 : relaxed4 -> Prop where
  | relaxed4_case_0 : forall (i : Nat), 
    ((((i == 0) || (i == 1)) || (i == 2)) || (i == 3)) ->
    wf_relaxed4 (. i)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:8.1-8.83 -/
opaque relaxed2 : forall (relaxed2 : relaxed2) (X : Type) (X : X) (X : X), X := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:9.1-9.89 -/
opaque relaxed4 : forall (relaxed4 : relaxed4) (X : Type) (X : X) (X : X) (X : X) (X : X), X := opaqueDef

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
opaque s33_to_u32 : forall (s33 : s33), u32 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:12.1-12.107 -/
opaque ibits_ : forall (N : N) (iN : iN), (List bit) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:13.1-13.107 -/
opaque fbits_ : forall (N : N) (fN : fN), (List bit) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:14.1-14.109 -/
opaque ibytes_ : forall (N : N) (iN : iN), (List byte) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:15.1-15.109 -/
opaque fbytes_ : forall (N : N) (fN : fN), (List byte) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:16.1-16.104 -/
opaque nbytes_ : forall (numtype : numtype) (num_ : num_), (List byte) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:17.1-17.104 -/
opaque vbytes_ : forall (vectype : vectype) (vec_ : vec_), (List byte) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:18.1-18.104 -/
opaque zbytes_ : forall (storagetype : storagetype) (lit_ : lit_), (List byte) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:19.1-19.104 -/
opaque cbytes_ : forall (Cnn : Cnn) (lit_ : lit_), (List byte) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:21.1-21.91 -/
opaque inv_ibits_ : forall (N : N) (_ : (List bit)), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:22.1-22.91 -/
opaque inv_fbits_ : forall (N : N) (_ : (List bit)), fN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:23.1-23.92 -/
opaque inv_ibytes_ : forall (N : N) (_ : (List byte)), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:24.1-24.92 -/
opaque inv_fbytes_ : forall (N : N) (_ : (List byte)), fN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:25.1-25.87 -/
opaque inv_nbytes_ : forall (numtype : numtype) (_ : (List byte)), num_ := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:26.1-26.87 -/
opaque inv_vbytes_ : forall (vectype : vectype) (_ : (List byte)), vec_ := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:27.1-27.92 -/
opaque inv_zbytes_ : forall (storagetype : storagetype) (_ : (List byte)), lit_ := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:28.1-28.87 -/
opaque inv_cbytes_ : forall (Cnn : Cnn) (_ : (List byte)), lit_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:52.1-52.54 -/
opaque signed_ : forall (N : N) (nat : Nat), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:56.1-56.68 -/
opaque inv_signed_ : forall (N : N) (int : Nat), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:61.1-61.46 -/
opaque sx : forall (storagetype : storagetype), (Option sx) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:68.1-68.51 -/
opaque zero : forall (lanetype : lanetype), lane_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:72.1-72.22 -/
opaque bool : forall (bool : Bool), Nat := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:76.1-76.23 -/
opaque truncz : forall (rat : Nat), Nat := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:80.1-80.59 -/
opaque ceilz : forall (rat : Nat), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:87.1-87.61 -/
opaque sat_u_ : forall (N : N) (int : Nat), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:92.1-92.61 -/
opaque sat_s_ : forall (N : N) (int : Nat), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:100.1-100.29 -/
opaque ineg_ : forall (N : N) (iN : iN), iN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:101.1-101.29 -/
opaque iabs_ : forall (N : N) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:102.1-102.29 -/
opaque iclz_ : forall (N : N) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:103.1-103.29 -/
opaque ictz_ : forall (N : N) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:104.1-104.32 -/
opaque ipopcnt_ : forall (N : N) (iN : iN), iN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:105.1-105.86 -/
opaque iextend_ : forall (N : N) (M : M) (sx : sx) (iN : iN), iN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:107.1-107.36 -/
opaque iadd_ : forall (N : N) (iN : iN) (iN : iN), iN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:108.1-108.36 -/
opaque isub_ : forall (N : N) (iN : iN) (iN : iN), iN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:109.1-109.36 -/
opaque imul_ : forall (N : N) (iN : iN) (iN : iN), iN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:110.1-110.83 -/
opaque idiv_ : forall (N : N) (sx : sx) (iN : iN) (iN : iN), (Option iN) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:111.1-111.83 -/
opaque irem_ : forall (N : N) (sx : sx) (iN : iN) (iN : iN), (Option iN) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:112.1-112.83 -/
opaque imin_ : forall (N : N) (sx : sx) (iN : iN) (iN : iN), iN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:113.1-113.83 -/
opaque imax_ : forall (N : N) (sx : sx) (iN : iN) (iN : iN), iN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:114.1-114.88 -/
opaque iadd_sat_ : forall (N : N) (sx : sx) (iN : iN) (iN : iN), iN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:115.1-115.88 -/
opaque isub_sat_ : forall (N : N) (sx : sx) (iN : iN) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:116.1-116.92 -/
opaque iq15mulr_sat_ : forall (N : N) (sx : sx) (iN : iN) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:117.1-117.101 -/
opaque irelaxed_q15mulr_ : forall (N : N) (sx : sx) (iN : iN) (iN : iN), (List iN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:118.1-118.84 -/
opaque iavgr_ : forall (N : N) (sx : sx) (iN : iN) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:120.1-120.29 -/
opaque inot_ : forall (N : N) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:121.1-121.29 -/
opaque irev_ : forall (N : N) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:122.1-122.36 -/
opaque iand_ : forall (N : N) (iN : iN) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:123.1-123.39 -/
opaque iandnot_ : forall (N : N) (iN : iN) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:124.1-124.35 -/
opaque ior_ : forall (N : N) (iN : iN) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:125.1-125.36 -/
opaque ixor_ : forall (N : N) (iN : iN) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:126.1-126.34 -/
opaque ishl_ : forall (N : N) (iN : iN) (u32 : u32), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:127.1-127.76 -/
opaque ishr_ : forall (N : N) (sx : sx) (iN : iN) (u32 : u32), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:128.1-128.37 -/
opaque irotl_ : forall (N : N) (iN : iN) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:129.1-129.37 -/
opaque irotr_ : forall (N : N) (iN : iN) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:131.1-131.49 -/
opaque ibitselect_ : forall (N : N) (iN : iN) (iN : iN) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:132.1-132.59 -/
opaque irelaxed_laneselect_ : forall (N : N) (iN : iN) (iN : iN) (iN : iN), (List iN) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:134.1-134.27 -/
opaque ieqz_ : forall (N : N) (iN : iN), u32 := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:135.1-135.27 -/
opaque inez_ : forall (N : N) (iN : iN), u32 := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:137.1-137.33 -/
opaque ieq_ : forall (N : N) (iN : iN) (iN : iN), u32 := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:138.1-138.33 -/
opaque ine_ : forall (N : N) (iN : iN) (iN : iN), u32 := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:139.1-139.75 -/
opaque ilt_ : forall (N : N) (sx : sx) (iN : iN) (iN : iN), u32 := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:140.1-140.75 -/
opaque igt_ : forall (N : N) (sx : sx) (iN : iN) (iN : iN), u32 := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:141.1-141.75 -/
opaque ile_ : forall (N : N) (sx : sx) (iN : iN) (iN : iN), u32 := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:142.1-142.75 -/
opaque ige_ : forall (N : N) (sx : sx) (iN : iN) (iN : iN), u32 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:242.1-242.30 -/
opaque fabs_ : forall (N : N) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:243.1-243.30 -/
opaque fneg_ : forall (N : N) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:244.1-244.31 -/
opaque fsqrt_ : forall (N : N) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:245.1-245.31 -/
opaque fceil_ : forall (N : N) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:246.1-246.32 -/
opaque ffloor_ : forall (N : N) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:247.1-247.32 -/
opaque ftrunc_ : forall (N : N) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:248.1-248.34 -/
opaque fnearest_ : forall (N : N) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:250.1-250.37 -/
opaque fadd_ : forall (N : N) (fN : fN) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:251.1-251.37 -/
opaque fsub_ : forall (N : N) (fN : fN) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:252.1-252.37 -/
opaque fmul_ : forall (N : N) (fN : fN) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:253.1-253.37 -/
opaque fdiv_ : forall (N : N) (fN : fN) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:254.1-254.37 -/
opaque fmin_ : forall (N : N) (fN : fN) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:255.1-255.37 -/
opaque fmax_ : forall (N : N) (fN : fN) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:256.1-256.38 -/
opaque fpmin_ : forall (N : N) (fN : fN) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:257.1-257.38 -/
opaque fpmax_ : forall (N : N) (fN : fN) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:258.1-258.82 -/
opaque frelaxed_min_ : forall (N : N) (fN : fN) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:259.1-259.82 -/
opaque frelaxed_max_ : forall (N : N) (fN : fN) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:260.1-260.42 -/
opaque fcopysign_ : forall (N : N) (fN : fN) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:262.1-262.33 -/
opaque feq_ : forall (N : N) (fN : fN) (fN : fN), u32 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:263.1-263.33 -/
opaque fne_ : forall (N : N) (fN : fN) (fN : fN), u32 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:264.1-264.33 -/
opaque flt_ : forall (N : N) (fN : fN) (fN : fN), u32 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:265.1-265.33 -/
opaque fgt_ : forall (N : N) (fN : fN) (fN : fN), u32 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:266.1-266.33 -/
opaque fle_ : forall (N : N) (fN : fN) (fN : fN), u32 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:267.1-267.33 -/
opaque fge_ : forall (N : N) (fN : fN) (fN : fN), u32 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:269.1-269.91 -/
opaque frelaxed_madd_ : forall (N : N) (fN : fN) (fN : fN) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:270.1-270.92 -/
opaque frelaxed_nmadd_ : forall (N : N) (fN : fN) (fN : fN) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:308.1-308.33 -/
opaque wrap__ : forall (M : M) (N : N) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:309.1-309.90 -/
opaque extend__ : forall (M : M) (N : N) (sx : sx) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:310.1-310.89 -/
opaque trunc__ : forall (M : M) (N : N) (sx : sx) (fN : fN), (Option iN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:311.1-311.94 -/
opaque trunc_sat__ : forall (M : M) (N : N) (sx : sx) (fN : fN), (Option iN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:312.1-312.98 -/
opaque relaxed_trunc__ : forall (M : M) (N : N) (sx : sx) (fN : fN), (Option iN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:313.1-313.36 -/
opaque demote__ : forall (M : M) (N : N) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:314.1-314.37 -/
opaque promote__ : forall (M : M) (N : N) (fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:315.1-315.91 -/
opaque convert__ : forall (M : M) (N : N) (sx : sx) (iN : iN), fN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:316.1-316.88 -/
opaque narrow__ : forall (M : M) (N : N) (sx : sx) (iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:318.1-318.76 -/
opaque reinterpret__ : forall (numtype_1 : numtype) (numtype_2 : numtype) (num_ : num_), num_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:338.1-339.49 -/
opaque lpacknum_ : forall (lanetype : lanetype) (num_ : num_), lane_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:340.1-341.49 -/
opaque cpacknum_ : forall (storagetype : storagetype) (lit_ : lit_), lit_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:350.1-351.53 -/
opaque lunpacknum_ : forall (lanetype : lanetype) (lane_ : lane_), num_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:352.1-353.53 -/
opaque cunpacknum_ : forall (storagetype : storagetype) (lit_ : lit_), lit_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:364.1-365.28 -/
opaque unop_ : forall (numtype : numtype) (unop_ : unop_) (num_ : num_), (List num_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:366.1-367.32 -/
opaque binop_ : forall (numtype : numtype) (binop_ : binop_) (num_ : num_) (num_ : num_), (List num_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:368.1-369.28 -/
opaque testop_ : forall (numtype : numtype) (testop_ : testop_) (num_ : num_), u32 := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 -/
opaque relop_ : forall (numtype : numtype) (relop_ : relop_) (num_ : num_) (num_ : num_), u32 := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:372.1-373.32 -/
opaque cvtop__ : forall (numtype_1 : numtype) (numtype_2 : numtype) (cvtop__ : cvtop__) (num_ : num_), (List num_) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:10.1-10.84 -/
opaque lanes_ : forall (shape : shape) (vec_ : vec_), (List lane_) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:12.1-13.37 -/
opaque inv_lanes_ : forall (shape : shape) (_ : (List lane_)), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:19.1-19.66 -/
opaque zeroop : forall (shape_1 : shape) (shape_2 : shape) (vcvtop__ : vcvtop__), (Option zero) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:27.1-27.66 -/
opaque halfop : forall (shape_1 : shape) (shape_2 : shape) (vcvtop__ : vcvtop__), (Option half) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:35.1-35.32 -/
opaque half : forall (half : half) (nat : Nat) (nat : Nat), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:40.1-40.46 -/
opaque iswizzle_lane_ : forall (N : N) (_ : (List iN)) (iN : iN), iN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:41.1-41.54 -/
opaque irelaxed_swizzle_lane_ : forall (N : N) (_ : (List iN)) (iN : iN), iN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:54.1-54.73 -/
opaque ivunop_ : forall (shape : shape) (f_ : N -> iN -> iN) (vec_ : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:55.1-55.74 -/
opaque fvunop_ : forall (shape : shape) (f_ : N -> fN -> (List fN)) (vec_ : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:57.1-57.93 -/
opaque ivbinop_ : forall (shape : shape) (f_ : N -> iN -> iN -> iN) (vec_ : vec_) (vec_ : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:58.1-58.103 -/
opaque ivbinopsx_ : forall (shape : shape) (f_ : N -> sx -> iN -> iN -> iN) (sx : sx) (vec_ : vec_) (vec_ : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:59.1-59.106 -/
opaque ivbinopsxnd_ : forall (shape : shape) (f_ : N -> sx -> iN -> iN -> (List iN)) (sx : sx) (vec_ : vec_) (vec_ : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:60.1-60.94 -/
opaque fvbinop_ : forall (shape : shape) (f_ : N -> fN -> fN -> (List fN)) (vec_ : vec_) (vec_ : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:62.1-62.116 -/
opaque ivternopnd_ : forall (shape : shape) (f_ : N -> iN -> iN -> iN -> (List iN)) (vec_ : vec_) (vec_ : vec_) (vec_ : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:63.1-63.114 -/
opaque fvternop_ : forall (shape : shape) (f_ : N -> fN -> fN -> fN -> (List fN)) (vec_ : vec_) (vec_ : vec_) (vec_ : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:65.1-65.65 -/
opaque ivtestop_ : forall (shape : shape) (f_ : N -> iN -> u32) (vec_ : vec_), u32 := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:66.1-66.65 -/
opaque fvtestop_ : forall (shape : shape) (f_ : N -> fN -> u32) (vec_ : vec_), u32 := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:68.1-68.90 -/
opaque ivrelop_ : forall (shape : shape) (f_ : N -> iN -> iN -> u32) (vec_ : vec_) (vec_ : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:69.1-69.100 -/
opaque ivrelopsx_ : forall (shape : shape) (f_ : N -> sx -> iN -> iN -> u32) (sx : sx) (vec_ : vec_) (vec_ : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:70.1-70.90 -/
opaque fvrelop_ : forall (shape : shape) (f_ : N -> fN -> fN -> u32) (vec_ : vec_) (vec_ : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:72.1-72.85 -/
opaque ivshiftop_ : forall (shape : shape) (f_ : N -> iN -> u32 -> iN) (vec_ : vec_) (u32 : u32), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:73.1-73.95 -/
opaque ivshiftopsx_ : forall (shape : shape) (f_ : N -> sx -> iN -> u32 -> iN) (sx : sx) (vec_ : vec_) (u32 : u32), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:75.1-75.43 -/
opaque ivbitmaskop_ : forall (shape : shape) (vec_ : vec_), u32 := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:76.1-76.96 -/
opaque ivswizzlop_ : forall (shape : shape) (f_ : N -> (List iN) -> iN -> iN) (vec_ : vec_) (vec_ : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:77.1-77.71 -/
opaque ivshufflop_ : forall (shape : shape) (_ : (List laneidx)) (vec_ : vec_) (vec_ : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:177.1-178.28 -/
opaque vvunop_ : forall (vectype : vectype) (vvunop : vvunop) (vec_ : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:179.1-180.31 -/
opaque vvbinop_ : forall (vectype : vectype) (vvbinop : vvbinop) (vec_ : vec_) (vec_ : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:181.1-182.34 -/
opaque vvternop_ : forall (vectype : vectype) (vvternop : vvternop) (vec_ : vec_) (vec_ : vec_) (vec_ : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:184.1-185.28 -/
opaque vunop_ : forall (shape : shape) (vunop_ : vunop_) (vec_ : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:186.1-187.31 -/
opaque vbinop_ : forall (shape : shape) (vbinop_ : vbinop_) (vec_ : vec_) (vec_ : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:188.1-189.34 -/
opaque vternop_ : forall (shape : shape) (vternop_ : vternop_) (vec_ : vec_) (vec_ : vec_) (vec_ : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:190.1-191.28 -/
opaque vtestop_ : forall (shape : shape) (vtestop_ : vtestop_) (vec_ : vec_), u32 := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:192.1-193.31 -/
opaque vrelop_ : forall (shape : shape) (vrelop_ : vrelop_) (vec_ : vec_) (vec_ : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:195.1-196.41 -/
opaque lcvtop__ : forall (shape_1 : shape) (shape_2 : shape) (vcvtop__ : vcvtop__) (lane_ : lane_), (List lane_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:197.1-198.41 -/
opaque vcvtop__ : forall (shape_1 : shape) (shape_2 : shape) (vcvtop__ : vcvtop__) (vec_ : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:200.1-201.34 -/
opaque vshiftop_ : forall (ishape : ishape) (vshiftop_ : vshiftop_) (vec_ : vec_) (u32 : u32), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:202.1-203.34 -/
opaque vbitmaskop_ : forall (ishape : ishape) (vec_ : vec_), u32 := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:204.1-205.31 -/
opaque vswizzlop_ : forall (bshape : bshape) (vswizzlop_ : vswizzlop_) (vec_ : vec_) (vec_ : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:206.1-207.40 -/
opaque vshufflop_ : forall (bshape : bshape) (_ : (List laneidx)) (vec_ : vec_) (vec_ : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:209.1-210.49 -/
opaque vnarrowop__ : forall (shape_1 : shape) (shape_2 : shape) (sx : sx) (vec_ : vec_) (vec_ : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:372.1-372.76 -/
opaque ivadd_pairwise_ : forall (N : N) (_ : (List iN)), (List iN) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:358.1-358.93 -/
opaque ivextunop__ : forall (shape_1 : shape) (shape_2 : shape) (f_ : N -> (List iN) -> (List iN)) (sx : sx) (vec_ : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:212.1-213.32 -/
opaque vextunop__ : forall (ishape_1 : ishape) (ishape_2 : ishape) (vextunop__ : vextunop__) (vec_ : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:379.1-379.40 -/
opaque ivdot_ : forall (N : N) (_ : (List iN)) (_ : (List iN)), (List iN) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:383.1-383.76 -/
opaque ivdot_sat_ : forall (N : N) (_ : (List iN)) (_ : (List iN)), (List iN) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:364.1-364.136 -/
opaque ivextbinop__ : forall (shape_1 : shape) (shape_2 : shape) (f_ : N -> (List iN) -> (List iN) -> (List iN)) (sx : sx) (sx : sx) (laneidx : laneidx) (laneidx : laneidx) (vec_ : vec_) (vec_ : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:376.1-376.40 -/
opaque ivmul_ : forall (N : N) (_ : (List iN)) (_ : (List iN)), (List iN) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:214.1-215.35 -/
opaque vextbinop__ : forall (ishape_1 : ishape) (ishape_2 : ishape) (vextbinop__ : vextbinop__) (vec_ : vec_) (vec_ : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:216.1-217.38 -/
opaque vextternop__ : forall (ishape_1 : ishape) (ishape_2 : ishape) (vextternop__ : vextternop__) (vec_ : vec_) (vec_ : vec_) (vec_ : vec_), vec_ := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:29.1-30.63 -/
inductive num : Type where
  | CONST (numtype : numtype) (num_ : num_) : num
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
opaque val_num : forall (_ : num), val := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:29.8-29.11 -/
inductive wf_num : num -> Prop where
  | num_case_0 : forall (numtype : numtype) (num_ : num_), 
    (wf_num_ numtype num_) ->
    wf_num (.CONST numtype num_)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:32.1-33.87 -/
inductive vec : Type where
  | VCONST (vectype : vectype) (vec_ : vec_) : vec
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
opaque val_vec : forall (_ : vec), val := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:32.8-32.11 -/
inductive wf_vec : vec -> Prop where
  | vec_case_0 : forall (vectype : vectype) (vec_ : vec_), 
    (wf_uN (vsize vectype) vec_) ->
    wf_vec (.VCONST vectype vec_)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:44.1-46.22 -/
inductive ref : Type where
  | REF.I31_NUM (u31 : u31) : ref
  | REF.STRUCT_ADDR (structaddr : structaddr) : ref
  | REF.ARRAY_ADDR (arrayaddr : arrayaddr) : ref
  | REF.FUNC_ADDR (funcaddr : funcaddr) : ref
  | REF.EXN_ADDR (exnaddr : exnaddr) : ref
  | REF.HOST_ADDR (hostaddr : hostaddr) : ref
  | REF.EXTERN (addrref : addrref) : ref
  | REF.NULL (heaptype : heaptype) : ref
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
opaque ref_addrref : forall (_ : addrref), ref := opaqueDef

/- Auxiliary Definition at:  -/
opaque instr_ref : forall (_ : ref), instr := opaqueDef

/- Auxiliary Definition at:  -/
opaque val_ref : forall (_ : ref), val := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:44.8-44.11 -/
inductive wf_ref : ref -> Prop where
  | ref_case_0 : forall (u31 : u31), 
    (wf_uN 31 u31) ->
    wf_ref (.REF.I31_NUM u31)
  | ref_case_1 : forall (structaddr : structaddr), wf_ref (.REF.STRUCT_ADDR structaddr)
  | ref_case_2 : forall (arrayaddr : arrayaddr), wf_ref (.REF.ARRAY_ADDR arrayaddr)
  | ref_case_3 : forall (funcaddr : funcaddr), wf_ref (.REF.FUNC_ADDR funcaddr)
  | ref_case_4 : forall (exnaddr : exnaddr), wf_ref (.REF.EXN_ADDR exnaddr)
  | ref_case_5 : forall (hostaddr : hostaddr), wf_ref (.REF.HOST_ADDR hostaddr)
  | ref_case_6 : forall (addrref : addrref), 
    (wf_addrref addrref) ->
    wf_ref (.REF.EXTERN addrref)
  | ref_case_7 : forall (heaptype : heaptype), 
    (wf_heaptype heaptype) ->
    wf_ref (.REF.NULL heaptype)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:51.1-52.58 -/
inductive result : Type where
  | _VALS ((List.map (fun (val : val) => val) val*) : (List val)) : result
  | REF.EXN_ADDRTHROW_REF (exnaddr : exnaddr) : result
  | TRAP : result
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:51.8-51.14 -/
inductive wf_result : result -> Prop where
  | result_case_0 : forall (val* : (List val)), 
    Forall (fun (val : val) => (wf_val val)) val* ->
    wf_result (._VALS (List.map (fun (val : val) => val) val*))
  | result_case_1 : forall (exnaddr : exnaddr), wf_result (.REF.EXN_ADDRTHROW_REF exnaddr)
  | result_case_2 : wf_result .TRAP

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:60.1-60.72 -/
inductive hostfunc : Type where
  |  : hostfunc
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:61.1-61.73 -/
inductive funccode : Type where
  | FUNC (typeidx : typeidx) ((List.map (fun (local : «local») => «local») local*) : (List «local»)) (expr : expr) : funccode
  |  : funccode
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:61.8-61.16 -/
inductive wf_funccode : funccode -> Prop where
  | funccode_case_0 : forall (typeidx : typeidx) (local* : (List «local»)) (expr : expr), 
    (wf_uN 32 typeidx) ->
    Forall (fun (local : «local») => (wf_local «local»)) local* ->
    Forall (fun (expr : instr) => (wf_instr expr)) expr ->
    wf_funccode (.FUNC typeidx (List.map (fun (local : «local») => «local») local*) expr)
  | funccode_case_1 : wf_funccode .

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
  | PACK (packtype : packtype) (iN : iN) : packval
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:88.8-88.15 -/
inductive wf_packval : packval -> Prop where
  | packval_case_0 : forall (packtype : packtype) (iN : iN), 
    (wf_uN (psize packtype) iN) ->
    wf_packval (.PACK packtype iN)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:91.1-92.18 -/
inductive fieldval : Type where
  | CONST (numtype : numtype) (num_ : num_) : fieldval
  | VCONST (vectype : vectype) (vec_ : vec_) : fieldval
  | REF.NULL (heaptype : heaptype) : fieldval
  | REF.I31_NUM (u31 : u31) : fieldval
  | REF.STRUCT_ADDR (structaddr : structaddr) : fieldval
  | REF.ARRAY_ADDR (arrayaddr : arrayaddr) : fieldval
  | REF.FUNC_ADDR (funcaddr : funcaddr) : fieldval
  | REF.EXN_ADDR (exnaddr : exnaddr) : fieldval
  | REF.HOST_ADDR (hostaddr : hostaddr) : fieldval
  | REF.EXTERN (addrref : addrref) : fieldval
  | PACK (packtype : packtype) (iN : iN) : fieldval
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
opaque fieldval_val : forall (_ : val), fieldval := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:91.8-91.16 -/
inductive wf_fieldval : fieldval -> Prop where
  | fieldval_case_0 : forall (numtype : numtype) (num_ : num_), 
    (wf_num_ numtype num_) ->
    wf_fieldval (.CONST numtype num_)
  | fieldval_case_1 : forall (vectype : vectype) (vec_ : vec_), 
    (wf_uN (vsize vectype) vec_) ->
    wf_fieldval (.VCONST vectype vec_)
  | fieldval_case_2 : forall (heaptype : heaptype), 
    (wf_heaptype heaptype) ->
    wf_fieldval (.REF.NULL heaptype)
  | fieldval_case_3 : forall (u31 : u31), 
    (wf_uN 31 u31) ->
    wf_fieldval (.REF.I31_NUM u31)
  | fieldval_case_4 : forall (structaddr : structaddr), wf_fieldval (.REF.STRUCT_ADDR structaddr)
  | fieldval_case_5 : forall (arrayaddr : arrayaddr), wf_fieldval (.REF.ARRAY_ADDR arrayaddr)
  | fieldval_case_6 : forall (funcaddr : funcaddr), wf_fieldval (.REF.FUNC_ADDR funcaddr)
  | fieldval_case_7 : forall (exnaddr : exnaddr), wf_fieldval (.REF.EXN_ADDR exnaddr)
  | fieldval_case_8 : forall (hostaddr : hostaddr), wf_fieldval (.REF.HOST_ADDR hostaddr)
  | fieldval_case_9 : forall (addrref : addrref), 
    (wf_addrref addrref) ->
    wf_fieldval (.REF.EXTERN addrref)
  | fieldval_case_10 : forall (packtype : packtype) (iN : iN), 
    (wf_uN (psize packtype) iN) ->
    wf_fieldval (.PACK packtype iN)

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
  |  (store : store) (frame : frame) : state
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:147.8-147.13 -/
inductive wf_state : state -> Prop where
  | state_case_0 : forall (store : store) (frame : frame), 
    (wf_store store) ->
    (wf_frame frame) ->
    wf_state (. store frame)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:148.1-148.57 -/
inductive config : Type where
  |  (state : state) ((List.map (fun (instr : instr) => instr) instr*) : (List instr)) : config
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:148.8-148.14 -/
inductive wf_config : config -> Prop where
  | config_case_0 : forall (state : state) (instr* : (List instr)), 
    (wf_state state) ->
    Forall (fun (instr : instr) => (wf_instr instr)) instr* ->
    wf_config (. state (List.map (fun (instr : instr) => instr) instr*))

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:175.1-175.31 -/
def Ki : Nat := 1024

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:181.1-181.100 -/
opaque packfield_ : forall (storagetype : storagetype) (val : val), fieldval := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:182.1-182.112 -/
opaque unpackfield_ : forall (storagetype : storagetype) (_ : (Option sx)) (fieldval : fieldval), val := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:193.1-193.86 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:193.1-193.86 -/
opaque tagsxa : forall (_ : (List externaddr)), (List tagaddr) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:194.1-194.89 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:194.1-194.89 -/
opaque globalsxa : forall (_ : (List externaddr)), (List globaladdr) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:195.1-195.86 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:195.1-195.86 -/
opaque memsxa : forall (_ : (List externaddr)), (List memaddr) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:196.1-196.88 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:196.1-196.88 -/
opaque tablesxa : forall (_ : (List externaddr)), (List tableaddr) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:197.1-197.87 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:197.1-197.87 -/
opaque funcsxa : forall (_ : (List externaddr)), (List funcaddr) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:222.1-222.74 -/
opaque store : forall (state : state), store := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:223.1-223.74 -/
opaque frame : forall (state : state), frame := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:228.1-228.76 -/
opaque tagaddr : forall (state : state), (List tagaddr) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:231.1-231.76 -/
opaque moduleinst : forall (state : state), moduleinst := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:232.1-232.76 -/
opaque taginst : forall (state : state), (List taginst) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:233.1-233.76 -/
opaque globalinst : forall (state : state), (List globalinst) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:234.1-234.76 -/
opaque meminst : forall (state : state), (List meminst) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:235.1-235.76 -/
opaque tableinst : forall (state : state), (List tableinst) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:236.1-236.76 -/
opaque funcinst : forall (state : state), (List funcinst) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:237.1-237.76 -/
opaque datainst : forall (state : state), (List datainst) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:238.1-238.76 -/
opaque eleminst : forall (state : state), (List eleminst) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:239.1-239.76 -/
opaque structinst : forall (state : state), (List structinst) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:240.1-240.76 -/
opaque arrayinst : forall (state : state), (List arrayinst) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:241.1-241.76 -/
opaque exninst : forall (state : state), (List exninst) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:256.1-256.85 -/
opaque type : forall (state : state) (typeidx : typeidx), deftype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:257.1-257.85 -/
opaque tag : forall (state : state) (tagidx : tagidx), taginst := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:258.1-258.85 -/
opaque global : forall (state : state) (globalidx : globalidx), globalinst := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:259.1-259.85 -/
opaque mem : forall (state : state) (memidx : memidx), meminst := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:260.1-260.85 -/
opaque table : forall (state : state) (tableidx : tableidx), tableinst := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:261.1-261.85 -/
opaque func : forall (state : state) (funcidx : funcidx), funcinst := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:262.1-262.85 -/
opaque data : forall (state : state) (dataidx : dataidx), datainst := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:263.1-263.85 -/
opaque elem : forall (state : state) (tableidx : tableidx), eleminst := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:264.1-264.85 -/
opaque «local» : forall (state : state) (localidx : localidx), (Option val) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:279.1-279.165 -/
opaque with_local : forall (state : state) (localidx : localidx) (val : val), state := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:280.1-280.172 -/
opaque with_global : forall (state : state) (globalidx : globalidx) (val : val), state := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:281.1-281.174 -/
opaque with_table : forall (state : state) (tableidx : tableidx) (nat : Nat) (ref : ref), state := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:282.1-282.165 -/
opaque with_tableinst : forall (state : state) (tableidx : tableidx) (tableinst : tableinst), state := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:283.1-283.176 -/
opaque with_mem : forall (state : state) (memidx : memidx) (nat : Nat) (nat : Nat) (_ : (List byte)), state := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:284.1-284.167 -/
opaque with_meminst : forall (state : state) (memidx : memidx) (meminst : meminst), state := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:285.1-285.169 -/
opaque with_elem : forall (state : state) (elemidx : elemidx) (_ : (List ref)), state := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:286.1-286.170 -/
opaque with_data : forall (state : state) (dataidx : dataidx) (_ : (List byte)), state := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:287.1-287.181 -/
opaque with_struct : forall (state : state) (structaddr : structaddr) (nat : Nat) (fieldval : fieldval), state := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:288.1-288.180 -/
opaque with_array : forall (state : state) (arrayaddr : arrayaddr) (nat : Nat) (fieldval : fieldval), state := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:302.1-302.140 -/
opaque add_structinst : forall (state : state) (_ : (List structinst)), state := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:303.1-303.139 -/
opaque add_arrayinst : forall (state : state) (_ : (List arrayinst)), state := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:304.1-304.137 -/
opaque add_exninst : forall (state : state) (_ : (List exninst)), state := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:313.1-313.62 -/
opaque growtable : forall (tableinst : tableinst) (nat : Nat) (ref : ref), (Option tableinst) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:314.1-314.62 -/
opaque growmem : forall (meminst : meminst) (nat : Nat), (Option meminst) := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.1-execution.values.spectec:23.1-23.60 -/
inductive Num_ok : store -> num -> numtype -> Prop where
  |  : forall (s : store) (nt : numtype) (c : num_), 
    (wf_store s) ->
    (wf_num (.CONST nt c)) ->
    Num_ok s (.CONST nt c) nt

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.1-execution.values.spectec:24.1-24.60 -/
inductive Vec_ok : store -> vec -> vectype -> Prop where
  |  : forall (s : store) (vt : vectype) (c : vec_), 
    (wf_store s) ->
    (wf_vec (.VCONST vt c)) ->
    Vec_ok s (.VCONST vt c) vt

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.1-execution.values.spectec:25.1-25.60 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.1-execution.values.spectec:25.1-25.60 -/
inductive Ref_ok : store -> ref -> reftype -> Prop where
  | null : forall (s : store) (ht : heaptype) (ht' : heaptype), 
    (wf_store s) ->
    (wf_ref (.REF.NULL ht)) ->
    (wf_reftype (.REF (some .NULL) ht')) ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (Heaptype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } ht' ht) ->
    Ref_ok s (.REF.NULL ht) (.REF (some .NULL) ht')
  | i31 : forall (s : store) (i : u31), 
    (wf_store s) ->
    (wf_ref (.REF.I31_NUM i)) ->
    (wf_reftype (.REF none .I31)) ->
    Ref_ok s (.REF.I31_NUM i) (.REF none .I31)
  | struct : forall (s : store) (a : addr) (dt : deftype), 
    (wf_store s) ->
    (wf_ref (.REF.STRUCT_ADDR a)) ->
    (wf_reftype (.REF none (heaptype_deftype dt))) ->
    (a < (List.length (s.STRUCTS))) ->
    ((((s.STRUCTS)[a]!).TYPE) == dt) ->
    Ref_ok s (.REF.STRUCT_ADDR a) (.REF none (heaptype_deftype dt))
  | array : forall (s : store) (a : addr) (dt : deftype), 
    (wf_store s) ->
    (wf_ref (.REF.ARRAY_ADDR a)) ->
    (wf_reftype (.REF none (heaptype_deftype dt))) ->
    (a < (List.length (s.ARRAYS))) ->
    ((((s.ARRAYS)[a]!).TYPE) == dt) ->
    Ref_ok s (.REF.ARRAY_ADDR a) (.REF none (heaptype_deftype dt))
  | func : forall (s : store) (a : addr) (dt : deftype), 
    (wf_store s) ->
    (wf_ref (.REF.FUNC_ADDR a)) ->
    (wf_reftype (.REF none (heaptype_deftype dt))) ->
    (a < (List.length (s.FUNCS))) ->
    ((((s.FUNCS)[a]!).TYPE) == dt) ->
    Ref_ok s (.REF.FUNC_ADDR a) (.REF none (heaptype_deftype dt))
  | exn : forall (s : store) (a : addr) (exn : exninst), 
    (wf_store s) ->
    (wf_exninst exn) ->
    (wf_ref (.REF.EXN_ADDR a)) ->
    (wf_reftype (.REF none .EXN)) ->
    (a < (List.length (s.EXNS))) ->
    (((s.EXNS)[a]!) == exn) ->
    Ref_ok s (.REF.EXN_ADDR a) (.REF none .EXN)
  | host : forall (s : store) (a : addr), 
    (wf_store s) ->
    (wf_ref (.REF.HOST_ADDR a)) ->
    (wf_reftype (.REF none .ANY)) ->
    Ref_ok s (.REF.HOST_ADDR a) (.REF none .ANY)
  | extern : forall (s : store) (addrref : addrref), 
    (wf_store s) ->
    (wf_ref (.REF.EXTERN addrref)) ->
    (wf_reftype (.REF none .EXTERN)) ->
    (wf_reftype (.REF none .ANY)) ->
    (Ref_ok s (ref_addrref addrref) (.REF none .ANY)) ->
    Ref_ok s (.REF.EXTERN addrref) (.REF none .EXTERN)
  | sub : forall (s : store) (ref : ref) (rt : reftype) (rt' : reftype), 
    (wf_store s) ->
    (wf_ref ref) ->
    (wf_reftype rt) ->
    (wf_reftype rt') ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (Ref_ok s ref rt') ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt' rt) ->
    Ref_ok s ref rt

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.1-execution.values.spectec:26.1-26.60 -/
inductive Val_ok : store -> val -> valtype -> Prop where
  | num : forall (s : store) (num : num) (nt : numtype), 
    (wf_store s) ->
    (wf_num num) ->
    (Num_ok s num nt) ->
    Val_ok s (val_num num) (valtype_numtype nt)
  | vec : forall (s : store) (vec : vec) (vt : vectype), 
    (wf_store s) ->
    (wf_vec vec) ->
    (Vec_ok s vec vt) ->
    Val_ok s (val_vec vec) (valtype_vectype vt)
  | ref : forall (s : store) (ref : ref) (rt : reftype), 
    (wf_store s) ->
    (wf_ref ref) ->
    (wf_reftype rt) ->
    (Ref_ok s ref rt) ->
    Val_ok s (val_ref ref) (valtype_reftype rt)

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.1-execution.values.spectec:86.1-86.84 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.1-execution.values.spectec:86.1-86.84 -/
inductive Externaddr_ok : store -> externaddr -> externtype -> Prop where
  | tag : forall (s : store) (a : addr) (taginst : taginst), 
    (wf_store s) ->
    (wf_externtype (.TAG (taginst.TYPE))) ->
    (a < (List.length (s.TAGS))) ->
    (((s.TAGS)[a]!) == taginst) ->
    Externaddr_ok s (.TAG a) (.TAG (taginst.TYPE))
  | global : forall (s : store) (a : addr) (globalinst : globalinst), 
    (wf_store s) ->
    (wf_externtype (.GLOBAL (globalinst.TYPE))) ->
    (a < (List.length (s.GLOBALS))) ->
    (((s.GLOBALS)[a]!) == globalinst) ->
    Externaddr_ok s (.GLOBAL a) (.GLOBAL (globalinst.TYPE))
  | mem : forall (s : store) (a : addr) (meminst : meminst), 
    (wf_store s) ->
    (wf_externtype (.MEM (meminst.TYPE))) ->
    (a < (List.length (s.MEMS))) ->
    (((s.MEMS)[a]!) == meminst) ->
    Externaddr_ok s (.MEM a) (.MEM (meminst.TYPE))
  | table : forall (s : store) (a : addr) (tableinst : tableinst), 
    (wf_store s) ->
    (wf_externtype (.TABLE (tableinst.TYPE))) ->
    (a < (List.length (s.TABLES))) ->
    (((s.TABLES)[a]!) == tableinst) ->
    Externaddr_ok s (.TABLE a) (.TABLE (tableinst.TYPE))
  | func : forall (s : store) (a : addr) (funcinst : funcinst), 
    (wf_store s) ->
    (wf_externtype (.FUNC (typeuse_deftype (funcinst.TYPE)))) ->
    (a < (List.length (s.FUNCS))) ->
    (((s.FUNCS)[a]!) == funcinst) ->
    Externaddr_ok s (.FUNC a) (.FUNC (typeuse_deftype (funcinst.TYPE)))
  | sub : forall (s : store) (externaddr : externaddr) (xt : externtype) (xt' : externtype), 
    (wf_store s) ->
    (wf_externtype xt) ->
    (wf_externtype xt') ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (Externaddr_ok s externaddr xt') ->
    (Externtype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } xt' xt) ->
    Externaddr_ok s externaddr xt

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.2-execution.types.spectec:5.1-5.96 -/
opaque inst_valtype : forall (moduleinst : moduleinst) (valtype : valtype), valtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.2-execution.types.spectec:6.1-6.96 -/
opaque inst_reftype : forall (moduleinst : moduleinst) (reftype : reftype), reftype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.2-execution.types.spectec:7.1-7.105 -/
opaque inst_globaltype : forall (moduleinst : moduleinst) (globaltype : globaltype), globaltype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.2-execution.types.spectec:8.1-8.96 -/
opaque inst_memtype : forall (moduleinst : moduleinst) (memtype : memtype), memtype := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.2-execution.types.spectec:9.1-9.102 -/
opaque inst_tabletype : forall (moduleinst : moduleinst) (tabletype : tabletype), tabletype := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:131.1-133.15 -/
inductive Step_pure_before_br_on_null-addr : (List instr) -> Prop where
  | br_on_null-null_0 : forall (val : val) (l : labelidx) (ht : heaptype), 
    (wf_val val) ->
    (wf_instr (.BR_ON_NULL l)) ->
    (wf_instr (.BR l)) ->
    (wf_val (.REF.NULL ht)) ->
    (val == (.REF.NULL ht)) ->
    Step_pure_before_br_on_null-addr [(instr_val val), (.BR_ON_NULL l)]

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:140.1-142.15 -/
inductive Step_pure_before_br_on_non_null-addr : (List instr) -> Prop where
  | br_on_non_null-null_0 : forall (val : val) (l : labelidx) (ht : heaptype), 
    (wf_val val) ->
    (wf_instr (.BR_ON_NON_NULL l)) ->
    (wf_val (.REF.NULL ht)) ->
    (val == (.REF.NULL ht)) ->
    Step_pure_before_br_on_non_null-addr [(instr_val val), (.BR_ON_NON_NULL l)]

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:632.1-634.15 -/
inductive Step_pure_before_ref.is_null-false : (List instr) -> Prop where
  | ref.is_null-true_0 : forall (ref : ref) (ht : heaptype), 
    (wf_ref ref) ->
    (wf_instr .REF.IS_NULL) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. 1)))) ->
    (wf_ref (.REF.NULL ht)) ->
    (ref == (.REF.NULL ht)) ->
    Step_pure_before_ref.is_null-false [(instr_ref ref), .REF.IS_NULL]

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:641.1-643.15 -/
inductive Step_pure_before_ref.as_non_null-addr : (List instr) -> Prop where
  | ref.as_non_null-null_0 : forall (ref : ref) (ht : heaptype), 
    (wf_ref ref) ->
    (wf_instr .REF.AS_NON_NULL) ->
    (wf_instr .TRAP) ->
    (wf_ref (.REF.NULL ht)) ->
    (ref == (.REF.NULL ht)) ->
    Step_pure_before_ref.as_non_null-addr [(instr_ref ref), .REF.AS_NON_NULL]

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:650.1-653.22 -/
inductive Step_pure_before_ref.eq-true : (List instr) -> Prop where
  | ref.eq-null_0 : forall (ref_1 : ref) (ref_2 : ref) (ht_1 : heaptype) (ht_2 : heaptype), 
    (wf_ref ref_1) ->
    (wf_ref ref_2) ->
    (wf_instr .REF.EQ) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. 1)))) ->
    (wf_ref (.REF.NULL ht_1)) ->
    (wf_ref (.REF.NULL ht_2)) ->
    ((ref_1 == (.REF.NULL ht_1)) && (ref_2 == (.REF.NULL ht_2))) ->
    Step_pure_before_ref.eq-true [(instr_ref ref_1), (instr_ref ref_2), .REF.EQ]

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:655.1-657.15 -/
inductive Step_pure_before_ref.eq-false : (List instr) -> Prop where
  | ref.eq-true_0 : forall (ref_1 : ref) (ref_2 : ref), 
    (wf_ref ref_1) ->
    (wf_ref ref_2) ->
    (wf_instr .REF.EQ) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. 1)))) ->
    (¬(Step_pure_before_ref.eq-true [(instr_ref ref_1), (instr_ref ref_2), .REF.EQ])) ->
    (ref_1 == ref_2) ->
    Step_pure_before_ref.eq-false [(instr_ref ref_1), (instr_ref ref_2), .REF.EQ]
  | ref.eq-null_1 : forall (ref_1 : ref) (ref_2 : ref) (ht_1 : heaptype) (ht_2 : heaptype), 
    (wf_ref ref_1) ->
    (wf_ref ref_2) ->
    (wf_instr .REF.EQ) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. 1)))) ->
    (wf_ref (.REF.NULL ht_1)) ->
    (wf_ref (.REF.NULL ht_2)) ->
    ((ref_1 == (.REF.NULL ht_1)) && (ref_2 == (.REF.NULL ht_2))) ->
    Step_pure_before_ref.eq-false [(instr_ref ref_1), (instr_ref ref_2), .REF.EQ]

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:6.1-6.88 -/
inductive Step_pure : (List instr) -> (List instr) -> Prop where
  | unreachable : 
    (wf_instr .UNREACHABLE) ->
    (wf_instr .TRAP) ->
    Step_pure [.UNREACHABLE] [.TRAP]
  | nop : 
    (wf_instr .NOP) ->
    Step_pure [.NOP] []
  | drop : forall (val : val), 
    (wf_val val) ->
    (wf_instr .DROP) ->
    Step_pure [(instr_val val), .DROP] []
  | select-true : forall (val_1 : val) (val_2 : val) (c : num_) (t*? : (Option (List valtype))), 
    (wf_val val_1) ->
    (wf_val val_2) ->
    (wf_instr (.CONST .I32 c)) ->
    (wf_instr (.SELECT (Option.map (fun (t* : (List valtype)) => (List.map (fun (t : valtype) => t) t*)) t*?))) ->
    ((proj_num__0 .I32 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 .I32 c))) != 0) ->
    Step_pure [(instr_val val_1), (instr_val val_2), (.CONST .I32 c), (.SELECT (Option.map (fun (t* : (List valtype)) => (List.map (fun (t : valtype) => t) t*)) t*?))] [(instr_val val_1)]
  | select-false : forall (val_1 : val) (val_2 : val) (c : num_) (t*? : (Option (List valtype))), 
    (wf_val val_1) ->
    (wf_val val_2) ->
    (wf_instr (.CONST .I32 c)) ->
    (wf_instr (.SELECT (Option.map (fun (t* : (List valtype)) => (List.map (fun (t : valtype) => t) t*)) t*?))) ->
    ((proj_num__0 .I32 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 .I32 c))) == 0) ->
    Step_pure [(instr_val val_1), (instr_val val_2), (.CONST .I32 c), (.SELECT (Option.map (fun (t* : (List valtype)) => (List.map (fun (t : valtype) => t) t*)) t*?))] [(instr_val val_2)]
  | if-true : forall (c : num_) (bt : blocktype) (instr_1* : (List instr)) (instr_2* : (List instr)), 
    (wf_instr (.CONST .I32 c)) ->
    (wf_instr (.IFELSE bt (List.map (fun (instr_1 : instr) => instr_1) instr_1*) (List.map (fun (instr_2 : instr) => instr_2) instr_2*))) ->
    (wf_instr (.BLOCK bt (List.map (fun (instr_1 : instr) => instr_1) instr_1*))) ->
    ((proj_num__0 .I32 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 .I32 c))) != 0) ->
    Step_pure [(.CONST .I32 c), (.IFELSE bt (List.map (fun (instr_1 : instr) => instr_1) instr_1*) (List.map (fun (instr_2 : instr) => instr_2) instr_2*))] [(.BLOCK bt (List.map (fun (instr_1 : instr) => instr_1) instr_1*))]
  | if-false : forall (c : num_) (bt : blocktype) (instr_1* : (List instr)) (instr_2* : (List instr)), 
    (wf_instr (.CONST .I32 c)) ->
    (wf_instr (.IFELSE bt (List.map (fun (instr_1 : instr) => instr_1) instr_1*) (List.map (fun (instr_2 : instr) => instr_2) instr_2*))) ->
    (wf_instr (.BLOCK bt (List.map (fun (instr_2 : instr) => instr_2) instr_2*))) ->
    ((proj_num__0 .I32 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 .I32 c))) == 0) ->
    Step_pure [(.CONST .I32 c), (.IFELSE bt (List.map (fun (instr_1 : instr) => instr_1) instr_1*) (List.map (fun (instr_2 : instr) => instr_2) instr_2*))] [(.BLOCK bt (List.map (fun (instr_2 : instr) => instr_2) instr_2*))]
  | label-vals : forall (n : n) (instr* : (List instr)) (val* : (List val)), 
    (wf_instr (.LABEL_ n (List.map (fun (instr : instr) => instr) instr*) (List.map (fun (val : val) => (instr_val val)) val*))) ->
    Step_pure [(.LABEL_ n (List.map (fun (instr : instr) => instr) instr*) (List.map (fun (val : val) => (instr_val val)) val*))] (List.map (fun (val : val) => (instr_val val)) val*)
  | br-label-zero : forall (n : n) (instr'* : (List instr)) (val'* : (List val)) (val* : (List val)) (l : labelidx) (instr* : (List instr)), 
    ((List.length val*) == n) ->
    (wf_instr (.LABEL_ n (List.map (fun (instr' : instr) => instr') instr'*) ((List.map (fun (val' : val) => (instr_val val')) val'*) ++ ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([(.BR l)] ++ (List.map (fun (instr : instr) => instr) instr*)))))) ->
    ((proj_uN_0 l) == 0) ->
    Step_pure [(.LABEL_ n (List.map (fun (instr' : instr) => instr') instr'*) ((List.map (fun (val' : val) => (instr_val val')) val'*) ++ ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([(.BR l)] ++ (List.map (fun (instr : instr) => instr) instr*)))))] ((List.map (fun (val : val) => (instr_val val)) val*) ++ (List.map (fun (instr' : instr) => instr') instr'*))
  | br-label-succ : forall (n : n) (instr'* : (List instr)) (val* : (List val)) (l : labelidx) (instr* : (List instr)), 
    (wf_instr (.LABEL_ n (List.map (fun (instr' : instr) => instr') instr'*) ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([(.BR l)] ++ (List.map (fun (instr : instr) => instr) instr*))))) ->
    (wf_instr (.BR (. ((((proj_uN_0 l) : Nat) - (1 : Nat)) : Nat)))) ->
    ((proj_uN_0 l) > 0) ->
    Step_pure [(.LABEL_ n (List.map (fun (instr' : instr) => instr') instr'*) ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([(.BR l)] ++ (List.map (fun (instr : instr) => instr) instr*))))] ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.BR (. ((((proj_uN_0 l) : Nat) - (1 : Nat)) : Nat)))])
  | br-handler : forall (n : n) (catch* : (List «catch»)) (val* : (List val)) (l : labelidx) (instr* : (List instr)), 
    (wf_instr (.HANDLER_ n (List.map (fun (catch : «catch») => «catch») catch*) ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([(.BR l)] ++ (List.map (fun (instr : instr) => instr) instr*))))) ->
    (wf_instr (.BR l)) ->
    Step_pure [(.HANDLER_ n (List.map (fun (catch : «catch») => «catch») catch*) ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([(.BR l)] ++ (List.map (fun (instr : instr) => instr) instr*))))] ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.BR l)])
  | br_if-true : forall (c : num_) (l : labelidx), 
    (wf_instr (.CONST .I32 c)) ->
    (wf_instr (.BR_IF l)) ->
    (wf_instr (.BR l)) ->
    ((proj_num__0 .I32 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 .I32 c))) != 0) ->
    Step_pure [(.CONST .I32 c), (.BR_IF l)] [(.BR l)]
  | br_if-false : forall (c : num_) (l : labelidx), 
    (wf_instr (.CONST .I32 c)) ->
    (wf_instr (.BR_IF l)) ->
    ((proj_num__0 .I32 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 .I32 c))) == 0) ->
    Step_pure [(.CONST .I32 c), (.BR_IF l)] []
  | br_table-lt : forall (i : num_) (l* : (List labelidx)) (l' : labelidx), 
    ((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) < (List.length (List.map (fun (l : labelidx) => l) l*))) ->
    ((proj_num__0 .I32 i) != none) ->
    (wf_instr (.CONST .I32 i)) ->
    (wf_instr (.BR_TABLE (List.map (fun (l : labelidx) => l) l*) l')) ->
    (wf_instr (.BR ((List.map (fun (l : labelidx) => l) l*)[(proj_uN_0 (Option.get! (proj_num__0 .I32 i)))]!))) ->
    Step_pure [(.CONST .I32 i), (.BR_TABLE (List.map (fun (l : labelidx) => l) l*) l')] [(.BR ((List.map (fun (l : labelidx) => l) l*)[(proj_uN_0 (Option.get! (proj_num__0 .I32 i)))]!))]
  | br_table-ge : forall (i : num_) (l* : (List labelidx)) (l' : labelidx), 
    (wf_instr (.CONST .I32 i)) ->
    (wf_instr (.BR_TABLE (List.map (fun (l : labelidx) => l) l*) l')) ->
    (wf_instr (.BR l')) ->
    ((proj_num__0 .I32 i) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) >= (List.length (List.map (fun (l : labelidx) => l) l*))) ->
    Step_pure [(.CONST .I32 i), (.BR_TABLE (List.map (fun (l : labelidx) => l) l*) l')] [(.BR l')]
  | br_on_null-null : forall (val : val) (l : labelidx) (ht : heaptype), 
    (wf_val val) ->
    (wf_instr (.BR_ON_NULL l)) ->
    (wf_instr (.BR l)) ->
    (wf_val (.REF.NULL ht)) ->
    (val == (.REF.NULL ht)) ->
    Step_pure [(instr_val val), (.BR_ON_NULL l)] [(.BR l)]
  | br_on_null-addr : forall (val : val) (l : labelidx), 
    (wf_val val) ->
    (wf_instr (.BR_ON_NULL l)) ->
    (¬(Step_pure_before_br_on_null-addr [(instr_val val), (.BR_ON_NULL l)])) ->
    Step_pure [(instr_val val), (.BR_ON_NULL l)] [(instr_val val)]
  | br_on_non_null-null : forall (val : val) (l : labelidx) (ht : heaptype), 
    (wf_val val) ->
    (wf_instr (.BR_ON_NON_NULL l)) ->
    (wf_val (.REF.NULL ht)) ->
    (val == (.REF.NULL ht)) ->
    Step_pure [(instr_val val), (.BR_ON_NON_NULL l)] []
  | br_on_non_null-addr : forall (val : val) (l : labelidx), 
    (wf_val val) ->
    (wf_instr (.BR_ON_NON_NULL l)) ->
    (wf_instr (.BR l)) ->
    (¬(Step_pure_before_br_on_non_null-addr [(instr_val val), (.BR_ON_NON_NULL l)])) ->
    Step_pure [(instr_val val), (.BR_ON_NON_NULL l)] [(instr_val val), (.BR l)]
  | call_indirect : forall (x : idx) (yy : typeuse), 
    (wf_instr (.CALL_INDIRECT x yy)) ->
    (wf_instr (.TABLE.GET x)) ->
    (wf_instr (.REF.CAST (.REF (some .NULL) (heaptype_typeuse yy)))) ->
    (wf_instr (.CALL_REF yy)) ->
    Step_pure [(.CALL_INDIRECT x yy)] [(.TABLE.GET x), (.REF.CAST (.REF (some .NULL) (heaptype_typeuse yy))), (.CALL_REF yy)]
  | return_call_indirect : forall (x : idx) (yy : typeuse), 
    (wf_instr (.RETURN_CALL_INDIRECT x yy)) ->
    (wf_instr (.TABLE.GET x)) ->
    (wf_instr (.REF.CAST (.REF (some .NULL) (heaptype_typeuse yy)))) ->
    (wf_instr (.RETURN_CALL_REF yy)) ->
    Step_pure [(.RETURN_CALL_INDIRECT x yy)] [(.TABLE.GET x), (.REF.CAST (.REF (some .NULL) (heaptype_typeuse yy))), (.RETURN_CALL_REF yy)]
  | frame-vals : forall (n : n) (f : frame) (val* : (List val)), 
    ((List.length val*) == n) ->
    (wf_instr (.FRAME_ n f (List.map (fun (val : val) => (instr_val val)) val*))) ->
    Step_pure [(.FRAME_ n f (List.map (fun (val : val) => (instr_val val)) val*))] (List.map (fun (val : val) => (instr_val val)) val*)
  | return-frame : forall (n : n) (f : frame) (val'* : (List val)) (val* : (List val)) (instr* : (List instr)), 
    ((List.length val*) == n) ->
    (wf_instr (.FRAME_ n f ((List.map (fun (val' : val) => (instr_val val')) val'*) ++ ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([.RETURN] ++ (List.map (fun (instr : instr) => instr) instr*)))))) ->
    Step_pure [(.FRAME_ n f ((List.map (fun (val' : val) => (instr_val val')) val'*) ++ ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([.RETURN] ++ (List.map (fun (instr : instr) => instr) instr*)))))] (List.map (fun (val : val) => (instr_val val)) val*)
  | return-label : forall (n : n) (instr'* : (List instr)) (val* : (List val)) (instr* : (List instr)), 
    (wf_instr (.LABEL_ n (List.map (fun (instr' : instr) => instr') instr'*) ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([.RETURN] ++ (List.map (fun (instr : instr) => instr) instr*))))) ->
    (wf_instr .RETURN) ->
    Step_pure [(.LABEL_ n (List.map (fun (instr' : instr) => instr') instr'*) ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([.RETURN] ++ (List.map (fun (instr : instr) => instr) instr*))))] ((List.map (fun (val : val) => (instr_val val)) val*) ++ [.RETURN])
  | return-handler : forall (n : n) (catch* : (List «catch»)) (val* : (List val)) (instr* : (List instr)), 
    (wf_instr (.HANDLER_ n (List.map (fun (catch : «catch») => «catch») catch*) ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([.RETURN] ++ (List.map (fun (instr : instr) => instr) instr*))))) ->
    (wf_instr .RETURN) ->
    Step_pure [(.HANDLER_ n (List.map (fun (catch : «catch») => «catch») catch*) ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([.RETURN] ++ (List.map (fun (instr : instr) => instr) instr*))))] ((List.map (fun (val : val) => (instr_val val)) val*) ++ [.RETURN])
  | handler-vals : forall (n : n) (catch* : (List «catch»)) (val* : (List val)), 
    (wf_instr (.HANDLER_ n (List.map (fun (catch : «catch») => «catch») catch*) (List.map (fun (val : val) => (instr_val val)) val*))) ->
    Step_pure [(.HANDLER_ n (List.map (fun (catch : «catch») => «catch») catch*) (List.map (fun (val : val) => (instr_val val)) val*))] (List.map (fun (val : val) => (instr_val val)) val*)
  | trap-instrs : forall (val* : (List val)) (instr* : (List instr)), 
    Forall (fun (val : val) => (wf_val val)) val* ->
    Forall (fun (instr : instr) => (wf_instr instr)) instr* ->
    (wf_instr .TRAP) ->
    (((List.map (fun (val : val) => val) val*) != []) || ((List.map (fun (instr : instr) => instr) instr*) != [])) ->
    Step_pure ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([.TRAP] ++ (List.map (fun (instr : instr) => instr) instr*))) [.TRAP]
  | trap-label : forall (n : n) (instr'* : (List instr)), 
    (wf_instr (.LABEL_ n (List.map (fun (instr' : instr) => instr') instr'*) [.TRAP])) ->
    (wf_instr .TRAP) ->
    Step_pure [(.LABEL_ n (List.map (fun (instr' : instr) => instr') instr'*) [.TRAP])] [.TRAP]
  | trap-frame : forall (n : n) (f : frame), 
    (wf_instr (.FRAME_ n f [.TRAP])) ->
    (wf_instr .TRAP) ->
    Step_pure [(.FRAME_ n f [.TRAP])] [.TRAP]
  | local.tee : forall (val : val) (x : idx), 
    (wf_val val) ->
    (wf_instr (.LOCAL.TEE x)) ->
    (wf_instr (.LOCAL.SET x)) ->
    Step_pure [(instr_val val), (.LOCAL.TEE x)] [(instr_val val), (instr_val val), (.LOCAL.SET x)]
  | ref.i31 : forall (i : num_), 
    ((proj_num__0 .I32 i) != none) ->
    (wf_instr (.CONST .I32 i)) ->
    (wf_instr .REF.I31) ->
    (wf_instr (.REF.I31_NUM (wrap__ 32 31 (Option.get! (proj_num__0 .I32 i))))) ->
    Step_pure [(.CONST .I32 i), .REF.I31] [(.REF.I31_NUM (wrap__ 32 31 (Option.get! (proj_num__0 .I32 i))))]
  | ref.is_null-true : forall (ref : ref) (ht : heaptype), 
    (wf_ref ref) ->
    (wf_instr .REF.IS_NULL) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. 1)))) ->
    (wf_ref (.REF.NULL ht)) ->
    (ref == (.REF.NULL ht)) ->
    Step_pure [(instr_ref ref), .REF.IS_NULL] [(.CONST .I32 (.mk_num__0 .I32 (. 1)))]
  | ref.is_null-false : forall (ref : ref), 
    (wf_ref ref) ->
    (wf_instr .REF.IS_NULL) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. 0)))) ->
    (¬(Step_pure_before_ref.is_null-false [(instr_ref ref), .REF.IS_NULL])) ->
    Step_pure [(instr_ref ref), .REF.IS_NULL] [(.CONST .I32 (.mk_num__0 .I32 (. 0)))]
  | ref.as_non_null-null : forall (ref : ref) (ht : heaptype), 
    (wf_ref ref) ->
    (wf_instr .REF.AS_NON_NULL) ->
    (wf_instr .TRAP) ->
    (wf_ref (.REF.NULL ht)) ->
    (ref == (.REF.NULL ht)) ->
    Step_pure [(instr_ref ref), .REF.AS_NON_NULL] [.TRAP]
  | ref.as_non_null-addr : forall (ref : ref), 
    (wf_ref ref) ->
    (wf_instr .REF.AS_NON_NULL) ->
    (¬(Step_pure_before_ref.as_non_null-addr [(instr_ref ref), .REF.AS_NON_NULL])) ->
    Step_pure [(instr_ref ref), .REF.AS_NON_NULL] [(instr_ref ref)]
  | ref.eq-null : forall (ref_1 : ref) (ref_2 : ref) (ht_1 : heaptype) (ht_2 : heaptype), 
    (wf_ref ref_1) ->
    (wf_ref ref_2) ->
    (wf_instr .REF.EQ) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. 1)))) ->
    (wf_ref (.REF.NULL ht_1)) ->
    (wf_ref (.REF.NULL ht_2)) ->
    ((ref_1 == (.REF.NULL ht_1)) && (ref_2 == (.REF.NULL ht_2))) ->
    Step_pure [(instr_ref ref_1), (instr_ref ref_2), .REF.EQ] [(.CONST .I32 (.mk_num__0 .I32 (. 1)))]
  | ref.eq-true : forall (ref_1 : ref) (ref_2 : ref), 
    (wf_ref ref_1) ->
    (wf_ref ref_2) ->
    (wf_instr .REF.EQ) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. 1)))) ->
    (¬(Step_pure_before_ref.eq-true [(instr_ref ref_1), (instr_ref ref_2), .REF.EQ])) ->
    (ref_1 == ref_2) ->
    Step_pure [(instr_ref ref_1), (instr_ref ref_2), .REF.EQ] [(.CONST .I32 (.mk_num__0 .I32 (. 1)))]
  | ref.eq-false : forall (ref_1 : ref) (ref_2 : ref), 
    (wf_ref ref_1) ->
    (wf_ref ref_2) ->
    (wf_instr .REF.EQ) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. 0)))) ->
    (¬(Step_pure_before_ref.eq-false [(instr_ref ref_1), (instr_ref ref_2), .REF.EQ])) ->
    Step_pure [(instr_ref ref_1), (instr_ref ref_2), .REF.EQ] [(.CONST .I32 (.mk_num__0 .I32 (. 0)))]
  | i31.get-null : forall (ht : heaptype) (sx : sx), 
    (wf_instr (.REF.NULL ht)) ->
    (wf_instr (.I31.GET sx)) ->
    (wf_instr .TRAP) ->
    Step_pure [(.REF.NULL ht), (.I31.GET sx)] [.TRAP]
  | i31.get-num : forall (i : u31) (sx : sx), 
    (wf_instr (.REF.I31_NUM i)) ->
    (wf_instr (.I31.GET sx)) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (extend__ 31 32 sx i)))) ->
    Step_pure [(.REF.I31_NUM i), (.I31.GET sx)] [(.CONST .I32 (.mk_num__0 .I32 (extend__ 31 32 sx i)))]
  | array.new : forall (val : val) (n : n) (x : idx), 
    (wf_val val) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. n)))) ->
    (wf_instr (.ARRAY.NEW x)) ->
    (wf_instr (.ARRAY.NEW_FIXED x (. n))) ->
    Step_pure [(instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.NEW x)] ((List.replicate n (instr_val val)) ++ [(.ARRAY.NEW_FIXED x (. n))])
  | extern.convert_any-null : forall (ht : heaptype), 
    (wf_instr (.REF.NULL ht)) ->
    (wf_instr .EXTERN.CONVERT_ANY) ->
    (wf_instr (.REF.NULL .EXTERN)) ->
    Step_pure [(.REF.NULL ht), .EXTERN.CONVERT_ANY] [(.REF.NULL .EXTERN)]
  | extern.convert_any-addr : forall (addrref : addrref), 
    (wf_instr .EXTERN.CONVERT_ANY) ->
    (wf_instr (.REF.EXTERN addrref)) ->
    Step_pure [(instr_addrref addrref), .EXTERN.CONVERT_ANY] [(.REF.EXTERN addrref)]
  | any.convert_extern-null : forall (ht : heaptype), 
    (wf_instr (.REF.NULL ht)) ->
    (wf_instr .ANY.CONVERT_EXTERN) ->
    (wf_instr (.REF.NULL .ANY)) ->
    Step_pure [(.REF.NULL ht), .ANY.CONVERT_EXTERN] [(.REF.NULL .ANY)]
  | any.convert_extern-addr : forall (addrref : addrref), 
    (wf_instr (.REF.EXTERN addrref)) ->
    (wf_instr .ANY.CONVERT_EXTERN) ->
    Step_pure [(.REF.EXTERN addrref), .ANY.CONVERT_EXTERN] [(instr_addrref addrref)]
  | unop-val : forall (nt : numtype) (c_1 : num_) (unop : unop_) (c : num_), 
    (wf_instr (.CONST nt c_1)) ->
    (wf_instr (.UNOP nt unop)) ->
    (wf_instr (.CONST nt c)) ->
    ((List.length (unop_ nt unop c_1)) > 0) ->
    (List.contains (unop_ nt unop c_1) c) ->
    Step_pure [(.CONST nt c_1), (.UNOP nt unop)] [(.CONST nt c)]
  | unop-trap : forall (nt : numtype) (c_1 : num_) (unop : unop_), 
    (wf_instr (.CONST nt c_1)) ->
    (wf_instr (.UNOP nt unop)) ->
    (wf_instr .TRAP) ->
    ((unop_ nt unop c_1) == []) ->
    Step_pure [(.CONST nt c_1), (.UNOP nt unop)] [.TRAP]
  | binop-val : forall (nt : numtype) (c_1 : num_) (c_2 : num_) (binop : binop_) (c : num_), 
    (wf_instr (.CONST nt c_1)) ->
    (wf_instr (.CONST nt c_2)) ->
    (wf_instr (.BINOP nt binop)) ->
    (wf_instr (.CONST nt c)) ->
    ((List.length (binop_ nt binop c_1 c_2)) > 0) ->
    (List.contains (binop_ nt binop c_1 c_2) c) ->
    Step_pure [(.CONST nt c_1), (.CONST nt c_2), (.BINOP nt binop)] [(.CONST nt c)]
  | binop-trap : forall (nt : numtype) (c_1 : num_) (c_2 : num_) (binop : binop_), 
    (wf_instr (.CONST nt c_1)) ->
    (wf_instr (.CONST nt c_2)) ->
    (wf_instr (.BINOP nt binop)) ->
    (wf_instr .TRAP) ->
    ((binop_ nt binop c_1 c_2) == []) ->
    Step_pure [(.CONST nt c_1), (.CONST nt c_2), (.BINOP nt binop)] [.TRAP]
  | testop : forall (nt : numtype) (c_1 : num_) (testop : testop_) (c : num_), 
    (wf_instr (.CONST nt c_1)) ->
    (wf_instr (.TESTOP nt testop)) ->
    (wf_instr (.CONST .I32 c)) ->
    ((proj_num__0 .I32 c) != none) ->
    ((Option.get! (proj_num__0 .I32 c)) == (testop_ nt testop c_1)) ->
    Step_pure [(.CONST nt c_1), (.TESTOP nt testop)] [(.CONST .I32 c)]
  | relop : forall (nt : numtype) (c_1 : num_) (c_2 : num_) (relop : relop_) (c : num_), 
    (wf_instr (.CONST nt c_1)) ->
    (wf_instr (.CONST nt c_2)) ->
    (wf_instr (.RELOP nt relop)) ->
    (wf_instr (.CONST .I32 c)) ->
    ((proj_num__0 .I32 c) != none) ->
    ((Option.get! (proj_num__0 .I32 c)) == (relop_ nt relop c_1 c_2)) ->
    Step_pure [(.CONST nt c_1), (.CONST nt c_2), (.RELOP nt relop)] [(.CONST .I32 c)]
  | cvtop-val : forall (nt_1 : numtype) (c_1 : num_) (nt_2 : numtype) (cvtop : cvtop__) (c : num_), 
    (wf_instr (.CONST nt_1 c_1)) ->
    (wf_instr (.CVTOP nt_2 nt_1 cvtop)) ->
    (wf_instr (.CONST nt_2 c)) ->
    ((List.length (cvtop__ nt_1 nt_2 cvtop c_1)) > 0) ->
    (List.contains (cvtop__ nt_1 nt_2 cvtop c_1) c) ->
    Step_pure [(.CONST nt_1 c_1), (.CVTOP nt_2 nt_1 cvtop)] [(.CONST nt_2 c)]
  | cvtop-trap : forall (nt_1 : numtype) (c_1 : num_) (nt_2 : numtype) (cvtop : cvtop__), 
    (wf_instr (.CONST nt_1 c_1)) ->
    (wf_instr (.CVTOP nt_2 nt_1 cvtop)) ->
    (wf_instr .TRAP) ->
    ((cvtop__ nt_1 nt_2 cvtop c_1) == []) ->
    Step_pure [(.CONST nt_1 c_1), (.CVTOP nt_2 nt_1 cvtop)] [.TRAP]
  | vvunop : forall (c_1 : vec_) (vvunop : vvunop) (c : vec_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VVUNOP .V128 vvunop)) ->
    (wf_instr (.VCONST .V128 c)) ->
    ((List.length (vvunop_ .V128 vvunop c_1)) > 0) ->
    (List.contains (vvunop_ .V128 vvunop c_1) c) ->
    Step_pure [(.VCONST .V128 c_1), (.VVUNOP .V128 vvunop)] [(.VCONST .V128 c)]
  | vvbinop : forall (c_1 : vec_) (c_2 : vec_) (vvbinop : vvbinop) (c : vec_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VCONST .V128 c_2)) ->
    (wf_instr (.VVBINOP .V128 vvbinop)) ->
    (wf_instr (.VCONST .V128 c)) ->
    ((List.length (vvbinop_ .V128 vvbinop c_1 c_2)) > 0) ->
    (List.contains (vvbinop_ .V128 vvbinop c_1 c_2) c) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VVBINOP .V128 vvbinop)] [(.VCONST .V128 c)]
  | vvternop : forall (c_1 : vec_) (c_2 : vec_) (c_3 : vec_) (vvternop : vvternop) (c : vec_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VCONST .V128 c_2)) ->
    (wf_instr (.VCONST .V128 c_3)) ->
    (wf_instr (.VVTERNOP .V128 vvternop)) ->
    (wf_instr (.VCONST .V128 c)) ->
    ((List.length (vvternop_ .V128 vvternop c_1 c_2 c_3)) > 0) ->
    (List.contains (vvternop_ .V128 vvternop c_1 c_2 c_3) c) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VCONST .V128 c_3), (.VVTERNOP .V128 vvternop)] [(.VCONST .V128 c)]
  | vvtestop : forall (c_1 : vec_) (c : num_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VVTESTOP .V128 .ANY_TRUE)) ->
    (wf_instr (.CONST .I32 c)) ->
    (wf_uN 128 (. 0)) ->
    ((proj_num__0 .I32 c) != none) ->
    ((Option.get! (proj_num__0 .I32 c)) == (ine_ (vsize .V128) c_1 (. 0))) ->
    Step_pure [(.VCONST .V128 c_1), (.VVTESTOP .V128 .ANY_TRUE)] [(.CONST .I32 c)]
  | vunop-val : forall (c_1 : vec_) (sh : shape) (vunop : vunop_) (c : vec_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VUNOP sh vunop)) ->
    (wf_instr (.VCONST .V128 c)) ->
    ((List.length (vunop_ sh vunop c_1)) > 0) ->
    (List.contains (vunop_ sh vunop c_1) c) ->
    Step_pure [(.VCONST .V128 c_1), (.VUNOP sh vunop)] [(.VCONST .V128 c)]
  | vunop-trap : forall (c_1 : vec_) (sh : shape) (vunop : vunop_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VUNOP sh vunop)) ->
    (wf_instr .TRAP) ->
    ((vunop_ sh vunop c_1) == []) ->
    Step_pure [(.VCONST .V128 c_1), (.VUNOP sh vunop)] [.TRAP]
  | vbinop-val : forall (c_1 : vec_) (c_2 : vec_) (sh : shape) (vbinop : vbinop_) (c : vec_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VCONST .V128 c_2)) ->
    (wf_instr (.VBINOP sh vbinop)) ->
    (wf_instr (.VCONST .V128 c)) ->
    ((List.length (vbinop_ sh vbinop c_1 c_2)) > 0) ->
    (List.contains (vbinop_ sh vbinop c_1 c_2) c) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VBINOP sh vbinop)] [(.VCONST .V128 c)]
  | vbinop-trap : forall (c_1 : vec_) (c_2 : vec_) (sh : shape) (vbinop : vbinop_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VCONST .V128 c_2)) ->
    (wf_instr (.VBINOP sh vbinop)) ->
    (wf_instr .TRAP) ->
    ((vbinop_ sh vbinop c_1 c_2) == []) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VBINOP sh vbinop)] [.TRAP]
  | vternop-val : forall (c_1 : vec_) (c_2 : vec_) (c_3 : vec_) (sh : shape) (vternop : vternop_) (c : vec_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VCONST .V128 c_2)) ->
    (wf_instr (.VCONST .V128 c_3)) ->
    (wf_instr (.VTERNOP sh vternop)) ->
    (wf_instr (.VCONST .V128 c)) ->
    ((List.length (vternop_ sh vternop c_1 c_2 c_3)) > 0) ->
    (List.contains (vternop_ sh vternop c_1 c_2 c_3) c) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VCONST .V128 c_3), (.VTERNOP sh vternop)] [(.VCONST .V128 c)]
  | vternop-trap : forall (c_1 : vec_) (c_2 : vec_) (c_3 : vec_) (sh : shape) (vternop : vternop_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VCONST .V128 c_2)) ->
    (wf_instr (.VCONST .V128 c_3)) ->
    (wf_instr (.VTERNOP sh vternop)) ->
    (wf_instr .TRAP) ->
    ((vternop_ sh vternop c_1 c_2 c_3) == []) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VCONST .V128 c_3), (.VTERNOP sh vternop)] [.TRAP]
  | vtestop : forall (c_1 : vec_) (sh : shape) (vtestop : vtestop_) (i : num_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VTESTOP sh vtestop)) ->
    (wf_instr (.CONST .I32 i)) ->
    ((proj_num__0 .I32 i) != none) ->
    ((Option.get! (proj_num__0 .I32 i)) == (vtestop_ sh vtestop c_1)) ->
    Step_pure [(.VCONST .V128 c_1), (.VTESTOP sh vtestop)] [(.CONST .I32 i)]
  | vrelop : forall (c_1 : vec_) (c_2 : vec_) (sh : shape) (vrelop : vrelop_) (c : vec_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VCONST .V128 c_2)) ->
    (wf_instr (.VRELOP sh vrelop)) ->
    (wf_instr (.VCONST .V128 c)) ->
    (c == (vrelop_ sh vrelop c_1 c_2)) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VRELOP sh vrelop)] [(.VCONST .V128 c)]
  | vshiftop : forall (c_1 : vec_) (i : num_) (sh : ishape) (vshiftop : vshiftop_) (c : vec_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.CONST .I32 i)) ->
    (wf_instr (.VSHIFTOP sh vshiftop)) ->
    (wf_instr (.VCONST .V128 c)) ->
    ((proj_num__0 .I32 i) != none) ->
    (c == (vshiftop_ sh vshiftop c_1 (Option.get! (proj_num__0 .I32 i)))) ->
    Step_pure [(.VCONST .V128 c_1), (.CONST .I32 i), (.VSHIFTOP sh vshiftop)] [(.VCONST .V128 c)]
  | vbitmask : forall (c_1 : vec_) (sh : ishape) (c : num_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VBITMASK sh)) ->
    (wf_instr (.CONST .I32 c)) ->
    ((proj_num__0 .I32 c) != none) ->
    ((Option.get! (proj_num__0 .I32 c)) == (vbitmaskop_ sh c_1)) ->
    Step_pure [(.VCONST .V128 c_1), (.VBITMASK sh)] [(.CONST .I32 c)]
  | vswizzlop : forall (c_1 : vec_) (c_2 : vec_) (sh : bshape) (swizzlop : vswizzlop_) (c : vec_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VCONST .V128 c_2)) ->
    (wf_instr (.VSWIZZLOP sh swizzlop)) ->
    (wf_instr (.VCONST .V128 c)) ->
    (c == (vswizzlop_ sh swizzlop c_1 c_2)) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VSWIZZLOP sh swizzlop)] [(.VCONST .V128 c)]
  | vshuffle : forall (c_1 : vec_) (c_2 : vec_) (sh : bshape) (i* : (List laneidx)) (c : vec_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VCONST .V128 c_2)) ->
    (wf_instr (.VSHUFFLE sh (List.map (fun (i : laneidx) => i) i*))) ->
    (wf_instr (.VCONST .V128 c)) ->
    (c == (vshufflop_ sh (List.map (fun (i : laneidx) => i) i*) c_1 c_2)) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VSHUFFLE sh (List.map (fun (i : laneidx) => i) i*))] [(.VCONST .V128 c)]
  | vsplat : forall (Lnn : Lnn) (c_1 : num_) (M : M) (c : vec_), 
    (wf_instr (.CONST (lunpack Lnn) c_1)) ->
    (wf_instr (.VSPLAT (.X Lnn (. M)))) ->
    (wf_instr (.VCONST .V128 c)) ->
    (wf_shape (.X Lnn (. M))) ->
    (c == (inv_lanes_ (.X Lnn (. M)) (List.replicate M (lpacknum_ Lnn c_1)))) ->
    Step_pure [(.CONST (lunpack Lnn) c_1), (.VSPLAT (.X Lnn (. M)))] [(.VCONST .V128 c)]
  | vextract_lane-num : forall (c_1 : vec_) (nt : numtype) (M : M) (i : laneidx) (c_2 : num_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VEXTRACT_LANE (.X (lanetype_numtype nt) (. M)) none i)) ->
    (wf_instr (.CONST nt c_2)) ->
    (wf_lane_ (lanetype (.X (lanetype_numtype nt) (. M))) (.mk_lane__0 nt c_2)) ->
    (wf_shape (.X (lanetype_numtype nt) (. M))) ->
    ((proj_uN_0 i) < (List.length (lanes_ (.X (lanetype_numtype nt) (. M)) c_1))) ->
    ((.mk_lane__0 nt c_2) == ((lanes_ (.X (lanetype_numtype nt) (. M)) c_1)[(proj_uN_0 i)]!)) ->
    Step_pure [(.VCONST .V128 c_1), (.VEXTRACT_LANE (.X (lanetype_numtype nt) (. M)) none i)] [(.CONST nt c_2)]
  | vextract_lane-pack : forall (c_1 : vec_) (pt : packtype) (M : M) (sx : sx) (i : laneidx) (c_2 : num_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VEXTRACT_LANE (.X (lanetype_packtype pt) (. M)) (some sx) i)) ->
    (wf_instr (.CONST .I32 c_2)) ->
    (wf_shape (.X (lanetype_packtype pt) (. M))) ->
    ((proj_num__0 .I32 c_2) != none) ->
    ((proj_lane__1 pt ((lanes_ (.X (lanetype_packtype pt) (. M)) c_1)[(proj_uN_0 i)]!)) != none) ->
    ((proj_uN_0 i) < (List.length (lanes_ (.X (lanetype_packtype pt) (. M)) c_1))) ->
    ((Option.get! (proj_num__0 .I32 c_2)) == (extend__ (psize pt) 32 sx (Option.get! (proj_lane__1 pt ((lanes_ (.X (lanetype_packtype pt) (. M)) c_1)[(proj_uN_0 i)]!))))) ->
    Step_pure [(.VCONST .V128 c_1), (.VEXTRACT_LANE (.X (lanetype_packtype pt) (. M)) (some sx) i)] [(.CONST .I32 c_2)]
  | vreplace_lane : forall (c_1 : vec_) (Lnn : Lnn) (c_2 : num_) (M : M) (i : laneidx) (c : vec_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.CONST (lunpack Lnn) c_2)) ->
    (wf_instr (.VREPLACE_LANE (.X Lnn (. M)) i)) ->
    (wf_instr (.VCONST .V128 c)) ->
    (wf_shape (.X Lnn (. M))) ->
    (c == (inv_lanes_ (.X Lnn (. M)) (List.modify (lanes_ (.X Lnn (. M)) c_1) (proj_uN_0 i) (fun (_ : lane_) => (lpacknum_ Lnn c_2))))) ->
    Step_pure [(.VCONST .V128 c_1), (.CONST (lunpack Lnn) c_2), (.VREPLACE_LANE (.X Lnn (. M)) i)] [(.VCONST .V128 c)]
  | vextunop : forall (c_1 : vec_) (sh_2 : ishape) (sh_1 : ishape) (vextunop : vextunop__) (c : vec_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VEXTUNOP sh_2 sh_1 vextunop)) ->
    (wf_instr (.VCONST .V128 c)) ->
    ((vextunop__ sh_1 sh_2 vextunop c_1) == c) ->
    Step_pure [(.VCONST .V128 c_1), (.VEXTUNOP sh_2 sh_1 vextunop)] [(.VCONST .V128 c)]
  | vextbinop : forall (c_1 : vec_) (c_2 : vec_) (sh_2 : ishape) (sh_1 : ishape) (vextbinop : vextbinop__) (c : vec_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VCONST .V128 c_2)) ->
    (wf_instr (.VEXTBINOP sh_2 sh_1 vextbinop)) ->
    (wf_instr (.VCONST .V128 c)) ->
    ((vextbinop__ sh_1 sh_2 vextbinop c_1 c_2) == c) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VEXTBINOP sh_2 sh_1 vextbinop)] [(.VCONST .V128 c)]
  | vextternop : forall (c_1 : vec_) (c_2 : vec_) (c_3 : vec_) (sh_2 : ishape) (sh_1 : ishape) (vextternop : vextternop__) (c : vec_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VCONST .V128 c_2)) ->
    (wf_instr (.VCONST .V128 c_3)) ->
    (wf_instr (.VEXTTERNOP sh_2 sh_1 vextternop)) ->
    (wf_instr (.VCONST .V128 c)) ->
    ((vextternop__ sh_1 sh_2 vextternop c_1 c_2 c_3) == c) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VCONST .V128 c_3), (.VEXTTERNOP sh_2 sh_1 vextternop)] [(.VCONST .V128 c)]
  | vnarrow : forall (c_1 : vec_) (c_2 : vec_) (sh_2 : ishape) (sh_1 : ishape) (sx : sx) (c : vec_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VCONST .V128 c_2)) ->
    (wf_instr (.VNARROW sh_2 sh_1 sx)) ->
    (wf_instr (.VCONST .V128 c)) ->
    (c == (vnarrowop__ (proj_ishape_0 sh_1) (proj_ishape_0 sh_2) sx c_1 c_2)) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VNARROW sh_2 sh_1 sx)] [(.VCONST .V128 c)]
  | vcvtop : forall (c_1 : vec_) (sh_2 : shape) (sh_1 : shape) (vcvtop : vcvtop__) (c : vec_), 
    (wf_instr (.VCONST .V128 c_1)) ->
    (wf_instr (.VCVTOP sh_2 sh_1 vcvtop)) ->
    (wf_instr (.VCONST .V128 c)) ->
    (c == (vcvtop__ sh_1 sh_2 vcvtop c_1)) ->
    Step_pure [(.VCONST .V128 c_1), (.VCVTOP sh_2 sh_1 vcvtop)] [(.VCONST .V128 c)]

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:69.1-69.71 -/
opaque blocktype_ : forall (state : state) (blocktype : blocktype), instrtype := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:151.1-153.15 -/
inductive Step_read_before_br_on_cast-fail : config -> Prop where
  | br_on_cast-succeed_0 : forall (s : store) (f : frame) (ref : ref) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype) (rt : reftype), 
    (wf_reftype rt) ->
    (wf_config (. (. s f) [(instr_ref ref), (.BR_ON_CAST l rt_1 rt_2)])) ->
    (wf_instr (.BR l)) ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (Ref_ok s ref rt) ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt (inst_reftype (f.MODULE) rt_2)) ->
    Step_read_before_br_on_cast-fail (. (. s f) [(instr_ref ref), (.BR_ON_CAST l rt_1 rt_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:162.1-164.15 -/
inductive Step_read_before_br_on_cast_fail-fail : config -> Prop where
  | br_on_cast_fail-succeed_0 : forall (s : store) (f : frame) (ref : ref) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype) (rt : reftype), 
    (wf_reftype rt) ->
    (wf_config (. (. s f) [(instr_ref ref), (.BR_ON_CAST_FAIL l rt_1 rt_2)])) ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (Ref_ok s ref rt) ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt (inst_reftype (f.MODULE) rt_2)) ->
    Step_read_before_br_on_cast_fail-fail (. (. s f) [(instr_ref ref), (.BR_ON_CAST_FAIL l rt_1 rt_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:268.1-271.15 -/
inductive Step_read_before_throw_ref-handler-next : config -> Prop where
  | throw_ref-handler-catch_all_ref_0 : forall (z : state) (n : n) (l : labelidx) (catch'* : (List «catch»)) (a : addr), 
    (wf_config (. z [(.HANDLER_ n ([(.CATCH_ALL_REF l)] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])])) ->
    (wf_instr (.REF.EXN_ADDR a)) ->
    (wf_instr (.BR l)) ->
    Step_read_before_throw_ref-handler-next (. z [(.HANDLER_ n ([(.CATCH_ALL_REF l)] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])])
  | throw_ref-handler-catch_all_0 : forall (z : state) (n : n) (l : labelidx) (catch'* : (List «catch»)) (a : addr), 
    (wf_config (. z [(.HANDLER_ n ([(.CATCH_ALL l)] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])])) ->
    (wf_instr (.BR l)) ->
    Step_read_before_throw_ref-handler-next (. z [(.HANDLER_ n ([(.CATCH_ALL l)] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])])
  | throw_ref-handler-catch_ref_0 : forall (z : state) (n : n) (x : idx) (l : labelidx) (catch'* : (List «catch»)) (a : addr) (val* : (List val)), 
    Forall (fun (val : val) => (wf_val val)) val* ->
    (wf_config (. z [(.HANDLER_ n ([(.CATCH_REF x l)] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])])) ->
    (wf_instr (.REF.EXN_ADDR a)) ->
    (wf_instr (.BR l)) ->
    (a < (List.length (exninst z))) ->
    ((proj_uN_0 x) < (List.length (tagaddr z))) ->
    ((((exninst z)[a]!).TAG) == ((tagaddr z)[(proj_uN_0 x)]!)) ->
    ((List.map (fun (val : val) => val) val*) == (((exninst z)[a]!).FIELDS)) ->
    Step_read_before_throw_ref-handler-next (. z [(.HANDLER_ n ([(.CATCH_REF x l)] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])])
  | throw_ref-handler-catch_0 : forall (z : state) (n : n) (x : idx) (l : labelidx) (catch'* : (List «catch»)) (a : addr) (val* : (List val)), 
    Forall (fun (val : val) => (wf_val val)) val* ->
    (wf_config (. z [(.HANDLER_ n ([(.CATCH x l)] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])])) ->
    (wf_instr (.BR l)) ->
    (a < (List.length (exninst z))) ->
    ((proj_uN_0 x) < (List.length (tagaddr z))) ->
    ((((exninst z)[a]!).TAG) == ((tagaddr z)[(proj_uN_0 x)]!)) ->
    ((List.map (fun (val : val) => val) val*) == (((exninst z)[a]!).FIELDS)) ->
    Step_read_before_throw_ref-handler-next (. z [(.HANDLER_ n ([(.CATCH x l)] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:357.1-360.14 -/
inductive Step_read_before_table.fill-zero : config -> Prop where
  | table.fill-oob_0 : forall (z : state) (at : addrtype) (i : num_) (val : val) (n : n) (x : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.FILL x)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 at i))) + n) > (List.length ((table z x).REFS))) ->
    Step_read_before_table.fill-zero (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.FILL x)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:362.1-366.15 -/
inductive Step_read_before_table.fill-succ : config -> Prop where
  | table.fill-zero_0 : forall (z : state) (at : addrtype) (i : num_) (val : val) (n : n) (x : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.FILL x)])) ->
    (¬(Step_read_before_table.fill-zero (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.FILL x)]))) ->
    (n == 0) ->
    Step_read_before_table.fill-succ (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.FILL x)])
  | table.fill-oob_1 : forall (z : state) (at : addrtype) (i : num_) (val : val) (n : n) (x : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.FILL x)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 at i))) + n) > (List.length ((table z x).REFS))) ->
    Step_read_before_table.fill-succ (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.FILL x)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:374.1-377.14 -/
inductive Step_read_before_table.copy-zero : config -> Prop where
  | table.copy-oob_0 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at_1 i_1) != none) ->
    ((proj_num__0 at_2 i_2) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + n) > (List.length ((table z x_1).REFS))) || (((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + n) > (List.length ((table z x_2).REFS)))) ->
    Step_read_before_table.copy-zero (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x_1 x_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:379.1-384.19 -/
inductive Step_read_before_table.copy-le : config -> Prop where
  | table.copy-zero_0 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)])) ->
    (¬(Step_read_before_table.copy-zero (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)]))) ->
    (n == 0) ->
    Step_read_before_table.copy-le (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)])
  | table.copy-oob_1 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at_1 i_1) != none) ->
    ((proj_num__0 at_2 i_2) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + n) > (List.length ((table z x_1).REFS))) || (((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + n) > (List.length ((table z x_2).REFS)))) ->
    Step_read_before_table.copy-le (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x_1 x_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:386.1-390.15 -/
inductive Step_read_before_table.copy-gt : config -> Prop where
  | table.copy-le_0 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)])) ->
    (wf_instr (.CONST (numtype_addrtype at_1) i_1)) ->
    (wf_instr (.CONST (numtype_addrtype at_2) i_2)) ->
    (wf_instr (.TABLE.GET y)) ->
    (wf_instr (.TABLE.SET x)) ->
    ((proj_num__0 at_1 i_1) != none) ->
    (wf_instr (.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (. ((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + 1))))) ->
    ((proj_num__0 at_2 i_2) != none) ->
    (wf_instr (.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (. ((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + 1))))) ->
    (wf_instr (.CONST (numtype_addrtype at') (.mk_num__0 at' (. (((n : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.TABLE.COPY x y)) ->
    (¬(Step_read_before_table.copy-le (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)]))) ->
    ((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) <= (proj_uN_0 (Option.get! (proj_num__0 at_2 i_2)))) ->
    Step_read_before_table.copy-gt (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)])
  | table.copy-zero_1 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)])) ->
    (¬(Step_read_before_table.copy-zero (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)]))) ->
    (n == 0) ->
    Step_read_before_table.copy-gt (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)])
  | table.copy-oob_2 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at_1 i_1) != none) ->
    ((proj_num__0 at_2 i_2) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + n) > (List.length ((table z x_1).REFS))) || (((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + n) > (List.length ((table z x_2).REFS)))) ->
    Step_read_before_table.copy-gt (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x_1 x_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:398.1-401.14 -/
inductive Step_read_before_table.init-zero : config -> Prop where
  | table.init-oob_0 : forall (z : state) (at : addrtype) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.TABLE.INIT x y)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    ((proj_num__0 .I32 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at i))) + n) > (List.length ((table z x).REFS))) || (((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + n) > (List.length ((elem z y).REFS)))) ->
    Step_read_before_table.init-zero (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.TABLE.INIT x y)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:403.1-407.15 -/
inductive Step_read_before_table.init-succ : config -> Prop where
  | table.init-zero_0 : forall (z : state) (at : addrtype) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.TABLE.INIT x y)])) ->
    (¬(Step_read_before_table.init-zero (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.TABLE.INIT x y)]))) ->
    (n == 0) ->
    Step_read_before_table.init-succ (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.TABLE.INIT x y)])
  | table.init-oob_1 : forall (z : state) (at : addrtype) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.TABLE.INIT x y)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    ((proj_num__0 .I32 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at i))) + n) > (List.length ((table z x).REFS))) || (((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + n) > (List.length ((elem z y).REFS)))) ->
    Step_read_before_table.init-succ (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.TABLE.INIT x y)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:559.1-562.14 -/
inductive Step_read_before_memory.fill-zero : config -> Prop where
  | memory.fill-oob_0 : forall (z : state) (at : addrtype) (i : num_) (val : val) (n : n) (x : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.FILL x)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 at i))) + n) > (List.length ((mem z x).BYTES))) ->
    Step_read_before_memory.fill-zero (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.FILL x)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:564.1-568.15 -/
inductive Step_read_before_memory.fill-succ : config -> Prop where
  | memory.fill-zero_0 : forall (z : state) (at : addrtype) (i : num_) (val : val) (n : n) (x : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.FILL x)])) ->
    (¬(Step_read_before_memory.fill-zero (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.FILL x)]))) ->
    (n == 0) ->
    Step_read_before_memory.fill-succ (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.FILL x)])
  | memory.fill-oob_1 : forall (z : state) (at : addrtype) (i : num_) (val : val) (n : n) (x : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.FILL x)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 at i))) + n) > (List.length ((mem z x).BYTES))) ->
    Step_read_before_memory.fill-succ (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.FILL x)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:576.1-579.14 -/
inductive Step_read_before_memory.copy-zero : config -> Prop where
  | memory.copy-oob_0 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at_1 i_1) != none) ->
    ((proj_num__0 at_2 i_2) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + n) > (List.length ((mem z x_1).BYTES))) || (((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + n) > (List.length ((mem z x_2).BYTES)))) ->
    Step_read_before_memory.copy-zero (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:581.1-586.19 -/
inductive Step_read_before_memory.copy-le : config -> Prop where
  | memory.copy-zero_0 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)])) ->
    (¬(Step_read_before_memory.copy-zero (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)]))) ->
    (n == 0) ->
    Step_read_before_memory.copy-le (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)])
  | memory.copy-oob_1 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at_1 i_1) != none) ->
    ((proj_num__0 at_2 i_2) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + n) > (List.length ((mem z x_1).BYTES))) || (((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + n) > (List.length ((mem z x_2).BYTES)))) ->
    Step_read_before_memory.copy-le (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:588.1-592.15 -/
inductive Step_read_before_memory.copy-gt : config -> Prop where
  | memory.copy-le_0 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)])) ->
    (wf_instr (.CONST (numtype_addrtype at_1) i_1)) ->
    (wf_instr (.CONST (numtype_addrtype at_2) i_2)) ->
    (wf_instr (.LOAD .I32 (some (.mk_loadop__0 .I32 (._ (. 8) .U))) x_2 (memarg0 ))) ->
    (wf_instr (.STORE .I32 (some (.mk_storeop__0 .I32 (. (. 8)))) x_1 (memarg0 ))) ->
    ((proj_num__0 at_1 i_1) != none) ->
    (wf_instr (.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (. ((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + 1))))) ->
    ((proj_num__0 at_2 i_2) != none) ->
    (wf_instr (.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (. ((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + 1))))) ->
    (wf_instr (.CONST (numtype_addrtype at') (.mk_num__0 at' (. (((n : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.MEMORY.COPY x_1 x_2)) ->
    (¬(Step_read_before_memory.copy-le (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)]))) ->
    ((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) <= (proj_uN_0 (Option.get! (proj_num__0 at_2 i_2)))) ->
    Step_read_before_memory.copy-gt (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)])
  | memory.copy-zero_1 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)])) ->
    (¬(Step_read_before_memory.copy-zero (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)]))) ->
    (n == 0) ->
    Step_read_before_memory.copy-gt (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)])
  | memory.copy-oob_2 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at_1 i_1) != none) ->
    ((proj_num__0 at_2 i_2) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + n) > (List.length ((mem z x_1).BYTES))) || (((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + n) > (List.length ((mem z x_2).BYTES)))) ->
    Step_read_before_memory.copy-gt (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:600.1-603.14 -/
inductive Step_read_before_memory.init-zero : config -> Prop where
  | memory.init-oob_0 : forall (z : state) (at : addrtype) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.MEMORY.INIT x y)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    ((proj_num__0 .I32 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at i))) + n) > (List.length ((mem z x).BYTES))) || (((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + n) > (List.length ((data z y).BYTES)))) ->
    Step_read_before_memory.init-zero (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.MEMORY.INIT x y)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:605.1-609.15 -/
inductive Step_read_before_memory.init-succ : config -> Prop where
  | memory.init-zero_0 : forall (z : state) (at : addrtype) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.MEMORY.INIT x y)])) ->
    (¬(Step_read_before_memory.init-zero (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.MEMORY.INIT x y)]))) ->
    (n == 0) ->
    Step_read_before_memory.init-succ (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.MEMORY.INIT x y)])
  | memory.init-oob_1 : forall (z : state) (at : addrtype) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.MEMORY.INIT x y)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    ((proj_num__0 .I32 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at i))) + n) > (List.length ((mem z x).BYTES))) || (((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + n) > (List.length ((data z y).BYTES)))) ->
    Step_read_before_memory.init-succ (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.MEMORY.INIT x y)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:666.1-668.15 -/
inductive Step_read_before_ref.test-false : config -> Prop where
  | ref.test-true_0 : forall (s : store) (f : frame) (ref : ref) (rt : reftype) (rt' : reftype), 
    (wf_reftype rt') ->
    (wf_config (. (. s f) [(instr_ref ref), (.REF.TEST rt)])) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. 1)))) ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (Ref_ok s ref rt') ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt' (inst_reftype (f.MODULE) rt)) ->
    Step_read_before_ref.test-false (. (. s f) [(instr_ref ref), (.REF.TEST rt)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:677.1-679.15 -/
inductive Step_read_before_ref.cast-fail : config -> Prop where
  | ref.cast-succeed_0 : forall (s : store) (f : frame) (ref : ref) (rt : reftype) (rt' : reftype), 
    (wf_reftype rt') ->
    (wf_config (. (. s f) [(instr_ref ref), (.REF.CAST rt)])) ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (Ref_ok s ref rt') ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt' (inst_reftype (f.MODULE) rt)) ->
    Step_read_before_ref.cast-fail (. (. s f) [(instr_ref ref), (.REF.CAST rt)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:805.1-808.14 -/
inductive Step_read_before_array.fill-zero : config -> Prop where
  | array.fill-oob_0 : forall (z : state) (a : addr) (i : num_) (val : val) (n : n) (x : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.FILL x)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i) != none) ->
    (a < (List.length (arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) + n) > (List.length (((arrayinst z)[a]!).FIELDS))) ->
    Step_read_before_array.fill-zero (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.FILL x)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:810.1-814.15 -/
inductive Step_read_before_array.fill-succ : config -> Prop where
  | array.fill-zero_0 : forall (z : state) (a : addr) (i : num_) (val : val) (n : n) (x : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.FILL x)])) ->
    (¬(Step_read_before_array.fill-zero (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.FILL x)]))) ->
    (n == 0) ->
    Step_read_before_array.fill-succ (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.FILL x)])
  | array.fill-oob_1 : forall (z : state) (a : addr) (i : num_) (val : val) (n : n) (x : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.FILL x)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i) != none) ->
    (a < (List.length (arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) + n) > (List.length (((arrayinst z)[a]!).FIELDS))) ->
    Step_read_before_array.fill-succ (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.FILL x)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:832.1-836.14 -/
inductive Step_read_before_array.copy-zero : config -> Prop where
  | array.copy-oob2_0 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i_2) != none) ->
    (a_2 < (List.length (arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i_2))) + n) > (List.length (((arrayinst z)[a_2]!).FIELDS))) ->
    Step_read_before_array.copy-zero (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])
  | array.copy-oob1_0 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i_1) != none) ->
    (a_1 < (List.length (arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i_1))) + n) > (List.length (((arrayinst z)[a_1]!).FIELDS))) ->
    Step_read_before_array.copy-zero (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:838.1-848.24 -/
inductive Step_read_before_array.copy-le : config -> Prop where
  | array.copy-zero_0 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])) ->
    (¬(Step_read_before_array.copy-zero (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)]))) ->
    (n == 0) ->
    Step_read_before_array.copy-le (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])
  | array.copy-oob2_1 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i_2) != none) ->
    (a_2 < (List.length (arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i_2))) + n) > (List.length (((arrayinst z)[a_2]!).FIELDS))) ->
    Step_read_before_array.copy-le (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])
  | array.copy-oob1_1 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i_1) != none) ->
    (a_1 < (List.length (arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i_1))) + n) > (List.length (((arrayinst z)[a_1]!).FIELDS))) ->
    Step_read_before_array.copy-le (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:850.1-859.24 -/
inductive Step_read_before_array.copy-gt : config -> Prop where
  | array.copy-le_0 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (n : n) (x_1 : idx) (x_2 : idx) (sx? : (Option sx)) (mut? : (Option «mut»)) (zt_2 : storagetype), 
    (wf_config (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])) ->
    (wf_instr (.REF.ARRAY_ADDR a_1)) ->
    (wf_instr (.CONST .I32 i_1)) ->
    (wf_instr (.REF.ARRAY_ADDR a_2)) ->
    (wf_instr (.CONST .I32 i_2)) ->
    (wf_instr (.ARRAY.GET (Option.map (fun (sx : sx) => sx) sx?) x_2)) ->
    (wf_instr (.ARRAY.SET x_1)) ->
    ((proj_num__0 .I32 i_1) != none) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 i_1))) + 1))))) ->
    ((proj_num__0 .I32 i_2) != none) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 i_2))) + 1))))) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. (((n : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.ARRAY.COPY x_1 x_2)) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt_2))) ->
    (¬(Step_read_before_array.copy-le (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)]))) ->
    (Expand (type z x_2) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt_2))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i_1))) <= (proj_uN_0 (Option.get! (proj_num__0 .I32 i_2)))) && ((Option.map (fun (sx : sx) => sx) sx?) == (sx zt_2))) ->
    Step_read_before_array.copy-gt (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])
  | array.copy-zero_1 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])) ->
    (¬(Step_read_before_array.copy-zero (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)]))) ->
    (n == 0) ->
    Step_read_before_array.copy-gt (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])
  | array.copy-oob2_2 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i_2) != none) ->
    (a_2 < (List.length (arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i_2))) + n) > (List.length (((arrayinst z)[a_2]!).FIELDS))) ->
    Step_read_before_array.copy-gt (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])
  | array.copy-oob1_2 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i_1) != none) ->
    (a_1 < (List.length (arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i_1))) + n) > (List.length (((arrayinst z)[a_1]!).FIELDS))) ->
    Step_read_before_array.copy-gt (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:875.1-879.14 -/
inductive Step_read_before_array.init_elem-zero : config -> Prop where
  | array.init_elem-oob2_0 : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 j) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + n) > (List.length ((elem z y).REFS))) ->
    Step_read_before_array.init_elem-zero (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)])
  | array.init_elem-oob1_0 : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i) != none) ->
    (a < (List.length (arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) + n) > (List.length (((arrayinst z)[a]!).FIELDS))) ->
    Step_read_before_array.init_elem-zero (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:881.1-887.34 -/
inductive Step_read_before_array.init_elem-succ : config -> Prop where
  | array.init_elem-zero_0 : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)])) ->
    (¬(Step_read_before_array.init_elem-zero (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)]))) ->
    (n == 0) ->
    Step_read_before_array.init_elem-succ (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)])
  | array.init_elem-oob2_1 : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 j) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + n) > (List.length ((elem z y).REFS))) ->
    Step_read_before_array.init_elem-succ (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)])
  | array.init_elem-oob1_1 : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i) != none) ->
    (a < (List.length (arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) + n) > (List.length (((arrayinst z)[a]!).FIELDS))) ->
    Step_read_before_array.init_elem-succ (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:904.1-908.14 -/
inductive Step_read_before_array.init_data-zero : config -> Prop where
  | array.init_data-oob2_0 : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx) (mut? : (Option «mut»)) (zt : storagetype), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)])) ->
    (wf_instr .TRAP) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    (Expand (type z x) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    ((proj_num__0 .I32 j) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + ((((n * (zsize zt)) : Nat) / (8 : Nat)) : Nat)) > (List.length ((data z y).BYTES))) ->
    Step_read_before_array.init_data-zero (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)])
  | array.init_data-oob1_0 : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i) != none) ->
    (a < (List.length (arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) + n) > (List.length (((arrayinst z)[a]!).FIELDS))) ->
    Step_read_before_array.init_data-zero (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:911.1-918.62 -/
inductive Step_read_before_array.init_data-num : config -> Prop where
  | array.init_data-zero_0 : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)])) ->
    (¬(Step_read_before_array.init_data-zero (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)]))) ->
    (n == 0) ->
    Step_read_before_array.init_data-num (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)])
  | array.init_data-oob2_1 : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx) (mut? : (Option «mut»)) (zt : storagetype), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)])) ->
    (wf_instr .TRAP) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    (Expand (type z x) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    ((proj_num__0 .I32 j) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + ((((n * (zsize zt)) : Nat) / (8 : Nat)) : Nat)) > (List.length ((data z y).BYTES))) ->
    Step_read_before_array.init_data-num (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)])
  | array.init_data-oob1_1 : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i) != none) ->
    (a < (List.length (arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) + n) > (List.length (((arrayinst z)[a]!).FIELDS))) ->
    Step_read_before_array.init_data-num (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:7.1-7.88 -/
inductive Step_read : config -> (List instr) -> Prop where
  | block : forall (z : state) (val* : (List val)) (m : m) (bt : blocktype) (instr* : (List instr)) (n : n) (t_1* : (List valtype)) (t_2* : (List valtype)), 
    ((List.length val*) == m) ->
    (wf_config (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.BLOCK bt (List.map (fun (instr : instr) => instr) instr*))]))) ->
    (wf_instr (.LABEL_ n [] ((List.map (fun (val : val) => (instr_val val)) val*) ++ (List.map (fun (instr : instr) => instr) instr*)))) ->
    ((List.length t_1*) == m) ->
    ((List.length t_2*) == n) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    ((blocktype_ z bt) == (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Step_read (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.BLOCK bt (List.map (fun (instr : instr) => instr) instr*))])) [(.LABEL_ n [] ((List.map (fun (val : val) => (instr_val val)) val*) ++ (List.map (fun (instr : instr) => instr) instr*)))]
  | loop : forall (z : state) (val* : (List val)) (m : m) (bt : blocktype) (instr* : (List instr)) (t_1* : (List valtype)) (t_2* : (List valtype)) (n : n), 
    ((List.length val*) == m) ->
    (wf_config (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.LOOP bt (List.map (fun (instr : instr) => instr) instr*))]))) ->
    (wf_instr (.LABEL_ m [(.LOOP bt (List.map (fun (instr : instr) => instr) instr*))] ((List.map (fun (val : val) => (instr_val val)) val*) ++ (List.map (fun (instr : instr) => instr) instr*)))) ->
    ((List.length t_1*) == m) ->
    ((List.length t_2*) == n) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    ((blocktype_ z bt) == (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Step_read (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.LOOP bt (List.map (fun (instr : instr) => instr) instr*))])) [(.LABEL_ m [(.LOOP bt (List.map (fun (instr : instr) => instr) instr*))] ((List.map (fun (val : val) => (instr_val val)) val*) ++ (List.map (fun (instr : instr) => instr) instr*)))]
  | br_on_cast-succeed : forall (s : store) (f : frame) (ref : ref) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype) (rt : reftype), 
    (wf_reftype rt) ->
    (wf_config (. (. s f) [(instr_ref ref), (.BR_ON_CAST l rt_1 rt_2)])) ->
    (wf_instr (.BR l)) ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (Ref_ok s ref rt) ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt (inst_reftype (f.MODULE) rt_2)) ->
    Step_read (. (. s f) [(instr_ref ref), (.BR_ON_CAST l rt_1 rt_2)]) [(instr_ref ref), (.BR l)]
  | br_on_cast-fail : forall (s : store) (f : frame) (ref : ref) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype), 
    (wf_config (. (. s f) [(instr_ref ref), (.BR_ON_CAST l rt_1 rt_2)])) ->
    (¬(Step_read_before_br_on_cast-fail (. (. s f) [(instr_ref ref), (.BR_ON_CAST l rt_1 rt_2)]))) ->
    Step_read (. (. s f) [(instr_ref ref), (.BR_ON_CAST l rt_1 rt_2)]) [(instr_ref ref)]
  | br_on_cast_fail-succeed : forall (s : store) (f : frame) (ref : ref) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype) (rt : reftype), 
    (wf_reftype rt) ->
    (wf_config (. (. s f) [(instr_ref ref), (.BR_ON_CAST_FAIL l rt_1 rt_2)])) ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (Ref_ok s ref rt) ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt (inst_reftype (f.MODULE) rt_2)) ->
    Step_read (. (. s f) [(instr_ref ref), (.BR_ON_CAST_FAIL l rt_1 rt_2)]) [(instr_ref ref)]
  | br_on_cast_fail-fail : forall (s : store) (f : frame) (ref : ref) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype), 
    (wf_config (. (. s f) [(instr_ref ref), (.BR_ON_CAST_FAIL l rt_1 rt_2)])) ->
    (wf_instr (.BR l)) ->
    (¬(Step_read_before_br_on_cast_fail-fail (. (. s f) [(instr_ref ref), (.BR_ON_CAST_FAIL l rt_1 rt_2)]))) ->
    Step_read (. (. s f) [(instr_ref ref), (.BR_ON_CAST_FAIL l rt_1 rt_2)]) [(instr_ref ref), (.BR l)]
  | call : forall (z : state) (x : idx) (a : addr), 
    (a < (List.length (funcinst z))) ->
    (wf_config (. z [(.CALL x)])) ->
    (wf_instr (.REF.FUNC_ADDR a)) ->
    (wf_instr (.CALL_REF (typeuse_deftype (((funcinst z)[a]!).TYPE)))) ->
    ((proj_uN_0 x) < (List.length ((moduleinst z).FUNCS))) ->
    ((((moduleinst z).FUNCS)[(proj_uN_0 x)]!) == a) ->
    Step_read (. z [(.CALL x)]) [(.REF.FUNC_ADDR a), (.CALL_REF (typeuse_deftype (((funcinst z)[a]!).TYPE)))]
  | call_ref-null : forall (z : state) (ht : heaptype) (yy : typeuse), 
    (wf_config (. z [(.REF.NULL ht), (.CALL_REF yy)])) ->
    (wf_instr .TRAP) ->
    Step_read (. z [(.REF.NULL ht), (.CALL_REF yy)]) [.TRAP]
  | call_ref-func : forall (z : state) (val* : (List val)) (n : n) (a : addr) (yy : typeuse) (m : m) (f : frame) (instr* : (List instr)) (fi : funcinst) (t_1* : (List valtype)) (t_2* : (List valtype)) (x : idx) (t* : (List valtype)), 
    ((List.length val*) == n) ->
    (wf_config (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.REF.FUNC_ADDR a), (.CALL_REF yy)]))) ->
    (wf_instr (.FRAME_ m f [(.LABEL_ m [] (List.map (fun (instr : instr) => instr) instr*))])) ->
    ((List.length t_1*) == n) ->
    ((List.length t_2*) == m) ->
    (wf_comptype (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (wf_funccode (.FUNC x (List.map (fun (t : valtype) => (.LOCAL t)) t*) (List.map (fun (instr : instr) => instr) instr*))) ->
    (wf_frame { LOCALS := ((List.map (fun (val : val) => (some val)) val*) ++ (List.map (fun (t : valtype) => (default_ t)) t*)), MODULE := (fi.MODULE) }) ->
    (a < (List.length (funcinst z))) ->
    (((funcinst z)[a]!) == fi) ->
    (Expand (fi.TYPE) (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    ((fi.CODE) == (.FUNC x (List.map (fun (t : valtype) => (.LOCAL t)) t*) (List.map (fun (instr : instr) => instr) instr*))) ->
    (f == { LOCALS := ((List.map (fun (val : val) => (some val)) val*) ++ (List.map (fun (t : valtype) => (default_ t)) t*)), MODULE := (fi.MODULE) }) ->
    Step_read (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.REF.FUNC_ADDR a), (.CALL_REF yy)])) [(.FRAME_ m f [(.LABEL_ m [] (List.map (fun (instr : instr) => instr) instr*))])]
  | return_call : forall (z : state) (x : idx) (a : addr), 
    (a < (List.length (funcinst z))) ->
    (wf_config (. z [(.RETURN_CALL x)])) ->
    (wf_instr (.REF.FUNC_ADDR a)) ->
    (wf_instr (.RETURN_CALL_REF (typeuse_deftype (((funcinst z)[a]!).TYPE)))) ->
    ((proj_uN_0 x) < (List.length ((moduleinst z).FUNCS))) ->
    ((((moduleinst z).FUNCS)[(proj_uN_0 x)]!) == a) ->
    Step_read (. z [(.RETURN_CALL x)]) [(.REF.FUNC_ADDR a), (.RETURN_CALL_REF (typeuse_deftype (((funcinst z)[a]!).TYPE)))]
  | return_call_ref-label : forall (z : state) (k : n) (instr'* : (List instr)) (val* : (List val)) (yy : typeuse) (instr* : (List instr)), 
    (wf_config (. z [(.LABEL_ k (List.map (fun (instr' : instr) => instr') instr'*) ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([(.RETURN_CALL_REF yy)] ++ (List.map (fun (instr : instr) => instr) instr*))))])) ->
    (wf_instr (.RETURN_CALL_REF yy)) ->
    Step_read (. z [(.LABEL_ k (List.map (fun (instr' : instr) => instr') instr'*) ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([(.RETURN_CALL_REF yy)] ++ (List.map (fun (instr : instr) => instr) instr*))))]) ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.RETURN_CALL_REF yy)])
  | return_call_ref-handler : forall (z : state) (k : n) (catch* : (List «catch»)) (val* : (List val)) (yy : typeuse) (instr* : (List instr)), 
    (wf_config (. z [(.HANDLER_ k (List.map (fun (catch : «catch») => «catch») catch*) ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([(.RETURN_CALL_REF yy)] ++ (List.map (fun (instr : instr) => instr) instr*))))])) ->
    (wf_instr (.RETURN_CALL_REF yy)) ->
    Step_read (. z [(.HANDLER_ k (List.map (fun (catch : «catch») => «catch») catch*) ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([(.RETURN_CALL_REF yy)] ++ (List.map (fun (instr : instr) => instr) instr*))))]) ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.RETURN_CALL_REF yy)])
  | return_call_ref-frame-null : forall (z : state) (k : n) (f : frame) (val* : (List val)) (ht : heaptype) (yy : typeuse) (instr* : (List instr)), 
    (wf_config (. z [(.FRAME_ k f ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([(.REF.NULL ht)] ++ ([(.RETURN_CALL_REF yy)] ++ (List.map (fun (instr : instr) => instr) instr*)))))])) ->
    (wf_instr .TRAP) ->
    Step_read (. z [(.FRAME_ k f ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([(.REF.NULL ht)] ++ ([(.RETURN_CALL_REF yy)] ++ (List.map (fun (instr : instr) => instr) instr*)))))]) [.TRAP]
  | return_call_ref-frame-addr : forall (z : state) (k : n) (f : frame) (val'* : (List val)) (val* : (List val)) (n : n) (a : addr) (yy : typeuse) (instr* : (List instr)) (t_1* : (List valtype)) (t_2* : (List valtype)) (m : m), 
    ((List.length val*) == n) ->
    (wf_config (. z [(.FRAME_ k f ((List.map (fun (val' : val) => (instr_val val')) val'*) ++ ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([(.REF.FUNC_ADDR a)] ++ ([(.RETURN_CALL_REF yy)] ++ (List.map (fun (instr : instr) => instr) instr*))))))])) ->
    (wf_instr (.REF.FUNC_ADDR a)) ->
    (wf_instr (.CALL_REF yy)) ->
    ((List.length t_1*) == n) ->
    ((List.length t_2*) == m) ->
    (wf_comptype (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    (a < (List.length (funcinst z))) ->
    (Expand (((funcinst z)[a]!).TYPE) (.FUNC (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Step_read (. z [(.FRAME_ k f ((List.map (fun (val' : val) => (instr_val val')) val'*) ++ ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([(.REF.FUNC_ADDR a)] ++ ([(.RETURN_CALL_REF yy)] ++ (List.map (fun (instr : instr) => instr) instr*))))))]) ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.REF.FUNC_ADDR a), (.CALL_REF yy)])
  | throw_ref-null : forall (z : state) (ht : heaptype), 
    (wf_config (. z [(.REF.NULL ht), .THROW_REF])) ->
    (wf_instr .TRAP) ->
    Step_read (. z [(.REF.NULL ht), .THROW_REF]) [.TRAP]
  | throw_ref-instrs : forall (z : state) (val* : (List val)) (a : addr) (instr* : (List instr)), 
    (wf_config (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([(.REF.EXN_ADDR a)] ++ ([.THROW_REF] ++ (List.map (fun (instr : instr) => instr) instr*)))))) ->
    (wf_instr (.REF.EXN_ADDR a)) ->
    (wf_instr .THROW_REF) ->
    (((List.map (fun (val : val) => val) val*) != []) || ((List.map (fun (instr : instr) => instr) instr*) != [])) ->
    Step_read (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ ([(.REF.EXN_ADDR a)] ++ ([.THROW_REF] ++ (List.map (fun (instr : instr) => instr) instr*))))) [(.REF.EXN_ADDR a), .THROW_REF]
  | throw_ref-label : forall (z : state) (n : n) (instr'* : (List instr)) (a : addr), 
    (wf_config (. z [(.LABEL_ n (List.map (fun (instr' : instr) => instr') instr'*) [(.REF.EXN_ADDR a), .THROW_REF])])) ->
    (wf_instr (.REF.EXN_ADDR a)) ->
    (wf_instr .THROW_REF) ->
    Step_read (. z [(.LABEL_ n (List.map (fun (instr' : instr) => instr') instr'*) [(.REF.EXN_ADDR a), .THROW_REF])]) [(.REF.EXN_ADDR a), .THROW_REF]
  | throw_ref-frame : forall (z : state) (n : n) (f : frame) (a : addr), 
    (wf_config (. z [(.FRAME_ n f [(.REF.EXN_ADDR a), .THROW_REF])])) ->
    (wf_instr (.REF.EXN_ADDR a)) ->
    (wf_instr .THROW_REF) ->
    Step_read (. z [(.FRAME_ n f [(.REF.EXN_ADDR a), .THROW_REF])]) [(.REF.EXN_ADDR a), .THROW_REF]
  | throw_ref-handler-empty : forall (z : state) (n : n) (a : addr), 
    (wf_config (. z [(.HANDLER_ n [] [(.REF.EXN_ADDR a), .THROW_REF])])) ->
    (wf_instr (.REF.EXN_ADDR a)) ->
    (wf_instr .THROW_REF) ->
    Step_read (. z [(.HANDLER_ n [] [(.REF.EXN_ADDR a), .THROW_REF])]) [(.REF.EXN_ADDR a), .THROW_REF]
  | throw_ref-handler-catch : forall (z : state) (n : n) (x : idx) (l : labelidx) (catch'* : (List «catch»)) (a : addr) (val* : (List val)), 
    Forall (fun (val : val) => (wf_val val)) val* ->
    (wf_config (. z [(.HANDLER_ n ([(.CATCH x l)] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])])) ->
    (wf_instr (.BR l)) ->
    (a < (List.length (exninst z))) ->
    ((proj_uN_0 x) < (List.length (tagaddr z))) ->
    ((((exninst z)[a]!).TAG) == ((tagaddr z)[(proj_uN_0 x)]!)) ->
    ((List.map (fun (val : val) => val) val*) == (((exninst z)[a]!).FIELDS)) ->
    Step_read (. z [(.HANDLER_ n ([(.CATCH x l)] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])]) ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.BR l)])
  | throw_ref-handler-catch_ref : forall (z : state) (n : n) (x : idx) (l : labelidx) (catch'* : (List «catch»)) (a : addr) (val* : (List val)), 
    Forall (fun (val : val) => (wf_val val)) val* ->
    (wf_config (. z [(.HANDLER_ n ([(.CATCH_REF x l)] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])])) ->
    (wf_instr (.REF.EXN_ADDR a)) ->
    (wf_instr (.BR l)) ->
    (a < (List.length (exninst z))) ->
    ((proj_uN_0 x) < (List.length (tagaddr z))) ->
    ((((exninst z)[a]!).TAG) == ((tagaddr z)[(proj_uN_0 x)]!)) ->
    ((List.map (fun (val : val) => val) val*) == (((exninst z)[a]!).FIELDS)) ->
    Step_read (. z [(.HANDLER_ n ([(.CATCH_REF x l)] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])]) ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.REF.EXN_ADDR a), (.BR l)])
  | throw_ref-handler-catch_all : forall (z : state) (n : n) (l : labelidx) (catch'* : (List «catch»)) (a : addr), 
    (wf_config (. z [(.HANDLER_ n ([(.CATCH_ALL l)] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])])) ->
    (wf_instr (.BR l)) ->
    Step_read (. z [(.HANDLER_ n ([(.CATCH_ALL l)] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])]) [(.BR l)]
  | throw_ref-handler-catch_all_ref : forall (z : state) (n : n) (l : labelidx) (catch'* : (List «catch»)) (a : addr), 
    (wf_config (. z [(.HANDLER_ n ([(.CATCH_ALL_REF l)] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])])) ->
    (wf_instr (.REF.EXN_ADDR a)) ->
    (wf_instr (.BR l)) ->
    Step_read (. z [(.HANDLER_ n ([(.CATCH_ALL_REF l)] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])]) [(.REF.EXN_ADDR a), (.BR l)]
  | throw_ref-handler-next : forall (z : state) (n : n) (catch : «catch») (catch'* : (List «catch»)) (a : addr), 
    (wf_config (. z [(.HANDLER_ n ([«catch»] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])])) ->
    (wf_instr (.HANDLER_ n (List.map (fun (catch' : «catch») => catch') catch'*) [(.REF.EXN_ADDR a), .THROW_REF])) ->
    (¬(Step_read_before_throw_ref-handler-next (. z [(.HANDLER_ n ([«catch»] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])]))) ->
    Step_read (. z [(.HANDLER_ n ([«catch»] ++ (List.map (fun (catch' : «catch») => catch') catch'*)) [(.REF.EXN_ADDR a), .THROW_REF])]) [(.HANDLER_ n (List.map (fun (catch' : «catch») => catch') catch'*) [(.REF.EXN_ADDR a), .THROW_REF])]
  | try_table : forall (z : state) (val* : (List val)) (m : m) (bt : blocktype) (catch* : (List «catch»)) (instr* : (List instr)) (n : n) (t_1* : (List valtype)) (t_2* : (List valtype)), 
    ((List.length val*) == m) ->
    (wf_config (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.TRY_TABLE bt (. (List.map (fun (catch : «catch») => «catch») catch*)) (List.map (fun (instr : instr) => instr) instr*))]))) ->
    (wf_instr (.HANDLER_ n (List.map (fun (catch : «catch») => «catch») catch*) [(.LABEL_ n [] ((List.map (fun (val : val) => (instr_val val)) val*) ++ (List.map (fun (instr : instr) => instr) instr*)))])) ->
    ((List.length t_1*) == m) ->
    ((List.length t_2*) == n) ->
    (wf_instrtype (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    ((blocktype_ z bt) == (. (. (List.map (fun (t_1 : valtype) => t_1) t_1*)) [] (. (List.map (fun (t_2 : valtype) => t_2) t_2*)))) ->
    Step_read (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.TRY_TABLE bt (. (List.map (fun (catch : «catch») => «catch») catch*)) (List.map (fun (instr : instr) => instr) instr*))])) [(.HANDLER_ n (List.map (fun (catch : «catch») => «catch») catch*) [(.LABEL_ n [] ((List.map (fun (val : val) => (instr_val val)) val*) ++ (List.map (fun (instr : instr) => instr) instr*)))])]
  | local.get : forall (z : state) (x : idx) (val : val), 
    (wf_val val) ->
    (wf_config (. z [(.LOCAL.GET x)])) ->
    ((«local» z x) == (some val)) ->
    Step_read (. z [(.LOCAL.GET x)]) [(instr_val val)]
  | global.get : forall (z : state) (x : idx) (val : val), 
    (wf_val val) ->
    (wf_config (. z [(.GLOBAL.GET x)])) ->
    (((global z x).VALUE) == val) ->
    Step_read (. z [(.GLOBAL.GET x)]) [(instr_val val)]
  | table.get-oob : forall (z : state) (at : addrtype) (i : num_) (x : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.TABLE.GET x)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 at i))) >= (List.length ((table z x).REFS))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.TABLE.GET x)]) [.TRAP]
  | table.get-val : forall (z : state) (at : addrtype) (i : num_) (x : idx), 
    ((proj_uN_0 (Option.get! (proj_num__0 at i))) < (List.length ((table z x).REFS))) ->
    ((proj_num__0 at i) != none) ->
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.TABLE.GET x)])) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.TABLE.GET x)]) [(instr_ref (((table z x).REFS)[(proj_uN_0 (Option.get! (proj_num__0 at i)))]!))]
  | table.size : forall (z : state) (x : idx) (at : addrtype) (n : n) (lim : limits) (rt : reftype), 
    (wf_config (. z [(.TABLE.SIZE x)])) ->
    (wf_instr (.CONST (numtype_addrtype at) (.mk_num__0 at (. n)))) ->
    (wf_tabletype (. at lim rt)) ->
    ((List.length ((table z x).REFS)) == n) ->
    (((table z x).TYPE) == (. at lim rt)) ->
    Step_read (. z [(.TABLE.SIZE x)]) [(.CONST (numtype_addrtype at) (.mk_num__0 at (. n)))]
  | table.fill-oob : forall (z : state) (at : addrtype) (i : num_) (val : val) (n : n) (x : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.FILL x)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 at i))) + n) > (List.length ((table z x).REFS))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.FILL x)]) [.TRAP]
  | table.fill-zero : forall (z : state) (at : addrtype) (i : num_) (val : val) (n : n) (x : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.FILL x)])) ->
    (¬(Step_read_before_table.fill-zero (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.FILL x)]))) ->
    (n == 0) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.FILL x)]) []
  | table.fill-succ : forall (z : state) (at : addrtype) (i : num_) (val : val) (n : n) (x : idx), 
    ((proj_num__0 at i) != none) ->
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.FILL x)])) ->
    (wf_instr (.CONST (numtype_addrtype at) i)) ->
    (wf_instr (.TABLE.SET x)) ->
    (wf_instr (.CONST (numtype_addrtype at) (.mk_num__0 at (. ((proj_uN_0 (Option.get! (proj_num__0 at i))) + 1))))) ->
    (wf_instr (.CONST (numtype_addrtype at) (.mk_num__0 at (. (((n : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.TABLE.FILL x)) ->
    (¬(Step_read_before_table.fill-succ (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.FILL x)]))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.FILL x)]) [(.CONST (numtype_addrtype at) i), (instr_val val), (.TABLE.SET x), (.CONST (numtype_addrtype at) (.mk_num__0 at (. ((proj_uN_0 (Option.get! (proj_num__0 at i))) + 1)))), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. (((n : Nat) - (1 : Nat)) : Nat)))), (.TABLE.FILL x)]
  | table.copy-oob : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at_1 i_1) != none) ->
    ((proj_num__0 at_2 i_2) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + n) > (List.length ((table z x_1).REFS))) || (((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + n) > (List.length ((table z x_2).REFS)))) ->
    Step_read (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x_1 x_2)]) [.TRAP]
  | table.copy-zero : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)])) ->
    (¬(Step_read_before_table.copy-zero (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)]))) ->
    (n == 0) ->
    Step_read (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)]) []
  | table.copy-le : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x : idx) (y : idx), 
    ((proj_num__0 at_1 i_1) != none) ->
    ((proj_num__0 at_2 i_2) != none) ->
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)])) ->
    (wf_instr (.CONST (numtype_addrtype at_1) i_1)) ->
    (wf_instr (.CONST (numtype_addrtype at_2) i_2)) ->
    (wf_instr (.TABLE.GET y)) ->
    (wf_instr (.TABLE.SET x)) ->
    (wf_instr (.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (. ((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + 1))))) ->
    (wf_instr (.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (. ((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + 1))))) ->
    (wf_instr (.CONST (numtype_addrtype at') (.mk_num__0 at' (. (((n : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.TABLE.COPY x y)) ->
    (¬(Step_read_before_table.copy-le (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)]))) ->
    ((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) <= (proj_uN_0 (Option.get! (proj_num__0 at_2 i_2)))) ->
    Step_read (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)]) [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.TABLE.GET y), (.TABLE.SET x), (.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (. ((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + 1)))), (.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (. ((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + 1)))), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. (((n : Nat) - (1 : Nat)) : Nat)))), (.TABLE.COPY x y)]
  | table.copy-gt : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x : idx) (y : idx), 
    ((proj_num__0 at_1 i_1) != none) ->
    ((proj_num__0 at_2 i_2) != none) ->
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)])) ->
    (wf_instr (.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (. (((((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + n) : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (. (((((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + n) : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.TABLE.GET y)) ->
    (wf_instr (.TABLE.SET x)) ->
    (wf_instr (.CONST (numtype_addrtype at_1) i_1)) ->
    (wf_instr (.CONST (numtype_addrtype at_2) i_2)) ->
    (wf_instr (.CONST (numtype_addrtype at') (.mk_num__0 at' (. (((n : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.TABLE.COPY x y)) ->
    (¬(Step_read_before_table.copy-gt (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)]))) ->
    Step_read (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.TABLE.COPY x y)]) [(.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (. (((((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + n) : Nat) - (1 : Nat)) : Nat)))), (.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (. (((((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + n) : Nat) - (1 : Nat)) : Nat)))), (.TABLE.GET y), (.TABLE.SET x), (.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. (((n : Nat) - (1 : Nat)) : Nat)))), (.TABLE.COPY x y)]
  | table.init-oob : forall (z : state) (at : addrtype) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.TABLE.INIT x y)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    ((proj_num__0 .I32 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at i))) + n) > (List.length ((table z x).REFS))) || (((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + n) > (List.length ((elem z y).REFS)))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.TABLE.INIT x y)]) [.TRAP]
  | table.init-zero : forall (z : state) (at : addrtype) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.TABLE.INIT x y)])) ->
    (¬(Step_read_before_table.init-zero (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.TABLE.INIT x y)]))) ->
    (n == 0) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.TABLE.INIT x y)]) []
  | table.init-succ : forall (z : state) (at : addrtype) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    ((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) < (List.length ((elem z y).REFS))) ->
    ((proj_num__0 .I32 j) != none) ->
    ((proj_num__0 at i) != none) ->
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.TABLE.INIT x y)])) ->
    (wf_instr (.CONST (numtype_addrtype at) i)) ->
    (wf_instr (.TABLE.SET x)) ->
    (wf_instr (.CONST (numtype_addrtype at) (.mk_num__0 at (. ((proj_uN_0 (Option.get! (proj_num__0 at i))) + 1))))) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + 1))))) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. (((n : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.TABLE.INIT x y)) ->
    (¬(Step_read_before_table.init-succ (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.TABLE.INIT x y)]))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.TABLE.INIT x y)]) [(.CONST (numtype_addrtype at) i), (instr_ref (((elem z y).REFS)[(proj_uN_0 (Option.get! (proj_num__0 .I32 j)))]!)), (.TABLE.SET x), (.CONST (numtype_addrtype at) (.mk_num__0 at (. ((proj_uN_0 (Option.get! (proj_num__0 at i))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (. (((n : Nat) - (1 : Nat)) : Nat)))), (.TABLE.INIT x y)]
  | load-num-oob : forall (z : state) (at : addrtype) (i : num_) (nt : numtype) (x : idx) (ao : memarg), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.LOAD nt none x ao)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) + ((((size nt) : Nat) / (8 : Nat)) : Nat)) > (List.length ((mem z x).BYTES))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.LOAD nt none x ao)]) [.TRAP]
  | load-num-val : forall (z : state) (at : addrtype) (i : num_) (nt : numtype) (x : idx) (ao : memarg) (c : num_), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.LOAD nt none x ao)])) ->
    (wf_instr (.CONST nt c)) ->
    ((proj_num__0 at i) != none) ->
    ((nbytes_ nt c) == (List.extract ((mem z x).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) ((((size nt) : Nat) / (8 : Nat)) : Nat))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.LOAD nt none x ao)]) [(.CONST nt c)]
  | load-pack-oob : forall (z : state) (at : addrtype) (i : num_) (Inn : Inn) (n : n) (sx : sx) (x : idx) (ao : memarg), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.LOAD (numtype_addrtype Inn) (some (.mk_loadop__0 Inn (._ (. n) sx))) x ao)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) + (((n : Nat) / (8 : Nat)) : Nat)) > (List.length ((mem z x).BYTES))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.LOAD (numtype_addrtype Inn) (some (.mk_loadop__0 Inn (._ (. n) sx))) x ao)]) [.TRAP]
  | load-pack-val : forall (z : state) (at : addrtype) (i : num_) (Inn : Inn) (n : n) (sx : sx) (x : idx) (ao : memarg) (c : iN), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.LOAD (numtype_addrtype Inn) (some (.mk_loadop__0 Inn (._ (. n) sx))) x ao)])) ->
    (wf_instr (.CONST (numtype_addrtype Inn) (.mk_num__0 Inn (extend__ n (size (numtype_addrtype Inn)) sx c)))) ->
    ((proj_num__0 at i) != none) ->
    ((ibytes_ n c) == (List.extract ((mem z x).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) (((n : Nat) / (8 : Nat)) : Nat))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.LOAD (numtype_addrtype Inn) (some (.mk_loadop__0 Inn (._ (. n) sx))) x ao)]) [(.CONST (numtype_addrtype Inn) (.mk_num__0 Inn (extend__ n (size (numtype_addrtype Inn)) sx c)))]
  | vload-oob : forall (z : state) (at : addrtype) (i : num_) (x : idx) (ao : memarg), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.VLOAD .V128 none x ao)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) + ((((vsize .V128) : Nat) / (8 : Nat)) : Nat)) > (List.length ((mem z x).BYTES))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.VLOAD .V128 none x ao)]) [.TRAP]
  | vload-val : forall (z : state) (at : addrtype) (i : num_) (x : idx) (ao : memarg) (c : vec_), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.VLOAD .V128 none x ao)])) ->
    (wf_instr (.VCONST .V128 c)) ->
    ((proj_num__0 at i) != none) ->
    ((vbytes_ .V128 c) == (List.extract ((mem z x).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) ((((vsize .V128) : Nat) / (8 : Nat)) : Nat))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.VLOAD .V128 none x ao)]) [(.VCONST .V128 c)]
  | vload-pack-oob : forall (z : state) (at : addrtype) (i : num_) (M : M) (K : K) (sx : sx) (x : idx) (ao : memarg), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.VLOAD .V128 (some (.SHAPEX_ (. M) K sx)) x ao)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) + ((((M * K) : Nat) / (8 : Nat)) : Nat)) > (List.length ((mem z x).BYTES))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.VLOAD .V128 (some (.SHAPEX_ (. M) K sx)) x ao)]) [.TRAP]
  | vload-pack-val : forall (z : state) (at : addrtype) (i : num_) (M : M) (K : K) (sx : sx) (x : idx) (ao : memarg) (c : vec_) (j* : (List iN)) (k* : (List Nat)) (Jnn : Jnn), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.VLOAD .V128 (some (.SHAPEX_ (. M) K sx)) x ao)])) ->
    (wf_instr (.VCONST .V128 c)) ->
    (wf_shape (.X (lanetype_Jnn Jnn) (. K))) ->
    ((List.length j*) == K) ->
    Forall (fun (j : iN) => (wf_lane_ (lanetype (.X (lanetype_Jnn Jnn) (. K))) (.mk_lane__2 Jnn (extend__ M (jsizenn Jnn) sx j)))) j* ->
    Forall (fun (j : iN) => ((proj_num__0 at i) != none)) j* ->
    Forall₂ (fun (j : iN) (k : Nat) => ((ibytes_ M j) == (List.extract ((mem z x).BYTES) (((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) + ((((k * M) : Nat) / (8 : Nat)) : Nat)) (((M : Nat) / (8 : Nat)) : Nat)))) j* k* ->
    ((c == (inv_lanes_ (.X (lanetype_Jnn Jnn) (. K)) (List.map (fun (j : iN) => (.mk_lane__2 Jnn (extend__ M (jsizenn Jnn) sx j))) j*))) && ((jsizenn Jnn) == (M * 2))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.VLOAD .V128 (some (.SHAPEX_ (. M) K sx)) x ao)]) [(.VCONST .V128 c)]
  | vload-splat-oob : forall (z : state) (at : addrtype) (i : num_) (N : N) (x : idx) (ao : memarg), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.VLOAD .V128 (some (.SPLAT (. N))) x ao)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) + (((N : Nat) / (8 : Nat)) : Nat)) > (List.length ((mem z x).BYTES))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.VLOAD .V128 (some (.SPLAT (. N))) x ao)]) [.TRAP]
  | vload-splat-val : forall (z : state) (at : addrtype) (i : num_) (N : N) (x : idx) (ao : memarg) (c : vec_) (j : iN) (Jnn : Jnn) (M : M), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.VLOAD .V128 (some (.SPLAT (. N))) x ao)])) ->
    (wf_instr (.VCONST .V128 c)) ->
    (wf_shape (.X (lanetype_Jnn Jnn) (. M))) ->
    (wf_lane_ (lanetype (.X (lanetype_Jnn Jnn) (. M))) (.mk_lane__2 Jnn (. (proj_uN_0 j)))) ->
    ((proj_num__0 at i) != none) ->
    ((ibytes_ N j) == (List.extract ((mem z x).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) (((N : Nat) / (8 : Nat)) : Nat))) ->
    (N == (jsize Jnn)) ->
    ((M : Nat) == ((128 : Nat) / (N : Nat))) ->
    (c == (inv_lanes_ (.X (lanetype_Jnn Jnn) (. M)) (List.replicate M (.mk_lane__2 Jnn (. (proj_uN_0 j)))))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.VLOAD .V128 (some (.SPLAT (. N))) x ao)]) [(.VCONST .V128 c)]
  | vload-zero-oob : forall (z : state) (at : addrtype) (i : num_) (N : N) (x : idx) (ao : memarg), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.VLOAD .V128 (some (.ZERO (. N))) x ao)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) + (((N : Nat) / (8 : Nat)) : Nat)) > (List.length ((mem z x).BYTES))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.VLOAD .V128 (some (.ZERO (. N))) x ao)]) [.TRAP]
  | vload-zero-val : forall (z : state) (at : addrtype) (i : num_) (N : N) (x : idx) (ao : memarg) (c : vec_) (j : iN), 
    (wf_uN N j) ->
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.VLOAD .V128 (some (.ZERO (. N))) x ao)])) ->
    (wf_instr (.VCONST .V128 c)) ->
    ((proj_num__0 at i) != none) ->
    ((ibytes_ N j) == (List.extract ((mem z x).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) (((N : Nat) / (8 : Nat)) : Nat))) ->
    (c == (extend__ N 128 .U j)) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.VLOAD .V128 (some (.ZERO (. N))) x ao)]) [(.VCONST .V128 c)]
  | vload_lane-oob : forall (z : state) (at : addrtype) (i : num_) (c_1 : vec_) (N : N) (x : idx) (ao : memarg) (j : laneidx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.VCONST .V128 c_1), (.VLOAD_LANE .V128 (. N) x ao j)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) + (((N : Nat) / (8 : Nat)) : Nat)) > (List.length ((mem z x).BYTES))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.VCONST .V128 c_1), (.VLOAD_LANE .V128 (. N) x ao j)]) [.TRAP]
  | vload_lane-val : forall (z : state) (at : addrtype) (i : num_) (c_1 : vec_) (N : N) (x : idx) (ao : memarg) (j : laneidx) (c : vec_) (k : iN) (Jnn : Jnn) (M : M), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.VCONST .V128 c_1), (.VLOAD_LANE .V128 (. N) x ao j)])) ->
    (wf_instr (.VCONST .V128 c)) ->
    (wf_shape (.X (lanetype_Jnn Jnn) (. M))) ->
    (wf_lane_ (lanetype (.X (lanetype_Jnn Jnn) (. M))) (.mk_lane__2 Jnn (. (proj_uN_0 k)))) ->
    ((proj_num__0 at i) != none) ->
    ((ibytes_ N k) == (List.extract ((mem z x).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) (((N : Nat) / (8 : Nat)) : Nat))) ->
    (N == (jsize Jnn)) ->
    ((M : Nat) == (((vsize .V128) : Nat) / (N : Nat))) ->
    (c == (inv_lanes_ (.X (lanetype_Jnn Jnn) (. M)) (List.modify (lanes_ (.X (lanetype_Jnn Jnn) (. M)) c_1) (proj_uN_0 j) (fun (_ : lane_) => (.mk_lane__2 Jnn (. (proj_uN_0 k))))))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.VCONST .V128 c_1), (.VLOAD_LANE .V128 (. N) x ao j)]) [(.VCONST .V128 c)]
  | memory.size : forall (z : state) (x : idx) (at : addrtype) (n : n) (lim : limits), 
    (wf_config (. z [(.MEMORY.SIZE x)])) ->
    (wf_instr (.CONST (numtype_addrtype at) (.mk_num__0 at (. n)))) ->
    (wf_memtype (.PAGE at lim)) ->
    ((n * (64 * (Ki ))) == (List.length ((mem z x).BYTES))) ->
    (((mem z x).TYPE) == (.PAGE at lim)) ->
    Step_read (. z [(.MEMORY.SIZE x)]) [(.CONST (numtype_addrtype at) (.mk_num__0 at (. n)))]
  | memory.fill-oob : forall (z : state) (at : addrtype) (i : num_) (val : val) (n : n) (x : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.FILL x)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 at i))) + n) > (List.length ((mem z x).BYTES))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.FILL x)]) [.TRAP]
  | memory.fill-zero : forall (z : state) (at : addrtype) (i : num_) (val : val) (n : n) (x : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.FILL x)])) ->
    (¬(Step_read_before_memory.fill-zero (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.FILL x)]))) ->
    (n == 0) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.FILL x)]) []
  | memory.fill-succ : forall (z : state) (at : addrtype) (i : num_) (val : val) (n : n) (x : idx), 
    ((proj_num__0 at i) != none) ->
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.FILL x)])) ->
    (wf_instr (.CONST (numtype_addrtype at) i)) ->
    (wf_instr (.STORE .I32 (some (.mk_storeop__0 .I32 (. (. 8)))) x (memarg0 ))) ->
    (wf_instr (.CONST (numtype_addrtype at) (.mk_num__0 at (. ((proj_uN_0 (Option.get! (proj_num__0 at i))) + 1))))) ->
    (wf_instr (.CONST (numtype_addrtype at) (.mk_num__0 at (. (((n : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.MEMORY.FILL x)) ->
    (¬(Step_read_before_memory.fill-succ (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.FILL x)]))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.FILL x)]) [(.CONST (numtype_addrtype at) i), (instr_val val), (.STORE .I32 (some (.mk_storeop__0 .I32 (. (. 8)))) x (memarg0 )), (.CONST (numtype_addrtype at) (.mk_num__0 at (. ((proj_uN_0 (Option.get! (proj_num__0 at i))) + 1)))), (instr_val val), (.CONST (numtype_addrtype at) (.mk_num__0 at (. (((n : Nat) - (1 : Nat)) : Nat)))), (.MEMORY.FILL x)]
  | memory.copy-oob : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at_1 i_1) != none) ->
    ((proj_num__0 at_2 i_2) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + n) > (List.length ((mem z x_1).BYTES))) || (((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + n) > (List.length ((mem z x_2).BYTES)))) ->
    Step_read (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)]) [.TRAP]
  | memory.copy-zero : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)])) ->
    (¬(Step_read_before_memory.copy-zero (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)]))) ->
    (n == 0) ->
    Step_read (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)]) []
  | memory.copy-le : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x_1 : idx) (x_2 : idx), 
    ((proj_num__0 at_1 i_1) != none) ->
    ((proj_num__0 at_2 i_2) != none) ->
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)])) ->
    (wf_instr (.CONST (numtype_addrtype at_1) i_1)) ->
    (wf_instr (.CONST (numtype_addrtype at_2) i_2)) ->
    (wf_instr (.LOAD .I32 (some (.mk_loadop__0 .I32 (._ (. 8) .U))) x_2 (memarg0 ))) ->
    (wf_instr (.STORE .I32 (some (.mk_storeop__0 .I32 (. (. 8)))) x_1 (memarg0 ))) ->
    (wf_instr (.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (. ((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + 1))))) ->
    (wf_instr (.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (. ((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + 1))))) ->
    (wf_instr (.CONST (numtype_addrtype at') (.mk_num__0 at' (. (((n : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.MEMORY.COPY x_1 x_2)) ->
    (¬(Step_read_before_memory.copy-le (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)]))) ->
    ((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) <= (proj_uN_0 (Option.get! (proj_num__0 at_2 i_2)))) ->
    Step_read (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)]) [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.LOAD .I32 (some (.mk_loadop__0 .I32 (._ (. 8) .U))) x_2 (memarg0 )), (.STORE .I32 (some (.mk_storeop__0 .I32 (. (. 8)))) x_1 (memarg0 )), (.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (. ((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + 1)))), (.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (. ((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + 1)))), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. (((n : Nat) - (1 : Nat)) : Nat)))), (.MEMORY.COPY x_1 x_2)]
  | memory.copy-gt : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (n : n) (x_1 : idx) (x_2 : idx), 
    ((proj_num__0 at_1 i_1) != none) ->
    ((proj_num__0 at_2 i_2) != none) ->
    (wf_config (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)])) ->
    (wf_instr (.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (. (((((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + n) : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (. (((((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + n) : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.LOAD .I32 (some (.mk_loadop__0 .I32 (._ (. 8) .U))) x_2 (memarg0 ))) ->
    (wf_instr (.STORE .I32 (some (.mk_storeop__0 .I32 (. (. 8)))) x_1 (memarg0 ))) ->
    (wf_instr (.CONST (numtype_addrtype at_1) i_1)) ->
    (wf_instr (.CONST (numtype_addrtype at_2) i_2)) ->
    (wf_instr (.CONST (numtype_addrtype at') (.mk_num__0 at' (. (((n : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.MEMORY.COPY x_1 x_2)) ->
    (¬(Step_read_before_memory.copy-gt (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)]))) ->
    Step_read (. z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. n))), (.MEMORY.COPY x_1 x_2)]) [(.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (. (((((proj_uN_0 (Option.get! (proj_num__0 at_1 i_1))) + n) : Nat) - (1 : Nat)) : Nat)))), (.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (. (((((proj_uN_0 (Option.get! (proj_num__0 at_2 i_2))) + n) : Nat) - (1 : Nat)) : Nat)))), (.LOAD .I32 (some (.mk_loadop__0 .I32 (._ (. 8) .U))) x_2 (memarg0 )), (.STORE .I32 (some (.mk_storeop__0 .I32 (. (. 8)))) x_1 (memarg0 )), (.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (. (((n : Nat) - (1 : Nat)) : Nat)))), (.MEMORY.COPY x_1 x_2)]
  | memory.init-oob : forall (z : state) (at : addrtype) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.MEMORY.INIT x y)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 at i) != none) ->
    ((proj_num__0 .I32 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at i))) + n) > (List.length ((mem z x).BYTES))) || (((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + n) > (List.length ((data z y).BYTES)))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.MEMORY.INIT x y)]) [.TRAP]
  | memory.init-zero : forall (z : state) (at : addrtype) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.MEMORY.INIT x y)])) ->
    (¬(Step_read_before_memory.init-zero (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.MEMORY.INIT x y)]))) ->
    (n == 0) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.MEMORY.INIT x y)]) []
  | memory.init-succ : forall (z : state) (at : addrtype) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    ((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) < (List.length ((data z y).BYTES))) ->
    ((proj_num__0 .I32 j) != none) ->
    ((proj_num__0 at i) != none) ->
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.MEMORY.INIT x y)])) ->
    (wf_instr (.CONST (numtype_addrtype at) i)) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. (proj_byte_0 (((data z y).BYTES)[(proj_uN_0 (Option.get! (proj_num__0 .I32 j)))]!)))))) ->
    (wf_instr (.STORE .I32 (some (.mk_storeop__0 .I32 (. (. 8)))) x (memarg0 ))) ->
    (wf_instr (.CONST (numtype_addrtype at) (.mk_num__0 at (. ((proj_uN_0 (Option.get! (proj_num__0 at i))) + 1))))) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + 1))))) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. (((n : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.MEMORY.INIT x y)) ->
    (¬(Step_read_before_memory.init-succ (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.MEMORY.INIT x y)]))) ->
    Step_read (. z [(.CONST (numtype_addrtype at) i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.MEMORY.INIT x y)]) [(.CONST (numtype_addrtype at) i), (.CONST .I32 (.mk_num__0 .I32 (. (proj_byte_0 (((data z y).BYTES)[(proj_uN_0 (Option.get! (proj_num__0 .I32 j)))]!))))), (.STORE .I32 (some (.mk_storeop__0 .I32 (. (. 8)))) x (memarg0 )), (.CONST (numtype_addrtype at) (.mk_num__0 at (. ((proj_uN_0 (Option.get! (proj_num__0 at i))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (. (((n : Nat) - (1 : Nat)) : Nat)))), (.MEMORY.INIT x y)]
  | ref.null-idx : forall (z : state) (x : idx), 
    (wf_config (. z [(.REF.NULL (._IDX x))])) ->
    (wf_instr (.REF.NULL (heaptype_deftype (type z x)))) ->
    Step_read (. z [(.REF.NULL (._IDX x))]) [(.REF.NULL (heaptype_deftype (type z x)))]
  | ref.func : forall (z : state) (x : idx), 
    ((proj_uN_0 x) < (List.length ((moduleinst z).FUNCS))) ->
    (wf_config (. z [(.REF.FUNC x)])) ->
    (wf_instr (.REF.FUNC_ADDR (((moduleinst z).FUNCS)[(proj_uN_0 x)]!))) ->
    Step_read (. z [(.REF.FUNC x)]) [(.REF.FUNC_ADDR (((moduleinst z).FUNCS)[(proj_uN_0 x)]!))]
  | ref.test-true : forall (s : store) (f : frame) (ref : ref) (rt : reftype) (rt' : reftype), 
    (wf_reftype rt') ->
    (wf_config (. (. s f) [(instr_ref ref), (.REF.TEST rt)])) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. 1)))) ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (Ref_ok s ref rt') ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt' (inst_reftype (f.MODULE) rt)) ->
    Step_read (. (. s f) [(instr_ref ref), (.REF.TEST rt)]) [(.CONST .I32 (.mk_num__0 .I32 (. 1)))]
  | ref.test-false : forall (s : store) (f : frame) (ref : ref) (rt : reftype), 
    (wf_config (. (. s f) [(instr_ref ref), (.REF.TEST rt)])) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. 0)))) ->
    (¬(Step_read_before_ref.test-false (. (. s f) [(instr_ref ref), (.REF.TEST rt)]))) ->
    Step_read (. (. s f) [(instr_ref ref), (.REF.TEST rt)]) [(.CONST .I32 (.mk_num__0 .I32 (. 0)))]
  | ref.cast-succeed : forall (s : store) (f : frame) (ref : ref) (rt : reftype) (rt' : reftype), 
    (wf_reftype rt') ->
    (wf_config (. (. s f) [(instr_ref ref), (.REF.CAST rt)])) ->
    (wf_context { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) ->
    (Ref_ok s ref rt') ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt' (inst_reftype (f.MODULE) rt)) ->
    Step_read (. (. s f) [(instr_ref ref), (.REF.CAST rt)]) [(instr_ref ref)]
  | ref.cast-fail : forall (s : store) (f : frame) (ref : ref) (rt : reftype), 
    (wf_config (. (. s f) [(instr_ref ref), (.REF.CAST rt)])) ->
    (wf_instr .TRAP) ->
    (¬(Step_read_before_ref.cast-fail (. (. s f) [(instr_ref ref), (.REF.CAST rt)]))) ->
    Step_read (. (. s f) [(instr_ref ref), (.REF.CAST rt)]) [.TRAP]
  | struct.new_default : forall (z : state) (x : idx) (val* : (List val)) (mut?* : (List (Option «mut»))) (zt* : (List storagetype)), 
    Forall (fun (val : val) => (wf_val val)) val* ->
    (wf_config (. z [(.STRUCT.NEW_DEFAULT x)])) ->
    (wf_instr (.STRUCT.NEW x)) ->
    ((List.length mut?*) == (List.length zt*)) ->
    (wf_comptype (.STRUCT (. (List.zipWith (fun (mut? : (Option «mut»)) (zt : storagetype) => (. (Option.map (fun (mut : «mut») => «mut») mut?) zt)) mut?* zt*)))) ->
    (Expand (type z x) (.STRUCT (. (List.zipWith (fun (mut? : (Option «mut»)) (zt : storagetype) => (. (Option.map (fun (mut : «mut») => «mut») mut?) zt)) mut?* zt*)))) ->
    ((List.length val*) == (List.length zt*)) ->
    Forall₂ (fun (val : val) (zt : storagetype) => ((default_ (unpack zt)) == (some val))) val* zt* ->
    Step_read (. z [(.STRUCT.NEW_DEFAULT x)]) ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.STRUCT.NEW x)])
  | struct.get-null : forall (z : state) (ht : heaptype) (sx? : (Option sx)) (x : idx) (i : u32), 
    (wf_config (. z [(.REF.NULL ht), (.STRUCT.GET (Option.map (fun (sx : sx) => sx) sx?) x i)])) ->
    (wf_instr .TRAP) ->
    Step_read (. z [(.REF.NULL ht), (.STRUCT.GET (Option.map (fun (sx : sx) => sx) sx?) x i)]) [.TRAP]
  | struct.get-struct : forall (z : state) (a : addr) (sx? : (Option sx)) (x : idx) (i : u32) (zt* : (List storagetype)) (mut?* : (List (Option «mut»))), 
    ((proj_uN_0 i) < (List.length (List.map (fun (zt : storagetype) => zt) zt*))) ->
    ((proj_uN_0 i) < (List.length (((structinst z)[a]!).FIELDS))) ->
    (a < (List.length (structinst z))) ->
    (wf_config (. z [(.REF.STRUCT_ADDR a), (.STRUCT.GET (Option.map (fun (sx : sx) => sx) sx?) x i)])) ->
    ((List.length mut?*) == (List.length zt*)) ->
    (wf_comptype (.STRUCT (. (List.zipWith (fun (mut? : (Option «mut»)) (zt : storagetype) => (. (Option.map (fun (mut : «mut») => «mut») mut?) zt)) mut?* zt*)))) ->
    (Expand (type z x) (.STRUCT (. (List.zipWith (fun (mut? : (Option «mut»)) (zt : storagetype) => (. (Option.map (fun (mut : «mut») => «mut») mut?) zt)) mut?* zt*)))) ->
    Step_read (. z [(.REF.STRUCT_ADDR a), (.STRUCT.GET (Option.map (fun (sx : sx) => sx) sx?) x i)]) [(instr_val (unpackfield_ ((List.map (fun (zt : storagetype) => zt) zt*)[(proj_uN_0 i)]!) (Option.map (fun (sx : sx) => sx) sx?) ((((structinst z)[a]!).FIELDS)[(proj_uN_0 i)]!)))]
  | array.new_default : forall (z : state) (n : n) (x : idx) (val : val) (mut? : (Option «mut»)) (zt : storagetype), 
    (wf_val val) ->
    (wf_config (. z [(.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.NEW_DEFAULT x)])) ->
    (wf_instr (.ARRAY.NEW_FIXED x (. n))) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    (Expand (type z x) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    ((default_ (unpack zt)) == (some val)) ->
    Step_read (. z [(.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.NEW_DEFAULT x)]) ((List.replicate n (instr_val val)) ++ [(.ARRAY.NEW_FIXED x (. n))])
  | array.new_elem-oob : forall (z : state) (i : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.NEW_ELEM x y)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) + n) > (List.length ((elem z y).REFS))) ->
    Step_read (. z [(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.NEW_ELEM x y)]) [.TRAP]
  | array.new_elem-alloc : forall (z : state) (i : num_) (n : n) (x : idx) (y : idx) (ref* : (List ref)), 
    ((List.length ref*) == n) ->
    Forall (fun (ref : ref) => (wf_ref ref)) ref* ->
    (wf_config (. z [(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.NEW_ELEM x y)])) ->
    (wf_instr (.ARRAY.NEW_FIXED x (. n))) ->
    ((proj_num__0 .I32 i) != none) ->
    ((List.map (fun (ref : ref) => ref) ref*) == (List.extract ((elem z y).REFS) (proj_uN_0 (Option.get! (proj_num__0 .I32 i))) n)) ->
    Step_read (. z [(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.NEW_ELEM x y)]) ((List.map (fun (ref : ref) => (instr_ref ref)) ref*) ++ [(.ARRAY.NEW_FIXED x (. n))])
  | array.new_data-oob : forall (z : state) (i : num_) (n : n) (x : idx) (y : idx) (mut? : (Option «mut»)) (zt : storagetype), 
    (wf_config (. z [(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.NEW_DATA x y)])) ->
    (wf_instr .TRAP) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    (Expand (type z x) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    ((proj_num__0 .I32 i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) + ((((n * (zsize zt)) : Nat) / (8 : Nat)) : Nat)) > (List.length ((data z y).BYTES))) ->
    Step_read (. z [(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.NEW_DATA x y)]) [.TRAP]
  | array.new_data-num : forall (z : state) (i : num_) (n : n) (x : idx) (y : idx) (zt : storagetype) (c* : (List lit_)) (mut? : (Option «mut»)), 
    ((List.length c*) == n) ->
    Forall (fun (c : lit_) => ((cunpack zt) != none)) c* ->
    Forall (fun (c : lit_) => (wf_lit_ zt c)) c* ->
    (wf_config (. z [(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.NEW_DATA x y)])) ->
    (wf_instr (.ARRAY.NEW_FIXED x (. n))) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    (Expand (type z x) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    ((proj_num__0 .I32 i) != none) ->
    ((concatn_ byte (List.map (fun (c : lit_) => (zbytes_ zt c)) c*) ((((zsize zt) : Nat) / (8 : Nat)) : Nat)) == (List.extract ((data z y).BYTES) (proj_uN_0 (Option.get! (proj_num__0 .I32 i))) ((((n * (zsize zt)) : Nat) / (8 : Nat)) : Nat))) ->
    Step_read (. z [(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.NEW_DATA x y)]) ((List.map (fun (c : lit_) => (const (Option.get! (cunpack zt)) (cunpacknum_ zt c))) c*) ++ [(.ARRAY.NEW_FIXED x (. n))])
  | array.get-null : forall (z : state) (ht : heaptype) (i : num_) (sx? : (Option sx)) (x : idx), 
    (wf_config (. z [(.REF.NULL ht), (.CONST .I32 i), (.ARRAY.GET (Option.map (fun (sx : sx) => sx) sx?) x)])) ->
    (wf_instr .TRAP) ->
    Step_read (. z [(.REF.NULL ht), (.CONST .I32 i), (.ARRAY.GET (Option.map (fun (sx : sx) => sx) sx?) x)]) [.TRAP]
  | array.get-oob : forall (z : state) (a : addr) (i : num_) (sx? : (Option sx)) (x : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.ARRAY.GET (Option.map (fun (sx : sx) => sx) sx?) x)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i) != none) ->
    (a < (List.length (arrayinst z))) ->
    ((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) >= (List.length (((arrayinst z)[a]!).FIELDS))) ->
    Step_read (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.ARRAY.GET (Option.map (fun (sx : sx) => sx) sx?) x)]) [.TRAP]
  | array.get-array : forall (z : state) (a : addr) (i : num_) (sx? : (Option sx)) (x : idx) (zt : storagetype) (mut? : (Option «mut»)), 
    ((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) < (List.length (((arrayinst z)[a]!).FIELDS))) ->
    (a < (List.length (arrayinst z))) ->
    ((proj_num__0 .I32 i) != none) ->
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.ARRAY.GET (Option.map (fun (sx : sx) => sx) sx?) x)])) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    (Expand (type z x) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    Step_read (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.ARRAY.GET (Option.map (fun (sx : sx) => sx) sx?) x)]) [(instr_val (unpackfield_ zt (Option.map (fun (sx : sx) => sx) sx?) ((((arrayinst z)[a]!).FIELDS)[(proj_uN_0 (Option.get! (proj_num__0 .I32 i)))]!)))]
  | array.len-null : forall (z : state) (ht : heaptype), 
    (wf_config (. z [(.REF.NULL ht), .ARRAY.LEN])) ->
    (wf_instr .TRAP) ->
    Step_read (. z [(.REF.NULL ht), .ARRAY.LEN]) [.TRAP]
  | array.len-array : forall (z : state) (a : addr), 
    (a < (List.length (arrayinst z))) ->
    (wf_config (. z [(.REF.ARRAY_ADDR a), .ARRAY.LEN])) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. (List.length (((arrayinst z)[a]!).FIELDS)))))) ->
    Step_read (. z [(.REF.ARRAY_ADDR a), .ARRAY.LEN]) [(.CONST .I32 (.mk_num__0 .I32 (. (List.length (((arrayinst z)[a]!).FIELDS)))))]
  | array.fill-null : forall (z : state) (ht : heaptype) (i : num_) (val : val) (n : n) (x : idx), 
    (wf_config (. z [(.REF.NULL ht), (.CONST .I32 i), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.FILL x)])) ->
    (wf_instr .TRAP) ->
    Step_read (. z [(.REF.NULL ht), (.CONST .I32 i), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.FILL x)]) [.TRAP]
  | array.fill-oob : forall (z : state) (a : addr) (i : num_) (val : val) (n : n) (x : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.FILL x)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i) != none) ->
    (a < (List.length (arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) + n) > (List.length (((arrayinst z)[a]!).FIELDS))) ->
    Step_read (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.FILL x)]) [.TRAP]
  | array.fill-zero : forall (z : state) (a : addr) (i : num_) (val : val) (n : n) (x : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.FILL x)])) ->
    (¬(Step_read_before_array.fill-zero (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.FILL x)]))) ->
    (n == 0) ->
    Step_read (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.FILL x)]) []
  | array.fill-succ : forall (z : state) (a : addr) (i : num_) (val : val) (n : n) (x : idx), 
    ((proj_num__0 .I32 i) != none) ->
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.FILL x)])) ->
    (wf_instr (.REF.ARRAY_ADDR a)) ->
    (wf_instr (.CONST .I32 i)) ->
    (wf_instr (.ARRAY.SET x)) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) + 1))))) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. (((n : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.ARRAY.FILL x)) ->
    (¬(Step_read_before_array.fill-succ (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.FILL x)]))) ->
    Step_read (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.FILL x)]) [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.ARRAY.SET x), (.REF.ARRAY_ADDR a), (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) + 1)))), (instr_val val), (.CONST .I32 (.mk_num__0 .I32 (. (((n : Nat) - (1 : Nat)) : Nat)))), (.ARRAY.FILL x)]
  | array.copy-null1 : forall (z : state) (ht_1 : heaptype) (i_1 : num_) (ref : ref) (i_2 : num_) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.REF.NULL ht_1), (.CONST .I32 i_1), (instr_ref ref), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    Step_read (. z [(.REF.NULL ht_1), (.CONST .I32 i_1), (instr_ref ref), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)]) [.TRAP]
  | array.copy-null2 : forall (z : state) (ref : ref) (i_1 : num_) (ht_2 : heaptype) (i_2 : num_) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(instr_ref ref), (.CONST .I32 i_1), (.REF.NULL ht_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    Step_read (. z [(instr_ref ref), (.CONST .I32 i_1), (.REF.NULL ht_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)]) [.TRAP]
  | array.copy-oob1 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i_1) != none) ->
    (a_1 < (List.length (arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i_1))) + n) > (List.length (((arrayinst z)[a_1]!).FIELDS))) ->
    Step_read (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)]) [.TRAP]
  | array.copy-oob2 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i_2) != none) ->
    (a_2 < (List.length (arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i_2))) + n) > (List.length (((arrayinst z)[a_2]!).FIELDS))) ->
    Step_read (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)]) [.TRAP]
  | array.copy-zero : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (n : n) (x_1 : idx) (x_2 : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])) ->
    (¬(Step_read_before_array.copy-zero (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)]))) ->
    (n == 0) ->
    Step_read (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)]) []
  | array.copy-le : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (n : n) (x_1 : idx) (x_2 : idx) (sx? : (Option sx)) (mut? : (Option «mut»)) (zt_2 : storagetype), 
    ((proj_num__0 .I32 i_1) != none) ->
    ((proj_num__0 .I32 i_2) != none) ->
    (wf_config (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])) ->
    (wf_instr (.REF.ARRAY_ADDR a_1)) ->
    (wf_instr (.CONST .I32 i_1)) ->
    (wf_instr (.REF.ARRAY_ADDR a_2)) ->
    (wf_instr (.CONST .I32 i_2)) ->
    (wf_instr (.ARRAY.GET (Option.map (fun (sx : sx) => sx) sx?) x_2)) ->
    (wf_instr (.ARRAY.SET x_1)) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 i_1))) + 1))))) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 i_2))) + 1))))) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. (((n : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.ARRAY.COPY x_1 x_2)) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt_2))) ->
    (¬(Step_read_before_array.copy-le (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)]))) ->
    (Expand (type z x_2) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt_2))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i_1))) <= (proj_uN_0 (Option.get! (proj_num__0 .I32 i_2)))) && ((Option.map (fun (sx : sx) => sx) sx?) == (sx zt_2))) ->
    Step_read (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)]) [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.ARRAY.GET (Option.map (fun (sx : sx) => sx) sx?) x_2), (.ARRAY.SET x_1), (.REF.ARRAY_ADDR a_1), (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 i_1))) + 1)))), (.REF.ARRAY_ADDR a_2), (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 i_2))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (. (((n : Nat) - (1 : Nat)) : Nat)))), (.ARRAY.COPY x_1 x_2)]
  | array.copy-gt : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (n : n) (x_1 : idx) (x_2 : idx) (sx? : (Option sx)) (mut? : (Option «mut»)) (zt_2 : storagetype), 
    ((proj_num__0 .I32 i_1) != none) ->
    ((proj_num__0 .I32 i_2) != none) ->
    (wf_config (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)])) ->
    (wf_instr (.REF.ARRAY_ADDR a_1)) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. (((((proj_uN_0 (Option.get! (proj_num__0 .I32 i_1))) + n) : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.REF.ARRAY_ADDR a_2)) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. (((((proj_uN_0 (Option.get! (proj_num__0 .I32 i_2))) + n) : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.ARRAY.GET (Option.map (fun (sx : sx) => sx) sx?) x_2)) ->
    (wf_instr (.ARRAY.SET x_1)) ->
    (wf_instr (.CONST .I32 i_1)) ->
    (wf_instr (.CONST .I32 i_2)) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. (((n : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.ARRAY.COPY x_1 x_2)) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt_2))) ->
    (¬(Step_read_before_array.copy-gt (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)]))) ->
    (Expand (type z x_2) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt_2))) ->
    ((Option.map (fun (sx : sx) => sx) sx?) == (sx zt_2)) ->
    Step_read (. z [(.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.COPY x_1 x_2)]) [(.REF.ARRAY_ADDR a_1), (.CONST .I32 (.mk_num__0 .I32 (. (((((proj_uN_0 (Option.get! (proj_num__0 .I32 i_1))) + n) : Nat) - (1 : Nat)) : Nat)))), (.REF.ARRAY_ADDR a_2), (.CONST .I32 (.mk_num__0 .I32 (. (((((proj_uN_0 (Option.get! (proj_num__0 .I32 i_2))) + n) : Nat) - (1 : Nat)) : Nat)))), (.ARRAY.GET (Option.map (fun (sx : sx) => sx) sx?) x_2), (.ARRAY.SET x_1), (.REF.ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF.ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (. (((n : Nat) - (1 : Nat)) : Nat)))), (.ARRAY.COPY x_1 x_2)]
  | array.init_elem-null : forall (z : state) (ht : heaptype) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.REF.NULL ht), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)])) ->
    (wf_instr .TRAP) ->
    Step_read (. z [(.REF.NULL ht), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)]) [.TRAP]
  | array.init_elem-oob1 : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i) != none) ->
    (a < (List.length (arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) + n) > (List.length (((arrayinst z)[a]!).FIELDS))) ->
    Step_read (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)]) [.TRAP]
  | array.init_elem-oob2 : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 j) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + n) > (List.length ((elem z y).REFS))) ->
    Step_read (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)]) [.TRAP]
  | array.init_elem-zero : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)])) ->
    (¬(Step_read_before_array.init_elem-zero (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)]))) ->
    (n == 0) ->
    Step_read (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)]) []
  | array.init_elem-succ : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx) (ref : ref), 
    ((proj_num__0 .I32 i) != none) ->
    ((proj_num__0 .I32 j) != none) ->
    (wf_ref ref) ->
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)])) ->
    (wf_instr (.REF.ARRAY_ADDR a)) ->
    (wf_instr (.CONST .I32 i)) ->
    (wf_instr (.ARRAY.SET x)) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) + 1))))) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + 1))))) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. (((n : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.ARRAY.INIT_ELEM x y)) ->
    (¬(Step_read_before_array.init_elem-succ (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)]))) ->
    ((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) < (List.length ((elem z y).REFS))) ->
    (ref == (((elem z y).REFS)[(proj_uN_0 (Option.get! (proj_num__0 .I32 j)))]!)) ->
    Step_read (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_ELEM x y)]) [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_ref ref), (.ARRAY.SET x), (.REF.ARRAY_ADDR a), (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (. (((n : Nat) - (1 : Nat)) : Nat)))), (.ARRAY.INIT_ELEM x y)]
  | array.init_data-null : forall (z : state) (ht : heaptype) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.REF.NULL ht), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)])) ->
    (wf_instr .TRAP) ->
    Step_read (. z [(.REF.NULL ht), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)]) [.TRAP]
  | array.init_data-oob1 : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)])) ->
    (wf_instr .TRAP) ->
    ((proj_num__0 .I32 i) != none) ->
    (a < (List.length (arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) + n) > (List.length (((arrayinst z)[a]!).FIELDS))) ->
    Step_read (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)]) [.TRAP]
  | array.init_data-oob2 : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx) (mut? : (Option «mut»)) (zt : storagetype), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)])) ->
    (wf_instr .TRAP) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    (Expand (type z x) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    ((proj_num__0 .I32 j) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + ((((n * (zsize zt)) : Nat) / (8 : Nat)) : Nat)) > (List.length ((data z y).BYTES))) ->
    Step_read (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)]) [.TRAP]
  | array.init_data-zero : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)])) ->
    (¬(Step_read_before_array.init_data-zero (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)]))) ->
    (n == 0) ->
    Step_read (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)]) []
  | array.init_data-num : forall (z : state) (a : addr) (i : num_) (j : num_) (n : n) (x : idx) (y : idx) (zt : storagetype) (c : lit_) (mut? : (Option «mut»)), 
    ((cunpack zt) != none) ->
    ((proj_num__0 .I32 i) != none) ->
    ((proj_num__0 .I32 j) != none) ->
    (wf_lit_ zt c) ->
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)])) ->
    (wf_instr (.REF.ARRAY_ADDR a)) ->
    (wf_instr (.CONST .I32 i)) ->
    (wf_instr (.ARRAY.SET x)) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) + 1))))) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + ((((zsize zt) : Nat) / (8 : Nat)) : Nat)))))) ->
    (wf_instr (.CONST .I32 (.mk_num__0 .I32 (. (((n : Nat) - (1 : Nat)) : Nat))))) ->
    (wf_instr (.ARRAY.INIT_DATA x y)) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    (¬(Step_read_before_array.init_data-num (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)]))) ->
    (Expand (type z x) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    ((zbytes_ zt c) == (List.extract ((data z y).BYTES) (proj_uN_0 (Option.get! (proj_num__0 .I32 j))) ((((zsize zt) : Nat) / (8 : Nat)) : Nat))) ->
    Step_read (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (. n))), (.ARRAY.INIT_DATA x y)]) [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (const (Option.get! (cunpack zt)) (cunpacknum_ zt c)), (.ARRAY.SET x), (.REF.ARRAY_ADDR a), (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (. ((proj_uN_0 (Option.get! (proj_num__0 .I32 j))) + ((((zsize zt) : Nat) / (8 : Nat)) : Nat))))), (.CONST .I32 (.mk_num__0 .I32 (. (((n : Nat) - (1 : Nat)) : Nat)))), (.ARRAY.INIT_DATA x y)]

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:5.1-5.88 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:5.1-5.88 -/
inductive Step : config -> config -> Prop where
  | pure : forall (z : state) (instr* : (List instr)) (instr'* : (List instr)), 
    (wf_config (. z (List.map (fun (instr : instr) => instr) instr*))) ->
    (wf_config (. z (List.map (fun (instr' : instr) => instr') instr'*))) ->
    (Step_pure (List.map (fun (instr : instr) => instr) instr*) (List.map (fun (instr' : instr) => instr') instr'*)) ->
    Step (. z (List.map (fun (instr : instr) => instr) instr*)) (. z (List.map (fun (instr' : instr) => instr') instr'*))
  | read : forall (z : state) (instr* : (List instr)) (instr'* : (List instr)), 
    (wf_config (. z (List.map (fun (instr : instr) => instr) instr*))) ->
    (wf_config (. z (List.map (fun (instr' : instr) => instr') instr'*))) ->
    (Step_read (. z (List.map (fun (instr : instr) => instr) instr*)) (List.map (fun (instr' : instr) => instr') instr'*)) ->
    Step (. z (List.map (fun (instr : instr) => instr) instr*)) (. z (List.map (fun (instr' : instr) => instr') instr'*))
  | ctxt-instrs : forall (z : state) (val* : (List val)) (instr* : (List instr)) (instr_1* : (List instr)) (z' : state) (instr'* : (List instr)), 
    (wf_config (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ ((List.map (fun (instr : instr) => instr) instr*) ++ (List.map (fun (instr_1 : instr) => instr_1) instr_1*))))) ->
    (wf_config (. z' ((List.map (fun (val : val) => (instr_val val)) val*) ++ ((List.map (fun (instr' : instr) => instr') instr'*) ++ (List.map (fun (instr_1 : instr) => instr_1) instr_1*))))) ->
    (wf_config (. z (List.map (fun (instr : instr) => instr) instr*))) ->
    (wf_config (. z' (List.map (fun (instr' : instr) => instr') instr'*))) ->
    (Step (. z (List.map (fun (instr : instr) => instr) instr*)) (. z' (List.map (fun (instr' : instr) => instr') instr'*))) ->
    (((List.map (fun (val : val) => val) val*) != []) || ((List.map (fun (instr_1 : instr) => instr_1) instr_1*) != [])) ->
    Step (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ ((List.map (fun (instr : instr) => instr) instr*) ++ (List.map (fun (instr_1 : instr) => instr_1) instr_1*)))) (. z' ((List.map (fun (val : val) => (instr_val val)) val*) ++ ((List.map (fun (instr' : instr) => instr') instr'*) ++ (List.map (fun (instr_1 : instr) => instr_1) instr_1*))))
  | ctxt-label : forall (z : state) (n : n) (instr_0* : (List instr)) (instr* : (List instr)) (z' : state) (instr'* : (List instr)), 
    (wf_config (. z [(.LABEL_ n (List.map (fun (instr_0 : instr) => instr_0) instr_0*) (List.map (fun (instr : instr) => instr) instr*))])) ->
    (wf_config (. z' [(.LABEL_ n (List.map (fun (instr_0 : instr) => instr_0) instr_0*) (List.map (fun (instr' : instr) => instr') instr'*))])) ->
    (wf_config (. z (List.map (fun (instr : instr) => instr) instr*))) ->
    (wf_config (. z' (List.map (fun (instr' : instr) => instr') instr'*))) ->
    (Step (. z (List.map (fun (instr : instr) => instr) instr*)) (. z' (List.map (fun (instr' : instr) => instr') instr'*))) ->
    Step (. z [(.LABEL_ n (List.map (fun (instr_0 : instr) => instr_0) instr_0*) (List.map (fun (instr : instr) => instr) instr*))]) (. z' [(.LABEL_ n (List.map (fun (instr_0 : instr) => instr_0) instr_0*) (List.map (fun (instr' : instr) => instr') instr'*))])
  | ctxt-frame : forall (s : store) (f : frame) (n : n) (f' : frame) (instr* : (List instr)) (s' : store) (f'' : frame) (instr'* : (List instr)), 
    (wf_config (. (. s f) [(.FRAME_ n f' (List.map (fun (instr : instr) => instr) instr*))])) ->
    (wf_config (. (. s' f) [(.FRAME_ n f'' (List.map (fun (instr' : instr) => instr') instr'*))])) ->
    (wf_config (. (. s f') (List.map (fun (instr : instr) => instr) instr*))) ->
    (wf_config (. (. s' f'') (List.map (fun (instr' : instr) => instr') instr'*))) ->
    (Step (. (. s f') (List.map (fun (instr : instr) => instr) instr*)) (. (. s' f'') (List.map (fun (instr' : instr) => instr') instr'*))) ->
    Step (. (. s f) [(.FRAME_ n f' (List.map (fun (instr : instr) => instr) instr*))]) (. (. s' f) [(.FRAME_ n f'' (List.map (fun (instr' : instr) => instr') instr'*))])
  | throw : forall (z : state) (val* : (List val)) (n : n) (x : idx) (exn : exninst) (a : addr) (t* : (List valtype)), 
    ((List.length val*) == n) ->
    (wf_config (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.THROW x)]))) ->
    (wf_config (. (add_exninst z [exn]) [(.REF.EXN_ADDR a), .THROW_REF])) ->
    ((List.length t*) == n) ->
    (wf_comptype (.FUNC (. (List.map (fun (t : valtype) => t) t*)) (. []))) ->
    ((proj_uN_0 x) < (List.length (tagaddr z))) ->
    (wf_exninst { TAG := ((tagaddr z)[(proj_uN_0 x)]!), FIELDS := (List.map (fun (val : val) => val) val*) }) ->
    (Expand (as_deftype ((tag z x).TYPE)) (.FUNC (. (List.map (fun (t : valtype) => t) t*)) (. []))) ->
    (a == (List.length (exninst z))) ->
    (exn == { TAG := ((tagaddr z)[(proj_uN_0 x)]!), FIELDS := (List.map (fun (val : val) => val) val*) }) ->
    Step (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.THROW x)])) (. (add_exninst z [exn]) [(.REF.EXN_ADDR a), .THROW_REF])
  | local.set : forall (z : state) (val : val) (x : idx), 
    (wf_config (. z [(instr_val val), (.LOCAL.SET x)])) ->
    (wf_config (. (with_local z x val) [])) ->
    Step (. z [(instr_val val), (.LOCAL.SET x)]) (. (with_local z x val) [])
  | global.set : forall (z : state) (val : val) (x : idx), 
    (wf_config (. z [(instr_val val), (.GLOBAL.SET x)])) ->
    (wf_config (. (with_global z x val) [])) ->
    Step (. z [(instr_val val), (.GLOBAL.SET x)]) (. (with_global z x val) [])
  | table.set-oob : forall (z : state) (at : addrtype) (i : num_) (ref : ref) (x : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (instr_ref ref), (.TABLE.SET x)])) ->
    (wf_config (. z [.TRAP])) ->
    ((proj_num__0 at i) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 at i))) >= (List.length ((table z x).REFS))) ->
    Step (. z [(.CONST (numtype_addrtype at) i), (instr_ref ref), (.TABLE.SET x)]) (. z [.TRAP])
  | table.set-val : forall (z : state) (at : addrtype) (i : num_) (ref : ref) (x : idx), 
    ((proj_num__0 at i) != none) ->
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (instr_ref ref), (.TABLE.SET x)])) ->
    (wf_config (. (with_table z x (proj_uN_0 (Option.get! (proj_num__0 at i))) ref) [])) ->
    ((proj_uN_0 (Option.get! (proj_num__0 at i))) < (List.length ((table z x).REFS))) ->
    Step (. z [(.CONST (numtype_addrtype at) i), (instr_ref ref), (.TABLE.SET x)]) (. (with_table z x (proj_uN_0 (Option.get! (proj_num__0 at i))) ref) [])
  | table.grow-succeed : forall (z : state) (ref : ref) (at : addrtype) (n : n) (x : idx) (ti : tableinst), 
    (wf_config (. z [(instr_ref ref), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.GROW x)])) ->
    (wf_config (. (with_tableinst z x ti) [(.CONST (numtype_addrtype at) (.mk_num__0 at (. (List.length ((table z x).REFS)))))])) ->
    ((growtable (table z x) n ref) != none) ->
    (ti == (Option.get! (growtable (table z x) n ref))) ->
    Step (. z [(instr_ref ref), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.GROW x)]) (. (with_tableinst z x ti) [(.CONST (numtype_addrtype at) (.mk_num__0 at (. (List.length ((table z x).REFS)))))])
  | table.grow-fail : forall (z : state) (ref : ref) (at : addrtype) (n : n) (x : idx), 
    (wf_config (. z [(instr_ref ref), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.GROW x)])) ->
    (wf_config (. z [(.CONST (numtype_addrtype at) (.mk_num__0 at (. (inv_signed_ (size (numtype_addrtype at)) (0 - (1 : Nat))))))])) ->
    Step (. z [(instr_ref ref), (.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.TABLE.GROW x)]) (. z [(.CONST (numtype_addrtype at) (.mk_num__0 at (. (inv_signed_ (size (numtype_addrtype at)) (0 - (1 : Nat))))))])
  | elem.drop : forall (z : state) (x : idx), 
    (wf_config (. z [(.ELEM.DROP x)])) ->
    (wf_config (. (with_elem z x []) [])) ->
    Step (. z [(.ELEM.DROP x)]) (. (with_elem z x []) [])
  | store-num-oob : forall (z : state) (at : addrtype) (i : num_) (nt : numtype) (c : num_) (x : idx) (ao : memarg), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.CONST nt c), (.STORE nt none x ao)])) ->
    (wf_config (. z [.TRAP])) ->
    ((proj_num__0 at i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) + ((((size nt) : Nat) / (8 : Nat)) : Nat)) > (List.length ((mem z x).BYTES))) ->
    Step (. z [(.CONST (numtype_addrtype at) i), (.CONST nt c), (.STORE nt none x ao)]) (. z [.TRAP])
  | store-num-val : forall (z : state) (at : addrtype) (i : num_) (nt : numtype) (c : num_) (x : idx) (ao : memarg) (b* : (List byte)), 
    ((proj_num__0 at i) != none) ->
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.CONST nt c), (.STORE nt none x ao)])) ->
    (wf_config (. (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) ((((size nt) : Nat) / (8 : Nat)) : Nat) (List.map (fun (b : byte) => b) b*)) [])) ->
    ((List.map (fun (b : byte) => b) b*) == (nbytes_ nt c)) ->
    Step (. z [(.CONST (numtype_addrtype at) i), (.CONST nt c), (.STORE nt none x ao)]) (. (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) ((((size nt) : Nat) / (8 : Nat)) : Nat) (List.map (fun (b : byte) => b) b*)) [])
  | store-pack-oob : forall (z : state) (at : addrtype) (i : num_) (Inn : Inn) (c : num_) (n : n) (x : idx) (ao : memarg), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.CONST (numtype_addrtype Inn) c), (.STORE (numtype_addrtype Inn) (some (.mk_storeop__0 Inn (. (. n)))) x ao)])) ->
    (wf_config (. z [.TRAP])) ->
    ((proj_num__0 at i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) + (((n : Nat) / (8 : Nat)) : Nat)) > (List.length ((mem z x).BYTES))) ->
    Step (. z [(.CONST (numtype_addrtype at) i), (.CONST (numtype_addrtype Inn) c), (.STORE (numtype_addrtype Inn) (some (.mk_storeop__0 Inn (. (. n)))) x ao)]) (. z [.TRAP])
  | store-pack-val : forall (z : state) (at : addrtype) (i : num_) (Inn : Inn) (c : num_) (n : n) (x : idx) (ao : memarg) (b* : (List byte)), 
    ((proj_num__0 at i) != none) ->
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.CONST (numtype_addrtype Inn) c), (.STORE (numtype_addrtype Inn) (some (.mk_storeop__0 Inn (. (. n)))) x ao)])) ->
    (wf_config (. (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) (((n : Nat) / (8 : Nat)) : Nat) (List.map (fun (b : byte) => b) b*)) [])) ->
    ((proj_num__0 Inn c) != none) ->
    ((List.map (fun (b : byte) => b) b*) == (ibytes_ n (wrap__ (size (numtype_addrtype Inn)) n (Option.get! (proj_num__0 Inn c))))) ->
    Step (. z [(.CONST (numtype_addrtype at) i), (.CONST (numtype_addrtype Inn) c), (.STORE (numtype_addrtype Inn) (some (.mk_storeop__0 Inn (. (. n)))) x ao)]) (. (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) (((n : Nat) / (8 : Nat)) : Nat) (List.map (fun (b : byte) => b) b*)) [])
  | vstore-oob : forall (z : state) (at : addrtype) (i : num_) (c : vec_) (x : idx) (ao : memarg), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.VCONST .V128 c), (.VSTORE .V128 x ao)])) ->
    (wf_config (. z [.TRAP])) ->
    ((proj_num__0 at i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) + ((((vsize .V128) : Nat) / (8 : Nat)) : Nat)) > (List.length ((mem z x).BYTES))) ->
    Step (. z [(.CONST (numtype_addrtype at) i), (.VCONST .V128 c), (.VSTORE .V128 x ao)]) (. z [.TRAP])
  | vstore-val : forall (z : state) (at : addrtype) (i : num_) (c : vec_) (x : idx) (ao : memarg) (b* : (List byte)), 
    ((proj_num__0 at i) != none) ->
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.VCONST .V128 c), (.VSTORE .V128 x ao)])) ->
    (wf_config (. (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) ((((vsize .V128) : Nat) / (8 : Nat)) : Nat) (List.map (fun (b : byte) => b) b*)) [])) ->
    ((List.map (fun (b : byte) => b) b*) == (vbytes_ .V128 c)) ->
    Step (. z [(.CONST (numtype_addrtype at) i), (.VCONST .V128 c), (.VSTORE .V128 x ao)]) (. (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) ((((vsize .V128) : Nat) / (8 : Nat)) : Nat) (List.map (fun (b : byte) => b) b*)) [])
  | vstore_lane-oob : forall (z : state) (at : addrtype) (i : num_) (c : vec_) (N : N) (x : idx) (ao : memarg) (j : laneidx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.VCONST .V128 c), (.VSTORE_LANE .V128 (. N) x ao j)])) ->
    (wf_config (. z [.TRAP])) ->
    ((proj_num__0 at i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) + N) > (List.length ((mem z x).BYTES))) ->
    Step (. z [(.CONST (numtype_addrtype at) i), (.VCONST .V128 c), (.VSTORE_LANE .V128 (. N) x ao j)]) (. z [.TRAP])
  | vstore_lane-val : forall (z : state) (at : addrtype) (i : num_) (c : vec_) (N : N) (x : idx) (ao : memarg) (j : laneidx) (b* : (List byte)) (Jnn : Jnn) (M : M), 
    ((proj_num__0 at i) != none) ->
    (wf_config (. z [(.CONST (numtype_addrtype at) i), (.VCONST .V128 c), (.VSTORE_LANE .V128 (. N) x ao j)])) ->
    (wf_config (. (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) (((N : Nat) / (8 : Nat)) : Nat) (List.map (fun (b : byte) => b) b*)) [])) ->
    ((proj_lane__2 Jnn ((lanes_ (.X (lanetype_Jnn Jnn) (. M)) c)[(proj_uN_0 j)]!)) != none) ->
    ((proj_uN_0 j) < (List.length (lanes_ (.X (lanetype_Jnn Jnn) (. M)) c))) ->
    (wf_uN N (. (proj_uN_0 (Option.get! (proj_lane__2 Jnn ((lanes_ (.X (lanetype_Jnn Jnn) (. M)) c)[(proj_uN_0 j)]!)))))) ->
    (N == (jsize Jnn)) ->
    ((M : Nat) == ((128 : Nat) / (N : Nat))) ->
    ((List.map (fun (b : byte) => b) b*) == (ibytes_ N (. (proj_uN_0 (Option.get! (proj_lane__2 Jnn ((lanes_ (.X (lanetype_Jnn Jnn) (. M)) c)[(proj_uN_0 j)]!))))))) ->
    Step (. z [(.CONST (numtype_addrtype at) i), (.VCONST .V128 c), (.VSTORE_LANE .V128 (. N) x ao j)]) (. (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 at i))) + (proj_uN_0 (ao.OFFSET))) (((N : Nat) / (8 : Nat)) : Nat) (List.map (fun (b : byte) => b) b*)) [])
  | memory.grow-succeed : forall (z : state) (at : addrtype) (n : n) (x : idx) (mi : meminst), 
    (wf_config (. z [(.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.GROW x)])) ->
    (wf_config (. (with_meminst z x mi) [(.CONST (numtype_addrtype at) (.mk_num__0 at (. ((((List.length ((mem z x).BYTES)) : Nat) / ((64 * (Ki )) : Nat)) : Nat))))])) ->
    ((growmem (mem z x) n) != none) ->
    (mi == (Option.get! (growmem (mem z x) n))) ->
    Step (. z [(.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.GROW x)]) (. (with_meminst z x mi) [(.CONST (numtype_addrtype at) (.mk_num__0 at (. ((((List.length ((mem z x).BYTES)) : Nat) / ((64 * (Ki )) : Nat)) : Nat))))])
  | memory.grow-fail : forall (z : state) (at : addrtype) (n : n) (x : idx), 
    (wf_config (. z [(.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.GROW x)])) ->
    (wf_config (. z [(.CONST (numtype_addrtype at) (.mk_num__0 at (. (inv_signed_ (size (numtype_addrtype at)) (0 - (1 : Nat))))))])) ->
    Step (. z [(.CONST (numtype_addrtype at) (.mk_num__0 at (. n))), (.MEMORY.GROW x)]) (. z [(.CONST (numtype_addrtype at) (.mk_num__0 at (. (inv_signed_ (size (numtype_addrtype at)) (0 - (1 : Nat))))))])
  | data.drop : forall (z : state) (x : idx), 
    (wf_config (. z [(.DATA.DROP x)])) ->
    (wf_config (. (with_data z x []) [])) ->
    Step (. z [(.DATA.DROP x)]) (. (with_data z x []) [])
  | struct.new : forall (z : state) (val* : (List val)) (n : n) (x : idx) (si : structinst) (a : addr) (mut?* : (List (Option «mut»))) (zt* : (List storagetype)), 
    ((List.length val*) == n) ->
    (wf_config (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.STRUCT.NEW x)]))) ->
    (wf_config (. (add_structinst z [si]) [(.REF.STRUCT_ADDR a)])) ->
    ((List.length mut?*) == n) ->
    ((List.length zt*) == n) ->
    (wf_comptype (.STRUCT (. (List.zipWith (fun (mut? : (Option «mut»)) (zt : storagetype) => (. (Option.map (fun (mut : «mut») => «mut») mut?) zt)) mut?* zt*)))) ->
    (wf_structinst { TYPE := (type z x), FIELDS := (List.zipWith (fun (val : val) (zt : storagetype) => (packfield_ zt val)) val* zt*) }) ->
    (Expand (type z x) (.STRUCT (. (List.zipWith (fun (mut? : (Option «mut»)) (zt : storagetype) => (. (Option.map (fun (mut : «mut») => «mut») mut?) zt)) mut?* zt*)))) ->
    (a == (List.length (structinst z))) ->
    (si == { TYPE := (type z x), FIELDS := (List.zipWith (fun (val : val) (zt : storagetype) => (packfield_ zt val)) val* zt*) }) ->
    Step (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.STRUCT.NEW x)])) (. (add_structinst z [si]) [(.REF.STRUCT_ADDR a)])
  | struct.set-null : forall (z : state) (ht : heaptype) (val : val) (x : idx) (i : u32), 
    (wf_config (. z [(.REF.NULL ht), (instr_val val), (.STRUCT.SET x i)])) ->
    (wf_config (. z [.TRAP])) ->
    Step (. z [(.REF.NULL ht), (instr_val val), (.STRUCT.SET x i)]) (. z [.TRAP])
  | struct.set-struct : forall (z : state) (a : addr) (val : val) (x : idx) (i : u32) (zt* : (List storagetype)) (mut?* : (List (Option «mut»))), 
    ((proj_uN_0 i) < (List.length (List.map (fun (zt : storagetype) => zt) zt*))) ->
    (wf_config (. z [(.REF.STRUCT_ADDR a), (instr_val val), (.STRUCT.SET x i)])) ->
    (wf_config (. (with_struct z a (proj_uN_0 i) (packfield_ ((List.map (fun (zt : storagetype) => zt) zt*)[(proj_uN_0 i)]!) val)) [])) ->
    ((List.length mut?*) == (List.length zt*)) ->
    (wf_comptype (.STRUCT (. (List.zipWith (fun (mut? : (Option «mut»)) (zt : storagetype) => (. (Option.map (fun (mut : «mut») => «mut») mut?) zt)) mut?* zt*)))) ->
    (Expand (type z x) (.STRUCT (. (List.zipWith (fun (mut? : (Option «mut»)) (zt : storagetype) => (. (Option.map (fun (mut : «mut») => «mut») mut?) zt)) mut?* zt*)))) ->
    Step (. z [(.REF.STRUCT_ADDR a), (instr_val val), (.STRUCT.SET x i)]) (. (with_struct z a (proj_uN_0 i) (packfield_ ((List.map (fun (zt : storagetype) => zt) zt*)[(proj_uN_0 i)]!) val)) [])
  | array.new_fixed : forall (z : state) (val* : (List val)) (n : n) (x : idx) (ai : arrayinst) (a : addr) (mut? : (Option «mut»)) (zt : storagetype), 
    ((List.length val*) == n) ->
    (wf_config (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.ARRAY.NEW_FIXED x (. n))]))) ->
    (wf_config (. (add_arrayinst z [ai]) [(.REF.ARRAY_ADDR a)])) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    (wf_arrayinst { TYPE := (type z x), FIELDS := (List.map (fun (val : val) => (packfield_ zt val)) val*) }) ->
    (Expand (type z x) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    ((a == (List.length (arrayinst z))) && (ai == { TYPE := (type z x), FIELDS := (List.map (fun (val : val) => (packfield_ zt val)) val*) })) ->
    Step (. z ((List.map (fun (val : val) => (instr_val val)) val*) ++ [(.ARRAY.NEW_FIXED x (. n))])) (. (add_arrayinst z [ai]) [(.REF.ARRAY_ADDR a)])
  | array.set-null : forall (z : state) (ht : heaptype) (i : num_) (val : val) (x : idx), 
    (wf_config (. z [(.REF.NULL ht), (.CONST .I32 i), (instr_val val), (.ARRAY.SET x)])) ->
    (wf_config (. z [.TRAP])) ->
    Step (. z [(.REF.NULL ht), (.CONST .I32 i), (instr_val val), (.ARRAY.SET x)]) (. z [.TRAP])
  | array.set-oob : forall (z : state) (a : addr) (i : num_) (val : val) (x : idx), 
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.ARRAY.SET x)])) ->
    (wf_config (. z [.TRAP])) ->
    ((proj_num__0 .I32 i) != none) ->
    (a < (List.length (arrayinst z))) ->
    ((proj_uN_0 (Option.get! (proj_num__0 .I32 i))) >= (List.length (((arrayinst z)[a]!).FIELDS))) ->
    Step (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.ARRAY.SET x)]) (. z [.TRAP])
  | array.set-array : forall (z : state) (a : addr) (i : num_) (val : val) (x : idx) (zt : storagetype) (mut? : (Option «mut»)), 
    ((proj_num__0 .I32 i) != none) ->
    (wf_config (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.ARRAY.SET x)])) ->
    (wf_config (. (with_array z a (proj_uN_0 (Option.get! (proj_num__0 .I32 i))) (packfield_ zt val)) [])) ->
    (wf_comptype (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    (Expand (type z x) (.ARRAY (. (Option.map (fun (mut : «mut») => «mut») mut?) zt))) ->
    Step (. z [(.REF.ARRAY_ADDR a), (.CONST .I32 i), (instr_val val), (.ARRAY.SET x)]) (. (with_array z a (proj_uN_0 (Option.get! (proj_num__0 .I32 i))) (packfield_ zt val)) [])

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:8.1-8.92 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:8.1-8.92 -/
inductive Steps : config -> config -> Prop where
  | refl : forall (z : state) (instr* : (List instr)), 
    (wf_config (. z (List.map (fun (instr : instr) => instr) instr*))) ->
    Steps (. z (List.map (fun (instr : instr) => instr) instr*)) (. z (List.map (fun (instr : instr) => instr) instr*))
  | trans : forall (z : state) (instr* : (List instr)) (z'' : state) (instr''* : (List instr)) (z' : state) (instr'* : (List instr)), 
    (wf_config (. z (List.map (fun (instr : instr) => instr) instr*))) ->
    (wf_config (. z'' (List.map (fun (instr'' : instr) => instr'') instr''*))) ->
    (wf_config (. z' (List.map (fun (instr' : instr) => instr') instr'*))) ->
    (Step (. z (List.map (fun (instr : instr) => instr) instr*)) (. z' (List.map (fun (instr' : instr) => instr') instr'*))) ->
    (Steps (. z' (List.map (fun (instr' : instr) => instr') instr'*)) (. z'' (List.map (fun (instr'' : instr) => instr'') instr''*))) ->
    Steps (. z (List.map (fun (instr : instr) => instr) instr*)) (. z'' (List.map (fun (instr'' : instr) => instr'') instr''*))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:1103.1-1103.108 -/
inductive Eval_expr : state -> expr -> state -> (List val) -> Prop where
  |  : forall (z : state) (instr* : (List instr)) (z' : state) (val* : (List val)), 
    (wf_config (. z (List.map (fun (instr : instr) => instr) instr*))) ->
    (wf_config (. z' (List.map (fun (val : val) => (instr_val val)) val*))) ->
    (Steps (. z (List.map (fun (instr : instr) => instr) instr*)) (. z' (List.map (fun (val : val) => (instr_val val)) val*))) ->
    Eval_expr z (List.map (fun (instr : instr) => instr) instr*) z' (List.map (fun (val : val) => val) val*)

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:7.1-7.63 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:7.1-7.63 -/
opaque alloctypes : forall (_ : (List type)), (List deftype) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:15.1-15.49 -/
opaque alloctag : forall (store : store) (tagtype : tagtype), store × tagaddr := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:20.1-20.102 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:20.1-20.102 -/
opaque alloctags : forall (store : store) (_ : (List tagtype)), store × (List tagaddr) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:26.1-26.63 -/
opaque allocglobal : forall (store : store) (globaltype : globaltype) (val : val), store × globaladdr := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:31.1-31.122 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:31.1-31.122 -/
opaque allocglobals : forall (store : store) (_ : (List globaltype)) (_ : (List val)), store × (List globaladdr) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:37.1-37.49 -/
opaque allocmem : forall (store : store) (memtype : memtype), store × memaddr := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:42.1-42.102 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:42.1-42.102 -/
opaque allocmems : forall (store : store) (_ : (List memtype)), store × (List memaddr) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:48.1-48.60 -/
opaque alloctable : forall (store : store) (tabletype : tabletype) (ref : ref), store × tableaddr := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:53.1-53.118 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:53.1-53.118 -/
opaque alloctables : forall (store : store) (_ : (List tabletype)) (_ : (List ref)), store × (List tableaddr) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:59.1-59.73 -/
opaque allocfunc : forall (store : store) (deftype : deftype) (funccode : funccode) (moduleinst : moduleinst), store × funcaddr := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:64.1-64.133 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:64.1-64.133 -/
opaque allocfuncs : forall (store : store) (_ : (List deftype)) (_ : (List funccode)) (_ : (List moduleinst)), store × (List funcaddr) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:70.1-70.59 -/
opaque allocdata : forall (store : store) (datatype : datatype) (_ : (List byte)), store × dataaddr := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:75.1-75.118 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:75.1-75.118 -/
opaque allocdatas : forall (store : store) (_ : (List datatype)) (_ : (List (List byte))), store × (List dataaddr) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:81.1-81.58 -/
opaque allocelem : forall (store : store) (elemtype : elemtype) (_ : (List ref)), store × elemaddr := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:86.1-86.117 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:86.1-86.117 -/
opaque allocelems : forall (store : store) (_ : (List elemtype)) (_ : (List (List ref))), store × (List elemaddr) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:92.1-92.90 -/
opaque allocexport : forall (moduleinst : moduleinst) (export : «export»), exportinst := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:99.1-99.104 -/
opaque allocexports : forall (moduleinst : moduleinst) (_ : (List «export»)), (List exportinst) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:103.1-103.88 -/
opaque allocmodule : forall (store : store) (module : module) (_ : (List externaddr)) (_ : (List val)) (_ : (List ref)) (_ : (List (List ref))), store × moduleinst := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:148.1-148.38 -/
opaque rundata_ : forall (dataidx : dataidx) (data : data), (List instr) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:153.1-153.38 -/
opaque runelem_ : forall (elemidx : elemidx) (elem : elem), (List instr) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:160.1-160.94 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:160.1-160.94 -/
opaque evalglobals : forall (state : state) (_ : (List globaltype)) (_ : (List expr)), state × (List val) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:169.1-169.54 -/
opaque instantiate : forall (store : store) (module : module) (_ : (List externaddr)), config := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:199.1-199.44 -/
opaque invoke : forall (store : store) (funcaddr : funcaddr) (_ : (List val)), config := opaqueDef

/- Type Alias Definition at: ../../../../specification/wasm-3.0/5.3-binary.instructions.spectec:82.1-82.35 -/
abbrev memidxop : Type := memidx × memarg

/- Type Alias Definition at: ../../../../specification/wasm-3.0/5.3-binary.instructions.spectec:123.1-123.31 -/
abbrev castop : Type := (Option null) × (Option null)

/- Type Alias Definition at: ../../../../specification/wasm-3.0/5.4-binary.modules.spectec:89.1-89.43 -/
abbrev startopt : Type := (List start)

/- Type Alias Definition at: ../../../../specification/wasm-3.0/5.4-binary.modules.spectec:124.1-124.46 -/
abbrev code : Type := (List «local») × expr

/- Type Alias Definition at: ../../../../specification/wasm-3.0/5.4-binary.modules.spectec:156.1-156.33 -/
abbrev nopt : Type := (List u32)
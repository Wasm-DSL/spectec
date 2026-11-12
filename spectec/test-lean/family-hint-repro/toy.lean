def List.ap (fs : List (α → β)) (xs : List α) : List β :=
  List.zipWith ((· ·)) fs xs

def Option.ap (f : Option (α → β)) (x : Option α) : Option β :=
  f.bind (fun f => x.map f)

opaque rat_to_nat (r : Rat) : Nat := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Inductive Type Definition at: test-lean/family-hint-repro/toy.spectec:5.1-5.39 -/
inductive numtype : Type where
  | I32 : numtype
  | I64 : numtype
  | F32 : numtype
  | F64 : numtype
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

/- Inductive Type Definition at: test-lean/family-hint-repro/toy.spectec:6.1-6.22 -/
inductive vectype : Type where
  | V128 : vectype
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

/- Inductive Type Definition at: test-lean/family-hint-repro/toy.spectec:8.1-8.23 -/
inductive Inn : Type where
  | I32 : Inn
  | I64 : Inn
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

/- Auxiliary Definition at:  -/
def numtype_Inn (var_0 : Inn) : numtype :=
  match var_0 with
  | Inn.I32 => numtype.I32
  | Inn.I64 => numtype.I64

/- Inductive Type Definition at: test-lean/family-hint-repro/toy.spectec:9.1-9.23 -/
inductive Fnn : Type where
  | F32 : Fnn
  | F64 : Fnn
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

/- Auxiliary Definition at:  -/
def numtype_Fnn (var_0 : Fnn) : numtype :=
  match var_0 with
  | Fnn.F32 => numtype.F32
  | Fnn.F64 => numtype.F64

/- Inductive Type Definition at: test-lean/family-hint-repro/toy.spectec:10.1-10.18 -/
inductive Vnn : Type where
  | V128 : Vnn
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

/- Inductive Type Definition at: test-lean/family-hint-repro/toy.spectec:12.1-12.21 -/
inductive num_ : Type where
  | mk_num__0 (v_Inn : Inn) (var_x : Nat) : num_
  | mk_num__1 (v_Fnn : Fnn) (var_x : Nat) : num_
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

/- Inductive Relations Definition at: test-lean/family-hint-repro/toy.spectec:12.8-12.13 -/
inductive wf_num_ : numtype → num_ → Prop where
  | num__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : Nat) :
    v_numtype = (numtype_Inn v_Inn) →
    wf_num_ v_numtype (num_.mk_num__0 v_Inn var_x)
  | num__case_1 (v_numtype : numtype) (v_Fnn : Fnn) (var_x : Nat) :
    v_numtype = (numtype_Fnn v_Fnn) →
    wf_num_ v_numtype (num_.mk_num__1 v_Fnn var_x)


/- Auxiliary Definition at: test-lean/family-hint-repro/toy.spectec:12.1-12.21 -/
def proj_num__0 (var_x : num_) : Option Nat :=
  match var_x with
  | num_.mk_num__0 v_Inn var_x => some var_x
  | _ => none

/- Auxiliary Definition at: test-lean/family-hint-repro/toy.spectec:12.1-12.21 -/
def proj_num__1 (var_x : num_) : Option Nat :=
  match var_x with
  | num_.mk_num__1 v_Fnn var_x => some var_x
  | _ => none

/- Type Alias Definition at: test-lean/family-hint-repro/toy.spectec:16.1-16.27 -/
abbrev vec_ : Type := Nat

/- Auxiliary Definition at: test-lean/family-hint-repro/toy.spectec:18.1-18.55 -/
def foo (v_numtype : numtype) (v_num_ : num_) : Option (List Nat) :=
  none

/- Axiom Definition at: test-lean/family-hint-repro/toy.spectec:19.1-19.55 -/
opaque bar (v_vectype : vectype) (v_vec_ : vec_) : List Nat := by
  first
     | exact Inhabited.default
     | intros ; assumption

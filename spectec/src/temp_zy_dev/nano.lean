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

/- Type Alias Definition at: doc/example/NanoWasm.spectec:7.1-7.22 -/
abbrev localidx : Type := Nat

/- Type Alias Definition at: doc/example/NanoWasm.spectec:8.1-8.23 -/
abbrev globalidx : Type := Nat

/- Inductive Type Definition at: doc/example/NanoWasm.spectec:10.1-10.17 -/
inductive «mut» : Type where
  | MUT : «mut»
deriving Inhabited, BEq


/- Inductive Type Definition at: doc/example/NanoWasm.spectec:11.1-11.39 -/
inductive valtype : Type where
  | I32 : valtype
  | I64 : valtype
  | F32 : valtype
  | F64 : valtype
deriving Inhabited, BEq


/- Inductive Type Definition at: doc/example/NanoWasm.spectec:12.1-12.39 -/
inductive functype : Type where
  | mk_functype (valtype_lst : (List valtype)) (_ : (List valtype)) : functype
deriving Inhabited, BEq


/- Inductive Type Definition at: doc/example/NanoWasm.spectec:13.1-13.33 -/
inductive globaltype : Type where
  | mk_globaltype (mut_opt : (Option «mut»)) (v_valtype : valtype) : globaltype
deriving Inhabited, BEq


/- Type Alias Definition at: doc/example/NanoWasm.spectec:15.1-15.19 -/
abbrev const : Type := Nat

/- Inductive Type Definition at: doc/example/NanoWasm.spectec:17.1-25.27 -/
inductive instr : Type where
  | NOP : instr
  | DROP : instr
  | SELECT : instr
  | CONST (v_valtype : valtype) (v_const : const) : instr
  | LOCAL_GET (v_localidx : localidx) : instr
  | LOCAL_SET (v_localidx : localidx) : instr
  | GLOBAL_GET (v_globalidx : globalidx) : instr
  | GLOBAL_SET (v_globalidx : globalidx) : instr
deriving Inhabited, BEq


/- Record Creation Definition at: doc/example/NanoWasm.spectec:30.1-30.58 -/
structure context where MKcontext ::
  GLOBALS : (List globaltype)
  LOCALS : (List valtype)
deriving Inhabited, BEq

def _append_context (arg1 arg2 : (context)) : context where
  GLOBALS := arg1.GLOBALS ++ arg2.GLOBALS
  LOCALS := arg1.LOCALS ++ arg2.LOCALS
instance : Append context where
  append arg1 arg2 := _append_context arg1 arg2



/- Inductive Relations Definition at: doc/example/NanoWasm.spectec:35.1-35.47 -/
inductive Instr_ok : context -> instr -> functype -> Prop where
  | nop : forall (C : context), Instr_ok C .NOP (.mk_functype [] [])
  | drop : forall (C : context) (t : valtype), Instr_ok C .DROP (.mk_functype [t] [])
  | select : forall (C : context) (t : valtype), Instr_ok C .SELECT (.mk_functype [t, t, .I32] [t])
  | const : forall (C : context) (t : valtype) (c : const), Instr_ok C (.CONST t c) (.mk_functype [] [t])
  | local_get : forall (C : context) (x : localidx) (t : valtype),
    (x < (List.length (C.LOCALS))) ->
    (((C.LOCALS)[x]!) == t) ->
    Instr_ok C (.LOCAL_GET x) (.mk_functype [] [t])
  | local_set : forall (C : context) (x : localidx) (t : valtype),
    (x < (List.length (C.LOCALS))) ->
    (((C.LOCALS)[x]!) == t) ->
    Instr_ok C (.LOCAL_SET x) (.mk_functype [t] [])
  | global_get : forall (C : context) (x : globalidx) (t : valtype),
    (x < (List.length (C.GLOBALS))) ->
    (((C.GLOBALS)[x]!) == (.mk_globaltype (some .MUT) t)) ->
    Instr_ok C (.GLOBAL_GET x) (.mk_functype [] [t])
  | global_set : forall (C : context) (x : globalidx) (t : valtype),
    (x < (List.length (C.GLOBALS))) ->
    (((C.GLOBALS)[x]!) == (.mk_globaltype (some .MUT) t)) ->
    Instr_ok C (.GLOBAL_GET x) (.mk_functype [t] [])

/- Type Alias Definition at: doc/example/NanoWasm.spectec:68.1-68.18 -/
abbrev addr : Type := Nat

/- Record Creation Definition at: doc/example/NanoWasm.spectec:69.1-69.38 -/
structure moduleinst where MKmoduleinst ::
  GLOBALS : (List addr)
deriving Inhabited, BEq

def _append_moduleinst (arg1 arg2 : (moduleinst)) : moduleinst where
  GLOBALS := arg1.GLOBALS ++ arg2.GLOBALS
instance : Append moduleinst where
  append arg1 arg2 := _append_moduleinst arg1 arg2



/- Inductive Type Definition at: doc/example/NanoWasm.spectec:71.1-71.33 -/
inductive val : Type where
  | CONST (v_valtype : valtype) (v_const : const) : val
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def instr_val : ∀  (var_0 : val) , instr
  | (.CONST x0 x1) =>
    (.CONST x0 x1)


/- Record Creation Definition at: doc/example/NanoWasm.spectec:73.1-73.32 -/
structure store where MKstore ::
  GLOBALS : (List val)
deriving Inhabited, BEq

def _append_store (arg1 arg2 : (store)) : store where
  GLOBALS := arg1.GLOBALS ++ arg2.GLOBALS
instance : Append store where
  append arg1 arg2 := _append_store arg1 arg2



/- Record Creation Definition at: doc/example/NanoWasm.spectec:74.1-74.50 -/
structure frame where MKframe ::
  LOCALS : (List val)
  MODULE : moduleinst
deriving Inhabited, BEq

def _append_frame (arg1 arg2 : (frame)) : frame where
  LOCALS := arg1.LOCALS ++ arg2.LOCALS
  MODULE := arg1.MODULE ++ arg2.MODULE
instance : Append frame where
  append arg1 arg2 := _append_frame arg1 arg2



/- Inductive Type Definition at: doc/example/NanoWasm.spectec:75.1-75.28 -/
inductive state : Type where
  | mk_state (v_store : store) (v_frame : frame) : state
deriving Inhabited, BEq


/- Inductive Type Definition at: doc/example/NanoWasm.spectec:76.1-76.30 -/
inductive config : Type where
  | mk_config (v_state : state) (instr_lst : (List instr)) : config
deriving Inhabited, BEq


/- Auxiliary Definition at: doc/example/NanoWasm.spectec:82.1-82.34 -/
def «local» : ∀  (v_state : state) (v_localidx : localidx) , val
  | (.mk_state s f), x =>
    ((f.LOCALS)[x]!)


/- Auxiliary Definition at: doc/example/NanoWasm.spectec:85.1-85.36 -/
def global : ∀  (v_state : state) (v_globalidx : globalidx) , val
  | (.mk_state s f), x =>
    ((s.GLOBALS)[(((f.MODULE).GLOBALS)[x]!)]!)


/- Auxiliary Definition at: doc/example/NanoWasm.spectec:88.1-88.48 -/
def update_local : ∀  (v_state : state) (v_localidx : localidx) (v_val : val) , state
  | (.mk_state s f), x, v =>
    (.mk_state s (f <| LOCALS := (List.modify (f.LOCALS) x (fun (_ : val) => v)) |>))


/- Auxiliary Definition at: doc/example/NanoWasm.spectec:91.1-91.50 -/
def update_global : ∀  (v_state : state) (v_globalidx : globalidx) (v_val : val) , state
  | (.mk_state s f), x, v =>
    (.mk_state (s <| GLOBALS := (List.modify (s.GLOBALS) (((f.MODULE).GLOBALS)[x]!) (fun (_ : val) => v)) |>) f)


/- Inductive Relations Definition at: doc/example/NanoWasm.spectec:96.1-96.37 -/
inductive Step_pure : (List instr) -> (List instr) -> Prop where
  | nop : Step_pure [.NOP] []
  | drop : forall (v_val : val), Step_pure [(instr_val v_val), .DROP] []
  | select_true : forall (val_1 : val) (val_2 : val) (c : const),
    (c != 0) ->
    Step_pure [(instr_val val_1), (instr_val val_2), (.CONST .I32 c), .SELECT] [(instr_val val_1)]
  | select_false : forall (val_1 : val) (val_2 : val) (c : const),
    (c == 0) ->
    Step_pure [(instr_val val_1), (instr_val val_2), (.CONST .I32 c), .SELECT] [(instr_val val_2)]

/- Inductive Relations Definition at: doc/example/NanoWasm.spectec:95.1-95.32 -/
inductive Step : config -> config -> Prop where
  | pure : forall (z : state) (instr_lst : (List instr)) (instr'_lst : (List instr)),
    (Step_pure instr_lst instr'_lst) ->
    Step (.mk_config z instr_lst) (.mk_config z instr'_lst)
  | local_get : forall (z : state) (x : localidx) (v_val : val),
    (v_val == («local» z x)) ->
    Step (.mk_config z [(.LOCAL_GET x)]) (.mk_config z [(instr_val v_val)])
  | local_set : forall (z : state) (v_val : val) (x : localidx) (z' : state),
    (z' == (update_local z x v_val)) ->
    Step (.mk_config z [(instr_val v_val), (.LOCAL_SET x)]) (.mk_config z' [])
  | global_get : forall (z : state) (x : globalidx) (v_val : val),
    (v_val == (global z x)) ->
    Step (.mk_config z [(.GLOBAL_GET x)]) (.mk_config z [(instr_val v_val)])
  | global_set : forall (z : state) (v_val : val) (x : globalidx) (z' : state),
    (z' == (update_global z x v_val)) ->
    Step (.mk_config z [(instr_val v_val), (.GLOBAL_SET x)]) (.mk_config z' [])

/- Axiom Definition at: doc/example/NanoWasm.spectec:136.1-136.30 -/
opaque float : forall (nat : Nat) (var_0 : (List Nat)), const := opaqueDef

/- Lean 4 export -/

/- A little prelude -/

set_option linter.unusedVariables false

instance : Append (Option a) where
  append := fun o1 o2 => match o1 with | none => o2 | _ => o1


inductive Forall (R : α → Prop) : List α → Prop
  | nil : Forall R []
  | cons {a l₁} : R a → Forall R l₁ → Forall R (a :: l₁)
attribute [simp] Forall.nil
inductive Forall₂ (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {a b l₁ l₂} : R a b → Forall₂ R l₁ l₂ → Forall₂ R (a :: l₁) (b :: l₂)
attribute [simp] Forall₂.nil
def Option.zipWith : (α → β → γ) → Option α → Option β → Option γ
  | f,  (some x), (some y) => some (f x y)
  | _, _, _ => none
def Option.toList : Option α → List α
  | none => List.nil
  | some x => [x]
def List.upd : List α → Nat → α → List α
  | [], _, _ => []
  | x::xs, 0, y => y :: xs
  | x::xs, n+1, y => x :: xs.upd n y
def List.upds : List α → Nat → Nat → List α → List α
  | xs, n, m, ys => xs.take n ++ ys ++ xs.drop (n + m)
def List.slice : List α → Nat → Nat → List α
  | xs, n, m => (xs.drop n)


/- Now, the generated code -/

@[reducible] def N := Nat

@[reducible] def Name := String



@[reducible] def Byte := Nat



@[reducible] def U32 := Nat



@[reducible] def Idx := Nat



@[reducible] def Funcidx := Idx



@[reducible] def Globalidx := Idx



@[reducible] def Tableidx := Idx



@[reducible] def Memidx := Idx



@[reducible] def Elemidx := Idx



@[reducible] def Dataidx := Idx



@[reducible] def Labelidx := Idx



@[reducible] def Localidx := Idx



inductive Numtype where
 | I32 : Numtype
 | I64 : Numtype
 | F32 : Numtype
 | F64 : Numtype
  deriving Inhabited, BEq



inductive Vectype where
 | V128 : Vectype
  deriving Inhabited, BEq



inductive Reftype where
 | FUNCREF : Reftype
 | EXTERNREF : Reftype
  deriving Inhabited, BEq



inductive Valtype where
 | I32 : Valtype
 | I64 : Valtype
 | F32 : Valtype
 | F64 : Valtype
 | V128 : Valtype
 | FUNCREF : Valtype
 | EXTERNREF : Valtype
 | BOT : Valtype
  deriving Inhabited, BEq

def «$valtype_numtype» : Numtype -> Valtype
  | Numtype.I32 => Valtype.I32
  | Numtype.I64 => Valtype.I64
  | Numtype.F32 => Valtype.F32
  | Numtype.F64 => Valtype.F64

def «$valtype_reftype» : Reftype -> Valtype
  | Reftype.FUNCREF => Valtype.FUNCREF
  | Reftype.EXTERNREF => Valtype.EXTERNREF

def «$valtype_vectype» : Vectype -> Valtype
  | Vectype.V128 => Valtype.V128



inductive In where
 | I32 : In
 | I64 : In
  deriving Inhabited, BEq

def «$numtype_in» : In -> Numtype
  | In.I32 => Numtype.I32
  | In.I64 => Numtype.I64

def «$valtype_in» : In -> Valtype
  | In.I32 => Valtype.I32
  | In.I64 => Valtype.I64



inductive Fn where
 | F32 : Fn
 | F64 : Fn
  deriving Inhabited, BEq

def «$numtype_fn» : Fn -> Numtype
  | Fn.F32 => Numtype.F32
  | Fn.F64 => Numtype.F64

def «$valtype_fn» : Fn -> Valtype
  | Fn.F32 => Valtype.F32
  | Fn.F64 => Valtype.F64



@[reducible] def Resulttype := (List Valtype)



@[reducible] def Limits := /- mixop: `[%..%]` -/ (U32 × U32)



@[reducible] def Globaltype := /- mixop: `MUT%?%` -/ ((Option Unit) × Valtype)



@[reducible] def Functype := /- mixop: `%->%` -/ (Resulttype × Resulttype)



@[reducible] def Tabletype := /- mixop: `%%` -/ (Limits × Reftype)



@[reducible] def Memtype := /- mixop: `%I8` -/ Limits



@[reducible] def Elemtype := Reftype



@[reducible] def Datatype := /- mixop: OK -/ Unit



inductive Externtype where
 | GLOBAL : Globaltype -> Externtype
 | FUNC : Functype -> Externtype
 | TABLE : Tabletype -> Externtype
 | MEM : Memtype -> Externtype
  deriving Inhabited, BEq



inductive Sx where
 | U : Sx
 | S : Sx
  deriving Inhabited, BEq



inductive Unop_IXX where
 | CLZ : Unop_IXX
 | CTZ : Unop_IXX
 | POPCNT : Unop_IXX
  deriving Inhabited, BEq

inductive Unop_FXX where
 | ABS : Unop_FXX
 | NEG : Unop_FXX
 | SQRT : Unop_FXX
 | CEIL : Unop_FXX
 | FLOOR : Unop_FXX
 | TRUNC : Unop_FXX
 | NEAREST : Unop_FXX
  deriving Inhabited, BEq

inductive Binop_IXX where
 | ADD : Binop_IXX
 | SUB : Binop_IXX
 | MUL : Binop_IXX
 | DIV : Sx -> Binop_IXX
 | REM : Sx -> Binop_IXX
 | AND : Binop_IXX
 | OR : Binop_IXX
 | XOR : Binop_IXX
 | SHL : Binop_IXX
 | SHR : Sx -> Binop_IXX
 | ROTL : Binop_IXX
 | ROTR : Binop_IXX
  deriving Inhabited, BEq

inductive Binop_FXX where
 | ADD : Binop_FXX
 | SUB : Binop_FXX
 | MUL : Binop_FXX
 | DIV : Binop_FXX
 | MIN : Binop_FXX
 | MAX : Binop_FXX
 | COPYSIGN : Binop_FXX
  deriving Inhabited, BEq

inductive Testop_IXX where
 | EQZ : Testop_IXX
  deriving Inhabited, BEq

inductive Testop_FXX where
  deriving BEq

inductive Relop_IXX where
 | EQ : Relop_IXX
 | NE : Relop_IXX
 | LT : Sx -> Relop_IXX
 | GT : Sx -> Relop_IXX
 | LE : Sx -> Relop_IXX
 | GE : Sx -> Relop_IXX
  deriving Inhabited, BEq

inductive Relop_FXX where
 | EQ : Relop_FXX
 | NE : Relop_FXX
 | LT : Relop_FXX
 | GT : Relop_FXX
 | LE : Relop_FXX
 | GE : Relop_FXX
  deriving Inhabited, BEq

inductive Unop_numtype where
 | _I : Unop_IXX -> Unop_numtype
 | _F : Unop_FXX -> Unop_numtype
  deriving Inhabited, BEq

inductive Binop_numtype where
 | _I : Binop_IXX -> Binop_numtype
 | _F : Binop_FXX -> Binop_numtype
  deriving Inhabited, BEq

inductive Testop_numtype where
 | _I : Testop_IXX -> Testop_numtype
 | _F : Testop_FXX -> Testop_numtype
  deriving Inhabited, BEq

inductive Relop_numtype where
 | _I : Relop_IXX -> Relop_numtype
 | _F : Relop_FXX -> Relop_numtype
  deriving Inhabited, BEq

inductive Cvtop where
 | CONVERT : Cvtop
 | REINTERPRET : Cvtop
  deriving Inhabited, BEq

@[reducible] def C_numtype := Nat

@[reducible] def C_vectype := Nat

@[reducible] def Blocktype := Functype



inductive Instr where
 | UNREACHABLE : Instr
 | NOP : Instr
 | DROP : Instr
 | SELECT : (Option Valtype) -> Instr
 | BLOCK : (Blocktype × (List Instr)) -> Instr
 | LOOP : (Blocktype × (List Instr)) -> Instr
 | IF : (Blocktype × (List Instr) × (List Instr)) -> Instr
 | BR : Labelidx -> Instr
 | BR_IF : Labelidx -> Instr
 | BR_TABLE : ((List Labelidx) × Labelidx) -> Instr
 | CALL : Funcidx -> Instr
 | CALL_INDIRECT : (Tableidx × Functype) -> Instr
 | RETURN : Instr
 | CONST : (Numtype × C_numtype) -> Instr
 | UNOP : (Numtype × Unop_numtype) -> Instr
 | BINOP : (Numtype × Binop_numtype) -> Instr
 | TESTOP : (Numtype × Testop_numtype) -> Instr
 | RELOP : (Numtype × Relop_numtype) -> Instr
 | EXTEND : (Numtype × N) -> Instr
 | CVTOP : (Numtype × Cvtop × Numtype × (Option Sx)) -> Instr
 | REF_NULL : Reftype -> Instr
 | REF_FUNC : Funcidx -> Instr
 | REF_IS_NULL : Instr
 | LOCAL_GET : Localidx -> Instr
 | LOCAL_SET : Localidx -> Instr
 | LOCAL_TEE : Localidx -> Instr
 | GLOBAL_GET : Globalidx -> Instr
 | GLOBAL_SET : Globalidx -> Instr
 | TABLE_GET : Tableidx -> Instr
 | TABLE_SET : Tableidx -> Instr
 | TABLE_SIZE : Tableidx -> Instr
 | TABLE_GROW : Tableidx -> Instr
 | TABLE_FILL : Tableidx -> Instr
 | TABLE_COPY : (Tableidx × Tableidx) -> Instr
 | TABLE_INIT : (Tableidx × Elemidx) -> Instr
 | ELEM_DROP : Elemidx -> Instr
 | MEMORY_SIZE : Instr
 | MEMORY_GROW : Instr
 | MEMORY_FILL : Instr
 | MEMORY_COPY : Instr
 | MEMORY_INIT : Dataidx -> Instr
 | DATA_DROP : Dataidx -> Instr
 | LOAD : (Numtype × (Option (N × Sx)) × U32 × U32) -> Instr
 | STORE : (Numtype × (Option N) × U32 × U32) -> Instr
  deriving Inhabited, BEq









@[reducible] def Expr := (List Instr)





inductive Elemmode where
 | TABLE : (Tableidx × Expr) -> Elemmode
 | DECLARE : Elemmode
  deriving Inhabited, BEq

inductive Datamode where
 | MEMORY : (Memidx × Expr) -> Datamode
  deriving Inhabited, BEq

@[reducible] def Func := /- mixop: `FUNC%%*%` -/ (Functype × (List Valtype) × Expr)



@[reducible] def Global := /- mixop: GLOBAL -/ (Globaltype × Expr)



@[reducible] def Table := /- mixop: TABLE -/ Tabletype



@[reducible] def Mem := /- mixop: MEMORY -/ Memtype



@[reducible] def Elem := /- mixop: `ELEM%%*%?` -/ (Reftype × (List Expr) × (Option Elemmode))



@[reducible] def Data := /- mixop: `DATA(*)%*%?` -/ ((List (List Byte)) × (Option Datamode))



@[reducible] def Start := /- mixop: START -/ Funcidx



inductive Externuse where
 | FUNC : Funcidx -> Externuse
 | GLOBAL : Globalidx -> Externuse
 | TABLE : Tableidx -> Externuse
 | MEM : Memidx -> Externuse
  deriving Inhabited, BEq



@[reducible] def Export := /- mixop: EXPORT -/ (Name × Externuse)



@[reducible] def Import := /- mixop: IMPORT -/ (Name × Name × Externtype)



@[reducible] def Module := /- mixop: `MODULE%*%*%*%*%*%*%*%?%*` -/ ((List Import) × (List Func) × (List Global) × (List Table) × (List Mem) × (List Elem) × (List Data) × (Option Start) × (List Export))



def «$Ki» : Unit -> Nat
  | () => 1024

def «$min» : (Nat × Nat) -> Nat
  | (0, j) => 0
  | (i, 0) => 0
  | ((i + 1), (j + 1)) => («$min» (i, j))

def «$size» : Valtype -> (Option Nat)
  | Valtype.I32 => (some 32)
  | Valtype.I64 => (some 64)
  | Valtype.F32 => (some 32)
  | Valtype.F64 => (some 64)
  | Valtype.V128 => (some 128)
  | x => none



def «$test_sub_ATOM_22» : N -> Nat
  | n_3_ATOM_y => 0

def «$curried_» : (N × N) -> Nat
  | (n_1, n_2) => (n_1 + n_2)

inductive Testfuse where
 | AB_ : (Nat × Nat × Nat) -> Testfuse
 | CD : (Nat × Nat × Nat) -> Testfuse
 | EF : (Nat × Nat × Nat) -> Testfuse
 | GH : (Nat × Nat × Nat) -> Testfuse
 | IJ : (Nat × Nat × Nat) -> Testfuse
 | KL : (Nat × Nat × Nat) -> Testfuse
 | MN : (Nat × Nat × Nat) -> Testfuse
 | OP : (Nat × Nat × Nat) -> Testfuse
 | QR : (Nat × Nat × Nat) -> Testfuse
  deriving Inhabited, BEq

structure Context where 
  FUNC : (List Functype)
  GLOBAL : (List Globaltype)
  TABLE : (List Tabletype)
  MEM : (List Memtype)
  ELEM : (List Elemtype)
  DATA : (List Datatype)
  LOCAL : (List Valtype)
  LABEL : (List Resulttype)
  RETURN : (Option Resulttype)
  deriving Inhabited, BEq
instance : Append Context where
  append := fun r1 r2 => {
    FUNC := r1.FUNC ++ r2.FUNC,
    GLOBAL := r1.GLOBAL ++ r2.GLOBAL,
    TABLE := r1.TABLE ++ r2.TABLE,
    MEM := r1.MEM ++ r2.MEM,
    ELEM := r1.ELEM ++ r2.ELEM,
    DATA := r1.DATA ++ r2.DATA,
    LOCAL := r1.LOCAL ++ r2.LOCAL,
    LABEL := r1.LABEL ++ r2.LABEL,
    RETURN := r1.RETURN ++ r2.RETURN,
  }



inductive Limits_ok : (Limits × Nat) -> Prop where
  | rule_0 (k : Nat) (n_1 : N) (n_2 : N) : 
    ((n_1 <= n_2) && (n_2 <= k)) -> 
    (Limits_ok ((n_1, n_2), k))



inductive Functype_ok : Functype -> Prop where
  | rule_0 (ft : Functype) : 
    (Functype_ok ft)



inductive Globaltype_ok : Globaltype -> Prop where
  | rule_0 (gt : Globaltype) : 
    (Globaltype_ok gt)



inductive Tabletype_ok : Tabletype -> Prop where
  | rule_0 (lim : Limits) (rt : Reftype) : 
    (Limits_ok (lim, ((((Nat.pow 2) 32)) - 1))) -> 
    (Tabletype_ok (lim, rt))



inductive Memtype_ok : Memtype -> Prop where
  | rule_0 (lim : Limits) : 
    (Limits_ok (lim, (((Nat.pow 2) 16)))) -> 
    (Memtype_ok lim)



inductive Externtype_ok : Externtype -> Prop where
  | func (functype : Functype) : 
    (Functype_ok functype) -> 
    (Externtype_ok (Externtype.FUNC functype))
  | «global» (globaltype : Globaltype) : 
    (Globaltype_ok globaltype) -> 
    (Externtype_ok (Externtype.GLOBAL globaltype))
  | table (tabletype : Tabletype) : 
    (Tabletype_ok tabletype) -> 
    (Externtype_ok (Externtype.TABLE tabletype))
  | mem (memtype : Memtype) : 
    (Memtype_ok memtype) -> 
    (Externtype_ok (Externtype.MEM memtype))



inductive Valtype_sub : (Valtype × Valtype) -> Prop where
  | refl (t : Valtype) : 
    (Valtype_sub (t, t))
  | bot (t : Valtype) : 
    (Valtype_sub (Valtype.BOT, t))



inductive Resulttype_sub : ((List Valtype) × (List Valtype)) -> Prop where
  | rule_0 (t_1 : (List Valtype)) (t_2 : (List Valtype)) : 
    (t_1.length == t_2.length) -> 
    (Forall₂ (λ t_1 t_2 ↦ (Valtype_sub (t_1, t_2))) t_1 t_2) -> 
    (Resulttype_sub (t_1, t_2))



inductive Limits_sub : (Limits × Limits) -> Prop where
  | rule_0 (n_11 : N) (n_12 : N) (n_21 : N) (n_22 : N) : 
    (n_11 >= n_21) -> 
    (n_12 <= n_22) -> 
    (Limits_sub ((n_11, n_12), (n_21, n_22)))



inductive Functype_sub : (Functype × Functype) -> Prop where
  | rule_0 (ft : Functype) : 
    (Functype_sub (ft, ft))



inductive Globaltype_sub : (Globaltype × Globaltype) -> Prop where
  | rule_0 (gt : Globaltype) : 
    (Globaltype_sub (gt, gt))



inductive Tabletype_sub : (Tabletype × Tabletype) -> Prop where
  | rule_0 (lim_1 : Limits) (lim_2 : Limits) (rt : Reftype) : 
    (Limits_sub (lim_1, lim_2)) -> 
    (Tabletype_sub ((lim_1, rt), (lim_2, rt)))



inductive Memtype_sub : (Memtype × Memtype) -> Prop where
  | rule_0 (lim_1 : Limits) (lim_2 : Limits) : 
    (Limits_sub (lim_1, lim_2)) -> 
    (Memtype_sub (lim_1, lim_2))



inductive Externtype_sub : (Externtype × Externtype) -> Prop where
  | func (ft_1 : Functype) (ft_2 : Functype) : 
    (Functype_sub (ft_1, ft_2)) -> 
    (Externtype_sub ((Externtype.FUNC ft_1), (Externtype.FUNC ft_2)))
  | «global» (gt_1 : Globaltype) (gt_2 : Globaltype) : 
    (Globaltype_sub (gt_1, gt_2)) -> 
    (Externtype_sub ((Externtype.GLOBAL gt_1), (Externtype.GLOBAL gt_2)))
  | table (tt_1 : Tabletype) (tt_2 : Tabletype) : 
    (Tabletype_sub (tt_1, tt_2)) -> 
    (Externtype_sub ((Externtype.TABLE tt_1), (Externtype.TABLE tt_2)))
  | mem (mt_1 : Memtype) (mt_2 : Memtype) : 
    (Memtype_sub (mt_1, mt_2)) -> 
    (Externtype_sub ((Externtype.MEM mt_1), (Externtype.MEM mt_2)))



inductive Blocktype_ok : (Context × Blocktype × Functype) -> Prop where
  | rule_0 (C : Context) (ft : Functype) : 
    (Functype_ok ft) -> 
    (Blocktype_ok (C, ft, ft))

mutual
inductive Instr_ok : (Context × Instr × Functype) -> Prop where
  | unreachable (C : Context) (t_1 : (List Valtype)) (t_2 : (List Valtype)) : 
    (Instr_ok (C, Instr.UNREACHABLE, (t_1, t_2)))
  | nop (C : Context) : 
    (Instr_ok (C, Instr.NOP, ([], [])))
  | drop (C : Context) (t : Valtype) : 
    (Instr_ok (C, Instr.DROP, ([t], [])))
  | select_expl (C : Context) (t : Valtype) : 
    (Instr_ok (C, (Instr.SELECT (some t)), ([t, t, Valtype.I32], [t])))
  | select_impl (C : Context) (numtype : Numtype) (t : Valtype) (t' : Valtype) (vectype : Vectype) : 
    (Valtype_sub (t, t')) -> 
    ((t' == («$valtype_numtype» numtype)) || (t' == («$valtype_vectype» vectype))) -> 
    (Instr_ok (C, (Instr.SELECT none), ([t, t, Valtype.I32], [t])))
  | block (C : Context) (bt : Blocktype) (instr : (List Instr)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) : 
    (Blocktype_ok (C, bt, (t_1, t_2))) -> 
    (InstrSeq_ok (({FUNC := [], GLOBAL := [], TABLE := [], MEM := [], ELEM := [], DATA := [], LOCAL := [], LABEL := (List.map (λ t_2 ↦ [t_2]) t_2), RETURN := none} ++ C), instr, (t_1, t_2))) -> 
    (Instr_ok (C, (Instr.BLOCK (bt, instr)), (t_1, t_2)))
  | loop (C : Context) (bt : Blocktype) (instr : (List Instr)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) : 
    (Blocktype_ok (C, bt, (t_1, t_2))) -> 
    (InstrSeq_ok (({FUNC := [], GLOBAL := [], TABLE := [], MEM := [], ELEM := [], DATA := [], LOCAL := [], LABEL := (List.map (λ t_1 ↦ [t_1]) t_1), RETURN := none} ++ C), instr, (t_1, t_2))) -> 
    (Instr_ok (C, (Instr.LOOP (bt, instr)), (t_1, t_2)))
  | if (C : Context) (bt : Blocktype) (instr_1 : (List Instr)) (instr_2 : (List Instr)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) : 
    (Blocktype_ok (C, bt, (t_1, t_2))) -> 
    (InstrSeq_ok (({FUNC := [], GLOBAL := [], TABLE := [], MEM := [], ELEM := [], DATA := [], LOCAL := [], LABEL := (List.map (λ t_2 ↦ [t_2]) t_2), RETURN := none} ++ C), instr_1, (t_1, t_2))) -> 
    (InstrSeq_ok (({FUNC := [], GLOBAL := [], TABLE := [], MEM := [], ELEM := [], DATA := [], LOCAL := [], LABEL := (List.map (λ t_2 ↦ [t_2]) t_2), RETURN := none} ++ C), instr_2, (t_1, t_2))) -> 
    (Instr_ok (C, (Instr.IF (bt, instr_1, instr_2)), (t_1, t_2)))
  | br (C : Context) (l : Labelidx) (t : (List Valtype)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) : 
    (l < C.LABEL.length) -> 
    ((C.LABEL.get! l) == t) -> 
    (Instr_ok (C, (Instr.BR l), ((t_1 ++ t), t_2)))
  | br_if (C : Context) (l : Labelidx) (t : (List Valtype)) : 
    (l < C.LABEL.length) -> 
    ((C.LABEL.get! l) == t) -> 
    (Instr_ok (C, (Instr.BR_IF l), ((t ++ [Valtype.I32]), t)))
  | br_table (C : Context) (l : (List Labelidx)) (l' : Labelidx) (t : (List Valtype)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) : 
    (Forall (λ l ↦ (l < C.LABEL.length)) l) -> 
    (l' < C.LABEL.length) -> 
    (Forall (λ l ↦ (Resulttype_sub (t, (C.LABEL.get! l)))) l) -> 
    (Resulttype_sub (t, (C.LABEL.get! l'))) -> 
    (Instr_ok (C, (Instr.BR_TABLE (l, l')), ((t_1 ++ t), t_2)))
  | return (C : Context) (t : (List Valtype)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) : 
    (C.RETURN == (some t)) -> 
    (Instr_ok (C, Instr.RETURN, ((t_1 ++ t), t_2)))
  | call (C : Context) (t_1 : (List Valtype)) (t_2 : (List Valtype)) (x : Idx) : 
    (x < C.FUNC.length) -> 
    ((C.FUNC.get! x) == (t_1, t_2)) -> 
    (Instr_ok (C, (Instr.CALL x), (t_1, t_2)))
  | call_indirect (C : Context) (ft : Functype) (lim : Limits) (t_1 : (List Valtype)) (t_2 : (List Valtype)) (x : Idx) : 
    (x < C.TABLE.length) -> 
    ((C.TABLE.get! x) == (lim, Reftype.FUNCREF)) -> 
    (ft == (t_1, t_2)) -> 
    (Instr_ok (C, (Instr.CALL_INDIRECT (x, ft)), ((t_1 ++ [Valtype.I32]), t_2)))
  | const (C : Context) (c_nt : C_numtype) (nt : Numtype) : 
    (Instr_ok (C, (Instr.CONST (nt, c_nt)), ([], [(«$valtype_numtype» nt)])))
  | unop (C : Context) (nt : Numtype) (unop : Unop_numtype) : 
    (Instr_ok (C, (Instr.UNOP (nt, unop)), ([(«$valtype_numtype» nt)], [(«$valtype_numtype» nt)])))
  | binop (C : Context) (binop : Binop_numtype) (nt : Numtype) : 
    (Instr_ok (C, (Instr.BINOP (nt, binop)), ([(«$valtype_numtype» nt), («$valtype_numtype» nt)], [(«$valtype_numtype» nt)])))
  | testop (C : Context) (nt : Numtype) (testop : Testop_numtype) : 
    (Instr_ok (C, (Instr.TESTOP (nt, testop)), ([(«$valtype_numtype» nt)], [Valtype.I32])))
  | relop (C : Context) (nt : Numtype) (relop : Relop_numtype) : 
    (Instr_ok (C, (Instr.RELOP (nt, relop)), ([(«$valtype_numtype» nt), («$valtype_numtype» nt)], [Valtype.I32])))
  | extend (C : Context) (n : N) (nt : Numtype) (o0 : Nat) : 
    ((«$size» («$valtype_numtype» nt)) == (some o0)) -> 
    (n <= o0) -> 
    (Instr_ok (C, (Instr.EXTEND (nt, n)), ([(«$valtype_numtype» nt)], [(«$valtype_numtype» nt)])))
  | reinterpret (C : Context) (nt_1 : Numtype) (nt_2 : Numtype) (o0 : Nat) (o1 : Nat) : 
    ((«$size» («$valtype_numtype» nt_1)) == (some o0)) -> 
    ((«$size» («$valtype_numtype» nt_2)) == (some o1)) -> 
    (nt_1 != nt_2) -> 
    (o0 == o1) -> 
    (Instr_ok (C, (Instr.CVTOP (nt_1, Cvtop.REINTERPRET, nt_2, none)), ([(«$valtype_numtype» nt_2)], [(«$valtype_numtype» nt_1)])))
  | convert_i (C : Context) (in_1 : In) (in_2 : In) (sx : (Option Sx)) (o0 : Nat) (o1 : Nat) : 
    ((«$size» («$valtype_in» in_1)) == (some o0)) -> 
    ((«$size» («$valtype_in» in_2)) == (some o1)) -> 
    (in_1 != in_2) -> 
    ((sx == none) = (o0 > o1)) -> 
    (Instr_ok (C, (Instr.CVTOP ((«$numtype_in» in_1), Cvtop.CONVERT, («$numtype_in» in_2), sx)), ([(«$valtype_in» in_2)], [(«$valtype_in» in_1)])))
  | convert_f (C : Context) (fn_1 : Fn) (fn_2 : Fn) : 
    (fn_1 != fn_2) -> 
    (Instr_ok (C, (Instr.CVTOP ((«$numtype_fn» fn_1), Cvtop.CONVERT, («$numtype_fn» fn_2), none)), ([(«$valtype_fn» fn_2)], [(«$valtype_fn» fn_1)])))
  | ref_null (C : Context) (rt : Reftype) : 
    (Instr_ok (C, (Instr.REF_NULL rt), ([], [(«$valtype_reftype» rt)])))
  | ref_func (C : Context) (ft : Functype) (x : Idx) : 
    (x < C.FUNC.length) -> 
    ((C.FUNC.get! x) == ft) -> 
    (Instr_ok (C, (Instr.REF_FUNC x), ([], [Valtype.FUNCREF])))
  | ref_is_null (C : Context) (rt : Reftype) : 
    (Instr_ok (C, Instr.REF_IS_NULL, ([(«$valtype_reftype» rt)], [Valtype.I32])))
  | local_get (C : Context) (t : Valtype) (x : Idx) : 
    (x < C.LOCAL.length) -> 
    ((C.LOCAL.get! x) == t) -> 
    (Instr_ok (C, (Instr.LOCAL_GET x), ([], [t])))
  | local_set (C : Context) (t : Valtype) (x : Idx) : 
    (x < C.LOCAL.length) -> 
    ((C.LOCAL.get! x) == t) -> 
    (Instr_ok (C, (Instr.LOCAL_SET x), ([t], [])))
  | local_tee (C : Context) (t : Valtype) (x : Idx) : 
    (x < C.LOCAL.length) -> 
    ((C.LOCAL.get! x) == t) -> 
    (Instr_ok (C, (Instr.LOCAL_TEE x), ([t], [t])))
  | global_get (C : Context) (t : Valtype) (x : Idx) (w0 : (Option Unit)) : 
    (x < C.GLOBAL.length) -> 
    ((C.GLOBAL.get! x) == (w0, t)) -> 
    (Instr_ok (C, (Instr.GLOBAL_GET x), ([], [t])))
  | global_set (C : Context) (t : Valtype) (x : Idx) : 
    (x < C.GLOBAL.length) -> 
    ((C.GLOBAL.get! x) == ((some ()), t)) -> 
    (Instr_ok (C, (Instr.GLOBAL_SET x), ([t], [])))
  | table_get (C : Context) (lim : Limits) (rt : Reftype) (x : Idx) : 
    (x < C.TABLE.length) -> 
    ((C.TABLE.get! x) == (lim, rt)) -> 
    (Instr_ok (C, (Instr.TABLE_GET x), ([Valtype.I32], [(«$valtype_reftype» rt)])))
  | table_set (C : Context) (lim : Limits) (rt : Reftype) (x : Idx) : 
    (x < C.TABLE.length) -> 
    ((C.TABLE.get! x) == (lim, rt)) -> 
    (Instr_ok (C, (Instr.TABLE_SET x), ([Valtype.I32, («$valtype_reftype» rt)], [])))
  | table_size (C : Context) (tt : Tabletype) (x : Idx) : 
    (x < C.TABLE.length) -> 
    ((C.TABLE.get! x) == tt) -> 
    (Instr_ok (C, (Instr.TABLE_SIZE x), ([], [Valtype.I32])))
  | table_grow (C : Context) (lim : Limits) (rt : Reftype) (x : Idx) : 
    (x < C.TABLE.length) -> 
    ((C.TABLE.get! x) == (lim, rt)) -> 
    (Instr_ok (C, (Instr.TABLE_GROW x), ([(«$valtype_reftype» rt), Valtype.I32], [Valtype.I32])))
  | table_fill (C : Context) (lim : Limits) (rt : Reftype) (x : Idx) : 
    (x < C.TABLE.length) -> 
    ((C.TABLE.get! x) == (lim, rt)) -> 
    (Instr_ok (C, (Instr.TABLE_FILL x), ([Valtype.I32, («$valtype_reftype» rt), Valtype.I32], [])))
  | table_copy (C : Context) (lim_1 : Limits) (lim_2 : Limits) (rt : Reftype) (x_1 : Idx) (x_2 : Idx) : 
    (x_1 < C.TABLE.length) -> 
    (x_2 < C.TABLE.length) -> 
    ((C.TABLE.get! x_1) == (lim_1, rt)) -> 
    ((C.TABLE.get! x_2) == (lim_2, rt)) -> 
    (Instr_ok (C, (Instr.TABLE_COPY (x_1, x_2)), ([Valtype.I32, Valtype.I32, Valtype.I32], [])))
  | table_init (C : Context) (lim : Limits) (rt : Reftype) (x_1 : Idx) (x_2 : Idx) : 
    (x_1 < C.TABLE.length) -> 
    (x_2 < C.ELEM.length) -> 
    ((C.TABLE.get! x_1) == (lim, rt)) -> 
    ((C.ELEM.get! x_2) == rt) -> 
    (Instr_ok (C, (Instr.TABLE_INIT (x_1, x_2)), ([Valtype.I32, Valtype.I32, Valtype.I32], [])))
  | elem_drop (C : Context) (rt : Reftype) (x : Idx) : 
    (x < C.ELEM.length) -> 
    ((C.ELEM.get! x) == rt) -> 
    (Instr_ok (C, (Instr.ELEM_DROP x), ([], [])))
  | memory_size (C : Context) (mt : Memtype) : 
    (0 < C.MEM.length) -> 
    ((C.MEM.get! 0) == mt) -> 
    (Instr_ok (C, Instr.MEMORY_SIZE, ([], [Valtype.I32])))
  | memory_grow (C : Context) (mt : Memtype) : 
    (0 < C.MEM.length) -> 
    ((C.MEM.get! 0) == mt) -> 
    (Instr_ok (C, Instr.MEMORY_GROW, ([Valtype.I32], [Valtype.I32])))
  | memory_fill (C : Context) (mt : Memtype) : 
    (0 < C.MEM.length) -> 
    ((C.MEM.get! 0) == mt) -> 
    (Instr_ok (C, Instr.MEMORY_FILL, ([Valtype.I32, Valtype.I32, Valtype.I32], [Valtype.I32])))
  | memory_copy (C : Context) (mt : Memtype) : 
    (0 < C.MEM.length) -> 
    ((C.MEM.get! 0) == mt) -> 
    (Instr_ok (C, Instr.MEMORY_COPY, ([Valtype.I32, Valtype.I32, Valtype.I32], [Valtype.I32])))
  | memory_init (C : Context) (mt : Memtype) (x : Idx) : 
    (0 < C.MEM.length) -> 
    (x < C.DATA.length) -> 
    ((C.MEM.get! 0) == mt) -> 
    ((C.DATA.get! x) == ()) -> 
    (Instr_ok (C, (Instr.MEMORY_INIT x), ([Valtype.I32, Valtype.I32, Valtype.I32], [Valtype.I32])))
  | data_drop (C : Context) (x : Idx) : 
    (x < C.DATA.length) -> 
    ((C.DATA.get! x) == ()) -> 
    (Instr_ok (C, (Instr.DATA_DROP x), ([], [])))
  | load (C : Context) («in» : In) (mt : Memtype) (n : (Option N)) (n_A : N) (n_O : N) (nt : Numtype) (sx : (Option Sx)) (o0 : Nat) (o1 : (Option Nat)) : 
    (0 < C.MEM.length) -> 
    ((n == none) = (o1 == none)) -> 
    ((n == none) = (sx == none)) -> 
    ((«$size» («$valtype_numtype» nt)) == (some o0)) -> 
    (Forall (λ o1 ↦ ((«$size» («$valtype_numtype» nt)) == (some o1))) o1.toList) -> 
    ((C.MEM.get! 0) == mt) -> 
    ((((Nat.pow 2) n_A)) <= (((Nat.div o0) 8))) -> 
    (Forall₂ (λ n o1 ↦ (((((Nat.pow 2) n_A)) <= (((Nat.div n) 8))) && ((((Nat.div n) 8)) < (((Nat.div o1) 8))))) n.toList o1.toList) -> 
    ((n == none) || (nt == («$numtype_in» «in»))) -> 
    (Instr_ok (C, (Instr.LOAD (nt, (Option.zipWith (λ n sx ↦ (n, sx)) n sx), n_A, n_O)), ([Valtype.I32], [(«$valtype_numtype» nt)])))
  | store (C : Context) («in» : In) (mt : Memtype) (n : (Option N)) (n_A : N) (n_O : N) (nt : Numtype) (o0 : Nat) (o1 : (Option Nat)) : 
    (0 < C.MEM.length) -> 
    ((n == none) = (o1 == none)) -> 
    ((«$size» («$valtype_numtype» nt)) == (some o0)) -> 
    (Forall (λ o1 ↦ ((«$size» («$valtype_numtype» nt)) == (some o1))) o1.toList) -> 
    ((C.MEM.get! 0) == mt) -> 
    ((((Nat.pow 2) n_A)) <= (((Nat.div o0) 8))) -> 
    (Forall₂ (λ n o1 ↦ (((((Nat.pow 2) n_A)) <= (((Nat.div n) 8))) && ((((Nat.div n) 8)) < (((Nat.div o1) 8))))) n.toList o1.toList) -> 
    ((n == none) || (nt == («$numtype_in» «in»))) -> 
    (Instr_ok (C, (Instr.STORE (nt, n, n_A, n_O)), ([Valtype.I32, («$valtype_numtype» nt)], [])))
inductive InstrSeq_ok : (Context × (List Instr) × Functype) -> Prop where
  | empty (C : Context) : 
    (InstrSeq_ok (C, [], ([], [])))
  | seq (C : Context) (instr_1 : Instr) (instr_2 : Instr) (t_1 : (List Valtype)) (t_2 : (List Valtype)) (t_3 : (List Valtype)) : 
    (Instr_ok (C, instr_1, (t_1, t_2))) -> 
    (InstrSeq_ok (C, [instr_2], (t_2, t_3))) -> 
    (InstrSeq_ok (C, ([instr_1] ++ [instr_2]), (t_1, t_3)))
  | weak (C : Context) (instr : (List Instr)) (t'_1 : (List Valtype)) (t'_2 : (List Valtype)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) : 
    (InstrSeq_ok (C, instr, (t_1, t_2))) -> 
    (Resulttype_sub (t'_1, t_1)) -> 
    (Resulttype_sub (t_2, t'_2)) -> 
    (InstrSeq_ok (C, instr, (t'_1, t'_2)))
  | frame (C : Context) (instr : (List Instr)) (t : (List Valtype)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) : 
    (InstrSeq_ok (C, instr, (t_1, t_2))) -> 
    (InstrSeq_ok (C, instr, ((t ++ t_1), (t ++ t_2))))end





inductive Expr_ok : (Context × Expr × Resulttype) -> Prop where
  | rule_0 (C : Context) (instr : (List Instr)) (t : (List Valtype)) : 
    (InstrSeq_ok (C, instr, ([], t))) -> 
    (Expr_ok (C, instr, t))





inductive Instr_const : (Context × Instr) -> Prop where
  | const (C : Context) (c : C_numtype) (nt : Numtype) : 
    (Instr_const (C, (Instr.CONST (nt, c))))
  | ref_null (C : Context) (rt : Reftype) : 
    (Instr_const (C, (Instr.REF_NULL rt)))
  | ref_func (C : Context) (x : Idx) : 
    (Instr_const (C, (Instr.REF_FUNC x)))
  | global_get (C : Context) (t : Valtype) (x : Idx) : 
    (x < C.GLOBAL.length) -> 
    ((C.GLOBAL.get! x) == (none, t)) -> 
    (Instr_const (C, (Instr.GLOBAL_GET x)))



inductive Expr_const : (Context × Expr) -> Prop where
  | rule_0 (C : Context) (instr : (List Instr)) : 
    (Forall (λ instr ↦ (Instr_const (C, instr))) instr) -> 
    (Expr_const (C, instr))



inductive Expr_ok_const : (Context × Expr × Valtype) -> Prop where
  | rule_0 (C : Context) (expr : Expr) (t : Valtype) : 
    (Expr_ok (C, expr, [t])) -> 
    (Expr_const (C, expr)) -> 
    (Expr_ok_const (C, expr, t))



inductive Func_ok : (Context × Func × Functype) -> Prop where
  | rule_0 (C : Context) (expr : Expr) (ft : Functype) (t : (List Valtype)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) : 
    (ft == (t_1, t_2)) -> 
    (Functype_ok ft) -> 
    (Expr_ok (({FUNC := [], GLOBAL := [], TABLE := [], MEM := [], ELEM := [], DATA := [], LOCAL := [], LABEL := [], RETURN := (some t_2)} ++ ({FUNC := [], GLOBAL := [], TABLE := [], MEM := [], ELEM := [], DATA := [], LOCAL := [], LABEL := [t_2], RETURN := none} ++ ({FUNC := [], GLOBAL := [], TABLE := [], MEM := [], ELEM := [], DATA := [], LOCAL := (t_1 ++ t), LABEL := [], RETURN := none} ++ C))), expr, t_2)) -> 
    (Func_ok (C, (ft, t, expr), ft))



inductive Global_ok : (Context × Global × Globaltype) -> Prop where
  | rule_0 (C : Context) (expr : Expr) (gt : Globaltype) (t : Valtype) (w0 : (Option Unit)) : 
    (Globaltype_ok gt) -> 
    (gt == (w0, t)) -> 
    (Expr_ok_const (C, expr, t)) -> 
    (Global_ok (C, (gt, expr), gt))



inductive Table_ok : (Context × Table × Tabletype) -> Prop where
  | rule_0 (C : Context) (tt : Tabletype) : 
    (Tabletype_ok tt) -> 
    (Table_ok (C, tt, tt))



inductive Mem_ok : (Context × Mem × Memtype) -> Prop where
  | rule_0 (C : Context) (mt : Memtype) : 
    (Memtype_ok mt) -> 
    (Mem_ok (C, mt, mt))



inductive Elemmode_ok : (Context × Elemmode × Reftype) -> Prop where
  | active (C : Context) (expr : Expr) (lim : Limits) (rt : Reftype) (x : Idx) : 
    (x < C.TABLE.length) -> 
    ((C.TABLE.get! x) == (lim, rt)) -> 
    (Expr_ok_const (C, expr, Valtype.I32)) /- *{} -/ -> 
    (Elemmode_ok (C, (Elemmode.TABLE (x, expr)), rt))
  | declare (C : Context) (rt : Reftype) : 
    (Elemmode_ok (C, Elemmode.DECLARE, rt))

inductive Elem_ok : (Context × Elem × Reftype) -> Prop where
  | rule_0 (C : Context) (elemmode : (Option Elemmode)) (expr : (List Expr)) (rt : Reftype) : 
    (Forall (λ expr ↦ (Expr_ok (C, expr, [(«$valtype_reftype» rt)]))) expr) -> 
    (Forall (λ elemmode ↦ (Elemmode_ok (C, elemmode, rt))) elemmode.toList) -> 
    (Elem_ok (C, (rt, expr, elemmode), rt))



inductive Datamode_ok : (Context × Datamode) -> Prop where
  | rule_0 (C : Context) (expr : Expr) (mt : Memtype) : 
    (0 < C.MEM.length) -> 
    ((C.MEM.get! 0) == mt) -> 
    (Expr_ok_const (C, expr, Valtype.I32)) /- *{} -/ -> 
    (Datamode_ok (C, (Datamode.MEMORY (0, expr))))

inductive Data_ok : (Context × Data) -> Prop where
  | rule_0 (C : Context) (b : (List (List Byte))) (datamode : (Option Datamode)) : 
    (Forall (λ datamode ↦ (Datamode_ok (C, datamode))) datamode.toList) -> 
    (Data_ok (C, ((List.map (λ b ↦ b) b), datamode)))







inductive Start_ok : (Context × Start) -> Prop where
  | rule_0 (C : Context) (x : Idx) : 
    (x < C.FUNC.length) -> 
    ((C.FUNC.get! x) == ([], [])) -> 
    (Start_ok (C, x))



inductive Import_ok : (Context × Import × Externtype) -> Prop where
  | rule_0 (C : Context) (name_1 : Name) (name_2 : Name) (xt : Externtype) : 
    (Externtype_ok xt) -> 
    (Import_ok (C, (name_1, name_2, xt), xt))



inductive Externuse_ok : (Context × Externuse × Externtype) -> Prop where
  | func (C : Context) (ft : Functype) (x : Idx) : 
    (x < C.FUNC.length) -> 
    ((C.FUNC.get! x) == ft) -> 
    (Externuse_ok (C, (Externuse.FUNC x), (Externtype.FUNC ft)))
  | «global» (C : Context) (gt : Globaltype) (x : Idx) : 
    (x < C.GLOBAL.length) -> 
    ((C.GLOBAL.get! x) == gt) -> 
    (Externuse_ok (C, (Externuse.GLOBAL x), (Externtype.GLOBAL gt)))
  | table (C : Context) (tt : Tabletype) (x : Idx) : 
    (x < C.TABLE.length) -> 
    ((C.TABLE.get! x) == tt) -> 
    (Externuse_ok (C, (Externuse.TABLE x), (Externtype.TABLE tt)))
  | mem (C : Context) (mt : Memtype) (x : Idx) : 
    (x < C.MEM.length) -> 
    ((C.MEM.get! x) == mt) -> 
    (Externuse_ok (C, (Externuse.MEM x), (Externtype.MEM mt)))

inductive Export_ok : (Context × Export × Externtype) -> Prop where
  | rule_0 (C : Context) (externuse : Externuse) (name : Name) (xt : Externtype) : 
    (Externuse_ok (C, externuse, xt)) -> 
    (Export_ok (C, (name, externuse), xt))





inductive Module_ok : Module -> Prop where
  | rule_0 (C : Context) (data : (List Data)) (elem : (List Elem)) («export» : (List Export)) (ft : (List Functype)) (func : (List Func)) («global» : (List Global)) (gt : (List Globaltype)) («import» : (List Import)) (mem : (List Mem)) (mt : (List Memtype)) (n : N) (rt : (List Reftype)) (start : (Option Start)) (table : (List Table)) (tt : (List Tabletype)) : 
    (ft.length == func.length) -> 
    («global».length == gt.length) -> 
    (table.length == tt.length) -> 
    (mem.length == mt.length) -> 
    (elem.length == rt.length) -> 
    (C == {FUNC := ft, GLOBAL := gt, TABLE := tt, MEM := mt, ELEM := rt, DATA := [()], LOCAL := [], LABEL := [], RETURN := none}) -> 
    (Forall₂ (λ ft func ↦ (Func_ok (C, func, ft))) ft func) -> 
    (Forall₂ (λ «global» gt ↦ (Global_ok (C, «global», gt))) «global» gt) -> 
    (Forall₂ (λ table tt ↦ (Table_ok (C, table, tt))) table tt) -> 
    (Forall₂ (λ mem mt ↦ (Mem_ok (C, mem, mt))) mem mt) -> 
    (Forall₂ (λ elem rt ↦ (Elem_ok (C, elem, rt))) elem rt) -> 
    (Forall (λ data ↦ (Data_ok (C, data))) data) -> 
    (Forall (λ start ↦ (Start_ok (C, start))) start.toList) -> 
    (mem.length <= 1) -> 
    (Module_ok («import», func, «global», table, mem, elem, data, start, «export»))



@[reducible] def Addr := Nat



@[reducible] def Funcaddr := Addr



@[reducible] def Globaladdr := Addr



@[reducible] def Tableaddr := Addr



@[reducible] def Memaddr := Addr



@[reducible] def Elemaddr := Addr



@[reducible] def Dataaddr := Addr



@[reducible] def Labeladdr := Addr



@[reducible] def Hostaddr := Addr



inductive Num where
 | CONST : (Numtype × C_numtype) -> Num
  deriving Inhabited, BEq



inductive Ref where
 | REF_NULL : Reftype -> Ref
 | REF_FUNC_ADDR : Funcaddr -> Ref
 | REF_HOST_ADDR : Hostaddr -> Ref
  deriving Inhabited, BEq



inductive Val where
 | CONST : (Numtype × C_numtype) -> Val
 | REF_NULL : Reftype -> Val
 | REF_FUNC_ADDR : Funcaddr -> Val
 | REF_HOST_ADDR : Hostaddr -> Val
  deriving Inhabited, BEq



inductive Result where
 | _VALS : (List Val) -> Result
 | TRAP : Result
  deriving Inhabited, BEq



inductive Externval where
 | FUNC : Funcaddr -> Externval
 | GLOBAL : Globaladdr -> Externval
 | TABLE : Tableaddr -> Externval
 | MEM : Memaddr -> Externval
  deriving Inhabited, BEq



def «$default_» : Valtype -> (Option Val)
  | Valtype.I32 => (some (Val.CONST (Numtype.I32, 0)))
  | Valtype.I64 => (some (Val.CONST (Numtype.I64, 0)))
  | Valtype.F32 => (some (Val.CONST (Numtype.F32, 0)))
  | Valtype.F64 => (some (Val.CONST (Numtype.F64, 0)))
  | Valtype.FUNCREF => (some (Val.REF_NULL Reftype.FUNCREF))
  | Valtype.EXTERNREF => (some (Val.REF_NULL Reftype.EXTERNREF))
  | x => none



@[reducible] def Exportinst := /- mixop: EXPORT -/ (Name × Externval)

structure Moduleinst where 
  FUNC : (List Funcaddr)
  GLOBAL : (List Globaladdr)
  TABLE : (List Tableaddr)
  MEM : (List Memaddr)
  ELEM : (List Elemaddr)
  DATA : (List Dataaddr)
  EXPORT : (List Exportinst)
  deriving Inhabited, BEq
instance : Append Moduleinst where
  append := fun r1 r2 => {
    FUNC := r1.FUNC ++ r2.FUNC,
    GLOBAL := r1.GLOBAL ++ r2.GLOBAL,
    TABLE := r1.TABLE ++ r2.TABLE,
    MEM := r1.MEM ++ r2.MEM,
    ELEM := r1.ELEM ++ r2.ELEM,
    DATA := r1.DATA ++ r2.DATA,
    EXPORT := r1.EXPORT ++ r2.EXPORT,
  }

@[reducible] def Funcinst := /- mixop: `%;%` -/ (Moduleinst × Func)



@[reducible] def Globalinst := Val



@[reducible] def Tableinst := (List Ref)



@[reducible] def Meminst := (List Byte)



@[reducible] def Eleminst := (List Ref)



@[reducible] def Datainst := (List Byte)





structure Store where 
  FUNC : (List Funcinst)
  GLOBAL : (List Globalinst)
  TABLE : (List Tableinst)
  MEM : (List Meminst)
  ELEM : (List Eleminst)
  DATA : (List Datainst)
  deriving Inhabited, BEq
instance : Append Store where
  append := fun r1 r2 => {
    FUNC := r1.FUNC ++ r2.FUNC,
    GLOBAL := r1.GLOBAL ++ r2.GLOBAL,
    TABLE := r1.TABLE ++ r2.TABLE,
    MEM := r1.MEM ++ r2.MEM,
    ELEM := r1.ELEM ++ r2.ELEM,
    DATA := r1.DATA ++ r2.DATA,
  }





structure Frame where 
  LOCAL : (List Val)
  MODULE : Moduleinst
  deriving Inhabited, BEq
instance : Append Frame where
  append := fun r1 r2 => {
    LOCAL := r1.LOCAL ++ r2.LOCAL,
    MODULE := r1.MODULE ++ r2.MODULE,
  }



@[reducible] def State := /- mixop: `%;%` -/ (Store × Frame)



inductive Admininstr where
 | UNREACHABLE : Admininstr
 | NOP : Admininstr
 | DROP : Admininstr
 | SELECT : (Option Valtype) -> Admininstr
 | BLOCK : (Blocktype × (List Instr)) -> Admininstr
 | LOOP : (Blocktype × (List Instr)) -> Admininstr
 | IF : (Blocktype × (List Instr) × (List Instr)) -> Admininstr
 | BR : Labelidx -> Admininstr
 | BR_IF : Labelidx -> Admininstr
 | BR_TABLE : ((List Labelidx) × Labelidx) -> Admininstr
 | CALL : Funcidx -> Admininstr
 | CALL_INDIRECT : (Tableidx × Functype) -> Admininstr
 | RETURN : Admininstr
 | CONST : (Numtype × C_numtype) -> Admininstr
 | UNOP : (Numtype × Unop_numtype) -> Admininstr
 | BINOP : (Numtype × Binop_numtype) -> Admininstr
 | TESTOP : (Numtype × Testop_numtype) -> Admininstr
 | RELOP : (Numtype × Relop_numtype) -> Admininstr
 | EXTEND : (Numtype × N) -> Admininstr
 | CVTOP : (Numtype × Cvtop × Numtype × (Option Sx)) -> Admininstr
 | REF_NULL : Reftype -> Admininstr
 | REF_FUNC : Funcidx -> Admininstr
 | REF_IS_NULL : Admininstr
 | LOCAL_GET : Localidx -> Admininstr
 | LOCAL_SET : Localidx -> Admininstr
 | LOCAL_TEE : Localidx -> Admininstr
 | GLOBAL_GET : Globalidx -> Admininstr
 | GLOBAL_SET : Globalidx -> Admininstr
 | TABLE_GET : Tableidx -> Admininstr
 | TABLE_SET : Tableidx -> Admininstr
 | TABLE_SIZE : Tableidx -> Admininstr
 | TABLE_GROW : Tableidx -> Admininstr
 | TABLE_FILL : Tableidx -> Admininstr
 | TABLE_COPY : (Tableidx × Tableidx) -> Admininstr
 | TABLE_INIT : (Tableidx × Elemidx) -> Admininstr
 | ELEM_DROP : Elemidx -> Admininstr
 | MEMORY_SIZE : Admininstr
 | MEMORY_GROW : Admininstr
 | MEMORY_FILL : Admininstr
 | MEMORY_COPY : Admininstr
 | MEMORY_INIT : Dataidx -> Admininstr
 | DATA_DROP : Dataidx -> Admininstr
 | LOAD : (Numtype × (Option (N × Sx)) × U32 × U32) -> Admininstr
 | STORE : (Numtype × (Option N) × U32 × U32) -> Admininstr
 | REF_FUNC_ADDR : Funcaddr -> Admininstr
 | REF_HOST_ADDR : Hostaddr -> Admininstr
 | CALL_ADDR : Funcaddr -> Admininstr
 | LABEL_ : (N × (List Instr) × (List Admininstr)) -> Admininstr
 | FRAME_ : (N × Frame × (List Admininstr)) -> Admininstr
 | TRAP : Admininstr
  deriving Inhabited, BEq

def «$admininstr_globalinst» : Globalinst -> Admininstr
  | (Val.CONST (x0, x1)) => (Admininstr.CONST (x0, x1))
  | (Val.REF_NULL x) => (Admininstr.REF_NULL x)
  | (Val.REF_FUNC_ADDR x) => (Admininstr.REF_FUNC_ADDR x)
  | (Val.REF_HOST_ADDR x) => (Admininstr.REF_HOST_ADDR x)

def «$admininstr_instr» : Instr -> Admininstr
  | Instr.UNREACHABLE => Admininstr.UNREACHABLE
  | Instr.NOP => Admininstr.NOP
  | Instr.DROP => Admininstr.DROP
  | (Instr.SELECT x) => (Admininstr.SELECT x)
  | (Instr.BLOCK (x0, x1)) => (Admininstr.BLOCK (x0, x1))
  | (Instr.LOOP (x0, x1)) => (Admininstr.LOOP (x0, x1))
  | (Instr.IF (x0, x1, x2)) => (Admininstr.IF (x0, x1, x2))
  | (Instr.BR x) => (Admininstr.BR x)
  | (Instr.BR_IF x) => (Admininstr.BR_IF x)
  | (Instr.BR_TABLE (x0, x1)) => (Admininstr.BR_TABLE (x0, x1))
  | (Instr.CALL x) => (Admininstr.CALL x)
  | (Instr.CALL_INDIRECT (x0, x1)) => (Admininstr.CALL_INDIRECT (x0, x1))
  | Instr.RETURN => Admininstr.RETURN
  | (Instr.CONST (x0, x1)) => (Admininstr.CONST (x0, x1))
  | (Instr.UNOP (x0, x1)) => (Admininstr.UNOP (x0, x1))
  | (Instr.BINOP (x0, x1)) => (Admininstr.BINOP (x0, x1))
  | (Instr.TESTOP (x0, x1)) => (Admininstr.TESTOP (x0, x1))
  | (Instr.RELOP (x0, x1)) => (Admininstr.RELOP (x0, x1))
  | (Instr.EXTEND (x0, x1)) => (Admininstr.EXTEND (x0, x1))
  | (Instr.CVTOP (x0, x1, x2, x3)) => (Admininstr.CVTOP (x0, x1, x2, x3))
  | (Instr.REF_NULL x) => (Admininstr.REF_NULL x)
  | (Instr.REF_FUNC x) => (Admininstr.REF_FUNC x)
  | Instr.REF_IS_NULL => Admininstr.REF_IS_NULL
  | (Instr.LOCAL_GET x) => (Admininstr.LOCAL_GET x)
  | (Instr.LOCAL_SET x) => (Admininstr.LOCAL_SET x)
  | (Instr.LOCAL_TEE x) => (Admininstr.LOCAL_TEE x)
  | (Instr.GLOBAL_GET x) => (Admininstr.GLOBAL_GET x)
  | (Instr.GLOBAL_SET x) => (Admininstr.GLOBAL_SET x)
  | (Instr.TABLE_GET x) => (Admininstr.TABLE_GET x)
  | (Instr.TABLE_SET x) => (Admininstr.TABLE_SET x)
  | (Instr.TABLE_SIZE x) => (Admininstr.TABLE_SIZE x)
  | (Instr.TABLE_GROW x) => (Admininstr.TABLE_GROW x)
  | (Instr.TABLE_FILL x) => (Admininstr.TABLE_FILL x)
  | (Instr.TABLE_COPY (x0, x1)) => (Admininstr.TABLE_COPY (x0, x1))
  | (Instr.TABLE_INIT (x0, x1)) => (Admininstr.TABLE_INIT (x0, x1))
  | (Instr.ELEM_DROP x) => (Admininstr.ELEM_DROP x)
  | Instr.MEMORY_SIZE => Admininstr.MEMORY_SIZE
  | Instr.MEMORY_GROW => Admininstr.MEMORY_GROW
  | Instr.MEMORY_FILL => Admininstr.MEMORY_FILL
  | Instr.MEMORY_COPY => Admininstr.MEMORY_COPY
  | (Instr.MEMORY_INIT x) => (Admininstr.MEMORY_INIT x)
  | (Instr.DATA_DROP x) => (Admininstr.DATA_DROP x)
  | (Instr.LOAD (x0, x1, x2, x3)) => (Admininstr.LOAD (x0, x1, x2, x3))
  | (Instr.STORE (x0, x1, x2, x3)) => (Admininstr.STORE (x0, x1, x2, x3))

def «$admininstr_ref» : Ref -> Admininstr
  | (Ref.REF_NULL x) => (Admininstr.REF_NULL x)
  | (Ref.REF_FUNC_ADDR x) => (Admininstr.REF_FUNC_ADDR x)
  | (Ref.REF_HOST_ADDR x) => (Admininstr.REF_HOST_ADDR x)

def «$admininstr_val» : Val -> Admininstr
  | (Val.CONST (x0, x1)) => (Admininstr.CONST (x0, x1))
  | (Val.REF_NULL x) => (Admininstr.REF_NULL x)
  | (Val.REF_FUNC_ADDR x) => (Admininstr.REF_FUNC_ADDR x)
  | (Val.REF_HOST_ADDR x) => (Admininstr.REF_HOST_ADDR x)

@[reducible] def Config := /- mixop: `%;%*` -/ (State × (List Admininstr))



def «$funcaddr» : State -> (List Funcaddr)
  | (s, f) => f.MODULE.FUNC



def «$funcinst» : State -> (List Funcinst)
  | (s, f) => s.FUNC



def «$func» : (State × Funcidx) -> Funcinst
  | ((s, f), x) => (s.FUNC.get! (f.MODULE.FUNC.get! x))



def «$global» : (State × Globalidx) -> Globalinst
  | ((s, f), x) => (s.GLOBAL.get! (f.MODULE.GLOBAL.get! x))



def «$table» : (State × Tableidx) -> Tableinst
  | ((s, f), x) => (s.TABLE.get! (f.MODULE.TABLE.get! x))



def «$mem» : (State × Memidx) -> Meminst
  | ((s, f), x) => (s.MEM.get! (f.MODULE.MEM.get! x))



def «$elem» : (State × Tableidx) -> Eleminst
  | ((s, f), x) => (s.ELEM.get! (f.MODULE.ELEM.get! x))



def «$data» : (State × Dataidx) -> Datainst
  | ((s, f), x) => (s.DATA.get! (f.MODULE.DATA.get! x))



def «$local» : (State × Localidx) -> Val
  | ((s, f), x) => (f.LOCAL.get! x)



def «$with_local» : (State × Localidx × Val) -> State
  | ((s, f), x, v) => (s, {f with LOCAL := (f.LOCAL.upd x v) })



def «$with_global» : (State × Globalidx × Val) -> State
  | ((s, f), x, v) => ({s with GLOBAL := (s.GLOBAL.upd (f.MODULE.GLOBAL.get! x) v) }, f)



def «$with_table» : (State × Tableidx × Nat × Ref) -> State
  | ((s, f), x, i, r) => ({s with TABLE := (s.TABLE.upd (f.MODULE.TABLE.get! x) ((s.TABLE.get! (f.MODULE.TABLE.get! x)).upd i r)) }, f)



def «$with_tableext» : (State × Tableidx × (List Ref)) -> State
  | ((s, f), x, r) => ({s with TABLE := (s.TABLE.upd (f.MODULE.TABLE.get! x) (List.append (s.TABLE.get! (f.MODULE.TABLE.get! x)) r)) }, f)



def «$with_mem» : (State × Tableidx × Nat × Nat × (List Byte)) -> State
  | ((s, f), x, i, j, b) => ({s with MEM := (s.MEM.upd (f.MODULE.MEM.get! x) ((s.MEM.get! (f.MODULE.MEM.get! x)).upds i j b)) }, f)



def «$with_memext» : (State × Tableidx × (List Byte)) -> State
  | ((s, f), x, b) => ({s with MEM := (s.MEM.upd (f.MODULE.MEM.get! x) (List.append (s.MEM.get! (f.MODULE.MEM.get! x)) b)) }, f)



def «$with_elem» : (State × Elemidx × (List Ref)) -> State
  | ((s, f), x, r) => ({s with ELEM := (s.ELEM.upd (f.MODULE.ELEM.get! x) r) }, f)



def «$with_data» : (State × Dataidx × (List Byte)) -> State
  | ((s, f), x, b) => ({s with DATA := (s.DATA.upd (f.MODULE.DATA.get! x) b) }, f)





inductive E where
 | _HOLE : E
 | _SEQ : ((List Val) × E × (List Instr)) -> E
 | LABEL_ : (N × (List Instr) × E) -> E
  deriving Inhabited, BEq



def «$unop» : (Unop_numtype × Numtype × C_numtype) -> (List C_numtype) := default



def «$binop» : (Binop_numtype × Numtype × C_numtype × C_numtype) -> (List C_numtype) := default



def «$testop» : (Testop_numtype × Numtype × C_numtype) -> C_numtype := default



def «$relop» : (Relop_numtype × Numtype × C_numtype × C_numtype) -> C_numtype := default



def «$ext» : (Nat × Nat × Sx × C_numtype) -> C_numtype := default



def «$cvtop» : (Numtype × Cvtop × Numtype × (Option Sx) × C_numtype) -> (List C_numtype) := default



def «$wrap_» : ((Nat × Nat) × C_numtype) -> Nat := default

def «$bytes_» : (Nat × C_numtype) -> (List Byte) := default

inductive Step_pure_before_ref_is_null_false : (List Admininstr) -> Prop where
  | ref_is_null_true (rt : Reftype) (val : Val) : 
    (val == (Val.REF_NULL rt)) -> 
    (Step_pure_before_ref_is_null_false [(«$admininstr_val» val), Admininstr.REF_IS_NULL])

inductive Step_pure : ((List Admininstr) × (List Admininstr)) -> Prop where
  | unreachable  : 
    (Step_pure ([Admininstr.UNREACHABLE], [Admininstr.TRAP]))
  | nop  : 
    (Step_pure ([Admininstr.NOP], []))
  | drop (val : Val) : 
    (Step_pure ([(«$admininstr_val» val), Admininstr.DROP], []))
  | select_true (c : C_numtype) (t : (Option Valtype)) (val_1 : Val) (val_2 : Val) : 
    (c != 0) -> 
    (Step_pure ([(«$admininstr_val» val_1), («$admininstr_val» val_2), (Admininstr.CONST (Numtype.I32, c)), (Admininstr.SELECT t)], [(«$admininstr_val» val_1)]))
  | select_false (c : C_numtype) (t : (Option Valtype)) (val_1 : Val) (val_2 : Val) : 
    (c == 0) -> 
    (Step_pure ([(«$admininstr_val» val_1), («$admininstr_val» val_2), (Admininstr.CONST (Numtype.I32, c)), (Admininstr.SELECT t)], [(«$admininstr_val» val_2)]))
  | block (bt : Blocktype) (instr : (List Instr)) (k : Nat) (n : N) (t_1 : (List Valtype)) (t_2 : (List Valtype)) (val : (List Val)) : 
    (bt == (t_1, t_2)) -> 
    (Step_pure (((List.map «$admininstr_val» val) ++ [(Admininstr.BLOCK (bt, instr))]), [(Admininstr.LABEL_ (n, [], ((List.map «$admininstr_val» val) ++ (List.map «$admininstr_instr» instr))))]))
  | loop (bt : Blocktype) (instr : (List Instr)) (k : Nat) (n : N) (t_1 : (List Valtype)) (t_2 : (List Valtype)) (val : (List Val)) : 
    (bt == (t_1, t_2)) -> 
    (Step_pure (((List.map «$admininstr_val» val) ++ [(Admininstr.LOOP (bt, instr))]), [(Admininstr.LABEL_ (k, [(Instr.LOOP (bt, instr))], ((List.map «$admininstr_val» val) ++ (List.map «$admininstr_instr» instr))))]))
  | if_true (bt : Blocktype) (c : C_numtype) (instr_1 : (List Instr)) (instr_2 : (List Instr)) : 
    (c != 0) -> 
    (Step_pure ([(Admininstr.CONST (Numtype.I32, c)), (Admininstr.IF (bt, instr_1, instr_2))], [(Admininstr.BLOCK (bt, instr_1))]))
  | if_false (bt : Blocktype) (c : C_numtype) (instr_1 : (List Instr)) (instr_2 : (List Instr)) : 
    (c == 0) -> 
    (Step_pure ([(Admininstr.CONST (Numtype.I32, c)), (Admininstr.IF (bt, instr_1, instr_2))], [(Admininstr.BLOCK (bt, instr_2))]))
  | label_vals (instr : (List Instr)) (n : N) (val : (List Val)) : 
    (Step_pure ([(Admininstr.LABEL_ (n, instr, (List.map «$admininstr_val» val)))], (List.map «$admininstr_val» val)))
  | br_zero (instr : (List Instr)) (instr' : (List Instr)) (n : N) (val : (List Val)) (val' : (List Val)) : 
    (Step_pure ([(Admininstr.LABEL_ (n, instr', ((List.map «$admininstr_val» val') ++ ((List.map «$admininstr_val» val) ++ ([(Admininstr.BR 0)] ++ (List.map «$admininstr_instr» instr))))))], ((List.map «$admininstr_val» val) ++ (List.map «$admininstr_instr» instr'))))
  | br_succ (instr : (List Instr)) (instr' : (List Instr)) (l : Labelidx) (n : N) (val : (List Val)) : 
    (Step_pure ([(Admininstr.LABEL_ (n, instr', ((List.map «$admininstr_val» val) ++ ([(Admininstr.BR (l + 1))] ++ (List.map «$admininstr_instr» instr)))))], ((List.map «$admininstr_val» val) ++ [(Admininstr.BR l)])))
  | br_if_true (c : C_numtype) (l : Labelidx) : 
    (c != 0) -> 
    (Step_pure ([(Admininstr.CONST (Numtype.I32, c)), (Admininstr.BR_IF l)], [(Admininstr.BR l)]))
  | br_if_false (c : C_numtype) (l : Labelidx) : 
    (c == 0) -> 
    (Step_pure ([(Admininstr.CONST (Numtype.I32, c)), (Admininstr.BR_IF l)], []))
  | br_table_lt (i : Nat) (l : (List Labelidx)) (l' : Labelidx) : 
    (i < l.length) -> 
    (Step_pure ([(Admininstr.CONST (Numtype.I32, i)), (Admininstr.BR_TABLE (l, l'))], [(Admininstr.BR (l.get! i))]))
  | br_table_ge (i : Nat) (l : (List Labelidx)) (l' : Labelidx) : 
    (i >= l.length) -> 
    (Step_pure ([(Admininstr.CONST (Numtype.I32, i)), (Admininstr.BR_TABLE (l, l'))], [(Admininstr.BR l')]))
  | frame_vals (f : Frame) (n : N) (val : (List Val)) : 
    (Step_pure ([(Admininstr.FRAME_ (n, f, (List.map «$admininstr_val» val)))], (List.map «$admininstr_val» val)))
  | return_frame (f : Frame) (instr : (List Instr)) (n : N) (val : (List Val)) (val' : (List Val)) : 
    (Step_pure ([(Admininstr.FRAME_ (n, f, ((List.map «$admininstr_val» val') ++ ((List.map «$admininstr_val» val) ++ ([Admininstr.RETURN] ++ (List.map «$admininstr_instr» instr))))))], (List.map «$admininstr_val» val)))
  | return_label (instr : (List Instr)) (instr' : (List Instr)) (k : Nat) (val : (List Val)) : 
    (Step_pure ([(Admininstr.LABEL_ (k, instr', ((List.map «$admininstr_val» val) ++ ([Admininstr.RETURN] ++ (List.map «$admininstr_instr» instr)))))], ((List.map «$admininstr_val» val) ++ [Admininstr.RETURN])))
  | unop_val (c : C_numtype) (c_1 : C_numtype) (nt : Numtype) (unop : Unop_numtype) : 
    ((«$unop» (unop, nt, c_1)) == [c]) -> 
    (Step_pure ([(Admininstr.CONST (nt, c_1)), (Admininstr.UNOP (nt, unop))], [(Admininstr.CONST (nt, c))]))
  | unop_trap (c_1 : C_numtype) (nt : Numtype) (unop : Unop_numtype) : 
    ((«$unop» (unop, nt, c_1)) == []) -> 
    (Step_pure ([(Admininstr.CONST (nt, c_1)), (Admininstr.UNOP (nt, unop))], [Admininstr.TRAP]))
  | binop_val (binop : Binop_numtype) (c : C_numtype) (c_1 : C_numtype) (c_2 : C_numtype) (nt : Numtype) : 
    ((«$binop» (binop, nt, c_1, c_2)) == [c]) -> 
    (Step_pure ([(Admininstr.CONST (nt, c_1)), (Admininstr.CONST (nt, c_2)), (Admininstr.BINOP (nt, binop))], [(Admininstr.CONST (nt, c))]))
  | binop_trap (binop : Binop_numtype) (c_1 : C_numtype) (c_2 : C_numtype) (nt : Numtype) : 
    ((«$binop» (binop, nt, c_1, c_2)) == []) -> 
    (Step_pure ([(Admininstr.CONST (nt, c_1)), (Admininstr.CONST (nt, c_2)), (Admininstr.BINOP (nt, binop))], [Admininstr.TRAP]))
  | testop (c : C_numtype) (c_1 : C_numtype) (nt : Numtype) (testop : Testop_numtype) : 
    (c == («$testop» (testop, nt, c_1))) -> 
    (Step_pure ([(Admininstr.CONST (nt, c_1)), (Admininstr.TESTOP (nt, testop))], [(Admininstr.CONST (Numtype.I32, c))]))
  | relop (c : C_numtype) (c_1 : C_numtype) (c_2 : C_numtype) (nt : Numtype) (relop : Relop_numtype) : 
    (c == («$relop» (relop, nt, c_1, c_2))) -> 
    (Step_pure ([(Admininstr.CONST (nt, c_1)), (Admininstr.CONST (nt, c_2)), (Admininstr.RELOP (nt, relop))], [(Admininstr.CONST (Numtype.I32, c))]))
  | extend (c : C_numtype) (n : N) (nt : Numtype) (o0 : Nat) : 
    ((«$size» («$valtype_numtype» nt)) == (some o0)) -> 
    (Step_pure ([(Admininstr.CONST (nt, c)), (Admininstr.EXTEND (nt, n))], [(Admininstr.CONST (nt, («$ext» (n, o0, Sx.S, c))))]))
  | cvtop_val (c : C_numtype) (c_1 : C_numtype) (cvtop : Cvtop) (nt_1 : Numtype) (nt_2 : Numtype) (sx : (Option Sx)) : 
    ((«$cvtop» (nt_1, cvtop, nt_2, sx, c_1)) == [c]) -> 
    (Step_pure ([(Admininstr.CONST (nt_1, c_1)), (Admininstr.CVTOP (nt_2, cvtop, nt_1, sx))], [(Admininstr.CONST (nt_2, c))]))
  | cvtop_trap (c_1 : C_numtype) (cvtop : Cvtop) (nt_1 : Numtype) (nt_2 : Numtype) (sx : (Option Sx)) : 
    ((«$cvtop» (nt_1, cvtop, nt_2, sx, c_1)) == []) -> 
    (Step_pure ([(Admininstr.CONST (nt_1, c_1)), (Admininstr.CVTOP (nt_2, cvtop, nt_1, sx))], [Admininstr.TRAP]))
  | ref_is_null_true (rt : Reftype) (val : Val) : 
    (val == (Val.REF_NULL rt)) -> 
    (Step_pure ([(«$admininstr_val» val), Admininstr.REF_IS_NULL], [(Admininstr.CONST (Numtype.I32, 1))]))
  | ref_is_null_false (val : Val) : 
    (Not (Step_pure_before_ref_is_null_false [(«$admininstr_val» val), Admininstr.REF_IS_NULL])) -> 
    (Step_pure ([(«$admininstr_val» val), Admininstr.REF_IS_NULL], [(Admininstr.CONST (Numtype.I32, 0))]))
  | local_tee (val : Val) (x : Idx) : 
    (Step_pure ([(«$admininstr_val» val), (Admininstr.LOCAL_TEE x)], [(«$admininstr_val» val), («$admininstr_val» val), (Admininstr.LOCAL_SET x)]))

inductive Step_read_before_call_indirect_trap : Config -> Prop where
  | call_indirect_call (a : Addr) (ft : Functype) (ft' : Functype) (i : Nat) (instr : (List Instr)) (m : Moduleinst) (t : (List Valtype)) (x : Idx) (z : State) : 
    (i < («$table» (z, x)).length) -> 
    (a < («$funcinst» z).length) -> 
    (((«$table» (z, x)).get! i) == (Ref.REF_FUNC_ADDR a)) -> 
    (((«$funcinst» z).get! a) == (m, (ft', t, instr))) -> 
    (ft == ft') -> 
    (Step_read_before_call_indirect_trap (z, [(Admininstr.CONST (Numtype.I32, i)), (Admininstr.CALL_INDIRECT (x, ft))]))

inductive Step_read_before_table_fill_zero : Config -> Prop where
  | table_fill_trap (i : Nat) (n : N) (val : Val) (x : Idx) (z : State) : 
    ((i + n) > («$table» (z, x)).length) -> 
    (Step_read_before_table_fill_zero (z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_FILL x)]))

inductive Step_read_before_table_fill_succ : Config -> Prop where
  | table_fill_zero (i : Nat) (n : N) (val : Val) (x : Idx) (z : State) : 
    (Not (Step_read_before_table_fill_zero (z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_FILL x)]))) -> 
    (n == 0) -> 
    (Step_read_before_table_fill_succ (z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_FILL x)]))
  | table_fill_trap (i : Nat) (n : N) (val : Val) (x : Idx) (z : State) : 
    ((i + n) > («$table» (z, x)).length) -> 
    (Step_read_before_table_fill_succ (z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_FILL x)]))

inductive Step_read_before_table_copy_zero : Config -> Prop where
  | table_copy_trap (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > («$table» (z, y)).length) || ((j + n) > («$table» (z, x)).length)) -> 
    (Step_read_before_table_copy_zero (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_COPY (x, y))]))

inductive Step_read_before_table_copy_le : Config -> Prop where
  | table_copy_zero (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (Not (Step_read_before_table_copy_zero (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_COPY (x, y))]))) -> 
    (n == 0) -> 
    (Step_read_before_table_copy_le (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_COPY (x, y))]))
  | table_copy_trap (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > («$table» (z, y)).length) || ((j + n) > («$table» (z, x)).length)) -> 
    (Step_read_before_table_copy_le (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_COPY (x, y))]))

inductive Step_read_before_table_copy_gt : Config -> Prop where
  | table_copy_le (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (Not (Step_read_before_table_copy_le (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_COPY (x, y))]))) -> 
    (j <= i) -> 
    (Step_read_before_table_copy_gt (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_COPY (x, y))]))
  | table_copy_zero (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (Not (Step_read_before_table_copy_zero (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_COPY (x, y))]))) -> 
    (n == 0) -> 
    (Step_read_before_table_copy_gt (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_COPY (x, y))]))
  | table_copy_trap (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > («$table» (z, y)).length) || ((j + n) > («$table» (z, x)).length)) -> 
    (Step_read_before_table_copy_gt (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_COPY (x, y))]))

inductive Step_read_before_table_init_zero : Config -> Prop where
  | table_init_trap (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > («$elem» (z, y)).length) || ((j + n) > («$table» (z, x)).length)) -> 
    (Step_read_before_table_init_zero (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_INIT (x, y))]))

inductive Step_read_before_table_init_succ : Config -> Prop where
  | table_init_zero (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (Not (Step_read_before_table_init_zero (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_INIT (x, y))]))) -> 
    (n == 0) -> 
    (Step_read_before_table_init_succ (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_INIT (x, y))]))
  | table_init_trap (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > («$elem» (z, y)).length) || ((j + n) > («$table» (z, x)).length)) -> 
    (Step_read_before_table_init_succ (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_INIT (x, y))]))

inductive Step_read_before_memory_fill_zero : Config -> Prop where
  | memory_fill_trap (i : Nat) (n : N) (val : Val) (z : State) : 
    ((i + n) > («$mem» (z, 0)).length) -> 
    (Step_read_before_memory_fill_zero (z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_FILL]))

inductive Step_read_before_memory_fill_succ : Config -> Prop where
  | memory_fill_zero (i : Nat) (n : N) (val : Val) (z : State) : 
    (Not (Step_read_before_memory_fill_zero (z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_FILL]))) -> 
    (n == 0) -> 
    (Step_read_before_memory_fill_succ (z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_FILL]))
  | memory_fill_trap (i : Nat) (n : N) (val : Val) (z : State) : 
    ((i + n) > («$mem» (z, 0)).length) -> 
    (Step_read_before_memory_fill_succ (z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_FILL]))

inductive Step_read_before_memory_copy_zero : Config -> Prop where
  | memory_copy_trap (i : Nat) (j : Nat) (n : N) (z : State) : 
    (((i + n) > («$mem» (z, 0)).length) || ((j + n) > («$mem» (z, 0)).length)) -> 
    (Step_read_before_memory_copy_zero (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_COPY]))

inductive Step_read_before_memory_copy_le : Config -> Prop where
  | memory_copy_zero (i : Nat) (j : Nat) (n : N) (z : State) : 
    (Not (Step_read_before_memory_copy_zero (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_COPY]))) -> 
    (n == 0) -> 
    (Step_read_before_memory_copy_le (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_COPY]))
  | memory_copy_trap (i : Nat) (j : Nat) (n : N) (z : State) : 
    (((i + n) > («$mem» (z, 0)).length) || ((j + n) > («$mem» (z, 0)).length)) -> 
    (Step_read_before_memory_copy_le (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_COPY]))

inductive Step_read_before_memory_copy_gt : Config -> Prop where
  | memory_copy_le (i : Nat) (j : Nat) (n : N) (z : State) : 
    (Not (Step_read_before_memory_copy_le (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_COPY]))) -> 
    (j <= i) -> 
    (Step_read_before_memory_copy_gt (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_COPY]))
  | memory_copy_zero (i : Nat) (j : Nat) (n : N) (z : State) : 
    (Not (Step_read_before_memory_copy_zero (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_COPY]))) -> 
    (n == 0) -> 
    (Step_read_before_memory_copy_gt (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_COPY]))
  | memory_copy_trap (i : Nat) (j : Nat) (n : N) (z : State) : 
    (((i + n) > («$mem» (z, 0)).length) || ((j + n) > («$mem» (z, 0)).length)) -> 
    (Step_read_before_memory_copy_gt (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_COPY]))

inductive Step_read_before_memory_init_zero : Config -> Prop where
  | memory_init_trap (i : Nat) (j : Nat) (n : N) (x : Idx) (z : State) : 
    (((i + n) > («$data» (z, x)).length) || ((j + n) > («$mem» (z, 0)).length)) -> 
    (Step_read_before_memory_init_zero (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.MEMORY_INIT x)]))

inductive Step_read_before_memory_init_succ : Config -> Prop where
  | memory_init_zero (i : Nat) (j : Nat) (n : N) (x : Idx) (z : State) : 
    (Not (Step_read_before_memory_init_zero (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.MEMORY_INIT x)]))) -> 
    (n == 0) -> 
    (Step_read_before_memory_init_succ (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.MEMORY_INIT x)]))
  | memory_init_trap (i : Nat) (j : Nat) (n : N) (x : Idx) (z : State) : 
    (((i + n) > («$data» (z, x)).length) || ((j + n) > («$mem» (z, 0)).length)) -> 
    (Step_read_before_memory_init_succ (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.MEMORY_INIT x)]))

inductive Step_read : (Config × (List Admininstr)) -> Prop where
  | call (x : Idx) (z : State) : 
    (x < («$funcaddr» z).length) -> 
    (Step_read ((z, [(Admininstr.CALL x)]), [(Admininstr.CALL_ADDR ((«$funcaddr» z).get! x))]))
  | call_indirect_call (a : Addr) (ft : Functype) (ft' : Functype) (i : Nat) (instr : (List Instr)) (m : Moduleinst) (t : (List Valtype)) (x : Idx) (z : State) : 
    (i < («$table» (z, x)).length) -> 
    (a < («$funcinst» z).length) -> 
    (((«$table» (z, x)).get! i) == (Ref.REF_FUNC_ADDR a)) -> 
    (((«$funcinst» z).get! a) == (m, (ft', t, instr))) -> 
    (ft == ft') -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, i)), (Admininstr.CALL_INDIRECT (x, ft))]), [(Admininstr.CALL_ADDR a)]))
  | call_indirect_trap (ft : Functype) (i : Nat) (x : Idx) (z : State) : 
    (Not (Step_read_before_call_indirect_trap (z, [(Admininstr.CONST (Numtype.I32, i)), (Admininstr.CALL_INDIRECT (x, ft))]))) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, i)), (Admininstr.CALL_INDIRECT (x, ft))]), [Admininstr.TRAP]))
  | call_addr (a : Addr) (f : Frame) (instr : (List Instr)) (k : Nat) (m : Moduleinst) (n : N) (t : (List Valtype)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) (val : (List Val)) (z : State) (o0 : (List Val)) : 
    (t.length == o0.length) -> 
    (a < («$funcinst» z).length) -> 
    (Forall₂ (λ t o0 ↦ ((«$default_» t) == (some o0))) t o0) -> 
    (((«$funcinst» z).get! a) == (m, ((t_1, t_2), t, instr))) -> 
    (f == {LOCAL := (val ++ o0), MODULE := m}) -> 
    (Step_read ((z, ((List.map «$admininstr_val» val) ++ [(Admininstr.CALL_ADDR a)])), [(Admininstr.FRAME_ (n, f, [(Admininstr.LABEL_ (n, [], (List.map «$admininstr_instr» instr)))]))]))
  | ref_func (x : Idx) (z : State) : 
    (x < («$funcaddr» z).length) -> 
    (Step_read ((z, [(Admininstr.REF_FUNC x)]), [(Admininstr.REF_FUNC_ADDR ((«$funcaddr» z).get! x))]))
  | local_get (x : Idx) (z : State) : 
    (Step_read ((z, [(Admininstr.LOCAL_GET x)]), [(«$admininstr_val» («$local» (z, x)))]))
  | global_get (x : Idx) (z : State) : 
    (Step_read ((z, [(Admininstr.GLOBAL_GET x)]), [(«$admininstr_globalinst» («$global» (z, x)))]))
  | table_get_trap (i : Nat) (x : Idx) (z : State) : 
    (i >= («$table» (z, x)).length) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, i)), (Admininstr.TABLE_GET x)]), [Admininstr.TRAP]))
  | table_get_val (i : Nat) (x : Idx) (z : State) : 
    (i < («$table» (z, x)).length) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, i)), (Admininstr.TABLE_GET x)]), [(«$admininstr_ref» ((«$table» (z, x)).get! i))]))
  | table_size (n : N) (x : Idx) (z : State) : 
    ((«$table» (z, x)).length == n) -> 
    (Step_read ((z, [(Admininstr.TABLE_SIZE x)]), [(Admininstr.CONST (Numtype.I32, n))]))
  | table_fill_trap (i : Nat) (n : N) (val : Val) (x : Idx) (z : State) : 
    ((i + n) > («$table» (z, x)).length) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_FILL x)]), [Admininstr.TRAP]))
  | table_fill_zero (i : Nat) (n : N) (val : Val) (x : Idx) (z : State) : 
    (Not (Step_read_before_table_fill_zero (z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_FILL x)]))) -> 
    (n == 0) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_FILL x)]), []))
  | table_fill_succ (i : Nat) (n : N) (val : Val) (x : Idx) (z : State) : 
    (Not (Step_read_before_table_fill_succ (z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_FILL x)]))) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_FILL x)]), [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.TABLE_SET x), (Admininstr.CONST (Numtype.I32, (i + 1))), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, (n - 1))), (Admininstr.TABLE_FILL x)]))
  | table_copy_trap (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > («$table» (z, y)).length) || ((j + n) > («$table» (z, x)).length)) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_COPY (x, y))]), [Admininstr.TRAP]))
  | table_copy_zero (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (Not (Step_read_before_table_copy_zero (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_COPY (x, y))]))) -> 
    (n == 0) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_COPY (x, y))]), []))
  | table_copy_le (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (Not (Step_read_before_table_copy_le (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_COPY (x, y))]))) -> 
    (j <= i) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_COPY (x, y))]), [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.TABLE_GET y), (Admininstr.TABLE_SET x), (Admininstr.CONST (Numtype.I32, (j + 1))), (Admininstr.CONST (Numtype.I32, (i + 1))), (Admininstr.CONST (Numtype.I32, (n - 1))), (Admininstr.TABLE_COPY (x, y))]))
  | table_copy_gt (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (Not (Step_read_before_table_copy_gt (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_COPY (x, y))]))) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_COPY (x, y))]), [(Admininstr.CONST (Numtype.I32, ((j + n) - 1))), (Admininstr.CONST (Numtype.I32, ((i + n) - 1))), (Admininstr.TABLE_GET y), (Admininstr.TABLE_SET x), (Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, (n - 1))), (Admininstr.TABLE_COPY (x, y))]))
  | table_init_trap (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > («$elem» (z, y)).length) || ((j + n) > («$table» (z, x)).length)) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_INIT (x, y))]), [Admininstr.TRAP]))
  | table_init_zero (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (Not (Step_read_before_table_init_zero (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_INIT (x, y))]))) -> 
    (n == 0) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_INIT (x, y))]), []))
  | table_init_succ (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (i < («$elem» (z, y)).length) -> 
    (Not (Step_read_before_table_init_succ (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_INIT (x, y))]))) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_INIT (x, y))]), [(Admininstr.CONST (Numtype.I32, j)), («$admininstr_ref» ((«$elem» (z, y)).get! i)), (Admininstr.TABLE_SET x), (Admininstr.CONST (Numtype.I32, (j + 1))), (Admininstr.CONST (Numtype.I32, (i + 1))), (Admininstr.CONST (Numtype.I32, (n - 1))), (Admininstr.TABLE_INIT (x, y))]))
  | load_num_trap (i : Nat) (n_A : N) (n_O : N) (nt : Numtype) (z : State) (o0 : Nat) : 
    ((«$size» («$valtype_numtype» nt)) == (some o0)) -> 
    (((i + n_O) + (((Nat.div o0) 8))) > («$mem» (z, 0)).length) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, i)), (Admininstr.LOAD (nt, none, n_A, n_O))]), [Admininstr.TRAP]))
  | load_num_val (c : C_numtype) (i : Nat) (n_A : N) (n_O : N) (nt : Numtype) (z : State) (o0 : Nat) (o1 : Nat) : 
    ((«$size» («$valtype_numtype» nt)) == (some o0)) -> 
    ((«$size» («$valtype_numtype» nt)) == (some o1)) -> 
    ((«$bytes_» (o0, c)) == ((«$mem» (z, 0)).slice (i + n_O) (((Nat.div o1) 8)))) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, i)), (Admininstr.LOAD (nt, none, n_A, n_O))]), [(Admininstr.CONST (nt, c))]))
  | load_pack_trap (i : Nat) (n : N) (n_A : N) (n_O : N) (nt : Numtype) (sx : Sx) (z : State) : 
    (((i + n_O) + (((Nat.div n) 8))) > («$mem» (z, 0)).length) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, i)), (Admininstr.LOAD (nt, (some (n, sx)), n_A, n_O))]), [Admininstr.TRAP]))
  | load_pack_val (c : C_numtype) (i : Nat) (n : N) (n_A : N) (n_O : N) (nt : Numtype) (sx : Sx) (z : State) (o0 : Nat) : 
    ((«$size» («$valtype_numtype» nt)) == (some o0)) -> 
    ((«$bytes_» (n, c)) == ((«$mem» (z, 0)).slice (i + n_O) (((Nat.div n) 8)))) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, i)), (Admininstr.LOAD (nt, (some (n, sx)), n_A, n_O))]), [(Admininstr.CONST (nt, («$ext» (n, o0, sx, c))))]))
  | memory_size (n : N) (z : State) : 
    (((n * 64) * («$Ki» ())) == («$mem» (z, 0)).length) -> 
    (Step_read ((z, [Admininstr.MEMORY_SIZE]), [(Admininstr.CONST (Numtype.I32, n))]))
  | memory_fill_trap (i : Nat) (n : N) (val : Val) (z : State) : 
    ((i + n) > («$mem» (z, 0)).length) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_FILL]), [Admininstr.TRAP]))
  | memory_fill_zero (i : Nat) (n : N) (val : Val) (z : State) : 
    (Not (Step_read_before_memory_fill_zero (z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_FILL]))) -> 
    (n == 0) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_FILL]), []))
  | memory_fill_succ (i : Nat) (n : N) (val : Val) (z : State) : 
    (Not (Step_read_before_memory_fill_succ (z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_FILL]))) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_FILL]), [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_val» val), (Admininstr.STORE (Numtype.I32, (some 8), 0, 0)), (Admininstr.CONST (Numtype.I32, (i + 1))), («$admininstr_val» val), (Admininstr.CONST (Numtype.I32, (n - 1))), Admininstr.MEMORY_FILL]))
  | memory_copy_trap (i : Nat) (j : Nat) (n : N) (z : State) : 
    (((i + n) > («$mem» (z, 0)).length) || ((j + n) > («$mem» (z, 0)).length)) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_COPY]), [Admininstr.TRAP]))
  | memory_copy_zero (i : Nat) (j : Nat) (n : N) (z : State) : 
    (Not (Step_read_before_memory_copy_zero (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_COPY]))) -> 
    (n == 0) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_COPY]), []))
  | memory_copy_le (i : Nat) (j : Nat) (n : N) (z : State) : 
    (Not (Step_read_before_memory_copy_le (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_COPY]))) -> 
    (j <= i) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_COPY]), [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.LOAD (Numtype.I32, (some (8, Sx.U)), 0, 0)), (Admininstr.STORE (Numtype.I32, (some 8), 0, 0)), (Admininstr.CONST (Numtype.I32, (j + 1))), (Admininstr.CONST (Numtype.I32, (i + 1))), (Admininstr.CONST (Numtype.I32, (n - 1))), Admininstr.MEMORY_COPY]))
  | memory_copy_gt (i : Nat) (j : Nat) (n : N) (z : State) : 
    (Not (Step_read_before_memory_copy_gt (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_COPY]))) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_COPY]), [(Admininstr.CONST (Numtype.I32, ((j + n) - 1))), (Admininstr.CONST (Numtype.I32, ((i + n) - 1))), (Admininstr.LOAD (Numtype.I32, (some (8, Sx.U)), 0, 0)), (Admininstr.STORE (Numtype.I32, (some 8), 0, 0)), (Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, (n - 1))), Admininstr.MEMORY_COPY]))
  | memory_init_trap (i : Nat) (j : Nat) (n : N) (x : Idx) (z : State) : 
    (((i + n) > («$data» (z, x)).length) || ((j + n) > («$mem» (z, 0)).length)) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.MEMORY_INIT x)]), [Admininstr.TRAP]))
  | memory_init_zero (i : Nat) (j : Nat) (n : N) (x : Idx) (z : State) : 
    (Not (Step_read_before_memory_init_zero (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.MEMORY_INIT x)]))) -> 
    (n == 0) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.MEMORY_INIT x)]), []))
  | memory_init_succ (i : Nat) (j : Nat) (n : N) (x : Idx) (z : State) : 
    (i < («$data» (z, x)).length) -> 
    (Not (Step_read_before_memory_init_succ (z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.MEMORY_INIT x)]))) -> 
    (Step_read ((z, [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.MEMORY_INIT x)]), [(Admininstr.CONST (Numtype.I32, j)), (Admininstr.CONST (Numtype.I32, ((«$data» (z, x)).get! i))), (Admininstr.STORE (Numtype.I32, (some 8), 0, 0)), (Admininstr.CONST (Numtype.I32, (j + 1))), (Admininstr.CONST (Numtype.I32, (i + 1))), (Admininstr.CONST (Numtype.I32, (n - 1))), (Admininstr.MEMORY_INIT x)]))

inductive Step : (Config × Config) -> Prop where
  | pure (instr : (List Instr)) (instr' : (List Instr)) (z : State) : 
    (Step_pure ((List.map «$admininstr_instr» instr), (List.map «$admininstr_instr» instr'))) -> 
    (Step ((z, (List.map «$admininstr_instr» instr)), (z, (List.map «$admininstr_instr» instr'))))
  | read (instr : (List Instr)) (instr' : (List Instr)) (z : State) : 
    (Step_read ((z, (List.map «$admininstr_instr» instr)), (List.map «$admininstr_instr» instr'))) -> 
    (Step ((z, (List.map «$admininstr_instr» instr)), (z, (List.map «$admininstr_instr» instr'))))
  | local_set (val : Val) (x : Idx) (z : State) : 
    (Step ((z, [(«$admininstr_val» val), (Admininstr.LOCAL_SET x)]), ((«$with_local» (z, x, val)), [])))
  | global_set (val : Val) (x : Idx) (z : State) : 
    (Step ((z, [(«$admininstr_val» val), (Admininstr.GLOBAL_SET x)]), ((«$with_global» (z, x, val)), [])))
  | table_set_trap (i : Nat) (ref : Ref) (x : Idx) (z : State) : 
    (i >= («$table» (z, x)).length) -> 
    (Step ((z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_ref» ref), (Admininstr.TABLE_GET x)]), (z, [Admininstr.TRAP])))
  | table_set_val (i : Nat) (ref : Ref) (x : Idx) (z : State) : 
    (i < («$table» (z, x)).length) -> 
    (Step ((z, [(Admininstr.CONST (Numtype.I32, i)), («$admininstr_ref» ref), (Admininstr.TABLE_GET x)]), ((«$with_table» (z, x, i, ref)), [])))
  | table_grow_succeed (n : N) (ref : Ref) (x : Idx) (z : State) : 
    (Step ((z, [(«$admininstr_ref» ref), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_GROW x)]), ((«$with_tableext» (z, x, [ref])), [(Admininstr.CONST (Numtype.I32, («$table» (z, x)).length))])))
  | table_grow_fail (n : N) (ref : Ref) (x : Idx) (z : State) : 
    (Step ((z, [(«$admininstr_ref» ref), (Admininstr.CONST (Numtype.I32, n)), (Admininstr.TABLE_GROW x)]), (z, [(Admininstr.CONST (Numtype.I32, (0 - 1)))])))
  | elem_drop (x : Idx) (z : State) : 
    (Step ((z, [(Admininstr.ELEM_DROP x)]), ((«$with_elem» (z, x, [])), [])))
  | store_num_trap (c : C_numtype) (i : Nat) (n_A : N) (n_O : N) (nt : Numtype) (z : State) (o0 : Nat) : 
    ((«$size» («$valtype_numtype» nt)) == (some o0)) -> 
    (((i + n_O) + (((Nat.div o0) 8))) > («$mem» (z, 0)).length) -> 
    (Step ((z, [(Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (nt, c)), (Admininstr.STORE (nt, none, n_A, n_O))]), (z, [Admininstr.TRAP])))
  | store_num_val (b : (List Byte)) (c : C_numtype) (i : Nat) (n_A : N) (n_O : N) (nt : Numtype) (z : State) (o0 : Nat) (o1 : Nat) : 
    ((«$size» («$valtype_numtype» nt)) == (some o0)) -> 
    ((«$size» («$valtype_numtype» nt)) == (some o1)) -> 
    (b == («$bytes_» (o1, c))) -> 
    (Step ((z, [(Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (nt, c)), (Admininstr.STORE (nt, none, n_A, n_O))]), ((«$with_mem» (z, 0, (i + n_O), (((Nat.div o0) 8)), b)), [])))
  | store_pack_trap (c : C_numtype) (i : Nat) (n : N) (n_A : N) (n_O : N) (nt : Numtype) (z : State) : 
    (((i + n_O) + (((Nat.div n) 8))) > («$mem» (z, 0)).length) -> 
    (Step ((z, [(Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (nt, c)), (Admininstr.STORE (nt, (some n), n_A, n_O))]), (z, [Admininstr.TRAP])))
  | store_pack_val (b : (List Byte)) (c : C_numtype) (i : Nat) (n : N) (n_A : N) (n_O : N) (nt : Numtype) (z : State) (o0 : Nat) : 
    ((«$size» («$valtype_numtype» nt)) == (some o0)) -> 
    (b == («$bytes_» (n, («$wrap_» ((o0, n), c))))) -> 
    (Step ((z, [(Admininstr.CONST (Numtype.I32, i)), (Admininstr.CONST (nt, c)), (Admininstr.STORE (nt, (some n), n_A, n_O))]), ((«$with_mem» (z, 0, (i + n_O), (((Nat.div n) 8)), b)), [])))
  | memory_grow_succeed (n : N) (z : State) : 
    (Step ((z, [(Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_GROW]), ((«$with_memext» (z, 0, [0])), [(Admininstr.CONST (Numtype.I32, (((Nat.div («$mem» (z, 0)).length) (64 * («$Ki» ()))))))])))
  | memory_grow_fail (n : N) (z : State) : 
    (Step ((z, [(Admininstr.CONST (Numtype.I32, n)), Admininstr.MEMORY_GROW]), (z, [(Admininstr.CONST (Numtype.I32, (0 - 1)))])))
  | data_drop (x : Idx) (z : State) : 
    (Step ((z, [(Admininstr.DATA_DROP x)]), ((«$with_data» (z, x, [])), [])))






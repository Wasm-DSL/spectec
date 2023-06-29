# Preview

```sh
$ dune exec ../src/exe-watsup/main.exe -- --haskell ../spec/*.watsup -o Test.hs
$ cat Test.hs
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE DuplicateRecordFields #-}
module Test where
import Prelude (Bool, String, undefined, error, Maybe, fromIntegral, (+), (!!))
import Numeric.Natural (Natural)
type N = Natural

type Name = String

type Byte = Natural

type U32 = Natural

type Idx = Natural

type Funcidx = Idx

type Globalidx = Idx

type Tableidx = Idx

type Memidx = Idx

type Elemidx = Idx

type Dataidx = Idx

type Labelidx = Idx

type Localidx = Idx

data Numtype
 = Numtype_I32
 | Numtype_I64
 | Numtype_F32
 | Numtype_F64

data Vectype
 = Vectype_V128

data Reftype
 = Reftype_FUNCREF
 | Reftype_EXTERNREF

data Valtype
 = Valtype_I32
 | Valtype_I64
 | Valtype_F32
 | Valtype_F64
 | Valtype_V128
 | Valtype_FUNCREF
 | Valtype_EXTERNREF
 | Valtype_BOT

valtype_numtype :: Numtype -> Valtype
valtype_numtype Numtype_I32 = Valtype_I32
valtype_numtype Numtype_I64 = Valtype_I64
valtype_numtype Numtype_F32 = Valtype_F32
valtype_numtype Numtype_F64 = Valtype_F64

valtype_vectype :: Vectype -> Valtype
valtype_vectype Vectype_V128 = Valtype_V128

valtype_reftype :: Reftype -> Valtype
valtype_reftype Reftype_FUNCREF = Valtype_FUNCREF
valtype_reftype Reftype_EXTERNREF = Valtype_EXTERNREF

data In
 = In_I32
 | In_I64

numtype_in :: In -> Numtype
numtype_in In_I32 = Numtype_I32
numtype_in In_I64 = Numtype_I64

valtype_in :: In -> Valtype
valtype_in In_I32 = Valtype_I32
valtype_in In_I64 = Valtype_I64

data Fn
 = Fn_F32
 | Fn_F64

numtype_fn :: Fn -> Numtype
numtype_fn Fn_F32 = Numtype_F32
numtype_fn Fn_F64 = Numtype_F64

valtype_fn :: Fn -> Valtype
valtype_fn Fn_F32 = Valtype_F32
valtype_fn Fn_F64 = Valtype_F64

type Resulttype = [Valtype]

type Limits = {- mixop: `[%..%]` -} (U32, U32)

type Mutflag = {- mixop: MUT -} ()

type Globaltype = {- mixop: `%?%` -} ((Maybe Mutflag), Valtype)

type Functype = {- mixop: `%->%` -} (Resulttype, Resulttype)

type Tabletype = {- mixop: `%%` -} (Limits, Reftype)

type Memtype = {- mixop: `%I8` -} Limits

type Elemtype = Reftype

type Datatype = {- mixop: OK -} ()

data Externtype
 = Externtype_GLOBAL Globaltype
 | Externtype_FUNC Functype
 | Externtype_TABLE Tabletype
 | Externtype_MEMORY Memtype

data Sx
 = Sx_U
 | Sx_S

data Unop_IXX
 = Unop_IXX_CLZ
 | Unop_IXX_CTZ
 | Unop_IXX_POPCNT

data Unop_FXX
 = Unop_FXX_ABS
 | Unop_FXX_NEG
 | Unop_FXX_SQRT
 | Unop_FXX_CEIL
 | Unop_FXX_FLOOR
 | Unop_FXX_TRUNC
 | Unop_FXX_NEAREST

data Binop_IXX
 = Binop_IXX_ADD
 | Binop_IXX_SUB
 | Binop_IXX_MUL
 | Binop_IXX_DIV Sx
 | Binop_IXX_REM Sx
 | Binop_IXX_AND
 | Binop_IXX_OR
 | Binop_IXX_XOR
 | Binop_IXX_SHL
 | Binop_IXX_SHR Sx
 | Binop_IXX_ROTL
 | Binop_IXX_ROTR

data Binop_FXX
 = Binop_FXX_ADD
 | Binop_FXX_SUB
 | Binop_FXX_MUL
 | Binop_FXX_DIV
 | Binop_FXX_MIN
 | Binop_FXX_MAX
 | Binop_FXX_COPYSIGN

data Testop_IXX
 = Testop_IXX_EQZ

data Testop_FXX

data Relop_IXX
 = Relop_IXX_EQ
 | Relop_IXX_NE
 | Relop_IXX_LT Sx
 | Relop_IXX_GT Sx
 | Relop_IXX_LE Sx
 | Relop_IXX_GE Sx

data Relop_FXX
 = Relop_FXX_EQ
 | Relop_FXX_NE
 | Relop_FXX_LT
 | Relop_FXX_GT
 | Relop_FXX_LE
 | Relop_FXX_GE

data Unop_numtype
 = Unop_numtype_I Unop_IXX
 | Unop_numtype_F Unop_FXX

data Binop_numtype
 = Binop_numtype_I Binop_IXX
 | Binop_numtype_F Binop_FXX

data Testop_numtype
 = Testop_numtype_I Testop_IXX
 | Testop_numtype_F Testop_FXX

data Relop_numtype
 = Relop_numtype_I Relop_IXX
 | Relop_numtype_F Relop_FXX

data Cvtop
 = Cvtop_CONVERT
 | Cvtop_REINTERPRET

type C_numtype = Natural

type C_vectype = Natural

type Blocktype = Functype

data Instr
 = Instr_UNREACHABLE
 | Instr_NOP
 | Instr_DROP
 | Instr_SELECT (Maybe Valtype)
 | Instr_BLOCK (Blocktype, [Instr])
 | Instr_LOOP (Blocktype, [Instr])
 | Instr_IF (Blocktype, [Instr], [Instr])
 | Instr_BR Labelidx
 | Instr_BR_IF Labelidx
 | Instr_BR_TABLE ([Labelidx], Labelidx)
 | Instr_CALL Funcidx
 | Instr_CALL_INDIRECT (Tableidx, Functype)
 | Instr_RETURN
 | Instr_CONST (Numtype, C_numtype)
 | Instr_UNOP (Numtype, Unop_numtype)
 | Instr_BINOP (Numtype, Binop_numtype)
 | Instr_TESTOP (Numtype, Testop_numtype)
 | Instr_RELOP (Numtype, Relop_numtype)
 | Instr_EXTEND (Numtype, N)
 | Instr_CVTOP (Numtype, Cvtop, Numtype, (Maybe Sx))
 | Instr_REF_NULL Reftype
 | Instr_REF_FUNC Funcidx
 | Instr_REF_IS_NULL
 | Instr_LOCAL_GET Localidx
 | Instr_LOCAL_SET Localidx
 | Instr_LOCAL_TEE Localidx
 | Instr_GLOBAL_GET Globalidx
 | Instr_GLOBAL_SET Globalidx
 | Instr_TABLE_GET Tableidx
 | Instr_TABLE_SET Tableidx
 | Instr_TABLE_SIZE Tableidx
 | Instr_TABLE_GROW Tableidx
 | Instr_TABLE_FILL Tableidx
 | Instr_TABLE_COPY (Tableidx, Tableidx)
 | Instr_TABLE_INIT (Tableidx, Elemidx)
 | Instr_ELEM_DROP Elemidx
 | Instr_MEMORY_SIZE
 | Instr_MEMORY_GROW
 | Instr_MEMORY_FILL
 | Instr_MEMORY_COPY
 | Instr_MEMORY_INIT Dataidx
 | Instr_DATA_DROP Dataidx
 | Instr_LOAD (Numtype, (Maybe (N, Sx)), Natural, Natural)
 | Instr_STORE (Numtype, (Maybe N), Natural, Natural)

type Expr = [Instr]

data Elemmode
 = Elemmode_TABLE (Tableidx, Expr)
 | Elemmode_DECLARE

data Datamode
 = Datamode_MEMORY (Memidx, Expr)

type Func = {- mixop: `FUNC%%*%` -} (Functype, [Valtype], Expr)

type Global = {- mixop: GLOBAL -} (Globaltype, Expr)

type Table = {- mixop: TABLE -} Tabletype

type Mem = {- mixop: MEMORY -} Memtype

type Elem = {- mixop: `ELEM%%*%?` -} (Reftype, [Expr], (Maybe Elemmode))

type Data = {- mixop: `DATA(*)%*%?` -} ([[Byte]], (Maybe Datamode))

type Start = {- mixop: START -} Funcidx

data Externuse
 = Externuse_FUNC Funcidx
 | Externuse_GLOBAL Globalidx
 | Externuse_TABLE Tableidx
 | Externuse_MEMORY Memidx

type Export = {- mixop: EXPORT -} (Name, Externuse)

type Import = {- mixop: IMPORT -} (Name, Name, Externtype)

type Module = {- mixop: `MODULE%*%*%*%*%*%*%*%*%*` -} ([Import], [Func], [Global], [Table], [Mem], [Elem], [Data], [Start], [Export])

size :: Valtype -> Natural
size Valtype_I32 = 32
size Valtype_I64 = 64
size Valtype_F32 = 32
size Valtype_F64 = 64
size Valtype_V128 = 128

test_sub_ATOM_22 :: N -> Natural
test_sub_ATOM_22 n_3_ATOM_y = 0

curried_ :: (N, N) -> Natural
curried_ (n_1, n_2) = (n_1 + n_2)

data Testfuse
 = Testfuse_AB_ (Natural, Natural, Natural)
 | Testfuse_CD (Natural, Natural, Natural)
 | Testfuse_EF (Natural, Natural, Natural)
 | Testfuse_GH (Natural, Natural, Natural)
 | Testfuse_IJ (Natural, Natural, Natural)
 | Testfuse_KL (Natural, Natural, Natural)
 | Testfuse_MN (Natural, Natural, Natural)
 | Testfuse_OP (Natural, Natural, Natural)
 | Testfuse_QR (Natural, Natural, Natural)

data Context = MkContext
 { fUNC :: [Functype]
 , gLOBAL :: [Globaltype]
 , tABLE :: [Tabletype]
 , mEM :: [Memtype]
 , eLEM :: [Elemtype]
 , dATA :: [Datatype]
 , lOCAL :: [Valtype]
 , lABEL :: [Resulttype]
 , rETURN :: (Maybe Resulttype)
 }




































































type Addr = Natural

type Funcaddr = Addr

type Globaladdr = Addr

type Tableaddr = Addr

type Memaddr = Addr

type Elemaddr = Addr

type Dataaddr = Addr

type Labeladdr = Addr

type Hostaddr = Addr

data Num
 = Num_CONST (Numtype, C_numtype)

data Ref
 = Ref_REF_NULL Reftype
 | Ref_REF_FUNC_ADDR Funcaddr
 | Ref_REF_HOST_ADDR Hostaddr

data Val
 = Val_CONST (Numtype, C_numtype)
 | Val_REF_NULL Reftype
 | Val_REF_FUNC_ADDR Funcaddr
 | Val_REF_HOST_ADDR Hostaddr

val_num :: Num -> Val
val_num (Num_CONST x) = (Val_CONST x)

val_ref :: Ref -> Val
val_ref (Ref_REF_NULL x) = (Val_REF_NULL x)
val_ref (Ref_REF_FUNC_ADDR x) = (Val_REF_FUNC_ADDR x)
val_ref (Ref_REF_HOST_ADDR x) = (Val_REF_HOST_ADDR x)

data Result
 = Result_VALS [Val]
 | Result_TRAP

data Externval
 = Externval_FUNC Funcaddr
 | Externval_GLOBAL Globaladdr
 | Externval_TABLE Tableaddr
 | Externval_MEM Memaddr

default_ :: Valtype -> Val
default_ Valtype_I32 = (Val_CONST (Numtype_I32, 0))
default_ Valtype_I64 = (Val_CONST (Numtype_I64, 0))
default_ Valtype_F32 = (Val_CONST (Numtype_F32, 0))
default_ Valtype_F64 = (Val_CONST (Numtype_F64, 0))
default_ Valtype_FUNCREF = (Val_REF_NULL Reftype_FUNCREF)
default_ Valtype_EXTERNREF = (Val_REF_NULL Reftype_EXTERNREF)

type Exportinst = {- mixop: EXPORT -} (Name, Externval)

data Moduleinst = MkModuleinst
 { fUNC :: [Funcaddr]
 , gLOBAL :: [Globaladdr]
 , tABLE :: [Tableaddr]
 , mEM :: [Memaddr]
 , eLEM :: [Elemaddr]
 , dATA :: [Dataaddr]
 , eXPORT :: [Exportinst]
 }

type Funcinst = {- mixop: `%;%` -} (Moduleinst, Func)

type Globalinst = Val

type Tableinst = [Ref]

type Meminst = [Byte]

type Eleminst = [Ref]

type Datainst = [Byte]

data Store = MkStore
 { fUNC :: [Funcinst]
 , gLOBAL :: [Globalinst]
 , tABLE :: [Tableinst]
 , mEM :: [Meminst]
 , eLEM :: [Eleminst]
 , dATA :: [Datainst]
 }

data Frame = MkFrame
 { lOCAL :: [Val]
 , mODULE :: Moduleinst
 }

type State = {- mixop: `%;%` -} (Store, Frame)

data Admininstr
 = Admininstr_UNREACHABLE
 | Admininstr_NOP
 | Admininstr_DROP
 | Admininstr_SELECT (Maybe Valtype)
 | Admininstr_BLOCK (Blocktype, [Instr])
 | Admininstr_LOOP (Blocktype, [Instr])
 | Admininstr_IF (Blocktype, [Instr], [Instr])
 | Admininstr_BR Labelidx
 | Admininstr_BR_IF Labelidx
 | Admininstr_BR_TABLE ([Labelidx], Labelidx)
 | Admininstr_CALL Funcidx
 | Admininstr_CALL_INDIRECT (Tableidx, Functype)
 | Admininstr_RETURN
 | Admininstr_CONST (Numtype, C_numtype)
 | Admininstr_UNOP (Numtype, Unop_numtype)
 | Admininstr_BINOP (Numtype, Binop_numtype)
 | Admininstr_TESTOP (Numtype, Testop_numtype)
 | Admininstr_RELOP (Numtype, Relop_numtype)
 | Admininstr_EXTEND (Numtype, N)
 | Admininstr_CVTOP (Numtype, Cvtop, Numtype, (Maybe Sx))
 | Admininstr_REF_NULL Reftype
 | Admininstr_REF_FUNC Funcidx
 | Admininstr_REF_IS_NULL
 | Admininstr_LOCAL_GET Localidx
 | Admininstr_LOCAL_SET Localidx
 | Admininstr_LOCAL_TEE Localidx
 | Admininstr_GLOBAL_GET Globalidx
 | Admininstr_GLOBAL_SET Globalidx
 | Admininstr_TABLE_GET Tableidx
 | Admininstr_TABLE_SET Tableidx
 | Admininstr_TABLE_SIZE Tableidx
 | Admininstr_TABLE_GROW Tableidx
 | Admininstr_TABLE_FILL Tableidx
 | Admininstr_TABLE_COPY (Tableidx, Tableidx)
 | Admininstr_TABLE_INIT (Tableidx, Elemidx)
 | Admininstr_ELEM_DROP Elemidx
 | Admininstr_MEMORY_SIZE
 | Admininstr_MEMORY_GROW
 | Admininstr_MEMORY_FILL
 | Admininstr_MEMORY_COPY
 | Admininstr_MEMORY_INIT Dataidx
 | Admininstr_DATA_DROP Dataidx
 | Admininstr_LOAD (Numtype, (Maybe (N, Sx)), Natural, Natural)
 | Admininstr_STORE (Numtype, (Maybe N), Natural, Natural)
 | Admininstr_REF_FUNC_ADDR Funcaddr
 | Admininstr_REF_HOST_ADDR Hostaddr
 | Admininstr_CALL_ADDR Funcaddr
 | Admininstr_LABEL_ (N, [Instr], [Admininstr])
 | Admininstr_FRAME_ (N, Frame, [Admininstr])
 | Admininstr_TRAP

admininstr_instr :: Instr -> Admininstr
admininstr_instr Instr_UNREACHABLE = Admininstr_UNREACHABLE
admininstr_instr Instr_NOP = Admininstr_NOP
admininstr_instr Instr_DROP = Admininstr_DROP
admininstr_instr (Instr_SELECT x) = (Admininstr_SELECT x)
admininstr_instr (Instr_BLOCK x) = (Admininstr_BLOCK x)
admininstr_instr (Instr_LOOP x) = (Admininstr_LOOP x)
admininstr_instr (Instr_IF x) = (Admininstr_IF x)
admininstr_instr (Instr_BR x) = (Admininstr_BR x)
admininstr_instr (Instr_BR_IF x) = (Admininstr_BR_IF x)
admininstr_instr (Instr_BR_TABLE x) = (Admininstr_BR_TABLE x)
admininstr_instr (Instr_CALL x) = (Admininstr_CALL x)
admininstr_instr (Instr_CALL_INDIRECT x) = (Admininstr_CALL_INDIRECT x)
admininstr_instr Instr_RETURN = Admininstr_RETURN
admininstr_instr (Instr_CONST x) = (Admininstr_CONST x)
admininstr_instr (Instr_UNOP x) = (Admininstr_UNOP x)
admininstr_instr (Instr_BINOP x) = (Admininstr_BINOP x)
admininstr_instr (Instr_TESTOP x) = (Admininstr_TESTOP x)
admininstr_instr (Instr_RELOP x) = (Admininstr_RELOP x)
admininstr_instr (Instr_EXTEND x) = (Admininstr_EXTEND x)
admininstr_instr (Instr_CVTOP x) = (Admininstr_CVTOP x)
admininstr_instr (Instr_REF_NULL x) = (Admininstr_REF_NULL x)
admininstr_instr (Instr_REF_FUNC x) = (Admininstr_REF_FUNC x)
admininstr_instr Instr_REF_IS_NULL = Admininstr_REF_IS_NULL
admininstr_instr (Instr_LOCAL_GET x) = (Admininstr_LOCAL_GET x)
admininstr_instr (Instr_LOCAL_SET x) = (Admininstr_LOCAL_SET x)
admininstr_instr (Instr_LOCAL_TEE x) = (Admininstr_LOCAL_TEE x)
admininstr_instr (Instr_GLOBAL_GET x) = (Admininstr_GLOBAL_GET x)
admininstr_instr (Instr_GLOBAL_SET x) = (Admininstr_GLOBAL_SET x)
admininstr_instr (Instr_TABLE_GET x) = (Admininstr_TABLE_GET x)
admininstr_instr (Instr_TABLE_SET x) = (Admininstr_TABLE_SET x)
admininstr_instr (Instr_TABLE_SIZE x) = (Admininstr_TABLE_SIZE x)
admininstr_instr (Instr_TABLE_GROW x) = (Admininstr_TABLE_GROW x)
admininstr_instr (Instr_TABLE_FILL x) = (Admininstr_TABLE_FILL x)
admininstr_instr (Instr_TABLE_COPY x) = (Admininstr_TABLE_COPY x)
admininstr_instr (Instr_TABLE_INIT x) = (Admininstr_TABLE_INIT x)
admininstr_instr (Instr_ELEM_DROP x) = (Admininstr_ELEM_DROP x)
admininstr_instr Instr_MEMORY_SIZE = Admininstr_MEMORY_SIZE
admininstr_instr Instr_MEMORY_GROW = Admininstr_MEMORY_GROW
admininstr_instr Instr_MEMORY_FILL = Admininstr_MEMORY_FILL
admininstr_instr Instr_MEMORY_COPY = Admininstr_MEMORY_COPY
admininstr_instr (Instr_MEMORY_INIT x) = (Admininstr_MEMORY_INIT x)
admininstr_instr (Instr_DATA_DROP x) = (Admininstr_DATA_DROP x)
admininstr_instr (Instr_LOAD x) = (Admininstr_LOAD x)
admininstr_instr (Instr_STORE x) = (Admininstr_STORE x)

admininstr_val :: Val -> Admininstr
admininstr_val (Val_CONST x) = (Admininstr_CONST x)
admininstr_val (Val_REF_NULL x) = (Admininstr_REF_NULL x)
admininstr_val (Val_REF_FUNC_ADDR x) = (Admininstr_REF_FUNC_ADDR x)
admininstr_val (Val_REF_HOST_ADDR x) = (Admininstr_REF_HOST_ADDR x)

admininstr_ref :: Ref -> Admininstr
admininstr_ref (Ref_REF_NULL x) = (Admininstr_REF_NULL x)
admininstr_ref (Ref_REF_FUNC_ADDR x) = (Admininstr_REF_FUNC_ADDR x)
admininstr_ref (Ref_REF_HOST_ADDR x) = (Admininstr_REF_HOST_ADDR x)

admininstr_globalinst :: Globalinst -> Admininstr
admininstr_globalinst x = undefined {- $admininstr_val(x) -}

type Config = {- mixop: `%;%*` -} (State, [Admininstr])

funcaddr :: State -> [Funcaddr]
funcaddr (s, f) = f.mODULE.fUNC

funcinst :: State -> [Funcinst]
funcinst (s, f) = s.fUNC

func :: (State, Funcidx) -> Funcinst
func ((s, f), x) = (s.fUNC !! (fromIntegral (f.mODULE.fUNC !! (fromIntegral x))))

global :: (State, Globalidx) -> Globalinst
global ((s, f), x) = (s.gLOBAL !! (fromIntegral (f.mODULE.gLOBAL !! (fromIntegral x))))

table :: (State, Tableidx) -> Tableinst
table ((s, f), x) = (s.tABLE !! (fromIntegral (f.mODULE.tABLE !! (fromIntegral x))))

mem :: (State, Memidx) -> Meminst
mem ((s, f), x) = (s.mEM !! (fromIntegral (f.mODULE.mEM !! (fromIntegral x))))

elem :: (State, Tableidx) -> Eleminst
elem ((s, f), x) = (s.eLEM !! (fromIntegral (f.mODULE.eLEM !! (fromIntegral x))))

data_ :: (State, Dataidx) -> Datainst
data_ ((s, f), x) = (s.dATA !! (fromIntegral (f.mODULE.dATA !! (fromIntegral x))))

local :: (State, Localidx) -> Val
local ((s, f), x) = (f.lOCAL !! (fromIntegral x))

with_local :: (State, Localidx, Val) -> State
with_local ((s, f), x, v) = (s, undefined {- f[LOCAL[x] = v] -})

with_global :: (State, Globalidx, Val) -> State
with_global ((s, f), x, v) = (undefined {- s[GLOBAL[f.MODULE_frame.GLOBAL_moduleinst[x]] = v] -}, f)

with_table :: (State, Tableidx, N, Ref) -> State
with_table ((s, f), x, i, r) = (undefined {- s[TABLE[f.MODULE_frame.TABLE_moduleinst[x]][i] = r] -}, f)

with_tableext :: (State, Tableidx, [Ref]) -> State
with_tableext ((s, f), x, r) = (undefined {- s[TABLE[f.MODULE_frame.TABLE_moduleinst[x]] =.. r*{r}] -}, f)

with_elem :: (State, Elemidx, [Ref]) -> State
with_elem ((s, f), x, r) = (undefined {- s[TABLE[f.MODULE_frame.TABLE_moduleinst[x]] = r*{r}] -}, f)

data E
 = E_HOLE
 | E_SEQ ([Val], E, [Instr])
 | E_LABEL_ (N, [Instr], E)

unop :: (Unop_numtype, Numtype, C_numtype) -> [C_numtype]
unop = error "function without clauses"

binop :: (Binop_numtype, Numtype, C_numtype, C_numtype) -> [C_numtype]
binop = error "function without clauses"

testop :: (Testop_numtype, Numtype, C_numtype) -> C_numtype
testop = error "function without clauses"

relop :: (Relop_numtype, Numtype, C_numtype, C_numtype) -> C_numtype
relop = error "function without clauses"

ext :: (Natural, Natural, Sx, C_numtype) -> C_numtype
ext = error "function without clauses"

cvtop :: (Numtype, Cvtop, Numtype, (Maybe Sx), C_numtype) -> [C_numtype]
cvtop = error "function without clauses"





$ ghc -c Test.hs
```

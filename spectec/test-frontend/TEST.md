# Preview

```sh
$ (cd ../spec && dune exec ../src/exe-watsup/main.exe -- *.watsup -v -l --print-il)
watsup 0.4 generator
== Parsing...
== Elaboration...

;; 0-aux.watsup:12.1-12.15
syntax n = nat

;; 0-aux.watsup:17.1-17.14
def Ki : nat
  ;; 0-aux.watsup:18.1-18.15
  def Ki = 1024

;; 0-aux.watsup:23.1-23.25
rec {

;; 0-aux.watsup:23.1-23.25
def min : (nat, nat) -> nat
  ;; 0-aux.watsup:24.1-24.19
  def {j : nat} min(0, j) = 0
  ;; 0-aux.watsup:25.1-25.19
  def {i : nat} min(i, 0) = 0
  ;; 0-aux.watsup:26.1-26.38
  def {i : nat, j : nat} min((i + 1), (j + 1)) = $min(i, j)
}

;; 0-aux.watsup:34.1-34.40
def test_sub_ATOM_22 : n -> nat
  ;; 0-aux.watsup:35.1-35.38
  def {n_3_ATOM_y : n} test_sub_ATOM_22(n_3_ATOM_y) = 0

;; 0-aux.watsup:37.1-37.26
def curried_ : (n, n) -> nat
  ;; 0-aux.watsup:38.1-38.39
  def {n_1 : n, n_2 : n} curried_(n_1, n_2) = (n_1 + n_2)

;; 0-aux.watsup:40.1-49.39
syntax testfuse =
  | AB_(nat, nat, nat)
  | CD(nat, nat, nat)
  | EF(nat, nat, nat)
  | GH(nat, nat, nat)
  | IJ(nat, nat, nat)
  | KL(nat, nat, nat)
  | MN(nat, nat, nat)
  | OP(nat, nat, nat)
  | QR(nat, nat, nat)

;; 1-syntax.watsup:5.1-5.37
syntax name = text

;; 1-syntax.watsup:12.1-12.36
syntax byte = nat

;; 1-syntax.watsup:13.1-13.45
syntax i31 = nat

;; 1-syntax.watsup:14.1-14.45
syntax i32 = nat

;; 1-syntax.watsup:23.1-23.36
syntax idx = i32

;; 1-syntax.watsup:24.1-24.45
syntax typeidx = idx

;; 1-syntax.watsup:25.1-25.49
syntax funcidx = idx

;; 1-syntax.watsup:26.1-26.49
syntax globalidx = idx

;; 1-syntax.watsup:27.1-27.47
syntax tableidx = idx

;; 1-syntax.watsup:28.1-28.46
syntax memidx = idx

;; 1-syntax.watsup:29.1-29.45
syntax elemidx = idx

;; 1-syntax.watsup:30.1-30.45
syntax dataidx = idx

;; 1-syntax.watsup:31.1-31.47
syntax labelidx = idx

;; 1-syntax.watsup:32.1-32.47
syntax localidx = idx

;; 1-syntax.watsup:45.1-45.19
syntax nul = `NULL%?`(()?)

;; 1-syntax.watsup:47.1-48.22
syntax numtype =
  | I32
  | I64
  | F32
  | F64

;; 1-syntax.watsup:50.1-51.5
syntax vectype =
  | V128

;; 1-syntax.watsup:58.1-59.10
syntax absheaptype =
  | ANY
  | EQ
  | I31
  | STRUCT
  | ARRAY
  | NONE
  | FUNC
  | NOFUNC
  | EXTERN
  | NOEXTERN
  | BOT

;; 1-syntax.watsup:83.1-83.18
syntax mut = `MUT%?`(()?)

;; 1-syntax.watsup:84.1-84.20
syntax fin = `FINAL%?`(()?)

;; 1-syntax.watsup:70.1-118.8
rec {

;; 1-syntax.watsup:70.1-71.10
syntax valtype =
  | I32
  | I64
  | F32
  | F64
  | V128
  | REF(nul, heaptype)
  | BOT

;; 1-syntax.watsup:77.1-78.11
syntax resulttype = valtype*

;; 1-syntax.watsup:89.1-90.21
syntax storagetype =
  | BOT
  | I32
  | I64
  | F32
  | F64
  | V128
  | REF(nul, heaptype)
  | I8
  | I16

;; 1-syntax.watsup:92.1-93.18
syntax fieldtype = `%%`(mut, storagetype)

;; 1-syntax.watsup:95.1-96.27
syntax functype = `%->%`(resulttype, resulttype)

;; 1-syntax.watsup:98.1-101.14
syntax comptype =
  | STRUCT(fieldtype*)
  | ARRAY(fieldtype)
  | FUNC(functype)

;; 1-syntax.watsup:105.1-107.50
syntax subtype =
  | SUB(fin, typeidx*, comptype)
  | SUBD(fin, heaptype*, comptype)

;; 1-syntax.watsup:109.1-110.13
syntax rectype =
  | REC(subtype*)

;; 1-syntax.watsup:115.1-118.8
syntax heaptype =
  | _IDX(typeidx)
  | ANY
  | EQ
  | I31
  | STRUCT
  | ARRAY
  | NONE
  | FUNC
  | NOFUNC
  | EXTERN
  | NOEXTERN
  | BOT
  | DEF(rectype, nat)
  | REC(nat)
}

;; 1-syntax.watsup:65.1-66.17
syntax reftype =
  | REF(nul, heaptype)

;; 1-syntax.watsup:73.1-73.39
syntax iN =
  | I32
  | I64

;; 1-syntax.watsup:74.1-74.39
syntax fN =
  | F32
  | F64

;; 1-syntax.watsup:86.1-87.9
syntax packedtype =
  | I8
  | I16

;; 1-syntax.watsup:112.1-113.31
syntax deftype =
  | DEF(rectype, nat)

;; 1-syntax.watsup:123.1-124.16
syntax limits = `[%..%]`(i32, i32)

;; 1-syntax.watsup:125.1-126.14
syntax globaltype = `%%`(mut, valtype)

;; 1-syntax.watsup:127.1-128.17
syntax tabletype = `%%`(limits, reftype)

;; 1-syntax.watsup:129.1-130.12
syntax memtype = `%I8`(limits)

;; 1-syntax.watsup:131.1-132.10
syntax elemtype = reftype

;; 1-syntax.watsup:133.1-134.5
syntax datatype = OK

;; 1-syntax.watsup:135.1-136.65
syntax externtype =
  | FUNC(deftype)
  | GLOBAL(globaltype)
  | TABLE(tabletype)
  | MEM(memtype)

;; 1-syntax.watsup:172.1-172.44
syntax sx =
  | U
  | S

;; 1-syntax.watsup:174.1-174.58
syntax unopIXX =
  | CLZ
  | CTZ
  | POPCNT

;; 1-syntax.watsup:175.1-175.89
syntax unopFXX =
  | ABS
  | NEG
  | SQRT
  | CEIL
  | FLOOR
  | TRUNC
  | NEAREST

;; 1-syntax.watsup:177.1-179.62
syntax binopIXX =
  | ADD
  | SUB
  | MUL
  | DIV(sx)
  | REM(sx)
  | AND
  | OR
  | XOR
  | SHL
  | SHR(sx)
  | ROTL
  | ROTR

;; 1-syntax.watsup:180.1-180.86
syntax binopFXX =
  | ADD
  | SUB
  | MUL
  | DIV
  | MIN
  | MAX
  | COPYSIGN

;; 1-syntax.watsup:182.1-182.47
syntax testopIXX =
  | EQZ

;; 1-syntax.watsup:183.1-183.43
syntax testopFXX =
  |

;; 1-syntax.watsup:185.1-186.108
syntax relopIXX =
  | EQ
  | NE
  | LT(sx)
  | GT(sx)
  | LE(sx)
  | GE(sx)

;; 1-syntax.watsup:187.1-187.69
syntax relopFXX =
  | EQ
  | NE
  | LT
  | GT
  | LE
  | GE

;; 1-syntax.watsup:189.1-189.48
syntax unop_numtype =
  | _I(unopIXX)
  | _F(unopFXX)

;; 1-syntax.watsup:190.1-190.51
syntax binop_numtype =
  | _I(binopIXX)
  | _F(binopFXX)

;; 1-syntax.watsup:191.1-191.54
syntax testop_numtype =
  | _I(testopIXX)
  | _F(testopFXX)

;; 1-syntax.watsup:192.1-192.51
syntax relop_numtype =
  | _I(relopIXX)
  | _F(relopFXX)

;; 1-syntax.watsup:193.1-193.39
syntax cvtop =
  | CONVERT
  | REINTERPRET

;; 1-syntax.watsup:205.1-205.23
syntax c_numtype = nat

;; 1-syntax.watsup:206.1-206.23
syntax c_vectype = nat

;; 1-syntax.watsup:209.1-209.52
syntax blocktype = functype

;; 1-syntax.watsup:279.1-300.89
rec {

;; 1-syntax.watsup:279.1-300.89
syntax instr =
  | UNREACHABLE
  | NOP
  | DROP
  | SELECT(valtype?)
  | BLOCK(blocktype, instr*)
  | LOOP(blocktype, instr*)
  | IF(blocktype, instr*, instr*)
  | BR(labelidx)
  | BR_IF(labelidx)
  | BR_TABLE(labelidx*, labelidx)
  | BR_ON_NULL(labelidx)
  | BR_ON_NON_NULL(labelidx)
  | BR_ON_CAST(labelidx, reftype, reftype)
  | BR_ON_CAST_FAIL(labelidx, reftype, reftype)
  | CALL(funcidx)
  | CALL_REF(typeidx)
  | CALL_INDIRECT(tableidx, typeidx)
  | RETURN
  | RETURN_CALL(funcidx)
  | RETURN_CALL_REF(typeidx)
  | RETURN_CALL_INDIRECT(tableidx, typeidx)
  | CONST(numtype, c_numtype)
  | UNOP(numtype, unop_numtype)
  | BINOP(numtype, binop_numtype)
  | TESTOP(numtype, testop_numtype)
  | RELOP(numtype, relop_numtype)
  | EXTEND(numtype, n)
  | CVTOP(numtype, cvtop, numtype, sx?)
  | REF.NULL(heaptype)
  | REF.I31
  | REF.FUNC(funcidx)
  | REF.IS_NULL
  | REF.AS_NON_NULL
  | REF.EQ
  | REF.TEST(reftype)
  | REF.CAST(reftype)
  | I31.GET(sx)
  | STRUCT.NEW(typeidx)
  | STRUCT.NEW_DEFAULT(typeidx)
  | STRUCT.GET(sx?, typeidx, i32)
  | STRUCT.SET(typeidx, i32)
  | ARRAY.NEW(typeidx)
  | ARRAY.NEW_DEFAULT(typeidx)
  | ARRAY.NEW_FIXED(typeidx, nat)
  | ARRAY.NEW_DATA(typeidx, dataidx)
  | ARRAY.NEW_ELEM(typeidx, elemidx)
  | ARRAY.GET(sx?, typeidx)
  | ARRAY.SET(typeidx)
  | ARRAY.LEN
  | ARRAY.FILL(typeidx)
  | ARRAY.COPY(typeidx, typeidx)
  | ARRAY.INIT_DATA(typeidx, dataidx)
  | ARRAY.INIT_ELEM(typeidx, elemidx)
  | EXTERN.INTERNALIZE
  | EXTERN.EXTERNALIZE
  | LOCAL.GET(localidx)
  | LOCAL.SET(localidx)
  | LOCAL.TEE(localidx)
  | GLOBAL.GET(globalidx)
  | GLOBAL.SET(globalidx)
  | TABLE.GET(tableidx)
  | TABLE.SET(tableidx)
  | TABLE.SIZE(tableidx)
  | TABLE.GROW(tableidx)
  | TABLE.FILL(tableidx)
  | TABLE.COPY(tableidx, tableidx)
  | TABLE.INIT(tableidx, elemidx)
  | ELEM.DROP(elemidx)
  | MEMORY.SIZE(memidx)
  | MEMORY.GROW(memidx)
  | MEMORY.FILL(memidx)
  | MEMORY.COPY(memidx, memidx)
  | MEMORY.INIT(memidx, dataidx)
  | DATA.DROP(dataidx)
  | LOAD(numtype, (n, sx)?, memidx, i32, i32)
  | STORE(numtype, n?, memidx, i32, i32)
}

;; 1-syntax.watsup:302.1-303.9
syntax expr = instr*

;; 1-syntax.watsup:312.1-312.50
syntax elemmode =
  | TABLE(tableidx, expr)
  | DECLARE

;; 1-syntax.watsup:313.1-313.39
syntax datamode =
  | MEMORY(memidx, expr)

;; 1-syntax.watsup:315.1-316.15
syntax type = TYPE(rectype)

;; 1-syntax.watsup:317.1-318.16
syntax local = LOCAL(valtype)

;; 1-syntax.watsup:319.1-320.27
syntax func = `FUNC%%*%`(typeidx, local*, expr)

;; 1-syntax.watsup:321.1-322.25
syntax global = GLOBAL(globaltype, expr)

;; 1-syntax.watsup:323.1-324.23
syntax table = TABLE(tabletype, expr)

;; 1-syntax.watsup:325.1-326.17
syntax mem = MEMORY(memtype)

;; 1-syntax.watsup:327.1-328.31
syntax elem = `ELEM%%*%?`(reftype, expr*, elemmode?)

;; 1-syntax.watsup:329.1-330.23
syntax data = `DATA%*%?`(byte*, datamode?)

;; 1-syntax.watsup:331.1-332.16
syntax start = START(funcidx)

;; 1-syntax.watsup:334.1-335.62
syntax externuse =
  | FUNC(funcidx)
  | GLOBAL(globalidx)
  | TABLE(tableidx)
  | MEM(memidx)

;; 1-syntax.watsup:336.1-337.24
syntax export = EXPORT(name, externuse)

;; 1-syntax.watsup:338.1-339.30
syntax import = IMPORT(name, name, externtype)

;; 1-syntax.watsup:341.1-342.76
syntax module = `MODULE%*%*%*%*%*%*%*%*%?%*`(type*, import*, func*, global*, table*, mem*, elem*, data*, start?, export*)

;; 2-syntax-aux.watsup:8.1-8.33
rec {

;; 2-syntax-aux.watsup:8.1-8.33
def setminus1 : (idx, idx*) -> idx*
  ;; 2-syntax-aux.watsup:13.1-13.31
  def {x : idx} setminus1(x, []) = [x]
  ;; 2-syntax-aux.watsup:14.1-14.61
  def {x : idx, y* : idx*, y_1 : idx} setminus1(x, [y_1] :: y*{y}) = []
    -- if (x = y_1)
  ;; 2-syntax-aux.watsup:15.1-15.60
  def {x : idx, y* : idx*, y_1 : idx} setminus1(x, [y_1] :: y*{y}) = $setminus1(x, y*{y})
    -- otherwise
}

;; 2-syntax-aux.watsup:7.1-7.49
rec {

;; 2-syntax-aux.watsup:7.1-7.49
def setminus : (idx*, idx*) -> idx*
  ;; 2-syntax-aux.watsup:10.1-10.37
  def {y* : idx*} setminus([], y*{y}) = []
  ;; 2-syntax-aux.watsup:11.1-11.66
  def {x* : idx*, x_1 : idx, y* : idx*} setminus([x_1] :: x*{x}, y*{y}) = $setminus1(x_1, y*{y}) :: $setminus(x*{x}, y*{y})
}

;; 2-syntax-aux.watsup:26.1-26.55
def size : valtype -> nat
  ;; 2-syntax-aux.watsup:27.1-27.20
  def size(I32_valtype) = 32
  ;; 2-syntax-aux.watsup:28.1-28.20
  def size(I64_valtype) = 64
  ;; 2-syntax-aux.watsup:29.1-29.20
  def size(F32_valtype) = 32
  ;; 2-syntax-aux.watsup:30.1-30.20
  def size(F64_valtype) = 64
  ;; 2-syntax-aux.watsup:31.1-31.22
  def size(V128_valtype) = 128

;; 2-syntax-aux.watsup:33.1-33.50
def packedsize : packedtype -> nat
  ;; 2-syntax-aux.watsup:34.1-34.24
  def packedsize(I8_packedtype) = 8
  ;; 2-syntax-aux.watsup:35.1-35.26
  def packedsize(I16_packedtype) = 16

;; 2-syntax-aux.watsup:37.1-37.52
def storagesize : storagetype -> nat
  ;; 2-syntax-aux.watsup:38.1-38.43
  def {valtype : valtype} storagesize(valtype <: storagetype) = $size(valtype)
  ;; 2-syntax-aux.watsup:39.1-39.55
  def {packedtype : packedtype} storagesize(packedtype <: storagetype) = $packedsize(packedtype)

;; 2-syntax-aux.watsup:44.1-44.62
def unpacktype : storagetype -> valtype
  ;; 2-syntax-aux.watsup:45.1-45.35
  def {valtype : valtype} unpacktype(valtype <: storagetype) = valtype
  ;; 2-syntax-aux.watsup:46.1-46.34
  def {packedtype : packedtype} unpacktype(packedtype <: storagetype) = I32_valtype

;; 2-syntax-aux.watsup:48.1-48.65
def unpacknumtype : storagetype -> numtype
  ;; 2-syntax-aux.watsup:49.1-49.38
  def {numtype : numtype} unpacknumtype(numtype <: storagetype) = numtype
  ;; 2-syntax-aux.watsup:50.1-50.37
  def {packedtype : packedtype} unpacknumtype(packedtype <: storagetype) = I32_numtype

;; 2-syntax-aux.watsup:52.1-52.51
def sxfield : storagetype -> sx?
  ;; 2-syntax-aux.watsup:53.1-53.32
  def {valtype : valtype} sxfield(valtype <: storagetype) = ?()
  ;; 2-syntax-aux.watsup:54.1-54.29
  def {packedtype : packedtype} sxfield(packedtype <: storagetype) = ?(S_sx)

;; 2-syntax-aux.watsup:59.1-59.59
def diffrt : (reftype, reftype) -> reftype
  ;; 2-syntax-aux.watsup:61.1-61.68
  def {ht_1 : heaptype, ht_2 : heaptype, nul_1 : nul} diffrt(REF_reftype(nul_1, ht_1), REF_reftype(`NULL%?`(?(())), ht_2)) = REF_reftype(`NULL%?`(?()), ht_1)
  ;; 2-syntax-aux.watsup:62.1-62.69
  def {ht_1 : heaptype, ht_2 : heaptype, nul_1 : nul} diffrt(REF_reftype(nul_1, ht_1), REF_reftype(`NULL%?`(?()), ht_2)) = REF_reftype(nul_1, ht_1)

;; 2-syntax-aux.watsup:67.1-67.42
syntax typevar =
  | _IDX(typeidx)
  | REC(nat)

;; 2-syntax-aux.watsup:70.1-70.42
def idx : typeidx -> typevar
  ;; 2-syntax-aux.watsup:71.1-71.21
  def {x : idx} idx(x) = _IDX_typevar(x)

;; 2-syntax-aux.watsup:76.1-76.92
rec {

;; 2-syntax-aux.watsup:76.1-76.92
def subst_typevar : (typevar, typevar*, heaptype*) -> heaptype
  ;; 2-syntax-aux.watsup:101.1-101.46
  def {xx : typevar} subst_typevar(xx, [], []) = (xx <: heaptype)
  ;; 2-syntax-aux.watsup:102.1-102.95
  def {ht'* : heaptype*, ht_1 : heaptype, xx : typevar, xx'* : typevar*, xx_1 : typevar} subst_typevar(xx, [xx_1] :: xx'*{xx'}, [ht_1] :: ht'*{ht'}) = ht_1
    -- if (xx = xx_1)
  ;; 2-syntax-aux.watsup:103.1-103.92
  def {ht'* : heaptype*, ht_1 : heaptype, xx : typevar, xx'* : typevar*, xx_1 : typevar} subst_typevar(xx, [xx_1] :: xx'*{xx'}, [ht_1] :: ht'*{ht'}) = $subst_typevar(xx, xx'*{xx'}, ht'*{ht'})
    -- otherwise
}

;; 2-syntax-aux.watsup:78.1-78.92
def subst_numtype : (numtype, typevar*, heaptype*) -> numtype
  ;; 2-syntax-aux.watsup:105.1-105.38
  def {ht* : heaptype*, nt : numtype, xx* : typevar*} subst_numtype(nt, xx*{xx}, ht*{ht}) = nt

;; 2-syntax-aux.watsup:79.1-79.92
def subst_vectype : (vectype, typevar*, heaptype*) -> vectype
  ;; 2-syntax-aux.watsup:106.1-106.38
  def {ht* : heaptype*, vt : vectype, xx* : typevar*} subst_vectype(vt, xx*{xx}, ht*{ht}) = vt

;; 2-syntax-aux.watsup:84.1-84.92
def subst_packedtype : (packedtype, typevar*, heaptype*) -> packedtype
  ;; 2-syntax-aux.watsup:119.1-119.41
  def {ht* : heaptype*, pt : packedtype, xx* : typevar*} subst_packedtype(pt, xx*{xx}, ht*{ht}) = pt

;; 2-syntax-aux.watsup:80.1-94.92
rec {

;; 2-syntax-aux.watsup:80.1-80.92
def subst_heaptype : (heaptype, typevar*, heaptype*) -> heaptype
  ;; 2-syntax-aux.watsup:108.1-108.67
  def {ht* : heaptype*, xx* : typevar*, xx' : typevar} subst_heaptype((xx' <: heaptype), xx*{xx}, ht*{ht}) = $subst_typevar(xx', xx*{xx}, ht*{ht})
  ;; 2-syntax-aux.watsup:109.1-109.65
  def {dt : deftype, ht* : heaptype*, xx* : typevar*} subst_heaptype((dt <: heaptype), xx*{xx}, ht*{ht}) = ($subst_deftype(dt, xx*{xx}, ht*{ht}) <: heaptype)
  ;; 2-syntax-aux.watsup:110.1-110.55
  def {ht* : heaptype*, ht' : heaptype, xx* : typevar*} subst_heaptype(ht', xx*{xx}, ht*{ht}) = ht'
    -- otherwise

;; 2-syntax-aux.watsup:81.1-81.92
def subst_reftype : (reftype, typevar*, heaptype*) -> reftype
  ;; 2-syntax-aux.watsup:112.1-112.85
  def {ht* : heaptype*, ht' : heaptype, nul : nul, xx* : typevar*} subst_reftype(REF_reftype(nul, ht'), xx*{xx}, ht*{ht}) = REF_reftype(nul, $subst_heaptype(ht', xx*{xx}, ht*{ht}))

;; 2-syntax-aux.watsup:82.1-82.92
def subst_valtype : (valtype, typevar*, heaptype*) -> valtype
  ;; 2-syntax-aux.watsup:114.1-114.64
  def {ht* : heaptype*, nt : numtype, xx* : typevar*} subst_valtype((nt <: valtype), xx*{xx}, ht*{ht}) = ($subst_numtype(nt, xx*{xx}, ht*{ht}) <: valtype)
  ;; 2-syntax-aux.watsup:115.1-115.64
  def {ht* : heaptype*, vt : vectype, xx* : typevar*} subst_valtype((vt <: valtype), xx*{xx}, ht*{ht}) = ($subst_vectype(vt, xx*{xx}, ht*{ht}) <: valtype)
  ;; 2-syntax-aux.watsup:116.1-116.64
  def {ht* : heaptype*, rt : reftype, xx* : typevar*} subst_valtype((rt <: valtype), xx*{xx}, ht*{ht}) = ($subst_reftype(rt, xx*{xx}, ht*{ht}) <: valtype)
  ;; 2-syntax-aux.watsup:117.1-117.40
  def {ht* : heaptype*, xx* : typevar*} subst_valtype(BOT_valtype, xx*{xx}, ht*{ht}) = BOT_valtype

;; 2-syntax-aux.watsup:85.1-85.92
def subst_storagetype : (storagetype, typevar*, heaptype*) -> storagetype
  ;; 2-syntax-aux.watsup:121.1-121.66
  def {ht* : heaptype*, t : valtype, xx* : typevar*} subst_storagetype((t <: storagetype), xx*{xx}, ht*{ht}) = ($subst_valtype(t, xx*{xx}, ht*{ht}) <: storagetype)
  ;; 2-syntax-aux.watsup:122.1-122.71
  def {ht* : heaptype*, pt : packedtype, xx* : typevar*} subst_storagetype((pt <: storagetype), xx*{xx}, ht*{ht}) = ($subst_packedtype(pt, xx*{xx}, ht*{ht}) <: storagetype)

;; 2-syntax-aux.watsup:86.1-86.92
def subst_fieldtype : (fieldtype, typevar*, heaptype*) -> fieldtype
  ;; 2-syntax-aux.watsup:124.1-124.80
  def {ht* : heaptype*, mut : mut, xx* : typevar*, zt : storagetype} subst_fieldtype(`%%`(mut, zt), xx*{xx}, ht*{ht}) = `%%`(mut, $subst_storagetype(zt, xx*{xx}, ht*{ht}))

;; 2-syntax-aux.watsup:88.1-88.92
def subst_comptype : (comptype, typevar*, heaptype*) -> comptype
  ;; 2-syntax-aux.watsup:126.1-126.85
  def {ht* : heaptype*, xx* : typevar*, yt* : fieldtype*} subst_comptype(STRUCT_comptype(yt*{yt}), xx*{xx}, ht*{ht}) = STRUCT_comptype($subst_fieldtype(yt, xx*{xx}, ht*{ht})*{yt})
  ;; 2-syntax-aux.watsup:127.1-127.81
  def {ht* : heaptype*, xx* : typevar*, yt : fieldtype} subst_comptype(ARRAY_comptype(yt), xx*{xx}, ht*{ht}) = ARRAY_comptype($subst_fieldtype(yt, xx*{xx}, ht*{ht}))
  ;; 2-syntax-aux.watsup:128.1-128.78
  def {ft : functype, ht* : heaptype*, xx* : typevar*} subst_comptype(FUNC_comptype(ft), xx*{xx}, ht*{ht}) = FUNC_comptype($subst_functype(ft, xx*{xx}, ht*{ht}))

;; 2-syntax-aux.watsup:89.1-89.92
def subst_subtype : (subtype, typevar*, heaptype*) -> subtype
  ;; 2-syntax-aux.watsup:130.1-131.76
  def {ct : comptype, fin : fin, ht* : heaptype*, xx* : typevar*, y* : idx*} subst_subtype(SUB_subtype(fin, y*{y}, ct), xx*{xx}, ht*{ht}) = SUBD_subtype(fin, $subst_heaptype(_IDX_heaptype(y), xx*{xx}, ht*{ht})*{y}, $subst_comptype(ct, xx*{xx}, ht*{ht}))
  ;; 2-syntax-aux.watsup:132.1-133.73
  def {ct : comptype, fin : fin, ht* : heaptype*, ht'* : heaptype*, xx* : typevar*} subst_subtype(SUBD_subtype(fin, ht'*{ht'}, ct), xx*{xx}, ht*{ht}) = SUBD_subtype(fin, $subst_heaptype(ht', xx*{xx}, ht*{ht})*{ht'}, $subst_comptype(ct, xx*{xx}, ht*{ht}))

;; 2-syntax-aux.watsup:90.1-90.92
def subst_rectype : (rectype, typevar*, heaptype*) -> rectype
  ;; 2-syntax-aux.watsup:135.1-135.76
  def {ht* : heaptype*, st* : subtype*, xx* : typevar*} subst_rectype(REC_rectype(st*{st}), xx*{xx}, ht*{ht}) = REC_rectype($subst_subtype(st, xx*{xx}, ht*{ht})*{st})

;; 2-syntax-aux.watsup:91.1-91.92
def subst_deftype : (deftype, typevar*, heaptype*) -> deftype
  ;; 2-syntax-aux.watsup:137.1-137.78
  def {ht* : heaptype*, i : nat, qt : rectype, xx* : typevar*} subst_deftype(DEF_deftype(qt, i), xx*{xx}, ht*{ht}) = DEF_deftype($subst_rectype(qt, xx*{xx}, ht*{ht}), i)

;; 2-syntax-aux.watsup:94.1-94.92
def subst_functype : (functype, typevar*, heaptype*) -> functype
  ;; 2-syntax-aux.watsup:140.1-140.113
  def {ht* : heaptype*, t_1* : valtype*, t_2* : valtype*, xx* : typevar*} subst_functype(`%->%`(t_1*{t_1}, t_2*{t_2}), xx*{xx}, ht*{ht}) = `%->%`($subst_valtype(t_1, xx*{xx}, ht*{ht})*{t_1}, $subst_valtype(t_2, xx*{xx}, ht*{ht})*{t_2})
}

;; 2-syntax-aux.watsup:93.1-93.92
def subst_globaltype : (globaltype, typevar*, heaptype*) -> globaltype
  ;; 2-syntax-aux.watsup:139.1-139.75
  def {ht* : heaptype*, mut : mut, t : valtype, xx* : typevar*} subst_globaltype(`%%`(mut, t), xx*{xx}, ht*{ht}) = `%%`(mut, $subst_valtype(t, xx*{xx}, ht*{ht}))

;; 2-syntax-aux.watsup:95.1-95.92
def subst_tabletype : (tabletype, typevar*, heaptype*) -> tabletype
  ;; 2-syntax-aux.watsup:142.1-142.76
  def {ht* : heaptype*, lim : limits, rt : reftype, xx* : typevar*} subst_tabletype(`%%`(lim, rt), xx*{xx}, ht*{ht}) = `%%`(lim, $subst_reftype(rt, xx*{xx}, ht*{ht}))

;; 2-syntax-aux.watsup:96.1-96.92
def subst_memtype : (memtype, typevar*, heaptype*) -> memtype
  ;; 2-syntax-aux.watsup:141.1-141.48
  def {ht* : heaptype*, lim : limits, xx* : typevar*} subst_memtype(`%I8`(lim), xx*{xx}, ht*{ht}) = `%I8`(lim)

;; 2-syntax-aux.watsup:98.1-98.92
def subst_externtype : (externtype, typevar*, heaptype*) -> externtype
  ;; 2-syntax-aux.watsup:144.1-144.79
  def {dt : deftype, ht* : heaptype*, xx* : typevar*} subst_externtype(FUNC_externtype(dt), xx*{xx}, ht*{ht}) = FUNC_externtype($subst_deftype(dt, xx*{xx}, ht*{ht}))
  ;; 2-syntax-aux.watsup:145.1-145.86
  def {gt : globaltype, ht* : heaptype*, xx* : typevar*} subst_externtype(GLOBAL_externtype(gt), xx*{xx}, ht*{ht}) = GLOBAL_externtype($subst_globaltype(gt, xx*{xx}, ht*{ht}))
  ;; 2-syntax-aux.watsup:146.1-146.83
  def {ht* : heaptype*, tt : tabletype, xx* : typevar*} subst_externtype(TABLE_externtype(tt), xx*{xx}, ht*{ht}) = TABLE_externtype($subst_tabletype(tt, xx*{xx}, ht*{ht}))
  ;; 2-syntax-aux.watsup:147.1-147.77
  def {ht* : heaptype*, mt : memtype, xx* : typevar*} subst_externtype(MEM_externtype(mt), xx*{xx}, ht*{ht}) = MEM_externtype($subst_memtype(mt, xx*{xx}, ht*{ht}))

;; 2-syntax-aux.watsup:150.1-150.74
def subst_all_reftype : (reftype, heaptype*) -> reftype
  ;; 2-syntax-aux.watsup:153.1-153.75
  def {ht^n : heaptype^n, n : n, rt : reftype, x^n : idx^n} subst_all_reftype(rt, ht^n{ht}) = $subst_reftype(rt, $idx(x)^(x<n){x}, ht^n{ht})

;; 2-syntax-aux.watsup:151.1-151.74
def subst_all_deftype : (deftype, heaptype*) -> deftype
  ;; 2-syntax-aux.watsup:154.1-154.75
  def {dt : deftype, ht^n : heaptype^n, n : n, x^n : idx^n} subst_all_deftype(dt, ht^n{ht}) = $subst_deftype(dt, $idx(x)^(x<n){x}, ht^n{ht})

;; 2-syntax-aux.watsup:156.1-156.77
rec {

;; 2-syntax-aux.watsup:156.1-156.77
def subst_all_deftypes : (deftype*, heaptype*) -> deftype*
  ;; 2-syntax-aux.watsup:158.1-158.48
  def {ht* : heaptype*} subst_all_deftypes([], ht*{ht}) = []
  ;; 2-syntax-aux.watsup:159.1-159.101
  def {dt* : deftype*, dt_1 : deftype, ht* : heaptype*} subst_all_deftypes([dt_1] :: dt*{dt}, ht*{ht}) = [$subst_all_deftype(dt_1, ht*{ht})] :: $subst_all_deftypes(dt*{dt}, ht*{ht})
}

;; 2-syntax-aux.watsup:164.1-164.65
def rollrt : (typeidx, rectype) -> rectype
  ;; 2-syntax-aux.watsup:173.1-173.93
  def {i^n^n : nat^n^n, n : n, st^n : subtype^n, x : idx} rollrt(x, REC_rectype(st^n{st})) = REC_rectype($subst_subtype(st, $idx(x + i)^(i<n){i}, REC_heaptype(i)^(i<n){i})^n{i st})

;; 2-syntax-aux.watsup:165.1-165.63
def unrollrt : rectype -> rectype
  ;; 2-syntax-aux.watsup:174.1-175.22
  def {i^n^n : nat^n^n, n : n, qt : rectype, st^n : subtype^n} unrollrt(REC_rectype(st^n{st})) = REC_rectype($subst_subtype(st, REC_typevar(i)^(i<n){i}, DEF_heaptype(qt, i)^(i<n){i})^n{i st})
    -- if (qt = REC_rectype(st^n{st}))

;; 2-syntax-aux.watsup:166.1-166.65
def rolldt : (typeidx, rectype) -> deftype*
  ;; 2-syntax-aux.watsup:177.1-177.79
  def {i^n : nat^n, n : n, qt : rectype, st^n : subtype^n, x : idx} rolldt(x, qt) = DEF_deftype(REC_rectype(st^n{st}), i)^(i<n){i}
    -- if ($rollrt(x, qt) = REC_rectype(st^n{st}))

;; 2-syntax-aux.watsup:167.1-167.63
def unrolldt : deftype -> subtype
  ;; 2-syntax-aux.watsup:178.1-178.77
  def {i : nat, qt : rectype, st* : subtype*} unrolldt(DEF_deftype(qt, i)) = st*{st}[i]
    -- if ($unrollrt(qt) = REC_rectype(st*{st}))

;; 2-syntax-aux.watsup:168.1-168.63
def expanddt : deftype -> comptype
  ;; 2-syntax-aux.watsup:180.1-180.85
  def {ct : comptype, dt : deftype, fin : fin, ht* : heaptype*} expanddt(dt) = ct
    -- if ($unrolldt(dt) = SUBD_subtype(fin, ht*{ht}, ct))

;; 2-syntax-aux.watsup:182.1-182.37
relation Expand: `%~~%`(deftype, comptype)
  ;; 2-syntax-aux.watsup:183.1-183.72
  rule _ {ct : comptype, dt : deftype}:
    `%~~%`(dt, ct)
    -- if ($expanddt(dt) = ct)

;; 2-syntax-aux.watsup:188.1-188.64
rec {

;; 2-syntax-aux.watsup:188.1-188.64
def funcsxt : externtype* -> deftype*
  ;; 2-syntax-aux.watsup:193.1-193.32
  def funcsxt([]) = []
  ;; 2-syntax-aux.watsup:194.1-194.47
  def {dt : deftype, et* : externtype*} funcsxt([FUNC_externtype(dt)] :: et*{et}) = [dt] :: $funcsxt(et*{et})
  ;; 2-syntax-aux.watsup:195.1-195.59
  def {et* : externtype*, externtype : externtype} funcsxt([externtype] :: et*{et}) = $funcsxt(et*{et})
    -- otherwise
}

;; 2-syntax-aux.watsup:189.1-189.66
rec {

;; 2-syntax-aux.watsup:189.1-189.66
def globalsxt : externtype* -> globaltype*
  ;; 2-syntax-aux.watsup:197.1-197.34
  def globalsxt([]) = []
  ;; 2-syntax-aux.watsup:198.1-198.53
  def {et* : externtype*, gt : globaltype} globalsxt([GLOBAL_externtype(gt)] :: et*{et}) = [gt] :: $globalsxt(et*{et})
  ;; 2-syntax-aux.watsup:199.1-199.63
  def {et* : externtype*, externtype : externtype} globalsxt([externtype] :: et*{et}) = $globalsxt(et*{et})
    -- otherwise
}

;; 2-syntax-aux.watsup:190.1-190.65
rec {

;; 2-syntax-aux.watsup:190.1-190.65
def tablesxt : externtype* -> tabletype*
  ;; 2-syntax-aux.watsup:201.1-201.33
  def tablesxt([]) = []
  ;; 2-syntax-aux.watsup:202.1-202.50
  def {et* : externtype*, tt : tabletype} tablesxt([TABLE_externtype(tt)] :: et*{et}) = [tt] :: $tablesxt(et*{et})
  ;; 2-syntax-aux.watsup:203.1-203.61
  def {et* : externtype*, externtype : externtype} tablesxt([externtype] :: et*{et}) = $tablesxt(et*{et})
    -- otherwise
}

;; 2-syntax-aux.watsup:191.1-191.63
rec {

;; 2-syntax-aux.watsup:191.1-191.63
def memsxt : externtype* -> memtype*
  ;; 2-syntax-aux.watsup:205.1-205.31
  def memsxt([]) = []
  ;; 2-syntax-aux.watsup:206.1-206.44
  def {et* : externtype*, mt : memtype} memsxt([MEM_externtype(mt)] :: et*{et}) = [mt] :: $memsxt(et*{et})
  ;; 2-syntax-aux.watsup:207.1-207.57
  def {et* : externtype*, externtype : externtype} memsxt([externtype] :: et*{et}) = $memsxt(et*{et})
    -- otherwise
}

;; 3-numerics.watsup:3.1-3.79
def unop : (unop_numtype, numtype, c_numtype) -> c_numtype*

;; 3-numerics.watsup:4.1-4.80
def binop : (binop_numtype, numtype, c_numtype, c_numtype) -> c_numtype*

;; 3-numerics.watsup:5.1-5.79
def testop : (testop_numtype, numtype, c_numtype) -> c_numtype

;; 3-numerics.watsup:6.1-6.80
def relop : (relop_numtype, numtype, c_numtype, c_numtype) -> c_numtype

;; 3-numerics.watsup:7.1-7.98
def cvtop : (cvtop, numtype, numtype, sx?, c_numtype) -> c_numtype*

;; 3-numerics.watsup:9.1-9.88
def wrap : (nat, nat, c_numtype) -> nat

;; 3-numerics.watsup:10.1-10.91
def ext : (nat, nat, sx, c_numtype) -> c_numtype

;; 3-numerics.watsup:12.1-12.83
def bytes : (nat, c_numtype) -> byte*

;; 4-runtime.watsup:5.1-5.39
syntax addr = nat

;; 4-runtime.watsup:6.1-6.53
syntax funcaddr = addr

;; 4-runtime.watsup:7.1-7.53
syntax globaladdr = addr

;; 4-runtime.watsup:8.1-8.51
syntax tableaddr = addr

;; 4-runtime.watsup:9.1-9.50
syntax memaddr = addr

;; 4-runtime.watsup:10.1-10.49
syntax elemaddr = addr

;; 4-runtime.watsup:11.1-11.49
syntax dataaddr = addr

;; 4-runtime.watsup:12.1-12.51
syntax labeladdr = addr

;; 4-runtime.watsup:13.1-13.49
syntax hostaddr = addr

;; 4-runtime.watsup:14.1-14.56
syntax structaddr = addr

;; 4-runtime.watsup:15.1-15.51
syntax arrayaddr = addr

;; 4-runtime.watsup:34.1-35.24
syntax num =
  | CONST(numtype, c_numtype)

;; 4-runtime.watsup:36.1-42.19
rec {

;; 4-runtime.watsup:36.1-42.19
syntax addrref =
  | REF.I31_NUM(i31)
  | REF.STRUCT_ADDR(structaddr)
  | REF.ARRAY_ADDR(arrayaddr)
  | REF.FUNC_ADDR(funcaddr)
  | REF.HOST_ADDR(hostaddr)
  | REF.EXTERN(addrref)
}

;; 4-runtime.watsup:43.1-45.8
syntax ref =
  | REF.I31_NUM(i31)
  | REF.STRUCT_ADDR(structaddr)
  | REF.ARRAY_ADDR(arrayaddr)
  | REF.FUNC_ADDR(funcaddr)
  | REF.HOST_ADDR(hostaddr)
  | REF.EXTERN(addrref)
  | REF.NULL(heaptype)

;; 4-runtime.watsup:46.1-47.10
syntax val =
  | CONST(numtype, c_numtype)
  | REF.NULL(heaptype)
  | REF.I31_NUM(i31)
  | REF.STRUCT_ADDR(structaddr)
  | REF.ARRAY_ADDR(arrayaddr)
  | REF.FUNC_ADDR(funcaddr)
  | REF.HOST_ADDR(hostaddr)
  | REF.EXTERN(addrref)

;; 4-runtime.watsup:49.1-50.18
syntax result =
  | _VALS(val*)
  | TRAP

;; 4-runtime.watsup:59.1-60.66
syntax externval =
  | FUNC(funcaddr)
  | GLOBAL(globaladdr)
  | TABLE(tableaddr)
  | MEM(memaddr)

;; 4-runtime.watsup:71.1-71.26
syntax c_packedtype = nat

;; 4-runtime.watsup:91.1-93.22
syntax exportinst = {NAME name, VALUE externval}

;; 4-runtime.watsup:106.1-114.25
syntax moduleinst = {TYPE deftype*, FUNC funcaddr*, GLOBAL globaladdr*, TABLE tableaddr*, MEM memaddr*, ELEM elemaddr*, DATA dataaddr*, EXPORT exportinst*}

;; 4-runtime.watsup:73.1-76.16
syntax funcinst = {TYPE deftype, MODULE moduleinst, CODE func}

;; 4-runtime.watsup:77.1-79.16
syntax globalinst = {TYPE globaltype, VALUE val}

;; 4-runtime.watsup:80.1-82.16
syntax tableinst = {TYPE tabletype, ELEM ref*}

;; 4-runtime.watsup:83.1-85.17
syntax meminst = {TYPE memtype, DATA byte*}

;; 4-runtime.watsup:86.1-88.16
syntax eleminst = {TYPE elemtype, ELEM ref*}

;; 4-runtime.watsup:89.1-90.17
syntax datainst = {DATA byte*}

;; 4-runtime.watsup:95.1-96.53
syntax packedval =
  | PACK(packedtype, c_packedtype)

;; 4-runtime.watsup:97.1-98.16
syntax fieldval =
  | CONST(numtype, c_numtype)
  | REF.NULL(heaptype)
  | REF.I31_NUM(i31)
  | REF.STRUCT_ADDR(structaddr)
  | REF.ARRAY_ADDR(arrayaddr)
  | REF.FUNC_ADDR(funcaddr)
  | REF.HOST_ADDR(hostaddr)
  | REF.EXTERN(addrref)
  | PACK(packedtype, c_packedtype)

;; 4-runtime.watsup:99.1-101.22
syntax structinst = {TYPE deftype, FIELD fieldval*}

;; 4-runtime.watsup:102.1-104.22
syntax arrayinst = {TYPE deftype, FIELD fieldval*}

;; 4-runtime.watsup:133.1-141.23
syntax store = {FUNC funcinst*, GLOBAL globalinst*, TABLE tableinst*, MEM meminst*, ELEM eleminst*, DATA datainst*, STRUCT structinst*, ARRAY arrayinst*}

;; 4-runtime.watsup:143.1-145.24
syntax frame = {LOCAL val?*, MODULE moduleinst}

;; 4-runtime.watsup:147.1-147.47
syntax state = `%;%`(store, frame)

;; 4-runtime.watsup:159.1-164.5
rec {

;; 4-runtime.watsup:159.1-164.5
syntax admininstr =
  | UNREACHABLE
  | NOP
  | DROP
  | SELECT(valtype?)
  | BLOCK(blocktype, instr*)
  | LOOP(blocktype, instr*)
  | IF(blocktype, instr*, instr*)
  | BR(labelidx)
  | BR_IF(labelidx)
  | BR_TABLE(labelidx*, labelidx)
  | BR_ON_NULL(labelidx)
  | BR_ON_NON_NULL(labelidx)
  | BR_ON_CAST(labelidx, reftype, reftype)
  | BR_ON_CAST_FAIL(labelidx, reftype, reftype)
  | CALL(funcidx)
  | CALL_REF(typeidx)
  | CALL_INDIRECT(tableidx, typeidx)
  | RETURN
  | RETURN_CALL(funcidx)
  | RETURN_CALL_REF(typeidx)
  | RETURN_CALL_INDIRECT(tableidx, typeidx)
  | CONST(numtype, c_numtype)
  | UNOP(numtype, unop_numtype)
  | BINOP(numtype, binop_numtype)
  | TESTOP(numtype, testop_numtype)
  | RELOP(numtype, relop_numtype)
  | EXTEND(numtype, n)
  | CVTOP(numtype, cvtop, numtype, sx?)
  | REF.NULL(heaptype)
  | REF.I31
  | REF.FUNC(funcidx)
  | REF.IS_NULL
  | REF.AS_NON_NULL
  | REF.EQ
  | REF.TEST(reftype)
  | REF.CAST(reftype)
  | I31.GET(sx)
  | STRUCT.NEW(typeidx)
  | STRUCT.NEW_DEFAULT(typeidx)
  | STRUCT.GET(sx?, typeidx, i32)
  | STRUCT.SET(typeidx, i32)
  | ARRAY.NEW(typeidx)
  | ARRAY.NEW_DEFAULT(typeidx)
  | ARRAY.NEW_FIXED(typeidx, nat)
  | ARRAY.NEW_DATA(typeidx, dataidx)
  | ARRAY.NEW_ELEM(typeidx, elemidx)
  | ARRAY.GET(sx?, typeidx)
  | ARRAY.SET(typeidx)
  | ARRAY.LEN
  | ARRAY.FILL(typeidx)
  | ARRAY.COPY(typeidx, typeidx)
  | ARRAY.INIT_DATA(typeidx, dataidx)
  | ARRAY.INIT_ELEM(typeidx, elemidx)
  | EXTERN.INTERNALIZE
  | EXTERN.EXTERNALIZE
  | LOCAL.GET(localidx)
  | LOCAL.SET(localidx)
  | LOCAL.TEE(localidx)
  | GLOBAL.GET(globalidx)
  | GLOBAL.SET(globalidx)
  | TABLE.GET(tableidx)
  | TABLE.SET(tableidx)
  | TABLE.SIZE(tableidx)
  | TABLE.GROW(tableidx)
  | TABLE.FILL(tableidx)
  | TABLE.COPY(tableidx, tableidx)
  | TABLE.INIT(tableidx, elemidx)
  | ELEM.DROP(elemidx)
  | MEMORY.SIZE(memidx)
  | MEMORY.GROW(memidx)
  | MEMORY.FILL(memidx)
  | MEMORY.COPY(memidx, memidx)
  | MEMORY.INIT(memidx, dataidx)
  | DATA.DROP(dataidx)
  | LOAD(numtype, (n, sx)?, memidx, i32, i32)
  | STORE(numtype, n?, memidx, i32, i32)
  | REF.I31_NUM(i31)
  | REF.STRUCT_ADDR(structaddr)
  | REF.ARRAY_ADDR(arrayaddr)
  | REF.FUNC_ADDR(funcaddr)
  | REF.HOST_ADDR(hostaddr)
  | REF.EXTERN(addrref)
  | LABEL_(n, instr*, admininstr*)
  | FRAME_(n, frame, admininstr*)
  | TRAP
}

;; 4-runtime.watsup:148.1-148.62
syntax config = `%;%*`(state, admininstr*)

;; 4-runtime.watsup:166.1-169.21
rec {

;; 4-runtime.watsup:166.1-169.21
syntax E =
  | _HOLE
  | _SEQ(val*, E, instr*)
  | LABEL_(n, instr*, E)
}

;; 5-runtime-aux.watsup:7.1-7.73
def inst_reftype : (moduleinst, reftype) -> reftype
  ;; 5-runtime-aux.watsup:9.1-10.22
  def {dt* : deftype*, mm : moduleinst, rt : reftype} inst_reftype(mm, rt) = $subst_all_reftype(rt, (dt <: heaptype)*{dt})
    -- if (dt*{dt} = mm.TYPE_moduleinst)

;; 5-runtime-aux.watsup:19.1-19.52
def default : valtype -> val?
  ;; 5-runtime-aux.watsup:21.1-21.34
  def default(I32_valtype) = ?(CONST_val(I32_numtype, 0))
  ;; 5-runtime-aux.watsup:22.1-22.34
  def default(I64_valtype) = ?(CONST_val(I64_numtype, 0))
  ;; 5-runtime-aux.watsup:23.1-23.34
  def default(F32_valtype) = ?(CONST_val(F32_numtype, 0))
  ;; 5-runtime-aux.watsup:24.1-24.34
  def default(F64_valtype) = ?(CONST_val(F64_numtype, 0))
  ;; 5-runtime-aux.watsup:25.1-25.42
  def {ht : heaptype} default(REF_valtype(`NULL%?`(?(())), ht)) = ?(REF.NULL_val(ht))
  ;; 5-runtime-aux.watsup:26.1-26.39
  def {ht : heaptype} default(REF_valtype(`NULL%?`(?()), ht)) = ?()

;; 5-runtime-aux.watsup:31.1-31.73
def packval : (storagetype, val) -> fieldval
  ;; 5-runtime-aux.watsup:34.1-34.27
  def {t : valtype, val : val} packval((t <: storagetype), val) = (val <: fieldval)
  ;; 5-runtime-aux.watsup:35.1-35.70
  def {i : nat, pt : packedtype} packval((pt <: storagetype), CONST_val(I32_numtype, i)) = PACK_fieldval(pt, $wrap(32, $packedsize(pt), i))

;; 5-runtime-aux.watsup:32.1-32.83
def unpackval : (storagetype, sx?, fieldval) -> val
  ;; 5-runtime-aux.watsup:37.1-37.38
  def {t : valtype, val : val} unpackval((t <: storagetype), ?(), (val <: fieldval)) = val
  ;; 5-runtime-aux.watsup:38.1-38.79
  def {i : nat, pt : packedtype, sx : sx} unpackval((pt <: storagetype), ?(sx), PACK_fieldval(pt, i)) = CONST_val(I32_numtype, $ext($packedsize(pt), 32, sx, i))

;; 5-runtime-aux.watsup:43.1-43.62
rec {

;; 5-runtime-aux.watsup:43.1-43.62
def funcsxv : externval* -> funcaddr*
  ;; 5-runtime-aux.watsup:48.1-48.32
  def funcsxv([]) = []
  ;; 5-runtime-aux.watsup:49.1-49.47
  def {fa : funcaddr, xv* : externval*} funcsxv([FUNC_externval(fa)] :: xv*{xv}) = [fa] :: $funcsxv(xv*{xv})
  ;; 5-runtime-aux.watsup:50.1-50.58
  def {externval : externval, xv* : externval*} funcsxv([externval] :: xv*{xv}) = $funcsxv(xv*{xv})
    -- otherwise
}

;; 5-runtime-aux.watsup:44.1-44.64
rec {

;; 5-runtime-aux.watsup:44.1-44.64
def globalsxv : externval* -> globaladdr*
  ;; 5-runtime-aux.watsup:52.1-52.34
  def globalsxv([]) = []
  ;; 5-runtime-aux.watsup:53.1-53.53
  def {ga : globaladdr, xv* : externval*} globalsxv([GLOBAL_externval(ga)] :: xv*{xv}) = [ga] :: $globalsxv(xv*{xv})
  ;; 5-runtime-aux.watsup:54.1-54.62
  def {externval : externval, xv* : externval*} globalsxv([externval] :: xv*{xv}) = $globalsxv(xv*{xv})
    -- otherwise
}

;; 5-runtime-aux.watsup:45.1-45.63
rec {

;; 5-runtime-aux.watsup:45.1-45.63
def tablesxv : externval* -> tableaddr*
  ;; 5-runtime-aux.watsup:56.1-56.33
  def tablesxv([]) = []
  ;; 5-runtime-aux.watsup:57.1-57.50
  def {ta : tableaddr, xv* : externval*} tablesxv([TABLE_externval(ta)] :: xv*{xv}) = [ta] :: $tablesxv(xv*{xv})
  ;; 5-runtime-aux.watsup:58.1-58.60
  def {externval : externval, xv* : externval*} tablesxv([externval] :: xv*{xv}) = $tablesxv(xv*{xv})
    -- otherwise
}

;; 5-runtime-aux.watsup:46.1-46.61
rec {

;; 5-runtime-aux.watsup:46.1-46.61
def memsxv : externval* -> memaddr*
  ;; 5-runtime-aux.watsup:60.1-60.31
  def memsxv([]) = []
  ;; 5-runtime-aux.watsup:61.1-61.44
  def {ma : memaddr, xv* : externval*} memsxv([MEM_externval(ma)] :: xv*{xv}) = [ma] :: $memsxv(xv*{xv})
  ;; 5-runtime-aux.watsup:62.1-62.56
  def {externval : externval, xv* : externval*} memsxv([externval] :: xv*{xv}) = $memsxv(xv*{xv})
    -- otherwise
}

;; 5-runtime-aux.watsup:72.1-72.57
def store : state -> store
  ;; 5-runtime-aux.watsup:75.1-75.23
  def {f : frame, s : store} store(`%;%`(s, f)) = s

;; 5-runtime-aux.watsup:73.1-73.57
def frame : state -> frame
  ;; 5-runtime-aux.watsup:76.1-76.23
  def {f : frame, s : store} frame(`%;%`(s, f)) = f

;; 5-runtime-aux.watsup:79.1-79.63
def funcaddr : state -> funcaddr*
  ;; 5-runtime-aux.watsup:80.1-80.38
  def {f : frame, s : store} funcaddr(`%;%`(s, f)) = f.MODULE_frame.FUNC_moduleinst

;; 5-runtime-aux.watsup:82.1-82.56
def funcinst : state -> funcinst*
  ;; 5-runtime-aux.watsup:92.1-92.31
  def {f : frame, s : store} funcinst(`%;%`(s, f)) = s.FUNC_store

;; 5-runtime-aux.watsup:83.1-83.58
def globalinst : state -> globalinst*
  ;; 5-runtime-aux.watsup:93.1-93.35
  def {f : frame, s : store} globalinst(`%;%`(s, f)) = s.GLOBAL_store

;; 5-runtime-aux.watsup:84.1-84.57
def tableinst : state -> tableinst*
  ;; 5-runtime-aux.watsup:94.1-94.33
  def {f : frame, s : store} tableinst(`%;%`(s, f)) = s.TABLE_store

;; 5-runtime-aux.watsup:85.1-85.55
def meminst : state -> meminst*
  ;; 5-runtime-aux.watsup:95.1-95.29
  def {f : frame, s : store} meminst(`%;%`(s, f)) = s.MEM_store

;; 5-runtime-aux.watsup:86.1-86.56
def eleminst : state -> eleminst*
  ;; 5-runtime-aux.watsup:96.1-96.31
  def {f : frame, s : store} eleminst(`%;%`(s, f)) = s.ELEM_store

;; 5-runtime-aux.watsup:87.1-87.56
def datainst : state -> datainst*
  ;; 5-runtime-aux.watsup:97.1-97.31
  def {f : frame, s : store} datainst(`%;%`(s, f)) = s.DATA_store

;; 5-runtime-aux.watsup:88.1-88.58
def structinst : state -> structinst*
  ;; 5-runtime-aux.watsup:98.1-98.35
  def {f : frame, s : store} structinst(`%;%`(s, f)) = s.STRUCT_store

;; 5-runtime-aux.watsup:89.1-89.57
def arrayinst : state -> arrayinst*
  ;; 5-runtime-aux.watsup:99.1-99.33
  def {f : frame, s : store} arrayinst(`%;%`(s, f)) = s.ARRAY_store

;; 5-runtime-aux.watsup:90.1-90.58
def moduleinst : state -> moduleinst
  ;; 5-runtime-aux.watsup:100.1-100.35
  def {f : frame, s : store} moduleinst(`%;%`(s, f)) = f.MODULE_frame

;; 5-runtime-aux.watsup:102.1-102.66
def type : (state, typeidx) -> deftype
  ;; 5-runtime-aux.watsup:111.1-111.40
  def {f : frame, s : store, x : idx} type(`%;%`(s, f), x) = f.MODULE_frame.TYPE_moduleinst[x]

;; 5-runtime-aux.watsup:103.1-103.67
def func : (state, funcidx) -> funcinst
  ;; 5-runtime-aux.watsup:112.1-112.48
  def {f : frame, s : store, x : idx} func(`%;%`(s, f), x) = s.FUNC_store[f.MODULE_frame.FUNC_moduleinst[x]]

;; 5-runtime-aux.watsup:104.1-104.69
def global : (state, globalidx) -> globalinst
  ;; 5-runtime-aux.watsup:113.1-113.54
  def {f : frame, s : store, x : idx} global(`%;%`(s, f), x) = s.GLOBAL_store[f.MODULE_frame.GLOBAL_moduleinst[x]]

;; 5-runtime-aux.watsup:105.1-105.68
def table : (state, tableidx) -> tableinst
  ;; 5-runtime-aux.watsup:114.1-114.51
  def {f : frame, s : store, x : idx} table(`%;%`(s, f), x) = s.TABLE_store[f.MODULE_frame.TABLE_moduleinst[x]]

;; 5-runtime-aux.watsup:106.1-106.66
def mem : (state, memidx) -> meminst
  ;; 5-runtime-aux.watsup:115.1-115.45
  def {f : frame, s : store, x : idx} mem(`%;%`(s, f), x) = s.MEM_store[f.MODULE_frame.MEM_moduleinst[x]]

;; 5-runtime-aux.watsup:107.1-107.67
def elem : (state, tableidx) -> eleminst
  ;; 5-runtime-aux.watsup:116.1-116.48
  def {f : frame, s : store, x : idx} elem(`%;%`(s, f), x) = s.ELEM_store[f.MODULE_frame.ELEM_moduleinst[x]]

;; 5-runtime-aux.watsup:108.1-108.67
def data : (state, dataidx) -> datainst
  ;; 5-runtime-aux.watsup:117.1-117.48
  def {f : frame, s : store, x : idx} data(`%;%`(s, f), x) = s.DATA_store[f.MODULE_frame.DATA_moduleinst[x]]

;; 5-runtime-aux.watsup:109.1-109.68
def local : (state, localidx) -> val?
  ;; 5-runtime-aux.watsup:118.1-118.35
  def {f : frame, s : store, x : idx} local(`%;%`(s, f), x) = f.LOCAL_frame[x]

;; 5-runtime-aux.watsup:123.1-123.88
def with_local : (state, localidx, val) -> state
  ;; 5-runtime-aux.watsup:134.1-134.52
  def {f : frame, s : store, v : val, x : idx} with_local(`%;%`(s, f), x, v) = `%;%`(s, f[LOCAL_frame[x] = ?(v)])

;; 5-runtime-aux.watsup:124.1-124.95
def with_global : (state, globalidx, val) -> state
  ;; 5-runtime-aux.watsup:135.1-135.77
  def {f : frame, s : store, v : val, x : idx} with_global(`%;%`(s, f), x, v) = `%;%`(s[GLOBAL_store[f.MODULE_frame.GLOBAL_moduleinst[x]].VALUE_globalinst = v], f)

;; 5-runtime-aux.watsup:125.1-125.96
def with_table : (state, tableidx, nat, ref) -> state
  ;; 5-runtime-aux.watsup:136.1-136.79
  def {f : frame, i : nat, r : ref, s : store, x : idx} with_table(`%;%`(s, f), x, i, r) = `%;%`(s[TABLE_store[f.MODULE_frame.TABLE_moduleinst[x]].ELEM_tableinst[i] = r], f)

;; 5-runtime-aux.watsup:126.1-126.88
def with_tableinst : (state, tableidx, tableinst) -> state
  ;; 5-runtime-aux.watsup:137.1-137.74
  def {f : frame, s : store, ti : tableinst, x : idx} with_tableinst(`%;%`(s, f), x, ti) = `%;%`(s[TABLE_store[f.MODULE_frame.TABLE_moduleinst[x]] = ti], f)

;; 5-runtime-aux.watsup:127.1-127.98
def with_mem : (state, memidx, nat, nat, byte*) -> state
  ;; 5-runtime-aux.watsup:138.1-138.82
  def {b* : byte*, f : frame, i : nat, j : nat, s : store, x : idx} with_mem(`%;%`(s, f), x, i, j, b*{b}) = `%;%`(s[MEM_store[f.MODULE_frame.MEM_moduleinst[x]].DATA_meminst[i : j] = b*{b}], f)

;; 5-runtime-aux.watsup:128.1-128.86
def with_meminst : (state, memidx, meminst) -> state
  ;; 5-runtime-aux.watsup:139.1-139.68
  def {f : frame, mi : meminst, s : store, x : idx} with_meminst(`%;%`(s, f), x, mi) = `%;%`(s[MEM_store[f.MODULE_frame.MEM_moduleinst[x]] = mi], f)

;; 5-runtime-aux.watsup:129.1-129.92
def with_elem : (state, elemidx, ref*) -> state
  ;; 5-runtime-aux.watsup:140.1-140.72
  def {f : frame, r* : ref*, s : store, x : idx} with_elem(`%;%`(s, f), x, r*{r}) = `%;%`(s[ELEM_store[f.MODULE_frame.ELEM_moduleinst[x]].ELEM_eleminst = r*{r}], f)

;; 5-runtime-aux.watsup:130.1-130.92
def with_data : (state, dataidx, byte*) -> state
  ;; 5-runtime-aux.watsup:141.1-141.72
  def {b* : byte*, f : frame, s : store, x : idx} with_data(`%;%`(s, f), x, b*{b}) = `%;%`(s[DATA_store[f.MODULE_frame.DATA_moduleinst[x]].DATA_datainst = b*{b}], f)

;; 5-runtime-aux.watsup:131.1-131.98
def with_struct : (state, structaddr, nat, fieldval) -> state
  ;; 5-runtime-aux.watsup:142.1-142.68
  def {a : addr, f : frame, fv : fieldval, i : nat, s : store} with_struct(`%;%`(s, f), a, i, fv) = `%;%`(s[STRUCT_store[a].FIELD_structinst[i] = fv], f)

;; 5-runtime-aux.watsup:132.1-132.98
def with_array : (state, arrayaddr, nat, fieldval) -> state
  ;; 5-runtime-aux.watsup:143.1-143.66
  def {a : addr, f : frame, fv : fieldval, i : nat, s : store} with_array(`%;%`(s, f), a, i, fv) = `%;%`(s[ARRAY_store[a].FIELD_arrayinst[i] = fv], f)

;; 5-runtime-aux.watsup:145.1-145.77
def ext_structinst : (state, structinst*) -> state
  ;; 5-runtime-aux.watsup:148.1-148.57
  def {f : frame, s : store, si* : structinst*} ext_structinst(`%;%`(s, f), si*{si}) = `%;%`(s[STRUCT_store =.. si*{si}], f)

;; 5-runtime-aux.watsup:146.1-146.76
def ext_arrayinst : (state, arrayinst*) -> state
  ;; 5-runtime-aux.watsup:149.1-149.55
  def {ai* : arrayinst*, f : frame, s : store} ext_arrayinst(`%;%`(s, f), ai*{ai}) = `%;%`(s[ARRAY_store =.. ai*{ai}], f)

;; 5-runtime-aux.watsup:154.1-154.62
def growtable : (tableinst, nat, ref) -> tableinst
  ;; 5-runtime-aux.watsup:157.1-160.22
  def {i : nat, j : nat, n : n, r : ref, r'* : ref*, rt : reftype, ti : tableinst, tt' : tabletype} growtable(ti, n, r) = {TYPE tt', ELEM r'*{r'} :: r^n{}}
    -- if (ti = {TYPE `%%`(`[%..%]`(i, j), rt), ELEM r'*{r'}})
    -- if (tt' = `%%`(`[%..%]`((i + n), j), rt))
    -- if ((i + n) <= j)

;; 5-runtime-aux.watsup:155.1-155.54
def growmemory : (meminst, nat) -> meminst
  ;; 5-runtime-aux.watsup:162.1-165.22
  def {b* : byte*, i : nat, j : nat, mi : meminst, mt' : memtype, n : n} growmemory(mi, n) = {TYPE mt', DATA b*{b} :: 0^((n * 64) * $Ki){}}
    -- if (mi = {TYPE `%I8`(`[%..%]`(i, j)), DATA b*{b}})
    -- if (mt' = `%I8`(`[%..%]`((i + n), j)))
    -- if ((i + n) <= j)

;; 6-typing.watsup:5.1-6.12
syntax init =
  | SET
  | UNSET

;; 6-typing.watsup:8.1-9.15
syntax localtype = `%%`(init, valtype)

;; 6-typing.watsup:11.1-12.37
syntax instrtype = `%->%*%`(resulttype, localidx*, resulttype)

;; 6-typing.watsup:15.1-19.62
syntax context = {TYPE deftype*, REC subtype*, FUNC deftype*, GLOBAL globaltype*, TABLE tabletype*, MEM memtype*, ELEM elemtype*, DATA datatype*, LOCAL localtype*, LABEL resulttype*, RETURN resulttype?}

;; 6-typing.watsup:26.1-26.86
rec {

;; 6-typing.watsup:26.1-26.86
def with_locals : (context, localidx*, localtype*) -> context
  ;; 6-typing.watsup:28.1-28.42
  def {C : context} with_locals(C, [], []) = C
  ;; 6-typing.watsup:29.1-29.85
  def {C : context, lt* : localtype*, lt_1 : localtype, x* : idx*, x_1 : idx} with_locals(C, [x_1] :: x*{x}, [lt_1] :: lt*{lt}) = $with_locals(C[LOCAL_context[x_1] = lt_1], x*{x}, lt*{lt})
}

;; 6-typing.watsup:33.1-33.65
rec {

;; 6-typing.watsup:33.1-33.65
def clostypes : deftype* -> deftype*
  ;; 6-typing.watsup:37.1-37.34
  def clostypes([]) = []
  ;; 6-typing.watsup:38.1-38.93
  def {dt* : deftype*, dt'* : deftype*, dt_N : deftype} clostypes(dt*{dt} :: [dt_N]) = dt'*{dt'} :: [$subst_all_deftype(dt_N, (dt' <: heaptype)*{dt'})]
    -- if (dt'*{dt'} = $clostypes(dt*{dt}))
}

;; 6-typing.watsup:32.1-32.65
def clostype : (context, deftype) -> deftype
  ;; 6-typing.watsup:35.1-35.84
  def {C : context, dt : deftype, dt'* : deftype*} clostype(C, dt) = $subst_all_deftype(dt, (dt' <: heaptype)*{dt'})
    -- if (dt'*{dt'} = $clostypes(C.TYPE_context))

;; 6-typing.watsup:47.1-47.71
relation Numtype_ok: `%|-%:OK`(context, numtype)
  ;; 6-typing.watsup:54.1-55.20
  rule _ {C : context, numtype : numtype}:
    `%|-%:OK`(C, numtype)

;; 6-typing.watsup:48.1-48.71
relation Vectype_ok: `%|-%:OK`(context, vectype)
  ;; 6-typing.watsup:57.1-58.20
  rule _ {C : context, vectype : vectype}:
    `%|-%:OK`(C, vectype)

;; 6-typing.watsup:49.1-49.72
relation Heaptype_ok: `%|-%:OK`(context, heaptype)
  ;; 6-typing.watsup:60.1-61.24
  rule abs {C : context, absheaptype : absheaptype}:
    `%|-%:OK`(C, (absheaptype <: heaptype))

  ;; 6-typing.watsup:63.1-65.23
  rule typeidx {C : context, dt : deftype, x : idx}:
    `%|-%:OK`(C, _IDX_heaptype(x))
    -- if (C.TYPE_context[x] = dt)

  ;; 6-typing.watsup:67.1-69.22
  rule rec {C : context, i : nat, st : subtype}:
    `%|-%:OK`(C, REC_heaptype(i))
    -- if (C.REC_context[i] = st)

;; 6-typing.watsup:50.1-50.71
relation Reftype_ok: `%|-%:OK`(context, reftype)
  ;; 6-typing.watsup:71.1-73.31
  rule _ {C : context, ht : heaptype, nul : nul}:
    `%|-%:OK`(C, REF_reftype(nul, ht))
    -- Heaptype_ok: `%|-%:OK`(C, ht)

;; 6-typing.watsup:51.1-51.71
relation Valtype_ok: `%|-%:OK`(context, valtype)
  ;; 6-typing.watsup:75.1-77.35
  rule num {C : context, numtype : numtype}:
    `%|-%:OK`(C, (numtype <: valtype))
    -- Numtype_ok: `%|-%:OK`(C, numtype)

  ;; 6-typing.watsup:79.1-81.35
  rule vec {C : context, vectype : vectype}:
    `%|-%:OK`(C, (vectype <: valtype))
    -- Vectype_ok: `%|-%:OK`(C, vectype)

  ;; 6-typing.watsup:83.1-85.35
  rule ref {C : context, reftype : reftype}:
    `%|-%:OK`(C, (reftype <: valtype))
    -- Reftype_ok: `%|-%:OK`(C, reftype)

  ;; 6-typing.watsup:87.1-88.16
  rule bot {C : context}:
    `%|-%:OK`(C, BOT_valtype)

;; 6-typing.watsup:93.1-93.74
relation Resulttype_ok: `%|-%:OK`(context, resulttype)
  ;; 6-typing.watsup:96.1-98.32
  rule _ {C : context, t* : valtype*}:
    `%|-%:OK`(C, t*{t})
    -- (Valtype_ok: `%|-%:OK`(C, t))*{t}

;; 6-typing.watsup:94.1-94.73
relation Instrtype_ok: `%|-%:OK`(context, instrtype)
  ;; 6-typing.watsup:100.1-104.27
  rule _ {C : context, lt* : localtype*, t_1* : valtype*, t_2* : valtype*, x* : idx*}:
    `%|-%:OK`(C, `%->%*%`(t_1*{t_1}, x*{x}, t_2*{t_2}))
    -- Resulttype_ok: `%|-%:OK`(C, t_1*{t_1})
    -- Resulttype_ok: `%|-%:OK`(C, t_2*{t_2})
    -- (if (C.LOCAL_context[x] = lt))*{lt x}

;; 6-typing.watsup:109.1-109.84
syntax oktypeidx =
  | OK(typeidx)

;; 6-typing.watsup:110.1-110.87
syntax oktypeidxnat =
  | OK(typeidx, nat)

;; 6-typing.watsup:112.1-112.76
relation Packedtype_ok: `%|-%:OK`(context, packedtype)
  ;; 6-typing.watsup:128.1-129.23
  rule _ {C : context, packedtype : packedtype}:
    `%|-%:OK`(C, packedtype)

;; 6-typing.watsup:114.1-114.77
relation Storagetype_ok: `%|-%:OK`(context, storagetype)
  ;; 6-typing.watsup:131.1-133.35
  rule val {C : context, valtype : valtype}:
    `%|-%:OK`(C, (valtype <: storagetype))
    -- Valtype_ok: `%|-%:OK`(C, valtype)

  ;; 6-typing.watsup:135.1-137.41
  rule packed {C : context, packedtype : packedtype}:
    `%|-%:OK`(C, (packedtype <: storagetype))
    -- Packedtype_ok: `%|-%:OK`(C, packedtype)

;; 6-typing.watsup:113.1-113.75
relation Fieldtype_ok: `%|-%:OK`(context, fieldtype)
  ;; 6-typing.watsup:139.1-141.34
  rule _ {C : context, mut : mut, zt : storagetype}:
    `%|-%:OK`(C, `%%`(mut, zt))
    -- Storagetype_ok: `%|-%:OK`(C, zt)

;; 6-typing.watsup:116.1-116.74
relation Functype_ok: `%|-%:OK`(context, functype)
  ;; 6-typing.watsup:225.1-228.35
  rule _ {C : context, t_1* : valtype*, t_2* : valtype*}:
    `%|-%:OK`(C, `%->%`(t_1*{t_1}, t_2*{t_2}))
    -- Resulttype_ok: `%|-%:OK`(C, t_1*{t_1})
    -- Resulttype_ok: `%|-%:OK`(C, t_2*{t_2})

;; 6-typing.watsup:115.1-115.74
relation Comptype_ok: `%|-%:OK`(context, comptype)
  ;; 6-typing.watsup:144.1-146.35
  rule struct {C : context, yt* : fieldtype*}:
    `%|-%:OK`(C, STRUCT_comptype(yt*{yt}))
    -- (Fieldtype_ok: `%|-%:OK`(C, yt))*{yt}

  ;; 6-typing.watsup:148.1-150.32
  rule array {C : context, yt : fieldtype}:
    `%|-%:OK`(C, ARRAY_comptype(yt))
    -- Fieldtype_ok: `%|-%:OK`(C, yt)

  ;; 6-typing.watsup:152.1-154.31
  rule func {C : context, ft : functype}:
    `%|-%:OK`(C, FUNC_comptype(ft))
    -- Functype_ok: `%|-%:OK`(C, ft)

;; 6-typing.watsup:391.1-391.91
relation Packedtype_sub: `%|-%<:%`(context, packedtype, packedtype)
  ;; 6-typing.watsup:398.1-399.32
  rule _ {C : context, packedtype : packedtype}:
    `%|-%<:%`(C, packedtype, packedtype)

;; 6-typing.watsup:269.1-269.78
relation Numtype_sub: `%|-%<:%`(context, numtype, numtype)
  ;; 6-typing.watsup:275.1-276.26
  rule _ {C : context, numtype : numtype}:
    `%|-%<:%`(C, numtype, numtype)

;; 6-typing.watsup:125.1-271.79
rec {

;; 6-typing.watsup:125.1-125.75
relation Deftype_sub: `%|-%<:%`(context, deftype, deftype)
  ;; 6-typing.watsup:434.1-436.58
  rule refl {C : context, deftype_1 : deftype, deftype_2 : deftype}:
    `%|-%<:%`(C, deftype_1, deftype_2)
    -- if ($clostype(C, deftype_1) = $clostype(C, deftype_2))

  ;; 6-typing.watsup:438.1-441.40
  rule super {C : context, ct : comptype, deftype_1 : deftype, deftype_2 : deftype, fin : fin, ht : heaptype, ht_1* : heaptype*, ht_2* : heaptype*}:
    `%|-%<:%`(C, deftype_1, deftype_2)
    -- if ($unrolldt(deftype_1) = SUBD_subtype(fin, ht_1*{ht_1} :: [ht] :: ht_2*{ht_2}, ct))
    -- Heaptype_sub: `%|-%<:%`(C, ht, (deftype_2 <: heaptype))

;; 6-typing.watsup:271.1-271.79
relation Heaptype_sub: `%|-%<:%`(context, heaptype, heaptype)
  ;; 6-typing.watsup:282.1-283.28
  rule refl {C : context, heaptype : heaptype}:
    `%|-%<:%`(C, heaptype, heaptype)

  ;; 6-typing.watsup:285.1-289.48
  rule trans {C : context, heaptype' : heaptype, heaptype_1 : heaptype, heaptype_2 : heaptype}:
    `%|-%<:%`(C, heaptype_1, heaptype_2)
    -- Heaptype_ok: `%|-%:OK`(C, heaptype')
    -- Heaptype_sub: `%|-%<:%`(C, heaptype_1, heaptype')
    -- Heaptype_sub: `%|-%<:%`(C, heaptype', heaptype_2)

  ;; 6-typing.watsup:291.1-292.17
  rule eq-any {C : context}:
    `%|-%<:%`(C, EQ_heaptype, ANY_heaptype)

  ;; 6-typing.watsup:294.1-295.17
  rule i31-eq {C : context}:
    `%|-%<:%`(C, I31_heaptype, EQ_heaptype)

  ;; 6-typing.watsup:297.1-298.20
  rule struct-eq {C : context}:
    `%|-%<:%`(C, STRUCT_heaptype, EQ_heaptype)

  ;; 6-typing.watsup:300.1-301.19
  rule array-eq {C : context}:
    `%|-%<:%`(C, ARRAY_heaptype, EQ_heaptype)

  ;; 6-typing.watsup:303.1-305.35
  rule struct {C : context, deftype : deftype, yt* : fieldtype*}:
    `%|-%<:%`(C, (deftype <: heaptype), STRUCT_heaptype)
    -- Expand: `%~~%`(deftype, STRUCT_comptype(yt*{yt}))

  ;; 6-typing.watsup:307.1-309.33
  rule array {C : context, deftype : deftype, yt : fieldtype}:
    `%|-%<:%`(C, (deftype <: heaptype), ARRAY_heaptype)
    -- Expand: `%~~%`(deftype, ARRAY_comptype(yt))

  ;; 6-typing.watsup:311.1-313.32
  rule func {C : context, deftype : deftype, ft : functype}:
    `%|-%<:%`(C, (deftype <: heaptype), FUNC_heaptype)
    -- Expand: `%~~%`(deftype, FUNC_comptype(ft))

  ;; 6-typing.watsup:315.1-317.46
  rule def {C : context, deftype_1 : deftype, deftype_2 : deftype}:
    `%|-%<:%`(C, (deftype_1 <: heaptype), (deftype_2 <: heaptype))
    -- Deftype_sub: `%|-%<:%`(C, deftype_1, deftype_2)

  ;; 6-typing.watsup:319.1-321.52
  rule typeidx-l {C : context, heaptype : heaptype, typeidx : typeidx}:
    `%|-%<:%`(C, _IDX_heaptype(typeidx), heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, (C.TYPE_context[typeidx] <: heaptype), heaptype)

  ;; 6-typing.watsup:323.1-325.52
  rule typeidx-r {C : context, heaptype : heaptype, typeidx : typeidx}:
    `%|-%<:%`(C, heaptype, _IDX_heaptype(typeidx))
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, (C.TYPE_context[typeidx] <: heaptype))

  ;; 6-typing.watsup:327.1-329.48
  rule rec {C : context, ct : comptype, fin : fin, ht : heaptype, ht_1* : heaptype*, ht_2* : heaptype*, i : nat}:
    `%|-%<:%`(C, REC_heaptype(i), ht)
    -- if (C.REC_context[i] = SUBD_subtype(fin, ht_1*{ht_1} :: [ht] :: ht_2*{ht_2}, ct))

  ;; 6-typing.watsup:331.1-333.40
  rule none {C : context, heaptype : heaptype}:
    `%|-%<:%`(C, NONE_heaptype, heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, ANY_heaptype)

  ;; 6-typing.watsup:335.1-337.41
  rule nofunc {C : context, heaptype : heaptype}:
    `%|-%<:%`(C, NOFUNC_heaptype, heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, FUNC_heaptype)

  ;; 6-typing.watsup:339.1-341.43
  rule noextern {C : context, heaptype : heaptype}:
    `%|-%<:%`(C, NOEXTERN_heaptype, heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, EXTERN_heaptype)

  ;; 6-typing.watsup:343.1-344.23
  rule bot {C : context, heaptype : heaptype}:
    `%|-%<:%`(C, BOT_heaptype, heaptype)
}

;; 6-typing.watsup:272.1-272.78
relation Reftype_sub: `%|-%<:%`(context, reftype, reftype)
  ;; 6-typing.watsup:347.1-349.37
  rule nonnull {C : context, ht_1 : heaptype, ht_2 : heaptype}:
    `%|-%<:%`(C, REF_reftype(`NULL%?`(?()), ht_1), REF_reftype(`NULL%?`(?()), ht_2))
    -- Heaptype_sub: `%|-%<:%`(C, ht_1, ht_2)

  ;; 6-typing.watsup:351.1-353.37
  rule null {C : context, ht_1 : heaptype, ht_2 : heaptype, nul : nul}:
    `%|-%<:%`(C, REF_reftype(nul, ht_1), REF_reftype(`NULL%?`(?(())), ht_2))
    -- Heaptype_sub: `%|-%<:%`(C, ht_1, ht_2)

;; 6-typing.watsup:270.1-270.78
relation Vectype_sub: `%|-%<:%`(context, vectype, vectype)
  ;; 6-typing.watsup:278.1-279.26
  rule _ {C : context, vectype : vectype}:
    `%|-%<:%`(C, vectype, vectype)

;; 6-typing.watsup:273.1-273.78
relation Valtype_sub: `%|-%<:%`(context, valtype, valtype)
  ;; 6-typing.watsup:356.1-358.46
  rule num {C : context, numtype_1 : numtype, numtype_2 : numtype}:
    `%|-%<:%`(C, (numtype_1 <: valtype), (numtype_2 <: valtype))
    -- Numtype_sub: `%|-%<:%`(C, numtype_1, numtype_2)

  ;; 6-typing.watsup:360.1-362.46
  rule vec {C : context, vectype_1 : vectype, vectype_2 : vectype}:
    `%|-%<:%`(C, (vectype_1 <: valtype), (vectype_2 <: valtype))
    -- Vectype_sub: `%|-%<:%`(C, vectype_1, vectype_2)

  ;; 6-typing.watsup:364.1-366.46
  rule ref {C : context, reftype_1 : reftype, reftype_2 : reftype}:
    `%|-%<:%`(C, (reftype_1 <: valtype), (reftype_2 <: valtype))
    -- Reftype_sub: `%|-%<:%`(C, reftype_1, reftype_2)

  ;; 6-typing.watsup:368.1-369.22
  rule bot {C : context, valtype : valtype}:
    `%|-%<:%`(C, BOT_valtype, valtype)

;; 6-typing.watsup:392.1-392.92
relation Storagetype_sub: `%|-%<:%`(context, storagetype, storagetype)
  ;; 6-typing.watsup:402.1-404.46
  rule val {C : context, valtype_1 : valtype, valtype_2 : valtype}:
    `%|-%<:%`(C, (valtype_1 <: storagetype), (valtype_2 <: storagetype))
    -- Valtype_sub: `%|-%<:%`(C, valtype_1, valtype_2)

  ;; 6-typing.watsup:406.1-408.55
  rule packed {C : context, packedtype_1 : packedtype, packedtype_2 : packedtype}:
    `%|-%<:%`(C, (packedtype_1 <: storagetype), (packedtype_2 <: storagetype))
    -- Packedtype_sub: `%|-%<:%`(C, packedtype_1, packedtype_2)

;; 6-typing.watsup:393.1-393.90
relation Fieldtype_sub: `%|-%<:%`(context, fieldtype, fieldtype)
  ;; 6-typing.watsup:411.1-413.40
  rule const {C : context, zt_1 : storagetype, zt_2 : storagetype}:
    `%|-%<:%`(C, `%%`(`MUT%?`(?()), zt_1), `%%`(`MUT%?`(?()), zt_2))
    -- Storagetype_sub: `%|-%<:%`(C, zt_1, zt_2)

  ;; 6-typing.watsup:415.1-418.40
  rule var {C : context, zt_1 : storagetype, zt_2 : storagetype}:
    `%|-%<:%`(C, `%%`(`MUT%?`(?(())), zt_1), `%%`(`MUT%?`(?(())), zt_2))
    -- Storagetype_sub: `%|-%<:%`(C, zt_1, zt_2)
    -- Storagetype_sub: `%|-%<:%`(C, zt_2, zt_1)

;; 6-typing.watsup:395.1-395.89
relation Functype_sub: `%|-%<:%`(context, functype, functype)
  ;; 6-typing.watsup:458.1-459.16
  rule _ {C : context, ft : functype}:
    `%|-%<:%`(C, ft, ft)

;; 6-typing.watsup:124.1-124.76
relation Comptype_sub: `%|-%<:%`(context, comptype, comptype)
  ;; 6-typing.watsup:421.1-423.41
  rule struct {C : context, yt'_1 : fieldtype, yt_1* : fieldtype*, yt_2* : fieldtype*}:
    `%|-%<:%`(C, STRUCT_comptype(yt_1*{yt_1} :: [yt'_1]), STRUCT_comptype(yt_2*{yt_2}))
    -- (Fieldtype_sub: `%|-%<:%`(C, yt_1, yt_2))*{yt_1 yt_2}

  ;; 6-typing.watsup:425.1-427.38
  rule array {C : context, yt_1 : fieldtype, yt_2 : fieldtype}:
    `%|-%<:%`(C, ARRAY_comptype(yt_1), ARRAY_comptype(yt_2))
    -- Fieldtype_sub: `%|-%<:%`(C, yt_1, yt_2)

  ;; 6-typing.watsup:429.1-431.37
  rule func {C : context, ft_1 : functype, ft_2 : functype}:
    `%|-%<:%`(C, FUNC_comptype(ft_1), FUNC_comptype(ft_2))
    -- Functype_sub: `%|-%<:%`(C, ft_1, ft_2)

;; 6-typing.watsup:117.1-117.73
relation Subtype_ok: `%|-%:%`(context, subtype, oktypeidx)
  ;; 6-typing.watsup:157.1-163.37
  rule _ {C : context, ct : comptype, ct'* : comptype*, fin : fin, x : idx, y* : idx*, y'** : idx**}:
    `%|-%:%`(C, SUB_subtype(fin, y*{y}, ct), OK_oktypeidx(x))
    -- if (|y*{y}| <= 1)
    -- (if (y < x))*{y}
    -- (if ($unrolldt(C.TYPE_context[y]) = SUB_subtype(`FINAL%?`(?()), y'*{y'}, ct')))*{ct' y y'}
    -- Comptype_ok: `%|-%:OK`(C, ct)
    -- (Comptype_sub: `%|-%<:%`(C, ct, ct'))*{ct'}

;; 6-typing.watsup:165.1-165.65
def before : (heaptype, typeidx, nat) -> bool
  ;; 6-typing.watsup:166.1-166.34
  def {deftype : deftype, i : nat, x : idx} before((deftype <: heaptype), x, i) = true
  ;; 6-typing.watsup:167.1-167.46
  def {i : nat, typeidx : typeidx, x : idx} before(_IDX_heaptype(typeidx), x, i) = (typeidx < x)
  ;; 6-typing.watsup:168.1-168.33
  def {i : nat, j : nat, x : idx} before(REC_heaptype(j), x, i) = (j < i)

;; 6-typing.watsup:170.1-170.69
def unrollht : (context, heaptype) -> subtype
  ;; 6-typing.watsup:171.1-171.47
  def {C : context, deftype : deftype} unrollht(C, (deftype <: heaptype)) = $unrolldt(deftype)
  ;; 6-typing.watsup:172.1-172.60
  def {C : context, typeidx : typeidx} unrollht(C, _IDX_heaptype(typeidx)) = $unrolldt(C.TYPE_context[typeidx])
  ;; 6-typing.watsup:173.1-173.35
  def {C : context, i : nat} unrollht(C, REC_heaptype(i)) = C.REC_context[i]

;; 6-typing.watsup:119.1-119.76
relation Subtype_ok2: `%|-%:%`(context, subtype, oktypeidxnat)
  ;; 6-typing.watsup:175.1-181.37
  rule _ {C : context, ct : comptype, ct'* : comptype*, fin : fin, ht* : heaptype*, ht'** : heaptype**, i : nat, x : idx, y* : idx*}:
    `%|-%:%`(C, SUBD_subtype(fin, ht*{ht}, ct), OK_oktypeidxnat(x, i))
    -- if (|y*{y}| <= 1)
    -- (if $before(ht, x, i))*{ht}
    -- (if ($unrollht(C, ht) = SUBD_subtype(`FINAL%?`(?()), ht'*{ht'}, ct')))*{ct' ht ht'}
    -- Comptype_ok: `%|-%:OK`(C, ct)
    -- (Comptype_sub: `%|-%<:%`(C, ct, ct'))*{ct'}

;; 6-typing.watsup:120.1-120.76
rec {

;; 6-typing.watsup:120.1-120.76
relation Rectype_ok2: `%|-%:%`(context, rectype, oktypeidxnat)
  ;; 6-typing.watsup:196.1-197.28
  rule empty {C : context, i : nat, x : idx}:
    `%|-%:%`(C, REC_rectype([]), OK_oktypeidxnat(x, i))

  ;; 6-typing.watsup:199.1-202.50
  rule cons {C : context, i : nat, st* : subtype*, st_1 : subtype, x : idx}:
    `%|-%:%`(C, REC_rectype([st_1] :: st*{st}), OK_oktypeidxnat(x, i))
    -- Subtype_ok2: `%|-%:%`(C, st_1, OK_oktypeidxnat(x, i))
    -- Rectype_ok2: `%|-%:%`(C, REC_rectype(st*{st}), OK_oktypeidxnat((x + 1), (i + 1)))
}

;; 6-typing.watsup:118.1-118.74
rec {

;; 6-typing.watsup:118.1-118.74
relation Rectype_ok: `%|-%:%`(context, rectype, oktypeidx)
  ;; 6-typing.watsup:184.1-185.27
  rule empty {C : context, x : idx}:
    `%|-%:%`(C, REC_rectype([]), OK_oktypeidx(x))

  ;; 6-typing.watsup:187.1-190.43
  rule cons {C : context, st* : subtype*, st_1 : subtype, x : idx}:
    `%|-%:%`(C, REC_rectype([st_1] :: st*{st}), OK_oktypeidx(x))
    -- Subtype_ok: `%|-%:%`(C, st_1, OK_oktypeidx(x))
    -- Rectype_ok: `%|-%:%`(C, REC_rectype(st*{st}), OK_oktypeidx(x + 1))

  ;; 6-typing.watsup:192.1-194.49
  rule rec2 {C : context, st* : subtype*, x : idx}:
    `%|-%:%`(C, REC_rectype(st*{st}), OK_oktypeidx(x))
    -- Rectype_ok2: `%|-%:%`(C ++ {TYPE [], REC st*{st}, FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [], RETURN ?()}, REC_rectype(st*{st}), OK_oktypeidxnat(x, 0))
}

;; 6-typing.watsup:121.1-121.73
relation Deftype_ok: `%|-%:OK`(context, deftype)
  ;; 6-typing.watsup:205.1-209.14
  rule _ {C : context, i : nat, n : n, qt : rectype, st^n : subtype^n, x : idx}:
    `%|-%:OK`(C, DEF_deftype(qt, i))
    -- Rectype_ok: `%|-%:%`(C, qt, OK_oktypeidx(x))
    -- if (qt = REC_rectype(st^n{st}))
    -- if (i < n)

;; 6-typing.watsup:214.1-214.74
relation Limits_ok: `%|-%:%`(context, limits, nat)
  ;; 6-typing.watsup:221.1-223.24
  rule _ {C : context, k : nat, n_1 : n, n_2 : n}:
    `%|-%:%`(C, `[%..%]`(n_1, n_2), k)
    -- if ((n_1 <= n_2) /\ (n_2 <= k))

;; 6-typing.watsup:215.1-215.74
relation Globaltype_ok: `%|-%:OK`(context, globaltype)
  ;; 6-typing.watsup:230.1-232.29
  rule _ {C : context, mut : mut, t : valtype}:
    `%|-%:OK`(C, `%%`(mut, t))
    -- Valtype_ok: `%|-%:OK`(C, t)

;; 6-typing.watsup:216.1-216.73
relation Tabletype_ok: `%|-%:OK`(context, tabletype)
  ;; 6-typing.watsup:234.1-237.30
  rule _ {C : context, lim : limits, rt : reftype}:
    `%|-%:OK`(C, `%%`(lim, rt))
    -- Limits_ok: `%|-%:%`(C, lim, ((2 ^ 32) - 1))
    -- Reftype_ok: `%|-%:OK`(C, rt)

;; 6-typing.watsup:217.1-217.71
relation Memtype_ok: `%|-%:OK`(context, memtype)
  ;; 6-typing.watsup:239.1-241.35
  rule _ {C : context, lim : limits}:
    `%|-%:OK`(C, `%I8`(lim))
    -- Limits_ok: `%|-%:%`(C, lim, (2 ^ 16))

;; 6-typing.watsup:218.1-218.74
relation Externtype_ok: `%|-%:OK`(context, externtype)
  ;; 6-typing.watsup:244.1-247.27
  rule func {C : context, dt : deftype, ft : functype}:
    `%|-%:OK`(C, FUNC_externtype(dt))
    -- Deftype_ok: `%|-%:OK`(C, dt)
    -- Expand: `%~~%`(dt, FUNC_comptype(ft))

  ;; 6-typing.watsup:249.1-251.33
  rule global {C : context, gt : globaltype}:
    `%|-%:OK`(C, GLOBAL_externtype(gt))
    -- Globaltype_ok: `%|-%:OK`(C, gt)

  ;; 6-typing.watsup:253.1-255.32
  rule table {C : context, tt : tabletype}:
    `%|-%:OK`(C, TABLE_externtype(tt))
    -- Tabletype_ok: `%|-%:OK`(C, tt)

  ;; 6-typing.watsup:257.1-259.30
  rule mem {C : context, mt : memtype}:
    `%|-%:OK`(C, MEM_externtype(mt))
    -- Memtype_ok: `%|-%:OK`(C, mt)

;; 6-typing.watsup:374.1-374.81
relation Resulttype_sub: `%|-%*<:%*`(context, valtype*, valtype*)
  ;; 6-typing.watsup:377.1-379.37
  rule _ {C : context, t_1* : valtype*, t_2* : valtype*}:
    `%|-%*<:%*`(C, t_1*{t_1}, t_2*{t_2})
    -- (Valtype_sub: `%|-%<:%`(C, t_1, t_2))*{t_1 t_2}

;; 6-typing.watsup:375.1-375.80
relation Instrtype_sub: `%|-%<:%`(context, instrtype, instrtype)
  ;; 6-typing.watsup:381.1-386.30
  rule _ {C : context, t* : valtype*, t_11* : valtype*, t_12* : valtype*, t_21* : valtype*, t_22* : valtype*, x* : idx*, x_1* : idx*, x_2* : idx*}:
    `%|-%<:%`(C, `%->%*%`(t_11*{t_11}, x_1*{x_1}, t_12*{t_12}), `%->%*%`(t_21*{t_21}, x_2*{x_2}, t_22*{t_22}))
    -- Resulttype_sub: `%|-%*<:%*`(C, t_21*{t_21}, t_11*{t_11})
    -- Resulttype_sub: `%|-%*<:%*`(C, t_12*{t_12}, t_22*{t_22})
    -- if (x*{x} = $setminus(x_2*{x_2}, x_1*{x_1}))
    -- (if (C.LOCAL_context[x] = `%%`(SET_init, t)))*{t x}

;; 6-typing.watsup:446.1-446.83
relation Limits_sub: `%|-%<:%`(context, limits, limits)
  ;; 6-typing.watsup:453.1-456.21
  rule _ {C : context, n_11 : n, n_12 : n, n_21 : n, n_22 : n}:
    `%|-%<:%`(C, `[%..%]`(n_11, n_12), `[%..%]`(n_21, n_22))
    -- if (n_11 >= n_21)
    -- if (n_12 <= n_22)

;; 6-typing.watsup:447.1-447.83
relation Globaltype_sub: `%|-%<:%`(context, globaltype, globaltype)
  ;; 6-typing.watsup:461.1-463.34
  rule const {C : context, t_1 : valtype, t_2 : valtype}:
    `%|-%<:%`(C, `%%`(`MUT%?`(?()), t_1), `%%`(`MUT%?`(?()), t_2))
    -- Valtype_sub: `%|-%<:%`(C, t_1, t_2)

  ;; 6-typing.watsup:465.1-468.34
  rule var {C : context, t_1 : valtype, t_2 : valtype}:
    `%|-%<:%`(C, `%%`(`MUT%?`(?(())), t_1), `%%`(`MUT%?`(?(())), t_2))
    -- Valtype_sub: `%|-%<:%`(C, t_1, t_2)
    -- Valtype_sub: `%|-%<:%`(C, t_2, t_1)

;; 6-typing.watsup:448.1-448.82
relation Tabletype_sub: `%|-%<:%`(context, tabletype, tabletype)
  ;; 6-typing.watsup:470.1-474.36
  rule _ {C : context, lim_1 : limits, lim_2 : limits, rt_1 : reftype, rt_2 : reftype}:
    `%|-%<:%`(C, `%%`(lim_1, rt_1), `%%`(lim_2, rt_2))
    -- Limits_sub: `%|-%<:%`(C, lim_1, lim_2)
    -- Reftype_sub: `%|-%<:%`(C, rt_1, rt_2)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)

;; 6-typing.watsup:449.1-449.80
relation Memtype_sub: `%|-%<:%`(context, memtype, memtype)
  ;; 6-typing.watsup:476.1-478.37
  rule _ {C : context, lim_1 : limits, lim_2 : limits}:
    `%|-%<:%`(C, `%I8`(lim_1), `%I8`(lim_2))
    -- Limits_sub: `%|-%<:%`(C, lim_1, lim_2)

;; 6-typing.watsup:450.1-450.83
relation Externtype_sub: `%|-%<:%`(context, externtype, externtype)
  ;; 6-typing.watsup:481.1-483.36
  rule func {C : context, dt_1 : deftype, dt_2 : deftype}:
    `%|-%<:%`(C, FUNC_externtype(dt_1), FUNC_externtype(dt_2))
    -- Deftype_sub: `%|-%<:%`(C, dt_1, dt_2)

  ;; 6-typing.watsup:485.1-487.39
  rule global {C : context, gt_1 : globaltype, gt_2 : globaltype}:
    `%|-%<:%`(C, GLOBAL_externtype(gt_1), GLOBAL_externtype(gt_2))
    -- Globaltype_sub: `%|-%<:%`(C, gt_1, gt_2)

  ;; 6-typing.watsup:489.1-491.38
  rule table {C : context, tt_1 : tabletype, tt_2 : tabletype}:
    `%|-%<:%`(C, TABLE_externtype(tt_1), TABLE_externtype(tt_2))
    -- Tabletype_sub: `%|-%<:%`(C, tt_1, tt_2)

  ;; 6-typing.watsup:493.1-495.36
  rule mem {C : context, mt_1 : memtype, mt_2 : memtype}:
    `%|-%<:%`(C, MEM_externtype(mt_1), MEM_externtype(mt_2))
    -- Memtype_sub: `%|-%<:%`(C, mt_1, mt_2)

;; 6-typing.watsup:565.1-565.76
relation Blocktype_ok: `%|-%:%`(context, blocktype, functype)
  ;; 6-typing.watsup:567.1-569.31
  rule _ {C : context, ft : functype}:
    `%|-%:%`(C, ft, ft)
    -- Functype_ok: `%|-%:OK`(C, ft)

;; 6-typing.watsup:503.1-505.74
rec {

;; 6-typing.watsup:503.1-503.67
relation Instr_ok: `%|-%:%`(context, instr, functype)
  ;; 6-typing.watsup:544.1-545.34
  rule unreachable {C : context, t_1* : valtype*, t_2* : valtype*}:
    `%|-%:%`(C, UNREACHABLE_instr, `%->%`(t_1*{t_1}, t_2*{t_2}))

  ;; 6-typing.watsup:547.1-548.32
  rule nop {C : context}:
    `%|-%:%`(C, NOP_instr, `%->%`([], []))

  ;; 6-typing.watsup:550.1-551.27
  rule drop {C : context, t : valtype}:
    `%|-%:%`(C, DROP_instr, `%->%`([t], []))

  ;; 6-typing.watsup:554.1-555.31
  rule select-expl {C : context, t : valtype}:
    `%|-%:%`(C, SELECT_instr(?(t)), `%->%`([t t I32_valtype], [t]))

  ;; 6-typing.watsup:557.1-560.37
  rule select-impl {C : context, numtype : numtype, t : valtype, t' : valtype, vectype : vectype}:
    `%|-%:%`(C, SELECT_instr(?()), `%->%`([t t I32_valtype], [t]))
    -- Valtype_sub: `%|-%<:%`(C, t, t')
    -- if ((t' = (numtype <: valtype)) \/ (t' = (vectype <: valtype)))

  ;; 6-typing.watsup:571.1-574.61
  rule block {C : context, bt : blocktype, instr* : instr*, t_1* : valtype*, t_2* : valtype*, x* : idx*}:
    `%|-%:%`(C, BLOCK_instr(bt, instr*{instr}), `%->%`(t_1*{t_1}, t_2*{t_2}))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`(t_1*{t_1}, t_2*{t_2}))
    -- Instrs_ok: `%|-%*:%`(C ++ {TYPE [], REC [], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2*{t_2}], RETURN ?()}, instr*{instr}, `%->%*%`(t_1*{t_1}, x*{x}, t_2*{t_2}))

  ;; 6-typing.watsup:576.1-579.61
  rule loop {C : context, bt : blocktype, instr* : instr*, t_1* : valtype*, t_2* : valtype*, x* : idx*}:
    `%|-%:%`(C, LOOP_instr(bt, instr*{instr}), `%->%`(t_1*{t_1}, t_2*{t_2}))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`(t_1*{t_1}, t_2*{t_2}))
    -- Instrs_ok: `%|-%*:%`(C ++ {TYPE [], REC [], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_1*{t_1}], RETURN ?()}, instr*{instr}, `%->%*%`(t_1*{t_1}, x*{x}, t_2*{t_2}))

  ;; 6-typing.watsup:581.1-585.65
  rule if {C : context, bt : blocktype, instr_1* : instr*, instr_2* : instr*, t_1* : valtype*, t_2* : valtype*, x_1* : idx*, x_2* : idx*}:
    `%|-%:%`(C, IF_instr(bt, instr_1*{instr_1}, instr_2*{instr_2}), `%->%`(t_1*{t_1} :: [I32_valtype], t_2*{t_2}))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`(t_1*{t_1}, t_2*{t_2}))
    -- Instrs_ok: `%|-%*:%`(C ++ {TYPE [], REC [], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2*{t_2}], RETURN ?()}, instr_1*{instr_1}, `%->%*%`(t_1*{t_1}, x_1*{x_1}, t_2*{t_2}))
    -- Instrs_ok: `%|-%*:%`(C ++ {TYPE [], REC [], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2*{t_2}], RETURN ?()}, instr_2*{instr_2}, `%->%*%`(t_1*{t_1}, x_2*{x_2}, t_2*{t_2}))

  ;; 6-typing.watsup:590.1-592.24
  rule br {C : context, l : labelidx, t* : valtype*, t_1* : valtype*, t_2* : valtype*}:
    `%|-%:%`(C, BR_instr(l), `%->%`(t_1*{t_1} :: t*{t}, t_2*{t_2}))
    -- if (C.LABEL_context[l] = t*{t})

  ;; 6-typing.watsup:594.1-596.24
  rule br_if {C : context, l : labelidx, t* : valtype*}:
    `%|-%:%`(C, BR_IF_instr(l), `%->%`(t*{t} :: [I32_valtype], t*{t}))
    -- if (C.LABEL_context[l] = t*{t})

  ;; 6-typing.watsup:598.1-601.44
  rule br_table {C : context, l* : labelidx*, l' : labelidx, t* : valtype*, t_1* : valtype*, t_2* : valtype*}:
    `%|-%:%`(C, BR_TABLE_instr(l*{l}, l'), `%->%`(t_1*{t_1} :: t*{t}, t_2*{t_2}))
    -- (Resulttype_sub: `%|-%*<:%*`(C, t*{t}, C.LABEL_context[l]))*{l}
    -- Resulttype_sub: `%|-%*<:%*`(C, t*{t}, C.LABEL_context[l'])

  ;; 6-typing.watsup:603.1-606.31
  rule br_on_null {C : context, ht : heaptype, l : labelidx, t* : valtype*}:
    `%|-%:%`(C, BR_ON_NULL_instr(l), `%->%`(t*{t} :: [REF_valtype(`NULL%?`(?(())), ht)], t*{t} :: [REF_valtype(`NULL%?`(?()), ht)]))
    -- if (C.LABEL_context[l] = t*{t})
    -- Heaptype_ok: `%|-%:OK`(C, ht)

  ;; 6-typing.watsup:608.1-611.31
  rule br_on_non_null {C : context, ht : heaptype, l : labelidx, t* : valtype*}:
    `%|-%:%`(C, BR_ON_NON_NULL_instr(l), `%->%`(t*{t} :: [REF_valtype(`NULL%?`(?(())), ht)], t*{t}))
    -- if (C.LABEL_context[l] = t*{t} :: [REF_valtype(`NULL%?`(?()), ht)])
    -- Heaptype_ok: `%|-%:OK`(C, ht)

  ;; 6-typing.watsup:613.1-619.34
  rule br_on_cast {C : context, l : labelidx, rt : reftype, rt_1 : reftype, rt_2 : reftype, t* : valtype*}:
    `%|-%:%`(C, BR_ON_CAST_instr(l, rt_1, rt_2), `%->%`(t*{t} :: [(rt_1 <: valtype)], t*{t} :: [($diffrt(rt_1, rt_2) <: valtype)]))
    -- if (C.LABEL_context[l] = t*{t} :: [(rt <: valtype)])
    -- Reftype_ok: `%|-%:OK`(C, rt_1)
    -- Reftype_ok: `%|-%:OK`(C, rt_2)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt)

  ;; 6-typing.watsup:621.1-627.49
  rule br_on_cast_fail {C : context, l : labelidx, rt : reftype, rt_1 : reftype, rt_2 : reftype, t* : valtype*}:
    `%|-%:%`(C, BR_ON_CAST_instr(l, rt_1, rt_2), `%->%`(t*{t} :: [(rt_1 <: valtype)], t*{t} :: [(rt_2 <: valtype)]))
    -- if (C.LABEL_context[l] = t*{t} :: [(rt <: valtype)])
    -- Reftype_ok: `%|-%:OK`(C, rt_1)
    -- Reftype_ok: `%|-%:OK`(C, rt_2)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)
    -- Reftype_sub: `%|-%<:%`(C, $diffrt(rt_1, rt_2), rt)

  ;; 6-typing.watsup:632.1-634.24
  rule return {C : context, t* : valtype*, t_1* : valtype*, t_2* : valtype*}:
    `%|-%:%`(C, RETURN_instr, `%->%`(t_1*{t_1} :: t*{t}, t_2*{t_2}))
    -- if (C.RETURN_context = ?(t*{t}))

  ;; 6-typing.watsup:636.1-638.46
  rule call {C : context, t_1* : valtype*, t_2* : valtype*, x : idx}:
    `%|-%:%`(C, CALL_instr(x), `%->%`(t_1*{t_1}, t_2*{t_2}))
    -- Expand: `%~~%`(C.FUNC_context[x], FUNC_comptype(`%->%`(t_1*{t_1}, t_2*{t_2})))

  ;; 6-typing.watsup:640.1-642.46
  rule call_ref {C : context, t_1* : valtype*, t_2* : valtype*, x : idx}:
    `%|-%:%`(C, CALL_REF_instr(x), `%->%`(t_1*{t_1} :: [REF_valtype(`NULL%?`(?(())), ($idx(x) <: heaptype))], t_2*{t_2}))
    -- Expand: `%~~%`(C.TYPE_context[x], FUNC_comptype(`%->%`(t_1*{t_1}, t_2*{t_2})))

  ;; 6-typing.watsup:644.1-648.46
  rule call_indirect {C : context, lim : limits, rt : reftype, t_1* : valtype*, t_2* : valtype*, x : idx, y : idx}:
    `%|-%:%`(C, CALL_INDIRECT_instr(x, y), `%->%`(t_1*{t_1} :: [I32_valtype], t_2*{t_2}))
    -- if (C.TABLE_context[x] = `%%`(lim, rt))
    -- Reftype_sub: `%|-%<:%`(C, rt, REF_reftype(`NULL%?`(?(())), FUNC_heaptype))
    -- Expand: `%~~%`(C.TYPE_context[y], FUNC_comptype(`%->%`(t_1*{t_1}, t_2*{t_2})))

  ;; 6-typing.watsup:650.1-654.40
  rule return_call {C : context, t'_2* : valtype*, t_1* : valtype*, t_2* : valtype*, t_3* : valtype*, t_4* : valtype*, x : idx}:
    `%|-%:%`(C, RETURN_CALL_instr(x), `%->%`(t_3*{t_3} :: t_1*{t_1}, t_4*{t_4}))
    -- Expand: `%~~%`(C.FUNC_context[x], FUNC_comptype(`%->%`(t_1*{t_1}, t_2*{t_2})))
    -- if (C.RETURN_context = ?(t'_2*{t'_2}))
    -- Resulttype_sub: `%|-%*<:%*`(C, t_2*{t_2}, t'_2*{t'_2})

  ;; 6-typing.watsup:656.1-660.40
  rule return_call_ref {C : context, t'_2* : valtype*, t_1* : valtype*, t_2* : valtype*, t_3* : valtype*, t_4* : valtype*, x : idx}:
    `%|-%:%`(C, RETURN_CALL_REF_instr(x), `%->%`(t_3*{t_3} :: t_1*{t_1} :: [REF_valtype(`NULL%?`(?(())), ($idx(x) <: heaptype))], t_4*{t_4}))
    -- Expand: `%~~%`(C.TYPE_context[x], FUNC_comptype(`%->%`(t_1*{t_1}, t_2*{t_2})))
    -- if (C.RETURN_context = ?(t'_2*{t'_2}))
    -- Resulttype_sub: `%|-%*<:%*`(C, t_2*{t_2}, t'_2*{t'_2})

  ;; 6-typing.watsup:662.1-668.40
  rule return_call_indirect {C : context, lim : limits, rt : reftype, t'_2* : valtype*, t_1* : valtype*, t_2* : valtype*, t_3* : valtype*, t_4* : valtype*, x : idx, y : idx}:
    `%|-%:%`(C, RETURN_CALL_INDIRECT_instr(x, y), `%->%`(t_3*{t_3} :: t_1*{t_1} :: [I32_valtype], t_4*{t_4}))
    -- if (C.TABLE_context[x] = `%%`(lim, rt))
    -- Reftype_sub: `%|-%<:%`(C, rt, REF_reftype(`NULL%?`(?(())), FUNC_heaptype))
    -- Expand: `%~~%`(C.TYPE_context[y], FUNC_comptype(`%->%`(t_1*{t_1}, t_2*{t_2})))
    -- if (C.RETURN_context = ?(t'_2*{t'_2}))
    -- Resulttype_sub: `%|-%*<:%*`(C, t_2*{t_2}, t'_2*{t'_2})

  ;; 6-typing.watsup:673.1-674.37
  rule const {C : context, c_nt : c_numtype, nt : numtype}:
    `%|-%:%`(C, CONST_instr(nt, c_nt), `%->%`([], [(nt <: valtype)]))

  ;; 6-typing.watsup:676.1-677.31
  rule unop {C : context, nt : numtype, unop : unop_numtype}:
    `%|-%:%`(C, UNOP_instr(nt, unop), `%->%`([(nt <: valtype)], [(nt <: valtype)]))

  ;; 6-typing.watsup:679.1-680.36
  rule binop {C : context, binop : binop_numtype, nt : numtype}:
    `%|-%:%`(C, BINOP_instr(nt, binop), `%->%`([(nt <: valtype) (nt <: valtype)], [(nt <: valtype)]))

  ;; 6-typing.watsup:682.1-683.36
  rule testop {C : context, nt : numtype, testop : testop_numtype}:
    `%|-%:%`(C, TESTOP_instr(nt, testop), `%->%`([(nt <: valtype)], [I32_valtype]))

  ;; 6-typing.watsup:685.1-686.37
  rule relop {C : context, nt : numtype, relop : relop_numtype}:
    `%|-%:%`(C, RELOP_instr(nt, relop), `%->%`([(nt <: valtype) (nt <: valtype)], [I32_valtype]))

  ;; 6-typing.watsup:689.1-691.23
  rule extend {C : context, n : n, nt : numtype}:
    `%|-%:%`(C, EXTEND_instr(nt, n), `%->%`([(nt <: valtype)], [(nt <: valtype)]))
    -- if (n <= $size(nt <: valtype))

  ;; 6-typing.watsup:693.1-696.34
  rule reinterpret {C : context, nt_1 : numtype, nt_2 : numtype}:
    `%|-%:%`(C, CVTOP_instr(nt_1, REINTERPRET_cvtop, nt_2, ?()), `%->%`([(nt_2 <: valtype)], [(nt_1 <: valtype)]))
    -- if (nt_1 =/= nt_2)
    -- if ($size(nt_1 <: valtype) = $size(nt_2 <: valtype))

  ;; 6-typing.watsup:698.1-701.52
  rule convert-i {C : context, iN_1 : iN, iN_2 : iN, sx? : sx?}:
    `%|-%:%`(C, CVTOP_instr((iN_1 <: numtype), CONVERT_cvtop, (iN_2 <: numtype), sx?{sx}), `%->%`([(iN_2 <: valtype)], [(iN_1 <: valtype)]))
    -- if (iN_1 =/= iN_2)
    -- if ((sx?{sx} = ?()) <=> ($size(iN_1 <: valtype) > $size(iN_2 <: valtype)))

  ;; 6-typing.watsup:703.1-705.22
  rule convert-f {C : context, fN_1 : fN, fN_2 : fN}:
    `%|-%:%`(C, CVTOP_instr((fN_1 <: numtype), CONVERT_cvtop, (fN_2 <: numtype), ?()), `%->%`([(fN_2 <: valtype)], [(fN_1 <: valtype)]))
    -- if (fN_1 =/= fN_2)

  ;; 6-typing.watsup:710.1-712.31
  rule ref.null {C : context, ht : heaptype}:
    `%|-%:%`(C, REF.NULL_instr(ht), `%->%`([], [REF_valtype(`NULL%?`(?(())), ht)]))
    -- Heaptype_ok: `%|-%:OK`(C, ht)

  ;; 6-typing.watsup:715.1-717.23
  rule ref.func {C : context, dt : deftype, x : idx}:
    `%|-%:%`(C, REF.FUNC_instr(x), `%->%`([], [REF_valtype(`NULL%?`(?()), (dt <: heaptype))]))
    -- if (C.FUNC_context[x] = dt)

  ;; 6-typing.watsup:719.1-720.42
  rule ref.i31 {C : context}:
    `%|-%:%`(C, REF.I31_instr, `%->%`([I32_valtype], [REF_valtype(`NULL%?`(?()), I31_heaptype)]))

  ;; 6-typing.watsup:722.1-723.31
  rule ref.is_null {C : context, rt : reftype}:
    `%|-%:%`(C, REF.IS_NULL_instr, `%->%`([(rt <: valtype)], [I32_valtype]))

  ;; 6-typing.watsup:725.1-727.31
  rule ref.as_non_null {C : context, ht : heaptype}:
    `%|-%:%`(C, REF.AS_NON_NULL_instr, `%->%`([REF_valtype(`NULL%?`(?(())), ht)], [REF_valtype(`NULL%?`(?()), ht)]))
    -- Heaptype_ok: `%|-%:OK`(C, ht)

  ;; 6-typing.watsup:729.1-730.51
  rule ref.eq {C : context}:
    `%|-%:%`(C, REF.EQ_instr, `%->%`([REF_valtype(`NULL%?`(?(())), EQ_heaptype) REF_valtype(`NULL%?`(?(())), EQ_heaptype)], [I32_valtype]))

  ;; 6-typing.watsup:732.1-736.33
  rule ref.test {C : context, rt : reftype, rt' : reftype}:
    `%|-%:%`(C, REF.TEST_instr(rt), `%->%`([(rt' <: valtype)], [I32_valtype]))
    -- Reftype_ok: `%|-%:OK`(C, rt)
    -- Reftype_ok: `%|-%:OK`(C, rt')
    -- Reftype_sub: `%|-%<:%`(C, rt, rt')

  ;; 6-typing.watsup:738.1-742.33
  rule ref.cast {C : context, rt : reftype, rt' : reftype}:
    `%|-%:%`(C, REF.CAST_instr(rt), `%->%`([(rt' <: valtype)], [(rt <: valtype)]))
    -- Reftype_ok: `%|-%:OK`(C, rt)
    -- Reftype_ok: `%|-%:OK`(C, rt')
    -- Reftype_sub: `%|-%<:%`(C, rt, rt')

  ;; 6-typing.watsup:747.1-748.42
  rule i31.get {C : context, sx : sx}:
    `%|-%:%`(C, I31.GET_instr(sx), `%->%`([REF_valtype(`NULL%?`(?(())), I31_heaptype)], [I32_valtype]))

  ;; 6-typing.watsup:753.1-755.43
  rule struct.new {C : context, mut* : mut*, x : idx, zt* : storagetype*}:
    `%|-%:%`(C, STRUCT.NEW_instr(x), `%->%`($unpacktype(zt)*{zt}, [REF_valtype(`NULL%?`(?()), ($idx(x) <: heaptype))]))
    -- Expand: `%~~%`(C.TYPE_context[x], STRUCT_comptype(`%%`(mut, zt)*{mut zt}))

  ;; 6-typing.watsup:757.1-760.43
  rule struct.new_default {C : context, mut* : mut*, val* : val*, x : idx, zt* : storagetype*}:
    `%|-%:%`(C, STRUCT.NEW_DEFAULT_instr(x), `%->%`($unpacktype(zt)*{zt}, [REF_valtype(`NULL%?`(?()), ($idx(x) <: heaptype))]))
    -- Expand: `%~~%`(C.TYPE_context[x], STRUCT_comptype(`%%`(mut, zt)*{mut zt}))
    -- (if ($default($unpacktype(zt)) = ?(val)))*{val zt}

  ;; 6-typing.watsup:762.1-766.47
  rule struct.get {C : context, i : nat, mut : mut, sx? : sx?, x : idx, yt* : fieldtype*, zt : storagetype}:
    `%|-%:%`(C, STRUCT.GET_instr(sx?{sx}, x, i), `%->%`([REF_valtype(`NULL%?`(?(())), ($idx(x) <: heaptype))], [$unpacktype(zt)]))
    -- Expand: `%~~%`(C.TYPE_context[x], STRUCT_comptype(yt*{yt}))
    -- if (yt*{yt}[i] = `%%`(mut, zt))
    -- if ((sx?{sx} = ?()) <=> (zt = ($unpacktype(zt) <: storagetype)))

  ;; 6-typing.watsup:768.1-771.24
  rule struct.set {C : context, i : nat, x : idx, yt* : fieldtype*, zt : storagetype}:
    `%|-%:%`(C, STRUCT.SET_instr(x, i), `%->%`([REF_valtype(`NULL%?`(?(())), ($idx(x) <: heaptype)) $unpacktype(zt)], []))
    -- Expand: `%~~%`(C.TYPE_context[x], STRUCT_comptype(yt*{yt}))
    -- if (yt*{yt}[i] = `%%`(`MUT%?`(?(())), zt))

  ;; 6-typing.watsup:776.1-778.41
  rule array.new {C : context, mut : mut, x : idx, zt : storagetype}:
    `%|-%:%`(C, ARRAY.NEW_instr(x), `%->%`([$unpacktype(zt) I32_valtype], [REF_valtype(`NULL%?`(?()), ($idx(x) <: heaptype))]))
    -- Expand: `%~~%`(C.TYPE_context[x], ARRAY_comptype(`%%`(mut, zt)))

  ;; 6-typing.watsup:780.1-783.40
  rule array.new_default {C : context, mut : mut, val : val, x : idx, zt : storagetype}:
    `%|-%:%`(C, ARRAY.NEW_DEFAULT_instr(x), `%->%`([I32_valtype], [REF_valtype(`NULL%?`(?()), ($idx(x) <: heaptype))]))
    -- Expand: `%~~%`(C.TYPE_context[x], ARRAY_comptype(`%%`(mut, zt)))
    -- if ($default($unpacktype(zt)) = ?(val))

  ;; 6-typing.watsup:785.1-787.41
  rule array.new_fixed {C : context, mut : mut, n : n, x : idx, zt : storagetype}:
    `%|-%:%`(C, ARRAY.NEW_FIXED_instr(x, n), `%->%`([$unpacktype(zt)], [REF_valtype(`NULL%?`(?()), ($idx(x) <: heaptype))]))
    -- Expand: `%~~%`(C.TYPE_context[x], ARRAY_comptype(`%%`(mut, zt)))

  ;; 6-typing.watsup:789.1-792.39
  rule array.new_elem {C : context, mut : mut, rt : reftype, x : idx, y : idx}:
    `%|-%:%`(C, ARRAY.NEW_ELEM_instr(x, y), `%->%`([I32_valtype I32_valtype], [REF_valtype(`NULL%?`(?()), ($idx(x) <: heaptype))]))
    -- Expand: `%~~%`(C.TYPE_context[x], ARRAY_comptype(`%%`(mut, (rt <: storagetype))))
    -- Reftype_sub: `%|-%<:%`(C, C.ELEM_context[y], rt)

  ;; 6-typing.watsup:794.1-798.23
  rule array.new_data {C : context, mut : mut, numtype : numtype, t : valtype, vectype : vectype, x : idx, y : idx}:
    `%|-%:%`(C, ARRAY.NEW_DATA_instr(x, y), `%->%`([I32_valtype I32_valtype], [REF_valtype(`NULL%?`(?()), ($idx(x) <: heaptype))]))
    -- Expand: `%~~%`(C.TYPE_context[x], ARRAY_comptype(`%%`(mut, (t <: storagetype))))
    -- if ((t = (numtype <: valtype)) \/ (t = (vectype <: valtype)))
    -- if (C.DATA_context[y] = OK)

  ;; 6-typing.watsup:800.1-803.47
  rule array.get {C : context, mut : mut, sx? : sx?, x : idx, zt : storagetype}:
    `%|-%:%`(C, ARRAY.GET_instr(sx?{sx}, x), `%->%`([REF_valtype(`NULL%?`(?(())), ($idx(x) <: heaptype)) I32_valtype], [$unpacktype(zt)]))
    -- Expand: `%~~%`(C.TYPE_context[x], ARRAY_comptype(`%%`(mut, zt)))
    -- if ((sx?{sx} = ?()) <=> (zt = ($unpacktype(zt) <: storagetype)))

  ;; 6-typing.watsup:805.1-807.41
  rule array.set {C : context, x : idx, zt : storagetype}:
    `%|-%:%`(C, ARRAY.SET_instr(x), `%->%`([REF_valtype(`NULL%?`(?(())), ($idx(x) <: heaptype)) I32_valtype $unpacktype(zt)], []))
    -- Expand: `%~~%`(C.TYPE_context[x], ARRAY_comptype(`%%`(`MUT%?`(?(())), zt)))

  ;; 6-typing.watsup:809.1-811.41
  rule array.len {C : context, x : idx, zt : storagetype}:
    `%|-%:%`(C, ARRAY.LEN_instr, `%->%`([REF_valtype(`NULL%?`(?(())), ARRAY_heaptype)], [I32_valtype]))
    -- Expand: `%~~%`(C.TYPE_context[x], ARRAY_comptype(`%%`(`MUT%?`(?(())), zt)))

  ;; 6-typing.watsup:813.1-815.41
  rule array.fill {C : context, x : idx, zt : storagetype}:
    `%|-%:%`(C, ARRAY.FILL_instr(x), `%->%`([REF_valtype(`NULL%?`(?(())), ($idx(x) <: heaptype)) I32_valtype $unpacktype(zt) I32_valtype], []))
    -- Expand: `%~~%`(C.TYPE_context[x], ARRAY_comptype(`%%`(`MUT%?`(?(())), zt)))

  ;; 6-typing.watsup:817.1-821.40
  rule array.copy {C : context, mut : mut, x_1 : idx, x_2 : idx, zt_1 : storagetype, zt_2 : storagetype}:
    `%|-%:%`(C, ARRAY.COPY_instr(x_1, x_2), `%->%`([REF_valtype(`NULL%?`(?(())), ($idx(x_1) <: heaptype)) I32_valtype REF_valtype(`NULL%?`(?(())), ($idx(x_2) <: heaptype)) I32_valtype I32_valtype], []))
    -- Expand: `%~~%`(C.TYPE_context[x_1], ARRAY_comptype(`%%`(`MUT%?`(?(())), zt_1)))
    -- Expand: `%~~%`(C.TYPE_context[x_2], ARRAY_comptype(`%%`(mut, zt_2)))
    -- Storagetype_sub: `%|-%<:%`(C, zt_2, zt_1)

  ;; 6-typing.watsup:823.1-826.43
  rule array.init_elem {C : context, x : idx, y : idx, zt : storagetype}:
    `%|-%:%`(C, ARRAY.INIT_ELEM_instr(x, y), `%->%`([REF_valtype(`NULL%?`(?(())), ($idx(x) <: heaptype)) I32_valtype I32_valtype I32_valtype], []))
    -- Expand: `%~~%`(C.TYPE_context[x], ARRAY_comptype(`%%`(`MUT%?`(?(())), zt)))
    -- Storagetype_sub: `%|-%<:%`(C, (C.ELEM_context[y] <: storagetype), zt)

  ;; 6-typing.watsup:828.1-832.23
  rule array.init_data {C : context, numtype : numtype, t : valtype, vectype : vectype, x : idx, y : idx, zt : storagetype}:
    `%|-%:%`(C, ARRAY.INIT_DATA_instr(x, y), `%->%`([REF_valtype(`NULL%?`(?(())), ($idx(x) <: heaptype)) I32_valtype I32_valtype I32_valtype], []))
    -- Expand: `%~~%`(C.TYPE_context[x], ARRAY_comptype(`%%`(`MUT%?`(?(())), zt)))
    -- if ((t = (numtype <: valtype)) \/ (t = (vectype <: valtype)))
    -- if (C.DATA_context[y] = OK)

  ;; 6-typing.watsup:837.1-838.62
  rule extern.externalize {C : context, nul : nul}:
    `%|-%:%`(C, EXTERN.EXTERNALIZE_instr, `%->%`([REF_valtype(nul, ANY_heaptype)], [REF_valtype(nul, EXTERN_heaptype)]))

  ;; 6-typing.watsup:840.1-841.62
  rule extern.internalize {C : context, nul : nul}:
    `%|-%:%`(C, EXTERN.INTERNALIZE_instr, `%->%`([REF_valtype(nul, EXTERN_heaptype)], [REF_valtype(nul, ANY_heaptype)]))

  ;; 6-typing.watsup:846.1-848.28
  rule local.get {C : context, init : init, t : valtype, x : idx}:
    `%|-%:%`(C, LOCAL.GET_instr(x), `%->%`([], [t]))
    -- if (C.LOCAL_context[x] = `%%`(init, t))

  ;; 6-typing.watsup:861.1-863.28
  rule global.get {C : context, mut : mut, t : valtype, x : idx}:
    `%|-%:%`(C, GLOBAL.GET_instr(x), `%->%`([], [t]))
    -- if (C.GLOBAL_context[x] = `%%`(mut, t))

  ;; 6-typing.watsup:865.1-867.28
  rule global.set {C : context, t : valtype, x : idx}:
    `%|-%:%`(C, GLOBAL.SET_instr(x), `%->%`([t], []))
    -- if (C.GLOBAL_context[x] = `%%`(`MUT%?`(?(())), t))

  ;; 6-typing.watsup:872.1-874.28
  rule table.get {C : context, lim : limits, rt : reftype, x : idx}:
    `%|-%:%`(C, TABLE.GET_instr(x), `%->%`([I32_valtype], [(rt <: valtype)]))
    -- if (C.TABLE_context[x] = `%%`(lim, rt))

  ;; 6-typing.watsup:876.1-878.28
  rule table.set {C : context, lim : limits, rt : reftype, x : idx}:
    `%|-%:%`(C, TABLE.SET_instr(x), `%->%`([I32_valtype (rt <: valtype)], []))
    -- if (C.TABLE_context[x] = `%%`(lim, rt))

  ;; 6-typing.watsup:880.1-882.24
  rule table.size {C : context, tt : tabletype, x : idx}:
    `%|-%:%`(C, TABLE.SIZE_instr(x), `%->%`([], [I32_valtype]))
    -- if (C.TABLE_context[x] = tt)

  ;; 6-typing.watsup:884.1-886.28
  rule table.grow {C : context, lim : limits, rt : reftype, x : idx}:
    `%|-%:%`(C, TABLE.GROW_instr(x), `%->%`([(rt <: valtype) I32_valtype], [I32_valtype]))
    -- if (C.TABLE_context[x] = `%%`(lim, rt))

  ;; 6-typing.watsup:888.1-890.28
  rule table.fill {C : context, lim : limits, rt : reftype, x : idx}:
    `%|-%:%`(C, TABLE.FILL_instr(x), `%->%`([I32_valtype (rt <: valtype) I32_valtype], []))
    -- if (C.TABLE_context[x] = `%%`(lim, rt))

  ;; 6-typing.watsup:892.1-896.36
  rule table.copy {C : context, lim_1 : limits, lim_2 : limits, rt_1 : reftype, rt_2 : reftype, x_1 : idx, x_2 : idx}:
    `%|-%:%`(C, TABLE.COPY_instr(x_1, x_2), `%->%`([I32_valtype I32_valtype I32_valtype], []))
    -- if (C.TABLE_context[x_1] = `%%`(lim_1, rt_1))
    -- if (C.TABLE_context[x_2] = `%%`(lim_2, rt_2))
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)

  ;; 6-typing.watsup:898.1-902.36
  rule table.init {C : context, lim : limits, rt_1 : reftype, rt_2 : reftype, x : idx, y : idx}:
    `%|-%:%`(C, TABLE.INIT_instr(x, y), `%->%`([I32_valtype I32_valtype I32_valtype], []))
    -- if (C.TABLE_context[x] = `%%`(lim, rt_1))
    -- if (C.ELEM_context[y] = rt_2)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)

  ;; 6-typing.watsup:904.1-906.23
  rule elem.drop {C : context, rt : reftype, x : idx}:
    `%|-%:%`(C, ELEM.DROP_instr(x), `%->%`([], []))
    -- if (C.ELEM_context[x] = rt)

  ;; 6-typing.watsup:911.1-913.22
  rule memory.size {C : context, mt : memtype, x : idx}:
    `%|-%:%`(C, MEMORY.SIZE_instr(x), `%->%`([], [I32_valtype]))
    -- if (C.MEM_context[x] = mt)

  ;; 6-typing.watsup:915.1-917.22
  rule memory.grow {C : context, mt : memtype, x : idx}:
    `%|-%:%`(C, MEMORY.GROW_instr(x), `%->%`([I32_valtype], [I32_valtype]))
    -- if (C.MEM_context[x] = mt)

  ;; 6-typing.watsup:919.1-921.22
  rule memory.fill {C : context, mt : memtype, x : idx}:
    `%|-%:%`(C, MEMORY.FILL_instr(x), `%->%`([I32_valtype I32_valtype I32_valtype], []))
    -- if (C.MEM_context[x] = mt)

  ;; 6-typing.watsup:923.1-926.26
  rule memory.copy {C : context, mt_1 : memtype, mt_2 : memtype, x_1 : idx, x_2 : idx}:
    `%|-%:%`(C, MEMORY.COPY_instr(x_1, x_2), `%->%`([I32_valtype I32_valtype I32_valtype], []))
    -- if (C.MEM_context[x_1] = mt_1)
    -- if (C.MEM_context[x_2] = mt_2)

  ;; 6-typing.watsup:928.1-931.23
  rule memory.init {C : context, mt : memtype, x : idx, y : idx}:
    `%|-%:%`(C, MEMORY.INIT_instr(x, y), `%->%`([I32_valtype I32_valtype I32_valtype], []))
    -- if (C.MEM_context[x] = mt)
    -- if (C.DATA_context[y] = OK)

  ;; 6-typing.watsup:933.1-935.23
  rule data.drop {C : context, x : idx}:
    `%|-%:%`(C, DATA.DROP_instr(x), `%->%`([], []))
    -- if (C.DATA_context[x] = OK)

  ;; 6-typing.watsup:937.1-942.32
  rule load {C : context, iN : iN, mt : memtype, n? : n?, n_A : n, n_O : n, nt : numtype, sx? : sx?, x : idx}:
    `%|-%:%`(C, LOAD_instr(nt, (n, sx)?{n sx}, x, n_A, n_O), `%->%`([I32_valtype], [(nt <: valtype)]))
    -- if (C.MEM_context[x] = mt)
    -- if ((2 ^ n_A) <= ($size(nt <: valtype) / 8))
    -- (if (((2 ^ n_A) <= (n / 8)) /\ ((n / 8) < ($size(nt <: valtype) / 8))))?{n}
    -- if ((n?{n} = ?()) \/ (nt = (iN <: numtype)))

  ;; 6-typing.watsup:944.1-949.32
  rule store {C : context, iN : iN, mt : memtype, n? : n?, n_A : n, n_O : n, nt : numtype, x : idx}:
    `%|-%:%`(C, STORE_instr(nt, n?{n}, x, n_A, n_O), `%->%`([I32_valtype (nt <: valtype)], []))
    -- if (C.MEM_context[x] = mt)
    -- if ((2 ^ n_A) <= ($size(nt <: valtype) / 8))
    -- (if (((2 ^ n_A) <= (n / 8)) /\ ((n / 8) < ($size(nt <: valtype) / 8))))?{n}
    -- if ((n?{n} = ?()) \/ (nt = (iN <: numtype)))

;; 6-typing.watsup:504.1-504.67
relation Instrf_ok: `%|-%:%`(context, instr, instrtype)
  ;; 6-typing.watsup:518.1-520.41
  rule instr {C : context, instr : instr, t_1* : valtype*, t_2* : valtype*}:
    `%|-%:%`(C, instr, `%->%*%`(t_1*{t_1}, [], t_2*{t_2}))
    -- Instr_ok: `%|-%:%`(C, instr, `%->%`(t_1*{t_1}, t_2*{t_2}))

  ;; 6-typing.watsup:850.1-852.28
  rule local.set {C : context, init : init, t : valtype, x : idx}:
    `%|-%:%`(C, LOCAL.SET_instr(x), `%->%*%`([t], [x], []))
    -- if (C.LOCAL_context[x] = `%%`(init, t))

  ;; 6-typing.watsup:854.1-856.28
  rule local.tee {C : context, init : init, t : valtype, x : idx}:
    `%|-%:%`(C, LOCAL.TEE_instr(x), `%->%*%`([t], [x], [t]))
    -- if (C.LOCAL_context[x] = `%%`(init, t))

;; 6-typing.watsup:505.1-505.74
relation Instrs_ok: `%|-%*:%`(context, instr*, instrtype)
  ;; 6-typing.watsup:522.1-523.45
  rule empty {C : context}:
    `%|-%*:%`(C, [], `%->%*%`([], [], []))

  ;; 6-typing.watsup:525.1-530.52
  rule seq {C : context, C' : context, init* : init*, instr_1 : instr, instr_2* : instr*, t* : valtype*, t_1* : valtype*, t_2* : valtype*, t_3* : valtype*, x_1* : idx*, x_2* : idx*}:
    `%|-%*:%`(C, [instr_1] :: instr_2*{instr_2}, `%->%*%`(t_1*{t_1}, x_1*{x_1} :: x_2*{x_2}, t_3*{t_3}))
    -- (if (C.LOCAL_context[x_1] = `%%`(init, t)))*{init t x_1}
    -- if (C' = $with_locals(C, x_1*{x_1}, `%%`(SET_init, t)*{t}))
    -- Instrf_ok: `%|-%:%`(C, instr_1, `%->%*%`(t_1*{t_1}, x_1*{x_1}, t_2*{t_2}))
    -- Instrs_ok: `%|-%*:%`(C', instr_2*{instr_2}, `%->%*%`(t_2*{t_2}, x_2*{x_2}, t_3*{t_3}))

  ;; 6-typing.watsup:532.1-535.35
  rule sub {C : context, instr* : instr*, it : instrtype, it' : instrtype}:
    `%|-%*:%`(C, instr*{instr}, it')
    -- Instrs_ok: `%|-%*:%`(C, instr*{instr}, it)
    -- Instrtype_sub: `%|-%<:%`(C, it, it')

  ;; 6-typing.watsup:537.1-539.47
  rule frame {C : context, instr* : instr*, t* : valtype*, t_1* : valtype*, t_2* : valtype*, x* : idx*}:
    `%|-%*:%`(C, instr*{instr}, `%->%*%`(t*{t} :: t_1*{t_1}, x*{x}, t*{t} :: t_2*{t_2}))
    -- Instrs_ok: `%|-%*:%`(C, instr*{instr}, `%->%*%`(t_1*{t_1}, x*{x}, t_2*{t_2}))
}

;; 6-typing.watsup:506.1-506.72
relation Expr_ok: `%|-%:%`(context, expr, resulttype)
  ;; 6-typing.watsup:511.1-513.53
  rule _ {C : context, instr* : instr*, t* : valtype*}:
    `%|-%:%`(C, instr*{instr}, t*{t})
    -- Instrs_ok: `%|-%*:%`(C, instr*{instr}, `%->%*%`([], [], t*{t}))

;; 6-typing.watsup:976.1-976.58
rec {

;; 6-typing.watsup:976.1-976.58
def in_binop : (binop_numtype, binopIXX*) -> bool
  ;; 6-typing.watsup:977.1-977.38
  def {binop : binop_numtype} in_binop(binop, []) = false
  ;; 6-typing.watsup:978.1-978.100
  def {binop : binop_numtype, binopIXX'* : binopIXX*, binopIXX_1 : binopIXX} in_binop(binop, [binopIXX_1] :: binopIXX'*{binopIXX'}) = ((binop = _I_binop_numtype(binopIXX_1)) \/ $in_binop(binop, binopIXX'*{binopIXX'}))
}

;; 6-typing.watsup:973.1-973.63
rec {

;; 6-typing.watsup:973.1-973.63
def in_numtype : (numtype, numtype*) -> bool
  ;; 6-typing.watsup:974.1-974.37
  def {nt : numtype} in_numtype(nt, []) = false
  ;; 6-typing.watsup:975.1-975.68
  def {nt : numtype, nt'* : numtype*, nt_1 : numtype} in_numtype(nt, [nt_1] :: nt'*{nt'}) = ((nt = nt_1) \/ $in_numtype(nt, nt'*{nt'}))
}

;; 6-typing.watsup:956.1-956.78
relation Instr_const: `%|-%CONST`(context, instr)
  ;; 6-typing.watsup:960.1-961.26
  rule const {C : context, c : c_numtype, nt : numtype}:
    `%|-%CONST`(C, CONST_instr(nt, c))

  ;; 6-typing.watsup:963.1-964.27
  rule ref.null {C : context, ht : heaptype}:
    `%|-%CONST`(C, REF.NULL_instr(ht))

  ;; 6-typing.watsup:966.1-967.26
  rule ref.func {C : context, x : idx}:
    `%|-%CONST`(C, REF.FUNC_instr(x))

  ;; 6-typing.watsup:969.1-971.32
  rule global.get {C : context, t : valtype, x : idx}:
    `%|-%CONST`(C, GLOBAL.GET_instr(x))
    -- if (C.GLOBAL_context[x] = `%%`(`MUT%?`(?()), t))

  ;; 6-typing.watsup:980.1-983.38
  rule binop {C : context, binop : binop_numtype, nt : numtype}:
    `%|-%CONST`(C, BINOP_instr(nt, binop))
    -- if $in_numtype(nt, [I32_numtype I64_numtype])
    -- if $in_binop(binop, [ADD_binopIXX SUB_binopIXX MUL_binopIXX])

;; 6-typing.watsup:957.1-957.77
relation Expr_const: `%|-%CONST`(context, expr)
  ;; 6-typing.watsup:986.1-987.38
  rule _ {C : context, instr* : instr*}:
    `%|-%CONST`(C, instr*{instr})
    -- (Instr_const: `%|-%CONST`(C, instr))*{instr}

;; 6-typing.watsup:958.1-958.78
relation Expr_ok_const: `%|-%:%CONST`(context, expr, valtype)
  ;; 6-typing.watsup:990.1-993.33
  rule _ {C : context, expr : expr, t : valtype}:
    `%|-%:%CONST`(C, expr, t)
    -- Expr_ok: `%|-%:%`(C, expr, [t])
    -- Expr_const: `%|-%CONST`(C, expr)

;; 6-typing.watsup:1002.1-1002.73
relation Type_ok: `%|-%:%*`(context, type, deftype*)
  ;; 6-typing.watsup:1014.1-1018.53
  rule _ {C : context, dt* : deftype*, rectype : rectype, x : idx}:
    `%|-%:%*`(C, TYPE(rectype), dt*{dt})
    -- if (x = |C.TYPE_context|)
    -- if (dt*{dt} = $rolldt(x, rectype))
    -- Rectype_ok: `%|-%:%`(C[TYPE_context =.. dt*{dt}], rectype, OK_oktypeidx(x))

;; 6-typing.watsup:1004.1-1004.74
relation Local_ok: `%|-%:%`(context, local, localtype)
  ;; 6-typing.watsup:1020.1-1022.32
  rule set {C : context, t : valtype}:
    `%|-%:%`(C, LOCAL(t), `%%`(SET_init, t))
    -- if ($default(t) =/= ?())

  ;; 6-typing.watsup:1024.1-1026.30
  rule unset {C : context, t : valtype}:
    `%|-%:%`(C, LOCAL(t), `%%`(UNSET_init, t))
    -- if ($default(t) = ?())

;; 6-typing.watsup:1003.1-1003.73
relation Func_ok: `%|-%:%`(context, func, deftype)
  ;; 6-typing.watsup:1028.1-1032.82
  rule _ {C : context, expr : expr, local* : local*, lt* : localtype*, t_1* : valtype*, t_2* : valtype*, x : idx}:
    `%|-%:%`(C, `FUNC%%*%`(x, local*{local}, expr), C.TYPE_context[x])
    -- Expand: `%~~%`(C.TYPE_context[x], FUNC_comptype(`%->%`(t_1*{t_1}, t_2*{t_2})))
    -- (Local_ok: `%|-%:%`(C, local, lt))*{local lt}
    -- Expr_ok: `%|-%:%`(C ++ {TYPE [], REC [], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL `%%`(SET_init, t_1)*{t_1} :: lt*{lt}, LABEL [], RETURN ?()} ++ {TYPE [], REC [], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2*{t_2}], RETURN ?()} ++ {TYPE [], REC [], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [], RETURN ?(t_2*{t_2})}, expr, t_2*{t_2})

;; 6-typing.watsup:1005.1-1005.75
relation Global_ok: `%|-%:%`(context, global, globaltype)
  ;; 6-typing.watsup:1034.1-1038.40
  rule _ {C : context, expr : expr, gt : globaltype, mut : mut, t : valtype}:
    `%|-%:%`(C, GLOBAL(gt, expr), gt)
    -- Globaltype_ok: `%|-%:OK`(C, gt)
    -- if (gt = `%%`(mut, t))
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, t)

;; 6-typing.watsup:1006.1-1006.74
relation Table_ok: `%|-%:%`(context, table, tabletype)
  ;; 6-typing.watsup:1040.1-1042.32
  rule _ {C : context, tt : tabletype}:
    `%|-%:%`(C, TABLE(tt, []), tt)
    -- Tabletype_ok: `%|-%:OK`(C, tt)

;; 6-typing.watsup:1007.1-1007.72
relation Mem_ok: `%|-%:%`(context, mem, memtype)
  ;; 6-typing.watsup:1044.1-1046.30
  rule _ {C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY(mt), mt)
    -- Memtype_ok: `%|-%:OK`(C, mt)

;; 6-typing.watsup:1010.1-1010.77
relation Elemmode_ok: `%|-%:%`(context, elemmode, reftype)
  ;; 6-typing.watsup:1057.1-1060.45
  rule active {C : context, expr : expr, lim : limits, rt : reftype, x : idx}:
    `%|-%:%`(C, TABLE_elemmode(x, expr), rt)
    -- if (C.TABLE_context[x] = `%%`(lim, rt))
    -- (Expr_ok_const: `%|-%:%CONST`(C, expr, I32_valtype))*{}

  ;; 6-typing.watsup:1062.1-1063.20
  rule declare {C : context, rt : reftype}:
    `%|-%:%`(C, DECLARE_elemmode, rt)

;; 6-typing.watsup:1008.1-1008.73
relation Elem_ok: `%|-%:%`(context, elem, reftype)
  ;; 6-typing.watsup:1048.1-1051.40
  rule _ {C : context, elemmode? : elemmode?, expr* : expr*, rt : reftype}:
    `%|-%:%`(C, `ELEM%%*%?`(rt, expr*{expr}, elemmode?{elemmode}), rt)
    -- (Expr_ok: `%|-%:%`(C, expr, [(rt <: valtype)]))*{expr}
    -- (Elemmode_ok: `%|-%:%`(C, elemmode, rt))?{elemmode}

;; 6-typing.watsup:1011.1-1011.77
relation Datamode_ok: `%|-%:OK`(context, datamode)
  ;; 6-typing.watsup:1065.1-1068.45
  rule _ {C : context, expr : expr, mt : memtype, x : idx}:
    `%|-%:OK`(C, MEMORY_datamode(x, expr))
    -- if (C.MEM_context[x] = mt)
    -- (Expr_ok_const: `%|-%:%CONST`(C, expr, I32_valtype))*{}

;; 6-typing.watsup:1009.1-1009.73
relation Data_ok: `%|-%:OK`(context, data)
  ;; 6-typing.watsup:1053.1-1055.40
  rule _ {C : context, b* : byte*, datamode? : datamode?}:
    `%|-%:OK`(C, `DATA%*%?`(b*{b}, datamode?{datamode}))
    -- (Datamode_ok: `%|-%:OK`(C, datamode))?{datamode}

;; 6-typing.watsup:1012.1-1012.74
relation Start_ok: `%|-%:OK`(context, start)
  ;; 6-typing.watsup:1070.1-1072.52
  rule _ {C : context, x : idx}:
    `%|-%:OK`(C, START(x))
    -- Expand: `%~~%`(C.FUNC_context[x], FUNC_comptype(`%->%`([], [])))

;; 6-typing.watsup:1077.1-1077.80
relation Import_ok: `%|-%:%`(context, import, externtype)
  ;; 6-typing.watsup:1081.1-1083.33
  rule _ {C : context, name_1 : name, name_2 : name, xt : externtype}:
    `%|-%:%`(C, IMPORT(name_1, name_2, xt), xt)
    -- Externtype_ok: `%|-%:OK`(C, xt)

;; 6-typing.watsup:1079.1-1079.83
relation Externuse_ok: `%|-%:%`(context, externuse, externtype)
  ;; 6-typing.watsup:1090.1-1092.23
  rule func {C : context, dt : deftype, x : idx}:
    `%|-%:%`(C, FUNC_externuse(x), FUNC_externtype(dt))
    -- if (C.FUNC_context[x] = dt)

  ;; 6-typing.watsup:1094.1-1096.25
  rule global {C : context, gt : globaltype, x : idx}:
    `%|-%:%`(C, GLOBAL_externuse(x), GLOBAL_externtype(gt))
    -- if (C.GLOBAL_context[x] = gt)

  ;; 6-typing.watsup:1098.1-1100.24
  rule table {C : context, tt : tabletype, x : idx}:
    `%|-%:%`(C, TABLE_externuse(x), TABLE_externtype(tt))
    -- if (C.TABLE_context[x] = tt)

  ;; 6-typing.watsup:1102.1-1104.22
  rule mem {C : context, mt : memtype, x : idx}:
    `%|-%:%`(C, MEM_externuse(x), MEM_externtype(mt))
    -- if (C.MEM_context[x] = mt)

;; 6-typing.watsup:1078.1-1078.80
relation Export_ok: `%|-%:%`(context, export, externtype)
  ;; 6-typing.watsup:1085.1-1087.39
  rule _ {C : context, externuse : externuse, name : name, xt : externtype}:
    `%|-%:%`(C, EXPORT(name, externuse), xt)
    -- Externuse_ok: `%|-%:%`(C, externuse, xt)

;; 6-typing.watsup:1111.1-1111.77
rec {

;; 6-typing.watsup:1111.1-1111.77
relation Globals_ok: `%|-%*:%*`(context, global*, globaltype*)
  ;; 6-typing.watsup:1154.1-1155.25
  rule empty {C : context}:
    `%|-%*:%*`(C, [], [])

  ;; 6-typing.watsup:1157.1-1160.54
  rule cons {C : context, global : global, global_1 : global, gt* : globaltype*, gt_1 : globaltype}:
    `%|-%*:%*`(C, [global_1] :: global*{}, [gt_1] :: gt*{gt})
    -- Global_ok: `%|-%:%`(C, global, gt_1)
    -- Globals_ok: `%|-%*:%*`(C[GLOBAL_context =.. [gt_1]], global*{}, gt*{gt})
}

;; 6-typing.watsup:1110.1-1110.75
rec {

;; 6-typing.watsup:1110.1-1110.75
relation Types_ok: `%|-%*:%*`(context, type*, deftype*)
  ;; 6-typing.watsup:1146.1-1147.25
  rule empty {C : context}:
    `%|-%*:%*`(C, [], [])

  ;; 6-typing.watsup:1149.1-1152.49
  rule cons {C : context, dt* : deftype*, dt_1 : deftype, type* : type*, type_1 : type}:
    `%|-%*:%*`(C, [type_1] :: type*{type}, dt_1*{} :: dt*{dt})
    -- Type_ok: `%|-%:%*`(C, type_1, [dt_1])
    -- Types_ok: `%|-%*:%*`(C[TYPE_context =.. dt_1*{}], type*{type}, dt*{dt})
}

;; 6-typing.watsup:1109.1-1109.76
relation Module_ok: `|-%:OK`(module)
  ;; 6-typing.watsup:1120.1-1143.29
  rule _ {C : context, C' : context, data^n : data^n, dt* : deftype*, dt'* : deftype*, elem* : elem*, et* : externtype*, export* : export*, func* : func*, global* : global*, gt* : globaltype*, idt* : deftype*, igt* : globaltype*, import* : import*, imt* : memtype*, itt* : tabletype*, ixt* : externtype*, mem* : mem*, mt* : memtype*, n : n, rt* : reftype*, start? : start?, table* : table*, tt* : tabletype*, type* : type*}:
    `|-%:OK`(`MODULE%*%*%*%*%*%*%*%*%?%*`(type*{type}, import*{import}, func*{func}, global*{global}, table*{table}, mem*{mem}, elem*{elem}, data^n{data}, start?{start}, export*{export}))
    -- Types_ok: `%|-%*:%*`({TYPE [], REC [], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [], RETURN ?()}, type*{type}, dt'*{dt'})
    -- (Import_ok: `%|-%:%`({TYPE dt'*{dt'}, REC [], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [], RETURN ?()}, import, ixt))*{import ixt}
    -- Globals_ok: `%|-%*:%*`(C', global*{global}, gt*{gt})
    -- (Table_ok: `%|-%:%`(C', table, tt))*{table tt}
    -- (Mem_ok: `%|-%:%`(C', mem, mt))*{mem mt}
    -- (Func_ok: `%|-%:%`(C, func, dt))*{dt func}
    -- (Elem_ok: `%|-%:%`(C, elem, rt))*{elem rt}
    -- (Data_ok: `%|-%:OK`(C, data))^n{data}
    -- (Start_ok: `%|-%:OK`(C, start))?{start}
    -- (Export_ok: `%|-%:%`(C, export, et))*{et export}
    -- if (C = {TYPE dt'*{dt'}, REC [], FUNC idt*{idt} :: dt*{dt}, GLOBAL igt*{igt} :: gt*{gt}, TABLE itt*{itt} :: tt*{tt}, MEM imt*{imt} :: mt*{mt}, ELEM rt*{rt}, DATA OK^n{}, LOCAL [], LABEL [], RETURN ?()})
    -- if (C' = {TYPE dt'*{dt'}, REC [], FUNC idt*{idt} :: dt*{dt}, GLOBAL igt*{igt}, TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [], RETURN ?()})
    -- if (idt*{idt} = $funcsxt(ixt*{ixt}))
    -- if (igt*{igt} = $globalsxt(ixt*{ixt}))
    -- if (itt*{itt} = $tablesxt(ixt*{ixt}))
    -- if (imt*{imt} = $memsxt(ixt*{ixt}))

;; 7-runtime-typing.watsup:5.1-5.40
relation Ref_ok: `%|-%:%`(store, ref, reftype)
  ;; 7-runtime-typing.watsup:7.1-8.35
  rule null {ht : heaptype, s : store}:
    `%|-%:%`(s, REF.NULL_ref(ht), REF_reftype(`NULL%?`(?(())), ht))

  ;; 7-runtime-typing.watsup:10.1-11.41
  rule i31 {i : nat, s : store}:
    `%|-%:%`(s, REF.I31_NUM_ref(i), REF_reftype(`NULL%?`(?()), I31_heaptype))

  ;; 7-runtime-typing.watsup:13.1-15.30
  rule struct {a : addr, dt : deftype, s : store}:
    `%|-%:%`(s, REF.STRUCT_ADDR_ref(a), REF_reftype(`NULL%?`(?()), (dt <: heaptype)))
    -- if (s.STRUCT_store[a].TYPE_structinst = dt)

  ;; 7-runtime-typing.watsup:17.1-19.29
  rule array {a : addr, dt : deftype, s : store}:
    `%|-%:%`(s, REF.ARRAY_ADDR_ref(a), REF_reftype(`NULL%?`(?()), (dt <: heaptype)))
    -- if (s.ARRAY_store[a].TYPE_arrayinst = dt)

  ;; 7-runtime-typing.watsup:21.1-23.28
  rule func {a : addr, dt : deftype, s : store}:
    `%|-%:%`(s, REF.FUNC_ADDR_ref(a), REF_reftype(`NULL%?`(?()), (dt <: heaptype)))
    -- if (s.FUNC_store[a].TYPE_funcinst = dt)

  ;; 7-runtime-typing.watsup:25.1-26.43
  rule host {a : addr, s : store}:
    `%|-%:%`(s, REF.HOST_ADDR_ref(a), REF_reftype(`NULL%?`(?()), ANY_heaptype))

  ;; 7-runtime-typing.watsup:28.1-29.49
  rule extern {addrref : addrref, s : store}:
    `%|-%:%`(s, REF.EXTERN_ref(addrref), REF_reftype(`NULL%?`(?()), EXTERN_heaptype))

;; 8-reduction.watsup:6.1-6.63
relation Step_pure: `%*~>%*`(admininstr*, admininstr*)
  ;; 8-reduction.watsup:42.1-43.24
  rule unreachable:
    `%*~>%*`([UNREACHABLE_admininstr], [TRAP_admininstr])

  ;; 8-reduction.watsup:45.1-46.19
  rule nop:
    `%*~>%*`([NOP_admininstr], [])

  ;; 8-reduction.watsup:48.1-49.24
  rule drop {val : val}:
    `%*~>%*`([(val <: admininstr) DROP_admininstr], [])

  ;; 8-reduction.watsup:52.1-54.16
  rule select-true {c : c_numtype, t? : valtype?, val_1 : val, val_2 : val}:
    `%*~>%*`([(val_1 <: admininstr) (val_2 <: admininstr) CONST_admininstr(I32_numtype, c) SELECT_admininstr(t?{t})], [(val_1 <: admininstr)])
    -- if (c =/= 0)

  ;; 8-reduction.watsup:56.1-58.14
  rule select-false {c : c_numtype, t? : valtype?, val_1 : val, val_2 : val}:
    `%*~>%*`([(val_1 <: admininstr) (val_2 <: admininstr) CONST_admininstr(I32_numtype, c) SELECT_admininstr(t?{t})], [(val_2 <: admininstr)])
    -- if (c = 0)

  ;; 8-reduction.watsup:63.1-65.28
  rule block {bt : blocktype, instr* : instr*, k : nat, n : n, t_1^k : valtype^k, t_2^n : valtype^n, val^k : val^k}:
    `%*~>%*`((val <: admininstr)^k{val} :: [BLOCK_admininstr(bt, instr*{instr})], [LABEL__admininstr(n, [], (val <: admininstr)^k{val} :: (instr <: admininstr)*{instr})])
    -- if (bt = `%->%`(t_1^k{t_1}, t_2^n{t_2}))

  ;; 8-reduction.watsup:67.1-69.28
  rule loop {bt : blocktype, instr* : instr*, k : nat, n : n, t_1^k : valtype^k, t_2^n : valtype^n, val^k : val^k}:
    `%*~>%*`((val <: admininstr)^k{val} :: [LOOP_admininstr(bt, instr*{instr})], [LABEL__admininstr(k, [LOOP_instr(bt, instr*{instr})], (val <: admininstr)^k{val} :: (instr <: admininstr)*{instr})])
    -- if (bt = `%->%`(t_1^k{t_1}, t_2^n{t_2}))

  ;; 8-reduction.watsup:71.1-73.16
  rule if-true {bt : blocktype, c : c_numtype, instr_1* : instr*, instr_2* : instr*}:
    `%*~>%*`([CONST_admininstr(I32_numtype, c) IF_admininstr(bt, instr_1*{instr_1}, instr_2*{instr_2})], [BLOCK_admininstr(bt, instr_1*{instr_1})])
    -- if (c =/= 0)

  ;; 8-reduction.watsup:75.1-77.14
  rule if-false {bt : blocktype, c : c_numtype, instr_1* : instr*, instr_2* : instr*}:
    `%*~>%*`([CONST_admininstr(I32_numtype, c) IF_admininstr(bt, instr_1*{instr_1}, instr_2*{instr_2})], [BLOCK_admininstr(bt, instr_2*{instr_2})])
    -- if (c = 0)

  ;; 8-reduction.watsup:80.1-81.38
  rule label-vals {instr* : instr*, n : n, val* : val*}:
    `%*~>%*`([LABEL__admininstr(n, instr*{instr}, (val <: admininstr)*{val})], (val <: admininstr)*{val})

  ;; 8-reduction.watsup:87.1-88.69
  rule br-zero {instr* : instr*, instr'* : instr*, n : n, val^n : val^n, val'* : val*}:
    `%*~>%*`([LABEL__admininstr(n, instr'*{instr'}, (val' <: admininstr)*{val'} :: (val <: admininstr)^n{val} :: [BR_admininstr(0)] :: (instr <: admininstr)*{instr})], (val <: admininstr)^n{val} :: (instr' <: admininstr)*{instr'})

  ;; 8-reduction.watsup:90.1-91.65
  rule br-succ {instr* : instr*, instr'* : instr*, l : labelidx, n : n, val* : val*}:
    `%*~>%*`([LABEL__admininstr(n, instr'*{instr'}, (val <: admininstr)*{val} :: [BR_admininstr(l + 1)] :: (instr <: admininstr)*{instr})], (val <: admininstr)*{val} :: [BR_admininstr(l)])

  ;; 8-reduction.watsup:94.1-96.16
  rule br_if-true {c : c_numtype, l : labelidx}:
    `%*~>%*`([CONST_admininstr(I32_numtype, c) BR_IF_admininstr(l)], [BR_admininstr(l)])
    -- if (c =/= 0)

  ;; 8-reduction.watsup:98.1-100.14
  rule br_if-false {c : c_numtype, l : labelidx}:
    `%*~>%*`([CONST_admininstr(I32_numtype, c) BR_IF_admininstr(l)], [])
    -- if (c = 0)

  ;; 8-reduction.watsup:103.1-105.17
  rule br_table-lt {i : nat, l* : labelidx*, l' : labelidx}:
    `%*~>%*`([CONST_admininstr(I32_numtype, i) BR_TABLE_admininstr(l*{l}, l')], [BR_admininstr(l*{l}[i])])
    -- if (i < |l*{l}|)

  ;; 8-reduction.watsup:107.1-109.18
  rule br_table-ge {i : nat, l* : labelidx*, l' : labelidx}:
    `%*~>%*`([CONST_admininstr(I32_numtype, i) BR_TABLE_admininstr(l*{l}, l')], [BR_admininstr(l')])
    -- if (i >= |l*{l}|)

  ;; 8-reduction.watsup:112.1-114.26
  rule br_on_null-null {ht : heaptype, l : labelidx, val : val}:
    `%*~>%*`([(val <: admininstr) BR_ON_NULL_admininstr(l)], [BR_admininstr(l)])
    -- if (val = REF.NULL_val(ht))

  ;; 8-reduction.watsup:116.1-118.15
  rule br_on_null-addr {l : labelidx, val : val}:
    `%*~>%*`([(val <: admininstr) BR_ON_NULL_admininstr(l)], [(val <: admininstr)])
    -- otherwise

  ;; 8-reduction.watsup:121.1-123.26
  rule br_on_non_null-null {ht : heaptype, l : labelidx, val : val}:
    `%*~>%*`([(val <: admininstr) BR_ON_NON_NULL_admininstr(l)], [])
    -- if (val = REF.NULL_val(ht))

  ;; 8-reduction.watsup:125.1-127.15
  rule br_on_non_null-addr {l : labelidx, val : val}:
    `%*~>%*`([(val <: admininstr) BR_ON_NON_NULL_admininstr(l)], [(val <: admininstr) BR_admininstr(l)])
    -- otherwise

  ;; 8-reduction.watsup:178.1-179.84
  rule call_indirect-call {x : idx, y : idx}:
    `%*~>%*`([CALL_INDIRECT_admininstr(x, y)], [TABLE.GET_admininstr(x) REF.CAST_admininstr(REF_reftype(`NULL%?`(?(())), ($idx(y) <: heaptype))) CALL_REF_admininstr(y)])

  ;; 8-reduction.watsup:181.1-182.98
  rule return_call_indirect {x : idx, y : idx}:
    `%*~>%*`([RETURN_CALL_INDIRECT_admininstr(x, y)], [TABLE.GET_admininstr(x) REF.CAST_admininstr(REF_reftype(`NULL%?`(?(())), ($idx(y) <: heaptype))) RETURN_CALL_REF_admininstr(y)])

  ;; 8-reduction.watsup:185.1-186.35
  rule frame-vals {f : frame, n : n, val^n : val^n}:
    `%*~>%*`([FRAME__admininstr(n, f, (val <: admininstr)^n{val})], (val <: admininstr)^n{val})

  ;; 8-reduction.watsup:188.1-189.55
  rule return-frame {f : frame, instr* : instr*, n : n, val^n : val^n, val'* : val*}:
    `%*~>%*`([FRAME__admininstr(n, f, (val' <: admininstr)*{val'} :: (val <: admininstr)^n{val} :: [RETURN_admininstr] :: (instr <: admininstr)*{instr})], (val <: admininstr)^n{val})

  ;; 8-reduction.watsup:191.1-192.60
  rule return-label {instr* : instr*, instr'* : instr*, k : nat, val* : val*}:
    `%*~>%*`([LABEL__admininstr(k, instr'*{instr'}, (val <: admininstr)*{val} :: [RETURN_admininstr] :: (instr <: admininstr)*{instr})], (val <: admininstr)*{val} :: [RETURN_admininstr])

  ;; 8-reduction.watsup:197.1-199.33
  rule unop-val {c : c_numtype, c_1 : c_numtype, nt : numtype, unop : unop_numtype}:
    `%*~>%*`([CONST_admininstr(nt, c_1) UNOP_admininstr(nt, unop)], [CONST_admininstr(nt, c)])
    -- if ($unop(unop, nt, c_1) = [c])

  ;; 8-reduction.watsup:201.1-203.39
  rule unop-trap {c_1 : c_numtype, nt : numtype, unop : unop_numtype}:
    `%*~>%*`([CONST_admininstr(nt, c_1) UNOP_admininstr(nt, unop)], [TRAP_admininstr])
    -- if ($unop(unop, nt, c_1) = [])

  ;; 8-reduction.watsup:206.1-208.40
  rule binop-val {binop : binop_numtype, c : c_numtype, c_1 : c_numtype, c_2 : c_numtype, nt : numtype}:
    `%*~>%*`([CONST_admininstr(nt, c_1) CONST_admininstr(nt, c_2) BINOP_admininstr(nt, binop)], [CONST_admininstr(nt, c)])
    -- if ($binop(binop, nt, c_1, c_2) = [c])

  ;; 8-reduction.watsup:210.1-212.46
  rule binop-trap {binop : binop_numtype, c_1 : c_numtype, c_2 : c_numtype, nt : numtype}:
    `%*~>%*`([CONST_admininstr(nt, c_1) CONST_admininstr(nt, c_2) BINOP_admininstr(nt, binop)], [TRAP_admininstr])
    -- if ($binop(binop, nt, c_1, c_2) = [])

  ;; 8-reduction.watsup:215.1-217.37
  rule testop {c : c_numtype, c_1 : c_numtype, nt : numtype, testop : testop_numtype}:
    `%*~>%*`([CONST_admininstr(nt, c_1) TESTOP_admininstr(nt, testop)], [CONST_admininstr(I32_numtype, c)])
    -- if (c = $testop(testop, nt, c_1))

  ;; 8-reduction.watsup:219.1-221.40
  rule relop {c : c_numtype, c_1 : c_numtype, c_2 : c_numtype, nt : numtype, relop : relop_numtype}:
    `%*~>%*`([CONST_admininstr(nt, c_1) CONST_admininstr(nt, c_2) RELOP_admininstr(nt, relop)], [CONST_admininstr(I32_numtype, c)])
    -- if (c = $relop(relop, nt, c_1, c_2))

  ;; 8-reduction.watsup:224.1-225.70
  rule extend {c : c_numtype, n : n, nt : numtype}:
    `%*~>%*`([CONST_admininstr(nt, c) EXTEND_admininstr(nt, n)], [CONST_admininstr(nt, $ext(n, $size(nt <: valtype), S_sx, c))])

  ;; 8-reduction.watsup:228.1-230.48
  rule cvtop-val {c : c_numtype, c_1 : c_numtype, cvtop : cvtop, nt_1 : numtype, nt_2 : numtype, sx? : sx?}:
    `%*~>%*`([CONST_admininstr(nt_1, c_1) CVTOP_admininstr(nt_2, cvtop, nt_1, sx?{sx})], [CONST_admininstr(nt_2, c)])
    -- if ($cvtop(cvtop, nt_1, nt_2, sx?{sx}, c_1) = [c])

  ;; 8-reduction.watsup:232.1-234.54
  rule cvtop-trap {c_1 : c_numtype, cvtop : cvtop, nt_1 : numtype, nt_2 : numtype, sx? : sx?}:
    `%*~>%*`([CONST_admininstr(nt_1, c_1) CVTOP_admininstr(nt_2, cvtop, nt_1, sx?{sx})], [TRAP_admininstr])
    -- if ($cvtop(cvtop, nt_1, nt_2, sx?{sx}, c_1) = [])

  ;; 8-reduction.watsup:242.1-243.60
  rule ref.i31 {i : nat}:
    `%*~>%*`([CONST_admininstr(I32_numtype, i) REF.I31_admininstr], [REF.I31_NUM_admininstr($wrap(32, 31, i))])

  ;; 8-reduction.watsup:246.1-248.28
  rule ref.is_null-true {ht : heaptype, val : val}:
    `%*~>%*`([(val <: admininstr) REF.IS_NULL_admininstr], [CONST_admininstr(I32_numtype, 1)])
    -- if (val = REF.NULL_val(ht))

  ;; 8-reduction.watsup:250.1-252.15
  rule ref.is_null-false {val : val}:
    `%*~>%*`([(val <: admininstr) REF.IS_NULL_admininstr], [CONST_admininstr(I32_numtype, 0)])
    -- otherwise

  ;; 8-reduction.watsup:255.1-257.28
  rule ref.as_non_null-null {ht : heaptype, ref : ref}:
    `%*~>%*`([(ref <: admininstr) REF.AS_NON_NULL_admininstr], [TRAP_admininstr])
    -- if (ref = REF.NULL_ref(ht))

  ;; 8-reduction.watsup:259.1-261.15
  rule ref.as_non_null-addr {ref : ref}:
    `%*~>%*`([(ref <: admininstr) REF.AS_NON_NULL_admininstr], [(ref <: admininstr)])
    -- otherwise

  ;; 8-reduction.watsup:264.1-266.55
  rule ref.eq-null {ht_1 : heaptype, ht_2 : heaptype, ref_1 : ref, ref_2 : ref}:
    `%*~>%*`([(ref_1 <: admininstr) (ref_2 <: admininstr) REF.EQ_admininstr], [CONST_admininstr(I32_numtype, 1)])
    -- if ((ref_1 = REF.NULL_ref(ht_1)) /\ (ref_2 = REF.NULL_ref(ht_2)))

  ;; 8-reduction.watsup:268.1-271.22
  rule ref.eq-true {ref_1 : ref, ref_2 : ref}:
    `%*~>%*`([(ref_1 <: admininstr) (ref_2 <: admininstr) REF.EQ_admininstr], [CONST_admininstr(I32_numtype, 1)])
    -- otherwise
    -- if (ref_1 = ref_2)

  ;; 8-reduction.watsup:273.1-275.15
  rule ref.eq-false {ref_1 : ref, ref_2 : ref}:
    `%*~>%*`([(ref_1 <: admininstr) (ref_2 <: admininstr) REF.EQ_admininstr], [CONST_admininstr(I32_numtype, 0)])
    -- otherwise

  ;; 8-reduction.watsup:300.1-301.39
  rule i31.get-null {ht : heaptype, sx : sx}:
    `%*~>%*`([REF.NULL_admininstr(ht) I31.GET_admininstr(sx)], [TRAP_admininstr])

  ;; 8-reduction.watsup:303.1-304.68
  rule i31.get-num {i : nat, sx : sx}:
    `%*~>%*`([REF.I31_NUM_admininstr(i) I31.GET_admininstr(sx)], [CONST_admininstr(I32_numtype, $ext(31, 32, sx, i))])

  ;; 8-reduction.watsup:519.1-520.58
  rule extern.externalize-null {ht : heaptype}:
    `%*~>%*`([REF.NULL_admininstr(ht) EXTERN.EXTERNALIZE_admininstr], [REF.NULL_admininstr(EXTERN_heaptype)])

  ;; 8-reduction.watsup:522.1-523.55
  rule extern.externalize-addr {addrref : addrref}:
    `%*~>%*`([(addrref <: admininstr) EXTERN.EXTERNALIZE_admininstr], [REF.EXTERN_admininstr(addrref)])

  ;; 8-reduction.watsup:526.1-527.55
  rule extern.internalize-null {ht : heaptype}:
    `%*~>%*`([REF.NULL_admininstr(ht) EXTERN.INTERNALIZE_admininstr], [REF.NULL_admininstr(ANY_heaptype)])

  ;; 8-reduction.watsup:529.1-530.55
  rule extern.internalize-addr {addrref : addrref}:
    `%*~>%*`([REF.EXTERN_admininstr(addrref) EXTERN.INTERNALIZE_admininstr], [(addrref <: admininstr)])

  ;; 8-reduction.watsup:542.1-543.47
  rule local.tee {val : val, x : idx}:
    `%*~>%*`([(val <: admininstr) LOCAL.TEE_admininstr(x)], [(val <: admininstr) (val <: admininstr) LOCAL.SET_admininstr(x)])

;; 8-reduction.watsup:7.1-7.63
relation Step_read: `%~>%*`(config, admininstr*)
  ;; 8-reduction.watsup:130.1-133.66
  rule br_on_cast-succeed {l : labelidx, ref : ref, rt : reftype, rt_1 : reftype, rt_2 : reftype, z : state}:
    `%~>%*`(`%;%*`(z, [(ref <: admininstr) BR_ON_CAST_admininstr(l, rt_1, rt_2)]), [(ref <: admininstr) BR_admininstr(l)])
    -- Ref_ok: `%|-%:%`($store(z), ref, rt)
    -- Reftype_sub: `%|-%<:%`({TYPE [], REC [], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [], RETURN ?()}, rt, $inst_reftype($moduleinst(z), rt_2))

  ;; 8-reduction.watsup:135.1-137.15
  rule br_on_cast-fail {l : labelidx, ref : ref, rt_1 : reftype, rt_2 : reftype, z : state}:
    `%~>%*`(`%;%*`(z, [(ref <: admininstr) BR_ON_CAST_admininstr(l, rt_1, rt_2)]), [(ref <: admininstr)])
    -- otherwise

  ;; 8-reduction.watsup:140.1-143.66
  rule br_on_cast_fail-succeed {l : labelidx, ref : ref, rt : reftype, rt_1 : reftype, rt_2 : reftype, z : state}:
    `%~>%*`(`%;%*`(z, [(ref <: admininstr) BR_ON_CAST_FAIL_admininstr(l, rt_1, rt_2)]), [(ref <: admininstr)])
    -- Ref_ok: `%|-%:%`($store(z), ref, rt)
    -- Reftype_sub: `%|-%<:%`({TYPE [], REC [], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [], RETURN ?()}, rt, $inst_reftype($moduleinst(z), rt_2))

  ;; 8-reduction.watsup:145.1-147.15
  rule br_on_cast_fail-fail {l : labelidx, ref : ref, rt_1 : reftype, rt_2 : reftype, z : state}:
    `%~>%*`(`%;%*`(z, [(ref <: admininstr) BR_ON_CAST_FAIL_admininstr(l, rt_1, rt_2)]), [(ref <: admininstr) BR_admininstr(l)])
    -- otherwise

  ;; 8-reduction.watsup:152.1-153.46
  rule call {x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CALL_admininstr(x)]), [CALL_REF_admininstr($funcaddr(z)[x])])

  ;; 8-reduction.watsup:155.1-156.42
  rule call_ref-null {ht : heaptype, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.NULL_admininstr(ht) CALL_REF_admininstr(x)]), [TRAP_admininstr])

  ;; 8-reduction.watsup:158.1-163.59
  rule call_ref-func {a : addr, f : frame, fi : funcinst, instr* : instr*, m : nat, n : n, t* : valtype*, t_1^n : valtype^n, t_2^m : valtype^m, val^n : val^n, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, (val <: admininstr)^n{val} :: [REF.FUNC_ADDR_admininstr(a) CALL_REF_admininstr(x)]), [FRAME__admininstr(m, f, [LABEL__admininstr(m, [], (instr <: admininstr)*{instr})])])
    -- if ($funcinst(z)[a] = fi)
    -- Expand: `%~~%`(fi.TYPE_funcinst, FUNC_comptype(`%->%`(t_1^n{t_1}, t_2^m{t_2})))
    -- if (fi.CODE_funcinst = `FUNC%%*%`(x, LOCAL(t)*{t}, instr*{instr}))
    -- if (f = {LOCAL ?(val)^n{val} :: $default(t)*{t}, MODULE fi.MODULE_funcinst})

  ;; 8-reduction.watsup:166.1-167.60
  rule return_call {x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [RETURN_CALL_admininstr(x)]), [RETURN_CALL_REF_admininstr($funcaddr(z)[x])])

  ;; 8-reduction.watsup:169.1-171.59
  rule return_call_ref-frame {a : addr, f : frame, instr* : instr*, k : nat, m : nat, n : n, ref : ref, t_1^n : valtype^n, t_2^m : valtype^m, val^n : val^n, val'* : val*, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [FRAME__admininstr(k, f, (val' <: admininstr)*{val'} :: (val <: admininstr)^n{val} :: [(ref <: admininstr)] :: [RETURN_CALL_REF_admininstr(x)] :: (instr <: admininstr)*{instr})]), (val <: admininstr)^n{val} :: [(ref <: admininstr) CALL_REF_admininstr(x)])
    -- Expand: `%~~%`($funcinst(z)[a].TYPE_funcinst, FUNC_comptype(`%->%`(t_1^n{t_1}, t_2^m{t_2})))

  ;; 8-reduction.watsup:173.1-175.59
  rule return_call_ref-label {a : addr, instr* : instr*, instr'* : instr*, k : nat, m : nat, n : n, ref : ref, t_1^n : valtype^n, t_2^m : valtype^m, val^n : val^n, val'* : val*, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [LABEL__admininstr(k, instr'*{instr'}, (val' <: admininstr)*{val'} :: (val <: admininstr)^n{val} :: [(ref <: admininstr)] :: [RETURN_CALL_REF_admininstr(x)] :: (instr <: admininstr)*{instr})]), (val <: admininstr)^n{val} :: [(ref <: admininstr) RETURN_CALL_REF_admininstr(x)])
    -- Expand: `%~~%`($funcinst(z)[a].TYPE_funcinst, FUNC_comptype(`%->%`(t_1^n{t_1}, t_2^m{t_2})))

  ;; 8-reduction.watsup:239.1-240.55
  rule ref.func {x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.FUNC_admininstr(x)]), [REF.FUNC_ADDR_admininstr($funcaddr(z)[x])])

  ;; 8-reduction.watsup:278.1-281.65
  rule ref.test-true {ref : ref, rt : reftype, rt' : reftype, z : state}:
    `%~>%*`(`%;%*`(z, [(ref <: admininstr) REF.TEST_admininstr(rt)]), [CONST_admininstr(I32_numtype, 1)])
    -- Ref_ok: `%|-%:%`($store(z), ref, rt')
    -- Reftype_sub: `%|-%<:%`({TYPE [], REC [], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [], RETURN ?()}, rt', $inst_reftype($moduleinst(z), rt))

  ;; 8-reduction.watsup:283.1-285.15
  rule ref.test-false {ref : ref, rt : reftype, z : state}:
    `%~>%*`(`%;%*`(z, [(ref <: admininstr) REF.TEST_admininstr(rt)]), [CONST_admininstr(I32_numtype, 0)])
    -- otherwise

  ;; 8-reduction.watsup:288.1-291.65
  rule ref.cast-succeed {ref : ref, rt : reftype, rt' : reftype, z : state}:
    `%~>%*`(`%;%*`(z, [(ref <: admininstr) REF.CAST_admininstr(rt)]), [(ref <: admininstr)])
    -- Ref_ok: `%|-%:%`($store(z), ref, rt')
    -- Reftype_sub: `%|-%<:%`({TYPE [], REC [], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [], RETURN ?()}, rt', $inst_reftype($moduleinst(z), rt))

  ;; 8-reduction.watsup:293.1-295.15
  rule ref.cast-fail {ref : ref, rt : reftype, z : state}:
    `%~>%*`(`%;%*`(z, [(ref <: admininstr) REF.CAST_admininstr(rt)]), [TRAP_admininstr])
    -- otherwise

  ;; 8-reduction.watsup:314.1-317.43
  rule struct.new_default {mut* : mut*, val* : val*, x : idx, z : state, zt* : storagetype*}:
    `%~>%*`(`%;%*`(z, [STRUCT.NEW_DEFAULT_admininstr(x)]), (val <: admininstr)*{val} :: [STRUCT.NEW_admininstr(x)])
    -- Expand: `%~~%`($type(z, x), STRUCT_comptype(`%%`(mut, zt)*{mut zt}))
    -- (if ($default($unpacktype(zt)) = ?(val)))*{val zt}

  ;; 8-reduction.watsup:320.1-321.50
  rule struct.get-null {ht : heaptype, i : nat, sx? : sx?, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.NULL_admininstr(ht) STRUCT.GET_admininstr(sx?{sx}, x, i)]), [TRAP_admininstr])

  ;; 8-reduction.watsup:323.1-326.41
  rule struct.get-struct {a : addr, i : nat, mut* : mut*, si : structinst, sx? : sx?, x : idx, z : state, zt* : storagetype*}:
    `%~>%*`(`%;%*`(z, [REF.STRUCT_ADDR_admininstr(a) STRUCT.GET_admininstr(sx?{sx}, x, i)]), [($unpackval(zt*{zt}[i], sx?{sx}, si.FIELD_structinst[i]) <: admininstr)])
    -- if ($structinst(z)[a] = si)
    -- Expand: `%~~%`(si.TYPE_structinst, STRUCT_comptype(`%%`(mut, zt)*{mut zt}))

  ;; 8-reduction.watsup:340.1-341.70
  rule array.new {n : n, val : val, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [(val <: admininstr) CONST_admininstr(I32_numtype, n) ARRAY.NEW_admininstr(x)]), (val <: admininstr)^n{} :: [ARRAY.NEW_FIXED_admininstr(x, n)])

  ;; 8-reduction.watsup:343.1-346.40
  rule array.new_default {mut : mut, n : n, val : val, x : idx, z : state, zt : storagetype}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, n) ARRAY.NEW_DEFAULT_admininstr(x)]), (val <: admininstr)^n{} :: [ARRAY.NEW_FIXED_admininstr(x, n)])
    -- Expand: `%~~%`($type(z, x), ARRAY_comptype(`%%`(mut, zt)))
    -- if ($default($unpacktype(zt)) = ?(val))

  ;; 8-reduction.watsup:354.1-356.38
  rule array.new_elem-oob {i : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, n) ARRAY.NEW_ELEM_admininstr(x, y)]), [TRAP_admininstr])
    -- if ((i + n) > |$elem(z, y).ELEM_eleminst|)

  ;; 8-reduction.watsup:358.1-360.40
  rule array.new_elem-alloc {i : nat, n : n, ref^n : ref^n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, n) ARRAY.NEW_ELEM_admininstr(x, y)]), (ref <: admininstr)^n{ref} :: [ARRAY.NEW_FIXED_admininstr(x, n)])
    -- if (ref^n{ref} = $elem(z, y).ELEM_eleminst[i : n])

  ;; 8-reduction.watsup:363.1-366.59
  rule array.new_data-oob {i : nat, mut : mut, n : n, x : idx, y : idx, z : state, zt : storagetype}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, n) ARRAY.NEW_DATA_admininstr(x, y)]), [TRAP_admininstr])
    -- Expand: `%~~%`($type(z, x), ARRAY_comptype(`%%`(mut, zt)))
    -- if ((i + ((n * $storagesize(zt)) / 8)) > |$data(z, y).DATA_datainst|)

  ;; 8-reduction.watsup:368.1-372.85
  rule array.new_data-alloc {c^n : c_numtype^n, i : nat, mut : mut, n : n, nt : numtype, x : idx, y : idx, z : state, zt : storagetype}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, n) ARRAY.NEW_DATA_admininstr(x, y)]), CONST_admininstr(nt, c)^n{c} :: [ARRAY.NEW_FIXED_admininstr(x, n)])
    -- Expand: `%~~%`($type(z, x), ARRAY_comptype(`%%`(mut, zt)))
    -- if (nt = $unpacknumtype(zt))
    -- if ($bytes($storagesize(zt), c)^n{c} = [$data(z, y).DATA_datainst][i : ((n * $storagesize(zt)) / 8)])

  ;; 8-reduction.watsup:375.1-376.61
  rule array.get-null {ht : heaptype, i : nat, sx? : sx?, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.NULL_admininstr(ht) CONST_admininstr(I32_numtype, i) ARRAY.GET_admininstr(sx?{sx}, x)]), [TRAP_admininstr])

  ;; 8-reduction.watsup:378.1-380.38
  rule array.get-oob {a : addr, i : nat, sx? : sx?, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) ARRAY.GET_admininstr(sx?{sx}, x)]), [TRAP_admininstr])
    -- if (i >= |$arrayinst(z)[a].FIELD_arrayinst|)

  ;; 8-reduction.watsup:382.1-385.53
  rule array.get-array {a : addr, fv : fieldval, i : nat, mut : mut, sx? : sx?, x : idx, z : state, zt : storagetype}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) ARRAY.GET_admininstr(sx?{sx}, x)]), [($unpackval(zt, sx?{sx}, fv) <: admininstr)])
    -- if (fv = $arrayinst(z)[a].FIELD_arrayinst[i])
    -- Expand: `%~~%`($arrayinst(z)[a].TYPE_arrayinst, ARRAY_comptype(`%%`(mut, zt)))

  ;; 8-reduction.watsup:401.1-402.39
  rule array.len-null {ht : heaptype, z : state}:
    `%~>%*`(`%;%*`(z, [REF.NULL_admininstr(ht) ARRAY.LEN_admininstr]), [TRAP_admininstr])

  ;; 8-reduction.watsup:404.1-406.37
  rule array.len-array {a : addr, n : n, z : state}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a) ARRAY.LEN_admininstr]), [CONST_admininstr(I32_numtype, n)])
    -- if (n = |$arrayinst(z)[a].FIELD_arrayinst|)

  ;; 8-reduction.watsup:409.1-410.76
  rule array.fill-null {ht : heaptype, i : nat, n : n, val : val, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.NULL_admininstr(ht) CONST_admininstr(I32_numtype, i) (val <: admininstr) CONST_admininstr(I32_numtype, n) ARRAY.FILL_admininstr(x)]), [TRAP_admininstr])

  ;; 8-reduction.watsup:412.1-414.44
  rule array.fill-oob {a : addr, i : nat, n : n, val : val, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) (val <: admininstr) CONST_admininstr(I32_numtype, n) ARRAY.FILL_admininstr(x)]), [TRAP_admininstr])
    -- if ((i + n) > |$arrayinst(z)[a].FIELD_arrayinst|)

  ;; 8-reduction.watsup:416.1-419.14
  rule array.fill-zero {a : addr, i : nat, n : n, val : val, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) (val <: admininstr) CONST_admininstr(I32_numtype, n) ARRAY.FILL_admininstr(x)]), [])
    -- otherwise
    -- if (n = 0)

  ;; 8-reduction.watsup:421.1-425.15
  rule array.fill-succ {a : addr, i : nat, n : n, val : val, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) (val <: admininstr) CONST_admininstr(I32_numtype, n) ARRAY.FILL_admininstr(x)]), [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) (val <: admininstr) ARRAY.SET_admininstr(x) REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, (i + 1)) (val <: admininstr) CONST_admininstr(I32_numtype, (n - 1)) ARRAY.FILL_admininstr(x)])
    -- otherwise

  ;; 8-reduction.watsup:427.1-428.102
  rule array.copy-null1 {ht_1 : heaptype, i_1 : nat, i_2 : nat, n : n, ref : ref, x_1 : idx, x_2 : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.NULL_admininstr(ht_1) CONST_admininstr(I32_numtype, i_1) (ref <: admininstr) CONST_admininstr(I32_numtype, i_2) CONST_admininstr(I32_numtype, n) ARRAY.COPY_admininstr(x_1, x_2)]), [TRAP_admininstr])

  ;; 8-reduction.watsup:430.1-431.102
  rule array.copy-null2 {ht_2 : heaptype, i_1 : nat, i_2 : nat, n : n, ref : ref, x_1 : idx, x_2 : idx, z : state}:
    `%~>%*`(`%;%*`(z, [(ref <: admininstr) CONST_admininstr(I32_numtype, i_1) REF.NULL_admininstr(ht_2) CONST_admininstr(I32_numtype, i_2) CONST_admininstr(I32_numtype, n) ARRAY.COPY_admininstr(x_1, x_2)]), [TRAP_admininstr])

  ;; 8-reduction.watsup:433.1-435.48
  rule array.copy-oob1 {a_1 : addr, a_2 : addr, i_1 : nat, i_2 : nat, n : n, x_1 : idx, x_2 : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a_1) CONST_admininstr(I32_numtype, i_1) REF.ARRAY_ADDR_admininstr(a_2) CONST_admininstr(I32_numtype, i_2) CONST_admininstr(I32_numtype, n) ARRAY.COPY_admininstr(x_1, x_2)]), [TRAP_admininstr])
    -- if ((i_1 + n) > |$arrayinst(z)[a_1].FIELD_arrayinst|)

  ;; 8-reduction.watsup:437.1-439.48
  rule array.copy-oob2 {a_1 : addr, a_2 : addr, i_1 : nat, i_2 : nat, n : n, x_1 : idx, x_2 : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a_1) CONST_admininstr(I32_numtype, i_1) REF.ARRAY_ADDR_admininstr(a_2) CONST_admininstr(I32_numtype, i_2) CONST_admininstr(I32_numtype, n) ARRAY.COPY_admininstr(x_1, x_2)]), [TRAP_admininstr])
    -- if ((i_2 + n) > |$arrayinst(z)[a_2].FIELD_arrayinst|)

  ;; 8-reduction.watsup:441.1-444.14
  rule array.copy-zero {a_1 : addr, a_2 : addr, i_1 : nat, i_2 : nat, n : n, x_1 : idx, x_2 : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a_1) CONST_admininstr(I32_numtype, i_1) REF.ARRAY_ADDR_admininstr(a_2) CONST_admininstr(I32_numtype, i_2) CONST_admininstr(I32_numtype, n) ARRAY.COPY_admininstr(x_1, x_2)]), [])
    -- otherwise
    -- if (n = 0)

  ;; 8-reduction.watsup:446.1-455.19
  rule array.copy-le {a_1 : addr, a_2 : addr, i_1 : nat, i_2 : nat, mut : mut, n : n, sx? : sx?, x_1 : idx, x_2 : idx, z : state, zt_2 : storagetype}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a_1) CONST_admininstr(I32_numtype, i_1) REF.ARRAY_ADDR_admininstr(a_2) CONST_admininstr(I32_numtype, i_2) CONST_admininstr(I32_numtype, n) ARRAY.COPY_admininstr(x_1, x_2)]), [REF.ARRAY_ADDR_admininstr(a_1) CONST_admininstr(I32_numtype, i_1) REF.ARRAY_ADDR_admininstr(a_2) CONST_admininstr(I32_numtype, i_2) ARRAY.GET_admininstr(sx?{sx}, x_2) ARRAY.SET_admininstr(x_1) REF.ARRAY_ADDR_admininstr(a_1) CONST_admininstr(I32_numtype, (i_1 + 1)) REF.ARRAY_ADDR_admininstr(a_2) CONST_admininstr(I32_numtype, (i_2 + 1)) CONST_admininstr(I32_numtype, (n - 1)) ARRAY.COPY_admininstr(x_1, x_2)])
    -- otherwise
    -- Expand: `%~~%`($type(z, x_2), ARRAY_comptype(`%%`(mut, zt_2)))
    -- if (sx?{sx} = $sxfield(zt_2))
    -- if (i_1 <= i_2)

  ;; 8-reduction.watsup:457.1-463.15
  rule array.copy-gt {a_1 : addr, a_2 : addr, i_1 : nat, i_2 : nat, n : n, sx? : sx?, x_1 : idx, x_2 : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a_1) CONST_admininstr(I32_numtype, i_1) REF.ARRAY_ADDR_admininstr(a_2) CONST_admininstr(I32_numtype, i_2) CONST_admininstr(I32_numtype, n) ARRAY.COPY_admininstr(x_1, x_2)]), [REF.ARRAY_ADDR_admininstr(a_1) CONST_admininstr(I32_numtype, ((i_1 + n) - 1)) REF.ARRAY_ADDR_admininstr(a_2) CONST_admininstr(I32_numtype, ((i_2 + n) - 1)) ARRAY.GET_admininstr(sx?{sx}, x_2) ARRAY.SET_admininstr(x_1) REF.ARRAY_ADDR_admininstr(a_1) CONST_admininstr(I32_numtype, i_1) REF.ARRAY_ADDR_admininstr(a_2) CONST_admininstr(I32_numtype, i_2) CONST_admininstr(I32_numtype, (n - 1)) ARRAY.COPY_admininstr(x_1, x_2)])
    -- otherwise

  ;; 8-reduction.watsup:466.1-467.93
  rule array.init_elem-null {ht : heaptype, i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.NULL_admininstr(ht) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, n) ARRAY.INIT_ELEM_admininstr(x, y)]), [TRAP_admininstr])

  ;; 8-reduction.watsup:469.1-471.44
  rule array.init_elem-oob1 {a : addr, i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, n) ARRAY.INIT_ELEM_admininstr(x, y)]), [TRAP_admininstr])
    -- if ((i + n) > |$arrayinst(z)[a].FIELD_arrayinst|)

  ;; 8-reduction.watsup:473.1-475.38
  rule array.init_elem-oob2 {a : addr, i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, n) ARRAY.INIT_ELEM_admininstr(x, y)]), [TRAP_admininstr])
    -- if ((j + n) > |$elem(z, y).ELEM_eleminst|)

  ;; 8-reduction.watsup:477.1-480.14
  rule array.init_elem-zero {a : addr, i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, n) ARRAY.INIT_ELEM_admininstr(x, y)]), [])
    -- otherwise
    -- if (n = 0)

  ;; 8-reduction.watsup:482.1-487.34
  rule array.init_elem-succ {a : addr, i : nat, j : nat, n : n, ref : ref, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, n) ARRAY.INIT_ELEM_admininstr(x, y)]), [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) (ref <: admininstr) ARRAY.SET_admininstr(x) REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, (i + 1)) CONST_admininstr(I32_numtype, (j + 1)) CONST_admininstr(I32_numtype, (n - 1)) ARRAY.INIT_ELEM_admininstr(x, y)])
    -- otherwise
    -- if (ref = $elem(z, y).ELEM_eleminst[j])

  ;; 8-reduction.watsup:490.1-491.93
  rule array.init_data-null {ht : heaptype, i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.NULL_admininstr(ht) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, n) ARRAY.INIT_DATA_admininstr(x, y)]), [TRAP_admininstr])

  ;; 8-reduction.watsup:493.1-495.44
  rule array.init_data-oob1 {a : addr, i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, n) ARRAY.INIT_DATA_admininstr(x, y)]), [TRAP_admininstr])
    -- if ((i + n) > |$arrayinst(z)[a].FIELD_arrayinst|)

  ;; 8-reduction.watsup:497.1-500.59
  rule array.init_data-oob2 {a : addr, i : nat, j : nat, mut : mut, n : n, x : idx, y : idx, z : state, zt : storagetype}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, n) ARRAY.INIT_DATA_admininstr(x, y)]), [TRAP_admininstr])
    -- Expand: `%~~%`($type(z, x), ARRAY_comptype(`%%`(mut, zt)))
    -- if ((j + ((n * $storagesize(zt)) / 8)) > |$data(z, y).DATA_datainst|)

  ;; 8-reduction.watsup:502.1-505.14
  rule array.init_data-zero {a : addr, i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, n) ARRAY.INIT_DATA_admininstr(x, y)]), [])
    -- otherwise
    -- if (n = 0)

  ;; 8-reduction.watsup:507.1-514.79
  rule array.init_data-succ {a : addr, c : c_numtype, i : nat, j : nat, mut : mut, n : n, nt : numtype, x : idx, y : idx, z : state, zt : storagetype}:
    `%~>%*`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, n) ARRAY.INIT_DATA_admininstr(x, y)]), [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) CONST_admininstr(nt, c) ARRAY.SET_admininstr(x) REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, (i + 1)) CONST_admininstr(I32_numtype, (j + 1)) CONST_admininstr(I32_numtype, (n - 1)) ARRAY.INIT_DATA_admininstr(x, y)])
    -- otherwise
    -- Expand: `%~~%`($type(z, x), ARRAY_comptype(`%%`(mut, zt)))
    -- if (nt = $unpacknumtype(zt))
    -- if ($bytes($storagesize(zt), c) = $data(z, y).DATA_datainst[j : ($storagesize(zt) / 8)])

  ;; 8-reduction.watsup:535.1-537.27
  rule local.get {val : val, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [LOCAL.GET_admininstr(x)]), [(val <: admininstr)])
    -- if ($local(z, x) = ?(val))

  ;; 8-reduction.watsup:548.1-549.45
  rule global.get {x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [GLOBAL.GET_admininstr(x)]), [($global(z, x).VALUE_globalinst <: admininstr)])

  ;; 8-reduction.watsup:557.1-559.33
  rule table.get-oob {i : nat, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) TABLE.GET_admininstr(x)]), [TRAP_admininstr])
    -- if (i >= |$table(z, x).ELEM_tableinst|)

  ;; 8-reduction.watsup:561.1-563.32
  rule table.get-val {i : nat, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) TABLE.GET_admininstr(x)]), [($table(z, x).ELEM_tableinst[i] <: admininstr)])
    -- if (i < |$table(z, x).ELEM_tableinst|)

  ;; 8-reduction.watsup:574.1-576.32
  rule table.size {n : n, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [TABLE.SIZE_admininstr(x)]), [CONST_admininstr(I32_numtype, n)])
    -- if (|$table(z, x).ELEM_tableinst| = n)

  ;; 8-reduction.watsup:587.1-589.39
  rule table.fill-oob {i : nat, n : n, val : val, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) (val <: admininstr) CONST_admininstr(I32_numtype, n) TABLE.FILL_admininstr(x)]), [TRAP_admininstr])
    -- if ((i + n) > |$table(z, x).ELEM_tableinst|)

  ;; 8-reduction.watsup:591.1-594.14
  rule table.fill-zero {i : nat, n : n, val : val, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) (val <: admininstr) CONST_admininstr(I32_numtype, n) TABLE.FILL_admininstr(x)]), [])
    -- otherwise
    -- if (n = 0)

  ;; 8-reduction.watsup:596.1-600.15
  rule table.fill-succ {i : nat, n : n, val : val, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) (val <: admininstr) CONST_admininstr(I32_numtype, n) TABLE.FILL_admininstr(x)]), [CONST_admininstr(I32_numtype, i) (val <: admininstr) TABLE.SET_admininstr(x) CONST_admininstr(I32_numtype, (i + 1)) (val <: admininstr) CONST_admininstr(I32_numtype, (n - 1)) TABLE.FILL_admininstr(x)])
    -- otherwise

  ;; 8-reduction.watsup:603.1-605.73
  rule table.copy-oob {i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, n) TABLE.COPY_admininstr(x, y)]), [TRAP_admininstr])
    -- if (((i + n) > |$table(z, y).ELEM_tableinst|) \/ ((j + n) > |$table(z, x).ELEM_tableinst|))

  ;; 8-reduction.watsup:607.1-610.14
  rule table.copy-zero {i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, n) TABLE.COPY_admininstr(x, y)]), [])
    -- otherwise
    -- if (n = 0)

  ;; 8-reduction.watsup:612.1-617.15
  rule table.copy-le {i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, n) TABLE.COPY_admininstr(x, y)]), [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) TABLE.GET_admininstr(y) TABLE.SET_admininstr(x) CONST_admininstr(I32_numtype, (j + 1)) CONST_admininstr(I32_numtype, (i + 1)) CONST_admininstr(I32_numtype, (n - 1)) TABLE.COPY_admininstr(x, y)])
    -- otherwise
    -- if (j <= i)

  ;; 8-reduction.watsup:619.1-623.15
  rule table.copy-gt {i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, n) TABLE.COPY_admininstr(x, y)]), [CONST_admininstr(I32_numtype, ((j + n) - 1)) CONST_admininstr(I32_numtype, ((i + n) - 1)) TABLE.GET_admininstr(y) TABLE.SET_admininstr(x) CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, (n - 1)) TABLE.COPY_admininstr(x, y)])
    -- otherwise

  ;; 8-reduction.watsup:626.1-628.72
  rule table.init-oob {i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, n) TABLE.INIT_admininstr(x, y)]), [TRAP_admininstr])
    -- if (((i + n) > |$elem(z, y).ELEM_eleminst|) \/ ((j + n) > |$table(z, x).ELEM_tableinst|))

  ;; 8-reduction.watsup:630.1-633.14
  rule table.init-zero {i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, n) TABLE.INIT_admininstr(x, y)]), [])
    -- otherwise
    -- if (n = 0)

  ;; 8-reduction.watsup:635.1-639.15
  rule table.init-succ {i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, n) TABLE.INIT_admininstr(x, y)]), [CONST_admininstr(I32_numtype, j) ($elem(z, y).ELEM_eleminst[i] <: admininstr) TABLE.SET_admininstr(x) CONST_admininstr(I32_numtype, (j + 1)) CONST_admininstr(I32_numtype, (i + 1)) CONST_admininstr(I32_numtype, (n - 1)) TABLE.INIT_admininstr(x, y)])
    -- otherwise

  ;; 8-reduction.watsup:648.1-650.53
  rule load-num-oob {i : nat, n_A : n, n_O : n, nt : numtype, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) LOAD_admininstr(nt, ?(), x, n_A, n_O)]), [TRAP_admininstr])
    -- if (((i + n_O) + ($size(nt <: valtype) / 8)) > |$mem(z, x).DATA_meminst|)

  ;; 8-reduction.watsup:652.1-654.70
  rule load-num-val {c : c_numtype, i : nat, n_A : n, n_O : n, nt : numtype, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) LOAD_admininstr(nt, ?(), x, n_A, n_O)]), [CONST_admininstr(nt, c)])
    -- if ($bytes($size(nt <: valtype), c) = $mem(z, x).DATA_meminst[(i + n_O) : ($size(nt <: valtype) / 8)])

  ;; 8-reduction.watsup:656.1-658.45
  rule load-pack-oob {i : nat, n : n, n_A : n, n_O : n, nt : numtype, sx : sx, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) LOAD_admininstr(nt, ?((n, sx)), x, n_A, n_O)]), [TRAP_admininstr])
    -- if (((i + n_O) + (n / 8)) > |$mem(z, x).DATA_meminst|)

  ;; 8-reduction.watsup:660.1-662.54
  rule load-pack-val {c : c_numtype, i : nat, n : n, n_A : n, n_O : n, nt : numtype, sx : sx, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) LOAD_admininstr(nt, ?((n, sx)), x, n_A, n_O)]), [CONST_admininstr(nt, $ext(n, $size(nt <: valtype), sx, c))])
    -- if ($bytes(n, c) = $mem(z, x).DATA_meminst[(i + n_O) : (n / 8)])

  ;; 8-reduction.watsup:682.1-684.44
  rule memory.size {n : n, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [MEMORY.SIZE_admininstr(x)]), [CONST_admininstr(I32_numtype, n)])
    -- if (((n * 64) * $Ki) = |$mem(z, x).DATA_meminst|)

  ;; 8-reduction.watsup:695.1-697.37
  rule memory.fill-oob {i : nat, n : n, val : val, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) (val <: admininstr) CONST_admininstr(I32_numtype, n) MEMORY.FILL_admininstr(x)]), [TRAP_admininstr])
    -- if ((i + n) > |$mem(z, x).DATA_meminst|)

  ;; 8-reduction.watsup:699.1-702.14
  rule memory.fill-zero {i : nat, n : n, val : val, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) (val <: admininstr) CONST_admininstr(I32_numtype, n) MEMORY.FILL_admininstr(x)]), [])
    -- otherwise
    -- if (n = 0)

  ;; 8-reduction.watsup:704.1-708.15
  rule memory.fill-succ {i : nat, n : n, val : val, x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) (val <: admininstr) CONST_admininstr(I32_numtype, n) MEMORY.FILL_admininstr(x)]), [CONST_admininstr(I32_numtype, i) (val <: admininstr) STORE_admininstr(I32_numtype, ?(8), x, 0, 0) CONST_admininstr(I32_numtype, (i + 1)) (val <: admininstr) CONST_admininstr(I32_numtype, (n - 1)) MEMORY.FILL_admininstr(x)])
    -- otherwise

  ;; 8-reduction.watsup:711.1-713.77
  rule memory.copy-oob {i_1 : nat, i_2 : nat, n : n, x_1 : idx, x_2 : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i_1) CONST_admininstr(I32_numtype, i_2) CONST_admininstr(I32_numtype, n) MEMORY.COPY_admininstr(x_1, x_2)]), [TRAP_admininstr])
    -- if (((i_1 + n) > |$mem(z, x_1).DATA_meminst|) \/ ((i_2 + n) > |$mem(z, x_2).DATA_meminst|))

  ;; 8-reduction.watsup:715.1-718.14
  rule memory.copy-zero {i_1 : nat, i_2 : nat, n : n, x_1 : idx, x_2 : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i_1) CONST_admininstr(I32_numtype, i_2) CONST_admininstr(I32_numtype, n) MEMORY.COPY_admininstr(x_1, x_2)]), [])
    -- otherwise
    -- if (n = 0)

  ;; 8-reduction.watsup:720.1-725.19
  rule memory.copy-le {i_1 : nat, i_2 : nat, n : n, x_1 : idx, x_2 : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i_1) CONST_admininstr(I32_numtype, i_2) CONST_admininstr(I32_numtype, n) MEMORY.COPY_admininstr(x_1, x_2)]), [CONST_admininstr(I32_numtype, i_1) CONST_admininstr(I32_numtype, i_2) LOAD_admininstr(I32_numtype, ?((8, U_sx)), x_2, 0, 0) STORE_admininstr(I32_numtype, ?(8), x_1, 0, 0) CONST_admininstr(I32_numtype, (i_1 + 1)) CONST_admininstr(I32_numtype, (i_2 + 1)) CONST_admininstr(I32_numtype, (n - 1)) MEMORY.COPY_admininstr(x_1, x_2)])
    -- otherwise
    -- if (i_1 <= i_2)

  ;; 8-reduction.watsup:727.1-731.15
  rule memory.copy-gt {i_1 : nat, i_2 : nat, n : n, x_1 : idx, x_2 : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, i_1) CONST_admininstr(I32_numtype, i_2) CONST_admininstr(I32_numtype, n) MEMORY.COPY_admininstr(x_1, x_2)]), [CONST_admininstr(I32_numtype, ((i_1 + n) - 1)) CONST_admininstr(I32_numtype, ((i_2 + n) - 1)) LOAD_admininstr(I32_numtype, ?((8, U_sx)), x_2, 0, 0) STORE_admininstr(I32_numtype, ?(8), x_1, 0, 0) CONST_admininstr(I32_numtype, i_1) CONST_admininstr(I32_numtype, i_2) CONST_admininstr(I32_numtype, (n - 1)) MEMORY.COPY_admininstr(x_1, x_2)])
    -- otherwise

  ;; 8-reduction.watsup:734.1-736.70
  rule memory.init-oob {i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, n) MEMORY.INIT_admininstr(x, y)]), [TRAP_admininstr])
    -- if (((i + n) > |$data(z, y).DATA_datainst|) \/ ((j + n) > |$mem(z, x).DATA_meminst|))

  ;; 8-reduction.watsup:738.1-741.14
  rule memory.init-zero {i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, n) MEMORY.INIT_admininstr(x, y)]), [])
    -- otherwise
    -- if (n = 0)

  ;; 8-reduction.watsup:743.1-747.15
  rule memory.init-succ {i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, n) MEMORY.INIT_admininstr(x, y)]), [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, $data(z, y).DATA_datainst[i]) STORE_admininstr(I32_numtype, ?(8), x, 0, 0) CONST_admininstr(I32_numtype, (j + 1)) CONST_admininstr(I32_numtype, (i + 1)) CONST_admininstr(I32_numtype, (n - 1)) MEMORY.INIT_admininstr(x, y)])
    -- otherwise

;; 8-reduction.watsup:5.1-5.63
relation Step: `%~>%`(config, config)
  ;; 8-reduction.watsup:9.1-11.34
  rule pure {instr* : instr*, instr'* : instr*, z : state}:
    `%~>%`(`%;%*`(z, (instr <: admininstr)*{instr}), `%;%*`(z, (instr' <: admininstr)*{instr'}))
    -- Step_pure: `%*~>%*`((instr <: admininstr)*{instr}, (instr' <: admininstr)*{instr'})

  ;; 8-reduction.watsup:13.1-15.37
  rule read {instr* : instr*, instr'* : instr*, z : state}:
    `%~>%`(`%;%*`(z, (instr <: admininstr)*{instr}), `%;%*`(z, (instr' <: admininstr)*{instr'}))
    -- Step_read: `%~>%*`(`%;%*`(z, (instr <: admininstr)*{instr}), (instr' <: admininstr)*{instr'})

  ;; 8-reduction.watsup:309.1-312.61
  rule struct.new {mut^n : mut^n, n : n, si : structinst, val^n : val^n, x : idx, z : state, zt^n : storagetype^n}:
    `%~>%`(`%;%*`(z, (val <: admininstr)^n{val} :: [STRUCT.NEW_admininstr(x)]), `%;%*`($ext_structinst(z, [si]), [REF.STRUCT_ADDR_admininstr(|$structinst(z)|)]))
    -- Expand: `%~~%`($type(z, x), STRUCT_comptype(`%%`(mut, zt)^n{mut zt}))
    -- if (si = {TYPE $type(z, x), FIELD $packval(zt, val)^n{val zt}})

  ;; 8-reduction.watsup:329.1-330.53
  rule struct.set-null {ht : heaptype, i : nat, val : val, x : idx, z : state}:
    `%~>%`(`%;%*`(z, [REF.NULL_admininstr(ht) (val <: admininstr) STRUCT.SET_admininstr(x, i)]), `%;%*`(z, [TRAP_admininstr]))

  ;; 8-reduction.watsup:332.1-335.35
  rule struct.set-struct {a : addr, fv : fieldval, i : nat, mut* : mut*, val : val, x : idx, z : state, zt* : storagetype*}:
    `%~>%`(`%;%*`(z, [REF.STRUCT_ADDR_admininstr(a) (val <: admininstr) STRUCT.SET_admininstr(x, i)]), `%;%*`($with_struct(z, a, i, fv), []))
    -- Expand: `%~~%`($structinst(z)[a].TYPE_structinst, STRUCT_comptype(`%%`(mut, zt)*{mut zt}))
    -- if (fv = $packval(zt*{zt}[i], val))

  ;; 8-reduction.watsup:348.1-351.61
  rule array.new_fixed {ai : arrayinst, mut : mut, n : n, val^n : val^n, x : idx, z : state, zt : storagetype}:
    `%~>%`(`%;%*`(z, (val <: admininstr)^n{val} :: [ARRAY.NEW_FIXED_admininstr(x, n)]), `%;%*`($ext_arrayinst(z, [ai]), [REF.ARRAY_ADDR_admininstr(|$arrayinst(z)|)]))
    -- Expand: `%~~%`($type(z, x), ARRAY_comptype(`%%`(mut, zt)))
    -- if (ai = {TYPE $type(z, x), FIELD $packval(zt, val)^n{val}})

  ;; 8-reduction.watsup:388.1-389.64
  rule array.set-null {ht : heaptype, i : nat, val : val, x : idx, z : state}:
    `%~>%`(`%;%*`(z, [REF.NULL_admininstr(ht) CONST_admininstr(I32_numtype, i) (val <: admininstr) ARRAY.SET_admininstr(x)]), `%;%*`(z, [TRAP_admininstr]))

  ;; 8-reduction.watsup:391.1-393.38
  rule array.set-oob {a : addr, i : nat, val : val, x : idx, z : state}:
    `%~>%`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) (val <: admininstr) ARRAY.SET_admininstr(x)]), `%;%*`(z, [TRAP_admininstr]))
    -- if (i >= |$arrayinst(z)[a].FIELD_arrayinst|)

  ;; 8-reduction.watsup:395.1-398.31
  rule array.set-array {a : addr, fv : fieldval, i : nat, mut : mut, val : val, x : idx, z : state, zt : storagetype}:
    `%~>%`(`%;%*`(z, [REF.ARRAY_ADDR_admininstr(a) CONST_admininstr(I32_numtype, i) (val <: admininstr) ARRAY.SET_admininstr(x)]), `%;%*`($with_array(z, a, i, fv), []))
    -- Expand: `%~~%`($arrayinst(z)[a].TYPE_arrayinst, ARRAY_comptype(`%%`(mut, zt)))
    -- if (fv = $packval(zt, val))

  ;; 8-reduction.watsup:539.1-540.60
  rule local.set {val : val, x : idx, z : state}:
    `%~>%`(`%;%*`(z, [(val <: admininstr) LOCAL.SET_admininstr(x)]), `%;%*`($with_local(z, x, val), []))

  ;; 8-reduction.watsup:551.1-552.62
  rule global.set {val : val, x : idx, z : state}:
    `%~>%`(`%;%*`(z, [(val <: admininstr) GLOBAL.SET_admininstr(x)]), `%;%*`($with_global(z, x, val), []))

  ;; 8-reduction.watsup:565.1-567.33
  rule table.set-oob {i : nat, ref : ref, x : idx, z : state}:
    `%~>%`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) (ref <: admininstr) TABLE.SET_admininstr(x)]), `%;%*`(z, [TRAP_admininstr]))
    -- if (i >= |$table(z, x).ELEM_tableinst|)

  ;; 8-reduction.watsup:569.1-571.32
  rule table.set-val {i : nat, ref : ref, x : idx, z : state}:
    `%~>%`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) (ref <: admininstr) TABLE.SET_admininstr(x)]), `%;%*`($with_table(z, x, i, ref), []))
    -- if (i < |$table(z, x).ELEM_tableinst|)

  ;; 8-reduction.watsup:579.1-581.46
  rule table.grow-succeed {n : n, ref : ref, ti : tableinst, x : idx, z : state}:
    `%~>%`(`%;%*`(z, [(ref <: admininstr) CONST_admininstr(I32_numtype, n) TABLE.GROW_admininstr(x)]), `%;%*`($with_tableinst(z, x, ti), [CONST_admininstr(I32_numtype, |$table(z, x).ELEM_tableinst|)]))
    -- if ($growtable($table(z, x), n, ref) = ti)

  ;; 8-reduction.watsup:583.1-584.64
  rule table.grow-fail {n : n, ref : ref, x : idx, z : state}:
    `%~>%`(`%;%*`(z, [(ref <: admininstr) CONST_admininstr(I32_numtype, n) TABLE.GROW_admininstr(x)]), `%;%*`(z, [CONST_admininstr(I32_numtype, - 1)]))

  ;; 8-reduction.watsup:642.1-643.59
  rule elem.drop {x : idx, z : state}:
    `%~>%`(`%;%*`(z, [ELEM.DROP_admininstr(x)]), `%;%*`($with_elem(z, x, []), []))

  ;; 8-reduction.watsup:665.1-667.53
  rule store-num-oob {c : c_numtype, i : nat, n_A : n, n_O : n, nt : numtype, x : idx, z : state}:
    `%~>%`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) CONST_admininstr(nt, c) STORE_admininstr(nt, ?(), x, n_A, n_O)]), `%;%*`(z, [TRAP_admininstr]))
    -- if (((i + n_O) + ($size(nt <: valtype) / 8)) > |$mem(z, x).DATA_meminst|)

  ;; 8-reduction.watsup:669.1-671.34
  rule store-num-val {b* : byte*, c : c_numtype, i : nat, n_A : n, n_O : n, nt : numtype, x : idx, z : state}:
    `%~>%`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) CONST_admininstr(nt, c) STORE_admininstr(nt, ?(), x, n_A, n_O)]), `%;%*`($with_mem(z, x, (i + n_O), ($size(nt <: valtype) / 8), b*{b}), []))
    -- if (b*{b} = $bytes($size(nt <: valtype), c))

  ;; 8-reduction.watsup:673.1-675.45
  rule store-pack-oob {c : c_numtype, i : nat, n : n, n_A : n, n_O : n, nt : numtype, x : idx, z : state}:
    `%~>%`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) CONST_admininstr(nt, c) STORE_admininstr(nt, ?(n), x, n_A, n_O)]), `%;%*`(z, [TRAP_admininstr]))
    -- if (((i + n_O) + (n / 8)) > |$mem(z, x).DATA_meminst|)

  ;; 8-reduction.watsup:677.1-679.47
  rule store-pack-val {b* : byte*, c : c_numtype, i : nat, n : n, n_A : n, n_O : n, nt : numtype, x : idx, z : state}:
    `%~>%`(`%;%*`(z, [CONST_admininstr(I32_numtype, i) CONST_admininstr(nt, c) STORE_admininstr(nt, ?(n), x, n_A, n_O)]), `%;%*`($with_mem(z, x, (i + n_O), (n / 8), b*{b}), []))
    -- if (b*{b} = $bytes(n, $wrap($size(nt <: valtype), n, c)))

  ;; 8-reduction.watsup:687.1-689.40
  rule memory.grow-succeed {mi : meminst, n : n, x : idx, z : state}:
    `%~>%`(`%;%*`(z, [CONST_admininstr(I32_numtype, n) MEMORY.GROW_admininstr(x)]), `%;%*`($with_meminst(z, x, mi), [CONST_admininstr(I32_numtype, (|$mem(z, 0).DATA_meminst| / (64 * $Ki)))]))
    -- if ($growmemory($mem(z, x), n) = mi)

  ;; 8-reduction.watsup:691.1-692.61
  rule memory.grow-fail {n : n, x : idx, z : state}:
    `%~>%`(`%;%*`(z, [CONST_admininstr(I32_numtype, n) MEMORY.GROW_admininstr(x)]), `%;%*`(z, [CONST_admininstr(I32_numtype, - 1)]))

  ;; 8-reduction.watsup:750.1-751.59
  rule data.drop {x : idx, z : state}:
    `%~>%`(`%;%*`(z, [DATA.DROP_admininstr(x)]), `%;%*`($with_data(z, x, []), []))

;; 8-reduction.watsup:20.1-20.59
rec {

;; 8-reduction.watsup:20.1-20.59
relation Eval: `%~>*%;%*`(config, state, val*)
  ;; 8-reduction.watsup:23.1-24.22
  rule done {val* : val*, z : state}:
    `%~>*%;%*`(`%;%*`(z, (val <: admininstr)*{val}), z, val*{val})

  ;; 8-reduction.watsup:26.1-29.43
  rule step {admininstr* : admininstr*, admininstr' : admininstr, val* : val*, z : state, z' : state, z'' : state}:
    `%~>*%;%*`(`%;%*`(z, admininstr*{admininstr}), z'', val*{val})
    -- Step: `%~>%`(`%;%*`(z, admininstr*{admininstr}), `%;%*`(z', admininstr'*{}))
    -- Eval: `%~>*%;%*`(`%;%*`(z', [admininstr']), z'', val*{val})
}

;; 8-reduction.watsup:21.1-21.69
relation Eval_expr: `%;%~>*%;%*`(state, expr, state, val*)
  ;; 8-reduction.watsup:31.1-33.35
  rule _ {instr* : instr*, val* : val*, z : state, z' : state}:
    `%;%~>*%;%*`(z, instr*{instr}, z', val*{val})
    -- Eval: `%~>*%;%*`(`%;%*`(z, (instr <: admininstr)*{instr}), z, val*{val})

;; 9-module.watsup:7.1-7.37
rec {

;; 9-module.watsup:7.1-7.37
def alloctypes : rectype* -> deftype*
  ;; 9-module.watsup:8.1-8.35
  def alloctypes([]) = []
  ;; 9-module.watsup:9.1-12.24
  def {deftype* : deftype*, deftype'* : deftype*, rectype : rectype, rectype'* : rectype*, x : idx} alloctypes(rectype'*{rectype'} :: [rectype]) = deftype'*{deftype'} :: deftype*{deftype}
    -- if (deftype'*{deftype'} = $alloctypes(rectype'*{rectype'}))
    -- if (deftype*{deftype} = $subst_all_deftypes($rolldt(x, rectype), (deftype' <: heaptype)*{deftype'}))
    -- if (x = |deftype'*{deftype'}|)
}

;; 9-module.watsup:14.1-14.60
def allocfunc : (store, moduleinst, func) -> (store, funcaddr)
  ;; 9-module.watsup:15.1-17.55
  def {expr : expr, fi : funcinst, func : func, local* : local*, mm : moduleinst, s : store, x : idx} allocfunc(s, mm, func) = (s[FUNC_store =.. [fi]], |s.FUNC_store|)
    -- if (func = `FUNC%%*%`(x, local*{local}, expr))
    -- if (fi = {TYPE mm.TYPE_moduleinst[x], MODULE mm, CODE func})

;; 9-module.watsup:19.1-19.63
rec {

;; 9-module.watsup:19.1-19.63
def allocfuncs : (store, moduleinst, func*) -> (store, funcaddr*)
  ;; 9-module.watsup:20.1-20.47
  def {mm : moduleinst, s : store} allocfuncs(s, mm, []) = (s, [])
  ;; 9-module.watsup:21.1-23.51
  def {fa : funcaddr, fa'* : funcaddr*, func : func, func'* : func*, mm : moduleinst, s : store, s_1 : store, s_2 : store} allocfuncs(s, mm, [func] :: func'*{func'}) = (s_2, [fa] :: fa'*{fa'})
    -- if ((s_1, fa) = $allocfunc(s, mm, func))
    -- if ((s_2, fa'*{fa'}) = $allocfuncs(s_1, mm, func'*{func'}))
}

;; 9-module.watsup:25.1-25.63
def allocglobal : (store, globaltype, val) -> (store, globaladdr)
  ;; 9-module.watsup:26.1-27.44
  def {gi : globalinst, globaltype : globaltype, s : store, val : val} allocglobal(s, globaltype, val) = (s[GLOBAL_store =.. [gi]], |s.GLOBAL_store|)
    -- if (gi = {TYPE globaltype, VALUE val})

;; 9-module.watsup:29.1-29.67
rec {

;; 9-module.watsup:29.1-29.67
def allocglobals : (store, globaltype*, val*) -> (store, globaladdr*)
  ;; 9-module.watsup:30.1-30.54
  def {s : store} allocglobals(s, [], []) = (s, [])
  ;; 9-module.watsup:31.1-33.62
  def {ga : globaladdr, ga'* : globaladdr*, globaltype : globaltype, globaltype'* : globaltype*, s : store, s_1 : store, s_2 : store, val : val, val'* : val*} allocglobals(s, [globaltype] :: globaltype'*{globaltype'}, [val] :: val'*{val'}) = (s_2, [ga] :: ga'*{ga'})
    -- if ((s_1, ga) = $allocglobal(s, globaltype, val))
    -- if ((s_2, ga'*{ga'}) = $allocglobals(s_1, globaltype'*{globaltype'}, val'*{val'}))
}

;; 9-module.watsup:35.1-35.60
def alloctable : (store, tabletype, ref) -> (store, tableaddr)
  ;; 9-module.watsup:36.1-37.49
  def {i : nat, j : nat, ref : ref, rt : reftype, s : store, ti : tableinst} alloctable(s, `%%`(`[%..%]`(i, j), rt), ref) = (s[TABLE_store =.. [ti]], |s.TABLE_store|)
    -- if (ti = {TYPE `%%`(`[%..%]`(i, j), rt), ELEM ref^i{}})

;; 9-module.watsup:39.1-39.64
rec {

;; 9-module.watsup:39.1-39.64
def alloctables : (store, tabletype*, ref*) -> (store, tableaddr*)
  ;; 9-module.watsup:40.1-40.53
  def {s : store} alloctables(s, [], []) = (s, [])
  ;; 9-module.watsup:41.1-43.60
  def {ref : ref, ref'* : ref*, s : store, s_1 : store, s_2 : store, ta : tableaddr, ta'* : tableaddr*, tabletype : tabletype, tabletype'* : tabletype*} alloctables(s, [tabletype] :: tabletype'*{tabletype'}, [ref] :: ref'*{ref'}) = (s_2, [ta] :: ta'*{ta'})
    -- if ((s_1, ta) = $alloctable(s, tabletype, ref))
    -- if ((s_2, ta'*{ta'}) = $alloctables(s_1, tabletype'*{tabletype'}, ref'*{ref'}))
}

;; 9-module.watsup:45.1-45.49
def allocmem : (store, memtype) -> (store, memaddr)
  ;; 9-module.watsup:46.1-47.62
  def {i : nat, j : nat, mi : meminst, s : store} allocmem(s, `%I8`(`[%..%]`(i, j))) = (s[MEM_store =.. [mi]], |s.MEM_store|)
    -- if (mi = {TYPE `%I8`(`[%..%]`(i, j)), DATA 0^((i * 64) * $Ki){}})

;; 9-module.watsup:49.1-49.52
rec {

;; 9-module.watsup:49.1-49.52
def allocmems : (store, memtype*) -> (store, memaddr*)
  ;; 9-module.watsup:50.1-50.42
  def {s : store} allocmems(s, []) = (s, [])
  ;; 9-module.watsup:51.1-53.49
  def {ma : memaddr, ma'* : memaddr*, memtype : memtype, memtype'* : memtype*, s : store, s_1 : store, s_2 : store} allocmems(s, [memtype] :: memtype'*{memtype'}) = (s_2, [ma] :: ma'*{ma'})
    -- if ((s_1, ma) = $allocmem(s, memtype))
    -- if ((s_2, ma'*{ma'}) = $allocmems(s_1, memtype'*{memtype'}))
}

;; 9-module.watsup:55.1-55.57
def allocelem : (store, reftype, ref*) -> (store, elemaddr)
  ;; 9-module.watsup:56.1-57.36
  def {ei : eleminst, ref* : ref*, rt : reftype, s : store} allocelem(s, rt, ref*{ref}) = (s[ELEM_store =.. [ei]], |s.ELEM_store|)
    -- if (ei = {TYPE rt, ELEM ref*{ref}})

;; 9-module.watsup:59.1-59.63
rec {

;; 9-module.watsup:59.1-59.63
def allocelems : (store, reftype*, ref**) -> (store, elemaddr*)
  ;; 9-module.watsup:60.1-60.52
  def {s : store} allocelems(s, [], []) = (s, [])
  ;; 9-module.watsup:61.1-63.55
  def {ea : elemaddr, ea'* : elemaddr*, ref* : ref*, ref'** : ref**, rt : reftype, rt'* : reftype*, s : store, s_1 : store, s_2 : store} allocelems(s, [rt] :: rt'*{rt'}, [ref*{ref}] :: ref'*{ref'}*{ref'}) = (s_2, [ea] :: ea'*{ea'})
    -- if ((s_1, ea) = $allocelem(s, rt, ref*{ref}))
    -- if ((s_2, ea'*{ea'}) = $allocelems(s_2, rt'*{rt'}, ref'*{ref'}*{ref'}))
}

;; 9-module.watsup:65.1-65.49
def allocdata : (store, byte*) -> (store, dataaddr)
  ;; 9-module.watsup:66.1-67.28
  def {byte* : byte*, di : datainst, s : store} allocdata(s, byte*{byte}) = (s[DATA_store =.. [di]], |s.DATA_store|)
    -- if (di = {DATA byte*{byte}})

;; 9-module.watsup:69.1-69.54
rec {

;; 9-module.watsup:69.1-69.54
def allocdatas : (store, byte**) -> (store, dataaddr*)
  ;; 9-module.watsup:70.1-70.43
  def {s : store} allocdatas(s, []) = (s, [])
  ;; 9-module.watsup:71.1-73.50
  def {byte* : byte*, byte'** : byte**, da : dataaddr, da'* : dataaddr*, s : store, s_1 : store, s_2 : store} allocdatas(s, [byte*{byte}] :: byte'*{byte'}*{byte'}) = (s_2, [da] :: da'*{da'})
    -- if ((s_1, da) = $allocdata(s, byte*{byte}))
    -- if ((s_2, da'*{da'}) = $allocdatas(s_1, byte'*{byte'}*{byte'}))
}

;; 9-module.watsup:78.1-78.83
def instexport : (funcaddr*, globaladdr*, tableaddr*, memaddr*, export) -> exportinst
  ;; 9-module.watsup:79.1-79.95
  def {fa* : funcaddr*, ga* : globaladdr*, ma* : memaddr*, name : name, ta* : tableaddr*, x : idx} instexport(fa*{fa}, ga*{ga}, ta*{ta}, ma*{ma}, EXPORT(name, FUNC_externuse(x))) = {NAME name, VALUE FUNC_externval(fa*{fa}[x])}
  ;; 9-module.watsup:80.1-80.99
  def {fa* : funcaddr*, ga* : globaladdr*, ma* : memaddr*, name : name, ta* : tableaddr*, x : idx} instexport(fa*{fa}, ga*{ga}, ta*{ta}, ma*{ma}, EXPORT(name, GLOBAL_externuse(x))) = {NAME name, VALUE GLOBAL_externval(ga*{ga}[x])}
  ;; 9-module.watsup:81.1-81.97
  def {fa* : funcaddr*, ga* : globaladdr*, ma* : memaddr*, name : name, ta* : tableaddr*, x : idx} instexport(fa*{fa}, ga*{ga}, ta*{ta}, ma*{ma}, EXPORT(name, TABLE_externuse(x))) = {NAME name, VALUE TABLE_externval(ta*{ta}[x])}
  ;; 9-module.watsup:82.1-82.93
  def {fa* : funcaddr*, ga* : globaladdr*, ma* : memaddr*, name : name, ta* : tableaddr*, x : idx} instexport(fa*{fa}, ga*{ga}, ta*{ta}, ma*{ma}, EXPORT(name, MEM_externuse(x))) = {NAME name, VALUE MEM_externval(ma*{ma}[x])}

;; 9-module.watsup:85.1-85.87
def allocmodule : (store, module, externval*, val*, ref*, ref**) -> (store, moduleinst)
  ;; 9-module.watsup:86.1-126.51
  def {byte*^n_d : byte*^n_d, da* : dataaddr*, datamode?^n_d : datamode?^n_d, dt* : deftype*, ea* : elemaddr*, elemmode?^n_e : elemmode?^n_e, export* : export*, expr_e*^n_e : expr*^n_e, expr_g^n_g : expr^n_g, expr_t^n_t : expr^n_t, externval* : externval*, fa* : funcaddr*, fa_ex* : funcaddr*, func^n_f : func^n_f, ga* : globaladdr*, ga_ex* : globaladdr*, globaltype^n_g : globaltype^n_g, i_d^n_d : nat^n_d, i_e^n_e : nat^n_e, i_f^n_f : nat^n_f, i_g^n_g : nat^n_g, i_m^n_m : nat^n_m, i_t^n_t : nat^n_t, import* : import*, ma* : memaddr*, ma_ex* : memaddr*, memtype^n_m : memtype^n_m, mm : moduleinst, module : module, n_d : n, n_e : n, n_f : n, n_g : n, n_m : n, n_t : n, rectype* : rectype*, ref_e** : ref**, ref_t* : ref*, reftype^n_e : reftype^n_e, s : store, s_1 : store, s_2 : store, s_3 : store, s_4 : store, s_5 : store, s_6 : store, start? : start?, ta* : tableaddr*, ta_ex* : tableaddr*, tabletype^n_t : tabletype^n_t, val_g* : val*, xi* : exportinst*} allocmodule(s, module, externval*{externval}, val_g*{val_g}, ref_t*{ref_t}, ref_e*{ref_e}*{ref_e}) = (s_6, mm)
    -- if (module = `MODULE%*%*%*%*%*%*%*%*%?%*`(TYPE(rectype)*{rectype}, import*{import}, func^n_f{func}, GLOBAL(globaltype, expr_g)^n_g{expr_g globaltype}, TABLE(tabletype, expr_t)^n_t{expr_t tabletype}, MEMORY(memtype)^n_m{memtype}, `ELEM%%*%?`(reftype, expr_e*{expr_e}, elemmode?{elemmode})^n_e{elemmode expr_e reftype}, `DATA%*%?`(byte*{byte}, datamode?{datamode})^n_d{byte datamode}, start?{start}, export*{export}))
    -- if (fa_ex*{fa_ex} = $funcsxv(externval*{externval}))
    -- if (ga_ex*{ga_ex} = $globalsxv(externval*{externval}))
    -- if (ta_ex*{ta_ex} = $tablesxv(externval*{externval}))
    -- if (ma_ex*{ma_ex} = $memsxv(externval*{externval}))
    -- if (fa*{fa} = (|s.FUNC_store| + i_f)^(i_f<n_f){i_f})
    -- if (ga*{ga} = (|s.GLOBAL_store| + i_g)^(i_g<n_g){i_g})
    -- if (ta*{ta} = (|s.TABLE_store| + i_t)^(i_t<n_t){i_t})
    -- if (ma*{ma} = (|s.MEM_store| + i_m)^(i_m<n_m){i_m})
    -- if (ea*{ea} = (|s.ELEM_store| + i_e)^(i_e<n_e){i_e})
    -- if (da*{da} = (|s.DATA_store| + i_d)^(i_d<n_d){i_d})
    -- if (xi*{xi} = $instexport(fa_ex*{fa_ex} :: fa*{fa}, ga_ex*{ga_ex} :: ga*{ga}, ta_ex*{ta_ex} :: ta*{ta}, ma_ex*{ma_ex} :: ma*{ma}, export)*{export})
    -- if (mm = {TYPE dt*{dt}, FUNC fa_ex*{fa_ex} :: fa*{fa}, GLOBAL ga_ex*{ga_ex} :: ga*{ga}, TABLE ta_ex*{ta_ex} :: ta*{ta}, MEM ma_ex*{ma_ex} :: ma*{ma}, ELEM ea*{ea}, DATA da*{da}, EXPORT xi*{xi}})
    -- if (dt*{dt} = $alloctypes(rectype*{rectype}))
    -- if ((s_1, fa*{fa}) = $allocfuncs(s, mm, func^n_f{func}))
    -- if ((s_2, ga*{ga}) = $allocglobals(s_1, globaltype^n_g{globaltype}, val_g*{val_g}))
    -- if ((s_3, ta*{ta}) = $alloctables(s_2, tabletype^n_t{tabletype}, ref_t*{ref_t}))
    -- if ((s_4, ma*{ma}) = $allocmems(s_3, memtype^n_m{memtype}))
    -- if ((s_5, ea*{ea}) = $allocelems(s_4, reftype^n_e{reftype}, ref_e*{ref_e}*{ref_e}))
    -- if ((s_6, da*{da}) = $allocdatas(s_5, byte*{byte}^n_d{byte}))

;; 9-module.watsup:133.1-133.38
rec {

;; 9-module.watsup:133.1-133.38
def concat_instr : instr** -> instr*
  ;; 9-module.watsup:134.1-134.37
  def concat_instr([]) = []
  ;; 9-module.watsup:135.1-135.74
  def {instr* : instr*, instr'** : instr**} concat_instr([instr*{instr}] :: instr'*{instr'}*{instr'}) = instr*{instr} :: $concat_instr(instr'*{instr'}*{instr'})
}

;; 9-module.watsup:137.1-137.33
def runelem : (elem, idx) -> instr*
  ;; 9-module.watsup:138.1-138.46
  def {expr* : expr*, reftype : reftype, y : idx} runelem(`ELEM%%*%?`(reftype, expr*{expr}, ?()), y) = []
  ;; 9-module.watsup:139.1-139.62
  def {expr* : expr*, reftype : reftype, y : idx} runelem(`ELEM%%*%?`(reftype, expr*{expr}, ?(DECLARE_elemmode)), y) = [ELEM.DROP_instr(y)]
  ;; 9-module.watsup:140.1-141.77
  def {expr* : expr*, instr* : instr*, reftype : reftype, x : idx, y : idx} runelem(`ELEM%%*%?`(reftype, expr*{expr}, ?(TABLE_elemmode(x, instr*{instr}))), y) = instr*{instr} :: [CONST_instr(I32_numtype, 0) CONST_instr(I32_numtype, |expr*{expr}|) TABLE.INIT_instr(x, y) ELEM.DROP_instr(y)]

;; 9-module.watsup:143.1-143.33
def rundata : (data, idx) -> instr*
  ;; 9-module.watsup:144.1-144.38
  def {byte* : byte*, y : idx} rundata(`DATA%*%?`(byte*{byte}, ?()), y) = []
  ;; 9-module.watsup:145.1-146.78
  def {byte* : byte*, instr* : instr*, x : idx, y : idx} rundata(`DATA%*%?`(byte*{byte}, ?(MEMORY_datamode(x, instr*{instr}))), y) = instr*{instr} :: [CONST_instr(I32_numtype, 0) CONST_instr(I32_numtype, |byte*{byte}|) MEMORY.INIT_instr(x, y) DATA.DROP_instr(y)]

;; 9-module.watsup:148.1-148.53
def instantiate : (store, module, externval*) -> config
  ;; 9-module.watsup:149.1-174.64
  def {data* : data*, elem* : elem*, elemmode?* : elemmode?*, export* : export*, expr_e** : expr**, expr_g* : expr*, expr_t* : expr*, externval* : externval*, f : frame, func^n_func : func^n_func, global* : global*, globaltype* : globaltype*, i^n_e : nat^n_e, i_func^n_func : nat^n_func, import* : import*, instr_d* : instr*, instr_e* : instr*, j^n_d : nat^n_d, mem* : mem*, mm : moduleinst, mm_init : moduleinst, module : module, n_d : n, n_e : n, n_func : n, ref_e** : ref**, ref_t* : ref*, reftype* : reftype*, s : store, s' : store, start? : start?, table* : table*, tabletype* : tabletype*, type* : type*, val_g* : val*, x? : idx?, z : state} instantiate(s, module, externval*{externval}) = `%;%*`(`%;%`(s', f), (instr_e <: admininstr)*{instr_e} :: (instr_d <: admininstr)*{instr_d} :: CALL_admininstr(x)?{x})
    -- if (module = `MODULE%*%*%*%*%*%*%*%*%?%*`(type*{type}, import*{import}, func^n_func{func}, global*{global}, table*{table}, mem*{mem}, elem*{elem}, data*{data}, start?{start}, export*{export}))
    -- if (global*{global} = GLOBAL(globaltype, expr_g)*{expr_g globaltype})
    -- if (table*{table} = TABLE(tabletype, expr_t)*{expr_t tabletype})
    -- if (elem*{elem} = `ELEM%%*%?`(reftype, expr_e*{expr_e}, elemmode?{elemmode})*{elemmode expr_e reftype})
    -- if (start?{start} = START(x)?{x})
    -- if (n_e = |elem*{elem}|)
    -- if (n_d = |data*{data}|)
    -- if (mm_init = {TYPE mm.TYPE_moduleinst, FUNC $funcsxv(externval*{externval}) :: (|s.FUNC_store| + i_func)^(i_func<n_func){i_func}, GLOBAL $globalsxv(externval*{externval}), TABLE [], MEM [], ELEM [], DATA [], EXPORT []})
    -- if (z = `%;%`(s, {LOCAL [], MODULE mm_init}))
    -- (Eval_expr: `%;%~>*%;%*`(z, expr_g, z, [val_g]))*{expr_g val_g}
    -- (Eval_expr: `%;%~>*%;%*`(z, expr_t, z, [(ref_t <: val)]))*{expr_t ref_t}
    -- (Eval_expr: `%;%~>*%;%*`(z, expr_e, z, [(ref_e <: val)]))*{expr_e ref_e}*{expr_e ref_e}
    -- if ((s', mm) = $allocmodule(s, module, externval*{externval}, val_g*{val_g}, ref_t*{ref_t}, ref_e*{ref_e}*{ref_e}))
    -- if (f = {LOCAL [], MODULE mm})
    -- if (instr_e*{instr_e} = $concat_instr($runelem(elem*{elem}[i], i)^(i<n_e){i}))
    -- if (instr_d*{instr_d} = $concat_instr($rundata(data*{data}[j], j)^(j<n_d){j}))

;; 9-module.watsup:181.1-181.44
def invoke : (store, funcaddr, val*) -> config
  ;; 9-module.watsup:182.1-195.53
  def {expr : expr, f : frame, fa : funcaddr, local* : local*, mm : moduleinst, n : n, s : store, t_1^n : valtype^n, t_2* : valtype*, val^n : val^n, x : idx} invoke(s, fa, val^n{val}) = `%;%*`(`%;%`(s, f), (val <: admininstr)^n{val} :: [REF.FUNC_ADDR_admininstr(fa) CALL_REF_admininstr(0)])
    -- if (mm = {TYPE [s.FUNC_store[fa].TYPE_funcinst], FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], EXPORT []})
    -- if (f = {LOCAL [], MODULE mm})
    -- if ($funcinst(`%;%`(s, f))[fa].CODE_funcinst = `FUNC%%*%`(x, local*{local}, expr))
    -- Expand: `%~~%`(s.FUNC_store[fa].TYPE_funcinst, FUNC_comptype(`%->%`(t_1^n{t_1}, t_2*{t_2})))

== IL Validation...
== Latex Generation...
$$
\begin{array}{@{}lrrl@{}}
& {\mathit{n}} &::=& {\mathit{nat}} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{Ki}} &=& 1024 &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{min}}(0,\, {\mathit{j}}) &=& 0 &  \\
{\mathrm{min}}({\mathit{i}},\, 0) &=& 0 &  \\
{\mathrm{min}}({\mathit{i}} + 1,\, {\mathit{j}} + 1) &=& {\mathrm{min}}({\mathit{i}},\, {\mathit{j}}) &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{test}}_{{\mathit{sub}}_{{\mathsf{atom}}_{{22}}}}({\mathit{n}}_{{3}_{{\mathsf{atom}}_{{\mathit{y}}}}}) &=& 0 &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{{\mathrm{curried}}}_{{\mathit{n}}_{{1}}}({\mathit{n}}_{{2}}) &=& {\mathit{n}}_{{1}} + {\mathit{n}}_{{2}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lrrl@{}}
& {\mathit{testfuse}} &::=& {\mathsf{ab}}_{{\mathit{nat}}}\,\,{\mathit{nat}}~{\mathit{nat}} \\ &&|&
{\mathsf{cd}}_{{\mathit{nat}}}\,{\mathit{nat}}~{\mathit{nat}} \\ &&|&
{\mathsf{ef\_}}{{\mathit{nat}}}~{\mathit{nat}}~{\mathit{nat}} \\ &&|&
{{\mathsf{gh}}_{{\mathit{nat}}}}{{\mathit{nat}}}~{\mathit{nat}} \\ &&|&
{{\mathsf{ij}}_{{\mathit{nat}}}}{{\mathit{nat}}}~{\mathit{nat}} \\ &&|&
{\mathsf{kl\_ab}}{{\mathit{nat}}}~{\mathit{nat}}~{\mathit{nat}} \\ &&|&
{\mathsf{mn\_}}{\mathsf{ab}}~{\mathit{nat}}~{\mathit{nat}}~{\mathit{nat}} \\ &&|&
{{\mathsf{op\_}}{\mathsf{ab}}}{{\mathit{nat}}}~{\mathit{nat}}~{\mathit{nat}} \\ &&|&
{{\mathsf{qr}}_{{\mathit{nat}}}}{\mathsf{ab}}~{\mathit{nat}}~{\mathit{nat}} \\
\mbox{(name)} & {\mathit{name}} &::=& {\mathit{text}} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
\mbox{(byte)} & {\mathit{byte}} &::=& {\mathit{nat}} \\
\mbox{(31-bit integer)} & {\mathit{i{\scriptstyle31}}} &::=& {\mathit{nat}} \\
\mbox{(32-bit integer)} & {\mathit{i{\scriptstyle32}}} &::=& {\mathit{nat}} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
\mbox{(index)} & {\mathit{idx}} &::=& {\mathit{i{\scriptstyle32}}} \\
\mbox{(type index)} & {\mathit{typeidx}} &::=& {\mathit{idx}} \\
\mbox{(function index)} & {\mathit{funcidx}} &::=& {\mathit{idx}} \\
\mbox{(global index)} & {\mathit{globalidx}} &::=& {\mathit{idx}} \\
\mbox{(table index)} & {\mathit{tableidx}} &::=& {\mathit{idx}} \\
\mbox{(memory index)} & {\mathit{memidx}} &::=& {\mathit{idx}} \\
\mbox{(elem index)} & {\mathit{elemidx}} &::=& {\mathit{idx}} \\
\mbox{(data index)} & {\mathit{dataidx}} &::=& {\mathit{idx}} \\
\mbox{(label index)} & {\mathit{labelidx}} &::=& {\mathit{idx}} \\
\mbox{(local index)} & {\mathit{localidx}} &::=& {\mathit{idx}} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
& {\mathit{nul}} &::=& {\mathsf{null}^?} \\
\mbox{(number type)} & {\mathit{numtype}} &::=& \mathsf{i{\scriptstyle32}} ~|~ \mathsf{i{\scriptstyle64}} ~|~ \mathsf{f{\scriptstyle32}} ~|~ \mathsf{f{\scriptstyle64}} \\
\mbox{(vector type)} & {\mathit{vectype}} &::=& \mathsf{v{\scriptstyle128}} \\
\mbox{(abstract heap type)} & {\mathit{absheaptype}} &::=& \mathsf{any} ~|~ \mathsf{eq} ~|~ \mathsf{i{\scriptstyle31}} ~|~ \mathsf{struct} ~|~ \mathsf{array} ~|~ \mathsf{none} \\ &&|&
\mathsf{func} ~|~ \mathsf{nofunc} \\ &&|&
\mathsf{extern} ~|~ \mathsf{noextern} \\ &&|&
\mathsf{bot} \\
\mbox{(heap type)} & {\mathit{heaptype}} &::=& {\mathit{absheaptype}} \\ &&|&
{\mathit{typeidx}} \\ &&|&
... \\
\mbox{(reference type)} & {\mathit{reftype}} &::=& \mathsf{ref}~{\mathit{nul}}~{\mathit{heaptype}} \\
\mbox{(value type)} & {\mathit{valtype}} &::=& {\mathit{numtype}} ~|~ {\mathit{vectype}} ~|~ {\mathit{reftype}} ~|~ \mathsf{bot} \\
& {{\mathsf{i}}{{\mathit{n}}}} &::=& \mathsf{i{\scriptstyle32}} ~|~ \mathsf{i{\scriptstyle64}} \\
& {{\mathsf{f}}{{\mathit{n}}}} &::=& \mathsf{f{\scriptstyle32}} ~|~ \mathsf{f{\scriptstyle64}} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
\mbox{(result type)} & {\mathit{resulttype}} &::=& {{\mathit{valtype}}^\ast} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
& {\mathit{mut}} &::=& {\mathsf{mut}^?} \\
& {\mathit{fin}} &::=& {\mathsf{final}^?} \\
\mbox{(packed type)} & {\mathit{packedtype}} &::=& \mathsf{i{\scriptstyle8}} ~|~ \mathsf{i{\scriptstyle16}} \\
\mbox{(storage type)} & {\mathit{storagetype}} &::=& {\mathit{valtype}} ~|~ {\mathit{packedtype}} \\
\mbox{(field type)} & {\mathit{fieldtype}} &::=& {\mathit{mut}}~{\mathit{storagetype}} \\
\mbox{(function type)} & {\mathit{functype}} &::=& {\mathit{resulttype}} \rightarrow {\mathit{resulttype}} \\
\mbox{(composite type)} & {\mathit{comptype}} &::=& \mathsf{struct}~{{\mathit{fieldtype}}^\ast} \\ &&|&
\mathsf{array}~{\mathit{fieldtype}} \\ &&|&
\mathsf{func}~{\mathit{functype}} \\
\mbox{(sub type)} & {\mathit{subtype}} &::=& \mathsf{sub}~{\mathit{fin}}~{{\mathit{typeidx}}^\ast}~{\mathit{comptype}} ~|~ \mathsf{sub}~{\mathit{fin}}~{{\mathit{heaptype}}^\ast}~{\mathit{comptype}} \\
\mbox{(recursive type)} & {\mathit{rectype}} &::=& \mathsf{rec}~{{\mathit{subtype}}^\ast} \\
\mbox{(defined type)} & {\mathit{deftype}} &::=& {\mathit{rectype}} . {\mathit{nat}} \\
\mbox{(heap type)} & {\mathit{heaptype}} &::=& ... ~|~ {\mathit{deftype}} \\ &&|&
 \\ &&|&
\mathsf{rec}~{\mathit{nat}} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
\mbox{(limits)} & {\mathit{limits}} &::=& [{\mathit{i{\scriptstyle32}}} .. {\mathit{i{\scriptstyle32}}}] \\
\mbox{(global type)} & {\mathit{globaltype}} &::=& {\mathit{mut}}~{\mathit{valtype}} \\
\mbox{(table type)} & {\mathit{tabletype}} &::=& {\mathit{limits}}~{\mathit{reftype}} \\
\mbox{(memory type)} & {\mathit{memtype}} &::=& {\mathit{limits}}~\mathsf{i{\scriptstyle8}} \\
\mbox{(element type)} & {\mathit{elemtype}} &::=& {\mathit{reftype}} \\
\mbox{(data type)} & {\mathit{datatype}} &::=& \mathsf{ok} \\
\mbox{(external type)} & {\mathit{externtype}} &::=& \mathsf{func}~{\mathit{deftype}} ~|~ \mathsf{global}~{\mathit{globaltype}} ~|~ \mathsf{table}~{\mathit{tabletype}} ~|~ \mathsf{mem}~{\mathit{memtype}} \\
\end{array}
$$

\vspace{1ex}

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
\mbox{(signedness)} & {\mathit{sx}} &::=& \mathsf{u} ~|~ \mathsf{s} \\
& {{\mathit{unop}}_{{\mathsf{ixx}}}} &::=& \mathsf{clz} ~|~ \mathsf{ctz} ~|~ \mathsf{popcnt} \\
& {{\mathit{unop}}_{{\mathsf{fxx}}}} &::=& \mathsf{abs} ~|~ \mathsf{neg} ~|~ \mathsf{sqrt} ~|~ \mathsf{ceil} ~|~ \mathsf{floor} ~|~ \mathsf{trunc} ~|~ \mathsf{nearest} \\
& {{\mathit{binop}}_{{\mathsf{ixx}}}} &::=& \mathsf{add} ~|~ \mathsf{sub} ~|~ \mathsf{mul} ~|~ {\mathsf{div\_}}{{\mathit{sx}}} ~|~ {\mathsf{rem\_}}{{\mathit{sx}}} \\ &&|&
\mathsf{and} ~|~ \mathsf{or} ~|~ \mathsf{xor} ~|~ \mathsf{shl} ~|~ {\mathsf{shr\_}}{{\mathit{sx}}} ~|~ \mathsf{rotl} ~|~ \mathsf{rotr} \\
& {{\mathit{binop}}_{{\mathsf{fxx}}}} &::=& \mathsf{add} ~|~ \mathsf{sub} ~|~ \mathsf{mul} ~|~ \mathsf{div} ~|~ \mathsf{min} ~|~ \mathsf{max} ~|~ \mathsf{copysign} \\
& {{\mathit{testop}}_{{\mathsf{ixx}}}} &::=& \mathsf{eqz} \\
& {{\mathit{testop}}_{{\mathsf{fxx}}}} &::=&  \\
& {{\mathit{relop}}_{{\mathsf{ixx}}}} &::=& \mathsf{eq} ~|~ \mathsf{ne} ~|~ {\mathsf{lt\_}}{{\mathit{sx}}} ~|~ {\mathsf{gt\_}}{{\mathit{sx}}} ~|~ {\mathsf{le\_}}{{\mathit{sx}}} ~|~ {\mathsf{ge\_}}{{\mathit{sx}}} \\
& {{\mathit{refop}}_{{\mathsf{fxx}}}} &::=& \mathsf{eq} ~|~ \mathsf{ne} ~|~ \mathsf{lt} ~|~ \mathsf{gt} ~|~ \mathsf{le} ~|~ \mathsf{ge} \\
& {\mathit{unop}}_{{\mathit{numtype}}} &::=& {{\mathit{unop}}_{{\mathsf{ixx}}}} ~|~ {{\mathit{unop}}_{{\mathsf{fxx}}}} \\
& {\mathit{binop}}_{{\mathit{numtype}}} &::=& {{\mathit{binop}}_{{\mathsf{ixx}}}} ~|~ {{\mathit{binop}}_{{\mathsf{fxx}}}} \\
& {\mathit{testop}}_{{\mathit{numtype}}} &::=& {{\mathit{testop}}_{{\mathsf{ixx}}}} ~|~ {{\mathit{testop}}_{{\mathsf{fxx}}}} \\
& {\mathit{relop}}_{{\mathit{numtype}}} &::=& {{\mathit{relop}}_{{\mathsf{ixx}}}} ~|~ {{\mathit{refop}}_{{\mathsf{fxx}}}} \\
& {\mathit{cvtop}} &::=& \mathsf{convert} ~|~ \mathsf{reinterpret} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
& {\mathit{c}}_{{\mathit{numtype}}} &::=& {\mathit{nat}} \\
& {\mathit{c}}_{{\mathit{vectype}}} &::=& {\mathit{nat}} \\
\end{array}
$$

$$
\begin{array}{@{}lrrl@{}}
\mbox{(block type)} & {\mathit{blocktype}} &::=& {\mathit{functype}} \\
\end{array}
$$

$$
\begin{array}{@{}lrrl@{}}
\mbox{(instruction)} & {\mathit{instr}} &::=& \mathsf{unreachable} \\ &&|&
\mathsf{nop} \\ &&|&
\mathsf{drop} \\ &&|&
\mathsf{select}~{{\mathit{valtype}}^?} \\ &&|&
\mathsf{block}~{\mathit{blocktype}}~{{\mathit{instr}}^\ast} \\ &&|&
\mathsf{loop}~{\mathit{blocktype}}~{{\mathit{instr}}^\ast} \\ &&|&
\mathsf{if}~{\mathit{blocktype}}~{{\mathit{instr}}^\ast}~\mathsf{else}~{{\mathit{instr}}^\ast} \\ &&|&
\mathsf{br}~{\mathit{labelidx}} \\ &&|&
\mathsf{br\_if}~{\mathit{labelidx}} \\ &&|&
\mathsf{br\_table}~{{\mathit{labelidx}}^\ast}~{\mathit{labelidx}} \\ &&|&
\mathsf{br\_on\_null}~{\mathit{labelidx}} \\ &&|&
\mathsf{br\_on\_non\_null}~{\mathit{labelidx}} \\ &&|&
\mathsf{br\_on\_cast}~{\mathit{labelidx}}~{\mathit{reftype}}~{\mathit{reftype}} \\ &&|&
\mathsf{br\_on\_cast\_fail}~{\mathit{labelidx}}~{\mathit{reftype}}~{\mathit{reftype}} \\ &&|&
\mathsf{call}~{\mathit{funcidx}} \\ &&|&
\mathsf{call\_ref}~{\mathit{typeidx}} \\ &&|&
\mathsf{call\_indirect}~{\mathit{tableidx}}~{\mathit{typeidx}} \\ &&|&
\mathsf{return} \\ &&|&
\mathsf{return\_call}~{\mathit{funcidx}} \\ &&|&
\mathsf{return\_call\_ref}~{\mathit{typeidx}} \\ &&|&
\mathsf{return\_call\_indirect}~{\mathit{tableidx}}~{\mathit{typeidx}} \\ &&|&
{\mathit{numtype}}.\mathsf{const}~{\mathit{c}}_{{\mathit{numtype}}} \\ &&|&
{\mathit{numtype}} . {\mathit{unop}}_{{\mathit{numtype}}} \\ &&|&
{\mathit{numtype}} . {\mathit{binop}}_{{\mathit{numtype}}} \\ &&|&
{\mathit{numtype}} . {\mathit{testop}}_{{\mathit{numtype}}} \\ &&|&
{\mathit{numtype}} . {\mathit{relop}}_{{\mathit{numtype}}} \\ &&|&
{{\mathit{numtype}}.\mathsf{extend}}{{\mathit{n}}} \\ &&|&
{\mathit{numtype}} . {{{{{\mathit{cvtop}}}{\mathsf{\_}}}{{\mathit{numtype}}}}{\mathsf{\_}}}{{{\mathit{sx}}^?}} \\ &&|&
\mathsf{ref.null}~{\mathit{heaptype}} \\ &&|&
\mathsf{ref.i{\scriptstyle31}} \\ &&|&
\mathsf{ref.func}~{\mathit{funcidx}} \\ &&|&
\mathsf{ref.is\_null} \\ &&|&
\mathsf{ref.as\_non\_null} \\ &&|&
\mathsf{ref.eq} \\ &&|&
\mathsf{ref.test}~{\mathit{reftype}} \\ &&|&
\mathsf{ref.cast}~{\mathit{reftype}} \\ &&|&
{{\mathsf{i{\scriptstyle31}.get}}{\mathsf{\_}}}{{\mathit{sx}}} \\ &&|&
\mathsf{struct.new}~{\mathit{typeidx}} \\ &&|&
\mathsf{struct.new\_default}~{\mathit{typeidx}} \\ &&|&
{{\mathsf{struct.get}}{\mathsf{\_}}}{{{\mathit{sx}}^?}}~{\mathit{typeidx}}~{\mathit{i{\scriptstyle32}}} \\ &&|&
\mathsf{struct.set}~{\mathit{typeidx}}~{\mathit{i{\scriptstyle32}}} \\ &&|&
\mathsf{array.new}~{\mathit{typeidx}} \\ &&|&
\mathsf{array.new\_default}~{\mathit{typeidx}} \\ &&|&
\mathsf{array.new\_fixed}~{\mathit{typeidx}}~{\mathit{nat}} \\ &&|&
\mathsf{array.new\_data}~{\mathit{typeidx}}~{\mathit{dataidx}} \\ &&|&
\mathsf{array.new\_elem}~{\mathit{typeidx}}~{\mathit{elemidx}} \\ &&|&
{{\mathsf{array.get}}{\mathsf{\_}}}{{{\mathit{sx}}^?}}~{\mathit{typeidx}} \\ &&|&
\mathsf{array.set}~{\mathit{typeidx}} \\ &&|&
\mathsf{array.len} \\ &&|&
\mathsf{array.fill}~{\mathit{typeidx}} \\ &&|&
\mathsf{array.copy}~{\mathit{typeidx}}~{\mathit{typeidx}} \\ &&|&
\mathsf{array.init\_data}~{\mathit{typeidx}}~{\mathit{dataidx}} \\ &&|&
\mathsf{array.init\_elem}~{\mathit{typeidx}}~{\mathit{elemidx}} \\ &&|&
\mathsf{extern.internalize} \\ &&|&
\mathsf{extern.externalize} \\ &&|&
\mathsf{local.get}~{\mathit{localidx}} \\ &&|&
\mathsf{local.set}~{\mathit{localidx}} \\ &&|&
\mathsf{local.tee}~{\mathit{localidx}} \\ &&|&
\mathsf{global.get}~{\mathit{globalidx}} \\ &&|&
\mathsf{global.set}~{\mathit{globalidx}} \\ &&|&
\mathsf{table.get}~{\mathit{tableidx}} \\ &&|&
\mathsf{table.set}~{\mathit{tableidx}} \\ &&|&
\mathsf{table.size}~{\mathit{tableidx}} \\ &&|&
\mathsf{table.grow}~{\mathit{tableidx}} \\ &&|&
\mathsf{table.fill}~{\mathit{tableidx}} \\ &&|&
\mathsf{table.copy}~{\mathit{tableidx}}~{\mathit{tableidx}} \\ &&|&
\mathsf{table.init}~{\mathit{tableidx}}~{\mathit{elemidx}} \\ &&|&
\mathsf{elem.drop}~{\mathit{elemidx}} \\ &&|&
\mathsf{memory.size}~{\mathit{memidx}} \\ &&|&
\mathsf{memory.grow}~{\mathit{memidx}} \\ &&|&
\mathsf{memory.fill}~{\mathit{memidx}} \\ &&|&
\mathsf{memory.copy}~{\mathit{memidx}}~{\mathit{memidx}} \\ &&|&
\mathsf{memory.init}~{\mathit{memidx}}~{\mathit{dataidx}} \\ &&|&
\mathsf{data.drop}~{\mathit{dataidx}} \\ &&|&
{{\mathit{numtype}}.\mathsf{load}}{{({{{\mathit{n}}}{\mathsf{\_}}}{{\mathit{sx}}})^?}}~{\mathit{memidx}}~{\mathit{i{\scriptstyle32}}}~{\mathit{i{\scriptstyle32}}} \\ &&|&
{{\mathit{numtype}}.\mathsf{store}}{{{\mathit{n}}^?}}~{\mathit{memidx}}~{\mathit{i{\scriptstyle32}}}~{\mathit{i{\scriptstyle32}}} \\
\mbox{(expression)} & {\mathit{expr}} &::=& {{\mathit{instr}}^\ast} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
& {\mathit{elemmode}} &::=& \mathsf{table}~{\mathit{tableidx}}~{\mathit{expr}} ~|~ \mathsf{declare} \\
& {\mathit{datamode}} &::=& \mathsf{memory}~{\mathit{memidx}}~{\mathit{expr}} \\
\mbox{(type definition)} & {\mathit{type}} &::=& \mathsf{type}~{\mathit{rectype}} \\
\mbox{(local)} & {\mathit{local}} &::=& \mathsf{local}~{\mathit{valtype}} \\
\mbox{(function)} & {\mathit{func}} &::=& \mathsf{func}~{\mathit{typeidx}}~{{\mathit{local}}^\ast}~{\mathit{expr}} \\
\mbox{(global)} & {\mathit{global}} &::=& \mathsf{global}~{\mathit{globaltype}}~{\mathit{expr}} \\
\mbox{(table)} & {\mathit{table}} &::=& \mathsf{table}~{\mathit{tabletype}}~{\mathit{expr}} \\
\mbox{(memory)} & {\mathit{mem}} &::=& \mathsf{memory}~{\mathit{memtype}} \\
\mbox{(table segment)} & {\mathit{elem}} &::=& \mathsf{elem}~{\mathit{reftype}}~{{\mathit{expr}}^\ast}~{{\mathit{elemmode}}^?} \\
\mbox{(memory segment)} & {\mathit{data}} &::=& \mathsf{data}~{{\mathit{byte}}^\ast}~{{\mathit{datamode}}^?} \\
\mbox{(start function)} & {\mathit{start}} &::=& \mathsf{start}~{\mathit{funcidx}} \\
\mbox{(external use)} & {\mathit{externuse}} &::=& \mathsf{func}~{\mathit{funcidx}} ~|~ \mathsf{global}~{\mathit{globalidx}} ~|~ \mathsf{table}~{\mathit{tableidx}} ~|~ \mathsf{mem}~{\mathit{memidx}} \\
\mbox{(export)} & {\mathit{export}} &::=& \mathsf{export}~{\mathit{name}}~{\mathit{externuse}} \\
\mbox{(import)} & {\mathit{import}} &::=& \mathsf{import}~{\mathit{name}}~{\mathit{name}}~{\mathit{externtype}} \\
\mbox{(module)} & {\mathit{module}} &::=& \mathsf{module}~{{\mathit{type}}^\ast}~{{\mathit{import}}^\ast}~{{\mathit{func}}^\ast}~{{\mathit{global}}^\ast}~{{\mathit{table}}^\ast}~{{\mathit{mem}}^\ast}~{{\mathit{elem}}^\ast}~{{\mathit{data}}^\ast}~{{\mathit{start}}^?}~{{\mathit{export}}^\ast} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
\epsilon \setminus {{\mathit{y}}^\ast} &=& \epsilon &  \\
{\mathit{x}}_{{1}}~{{\mathit{x}}^\ast} \setminus {{\mathit{y}}^\ast} &=& {\mathrm{setminus{\scriptstyle1}}}({\mathit{x}}_{{1}},\, {{\mathit{y}}^\ast})~{{\mathit{x}}^\ast} \setminus {{\mathit{y}}^\ast} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{setminus{\scriptstyle1}}}({\mathit{x}},\, \epsilon) &=& {\mathit{x}} &  \\
{\mathrm{setminus{\scriptstyle1}}}({\mathit{x}},\, {\mathit{y}}_{{1}}~{{\mathit{y}}^\ast}) &=& \epsilon &\quad
  \mbox{if}~{\mathit{x}} = {\mathit{y}}_{{1}} \\
{\mathrm{setminus{\scriptstyle1}}}({\mathit{x}},\, {\mathit{y}}_{{1}}~{{\mathit{y}}^\ast}) &=& {\mathrm{setminus{\scriptstyle1}}}({\mathit{x}},\, {{\mathit{y}}^\ast}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{|\mathsf{i{\scriptstyle32}}|} &=& 32 &  \\
{|\mathsf{i{\scriptstyle64}}|} &=& 64 &  \\
{|\mathsf{f{\scriptstyle32}}|} &=& 32 &  \\
{|\mathsf{f{\scriptstyle64}}|} &=& 64 &  \\
{|\mathsf{v{\scriptstyle128}}|} &=& 128 &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{|\mathsf{i{\scriptstyle8}}|} &=& 8 &  \\
{|\mathsf{i{\scriptstyle16}}|} &=& 16 &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{|{\mathit{valtype}}|} &=& {|{\mathit{valtype}}|} &  \\
{|{\mathit{packedtype}}|} &=& {|{\mathit{packedtype}}|} &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{unpack}}({\mathit{valtype}}) &=& {\mathit{valtype}} &  \\
{\mathrm{unpack}}({\mathit{packedtype}}) &=& \mathsf{i{\scriptstyle32}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{unpack}}({\mathit{numtype}}) &=& {\mathit{numtype}} &  \\
{\mathrm{unpack}}({\mathit{packedtype}}) &=& \mathsf{i{\scriptstyle32}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{sx}}({\mathit{valtype}}) &=& \epsilon &  \\
{\mathrm{sx}}({\mathit{packedtype}}) &=& \mathsf{s} &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
(\mathsf{ref}~{\mathit{nul}}_{{1}}~{\mathit{ht}}_{{1}}) - (\mathsf{ref}~\mathsf{null}~{\mathit{ht}}_{{2}}) &=& (\mathsf{ref}~\epsilon~{\mathit{ht}}_{{1}}) &  \\
(\mathsf{ref}~{\mathit{nul}}_{{1}}~{\mathit{ht}}_{{1}}) - (\mathsf{ref}~\epsilon~{\mathit{ht}}_{{2}}) &=& (\mathsf{ref}~{\mathit{nul}}_{{1}}~{\mathit{ht}}_{{1}}) &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
& {\mathit{typevar}} &::=& {\mathit{typeidx}} ~|~ \mathsf{rec}~{\mathit{nat}} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathit{x}} &=& {\mathit{x}} &  \\
\end{array}
$$

\vspace{1ex}

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{{\mathit{xx}}}{[\epsilon := \epsilon]} &=& {\mathit{xx}} &  \\
{{\mathit{xx}}}{[{\mathit{xx}}_{{1}}~{{\mathit{xx}'}^\ast} := {\mathit{ht}}_{{1}}~{{\mathit{ht}'}^\ast}]} &=& {\mathit{ht}}_{{1}} &\quad
  \mbox{if}~{\mathit{xx}} = {\mathit{xx}}_{{1}} \\
{{\mathit{xx}}}{[{\mathit{xx}}_{{1}}~{{\mathit{xx}'}^\ast} := {\mathit{ht}}_{{1}}~{{\mathit{ht}'}^\ast}]} &=& {{\mathit{xx}}}{[{{\mathit{xx}'}^\ast} := {{\mathit{ht}'}^\ast}]} &\quad
  \mbox{otherwise} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{{\mathit{nt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& {\mathit{nt}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{{\mathit{vt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& {\mathit{vt}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{{\mathit{xx}'}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& {{\mathit{xx}'}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
{{\mathit{dt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& {{\mathit{dt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
{{\mathit{ht}'}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& {\mathit{ht}'} &\quad
  \mbox{otherwise} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{(\mathsf{ref}~{\mathit{nul}}~{\mathit{ht}'})}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& \mathsf{ref}~{\mathit{nul}}~{{\mathit{ht}'}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{{\mathit{nt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& {{\mathit{nt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
{{\mathit{vt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& {{\mathit{vt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
{{\mathit{rt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& {{\mathit{rt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
{\mathsf{bot}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& \mathsf{bot} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{{\mathit{pt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& {\mathit{pt}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{{\mathit{t}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& {{\mathit{t}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
{{\mathit{pt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& {{\mathit{pt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{({\mathit{mut}}~{\mathit{zt}})}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& {\mathit{mut}}~{{\mathit{zt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{(\mathsf{struct}~{{\mathit{yt}}^\ast})}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& \mathsf{struct}~{{{\mathit{yt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]}^\ast} &  \\
{(\mathsf{array}~{\mathit{yt}})}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& \mathsf{array}~{{\mathit{yt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
{(\mathsf{func}~{\mathit{ft}})}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& \mathsf{func}~{{\mathit{ft}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{(\mathsf{sub}~{\mathit{fin}}~{{\mathit{y}}^\ast}~{\mathit{ct}})}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& \mathsf{sub}~{\mathit{fin}}~{{{\mathit{y}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]}^\ast}~{{\mathit{ct}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
{(\mathsf{sub}~{\mathit{fin}}~{{\mathit{ht}'}^\ast}~{\mathit{ct}})}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& \mathsf{sub}~{\mathit{fin}}~{{{\mathit{ht}'}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]}^\ast}~{{\mathit{ct}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{(\mathsf{rec}~{{\mathit{st}}^\ast})}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& \mathsf{rec}~{{{\mathit{st}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]}^\ast} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{({\mathit{qt}} . {\mathit{i}})}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& {{\mathit{qt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} . {\mathit{i}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{({\mathit{mut}}~{\mathit{t}})}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& {\mathit{mut}}~{{\mathit{t}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{({{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast})}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& {{{\mathit{t}}_{{1}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]}^\ast} \rightarrow {{{\mathit{t}}_{{2}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]}^\ast} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{({\mathit{lim}}~\mathsf{i{\scriptstyle8}})}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& {\mathit{lim}}~\mathsf{i{\scriptstyle8}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{({\mathit{lim}}~{\mathit{rt}})}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& {\mathit{lim}}~{{\mathit{rt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{(\mathsf{func}~{\mathit{dt}})}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& \mathsf{func}~{{\mathit{dt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
{(\mathsf{global}~{\mathit{gt}})}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& \mathsf{global}~{{\mathit{gt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
{(\mathsf{table}~{\mathit{tt}})}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& \mathsf{table}~{{\mathit{tt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
{(\mathsf{mem}~{\mathit{mt}})}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &=& \mathsf{mem}~{{\mathit{mt}}}{[{{\mathit{xx}}^\ast} := {{\mathit{ht}}^\ast}]} &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{{\mathit{rt}}}{[{ := }\;{{\mathit{ht}}^{{\mathit{n}}}}]} &=& {{\mathit{rt}}}{[{{\mathit{x}}^{{\mathit{x}}<{\mathit{n}}}} := {{\mathit{ht}}^{{\mathit{n}}}}]} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{{\mathit{dt}}}{[{ := }\;{{\mathit{ht}}^{{\mathit{n}}}}]} &=& {{\mathit{dt}}}{[{{\mathit{x}}^{{\mathit{x}}<{\mathit{n}}}} := {{\mathit{ht}}^{{\mathit{n}}}}]} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\epsilon}{[{ := }\;{{\mathit{ht}}^\ast}]} &=& \epsilon &  \\
{{\mathit{dt}}_{{1}}~{{\mathit{dt}}^\ast}}{[{ := }\;{{\mathit{ht}}^\ast}]} &=& {{\mathit{dt}}_{{1}}}{[{ := }\;{{\mathit{ht}}^\ast}]}~{{{\mathit{dt}}^\ast}}{[{ := }\;{{\mathit{ht}}^\ast}]} &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{{\mathrm{roll}}}_{{\mathit{x}}}(\mathsf{rec}~{{\mathit{st}}^{{\mathit{n}}}}) &=& \mathsf{rec}~{({{\mathit{st}}}{[{({\mathit{x}} + {\mathit{i}})^{{\mathit{i}}<{\mathit{n}}}} := {(\mathsf{rec}~{\mathit{i}})^{{\mathit{i}}<{\mathit{n}}}}]})^{{\mathit{n}}}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{unroll}}(\mathsf{rec}~{{\mathit{st}}^{{\mathit{n}}}}) &=& \mathsf{rec}~{({{\mathit{st}}}{[{(\mathsf{rec}~{\mathit{i}})^{{\mathit{i}}<{\mathit{n}}}} := {({\mathit{qt}} . {\mathit{i}})^{{\mathit{i}}<{\mathit{n}}}}]})^{{\mathit{n}}}} &\quad
  \mbox{if}~{\mathit{qt}} = \mathsf{rec}~{{\mathit{st}}^{{\mathit{n}}}} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{{\mathrm{roll}}}_{{\mathit{x}}}({\mathit{qt}}) &=& {((\mathsf{rec}~{{\mathit{st}}^{{\mathit{n}}}}) . {\mathit{i}})^{{\mathit{i}}<{\mathit{n}}}} &\quad
  \mbox{if}~{{\mathrm{roll}}}_{{\mathit{x}}}({\mathit{qt}}) = \mathsf{rec}~{{\mathit{st}}^{{\mathit{n}}}} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{unroll}}({\mathit{qt}} . {\mathit{i}}) &=& {{\mathit{st}}^\ast}[{\mathit{i}}] &\quad
  \mbox{if}~{\mathrm{unroll}}({\mathit{qt}}) = \mathsf{rec}~{{\mathit{st}}^\ast} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{expand}}({\mathit{dt}}) &=& {\mathit{ct}} &\quad
  \mbox{if}~{\mathrm{unroll}}({\mathit{dt}}) = \mathsf{sub}~{\mathit{fin}}~{{\mathit{ht}}^\ast}~{\mathit{ct}} \\
\end{array}
$$

$\boxed{{\mathit{deftype}} \approx {\mathit{comptype}}}$

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize Expand}]} \quad & {\mathit{dt}} &\approx& {\mathit{ct}} &\quad
  \mbox{if}~{\mathrm{expand}}({\mathit{dt}}) = {\mathit{ct}} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{funcs}}(\epsilon) &=& \epsilon &  \\
{\mathrm{funcs}}((\mathsf{func}~{\mathit{dt}})~{{\mathit{et}}^\ast}) &=& {\mathit{dt}}~{\mathrm{funcs}}({{\mathit{et}}^\ast}) &  \\
{\mathrm{funcs}}({\mathit{externtype}}~{{\mathit{et}}^\ast}) &=& {\mathrm{funcs}}({{\mathit{et}}^\ast}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{globals}}(\epsilon) &=& \epsilon &  \\
{\mathrm{globals}}((\mathsf{global}~{\mathit{gt}})~{{\mathit{et}}^\ast}) &=& {\mathit{gt}}~{\mathrm{globals}}({{\mathit{et}}^\ast}) &  \\
{\mathrm{globals}}({\mathit{externtype}}~{{\mathit{et}}^\ast}) &=& {\mathrm{globals}}({{\mathit{et}}^\ast}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{tables}}(\epsilon) &=& \epsilon &  \\
{\mathrm{tables}}((\mathsf{table}~{\mathit{tt}})~{{\mathit{et}}^\ast}) &=& {\mathit{tt}}~{\mathrm{tables}}({{\mathit{et}}^\ast}) &  \\
{\mathrm{tables}}({\mathit{externtype}}~{{\mathit{et}}^\ast}) &=& {\mathrm{tables}}({{\mathit{et}}^\ast}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{mems}}(\epsilon) &=& \epsilon &  \\
{\mathrm{mems}}((\mathsf{mem}~{\mathit{mt}})~{{\mathit{et}}^\ast}) &=& {\mathit{mt}}~{\mathrm{mems}}({{\mathit{et}}^\ast}) &  \\
{\mathrm{mems}}({\mathit{externtype}}~{{\mathit{et}}^\ast}) &=& {\mathrm{mems}}({{\mathit{et}}^\ast}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

$$
\begin{array}{@{}lrrl@{}}
\mbox{(address)} & {\mathit{addr}} &::=& {\mathit{nat}} \\
\mbox{(function address)} & {\mathit{funcaddr}} &::=& {\mathit{addr}} \\
\mbox{(global address)} & {\mathit{globaladdr}} &::=& {\mathit{addr}} \\
\mbox{(table address)} & {\mathit{tableaddr}} &::=& {\mathit{addr}} \\
\mbox{(memory address)} & {\mathit{memaddr}} &::=& {\mathit{addr}} \\
\mbox{(elem address)} & {\mathit{elemaddr}} &::=& {\mathit{addr}} \\
\mbox{(data address)} & {\mathit{dataaddr}} &::=& {\mathit{addr}} \\
\mbox{(label address)} & {\mathit{labeladdr}} &::=& {\mathit{addr}} \\
\mbox{(host address)} & {\mathit{hostaddr}} &::=& {\mathit{addr}} \\
\mbox{(structure address)} & {\mathit{structaddr}} &::=& {\mathit{addr}} \\
\mbox{(array address)} & {\mathit{arrayaddr}} &::=& {\mathit{addr}} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
\mbox{(number)} & {\mathit{num}} &::=& {\mathit{numtype}}.\mathsf{const}~{\mathit{c}}_{{\mathit{numtype}}} \\
\mbox{(address reference)} & {\mathit{addrref}} &::=& \mathsf{ref.i{\scriptstyle31}}~{\mathit{i{\scriptstyle31}}} \\ &&|&
\mathsf{ref.struct}~{\mathit{structaddr}} \\ &&|&
\mathsf{ref.array}~{\mathit{arrayaddr}} \\ &&|&
\mathsf{ref.func}~{\mathit{funcaddr}} \\ &&|&
\mathsf{ref.host}~{\mathit{hostaddr}} \\ &&|&
\mathsf{ref.extern}~{\mathit{addrref}} \\
\mbox{(reference)} & {\mathit{ref}} &::=& {\mathit{addrref}} ~|~ \mathsf{ref.null}~{\mathit{heaptype}} \\ &&|&
 \\
\mbox{(value)} & {\mathit{val}} &::=& {\mathit{num}} ~|~ {\mathit{ref}} \\
\mbox{(result)} & {\mathit{result}} &::=& {{\mathit{val}}^\ast} ~|~ \mathsf{trap} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
\mbox{(external value)} & {\mathit{externval}} &::=& \mathsf{func}~{\mathit{funcaddr}} ~|~ \mathsf{global}~{\mathit{globaladdr}} ~|~ \mathsf{table}~{\mathit{tableaddr}} ~|~ \mathsf{mem}~{\mathit{memaddr}} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
& {\mathit{c}}_{{\mathit{packedtype}}} &::=& {\mathit{nat}} \\
\mbox{(function instance)} & {\mathit{funcinst}} &::=& \{\; \begin{array}[t]{@{}l@{}}
\mathsf{type}~{\mathit{deftype}},\; \\
  \mathsf{module}~{\mathit{moduleinst}},\; \\
  \mathsf{code}~{\mathit{func}} \;\}\end{array} \\
\mbox{(global instance)} & {\mathit{globalinst}} &::=& \{\; \begin{array}[t]{@{}l@{}}
\mathsf{type}~{\mathit{globaltype}},\; \\
  \mathsf{value}~{\mathit{val}} \;\}\end{array} \\
\mbox{(table instance)} & {\mathit{tableinst}} &::=& \{\; \begin{array}[t]{@{}l@{}}
\mathsf{type}~{\mathit{tabletype}},\; \\
  \mathsf{elem}~{{\mathit{ref}}^\ast} \;\}\end{array} \\
\mbox{(memory instance)} & {\mathit{meminst}} &::=& \{\; \begin{array}[t]{@{}l@{}}
\mathsf{type}~{\mathit{memtype}},\; \\
  \mathsf{data}~{{\mathit{byte}}^\ast} \;\}\end{array} \\
\mbox{(element instance)} & {\mathit{eleminst}} &::=& \{\; \begin{array}[t]{@{}l@{}}
\mathsf{type}~{\mathit{elemtype}},\; \\
  \mathsf{elem}~{{\mathit{ref}}^\ast} \;\}\end{array} \\
\mbox{(data instance)} & {\mathit{datainst}} &::=& \{\; \begin{array}[t]{@{}l@{}}
\mathsf{data}~{{\mathit{byte}}^\ast} \;\}\end{array} \\
\mbox{(export instance)} & {\mathit{exportinst}} &::=& \{\; \begin{array}[t]{@{}l@{}}
\mathsf{name}~{\mathit{name}},\; \\
  \mathsf{value}~{\mathit{externval}} \;\}\end{array} \\
\mbox{(packed value)} & {\mathit{packedval}} &::=& {\mathit{packedtype}}.\mathsf{pack}~{\mathit{c}}_{{\mathit{packedtype}}} \\
\mbox{(field value)} & {\mathit{fieldval}} &::=& {\mathit{val}} ~|~ {\mathit{packedval}} \\
\mbox{(structure instance)} & {\mathit{structinst}} &::=& \{\; \begin{array}[t]{@{}l@{}}
\mathsf{type}~{\mathit{deftype}},\; \\
  \mathsf{field}~{{\mathit{fieldval}}^\ast} \;\}\end{array} \\
\mbox{(array instance)} & {\mathit{arrayinst}} &::=& \{\; \begin{array}[t]{@{}l@{}}
\mathsf{type}~{\mathit{deftype}},\; \\
  \mathsf{field}~{{\mathit{fieldval}}^\ast} \;\}\end{array} \\
\mbox{(module instance)} & {\mathit{moduleinst}} &::=& \{\; \begin{array}[t]{@{}l@{}}
\mathsf{type}~{{\mathit{deftype}}^\ast},\; \\
  \mathsf{func}~{{\mathit{funcaddr}}^\ast},\; \\
  \mathsf{global}~{{\mathit{globaladdr}}^\ast},\; \\
  \mathsf{table}~{{\mathit{tableaddr}}^\ast},\; \\
  \mathsf{mem}~{{\mathit{memaddr}}^\ast},\; \\
  \mathsf{elem}~{{\mathit{elemaddr}}^\ast},\; \\
  \mathsf{data}~{{\mathit{dataaddr}}^\ast},\; \\
  \mathsf{export}~{{\mathit{exportinst}}^\ast} \;\}\end{array} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
\mbox{(store)} & {\mathit{store}} &::=& \{\; \begin{array}[t]{@{}l@{}}
\mathsf{func}~{{\mathit{funcinst}}^\ast},\; \\
  \mathsf{global}~{{\mathit{globalinst}}^\ast},\; \\
  \mathsf{table}~{{\mathit{tableinst}}^\ast},\; \\
  \mathsf{mem}~{{\mathit{meminst}}^\ast},\; \\
  \mathsf{elem}~{{\mathit{eleminst}}^\ast},\; \\
  \mathsf{data}~{{\mathit{datainst}}^\ast},\; \\
  \mathsf{struct}~{{\mathit{structinst}}^\ast},\; \\
  \mathsf{array}~{{\mathit{arrayinst}}^\ast} \;\}\end{array} \\
\mbox{(frame)} & {\mathit{frame}} &::=& \{\; \begin{array}[t]{@{}l@{}}
\mathsf{local}~{({{\mathit{val}}^?})^\ast},\; \\
  \mathsf{module}~{\mathit{moduleinst}} \;\}\end{array} \\
\mbox{(state)} & {\mathit{state}} &::=& {\mathit{store}} ; {\mathit{frame}} \\
\mbox{(configuration)} & {\mathit{config}} &::=& {\mathit{state}} ; {{{\mathit{instr}}}^\ast} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
\mbox{(administrative instruction)} & {{\mathit{instr}}} &::=& {\mathit{instr}} \\ &&|&
{\mathit{addrref}} \\ &&|&
{{\mathsf{label}}_{{\mathit{n}}}}{\{{{\mathit{instr}}^\ast}\}}~{{{\mathit{instr}}}^\ast} \\ &&|&
{{\mathsf{frame}}_{{\mathit{n}}}}{\{{\mathit{frame}}\}}~{{{\mathit{instr}}}^\ast} \\ &&|&
\mathsf{trap} \\
\mbox{(evaluation context)} & {\mathit{E}} &::=& [\mathsf{\_}] \\ &&|&
{{\mathit{val}}^\ast}~{\mathit{E}}~{{\mathit{instr}}^\ast} \\ &&|&
{{\mathsf{label}}_{{\mathit{n}}}}{\{{{\mathit{instr}}^\ast}\}}~{\mathit{E}} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{{\mathrm{inst}}}_{{\mathit{mm}}}({\mathit{rt}}) &=& {{\mathit{rt}}}{[{ := }\;{{\mathit{dt}}^\ast}]} &\quad
  \mbox{if}~{{\mathit{dt}}^\ast} = {\mathit{mm}}.\mathsf{type} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{{\mathrm{default}}}_{\mathsf{i{\scriptstyle32}}} &=& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~0) &  \\
{{\mathrm{default}}}_{\mathsf{i{\scriptstyle64}}} &=& (\mathsf{i{\scriptstyle64}}.\mathsf{const}~0) &  \\
{{\mathrm{default}}}_{\mathsf{f{\scriptstyle32}}} &=& (\mathsf{f{\scriptstyle32}}.\mathsf{const}~0) &  \\
{{\mathrm{default}}}_{\mathsf{f{\scriptstyle64}}} &=& (\mathsf{f{\scriptstyle64}}.\mathsf{const}~0) &  \\
{{\mathrm{default}}}_{\mathsf{ref}~\mathsf{null}~{\mathit{ht}}} &=& (\mathsf{ref.null}~{\mathit{ht}}) &  \\
{{\mathrm{default}}}_{\mathsf{ref}~\epsilon~{\mathit{ht}}} &=& \epsilon &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{{\mathrm{pack}}}_{{\mathit{t}}}({\mathit{val}}) &=& {\mathit{val}} &  \\
{{\mathrm{pack}}}_{{\mathit{pt}}}(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}) &=& {\mathit{pt}}.\mathsf{pack}~{{{\mathrm{wrap}}}_{32,{|{\mathit{pt}}|}}}{({\mathit{i}})} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{{{{\mathrm{unpack}}}_{{\mathit{t}}}^{\epsilon}}}{({\mathit{val}})} &=& {\mathit{val}} &  \\
{{{{\mathrm{unpack}}}_{{\mathit{pt}}}^{{\mathit{sx}}}}}{({\mathit{pt}}.\mathsf{pack}~{\mathit{i}})} &=& \mathsf{i{\scriptstyle32}}.\mathsf{const}~{{{{\mathrm{ext}}}_{{|{\mathit{pt}}|},32}^{{\mathit{sx}}}}}{({\mathit{i}})} &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{funcs}}(\epsilon) &=& \epsilon &  \\
{\mathrm{funcs}}((\mathsf{func}~{\mathit{fa}})~{{\mathit{xv}}^\ast}) &=& {\mathit{fa}}~{\mathrm{funcs}}({{\mathit{xv}}^\ast}) &  \\
{\mathrm{funcs}}({\mathit{externval}}~{{\mathit{xv}}^\ast}) &=& {\mathrm{funcs}}({{\mathit{xv}}^\ast}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{globals}}(\epsilon) &=& \epsilon &  \\
{\mathrm{globals}}((\mathsf{global}~{\mathit{ga}})~{{\mathit{xv}}^\ast}) &=& {\mathit{ga}}~{\mathrm{globals}}({{\mathit{xv}}^\ast}) &  \\
{\mathrm{globals}}({\mathit{externval}}~{{\mathit{xv}}^\ast}) &=& {\mathrm{globals}}({{\mathit{xv}}^\ast}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{tables}}(\epsilon) &=& \epsilon &  \\
{\mathrm{tables}}((\mathsf{table}~{\mathit{ta}})~{{\mathit{xv}}^\ast}) &=& {\mathit{ta}}~{\mathrm{tables}}({{\mathit{xv}}^\ast}) &  \\
{\mathrm{tables}}({\mathit{externval}}~{{\mathit{xv}}^\ast}) &=& {\mathrm{tables}}({{\mathit{xv}}^\ast}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{mems}}(\epsilon) &=& \epsilon &  \\
{\mathrm{mems}}((\mathsf{mem}~{\mathit{ma}})~{{\mathit{xv}}^\ast}) &=& {\mathit{ma}}~{\mathrm{mems}}({{\mathit{xv}}^\ast}) &  \\
{\mathrm{mems}}({\mathit{externval}}~{{\mathit{xv}}^\ast}) &=& {\mathrm{mems}}({{\mathit{xv}}^\ast}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}}).\mathsf{store} &=& {\mathit{s}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}}).\mathsf{frame} &=& {\mathit{f}} &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}}).\mathsf{module}.\mathsf{func} &=& {\mathit{f}}.\mathsf{module}.\mathsf{func} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}}).\mathsf{func} &=& {\mathit{s}}.\mathsf{func} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}}).\mathsf{global} &=& {\mathit{s}}.\mathsf{global} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}}).\mathsf{table} &=& {\mathit{s}}.\mathsf{table} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}}).\mathsf{mem} &=& {\mathit{s}}.\mathsf{mem} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}}).\mathsf{elem} &=& {\mathit{s}}.\mathsf{elem} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}}).\mathsf{data} &=& {\mathit{s}}.\mathsf{data} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}}).\mathsf{struct} &=& {\mathit{s}}.\mathsf{struct} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}}).\mathsf{array} &=& {\mathit{s}}.\mathsf{array} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}}).\mathsf{module} &=& {\mathit{f}}.\mathsf{module} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}}).\mathsf{type}~[{\mathit{x}}] &=& {\mathit{f}}.\mathsf{module}.\mathsf{type}[{\mathit{x}}] &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{({\mathit{s}} ; {\mathit{f}}).\mathsf{func}}{[{\mathit{x}}]} &=& {\mathit{s}}.\mathsf{func}[{\mathit{f}}.\mathsf{module}.\mathsf{func}[{\mathit{x}}]] &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{({\mathit{s}} ; {\mathit{f}}).\mathsf{global}}{[{\mathit{x}}]} &=& {\mathit{s}}.\mathsf{global}[{\mathit{f}}.\mathsf{module}.\mathsf{global}[{\mathit{x}}]] &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{({\mathit{s}} ; {\mathit{f}}).\mathsf{table}}{[{\mathit{x}}]} &=& {\mathit{s}}.\mathsf{table}[{\mathit{f}}.\mathsf{module}.\mathsf{table}[{\mathit{x}}]] &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{({\mathit{s}} ; {\mathit{f}}).\mathsf{mem}}{[{\mathit{x}}]} &=& {\mathit{s}}.\mathsf{mem}[{\mathit{f}}.\mathsf{module}.\mathsf{mem}[{\mathit{x}}]] &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{({\mathit{s}} ; {\mathit{f}}).\mathsf{elem}}{[{\mathit{x}}]} &=& {\mathit{s}}.\mathsf{elem}[{\mathit{f}}.\mathsf{module}.\mathsf{elem}[{\mathit{x}}]] &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{({\mathit{s}} ; {\mathit{f}}).\mathsf{data}}{[{\mathit{x}}]} &=& {\mathit{s}}.\mathsf{data}[{\mathit{f}}.\mathsf{module}.\mathsf{data}[{\mathit{x}}]] &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{({\mathit{s}} ; {\mathit{f}}).\mathsf{local}}{[{\mathit{x}}]} &=& {\mathit{f}}.\mathsf{local}[{\mathit{x}}] &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}})[\mathsf{local}[{\mathit{x}}] = {\mathit{v}}] &=& {\mathit{s}} ; {\mathit{f}}[\mathsf{local}[{\mathit{x}}] = {\mathit{v}}] &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}})[\mathsf{global}[{\mathit{x}}].\mathsf{value} = {\mathit{v}}] &=& {\mathit{s}}[\mathsf{global}[{\mathit{f}}.\mathsf{module}.\mathsf{global}[{\mathit{x}}]].\mathsf{value} = {\mathit{v}}] ; {\mathit{f}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}})[\mathsf{table}[{\mathit{x}}].\mathsf{elem}[{\mathit{i}}] = {\mathit{r}}] &=& {\mathit{s}}[\mathsf{table}[{\mathit{f}}.\mathsf{module}.\mathsf{table}[{\mathit{x}}]].\mathsf{elem}[{\mathit{i}}] = {\mathit{r}}] ; {\mathit{f}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}})[\mathsf{table}[{\mathit{x}}] = {\mathit{ti}}] &=& {\mathit{s}}[\mathsf{table}[{\mathit{f}}.\mathsf{module}.\mathsf{table}[{\mathit{x}}]] = {\mathit{ti}}] ; {\mathit{f}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}})[\mathsf{mem}[{\mathit{x}}].\mathsf{data}[{\mathit{i}} : {\mathit{j}}] = {{\mathit{b}}^\ast}] &=& {\mathit{s}}[\mathsf{mem}[{\mathit{f}}.\mathsf{module}.\mathsf{mem}[{\mathit{x}}]].\mathsf{data}[{\mathit{i}} : {\mathit{j}}] = {{\mathit{b}}^\ast}] ; {\mathit{f}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}})[\mathsf{mem}[{\mathit{x}}] = {\mathit{mi}}] &=& {\mathit{s}}[\mathsf{mem}[{\mathit{f}}.\mathsf{module}.\mathsf{mem}[{\mathit{x}}]] = {\mathit{mi}}] ; {\mathit{f}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}})[\mathsf{elem}[{\mathit{x}}].\mathsf{elem} = {{\mathit{r}}^\ast}] &=& {\mathit{s}}[\mathsf{elem}[{\mathit{f}}.\mathsf{module}.\mathsf{elem}[{\mathit{x}}]].\mathsf{elem} = {{\mathit{r}}^\ast}] ; {\mathit{f}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}})[\mathsf{data}[{\mathit{x}}].\mathsf{data} = {{\mathit{b}}^\ast}] &=& {\mathit{s}}[\mathsf{data}[{\mathit{f}}.\mathsf{module}.\mathsf{data}[{\mathit{x}}]].\mathsf{data} = {{\mathit{b}}^\ast}] ; {\mathit{f}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{with}}_{{\mathit{struct}}}(({\mathit{s}} ; {\mathit{f}}),\, {\mathit{a}},\, {\mathit{i}},\, {\mathit{fv}}) &=& {\mathit{s}}[\mathsf{struct}[{\mathit{a}}].\mathsf{field}[{\mathit{i}}] = {\mathit{fv}}] ; {\mathit{f}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{with}}_{{\mathit{array}}}(({\mathit{s}} ; {\mathit{f}}),\, {\mathit{a}},\, {\mathit{i}},\, {\mathit{fv}}) &=& {\mathit{s}}[\mathsf{array}[{\mathit{a}}].\mathsf{field}[{\mathit{i}}] = {\mathit{fv}}] ; {\mathit{f}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}})[\mathsf{struct} = ..{{\mathit{si}}^\ast}] &=& {\mathit{s}}[\mathsf{struct} = ..{{\mathit{si}}^\ast}] ; {\mathit{f}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
({\mathit{s}} ; {\mathit{f}})[\mathsf{array} = ..{{\mathit{ai}}^\ast}] &=& {\mathit{s}}[\mathsf{array} = ..{{\mathit{ai}}^\ast}] ; {\mathit{f}} &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{growtable}}({\mathit{ti}},\, {\mathit{n}},\, {\mathit{r}}) &=& \{ \begin{array}[t]{@{}l@{}}
\mathsf{type}~{\mathit{tt}'},\; \mathsf{elem}~{{\mathit{r}'}^\ast}~{{\mathit{r}}^{{\mathit{n}}}} \}\end{array} &\quad
  \mbox{if}~{\mathit{ti}} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{type}~([{\mathit{i}} .. {\mathit{j}}]~{\mathit{rt}}),\; \mathsf{elem}~{{\mathit{r}'}^\ast} \}\end{array} \\
 &&&\quad {\land}~{\mathit{tt}'} = [({\mathit{i}} + {\mathit{n}}) .. {\mathit{j}}]~{\mathit{rt}} \\
 &&&\quad {\land}~{\mathit{i}} + {\mathit{n}} \leq {\mathit{j}} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{growmemory}}({\mathit{mi}},\, {\mathit{n}}) &=& \{ \begin{array}[t]{@{}l@{}}
\mathsf{type}~{\mathit{mt}'},\; \mathsf{data}~{{\mathit{b}}^\ast}~{0^{{\mathit{n}} \cdot 64 \cdot {\mathrm{Ki}}}} \}\end{array} &\quad
  \mbox{if}~{\mathit{mi}} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{type}~([{\mathit{i}} .. {\mathit{j}}]~\mathsf{i{\scriptstyle8}}),\; \mathsf{data}~{{\mathit{b}}^\ast} \}\end{array} \\
 &&&\quad {\land}~{\mathit{mt}'} = [({\mathit{i}} + {\mathit{n}}) .. {\mathit{j}}]~\mathsf{i{\scriptstyle8}} \\
 &&&\quad {\land}~{\mathit{i}} + {\mathit{n}} \leq {\mathit{j}} \\
\end{array}
$$

$$
\begin{array}{@{}lrrl@{}}
\mbox{(initialization status)} & {\mathit{init}} &::=& \mathsf{set} ~|~ \mathsf{unset} \\
\mbox{(local type)} & {\mathit{localtype}} &::=& {\mathit{init}}~{\mathit{valtype}} \\
\mbox{(instruction type)} & {\mathit{instrtype}} &::=& {\mathit{resulttype}} \rightarrow {{\mathit{localidx}}^\ast}~{\mathit{resulttype}} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
\mbox{(context)} & {\mathit{context}} &::=& \{\; \begin{array}[t]{@{}l@{}}
\mathsf{type}~{{\mathit{deftype}}^\ast},\; \mathsf{rec}~{{\mathit{subtype}}^\ast},\; \\
  \mathsf{func}~{{\mathit{deftype}}^\ast},\; \mathsf{global}~{{\mathit{globaltype}}^\ast},\; \mathsf{table}~{{\mathit{tabletype}}^\ast},\; \mathsf{mem}~{{\mathit{memtype}}^\ast},\; \\
  \mathsf{elem}~{{\mathit{elemtype}}^\ast},\; \mathsf{data}~{{\mathit{datatype}}^\ast},\; \\
  \mathsf{local}~{{\mathit{localtype}}^\ast},\; \mathsf{label}~{{\mathit{resulttype}}^\ast},\; \mathsf{return}~{{\mathit{resulttype}}^?} \;\}\end{array} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathit{C}}[\mathsf{local}[\epsilon] = \epsilon] &=& {\mathit{C}} &  \\
{\mathit{C}}[\mathsf{local}[{\mathit{x}}_{{1}}~{{\mathit{x}}^\ast}] = {\mathit{lt}}_{{1}}~{{\mathit{lt}}^\ast}] &=& {\mathit{C}}[\mathsf{local}[{\mathit{x}}_{{1}}] = {\mathit{lt}}_{{1}}][\mathsf{local}[{{\mathit{x}}^\ast}] = {{\mathit{lt}}^\ast}] &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{{\mathrm{clos}}}_{{\mathit{C}}}~({\mathit{dt}}) &=& {{\mathit{dt}}}{[{ := }\;{{\mathit{dt}'}^\ast}]} &\quad
  \mbox{if}~{{\mathit{dt}'}^\ast} = {\mathrm{clos}}{}^\ast~({\mathit{C}}.\mathsf{type}) \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{clos}}{}^\ast~(\epsilon) &=& \epsilon &  \\
{\mathrm{clos}}{}^\ast~({{\mathit{dt}}^\ast}~{\mathit{dt}}_{{\mathsf{n}}}) &=& {{\mathit{dt}'}^\ast}~{{\mathit{dt}}_{{\mathsf{n}}}}{[{ := }\;{{\mathit{dt}'}^\ast}]} &\quad
  \mbox{if}~{{\mathit{dt}'}^\ast} = {\mathrm{clos}}{}^\ast~({{\mathit{dt}}^\ast}) \\
\end{array}
$$

\vspace{1ex}

$\boxed{{\mathit{context}} \vdash {\mathit{numtype}} : \mathsf{ok}}$

$\boxed{{\mathit{context}} \vdash {\mathit{vectype}} : \mathsf{ok}}$

$\boxed{{\mathit{context}} \vdash {\mathit{heaptype}} : \mathsf{ok}}$

$\boxed{{\mathit{context}} \vdash {\mathit{reftype}} : \mathsf{ok}}$

$\boxed{{\mathit{context}} \vdash {\mathit{valtype}} : \mathsf{ok}}$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash {\mathit{numtype}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}num}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash {\mathit{vectype}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}vec}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash {\mathit{absheaptype}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}heap{-}abs}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] = {\mathit{dt}}
}{
{\mathit{C}} \vdash {\mathit{x}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}heap{-}typeidx}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{rec}[{\mathit{i}}] = {\mathit{st}}
}{
{\mathit{C}} \vdash \mathsf{rec}~{\mathit{i}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}heap{-}rec}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{ht}} : \mathsf{ok}
}{
{\mathit{C}} \vdash \mathsf{ref}~{\mathit{nul}}~{\mathit{ht}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}ref}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{numtype}} : \mathsf{ok}
}{
{\mathit{C}} \vdash {\mathit{numtype}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}val{-}num}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{vectype}} : \mathsf{ok}
}{
{\mathit{C}} \vdash {\mathit{vectype}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}val{-}vec}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{reftype}} : \mathsf{ok}
}{
{\mathit{C}} \vdash {\mathit{reftype}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}val{-}ref}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{bot} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}val{-}bot}]}
\qquad
\end{array}
$$

\vspace{1ex}

$\boxed{{\mathit{context}} \vdash {\mathit{resulttype}} : \mathsf{ok}}$

$\boxed{{\mathit{context}} \vdash {\mathit{instrtype}} : \mathsf{ok}}$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
({\mathit{C}} \vdash {\mathit{t}} : \mathsf{ok})^\ast
}{
{\mathit{C}} \vdash {{\mathit{t}}^\ast} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}result}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {{\mathit{t}}_{{1}}^\ast} : \mathsf{ok}
 \qquad
{\mathit{C}} \vdash {{\mathit{t}}_{{2}}^\ast} : \mathsf{ok}
 \qquad
(({\mathit{C}}.\mathsf{local}[{\mathit{x}}] = {\mathit{lt}}))^\ast
}{
{\mathit{C}} \vdash {{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{x}}^\ast}~{{\mathit{t}}_{{2}}^\ast} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}instr}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
& {{\mathsf{ok}}{({\mathit{typeidx}})}} &::=& {\mathsf{ok}}{({\mathit{typeidx}})} \\
& {{\mathsf{ok}}{({\mathit{typeidx}},\, {\mathit{n}})}} &::=& {\mathsf{ok}}{({\mathit{typeidx}},\, {\mathit{nat}})} \\
\end{array}
$$

$\boxed{{\mathit{context}} \vdash {\mathit{packedtype}} : \mathsf{ok}}$

$\boxed{{\mathit{context}} \vdash {\mathit{fieldtype}} : \mathsf{ok}}$

$\boxed{{\mathit{context}} \vdash {\mathit{storagetype}} : \mathsf{ok}}$

$\boxed{{\mathit{context}} \vdash {\mathit{comptype}} : \mathsf{ok}}$

$\boxed{{\mathit{context}} \vdash {\mathit{functype}} : \mathsf{ok}}$

$\boxed{{\mathit{context}} \vdash {\mathit{subtype}} : {{\mathsf{ok}}{({\mathit{typeidx}})}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{rectype}} : {{\mathsf{ok}}{({\mathit{typeidx}})}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{subtype}} : {{\mathsf{ok}}{({\mathit{typeidx}},\, {\mathit{n}})}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{rectype}} : {{\mathsf{ok}}{({\mathit{typeidx}},\, {\mathit{n}})}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{deftype}} : \mathsf{ok}}$

$\boxed{{\mathit{context}} \vdash {\mathit{comptype}} \leq {\mathit{comptype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{deftype}} \leq {\mathit{deftype}}}$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash {\mathit{packedtype}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}packed}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{valtype}} : \mathsf{ok}
}{
{\mathit{C}} \vdash {\mathit{valtype}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}storage{-}val}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{packedtype}} : \mathsf{ok}
}{
{\mathit{C}} \vdash {\mathit{packedtype}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}storage{-}packed}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{zt}} : \mathsf{ok}
}{
{\mathit{C}} \vdash {\mathit{mut}}~{\mathit{zt}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}field}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
({\mathit{C}} \vdash {\mathit{yt}} : \mathsf{ok})^\ast
}{
{\mathit{C}} \vdash \mathsf{struct}~{{\mathit{yt}}^\ast} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}comp{-}struct}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{yt}} : \mathsf{ok}
}{
{\mathit{C}} \vdash \mathsf{array}~{\mathit{yt}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}comp{-}array}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{ft}} : \mathsf{ok}
}{
{\mathit{C}} \vdash \mathsf{func}~{\mathit{ft}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}comp{-}func}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{|{{\mathit{y}}^\ast}|} \leq 1
 \qquad
(({\mathit{y}} < {\mathit{x}}))^\ast
 \qquad
(({\mathrm{unroll}}({\mathit{C}}.\mathsf{type}[{\mathit{y}}]) = \mathsf{sub}~\epsilon~{{\mathit{y}'}^\ast}~{\mathit{ct}'}))^\ast
 \qquad
{\mathit{C}} \vdash {\mathit{ct}} : \mathsf{ok}
 \qquad
({\mathit{C}} \vdash {\mathit{ct}} \leq {\mathit{ct}'})^\ast
}{
{\mathit{C}} \vdash \mathsf{sub}~{\mathit{fin}}~{{\mathit{y}}^\ast}~{\mathit{ct}} : {\mathsf{ok}}{({\mathit{x}})}
} \, {[\textsc{\scriptsize K{-}sub}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathit{deftype}} \prec {\mathit{x}}, {\mathit{i}} &=& \mathsf{true} &  \\
{\mathit{typeidx}} \prec {\mathit{x}}, {\mathit{i}} &=& {\mathit{typeidx}} < {\mathit{x}} &  \\
\mathsf{rec}~{\mathit{j}} \prec {\mathit{x}}, {\mathit{i}} &=& {\mathit{j}} < {\mathit{i}} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{{\mathrm{unroll}}}_{{\mathit{C}}}({\mathit{deftype}}) &=& {\mathrm{unroll}}({\mathit{deftype}}) &  \\
{{\mathrm{unroll}}}_{{\mathit{C}}}({\mathit{typeidx}}) &=& {\mathrm{unroll}}({\mathit{C}}.\mathsf{type}[{\mathit{typeidx}}]) &  \\
{{\mathrm{unroll}}}_{{\mathit{C}}}(\mathsf{rec}~{\mathit{i}}) &=& {\mathit{C}}.\mathsf{rec}[{\mathit{i}}] &  \\
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{|{{\mathit{y}}^\ast}|} \leq 1
 \qquad
(({\mathit{ht}} \prec {\mathit{x}}, {\mathit{i}}))^\ast
 \qquad
(({{\mathrm{unroll}}}_{{\mathit{C}}}({\mathit{ht}}) = \mathsf{sub}~\epsilon~{{\mathit{ht}'}^\ast}~{\mathit{ct}'}))^\ast
 \qquad
{\mathit{C}} \vdash {\mathit{ct}} : \mathsf{ok}
 \qquad
({\mathit{C}} \vdash {\mathit{ct}} \leq {\mathit{ct}'})^\ast
}{
{\mathit{C}} \vdash \mathsf{sub}~{\mathit{fin}}~{{\mathit{ht}}^\ast}~{\mathit{ct}} : {\mathsf{ok}}{({\mathit{x}},\, {\mathit{i}})}
} \, {[\textsc{\scriptsize K{-}sub2}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{rec}~\epsilon : {\mathsf{ok}}{({\mathit{x}})}
} \, {[\textsc{\scriptsize K{-}rect{-}empty}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{st}}_{{1}} : {\mathsf{ok}}{({\mathit{x}})}
 \qquad
{\mathit{C}} \vdash \mathsf{rec}~{{\mathit{st}}^\ast} : {\mathsf{ok}}{({\mathit{x}} + 1)}
}{
{\mathit{C}} \vdash \mathsf{rec}~{\mathit{st}}_{{1}}~{{\mathit{st}}^\ast} : {\mathsf{ok}}{({\mathit{x}})}
} \, {[\textsc{\scriptsize K{-}rect{-}cons}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}, \mathsf{rec}~{{\mathit{st}}^\ast} \vdash \mathsf{rec}~{{\mathit{st}}^\ast} : {\mathsf{ok}}{({\mathit{x}},\, 0)}
}{
{\mathit{C}} \vdash \mathsf{rec}~{{\mathit{st}}^\ast} : {\mathsf{ok}}{({\mathit{x}})}
} \, {[\textsc{\scriptsize K{-}rect{-}rec2}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{rec}~\epsilon : {\mathsf{ok}}{({\mathit{x}},\, {\mathit{i}})}
} \, {[\textsc{\scriptsize K{-}rec2{-}empty}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{st}}_{{1}} : {\mathsf{ok}}{({\mathit{x}},\, {\mathit{i}})}
 \qquad
{\mathit{C}} \vdash \mathsf{rec}~{{\mathit{st}}^\ast} : {\mathsf{ok}}{({\mathit{x}} + 1,\, {\mathit{i}} + 1)}
}{
{\mathit{C}} \vdash \mathsf{rec}~{\mathit{st}}_{{1}}~{{\mathit{st}}^\ast} : {\mathsf{ok}}{({\mathit{x}},\, {\mathit{i}})}
} \, {[\textsc{\scriptsize K{-}rec2{-}cons}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{qt}} : {\mathsf{ok}}{({\mathit{x}})}
 \qquad
{\mathit{qt}} = \mathsf{rec}~{{\mathit{st}}^{{\mathit{n}}}}
 \qquad
{\mathit{i}} < {\mathit{n}}
}{
{\mathit{C}} \vdash {\mathit{qt}} . {\mathit{i}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}def}]}
\qquad
\end{array}
$$

\vspace{1ex}

$\boxed{{\mathit{context}} \vdash {\mathit{limits}} : {\mathit{nat}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{globaltype}} : \mathsf{ok}}$

$\boxed{{\mathit{context}} \vdash {\mathit{tabletype}} : \mathsf{ok}}$

$\boxed{{\mathit{context}} \vdash {\mathit{memtype}} : \mathsf{ok}}$

$\boxed{{\mathit{context}} \vdash {\mathit{externtype}} : \mathsf{ok}}$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{n}}_{{1}} \leq {\mathit{n}}_{{2}} \leq {\mathit{k}}
}{
{\mathit{C}} \vdash [{\mathit{n}}_{{1}} .. {\mathit{n}}_{{2}}] : {\mathit{k}}
} \, {[\textsc{\scriptsize K{-}limits}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {{\mathit{t}}_{{1}}^\ast} : \mathsf{ok}
 \qquad
{\mathit{C}} \vdash {{\mathit{t}}_{{2}}^\ast} : \mathsf{ok}
}{
{\mathit{C}} \vdash {{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}func}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{t}} : \mathsf{ok}
}{
{\mathit{C}} \vdash {\mathit{mut}}~{\mathit{t}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}global}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{lim}} : {2^{32}} - 1
 \qquad
{\mathit{C}} \vdash {\mathit{rt}} : \mathsf{ok}
}{
{\mathit{C}} \vdash {\mathit{lim}}~{\mathit{rt}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}table}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{lim}} : {2^{16}}
}{
{\mathit{C}} \vdash {\mathit{lim}}~\mathsf{i{\scriptstyle8}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}mem}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{dt}} : \mathsf{ok}
 \qquad
{\mathit{dt}} \approx \mathsf{func}~{\mathit{ft}}
}{
{\mathit{C}} \vdash \mathsf{func}~{\mathit{dt}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}extern{-}func}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{gt}} : \mathsf{ok}
}{
{\mathit{C}} \vdash \mathsf{global}~{\mathit{gt}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}extern{-}global}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{tt}} : \mathsf{ok}
}{
{\mathit{C}} \vdash \mathsf{table}~{\mathit{tt}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}extern{-}table}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{mt}} : \mathsf{ok}
}{
{\mathit{C}} \vdash \mathsf{mem}~{\mathit{mt}} : \mathsf{ok}
} \, {[\textsc{\scriptsize K{-}extern{-}mem}]}
\qquad
\end{array}
$$

\vspace{1ex}

$\boxed{{\mathit{context}} \vdash {\mathit{numtype}} \leq {\mathit{numtype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{vectype}} \leq {\mathit{vectype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{heaptype}} \leq {\mathit{heaptype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{reftype}} \leq {\mathit{reftype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{valtype}} \leq {\mathit{valtype}}}$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash {\mathit{numtype}} \leq {\mathit{numtype}}
} \, {[\textsc{\scriptsize S{-}num}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash {\mathit{vectype}} \leq {\mathit{vectype}}
} \, {[\textsc{\scriptsize S{-}vec}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash {\mathit{heaptype}} \leq {\mathit{heaptype}}
} \, {[\textsc{\scriptsize S{-}heap{-}refl}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{heaptype}'} : \mathsf{ok}
 \qquad
{\mathit{C}} \vdash {\mathit{heaptype}}_{{1}} \leq {\mathit{heaptype}'}
 \qquad
{\mathit{C}} \vdash {\mathit{heaptype}'} \leq {\mathit{heaptype}}_{{2}}
}{
{\mathit{C}} \vdash {\mathit{heaptype}}_{{1}} \leq {\mathit{heaptype}}_{{2}}
} \, {[\textsc{\scriptsize S{-}heap{-}trans}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{eq} \leq \mathsf{any}
} \, {[\textsc{\scriptsize S{-}heap{-}eq{-}any}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{i{\scriptstyle31}} \leq \mathsf{eq}
} \, {[\textsc{\scriptsize S{-}heap{-}i31{-}eq}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{struct} \leq \mathsf{eq}
} \, {[\textsc{\scriptsize S{-}heap{-}struct{-}eq}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{array} \leq \mathsf{eq}
} \, {[\textsc{\scriptsize S{-}heap{-}array{-}eq}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{deftype}} \approx \mathsf{struct}~{{\mathit{yt}}^\ast}
}{
{\mathit{C}} \vdash {\mathit{deftype}} \leq \mathsf{struct}
} \, {[\textsc{\scriptsize S{-}heap{-}struct}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{deftype}} \approx \mathsf{array}~{\mathit{yt}}
}{
{\mathit{C}} \vdash {\mathit{deftype}} \leq \mathsf{array}
} \, {[\textsc{\scriptsize S{-}heap{-}array}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{deftype}} \approx \mathsf{func}~{\mathit{ft}}
}{
{\mathit{C}} \vdash {\mathit{deftype}} \leq \mathsf{func}
} \, {[\textsc{\scriptsize S{-}heap{-}func}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{deftype}}_{{1}} \leq {\mathit{deftype}}_{{2}}
}{
{\mathit{C}} \vdash {\mathit{deftype}}_{{1}} \leq {\mathit{deftype}}_{{2}}
} \, {[\textsc{\scriptsize S{-}heap{-}def}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{C}}.\mathsf{type}[{\mathit{typeidx}}] \leq {\mathit{heaptype}}
}{
{\mathit{C}} \vdash {\mathit{typeidx}} \leq {\mathit{heaptype}}
} \, {[\textsc{\scriptsize S{-}heap{-}typeidx{-}l}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{heaptype}} \leq {\mathit{C}}.\mathsf{type}[{\mathit{typeidx}}]
}{
{\mathit{C}} \vdash {\mathit{heaptype}} \leq {\mathit{typeidx}}
} \, {[\textsc{\scriptsize S{-}heap{-}typeidx{-}r}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{rec}[{\mathit{i}}] = \mathsf{sub}~{\mathit{fin}}~({{\mathit{ht}}_{{1}}^\ast}~{\mathit{ht}}~{{\mathit{ht}}_{{2}}^\ast})~{\mathit{ct}}
}{
{\mathit{C}} \vdash \mathsf{rec}~{\mathit{i}} \leq {\mathit{ht}}
} \, {[\textsc{\scriptsize S{-}heap{-}rec}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{heaptype}} \leq \mathsf{any}
}{
{\mathit{C}} \vdash \mathsf{none} \leq {\mathit{heaptype}}
} \, {[\textsc{\scriptsize S{-}heap{-}none}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{heaptype}} \leq \mathsf{func}
}{
{\mathit{C}} \vdash \mathsf{nofunc} \leq {\mathit{heaptype}}
} \, {[\textsc{\scriptsize S{-}heap{-}nofunc}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{heaptype}} \leq \mathsf{extern}
}{
{\mathit{C}} \vdash \mathsf{noextern} \leq {\mathit{heaptype}}
} \, {[\textsc{\scriptsize S{-}heap{-}noextern}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{bot} \leq {\mathit{heaptype}}
} \, {[\textsc{\scriptsize S{-}heap{-}bot}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{ht}}_{{1}} \leq {\mathit{ht}}_{{2}}
}{
{\mathit{C}} \vdash \mathsf{ref}~\epsilon~{\mathit{ht}}_{{1}} \leq \mathsf{ref}~\epsilon~{\mathit{ht}}_{{2}}
} \, {[\textsc{\scriptsize S{-}ref{-}nonnull}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{ht}}_{{1}} \leq {\mathit{ht}}_{{2}}
}{
{\mathit{C}} \vdash \mathsf{ref}~{\mathit{nul}}~{\mathit{ht}}_{{1}} \leq \mathsf{ref}~\mathsf{null}~{\mathit{ht}}_{{2}}
} \, {[\textsc{\scriptsize S{-}ref{-}null}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{numtype}}_{{1}} \leq {\mathit{numtype}}_{{2}}
}{
{\mathit{C}} \vdash {\mathit{numtype}}_{{1}} \leq {\mathit{numtype}}_{{2}}
} \, {[\textsc{\scriptsize S{-}val{-}num}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{vectype}}_{{1}} \leq {\mathit{vectype}}_{{2}}
}{
{\mathit{C}} \vdash {\mathit{vectype}}_{{1}} \leq {\mathit{vectype}}_{{2}}
} \, {[\textsc{\scriptsize S{-}val{-}vec}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{reftype}}_{{1}} \leq {\mathit{reftype}}_{{2}}
}{
{\mathit{C}} \vdash {\mathit{reftype}}_{{1}} \leq {\mathit{reftype}}_{{2}}
} \, {[\textsc{\scriptsize S{-}val{-}ref}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{bot} \leq {\mathit{valtype}}
} \, {[\textsc{\scriptsize S{-}val{-}bot}]}
\qquad
\end{array}
$$

\vspace{1ex}

$\boxed{{\mathit{context}} \vdash {{\mathit{valtype}}^\ast} \leq {{\mathit{valtype}}^\ast}}$

$\boxed{{\mathit{context}} \vdash {\mathit{instrtype}} \leq {\mathit{instrtype}}}$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
({\mathit{C}} \vdash {\mathit{t}}_{{1}} \leq {\mathit{t}}_{{2}})^\ast
}{
{\mathit{C}} \vdash {{\mathit{t}}_{{1}}^\ast} \leq {{\mathit{t}}_{{2}}^\ast}
} \, {[\textsc{\scriptsize S{-}result}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {{\mathit{t}}_{{21}}^\ast} \leq {{\mathit{t}}_{{11}}^\ast}
 \qquad
{\mathit{C}} \vdash {{\mathit{t}}_{{12}}^\ast} \leq {{\mathit{t}}_{{22}}^\ast}
 \qquad
{{\mathit{x}}^\ast} = {{\mathit{x}}_{{2}}^\ast} \setminus {{\mathit{x}}_{{1}}^\ast}
 \qquad
(({\mathit{C}}.\mathsf{local}[{\mathit{x}}] = \mathsf{set}~{\mathit{t}}))^\ast
}{
{\mathit{C}} \vdash {{\mathit{t}}_{{11}}^\ast} \rightarrow ({{\mathit{x}}_{{1}}^\ast})~{{\mathit{t}}_{{12}}^\ast} \leq {{\mathit{t}}_{{21}}^\ast} \rightarrow ({{\mathit{x}}_{{2}}^\ast})~{{\mathit{t}}_{{22}}^\ast}
} \, {[\textsc{\scriptsize S{-}instr}]}
\qquad
\end{array}
$$

\vspace{1ex}

$\boxed{{\mathit{context}} \vdash {\mathit{packedtype}} \leq {\mathit{packedtype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{storagetype}} \leq {\mathit{storagetype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{fieldtype}} \leq {\mathit{fieldtype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{functype}} \leq {\mathit{functype}}}$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash {\mathit{packedtype}} \leq {\mathit{packedtype}}
} \, {[\textsc{\scriptsize S{-}packed}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{valtype}}_{{1}} \leq {\mathit{valtype}}_{{2}}
}{
{\mathit{C}} \vdash {\mathit{valtype}}_{{1}} \leq {\mathit{valtype}}_{{2}}
} \, {[\textsc{\scriptsize S{-}storage{-}val}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{packedtype}}_{{1}} \leq {\mathit{packedtype}}_{{2}}
}{
{\mathit{C}} \vdash {\mathit{packedtype}}_{{1}} \leq {\mathit{packedtype}}_{{2}}
} \, {[\textsc{\scriptsize S{-}storage{-}packed}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{zt}}_{{1}} \leq {\mathit{zt}}_{{2}}
}{
{\mathit{C}} \vdash \epsilon~{\mathit{zt}}_{{1}} \leq \epsilon~{\mathit{zt}}_{{2}}
} \, {[\textsc{\scriptsize S{-}field{-}const}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{zt}}_{{1}} \leq {\mathit{zt}}_{{2}}
 \qquad
{\mathit{C}} \vdash {\mathit{zt}}_{{2}} \leq {\mathit{zt}}_{{1}}
}{
{\mathit{C}} \vdash \mathsf{mut}~{\mathit{zt}}_{{1}} \leq \mathsf{mut}~{\mathit{zt}}_{{2}}
} \, {[\textsc{\scriptsize S{-}field{-}var}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
({\mathit{C}} \vdash {\mathit{yt}}_{{1}} \leq {\mathit{yt}}_{{2}})^\ast
}{
{\mathit{C}} \vdash \mathsf{struct}~{{\mathit{yt}}_{{1}}^\ast}~{\mathit{yt}'}_{{1}} \leq \mathsf{struct}~{{\mathit{yt}}_{{2}}^\ast}
} \, {[\textsc{\scriptsize S{-}comp{-}struct}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{yt}}_{{1}} \leq {\mathit{yt}}_{{2}}
}{
{\mathit{C}} \vdash \mathsf{array}~{\mathit{yt}}_{{1}} \leq \mathsf{array}~{\mathit{yt}}_{{2}}
} \, {[\textsc{\scriptsize S{-}comp{-}array}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{ft}}_{{1}} \leq {\mathit{ft}}_{{2}}
}{
{\mathit{C}} \vdash \mathsf{func}~{\mathit{ft}}_{{1}} \leq \mathsf{func}~{\mathit{ft}}_{{2}}
} \, {[\textsc{\scriptsize S{-}comp{-}func}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{{\mathrm{clos}}}_{{\mathit{C}}}~({\mathit{deftype}}_{{1}}) = {{\mathrm{clos}}}_{{\mathit{C}}}~({\mathit{deftype}}_{{2}})
}{
{\mathit{C}} \vdash {\mathit{deftype}}_{{1}} \leq {\mathit{deftype}}_{{2}}
} \, {[\textsc{\scriptsize S{-}def{-}refl}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathrm{unroll}}({\mathit{deftype}}_{{1}}) = \mathsf{sub}~{\mathit{fin}}~({{\mathit{ht}}_{{1}}^\ast}~{\mathit{ht}}~{{\mathit{ht}}_{{2}}^\ast})~{\mathit{ct}}
 \qquad
{\mathit{C}} \vdash {\mathit{ht}} \leq {\mathit{deftype}}_{{2}}
}{
{\mathit{C}} \vdash {\mathit{deftype}}_{{1}} \leq {\mathit{deftype}}_{{2}}
} \, {[\textsc{\scriptsize S{-}def{-}super}]}
\qquad
\end{array}
$$

\vspace{1ex}

$\boxed{{\mathit{context}} \vdash {\mathit{limits}} \leq {\mathit{limits}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{globaltype}} \leq {\mathit{globaltype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{tabletype}} \leq {\mathit{tabletype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{memtype}} \leq {\mathit{memtype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{externtype}} \leq {\mathit{externtype}}}$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{n}}_{{11}} \geq {\mathit{n}}_{{21}}
 \qquad
{\mathit{n}}_{{12}} \leq {\mathit{n}}_{{22}}
}{
{\mathit{C}} \vdash [{\mathit{n}}_{{11}} .. {\mathit{n}}_{{12}}] \leq [{\mathit{n}}_{{21}} .. {\mathit{n}}_{{22}}]
} \, {[\textsc{\scriptsize S{-}limits}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash {\mathit{ft}} \leq {\mathit{ft}}
} \, {[\textsc{\scriptsize S{-}func}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{t}}_{{1}} \leq {\mathit{t}}_{{2}}
}{
{\mathit{C}} \vdash \epsilon~{\mathit{t}}_{{1}} \leq \epsilon~{\mathit{t}}_{{2}}
} \, {[\textsc{\scriptsize S{-}global{-}const}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{t}}_{{1}} \leq {\mathit{t}}_{{2}}
 \qquad
{\mathit{C}} \vdash {\mathit{t}}_{{2}} \leq {\mathit{t}}_{{1}}
}{
{\mathit{C}} \vdash \mathsf{mut}~{\mathit{t}}_{{1}} \leq \mathsf{mut}~{\mathit{t}}_{{2}}
} \, {[\textsc{\scriptsize S{-}global{-}var}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{lim}}_{{1}} \leq {\mathit{lim}}_{{2}}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}}_{{1}} \leq {\mathit{rt}}_{{2}}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}}_{{2}} \leq {\mathit{rt}}_{{1}}
}{
{\mathit{C}} \vdash {\mathit{lim}}_{{1}}~{\mathit{rt}}_{{1}} \leq {\mathit{lim}}_{{2}}~{\mathit{rt}}_{{2}}
} \, {[\textsc{\scriptsize S{-}table}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{lim}}_{{1}} \leq {\mathit{lim}}_{{2}}
}{
{\mathit{C}} \vdash {\mathit{lim}}_{{1}}~\mathsf{i{\scriptstyle8}} \leq {\mathit{lim}}_{{2}}~\mathsf{i{\scriptstyle8}}
} \, {[\textsc{\scriptsize S{-}mem}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{dt}}_{{1}} \leq {\mathit{dt}}_{{2}}
}{
{\mathit{C}} \vdash \mathsf{func}~{\mathit{dt}}_{{1}} \leq \mathsf{func}~{\mathit{dt}}_{{2}}
} \, {[\textsc{\scriptsize S{-}extern{-}func}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{gt}}_{{1}} \leq {\mathit{gt}}_{{2}}
}{
{\mathit{C}} \vdash \mathsf{global}~{\mathit{gt}}_{{1}} \leq \mathsf{global}~{\mathit{gt}}_{{2}}
} \, {[\textsc{\scriptsize S{-}extern{-}global}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{tt}}_{{1}} \leq {\mathit{tt}}_{{2}}
}{
{\mathit{C}} \vdash \mathsf{table}~{\mathit{tt}}_{{1}} \leq \mathsf{table}~{\mathit{tt}}_{{2}}
} \, {[\textsc{\scriptsize S{-}extern{-}table}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{mt}}_{{1}} \leq {\mathit{mt}}_{{2}}
}{
{\mathit{C}} \vdash \mathsf{mem}~{\mathit{mt}}_{{1}} \leq \mathsf{mem}~{\mathit{mt}}_{{2}}
} \, {[\textsc{\scriptsize S{-}extern{-}mem}]}
\qquad
\end{array}
$$

\vspace{1ex}

$\boxed{{\mathit{context}} \vdash {\mathit{instr}} : {\mathit{functype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{instr}} : {\mathit{instrtype}}}$

$\boxed{{\mathit{context}} \vdash {{\mathit{instr}}^\ast} : {\mathit{instrtype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{expr}} : {\mathit{resulttype}}}$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {{\mathit{instr}}^\ast} : \epsilon \rightarrow (\epsilon)~{{\mathit{t}}^\ast}
}{
{\mathit{C}} \vdash {{\mathit{instr}}^\ast} : {{\mathit{t}}^\ast}
} \, {[\textsc{\scriptsize T{-}expr}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{instr}} : {{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast}
}{
{\mathit{C}} \vdash {\mathit{instr}} : {{\mathit{t}}_{{1}}^\ast} \rightarrow (\epsilon)~{{\mathit{t}}_{{2}}^\ast}
} \, {[\textsc{\scriptsize T{-}instr}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \epsilon : \epsilon \rightarrow (\epsilon)~\epsilon
} \, {[\textsc{\scriptsize T{-}instr*{-}empty}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
(({\mathit{C}}.\mathsf{local}[{\mathit{x}}_{{1}}] = {\mathit{init}}~{\mathit{t}}))^\ast
 \qquad
{\mathit{C}'} = {\mathit{C}}[\mathsf{local}[{{\mathit{x}}_{{1}}^\ast}] = {(\mathsf{set}~{\mathit{t}})^\ast}]
 \qquad
{\mathit{C}} \vdash {\mathit{instr}}_{{1}} : {{\mathit{t}}_{{1}}^\ast} \rightarrow ({{\mathit{x}}_{{1}}^\ast})~{{\mathit{t}}_{{2}}^\ast}
 \qquad
{\mathit{C}'} \vdash {{\mathit{instr}}_{{2}}^\ast} : {{\mathit{t}}_{{2}}^\ast} \rightarrow ({{\mathit{x}}_{{2}}^\ast})~{{\mathit{t}}_{{3}}^\ast}
}{
{\mathit{C}} \vdash {\mathit{instr}}_{{1}}~{{\mathit{instr}}_{{2}}^\ast} : {{\mathit{t}}_{{1}}^\ast} \rightarrow ({{\mathit{x}}_{{1}}^\ast}~{{\mathit{x}}_{{2}}^\ast})~{{\mathit{t}}_{{3}}^\ast}
} \, {[\textsc{\scriptsize T{-}instr*{-}seq}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {{\mathit{instr}}^\ast} : {\mathit{it}}
 \qquad
{\mathit{C}} \vdash {\mathit{it}} \leq {\mathit{it}'}
}{
{\mathit{C}} \vdash {{\mathit{instr}}^\ast} : {\mathit{it}'}
} \, {[\textsc{\scriptsize T{-}instr*{-}sub}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {{\mathit{instr}}^\ast} : {{\mathit{t}}_{{1}}^\ast} \rightarrow ({{\mathit{x}}^\ast})~{{\mathit{t}}_{{2}}^\ast}
}{
{\mathit{C}} \vdash {{\mathit{instr}}^\ast} : {{\mathit{t}}^\ast}~{{\mathit{t}}_{{1}}^\ast} \rightarrow ({{\mathit{x}}^\ast})~({{\mathit{t}}^\ast}~{{\mathit{t}}_{{2}}^\ast})
} \, {[\textsc{\scriptsize T{-}instr*{-}frame}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{unreachable} : {{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast}
} \, {[\textsc{\scriptsize T{-}unreachable}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{nop} : \epsilon \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}nop}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{drop} : {\mathit{t}} \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}drop}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{select}~{\mathit{t}} : {\mathit{t}}~{\mathit{t}}~\mathsf{i{\scriptstyle32}} \rightarrow {\mathit{t}}
} \, {[\textsc{\scriptsize T{-}select{-}expl}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{t}} \leq {\mathit{t}'}
 \qquad
{\mathit{t}'} = {\mathit{numtype}} \lor {\mathit{t}'} = {\mathit{vectype}}
}{
{\mathit{C}} \vdash \mathsf{select} : {\mathit{t}}~{\mathit{t}}~\mathsf{i{\scriptstyle32}} \rightarrow {\mathit{t}}
} \, {[\textsc{\scriptsize T{-}select{-}impl}]}
\qquad
\end{array}
$$

\vspace{1ex}

$\boxed{{\mathit{context}} \vdash {\mathit{blocktype}} : {\mathit{functype}}}$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{ft}} : \mathsf{ok}
}{
{\mathit{C}} \vdash {\mathit{ft}} : {\mathit{ft}}
} \, {[\textsc{\scriptsize K{-}block}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{bt}} : {{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast}
 \qquad
{\mathit{C}}, \mathsf{label}~({{\mathit{t}}_{{2}}^\ast}) \vdash {{\mathit{instr}}^\ast} : {{\mathit{t}}_{{1}}^\ast} \rightarrow ({{\mathit{x}}^\ast})~{{\mathit{t}}_{{2}}^\ast}
}{
{\mathit{C}} \vdash \mathsf{block}~{\mathit{bt}}~{{\mathit{instr}}^\ast} : {{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast}
} \, {[\textsc{\scriptsize T{-}block}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{bt}} : {{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast}
 \qquad
{\mathit{C}}, \mathsf{label}~({{\mathit{t}}_{{1}}^\ast}) \vdash {{\mathit{instr}}^\ast} : {{\mathit{t}}_{{1}}^\ast} \rightarrow ({{\mathit{x}}^\ast})~{{\mathit{t}}_{{2}}^\ast}
}{
{\mathit{C}} \vdash \mathsf{loop}~{\mathit{bt}}~{{\mathit{instr}}^\ast} : {{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast}
} \, {[\textsc{\scriptsize T{-}loop}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{bt}} : {{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast}
 \qquad
{\mathit{C}}, \mathsf{label}~({{\mathit{t}}_{{2}}^\ast}) \vdash {{\mathit{instr}}_{{1}}^\ast} : {{\mathit{t}}_{{1}}^\ast} \rightarrow ({{\mathit{x}}_{{1}}^\ast})~{{\mathit{t}}_{{2}}^\ast}
 \qquad
{\mathit{C}}, \mathsf{label}~({{\mathit{t}}_{{2}}^\ast}) \vdash {{\mathit{instr}}_{{2}}^\ast} : {{\mathit{t}}_{{1}}^\ast} \rightarrow ({{\mathit{x}}_{{2}}^\ast})~{{\mathit{t}}_{{2}}^\ast}
}{
{\mathit{C}} \vdash \mathsf{if}~{\mathit{bt}}~{{\mathit{instr}}_{{1}}^\ast}~\mathsf{else}~{{\mathit{instr}}_{{2}}^\ast} : {{\mathit{t}}_{{1}}^\ast}~\mathsf{i{\scriptstyle32}} \rightarrow {{\mathit{t}}_{{2}}^\ast}
} \, {[\textsc{\scriptsize T{-}if}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{label}[{\mathit{l}}] = {{\mathit{t}}^\ast}
}{
{\mathit{C}} \vdash \mathsf{br}~{\mathit{l}} : {{\mathit{t}}_{{1}}^\ast}~{{\mathit{t}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast}
} \, {[\textsc{\scriptsize T{-}br}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{label}[{\mathit{l}}] = {{\mathit{t}}^\ast}
}{
{\mathit{C}} \vdash \mathsf{br\_if}~{\mathit{l}} : {{\mathit{t}}^\ast}~\mathsf{i{\scriptstyle32}} \rightarrow {{\mathit{t}}^\ast}
} \, {[\textsc{\scriptsize T{-}br\_if}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
({\mathit{C}} \vdash {{\mathit{t}}^\ast} \leq {\mathit{C}}.\mathsf{label}[{\mathit{l}}])^\ast
 \qquad
{\mathit{C}} \vdash {{\mathit{t}}^\ast} \leq {\mathit{C}}.\mathsf{label}[{\mathit{l}'}]
}{
{\mathit{C}} \vdash \mathsf{br\_table}~{{\mathit{l}}^\ast}~{\mathit{l}'} : {{\mathit{t}}_{{1}}^\ast}~{{\mathit{t}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast}
} \, {[\textsc{\scriptsize T{-}br\_table}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{label}[{\mathit{l}}] = {{\mathit{t}}^\ast}
 \qquad
{\mathit{C}} \vdash {\mathit{ht}} : \mathsf{ok}
}{
{\mathit{C}} \vdash \mathsf{br\_on\_null}~{\mathit{l}} : {{\mathit{t}}^\ast}~(\mathsf{ref}~\mathsf{null}~{\mathit{ht}}) \rightarrow {{\mathit{t}}^\ast}~(\mathsf{ref}~\epsilon~{\mathit{ht}})
} \, {[\textsc{\scriptsize T{-}br\_on\_null}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{label}[{\mathit{l}}] = {{\mathit{t}}^\ast}~(\mathsf{ref}~\epsilon~{\mathit{ht}})
 \qquad
{\mathit{C}} \vdash {\mathit{ht}} : \mathsf{ok}
}{
{\mathit{C}} \vdash \mathsf{br\_on\_non\_null}~{\mathit{l}} : {{\mathit{t}}^\ast}~(\mathsf{ref}~\mathsf{null}~{\mathit{ht}}) \rightarrow {{\mathit{t}}^\ast}
} \, {[\textsc{\scriptsize T{-}br\_on\_non\_null}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{label}[{\mathit{l}}] = {{\mathit{t}}^\ast}~{\mathit{rt}}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}}_{{1}} : \mathsf{ok}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}}_{{2}} : \mathsf{ok}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}}_{{2}} \leq {\mathit{rt}}_{{1}}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}}_{{2}} \leq {\mathit{rt}}
}{
{\mathit{C}} \vdash \mathsf{br\_on\_cast}~{\mathit{l}}~{\mathit{rt}}_{{1}}~{\mathit{rt}}_{{2}} : {{\mathit{t}}^\ast}~{\mathit{rt}}_{{1}} \rightarrow {{\mathit{t}}^\ast}~({\mathit{rt}}_{{1}} - {\mathit{rt}}_{{2}})
} \, {[\textsc{\scriptsize T{-}br\_on\_cast}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{label}[{\mathit{l}}] = {{\mathit{t}}^\ast}~{\mathit{rt}}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}}_{{1}} : \mathsf{ok}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}}_{{2}} : \mathsf{ok}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}}_{{2}} \leq {\mathit{rt}}_{{1}}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}}_{{1}} - {\mathit{rt}}_{{2}} \leq {\mathit{rt}}
}{
{\mathit{C}} \vdash \mathsf{br\_on\_cast}~{\mathit{l}}~{\mathit{rt}}_{{1}}~{\mathit{rt}}_{{2}} : {{\mathit{t}}^\ast}~{\mathit{rt}}_{{1}} \rightarrow {{\mathit{t}}^\ast}~{\mathit{rt}}_{{2}}
} \, {[\textsc{\scriptsize T{-}br\_on\_cast\_fail}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{return} = ({{\mathit{t}}^\ast})
}{
{\mathit{C}} \vdash \mathsf{return} : {{\mathit{t}}_{{1}}^\ast}~{{\mathit{t}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast}
} \, {[\textsc{\scriptsize T{-}return}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{func}[{\mathit{x}}] \approx \mathsf{func}~({{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast})
}{
{\mathit{C}} \vdash \mathsf{call}~{\mathit{x}} : {{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast}
} \, {[\textsc{\scriptsize T{-}call}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{func}~({{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast})
}{
{\mathit{C}} \vdash \mathsf{call\_ref}~{\mathit{x}} : {{\mathit{t}}_{{1}}^\ast}~(\mathsf{ref}~\mathsf{null}~{\mathit{x}}) \rightarrow {{\mathit{t}}_{{2}}^\ast}
} \, {[\textsc{\scriptsize T{-}call\_ref}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{table}[{\mathit{x}}] = {\mathit{lim}}~{\mathit{rt}}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}} \leq (\mathsf{ref}~\mathsf{null}~\mathsf{func})
 \qquad
{\mathit{C}}.\mathsf{type}[{\mathit{y}}] \approx \mathsf{func}~({{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast})
}{
{\mathit{C}} \vdash \mathsf{call\_indirect}~{\mathit{x}}~{\mathit{y}} : {{\mathit{t}}_{{1}}^\ast}~\mathsf{i{\scriptstyle32}} \rightarrow {{\mathit{t}}_{{2}}^\ast}
} \, {[\textsc{\scriptsize T{-}call\_indirect}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{func}[{\mathit{x}}] \approx \mathsf{func}~({{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast})
 \qquad
{\mathit{C}}.\mathsf{return} = ({{\mathit{t}'}_{{2}}^\ast})
 \qquad
{\mathit{C}} \vdash {{\mathit{t}}_{{2}}^\ast} \leq {{\mathit{t}'}_{{2}}^\ast}
}{
{\mathit{C}} \vdash \mathsf{return\_call}~{\mathit{x}} : {{\mathit{t}}_{{3}}^\ast}~{{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{4}}^\ast}
} \, {[\textsc{\scriptsize T{-}return\_call}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{func}~({{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast})
 \qquad
{\mathit{C}}.\mathsf{return} = ({{\mathit{t}'}_{{2}}^\ast})
 \qquad
{\mathit{C}} \vdash {{\mathit{t}}_{{2}}^\ast} \leq {{\mathit{t}'}_{{2}}^\ast}
}{
{\mathit{C}} \vdash \mathsf{return\_call\_ref}~{\mathit{x}} : {{\mathit{t}}_{{3}}^\ast}~{{\mathit{t}}_{{1}}^\ast}~(\mathsf{ref}~\mathsf{null}~{\mathit{x}}) \rightarrow {{\mathit{t}}_{{4}}^\ast}
} \, {[\textsc{\scriptsize T{-}return\_call\_ref}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{table}[{\mathit{x}}] = {\mathit{lim}}~{\mathit{rt}}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}} \leq (\mathsf{ref}~\mathsf{null}~\mathsf{func})
 \qquad
{\mathit{C}}.\mathsf{type}[{\mathit{y}}] \approx \mathsf{func}~({{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast})
 \qquad
{\mathit{C}}.\mathsf{return} = ({{\mathit{t}'}_{{2}}^\ast})
 \qquad
{\mathit{C}} \vdash {{\mathit{t}}_{{2}}^\ast} \leq {{\mathit{t}'}_{{2}}^\ast}
}{
{\mathit{C}} \vdash \mathsf{return\_call\_indirect}~{\mathit{x}}~{\mathit{y}} : {{\mathit{t}}_{{3}}^\ast}~{{\mathit{t}}_{{1}}^\ast}~\mathsf{i{\scriptstyle32}} \rightarrow {{\mathit{t}}_{{4}}^\ast}
} \, {[\textsc{\scriptsize T{-}return\_call\_indirect}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash {\mathit{nt}}.\mathsf{const}~{\mathit{c}}_{{\mathit{nt}}} : \epsilon \rightarrow {\mathit{nt}}
} \, {[\textsc{\scriptsize T{-}const}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash {\mathit{nt}} . {\mathit{unop}} : {\mathit{nt}} \rightarrow {\mathit{nt}}
} \, {[\textsc{\scriptsize T{-}unop}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash {\mathit{nt}} . {\mathit{binop}} : {\mathit{nt}}~{\mathit{nt}} \rightarrow {\mathit{nt}}
} \, {[\textsc{\scriptsize T{-}binop}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash {\mathit{nt}} . {\mathit{testop}} : {\mathit{nt}} \rightarrow \mathsf{i{\scriptstyle32}}
} \, {[\textsc{\scriptsize T{-}testop}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash {\mathit{nt}} . {\mathit{relop}} : {\mathit{nt}}~{\mathit{nt}} \rightarrow \mathsf{i{\scriptstyle32}}
} \, {[\textsc{\scriptsize T{-}relop}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{n}} \leq {|{\mathit{nt}}|}
}{
{\mathit{C}} \vdash {{\mathit{nt}}.\mathsf{extend}}{{\mathit{n}}} : {\mathit{nt}} \rightarrow {\mathit{nt}}
} \, {[\textsc{\scriptsize T{-}extend}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{nt}}_{{1}} \neq {\mathit{nt}}_{{2}}
 \qquad
{|{\mathit{nt}}_{{1}}|} = {|{\mathit{nt}}_{{2}}|}
}{
{\mathit{C}} \vdash \mathsf{cvtop}~{\mathit{nt}}_{{1}}~\mathsf{reinterpret}~{\mathit{nt}}_{{2}} : {\mathit{nt}}_{{2}} \rightarrow {\mathit{nt}}_{{1}}
} \, {[\textsc{\scriptsize T{-}reinterpret}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{{\mathsf{i}}{{\mathit{n}}}}_{{1}} \neq {{\mathsf{i}}{{\mathit{n}}}}_{{2}}
 \qquad
{{\mathit{sx}}^?} = \epsilon \Leftrightarrow {|{{\mathsf{i}}{{\mathit{n}}}}_{{1}}|} > {|{{\mathsf{i}}{{\mathit{n}}}}_{{2}}|}
}{
{\mathit{C}} \vdash {{\mathsf{i}}{{\mathit{n}}}}_{{1}} . {{{{\mathsf{convert}}{\mathsf{\_}}}{{{\mathsf{i}}{{\mathit{n}}}}_{{2}}}}{\mathsf{\_}}}{{{\mathit{sx}}^?}} : {{\mathsf{i}}{{\mathit{n}}}}_{{2}} \rightarrow {{\mathsf{i}}{{\mathit{n}}}}_{{1}}
} \, {[\textsc{\scriptsize T{-}convert{-}i}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{{\mathsf{f}}{{\mathit{n}}}}_{{1}} \neq {{\mathsf{f}}{{\mathit{n}}}}_{{2}}
}{
{\mathit{C}} \vdash \mathsf{cvtop}~{{\mathsf{f}}{{\mathit{n}}}}_{{1}}~\mathsf{convert}~{{\mathsf{f}}{{\mathit{n}}}}_{{2}} : {{\mathsf{f}}{{\mathit{n}}}}_{{2}} \rightarrow {{\mathsf{f}}{{\mathit{n}}}}_{{1}}
} \, {[\textsc{\scriptsize T{-}convert{-}f}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{ht}} : \mathsf{ok}
}{
{\mathit{C}} \vdash \mathsf{ref.null}~{\mathit{ht}} : \epsilon \rightarrow (\mathsf{ref}~\mathsf{null}~{\mathit{ht}})
} \, {[\textsc{\scriptsize T{-}ref.null}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{func}[{\mathit{x}}] = {\mathit{dt}}
}{
{\mathit{C}} \vdash \mathsf{ref.func}~{\mathit{x}} : \epsilon \rightarrow (\mathsf{ref}~\epsilon~{\mathit{dt}})
} \, {[\textsc{\scriptsize T{-}ref.func}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{ref.i{\scriptstyle31}} : \mathsf{i{\scriptstyle32}} \rightarrow (\mathsf{ref}~\epsilon~\mathsf{i{\scriptstyle31}})
} \, {[\textsc{\scriptsize T{-}ref.i31}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{ref.is\_null} : {\mathit{rt}} \rightarrow \mathsf{i{\scriptstyle32}}
} \, {[\textsc{\scriptsize T{-}ref.is\_null}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{ht}} : \mathsf{ok}
}{
{\mathit{C}} \vdash \mathsf{ref.as\_non\_null} : (\mathsf{ref}~\mathsf{null}~{\mathit{ht}}) \rightarrow (\mathsf{ref}~\epsilon~{\mathit{ht}})
} \, {[\textsc{\scriptsize T{-}ref.as\_non\_null}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{ref.eq} : (\mathsf{ref}~\mathsf{null}~\mathsf{eq})~(\mathsf{ref}~\mathsf{null}~\mathsf{eq}) \rightarrow \mathsf{i{\scriptstyle32}}
} \, {[\textsc{\scriptsize T{-}ref.eq}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{rt}} : \mathsf{ok}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}'} : \mathsf{ok}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}} \leq {\mathit{rt}'}
}{
{\mathit{C}} \vdash \mathsf{ref.test}~{\mathit{rt}} : {\mathit{rt}'} \rightarrow \mathsf{i{\scriptstyle32}}
} \, {[\textsc{\scriptsize T{-}ref.test}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{rt}} : \mathsf{ok}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}'} : \mathsf{ok}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}} \leq {\mathit{rt}'}
}{
{\mathit{C}} \vdash \mathsf{ref.cast}~{\mathit{rt}} : {\mathit{rt}'} \rightarrow {\mathit{rt}}
} \, {[\textsc{\scriptsize T{-}ref.cast}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash {{\mathsf{i{\scriptstyle31}.get}}{\mathsf{\_}}}{{\mathit{sx}}} : (\mathsf{ref}~\mathsf{null}~\mathsf{i{\scriptstyle31}}) \rightarrow \mathsf{i{\scriptstyle32}}
} \, {[\textsc{\scriptsize T{-}i31.get}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{struct}~{({\mathit{mut}}~{\mathit{zt}})^\ast}
}{
{\mathit{C}} \vdash \mathsf{struct.new}~{\mathit{x}} : {{\mathrm{unpack}}({\mathit{zt}})^\ast} \rightarrow (\mathsf{ref}~\epsilon~{\mathit{x}})
} \, {[\textsc{\scriptsize T{-}struct.new}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{struct}~{({\mathit{mut}}~{\mathit{zt}})^\ast}
 \qquad
(({{\mathrm{default}}}_{{\mathrm{unpack}}({\mathit{zt}})} = {\mathit{val}}))^\ast
}{
{\mathit{C}} \vdash \mathsf{struct.new\_default}~{\mathit{x}} : {{\mathrm{unpack}}({\mathit{zt}})^\ast} \rightarrow (\mathsf{ref}~\epsilon~{\mathit{x}})
} \, {[\textsc{\scriptsize T{-}struct.new\_default}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{struct}~{{\mathit{yt}}^\ast}
 \qquad
{{\mathit{yt}}^\ast}[{\mathit{i}}] = {\mathit{mut}}~{\mathit{zt}}
 \qquad
{{\mathit{sx}}^?} = \epsilon \Leftrightarrow {\mathit{zt}} = {\mathrm{unpack}}({\mathit{zt}})
}{
{\mathit{C}} \vdash {{\mathsf{struct.get}}{\mathsf{\_}}}{{{\mathit{sx}}^?}}~{\mathit{x}}~{\mathit{i}} : (\mathsf{ref}~\mathsf{null}~{\mathit{x}}) \rightarrow {\mathrm{unpack}}({\mathit{zt}})
} \, {[\textsc{\scriptsize T{-}struct.get}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{struct}~{{\mathit{yt}}^\ast}
 \qquad
{{\mathit{yt}}^\ast}[{\mathit{i}}] = \mathsf{mut}~{\mathit{zt}}
}{
{\mathit{C}} \vdash \mathsf{struct.set}~{\mathit{x}}~{\mathit{i}} : (\mathsf{ref}~\mathsf{null}~{\mathit{x}})~{\mathrm{unpack}}({\mathit{zt}}) \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}struct.set}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{array}~({\mathit{mut}}~{\mathit{zt}})
}{
{\mathit{C}} \vdash \mathsf{array.new}~{\mathit{x}} : {\mathrm{unpack}}({\mathit{zt}})~\mathsf{i{\scriptstyle32}} \rightarrow (\mathsf{ref}~\epsilon~{\mathit{x}})
} \, {[\textsc{\scriptsize T{-}array.new}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{array}~({\mathit{mut}}~{\mathit{zt}})
 \qquad
{{\mathrm{default}}}_{{\mathrm{unpack}}({\mathit{zt}})} = {\mathit{val}}
}{
{\mathit{C}} \vdash \mathsf{array.new\_default}~{\mathit{x}} : \mathsf{i{\scriptstyle32}} \rightarrow (\mathsf{ref}~\epsilon~{\mathit{x}})
} \, {[\textsc{\scriptsize T{-}array.new\_default}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{array}~({\mathit{mut}}~{\mathit{zt}})
}{
{\mathit{C}} \vdash \mathsf{array.new\_fixed}~{\mathit{x}}~{\mathit{n}} : {\mathrm{unpack}}({\mathit{zt}}) \rightarrow (\mathsf{ref}~\epsilon~{\mathit{x}})
} \, {[\textsc{\scriptsize T{-}array.new\_fixed}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{array}~({\mathit{mut}}~{\mathit{rt}})
 \qquad
{\mathit{C}} \vdash {\mathit{C}}.\mathsf{elem}[{\mathit{y}}] \leq {\mathit{rt}}
}{
{\mathit{C}} \vdash \mathsf{array.new\_elem}~{\mathit{x}}~{\mathit{y}} : \mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle32}} \rightarrow (\mathsf{ref}~\epsilon~{\mathit{x}})
} \, {[\textsc{\scriptsize T{-}array.new\_elem}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{array}~({\mathit{mut}}~{\mathit{t}})
 \qquad
{\mathit{t}} = {\mathit{numtype}} \lor {\mathit{t}} = {\mathit{vectype}}
 \qquad
{\mathit{C}}.\mathsf{data}[{\mathit{y}}] = \mathsf{ok}
}{
{\mathit{C}} \vdash \mathsf{array.new\_data}~{\mathit{x}}~{\mathit{y}} : \mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle32}} \rightarrow (\mathsf{ref}~\epsilon~{\mathit{x}})
} \, {[\textsc{\scriptsize T{-}array.new\_data}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{array}~({\mathit{mut}}~{\mathit{zt}})
 \qquad
{{\mathit{sx}}^?} = \epsilon \Leftrightarrow {\mathit{zt}} = {\mathrm{unpack}}({\mathit{zt}})
}{
{\mathit{C}} \vdash {{\mathsf{array.get}}{\mathsf{\_}}}{{{\mathit{sx}}^?}}~{\mathit{x}} : (\mathsf{ref}~\mathsf{null}~{\mathit{x}})~\mathsf{i{\scriptstyle32}} \rightarrow {\mathrm{unpack}}({\mathit{zt}})
} \, {[\textsc{\scriptsize T{-}array.get}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{array}~(\mathsf{mut}~{\mathit{zt}})
}{
{\mathit{C}} \vdash \mathsf{array.set}~{\mathit{x}} : (\mathsf{ref}~\mathsf{null}~{\mathit{x}})~\mathsf{i{\scriptstyle32}}~{\mathrm{unpack}}({\mathit{zt}}) \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}array.set}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{array}~(\mathsf{mut}~{\mathit{zt}})
}{
{\mathit{C}} \vdash \mathsf{array.len} : (\mathsf{ref}~\mathsf{null}~\mathsf{array}) \rightarrow \mathsf{i{\scriptstyle32}}
} \, {[\textsc{\scriptsize T{-}array.len}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{array}~(\mathsf{mut}~{\mathit{zt}})
}{
{\mathit{C}} \vdash \mathsf{array.fill}~{\mathit{x}} : (\mathsf{ref}~\mathsf{null}~{\mathit{x}})~\mathsf{i{\scriptstyle32}}~{\mathrm{unpack}}({\mathit{zt}})~\mathsf{i{\scriptstyle32}} \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}array.fill}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}_{{1}}] \approx \mathsf{array}~(\mathsf{mut}~{\mathit{zt}}_{{1}})
 \qquad
{\mathit{C}}.\mathsf{type}[{\mathit{x}}_{{2}}] \approx \mathsf{array}~({\mathit{mut}}~{\mathit{zt}}_{{2}})
 \qquad
{\mathit{C}} \vdash {\mathit{zt}}_{{2}} \leq {\mathit{zt}}_{{1}}
}{
{\mathit{C}} \vdash \mathsf{array.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}} : (\mathsf{ref}~\mathsf{null}~{\mathit{x}}_{{1}})~\mathsf{i{\scriptstyle32}}~(\mathsf{ref}~\mathsf{null}~{\mathit{x}}_{{2}})~\mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle32}} \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}array.copy}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{array}~(\mathsf{mut}~{\mathit{zt}})
 \qquad
{\mathit{C}} \vdash {\mathit{C}}.\mathsf{elem}[{\mathit{y}}] \leq {\mathit{zt}}
}{
{\mathit{C}} \vdash \mathsf{array.init\_elem}~{\mathit{x}}~{\mathit{y}} : (\mathsf{ref}~\mathsf{null}~{\mathit{x}})~\mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle32}} \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}array.init\_elem}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{array}~(\mathsf{mut}~{\mathit{zt}})
 \qquad
{\mathit{t}} = {\mathit{numtype}} \lor {\mathit{t}} = {\mathit{vectype}}
 \qquad
{\mathit{C}}.\mathsf{data}[{\mathit{y}}] = \mathsf{ok}
}{
{\mathit{C}} \vdash \mathsf{array.init\_data}~{\mathit{x}}~{\mathit{y}} : (\mathsf{ref}~\mathsf{null}~{\mathit{x}})~\mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle32}} \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}array.init\_data}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{extern.externalize} : (\mathsf{ref}~{\mathit{nul}}~\mathsf{any}) \rightarrow (\mathsf{ref}~{\mathit{nul}}~\mathsf{extern})
} \, {[\textsc{\scriptsize T{-}extern.externalize}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{extern.internalize} : (\mathsf{ref}~{\mathit{nul}}~\mathsf{extern}) \rightarrow (\mathsf{ref}~{\mathit{nul}}~\mathsf{any})
} \, {[\textsc{\scriptsize T{-}extern.internalize}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{local}[{\mathit{x}}] = {\mathit{init}}~{\mathit{t}}
}{
{\mathit{C}} \vdash \mathsf{local.get}~{\mathit{x}} : \epsilon \rightarrow {\mathit{t}}
} \, {[\textsc{\scriptsize T{-}local.get}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{local}[{\mathit{x}}] = {\mathit{init}}~{\mathit{t}}
}{
{\mathit{C}} \vdash \mathsf{local.set}~{\mathit{x}} : {\mathit{t}} \rightarrow ({\mathit{x}})~\epsilon
} \, {[\textsc{\scriptsize T{-}local.set}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{local}[{\mathit{x}}] = {\mathit{init}}~{\mathit{t}}
}{
{\mathit{C}} \vdash \mathsf{local.tee}~{\mathit{x}} : {\mathit{t}} \rightarrow ({\mathit{x}})~{\mathit{t}}
} \, {[\textsc{\scriptsize T{-}local.tee}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{global}[{\mathit{x}}] = {\mathit{mut}}~{\mathit{t}}
}{
{\mathit{C}} \vdash \mathsf{global.get}~{\mathit{x}} : \epsilon \rightarrow {\mathit{t}}
} \, {[\textsc{\scriptsize T{-}global.get}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{global}[{\mathit{x}}] = \mathsf{mut}~{\mathit{t}}
}{
{\mathit{C}} \vdash \mathsf{global.set}~{\mathit{x}} : {\mathit{t}} \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}global.set}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{table}[{\mathit{x}}] = {\mathit{lim}}~{\mathit{rt}}
}{
{\mathit{C}} \vdash \mathsf{table.get}~{\mathit{x}} : \mathsf{i{\scriptstyle32}} \rightarrow {\mathit{rt}}
} \, {[\textsc{\scriptsize T{-}table.get}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{table}[{\mathit{x}}] = {\mathit{lim}}~{\mathit{rt}}
}{
{\mathit{C}} \vdash \mathsf{table.set}~{\mathit{x}} : \mathsf{i{\scriptstyle32}}~{\mathit{rt}} \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}table.set}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{table}[{\mathit{x}}] = {\mathit{tt}}
}{
{\mathit{C}} \vdash \mathsf{table.size}~{\mathit{x}} : \epsilon \rightarrow \mathsf{i{\scriptstyle32}}
} \, {[\textsc{\scriptsize T{-}table.size}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{table}[{\mathit{x}}] = {\mathit{lim}}~{\mathit{rt}}
}{
{\mathit{C}} \vdash \mathsf{table.grow}~{\mathit{x}} : {\mathit{rt}}~\mathsf{i{\scriptstyle32}} \rightarrow \mathsf{i{\scriptstyle32}}
} \, {[\textsc{\scriptsize T{-}table.grow}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{table}[{\mathit{x}}] = {\mathit{lim}}~{\mathit{rt}}
}{
{\mathit{C}} \vdash \mathsf{table.fill}~{\mathit{x}} : \mathsf{i{\scriptstyle32}}~{\mathit{rt}}~\mathsf{i{\scriptstyle32}} \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}table.fill}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{table}[{\mathit{x}}_{{1}}] = {\mathit{lim}}_{{1}}~{\mathit{rt}}_{{1}}
 \qquad
{\mathit{C}}.\mathsf{table}[{\mathit{x}}_{{2}}] = {\mathit{lim}}_{{2}}~{\mathit{rt}}_{{2}}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}}_{{2}} \leq {\mathit{rt}}_{{1}}
}{
{\mathit{C}} \vdash \mathsf{table.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}} : \mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle32}} \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}table.copy}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{table}[{\mathit{x}}] = {\mathit{lim}}~{\mathit{rt}}_{{1}}
 \qquad
{\mathit{C}}.\mathsf{elem}[{\mathit{y}}] = {\mathit{rt}}_{{2}}
 \qquad
{\mathit{C}} \vdash {\mathit{rt}}_{{2}} \leq {\mathit{rt}}_{{1}}
}{
{\mathit{C}} \vdash \mathsf{table.init}~{\mathit{x}}~{\mathit{y}} : \mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle32}} \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}table.init}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{elem}[{\mathit{x}}] = {\mathit{rt}}
}{
{\mathit{C}} \vdash \mathsf{elem.drop}~{\mathit{x}} : \epsilon \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}elem.drop}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{mem}[{\mathit{x}}] = {\mathit{mt}}
}{
{\mathit{C}} \vdash \mathsf{memory.size}~{\mathit{x}} : \epsilon \rightarrow \mathsf{i{\scriptstyle32}}
} \, {[\textsc{\scriptsize T{-}memory.size}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{mem}[{\mathit{x}}] = {\mathit{mt}}
}{
{\mathit{C}} \vdash \mathsf{memory.grow}~{\mathit{x}} : \mathsf{i{\scriptstyle32}} \rightarrow \mathsf{i{\scriptstyle32}}
} \, {[\textsc{\scriptsize T{-}memory.grow}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{mem}[{\mathit{x}}] = {\mathit{mt}}
}{
{\mathit{C}} \vdash \mathsf{memory.fill}~{\mathit{x}} : \mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle32}} \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}memory.fill}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{mem}[{\mathit{x}}_{{1}}] = {\mathit{mt}}_{{1}}
 \qquad
{\mathit{C}}.\mathsf{mem}[{\mathit{x}}_{{2}}] = {\mathit{mt}}_{{2}}
}{
{\mathit{C}} \vdash \mathsf{memory.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}} : \mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle32}} \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}memory.copy}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{mem}[{\mathit{x}}] = {\mathit{mt}}
 \qquad
{\mathit{C}}.\mathsf{data}[{\mathit{y}}] = \mathsf{ok}
}{
{\mathit{C}} \vdash \mathsf{memory.init}~{\mathit{x}}~{\mathit{y}} : \mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle32}} \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}memory.init}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{data}[{\mathit{x}}] = \mathsf{ok}
}{
{\mathit{C}} \vdash \mathsf{data.drop}~{\mathit{x}} : \epsilon \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}data.drop}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{mem}[{\mathit{x}}] = {\mathit{mt}}
 \qquad
{2^{{\mathit{n}}_{{\mathsf{a}}}}} \leq {|{\mathit{nt}}|} / 8
 \qquad
({2^{{\mathit{n}}_{{\mathsf{a}}}}} \leq {\mathit{n}} / 8 < {|{\mathit{nt}}|} / 8)^?
 \qquad
{{\mathit{n}}^?} = \epsilon \lor {\mathit{nt}} = {{\mathsf{i}}{{\mathit{n}}}}
}{
{\mathit{C}} \vdash {{\mathit{nt}}.\mathsf{load}}{{({{{\mathit{n}}}{\mathsf{\_}}}{{\mathit{sx}}})^?}}~{\mathit{x}}~{\mathit{n}}_{{\mathsf{a}}}~{\mathit{n}}_{{\mathsf{o}}} : \mathsf{i{\scriptstyle32}} \rightarrow {\mathit{nt}}
} \, {[\textsc{\scriptsize T{-}load}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{mem}[{\mathit{x}}] = {\mathit{mt}}
 \qquad
{2^{{\mathit{n}}_{{\mathsf{a}}}}} \leq {|{\mathit{nt}}|} / 8
 \qquad
({2^{{\mathit{n}}_{{\mathsf{a}}}}} \leq {\mathit{n}} / 8 < {|{\mathit{nt}}|} / 8)^?
 \qquad
{{\mathit{n}}^?} = \epsilon \lor {\mathit{nt}} = {{\mathsf{i}}{{\mathit{n}}}}
}{
{\mathit{C}} \vdash {{\mathit{nt}}.\mathsf{store}}{{{\mathit{n}}^?}}~{\mathit{x}}~{\mathit{n}}_{{\mathsf{a}}}~{\mathit{n}}_{{\mathsf{o}}} : \mathsf{i{\scriptstyle32}}~{\mathit{nt}} \rightarrow \epsilon
} \, {[\textsc{\scriptsize T{-}store}]}
\qquad
\end{array}
$$

\vspace{1ex}

$\boxed{{\mathit{context}} \vdash {\mathit{instr}}~\mathsf{const}}$

$\boxed{{\mathit{context}} \vdash {\mathit{expr}}~\mathsf{const}}$

$\boxed{{\mathit{context}} \vdash {\mathit{expr}} : {\mathit{valtype}}~\mathsf{const}}$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash ({\mathit{nt}}.\mathsf{const}~{\mathit{c}})~\mathsf{const}
} \, {[\textsc{\scriptsize C{-}instr{-}const}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash (\mathsf{ref.null}~{\mathit{ht}})~\mathsf{const}
} \, {[\textsc{\scriptsize C{-}instr{-}ref.null}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash (\mathsf{ref.func}~{\mathit{x}})~\mathsf{const}
} \, {[\textsc{\scriptsize C{-}instr{-}ref.func}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{global}[{\mathit{x}}] = \epsilon~{\mathit{t}}
}{
{\mathit{C}} \vdash (\mathsf{global.get}~{\mathit{x}})~\mathsf{const}
} \, {[\textsc{\scriptsize C{-}instr{-}global.get}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathit{nt}} \in \epsilon &=& \mathsf{false} &  \\
{\mathit{nt}} \in {\mathit{nt}}_{{1}}~{{\mathit{nt}'}^\ast} &=& {\mathit{nt}} = {\mathit{nt}}_{{1}} \lor {\mathit{nt}} \in {{\mathit{nt}'}^\ast} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathit{binop}} \in \epsilon &=& \mathsf{false} &  \\
{\mathit{binop}} \in {{\mathit{binop}}_{{\mathsf{ixx}}}}_{{1}}~{{{\mathit{binop}}_{{\mathsf{ixx}}}'}^\ast} &=& {\mathit{binop}} = {{\mathit{binop}}_{{\mathsf{ixx}}}}_{{1}} \lor {\mathit{binop}} \in {{{\mathit{binop}}_{{\mathsf{ixx}}}'}^\ast} &  \\
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{nt}} \in \mathsf{i{\scriptstyle32}}~\mathsf{i{\scriptstyle64}}
 \qquad
{\mathit{binop}} \in \mathsf{add}~\mathsf{sub}~\mathsf{mul}
}{
{\mathit{C}} \vdash ({\mathit{nt}} . {\mathit{binop}})~\mathsf{const}
} \, {[\textsc{\scriptsize C{-}instr{-}binop}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
({\mathit{C}} \vdash {\mathit{instr}}~\mathsf{const})^\ast
}{
{\mathit{C}} \vdash {{\mathit{instr}}^\ast}~\mathsf{const}
} \, {[\textsc{\scriptsize C{-}expr}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{expr}} : {\mathit{t}}
 \qquad
{\mathit{C}} \vdash {\mathit{expr}}~\mathsf{const}
}{
{\mathit{C}} \vdash {\mathit{expr}} : {\mathit{t}}~\mathsf{const}
} \, {[\textsc{\scriptsize TC{-}expr}]}
\qquad
\end{array}
$$

\vspace{1ex}

$\boxed{{\mathit{context}} \vdash {\mathit{type}} : {{\mathit{deftype}}^\ast}}$

$\boxed{{\mathit{context}} \vdash {\mathit{func}} : {\mathit{deftype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{local}} : {\mathit{localtype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{global}} : {\mathit{globaltype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{table}} : {\mathit{tabletype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{mem}} : {\mathit{memtype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{elem}} : {\mathit{reftype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{data}} : \mathsf{ok}}$

$\boxed{{\mathit{context}} \vdash {\mathit{elemmode}} : {\mathit{reftype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{datamode}} : \mathsf{ok}}$

$\boxed{{\mathit{context}} \vdash {\mathit{start}} : \mathsf{ok}}$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{x}} = {|{\mathit{C}}.\mathsf{type}|}
 \qquad
{{\mathit{dt}}^\ast} = {{\mathrm{roll}}}_{{\mathit{x}}}({\mathit{rectype}})
 \qquad
{\mathit{C}}[\mathsf{type} = ..{{\mathit{dt}}^\ast}] \vdash {\mathit{rectype}} : {\mathsf{ok}}{({\mathit{x}})}
}{
{\mathit{C}} \vdash \mathsf{type}~{\mathit{rectype}} : {{\mathit{dt}}^\ast}
} \, {[\textsc{\scriptsize T{-}type}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{{\mathrm{default}}}_{{\mathit{t}}} \neq \epsilon
}{
{\mathit{C}} \vdash \mathsf{local}~{\mathit{t}} : \mathsf{set}~{\mathit{t}}
} \, {[\textsc{\scriptsize T{-}local{-}set}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{{\mathrm{default}}}_{{\mathit{t}}} = \epsilon
}{
{\mathit{C}} \vdash \mathsf{local}~{\mathit{t}} : \mathsf{unset}~{\mathit{t}}
} \, {[\textsc{\scriptsize T{-}local{-}unset}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{type}[{\mathit{x}}] \approx \mathsf{func}~({{\mathit{t}}_{{1}}^\ast} \rightarrow {{\mathit{t}}_{{2}}^\ast})
 \qquad
({\mathit{C}} \vdash {\mathit{local}} : {\mathit{lt}})^\ast
 \qquad
{\mathit{C}}, \mathsf{local}~{(\mathsf{set}~{\mathit{t}}_{{1}})^\ast}~{{\mathit{lt}}^\ast}, \mathsf{label}~({{\mathit{t}}_{{2}}^\ast}), \mathsf{return}~({{\mathit{t}}_{{2}}^\ast}) \vdash {\mathit{expr}} : {{\mathit{t}}_{{2}}^\ast}
}{
{\mathit{C}} \vdash \mathsf{func}~{\mathit{x}}~{{\mathit{local}}^\ast}~{\mathit{expr}} : {\mathit{C}}.\mathsf{type}[{\mathit{x}}]
} \, {[\textsc{\scriptsize T{-}func}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{gt}} : \mathsf{ok}
 \qquad
{\mathit{gt}} = {\mathit{mut}}~{\mathit{t}}
 \qquad
{\mathit{C}} \vdash {\mathit{expr}} : {\mathit{t}}~\mathsf{const}
}{
{\mathit{C}} \vdash \mathsf{global}~{\mathit{gt}}~{\mathit{expr}} : {\mathit{gt}}
} \, {[\textsc{\scriptsize T{-}global}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{tt}} : \mathsf{ok}
}{
{\mathit{C}} \vdash \mathsf{table}~{\mathit{tt}} : {\mathit{tt}}
} \, {[\textsc{\scriptsize T{-}table}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{mt}} : \mathsf{ok}
}{
{\mathit{C}} \vdash \mathsf{memory}~{\mathit{mt}} : {\mathit{mt}}
} \, {[\textsc{\scriptsize T{-}mem}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
({\mathit{C}} \vdash {\mathit{expr}} : {\mathit{rt}})^\ast
 \qquad
({\mathit{C}} \vdash {\mathit{elemmode}} : {\mathit{rt}})^?
}{
{\mathit{C}} \vdash \mathsf{elem}~{\mathit{rt}}~{{\mathit{expr}}^\ast}~{{\mathit{elemmode}}^?} : {\mathit{rt}}
} \, {[\textsc{\scriptsize T{-}elem}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
({\mathit{C}} \vdash {\mathit{datamode}} : \mathsf{ok})^?
}{
{\mathit{C}} \vdash \mathsf{data}~{{\mathit{b}}^\ast}~{{\mathit{datamode}}^?} : \mathsf{ok}
} \, {[\textsc{\scriptsize T{-}data}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{table}[{\mathit{x}}] = {\mathit{lim}}~{\mathit{rt}}
 \qquad
({\mathit{C}} \vdash {\mathit{expr}} : \mathsf{i{\scriptstyle32}}~\mathsf{const})^\ast
}{
{\mathit{C}} \vdash \mathsf{table}~{\mathit{x}}~{\mathit{expr}} : {\mathit{rt}}
} \, {[\textsc{\scriptsize T{-}elemmode{-}active}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \mathsf{declare} : {\mathit{rt}}
} \, {[\textsc{\scriptsize T{-}elemmode{-}declare}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{mem}[{\mathit{x}}] = {\mathit{mt}}
 \qquad
({\mathit{C}} \vdash {\mathit{expr}} : \mathsf{i{\scriptstyle32}}~\mathsf{const})^\ast
}{
{\mathit{C}} \vdash \mathsf{memory}~{\mathit{x}}~{\mathit{expr}} : \mathsf{ok}
} \, {[\textsc{\scriptsize T{-}datamode}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{func}[{\mathit{x}}] \approx \mathsf{func}~(\epsilon \rightarrow \epsilon)
}{
{\mathit{C}} \vdash \mathsf{start}~{\mathit{x}} : \mathsf{ok}
} \, {[\textsc{\scriptsize T{-}start}]}
\qquad
\end{array}
$$

\vspace{1ex}

$\boxed{{\mathit{context}} \vdash {\mathit{import}} : {\mathit{externtype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{export}} : {\mathit{externtype}}}$

$\boxed{{\mathit{context}} \vdash {\mathit{externuse}} : {\mathit{externtype}}}$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{xt}} : \mathsf{ok}
}{
{\mathit{C}} \vdash \mathsf{import}~{\mathit{name}}_{{1}}~{\mathit{name}}_{{2}}~{\mathit{xt}} : {\mathit{xt}}
} \, {[\textsc{\scriptsize T{-}import}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{externuse}} : {\mathit{xt}}
}{
{\mathit{C}} \vdash \mathsf{export}~{\mathit{name}}~{\mathit{externuse}} : {\mathit{xt}}
} \, {[\textsc{\scriptsize T{-}export}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{func}[{\mathit{x}}] = {\mathit{dt}}
}{
{\mathit{C}} \vdash \mathsf{func}~{\mathit{x}} : \mathsf{func}~{\mathit{dt}}
} \, {[\textsc{\scriptsize T{-}externuse{-}func}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{global}[{\mathit{x}}] = {\mathit{gt}}
}{
{\mathit{C}} \vdash \mathsf{global}~{\mathit{x}} : \mathsf{global}~{\mathit{gt}}
} \, {[\textsc{\scriptsize T{-}externuse{-}global}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{table}[{\mathit{x}}] = {\mathit{tt}}
}{
{\mathit{C}} \vdash \mathsf{table}~{\mathit{x}} : \mathsf{table}~{\mathit{tt}}
} \, {[\textsc{\scriptsize T{-}externuse{-}table}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}}.\mathsf{mem}[{\mathit{x}}] = {\mathit{mt}}
}{
{\mathit{C}} \vdash \mathsf{mem}~{\mathit{x}} : \mathsf{mem}~{\mathit{mt}}
} \, {[\textsc{\scriptsize T{-}externuse{-}mem}]}
\qquad
\end{array}
$$

\vspace{1ex}

$\boxed{{ \vdash }\;{\mathit{module}} : \mathsf{ok}}$

$\boxed{{\mathit{context}} \vdash {{\mathit{type}}^\ast} : {{\mathit{deftype}}^\ast}}$

$\boxed{{\mathit{context}} \vdash {{\mathit{global}}^\ast} : {{\mathit{globaltype}}^\ast}}$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
\begin{array}{@{}c@{}}
\{ \begin{array}[t]{@{}l@{}}
 \}\end{array} \vdash {{\mathit{type}}^\ast} : {{\mathit{dt}'}^\ast}
 \qquad
(\{ \begin{array}[t]{@{}l@{}}
\mathsf{type}~{{\mathit{dt}'}^\ast} \}\end{array} \vdash {\mathit{import}} : {\mathit{ixt}})^\ast
 \\
{\mathit{C}'} \vdash {{\mathit{global}}^\ast} : {{\mathit{gt}}^\ast}
 \qquad
({\mathit{C}'} \vdash {\mathit{table}} : {\mathit{tt}})^\ast
 \qquad
({\mathit{C}'} \vdash {\mathit{mem}} : {\mathit{mt}})^\ast
 \qquad
({\mathit{C}} \vdash {\mathit{func}} : {\mathit{dt}})^\ast
 \\
({\mathit{C}} \vdash {\mathit{elem}} : {\mathit{rt}})^\ast
 \qquad
({\mathit{C}} \vdash {\mathit{data}} : \mathsf{ok})^{{\mathit{n}}}
 \qquad
({\mathit{C}} \vdash {\mathit{start}} : \mathsf{ok})^?
 \qquad
({\mathit{C}} \vdash {\mathit{export}} : {\mathit{et}})^\ast
 \\
{\mathit{C}} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{type}~{{\mathit{dt}'}^\ast},\; \mathsf{func}~{{\mathit{idt}}^\ast}~{{\mathit{dt}}^\ast},\; \mathsf{global}~{{\mathit{igt}}^\ast}~{{\mathit{gt}}^\ast},\; \mathsf{table}~{{\mathit{itt}}^\ast}~{{\mathit{tt}}^\ast},\; \mathsf{mem}~{{\mathit{imt}}^\ast}~{{\mathit{mt}}^\ast},\; \mathsf{elem}~{{\mathit{rt}}^\ast},\; \mathsf{data}~{\mathsf{ok}^{{\mathit{n}}}} \}\end{array}
 \\
{\mathit{C}'} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{type}~{{\mathit{dt}'}^\ast},\; \mathsf{func}~{{\mathit{idt}}^\ast}~{{\mathit{dt}}^\ast},\; \mathsf{global}~{{\mathit{igt}}^\ast} \}\end{array}
 \\
{{\mathit{idt}}^\ast} = {\mathrm{funcs}}({{\mathit{ixt}}^\ast})
 \qquad
{{\mathit{igt}}^\ast} = {\mathrm{globals}}({{\mathit{ixt}}^\ast})
 \qquad
{{\mathit{itt}}^\ast} = {\mathrm{tables}}({{\mathit{ixt}}^\ast})
 \qquad
{{\mathit{imt}}^\ast} = {\mathrm{mems}}({{\mathit{ixt}}^\ast})
\end{array}
}{
{ \vdash }\;\mathsf{module}~{{\mathit{type}}^\ast}~{{\mathit{import}}^\ast}~{{\mathit{func}}^\ast}~{{\mathit{global}}^\ast}~{{\mathit{table}}^\ast}~{{\mathit{mem}}^\ast}~{{\mathit{elem}}^\ast}~{{\mathit{data}}^{{\mathit{n}}}}~{{\mathit{start}}^?}~{{\mathit{export}}^\ast} : \mathsf{ok}
} \, {[\textsc{\scriptsize T{-}module}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \epsilon : \epsilon
} \, {[\textsc{\scriptsize T{-}types{-}empty}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{type}}_{{1}} : {\mathit{dt}}_{{1}}
 \qquad
{\mathit{C}}[\mathsf{type} = ..{{\mathit{dt}}_{{1}}^\ast}] \vdash {{\mathit{type}}^\ast} : {{\mathit{dt}}^\ast}
}{
{\mathit{C}} \vdash {\mathit{type}}_{{1}}~{{\mathit{type}}^\ast} : {{\mathit{dt}}_{{1}}^\ast}~{{\mathit{dt}}^\ast}
} \, {[\textsc{\scriptsize T{-}types{-}cons}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{C}} \vdash \epsilon : \epsilon
} \, {[\textsc{\scriptsize T{-}globals{-}empty}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{C}} \vdash {\mathit{global}} : {\mathit{gt}}_{{1}}
 \qquad
{\mathit{C}}[\mathsf{global} = ..{\mathit{gt}}_{{1}}] \vdash {{\mathit{global}}^\ast} : {{\mathit{gt}}^\ast}
}{
{\mathit{C}} \vdash {\mathit{global}}_{{1}}~{{\mathit{global}}^\ast} : {\mathit{gt}}_{{1}}~{{\mathit{gt}}^\ast}
} \, {[\textsc{\scriptsize T{-}globals{-}cons}]}
\qquad
\end{array}
$$

$\boxed{{\mathit{store}} \vdash {\mathit{ref}} : {\mathit{reftype}}}$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{s}} \vdash \mathsf{ref.null}~{\mathit{ht}} : (\mathsf{ref}~\mathsf{null}~{\mathit{ht}})
} \, {[\textsc{\scriptsize Ref\_ok{-}null}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{s}} \vdash \mathsf{ref.i{\scriptstyle31}}~{\mathit{i}} : (\mathsf{ref}~\epsilon~\mathsf{i{\scriptstyle31}})
} \, {[\textsc{\scriptsize Ref\_ok{-}i31}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{s}}.\mathsf{struct}[{\mathit{a}}].\mathsf{type} = {\mathit{dt}}
}{
{\mathit{s}} \vdash \mathsf{ref.struct}~{\mathit{a}} : (\mathsf{ref}~\epsilon~{\mathit{dt}})
} \, {[\textsc{\scriptsize Ref\_ok{-}struct}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{s}}.\mathsf{array}[{\mathit{a}}].\mathsf{type} = {\mathit{dt}}
}{
{\mathit{s}} \vdash \mathsf{ref.array}~{\mathit{a}} : (\mathsf{ref}~\epsilon~{\mathit{dt}})
} \, {[\textsc{\scriptsize Ref\_ok{-}array}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{\mathit{s}}.\mathsf{func}[{\mathit{a}}].\mathsf{type} = {\mathit{dt}}
}{
{\mathit{s}} \vdash \mathsf{ref.func}~{\mathit{a}} : (\mathsf{ref}~\epsilon~{\mathit{dt}})
} \, {[\textsc{\scriptsize Ref\_ok{-}func}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{s}} \vdash \mathsf{ref.host}~{\mathit{a}} : (\mathsf{ref}~\epsilon~\mathsf{any})
} \, {[\textsc{\scriptsize Ref\_ok{-}host}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{\mathit{s}} \vdash \mathsf{ref.extern}~{\mathit{addrref}} : (\mathsf{ref}~\epsilon~\mathsf{extern})
} \, {[\textsc{\scriptsize Ref\_ok{-}extern}]}
\qquad
\end{array}
$$

$\boxed{{\mathit{config}} \hookrightarrow {\mathit{config}}}$

$\boxed{{{{\mathit{instr}}}^\ast} \hookrightarrow {{{\mathit{instr}}}^\ast}}$

$\boxed{{\mathit{config}} \hookrightarrow {{{\mathit{instr}}}^\ast}}$

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}pure}]} \quad & {\mathit{z}} ; {{\mathit{instr}}^\ast} &\hookrightarrow& {\mathit{z}} ; {{\mathit{instr}'}^\ast} &\quad
  \mbox{if}~{{\mathit{instr}}^\ast} \hookrightarrow {{\mathit{instr}'}^\ast} \\
{[\textsc{\scriptsize E{-}read}]} \quad & {\mathit{z}} ; {{\mathit{instr}}^\ast} &\hookrightarrow& {\mathit{z}} ; {{\mathit{instr}'}^\ast} &\quad
  \mbox{if}~{\mathit{z}} ; {{\mathit{instr}}^\ast} \hookrightarrow {{\mathit{instr}'}^\ast} \\
\end{array}
$$

\vspace{1ex}

$\boxed{{\mathit{config}} \hookrightarrow^\ast {\mathit{state}} ; {{\mathit{val}}^\ast}}$

$\boxed{{\mathit{state}} ; {\mathit{expr}} \hookrightarrow^\ast {\mathit{state}} ; {{\mathit{val}}^\ast}}$

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}expr{-}done}]} \quad & {\mathit{z}} ; {{\mathit{val}}^\ast} &\hookrightarrow^\ast& {\mathit{z}} ; {{\mathit{val}}^\ast} &  \\
{[\textsc{\scriptsize E{-}expr{-}step}]} \quad & {\mathit{z}} ; {{{\mathit{instr}}}^\ast} &\hookrightarrow^\ast& {\mathit{z}''} ; {{\mathit{val}}^\ast} &\quad
  \mbox{if}~{\mathit{z}} ; {{{\mathit{instr}}}^\ast} \hookrightarrow {\mathit{z}'} ; {{{\mathit{instr}}'}^\ast} \\
 &&&&\quad {\land}~{\mathit{z}'} ; {{\mathit{instr}}'} \hookrightarrow^\ast {\mathit{z}''} ; {{\mathit{val}}^\ast} \\
\end{array}
$$

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}expr}]} \quad & {\mathit{z}} ; {{\mathit{instr}}^\ast} &\hookrightarrow^\ast& {\mathit{z}'} ; {{\mathit{val}}^\ast} &\quad
  \mbox{if}~{\mathit{z}} ; {{\mathit{instr}}^\ast} \hookrightarrow^\ast {\mathit{z}} ; {{\mathit{val}}^\ast} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}unreachable}]} \quad & \mathsf{unreachable} &\hookrightarrow& \mathsf{trap} &  \\
{[\textsc{\scriptsize E{-}nop}]} \quad & \mathsf{nop} &\hookrightarrow& \epsilon &  \\
{[\textsc{\scriptsize E{-}drop}]} \quad & {\mathit{val}}~\mathsf{drop} &\hookrightarrow& \epsilon &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}select{-}true}]} \quad & {\mathit{val}}_{{1}}~{\mathit{val}}_{{2}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{c}})~(\mathsf{select}~{{\mathit{t}}^?}) &\hookrightarrow& {\mathit{val}}_{{1}} &\quad
  \mbox{if}~{\mathit{c}} \neq 0 \\
{[\textsc{\scriptsize E{-}select{-}false}]} \quad & {\mathit{val}}_{{1}}~{\mathit{val}}_{{2}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{c}})~(\mathsf{select}~{{\mathit{t}}^?}) &\hookrightarrow& {\mathit{val}}_{{2}} &\quad
  \mbox{if}~{\mathit{c}} = 0 \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}block}]} \quad & {{\mathit{val}}^{{\mathit{k}}}}~(\mathsf{block}~{\mathit{bt}}~{{\mathit{instr}}^\ast}) &\hookrightarrow& ({{\mathsf{label}}_{{\mathit{n}}}}{\{\epsilon\}}~{{\mathit{val}}^{{\mathit{k}}}}~{{\mathit{instr}}^\ast}) &\quad
  \mbox{if}~{\mathit{bt}} = {{\mathit{t}}_{{1}}^{{\mathit{k}}}} \rightarrow {{\mathit{t}}_{{2}}^{{\mathit{n}}}} \\
{[\textsc{\scriptsize E{-}loop}]} \quad & {{\mathit{val}}^{{\mathit{k}}}}~(\mathsf{loop}~{\mathit{bt}}~{{\mathit{instr}}^\ast}) &\hookrightarrow& ({{\mathsf{label}}_{{\mathit{k}}}}{\{\mathsf{loop}~{\mathit{bt}}~{{\mathit{instr}}^\ast}\}}~{{\mathit{val}}^{{\mathit{k}}}}~{{\mathit{instr}}^\ast}) &\quad
  \mbox{if}~{\mathit{bt}} = {{\mathit{t}}_{{1}}^{{\mathit{k}}}} \rightarrow {{\mathit{t}}_{{2}}^{{\mathit{n}}}} \\
{[\textsc{\scriptsize E{-}if{-}true}]} \quad & (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{c}})~(\mathsf{if}~{\mathit{bt}}~{{\mathit{instr}}_{{1}}^\ast}~\mathsf{else}~{{\mathit{instr}}_{{2}}^\ast}) &\hookrightarrow& (\mathsf{block}~{\mathit{bt}}~{{\mathit{instr}}_{{1}}^\ast}) &\quad
  \mbox{if}~{\mathit{c}} \neq 0 \\
{[\textsc{\scriptsize E{-}if{-}false}]} \quad & (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{c}})~(\mathsf{if}~{\mathit{bt}}~{{\mathit{instr}}_{{1}}^\ast}~\mathsf{else}~{{\mathit{instr}}_{{2}}^\ast}) &\hookrightarrow& (\mathsf{block}~{\mathit{bt}}~{{\mathit{instr}}_{{2}}^\ast}) &\quad
  \mbox{if}~{\mathit{c}} = 0 \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}label{-}vals}]} \quad & ({{\mathsf{label}}_{{\mathit{n}}}}{\{{{\mathit{instr}}^\ast}\}}~{{\mathit{val}}^\ast}) &\hookrightarrow& {{\mathit{val}}^\ast} &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}br{-}zero}]} \quad & ({{\mathsf{label}}_{{\mathit{n}}}}{\{{{\mathit{instr}'}^\ast}\}}~{{\mathit{val}'}^\ast}~{{\mathit{val}}^{{\mathit{n}}}}~(\mathsf{br}~0)~{{\mathit{instr}}^\ast}) &\hookrightarrow& {{\mathit{val}}^{{\mathit{n}}}}~{{\mathit{instr}'}^\ast} &  \\
{[\textsc{\scriptsize E{-}br{-}succ}]} \quad & ({{\mathsf{label}}_{{\mathit{n}}}}{\{{{\mathit{instr}'}^\ast}\}}~{{\mathit{val}}^\ast}~(\mathsf{br}~{\mathit{l}} + 1)~{{\mathit{instr}}^\ast}) &\hookrightarrow& {{\mathit{val}}^\ast}~(\mathsf{br}~{\mathit{l}}) &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}br\_if{-}true}]} \quad & (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{c}})~(\mathsf{br\_if}~{\mathit{l}}) &\hookrightarrow& (\mathsf{br}~{\mathit{l}}) &\quad
  \mbox{if}~{\mathit{c}} \neq 0 \\
{[\textsc{\scriptsize E{-}br\_if{-}false}]} \quad & (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{c}})~(\mathsf{br\_if}~{\mathit{l}}) &\hookrightarrow& \epsilon &\quad
  \mbox{if}~{\mathit{c}} = 0 \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}br\_table{-}lt}]} \quad & (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{br\_table}~{{\mathit{l}}^\ast}~{\mathit{l}'}) &\hookrightarrow& (\mathsf{br}~{{\mathit{l}}^\ast}[{\mathit{i}}]) &\quad
  \mbox{if}~{\mathit{i}} < {|{{\mathit{l}}^\ast}|} \\
{[\textsc{\scriptsize E{-}br\_table{-}ge}]} \quad & (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{br\_table}~{{\mathit{l}}^\ast}~{\mathit{l}'}) &\hookrightarrow& (\mathsf{br}~{\mathit{l}'}) &\quad
  \mbox{if}~{\mathit{i}} \geq {|{{\mathit{l}}^\ast}|} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}br\_on\_null{-}null}]} \quad & {\mathit{val}}~(\mathsf{br\_on\_null}~{\mathit{l}}) &\hookrightarrow& (\mathsf{br}~{\mathit{l}}) &\quad
  \mbox{if}~{\mathit{val}} = \mathsf{ref.null}~{\mathit{ht}} \\
{[\textsc{\scriptsize E{-}br\_on\_null{-}addr}]} \quad & {\mathit{val}}~(\mathsf{br\_on\_null}~{\mathit{l}}) &\hookrightarrow& {\mathit{val}} &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}br\_on\_non\_null{-}null}]} \quad & {\mathit{val}}~(\mathsf{br\_on\_non\_null}~{\mathit{l}}) &\hookrightarrow& \epsilon &\quad
  \mbox{if}~{\mathit{val}} = \mathsf{ref.null}~{\mathit{ht}} \\
{[\textsc{\scriptsize E{-}br\_on\_non\_null{-}addr}]} \quad & {\mathit{val}}~(\mathsf{br\_on\_non\_null}~{\mathit{l}}) &\hookrightarrow& {\mathit{val}}~(\mathsf{br}~{\mathit{l}}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}br\_on\_cast{-}succeed}]} \quad & {\mathit{z}} ; {\mathit{ref}}~(\mathsf{br\_on\_cast}~{\mathit{l}}~{\mathit{rt}}_{{1}}~{\mathit{rt}}_{{2}}) &\hookrightarrow& {\mathit{ref}}~(\mathsf{br}~{\mathit{l}}) &\quad
  \mbox{if}~{\mathit{z}}.\mathsf{store} \vdash {\mathit{ref}} : {\mathit{rt}} \\
 &&&&\quad {\land}~\{ \begin{array}[t]{@{}l@{}}
 \}\end{array} \vdash {\mathit{rt}} \leq {{\mathrm{inst}}}_{{\mathit{z}}.\mathsf{module}}({\mathit{rt}}_{{2}}) \\
{[\textsc{\scriptsize E{-}br\_on\_cast{-}fail}]} \quad & {\mathit{z}} ; {\mathit{ref}}~(\mathsf{br\_on\_cast}~{\mathit{l}}~{\mathit{rt}}_{{1}}~{\mathit{rt}}_{{2}}) &\hookrightarrow& {\mathit{ref}} &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}br\_on\_cast\_fail{-}succeed}]} \quad & {\mathit{z}} ; {\mathit{ref}}~(\mathsf{br\_on\_cast\_fail}~{\mathit{l}}~{\mathit{rt}}_{{1}}~{\mathit{rt}}_{{2}}) &\hookrightarrow& {\mathit{ref}} &\quad
  \mbox{if}~{\mathit{z}}.\mathsf{store} \vdash {\mathit{ref}} : {\mathit{rt}} \\
 &&&&\quad {\land}~\{ \begin{array}[t]{@{}l@{}}
 \}\end{array} \vdash {\mathit{rt}} \leq {{\mathrm{inst}}}_{{\mathit{z}}.\mathsf{module}}({\mathit{rt}}_{{2}}) \\
{[\textsc{\scriptsize E{-}br\_on\_cast\_fail{-}fail}]} \quad & {\mathit{z}} ; {\mathit{ref}}~(\mathsf{br\_on\_cast\_fail}~{\mathit{l}}~{\mathit{rt}}_{{1}}~{\mathit{rt}}_{{2}}) &\hookrightarrow& {\mathit{ref}}~(\mathsf{br}~{\mathit{l}}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}call}]} \quad & {\mathit{z}} ; (\mathsf{call}~{\mathit{x}}) &\hookrightarrow& (\mathsf{call\_ref}~{\mathit{z}}.\mathsf{module}.\mathsf{func}[{\mathit{x}}]) &  \\
{[\textsc{\scriptsize E{-}call\_ref{-}null}]} \quad & {\mathit{z}} ; (\mathsf{ref.null}~{\mathit{ht}})~(\mathsf{call\_ref}~{\mathit{x}}) &\hookrightarrow& \mathsf{trap} &  \\
{[\textsc{\scriptsize E{-}call\_ref{-}func}]} \quad & {\mathit{z}} ; {{\mathit{val}}^{{\mathit{n}}}}~(\mathsf{ref.func}~{\mathit{a}})~(\mathsf{call\_ref}~{\mathit{x}}) &\hookrightarrow& ({{\mathsf{frame}}_{{\mathit{m}}}}{\{{\mathit{f}}\}}~({{\mathsf{label}}_{{\mathit{m}}}}{\{\epsilon\}}~{{\mathit{instr}}^\ast})) &\quad
  \mbox{if}~{\mathit{z}}.\mathsf{func}[{\mathit{a}}] = {\mathit{fi}} \\
 &&&&\quad {\land}~{\mathit{fi}}.\mathsf{type} \approx \mathsf{func}~({{\mathit{t}}_{{1}}^{{\mathit{n}}}} \rightarrow {{\mathit{t}}_{{2}}^{{\mathit{m}}}}) \\
 &&&&\quad {\land}~{\mathit{fi}}.\mathsf{code} = \mathsf{func}~{\mathit{x}}~{(\mathsf{local}~{\mathit{t}})^\ast}~({{\mathit{instr}}^\ast}) \\
 &&&&\quad {\land}~{\mathit{f}} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{local}~{{\mathit{val}}^{{\mathit{n}}}}~{({{\mathrm{default}}}_{{\mathit{t}}})^\ast},\; \mathsf{module}~{\mathit{fi}}.\mathsf{module} \}\end{array} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}return\_call}]} \quad & {\mathit{z}} ; (\mathsf{return\_call}~{\mathit{x}}) &\hookrightarrow& (\mathsf{return\_call\_ref}~{\mathit{z}}.\mathsf{module}.\mathsf{func}[{\mathit{x}}]) &  \\
{[\textsc{\scriptsize E{-}return\_call\_ref{-}frame}]} \quad & {\mathit{z}} ; ({{\mathsf{frame}}_{{\mathit{k}}}}{\{{\mathit{f}}\}}~{{\mathit{val}'}^\ast}~{{\mathit{val}}^{{\mathit{n}}}}~{\mathit{ref}}~(\mathsf{return\_call\_ref}~{\mathit{x}})~{{\mathit{instr}}^\ast}) &\hookrightarrow& {{\mathit{val}}^{{\mathit{n}}}}~{\mathit{ref}}~(\mathsf{call\_ref}~{\mathit{x}}) &\quad
  \mbox{if}~{\mathit{z}}.\mathsf{func}[{\mathit{a}}].\mathsf{type} \approx \mathsf{func}~({{\mathit{t}}_{{1}}^{{\mathit{n}}}} \rightarrow {{\mathit{t}}_{{2}}^{{\mathit{m}}}}) \\
{[\textsc{\scriptsize E{-}return\_call\_ref{-}label}]} \quad & {\mathit{z}} ; ({{\mathsf{label}}_{{\mathit{k}}}}{\{{{\mathit{instr}'}^\ast}\}}~{{\mathit{val}'}^\ast}~{{\mathit{val}}^{{\mathit{n}}}}~{\mathit{ref}}~(\mathsf{return\_call\_ref}~{\mathit{x}})~{{\mathit{instr}}^\ast}) &\hookrightarrow& {{\mathit{val}}^{{\mathit{n}}}}~{\mathit{ref}}~(\mathsf{return\_call\_ref}~{\mathit{x}}) &\quad
  \mbox{if}~{\mathit{z}}.\mathsf{func}[{\mathit{a}}].\mathsf{type} \approx \mathsf{func}~({{\mathit{t}}_{{1}}^{{\mathit{n}}}} \rightarrow {{\mathit{t}}_{{2}}^{{\mathit{m}}}}) \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}call\_indirect{-}call}]} \quad & (\mathsf{call\_indirect}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& (\mathsf{table.get}~{\mathit{x}})~(\mathsf{ref.cast}~(\mathsf{ref}~\mathsf{null}~{\mathit{y}}))~(\mathsf{call\_ref}~{\mathit{y}}) &  \\
{[\textsc{\scriptsize E{-}return\_call\_indirect}]} \quad & (\mathsf{return\_call\_indirect}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& (\mathsf{table.get}~{\mathit{x}})~(\mathsf{ref.cast}~(\mathsf{ref}~\mathsf{null}~{\mathit{y}}))~(\mathsf{return\_call\_ref}~{\mathit{y}}) &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}frame{-}vals}]} \quad & ({{\mathsf{frame}}_{{\mathit{n}}}}{\{{\mathit{f}}\}}~{{\mathit{val}}^{{\mathit{n}}}}) &\hookrightarrow& {{\mathit{val}}^{{\mathit{n}}}} &  \\
{[\textsc{\scriptsize E{-}return{-}frame}]} \quad & ({{\mathsf{frame}}_{{\mathit{n}}}}{\{{\mathit{f}}\}}~{{\mathit{val}'}^\ast}~{{\mathit{val}}^{{\mathit{n}}}}~\mathsf{return}~{{\mathit{instr}}^\ast}) &\hookrightarrow& {{\mathit{val}}^{{\mathit{n}}}} &  \\
{[\textsc{\scriptsize E{-}return{-}label}]} \quad & ({{\mathsf{label}}_{{\mathit{k}}}}{\{{{\mathit{instr}'}^\ast}\}}~{{\mathit{val}}^\ast}~\mathsf{return}~{{\mathit{instr}}^\ast}) &\hookrightarrow& {{\mathit{val}}^\ast}~\mathsf{return} &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}unop{-}val}]} \quad & ({\mathit{nt}}.\mathsf{const}~{\mathit{c}}_{{1}})~({\mathit{nt}} . {\mathit{unop}}) &\hookrightarrow& ({\mathit{nt}}.\mathsf{const}~{\mathit{c}}) &\quad
  \mbox{if}~{{{{\mathit{unop}}}{}}_{{\mathit{nt}}}}{({\mathit{c}}_{{1}})} = {\mathit{c}} \\
{[\textsc{\scriptsize E{-}unop{-}trap}]} \quad & ({\mathit{nt}}.\mathsf{const}~{\mathit{c}}_{{1}})~({\mathit{nt}} . {\mathit{unop}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{{{{\mathit{unop}}}{}}_{{\mathit{nt}}}}{({\mathit{c}}_{{1}})} = \epsilon \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}binop{-}val}]} \quad & ({\mathit{nt}}.\mathsf{const}~{\mathit{c}}_{{1}})~({\mathit{nt}}.\mathsf{const}~{\mathit{c}}_{{2}})~({\mathit{nt}} . {\mathit{binop}}) &\hookrightarrow& ({\mathit{nt}}.\mathsf{const}~{\mathit{c}}) &\quad
  \mbox{if}~{{{{\mathit{binop}}}{}}_{{\mathit{nt}}}}{({\mathit{c}}_{{1}},\, {\mathit{c}}_{{2}})} = {\mathit{c}} \\
{[\textsc{\scriptsize E{-}binop{-}trap}]} \quad & ({\mathit{nt}}.\mathsf{const}~{\mathit{c}}_{{1}})~({\mathit{nt}}.\mathsf{const}~{\mathit{c}}_{{2}})~({\mathit{nt}} . {\mathit{binop}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{{{{\mathit{binop}}}{}}_{{\mathit{nt}}}}{({\mathit{c}}_{{1}},\, {\mathit{c}}_{{2}})} = \epsilon \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}testop}]} \quad & ({\mathit{nt}}.\mathsf{const}~{\mathit{c}}_{{1}})~({\mathit{nt}} . {\mathit{testop}}) &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{c}}) &\quad
  \mbox{if}~{\mathit{c}} = {{{{\mathit{testop}}}{}}_{{\mathit{nt}}}}{({\mathit{c}}_{{1}})} \\
{[\textsc{\scriptsize E{-}relop}]} \quad & ({\mathit{nt}}.\mathsf{const}~{\mathit{c}}_{{1}})~({\mathit{nt}}.\mathsf{const}~{\mathit{c}}_{{2}})~({\mathit{nt}} . {\mathit{relop}}) &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{c}}) &\quad
  \mbox{if}~{\mathit{c}} = {{{{\mathit{relop}}}{}}_{{\mathit{nt}}}}{({\mathit{c}}_{{1}},\, {\mathit{c}}_{{2}})} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}extend}]} \quad & ({\mathit{nt}}.\mathsf{const}~{\mathit{c}})~({{\mathit{nt}}.\mathsf{extend}}{{\mathit{n}}}) &\hookrightarrow& ({\mathit{nt}}.\mathsf{const}~{{{{\mathrm{ext}}}_{{\mathit{n}},{|{\mathit{nt}}|}}^{\mathsf{s}}}}{({\mathit{c}})}) &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}cvtop{-}val}]} \quad & ({\mathit{nt}}_{{1}}.\mathsf{const}~{\mathit{c}}_{{1}})~({\mathit{nt}}_{{2}} . {{{{{\mathit{cvtop}}}{\mathsf{\_}}}{{\mathit{nt}}_{{1}}}}{\mathsf{\_}}}{{{\mathit{sx}}^?}}) &\hookrightarrow& ({\mathit{nt}}_{{2}}.\mathsf{const}~{\mathit{c}}) &\quad
  \mbox{if}~{{{\mathit{cvtop}}}{{{}_{{\mathit{nt}}_{{1}},{\mathit{nt}}_{{2}}}^{{{\mathit{sx}}^?}}}}}{({\mathit{c}}_{{1}})} = {\mathit{c}} \\
{[\textsc{\scriptsize E{-}cvtop{-}trap}]} \quad & ({\mathit{nt}}_{{1}}.\mathsf{const}~{\mathit{c}}_{{1}})~({\mathit{nt}}_{{2}} . {{{{{\mathit{cvtop}}}{\mathsf{\_}}}{{\mathit{nt}}_{{1}}}}{\mathsf{\_}}}{{{\mathit{sx}}^?}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{{{\mathit{cvtop}}}{{{}_{{\mathit{nt}}_{{1}},{\mathit{nt}}_{{2}}}^{{{\mathit{sx}}^?}}}}}{({\mathit{c}}_{{1}})} = \epsilon \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}ref.func}]} \quad & {\mathit{z}} ; (\mathsf{ref.func}~{\mathit{x}}) &\hookrightarrow& (\mathsf{ref.func}~{\mathit{z}}.\mathsf{module}.\mathsf{func}[{\mathit{x}}]) &  \\
\end{array}
$$

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}ref.i31}]} \quad & (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~\mathsf{ref.i{\scriptstyle31}} &\hookrightarrow& (\mathsf{ref.i{\scriptstyle31}}~{{{\mathrm{wrap}}}_{32,31}}{({\mathit{i}})}) &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}ref.is\_null{-}true}]} \quad & {\mathit{val}}~\mathsf{ref.is\_null} &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~1) &\quad
  \mbox{if}~{\mathit{val}} = (\mathsf{ref.null}~{\mathit{ht}}) \\
{[\textsc{\scriptsize E{-}ref.is\_null{-}false}]} \quad & {\mathit{val}}~\mathsf{ref.is\_null} &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~0) &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}ref.as\_non\_null{-}null}]} \quad & {\mathit{ref}}~\mathsf{ref.as\_non\_null} &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{ref}} = (\mathsf{ref.null}~{\mathit{ht}}) \\
{[\textsc{\scriptsize E{-}ref.as\_non\_null{-}addr}]} \quad & {\mathit{ref}}~\mathsf{ref.as\_non\_null} &\hookrightarrow& {\mathit{ref}} &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}ref.eq{-}null}]} \quad & {\mathit{ref}}_{{1}}~{\mathit{ref}}_{{2}}~\mathsf{ref.eq} &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~1) &\quad
  \mbox{if}~{\mathit{ref}}_{{1}} = \mathsf{ref.null}~{\mathit{ht}}_{{1}} \land {\mathit{ref}}_{{2}} = \mathsf{ref.null}~{\mathit{ht}}_{{2}} \\
{[\textsc{\scriptsize E{-}ref.eq{-}true}]} \quad & {\mathit{ref}}_{{1}}~{\mathit{ref}}_{{2}}~\mathsf{ref.eq} &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~1) &\quad
  \mbox{otherwise, if}~{\mathit{ref}}_{{1}} = {\mathit{ref}}_{{2}} \\
{[\textsc{\scriptsize E{-}ref.eq{-}false}]} \quad & {\mathit{ref}}_{{1}}~{\mathit{ref}}_{{2}}~\mathsf{ref.eq} &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~0) &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}ref.test{-}true}]} \quad & {\mathit{z}} ; {\mathit{ref}}~(\mathsf{ref.test}~{\mathit{rt}}) &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~1) &\quad
  \mbox{if}~{\mathit{z}}.\mathsf{store} \vdash {\mathit{ref}} : {\mathit{rt}'} \\
 &&&&\quad {\land}~\{ \begin{array}[t]{@{}l@{}}
 \}\end{array} \vdash {\mathit{rt}'} \leq {{\mathrm{inst}}}_{{\mathit{z}}.\mathsf{module}}({\mathit{rt}}) \\
{[\textsc{\scriptsize E{-}ref.test{-}false}]} \quad & {\mathit{z}} ; {\mathit{ref}}~(\mathsf{ref.test}~{\mathit{rt}}) &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~0) &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}ref.cast{-}succeed}]} \quad & {\mathit{z}} ; {\mathit{ref}}~(\mathsf{ref.cast}~{\mathit{rt}}) &\hookrightarrow& {\mathit{ref}} &\quad
  \mbox{if}~{\mathit{z}}.\mathsf{store} \vdash {\mathit{ref}} : {\mathit{rt}'} \\
 &&&&\quad {\land}~\{ \begin{array}[t]{@{}l@{}}
 \}\end{array} \vdash {\mathit{rt}'} \leq {{\mathrm{inst}}}_{{\mathit{z}}.\mathsf{module}}({\mathit{rt}}) \\
{[\textsc{\scriptsize E{-}ref.cast{-}fail}]} \quad & {\mathit{z}} ; {\mathit{ref}}~(\mathsf{ref.cast}~{\mathit{rt}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}i31.get{-}null}]} \quad & (\mathsf{ref.null}~{\mathit{ht}})~({{\mathsf{i{\scriptstyle31}.get}}{\mathsf{\_}}}{{\mathit{sx}}}) &\hookrightarrow& \mathsf{trap} &  \\
{[\textsc{\scriptsize E{-}i31.get{-}num}]} \quad & (\mathsf{ref.i{\scriptstyle31}}~{\mathit{i}})~({{\mathsf{i{\scriptstyle31}.get}}{\mathsf{\_}}}{{\mathit{sx}}}) &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{{{{\mathrm{ext}}}_{31,32}^{{\mathit{sx}}}}}{({\mathit{i}})}) &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}struct.new}]} \quad & {\mathit{z}} ; {{\mathit{val}}^{{\mathit{n}}}}~(\mathsf{struct.new}~{\mathit{x}}) &\hookrightarrow& {\mathit{z}}[\mathsf{struct} = ..{\mathit{si}}] ; (\mathsf{ref.struct}~{|{\mathit{z}}.\mathsf{struct}|}) &\quad
  \mbox{if}~{\mathit{z}}.\mathsf{type}~[{\mathit{x}}] \approx \mathsf{struct}~{({\mathit{mut}}~{\mathit{zt}})^{{\mathit{n}}}} \\
 &&&&\quad {\land}~{\mathit{si}} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{type}~{\mathit{z}}.\mathsf{type}~[{\mathit{x}}],\; \mathsf{field}~{({{\mathrm{pack}}}_{{\mathit{zt}}}({\mathit{val}}))^{{\mathit{n}}}} \}\end{array} \\
\end{array}
$$

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}struct.new\_default}]} \quad & {\mathit{z}} ; (\mathsf{struct.new\_default}~{\mathit{x}}) &\hookrightarrow& {{\mathit{val}}^\ast}~(\mathsf{struct.new}~{\mathit{x}}) &\quad
  \mbox{if}~{\mathit{z}}.\mathsf{type}~[{\mathit{x}}] \approx \mathsf{struct}~{({\mathit{mut}}~{\mathit{zt}})^\ast} \\
 &&&&\quad {\land}~(({{\mathrm{default}}}_{{\mathrm{unpack}}({\mathit{zt}})} = {\mathit{val}}))^\ast \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}struct.get{-}null}]} \quad & {\mathit{z}} ; (\mathsf{ref.null}~{\mathit{ht}})~({{\mathsf{struct.get}}{\mathsf{\_}}}{{{\mathit{sx}}^?}}~{\mathit{x}}~{\mathit{i}}) &\hookrightarrow& \mathsf{trap} &  \\
{[\textsc{\scriptsize E{-}struct.get{-}struct}]} \quad & {\mathit{z}} ; (\mathsf{ref.struct}~{\mathit{a}})~({{\mathsf{struct.get}}{\mathsf{\_}}}{{{\mathit{sx}}^?}}~{\mathit{x}}~{\mathit{i}}) &\hookrightarrow& {{{{\mathrm{unpack}}}_{{{\mathit{zt}}^\ast}[{\mathit{i}}]}^{{{\mathit{sx}}^?}}}}{({\mathit{si}}.\mathsf{field}[{\mathit{i}}])} &\quad
  \mbox{if}~{\mathit{z}}.\mathsf{struct}[{\mathit{a}}] = {\mathit{si}} \\
 &&&&\quad {\land}~{\mathit{si}}.\mathsf{type} \approx \mathsf{struct}~{({\mathit{mut}}~{\mathit{zt}})^\ast} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}struct.set{-}null}]} \quad & {\mathit{z}} ; (\mathsf{ref.null}~{\mathit{ht}})~{\mathit{val}}~(\mathsf{struct.set}~{\mathit{x}}~{\mathit{i}}) &\hookrightarrow& {\mathit{z}} ; \mathsf{trap} &  \\
{[\textsc{\scriptsize E{-}struct.set{-}struct}]} \quad & {\mathit{z}} ; (\mathsf{ref.struct}~{\mathit{a}})~{\mathit{val}}~(\mathsf{struct.set}~{\mathit{x}}~{\mathit{i}}) &\hookrightarrow& {\mathrm{with}}_{{\mathit{struct}}}({\mathit{z}},\, {\mathit{a}},\, {\mathit{i}},\, {\mathit{fv}}) ; \epsilon &\quad
  \mbox{if}~{\mathit{z}}.\mathsf{struct}[{\mathit{a}}].\mathsf{type} \approx \mathsf{struct}~{({\mathit{mut}}~{\mathit{zt}})^\ast} \\
 &&&&\quad {\land}~{\mathit{fv}} = {{\mathrm{pack}}}_{{{\mathit{zt}}^\ast}[{\mathit{i}}]}({\mathit{val}}) \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}array.new}]} \quad & {\mathit{z}} ; {\mathit{val}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.new}~{\mathit{x}}) &\hookrightarrow& {{\mathit{val}}^{{\mathit{n}}}}~(\mathsf{array.new\_fixed}~{\mathit{x}}~{\mathit{n}}) &  \\
{[\textsc{\scriptsize E{-}array.new\_default}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.new\_default}~{\mathit{x}}) &\hookrightarrow& {{\mathit{val}}^{{\mathit{n}}}}~(\mathsf{array.new\_fixed}~{\mathit{x}}~{\mathit{n}}) &\quad
  \mbox{if}~{\mathit{z}}.\mathsf{type}~[{\mathit{x}}] \approx \mathsf{array}~({\mathit{mut}}~{\mathit{zt}}) \\
 &&&&\quad {\land}~{{\mathrm{default}}}_{{\mathrm{unpack}}({\mathit{zt}})} = {\mathit{val}} \\
\end{array}
$$

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}array.new\_fixed}]} \quad & {\mathit{z}} ; {{\mathit{val}}^{{\mathit{n}}}}~(\mathsf{array.new\_fixed}~{\mathit{x}}~{\mathit{n}}) &\hookrightarrow& {\mathit{z}}[\mathsf{array} = ..{\mathit{ai}}] ; (\mathsf{ref.array}~{|{\mathit{z}}.\mathsf{array}|}) &\quad
  \mbox{if}~{\mathit{z}}.\mathsf{type}~[{\mathit{x}}] \approx \mathsf{array}~({\mathit{mut}}~{\mathit{zt}}) \\
 &&&&\quad {\land}~{\mathit{ai}} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{type}~{\mathit{z}}.\mathsf{type}~[{\mathit{x}}],\; \mathsf{field}~{({{\mathrm{pack}}}_{{\mathit{zt}}}({\mathit{val}}))^{{\mathit{n}}}} \}\end{array} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}array.new\_elem{-}oob}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.new\_elem}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}} + {\mathit{n}} > {|{{\mathit{z}}.\mathsf{elem}}{[{\mathit{y}}]}.\mathsf{elem}|} \\
{[\textsc{\scriptsize E{-}array.new\_elem{-}alloc}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.new\_elem}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& {{\mathit{ref}}^{{\mathit{n}}}}~(\mathsf{array.new\_fixed}~{\mathit{x}}~{\mathit{n}}) &\quad
  \mbox{if}~{{\mathit{ref}}^{{\mathit{n}}}} = {{\mathit{z}}.\mathsf{elem}}{[{\mathit{y}}]}.\mathsf{elem}[{\mathit{i}} : {\mathit{n}}] \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}array.new\_data{-}oob}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.new\_data}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{z}}.\mathsf{type}~[{\mathit{x}}] \approx \mathsf{array}~({\mathit{mut}}~{\mathit{zt}}) \\
 &&&&\quad {\land}~{\mathit{i}} + {\mathit{n}} \cdot {|{\mathit{zt}}|} / 8 > {|{{\mathit{z}}.\mathsf{data}}{[{\mathit{y}}]}.\mathsf{data}|} \\
{[\textsc{\scriptsize E{-}array.new\_data{-}alloc}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.new\_data}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& {({\mathit{nt}}.\mathsf{const}~{\mathit{c}})^{{\mathit{n}}}}~(\mathsf{array.new\_fixed}~{\mathit{x}}~{\mathit{n}}) &\quad
  \mbox{if}~{\mathit{z}}.\mathsf{type}~[{\mathit{x}}] \approx \mathsf{array}~({\mathit{mut}}~{\mathit{zt}}) \\
 &&&&\quad {\land}~{\mathit{nt}} = {\mathrm{unpack}}({\mathit{zt}}) \\
 &&&&\quad {\land}~{{{{\mathrm{bytes}}}_{{|{\mathit{zt}}|}}}{{\mathit{c}}}^{{\mathit{n}}}} = {{\mathit{z}}.\mathsf{data}}{[{\mathit{y}}]}.\mathsf{data}[{\mathit{i}} : {\mathit{n}} \cdot {|{\mathit{zt}}|} / 8] \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}array.get{-}null}]} \quad & {\mathit{z}} ; (\mathsf{ref.null}~{\mathit{ht}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~({{\mathsf{array.get}}{\mathsf{\_}}}{{{\mathit{sx}}^?}}~{\mathit{x}}) &\hookrightarrow& \mathsf{trap} &  \\
{[\textsc{\scriptsize E{-}array.get{-}oob}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~({{\mathsf{array.get}}{\mathsf{\_}}}{{{\mathit{sx}}^?}}~{\mathit{x}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}} \geq {|{\mathit{z}}.\mathsf{array}[{\mathit{a}}].\mathsf{field}|} \\
{[\textsc{\scriptsize E{-}array.get{-}array}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~({{\mathsf{array.get}}{\mathsf{\_}}}{{{\mathit{sx}}^?}}~{\mathit{x}}) &\hookrightarrow& {{{{\mathrm{unpack}}}_{{\mathit{zt}}}^{{{\mathit{sx}}^?}}}}{({\mathit{fv}})} &\quad
  \mbox{if}~{\mathit{fv}} = {\mathit{z}}.\mathsf{array}[{\mathit{a}}].\mathsf{field}[{\mathit{i}}] \\
 &&&&\quad {\land}~{\mathit{z}}.\mathsf{array}[{\mathit{a}}].\mathsf{type} \approx \mathsf{array}~({\mathit{mut}}~{\mathit{zt}}) \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}array.set{-}null}]} \quad & {\mathit{z}} ; (\mathsf{ref.null}~{\mathit{ht}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{val}}~(\mathsf{array.set}~{\mathit{x}}) &\hookrightarrow& {\mathit{z}} ; \mathsf{trap} &  \\
{[\textsc{\scriptsize E{-}array.set{-}oob}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{val}}~(\mathsf{array.set}~{\mathit{x}}) &\hookrightarrow& {\mathit{z}} ; \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}} \geq {|{\mathit{z}}.\mathsf{array}[{\mathit{a}}].\mathsf{field}|} \\
{[\textsc{\scriptsize E{-}array.set{-}array}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{val}}~(\mathsf{array.set}~{\mathit{x}}) &\hookrightarrow& {\mathrm{with}}_{{\mathit{array}}}({\mathit{z}},\, {\mathit{a}},\, {\mathit{i}},\, {\mathit{fv}}) ; \epsilon &\quad
  \mbox{if}~{\mathit{z}}.\mathsf{array}[{\mathit{a}}].\mathsf{type} \approx \mathsf{array}~({\mathit{mut}}~{\mathit{zt}}) \\
 &&&&\quad {\land}~{\mathit{fv}} = {{\mathrm{pack}}}_{{\mathit{zt}}}({\mathit{val}}) \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}array.len{-}null}]} \quad & {\mathit{z}} ; (\mathsf{ref.null}~{\mathit{ht}})~\mathsf{array.len} &\hookrightarrow& \mathsf{trap} &  \\
{[\textsc{\scriptsize E{-}array.len{-}array}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}})~\mathsf{array.len} &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}}) &\quad
  \mbox{if}~{\mathit{n}} = {|{\mathit{z}}.\mathsf{array}[{\mathit{a}}].\mathsf{field}|} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}array.fill{-}null}]} \quad & {\mathit{z}} ; (\mathsf{ref.null}~{\mathit{ht}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{val}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.fill}~{\mathit{x}}) &\hookrightarrow& \mathsf{trap} &  \\
{[\textsc{\scriptsize E{-}array.fill{-}oob}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{val}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.fill}~{\mathit{x}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}} + {\mathit{n}} > {|{\mathit{z}}.\mathsf{array}[{\mathit{a}}].\mathsf{field}|} \\
{[\textsc{\scriptsize E{-}array.fill{-}zero}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{val}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.fill}~{\mathit{x}}) &\hookrightarrow& \epsilon &\quad
  \mbox{otherwise, if}~{\mathit{n}} = 0 \\
{[\textsc{\scriptsize E{-}array.fill{-}succ}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{val}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.fill}~{\mathit{x}}) &\hookrightarrow& (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{val}}~(\mathsf{array.set}~{\mathit{x}})~(\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}} + 1)~{\mathit{val}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}} - 1)~(\mathsf{array.fill}~{\mathit{x}}) &\quad
  \mbox{otherwise} \\
{[\textsc{\scriptsize E{-}array.copy{-}null1}]} \quad & {\mathit{z}} ; (\mathsf{ref.null}~{\mathit{ht}}_{{1}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}})~{\mathit{ref}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}}) &\hookrightarrow& \mathsf{trap} &  \\
{[\textsc{\scriptsize E{-}array.copy{-}null2}]} \quad & {\mathit{z}} ; {\mathit{ref}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}})~(\mathsf{ref.null}~{\mathit{ht}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}}) &\hookrightarrow& \mathsf{trap} &  \\
{[\textsc{\scriptsize E{-}array.copy{-}oob1}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}}_{{1}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}})~(\mathsf{ref.array}~{\mathit{a}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}}_{{1}} + {\mathit{n}} > {|{\mathit{z}}.\mathsf{array}[{\mathit{a}}_{{1}}].\mathsf{field}|} \\
{[\textsc{\scriptsize E{-}array.copy{-}oob2}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}}_{{1}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}})~(\mathsf{ref.array}~{\mathit{a}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}}_{{2}} + {\mathit{n}} > {|{\mathit{z}}.\mathsf{array}[{\mathit{a}}_{{2}}].\mathsf{field}|} \\
{[\textsc{\scriptsize E{-}array.copy{-}zero}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}}_{{1}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}})~(\mathsf{ref.array}~{\mathit{a}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}}) &\hookrightarrow& \epsilon &\quad
  \mbox{otherwise, if}~{\mathit{n}} = 0 \\
{[\textsc{\scriptsize E{-}array.copy{-}le}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}}_{{1}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}})~(\mathsf{ref.array}~{\mathit{a}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}}) &\hookrightarrow& (\mathsf{ref.array}~{\mathit{a}}_{{1}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}})~(\mathsf{ref.array}~{\mathit{a}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}})~({{\mathsf{array.get}}{\mathsf{\_}}}{{{\mathit{sx}}^?}}~{\mathit{x}}_{{2}})~(\mathsf{array.set}~{\mathit{x}}_{{1}})~(\mathsf{ref.array}~{\mathit{a}}_{{1}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}} + 1)~(\mathsf{ref.array}~{\mathit{a}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}} + 1)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}} - 1)~(\mathsf{array.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}}) &\quad
  \mbox{otherwise, if}~{\mathit{z}}.\mathsf{type}~[{\mathit{x}}_{{2}}] \approx \mathsf{array}~({\mathit{mut}}~{\mathit{zt}}_{{2}}) \\
 &&&&\quad {\land}~{{\mathit{sx}}^?} = {\mathrm{sx}}({\mathit{zt}}_{{2}}) \\
 &&&&\quad {\land}~{\mathit{i}}_{{1}} \leq {\mathit{i}}_{{2}} \\
{[\textsc{\scriptsize E{-}array.copy{-}gt}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}}_{{1}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}})~(\mathsf{ref.array}~{\mathit{a}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}}) &\hookrightarrow& (\mathsf{ref.array}~{\mathit{a}}_{{1}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}} + {\mathit{n}} - 1)~(\mathsf{ref.array}~{\mathit{a}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}} + {\mathit{n}} - 1)~({{\mathsf{array.get}}{\mathsf{\_}}}{{{\mathit{sx}}^?}}~{\mathit{x}}_{{2}})~(\mathsf{array.set}~{\mathit{x}}_{{1}})~(\mathsf{ref.array}~{\mathit{a}}_{{1}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}})~(\mathsf{ref.array}~{\mathit{a}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}} - 1)~(\mathsf{array.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}array.init\_elem{-}null}]} \quad & {\mathit{z}} ; (\mathsf{ref.null}~{\mathit{ht}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.init\_elem}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& \mathsf{trap} &  \\
{[\textsc{\scriptsize E{-}array.init\_elem{-}oob1}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.init\_elem}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}} + {\mathit{n}} > {|{\mathit{z}}.\mathsf{array}[{\mathit{a}}].\mathsf{field}|} \\
{[\textsc{\scriptsize E{-}array.init\_elem{-}oob2}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.init\_elem}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{j}} + {\mathit{n}} > {|{{\mathit{z}}.\mathsf{elem}}{[{\mathit{y}}]}.\mathsf{elem}|} \\
{[\textsc{\scriptsize E{-}array.init\_elem{-}zero}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.init\_elem}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& \epsilon &\quad
  \mbox{otherwise, if}~{\mathit{n}} = 0 \\
{[\textsc{\scriptsize E{-}array.init\_elem{-}succ}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.init\_elem}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{ref}}~(\mathsf{array.set}~{\mathit{x}})~(\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}} + 1)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}} + 1)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}} - 1)~(\mathsf{array.init\_elem}~{\mathit{x}}~{\mathit{y}}) &\quad
  \mbox{otherwise, if}~{\mathit{ref}} = {{\mathit{z}}.\mathsf{elem}}{[{\mathit{y}}]}.\mathsf{elem}[{\mathit{j}}] \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}array.init\_data{-}null}]} \quad & {\mathit{z}} ; (\mathsf{ref.null}~{\mathit{ht}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.init\_data}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& \mathsf{trap} &  \\
{[\textsc{\scriptsize E{-}array.init\_data{-}oob1}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.init\_data}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}} + {\mathit{n}} > {|{\mathit{z}}.\mathsf{array}[{\mathit{a}}].\mathsf{field}|} \\
{[\textsc{\scriptsize E{-}array.init\_data{-}oob2}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.init\_data}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{z}}.\mathsf{type}~[{\mathit{x}}] \approx \mathsf{array}~({\mathit{mut}}~{\mathit{zt}}) \\
 &&&&\quad {\land}~{\mathit{j}} + {\mathit{n}} \cdot {|{\mathit{zt}}|} / 8 > {|{{\mathit{z}}.\mathsf{data}}{[{\mathit{y}}]}.\mathsf{data}|} \\
{[\textsc{\scriptsize E{-}array.init\_data{-}zero}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.init\_data}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& \epsilon &\quad
  \mbox{otherwise, if}~{\mathit{n}} = 0 \\
{[\textsc{\scriptsize E{-}array.init\_data{-}succ}]} \quad & {\mathit{z}} ; (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{array.init\_data}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& (\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~({\mathit{nt}}.\mathsf{const}~{\mathit{c}})~(\mathsf{array.set}~{\mathit{x}})~(\mathsf{ref.array}~{\mathit{a}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}} + 1)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}} + 1)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}} - 1)~(\mathsf{array.init\_data}~{\mathit{x}}~{\mathit{y}}) &\quad
  \mbox{otherwise, if}~{\mathit{z}}.\mathsf{type}~[{\mathit{x}}] \approx \mathsf{array}~({\mathit{mut}}~{\mathit{zt}}) \\
 &&&&\quad {\land}~{\mathit{nt}} = {\mathrm{unpack}}({\mathit{zt}}) \\
 &&&&\quad {\land}~{{{\mathrm{bytes}}}_{{|{\mathit{zt}}|}}}{{\mathit{c}}} = {{\mathit{z}}.\mathsf{data}}{[{\mathit{y}}]}.\mathsf{data}[{\mathit{j}} : {|{\mathit{zt}}|} / 8] \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}extern.externalize{-}null}]} \quad & (\mathsf{ref.null}~{\mathit{ht}})~\mathsf{extern.externalize} &\hookrightarrow& (\mathsf{ref.null}~\mathsf{extern}) &  \\
{[\textsc{\scriptsize E{-}extern.externalize{-}addr}]} \quad & {\mathit{addrref}}~\mathsf{extern.externalize} &\hookrightarrow& (\mathsf{ref.extern}~{\mathit{addrref}}) &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}extern.internalize{-}null}]} \quad & (\mathsf{ref.null}~{\mathit{ht}})~\mathsf{extern.internalize} &\hookrightarrow& (\mathsf{ref.null}~\mathsf{any}) &  \\
{[\textsc{\scriptsize E{-}extern.internalize{-}addr}]} \quad & (\mathsf{ref.extern}~{\mathit{addrref}})~\mathsf{extern.internalize} &\hookrightarrow& {\mathit{addrref}} &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}local.get}]} \quad & {\mathit{z}} ; (\mathsf{local.get}~{\mathit{x}}) &\hookrightarrow& {\mathit{val}} &\quad
  \mbox{if}~{{\mathit{z}}.\mathsf{local}}{[{\mathit{x}}]} = {\mathit{val}} \\
\end{array}
$$

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}local.set}]} \quad & {\mathit{z}} ; {\mathit{val}}~(\mathsf{local.set}~{\mathit{x}}) &\hookrightarrow& {\mathit{z}}[\mathsf{local}[{\mathit{x}}] = {\mathit{val}}] ; \epsilon &  \\
\end{array}
$$

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}local.tee}]} \quad & {\mathit{val}}~(\mathsf{local.tee}~{\mathit{x}}) &\hookrightarrow& {\mathit{val}}~{\mathit{val}}~(\mathsf{local.set}~{\mathit{x}}) &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}global.get}]} \quad & {\mathit{z}} ; (\mathsf{global.get}~{\mathit{x}}) &\hookrightarrow& {{\mathit{z}}.\mathsf{global}}{[{\mathit{x}}]}.\mathsf{value} &  \\
\end{array}
$$

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}global.set}]} \quad & {\mathit{z}} ; {\mathit{val}}~(\mathsf{global.set}~{\mathit{x}}) &\hookrightarrow& {\mathit{z}}[\mathsf{global}[{\mathit{x}}].\mathsf{value} = {\mathit{val}}] ; \epsilon &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}table.get{-}oob}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{table.get}~{\mathit{x}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}} \geq {|{{\mathit{z}}.\mathsf{table}}{[{\mathit{x}}]}.\mathsf{elem}|} \\
{[\textsc{\scriptsize E{-}table.get{-}val}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{table.get}~{\mathit{x}}) &\hookrightarrow& {{\mathit{z}}.\mathsf{table}}{[{\mathit{x}}]}.\mathsf{elem}[{\mathit{i}}] &\quad
  \mbox{if}~{\mathit{i}} < {|{{\mathit{z}}.\mathsf{table}}{[{\mathit{x}}]}.\mathsf{elem}|} \\
\end{array}
$$

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}table.set{-}oob}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{ref}}~(\mathsf{table.set}~{\mathit{x}}) &\hookrightarrow& {\mathit{z}} ; \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}} \geq {|{{\mathit{z}}.\mathsf{table}}{[{\mathit{x}}]}.\mathsf{elem}|} \\
{[\textsc{\scriptsize E{-}table.set{-}val}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{ref}}~(\mathsf{table.set}~{\mathit{x}}) &\hookrightarrow& {\mathit{z}}[\mathsf{table}[{\mathit{x}}].\mathsf{elem}[{\mathit{i}}] = {\mathit{ref}}] ; \epsilon &\quad
  \mbox{if}~{\mathit{i}} < {|{{\mathit{z}}.\mathsf{table}}{[{\mathit{x}}]}.\mathsf{elem}|} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}table.size}]} \quad & {\mathit{z}} ; (\mathsf{table.size}~{\mathit{x}}) &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}}) &\quad
  \mbox{if}~{|{{\mathit{z}}.\mathsf{table}}{[{\mathit{x}}]}.\mathsf{elem}|} = {\mathit{n}} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}table.grow{-}succeed}]} \quad & {\mathit{z}} ; {\mathit{ref}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{table.grow}~{\mathit{x}}) &\hookrightarrow& {\mathit{z}}[\mathsf{table}[{\mathit{x}}] = {\mathit{ti}}] ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{|{{\mathit{z}}.\mathsf{table}}{[{\mathit{x}}]}.\mathsf{elem}|}) &\quad
  \mbox{if}~{\mathrm{growtable}}({{\mathit{z}}.\mathsf{table}}{[{\mathit{x}}]},\, {\mathit{n}},\, {\mathit{ref}}) = {\mathit{ti}} \\
{[\textsc{\scriptsize E{-}table.grow{-}fail}]} \quad & {\mathit{z}} ; {\mathit{ref}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{table.grow}~{\mathit{x}}) &\hookrightarrow& {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~-1) &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}table.fill{-}oob}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{val}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{table.fill}~{\mathit{x}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}} + {\mathit{n}} > {|{{\mathit{z}}.\mathsf{table}}{[{\mathit{x}}]}.\mathsf{elem}|} \\
{[\textsc{\scriptsize E{-}table.fill{-}zero}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{val}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{table.fill}~{\mathit{x}}) &\hookrightarrow& \epsilon &\quad
  \mbox{otherwise, if}~{\mathit{n}} = 0 \\
{[\textsc{\scriptsize E{-}table.fill{-}succ}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{val}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{table.fill}~{\mathit{x}}) &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{val}}~(\mathsf{table.set}~{\mathit{x}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}} + 1)~{\mathit{val}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}} - 1)~(\mathsf{table.fill}~{\mathit{x}}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}table.copy{-}oob}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{table.copy}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}} + {\mathit{n}} > {|{{\mathit{z}}.\mathsf{table}}{[{\mathit{y}}]}.\mathsf{elem}|} \lor {\mathit{j}} + {\mathit{n}} > {|{{\mathit{z}}.\mathsf{table}}{[{\mathit{x}}]}.\mathsf{elem}|} \\
{[\textsc{\scriptsize E{-}table.copy{-}zero}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{table.copy}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& \epsilon &\quad
  \mbox{otherwise, if}~{\mathit{n}} = 0 \\
{[\textsc{\scriptsize E{-}table.copy{-}le}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{table.copy}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{table.get}~{\mathit{y}})~(\mathsf{table.set}~{\mathit{x}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}} + 1)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}} + 1)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}} - 1)~(\mathsf{table.copy}~{\mathit{x}}~{\mathit{y}}) &\quad
  \mbox{otherwise, if}~{\mathit{j}} \leq {\mathit{i}} \\
{[\textsc{\scriptsize E{-}table.copy{-}gt}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{table.copy}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}} + {\mathit{n}} - 1)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}} + {\mathit{n}} - 1)~(\mathsf{table.get}~{\mathit{y}})~(\mathsf{table.set}~{\mathit{x}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}} - 1)~(\mathsf{table.copy}~{\mathit{x}}~{\mathit{y}}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}table.init{-}oob}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{table.init}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}} + {\mathit{n}} > {|{{\mathit{z}}.\mathsf{elem}}{[{\mathit{y}}]}.\mathsf{elem}|} \lor {\mathit{j}} + {\mathit{n}} > {|{{\mathit{z}}.\mathsf{table}}{[{\mathit{x}}]}.\mathsf{elem}|} \\
{[\textsc{\scriptsize E{-}table.init{-}zero}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{table.init}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& \epsilon &\quad
  \mbox{otherwise, if}~{\mathit{n}} = 0 \\
{[\textsc{\scriptsize E{-}table.init{-}succ}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{table.init}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~{{\mathit{z}}.\mathsf{elem}}{[{\mathit{y}}]}.\mathsf{elem}[{\mathit{i}}]~(\mathsf{table.set}~{\mathit{x}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}} + 1)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}} + 1)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}} - 1)~(\mathsf{table.init}~{\mathit{x}}~{\mathit{y}}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}elem.drop}]} \quad & {\mathit{z}} ; (\mathsf{elem.drop}~{\mathit{x}}) &\hookrightarrow& {\mathit{z}}[\mathsf{elem}[{\mathit{x}}].\mathsf{elem} = \epsilon] ; \epsilon &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}load{-}num{-}oob}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{load}~{\mathit{nt}}~{\mathit{x}}~{\mathit{n}}_{{\mathsf{a}}}~{\mathit{n}}_{{\mathsf{o}}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}} + {\mathit{n}}_{{\mathsf{o}}} + {|{\mathit{nt}}|} / 8 > {|{{\mathit{z}}.\mathsf{mem}}{[{\mathit{x}}]}.\mathsf{data}|} \\
{[\textsc{\scriptsize E{-}load{-}num{-}val}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{load}~{\mathit{nt}}~{\mathit{x}}~{\mathit{n}}_{{\mathsf{a}}}~{\mathit{n}}_{{\mathsf{o}}}) &\hookrightarrow& ({\mathit{nt}}.\mathsf{const}~{\mathit{c}}) &\quad
  \mbox{if}~{{{\mathrm{bytes}}}_{{|{\mathit{nt}}|}}}{{\mathit{c}}} = {{\mathit{z}}.\mathsf{mem}}{[{\mathit{x}}]}.\mathsf{data}[{\mathit{i}} + {\mathit{n}}_{{\mathsf{o}}} : {|{\mathit{nt}}|} / 8] \\
{[\textsc{\scriptsize E{-}load{-}pack{-}oob}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~({{\mathit{nt}}.\mathsf{load}}{{{{\mathit{n}}}{\mathsf{\_}}}{{\mathit{sx}}}}~{\mathit{x}}~{\mathit{n}}_{{\mathsf{a}}}~{\mathit{n}}_{{\mathsf{o}}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}} + {\mathit{n}}_{{\mathsf{o}}} + {\mathit{n}} / 8 > {|{{\mathit{z}}.\mathsf{mem}}{[{\mathit{x}}]}.\mathsf{data}|} \\
{[\textsc{\scriptsize E{-}load{-}pack{-}val}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~({{\mathit{nt}}.\mathsf{load}}{{{{\mathit{n}}}{\mathsf{\_}}}{{\mathit{sx}}}}~{\mathit{x}}~{\mathit{n}}_{{\mathsf{a}}}~{\mathit{n}}_{{\mathsf{o}}}) &\hookrightarrow& ({\mathit{nt}}.\mathsf{const}~{{{{\mathrm{ext}}}_{{\mathit{n}},{|{\mathit{nt}}|}}^{{\mathit{sx}}}}}{({\mathit{c}})}) &\quad
  \mbox{if}~{{{\mathrm{bytes}}}_{{\mathit{n}}}}{{\mathit{c}}} = {{\mathit{z}}.\mathsf{mem}}{[{\mathit{x}}]}.\mathsf{data}[{\mathit{i}} + {\mathit{n}}_{{\mathsf{o}}} : {\mathit{n}} / 8] \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}store{-}num{-}oob}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~({\mathit{nt}}.\mathsf{const}~{\mathit{c}})~(\mathsf{store}~{\mathit{nt}}~{\mathit{x}}~{\mathit{n}}_{{\mathsf{a}}}~{\mathit{n}}_{{\mathsf{o}}}) &\hookrightarrow& {\mathit{z}} ; \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}} + {\mathit{n}}_{{\mathsf{o}}} + {|{\mathit{nt}}|} / 8 > {|{{\mathit{z}}.\mathsf{mem}}{[{\mathit{x}}]}.\mathsf{data}|} \\
{[\textsc{\scriptsize E{-}store{-}num{-}val}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~({\mathit{nt}}.\mathsf{const}~{\mathit{c}})~(\mathsf{store}~{\mathit{nt}}~{\mathit{x}}~{\mathit{n}}_{{\mathsf{a}}}~{\mathit{n}}_{{\mathsf{o}}}) &\hookrightarrow& {\mathit{z}}[\mathsf{mem}[{\mathit{x}}].\mathsf{data}[{\mathit{i}} + {\mathit{n}}_{{\mathsf{o}}} : {|{\mathit{nt}}|} / 8] = {{\mathit{b}}^\ast}] ; \epsilon &\quad
  \mbox{if}~{{\mathit{b}}^\ast} = {{{\mathrm{bytes}}}_{{|{\mathit{nt}}|}}}{{\mathit{c}}} \\
{[\textsc{\scriptsize E{-}store{-}pack{-}oob}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~({\mathit{nt}}.\mathsf{const}~{\mathit{c}})~({{\mathit{nt}}.\mathsf{store}}{{\mathit{n}}}~{\mathit{x}}~{\mathit{n}}_{{\mathsf{a}}}~{\mathit{n}}_{{\mathsf{o}}}) &\hookrightarrow& {\mathit{z}} ; \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}} + {\mathit{n}}_{{\mathsf{o}}} + {\mathit{n}} / 8 > {|{{\mathit{z}}.\mathsf{mem}}{[{\mathit{x}}]}.\mathsf{data}|} \\
{[\textsc{\scriptsize E{-}store{-}pack{-}val}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~({\mathit{nt}}.\mathsf{const}~{\mathit{c}})~({{\mathit{nt}}.\mathsf{store}}{{\mathit{n}}}~{\mathit{x}}~{\mathit{n}}_{{\mathsf{a}}}~{\mathit{n}}_{{\mathsf{o}}}) &\hookrightarrow& {\mathit{z}}[\mathsf{mem}[{\mathit{x}}].\mathsf{data}[{\mathit{i}} + {\mathit{n}}_{{\mathsf{o}}} : {\mathit{n}} / 8] = {{\mathit{b}}^\ast}] ; \epsilon &\quad
  \mbox{if}~{{\mathit{b}}^\ast} = {{{\mathrm{bytes}}}_{{\mathit{n}}}}{{{{\mathrm{wrap}}}_{{|{\mathit{nt}}|},{\mathit{n}}}}{({\mathit{c}})}} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}memory.size}]} \quad & {\mathit{z}} ; (\mathsf{memory.size}~{\mathit{x}}) &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}}) &\quad
  \mbox{if}~{\mathit{n}} \cdot 64 \cdot {\mathrm{Ki}} = {|{{\mathit{z}}.\mathsf{mem}}{[{\mathit{x}}]}.\mathsf{data}|} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}memory.grow{-}succeed}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{memory.grow}~{\mathit{x}}) &\hookrightarrow& {\mathit{z}}[\mathsf{mem}[{\mathit{x}}] = {\mathit{mi}}] ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{|{{\mathit{z}}.\mathsf{mem}}{[0]}.\mathsf{data}|} / (64 \cdot {\mathrm{Ki}})) &\quad
  \mbox{if}~{\mathrm{growmemory}}({{\mathit{z}}.\mathsf{mem}}{[{\mathit{x}}]},\, {\mathit{n}}) = {\mathit{mi}} \\
{[\textsc{\scriptsize E{-}memory.grow{-}fail}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{memory.grow}~{\mathit{x}}) &\hookrightarrow& {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~-1) &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}memory.fill{-}oob}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{val}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{memory.fill}~{\mathit{x}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}} + {\mathit{n}} > {|{{\mathit{z}}.\mathsf{mem}}{[{\mathit{x}}]}.\mathsf{data}|} \\
{[\textsc{\scriptsize E{-}memory.fill{-}zero}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{val}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{memory.fill}~{\mathit{x}}) &\hookrightarrow& \epsilon &\quad
  \mbox{otherwise, if}~{\mathit{n}} = 0 \\
{[\textsc{\scriptsize E{-}memory.fill{-}succ}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{val}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{memory.fill}~{\mathit{x}}) &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~{\mathit{val}}~({\mathsf{i{\scriptstyle32}}.\mathsf{store}}{8}~{\mathit{x}}~0~0)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}} + 1)~{\mathit{val}}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}} - 1)~(\mathsf{memory.fill}~{\mathit{x}}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}memory.copy{-}oob}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{memory.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}}_{{1}} + {\mathit{n}} > {|{{\mathit{z}}.\mathsf{mem}}{[{\mathit{x}}_{{1}}]}.\mathsf{data}|} \lor {\mathit{i}}_{{2}} + {\mathit{n}} > {|{{\mathit{z}}.\mathsf{mem}}{[{\mathit{x}}_{{2}}]}.\mathsf{data}|} \\
{[\textsc{\scriptsize E{-}memory.copy{-}zero}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{memory.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}}) &\hookrightarrow& \epsilon &\quad
  \mbox{otherwise, if}~{\mathit{n}} = 0 \\
{[\textsc{\scriptsize E{-}memory.copy{-}le}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{memory.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}}) &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}})~({\mathsf{i{\scriptstyle32}}.\mathsf{load}}{{{8}{\mathsf{\_}}}{\mathsf{u}}}~{\mathit{x}}_{{2}}~0~0)~({\mathsf{i{\scriptstyle32}}.\mathsf{store}}{8}~{\mathit{x}}_{{1}}~0~0)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}} + 1)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}} + 1)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}} - 1)~(\mathsf{memory.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}}) &\quad
  \mbox{otherwise, if}~{\mathit{i}}_{{1}} \leq {\mathit{i}}_{{2}} \\
{[\textsc{\scriptsize E{-}memory.copy{-}gt}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{memory.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}}) &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}} + {\mathit{n}} - 1)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}} + {\mathit{n}} - 1)~({\mathsf{i{\scriptstyle32}}.\mathsf{load}}{{{8}{\mathsf{\_}}}{\mathsf{u}}}~{\mathit{x}}_{{2}}~0~0)~({\mathsf{i{\scriptstyle32}}.\mathsf{store}}{8}~{\mathit{x}}_{{1}}~0~0)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{1}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}}_{{2}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}} - 1)~(\mathsf{memory.copy}~{\mathit{x}}_{{1}}~{\mathit{x}}_{{2}}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}memory.init{-}oob}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{memory.init}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{if}~{\mathit{i}} + {\mathit{n}} > {|{{\mathit{z}}.\mathsf{data}}{[{\mathit{y}}]}.\mathsf{data}|} \lor {\mathit{j}} + {\mathit{n}} > {|{{\mathit{z}}.\mathsf{mem}}{[{\mathit{x}}]}.\mathsf{data}|} \\
{[\textsc{\scriptsize E{-}memory.init{-}zero}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{memory.init}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& \epsilon &\quad
  \mbox{otherwise, if}~{\mathit{n}} = 0 \\
{[\textsc{\scriptsize E{-}memory.init{-}succ}]} \quad & {\mathit{z}} ; (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}})~(\mathsf{memory.init}~{\mathit{x}}~{\mathit{y}}) &\hookrightarrow& (\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}})~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{{\mathit{z}}.\mathsf{data}}{[{\mathit{y}}]}.\mathsf{data}[{\mathit{i}}])~({\mathsf{i{\scriptstyle32}}.\mathsf{store}}{8}~{\mathit{x}}~0~0)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{j}} + 1)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{i}} + 1)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{\mathit{n}} - 1)~(\mathsf{memory.init}~{\mathit{x}}~{\mathit{y}}) &\quad
  \mbox{otherwise} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E{-}data.drop}]} \quad & {\mathit{z}} ; (\mathsf{data.drop}~{\mathit{x}}) &\hookrightarrow& {\mathit{z}}[\mathsf{data}[{\mathit{x}}].\mathsf{data} = \epsilon] ; \epsilon &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{alloctypes}}(\epsilon) &=& \epsilon &  \\
{\mathrm{alloctypes}}({{\mathit{rectype}'}^\ast}~{\mathit{rectype}}) &=& {{\mathit{deftype}'}^\ast}~{{\mathit{deftype}}^\ast} &\quad
  \mbox{if}~{{\mathit{deftype}'}^\ast} = {\mathrm{alloctypes}}({{\mathit{rectype}'}^\ast}) \\
 &&&\quad {\land}~{{\mathit{deftype}}^\ast} = {{{\mathrm{roll}}}_{{\mathit{x}}}({\mathit{rectype}})}{[{ := }\;{{\mathit{deftype}'}^\ast}]} \\
 &&&\quad {\land}~{\mathit{x}} = {|{{\mathit{deftype}'}^\ast}|} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{allocfunc}}({\mathit{s}},\, {\mathit{mm}},\, {\mathit{func}}) &=& ({\mathit{s}}[\mathsf{func} = ..{\mathit{fi}}],\, {|{\mathit{s}}.\mathsf{func}|}) &\quad
  \mbox{if}~{\mathit{func}} = \mathsf{func}~{\mathit{x}}~{{\mathit{local}}^\ast}~{\mathit{expr}} \\
 &&&\quad {\land}~{\mathit{fi}} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{type}~{\mathit{mm}}.\mathsf{type}[{\mathit{x}}],\; \mathsf{module}~{\mathit{mm}},\; \mathsf{code}~{\mathit{func}} \}\end{array} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{allocfuncs}}({\mathit{s}},\, {\mathit{mm}},\, \epsilon) &=& ({\mathit{s}},\, \epsilon) &  \\
{\mathrm{allocfuncs}}({\mathit{s}},\, {\mathit{mm}},\, {\mathit{func}}~{{\mathit{func}'}^\ast}) &=& ({\mathit{s}}_{{2}},\, {\mathit{fa}}~{{\mathit{fa}'}^\ast}) &\quad
  \mbox{if}~({\mathit{s}}_{{1}},\, {\mathit{fa}}) = {\mathrm{allocfunc}}({\mathit{s}},\, {\mathit{mm}},\, {\mathit{func}}) \\
 &&&\quad {\land}~({\mathit{s}}_{{2}},\, {{\mathit{fa}'}^\ast}) = {\mathrm{allocfuncs}}({\mathit{s}}_{{1}},\, {\mathit{mm}},\, {{\mathit{func}'}^\ast}) \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{allocglobal}}({\mathit{s}},\, {\mathit{globaltype}},\, {\mathit{val}}) &=& ({\mathit{s}}[\mathsf{global} = ..{\mathit{gi}}],\, {|{\mathit{s}}.\mathsf{global}|}) &\quad
  \mbox{if}~{\mathit{gi}} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{type}~{\mathit{globaltype}},\; \mathsf{value}~{\mathit{val}} \}\end{array} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{allocglobals}}({\mathit{s}},\, \epsilon,\, \epsilon) &=& ({\mathit{s}},\, \epsilon) &  \\
{\mathrm{allocglobals}}({\mathit{s}},\, {\mathit{globaltype}}~{{\mathit{globaltype}'}^\ast},\, {\mathit{val}}~{{\mathit{val}'}^\ast}) &=& ({\mathit{s}}_{{2}},\, {\mathit{ga}}~{{\mathit{ga}'}^\ast}) &\quad
  \mbox{if}~({\mathit{s}}_{{1}},\, {\mathit{ga}}) = {\mathrm{allocglobal}}({\mathit{s}},\, {\mathit{globaltype}},\, {\mathit{val}}) \\
 &&&\quad {\land}~({\mathit{s}}_{{2}},\, {{\mathit{ga}'}^\ast}) = {\mathrm{allocglobals}}({\mathit{s}}_{{1}},\, {{\mathit{globaltype}'}^\ast},\, {{\mathit{val}'}^\ast}) \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{alloctable}}({\mathit{s}},\, [{\mathit{i}} .. {\mathit{j}}]~{\mathit{rt}},\, {\mathit{ref}}) &=& ({\mathit{s}}[\mathsf{table} = ..{\mathit{ti}}],\, {|{\mathit{s}}.\mathsf{table}|}) &\quad
  \mbox{if}~{\mathit{ti}} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{type}~([{\mathit{i}} .. {\mathit{j}}]~{\mathit{rt}}),\; \mathsf{elem}~{{\mathit{ref}}^{{\mathit{i}}}} \}\end{array} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{alloctables}}({\mathit{s}},\, \epsilon,\, \epsilon) &=& ({\mathit{s}},\, \epsilon) &  \\
{\mathrm{alloctables}}({\mathit{s}},\, {\mathit{tabletype}}~{{\mathit{tabletype}'}^\ast},\, {\mathit{ref}}~{{\mathit{ref}'}^\ast}) &=& ({\mathit{s}}_{{2}},\, {\mathit{ta}}~{{\mathit{ta}'}^\ast}) &\quad
  \mbox{if}~({\mathit{s}}_{{1}},\, {\mathit{ta}}) = {\mathrm{alloctable}}({\mathit{s}},\, {\mathit{tabletype}},\, {\mathit{ref}}) \\
 &&&\quad {\land}~({\mathit{s}}_{{2}},\, {{\mathit{ta}'}^\ast}) = {\mathrm{alloctables}}({\mathit{s}}_{{1}},\, {{\mathit{tabletype}'}^\ast},\, {{\mathit{ref}'}^\ast}) \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{allocmem}}({\mathit{s}},\, [{\mathit{i}} .. {\mathit{j}}]~\mathsf{i{\scriptstyle8}}) &=& ({\mathit{s}}[\mathsf{mem} = ..{\mathit{mi}}],\, {|{\mathit{s}}.\mathsf{mem}|}) &\quad
  \mbox{if}~{\mathit{mi}} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{type}~([{\mathit{i}} .. {\mathit{j}}]~\mathsf{i{\scriptstyle8}}),\; \mathsf{data}~{0^{{\mathit{i}} \cdot 64 \cdot {\mathrm{Ki}}}} \}\end{array} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{allocmems}}({\mathit{s}},\, \epsilon) &=& ({\mathit{s}},\, \epsilon) &  \\
{\mathrm{allocmems}}({\mathit{s}},\, {\mathit{memtype}}~{{\mathit{memtype}'}^\ast}) &=& ({\mathit{s}}_{{2}},\, {\mathit{ma}}~{{\mathit{ma}'}^\ast}) &\quad
  \mbox{if}~({\mathit{s}}_{{1}},\, {\mathit{ma}}) = {\mathrm{allocmem}}({\mathit{s}},\, {\mathit{memtype}}) \\
 &&&\quad {\land}~({\mathit{s}}_{{2}},\, {{\mathit{ma}'}^\ast}) = {\mathrm{allocmems}}({\mathit{s}}_{{1}},\, {{\mathit{memtype}'}^\ast}) \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{allocelem}}({\mathit{s}},\, {\mathit{rt}},\, {{\mathit{ref}}^\ast}) &=& ({\mathit{s}}[\mathsf{elem} = ..{\mathit{ei}}],\, {|{\mathit{s}}.\mathsf{elem}|}) &\quad
  \mbox{if}~{\mathit{ei}} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{type}~{\mathit{rt}},\; \mathsf{elem}~{{\mathit{ref}}^\ast} \}\end{array} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{allocelems}}({\mathit{s}},\, \epsilon,\, \epsilon) &=& ({\mathit{s}},\, \epsilon) &  \\
{\mathrm{allocelems}}({\mathit{s}},\, {\mathit{rt}}~{{\mathit{rt}'}^\ast},\, ({{\mathit{ref}}^\ast})~{({{\mathit{ref}'}^\ast})^\ast}) &=& ({\mathit{s}}_{{2}},\, {\mathit{ea}}~{{\mathit{ea}'}^\ast}) &\quad
  \mbox{if}~({\mathit{s}}_{{1}},\, {\mathit{ea}}) = {\mathrm{allocelem}}({\mathit{s}},\, {\mathit{rt}},\, {{\mathit{ref}}^\ast}) \\
 &&&\quad {\land}~({\mathit{s}}_{{2}},\, {{\mathit{ea}'}^\ast}) = {\mathrm{allocelems}}({\mathit{s}}_{{2}},\, {{\mathit{rt}'}^\ast},\, {({{\mathit{ref}'}^\ast})^\ast}) \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{allocdata}}({\mathit{s}},\, {{\mathit{byte}}^\ast}) &=& ({\mathit{s}}[\mathsf{data} = ..{\mathit{di}}],\, {|{\mathit{s}}.\mathsf{data}|}) &\quad
  \mbox{if}~{\mathit{di}} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{data}~{{\mathit{byte}}^\ast} \}\end{array} \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{allocdatas}}({\mathit{s}},\, \epsilon) &=& ({\mathit{s}},\, \epsilon) &  \\
{\mathrm{allocdatas}}({\mathit{s}},\, ({{\mathit{byte}}^\ast})~{({{\mathit{byte}'}^\ast})^\ast}) &=& ({\mathit{s}}_{{2}},\, {\mathit{da}}~{{\mathit{da}'}^\ast}) &\quad
  \mbox{if}~({\mathit{s}}_{{1}},\, {\mathit{da}}) = {\mathrm{allocdata}}({\mathit{s}},\, {{\mathit{byte}}^\ast}) \\
 &&&\quad {\land}~({\mathit{s}}_{{2}},\, {{\mathit{da}'}^\ast}) = {\mathrm{allocdatas}}({\mathit{s}}_{{1}},\, {({{\mathit{byte}'}^\ast})^\ast}) \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{instexport}}({{\mathit{fa}}^\ast},\, {{\mathit{ga}}^\ast},\, {{\mathit{ta}}^\ast},\, {{\mathit{ma}}^\ast},\, \mathsf{export}~{\mathit{name}}~(\mathsf{func}~{\mathit{x}})) &=& \{ \begin{array}[t]{@{}l@{}}
\mathsf{name}~{\mathit{name}},\; \mathsf{value}~(\mathsf{func}~{{\mathit{fa}}^\ast}[{\mathit{x}}]) \}\end{array} &  \\
{\mathrm{instexport}}({{\mathit{fa}}^\ast},\, {{\mathit{ga}}^\ast},\, {{\mathit{ta}}^\ast},\, {{\mathit{ma}}^\ast},\, \mathsf{export}~{\mathit{name}}~(\mathsf{global}~{\mathit{x}})) &=& \{ \begin{array}[t]{@{}l@{}}
\mathsf{name}~{\mathit{name}},\; \mathsf{value}~(\mathsf{global}~{{\mathit{ga}}^\ast}[{\mathit{x}}]) \}\end{array} &  \\
{\mathrm{instexport}}({{\mathit{fa}}^\ast},\, {{\mathit{ga}}^\ast},\, {{\mathit{ta}}^\ast},\, {{\mathit{ma}}^\ast},\, \mathsf{export}~{\mathit{name}}~(\mathsf{table}~{\mathit{x}})) &=& \{ \begin{array}[t]{@{}l@{}}
\mathsf{name}~{\mathit{name}},\; \mathsf{value}~(\mathsf{table}~{{\mathit{ta}}^\ast}[{\mathit{x}}]) \}\end{array} &  \\
{\mathrm{instexport}}({{\mathit{fa}}^\ast},\, {{\mathit{ga}}^\ast},\, {{\mathit{ta}}^\ast},\, {{\mathit{ma}}^\ast},\, \mathsf{export}~{\mathit{name}}~(\mathsf{mem}~{\mathit{x}})) &=& \{ \begin{array}[t]{@{}l@{}}
\mathsf{name}~{\mathit{name}},\; \mathsf{value}~(\mathsf{mem}~{{\mathit{ma}}^\ast}[{\mathit{x}}]) \}\end{array} &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{allocmodule}}({\mathit{s}},\, {\mathit{module}},\, {{\mathit{externval}}^\ast},\, {{\mathit{val}}_{{\mathit{g}}}^\ast},\, {{\mathit{ref}}_{{\mathit{t}}}^\ast},\, {({{\mathit{ref}}_{{\mathit{e}}}^\ast})^\ast}) &=& ({\mathit{s}}_{{6}},\, {\mathit{mm}}) &\quad
  \mbox{if}~{\mathit{module}} = \mathsf{module}~{(\mathsf{type}~{\mathit{rectype}})^\ast}~{{\mathit{import}}^\ast}~{{\mathit{func}}^{{\mathit{n}}_{{\mathit{f}}}}}~{(\mathsf{global}~{\mathit{globaltype}}~{\mathit{expr}}_{{\mathit{g}}})^{{\mathit{n}}_{{\mathit{g}}}}}~{(\mathsf{table}~{\mathit{tabletype}}~{\mathit{expr}}_{{\mathit{t}}})^{{\mathit{n}}_{{\mathit{t}}}}}~{(\mathsf{memory}~{\mathit{memtype}})^{{\mathit{n}}_{{\mathit{m}}}}}~{(\mathsf{elem}~{\mathit{reftype}}~{{\mathit{expr}}_{{\mathit{e}}}^\ast}~{{\mathit{elemmode}}^?})^{{\mathit{n}}_{{\mathit{e}}}}}~{(\mathsf{data}~{{\mathit{byte}}^\ast}~{{\mathit{datamode}}^?})^{{\mathit{n}}_{{\mathit{d}}}}}~{{\mathit{start}}^?}~{{\mathit{export}}^\ast} \\
 &&&\quad {\land}~{{\mathit{fa}}_{{\mathit{ex}}}^\ast} = {\mathrm{funcs}}({{\mathit{externval}}^\ast}) \\
 &&&\quad {\land}~{{\mathit{ga}}_{{\mathit{ex}}}^\ast} = {\mathrm{globals}}({{\mathit{externval}}^\ast}) \\
 &&&\quad {\land}~{{\mathit{ta}}_{{\mathit{ex}}}^\ast} = {\mathrm{tables}}({{\mathit{externval}}^\ast}) \\
 &&&\quad {\land}~{{\mathit{ma}}_{{\mathit{ex}}}^\ast} = {\mathrm{mems}}({{\mathit{externval}}^\ast}) \\
 &&&\quad {\land}~{{\mathit{fa}}^\ast} = {{|{\mathit{s}}.\mathsf{func}|} + {\mathit{i}}_{{\mathit{f}}}^{{\mathit{i}}_{{\mathit{f}}}<{\mathit{n}}_{{\mathit{f}}}}} \\
 &&&\quad {\land}~{{\mathit{ga}}^\ast} = {{|{\mathit{s}}.\mathsf{global}|} + {\mathit{i}}_{{\mathit{g}}}^{{\mathit{i}}_{{\mathit{g}}}<{\mathit{n}}_{{\mathit{g}}}}} \\
 &&&\quad {\land}~{{\mathit{ta}}^\ast} = {{|{\mathit{s}}.\mathsf{table}|} + {\mathit{i}}_{{\mathit{t}}}^{{\mathit{i}}_{{\mathit{t}}}<{\mathit{n}}_{{\mathit{t}}}}} \\
 &&&\quad {\land}~{{\mathit{ma}}^\ast} = {{|{\mathit{s}}.\mathsf{mem}|} + {\mathit{i}}_{{\mathit{m}}}^{{\mathit{i}}_{{\mathit{m}}}<{\mathit{n}}_{{\mathit{m}}}}} \\
 &&&\quad {\land}~{{\mathit{ea}}^\ast} = {{|{\mathit{s}}.\mathsf{elem}|} + {\mathit{i}}_{{\mathit{e}}}^{{\mathit{i}}_{{\mathit{e}}}<{\mathit{n}}_{{\mathit{e}}}}} \\
 &&&\quad {\land}~{{\mathit{da}}^\ast} = {{|{\mathit{s}}.\mathsf{data}|} + {\mathit{i}}_{{\mathit{d}}}^{{\mathit{i}}_{{\mathit{d}}}<{\mathit{n}}_{{\mathit{d}}}}} \\
 &&&\quad {\land}~{{\mathit{xi}}^\ast} = {{\mathrm{instexport}}({{\mathit{fa}}_{{\mathit{ex}}}^\ast}~{{\mathit{fa}}^\ast},\, {{\mathit{ga}}_{{\mathit{ex}}}^\ast}~{{\mathit{ga}}^\ast},\, {{\mathit{ta}}_{{\mathit{ex}}}^\ast}~{{\mathit{ta}}^\ast},\, {{\mathit{ma}}_{{\mathit{ex}}}^\ast}~{{\mathit{ma}}^\ast},\, {\mathit{export}})^\ast} \\
 &&&\quad {\land}~{\mathit{mm}} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{type}~{{\mathit{dt}}^\ast},\; \\
  \mathsf{func}~{{\mathit{fa}}_{{\mathit{ex}}}^\ast}~{{\mathit{fa}}^\ast},\; \\
  \mathsf{global}~{{\mathit{ga}}_{{\mathit{ex}}}^\ast}~{{\mathit{ga}}^\ast},\; \\
  \mathsf{table}~{{\mathit{ta}}_{{\mathit{ex}}}^\ast}~{{\mathit{ta}}^\ast},\; \\
  \mathsf{mem}~{{\mathit{ma}}_{{\mathit{ex}}}^\ast}~{{\mathit{ma}}^\ast},\; \\
  \mathsf{elem}~{{\mathit{ea}}^\ast},\; \\
  \mathsf{data}~{{\mathit{da}}^\ast},\; \\
  \mathsf{export}~{{\mathit{xi}}^\ast} \}\end{array} \\
 &&&\quad {\land}~{{\mathit{dt}}^\ast} = {\mathrm{alloctypes}}({{\mathit{rectype}}^\ast}) \\
 &&&\quad {\land}~({\mathit{s}}_{{1}},\, {{\mathit{fa}}^\ast}) = {\mathrm{allocfuncs}}({\mathit{s}},\, {\mathit{mm}},\, {{\mathit{func}}^{{\mathit{n}}_{{\mathit{f}}}}}) \\
 &&&\quad {\land}~({\mathit{s}}_{{2}},\, {{\mathit{ga}}^\ast}) = {\mathrm{allocglobals}}({\mathit{s}}_{{1}},\, {{\mathit{globaltype}}^{{\mathit{n}}_{{\mathit{g}}}}},\, {{\mathit{val}}_{{\mathit{g}}}^\ast}) \\
 &&&\quad {\land}~({\mathit{s}}_{{3}},\, {{\mathit{ta}}^\ast}) = {\mathrm{alloctables}}({\mathit{s}}_{{2}},\, {{\mathit{tabletype}}^{{\mathit{n}}_{{\mathit{t}}}}},\, {{\mathit{ref}}_{{\mathit{t}}}^\ast}) \\
 &&&\quad {\land}~({\mathit{s}}_{{4}},\, {{\mathit{ma}}^\ast}) = {\mathrm{allocmems}}({\mathit{s}}_{{3}},\, {{\mathit{memtype}}^{{\mathit{n}}_{{\mathit{m}}}}}) \\
 &&&\quad {\land}~({\mathit{s}}_{{5}},\, {{\mathit{ea}}^\ast}) = {\mathrm{allocelems}}({\mathit{s}}_{{4}},\, {{\mathit{reftype}}^{{\mathit{n}}_{{\mathit{e}}}}},\, {({{\mathit{ref}}_{{\mathit{e}}}^\ast})^\ast}) \\
 &&&\quad {\land}~({\mathit{s}}_{{6}},\, {{\mathit{da}}^\ast}) = {\mathrm{allocdatas}}({\mathit{s}}_{{5}},\, {({{\mathit{byte}}^\ast})^{{\mathit{n}}_{{\mathit{d}}}}}) \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{concat}}_{{\mathit{instr}}}(\epsilon) &=& \epsilon &  \\
{\mathrm{concat}}_{{\mathit{instr}}}(({{\mathit{instr}}^\ast})~{({{\mathit{instr}'}^\ast})^\ast}) &=& {{\mathit{instr}}^\ast}~{\mathrm{concat}}_{{\mathit{instr}}}({({{\mathit{instr}'}^\ast})^\ast}) &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{runelem}}(\mathsf{elem}~{\mathit{reftype}}~{{\mathit{expr}}^\ast},\, {\mathit{y}}) &=& \epsilon &  \\
{\mathrm{runelem}}(\mathsf{elem}~{\mathit{reftype}}~{{\mathit{expr}}^\ast}~(\mathsf{declare}),\, {\mathit{y}}) &=& (\mathsf{elem.drop}~{\mathit{y}}) &  \\
{\mathrm{runelem}}(\mathsf{elem}~{\mathit{reftype}}~{{\mathit{expr}}^\ast}~(\mathsf{table}~{\mathit{x}}~{{\mathit{instr}}^\ast}),\, {\mathit{y}}) &=& {{\mathit{instr}}^\ast}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~0)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{|{{\mathit{expr}}^\ast}|})~(\mathsf{table.init}~{\mathit{x}}~{\mathit{y}})~(\mathsf{elem.drop}~{\mathit{y}}) &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{rundata}}(\mathsf{data}~{{\mathit{byte}}^\ast},\, {\mathit{y}}) &=& \epsilon &  \\
{\mathrm{rundata}}(\mathsf{data}~{{\mathit{byte}}^\ast}~(\mathsf{memory}~{\mathit{x}}~{{\mathit{instr}}^\ast}),\, {\mathit{y}}) &=& {{\mathit{instr}}^\ast}~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~0)~(\mathsf{i{\scriptstyle32}}.\mathsf{const}~{|{{\mathit{byte}}^\ast}|})~(\mathsf{memory.init}~{\mathit{x}}~{\mathit{y}})~(\mathsf{data.drop}~{\mathit{y}}) &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{instantiate}}({\mathit{s}},\, {\mathit{module}},\, {{\mathit{externval}}^\ast}) &=& {\mathit{s}'} ; {\mathit{f}} ; {{\mathit{instr}}_{{\mathit{e}}}^\ast}~{{\mathit{instr}}_{{\mathit{d}}}^\ast}~{(\mathsf{call}~{\mathit{x}})^?} &\quad
  \mbox{if}~{\mathit{module}} = \mathsf{module}~{{\mathit{type}}^\ast}~{{\mathit{import}}^\ast}~{{\mathit{func}}^{{\mathit{n}}_{{\mathit{func}}}}}~{{\mathit{global}}^\ast}~{{\mathit{table}}^\ast}~{{\mathit{mem}}^\ast}~{{\mathit{elem}}^\ast}~{{\mathit{data}}^\ast}~{{\mathit{start}}^?}~{{\mathit{export}}^\ast} \\
 &&&\quad {\land}~{{\mathit{global}}^\ast} = {(\mathsf{global}~{\mathit{globaltype}}~{\mathit{expr}}_{{\mathit{g}}})^\ast} \\
 &&&\quad {\land}~{{\mathit{table}}^\ast} = {(\mathsf{table}~{\mathit{tabletype}}~{\mathit{expr}}_{{\mathit{t}}})^\ast} \\
 &&&\quad {\land}~{{\mathit{elem}}^\ast} = {(\mathsf{elem}~{\mathit{reftype}}~{{\mathit{expr}}_{{\mathit{e}}}^\ast}~{{\mathit{elemmode}}^?})^\ast} \\
 &&&\quad {\land}~{{\mathit{start}}^?} = {(\mathsf{start}~{\mathit{x}})^?} \\
 &&&\quad {\land}~{\mathit{n}}_{{\mathit{e}}} = {|{{\mathit{elem}}^\ast}|} \\
 &&&\quad {\land}~{\mathit{n}}_{{\mathit{d}}} = {|{{\mathit{data}}^\ast}|} \\
 &&&\quad {\land}~{\mathit{mm}}_{{\mathit{init}}} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{type}~{\mathit{mm}}.\mathsf{type},\; \\
  \mathsf{func}~{\mathrm{funcs}}({{\mathit{externval}}^\ast})~{{|{\mathit{s}}.\mathsf{func}|} + {\mathit{i}}_{{\mathit{func}}}^{{\mathit{i}}_{{\mathit{func}}}<{\mathit{n}}_{{\mathit{func}}}}},\; \\
  \mathsf{global}~{\mathrm{globals}}({{\mathit{externval}}^\ast}),\; \\
  \mathsf{table}~\epsilon,\; \\
  \mathsf{mem}~\epsilon,\; \\
  \mathsf{elem}~\epsilon,\; \\
  \mathsf{data}~\epsilon,\; \\
  \mathsf{export}~\epsilon \}\end{array} \\
 &&&\quad {\land}~{\mathit{z}} = {\mathit{s}} ; \{ \begin{array}[t]{@{}l@{}}
\mathsf{module}~{\mathit{mm}}_{{\mathit{init}}} \}\end{array} \\
 &&&\quad {\land}~({\mathit{z}} ; {\mathit{expr}}_{{\mathit{g}}} \hookrightarrow^\ast {\mathit{z}} ; {\mathit{val}}_{{\mathit{g}}})^\ast \\
 &&&\quad {\land}~({\mathit{z}} ; {\mathit{expr}}_{{\mathit{t}}} \hookrightarrow^\ast {\mathit{z}} ; {\mathit{ref}}_{{\mathit{t}}})^\ast \\
 &&&\quad {\land}~{({\mathit{z}} ; {\mathit{expr}}_{{\mathit{e}}} \hookrightarrow^\ast {\mathit{z}} ; {\mathit{ref}}_{{\mathit{e}}})^\ast}^\ast \\
 &&&\quad {\land}~({\mathit{s}'},\, {\mathit{mm}}) = {\mathrm{allocmodule}}({\mathit{s}},\, {\mathit{module}},\, {{\mathit{externval}}^\ast},\, {{\mathit{val}}_{{\mathit{g}}}^\ast},\, {{\mathit{ref}}_{{\mathit{t}}}^\ast},\, {({{\mathit{ref}}_{{\mathit{e}}}^\ast})^\ast}) \\
 &&&\quad {\land}~{\mathit{f}} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{module}~{\mathit{mm}} \}\end{array} \\
 &&&\quad {\land}~{{\mathit{instr}}_{{\mathit{e}}}^\ast} = {\mathrm{concat}}_{{\mathit{instr}}}({{\mathrm{runelem}}({{\mathit{elem}}^\ast}[{\mathit{i}}],\, {\mathit{i}})^{{\mathit{i}}<{\mathit{n}}_{{\mathit{e}}}}}) \\
 &&&\quad {\land}~{{\mathit{instr}}_{{\mathit{d}}}^\ast} = {\mathrm{concat}}_{{\mathit{instr}}}({{\mathrm{rundata}}({{\mathit{data}}^\ast}[{\mathit{j}}],\, {\mathit{j}})^{{\mathit{j}}<{\mathit{n}}_{{\mathit{d}}}}}) \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
{\mathrm{invoke}}({\mathit{s}},\, {\mathit{fa}},\, {{\mathit{val}}^{{\mathit{n}}}}) &=& {\mathit{s}} ; {\mathit{f}} ; {{\mathit{val}}^{{\mathit{n}}}}~(\mathsf{ref.func}~{\mathit{fa}})~(\mathsf{call\_ref}~0) &\quad
  \mbox{if}~{\mathit{mm}} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{type}~{\mathit{s}}.\mathsf{func}[{\mathit{fa}}].\mathsf{type},\; \\
  \mathsf{func}~\epsilon,\; \\
  \mathsf{global}~\epsilon,\; \\
  \mathsf{table}~\epsilon,\; \\
  \mathsf{mem}~\epsilon,\; \\
  \mathsf{elem}~\epsilon,\; \\
  \mathsf{data}~\epsilon,\; \\
  \mathsf{export}~\epsilon \}\end{array} \\
 &&&\quad {\land}~{\mathit{f}} = \{ \begin{array}[t]{@{}l@{}}
\mathsf{local}~\epsilon,\; \mathsf{module}~{\mathit{mm}} \}\end{array} \\
 &&&\quad {\land}~({\mathit{s}} ; {\mathit{f}}).\mathsf{func}[{\mathit{fa}}].\mathsf{code} = \mathsf{func}~{\mathit{x}}~{{\mathit{local}}^\ast}~{\mathit{expr}} \\
 &&&\quad {\land}~{\mathit{s}}.\mathsf{func}[{\mathit{fa}}].\mathsf{type} \approx \mathsf{func}~({{\mathit{t}}_{{1}}^{{\mathit{n}}}} \rightarrow {{\mathit{t}}_{{2}}^\ast}) \\
\end{array}
$$


== Complete.
```

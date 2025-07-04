open Reference_interpreter
open Ast
open Types
open Value
open Al.Ast
open Al.Al_util
open Al.Print
open Source
open Util


(* Errors *)

exception WrongConversion of string

let error category msg =
  raise (WrongConversion (Printf.sprintf "%s: invalid construction %s" category msg))

let error_value category v = error category ("`" ^ string_of_value v ^ "`")

let error_values category vs = error category ("`[" ^ string_of_values ", " vs ^ "]`")

let error_instr category instr' =
  error category ("`" ^ Reference_interpreter.Sexpr.to_string 60 (Arrange.instr (instr' @@ no_region)) ^ "`")

(* Constant *)

let default_table_max = 4294967295L
let default_memory_max = 65536L
let version = ref 3


(* Destruct *)

(* Destruct data structure *)

let al_to_opt (f: value -> 'a) (v: value): 'a option = unwrap_optv v |> Option.map f
let al_to_list (f: value -> 'a) (v: value): 'a list =
  unwrap_listv v |> (!) |> Array.to_list |> List.map f
let al_to_seq f s = al_to_list f s |> List.to_seq
let al_to_phrase (f: value -> 'a) (v: value): 'a phrase = f v @@ no_region


(* Destruct minor *)

type layout = { width : int; exponent : int; mantissa : int }
let layout32 = { width = 32; exponent = 8; mantissa = 23 }
let layout64 = { width = 64; exponent = 11; mantissa = 52 }

let mask_sign layout = Z.shift_left Z.one (layout.width - 1)
let mask_mag layout = Z.pred (mask_sign layout)
let mask_mant layout = Z.(pred (shift_left one layout.mantissa))
let mask_exp layout = Z.(mask_mag layout - mask_mant layout)
let bias layout = let em1 = layout.exponent - 1 in Z.((one + one)**em1 - one)

let al_to_z_nat: value -> Z.t = unwrap_natv
let al_to_z_int: value -> Z.t = unwrap_intv
let z_to_intN signed unsigned z = if z < Z.zero then signed z else unsigned z

let al_to_fmagN layout = function
  | CaseV ("NORM", [ m; n ]) ->
    Z.(shift_left (al_to_z_int n + bias layout) layout.mantissa + al_to_z_nat m)
  | CaseV ("SUBNORM", [ m ]) -> al_to_z_nat m
  | CaseV ("INF", []) -> mask_exp layout
  | CaseV ("NAN", [ m ]) -> Z.(mask_exp layout + al_to_z_nat m)
  | v -> error_value "fmagN" v

let al_to_floatN layout = function
  | CaseV ("POS", [ mag ]) -> al_to_fmagN layout mag
  | CaseV ("NEG", [ mag ]) -> Z.(mask_sign layout + al_to_fmagN layout mag)
  | v -> error_value "floatN" v

let e64 = Z.(shift_left one 64)
let z_to_vec128 i =
  let hi, lo = Z.div_rem i e64 in
  V128.I64x2.of_lanes [Z.to_int64_unsigned lo; Z.to_int64_unsigned hi]

let al_to_nat (v: value): int = al_to_z_nat v |> Z.to_int
let al_to_nat32 (v: value): I32.t = al_to_z_nat v |> z_to_intN Z.to_int32 Z.to_int32_unsigned
let al_to_nat64 (v: value): I64.t = al_to_z_nat v |> z_to_intN Z.to_int64 Z.to_int64_unsigned
let al_to_float32 (v: value): F32.t = al_to_floatN layout32 v |> Z.to_int32_unsigned |> F32.of_bits
let al_to_float64 (v: value): F64.t = al_to_floatN layout64 v |> Z.to_int64_unsigned |> F64.of_bits
let al_to_vec128 (v: value): V128.t = al_to_z_nat v |> z_to_vec128
let al_to_idx: value -> idx = al_to_phrase al_to_nat32
let al_to_byte (v: value): Char.t = al_to_nat v |> Char.chr
let al_to_bytes (v: value): string = al_to_seq al_to_byte v |> String.of_seq
let al_to_string = function
  | TextV str -> str
  | v -> error_value "text" v
let al_to_name name = name |> al_to_string |> Utf8.decode
let al_to_bool = unwrap_boolv


(* Destruct type *)

let al_to_null: value -> null = function
  | OptV None -> NoNull
  | OptV _ -> Null
  | v -> error_value "null" v

let al_to_final: value -> final = function
  | OptV None -> NoFinal
  | OptV _ -> Final
  | v -> error_value "final" v

let al_to_mut: value -> mut = function
  | OptV None -> Cons
  | OptV _ -> Var
  | v -> error_value "mut" v

let rec al_to_storage_type: value -> storage_type = function
  | CaseV ("I8", []) -> PackStorageT Pack8
  | CaseV ("I16", []) -> PackStorageT Pack16
  | v -> ValStorageT (al_to_val_type v)

and al_to_field_type: value -> field_type = function
  | CaseV (_, [ mut; st ]) -> FieldT (al_to_mut mut, al_to_storage_type st)
  | v -> error_value "field type" v

and al_to_result_type: value -> result_type = function
  v -> al_to_list al_to_val_type v

and al_to_str_type: value -> str_type = function
  | CaseV ("STRUCT", [ ftl ]) -> DefStructT (StructT (al_to_list al_to_field_type ftl))
  | CaseV ("ARRAY", [ ft ]) -> DefArrayT (ArrayT (al_to_field_type ft))
  | CaseV ("FUNC", [ CaseV ("->", [ rt1; rt2 ]) ]) ->
    DefFuncT (FuncT (al_to_result_type rt1, (al_to_result_type rt2)))
  | v -> error_value "str type" v

and al_to_sub_type: value -> sub_type = function
  | CaseV ("SUB", [ fin; htl; st ]) ->
    SubT (al_to_final fin, al_to_list al_to_heap_type htl, al_to_str_type st)
  | v -> error_value "sub type" v

and al_to_rec_type: value -> rec_type = function
  | CaseV ("REC", [ stl ]) -> RecT (al_to_list al_to_sub_type stl)
  | v -> error_value "rec type" v

and al_to_def_type: value -> def_type = function
  | CaseV ("_DEF", [ rt; i32 ]) -> DefT (al_to_rec_type rt, al_to_nat32 i32)
  | v -> error_value "def type" v

and al_to_typeuse: value -> idx = function
  | v when !version <= 2 -> al_to_idx v
  | CaseV ("_IDX", [ i32 ]) -> al_to_idx i32
  | CaseV ("REC", _) -> 0l @@ no_region   (* dummy *)
  | CaseV ("_DEF", _) -> 0l @@ no_region   (* dummy *)
  | v -> error_value "type use" v

and al_to_heap_type: value -> heap_type = function
  | CaseV ("_IDX", [ i32 ]) -> VarHT (StatX (al_to_nat32 i32))
  | CaseV ("REC", [ i32 ]) -> VarHT (RecX (al_to_nat32 i32))
  | CaseV ("_DEF", _) as v -> DefHT (al_to_def_type v)
  | CaseV (tag, []) as v ->
    (match tag with
    | "BOT" -> BotHT
    | "ANY" -> AnyHT
    | "NONE" -> NoneHT
    | "EQ" -> EqHT
    | "I31" -> I31HT
    | "STRUCT" -> StructHT
    | "ARRAY" -> ArrayHT
    | "FUNC" | "FUNCREF" -> FuncHT
    | "NOFUNC" -> NoFuncHT
    | "EXN" | "EXNREF" -> ExnHT
    | "NOEXN" -> NoExnHT
    | "EXTERN" | "EXTERNREF" -> ExternHT
    | "NOEXTERN" -> NoExternHT
    | _ -> error_value "abstract heap type" v)
  | v -> error_value "heap type" v

and al_to_ref_type: value -> ref_type = function
  | CaseV ("REF", [ n; ht ]) -> al_to_null n, al_to_heap_type ht
  | v -> error_value "ref type" v

and al_to_addr_type: value -> addr_type = function
  | CaseV ("I32", []) -> I32AT
  | CaseV ("I64", []) -> I64AT
  | v -> error_value "addr type" v

and al_to_num_type: value -> num_type = function
  | CaseV ("I32", []) -> I32T
  | CaseV ("I64", []) -> I64T
  | CaseV ("F32", []) -> F32T
  | CaseV ("F64", []) -> F64T
  | v -> error_value "num type" v

and al_to_val_type: value -> val_type = function
  | CaseV ("I32", _) | CaseV ("I64", _)
  | CaseV ("F32", _) | CaseV ("F64", _) as v -> NumT (al_to_num_type v)
  | CaseV ("V128", []) -> VecT V128T
  | CaseV ("REF", _) as v -> RefT (al_to_ref_type v)
  | CaseV ("BOT", []) -> BotT
  | v -> error_value "val type" v

let al_to_block_type: value -> block_type = function
  | CaseV ("_IDX", [ idx ]) -> VarBlockType (al_to_idx idx)
  | CaseV ("_RESULT", [ vt_opt ]) -> ValBlockType (al_to_opt al_to_val_type vt_opt)
  | v -> error_value "block type" v

let al_to_limits (default: int64): value -> limits = function
  | CaseV ("[", [ min; max ]) ->
    let max' =
      match al_to_nat64 max with
      | i64 when default = i64 -> None
      | _ -> Some (al_to_nat64 max)
    in
    { min = al_to_nat64 min; max = max' }
  | v -> error_value "limits" v


let al_to_global_type: value -> global_type = function
  | TupV [ mut; vt ] | CaseV (_, [ mut; vt ]) -> GlobalT (al_to_mut mut, al_to_val_type vt)
  | v -> error_value "global type" v

let al_to_table_type: value -> table_type = function
  | TupV [ at; limits; rt ] | CaseV (_, [ at; limits; rt ]) -> TableT (al_to_addr_type at, al_to_limits default_table_max limits, al_to_ref_type rt)
  | v -> error_value "table type" v

let al_to_memory_type: value -> memory_type = function
  | CaseV ("PAGE", [ at; limits ]) -> MemoryT (al_to_addr_type at, al_to_limits default_memory_max limits)
  | v -> error_value "memory type" v

let al_to_tag_type: value -> tag_type = function
  | dt -> TagT (al_to_def_type dt)


(* Destruct operator *)

let num i = `Nat (Z.of_int i)
let two = num 2
let four = num 4
let eight = num 8
let sixteen = num 16
let thirtytwo = num 32
let sixtyfour = num 64

let al_to_op f1 f2 = function
  | [ CaseV ("I32", []); op ] -> I32 (f1 op)
  | [ CaseV ("I64", []); op ] -> I64 (f1 op)
  | [ CaseV ("F32", []); op ] -> F32 (f2 op)
  | [ CaseV ("F64", []); op ] -> F64 (f2 op)
  | l -> error_values "op" l

let al_to_int_unop: value -> IntOp.unop = function
  | CaseV ("CLZ", []) -> IntOp.Clz
  | CaseV ("CTZ", []) -> IntOp.Ctz
  | CaseV ("POPCNT", []) -> IntOp.Popcnt
  | CaseV ("EXTEND", [NumV z]) when z = eight -> IntOp.ExtendS Pack.Pack8
  | CaseV ("EXTEND", [NumV z]) when z = sixteen -> IntOp.ExtendS Pack.Pack16
  | CaseV ("EXTEND", [NumV z]) when z = thirtytwo -> IntOp.ExtendS Pack.Pack32
  | CaseV ("EXTEND", [NumV z]) when z = sixtyfour -> IntOp.ExtendS Pack.Pack64
  | v -> error_value "integer unop" v
let al_to_float_unop: value -> FloatOp.unop = function
  | CaseV ("NEG", []) -> FloatOp.Neg
  | CaseV ("ABS", []) -> FloatOp.Abs
  | CaseV ("CEIL", []) -> FloatOp.Ceil
  | CaseV ("FLOOR", []) -> FloatOp.Floor
  | CaseV ("TRUNC", []) -> FloatOp.Trunc
  | CaseV ("NEAREST", []) -> FloatOp.Nearest
  | CaseV ("SQRT", []) -> FloatOp.Sqrt
  | v -> error_value "float unop" v
let al_to_unop: value list -> Ast.unop = al_to_op al_to_int_unop al_to_float_unop

let al_to_int_binop: value -> IntOp.binop = function
  | CaseV ("ADD", []) -> IntOp.Add
  | CaseV ("SUB", []) -> IntOp.Sub
  | CaseV ("MUL", []) -> IntOp.Mul
  | CaseV ("DIV", [CaseV ("S", [])]) -> IntOp.DivS
  | CaseV ("DIV", [CaseV ("U", [])]) -> IntOp.DivU
  | CaseV ("REM", [CaseV ("S", [])]) -> IntOp.RemS
  | CaseV ("REM", [CaseV ("U", [])]) -> IntOp.RemU
  | CaseV ("AND", []) -> IntOp.And
  | CaseV ("OR", []) -> IntOp.Or
  | CaseV ("XOR", []) -> IntOp.Xor
  | CaseV ("SHL", []) -> IntOp.Shl
  | CaseV ("SHR", [CaseV ("S", [])]) -> IntOp.ShrS
  | CaseV ("SHR", [CaseV ("U", [])]) -> IntOp.ShrU
  | CaseV ("ROTL", []) -> IntOp.Rotl
  | CaseV ("ROTR", []) -> IntOp.Rotr
  | v -> error_value "integer binop" v
let al_to_float_binop: value -> FloatOp.binop = function
  | CaseV ("ADD", []) -> FloatOp.Add
  | CaseV ("SUB", []) -> FloatOp.Sub
  | CaseV ("MUL", []) -> FloatOp.Mul
  | CaseV ("DIV", []) -> FloatOp.Div
  | CaseV ("MIN", []) -> FloatOp.Min
  | CaseV ("MAX", []) -> FloatOp.Max
  | CaseV ("COPYSIGN", []) -> FloatOp.CopySign
  | v -> error_value "float binop" v
let al_to_binop: value list -> Ast.binop = al_to_op al_to_int_binop al_to_float_binop

let al_to_int_testop: value -> IntOp.testop = function
  | CaseV ("EQZ", []) -> IntOp.Eqz
  | v -> error_value "integer testop" v
let al_to_testop: value list -> Ast.testop = function
  | [ CaseV ("I32", []); op ] -> Value.I32 (al_to_int_testop op)
  | [ CaseV ("I64", []); op ] -> Value.I64 (al_to_int_testop op)
  | l -> error_values "testop" l

let al_to_int_relop: value -> IntOp.relop = function
  | CaseV ("EQ", []) -> IntOp.Eq
  | CaseV ("NE", []) -> IntOp.Ne
  | CaseV ("LT", [CaseV ("S", [])]) -> IntOp.LtS
  | CaseV ("LT", [CaseV ("U", [])]) -> IntOp.LtU
  | CaseV ("GT", [CaseV ("S", [])]) -> IntOp.GtS
  | CaseV ("GT", [CaseV ("U", [])]) -> IntOp.GtU
  | CaseV ("LE", [CaseV ("S", [])]) -> IntOp.LeS
  | CaseV ("LE", [CaseV ("U", [])]) -> IntOp.LeU
  | CaseV ("GE", [CaseV ("S", [])]) -> IntOp.GeS
  | CaseV ("GE", [CaseV ("U", [])]) -> IntOp.GeU
  | v -> error_value "integer relop" v
let al_to_float_relop: value -> FloatOp.relop = function
  | CaseV ("EQ", []) -> FloatOp.Eq
  | CaseV ("NE", []) -> FloatOp.Ne
  | CaseV ("LT", []) -> FloatOp.Lt
  | CaseV ("GT", []) -> FloatOp.Gt
  | CaseV ("LE", []) -> FloatOp.Le
  | CaseV ("GE", []) -> FloatOp.Ge
  | v -> error_value "float relop" v
let al_to_relop: value list -> relop = al_to_op al_to_int_relop al_to_float_relop

let al_to_int_cvtop: value list -> IntOp.cvtop = function
  | [ CaseV ("I64", []); CaseV ("I32", []); CaseV ("EXTEND", [ CaseV (sx, []) ]) ] as l ->
    (match sx with
    | "S" -> IntOp.ExtendSI32
    | "U" -> IntOp.ExtendUI32
    | _ -> error_values "extend" l)
  | [ CaseV ("I32", []); CaseV ("I64", []); CaseV ("WRAP", []) ] -> IntOp.WrapI64
  | [ CaseV (_, []); CaseV (nt, []); CaseV ("TRUNC", [ CaseV (sx, []) ]) ] as l ->
    (match nt, sx with
    | "F32", "S" -> IntOp.TruncSF32
    | "F32", "U" -> IntOp.TruncUF32
    | "F64", "S" -> IntOp.TruncSF64
    | "F64", "U" -> IntOp.TruncUF64
    | _ -> error_values "trunc" l)
  | [ CaseV (_, []); CaseV (nt, []); CaseV ("TRUNC_SAT", [ CaseV (sx, []) ]) ] as l ->
    (match nt, sx with
    | "F32", "S" -> IntOp.TruncSatSF32
    | "F32", "U" -> IntOp.TruncSatUF32
    | "F64", "S" -> IntOp.TruncSatSF64
    | "F64", "U" -> IntOp.TruncSatUF64
    | _ -> error_values "trunc_sat" l)
  | [ _; _; CaseV ("REINTERPRET", []) ] -> IntOp.ReinterpretFloat
  | l -> error_values "integer cvtop" l
let al_to_float_cvtop : value list -> FloatOp.cvtop = function
  | [ CaseV (_, []); CaseV (nt, []); CaseV ("CONVERT", [ CaseV (sx, []) ]) ] as l ->
    (match nt, sx with
    | "I32", "S" -> FloatOp.ConvertSI32
    | "I32", "U" -> FloatOp.ConvertUI32
    | "I64", "S" -> FloatOp.ConvertSI64
    | "I64", "U" -> FloatOp.ConvertUI64
    | _ -> error_values "convert" l)
  | [ CaseV ("F64", []); CaseV ("F32", []); CaseV ("PROMOTE", []) ] -> FloatOp.PromoteF32
  | [ CaseV ("F32", []); CaseV ("F64", []); CaseV ("DEMOTE", []) ] -> FloatOp.DemoteF64
  | [ _; _; CaseV ("REINTERPRET", []) ] -> FloatOp.ReinterpretInt
  | l -> error_values "float cvtop" l
let al_to_cvtop: value list -> cvtop = function
  | CaseV ("I32", []) :: _ as op -> I32 (al_to_int_cvtop op)
  | CaseV ("I64", []) :: _ as op -> I64 (al_to_int_cvtop op)
  | CaseV ("F32", []) :: _ as op -> F32 (al_to_float_cvtop op)
  | CaseV ("F64", []) :: _ as op -> F64 (al_to_float_cvtop op)
  | l -> error_values "cvtop" l

(* Vector operator *)

let al_to_extension : value -> Pack.extension = function
  | CaseV ("S", []) -> Pack.SX
  | CaseV ("U", []) -> Pack.ZX
  | v -> error_value "extension" v

let al_to_vop f1 f2 = function
  | [ CaseV ("X", [ CaseV ("I8", []); NumV z ]); vop ] when z = sixteen -> V128 (V128.I8x16 (f1 vop))
  | [ CaseV ("X", [ CaseV ("I16", []); NumV z ]); vop ] when z = eight -> V128 (V128.I16x8 (f1 vop))
  | [ CaseV ("X", [ CaseV ("I32", []); NumV z ]); vop ] when z = four -> V128 (V128.I32x4 (f1 vop))
  | [ CaseV ("X", [ CaseV ("I64", []); NumV z ]); vop ] when z = two -> V128 (V128.I64x2 (f1 vop))
  | [ CaseV ("X", [ CaseV ("F32", []); NumV z ]); vop ] when z = four -> V128 (V128.F32x4 (f2 vop))
  | [ CaseV ("X", [ CaseV ("F64", []); NumV z ]); vop ] when z = two -> V128 (V128.F64x2 (f2 vop))
  | l -> error_values "vop" l

let al_to_vvop f = function
  | [ CaseV ("V128", []); vop ] -> V128 (f vop)
  | l -> error_values "vvop" l

let al_to_int_vtestop : value -> V128Op.itestop = function
  | CaseV ("ALL_TRUE", []) -> V128Op.AllTrue
  | v -> error_value "integer vtestop" v

let al_to_float_vtestop : value -> Ast.void = function
  | v -> error_value "float vtestop" v

let al_to_vtestop : value list -> vec_testop =
  al_to_vop al_to_int_vtestop al_to_float_vtestop

let al_to_vbitmaskop : value list -> vec_bitmaskop = function
  | [ CaseV ("X", [ CaseV ("I8", []); NumV z ]) ] when z = sixteen -> V128 (V128.I8x16 (V128Op.Bitmask))
  | [ CaseV ("X", [ CaseV ("I16", []); NumV z ]) ] when z = eight -> V128 (V128.I16x8 (V128Op.Bitmask))
  | [ CaseV ("X", [ CaseV ("I32", []); NumV z ]) ] when z = four -> V128 (V128.I32x4 (V128Op.Bitmask))
  | [ CaseV ("X", [ CaseV ("I64", []); NumV z ]) ] when z = two -> V128 (V128.I64x2 (V128Op.Bitmask))
  | l -> error_values "vbitmaskop" l

let al_to_int_vrelop : value -> V128Op.irelop = function
  | CaseV ("EQ", []) -> V128Op.Eq
  | CaseV ("NE", []) -> V128Op.Ne
  | CaseV ("LT", [CaseV ("S", [])]) -> V128Op.LtS
  | CaseV ("LT", [CaseV ("U", [])]) -> V128Op.LtU
  | CaseV ("LE", [CaseV ("S", [])]) -> V128Op.LeS
  | CaseV ("LE", [CaseV ("U", [])]) -> V128Op.LeU
  | CaseV ("GT", [CaseV ("S", [])]) -> V128Op.GtS
  | CaseV ("GT", [CaseV ("U", [])]) -> V128Op.GtU
  | CaseV ("GE", [CaseV ("S", [])]) -> V128Op.GeS
  | CaseV ("GE", [CaseV ("U", [])]) -> V128Op.GeU
  | v -> error_value "integer vrelop" v

let al_to_float_vrelop : value -> V128Op.frelop = function
  | CaseV ("EQ", []) -> V128Op.Eq
  | CaseV ("NE", []) -> V128Op.Ne
  | CaseV ("LT", []) -> V128Op.Lt
  | CaseV ("LE", []) -> V128Op.Le
  | CaseV ("GT", []) -> V128Op.Gt
  | CaseV ("GE", []) -> V128Op.Ge
  | v -> error_value "float vrelop" v

let al_to_vrelop : value list -> vec_relop =
  al_to_vop al_to_int_vrelop al_to_float_vrelop

let al_to_int_vunop : value -> V128Op.iunop = function
  | CaseV ("ABS", []) -> V128Op.Abs
  | CaseV ("NEG", []) -> V128Op.Neg
  | CaseV ("POPCNT", []) -> V128Op.Popcnt
  | v -> error_value "integer vunop" v

let al_to_float_vunop : value -> V128Op.funop = function
  | CaseV ("ABS", []) -> V128Op.Abs
  | CaseV ("NEG", []) -> V128Op.Neg
  | CaseV ("SQRT", []) -> V128Op.Sqrt
  | CaseV ("CEIL", []) -> V128Op.Ceil
  | CaseV ("FLOOR", []) -> V128Op.Floor
  | CaseV ("TRUNC", []) -> V128Op.Trunc
  | CaseV ("NEAREST", []) -> V128Op.Nearest
  | v -> error_value "float vunop" v

let al_to_vunop : value list -> vec_unop =
  al_to_vop al_to_int_vunop al_to_float_vunop

let al_to_int_vbinop : value -> V128Op.ibinop = function
  | CaseV ("ADD", []) -> V128Op.Add
  | CaseV ("SUB", []) -> V128Op.Sub
  | CaseV ("MUL", []) -> V128Op.Mul
  | CaseV ("MIN", [CaseV ("S", [])]) -> V128Op.MinS
  | CaseV ("MIN", [CaseV ("U", [])]) -> V128Op.MinU
  | CaseV ("MAX", [CaseV ("S", [])]) -> V128Op.MaxS
  | CaseV ("MAX", [CaseV ("U", [])]) -> V128Op.MaxU
  | CaseV ("AVGR", []) -> V128Op.AvgrU
  | CaseV ("ADD_SAT", [CaseV ("S", [])]) -> V128Op.AddSatS
  | CaseV ("ADD_SAT", [CaseV ("U", [])]) -> V128Op.AddSatU
  | CaseV ("SUB_SAT", [CaseV ("S", [])]) -> V128Op.SubSatS
  | CaseV ("SUB_SAT", [CaseV ("U", [])]) -> V128Op.SubSatU
  | CaseV ("Q15MULR_SAT", [(*CaseV ("S", [])*)]) -> V128Op.Q15MulRSatS
  | CaseV ("RELAXED_Q15MULR", [(*CaseV ("S", [])*)]) -> V128Op.RelaxedQ15MulRS
  | v -> error_value "integer vbinop" v

let al_to_float_vbinop : value -> V128Op.fbinop = function
  | CaseV ("ADD", []) -> V128Op.Add
  | CaseV ("SUB", []) -> V128Op.Sub
  | CaseV ("MUL", []) -> V128Op.Mul
  | CaseV ("DIV", []) -> V128Op.Div
  | CaseV ("MIN", []) -> V128Op.Min
  | CaseV ("MAX", []) -> V128Op.Max
  | CaseV ("PMIN", []) -> V128Op.Pmin
  | CaseV ("PMAX", []) -> V128Op.Pmax
  | CaseV ("RELAXED_MIN", []) -> V128Op.RelaxedMin
  | CaseV ("RELAXED_MAX", []) -> V128Op.RelaxedMax
  | v -> error_value "float vbinop" v

let al_to_vbinop : value list -> vec_binop = al_to_vop al_to_int_vbinop al_to_float_vbinop

let al_to_int_vternop : value -> V128Op.iternop = function
  | CaseV ("RELAXED_LANESELECT", []) -> V128Op.RelaxedLaneselect
  | v -> error_value "integer vternop" v

let al_to_float_vternop : value -> V128Op.fternop = function
  | CaseV ("RELAXED_MADD", []) -> V128Op.RelaxedMadd
  | CaseV ("RELAXED_NMADD", []) -> V128Op.RelaxedNmadd
  | v -> error_value "float vternop" v

let al_to_vternop : value list -> vec_ternop = al_to_vop al_to_int_vternop al_to_float_vternop

let al_to_special_vbinop = function
  | CaseV ("VSWIZZLOP", [ CaseV ("X", [ CaseV ("I8", []); NumV z ]); op ]) as v when z = sixteen ->
    (match op with
    | CaseV ("SWIZZLE", []) -> V128 (V128.I8x16 (V128Op.Swizzle))
    | CaseV ("RELAXED_SWIZZLE", []) -> V128 (V128.I8x16 (V128Op.RelaxedSwizzle))
    | _ ->  error_value "special vbinop" v)
  | CaseV ("VSWIZZLE", [ CaseV ("X", [ CaseV ("I8", []); NumV z ]) ]) when z = sixteen && !version = 2 -> V128 (V128.I8x16 (V128Op.Swizzle))
  | CaseV ("VSHUFFLE", [ CaseV ("X", [ CaseV ("I8", []); NumV z ]); l ]) when z = sixteen -> V128 (V128.I8x16 (V128Op.Shuffle (al_to_list al_to_nat l)))
  | CaseV ("VNARROW", [ CaseV ("X", [ CaseV ("I8", []); NumV z1 ]); CaseV ("X", [ CaseV ("I16", []); NumV z2 ]); CaseV ("S", []) ]) when z1 = sixteen && z2 = eight -> V128 (V128.I8x16 (V128Op.NarrowS))
  | CaseV ("VNARROW", [ CaseV ("X", [ CaseV ("I16", []); NumV z1 ]); CaseV ("X", [ CaseV ("I32", []); NumV z2 ]); CaseV ("S", []) ]) when z1 = eight && z2 = four -> V128 (V128.I16x8 (V128Op.NarrowS))
  | CaseV ("VNARROW", [ CaseV ("X", [ CaseV ("I8", []); NumV z1 ]); CaseV ("X", [ CaseV ("I16", []); NumV z2 ]); CaseV ("U", []) ]) when z1 = sixteen && z2 = eight -> V128 (V128.I8x16 (V128Op.NarrowU))
  | CaseV ("VNARROW", [ CaseV ("X", [ CaseV ("I16", []); NumV z1 ]); CaseV ("X", [ CaseV ("I32", []); NumV z2 ]); CaseV ("U", []) ]) when z1 = eight && z2 = four -> V128 (V128.I16x8 (V128Op.NarrowU))
  | CaseV ("VEXTBINOP", [ c1; c2; ext ]) as v ->
    let ext' =
      match ext with
      | CaseV ("EXTMUL", [CaseV ("HIGH", []); CaseV ("S", [])]) -> V128Op.ExtMulHighS
      | CaseV ("EXTMUL", [CaseV ("HIGH", []); CaseV ("U", [])]) -> V128Op.ExtMulHighU
      | CaseV ("EXTMUL", [CaseV ("LOW", []); CaseV ("S", [])]) -> V128Op.ExtMulLowS
      | CaseV ("EXTMUL", [CaseV ("LOW", []); CaseV ("U", [])]) -> V128Op.ExtMulLowU
      | CaseV ("DOT", [(*CaseV ("S", [])*)]) -> V128Op.DotS
      | CaseV ("RELAXED_DOT", [(*CaseV ("S", [])*)]) -> V128Op.RelaxedDot
      | _ -> error_value "special vextbinop operator" ext
    in
    (match c1, c2 with
    | CaseV ("X", [ CaseV ("I16", []); NumV z1 ]), CaseV ("X", [ CaseV ("I8", []); NumV z2 ]) when z1 = eight && z2 = sixteen -> V128 (V128.I16x8 ext')
    | CaseV ("X", [ CaseV ("I32", []); NumV z1 ]), CaseV ("X", [ CaseV ("I16", []); NumV z2 ]) when z1 = four && z2 = eight -> V128 (V128.I32x4 ext')
    | CaseV ("X", [ CaseV ("I64", []); NumV z1 ]), CaseV ("X", [ CaseV ("I32", []); NumV z2 ]) when z1 = two && z2 = four -> V128 (V128.I64x2 ext')
    | _   -> error_value "special vextbinop shapes" v)
  | v -> error_value "special vbinop" v

let al_to_special_vternop = function
  | CaseV ("VEXTTERNOP", [ c1; c2; ext ]) as v ->
    let ext' =
      match ext with
      | CaseV ("RELAXED_DOT_ADD", [(*CaseV ("S", [])*)]) -> V128Op.RelaxedDotAdd
      | _ -> error_value "special vextternop operator" ext
    in
    (match c1, c2 with
    | CaseV ("X", [ CaseV ("I32", []); NumV z1 ]), CaseV ("X", [ CaseV ("I8", []); NumV z2 ]) when z1 = four && z2 = sixteen -> V128 (V128.I32x4 ext')
    | _   -> error_value "special vextternop shapes" v)
  | v -> error_value "special vternop" v

let al_to_int_vcvtop : value list -> V128Op.icvtop = function
  | [ _sh; CaseV ("EXTEND", [ CaseV (half, []); CaseV (ext, []) ] ) ] as l -> (
      match half, ext with
      | "LOW", "S" -> V128Op.ExtendLowS
      | "LOW", "U" -> V128Op.ExtendLowU
      | "HIGH", "S" -> V128Op.ExtendHighS
      | "HIGH", "U" -> V128Op.ExtendHighU
      | _ -> error_values "integer vcvtop" l
    )
  | [ sh; CaseV ("TRUNC_SAT", [ CaseV (ext, []); _zero ] ) ] as l -> (
      match sh, ext with
      | CaseV ("X", [ CaseV ("F32", []); NumV z ]), "S" when z = four -> V128Op.TruncSatSF32x4
      | CaseV ("X", [ CaseV ("F32", []); NumV z ]), "U" when z = four -> V128Op.TruncSatUF32x4
      | CaseV ("X", [ CaseV ("F64", []); NumV z ]), "S" when z = two -> V128Op.TruncSatSZeroF64x2
      | CaseV ("X", [ CaseV ("F64", []); NumV z ]), "U" when z = two -> V128Op.TruncSatUZeroF64x2
      | _ -> error_values "integer vcvtop" l
    )
  | [ sh; CaseV ("RELAXED_TRUNC", [ CaseV (ext, []); _zero ] ) ] as l -> (
      match sh, ext with
      | CaseV ("X", [ CaseV ("F32", []); NumV z ]), "S" when z = four -> V128Op.RelaxedTruncSF32x4
      | CaseV ("X", [ CaseV ("F32", []); NumV z ]), "U" when z = four -> V128Op.RelaxedTruncUF32x4
      | CaseV ("X", [ CaseV ("F64", []); NumV z ]), "S" when z = two -> V128Op.RelaxedTruncSZeroF64x2
      | CaseV ("X", [ CaseV ("F64", []); NumV z ]), "U" when z = two -> V128Op.RelaxedTruncUZeroF64x2
      | _ -> error_values "integer vcvtop" l
    )
  | l -> error_values "integer vcvtop" l

let al_to_float_vcvtop : value list -> V128Op.fcvtop = function
  | [ _sh; CaseV ("DEMOTE", [ _zero ]) ] -> V128Op.DemoteZeroF64x2
  | [ _sh; CaseV ("CONVERT", [ _half; CaseV (ext, []) ]) ] as l -> (
    match ext with
    | "S" -> V128Op.ConvertSI32x4
    | "U" -> V128Op.ConvertUI32x4
    | _ -> error_values "float vcvtop" l
  )
  | [ _sh; CaseV ("PROMOTE", [ ]) ] -> V128Op.PromoteLowF32x4
  | l -> error_values "float vcvtop" l

let al_to_vcvtop : value list -> vec_cvtop = function
  | CaseV ("X", [ CaseV ("I8", []); NumV z ]) :: op when z = sixteen -> V128 (V128.I8x16 (al_to_int_vcvtop op))
  | CaseV ("X", [ CaseV ("I16", []); NumV z ]) :: op when z = eight -> V128 (V128.I16x8 (al_to_int_vcvtop op))
  | CaseV ("X", [ CaseV ("I32", []); NumV z ]) :: op when z = four -> V128 (V128.I32x4 (al_to_int_vcvtop op))
  | CaseV ("X", [ CaseV ("I64", []); NumV z ]) :: op when z = two -> V128 (V128.I64x2 (al_to_int_vcvtop op))
  | CaseV ("X", [ CaseV ("F32", []); NumV z ]) :: op when z = four -> V128 (V128.F32x4 (al_to_float_vcvtop op))
  | CaseV ("X", [ CaseV ("F64", []); NumV z ]) :: op when z = two -> V128 (V128.F64x2 (al_to_float_vcvtop op))
  | l -> error_values "vcvtop" l

let al_to_special_vcvtop = function
  | [ CaseV ("X", [ CaseV ("I16", []); NumV z1 ]); CaseV ("X", [ CaseV ("I8", []); NumV z2 ]); CaseV ("EXTADD_PAIRWISE", [ ext ]) ] when z1 = eight && z2 = sixteen ->
    let ext =
      match ext with
      | CaseV ("S", []) -> V128Op.ExtAddPairwiseS
      | CaseV ("U", []) -> V128Op.ExtAddPairwiseU
      | v -> error_value "special vcvtop" v
    in
    V128 (V128.I16x8 ext)
  | [ CaseV ("X", [ CaseV ("I32", []); NumV z1 ]); CaseV ("X", [ CaseV ("I16", []); NumV z2 ]); CaseV ("EXTADD_PAIRWISE", [ ext ]) ] when z1 = four && z2 = eight ->
    let ext =
      match ext with
      | CaseV ("S", []) -> V128Op.ExtAddPairwiseS
      | CaseV ("U", []) -> V128Op.ExtAddPairwiseU
      | v -> error_value "special vcvtop" v
    in
    V128 (V128.I32x4 ext)
  | l -> error_values "special vcvtop" l

let al_to_int_vshiftop : value -> V128Op.ishiftop = function
  | CaseV ("SHL", []) -> V128Op.Shl
  | CaseV ("SHR", [CaseV ("S", [])]) -> V128Op.ShrS
  | CaseV ("SHR", [CaseV ("U", [])]) -> V128Op.ShrU
  | v -> error_value "integer vshiftop" v
let al_to_float_vshiftop : value -> void = error_value "float vshiftop"
let al_to_vshiftop : value list -> vec_shiftop = al_to_vop al_to_int_vshiftop al_to_float_vshiftop

let al_to_vvtestop' : value -> V128Op.vtestop = function
  | CaseV ("ANY_TRUE", []) -> V128Op.AnyTrue
  | v -> error_value "vvtestop" v
let al_to_vvtestop : value list -> vec_vtestop = al_to_vvop al_to_vvtestop'

let al_to_vvunop' : value -> V128Op.vunop = function
  | CaseV ("NOT", []) -> V128Op.Not
  | v -> error_value "vvunop" v
let al_to_vvunop : value list -> vec_vunop = al_to_vvop al_to_vvunop'

let al_to_vvbinop' = function
  | CaseV ("AND", []) -> V128Op.And
  | CaseV ("OR", []) -> V128Op.Or
  | CaseV ("XOR", []) -> V128Op.Xor
  | CaseV ("ANDNOT", []) -> V128Op.AndNot
  | v -> error_value "vvbinop" v
let al_to_vvbinop : value list -> vec_vbinop = al_to_vvop al_to_vvbinop'

let al_to_vvternop' : value -> V128Op.vternop = function
  | CaseV ("BITSELECT", []) -> V128Op.Bitselect
  | v -> error_value "vvternop" v
let al_to_vvternop : value list -> vec_vternop = al_to_vvop al_to_vvternop'

let al_to_vsplatop : value list -> vec_splatop = function
  | [ CaseV ("X", [ CaseV ("I8", []); NumV z ]) ] when z = sixteen -> V128 (V128.I8x16 Splat)
  | [ CaseV ("X", [ CaseV ("I16", []); NumV z ]) ] when z = eight -> V128 (V128.I16x8 Splat)
  | [ CaseV ("X", [ CaseV ("I32", []); NumV z ]) ] when z = four -> V128 (V128.I32x4 Splat)
  | [ CaseV ("X", [ CaseV ("I64", []); NumV z ]) ] when z = two -> V128 (V128.I64x2 Splat)
  | [ CaseV ("X", [ CaseV ("F32", []); NumV z ]) ] when z = four -> V128 (V128.F32x4 Splat)
  | [ CaseV ("X", [ CaseV ("F64", []); NumV z ]) ] when z = two -> V128 (V128.F64x2 Splat)
  | vs -> error_values "vsplatop" vs

let al_to_vextractop : value list -> vec_extractop = function
  | [ CaseV ("X", [ CaseV ("I8", []); NumV z ]); OptV (Some ext); n ] when z = sixteen ->
    V128 (V128.I8x16 (Extract (al_to_nat n, al_to_extension ext)))
  | [ CaseV ("X", [ CaseV ("I16", []); NumV z ]); OptV (Some ext); n ] when z = eight ->
    V128 (V128.I16x8 (Extract (al_to_nat n, al_to_extension ext)))
  | [ CaseV ("X", [ CaseV ("I32", []); NumV z ]); OptV None; n ] when z = four ->
    V128 (V128.I32x4 (Extract (al_to_nat n, ())))
  | [ CaseV ("X", [ CaseV ("I64", []); NumV z ]); OptV None; n ] when z = two ->
    V128 (V128.I64x2 (Extract (al_to_nat n, ())))
  | [ CaseV ("X", [ CaseV ("F32", []); NumV z ]); OptV None; n ] when z = four ->
    V128 (V128.F32x4 (Extract (al_to_nat n, ())))
  | [ CaseV ("X", [ CaseV ("F64", []); NumV z ]); OptV None; n ] when z = two ->
    V128 (V128.F64x2 (Extract (al_to_nat n, ())))
  | vs -> error_values "vextractop" vs

let al_to_vreplaceop : value list -> vec_replaceop = function
  | [ CaseV ("X", [ CaseV ("I8", []); NumV z ]); n ] when z = sixteen -> V128 (V128.I8x16 (Replace (al_to_nat n)))
  | [ CaseV ("X", [ CaseV ("I16", []); NumV z ]); n ] when z = eight -> V128 (V128.I16x8 (Replace (al_to_nat n)))
  | [ CaseV ("X", [ CaseV ("I32", []); NumV z ]); n ] when z = four -> V128 (V128.I32x4 (Replace (al_to_nat n)))
  | [ CaseV ("X", [ CaseV ("I64", []); NumV z ]); n ] when z = two -> V128 (V128.I64x2 (Replace (al_to_nat n)))
  | [ CaseV ("X", [ CaseV ("F32", []); NumV z ]); n ] when z = four -> V128 (V128.F32x4 (Replace (al_to_nat n)))
  | [ CaseV ("X", [ CaseV ("F64", []); NumV z ]); n ] when z = two -> V128 (V128.F64x2 (Replace (al_to_nat n)))
  | vs -> error_values "vreplaceop" vs

let al_to_pack_size : value -> Pack.pack_size = function
  | NumV z when z = eight -> Pack.Pack8
  | NumV z when z = sixteen -> Pack.Pack16
  | NumV z when z = thirtytwo -> Pack.Pack32
  | NumV z when z = sixtyfour -> Pack.Pack64
  | v -> error_value "pack_size" v

let al_to_extension: value -> Pack.extension = function
  | CaseV ("S", []) -> Pack.SX
  | CaseV ("U", []) -> Pack.ZX
  | v -> error_value "extension" v

let al_to_memop (f: value -> 'p) : value list -> idx * (num_type, 'p) memop = function
  | [ nt; p; StrV str ] when !version <= 2 ->
    0l @@ no_region,
    {
      ty = al_to_num_type nt;
      align = Record.find "ALIGN" str |> al_to_nat;
      offset = Record.find "OFFSET" str |> al_to_nat64;
      pack = f p;
    }
  | [ nt; p; idx; StrV str ] when !version >= 3 ->
    al_to_idx idx,
    {
      ty = al_to_num_type nt;
      align = Record.find "ALIGN" str |> al_to_nat;
      offset = Record.find "OFFSET" str |> al_to_nat64;
      pack = f p;
    }
  | v -> error_values "memop" v

let al_to_pack_size_extension: value -> Pack.pack_size * Pack.extension = function
  | CaseV ("_", [ p; ext ]) -> al_to_pack_size p, al_to_extension ext
  | v -> error_value "pack size, extension" v

let al_to_loadop: value list -> idx * loadop = al_to_opt al_to_pack_size_extension |> al_to_memop

let al_to_storeop: value list -> idx * storeop = al_to_opt al_to_pack_size |> al_to_memop

let al_to_vmemop' (f: value -> 'p): value list -> (vec_type, 'p) memop = function
  | [ StrV str ] ->
    {
      ty = V128T;
      align = Record.find "ALIGN" str |> al_to_nat;
      offset = Record.find "OFFSET" str |> al_to_nat64;
      pack = f (natV Z.zero);
    }
  | [ p; StrV str ] ->
    {
      ty = V128T;
      align = Record.find "ALIGN" str |> al_to_nat;
      offset = Record.find "OFFSET" str |> al_to_nat64;
      pack = f p;
    }
  | v -> error_values "vmemop" v

let al_to_vmemop (f: value -> 'p) (g: value list -> value * (value list)): value list -> idx * (vec_type, 'p) memop = function
  | vl when !version <= 2 ->
    0l @@ no_region, al_to_vmemop' f vl
  | vl when !version >= 3 ->
    let idx, vl' = g vl in
    al_to_idx idx, al_to_vmemop' f vl'
  | v -> error_values "vmemop" v

let al_to_pack_shape = function
  | [NumV z1; NumV z2] when z1 = eight && z2 = eight -> Pack.Pack8x8
  | [NumV z1; NumV z2] when z1 = sixteen && z2 = four -> Pack.Pack16x4
  | [NumV z1; NumV z2] when z1 = thirtytwo && z2 = two -> Pack.Pack32x2
  | vs -> error_value "pack shape" (TupV vs)

let al_to_vloadop': value -> Pack.pack_size * Pack.vec_extension = function
  | CaseV ("SHAPE", [ v1; v2; ext ] ) ->
    let pack_shape = al_to_pack_shape [v1; v2] in
    (
      Pack.Pack64,
      Pack.ExtLane (pack_shape, al_to_extension ext)
    )
  | CaseV ("SPLAT", [ pack_size ]) -> al_to_pack_size pack_size, Pack.ExtSplat
  | CaseV ("ZERO", [ pack_size ]) -> al_to_pack_size pack_size, Pack.ExtZero
  | v -> error_value "vloadop'" v

let al_to_vloadop: value list -> idx * vec_loadop = function
  | CaseV ("V128", []) :: vl ->
    let split vl =
      match vl with
      | memop :: idx :: vl' -> idx, memop :: vl'
      | _ -> error_values "vloadop" vl
    in
    al_to_vmemop (al_to_opt al_to_vloadop') split vl
  | vs -> error_value "vloadop" (TupV vs)

let al_to_vstoreop = function
  | CaseV ("V128", []) :: vl ->
    let split = Util.Lib.List.split_hd in
    al_to_vmemop (fun _ -> ()) split vl
  | vs -> error_value "vstoreop" (TupV vs)

let al_to_vlaneop: value list -> idx * vec_laneop * int = function
  | CaseV ("V128", []) :: vl ->
    let h, t = Util.Lib.List.split_last vl in
    let split vl =
      match vl with
      | ps :: idx :: vl' -> idx, ps :: vl'
      | _ -> error_values "vlaneop" vl
    in
    let idx, op = al_to_vmemop al_to_pack_size split h in
    idx, op, al_to_nat t
  | vs -> error_value "vlaneop" (TupV vs)


(* Destruct expressions *)

let al_to_catch' = function
  | CaseV ("CATCH", [ idx1; idx2 ]) -> Catch (al_to_idx idx1, al_to_idx idx2)
  | CaseV ("CATCH_REF", [ idx1; idx2 ]) -> CatchRef (al_to_idx idx1, al_to_idx idx2)
  | CaseV ("CATCH_ALL", [ idx ]) -> CatchAll (al_to_idx idx)
  | CaseV ("CATCH_ALL_REF", [ idx ]) -> CatchAllRef (al_to_idx idx)
  | v -> error_value "catch" v
let al_to_catch (v: value): Ast.catch = al_to_phrase al_to_catch' v

let al_to_num: value -> num = function
  | CaseV ("CONST", [ CaseV ("I32", []); i32 ]) -> I32 (al_to_nat32 i32)
  | CaseV ("CONST", [ CaseV ("I64", []); i64 ]) -> I64 (al_to_nat64 i64)
  | CaseV ("CONST", [ CaseV ("F32", []); f32 ]) -> F32 (al_to_float32 f32)
  | CaseV ("CONST", [ CaseV ("F64", []); f64 ]) -> F64 (al_to_float64 f64)
  | v -> error_value "num" v

let al_to_vec: value -> vec = function
  | CaseV ("VCONST", [ CaseV ("V128", []); v128 ]) -> V128 (al_to_vec128 v128)
  | v -> error_value "vec" v

let rec al_to_instr (v: value): Ast.instr = al_to_phrase al_to_instr' v
and al_to_instr': value -> Ast.instr' = function
  (* wasm values *)
  | CaseV ("CONST", _) as v -> Const (al_to_phrase al_to_num v)
  | CaseV ("VCONST", _) as v -> VecConst (al_to_phrase al_to_vec v)
  | CaseV ("REF.NULL", [ ht ]) -> RefNull (al_to_heap_type ht)
  (* wasm instructions *)
  | CaseV ("UNREACHABLE", []) -> Unreachable
  | CaseV ("NOP", []) -> Nop
  | CaseV ("DROP", []) -> Drop
  | CaseV ("UNOP", op) -> Unary (al_to_unop op)
  | CaseV ("BINOP", op) -> Binary (al_to_binop op)
  | CaseV ("TESTOP", op) -> Test (al_to_testop op)
  | CaseV ("RELOP", op) -> Compare (al_to_relop op)
  | CaseV ("CVTOP", op) -> Convert (al_to_cvtop op)
  | CaseV ("VTESTOP", vop) -> VecTest (al_to_vtestop vop)
  | CaseV ("VRELOP", vop) -> VecCompare (al_to_vrelop vop)
  | CaseV ("VUNOP", vop) -> VecUnary (al_to_vunop vop)
  | CaseV ("VBINOP", vop) -> VecBinary (al_to_vbinop vop)
  | CaseV ("VTERNOP", vop) -> VecTernary (al_to_vternop vop)
  | CaseV (("VSWIZZLOP" | "VSWIZZLE" | "VSHUFFLE" | "VNARROW" | "VEXTBINOP"), _) as v -> VecBinary (al_to_special_vbinop v)
  | CaseV ("VEXTTERNOP", _) as v -> VecTernary (al_to_special_vternop v)
  | CaseV ("VCVTOP", vop) -> VecConvert (al_to_vcvtop vop)
  | CaseV ("VEXTUNOP", vop) -> VecConvert (al_to_special_vcvtop vop)
  | CaseV ("VSHIFTOP", vop) -> VecShift (al_to_vshiftop vop)
  | CaseV ("VBITMASK", vop) -> VecBitmask (al_to_vbitmaskop vop)
  | CaseV ("VVTESTOP", vop) -> VecTestBits (al_to_vvtestop vop)
  | CaseV ("VVUNOP", vop) -> VecUnaryBits (al_to_vvunop vop)
  | CaseV ("VVBINOP", vop) -> VecBinaryBits (al_to_vvbinop vop)
  | CaseV ("VVTERNOP", vop) -> VecTernaryBits (al_to_vvternop vop)
  | CaseV ("VSPLAT", vop) -> VecSplat (al_to_vsplatop vop)
  | CaseV ("VEXTRACT_LANE", vop) -> VecExtract (al_to_vextractop vop)
  | CaseV ("VREPLACE_LANE", vop) -> VecReplace (al_to_vreplaceop vop)
  | CaseV ("REF.IS_NULL", []) -> RefIsNull
  | CaseV ("REF.FUNC", [ idx ]) -> RefFunc (al_to_idx idx)
  | CaseV ("SELECT", []) when !version = 1 -> Select None
  | CaseV ("SELECT", [ vtl_opt ]) when !version <> 1 -> Select (al_to_opt (al_to_list al_to_val_type) vtl_opt)
  | CaseV ("LOCAL.GET", [ idx ]) -> LocalGet (al_to_idx idx)
  | CaseV ("LOCAL.SET", [ idx ]) -> LocalSet (al_to_idx idx)
  | CaseV ("LOCAL.TEE", [ idx ]) -> LocalTee (al_to_idx idx)
  | CaseV ("GLOBAL.GET", [ idx ]) -> GlobalGet (al_to_idx idx)
  | CaseV ("GLOBAL.SET", [ idx ]) -> GlobalSet (al_to_idx idx)
  | CaseV ("TABLE.GET", [ idx ]) -> TableGet (al_to_idx idx)
  | CaseV ("TABLE.SET", [ idx ]) -> TableSet (al_to_idx idx)
  | CaseV ("TABLE.SIZE", [ idx ]) -> TableSize (al_to_idx idx)
  | CaseV ("TABLE.GROW", [ idx ]) -> TableGrow (al_to_idx idx)
  | CaseV ("TABLE.FILL", [ idx ]) -> TableFill (al_to_idx idx)
  | CaseV ("TABLE.COPY", [ idx1; idx2 ]) -> TableCopy (al_to_idx idx1, al_to_idx idx2)
  | CaseV ("TABLE.INIT", [ idx1; idx2 ]) -> TableInit (al_to_idx idx1, al_to_idx idx2)
  | CaseV ("ELEM.DROP", [ idx ]) -> ElemDrop (al_to_idx idx)
  | CaseV ("BLOCK", [ bt; instrs ]) ->
    Block (al_to_block_type bt, al_to_list al_to_instr instrs)
  | CaseV ("LOOP", [ bt; instrs ]) ->
    Loop (al_to_block_type bt, al_to_list al_to_instr instrs)
  | CaseV ("IF", [ bt; instrs1; instrs2 ]) ->
    If (al_to_block_type bt, al_to_list al_to_instr instrs1, al_to_list al_to_instr instrs2)
  | CaseV ("BR", [ idx ]) -> Br (al_to_idx idx)
  | CaseV ("BR_IF", [ idx ]) -> BrIf (al_to_idx idx)
  | CaseV ("BR_TABLE", [ idxs; idx ]) -> BrTable (al_to_list al_to_idx idxs, al_to_idx idx)
  | CaseV ("BR_ON_NULL", [ idx ]) -> BrOnNull (al_to_idx idx)
  | CaseV ("BR_ON_NON_NULL", [ idx ]) -> BrOnNonNull (al_to_idx idx)
  | CaseV ("BR_ON_CAST", [ idx; rt1; rt2 ]) ->
    BrOnCast (al_to_idx idx, al_to_ref_type rt1, al_to_ref_type rt2)
  | CaseV ("BR_ON_CAST_FAIL", [ idx; rt1; rt2 ]) ->
    BrOnCastFail (al_to_idx idx, al_to_ref_type rt1, al_to_ref_type rt2)
  | CaseV ("RETURN", []) -> Return
  | CaseV ("CALL", [ idx ]) -> Call (al_to_idx idx)
  | CaseV ("CALL_REF", [ OptV (Some (idx)) ]) -> CallRef (al_to_idx idx)
  | CaseV ("CALL_INDIRECT", [ idx1; typeuse2 ]) ->
    CallIndirect (al_to_idx idx1, al_to_typeuse typeuse2)
  | CaseV ("RETURN_CALL", [ idx ]) -> ReturnCall (al_to_idx idx)
  | CaseV ("RETURN_CALL_REF", [ OptV (Some (typeuse)) ]) -> ReturnCallRef (al_to_typeuse typeuse)
  | CaseV ("RETURN_CALL_INDIRECT", [ idx1; typeuse2 ]) ->
    ReturnCallIndirect (al_to_idx idx1, al_to_typeuse typeuse2)
  | CaseV ("THROW", [ idx ]) -> Throw (al_to_idx idx)
  | CaseV ("THROW_REF", []) -> ThrowRef
  | CaseV ("TRY_TABLE", [ bt; catches; instrs ]) ->
    TryTable (al_to_block_type bt, al_to_list al_to_catch catches, al_to_list al_to_instr instrs)
  | CaseV ("LOAD", loadop) -> let idx, op = al_to_loadop loadop in Load (idx, op)
  | CaseV ("STORE", storeop) -> let idx, op = al_to_storeop storeop in Store (idx, op)
  | CaseV ("VLOAD", vloadop) -> let idx, op = al_to_vloadop vloadop in VecLoad (idx, op)
  | CaseV ("VLOAD_LANE", vlaneop) ->
    let idx, op, i = al_to_vlaneop vlaneop in VecLoadLane (idx, op, i)
  | CaseV ("VSTORE", vstoreop) -> let idx, op = al_to_vstoreop vstoreop in VecStore (idx, op)
  | CaseV ("VSTORE_LANE", vlaneop) ->
    let idx, op, i = al_to_vlaneop vlaneop in VecStoreLane (idx, op, i)
  | CaseV ("MEMORY.SIZE", [ idx ]) -> MemorySize (al_to_idx idx)
  | CaseV ("MEMORY.GROW", [ idx ]) -> MemoryGrow (al_to_idx idx)
  | CaseV ("MEMORY.FILL", [ idx ]) -> MemoryFill (al_to_idx idx)
  | CaseV ("MEMORY.COPY", [ idx1; idx2 ]) -> MemoryCopy (al_to_idx idx1, al_to_idx idx2)
  | CaseV ("MEMORY.INIT", [ idx1; idx2 ]) -> MemoryInit (al_to_idx idx1, al_to_idx idx2)
  | CaseV ("DATA.DROP", [ idx ]) -> DataDrop (al_to_idx idx)
  | CaseV ("REF.AS_NON_NULL", []) -> RefAsNonNull
  | CaseV ("REF.TEST", [ rt ]) -> RefTest (al_to_ref_type rt)
  | CaseV ("REF.CAST", [ rt ]) -> RefCast (al_to_ref_type rt)
  | CaseV ("REF.EQ", []) -> RefEq
  | CaseV ("REF.I31", []) -> RefI31
  | CaseV ("I31.GET", [ ext ]) -> I31Get (al_to_extension ext)
  | CaseV ("STRUCT.NEW", [ idx ]) -> StructNew (al_to_idx idx, Explicit)
  | CaseV ("STRUCT.NEW_DEFAULT", [ idx ]) -> StructNew (al_to_idx idx, Implicit)
  | CaseV ("STRUCT.GET", [ ext_opt; idx1; idx2 ]) ->
    StructGet (al_to_idx idx1, al_to_idx idx2, al_to_opt al_to_extension ext_opt)
  | CaseV ("STRUCT.SET", [ idx1; idx2 ]) -> StructSet (al_to_idx idx1, al_to_idx idx2)
  | CaseV ("ARRAY.NEW", [ idx ]) -> ArrayNew (al_to_idx idx, Explicit)
  | CaseV ("ARRAY.NEW_DEFAULT", [ idx ]) -> ArrayNew (al_to_idx idx, Implicit)
  | CaseV ("ARRAY.NEW_FIXED", [ idx; i32 ]) ->
    ArrayNewFixed (al_to_idx idx, al_to_nat32 i32)
  | CaseV ("ARRAY.NEW_ELEM", [ idx1; idx2 ]) ->
    ArrayNewElem (al_to_idx idx1, al_to_idx idx2)
  | CaseV ("ARRAY.NEW_DATA", [ idx1; idx2 ]) ->
    ArrayNewData (al_to_idx idx1, al_to_idx idx2)
  | CaseV ("ARRAY.GET", [ ext_opt; idx ]) ->
    ArrayGet (al_to_idx idx, al_to_opt al_to_extension ext_opt)
  | CaseV ("ARRAY.SET", [ idx ]) -> ArraySet (al_to_idx idx)
  | CaseV ("ARRAY.LEN", []) -> ArrayLen
  | CaseV ("ARRAY.COPY", [ idx1; idx2 ]) -> ArrayCopy (al_to_idx idx1, al_to_idx idx2)
  | CaseV ("ARRAY.FILL", [ idx ]) -> ArrayFill (al_to_idx idx)
  | CaseV ("ARRAY.INIT_DATA", [ idx1; idx2 ]) ->
    ArrayInitData (al_to_idx idx1, al_to_idx idx2)
  | CaseV ("ARRAY.INIT_ELEM", [ idx1; idx2 ]) ->
    ArrayInitElem (al_to_idx idx1, al_to_idx idx2)
  | CaseV ("ANY.CONVERT_EXTERN", []) -> ExternConvert Internalize
  | CaseV ("EXTERN.CONVERT_ANY", []) -> ExternConvert Externalize
  | v -> error_value "instruction" v

let al_to_const: value -> const = al_to_list al_to_instr |> al_to_phrase


(* Deconstruct module *)

let al_to_type: value -> type_ = function
  | CaseV ("TYPE", [ rt ]) -> al_to_phrase al_to_rec_type rt
  | v -> error_value "type" v

let al_to_local': value -> local' = function
  | CaseV ("LOCAL", [ vt ]) -> { ltype = al_to_val_type vt }
  | v -> error_value "local" v
let al_to_local: value -> local = al_to_phrase al_to_local'

let al_to_func': value -> func' = function
  | CaseV ("FUNC", [ idx; locals; instrs ]) ->
    {
      ftype = al_to_idx idx;
      locals = al_to_list al_to_local locals;
      body = al_to_list al_to_instr instrs;
    }
  | v -> error_value "func" v
let al_to_func: value -> func = al_to_phrase al_to_func'

let al_to_global': value -> global' = function
  | CaseV ("GLOBAL", [ gt; const ]) ->
    { gtype = al_to_global_type gt; ginit = al_to_const const }
  | v -> error_value "global" v
let al_to_global: value -> global = al_to_phrase al_to_global'

let al_to_table': value -> table' = function
  | CaseV ("TABLE", [ tt; const ]) ->
    { ttype = al_to_table_type tt; tinit = al_to_const const }
  | v -> error_value "table" v
let al_to_table: value -> table = al_to_phrase al_to_table'

let al_to_memory': value -> memory' = function
  | CaseV ("MEMORY", [ mt ]) -> { mtype = al_to_memory_type mt }
  | v -> error_value "memory" v
let al_to_memory: value -> memory = al_to_phrase al_to_memory'

let al_to_tag': value -> tag' = function
  | CaseV ("TAG", [ CaseV ("_IDX", [ idx ]) ]) -> { tgtype = al_to_idx idx }
  | v -> error_value "tag" v
let al_to_tag: value -> tag = al_to_phrase al_to_tag'

let al_to_segment': value -> segment_mode' = function
  | CaseV ("PASSIVE", []) -> Passive
  | CaseV ("ACTIVE", [ idx; const ]) ->
    Active { index = al_to_idx idx; offset = al_to_const const }
  | CaseV ("DECLARE", []) -> Declarative
  | v -> error_value "segment mode" v
let al_to_segment: value -> segment_mode = al_to_phrase al_to_segment'

let al_to_elem': value -> elem_segment' = function
  | CaseV ("ELEM", [ rt; consts; seg ]) ->
    {
      etype = al_to_ref_type rt;
      einit = al_to_list al_to_const consts;
      emode = al_to_segment seg
    }
  | v -> error_value "elem segment" v
let al_to_elem: value -> elem_segment = al_to_phrase al_to_elem'

let al_to_data': value -> data_segment' = function
  | CaseV ("DATA", [ bytes_; seg ]) ->
    { dinit = al_to_bytes bytes_; dmode = al_to_segment seg }
  | v -> error_value "data segment" v
let al_to_data: value -> data_segment = al_to_phrase al_to_data'

let al_to_extern_type types = function
  | CaseV ("FUNC", [ CaseV ("_DEF", _) as dt ]) -> ExternFuncT (al_to_def_type dt)
  | CaseV ("FUNC", [ CaseV ("_IDX", [ idx ]) ]) -> ExternFuncT (List.nth types (Int32.to_int (al_to_idx idx).it))
  | CaseV ("GLOBAL", [globaltype]) -> ExternGlobalT (al_to_global_type globaltype)
  | CaseV ("TABLE", [tabletype]) -> ExternTableT (al_to_table_type tabletype)
  | CaseV ("MEM", [memtype]) -> ExternMemoryT (al_to_memory_type memtype)
  | CaseV ("TAG", [ CaseV ("_DEF", _) as dt ]) -> ExternTagT (TagT (al_to_def_type dt))
  | CaseV ("TAG", [ CaseV ("_IDX", [ idx ]) ]) -> ExternTagT (TagT (List.nth types (Int32.to_int (al_to_idx idx).it)))
  | v -> error_value "extern_type" v

let al_to_import_desc' types = function
  | CaseV ("FUNC", [ CaseV ("_IDX", [ idx ]) ]) -> FuncImport (al_to_idx idx)
  | CaseV ("FUNC", [ CaseV ("_DEF", _) as dt ]) ->
    let x =
      { empty_module with types } @@ no_region
      |> def_types_of
      |> List.mapi (fun idx dt' -> idx, dt')
      |> List.find_map (fun (idx, dt') -> if al_to_def_type dt = dt' then Some idx else None)
      |> Option.get
      |> Int32.of_int
    in
    FuncImport (x @@ no_region)
  | CaseV ("TABLE", [ tt ]) -> TableImport (al_to_table_type tt)
  | CaseV ("MEM", [ mt ]) -> MemoryImport (al_to_memory_type mt)
  | CaseV ("GLOBAL", [ gt ]) -> GlobalImport (al_to_global_type gt)
  | CaseV ("TAG", [ CaseV ("_IDX", [ idx ]) ]) -> TagImport (al_to_idx idx)
  | CaseV ("TAG", [ CaseV ("_DEF", _) as dt ]) ->
    let x =
      { empty_module with types } @@ no_region
      |> def_types_of
      |> List.mapi (fun idx dt' -> idx, dt')
      |> List.find_map (fun (idx, dt') -> if al_to_def_type dt = dt' then Some idx else None)
      |> Option.get
      |> Int32.of_int
    in
    TagImport (x @@ no_region)
  | v -> error_value "import desc" v
let al_to_import_desc types idesc = al_to_import_desc' types idesc @@ no_region

let al_to_import types = function
  | CaseV ("IMPORT", [ module_name; item_name; idesc ]) ->
    { module_name = al_to_name module_name;
      item_name = al_to_name item_name;
      idesc = al_to_import_desc types idesc;
    } @@ no_region
  | v -> error_value "import" v

let al_to_export_desc': value -> export_desc' = function
  | CaseV ("FUNC", [ idx ]) -> FuncExport (al_to_idx idx)
  | CaseV ("TABLE", [ idx ]) -> TableExport (al_to_idx idx)
  | CaseV ("MEM", [ idx ]) -> MemoryExport (al_to_idx idx)
  | CaseV ("GLOBAL", [ idx ]) -> GlobalExport (al_to_idx idx)
  | CaseV ("TAG", [ idx ]) -> TagExport (al_to_idx idx)
  | v -> error_value "export desc" v
let al_to_export_desc: value -> export_desc = al_to_phrase al_to_export_desc'

let al_to_start': value -> start' = function
  | CaseV ("START", [ idx ]) -> { sfunc = al_to_idx idx }
  | v -> error_value "start" v
let al_to_start: value -> start = al_to_phrase al_to_start'

let al_to_export': value -> export' = function
  | CaseV ("EXPORT", [ name; ed ]) ->
    { name = al_to_name name; edesc = al_to_export_desc ed }
  | v -> error_value "export" v
let al_to_export: value -> export = al_to_phrase al_to_export'

let rec al_to_module': value -> module_' = function
  | CaseV ("MODULE", [
      types; imports; funcs; globals; tables; memories; elems; datas; start; exports
    ]) when !version < 3 ->
    al_to_module' (CaseV ("MODULE", [
      types; imports; listV [||]; globals; memories; tables; funcs; datas; elems; start; exports
    ]))
  | CaseV ("MODULE", [
      types; imports; tags; globals; memories; tables; funcs; datas; elems; start; exports
    ]) ->
    {
      types = al_to_list al_to_type types;
      imports = al_to_list (al_to_import (al_to_list al_to_type types)) imports;
      tags = al_to_list al_to_tag tags;
      globals = al_to_list al_to_global globals;
      memories = al_to_list al_to_memory memories;
      tables = al_to_list al_to_table tables;
      funcs = al_to_list al_to_func funcs;
      datas = al_to_list al_to_data datas;
      elems = al_to_list al_to_elem elems;
      start = al_to_opt al_to_start start;
      exports = al_to_list al_to_export exports;
    }
  | v -> error_value "module" v
let al_to_module: value -> module_ = al_to_phrase al_to_module'


(* Destruct value *)

let rec al_to_field: value -> Aggr.field = function
  | CaseV ("PACK", [pack_size; c]) ->
    (* TODO: fix bug in packsize *)
    let pack_size' =
      match pack_size with
      | CaseV ("I8", []) -> Pack.Pack8
      | CaseV ("I16", []) -> Pack.Pack16
      | CaseV ("I32", []) -> Pack.Pack32
      | CaseV ("I64", []) -> Pack.Pack64
      | v -> error_value "packsize" v
    in
    Aggr.PackField (pack_size', ref (al_to_nat c))
  | v -> Aggr.ValField (ref (al_to_value v))

and al_to_array: value -> Aggr.array = function
  | StrV r when Record.mem "TYPE" r && Record.mem "FIELDS" r ->
    Aggr.Array (
      al_to_def_type (Record.find "TYPE" r),
      al_to_list al_to_field (Record.find "FIELDS" r)
    )
  | v -> error_value "array" v

and al_to_struct: value -> Aggr.struct_ = function
  | StrV r when Record.mem "TYPE" r && Record.mem "FIELDS" r ->
    Aggr.Struct (
      al_to_def_type (Record.find "TYPE" r),
      al_to_list al_to_field (Record.find "FIELDS" r)
    )
  | v -> error_value "struct" v

and al_to_tag: value -> Tag.t = function
  | StrV r when Record.mem "TYPE" r ->
    Tag.alloc (al_to_tag_type (Record.find "TYPE" r))
  | v -> error_value "tag" v

and al_to_exn: value -> Exn.exn_ = function
  | StrV r when Record.mem "TAG" r && Record.mem "FIELDS" r ->
    let tag_insts = Ds.Store.access "TAGS" in
    let tag = Record.find "TAG" r |> al_to_nat |> listv_nth tag_insts |> al_to_tag in
    Exn.Exn (
      tag,
      al_to_list al_to_value (Record.find "FIELDS" r)
    )
  | v -> error_value "exn" v

and al_to_funcinst: value -> Instance.func_inst = function
  | StrV r when Record.mem "TYPE" r && Record.mem "MODULE" r && Record.mem "CODE" r ->
    Func.AstFunc (
      al_to_def_type (Record.find "TYPE" r),
      Reference_interpreter.Lib.Promise.make (), (* TODO: Fulfill the promise with module instance *)
      al_to_func (Record.find "CODE" r)
    )
  | v -> error_value "funcinst" v

and al_to_ref: value -> ref_ = function
  | CaseV ("REF.NULL", [ ht ]) -> NullRef (al_to_heap_type ht)
  | CaseV ("REF.I31_NUM", [ i ]) -> I31.I31Ref (al_to_nat i)
  | CaseV ("REF.STRUCT_ADDR", [ addr ]) ->
    let struct_insts = Ds.Store.access "STRUCTS" in
    let struct_ = addr |> al_to_nat |> listv_nth struct_insts |> al_to_struct in
    Aggr.StructRef struct_
  | CaseV ("REF.ARRAY_ADDR", [ addr ]) ->
    let arr_insts = Ds.Store.access "ARRAYS" in
    let arr = addr |> al_to_nat |> listv_nth arr_insts |> al_to_array in
    Aggr.ArrayRef arr
  | CaseV ("REF.FUNC_ADDR", [ addr ]) ->
    let func_insts = Ds.Store.access "FUNCS" in
    let func = addr |> al_to_nat |> listv_nth func_insts |> al_to_funcinst in
    Instance.FuncRef func
  | CaseV ("REF.HOST_ADDR", [ i32 ]) -> Script.HostRef (al_to_nat32 i32)
  | CaseV ("REF.EXTERN", [ r ]) -> Extern.ExternRef (al_to_ref r)
  | v -> error_value "ref" v

and al_to_value: value -> Value.value = function
  | CaseV ("CONST", _) as v -> Num (al_to_num v)
  | CaseV (ref_, _) as v when String.sub ref_ 0 4 = "REF." -> Ref (al_to_ref v)
  | CaseV ("VCONST", _) as v -> Vec (al_to_vec v)
  | v -> error_value "value" v


(* Construct *)

(* Construct data structure *)

let al_of_list f l = List.map f l |> listV_of_list
let al_of_seq f s = List.of_seq s |> al_of_list f
let al_of_opt f opt = Option.map f opt |> optV


(* Construct minor *)

let al_of_z_nat z = natV z
let al_of_z_int z = intV z

let al_of_fmagN layout i =
  let n = Z.logand i (mask_exp layout) in
  let m = Z.logand i (mask_mant layout) in
  if n = Z.zero then
    CaseV ("SUBNORM", [ al_of_z_nat m ])
  else if n <> mask_exp layout then
    CaseV ("NORM", [ al_of_z_nat m; al_of_z_int Z.(shift_right n layout.mantissa - bias layout) ])
  else if m = Z.zero then
    CaseV ("INF", [])
  else
    CaseV ("NAN", [ al_of_z_nat m ])

let al_of_floatN layout i =
  let i' = Z.logand i (mask_mag layout) in
  let mag = al_of_fmagN layout i in
  CaseV ((if i' = i then "POS" else "NEG"), [ mag ])

let vec128_to_z vec =
  match V128.I64x2.to_lanes vec with
  | [ v1; v2 ] -> Z.(of_int64_unsigned v1 + e64 * of_int64_unsigned v2)
  | _ -> assert false

let al_of_nat i = Z.of_int i |> al_of_z_nat
let al_of_nat8 i8 =
  (* NOTE: int8 is considered to be unsigned *)
  Z.of_int32_unsigned Int32.(logand i8 0x0000_00ffl) |> al_of_z_nat
let al_of_nat16 i16 =
  (* NOTE: int32 is considered to be unsigned *)
  Z.of_int32_unsigned Int32.(logand i16 0x0000_ffffl) |> al_of_z_nat
let al_of_nat32 i32 =
  (* NOTE: int32 is considered to be unsigned *)
  Z.of_int32_unsigned i32 |> al_of_z_nat
let al_of_nat64 i64 =
  (* NOTE: int32 is considered to be unsigned *)
  Z.of_int64_unsigned i64 |> al_of_z_nat
let al_of_float32 f32 = F32.to_bits f32 |> Z.of_int32_unsigned |> al_of_floatN layout32
let al_of_float64 f64 = F64.to_bits f64 |> Z.of_int64_unsigned |> al_of_floatN layout64
let al_of_vec128 vec = vec128_to_z vec |> al_of_z_nat
let al_of_bool b = Stdlib.Bool.to_int b |> al_of_nat
let al_of_idx idx = al_of_nat32 idx.it
let al_of_byte byte = Char.code byte |> al_of_nat
let al_of_bytes bytes_ = String.to_seq bytes_ |> al_of_seq al_of_byte
let al_of_name name = TextV (Utf8.encode name)
let al_with_version vs f a = if (List.mem !version vs) then [ f a ] else []
let al_of_memidx idx = al_with_version [ 3 ] (fun v -> v) (al_of_idx idx)

(* Helper *)

let arg_of_case case i = function
| CaseV (case', args) when case = case' -> List.nth args i
| v -> fail_value "arg_of_case" v

let arg_of_tup i = function
| TupV args -> List.nth args i
| v -> fail_value "arg_of_tup" v

(* Construct type *)

let al_of_null = function
  | NoNull -> none "NULL"
  | Null -> some "NULL"

let al_of_final = function
  | NoFinal -> none "FINAL"
  | Final -> some "FINAL"

let al_of_mut = function
  | Cons -> none "MUT"
  | Var -> some "MUT"

let rec al_of_storage_type = function
  | ValStorageT vt -> al_of_val_type vt
  | PackStorageT _ as st -> nullary (string_of_storage_type st)

and al_of_field_type = function
  | FieldT (mut, st) -> CaseV ("", [ al_of_mut mut; al_of_storage_type st ])

and al_of_result_type rt = al_of_list al_of_val_type rt

and al_of_str_type = function
  | DefStructT (StructT ftl) -> CaseV ("STRUCT", [ al_of_list al_of_field_type ftl ])
  | DefArrayT (ArrayT ft) -> CaseV ("ARRAY", [ al_of_field_type ft ])
  | DefFuncT (FuncT (rt1, rt2)) ->
    CaseV ("FUNC", [ CaseV ("->", [ al_of_result_type rt1; al_of_result_type rt2 ])])

and al_of_sub_type = function
  | SubT (fin, htl, st) ->
    CaseV ("SUB", [ al_of_final fin; al_of_list al_of_heap_type htl; al_of_str_type st ])

and al_of_rec_type = function
  | RecT stl -> CaseV ("REC", [ al_of_list al_of_sub_type stl ])

and al_of_def_type = function
  | DefT (rt, i) -> CaseV ("_DEF", [al_of_rec_type rt; al_of_nat32 i])

and al_of_typeuse = function
  | idx when !version <= 2 -> al_of_idx idx
  | idx -> CaseV ("_IDX", [ al_of_idx idx ])

and al_of_heap_type = function
  | VarHT (StatX i) -> CaseV ("_IDX", [ al_of_nat32 i ])
  | VarHT (RecX i) -> CaseV ("REC", [ al_of_nat32 i ])
  | DefHT dt -> al_of_def_type dt
  | BotHT -> nullary "BOT"
  | FuncHT | ExternHT as ht when !version = 2 ->
    string_of_heap_type ht ^ "REF" |> nullary
  | ht -> string_of_heap_type ht |> nullary

and al_of_ref_type (null, ht) =
  if !version = 3 then
    CaseV ("REF", [ al_of_null null; al_of_heap_type ht ])
  else
    al_of_heap_type ht

and al_of_addr_type at = string_of_addr_type at |> nullary

and al_of_num_type nt = string_of_num_type nt |> nullary

and al_of_vec_type vt = string_of_vec_type vt |> nullary

and al_of_val_type = function
  | RefT rt -> al_of_ref_type rt
  | NumT nt -> al_of_num_type nt
  | VecT vt -> al_of_vec_type vt
  | BotT -> nullary "BOT"

let al_of_blocktype = function
  | VarBlockType idx -> CaseV ("_IDX", [ al_of_idx idx ])
  | ValBlockType vt_opt ->
    if !version = 1 then
      al_of_opt al_of_val_type vt_opt
    else
      CaseV ("_RESULT", [ al_of_opt al_of_val_type vt_opt ])

let al_of_limits default limits =
  let max =
    match limits.max with
    | Some v -> al_of_nat64 v
    | None -> al_of_nat64 default
  in

  CaseV ("[", [ al_of_nat64 limits.min; max ]) (* TODO: Something better tan this is needed *)

let al_of_tag_type = function
  | TagT dt -> al_of_def_type dt

let al_of_global_type = function
  | GlobalT (mut, vt) -> CaseV ("", [ al_of_mut mut; al_of_val_type vt ])

let al_of_table_type = function
  | TableT (at, limits, rt) ->
    match !version with
    | 3 -> CaseV ("", [ al_of_addr_type at; al_of_limits default_table_max limits; al_of_ref_type rt ])
    | _ -> CaseV ("", [                     al_of_limits default_table_max limits; al_of_ref_type rt ])

let al_of_memory_type = function
  | MemoryT (at, limits) ->
    match !version with
    | 3 -> CaseV ("PAGE", [ al_of_addr_type at; al_of_limits default_memory_max limits ])
    | _ -> CaseV ("PAGE", [                     al_of_limits default_memory_max limits ])

(* Construct value *)

let al_of_num = function
  | I32 i32 -> CaseV ("CONST", [ nullary "I32"; al_of_nat32 i32 ])
  | I64 i64 -> CaseV ("CONST", [ nullary "I64"; al_of_nat64 i64 ])
  | F32 f32 -> CaseV ("CONST", [ nullary "F32"; al_of_float32 f32 ])
  | F64 f64 -> CaseV ("CONST", [ nullary "F64"; al_of_float64 f64 ])

let al_of_vec = function
  | V128 v128 -> CaseV ("VCONST", [ nullary "V128"; al_of_vec128 v128 ])

let al_of_vec_shape shape (lanes: int64 list) =
  al_of_vec (V128  (
    match shape with
    | V128.I8x16() -> V128.I8x16.of_lanes (List.map Int64.to_int32 lanes)
    | V128.I16x8() -> V128.I16x8.of_lanes (List.map Int64.to_int32 lanes)
    | V128.I32x4() -> V128.I32x4.of_lanes (List.map Int64.to_int32 lanes)
    | V128.I64x2() -> V128.I64x2.of_lanes lanes
    | V128.F32x4() -> V128.F32x4.of_lanes (List.map (fun i -> i |> Int64.to_int32 |> F32.of_bits) lanes)
    | V128.F64x2() -> V128.F64x2.of_lanes (List.map F64.of_bits lanes)
  ))

let rec al_of_ref = function
  | NullRef ht -> CaseV ("REF.NULL", [ al_of_heap_type ht ])
  (*
  | I31.I31Ref i ->
    CaseV ("REF.I31_NUM", [ NumV (Int64.of_int i) ])
  | Aggr.StructRef a ->
    CaseV ("REF.STRUCT_ADDR", [ NumV (int64_of_int32_u a) ])
  | Aggr.ArrayRef a ->
    CaseV ("REF.ARRAY_ADDR", [ NumV (int64_of_int32_u a) ])
  | Instance.FuncRef a ->
    CaseV ("REF.FUNC_ADDR", [ NumV (int64_of_int32_u a) ])
  *)
  | Script.HostRef i32 -> CaseV ("REF.HOST_ADDR", [ al_of_nat32 i32 ])
  | Extern.ExternRef r -> CaseV ("REF.EXTERN", [ al_of_ref r ])
  | r -> string_of_ref r |> error "al_of_ref"

let al_of_value = function
  | Num n -> al_of_num n
  | Vec v -> al_of_vec v
  | Ref r -> al_of_ref r


(* Construct operation *)

let al_of_op f1 f2 = function
  | I32 op -> [ nullary "I32"; f1 op ]
  | I64 op -> [ nullary "I64"; f1 op ]
  | F32 op -> [ nullary "F32"; f2 op ]
  | F64 op -> [ nullary "F64"; f2 op ]

let al_of_int_unop = function
  | IntOp.Clz -> CaseV ("CLZ", [])
  | IntOp.Ctz -> CaseV ("CTZ", [])
  | IntOp.Popcnt -> CaseV ("POPCNT", [])
  | IntOp.ExtendS Pack.Pack8 -> CaseV ("EXTEND", [al_of_nat 8])
  | IntOp.ExtendS Pack.Pack16 -> CaseV ("EXTEND", [al_of_nat 16])
  | IntOp.ExtendS Pack.Pack32 -> CaseV ("EXTEND", [al_of_nat 32])
  | IntOp.ExtendS Pack.Pack64 -> CaseV ("EXTEND", [al_of_nat 64])

let al_of_float_unop = function
  | FloatOp.Neg -> CaseV ("NEG", [])
  | FloatOp.Abs -> CaseV ("ABS", [])
  | FloatOp.Ceil -> CaseV ("CEIL", [])
  | FloatOp.Floor -> CaseV ("FLOOR", [])
  | FloatOp.Trunc -> CaseV ("TRUNC", [])
  | FloatOp.Nearest -> CaseV ("NEAREST", [])
  | FloatOp.Sqrt -> CaseV ("SQRT", [])

let al_of_unop = al_of_op al_of_int_unop al_of_float_unop

let al_of_int_binop = function
  | IntOp.Add -> CaseV ("ADD", [])
  | IntOp.Sub -> CaseV ("SUB", [])
  | IntOp.Mul -> CaseV ("MUL", [])
  | IntOp.DivS -> CaseV ("DIV", [CaseV ("S", [])])
  | IntOp.DivU -> CaseV ("DIV", [CaseV ("U", [])])
  | IntOp.RemS -> CaseV ("REM", [CaseV ("S", [])])
  | IntOp.RemU -> CaseV ("REM", [CaseV ("U", [])])
  | IntOp.And -> CaseV ("AND", [])
  | IntOp.Or -> CaseV ("OR", [])
  | IntOp.Xor -> CaseV ("XOR", [])
  | IntOp.Shl -> CaseV ("SHL", [])
  | IntOp.ShrS -> CaseV ("SHR", [CaseV ("S", [])])
  | IntOp.ShrU -> CaseV ("SHR", [CaseV ("U", [])])
  | IntOp.Rotl -> CaseV ("ROTL", [])
  | IntOp.Rotr -> CaseV ("ROTR", [])

let al_of_float_binop = function
  | FloatOp.Add -> CaseV ("ADD", [])
  | FloatOp.Sub -> CaseV ("SUB", [])
  | FloatOp.Mul -> CaseV ("MUL", [])
  | FloatOp.Div -> CaseV ("DIV", [])
  | FloatOp.Min -> CaseV ("MIN", [])
  | FloatOp.Max -> CaseV ("MAX", [])
  | FloatOp.CopySign -> CaseV ("COPYSIGN", [])

let al_of_binop = al_of_op al_of_int_binop al_of_float_binop

let al_of_int_testop: IntOp.testop -> value = function
  | IntOp.Eqz -> CaseV ("EQZ", [])

let al_of_float_testop: FloatOp.testop -> value = function
  | _ -> .

let al_of_testop: testop -> value list = al_of_op al_of_int_testop al_of_float_testop

let al_of_int_relop = function
  | IntOp.Eq -> CaseV ("EQ", [])
  | IntOp.Ne -> CaseV ("NE", [])
  | IntOp.LtS -> CaseV ("LT", [CaseV ("S", [])])
  | IntOp.LtU -> CaseV ("LT", [CaseV ("U", [])])
  | IntOp.GtS -> CaseV ("GT", [CaseV ("S", [])])
  | IntOp.GtU -> CaseV ("GT", [CaseV ("U", [])])
  | IntOp.LeS -> CaseV ("LE", [CaseV ("S", [])])
  | IntOp.LeU -> CaseV ("LE", [CaseV ("U", [])])
  | IntOp.GeS -> CaseV ("GE", [CaseV ("S", [])])
  | IntOp.GeU -> CaseV ("GE", [CaseV ("U", [])])

let al_of_float_relop = function
  | FloatOp.Eq -> CaseV ("EQ", [])
  | FloatOp.Ne -> CaseV ("NE", [])
  | FloatOp.Lt -> CaseV ("LT", [])
  | FloatOp.Gt -> CaseV ("GT", [])
  | FloatOp.Le -> CaseV ("LE", [])
  | FloatOp.Ge -> CaseV ("GE", [])

let al_of_relop = al_of_op al_of_int_relop al_of_float_relop

let al_of_int_cvtop num_bits = function
  | IntOp.ExtendSI32 -> "I32", "EXTEND", [ nullary "S" ]
  | IntOp.ExtendUI32 -> "I32", "EXTEND", [ nullary "U" ]
  | IntOp.WrapI64 -> "I64", "WRAP", []
  | IntOp.TruncSF32 -> "F32", "TRUNC", [ nullary "S" ]
  | IntOp.TruncUF32 -> "F32", "TRUNC", [ nullary "U" ]
  | IntOp.TruncSF64 -> "F64", "TRUNC", [ nullary "S" ]
  | IntOp.TruncUF64 -> "F64", "TRUNC", [ nullary "U" ]
  | IntOp.TruncSatSF32 -> "F32", "TRUNC_SAT", [ nullary "S" ]
  | IntOp.TruncSatUF32 -> "F32", "TRUNC_SAT", [ nullary "U" ]
  | IntOp.TruncSatSF64 -> "F64", "TRUNC_SAT", [ nullary "S" ]
  | IntOp.TruncSatUF64 -> "F64", "TRUNC_SAT", [ nullary "U" ]
  | IntOp.ReinterpretFloat -> "F" ^ num_bits, "REINTERPRET", []

let al_of_float_cvtop num_bits = function
  | FloatOp.ConvertSI32 -> "I32", "CONVERT", [ nullary "S" ]
  | FloatOp.ConvertUI32 -> "I32", "CONVERT", [ nullary "U" ]
  | FloatOp.ConvertSI64 -> "I64", "CONVERT", [ nullary "S" ]
  | FloatOp.ConvertUI64 -> "I64", "CONVERT", [ nullary "U" ]
  | FloatOp.PromoteF32 -> "F32", "PROMOTE", []
  | FloatOp.DemoteF64 -> "F64", "DEMOTE", []
  | FloatOp.ReinterpretInt -> "I" ^ num_bits, "REINTERPRET", []

let al_of_cvtop = function
  | I32 op ->
    let to_, op', ext = al_of_int_cvtop "32" op in
    [ nullary "I32"; nullary to_; caseV (op', ext) ]
  | I64 op ->
    let to_, op', ext = al_of_int_cvtop "64" op in
    [ nullary "I64"; nullary to_; caseV (op', ext) ]
  | F32 op ->
    let to_, op', ext = al_of_float_cvtop "32" op in
    [ nullary "F32"; nullary to_; caseV (op', ext) ]
  | F64 op ->
    let to_, op', ext = al_of_float_cvtop "64" op in
    [ nullary "F64"; nullary to_; caseV (op', ext) ]

(* Vector operator *)

let al_of_extension = function
  | Pack.SX -> nullary "S"
  | Pack.ZX -> nullary "U"

let al_of_vop f1 f2 = function
  | V128 vop -> (
    match vop with
    | V128.I8x16 op -> [ CaseV ("X", [ nullary "I8"; numV sixteen ]); f1 op ]
    | V128.I16x8 op -> [ CaseV ("X", [ nullary "I16"; numV eight ]); f1 op ]
    | V128.I32x4 op -> [ CaseV ("X", [ nullary "I32"; numV four ]); f1 op ]
    | V128.I64x2 op -> [ CaseV ("X", [ nullary "I64"; numV two ]); f1 op ]
    | V128.F32x4 op -> [ CaseV ("X", [ nullary "F32"; numV four ]); f2 op ]
    | V128.F64x2 op -> [ CaseV ("X", [ nullary "F64"; numV two ]); f2 op ]
  )

let al_of_vop_opt f1 f2 = function
  | V128 vop -> (
    match vop with
    | V128.I8x16 op -> Option.map (fun v -> [ CaseV ("X", [ nullary "I8"; numV sixteen ]); v ]) (f1 op)
    | V128.I16x8 op -> Option.map (fun v -> [ CaseV ("X", [ nullary "I16"; numV eight ]); v ]) (f1 op)
    | V128.I32x4 op -> Option.map (fun v -> [ CaseV ("X", [ nullary "I32"; numV four ]); v ]) (f1 op)
    | V128.I64x2 op -> Option.map (fun v -> [ CaseV ("X", [ nullary "I64"; numV two ]); v ]) (f1 op)
    | V128.F32x4 op -> Option.map (fun v -> [ CaseV ("X", [ nullary "F32"; numV four ]); v ]) (f2 op)
    | V128.F64x2 op -> Option.map (fun v -> [ CaseV ("X", [ nullary "F64"; numV two ]); v ]) (f2 op)
  )

let al_of_viop f1:
    ('a, 'a, 'a, 'a, void, void) V128.laneop vecop -> value list = function
  | V128 vop -> (
    match vop with
    | V128.I8x16 op -> [ CaseV ("X", [ nullary "I8"; numV sixteen ]); f1 op ]
    | V128.I16x8 op -> [ CaseV ("X", [ nullary "I16"; numV eight ]); f1 op ]
    | V128.I32x4 op -> [ CaseV ("X", [ nullary "I32"; numV four ]); f1 op ]
    | V128.I64x2 op -> [ CaseV ("X", [ nullary "I64"; numV two ]); f1 op ]
    | _ -> .
  )

let al_of_vbitmaskop = function
  | V128 (vop : V128Op.bitmaskop) -> (
    match vop with
    | V128.I8x16 _ -> [ CaseV ("X", [ nullary "I8"; numV sixteen ]) ]
    | V128.I16x8 _ -> [ CaseV ("X", [ nullary "I16"; numV eight ]) ]
    | V128.I32x4 _ -> [ CaseV ("X", [ nullary "I32"; numV four ]) ]
    | V128.I64x2 _ -> [ CaseV ("X", [ nullary "I64"; numV two ]) ]
    | _ -> .
  )

let al_of_int_vtestop : V128Op.itestop -> value = function
  | V128Op.AllTrue -> nullary "ALL_TRUE"

let al_of_float_vtestop : Ast.void -> value = function
  | _ -> .

let al_of_vtestop = al_of_vop al_of_int_vtestop al_of_float_vtestop

let al_of_int_vrelop : V128Op.irelop -> value = function
  | V128Op.Eq -> nullary "EQ"
  | V128Op.Ne -> nullary "NE"
  | V128Op.LtS -> caseV ("LT", [nullary "S"])
  | V128Op.LtU -> caseV ("LT", [nullary "U"])
  | V128Op.LeS -> caseV ("LE", [nullary "S"])
  | V128Op.LeU -> caseV ("LE", [nullary "U"])
  | V128Op.GtS -> caseV ("GT", [nullary "S"])
  | V128Op.GtU -> caseV ("GT", [nullary "U"])
  | V128Op.GeS -> caseV ("GE", [nullary "S"])
  | V128Op.GeU -> caseV ("GE", [nullary "U"])

let al_of_float_vrelop : V128Op.frelop -> value = function
  | V128Op.Eq -> nullary "EQ"
  | V128Op.Ne -> nullary "NE"
  | V128Op.Lt -> nullary "LT"
  | V128Op.Le -> nullary "LE"
  | V128Op.Gt -> nullary "GT"
  | V128Op.Ge -> nullary "GE"

let al_of_vrelop = al_of_vop al_of_int_vrelop al_of_float_vrelop

let al_of_int_vunop : V128Op.iunop -> value = function
  | V128Op.Abs -> nullary "ABS"
  | V128Op.Neg -> nullary "NEG"
  | V128Op.Popcnt -> nullary "POPCNT"

let al_of_float_vunop : V128Op.funop -> value = function
  | V128Op.Abs -> nullary "ABS"
  | V128Op.Neg -> nullary "NEG"
  | V128Op.Sqrt -> nullary "SQRT"
  | V128Op.Ceil -> nullary "CEIL"
  | V128Op.Floor -> nullary "FLOOR"
  | V128Op.Trunc -> nullary "TRUNC"
  | V128Op.Nearest -> nullary "NEAREST"

let al_of_vunop = al_of_vop al_of_int_vunop al_of_float_vunop

let al_of_int_vbinop_opt : V128Op.ibinop -> value option = function
  | V128Op.Add -> Some (nullary "ADD")
  | V128Op.Sub -> Some (nullary "SUB")
  | V128Op.Mul -> Some (nullary "MUL")
  | V128Op.MinS -> Some (caseV ("MIN", [nullary "S"]))
  | V128Op.MinU -> Some (caseV ("MIN", [nullary "U"]))
  | V128Op.MaxS -> Some (caseV ("MAX", [nullary "S"]))
  | V128Op.MaxU -> Some (caseV ("MAX", [nullary "U"]))
  | V128Op.AvgrU -> Some (nullary "AVGR")
  | V128Op.AddSatS -> Some (caseV ("ADD_SAT", [nullary "S"]))
  | V128Op.AddSatU -> Some (caseV ("ADD_SAT", [nullary "U"]))
  | V128Op.SubSatS -> Some (caseV ("SUB_SAT", [nullary "S"]))
  | V128Op.SubSatU -> Some (caseV ("SUB_SAT", [nullary "U"]))
  | V128Op.Q15MulRSatS -> Some (caseV ("Q15MULR_SAT", [(*nullary "S"*)]))
  | V128Op.RelaxedQ15MulRS -> Some (caseV ("RELAXED_Q15MULR", [(*nullary "S"*)]))
  | _ -> None

let al_of_float_vbinop_opt : V128Op.fbinop -> value option = function
  | V128Op.Add -> Some (nullary "ADD")
  | V128Op.Sub -> Some (nullary "SUB")
  | V128Op.Mul -> Some (nullary "MUL")
  | V128Op.Div -> Some (nullary "DIV")
  | V128Op.Min -> Some (nullary "MIN")
  | V128Op.Max -> Some (nullary "MAX")
  | V128Op.Pmin -> Some (nullary "PMIN")
  | V128Op.Pmax -> Some (nullary "PMAX")
  | V128Op.RelaxedMin -> Some (nullary "RELAXED_MIN")
  | V128Op.RelaxedMax -> Some (nullary "RELAXED_MAX")

let al_of_vbinop_opt = al_of_vop_opt al_of_int_vbinop_opt al_of_float_vbinop_opt

let al_of_int_vternop_opt : V128Op.iternop -> value option = function
  | V128Op.RelaxedLaneselect -> Some (nullary "RELAXED_LANESELECT")
  | _ -> None

let al_of_float_vternop_opt : V128Op.fternop -> value option = function
  | V128Op.RelaxedMadd -> Some (nullary "RELAXED_MADD")
  | V128Op.RelaxedNmadd -> Some (nullary "RELAXED_NMADD")

let al_of_vternop_opt = al_of_vop_opt al_of_int_vternop_opt al_of_float_vternop_opt

let al_of_special_vbinop = function
  | V128 (V128.I8x16 (V128Op.Swizzle)) when !version = 2 -> CaseV ("VSWIZZLE", [ CaseV ("X", [ nullary "I8"; numV sixteen ]); ])
  | V128 (V128.I8x16 (V128Op.Swizzle)) -> CaseV ("VSWIZZLOP", [ CaseV ("X", [ nullary "I8"; numV sixteen ]); nullary "SWIZZLE" ])
  | V128 (V128.I8x16 (V128Op.RelaxedSwizzle)) -> CaseV ("VSWIZZLOP", [ CaseV ("X", [ nullary "I8"; numV sixteen ]); nullary "RELAXED_SWIZZLE" ])
  | V128 (V128.I8x16 (V128Op.Shuffle l)) -> CaseV ("VSHUFFLE", [ CaseV ("X", [ nullary "I8"; numV sixteen ]); al_of_list al_of_nat l ])
  | V128 (V128.I8x16 (V128Op.NarrowS)) -> CaseV ("VNARROW", [ CaseV ("X", [ nullary "I8"; numV sixteen ]); CaseV ("X", [ nullary "I16"; numV eight ]); al_of_extension Pack.SX ])
  | V128 (V128.I16x8 (V128Op.NarrowS)) -> CaseV ("VNARROW", [ CaseV ("X", [ nullary "I16"; numV eight ]); CaseV ("X", [ nullary "I32"; numV four ]); al_of_extension Pack.SX ])
  | V128 (V128.I8x16 (V128Op.NarrowU)) -> CaseV ("VNARROW", [ CaseV ("X", [ nullary "I8"; numV sixteen ]); CaseV ("X", [ nullary "I16"; numV eight ]); al_of_extension Pack.ZX ])
  | V128 (V128.I16x8 (V128Op.NarrowU)) -> CaseV ("VNARROW", [ CaseV ("X", [ nullary "I16"; numV eight]); CaseV ("X", [ nullary "I32"; numV four ]); al_of_extension Pack.ZX ])
  | V128 (V128.I16x8 (V128Op.ExtMulHighS)) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I16"; numV eight ]); CaseV ("X", [ nullary "I8"; numV sixteen ]); caseV ("EXTMUL", [nullary "HIGH"; al_of_extension Pack.SX]) ])
  | V128 (V128.I16x8 (V128Op.ExtMulHighU)) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I16"; numV eight ]); CaseV ("X", [ nullary "I8"; numV sixteen ]); caseV ("EXTMUL", [nullary "HIGH"; al_of_extension Pack.ZX]) ])
  | V128 (V128.I16x8 (V128Op.ExtMulLowS)) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I16"; numV eight ]); CaseV ("X", [ nullary "I8"; numV sixteen ]); caseV ("EXTMUL", [nullary "LOW"; al_of_extension Pack.SX]) ])
  | V128 (V128.I16x8 (V128Op.ExtMulLowU)) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I16"; numV eight ]); CaseV ("X", [ nullary "I8"; numV sixteen ]); caseV ("EXTMUL", [nullary "LOW"; al_of_extension Pack.ZX]) ] )
  | V128 (V128.I32x4 (V128Op.ExtMulHighS)) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I32"; numV four ]); CaseV ("X", [ nullary "I16"; numV eight ]); caseV ("EXTMUL", [nullary "HIGH"; al_of_extension Pack.SX]) ])
  | V128 (V128.I32x4 (V128Op.ExtMulHighU)) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I32"; numV four ]); CaseV ("X", [ nullary "I16"; numV eight ]); caseV ("EXTMUL", [nullary "HIGH"; al_of_extension Pack.ZX]) ])
  | V128 (V128.I32x4 (V128Op.ExtMulLowS)) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I32"; numV four ]); CaseV ("X", [ nullary "I16"; numV eight ]); caseV ("EXTMUL", [nullary "LOW"; al_of_extension Pack.SX]) ])
  | V128 (V128.I32x4 (V128Op.ExtMulLowU)) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I32"; numV four ]); CaseV ("X", [ nullary "I16"; numV eight ]); caseV ("EXTMUL", [nullary "LOW"; al_of_extension Pack.ZX]) ] )
  | V128 (V128.I64x2 (V128Op.ExtMulHighS)) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I64"; numV two ]); CaseV ("X", [ nullary "I32"; numV four ]); caseV ("EXTMUL", [nullary "HIGH"; al_of_extension Pack.SX]) ])
  | V128 (V128.I64x2 (V128Op.ExtMulHighU)) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I64"; numV two ]); CaseV ("X", [ nullary "I32"; numV four ]); caseV ("EXTMUL", [nullary "HIGH"; al_of_extension Pack.ZX]) ])
  | V128 (V128.I64x2 (V128Op.ExtMulLowS)) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I64"; numV two ]); CaseV ("X", [ nullary "I32"; numV four ]); caseV ("EXTMUL", [nullary "LOW"; al_of_extension Pack.SX]) ])
  | V128 (V128.I64x2 (V128Op.ExtMulLowU)) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I64"; numV two ]); CaseV ("X", [ nullary "I32"; numV four ]); caseV ("EXTMUL", [nullary "LOW"; al_of_extension Pack.ZX]) ] )
  | V128 (V128.I32x4 (V128Op.DotS)) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I32"; numV four ]); CaseV ("X", [ nullary "I16"; numV eight ]); caseV ("DOT", [(*al_of_extension Pack.SX*)]) ])
  | V128 (V128.I16x8 (V128Op.RelaxedDot)) -> CaseV ("VEXTBINOP", [ CaseV ("X", [ nullary "I16"; numV eight ]); CaseV ("X", [ nullary "I8"; numV sixteen ]); caseV ("RELAXED_DOT", [(*al_of_extension Pack.SX*)]) ])
  | vop -> error_instr "al_of_special_vbinop" (VecBinary vop)

let al_of_special_vternop = function
  | V128 (V128.I32x4 V128Op.RelaxedDotAdd) -> CaseV ("VEXTTERNOP", [ CaseV ("X", [ nullary "I32"; numV four ]); CaseV ("X", [ nullary "I8"; numV sixteen ]); caseV ("RELAXED_DOT_ADD", [(*al_of_extension Pack.SX*)]) ])
  | vop -> error_instr "al_of_special_vternop" (VecTernary vop)

let al_of_int_vcvtop_opt = function
  | V128Op.ExtendLowS -> Some (None, caseV ("EXTEND", [nullary "LOW"; nullary "S"]))
  | V128Op.ExtendLowU -> Some (None, caseV ("EXTEND", [nullary "LOW"; nullary "U"]))
  | V128Op.ExtendHighS -> Some (None, caseV ("EXTEND", [nullary "HIGH"; nullary "S"]))
  | V128Op.ExtendHighU -> Some (None, caseV ("EXTEND", [nullary "HIGH"; nullary "U"]))
  | V128Op.TruncSatSF32x4 -> Some (Some (CaseV ("X", [ nullary "F32"; numV four ])), caseV ("TRUNC_SAT", [nullary "S"; noneV]))
  | V128Op.TruncSatUF32x4 -> Some (Some (CaseV ("X", [ nullary "F32"; numV four ])), caseV ("TRUNC_SAT", [nullary "U"; noneV]))
  | V128Op.TruncSatSZeroF64x2 -> Some (Some (CaseV ("X", [ nullary "F64"; numV two ])), caseV ("TRUNC_SAT", [nullary "S"; someV (nullary "ZERO")]))
  | V128Op.TruncSatUZeroF64x2 -> Some (Some (CaseV ("X", [ nullary "F64"; numV two ])), caseV ("TRUNC_SAT", [nullary "U"; someV (nullary "ZERO")]))
  | V128Op.RelaxedTruncSF32x4 -> Some (Some (CaseV ("X", [ nullary "F32"; numV four ])), caseV ("RELAXED_TRUNC", [nullary "S"; noneV]))
  | V128Op.RelaxedTruncUF32x4 -> Some (Some (CaseV ("X", [ nullary "F32"; numV four ])), caseV ("RELAXED_TRUNC", [nullary "U"; noneV]))
  | V128Op.RelaxedTruncSZeroF64x2 -> Some (Some (CaseV ("X", [ nullary "F64"; numV two ])), caseV ("RELAXED_TRUNC", [nullary "S"; someV (nullary "ZERO")]))
  | V128Op.RelaxedTruncUZeroF64x2 -> Some (Some (CaseV ("X", [ nullary "F64"; numV two ])), caseV ("RELAXED_TRUNC", [nullary "U"; someV (nullary "ZERO")]))
  | _ -> None

let al_of_float32_vcvtop_opt = function
  | V128Op.DemoteZeroF64x2 -> Some (Some (CaseV ("X", [ nullary "F64"; numV two ])), caseV ("DEMOTE", [nullary "ZERO"]))
  | V128Op.ConvertSI32x4 -> Some (Some (CaseV ("X", [ nullary "I32"; numV four ])), caseV ("CONVERT", [noneV; nullary "S"]))
  | V128Op.ConvertUI32x4 -> Some (Some (CaseV ("X", [ nullary "I32"; numV four ])), caseV ("CONVERT", [noneV; nullary "U"]))
  | _ -> None

let al_of_float64_vcvtop_opt = function
  | V128Op.PromoteLowF32x4 -> Some (Some (CaseV ("X", [ nullary "F32"; numV four ])), nullary "PROMOTE")
  | V128Op.ConvertSI32x4 -> Some (Some (CaseV ("X", [ nullary "I32"; numV four ])), caseV ("CONVERT", [someV (nullary "LOW"); nullary "S"]))
  | V128Op.ConvertUI32x4 -> Some (Some (CaseV ("X", [ nullary "I32"; numV four ])), caseV ("CONVERT", [someV (nullary "LOW"); nullary "U"]))
  | _ -> None

let al_of_vcvtop_opt = function
  | V128 vop -> (
    match vop with
    | V128.I8x16 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> error_instr "al_of_vcvtop" (VecConvert (V128 vop)) in
        [ CaseV ("X", [ nullary "I8"; numV sixteen ]); sh; op' ]
      ) (al_of_int_vcvtop_opt op)
    )
    | V128.I16x8 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> CaseV ("X", [ nullary "I8"; numV sixteen ]) in
        [ CaseV ("X", [ nullary "I16"; numV eight ]); sh; op' ]
      ) (al_of_int_vcvtop_opt op)
    )
    | V128.I32x4 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> CaseV ("X", [ nullary "I16"; numV eight ]) in
        [ CaseV ("X", [ nullary "I32"; numV four ]); sh; op' ]
      ) (al_of_int_vcvtop_opt op)
    )
    | V128.I64x2 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> CaseV ("X", [ nullary "I32"; numV four ]) in
        [ CaseV ("X", [ nullary "I64"; numV two ]); sh; op' ]
      ) (al_of_int_vcvtop_opt op)
    )
    | V128.F32x4 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> error_instr "al_of_vcvtop" (VecConvert (V128 vop)) in
        [ CaseV ("X", [ nullary "F32"; numV four ]); sh; op' ]
      ) (al_of_float32_vcvtop_opt op)
    )
    | V128.F64x2 op -> (
      Option.map (fun (to_, op') ->
        let sh = match to_ with Some sh -> sh | None -> error_instr "al_of_vcvtop" (VecConvert (V128 vop)) in
        [ CaseV ("X", [ nullary "F64"; numV two ]); sh; op' ]
      ) (al_of_float64_vcvtop_opt op)
    )
  )


let al_of_special_vcvtop = function
  | V128 (V128.I16x8 (V128Op.ExtAddPairwiseS)) -> CaseV ("VEXTUNOP", [ CaseV ("X", [ nullary "I16"; numV eight]); CaseV ("X", [ nullary "I8"; numV sixteen ]); caseV ("EXTADD_PAIRWISE", [al_of_extension Pack.SX]) ])
  | V128 (V128.I16x8 (V128Op.ExtAddPairwiseU)) -> CaseV ("VEXTUNOP", [ CaseV ("X", [ nullary "I16"; numV eight]); CaseV ("X", [ nullary "I8"; numV sixteen ]); caseV ("EXTADD_PAIRWISE", [al_of_extension Pack.ZX]) ])
  | V128 (V128.I32x4 (V128Op.ExtAddPairwiseS)) -> CaseV ("VEXTUNOP", [ CaseV ("X", [ nullary "I32"; numV four]); CaseV ("X", [ nullary "I16"; numV eight ]); caseV ("EXTADD_PAIRWISE", [al_of_extension Pack.SX]) ])
  | V128 (V128.I32x4 (V128Op.ExtAddPairwiseU)) -> CaseV ("VEXTUNOP", [ CaseV ("X", [ nullary "I32"; numV four]); CaseV ("X", [ nullary "I16"; numV eight ]); caseV ("EXTADD_PAIRWISE", [al_of_extension Pack.ZX]) ])
  | vop -> error_instr "al_of_special_vcvtop" (VecConvert vop)

let al_of_int_vshiftop : V128Op.ishiftop -> value = function
  | V128Op.Shl -> nullary "SHL"
  | V128Op.ShrS -> caseV ("SHR", [nullary "S"])
  | V128Op.ShrU -> caseV ("SHR", [nullary "U"])

let al_of_vshiftop = al_of_viop al_of_int_vshiftop

let al_of_vvtestop : vec_vtestop -> value list = function
  | V128 vop -> (
    match vop with
    | V128Op.AnyTrue ->
      [ nullary "V128"; nullary "ANY_TRUE" ]
  )

let al_of_vvunop : vec_vunop -> value list = function
  | V128 vop -> (
    match vop with
    | V128Op.Not -> [ nullary "V128"; nullary "NOT" ]
  )

let al_of_vvbinop : vec_vbinop -> value list = function
  | V128 vop -> (
    match vop with
    | V128Op.And -> [ nullary "V128"; nullary "AND" ]
    | V128Op.Or -> [ nullary "V128"; nullary "OR" ]
    | V128Op.Xor -> [ nullary "V128"; nullary "XOR" ]
    | V128Op.AndNot -> [ nullary "V128"; nullary "ANDNOT" ]
  )

let al_of_vvternop : vec_vternop -> value list = function
  | V128 vop -> (
    match vop with
    | V128Op.Bitselect ->
      [ nullary "V128"; nullary "BITSELECT" ]
  )

let al_of_vsplatop : vec_splatop -> value list = function
  | V128 vop -> (
    match vop with
    | V128.I8x16 _ -> [ CaseV ("X", [ nullary "I8"; numV sixteen ]) ]
    | V128.I16x8 _ -> [ CaseV ("X", [ nullary "I16"; numV eight ]) ]
    | V128.I32x4 _ -> [ CaseV ("X", [ nullary "I32"; numV four ]) ]
    | V128.I64x2 _ -> [ CaseV ("X", [ nullary "I64"; numV two ]) ]
    | V128.F32x4 _ -> [ CaseV ("X", [ nullary "F32"; numV four ]) ]
    | V128.F64x2 _ -> [ CaseV ("X", [ nullary "F64"; numV two ]) ]
  )

let al_of_vextractop : vec_extractop -> value list = function
  | V128 vop -> (
    match vop with
    | V128.I8x16 vop' -> (
      match vop' with
      | Extract (n, ext) ->
        [ CaseV ("X", [ nullary "I8"; numV sixteen ]); optV (Some (al_of_extension ext)); al_of_nat n; ]
    )
    | V128.I16x8 vop' -> (
      match vop' with
      | Extract (n, ext) ->
        [ CaseV ("X", [ nullary "I16"; numV eight ]); optV (Some (al_of_extension ext)); al_of_nat n; ]
    )
    | V128.I32x4 vop' -> (
      match vop' with
      | Extract (n, _) -> [ CaseV ("X", [ nullary "I32"; numV four ]); optV None; al_of_nat n ]
    )
    | V128.I64x2 vop' -> (
      match vop' with
      | Extract (n, _) -> [ CaseV ("X", [ nullary "I64"; numV two ]); optV None; al_of_nat n ]
    )
    | V128.F32x4 vop' -> (
      match vop' with
      | Extract (n, _) -> [ CaseV ("X", [ nullary "F32"; numV four ]); optV None; al_of_nat n ]
    )
    | V128.F64x2 vop' -> (
      match vop' with
      | Extract (n, _) -> [ CaseV ("X", [ nullary "F64"; numV two ]); optV None; al_of_nat n ]
    )
  )

let al_of_vreplaceop : vec_replaceop -> value list = function
  | V128 vop -> (
    match vop with
    | V128.I8x16 (Replace n) -> [ CaseV ("X", [ nullary "I8"; numV sixteen ]); al_of_nat n ]
    | V128.I16x8 (Replace n) -> [ CaseV ("X", [ nullary "I16"; numV eight ]); al_of_nat n ]
    | V128.I32x4 (Replace n) -> [ CaseV ("X", [ nullary "I32"; numV four ]); al_of_nat n ]
    | V128.I64x2 (Replace n) -> [ CaseV ("X", [ nullary "I64"; numV two ]); al_of_nat n ]
    | V128.F32x4 (Replace n) -> [ CaseV ("X", [ nullary "F32"; numV four ]); al_of_nat n ]
    | V128.F64x2 (Replace n) -> [ CaseV ("X", [ nullary "F64"; numV two ]); al_of_nat n ]
  )

let al_of_pack_size = function
  | Pack.Pack8 -> al_of_nat 8
  | Pack.Pack16 -> al_of_nat 16
  | Pack.Pack32 -> al_of_nat 32
  | Pack.Pack64 -> al_of_nat 64

let al_of_pack_shape = function
  | Pack.Pack8x8 -> [NumV eight; NumV eight]
  | Pack.Pack16x4 -> [NumV sixteen; NumV four]
  | Pack.Pack32x2 -> [NumV thirtytwo; NumV two]

let al_of_extension = function
  | Pack.SX -> nullary "S"
  | Pack.ZX -> nullary "U"

let al_of_memop f idx memop =
  let str =
    Record.empty
    |> Record.add "ALIGN" (al_of_nat memop.align)
    |> Record.add "OFFSET" (al_of_nat64 memop.offset)
  in
  [ al_of_num_type memop.ty; f memop.pack ] @ al_of_memidx idx @ [ StrV str ]

let al_of_pack_size_extension (p, s) =
  CaseV ("_", [ al_of_pack_size p; al_of_extension s ])

let al_of_loadop = al_of_opt al_of_pack_size_extension |> al_of_memop

let al_of_storeop = al_of_opt al_of_pack_size |> al_of_memop

let al_of_vloadop idx vloadop =
  let str =
    Record.empty
    |> Record.add "ALIGN" (al_of_nat vloadop.align)
    |> Record.add "OFFSET" (al_of_nat64 vloadop.offset)
  in

  let vmemop = match vloadop.pack with
  | Option.Some (pack_size, vextension) -> (
    match vextension with
    | Pack.ExtLane (pack_shape, extension) ->
      CaseV ("SHAPE", al_of_pack_shape pack_shape @ [al_of_extension extension])
    | Pack.ExtSplat -> CaseV ("SPLAT", [ al_of_pack_size pack_size ])
    | Pack.ExtZero -> CaseV ("ZERO", [ al_of_pack_size pack_size ])
  ) |> Option.some |> optV
  | None -> OptV None in

  al_of_vec_type V128T :: vmemop :: al_of_memidx idx @ [ StrV str ]

let al_of_vstoreop idx vstoreop =
  let str =
    Record.empty
    |> Record.add "ALIGN" (al_of_nat vstoreop.align)
    |> Record.add "OFFSET" (al_of_nat64 vstoreop.offset)
  in

  al_of_vec_type V128T :: al_of_memidx idx @ [ StrV str ]

let al_of_vlaneop idx vlaneop laneidx =
  let pack_size = vlaneop.pack in

  let str =
    Record.empty
    |> Record.add "ALIGN" (al_of_nat vlaneop.align)
    |> Record.add "OFFSET" (al_of_nat64 vlaneop.offset)
  in

  [ al_of_vec_type V128T; al_of_pack_size pack_size ] @ al_of_memidx idx @ [ StrV str; al_of_nat laneidx ]

(* Construct instruction *)

let al_of_catch catch =
  match catch.it with
  | Catch (idx1, idx2) -> CaseV ("CATCH", [ al_of_idx idx1; al_of_idx idx2 ])
  | CatchRef (idx1, idx2) -> CaseV ("CATCH_REF", [ al_of_idx idx1; al_of_idx idx2 ])
  | CatchAll idx -> CaseV ("CATCH_ALL", [ al_of_idx idx ])
  | CatchAllRef idx -> CaseV ("CATCH_ALL_REF", [ al_of_idx idx ])

let rec al_of_instr instr =
  match instr.it with
  (* wasm values *)
  | Const num -> al_of_num num.it
  | VecConst vec -> al_of_vec vec.it
  | RefNull ht -> CaseV ("REF.NULL", [ al_of_heap_type ht ])
  (* wasm instructions *)
  | Unreachable -> nullary "UNREACHABLE"
  | Nop -> nullary "NOP"
  | Drop -> nullary "DROP"
  | Unary op -> CaseV ("UNOP", al_of_unop op)
  | Binary op -> CaseV ("BINOP", al_of_binop op)
  | Test op -> CaseV ("TESTOP", al_of_testop op)
  | Compare op -> CaseV ("RELOP", al_of_relop op)
  | Convert op -> CaseV ("CVTOP", al_of_cvtop op)
  | VecTest vop -> CaseV ("VTESTOP", al_of_vtestop vop)
  | VecCompare vop -> CaseV ("VRELOP", al_of_vrelop vop)
  | VecUnary vop -> CaseV ("VUNOP", al_of_vunop vop)
  | VecBinary vop -> (match al_of_vbinop_opt vop with Some l -> CaseV ("VBINOP", l) | None -> al_of_special_vbinop vop)
  | VecTernary vop -> (match al_of_vternop_opt vop with Some l -> CaseV ("VTERNOP", l) | None -> al_of_special_vternop vop)
  | VecConvert vop -> (match al_of_vcvtop_opt vop with Some l -> CaseV ("VCVTOP", l) | None -> al_of_special_vcvtop vop)
  | VecShift vop -> CaseV ("VSHIFTOP", al_of_vshiftop vop)
  | VecBitmask vop -> CaseV ("VBITMASK", al_of_vbitmaskop vop)
  | VecTestBits vop -> CaseV ("VVTESTOP", al_of_vvtestop vop)
  | VecUnaryBits vop -> CaseV ("VVUNOP", al_of_vvunop vop)
  | VecBinaryBits vop -> CaseV ("VVBINOP", al_of_vvbinop vop)
  | VecTernaryBits vop -> CaseV ("VVTERNOP", al_of_vvternop vop)
  | VecSplat vop -> CaseV ("VSPLAT", al_of_vsplatop vop)
  | VecExtract vop -> CaseV ("VEXTRACT_LANE", al_of_vextractop vop)
  | VecReplace vop -> CaseV ("VREPLACE_LANE", al_of_vreplaceop vop)
  | RefIsNull -> nullary "REF.IS_NULL"
  | RefFunc idx -> CaseV ("REF.FUNC", [ al_of_idx idx ])
  | Select vtl_opt when !version = 1 -> assert (vtl_opt = None); nullary "SELECT"
  | Select vtl_opt -> CaseV ("SELECT", [ al_of_opt (al_of_list al_of_val_type) vtl_opt ])
  | LocalGet idx -> CaseV ("LOCAL.GET", [ al_of_idx idx ])
  | LocalSet idx -> CaseV ("LOCAL.SET", [ al_of_idx idx ])
  | LocalTee idx -> CaseV ("LOCAL.TEE", [ al_of_idx idx ])
  | GlobalGet idx -> CaseV ("GLOBAL.GET", [ al_of_idx idx ])
  | GlobalSet idx -> CaseV ("GLOBAL.SET", [ al_of_idx idx ])
  | TableGet idx -> CaseV ("TABLE.GET", [ al_of_idx idx ])
  | TableSet idx -> CaseV ("TABLE.SET", [ al_of_idx idx ])
  | TableSize idx -> CaseV ("TABLE.SIZE", [ al_of_idx idx ])
  | TableGrow idx -> CaseV ("TABLE.GROW", [ al_of_idx idx ])
  | TableFill idx -> CaseV ("TABLE.FILL", [ al_of_idx idx ])
  | TableCopy (idx1, idx2) -> CaseV ("TABLE.COPY", [ al_of_idx idx1; al_of_idx idx2 ])
  | TableInit (idx1, idx2) -> CaseV ("TABLE.INIT", [ al_of_idx idx1; al_of_idx idx2 ])
  | ElemDrop idx -> CaseV ("ELEM.DROP", [ al_of_idx idx ])
  | Block (bt, instrs) ->
    CaseV ("BLOCK", [ al_of_blocktype bt; al_of_list al_of_instr instrs ])
  | Loop (bt, instrs) ->
    CaseV ("LOOP", [ al_of_blocktype bt; al_of_list al_of_instr instrs ])
  | If (bt, instrs1, instrs2) ->
    CaseV ("IF", [
      al_of_blocktype bt;
      al_of_list al_of_instr instrs1;
      al_of_list al_of_instr instrs2;
    ])
  | Br idx -> CaseV ("BR", [ al_of_idx idx ])
  | BrIf idx -> CaseV ("BR_IF", [ al_of_idx idx ])
  | BrTable (idxs, idx) ->
    CaseV ("BR_TABLE", [ al_of_list al_of_idx idxs; al_of_idx idx ])
  | BrOnNull idx -> CaseV ("BR_ON_NULL", [ al_of_idx idx ])
  | BrOnNonNull idx -> CaseV ("BR_ON_NON_NULL", [ al_of_idx idx ])
  | BrOnCast (idx, rt1, rt2) ->
    CaseV ("BR_ON_CAST", [ al_of_idx idx; al_of_ref_type rt1; al_of_ref_type rt2 ])
  | BrOnCastFail (idx, rt1, rt2) ->
    CaseV ("BR_ON_CAST_FAIL", [ al_of_idx idx; al_of_ref_type rt1; al_of_ref_type rt2 ])
  | Return -> nullary "RETURN"
  | Call idx -> CaseV ("CALL", [ al_of_idx idx ])
  | CallRef idx -> CaseV ("CALL_REF", [ optV (Some (al_of_idx idx)) ])
  | CallIndirect (idx1, idx2) ->
    let args = al_with_version [ 2; 3 ] al_of_idx idx1 @ [ al_of_typeuse idx2 ] in
    CaseV ("CALL_INDIRECT", args)
  | ReturnCall idx -> CaseV ("RETURN_CALL", [ al_of_idx idx ])
  | ReturnCallRef idx -> CaseV ("RETURN_CALL_REF", [ optV (Some (al_of_typeuse idx)) ])
  | ReturnCallIndirect (idx1, idx2) ->
    CaseV ("RETURN_CALL_INDIRECT", [ al_of_idx idx1; al_of_typeuse idx2 ])
  | Throw idx -> CaseV ("THROW", [ al_of_idx idx ])
  | ThrowRef -> nullary "THROW_REF"
  | TryTable (bt, catches, instrs) ->
    CaseV ("TRY_TABLE", [
      al_of_blocktype bt;
      al_of_list al_of_catch catches;
      al_of_list al_of_instr instrs
    ])
  | Load (idx, loadop) -> CaseV ("LOAD", al_of_loadop idx loadop)
  | Store (idx, storeop) -> CaseV ("STORE", al_of_storeop idx storeop)
  | VecLoad (idx, vloadop) -> CaseV ("VLOAD", al_of_vloadop idx vloadop)
  | VecLoadLane (idx, vlaneop, i) -> CaseV ("VLOAD_LANE", al_of_vlaneop idx vlaneop i)
  | VecStore (idx, vstoreop) -> CaseV ("VSTORE", al_of_vstoreop idx vstoreop)
  | VecStoreLane (idx, vlaneop, i) -> CaseV ("VSTORE_LANE", al_of_vlaneop idx vlaneop i)
  | MemorySize idx -> CaseV ("MEMORY.SIZE", al_of_memidx idx)
  | MemoryGrow idx -> CaseV ("MEMORY.GROW", al_of_memidx idx)
  | MemoryFill idx -> CaseV ("MEMORY.FILL", al_of_memidx idx)
  | MemoryCopy (idx1, idx2) -> CaseV ("MEMORY.COPY", al_of_memidx idx1 @ al_of_memidx idx2)
  | MemoryInit (idx1, idx2) -> CaseV ("MEMORY.INIT", al_of_memidx idx1 @ [ al_of_idx idx2 ])
  | DataDrop idx -> CaseV ("DATA.DROP", [ al_of_idx idx ])
  | RefAsNonNull -> nullary "REF.AS_NON_NULL"
  | RefTest rt -> CaseV ("REF.TEST", [ al_of_ref_type rt ])
  | RefCast rt -> CaseV ("REF.CAST", [ al_of_ref_type rt ])
  | RefEq -> nullary "REF.EQ"
  | RefI31 -> nullary "REF.I31"
  | I31Get ext -> CaseV ("I31.GET", [ al_of_extension ext ])
  | StructNew (idx, Explicit) -> CaseV ("STRUCT.NEW", [ al_of_idx idx ])
  | StructNew (idx, Implicit) -> CaseV ("STRUCT.NEW_DEFAULT", [ al_of_idx idx ])
  | StructGet (idx1, idx2, ext_opt) ->
    CaseV ("STRUCT.GET", [
      al_of_opt al_of_extension ext_opt;
      al_of_idx idx1;
      al_of_idx idx2;
    ])
  | StructSet (idx1, idx2) -> CaseV ("STRUCT.SET", [ al_of_idx idx1; al_of_idx idx2 ])
  | ArrayNew (idx, Explicit) -> CaseV ("ARRAY.NEW", [ al_of_idx idx ])
  | ArrayNew (idx, Implicit) -> CaseV ("ARRAY.NEW_DEFAULT", [ al_of_idx idx ])
  | ArrayNewFixed (idx, i32) ->
    CaseV ("ARRAY.NEW_FIXED", [ al_of_idx idx; al_of_nat32 i32 ])
  | ArrayNewElem (idx1, idx2) ->
    CaseV ("ARRAY.NEW_ELEM", [ al_of_idx idx1; al_of_idx idx2 ])
  | ArrayNewData (idx1, idx2) ->
    CaseV ("ARRAY.NEW_DATA", [ al_of_idx idx1; al_of_idx idx2 ])
  | ArrayGet (idx, ext_opt) ->
    CaseV ("ARRAY.GET", [ al_of_opt al_of_extension ext_opt; al_of_idx idx ])
  | ArraySet idx -> CaseV ("ARRAY.SET", [ al_of_idx idx ])
  | ArrayLen -> nullary "ARRAY.LEN"
  | ArrayCopy (idx1, idx2) -> CaseV ("ARRAY.COPY", [ al_of_idx idx1; al_of_idx idx2 ])
  | ArrayFill idx -> CaseV ("ARRAY.FILL", [ al_of_idx idx ])
  | ArrayInitData (idx1, idx2) ->
    CaseV ("ARRAY.INIT_DATA", [ al_of_idx idx1; al_of_idx idx2 ])
  | ArrayInitElem (idx1, idx2) ->
    CaseV ("ARRAY.INIT_ELEM", [ al_of_idx idx1; al_of_idx idx2 ])
  | ExternConvert Internalize -> nullary "ANY.CONVERT_EXTERN"
  | ExternConvert Externalize -> nullary "EXTERN.CONVERT_ANY"
  (* | _ -> CaseV ("TODO: Unconstructed Wasm instruction (al_of_instr)", []) *)

let al_of_const const = al_of_list al_of_instr const.it


(* Construct module *)

let al_of_type ty =
  match !version with
  | 3 ->
    CaseV ("TYPE", [ al_of_rec_type ty.it ])
  | _ ->
    let sub_types =
      al_of_rec_type ty.it
      |> arg_of_case "REC" 0
      |> unwrap_listv_to_list
    in

    match sub_types with
    | [ subtype ] ->
      let rt = subtype |> arg_of_case "SUB" 2 |> arg_of_case "FUNC" 0 in
      CaseV ("TYPE", [ rt ])
    | _ -> failwith ("Rectype is not supported in Wasm " ^ (string_of_int !version))

let al_of_local l = CaseV ("LOCAL", [ al_of_val_type l.it.ltype ])

let al_of_func func =
  CaseV ("FUNC", [
    al_of_idx func.it.ftype;
    al_of_list al_of_local func.it.locals;
    al_of_list al_of_instr func.it.body;
  ])

let al_of_global global =
  CaseV ("GLOBAL", [
    al_of_global_type global.it.gtype;
    al_of_const global.it.ginit;
  ])

let al_of_table table =
  match !version with
  | 1 -> CaseV ("TABLE", [ al_of_table_type table.it.ttype |> arg_of_case "" 0 ])
  | 2 -> CaseV ("TABLE", [ al_of_table_type table.it.ttype ])
  | 3 -> CaseV ("TABLE", [ al_of_table_type table.it.ttype; al_of_const table.it.tinit ])
  | _ -> failwith "Unsupported version"

let al_of_memory memory =
  let arg = al_of_memory_type memory.it.mtype in
  let arg' =
    if !version = 1 then
      arg_of_case "PAGE" 0 arg
    else arg
  in
  CaseV ("MEMORY", [ arg' ])

let al_of_tag tag =
  CaseV ("TAG", [ CaseV ("_IDX", [ al_of_idx tag.it.tgtype ]) ])

let al_of_segment segment =
  match segment.it with
  | Passive -> nullary "PASSIVE"
  | Active { index; offset } ->
    CaseV ("ACTIVE", [ al_of_idx index; al_of_const offset ])
  | Declarative -> nullary "DECLARE"

let al_of_elem elem =
  if !version = 1 then
    CaseV ("ELEM", [
      al_of_segment elem.it.emode |> arg_of_case "ACTIVE" 1;
      al_of_list al_of_const elem.it.einit
      |> unwrap_listv_to_list
      |> List.map (fun expr -> expr |> unwrap_listv_to_list |> List.hd |> (arg_of_case "REF.FUNC" 0))
      |> listV_of_list;
    ])
  else
    CaseV ("ELEM", [
      al_of_ref_type elem.it.etype;
      al_of_list al_of_const elem.it.einit;
      al_of_segment elem.it.emode;
    ])

let al_of_data data =
  let seg = al_of_segment data.it.dmode in
  let bytes_ = al_of_bytes data.it.dinit in
  if !version = 1 then
    CaseV ("DATA", [ arg_of_case "ACTIVE" 1 seg; bytes_ ])
  else
    CaseV ("DATA", [ bytes_; seg ])


let al_of_extern_type = function
  | ExternFuncT (dt) -> CaseV ("FUNC", [al_of_def_type dt])
  | ExternGlobalT (globaltype) -> CaseV ("GLOBAL", [al_of_global_type globaltype])
  | ExternTableT (tabletype) -> CaseV ("TABLE", [al_of_table_type tabletype])
  | ExternMemoryT (memtype) -> CaseV ("MEM", [al_of_memory_type memtype])
  | ExternTagT (tagtype) -> CaseV ("TAG", [al_of_tag_type tagtype])

let al_of_import_desc idesc =
  match idesc.it with
  | FuncImport x -> CaseV ("FUNC", [ al_of_typeuse x ])
  | TableImport tt -> CaseV ("TABLE", [ al_of_table_type tt ])
  | MemoryImport mt -> CaseV ("MEM", [ al_of_memory_type mt ])
  | GlobalImport gt -> CaseV ("GLOBAL", [ al_of_global_type gt ])
  | TagImport x -> CaseV ("TAG", [ al_of_typeuse x ])

let al_of_import import =
  CaseV ("IMPORT", [
    al_of_name import.it.module_name;
    al_of_name import.it.item_name;
    al_of_import_desc import.it.idesc;
  ])

let al_of_export_desc export_desc = match export_desc.it with
  | FuncExport idx -> CaseV ("FUNC", [ al_of_idx idx ])
  | TableExport idx -> CaseV ("TABLE", [ al_of_idx idx ])
  | MemoryExport idx -> CaseV ("MEM", [ al_of_idx idx ])
  | GlobalExport idx -> CaseV ("GLOBAL", [ al_of_idx idx ])
  | TagExport idx -> CaseV ("TAG", [ al_of_idx idx ])

let al_of_start start = CaseV ("START", [ al_of_idx start.it.sfunc ])

let al_of_export export =
  CaseV ("EXPORT", [ al_of_name export.it.name; al_of_export_desc export.it.edesc ])

let al_of_module module_ =
  CaseV ("MODULE",
    if !version < 3 then [
      al_of_list al_of_type module_.it.types;
      al_of_list al_of_import module_.it.imports;
      al_of_list al_of_func module_.it.funcs;
      al_of_list al_of_global module_.it.globals;
      al_of_list al_of_table module_.it.tables;
      al_of_list al_of_memory module_.it.memories;
      al_of_list al_of_elem module_.it.elems;
      al_of_list al_of_data module_.it.datas;
      al_of_opt al_of_start module_.it.start;
      al_of_list al_of_export module_.it.exports;
    ] else [
      al_of_list al_of_type module_.it.types;
      al_of_list al_of_import module_.it.imports;
      al_of_list al_of_tag module_.it.tags;
      al_of_list al_of_global module_.it.globals;
      al_of_list al_of_memory module_.it.memories;
      al_of_list al_of_table module_.it.tables;
      al_of_list al_of_func module_.it.funcs;
      al_of_list al_of_data module_.it.datas;
      al_of_list al_of_elem module_.it.elems;
      al_of_opt al_of_start module_.it.start;
      al_of_list al_of_export module_.it.exports;
    ]
  )

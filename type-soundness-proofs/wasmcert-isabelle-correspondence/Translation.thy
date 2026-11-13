(* Translation from the SpecTec-generated Wasm 2.0 semantics
   (isabelle_reference_output_wasm2) to WasmCert-Isabelle (WebAssembly_Dev).
   Isabelle counterpart of ../wasmcert-rocq/translation.v.

   The translation is total.  Its holes are uninterpreted constants:
   - [vec_unop], [vec_binop], [vec_ternop], [vec_testop], [vec_shiftop]: the
     WasmCert operator a SpecTec vector instruction is sent to.  WasmCert-Isabelle
     represents SIMD operators as elements of unspecified finite carriers
     ([unop_vec], [binop_vec], ...), executed by uninterpreted functions
     ([app_unop_vec_v], ...), so there is nothing to translate them against;
   - [hostref]: the WasmCert host reference standing for a SpecTec host address
     (WasmCert's [host_ref] is a [typedecl]).
   Everything else is concrete.  In particular SpecTec floats are sent to their
   IEEE 754 bit patterns, which is how WasmCert-Isabelle represents [f32]/[f64]. *)

theory Translation
  imports Base
begin

(* Short names for the SpecTec types whose names WasmCert also uses. *)
type_synonym sp_byte = "isabelle_reference_output_wasm2.byte"
type_synonym sp_sx = "isabelle_reference_output_wasm2.sx"
type_synonym sp_mut = "isabelle_reference_output_wasm2.r_MUT option"

section \<open>Holes\<close>

consts
  vec_unop :: "instr \<Rightarrow> unop_vec"
  vec_binop :: "instr \<Rightarrow> binop_vec"
  vec_ternop :: "instr \<Rightarrow> ternop_vec"
  vec_testop :: "instr \<Rightarrow> testop_vec"
  vec_shiftop :: "instr \<Rightarrow> shiftop_vec"
  hostref :: "nat \<Rightarrow> host_ref"

section \<open>Numbers\<close>

definition un :: "uN \<Rightarrow> nat" where
  "un u = (case u of mk_uN n \<Rightarrow> n)"

lemma un_simp[simp]: "un (mk_uN n) = n"
  by (simp add: un_def)

section \<open>Types\<close>

fun tr_numtype :: "numtype \<Rightarrow> t_num" where
  "tr_numtype I32 = T_i32"
| "tr_numtype I64 = T_i64"
| "tr_numtype F32 = T_f32"
| "tr_numtype F64 = T_f64"

fun tr_reftype :: "reftype \<Rightarrow> t_ref" where
  "tr_reftype FUNCREF = T_func_ref"
| "tr_reftype EXTERNREF = T_ext_ref"

fun tr_valtype :: "valtype \<Rightarrow> t" where
  "tr_valtype valtype_I32 = T_num T_i32"
| "tr_valtype valtype_I64 = T_num T_i64"
| "tr_valtype valtype_F32 = T_num T_f32"
| "tr_valtype valtype_F64 = T_num T_f64"
| "tr_valtype valtype_V128 = T_vec T_v128"
| "tr_valtype valtype_FUNCREF = T_ref T_func_ref"
| "tr_valtype valtype_EXTERNREF = T_ref T_ext_ref"
| "tr_valtype BOT = T_bot"

fun tr_resulttype :: "resulttype \<Rightarrow> t list" where
  "tr_resulttype (mk_list l) = map tr_valtype l"

fun tr_functype :: "functype \<Rightarrow> tf" where
  "tr_functype (mk_functype t1 t2) = Tf (tr_resulttype t1) (tr_resulttype t2)"

fun tr_limits :: "limits \<Rightarrow> limit_t" where
  "tr_limits (mk_limits mn mx) = \<lparr>l_min = un mn, l_max = map_option un mx\<rparr>"

fun tr_mut :: "sp_mut \<Rightarrow> Wasm_Ast.mut" where
  "tr_mut (Some _) = T_mut"
| "tr_mut None = T_immut"

fun tr_globaltype :: "globaltype \<Rightarrow> tg" where
  "tr_globaltype (mk_globaltype m t) = \<lparr>tg_mut = tr_mut m, tg_t = tr_valtype t\<rparr>"

fun tr_tabletype :: "tabletype \<Rightarrow> tab_t" where
  "tr_tabletype (mk_tabletype l rt) = T_tab (tr_limits l) (tr_reftype rt)"

fun tr_memtype :: "memtype \<Rightarrow> mem_t" where
  "tr_memtype (PAGE l) = tr_limits l"

section \<open>Values\<close>

definition tr_i32 :: "uN \<Rightarrow> Wasm_Ast.i32" where
  "tr_i32 u = Abs_i32 (of_nat (un u))"

definition tr_i64 :: "uN \<Rightarrow> Wasm_Ast.i64" where
  "tr_i64 u = Abs_i64 (of_nat (un u))"

(* IEEE 754 bit pattern of a SpecTec float with [M] significand and [E] exponent bits.
   The biased exponent of a normal float is [e + (2^(E-1) - 1)], which is between
   1 and [2^E - 2] for a well-formed one. *)
fun fmag_bits :: "nat \<Rightarrow> nat \<Rightarrow> fNmag \<Rightarrow> nat" where
  "fmag_bits M E (NORM m e) = nat (e + int (2 ^ (E - 1) - 1)) * 2 ^ M + m"
| "fmag_bits M E (SUBNORM m) = m"
| "fmag_bits M E res_INF = (2 ^ E - 1) * 2 ^ M"
| "fmag_bits M E (NAN m) = (2 ^ E - 1) * 2 ^ M + m"

fun fN_bits :: "nat \<Rightarrow> nat \<Rightarrow> fN \<Rightarrow> nat" where
  "fN_bits M E (POS x) = fmag_bits M E x"
| "fN_bits M E (NEG x) = 2 ^ (M + E) + fmag_bits M E x"

definition tr_f32 :: "fN \<Rightarrow> Wasm_Ast.f32" where
  "tr_f32 x = Abs_f32 (of_nat (fN_bits 23 8 x))"

definition tr_f64 :: "fN \<Rightarrow> Wasm_Ast.f64" where
  "tr_f64 x = Abs_f64 (of_nat (fN_bits 52 11 x))"

fun tr_num :: "num_underscore \<Rightarrow> v_num" where
  "tr_num (mk_num__0 Inn_I32 i) = ConstInt32 (tr_i32 i)"
| "tr_num (mk_num__0 Inn_I64 i) = ConstInt64 (tr_i64 i)"
| "tr_num (mk_num__1 Fnn_F32 x) = ConstFloat32 (tr_f32 x)"
| "tr_num (mk_num__1 Fnn_F64 x) = ConstFloat64 (tr_f64 x)"

definition tr_v128 :: "uN \<Rightarrow> v128" where
  "tr_v128 u = Abs_v128 (of_nat (un u))"

definition tr_vec :: "uN \<Rightarrow> v_vec" where
  "tr_vec u = ConstVec128 (tr_v128 u)"

definition tr_host :: "nat \<Rightarrow> host" where
  "tr_host a = Host_ref (hostref a)"

fun tr_ref :: "ref \<Rightarrow> v_ref" where
  "tr_ref (ref_REF_NULL rt) = ConstNull (tr_reftype rt)"
| "tr_ref (REF_FUNC_ADDR a) = ConstRefFunc a"
| "tr_ref (REF_HOST_ADDR a) = ConstRefExtern (tr_host a)"

fun tr_val :: "val \<Rightarrow> v" where
  "tr_val (val_CONST _ c) = V_num (tr_num c)"
| "tr_val (val_VCONST _ c) = V_vec (tr_vec c)"
| "tr_val (val_REF_NULL rt) = V_ref (ConstNull (tr_reftype rt))"
| "tr_val (val_REF_FUNC_ADDR a) = V_ref (ConstRefFunc a)"
| "tr_val (val_REF_HOST_ADDR a) = V_ref (ConstRefExtern (tr_host a))"

section \<open>Operators\<close>

fun tr_sx :: "sp_sx \<Rightarrow> Wasm_Ast.sx" where
  "tr_sx isabelle_reference_output_wasm2.U = Wasm_Ast.U"
| "tr_sx isabelle_reference_output_wasm2.S = Wasm_Ast.S"

(* Packed width in bits to WasmCert's packed type. *)
definition tp_of_bits :: "nat \<Rightarrow> tp_num" where
  "tp_of_bits n = (if n = 8 then Tp_i8 else if n = 16 then Tp_i16 else Tp_i32)"

fun tr_unop :: "unop_underscore \<Rightarrow> unop" where
  "tr_unop (mk_unop__0 _ CLZ) = Unop_i Clz"
| "tr_unop (mk_unop__0 _ CTZ) = Unop_i Ctz"
| "tr_unop (mk_unop__0 _ POPCNT) = Unop_i Popcnt"
| "tr_unop (mk_unop__0 _ (EXTEND n)) = Extend_s (tp_of_bits n)"
| "tr_unop (mk_unop__1 _ ABS) = Unop_f Abs"
| "tr_unop (mk_unop__1 _ unop_Fnn_NEG) = Unop_f Neg"
| "tr_unop (mk_unop__1 _ SQRT) = Unop_f Sqrt"
| "tr_unop (mk_unop__1 _ CEIL) = Unop_f Ceil"
| "tr_unop (mk_unop__1 _ FLOOR) = Unop_f Floor"
| "tr_unop (mk_unop__1 _ TRUNC) = Unop_f Trunc"
| "tr_unop (mk_unop__1 _ NEAREST) = Unop_f Nearest"

fun tr_binop :: "binop_underscore \<Rightarrow> binop" where
  "tr_binop (mk_binop__0 _ ADD) = Binop_i Add"
| "tr_binop (mk_binop__0 _ SUB) = Binop_i Sub"
| "tr_binop (mk_binop__0 _ MUL) = Binop_i Mul"
| "tr_binop (mk_binop__0 _ (DIV s)) = Binop_i (Div (tr_sx s))"
| "tr_binop (mk_binop__0 _ (REM s)) = Binop_i (Rem (tr_sx s))"
| "tr_binop (mk_binop__0 _ AND) = Binop_i And"
| "tr_binop (mk_binop__0 _ OR) = Binop_i Or"
| "tr_binop (mk_binop__0 _ XOR) = Binop_i Xor"
| "tr_binop (mk_binop__0 _ SHL) = Binop_i Shl"
| "tr_binop (mk_binop__0 _ (SHR s)) = Binop_i (Shr (tr_sx s))"
| "tr_binop (mk_binop__0 _ ROTL) = Binop_i Rotl"
| "tr_binop (mk_binop__0 _ ROTR) = Binop_i Rotr"
| "tr_binop (mk_binop__1 _ binop_Fnn_ADD) = Binop_f Addf"
| "tr_binop (mk_binop__1 _ binop_Fnn_SUB) = Binop_f Subf"
| "tr_binop (mk_binop__1 _ binop_Fnn_MUL) = Binop_f Mulf"
| "tr_binop (mk_binop__1 _ binop_Fnn_DIV) = Binop_f Divf"
| "tr_binop (mk_binop__1 _ res_MIN) = Binop_f Min"
| "tr_binop (mk_binop__1 _ res_MAX) = Binop_f Max"
| "tr_binop (mk_binop__1 _ COPYSIGN) = Binop_f Copysign"

fun tr_relop :: "relop_underscore \<Rightarrow> relop" where
  "tr_relop (mk_relop__0 _ EQ) = Relop_i Eq"
| "tr_relop (mk_relop__0 _ NE) = Relop_i Ne"
| "tr_relop (mk_relop__0 _ (LT s)) = Relop_i (Lt (tr_sx s))"
| "tr_relop (mk_relop__0 _ (GT s)) = Relop_i (Gt (tr_sx s))"
| "tr_relop (mk_relop__0 _ (LE s)) = Relop_i (Le (tr_sx s))"
| "tr_relop (mk_relop__0 _ (GE s)) = Relop_i (Ge (tr_sx s))"
| "tr_relop (mk_relop__1 _ relop_Fnn_EQ) = Relop_f Eqf"
| "tr_relop (mk_relop__1 _ relop_Fnn_NE) = Relop_f Nef"
| "tr_relop (mk_relop__1 _ relop_Fnn_LT) = Relop_f Ltf"
| "tr_relop (mk_relop__1 _ relop_Fnn_GT) = Relop_f Gtf"
| "tr_relop (mk_relop__1 _ relop_Fnn_LE) = Relop_f Lef"
| "tr_relop (mk_relop__1 _ relop_Fnn_GE) = Relop_f Gef"

(* WasmCert has one [Convert] operator for wrap, extend, trunc, trunc_sat,
   convert, promote and demote, told apart by the operand types and the optional
   (saturation, signedness) annotation, which is [None] exactly for wrap,
   promote and demote ([convert] typing rule). *)
fun tr_cvtop :: "cvtop__underscore \<Rightarrow> cvtop \<times> (sat \<times> Wasm_Ast.sx) option" where
  "tr_cvtop (mk_cvtop___0 _ _ (cvtop__Inn_1_Inn_2_EXTEND s)) = (Convert, Some (Nonsat, tr_sx s))"
| "tr_cvtop (mk_cvtop___0 _ _ WRAP) = (Convert, None)"
| "tr_cvtop (mk_cvtop___1 _ _ (CONVERT s)) = (Convert, Some (Nonsat, tr_sx s))"
| "tr_cvtop (mk_cvtop___1 _ _ REINTERPRET) = (Reinterpret, None)"
| "tr_cvtop (mk_cvtop___2 _ _ (cvtop__Fnn_1_Inn_2_TRUNC s)) = (Convert, Some (Nonsat, tr_sx s))"
| "tr_cvtop (mk_cvtop___2 _ _ (TRUNC_SAT s)) = (Convert, Some (Sat, tr_sx s))"
| "tr_cvtop (mk_cvtop___2 _ _ cvtop__Fnn_1_Inn_2_REINTERPRET) = (Reinterpret, None)"
| "tr_cvtop (mk_cvtop___3 _ _ PROMOTE) = (Convert, None)"
| "tr_cvtop (mk_cvtop___3 _ _ DEMOTE) = (Convert, None)"

definition sz_bits :: "sz \<Rightarrow> nat" where
  "sz_bits s = (case s of mk_sz n \<Rightarrow> n)"

lemma sz_bits_simp[simp]: "sz_bits (mk_sz n) = n"
  by (simp add: sz_bits_def)

definition tr_tp :: "sz \<Rightarrow> tp_num" where
  "tr_tp s = tp_of_bits (sz_bits s)"

fun tr_loadop :: "loadop_underscore option \<Rightarrow> (tp_num \<times> Wasm_Ast.sx) option" where
  "tr_loadop (Some (mk_loadop__0 _ (mk_loadop_Inn s x))) = Some (tr_tp s, tr_sx x)"
| "tr_loadop None = None"

(* Lane width in bits to WasmCert's integer vector shape. *)
definition svi_of_bits :: "nat \<Rightarrow> shape_vec_i" where
  "svi_of_bits n = (if n = 8 then I8_16 else if n = 16 then I16_8 else if n = 32 then I32_4 else I64_2)"

definition tpv_of_bits :: "nat \<Rightarrow> tp_vec" where
  "tpv_of_bits n = (if n = 8 then Tp_v8_8 else if n = 16 then Tp_v16_4 else Tp_v32_2)"

fun tr_vloadop :: "vloadop_underscore option \<Rightarrow> loadop_vec" where
  "tr_vloadop None = Load_128"
| "tr_vloadop (Some (SHAPEX_underscore s _ x)) = Load_packed_vec (tpv_of_bits (sz_bits s)) (tr_sx x)"
| "tr_vloadop (Some (SPLAT s)) = Load_splat (svi_of_bits (sz_bits s))"
| "tr_vloadop (Some (vloadop__ZERO s)) = (if sz_bits s = 32 then Load_32_zero else Load_64_zero)"

fun tr_blocktype :: "blocktype \<Rightarrow> tb" where
  "tr_blocktype (underscore_RESULT t) = Tbv (map_option tr_valtype t)"
| "tr_blocktype (underscore_IDX x) = Tbf (un x)"

fun tr_shape :: "shape \<Rightarrow> shape_vec" where
  "tr_shape (X lanetype_I8 _) = Svi I8_16"
| "tr_shape (X lanetype_I16 _) = Svi I16_8"
| "tr_shape (X lanetype_I32 _) = Svi I32_4"
| "tr_shape (X lanetype_I64 _) = Svi I64_2"
| "tr_shape (X lanetype_F32 _) = Svf F32_4"
| "tr_shape (X lanetype_F64 _) = Svf F64_2"

(* WasmCert always annotates a lane extraction with a signedness; SpecTec only
   does for packed lanes.  [U] is the one WasmCert accepts for unpacked lanes. *)
fun tr_lane_sx :: "sp_sx option \<Rightarrow> Wasm_Ast.sx" where
  "tr_lane_sx None = Wasm_Ast.U"
| "tr_lane_sx (Some s) = tr_sx s"

(* WasmCert's [Select] carries at most one type; SpecTec's carries a list that
   typing restricts to a singleton. *)
fun tr_select :: "valtype list option \<Rightarrow> t option" where
  "tr_select None = None"
| "tr_select (Some ts) = Some (tr_valtype (hd ts))"

section \<open>Instructions\<close>

definition tr_align :: "memarg \<Rightarrow> nat" where
  "tr_align ao = un (ALIGN ao)"

definition tr_offset :: "memarg \<Rightarrow> nat" where
  "tr_offset ao = un (OFFSET ao)"

primrec tr_st0 :: "instr_st0 \<Rightarrow> b_e" where
  "tr_st0 (CALL_INDIRECT x y) = Call_indirect (un x) (un y)"
| "tr_st0 (CALL x) = Call (un x)"
| "tr_st0 (BR_TABLE ls l) = Br_table (map un ls) (un l)"
| "tr_st0 (BR_IF l) = Br_if (un l)"
| "tr_st0 (BR l) = Br (un l)"
| "tr_st0 (SELECT ts) = Select (tr_select ts)"
| "tr_st0 DROP = Drop"
| "tr_st0 UNREACHABLE = Unreachable"
| "tr_st0 NOP = Nop"

primrec tr_st1 :: "instr_st1 \<Rightarrow> b_e" where
  "tr_st1 (VCONST _ c) = EConstVec (tr_vec c)"
| "tr_st1 (CVTOP nt1 nt2 op) = Cvtop (tr_numtype nt1) (fst (tr_cvtop op)) (tr_numtype nt2) (snd (tr_cvtop op))"
| "tr_st1 (RELOP nt op) = Relop (tr_numtype nt) (tr_relop op)"
| "tr_st1 (TESTOP nt op) = Testop (tr_numtype nt) Eqz"
| "tr_st1 (BINOP nt op) = Binop (tr_numtype nt) (tr_binop op)"
| "tr_st1 (UNOP nt op) = Unop (tr_numtype nt) (tr_unop op)"
| "tr_st1 (res_CONST _ c) = EConstNum (tr_num c)"
| "tr_st1 RETURN = Return"
| "tr_st1 (VVUNOP a b) = Unop_vec (vec_unop (instr_sc1 (VVUNOP a b)))"

(* Vector instructions: the instruction class is fixed, the operator is a hole. *)
primrec tr_st2 :: "instr_st2 \<Rightarrow> b_e" where
  "tr_st2 (VSHIFTOP a b) = Shift_vec (vec_shiftop (instr_sc2 (VSHIFTOP a b)))"
| "tr_st2 (VRELOP a b) = Binop_vec (vec_binop (instr_sc2 (VRELOP a b)))"
| "tr_st2 (VTESTOP a b) = Test_vec (vec_testop (instr_sc2 (VTESTOP a b)))"
| "tr_st2 (VBINOP a b) = Binop_vec (vec_binop (instr_sc2 (VBINOP a b)))"
| "tr_st2 (VUNOP a b) = Unop_vec (vec_unop (instr_sc2 (VUNOP a b)))"
| "tr_st2 (VVTESTOP a b) = Test_vec (vec_testop (instr_sc2 (VVTESTOP a b)))"
| "tr_st2 (VVTERNOP a b) = Ternop_vec (vec_ternop (instr_sc2 (VVTERNOP a b)))"
| "tr_st2 (VVBINOP a b) = Binop_vec (vec_binop (instr_sc2 (VVBINOP a b)))"
| "tr_st2 (VBITMASK a) = Test_vec (vec_testop (instr_sc2 (VBITMASK a)))"

primrec tr_st3 :: "instr_st3 \<Rightarrow> b_e" where
  "tr_st3 (VNARROW a b c) = Binop_vec (vec_binop (instr_sc3 (VNARROW a b c)))"
| "tr_st3 (VEXTBINOP a b c) = Binop_vec (vec_binop (instr_sc3 (VEXTBINOP a b c)))"
| "tr_st3 (VEXTUNOP a b c) = Unop_vec (vec_unop (instr_sc3 (VEXTUNOP a b c)))"
| "tr_st3 (VREPLACE_LANE sh j) = Replace_vec (tr_shape sh) (un j)"
| "tr_st3 (VEXTRACT_LANE sh s j) = Extract_vec (tr_shape sh) (tr_lane_sx s) (un j)"
| "tr_st3 (VSPLAT sh) = Splat_vec (tr_shape sh)"
| "tr_st3 (VSHUFFLE a ls) = Binop_vec (vec_binop (instr_sc3 (VSHUFFLE a ls)))"
| "tr_st3 (VSWIZZLE a) = Binop_vec (vec_binop (instr_sc3 (VSWIZZLE a)))"
| "tr_st3 (VCVTOP a b c) = Unop_vec (vec_unop (instr_sc3 (VCVTOP a b c)))"

primrec tr_st4 :: "instr_st4 \<Rightarrow> b_e" where
  "tr_st4 (GLOBAL_SET x) = Global_set (un x)"
| "tr_st4 (GLOBAL_GET x) = Global_get (un x)"
| "tr_st4 (LOCAL_TEE x) = Local_tee (un x)"
| "tr_st4 (LOCAL_SET x) = Local_set (un x)"
| "tr_st4 (LOCAL_GET x) = Local_get (un x)"
| "tr_st4 REF_IS_NULL = Ref_is_null"
| "tr_st4 (REF_FUNC x) = Ref_func (un x)"
| "tr_st4 (REF_NULL rt) = Ref_null (tr_reftype rt)"
| "tr_st4 (TABLE_GET x) = Table_get (un x)"

primrec tr_st5 :: "instr_st5 \<Rightarrow> b_e" where
  "tr_st5 (LOAD nt lo ao) = Load (tr_numtype nt) (tr_loadop lo) (tr_align ao) (tr_offset ao)"
| "tr_st5 (ELEM_DROP x) = Elem_drop (un x)"
| "tr_st5 (TABLE_INIT x y) = Table_init (un x) (un y)"
| "tr_st5 (TABLE_COPY x y) = Table_copy (un x) (un y)"
| "tr_st5 (TABLE_FILL x) = Table_fill (un x)"
| "tr_st5 (TABLE_GROW x) = Table_grow (un x)"
| "tr_st5 (TABLE_SIZE x) = Table_size (un x)"
| "tr_st5 (TABLE_SET x) = Table_set (un x)"
| "tr_st5 (STORE nt so ao) = Store (tr_numtype nt) (map_option tr_tp so) (tr_align ao) (tr_offset ao)"

primrec tr_st6 :: "instr_st6 \<Rightarrow> b_e" where
  "tr_st6 MEMORY_COPY = Memory_copy"
| "tr_st6 MEMORY_FILL = Memory_fill"
| "tr_st6 MEMORY_GROW = Memory_grow"
| "tr_st6 MEMORY_SIZE = Memory_size"
| "tr_st6 (VSTORE_LANE _ s ao j) = Store_vec (Store_lane (svi_of_bits (sz_bits s)) (un j)) (tr_align ao) (tr_offset ao)"
| "tr_st6 (VSTORE _ ao) = Store_vec Store_128 (tr_align ao) (tr_offset ao)"
| "tr_st6 (VLOAD_LANE _ s ao j) = Load_lane_vec (svi_of_bits (sz_bits s)) (un j) (tr_align ao) (tr_offset ao)"
| "tr_st6 (VLOAD _ lo ao) = Load_vec (tr_vloadop lo) (tr_align ao) (tr_offset ao)"
| "tr_st6 (MEMORY_INIT x) = Memory_init (un x)"

primrec tr_instr :: "instr \<Rightarrow> b_e" and tr_instr7 :: "instr_st7 \<Rightarrow> b_e" where
  "tr_instr (instr_sc0 x) = tr_st0 x"
| "tr_instr (instr_sc1 x) = tr_st1 x"
| "tr_instr (instr_sc2 x) = tr_st2 x"
| "tr_instr (instr_sc3 x) = tr_st3 x"
| "tr_instr (instr_sc4 x) = tr_st4 x"
| "tr_instr (instr_sc5 x) = tr_st5 x"
| "tr_instr (instr_sc6 x) = tr_st6 x"
| "tr_instr (instr_sc7 x) = tr_instr7 x"
| "tr_instr7 (IFELSE bt is1 is2) = If (tr_blocktype bt) (map tr_instr is1) (map tr_instr is2)"
| "tr_instr7 (LOOP bt ins) = Loop (tr_blocktype bt) (map tr_instr ins)"
| "tr_instr7 (BLOCK bt ins) = Block (tr_blocktype bt) (map tr_instr ins)"
| "tr_instr7 (DATA_DROP x) = Data_drop (un x)"

definition tr_instrs :: "instr list \<Rightarrow> b_e list" where
  "tr_instrs ins = map tr_instr ins"

section \<open>Runtime structures\<close>

fun tr_byte :: "sp_byte \<Rightarrow> Wasm_Ast.byte" where
  "tr_byte (mk_byte n) = byte_of_nat n"

fun tr_local :: "local \<Rightarrow> t" where
  "tr_local (LOCAL t) = tr_valtype t"

(* WasmCert's module instances have no exports. *)
definition tr_moduleinst :: "moduleinst \<Rightarrow> inst" where
  "tr_moduleinst mi =
     \<lparr>inst.types = map tr_functype (TYPES mi), inst.funcs = FUNCS mi, inst.tabs = TABLES mi,
      inst.mems = MEMS mi, inst.globs = GLOBALS mi, inst.elems = ELEMS mi, inst.datas = DATAS mi\<rparr>"

(* WasmCert's closures carry the local types and body, not the type index. *)
definition tr_funcinst :: "funcinst \<Rightarrow> cl" where
  "tr_funcinst fi =
     (case CODE fi of func_FUNC _ ls body \<Rightarrow>
        Func_native (tr_moduleinst (funcinst_MODULE fi)) (tr_functype (funcinst_TYPE fi))
          (map tr_local ls) (tr_instrs body))"

(* WasmCert's global instances store the mutability; the value type is the value's. *)
definition tr_globalinst :: "globalinst \<Rightarrow> global" where
  "tr_globalinst gi =
     (case globalinst_TYPE gi of mk_globaltype m _ \<Rightarrow> \<lparr>g_mut = tr_mut m, g_val = tr_val (VALUE gi)\<rparr>)"

definition tr_tableinst :: "tableinst \<Rightarrow> tabinst" where
  "tr_tableinst ti = (tr_tabletype (tableinst_TYPE ti), map tr_ref (REFS ti))"

definition tr_meminst :: "meminst \<Rightarrow> mem" where
  "tr_meminst mi = (tr_memtype (meminst_TYPE mi), Abs_mem_rep (map tr_byte (BYTES mi)))"

definition tr_eleminst :: "isabelle_reference_output_wasm2.eleminst \<Rightarrow> Wasm_Ast.eleminst" where
  "tr_eleminst ei = (tr_reftype (eleminst_TYPE ei), map tr_ref (eleminst_REFS ei))"

definition tr_datainst :: "isabelle_reference_output_wasm2.datainst \<Rightarrow> Wasm_Ast.datainst" where
  "tr_datainst di = map tr_byte (datainst_BYTES di)"

definition tr_store :: "store \<Rightarrow> s" where
  "tr_store st =
     \<lparr>s.funcs = map tr_funcinst (store_FUNCS st), s.tabs = map tr_tableinst (store_TABLES st),
      s.mems = map tr_meminst (store_MEMS st), s.globs = map tr_globalinst (store_GLOBALS st),
      s.elems = map tr_eleminst (store_ELEMS st), s.datas = map tr_datainst (store_DATAS st)\<rparr>"

definition tr_frame :: "frame \<Rightarrow> f" where
  "tr_frame fr = \<lparr>f_locs = map tr_val (LOCALS fr), f_inst = tr_moduleinst (frame_MODULE fr)\<rparr>"

section \<open>Administrative instructions\<close>

(* The plain instruction an administrative instruction stands for. *)
primrec instr_of_a0 :: "admininstr_st0 \<Rightarrow> instr" where
  "instr_of_a0 (admininstr_st0_BR_IF l) = instr_sc0 (BR_IF l)"
| "instr_of_a0 (admininstr_st0_BR l) = instr_sc0 (BR l)"
| "instr_of_a0 (admininstr_st0_IFELSE bt a b) = instr_sc7 (IFELSE bt a b)"
| "instr_of_a0 (admininstr_st0_LOOP bt a) = instr_sc7 (LOOP bt a)"
| "instr_of_a0 (admininstr_st0_BLOCK bt a) = instr_sc7 (BLOCK bt a)"
| "instr_of_a0 (admininstr_st0_SELECT ts) = instr_sc0 (SELECT ts)"
| "instr_of_a0 admininstr_st0_DROP = instr_sc0 DROP"
| "instr_of_a0 admininstr_st0_UNREACHABLE = instr_sc0 UNREACHABLE"
| "instr_of_a0 admininstr_st0_NOP = instr_sc0 NOP"

primrec instr_of_a1 :: "admininstr_st1 \<Rightarrow> instr" where
  "instr_of_a1 (admininstr_st1_RELOP nt op) = instr_sc1 (RELOP nt op)"
| "instr_of_a1 (admininstr_st1_TESTOP nt op) = instr_sc1 (TESTOP nt op)"
| "instr_of_a1 (admininstr_st1_BINOP nt op) = instr_sc1 (BINOP nt op)"
| "instr_of_a1 (admininstr_st1_UNOP nt op) = instr_sc1 (UNOP nt op)"
| "instr_of_a1 (admininstr_st1_CONST nt c) = instr_sc1 (res_CONST nt c)"
| "instr_of_a1 admininstr_st1_RETURN = instr_sc1 RETURN"
| "instr_of_a1 (admininstr_st1_CALL_INDIRECT x y) = instr_sc0 (CALL_INDIRECT x y)"
| "instr_of_a1 (admininstr_st1_CALL x) = instr_sc0 (CALL x)"
| "instr_of_a1 (admininstr_st1_BR_TABLE ls l) = instr_sc0 (BR_TABLE ls l)"

primrec instr_of_a2 :: "admininstr_st2 \<Rightarrow> instr" where
  "instr_of_a2 (admininstr_st2_VBINOP a b) = instr_sc2 (VBINOP a b)"
| "instr_of_a2 (admininstr_st2_VUNOP a b) = instr_sc2 (VUNOP a b)"
| "instr_of_a2 (admininstr_st2_VVTESTOP a b) = instr_sc2 (VVTESTOP a b)"
| "instr_of_a2 (admininstr_st2_VVTERNOP a b) = instr_sc2 (VVTERNOP a b)"
| "instr_of_a2 (admininstr_st2_VVBINOP a b) = instr_sc2 (VVBINOP a b)"
| "instr_of_a2 (admininstr_st2_VVUNOP a b) = instr_sc1 (VVUNOP a b)"
| "instr_of_a2 (admininstr_st2_VCONST a b) = instr_sc1 (VCONST a b)"
| "instr_of_a2 (admininstr_st2_CVTOP a b c) = instr_sc1 (CVTOP a b c)"
| "instr_of_a2 (admininstr_st2_VTESTOP a b) = instr_sc2 (VTESTOP a b)"

primrec instr_of_a3 :: "admininstr_st3 \<Rightarrow> instr" where
  "instr_of_a3 (admininstr_st3_VREPLACE_LANE a b) = instr_sc3 (VREPLACE_LANE a b)"
| "instr_of_a3 (admininstr_st3_VEXTRACT_LANE a b c) = instr_sc3 (VEXTRACT_LANE a b c)"
| "instr_of_a3 (admininstr_st3_VSPLAT a) = instr_sc3 (VSPLAT a)"
| "instr_of_a3 (admininstr_st3_VSHUFFLE a b) = instr_sc3 (VSHUFFLE a b)"
| "instr_of_a3 (admininstr_st3_VSWIZZLE a) = instr_sc3 (VSWIZZLE a)"
| "instr_of_a3 (admininstr_st3_VBITMASK a) = instr_sc2 (VBITMASK a)"
| "instr_of_a3 (admininstr_st3_VSHIFTOP a b) = instr_sc2 (VSHIFTOP a b)"
| "instr_of_a3 (admininstr_st3_VRELOP a b) = instr_sc2 (VRELOP a b)"
| "instr_of_a3 (admininstr_st3_VEXTUNOP a b c) = instr_sc3 (VEXTUNOP a b c)"

primrec instr_of_a4 :: "admininstr_st4 \<Rightarrow> instr" where
  "instr_of_a4 (admininstr_st4_LOCAL_SET x) = instr_sc4 (LOCAL_SET x)"
| "instr_of_a4 (admininstr_st4_LOCAL_GET x) = instr_sc4 (LOCAL_GET x)"
| "instr_of_a4 admininstr_st4_REF_IS_NULL = instr_sc4 REF_IS_NULL"
| "instr_of_a4 (admininstr_st4_REF_FUNC x) = instr_sc4 (REF_FUNC x)"
| "instr_of_a4 (admininstr_st4_REF_NULL rt) = instr_sc4 (REF_NULL rt)"
| "instr_of_a4 (admininstr_st4_VCVTOP a b c) = instr_sc3 (VCVTOP a b c)"
| "instr_of_a4 (admininstr_st4_VNARROW a b c) = instr_sc3 (VNARROW a b c)"
| "instr_of_a4 (admininstr_st4_VEXTBINOP a b c) = instr_sc3 (VEXTBINOP a b c)"
| "instr_of_a4 (admininstr_st4_LOCAL_TEE x) = instr_sc4 (LOCAL_TEE x)"

primrec instr_of_a5 :: "admininstr_st5 \<Rightarrow> instr" where
  "instr_of_a5 (admininstr_st5_TABLE_COPY x y) = instr_sc5 (TABLE_COPY x y)"
| "instr_of_a5 (admininstr_st5_TABLE_FILL x) = instr_sc5 (TABLE_FILL x)"
| "instr_of_a5 (admininstr_st5_TABLE_GROW x) = instr_sc5 (TABLE_GROW x)"
| "instr_of_a5 (admininstr_st5_TABLE_SIZE x) = instr_sc5 (TABLE_SIZE x)"
| "instr_of_a5 (admininstr_st5_TABLE_SET x) = instr_sc5 (TABLE_SET x)"
| "instr_of_a5 (admininstr_st5_TABLE_GET x) = instr_sc4 (TABLE_GET x)"
| "instr_of_a5 (admininstr_st5_GLOBAL_SET x) = instr_sc4 (GLOBAL_SET x)"
| "instr_of_a5 (admininstr_st5_GLOBAL_GET x) = instr_sc4 (GLOBAL_GET x)"
| "instr_of_a5 (admininstr_st5_TABLE_INIT x y) = instr_sc5 (TABLE_INIT x y)"

primrec instr_of_a6 :: "admininstr_st6 \<Rightarrow> instr" where
  "instr_of_a6 admininstr_st6_MEMORY_SIZE = instr_sc6 MEMORY_SIZE"
| "instr_of_a6 (admininstr_st6_VSTORE_LANE a b c d) = instr_sc6 (VSTORE_LANE a b c d)"
| "instr_of_a6 (admininstr_st6_VSTORE a b) = instr_sc6 (VSTORE a b)"
| "instr_of_a6 (admininstr_st6_VLOAD_LANE a b c d) = instr_sc6 (VLOAD_LANE a b c d)"
| "instr_of_a6 (admininstr_st6_VLOAD a b c) = instr_sc6 (VLOAD a b c)"
| "instr_of_a6 (admininstr_st6_STORE a b c) = instr_sc5 (STORE a b c)"
| "instr_of_a6 (admininstr_st6_LOAD a b c) = instr_sc5 (LOAD a b c)"
| "instr_of_a6 (admininstr_st6_ELEM_DROP x) = instr_sc5 (ELEM_DROP x)"
| "instr_of_a6 admininstr_st6_MEMORY_GROW = instr_sc6 MEMORY_GROW"

(* The non-instruction administrative instructions are in admininstr_st7/st8. *)
primrec tr_admin :: "admininstr \<Rightarrow> e" and tr_a7 :: "admininstr_st7 \<Rightarrow> e"
    and tr_admin8 :: "admininstr_st8 \<Rightarrow> e" where
  "tr_admin (admininstr_sc0 x) = Basic (tr_instr (instr_of_a0 x))"
| "tr_admin (admininstr_sc1 x) = Basic (tr_instr (instr_of_a1 x))"
| "tr_admin (admininstr_sc2 x) = Basic (tr_instr (instr_of_a2 x))"
| "tr_admin (admininstr_sc3 x) = Basic (tr_instr (instr_of_a3 x))"
| "tr_admin (admininstr_sc4 x) = Basic (tr_instr (instr_of_a4 x))"
| "tr_admin (admininstr_sc5 x) = Basic (tr_instr (instr_of_a5 x))"
| "tr_admin (admininstr_sc6 x) = Basic (tr_instr (instr_of_a6 x))"
| "tr_admin (admininstr_sc7 x) = tr_a7 x"
| "tr_admin (admininstr_sc8 x) = tr_admin8 x"
| "tr_a7 (LABEL_underscore n ins es) = Label n (map Basic (tr_instrs ins)) (map tr_admin es)"
| "tr_a7 admininstr_st7_TRAP = Trap"
| "tr_a7 (CALL_ADDR a) = Invoke a"
| "tr_a7 (admininstr_st7_REF_HOST_ADDR a) = Ref (ConstRefExtern (tr_host a))"
| "tr_a7 (admininstr_st7_REF_FUNC_ADDR a) = Ref (ConstRefFunc a)"
| "tr_a7 (admininstr_st7_DATA_DROP x) = Basic (tr_instr (instr_sc7 (DATA_DROP x)))"
| "tr_a7 (admininstr_st7_MEMORY_INIT x) = Basic (tr_instr (instr_sc6 (MEMORY_INIT x)))"
| "tr_a7 admininstr_st7_MEMORY_COPY = Basic (tr_instr (instr_sc6 MEMORY_COPY))"
| "tr_a7 admininstr_st7_MEMORY_FILL = Basic (tr_instr (instr_sc6 MEMORY_FILL))"
| "tr_admin8 (FRAME_underscore n fr es) = Frame n (tr_frame fr) (map tr_admin es)"

definition tr_admins :: "admininstr list \<Rightarrow> e list" where
  "tr_admins es = map tr_admin es"

(* A configuration: store, frame and instruction sequence. *)
fun tr_config :: "config \<Rightarrow> s \<times> f \<times> e list" where
  "tr_config (mk_config (mk_state st fr) es) = (tr_store st, tr_frame fr, tr_admins es)"

section \<open>Typing contexts\<close>

(* SpecTec's Wasm 2.0 contexts have no [refs] component, so [ref.func x] is not
   restricted to declared references there.  WasmCert's [refs] is set to every
   function index, which makes the two checks coincide. *)
definition tr_context :: "res_context \<Rightarrow> t_context" where
  "tr_context C =
     \<lparr>types_t = map tr_functype (context_TYPES C), func_t = map tr_functype (context_FUNCS C),
      global = map tr_globaltype (context_GLOBALS C), elem = map tr_reftype (context_ELEMS C),
      data = map (\<lambda>_. ()) (context_DATAS C), table = map tr_tabletype (context_TABLES C),
      memory = map tr_memtype (context_MEMS C), local = map tr_valtype (context_LOCALS C),
      label = map tr_resulttype (LABELS C), return = map_option tr_resulttype (context_RETURN C),
      refs = [0..<length (context_FUNCS C)]\<rparr>"

section \<open>Basic commutation lemmas\<close>

termination admininstr_instr by lexicographic_order
termination admininstr_val by lexicographic_order
termination admininstr_ref by lexicographic_order

lemma tr_admin_instr[simp]: "tr_admin (admininstr_instr i) = Basic (tr_instr i)"
  by (cases i rule: instr.exhaust)
     (rename_tac x, case_tac x; simp add: admininstr_instr.simps)+

(* SpecTec's null reference value is the instruction [REF.NULL t]; WasmCert-Isabelle
   distinguishes the instruction [$Ref_null t] from the value [Ref (ConstNull t)]
   it reduces to (rule [null]).  The translation keeps the instruction, so a
   SpecTec null value translates to a WasmCert instruction, not a WasmCert value.
   (WasmCert-Coq, like SpecTec, takes the instruction to be the value.) *)
lemma tr_admin_val[simp]:
  "tr_admin (admininstr_val v) =
     (case v of val_REF_NULL rt \<Rightarrow> $Ref_null (tr_reftype rt) | _ \<Rightarrow> $C (tr_val v))"
  by (cases v) (simp_all add: admininstr_val.simps v_to_e_def tr_vec_def)

lemma tr_admin_ref[simp]:
  "tr_admin (admininstr_ref r) =
     (case r of ref_REF_NULL rt \<Rightarrow> $Ref_null (tr_reftype rt) | _ \<Rightarrow> Ref (tr_ref r))"
  by (cases r) (simp_all add: admininstr_ref.simps)

end

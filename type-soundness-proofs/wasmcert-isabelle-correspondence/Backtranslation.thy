(* Translation from WasmCert-Isabelle back to the SpecTec-generated Wasm 2.0 semantics:
   the inverse of [Translation].  Isabelle counterpart of
   ../wasmcert-rocq/backtranslation.v.

   The translation is partial ([option]-valued).  It fails on
   - WasmCert values that SpecTec's well-formedness rules out: indices and limits
     that do not fit in a u32, lane indices that do not fit in a u8, operators at
     the wrong number type, and conversions or annotations the forward translation
     never produces (e.g. a saturating sign extension);
   - host functions and host references that are not the image of a host address;
   - closures whose function type does not occur in their instance's type list.

   Information WasmCert-Isabelle does not keep is chosen canonically:
   - the type index of a function is the first index of its type;
   - module instances have no exports;
   - the type of a global instance is the type of its value;
   - the evaluated null reference [Ref (ConstNull t)] is read back as the
     instruction [REF.NULL t], which is also SpecTec's null value.

   Its holes are uninterpreted constants: [vec_dec], the SpecTec instruction a
   WasmCert vector instruction stands for (the counterpart of [vec_unop] etc.), and
   [of_hostref], the host address of a WasmCert host reference (the counterpart of
   [hostref]). *)
theory Backtranslation
  imports Spec_Aux
begin

consts
  vec_dec :: "b_e \<Rightarrow> instr option"
  of_hostref :: "host_ref \<Rightarrow> nat option"

section \<open>Option helpers\<close>

definition guard :: "bool \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "guard b x = (if b then x else None)"

lemma guard_simps[simp]: "guard True x = x" "guard False x = None"
  by (simp_all add: guard_def)

definition oopt :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a option \<Rightarrow> 'b option option" where
  "oopt f x = (case x of None \<Rightarrow> Some None | Some a \<Rightarrow> map_option Some (f a))"

definition olist :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "olist f xs = those (map f xs)"

section \<open>Types\<close>

fun of_numtype :: "t_num \<Rightarrow> numtype" where
  "of_numtype T_i32 = I32"
| "of_numtype T_i64 = I64"
| "of_numtype T_f32 = F32"
| "of_numtype T_f64 = F64"

fun of_Inn :: "t_num \<Rightarrow> Inn option" where
  "of_Inn T_i32 = Some Inn_I32"
| "of_Inn T_i64 = Some Inn_I64"
| "of_Inn _ = None"

fun of_Fnn :: "t_num \<Rightarrow> Fnn option" where
  "of_Fnn T_f32 = Some Fnn_F32"
| "of_Fnn T_f64 = Some Fnn_F64"
| "of_Fnn _ = None"

fun of_reftype :: "t_ref \<Rightarrow> reftype" where
  "of_reftype T_func_ref = FUNCREF"
| "of_reftype T_ext_ref = EXTERNREF"

fun of_valtype :: "t \<Rightarrow> valtype" where
  "of_valtype (T_num T_i32) = valtype_I32"
| "of_valtype (T_num T_i64) = valtype_I64"
| "of_valtype (T_num T_f32) = valtype_F32"
| "of_valtype (T_num T_f64) = valtype_F64"
| "of_valtype (T_vec T_v128) = valtype_V128"
| "of_valtype (T_ref T_func_ref) = valtype_FUNCREF"
| "of_valtype (T_ref T_ext_ref) = valtype_EXTERNREF"
| "of_valtype T_bot = BOT"

definition of_resulttype :: "t list \<Rightarrow> resulttype" where
  "of_resulttype ts = mk_list (map of_valtype ts)"

fun of_functype :: "tf \<Rightarrow> functype" where
  "of_functype (Tf t1 t2) = mk_functype (of_resulttype t1) (of_resulttype t2)"

definition of_u32 :: "nat \<Rightarrow> uN option" where
  "of_u32 n = guard (n < 2 ^ 32) (Some (mk_uN n))"

definition of_u8 :: "nat \<Rightarrow> uN option" where
  "of_u8 n = guard (n < 2 ^ 8) (Some (mk_uN n))"

definition of_limits :: "limit_t \<Rightarrow> limits option" where
  "of_limits l =
     (case (of_u32 (l_min l), oopt of_u32 (l_max l)) of
        (Some mn, Some mx) \<Rightarrow> Some (mk_limits mn mx) | _ \<Rightarrow> None)"

fun of_mut :: "Wasm_Ast.mut \<Rightarrow> sp_mut" where
  "of_mut T_mut = Some MUT"
| "of_mut T_immut = None"

definition of_globaltype :: "tg \<Rightarrow> globaltype" where
  "of_globaltype g = mk_globaltype (of_mut (tg_mut g)) (of_valtype (tg_t g))"

fun of_tabletype :: "tab_t \<Rightarrow> tabletype option" where
  "of_tabletype (T_tab l rt) = map_option (\<lambda>l'. mk_tabletype l' (of_reftype rt)) (of_limits l)"

definition of_memtype :: "mem_t \<Rightarrow> memtype option" where
  "of_memtype l = map_option PAGE (of_limits l)"

section \<open>Values\<close>

definition of_i32 :: "Wasm_Ast.i32 \<Rightarrow> uN" where
  "of_i32 i = mk_uN (unat (Rep_i32 i))"

definition of_i64 :: "Wasm_Ast.i64 \<Rightarrow> uN" where
  "of_i64 i = mk_uN (unat (Rep_i64 i))"

(* Inverse of [fmag_bits]/[fN_bits]. *)
definition fmag_of_bits :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> fNmag option" where
  "fmag_of_bits M E b =
     (let e = b div 2 ^ M; m = b mod 2 ^ M; bias = 2 ^ (E - 1) - 1 in
      if e = 0 then Some (SUBNORM m)
      else if e = 2 ^ E - 1 then Some (if m = 0 then res_INF else NAN m)
      else Some (NORM m (int e - int bias)))"

definition fN_of_bits :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> fN option" where
  "fN_of_bits M E b =
     map_option (if b div 2 ^ (M + E) = 0 then POS else NEG) (fmag_of_bits M E (b mod 2 ^ (M + E)))"

definition of_f32 :: "Wasm_Ast.f32 \<Rightarrow> fN option" where
  "of_f32 x = fN_of_bits 23 8 (unat (Rep_f32 x))"

definition of_f64 :: "Wasm_Ast.f64 \<Rightarrow> fN option" where
  "of_f64 x = fN_of_bits 52 11 (unat (Rep_f64 x))"

fun of_num :: "v_num \<Rightarrow> num_underscore option" where
  "of_num (ConstInt32 i) = Some (mk_num__0 Inn_I32 (of_i32 i))"
| "of_num (ConstInt64 i) = Some (mk_num__0 Inn_I64 (of_i64 i))"
| "of_num (ConstFloat32 x) = map_option (mk_num__1 Fnn_F32) (of_f32 x)"
| "of_num (ConstFloat64 x) = map_option (mk_num__1 Fnn_F64) (of_f64 x)"

definition of_v128 :: "v128 \<Rightarrow> uN" where
  "of_v128 v = mk_uN (unat (Rep_v128 v))"

fun of_vec :: "v_vec \<Rightarrow> uN" where
  "of_vec (ConstVec128 v) = of_v128 v"

fun of_host :: "host \<Rightarrow> nat option" where
  "of_host (Host_ref h) = of_hostref h"
| "of_host (Host_func _) = None"

fun of_ref :: "v_ref \<Rightarrow> ref option" where
  "of_ref (ConstNull t) = Some (ref_REF_NULL (of_reftype t))"
| "of_ref (ConstRefFunc a) = Some (REF_FUNC_ADDR a)"
| "of_ref (ConstRefExtern h) = map_option REF_HOST_ADDR (of_host h)"

fun of_val :: "v \<Rightarrow> val option" where
  "of_val (V_num c) = map_option (val_CONST (of_numtype (typeof_num c))) (of_num c)"
| "of_val (V_vec c) = Some (val_VCONST V128 (of_vec c))"
| "of_val (V_ref (ConstNull t)) = Some (val_REF_NULL (of_reftype t))"
| "of_val (V_ref (ConstRefFunc a)) = Some (val_REF_FUNC_ADDR a)"
| "of_val (V_ref (ConstRefExtern h)) = map_option val_REF_HOST_ADDR (of_host h)"

section \<open>Operators\<close>

fun of_sx :: "Wasm_Ast.sx \<Rightarrow> sp_sx" where
  "of_sx Wasm_Ast.U = isabelle_reference_output_wasm2.U"
| "of_sx Wasm_Ast.S = isabelle_reference_output_wasm2.S"

fun bits_of_tp :: "tp_num \<Rightarrow> nat" where
  "bits_of_tp Tp_i8 = 8"
| "bits_of_tp Tp_i16 = 16"
| "bits_of_tp Tp_i32 = 32"

fun of_unop_i :: "unop_i \<Rightarrow> unop_Inn" where
  "of_unop_i Clz = CLZ" | "of_unop_i Ctz = CTZ" | "of_unop_i Popcnt = POPCNT"

fun of_unop_f :: "unop_f \<Rightarrow> unop_Fnn" where
  "of_unop_f Neg = unop_Fnn_NEG" | "of_unop_f Abs = ABS" | "of_unop_f Ceil = CEIL"
| "of_unop_f Floor = FLOOR" | "of_unop_f Trunc = TRUNC" | "of_unop_f Nearest = NEAREST"
| "of_unop_f Sqrt = SQRT"

fun of_unop :: "t_num \<Rightarrow> unop \<Rightarrow> unop_underscore option" where
  "of_unop t (Unop_i uo) = map_option (\<lambda>i. mk_unop__0 i (of_unop_i uo)) (of_Inn t)"
| "of_unop t (Unop_f uo) = map_option (\<lambda>f. mk_unop__1 f (of_unop_f uo)) (of_Fnn t)"
| "of_unop t (Extend_s tp) = map_option (\<lambda>i. mk_unop__0 i (EXTEND (bits_of_tp tp))) (of_Inn t)"

fun of_binop_i :: "binop_i \<Rightarrow> binop_Inn" where
  "of_binop_i Add = ADD" | "of_binop_i Sub = SUB" | "of_binop_i Mul = MUL"
| "of_binop_i (Div s) = DIV (of_sx s)" | "of_binop_i (Rem s) = REM (of_sx s)"
| "of_binop_i And = AND" | "of_binop_i Or = OR" | "of_binop_i Xor = XOR"
| "of_binop_i Shl = SHL" | "of_binop_i (Shr s) = SHR (of_sx s)"
| "of_binop_i Rotl = ROTL" | "of_binop_i Rotr = ROTR"

fun of_binop_f :: "binop_f \<Rightarrow> binop_Fnn" where
  "of_binop_f Addf = binop_Fnn_ADD" | "of_binop_f Subf = binop_Fnn_SUB"
| "of_binop_f Mulf = binop_Fnn_MUL" | "of_binop_f Divf = binop_Fnn_DIV"
| "of_binop_f Min = res_MIN" | "of_binop_f Max = res_MAX" | "of_binop_f Copysign = COPYSIGN"

fun of_binop :: "t_num \<Rightarrow> binop \<Rightarrow> binop_underscore option" where
  "of_binop t (Binop_i uo) = map_option (\<lambda>i. mk_binop__0 i (of_binop_i uo)) (of_Inn t)"
| "of_binop t (Binop_f uo) = map_option (\<lambda>f. mk_binop__1 f (of_binop_f uo)) (of_Fnn t)"

definition of_testop :: "t_num \<Rightarrow> testop_underscore option" where
  "of_testop t = map_option (\<lambda>i. mk_testop__0 i EQZ) (of_Inn t)"

fun of_relop_i :: "relop_i \<Rightarrow> relop_Inn" where
  "of_relop_i Eq = EQ" | "of_relop_i Ne = NE"
| "of_relop_i (Lt s) = LT (of_sx s)" | "of_relop_i (Gt s) = GT (of_sx s)"
| "of_relop_i (Le s) = LE (of_sx s)" | "of_relop_i (Ge s) = GE (of_sx s)"

fun of_relop_f :: "relop_f \<Rightarrow> relop_Fnn" where
  "of_relop_f Eqf = relop_Fnn_EQ" | "of_relop_f Nef = relop_Fnn_NE"
| "of_relop_f Ltf = relop_Fnn_LT" | "of_relop_f Gtf = relop_Fnn_GT"
| "of_relop_f Lef = relop_Fnn_LE" | "of_relop_f Gef = relop_Fnn_GE"

fun of_relop :: "t_num \<Rightarrow> relop \<Rightarrow> relop_underscore option" where
  "of_relop t (Relop_i uo) = map_option (\<lambda>i. mk_relop__0 i (of_relop_i uo)) (of_Inn t)"
| "of_relop t (Relop_f uo) = map_option (\<lambda>f. mk_relop__1 f (of_relop_f uo)) (of_Fnn t)"

(* [Cvtop t2 op t1 sat_sx] converts from [t1] to [t2].  Only the operator/annotation
   combinations [tr_cvtop] produces are read back. *)
fun of_cvtop :: "t_num \<Rightarrow> cvtop \<Rightarrow> t_num \<Rightarrow> (sat \<times> Wasm_Ast.sx) option \<Rightarrow> cvtop__underscore option" where
  "of_cvtop T_i64 Convert T_i32 (Some (Nonsat, s)) =
     Some (mk_cvtop___0 Inn_I32 Inn_I64 (cvtop__Inn_1_Inn_2_EXTEND (of_sx s)))"
| "of_cvtop T_i32 Convert T_i64 None = Some (mk_cvtop___0 Inn_I64 Inn_I32 WRAP)"
| "of_cvtop t2 Convert t1 (Some (Nonsat, s)) =
     (case (of_Inn t1, of_Fnn t2, of_Fnn t1, of_Inn t2) of
        (Some i, Some f, _, _) \<Rightarrow> Some (mk_cvtop___1 i f (CONVERT (of_sx s)))
      | (_, _, Some f, Some i) \<Rightarrow> Some (mk_cvtop___2 f i (cvtop__Fnn_1_Inn_2_TRUNC (of_sx s)))
      | _ \<Rightarrow> None)"
| "of_cvtop t2 Convert t1 (Some (Sat, s)) =
     (case (of_Fnn t1, of_Inn t2) of
        (Some f, Some i) \<Rightarrow> Some (mk_cvtop___2 f i (TRUNC_SAT (of_sx s))) | _ \<Rightarrow> None)"
| "of_cvtop T_f64 Convert T_f32 None = Some (mk_cvtop___3 Fnn_F32 Fnn_F64 PROMOTE)"
| "of_cvtop T_f32 Convert T_f64 None = Some (mk_cvtop___3 Fnn_F64 Fnn_F32 DEMOTE)"
| "of_cvtop T_f32 Reinterpret T_i32 None = Some (mk_cvtop___1 Inn_I32 Fnn_F32 REINTERPRET)"
| "of_cvtop T_f64 Reinterpret T_i64 None = Some (mk_cvtop___1 Inn_I64 Fnn_F64 REINTERPRET)"
| "of_cvtop T_i32 Reinterpret T_f32 None = Some (mk_cvtop___2 Fnn_F32 Inn_I32 cvtop__Fnn_1_Inn_2_REINTERPRET)"
| "of_cvtop T_i64 Reinterpret T_f64 None = Some (mk_cvtop___2 Fnn_F64 Inn_I64 cvtop__Fnn_1_Inn_2_REINTERPRET)"
| "of_cvtop _ _ _ _ = None"

definition of_memarg :: "nat \<Rightarrow> nat \<Rightarrow> memarg option" where
  "of_memarg a off =
     (case (of_u32 a, of_u32 off) of (Some a', Some o') \<Rightarrow> Some \<lparr>ALIGN = a', OFFSET = o'\<rparr> | _ \<Rightarrow> None)"

(* A packed access must be narrower than its integer type. *)
definition of_pack :: "t_num \<Rightarrow> tp_num \<Rightarrow> Inn option" where
  "of_pack t tp = (case of_Inn t of
                     Some i \<Rightarrow> guard (bits_of_tp tp < 8 * t_num_length t) (Some i) | None \<Rightarrow> None)"

fun of_loadop :: "t_num \<Rightarrow> (tp_num \<times> Wasm_Ast.sx) option \<Rightarrow> loadop_underscore option option" where
  "of_loadop t None = Some None"
| "of_loadop t (Some (tp, s)) =
     map_option (\<lambda>i. Some (mk_loadop__0 i (mk_loadop_Inn (mk_sz (bits_of_tp tp)) (of_sx s)))) (of_pack t tp)"

fun of_storeop :: "t_num \<Rightarrow> tp_num option \<Rightarrow> sz option option" where
  "of_storeop t None = Some None"
| "of_storeop t (Some tp) = map_option (\<lambda>_. Some (mk_sz (bits_of_tp tp))) (of_pack t tp)"

fun bits_of_svi :: "shape_vec_i \<Rightarrow> nat" where
  "bits_of_svi I8_16 = 8" | "bits_of_svi I16_8 = 16" | "bits_of_svi I32_4 = 32" | "bits_of_svi I64_2 = 64"

fun of_vloadop :: "loadop_vec \<Rightarrow> vloadop_underscore option" where
  "of_vloadop Load_128 = None"
| "of_vloadop (Load_packed_vec Tp_v8_8 s) = Some (SHAPEX_underscore (mk_sz 8) 8 (of_sx s))"
| "of_vloadop (Load_packed_vec Tp_v16_4 s) = Some (SHAPEX_underscore (mk_sz 16) 4 (of_sx s))"
| "of_vloadop (Load_packed_vec Tp_v32_2 s) = Some (SHAPEX_underscore (mk_sz 32) 2 (of_sx s))"
| "of_vloadop Load_32_zero = Some (vloadop__ZERO (mk_sz 32))"
| "of_vloadop Load_64_zero = Some (vloadop__ZERO (mk_sz 64))"
| "of_vloadop (Load_splat svi) = Some (SPLAT (mk_sz (bits_of_svi svi)))"

fun of_blocktype :: "tb \<Rightarrow> blocktype option" where
  "of_blocktype (Tbv t) = Some (underscore_RESULT (map_option of_valtype t))"
| "of_blocktype (Tbf x) = map_option underscore_IDX (of_u32 x)"

fun of_shape :: "shape_vec \<Rightarrow> shape" where
  "of_shape (Svi I8_16) = X lanetype_I8 (mk_dim 16)"
| "of_shape (Svi I16_8) = X lanetype_I16 (mk_dim 8)"
| "of_shape (Svi I32_4) = X lanetype_I32 (mk_dim 4)"
| "of_shape (Svi I64_2) = X lanetype_I64 (mk_dim 2)"
| "of_shape (Svf F32_4) = X lanetype_F32 (mk_dim 4)"
| "of_shape (Svf F64_2) = X lanetype_F64 (mk_dim 2)"

(* Lanes narrower than 32 bits are extracted with a signedness, the others with [U]. *)
fun packed_shape :: "shape_vec \<Rightarrow> bool" where
  "packed_shape (Svi I8_16) = True"
| "packed_shape (Svi I16_8) = True"
| "packed_shape _ = False"

definition of_lane_sx :: "shape_vec \<Rightarrow> Wasm_Ast.sx \<Rightarrow> sp_sx option option" where
  "of_lane_sx sv s = (if packed_shape sv then Some (Some (of_sx s))
                      else if s = Wasm_Ast.U then Some None else None)"

section \<open>Instructions\<close>

(* The instruction constructors, as functions into [instr]. *)
abbreviation "I0 \<equiv> instr_sc0" abbreviation "I1 \<equiv> instr_sc1" abbreviation "I3 \<equiv> instr_sc3"
abbreviation "I4 \<equiv> instr_sc4" abbreviation "I5 \<equiv> instr_sc5" abbreviation "I6 \<equiv> instr_sc6"
abbreviation "I7 \<equiv> instr_sc7"

definition idx1 :: "(uN \<Rightarrow> instr) \<Rightarrow> nat \<Rightarrow> instr option" where
  "idx1 k x = map_option k (of_u32 x)"

definition idx2 :: "(uN \<Rightarrow> uN \<Rightarrow> instr) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> instr option" where
  "idx2 k x y = (case (of_u32 x, of_u32 y) of (Some x', Some y') \<Rightarrow> Some (k x' y') | _ \<Rightarrow> None)"

definition with_memarg :: "(memarg \<Rightarrow> instr) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> instr option" where
  "with_memarg k a off = map_option k (of_memarg a off)"

fun of_instr :: "b_e \<Rightarrow> instr option" where
  "of_instr Unreachable = Some (I0 UNREACHABLE)"
| "of_instr Nop = Some (I0 NOP)"
| "of_instr Drop = Some (I0 DROP)"
| "of_instr (Select t) = Some (I0 (SELECT (map_option (\<lambda>t. [of_valtype t]) t)))"
| "of_instr (Block tb es) =
     (case (of_blocktype tb, those (map of_instr es)) of
        (Some bt, Some es') \<Rightarrow> Some (I7 (BLOCK bt es')) | _ \<Rightarrow> None)"
| "of_instr (Loop tb es) =
     (case (of_blocktype tb, those (map of_instr es)) of
        (Some bt, Some es') \<Rightarrow> Some (I7 (LOOP bt es')) | _ \<Rightarrow> None)"
| "of_instr (If tb es1 es2) =
     (case (of_blocktype tb, those (map of_instr es1), those (map of_instr es2)) of
        (Some bt, Some es1', Some es2') \<Rightarrow> Some (I7 (IFELSE bt es1' es2')) | _ \<Rightarrow> None)"
| "of_instr (Br l) = idx1 (\<lambda>x. I0 (BR x)) l"
| "of_instr (Br_if l) = idx1 (\<lambda>x. I0 (BR_IF x)) l"
| "of_instr (Br_table ls l) =
     (case (those (map of_u32 ls), of_u32 l) of
        (Some ls', Some l') \<Rightarrow> Some (I0 (BR_TABLE ls' l')) | _ \<Rightarrow> None)"
| "of_instr Return = Some (I1 RETURN)"
| "of_instr (Call x) = idx1 (\<lambda>x. I0 (CALL x)) x"
| "of_instr (Call_indirect x y) = idx2 (\<lambda>x y. I0 (CALL_INDIRECT x y)) x y"
| "of_instr (Local_get x) = idx1 (\<lambda>x. I4 (LOCAL_GET x)) x"
| "of_instr (Local_set x) = idx1 (\<lambda>x. I4 (LOCAL_SET x)) x"
| "of_instr (Local_tee x) = idx1 (\<lambda>x. I4 (LOCAL_TEE x)) x"
| "of_instr (Global_get x) = idx1 (\<lambda>x. I4 (GLOBAL_GET x)) x"
| "of_instr (Global_set x) = idx1 (\<lambda>x. I4 (GLOBAL_SET x)) x"
| "of_instr (Table_get x) = idx1 (\<lambda>x. I4 (TABLE_GET x)) x"
| "of_instr (Table_set x) = idx1 (\<lambda>x. I5 (TABLE_SET x)) x"
| "of_instr (Table_size x) = idx1 (\<lambda>x. I5 (TABLE_SIZE x)) x"
| "of_instr (Table_grow x) = idx1 (\<lambda>x. I5 (TABLE_GROW x)) x"
| "of_instr (Load t lo a off) =
     (case of_loadop t lo of
        Some lo' \<Rightarrow> with_memarg (\<lambda>m. I5 (LOAD (of_numtype t) lo' m)) a off | None \<Rightarrow> None)"
| "of_instr (Store t so a off) =
     (case of_storeop t so of
        Some so' \<Rightarrow> with_memarg (\<lambda>m. I5 (STORE (of_numtype t) so' m)) a off | None \<Rightarrow> None)"
| "of_instr (Load_vec lv a off) = with_memarg (\<lambda>m. I6 (VLOAD V128 (of_vloadop lv) m)) a off"
| "of_instr (Load_lane_vec svi j a off) =
     (case of_u8 j of
        Some j' \<Rightarrow> with_memarg (\<lambda>m. I6 (VLOAD_LANE V128 (mk_sz (bits_of_svi svi)) m j')) a off
      | None \<Rightarrow> None)"
| "of_instr (Store_vec Store_128 a off) = with_memarg (\<lambda>m. I6 (VSTORE V128 m)) a off"
| "of_instr (Store_vec (Store_lane svi j) a off) =
     (case of_u8 j of
        Some j' \<Rightarrow> with_memarg (\<lambda>m. I6 (VSTORE_LANE V128 (mk_sz (bits_of_svi svi)) m j')) a off
      | None \<Rightarrow> None)"
| "of_instr Memory_size = Some (I6 MEMORY_SIZE)"
| "of_instr Memory_grow = Some (I6 MEMORY_GROW)"
| "of_instr (Memory_init x) = idx1 (\<lambda>x. I6 (MEMORY_INIT x)) x"
| "of_instr Memory_fill = Some (I6 MEMORY_FILL)"
| "of_instr Memory_copy = Some (I6 MEMORY_COPY)"
| "of_instr (Table_init x y) = idx2 (\<lambda>x y. I5 (TABLE_INIT x y)) x y"
| "of_instr (Table_copy x y) = idx2 (\<lambda>x y. I5 (TABLE_COPY x y)) x y"
| "of_instr (Table_fill x) = idx1 (\<lambda>x. I5 (TABLE_FILL x)) x"
| "of_instr (Elem_drop x) = idx1 (\<lambda>x. I5 (ELEM_DROP x)) x"
| "of_instr (Data_drop x) = idx1 (\<lambda>x. I7 (DATA_DROP x)) x"
| "of_instr (EConstNum c) = map_option (\<lambda>c'. I1 (res_CONST (of_numtype (typeof_num c)) c')) (of_num c)"
| "of_instr (EConstVec c) = Some (I1 (VCONST V128 (of_vec c)))"
| "of_instr (Unop t op) = map_option (\<lambda>op'. I1 (UNOP (of_numtype t) op')) (of_unop t op)"
| "of_instr (Binop t op) = map_option (\<lambda>op'. I1 (BINOP (of_numtype t) op')) (of_binop t op)"
| "of_instr (Testop t op) = map_option (\<lambda>op'. I1 (TESTOP (of_numtype t) op')) (of_testop t)"
| "of_instr (Relop t op) = map_option (\<lambda>op'. I1 (RELOP (of_numtype t) op')) (of_relop t op)"
| "of_instr (Cvtop t2 op t1 s) =
     map_option (\<lambda>op'. I1 (CVTOP (of_numtype t2) (of_numtype t1) op')) (of_cvtop t2 op t1 s)"
| "of_instr (Ref_null t) = Some (I4 (REF_NULL (of_reftype t)))"
| "of_instr Ref_is_null = Some (I4 REF_IS_NULL)"
| "of_instr (Ref_func x) = idx1 (\<lambda>x. I4 (REF_FUNC x)) x"
| "of_instr (Unop_vec op) = vec_dec (Unop_vec op)"
| "of_instr (Binop_vec op) = vec_dec (Binop_vec op)"
| "of_instr (Ternop_vec op) = vec_dec (Ternop_vec op)"
| "of_instr (Test_vec op) = vec_dec (Test_vec op)"
| "of_instr (Shift_vec op) = vec_dec (Shift_vec op)"
| "of_instr (Splat_vec sv) = Some (I3 (VSPLAT (of_shape sv)))"
| "of_instr (Extract_vec sv s j) =
     (case (of_lane_sx sv s, of_u8 j) of
        (Some s', Some j') \<Rightarrow> Some (I3 (VEXTRACT_LANE (of_shape sv) s' j')) | _ \<Rightarrow> None)"
| "of_instr (Replace_vec sv j) = map_option (\<lambda>j'. I3 (VREPLACE_LANE (of_shape sv) j')) (of_u8 j)"

definition of_instrs :: "b_e list \<Rightarrow> instr list option" where
  "of_instrs es = those (map of_instr es)"

section \<open>Runtime structures\<close>

definition of_byte :: "Wasm_Ast.byte \<Rightarrow> sp_byte" where
  "of_byte b = mk_byte (nat_of_uint8 b)"

definition of_local :: "t \<Rightarrow> local" where
  "of_local t = LOCAL (of_valtype t)"

(* WasmCert's instances have no exports. *)
definition of_inst :: "inst \<Rightarrow> moduleinst" where
  "of_inst i =
     \<lparr>TYPES = map of_functype (inst.types i), FUNCS = inst.funcs i, GLOBALS = inst.globs i,
      TABLES = inst.tabs i, MEMS = inst.mems i, ELEMS = inst.elems i, DATAS = inst.datas i,
      EXPORTS = []\<rparr>"

fun first_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "first_index x [] = None"
| "first_index x (y # ys) = (if x = y then Some 0 else map_option Suc (first_index x ys))"

(* A closure's type index is the first index of its function type. *)
fun of_cl :: "cl \<Rightarrow> funcinst option" where
  "of_cl (Func_native i tf ts es) =
     (case (Option.bind (first_index tf (inst.types i)) of_u32, those (map of_instr es)) of
        (Some x, Some body) \<Rightarrow>
          Some \<lparr>funcinst_TYPE = of_functype tf, funcinst_MODULE = of_inst i,
                CODE = func_FUNC x (map of_local ts) body\<rparr>
      | _ \<Rightarrow> None)"
| "of_cl (Func_host _ _) = None"

(* A global instance's type is its value's type. *)
definition of_global :: "global \<Rightarrow> globalinst option" where
  "of_global g =
     map_option (\<lambda>v. \<lparr>globalinst_TYPE = mk_globaltype (of_mut (g_mut g)) (of_valtype (typeof (g_val g))),
                      VALUE = v\<rparr>) (of_val (g_val g))"

definition of_tabinst :: "tabinst \<Rightarrow> tableinst option" where
  "of_tabinst t =
     (case (of_tabletype (fst t), those (map of_ref (snd t))) of
        (Some tt, Some rs) \<Rightarrow> Some \<lparr>tableinst_TYPE = tt, REFS = rs\<rparr> | _ \<Rightarrow> None)"

definition of_mem :: "mem \<Rightarrow> meminst option" where
  "of_mem m =
     map_option (\<lambda>mt. \<lparr>meminst_TYPE = mt, BYTES = map of_byte (Rep_mem_rep (snd m))\<rparr>) (of_memtype (fst m))"

definition of_eleminst :: "Wasm_Ast.eleminst \<Rightarrow> isabelle_reference_output_wasm2.eleminst option" where
  "of_eleminst e =
     map_option (\<lambda>rs. \<lparr>eleminst_TYPE = of_reftype (fst e), eleminst_REFS = rs\<rparr>) (those (map of_ref (snd e)))"

definition of_datainst :: "Wasm_Ast.datainst \<Rightarrow> isabelle_reference_output_wasm2.datainst" where
  "of_datainst d = \<lparr>datainst_BYTES = map of_byte d\<rparr>"

definition of_store :: "s \<Rightarrow> store option" where
  "of_store st =
     (case (those (map of_cl (s.funcs st)), those (map of_global (s.globs st)),
            those (map of_tabinst (s.tabs st)), those (map of_mem (s.mems st)),
            those (map of_eleminst (s.elems st))) of
        (Some fs, Some gs, Some ts, Some ms, Some es) \<Rightarrow>
          Some \<lparr>store_FUNCS = fs, store_GLOBALS = gs, store_TABLES = ts, store_MEMS = ms,
                store_ELEMS = es, store_DATAS = map of_datainst (s.datas st)\<rparr>
      | _ \<Rightarrow> None)"

definition of_frame :: "f \<Rightarrow> frame option" where
  "of_frame fr =
     map_option (\<lambda>vs. \<lparr>LOCALS = vs, frame_MODULE = of_inst (f_inst fr)\<rparr>) (those (map of_val (f_locs fr)))"

section \<open>Administrative instructions\<close>

fun of_basic :: "e \<Rightarrow> b_e option" where
  "of_basic (Basic b) = Some b"
| "of_basic _ = None"

fun of_admin :: "e \<Rightarrow> admininstr option" where
  "of_admin (Basic b) = map_option admininstr_instr (of_instr b)"
| "of_admin Trap = Some (admininstr_sc7 admininstr_st7_TRAP)"
| "of_admin (Invoke a) = Some (admininstr_sc7 (CALL_ADDR a))"
| "of_admin (Label n es0 es) =
     (case (Option.bind (those (map of_basic es0)) of_instrs, those (map of_admin es)) of
        (Some ins, Some es') \<Rightarrow> Some (admininstr_sc7 (LABEL_underscore n ins es')) | _ \<Rightarrow> None)"
| "of_admin (Frame n fr es) =
     (case (of_frame fr, those (map of_admin es)) of
        (Some fr', Some es') \<Rightarrow> Some (admininstr_sc8 (FRAME_underscore n fr' es')) | _ \<Rightarrow> None)"
| "of_admin (Ref r) = map_option admininstr_ref (of_ref r)"

definition of_admins :: "e list \<Rightarrow> admininstr list option" where
  "of_admins es = those (map of_admin es)"

fun of_config :: "s \<times> f \<times> e list \<Rightarrow> config option" where
  "of_config (st, fr, es) =
     (case (of_store st, of_frame fr, of_admins es) of
        (Some st', Some fr', Some es') \<Rightarrow> Some (mk_config (mk_state st' fr') es') | _ \<Rightarrow> None)"

section \<open>Typing contexts\<close>

(* WasmCert's [refs] component has no SpecTec counterpart and is dropped. *)
definition of_context :: "t_context \<Rightarrow> res_context option" where
  "of_context C =
     (case (those (map of_tabletype (table C)), those (map of_memtype (memory C))) of
        (Some tts, Some mts) \<Rightarrow>
          Some \<lparr>context_TYPES = map of_functype (types_t C), context_FUNCS = map of_functype (func_t C),
                context_GLOBALS = map of_globaltype (global C), context_TABLES = tts, context_MEMS = mts,
                context_ELEMS = map of_reftype (elem C), context_DATAS = map (\<lambda>_. OK) (data C),
                context_LOCALS = map of_valtype (local C), LABELS = map of_resulttype (label C),
                context_RETURN = map_option of_resulttype (return C)\<rparr>
      | _ \<Rightarrow> None)"

end

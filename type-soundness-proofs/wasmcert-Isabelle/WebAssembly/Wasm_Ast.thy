section \<open>WebAssembly Core AST\<close>

theory Wasm_Ast
  imports
    Main
    "HOL-Library.Word"
    "Word_Lib.Reversed_Bit_Lists"
    "Native_Word.Uint8"
begin

type_synonym
  i = nat
type_synonym
  off = nat
type_synonym
  a = nat

typedef i32 = "UNIV :: (32 word) set" ..
typedef i64 = "UNIV :: (64 word) set" ..

typedef f32 = "UNIV :: (32 word) set" ..
typedef f64 = "UNIV :: (64 word) set" ..
typedef v128 = "UNIV :: (128 word) set" ..

setup_lifting type_definition_i32
declare Quotient_i32[transfer_rule]
setup_lifting type_definition_i64
declare Quotient_i64[transfer_rule]

type_synonym byte = uint8

definition "msb_byte = (msb::byte \<Rightarrow> bool)"
definition "zero_byte = (0::byte)"
definition "negone_byte = (-1::byte)"

definition "nat_of_byte = nat_of_uint8"
definition "byte_of_nat = uint8_of_nat"

type_synonym bytes = "byte list"

definition bytes_takefill :: "byte \<Rightarrow> nat \<Rightarrow> bytes \<Rightarrow> bytes" where
  "bytes_takefill = (\<lambda>(a::byte) n as. takefill a n as)"

definition bytes_replicate :: "nat \<Rightarrow> byte \<Rightarrow> bytes" where
  "bytes_replicate = (\<lambda>n (b::byte). replicate n b)"

definition msbyte :: "bytes \<Rightarrow> byte" where
  "msbyte bs = last (bs)"

record limit_t =
  l_min :: nat
  l_max :: "nat option"

free_constructors case_limit_t_ext for limit_t_ext
  using limit_t.cases_scheme
  by blast+


definition Ki64 :: "nat" where
  "Ki64 = 65536"

typedef mem_rep = "UNIV :: (byte list) set" ..
setup_lifting type_definition_mem_rep
declare Quotient_mem_rep[transfer_rule]

type_synonym mem_t =
  "limit_t"

type_synonym mem = "(mem_t \<times> mem_rep)"

lift_definition mem_rep_mk :: "nat \<Rightarrow> mem_rep" is "(\<lambda>n. (bytes_replicate (n * Ki64) zero_byte))" .

definition mem_mk :: "limit_t \<Rightarrow> mem" where
  "mem_mk lim = (lim, mem_rep_mk (l_min lim))"

lift_definition mem_rep_byte_at :: "mem_rep \<Rightarrow> nat \<Rightarrow> byte" is "(\<lambda>m n. m!n)::(byte list) \<Rightarrow> nat \<Rightarrow> byte" .
definition byte_at :: "mem \<Rightarrow> nat \<Rightarrow> byte" where
  "byte_at m n = mem_rep_byte_at (snd m) n"

lift_definition mem_rep_length :: "mem_rep \<Rightarrow> nat" is "(\<lambda>m. length m)" .
definition mem_length :: "mem \<Rightarrow> nat" where
  "mem_length m = mem_rep_length (snd m)"

definition mem_max :: "mem \<Rightarrow> nat option" where
  "mem_max m = l_max (fst m)"

lift_definition mem_rep_read_bytes :: "mem_rep \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bytes" is "(\<lambda>m n l. (take l (drop n m))::(byte list))" .
definition read_bytes :: "mem \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bytes" where
  "read_bytes m n l = mem_rep_read_bytes (snd m) n l"

lift_definition mem_rep_write_bytes :: "mem_rep \<Rightarrow> nat \<Rightarrow> bytes \<Rightarrow> mem_rep" is "(\<lambda>m n bs. ((take n m) @ bs @ (drop (n + length bs) m)) :: byte list)" .
definition write_bytes :: "mem \<Rightarrow> nat \<Rightarrow> bytes \<Rightarrow> mem" where
  "write_bytes m n bs = (fst m, mem_rep_write_bytes (snd m) n bs)"

lift_definition mem_rep_append :: "mem_rep \<Rightarrow> nat \<Rightarrow> byte \<Rightarrow> mem_rep" is "(\<lambda>m n b. (append m (replicate n b))::byte list)" .
definition mem_append :: "mem \<Rightarrow> nat \<Rightarrow> byte \<Rightarrow> mem" where
  "mem_append m n b = ((fst m)\<lparr>l_min := l_min (fst m) + (n div Ki64)\<rparr>, mem_rep_append (snd m) n b)"

lemma take_drop_map:
  assumes "ind+n \<le> length bs"
  shows "(take n (drop ind bs)) = (map ((!) bs) [ind..<ind + n])"
proof -
  have "(drop ind bs) = (map ((!) bs) [ind..<length bs])"
    using drop_map map_nth
    by (metis add.commute add.right_neutral drop_upt)
  thus ?thesis
    by (simp add: assms(1) take_map)
qed

lemma read_bytes_map:
  assumes "ind+n \<le> mem_length m"
  shows "read_bytes m ind n = (map (\<lambda>k. byte_at m k) [ind..<ind+n])"
  using assms
  unfolding read_bytes_def mem_rep_read_bytes_def mem_rep_byte_at_def
            byte_at_def mem_length_def mem_rep_length_def
  by (simp add: take_drop_map split: prod.splits)

typedecl host_func
typedecl host_ref
datatype host = Host_func host_func | Host_ref host_ref
typedecl host_state

datatype
  t_num = T_i32 | T_i64 | T_f32 | T_f64

datatype
  t_vec = T_v128

datatype
  t_ref = T_func_ref | T_ext_ref

datatype
  t = T_num t_num | T_vec t_vec | T_ref t_ref | T_bot

datatype
  tp_num = Tp_i8 | Tp_i16 | Tp_i32

datatype
  tp_vec = Tp_v8_8 | Tp_v16_4 | Tp_v32_2

datatype
  mut = T_immut | T_mut

record tg =
  tg_mut :: mut
  tg_t :: t

free_constructors case_tg_ext for tg_ext
  using tg.cases_scheme
  by blast+


datatype
  tf = Tf (dom: "t list") (ran: "t list") ("_ '_> _" 60)
hide_const (open) tf.dom tf.ran
  
datatype
  tb = Tbf i | Tbv "t option"

datatype tab_t = T_tab limit_t t_ref

definition tab_t_lim :: "tab_t \<Rightarrow> limit_t" where
"tab_t_lim tt = (case tt of
  T_tab lim _ \<Rightarrow> lim)"

definition tab_t_reftype :: "tab_t \<Rightarrow> t_ref" where
"tab_t_reftype tt = (case tt of
  T_tab _ t \<Rightarrow> t)"

type_synonym data_t = "unit"
type_synonym elem_t = "t_ref"

record t_context =
  types_t :: "tf list"
  func_t :: "tf list"
  global :: "tg list"
  elem :: "elem_t list"
  data :: "data_t list"
  table :: "tab_t list"
  memory :: "mem_t list"
  local :: "t list"
  label :: "(t list) list"
  return :: "(t list) option"
  refs :: "i list"

datatype
  v_num = ConstInt32 i32
        | ConstInt64 i64
        | ConstFloat32 f32
        | ConstFloat64 f64

datatype
  v_ref = ConstNull t_ref
  | ConstRefFunc i
  | ConstRefExtern host

datatype
  v_vec = ConstVec128 v128

datatype
  v = V_num v_num | V_vec v_vec | V_ref v_ref

datatype
  sx = S | U

datatype
  sat = Sat | Nonsat

datatype
  unop_i = Clz | Ctz | Popcnt

datatype
  unop_f = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt

datatype
  unop = Unop_i unop_i | Unop_f unop_f
         | Extend_s tp_num

datatype
  binop_i = Add | Sub | Mul | Div sx | Rem sx | And | Or | Xor | Shl | Shr sx | Rotl | Rotr

datatype
  binop_f = Addf | Subf | Mulf | Divf | Min | Max | Copysign

datatype
  binop = Binop_i binop_i | Binop_f binop_f
  
datatype
  testop = Eqz
  
datatype
  relop_i = Eq | Ne | Lt sx | Gt sx | Le sx | Ge sx
  
datatype
  relop_f = Eqf | Nef | Ltf | Gtf | Lef | Gef

datatype
  relop = Relop_i relop_i | Relop_f relop_f

datatype
  cvtop = Convert | Reinterpret

datatype shape_vec_i = I8_16 | I16_8 | I32_4 | I64_2

datatype shape_vec_f = F32_4 | F64_2

datatype shape_vec = Svi shape_vec_i | Svf shape_vec_f

datatype
  loadop_vec =
    Load_128
  | Load_packed_vec tp_vec sx
  | Load_32_zero
  | Load_64_zero
  | Load_splat shape_vec_i

datatype
  storeop_vec =
    Store_128
  | Store_lane shape_vec_i i

  
consts unop_vec_carrier :: "nat set"  
specification (unop_vec_carrier) 
  unop_vec_finite[simp]: "finite unop_vec_carrier" 
  unop_vec_ne: "unop_vec_carrier \<noteq> {}" 
  by blast  

typedef unop_vec = "unop_vec_carrier" using unop_vec_ne by blast

lemma range_unop_vec[simp]: "range Rep_unop_vec = unop_vec_carrier"
  apply (auto)
  apply (simp add: Rep_unop_vec)
  by (metis Rep_unop_vec_cases rangeI)

instance unop_vec :: finite
  apply standard
  apply (rule finite_imageD[where f=Rep_unop_vec])
  apply (auto)
  by (meson Rep_unop_vec_inject inj_onI)



consts binop_vec_carrier :: "nat set"  
specification (binop_vec_carrier) 
  binop_vec_finite[simp]: "finite binop_vec_carrier" 
  binop_vec_ne: "binop_vec_carrier \<noteq> {}" 
  by blast  

typedef binop_vec = "binop_vec_carrier" using binop_vec_ne by blast

lemma range_binop_vec[simp]: "range Rep_binop_vec = binop_vec_carrier"
  apply (auto)
  apply (simp add: Rep_binop_vec)
  by (metis Rep_binop_vec_cases rangeI)

instance binop_vec :: finite
  apply standard
  apply (rule finite_imageD[where f=Rep_binop_vec])
  apply (auto)
  by (meson Rep_binop_vec_inject inj_onI)
  
  
consts ternop_vec_carrier :: "nat set"  
specification (ternop_vec_carrier) 
  ternop_vec_finite[simp]: "finite ternop_vec_carrier" 
  ternop_vec_ne: "ternop_vec_carrier \<noteq> {}" 
  by blast  

typedef ternop_vec = "ternop_vec_carrier" using ternop_vec_ne by blast

lemma range_ternop_vec[simp]: "range Rep_ternop_vec = ternop_vec_carrier"
  apply (auto)
  apply (simp add: Rep_ternop_vec)
  by (metis Rep_ternop_vec_cases rangeI)

instance ternop_vec :: finite
  apply standard
  apply (rule finite_imageD[where f=Rep_ternop_vec])
  apply (auto)
  by (meson Rep_ternop_vec_inject inj_onI)
  

  
consts testop_vec_carrier :: "nat set"  
specification (testop_vec_carrier) 
  testop_vec_finite[simp]: "finite testop_vec_carrier" 
  testop_vec_ne: "testop_vec_carrier \<noteq> {}" 
  by blast  

typedef testop_vec = "testop_vec_carrier" using testop_vec_ne by blast

lemma range_testop_vec[simp]: "range Rep_testop_vec = testop_vec_carrier"
  apply (auto)
  apply (simp add: Rep_testop_vec)
  by (metis Rep_testop_vec_cases rangeI)

instance testop_vec :: finite
  apply standard
  apply (rule finite_imageD[where f=Rep_testop_vec])
  apply (auto)
  by (meson Rep_testop_vec_inject inj_onI)

  
consts shiftop_vec_carrier :: "nat set"  
specification (shiftop_vec_carrier) 
  shiftop_vec_finite[simp]: "finite shiftop_vec_carrier" 
  shiftop_vec_ne: "shiftop_vec_carrier \<noteq> {}" 
  by blast  

typedef shiftop_vec = "shiftop_vec_carrier" using shiftop_vec_ne by blast

lemma range_shiftop_vec[simp]: "range Rep_shiftop_vec = shiftop_vec_carrier"
  apply (auto)
  apply (simp add: Rep_shiftop_vec)
  by (metis Rep_shiftop_vec_cases rangeI)

instance shiftop_vec :: finite
  apply standard
  apply (rule finite_imageD[where f=Rep_shiftop_vec])
  apply (auto)
  by (meson Rep_shiftop_vec_inject inj_onI)
  
      
datatype
  b_e =
    Unreachable
    | Nop
    | Drop
    | Select "(t option)"
    | Block tb "b_e list"
    | Loop tb "b_e list"
    | If tb "b_e list" "b_e list"
    | Br i
    | Br_if i
    | Br_table "i list" i
    | Return
    | Call i
    | Call_indirect i i
    | Local_get i
    | Local_set i
    | Local_tee i
    | Global_get i
    | Global_set i
    | Table_get i
    | Table_set i
    | Table_size i
    | Table_grow i
    | Load t_num "(tp_num \<times> sx) option" a off
    | Store t_num "tp_num option" a off
    | Load_vec loadop_vec a off
    | Load_lane_vec shape_vec_i i a off
    | Store_vec storeop_vec a off
    | Memory_size
    | Memory_grow
    | Memory_init i
    | Memory_fill
    | Memory_copy
    | Table_init i i
    | Table_copy i i
    | Table_fill i
    | Elem_drop i
    | Data_drop i
    | EConstNum v_num
    | EConstVec v_vec
    | Unop t_num unop
    | Binop t_num binop
    | Testop t_num testop
    | Relop t_num relop
    | Cvtop t_num cvtop t_num "(sat \<times> sx) option"
    | Ref_null t_ref
    | Ref_is_null
    | Ref_func i
    | Unop_vec unop_vec
    | Binop_vec binop_vec
    | Ternop_vec ternop_vec
    | Test_vec testop_vec
    | Shift_vec shiftop_vec
    | Splat_vec shape_vec
    | Extract_vec shape_vec sx i
    | Replace_vec shape_vec i

record inst =
  types :: "tf list"
  funcs :: "i list"
  tabs :: "i list"
  mems :: "i list"
  globs :: "i list"
  elems :: "i list"
  datas :: "i list"

datatype cl =
  Func_native inst tf "t list" "b_e list"
| Func_host tf host

type_synonym tabinst = "tab_t \<times> v_ref list"
type_synonym eleminst = "elem_t \<times> v_ref list"
type_synonym datainst =  "bytes"

abbreviation "tab_size (t::tabinst) \<equiv> length (snd t)"
definition tab_max :: "tabinst \<Rightarrow> nat option" where
  "tab_max t \<equiv> (case t of
    (T_tab limits _, _) \<Rightarrow> l_max limits)"

definition tab_reftype :: "tabinst \<Rightarrow> t_ref" where
  "tab_reftype t \<equiv> (case (fst t) of
    T_tab _ tt \<Rightarrow> tt)"

record global =
  g_mut :: mut
  g_val :: v

record s =
  funcs :: "cl list"
  tabs :: "tabinst list"
  mems :: "mem list"
  globs :: "global list"
  elems :: "eleminst list"
  datas :: "datainst list"

record f =
  f_locs :: "v list"
  f_inst :: inst

datatype e =
  Basic b_e ("$_" 50)
  | Trap
  | Invoke i
  | Label nat "e list" "e list"
  | Frame nat f "e list"
  | Ref v_ref

datatype Lholed =
    LBase "v list" "e list"
    | LRec "v list" nat "e list" Lholed "e list"

end

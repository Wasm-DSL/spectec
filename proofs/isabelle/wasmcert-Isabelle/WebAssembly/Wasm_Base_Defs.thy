section \<open> WebAssembly Base Definitions \<close>

theory Wasm_Base_Defs
  imports
    Wasm_Ast
    Wasm_Subtyping
    Wasm_Type_Abs
    Wasm_Type_Word
    Word_Lib.Rsplit
    "../libs/More_More_Word"
begin

instantiation i32 :: wasm_base begin
lift_definition zero_i32 :: i32 is "of_nat 0" .
instance ..
end

instantiation i32 :: len begin
definition len_of_i32 :: "i32 itself \<Rightarrow> nat" where [simp]: "len_of_i32 _ = 32"
instance apply standard unfolding len_of_i32_def by simp
end

instantiation i64 :: wasm_base begin
lift_definition zero_i64 :: i64 is "of_nat 0" .
instance ..
end

instantiation i64 :: len begin
definition len_of_i64 :: "i64 itself \<Rightarrow> nat" where [simp]: "len_of_i64 _ = 64"
instance apply standard unfolding len_of_i32_def by simp
end

interpretation I32: Wasm_Int_Word Rep_i32 Abs_i32
  apply standard unfolding zero_i32_def using Rep_i32_inverse Abs_i32_inverse by auto

interpretation I64: Wasm_Int_Word Rep_i64 Abs_i64
  apply standard unfolding zero_i64_def using Rep_i64_inverse Abs_i64_inverse by auto

instantiation i32 :: wasm_int begin
  lift_definition int_clz_i32 :: "i32 \<Rightarrow> i32" is "I32.int_clz" .
  lift_definition int_ctz_i32 :: "i32 \<Rightarrow> i32" is "I32.int_ctz" .
  lift_definition int_popcnt_i32 :: "i32 \<Rightarrow> i32" is "I32.int_popcnt" .
  lift_definition int_add_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_add" .
  lift_definition int_sub_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_sub" .
  lift_definition int_mul_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_mul" .
  lift_definition int_div_u_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32 option" is "I32.int_div_u" .
  lift_definition int_div_s_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32 option" is "I32.int_div_s" .
  lift_definition int_rem_u_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32 option" is "I32.int_rem_u" .
  lift_definition int_rem_s_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32 option" is "I32.int_rem_s".
  lift_definition int_and_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_and" .
  lift_definition int_or_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_or" .
  lift_definition int_xor_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_xor" .
  lift_definition int_shl_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_shl" .
  lift_definition int_shr_u_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_shr_u" .
  lift_definition int_shr_s_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_shr_s" .
  lift_definition int_rotl_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_rotl" .
  lift_definition int_rotr_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_rotr" .
  lift_definition int_eqz_i32 :: "i32 \<Rightarrow> bool" is "I32.int_eqz" .
  lift_definition int_eq_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_eq" .
  lift_definition int_lt_u_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_lt_u" .
  lift_definition int_lt_s_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_lt_s" .
  lift_definition int_gt_u_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_gt_u" .
  lift_definition int_gt_s_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_gt_s" .
  lift_definition int_le_u_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_le_u" .
  lift_definition int_le_s_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_le_s" .
  lift_definition int_ge_u_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_ge_u" .
  lift_definition int_ge_s_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_ge_s" .
  lift_definition nat_of_int_i32 :: "i32 \<Rightarrow> nat" is unat .
  lift_definition int_of_nat_i32 :: "nat \<Rightarrow> i32" is of_nat .
instance
  apply (rule Wasm_Type_Abs.wasm_int.intro_of_class)
  apply (unfold int_clz_i32_def int_ctz_i32_def int_popcnt_i32_def int_add_i32_def int_sub_i32_def
  int_mul_i32_def int_div_u_i32_def int_div_s_i32_def int_rem_u_i32_def int_rem_s_i32_def
  int_and_i32_def int_or_i32_def int_xor_i32_def int_shl_i32_def int_shr_u_i32_def int_shr_s_i32_def
  int_rotl_i32_def int_rotr_i32_def int_eqz_i32_def int_eq_i32_def int_lt_u_i32_def int_lt_s_i32_def
  int_gt_u_i32_def int_gt_s_i32_def int_le_u_i32_def int_le_s_i32_def int_ge_u_i32_def
  int_ge_s_i32_def nat_of_int_i32_def int_of_nat_i32_def)
  by (rule I32.Int.wasm_int_axioms[unfolded I32.nat_of_int_def I32.int_of_nat_def])
end

instantiation i64 :: wasm_int begin
  lift_definition int_clz_i64 :: "i64 \<Rightarrow> i64" is "I64.int_clz" .
  lift_definition int_ctz_i64 :: "i64 \<Rightarrow> i64" is "I64.int_ctz" .
  lift_definition int_popcnt_i64 :: "i64 \<Rightarrow> i64" is "I64.int_popcnt" .
  lift_definition int_add_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> i64" is "I64.int_add" .
  lift_definition int_sub_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> i64" is "I64.int_sub" .
  lift_definition int_mul_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> i64" is "I64.int_mul" .
  lift_definition int_div_u_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> i64 option" is "I64.int_div_u" .
  lift_definition int_div_s_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> i64 option" is "I64.int_div_s" .
  lift_definition int_rem_u_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> i64 option" is "I64.int_rem_u" .
  lift_definition int_rem_s_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> i64 option" is "I64.int_rem_s".
  lift_definition int_and_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> i64" is "I64.int_and" .
  lift_definition int_or_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> i64" is "I64.int_or" .
  lift_definition int_xor_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> i64" is "I64.int_xor" .
  lift_definition int_shl_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> i64" is "I64.int_shl" .
  lift_definition int_shr_u_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> i64" is "I64.int_shr_u" .
  lift_definition int_shr_s_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> i64" is "I64.int_shr_s" .
  lift_definition int_rotl_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> i64" is "I64.int_rotl" .
  lift_definition int_rotr_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> i64" is "I64.int_rotr" .
  lift_definition int_eqz_i64 :: "i64 \<Rightarrow> bool" is "I64.int_eqz" .
  lift_definition int_eq_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> bool" is "I64.int_eq" .
  lift_definition int_lt_u_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> bool" is "I64.int_lt_u" .
  lift_definition int_lt_s_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> bool" is "I64.int_lt_s" .
  lift_definition int_gt_u_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> bool" is "I64.int_gt_u" .
  lift_definition int_gt_s_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> bool" is "I64.int_gt_s" .
  lift_definition int_le_u_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> bool" is "I64.int_le_u" .
  lift_definition int_le_s_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> bool" is "I64.int_le_s" .
  lift_definition int_ge_u_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> bool" is "I64.int_ge_u" .
  lift_definition int_ge_s_i64 :: "i64 \<Rightarrow> i64 \<Rightarrow> bool" is "I64.int_ge_s" .
  lift_definition nat_of_int_i64 :: "i64 \<Rightarrow> nat" is unat .
  lift_definition int_of_nat_i64 :: "nat \<Rightarrow> i64" is of_nat .
instance
  apply (rule Wasm_Type_Abs.wasm_int.intro_of_class)
  apply (unfold int_clz_i64_def int_ctz_i64_def int_popcnt_i64_def int_add_i64_def int_sub_i64_def
  int_mul_i64_def int_div_u_i64_def int_div_s_i64_def int_rem_u_i64_def int_rem_s_i64_def
  int_and_i64_def int_or_i64_def int_xor_i64_def int_shl_i64_def int_shr_u_i64_def int_shr_s_i64_def
  int_rotl_i64_def int_rotr_i64_def int_eqz_i64_def int_eq_i64_def int_lt_u_i64_def int_lt_s_i64_def
  int_gt_u_i64_def int_gt_s_i64_def int_le_u_i64_def int_le_s_i64_def int_ge_u_i64_def
  int_ge_s_i64_def nat_of_int_i64_def int_of_nat_i64_def)
  by (rule I64.Int.wasm_int_axioms[unfolded I64.nat_of_int_def I64.int_of_nat_def])
end

instantiation f32 :: wasm_float begin instance .. end
instantiation f64 :: wasm_float begin instance .. end

instantiation v128 :: wasm_base begin instance .. end

consts
  binop_vec_wf :: "binop_vec \<Rightarrow> bool"

  app_unop_vec_v :: "unop_vec \<Rightarrow> v128 \<Rightarrow> v128"
  app_binop_vec_v :: "binop_vec \<Rightarrow> v128 \<Rightarrow> v128 \<Rightarrow> v128 option"
  app_shuffle_vec_v :: "i list \<Rightarrow> v128 \<Rightarrow> v128 \<Rightarrow> v128"
  app_ternop_vec_v :: "ternop_vec \<Rightarrow> v128 \<Rightarrow> v128 \<Rightarrow> v128 \<Rightarrow> v128"
  app_test_vec_v :: "testop_vec \<Rightarrow> v128 \<Rightarrow> i32"
  app_shift_vec_v :: "shiftop_vec \<Rightarrow> v128 \<Rightarrow> i32 \<Rightarrow> v128"

consts
  ui32_trunc_f32 :: "f32 \<Rightarrow> i32 option"
  si32_trunc_f32 :: "f32 \<Rightarrow> i32 option"
  ui32_trunc_f64 :: "f64 \<Rightarrow> i32 option"
  si32_trunc_f64 :: "f64 \<Rightarrow> i32 option"
  ui64_trunc_f32 :: "f32 \<Rightarrow> i64 option"
  si64_trunc_f32 :: "f32 \<Rightarrow> i64 option"
  ui64_trunc_f64 :: "f64 \<Rightarrow> i64 option"
  si64_trunc_f64 :: "f64 \<Rightarrow> i64 option"
  ui32_trunc_sat_f32 :: "f32 \<Rightarrow> i32"
  si32_trunc_sat_f32 :: "f32 \<Rightarrow> i32"
  ui32_trunc_sat_f64 :: "f64 \<Rightarrow> i32"
  si32_trunc_sat_f64 :: "f64 \<Rightarrow> i32"
  ui64_trunc_sat_f32 :: "f32 \<Rightarrow> i64"
  si64_trunc_sat_f32 :: "f32 \<Rightarrow> i64"
  ui64_trunc_sat_f64 :: "f64 \<Rightarrow> i64"
  si64_trunc_sat_f64 :: "f64 \<Rightarrow> i64"
  f32_convert_ui32 :: "i32 \<Rightarrow> f32"
  f32_convert_si32 :: "i32 \<Rightarrow> f32"
  f32_convert_ui64 :: "i64 \<Rightarrow> f32"
  f32_convert_si64 :: "i64 \<Rightarrow> f32"
  f64_convert_ui32 :: "i32 \<Rightarrow> f64"
  f64_convert_si32 :: "i32 \<Rightarrow> f64"
  f64_convert_ui64 :: "i64 \<Rightarrow> f64"
  f64_convert_si64 :: "i64 \<Rightarrow> f64"
  wasm_demote :: "f64 \<Rightarrow> f32"
  wasm_promote :: "f32 \<Rightarrow> f64"
  serialise_f32 :: "f32 \<Rightarrow> bytes"
  serialise_f64 :: "f64 \<Rightarrow> bytes"
  deserialise_f32 :: "bytes \<Rightarrow> f32"
  deserialise_f64 :: "bytes \<Rightarrow> f64"
  serialise_v128 :: "v128 \<Rightarrow> bytes"
  deserialise_v128 :: "bytes \<Rightarrow> v128"

specification (serialise_f32) serialise_f32_len: "serialise_f32 x = bs \<Longrightarrow> length bs = 4" apply (rule exI[where x="\<lambda>_. replicate 4 undefined"]) by auto
specification (serialise_f64) serialise_f64_len: "serialise_f64 x = bs \<Longrightarrow> length bs = 8" apply (rule exI[where x="\<lambda>_. replicate 8 undefined"]) by auto
specification (serialise_v128) serialise_v128_len: "serialise_v128 x = bs \<Longrightarrow> length bs = 16" apply (rule exI[where x="\<lambda>_. replicate 16 undefined"]) by auto
  
lift_definition wasm_wrap :: "i64 \<Rightarrow> i32" is "Word.ucast" .
lift_definition wasm_extend_u :: "i32 \<Rightarrow> i64" is "Word.ucast" .
lift_definition wasm_extend_s :: "i32 \<Rightarrow> i64" is "Word.scast" .

lift_definition serialise_i32 :: "i32 \<Rightarrow> bytes" is "(map Abs_uint8')\<circ>word_rsplit_rev" .
lift_definition serialise_i64 :: "i64 \<Rightarrow> bytes" is "(map Abs_uint8')\<circ>word_rsplit_rev" .

lift_definition deserialise_i32 :: "bytes \<Rightarrow> i32" is "word_rcat_rev\<circ>(map Rep_uint8')" .
lift_definition deserialise_i64 :: "bytes \<Rightarrow> i64" is "word_rcat_rev\<circ>(map Rep_uint8')" .

lift_definition wasm_bool :: "bool \<Rightarrow> i32" is "(\<lambda>b. if b then 1 else 0)" .
lift_definition  int32_minus_one :: i32 is "max_word" .

definition mem_size :: "mem \<Rightarrow> nat" where
  "mem_size m = (mem_length m) div Ki64"

abbreviation "mem_agree m \<equiv> l_min (fst m) * Ki64 = mem_length m \<and> pred_option ((\<le>) (mem_size m)) (mem_max m)"

definition mem_grow :: "mem \<Rightarrow> nat \<Rightarrow> mem option" where
  "mem_grow m n = (let len = (mem_size m) + n in
                   if (len \<le> 2^16 \<and> pred_option (\<lambda>max. len \<le> max) (mem_max m))
                    then Some (mem_append m (n * Ki64) zero_byte)
                    else None)"

definition load :: "mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> nat \<Rightarrow> bytes option" where
  "load m n off l = (if (mem_length m \<ge> (n+off+l))
                       then Some (read_bytes m (n+off) l)
                       else None)"

definition sign_extend :: "sx \<Rightarrow> nat \<Rightarrow> bytes \<Rightarrow> bytes" where
  "sign_extend sx l bytes = (let msb = msb_byte (msbyte bytes) in
                          let byte = (case sx of
                                        U \<Rightarrow> zero_byte
                                      | S \<Rightarrow> if msb then negone_byte else zero_byte) in
                          bytes_takefill byte l bytes)"

definition load_packed :: "sx \<Rightarrow> mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bytes option" where
  "load_packed sx m n off lp l = map_option (sign_extend sx l) (load m n off lp)"

definition store :: "mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> bytes \<Rightarrow> nat \<Rightarrow> mem option" where
  "store m n off bs l = (if (mem_length m \<ge> (n+off+l))
                          then Some (write_bytes m (n+off) (bytes_takefill zero_byte l bs))
                          else None)"

definition store_packed :: "mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> bytes \<Rightarrow> nat \<Rightarrow> mem option" where
  "store_packed = store"

definition store_tab_list :: "tabinst \<Rightarrow> nat \<Rightarrow> v_ref list \<Rightarrow> tabinst option" where
  "store_tab_list tab n vrs = (if (tab_size tab \<ge> (n+(length vrs)))
                          then Some (fst tab, ((take n (snd tab)) @ vrs @ (drop (n + length vrs) (snd tab))))
                          else None)"

definition store_tab1 :: "tabinst \<Rightarrow> nat \<Rightarrow> v_ref \<Rightarrow> tabinst option" where
  "store_tab1 tab n vr = (if (n < tab_size tab)
                          then Some (fst tab, (take n (snd tab)) @ [vr] @ (drop (n + 1) (snd tab)))
                          else None)"

definition load_tabs1 :: "tabinst list \<Rightarrow> i \<Rightarrow> nat \<Rightarrow> v_ref option" where
  "load_tabs1 tables ti n = 
    (if (n < tab_size (tables!ti))
     then Some ((snd ((tables!ti)))!n)
     else None)"

definition store_tabs1 :: "tabinst list \<Rightarrow> i \<Rightarrow> nat \<Rightarrow> v_ref \<Rightarrow> (tabinst list) option" where
  "store_tabs1 tables ti n vr = 
    (case (store_tab1 (tables!ti) n vr) of
        Some tab' \<Rightarrow> Some ((take ti tables) @ [tab'] @ (drop (ti+1) tables))
      | None \<Rightarrow> None)"

definition grow_tab :: "tabinst \<Rightarrow> nat \<Rightarrow> v_ref \<Rightarrow> tabinst option" where
  "grow_tab t n vr = (let len = (tab_size t) + n;
                          old_limits = tab_t_lim (fst t);
                          limits' = old_limits\<lparr>l_min:= len\<rparr>
                       in
                   if (len < 2^32 \<and> pred_option (\<lambda>max. len \<le> max) (tab_max t))
                    then Some ((T_tab limits' (tab_t_reftype (fst t))), snd t @ (replicate n vr))
                    else None)"

consts
  host_func_apply :: "s \<Rightarrow> tf \<Rightarrow> host_func \<Rightarrow> v list \<Rightarrow> host_state \<Rightarrow> (s \<times> v list) option \<Rightarrow> bool"

definition wasm_deserialise_num :: "bytes \<Rightarrow> t_num \<Rightarrow> v_num" where
  "wasm_deserialise_num bs t = (case t of
                                  T_i32 \<Rightarrow> ConstInt32 (deserialise_i32 bs)
                                | T_i64 \<Rightarrow> ConstInt64 (deserialise_i64 bs)
                                | T_f32 \<Rightarrow> ConstFloat32 (deserialise_f32 bs)
                                | T_f64 \<Rightarrow> ConstFloat64 (deserialise_f64 bs))"

definition wasm_deserialise :: "bytes \<Rightarrow> t \<Rightarrow> v" where
  "wasm_deserialise bs t = (case t of
                              T_num t_n \<Rightarrow> V_num (wasm_deserialise_num bs t_n)
                            | T_vec t_v \<Rightarrow> V_vec (ConstVec128 (deserialise_v128 bs)))"

definition bits_num :: "v_num \<Rightarrow> bytes" where
  "bits_num v = (case v of
                   ConstInt32 c \<Rightarrow> (serialise_i32 c)
                 | ConstInt64 c \<Rightarrow> (serialise_i64 c)
                 | ConstFloat32 c \<Rightarrow> (serialise_f32 c)
                 | ConstFloat64 c \<Rightarrow> (serialise_f64 c))"

definition bits_vec :: "v_vec \<Rightarrow> bytes" where
  "bits_vec v = (case v of
                   ConstVec128 c \<Rightarrow> (serialise_v128 c))"



definition bits :: "v \<Rightarrow> bytes" where
  "bits v = (case v of
               V_num v_n \<Rightarrow> bits_num v_n
             | V_vec v_v \<Rightarrow> bits_vec v_v)"

definition bitzero_num :: "t_num \<Rightarrow> v_num" where
  "bitzero_num t = (case t of
                      T_i32 \<Rightarrow> ConstInt32 0
                    | T_i64 \<Rightarrow> ConstInt64 0
                    | T_f32 \<Rightarrow> ConstFloat32 0
                    | T_f64 \<Rightarrow> ConstFloat64 0)"

definition bitzero_vec :: "t_vec \<Rightarrow> v_vec" where
  "bitzero_vec t = (case t of
                      T_v128 \<Rightarrow> ConstVec128 0)"

definition bitzero_ref :: "t_ref \<Rightarrow> v_ref" where
  "bitzero_ref t = (case t of
                      T_func_ref \<Rightarrow> ConstNull (T_func_ref)
                    | T_ext_ref \<Rightarrow> ConstNull (T_ext_ref)
                    
)"

definition bitzero :: "t \<Rightarrow> v option" where
  "bitzero t = (case t of
                 T_num t_n \<Rightarrow> Some (V_num (bitzero_num t_n))
               | T_vec t_v \<Rightarrow> Some (V_vec (bitzero_vec t_v))
               | T_ref t_r \<Rightarrow> Some (V_ref (bitzero_ref t_r))
               | T_bot \<Rightarrow> None)"

definition n_zeros :: "t list \<Rightarrow> (v list) option" where
  "n_zeros ts = those (map bitzero ts)"

definition typeof_num :: "v_num \<Rightarrow> t_num" where
  "typeof_num v = (case v of
                     ConstInt32 _ \<Rightarrow> T_i32
                   | ConstInt64 _ \<Rightarrow> T_i64
                   | ConstFloat32 _ \<Rightarrow> T_f32
                   | ConstFloat64 _ \<Rightarrow> T_f64)"

definition typeof_vec :: "v_vec \<Rightarrow> t_vec" where
  "typeof_vec v = (case v of ConstVec128 _ \<Rightarrow> T_v128)"

definition typeof_ref :: "v_ref \<Rightarrow> t_ref" where
  "typeof_ref v = (case v of
                     ConstRefFunc _ \<Rightarrow> T_func_ref
                   | ConstRefExtern _ \<Rightarrow> T_ext_ref
                   | ConstNull t_ref \<Rightarrow> t_ref)"

definition is_null_ref :: "v_ref \<Rightarrow> bool" where
  "is_null_ref v = (case v of
                     ConstNull t_ref \<Rightarrow> True
                   | _ \<Rightarrow> False)"

definition typeof :: "v \<Rightarrow> t" where
  "typeof v = (case v of
                 V_num v_n \<Rightarrow> T_num (typeof_num v_n)
               | V_vec v_v \<Rightarrow> T_vec (typeof_vec v_v)
               | V_ref v_r \<Rightarrow> T_ref (typeof_ref v_r))"

definition is_num_type :: "t \<Rightarrow> bool" where
  "is_num_type t = (case t of
                      T_num _ \<Rightarrow> True
                    | _ \<Rightarrow> False)"

definition is_vec_type :: "t \<Rightarrow> bool" where
  "is_vec_type t = (case t of
                      T_vec _ \<Rightarrow> True
                    | _ \<Rightarrow> False)"

definition is_ref_type :: "t \<Rightarrow> bool" where
  "is_ref_type t = (case t of
                      T_ref _ \<Rightarrow> True
                    | _ \<Rightarrow> False)"

definition vec_lane_t :: "shape_vec \<Rightarrow> t_num" where
  "vec_lane_t sv = (case sv of
                      Svi I8_16 \<Rightarrow> T_i32
                    | Svi I16_8 \<Rightarrow> T_i32
                    | Svi I32_4 \<Rightarrow> T_i32
                    | Svi I64_2 \<Rightarrow> T_i64
                    | Svf F32_4 \<Rightarrow> T_f32
                    | Svf F64_2 \<Rightarrow> T_f64)"

definition vec_i_length :: "shape_vec_i \<Rightarrow> nat" where
  "vec_i_length sv = (case sv of
                       I8_16 \<Rightarrow> 1
                     | I16_8 \<Rightarrow> 2
                     | I32_4 \<Rightarrow> 4
                     | I64_2 \<Rightarrow> 8)"

definition vec_f_length :: "shape_vec_f \<Rightarrow> nat" where
  "vec_f_length sv = (case sv of
                       F32_4 \<Rightarrow> 4
                     | F64_2 \<Rightarrow> 8)"

definition vec_length :: "shape_vec \<Rightarrow> nat" where
  "vec_length sv = (case sv of
                     Svi svi \<Rightarrow> vec_i_length svi
                   | Svf svf \<Rightarrow> vec_f_length svf)"

definition vec_i_num :: "shape_vec_i \<Rightarrow> nat" where
  "vec_i_num sv = (case sv of
                   I8_16 \<Rightarrow> 16
                 | I16_8 \<Rightarrow> 8
                 | I32_4 \<Rightarrow> 4
                 | I64_2 \<Rightarrow> 2)"

definition vec_f_num :: "shape_vec_f \<Rightarrow> nat" where
  "vec_f_num sv = (case sv of
                   F32_4 \<Rightarrow> 4
                 | F64_2 \<Rightarrow> 2)"

definition vec_num :: "shape_vec \<Rightarrow> nat" where
  "vec_num sv = (case sv of
                   Svi svi \<Rightarrow> vec_i_num svi
                 | Svf svf \<Rightarrow> vec_f_num svf)"

definition option_projl :: "('a \<times> 'b) option \<Rightarrow> 'a option" where
  "option_projl x = map_option fst x"

definition option_projr :: "('a \<times> 'b) option \<Rightarrow> 'b option" where
  "option_projr x = map_option snd x"

definition t_num_length :: "t_num \<Rightarrow> nat" where
 "t_num_length t = (case t of
                      T_i32 \<Rightarrow> 4
                    | T_i64 \<Rightarrow> 8
                    | T_f32 \<Rightarrow> 4
                    | T_f64 \<Rightarrow> 8)"

definition t_vec_length :: "t_vec \<Rightarrow> nat" where
 "t_vec_length t = (case t of
                      T_v128 \<Rightarrow> 16)"

definition t_length :: "t \<Rightarrow> nat" where
 "t_length t = (case t of
                  T_num t_n \<Rightarrow> t_num_length t_n
                | T_vec t_v \<Rightarrow> t_vec_length t_v)"

definition tp_num_length :: "tp_num \<Rightarrow> nat" where
 "tp_num_length tp = (case tp of
                       Tp_i8 \<Rightarrow> 1
                     | Tp_i16 \<Rightarrow> 2
                     | Tp_i32 \<Rightarrow> 4)"

definition tp_vec_length :: "tp_vec \<Rightarrow> nat" where
 "tp_vec_length tp = (case tp of
                       Tp_v8_8 \<Rightarrow> 1
                     | Tp_v16_4 \<Rightarrow> 2
                     | Tp_v32_2 \<Rightarrow> 4)"

definition tp_vec_num :: "tp_vec \<Rightarrow> nat" where
 "tp_vec_num tp = (case tp of
                     Tp_v8_8 \<Rightarrow> 8
                   | Tp_v16_4 \<Rightarrow> 4
                   | Tp_v32_2 \<Rightarrow> 2)"

definition is_int_t_num :: "t_num \<Rightarrow> bool" where
 "is_int_t_num t = (case t of
                      T_i32 \<Rightarrow> True
                    | T_i64 \<Rightarrow> True
                    | T_f32 \<Rightarrow> False
                    | T_f64 \<Rightarrow> False)"

definition is_float_t_num :: "t_num \<Rightarrow> bool" where
 "is_float_t_num t = (case t of
                        T_i32 \<Rightarrow> False
                      | T_i64 \<Rightarrow> False
                      | T_f32 \<Rightarrow> True
                      | T_f64 \<Rightarrow> True)"

definition is_mut :: "tg \<Rightarrow> bool" where
  "is_mut tg = (tg_mut tg = T_mut)"

definition unop_t_num_agree :: "unop \<Rightarrow> t_num \<Rightarrow> bool" where
  "unop_t_num_agree unop t =
     (case unop of
        Unop_i _ \<Rightarrow> is_int_t_num t
      | Unop_f _ \<Rightarrow> is_float_t_num t
      | Extend_s tp \<Rightarrow> is_int_t_num t \<and> t_num_length t > tp_num_length tp)"

definition binop_t_num_agree :: "binop \<Rightarrow> t_num \<Rightarrow> bool" where
  "binop_t_num_agree binop t =
     (case binop of
        Binop_i _ \<Rightarrow> is_int_t_num t
      | Binop_f _ \<Rightarrow> is_float_t_num t)"

definition relop_t_num_agree :: "relop \<Rightarrow> t_num \<Rightarrow> bool" where
  "relop_t_num_agree relop t =
     (case relop of
        Relop_i _ \<Rightarrow> is_int_t_num t
      | Relop_f _ \<Rightarrow> is_float_t_num t)"

definition app_unop_i :: "unop_i \<Rightarrow> 'i::wasm_int \<Rightarrow> 'i::wasm_int" where
  "app_unop_i iop c =
     (case iop of
     Ctz \<Rightarrow> int_ctz c
   | Clz \<Rightarrow> int_clz c
   | Popcnt \<Rightarrow> int_popcnt c)"

definition app_unop_i_v :: "unop_i \<Rightarrow> v_num \<Rightarrow> v_num" where
  "app_unop_i_v iop v =
    (case v of
       (ConstInt32 c) \<Rightarrow> ConstInt32 (app_unop_i iop c)
     | (ConstInt64 c) \<Rightarrow> ConstInt64 (app_unop_i iop c)
     | v' \<Rightarrow> v')"

definition app_unop_f :: "unop_f \<Rightarrow> 'f::wasm_float \<Rightarrow> 'f::wasm_float" where
  "app_unop_f fop c =
                 (case fop of
                    Neg \<Rightarrow> float_neg c
                  | Abs \<Rightarrow> float_abs c
                  | Ceil \<Rightarrow> float_ceil c
                  | Floor \<Rightarrow> float_floor c
                  | Trunc \<Rightarrow> float_trunc c
                  | Nearest \<Rightarrow> float_nearest c
                  | Sqrt \<Rightarrow> float_sqrt c)"

definition app_unop_f_v :: "unop_f \<Rightarrow> v_num \<Rightarrow> v_num" where
  "app_unop_f_v fop v =
    (case v of
       (ConstFloat32 c) \<Rightarrow> ConstFloat32 (app_unop_f fop c)
     | (ConstFloat64 c) \<Rightarrow> ConstFloat64 (app_unop_f fop c)
     | v' \<Rightarrow> v')"

definition app_extend_s :: "tp_num \<Rightarrow> v_num \<Rightarrow> v_num" where
  "app_extend_s tp v =
     wasm_deserialise_num (sign_extend S (t_num_length (typeof_num v)) (take (tp_num_length tp) (bits_num v))) (typeof_num v)"

definition app_unop :: "unop \<Rightarrow> v_num \<Rightarrow> v_num" where
  "app_unop uop v =
    (case uop of
       Unop_i iop \<Rightarrow> app_unop_i_v iop v
     | Unop_f fop \<Rightarrow> app_unop_f_v fop v
     | Extend_s tp \<Rightarrow> app_extend_s tp v)"

definition app_binop_i :: "binop_i \<Rightarrow> 'i::wasm_int \<Rightarrow> 'i::wasm_int \<Rightarrow> ('i::wasm_int) option" where
  "app_binop_i iop c1 c2 = (case iop of
                              Add \<Rightarrow> Some (int_add c1 c2)
                            | Sub \<Rightarrow> Some (int_sub c1 c2)
                            | Mul \<Rightarrow> Some (int_mul c1 c2)
                            | Div U \<Rightarrow> int_div_u c1 c2
                            | Div S \<Rightarrow> int_div_s c1 c2
                            | Rem U \<Rightarrow> int_rem_u c1 c2
                            | Rem S \<Rightarrow> int_rem_s c1 c2
                            | And \<Rightarrow> Some (int_and c1 c2)
                            | Or \<Rightarrow> Some (int_or c1 c2)
                            | Xor \<Rightarrow> Some (int_xor c1 c2)
                            | Shl \<Rightarrow> Some (int_shl c1 c2)
                            | Shr U \<Rightarrow> Some (int_shr_u c1 c2)
                            | Shr S \<Rightarrow> Some (int_shr_s c1 c2)
                            | Rotl \<Rightarrow> Some (int_rotl c1 c2)
                            | Rotr \<Rightarrow> Some (int_rotr c1 c2))"

definition app_binop_i_v :: "binop_i \<Rightarrow> v_num \<Rightarrow> v_num \<Rightarrow> v_num option" where
  "app_binop_i_v iop v1 v2 =
    (case (v1,v2) of
       ((ConstInt32 c1), (ConstInt32 c2)) \<Rightarrow> map_option ConstInt32 (app_binop_i iop c1 c2)
     | ((ConstInt64 c1), (ConstInt64 c2)) \<Rightarrow> map_option ConstInt64 (app_binop_i iop c1 c2)
     | _ \<Rightarrow> None)"

definition app_binop_f :: "binop_f \<Rightarrow> 'f::wasm_float \<Rightarrow> 'f::wasm_float \<Rightarrow> ('f::wasm_float) option" where
  "app_binop_f fop c1 c2 = (case fop of
                              Addf \<Rightarrow> Some (float_add c1 c2)
                            | Subf \<Rightarrow> Some (float_sub c1 c2)
                            | Mulf \<Rightarrow> Some (float_mul c1 c2)
                            | Divf \<Rightarrow> Some (float_div c1 c2)
                            | Min \<Rightarrow> Some (float_min c1 c2)
                            | Max \<Rightarrow> Some (float_max c1 c2)
                            | Copysign \<Rightarrow> Some (float_copysign c1 c2))"

definition app_binop_f_v :: "binop_f \<Rightarrow> v_num \<Rightarrow> v_num \<Rightarrow> v_num option" where
  "app_binop_f_v fop v1 v2 =
    (case (v1,v2) of
       ((ConstFloat32 c1), (ConstFloat32 c2)) \<Rightarrow> map_option ConstFloat32 (app_binop_f fop c1 c2)
     | ((ConstFloat64 c1), (ConstFloat64 c2)) \<Rightarrow> map_option ConstFloat64 (app_binop_f fop c1 c2)
     | _ \<Rightarrow> None)"

definition app_binop :: "binop \<Rightarrow> v_num \<Rightarrow> v_num \<Rightarrow> v_num option" where
  "app_binop bop v1 v2 =
    (case bop of
       Binop_i iop \<Rightarrow> app_binop_i_v iop v1 v2
     | Binop_f fop \<Rightarrow> app_binop_f_v fop v1 v2)"

definition app_testop_i :: "testop \<Rightarrow> 'i::wasm_int \<Rightarrow> bool" where
  "app_testop_i testop c = (case testop of Eqz \<Rightarrow> int_eqz c)"

definition app_testop :: "testop \<Rightarrow> v_num \<Rightarrow> v_num" where
  "app_testop op v =
    (case v of
       ConstInt32 c \<Rightarrow> ConstInt32 (wasm_bool (app_testop_i op c))
     | ConstInt64 c \<Rightarrow> ConstInt32 (wasm_bool (app_testop_i op c))
     | _ \<Rightarrow> ConstInt32 0)"


definition app_relop_i :: "relop_i \<Rightarrow> 'i::wasm_int \<Rightarrow> 'i::wasm_int \<Rightarrow> bool" where
  "app_relop_i rop c1 c2 = (case rop of
                              Eq \<Rightarrow> int_eq c1 c2
                            | Ne \<Rightarrow> int_ne c1 c2
                            | Lt U \<Rightarrow> int_lt_u c1 c2
                            | Lt S \<Rightarrow> int_lt_s c1 c2
                            | Gt U \<Rightarrow> int_gt_u c1 c2
                            | Gt S \<Rightarrow> int_gt_s c1 c2
                            | Le U \<Rightarrow> int_le_u c1 c2
                            | Le S \<Rightarrow> int_le_s c1 c2
                            | Ge U \<Rightarrow> int_ge_u c1 c2
                            | Ge S \<Rightarrow> int_ge_s c1 c2)"

definition app_relop_i_v :: "relop_i \<Rightarrow> v_num \<Rightarrow> v_num \<Rightarrow> v_num" where
  "app_relop_i_v iop v1 v2 =
    (case (v1,v2) of
       ((ConstInt32 c1), (ConstInt32 c2)) \<Rightarrow> ConstInt32 (wasm_bool (app_relop_i iop c1 c2))
     | ((ConstInt64 c1), (ConstInt64 c2)) \<Rightarrow> ConstInt32 (wasm_bool (app_relop_i iop c1 c2))
     | _ \<Rightarrow> ConstInt32 0)"

definition app_relop_f :: "relop_f \<Rightarrow> 'f::wasm_float \<Rightarrow> 'f::wasm_float \<Rightarrow> bool" where
  "app_relop_f rop c1 c2 = (case rop of
                              Eqf \<Rightarrow> float_eq c1 c2
                            | Nef \<Rightarrow> float_ne c1 c2
                            | Ltf \<Rightarrow> float_lt c1 c2
                            | Gtf \<Rightarrow> float_gt c1 c2
                            | Lef \<Rightarrow> float_le c1 c2
                            | Gef \<Rightarrow> float_ge c1 c2)"

definition app_relop_f_v :: "relop_f \<Rightarrow> v_num \<Rightarrow> v_num \<Rightarrow> v_num" where
  "app_relop_f_v fop v1 v2 =
    (case (v1,v2) of
       ((ConstFloat32 c1), (ConstFloat32 c2)) \<Rightarrow> ConstInt32 (wasm_bool (app_relop_f fop c1 c2))
     | ((ConstFloat64 c1), (ConstFloat64 c2)) \<Rightarrow> ConstInt32 (wasm_bool (app_relop_f fop c1 c2))
     | _ \<Rightarrow> ConstInt32 0)"

definition app_relop :: "relop \<Rightarrow> v_num \<Rightarrow> v_num \<Rightarrow> v_num" where
  "app_relop rop v1 v2 =
    (case rop of
       Relop_i iop \<Rightarrow> app_relop_i_v iop v1 v2
     | Relop_f fop \<Rightarrow> app_relop_f_v fop v1 v2)"

definition insert_lane_vec_bs :: "nat \<Rightarrow> i \<Rightarrow> bytes \<Rightarrow> bytes \<Rightarrow> bytes" where
  "insert_lane_vec_bs len_lane i bs_lane bs_vec =
     ((take (i * len_lane) bs_vec) @ (take len_lane bs_lane) @ (drop ((i+1) * len_lane) bs_vec))"

definition app_unop_vec :: "unop_vec \<Rightarrow> v_vec \<Rightarrow> v_vec" where
  "app_unop_vec uop v1 =
     (case v1 of ConstVec128 c \<Rightarrow> ConstVec128 (app_unop_vec_v uop c))"

definition app_binop_vec :: "binop_vec \<Rightarrow> v_vec \<Rightarrow> v_vec \<Rightarrow> v_vec option" where
  "app_binop_vec bop v1 v2 =
    (case (v1,v2) of (ConstVec128 c1,ConstVec128 c2) \<Rightarrow> map_option ConstVec128 (app_binop_vec_v bop c1 c2))"

definition app_shuffle_vec :: "i list \<Rightarrow> v_vec \<Rightarrow> v_vec \<Rightarrow> v_vec" where
  "app_shuffle_vec is v1 v2 =
     (case (v1,v2) of (ConstVec128 c1,ConstVec128 c2) \<Rightarrow> ConstVec128 (app_shuffle_vec_v is c1 c2))"

definition app_ternop_vec :: "ternop_vec \<Rightarrow> v_vec \<Rightarrow> v_vec \<Rightarrow> v_vec \<Rightarrow> v_vec" where
  "app_ternop_vec op v1 v2 v3 = 
     (case (v1,v2,v3) of (ConstVec128 c1,ConstVec128 c2,ConstVec128 c3) \<Rightarrow> ConstVec128 (app_ternop_vec_v op c1 c2 c3))"

definition app_test_vec :: "testop_vec \<Rightarrow> v_vec \<Rightarrow> i32" where
  "app_test_vec op v1 =
    (case v1 of ConstVec128 c \<Rightarrow> (app_test_vec_v op c))"

definition app_shift_vec :: "shiftop_vec \<Rightarrow> v_vec \<Rightarrow> i32 \<Rightarrow> v_vec" where
  "app_shift_vec sop v cn =
     (case v of ConstVec128 cv \<Rightarrow> ConstVec128 (app_shift_vec_v sop cv cn))"

definition app_splat_vec :: "shape_vec \<Rightarrow> v_num \<Rightarrow> v_vec" where
  "app_splat_vec sv v = ConstVec128 (deserialise_v128 ((\<lambda>bs. concat (replicate (vec_num sv) bs)) (take (vec_length sv) (bits_num v))))"

definition app_extract_vec :: "shape_vec \<Rightarrow> sx \<Rightarrow> i \<Rightarrow> v_vec \<Rightarrow> v_num" where
  "app_extract_vec sv sx i vv =
     (let bs_v = bits_vec vv in
      let len_lane = vec_length sv in
      let bs_n = (take len_lane (drop (i * len_lane) bs_v)) in
      case sv of
        Svi I8_16 \<Rightarrow> ConstInt32 (deserialise_i32 (sign_extend sx 4 bs_n))
      | Svi I16_8 \<Rightarrow> ConstInt32 (deserialise_i32 (sign_extend sx 4 bs_n))
      | Svi I32_4 \<Rightarrow> ConstInt32 (deserialise_i32 bs_n)
      | Svi I64_2 \<Rightarrow> ConstInt64 (deserialise_i64 bs_n)
      | Svf F32_4 \<Rightarrow> ConstFloat32 (deserialise_f32 bs_n)
      | Svf F64_2 \<Rightarrow> ConstFloat64 (deserialise_f64 bs_n))"

definition app_replace_vec :: "shape_vec \<Rightarrow> i \<Rightarrow> v_vec \<Rightarrow> v_num \<Rightarrow> v_vec" where
  "app_replace_vec sv i vv vn =
     (let bs_v = bits_vec vv in
      let bs_n = bits_num vn in
      ConstVec128 (deserialise_v128 (insert_lane_vec_bs (vec_length sv) i bs_n bs_v)))"

fun read_bytes_vec :: "nat \<Rightarrow> nat \<Rightarrow> sx \<Rightarrow> mem \<Rightarrow> nat \<Rightarrow> bytes" where
  "read_bytes_vec 0 len sx m ind = []"
| "read_bytes_vec (Suc n) len sx m ind = (sign_extend sx (len*2) (read_bytes m ind len)) @ (read_bytes_vec n len sx m (ind+len))"

definition load_packed_vec :: "tp_vec \<Rightarrow> sx \<Rightarrow> mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> bytes option" where
  "load_packed_vec tp sx m n off = (if (mem_length m \<ge> (n+off+((tp_vec_num tp)*(tp_vec_length tp))))
                                     then Some (read_bytes_vec (tp_vec_num tp) (tp_vec_length tp) sx m (n+off))
                                     else None)"

definition load_vec :: "loadop_vec \<Rightarrow> mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> bytes option" where
  "load_vec lvop m n off  = (case lvop of
                               Load_128 \<Rightarrow> load m n off (t_vec_length T_v128)
                             | Load_packed_vec tp sx \<Rightarrow> load_packed_vec tp sx m n off
                             | Load_32_zero \<Rightarrow> map_option (\<lambda>bs. bytes_takefill zero_byte (t_vec_length T_v128) bs) (load m n off 4)
                             | Load_64_zero \<Rightarrow> map_option (\<lambda>bs. bytes_takefill zero_byte (t_vec_length T_v128) bs) (load m n off 8)
                             | Load_splat svi \<Rightarrow> map_option (\<lambda>bs. concat (replicate (vec_i_num svi) bs)) (load m n off (vec_i_length svi)))"

definition insert_lane_vec :: "shape_vec_i \<Rightarrow> i \<Rightarrow> bytes \<Rightarrow> v128 \<Rightarrow> v128" where
  "insert_lane_vec svi i bs v =
     (let bs_v = (serialise_v128 v) in
     deserialise_v128 (insert_lane_vec_bs (vec_i_length svi) i bs bs_v))"

definition store_serialise_vec :: "storeop_vec \<Rightarrow> v128 \<Rightarrow> bytes" where
  "store_serialise_vec svop v = (case svop of
                                  Store_128 \<Rightarrow> serialise_v128 v
                                | Store_lane svi i \<Rightarrow> take (vec_i_length svi) (drop (i * (vec_i_length svi)) (serialise_v128 v)))"

definition cl_type :: "cl \<Rightarrow> tf" where
  "cl_type cl = (case cl of Func_native _ tf _ _ \<Rightarrow> tf | Func_host tf _ \<Rightarrow> tf)"

definition tb_tf :: "inst \<Rightarrow> tb \<Rightarrow> tf" where
  "tb_tf inst tb = (case tb of
                      Tbf i \<Rightarrow> (inst.types inst)!i
                    | Tbv (Some t) \<Rightarrow> ([] _> [t])
                    | Tbv None \<Rightarrow> ([] _> []))"

definition tb_tf_t :: "t_context \<Rightarrow> tb \<Rightarrow> tf option" where
  "tb_tf_t \<C> tb = (case tb of
                      Tbf i \<Rightarrow> let tfs = (types_t \<C>) in
                               if i < length tfs then Some (tfs!i) else None
                    | Tbv (Some t) \<Rightarrow> Some ([] _> [t])
                    | Tbv None \<Rightarrow> Some ([] _> []))"

definition rglob_is_mut :: "global \<Rightarrow> bool" where
  "rglob_is_mut g = (g_mut g = T_mut)"

definition stypes :: "inst \<Rightarrow> nat \<Rightarrow> tf" where
  "stypes i j = ((types i)!j)"

definition sfunc_ind :: "inst \<Rightarrow> nat \<Rightarrow> nat" where
  "sfunc_ind i j = ((inst.funcs i)!j)"

definition sfunc :: "s \<Rightarrow> inst \<Rightarrow> nat \<Rightarrow> cl" where
  "sfunc s i j = (funcs s)!(sfunc_ind i j)"

definition sglob_ind :: "inst \<Rightarrow> nat \<Rightarrow> nat" where
  "sglob_ind i j = ((inst.globs i)!j)"

definition sglob :: "s \<Rightarrow> inst \<Rightarrow> nat \<Rightarrow> global" where
  "sglob s i j = (globs s)!(sglob_ind i j)"

definition sglob_val :: "s \<Rightarrow> inst \<Rightarrow> nat \<Rightarrow> v" where
  "sglob_val s i j = g_val (sglob s i j)"

definition smem_ind :: "inst \<Rightarrow> nat option" where
  "smem_ind i = (case (inst.mems i) of (n#_) \<Rightarrow> Some n | [] \<Rightarrow> None)"

definition tab_cl_ind :: "tabinst list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> v_ref option" where
  "tab_cl_ind st i j = (let stabinst = snd (st!i) in
                       (if ((length stabinst) > j) then Some (stabinst!j)
                        else None))"

definition is_some_const_ref_func :: "v_ref option \<Rightarrow> bool" where
  "is_some_const_ref_func x = (case x of
    Some (ConstRefFunc i) \<Rightarrow> True
  | _ \<Rightarrow> False
)"

definition stab_cl_ind :: "s \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> v_ref option" where
  "stab_cl_ind s i j = tab_cl_ind (tabs s) i j"

definition stab:: "s \<Rightarrow> inst \<Rightarrow> i \<Rightarrow> nat \<Rightarrow> v_ref option" where
  "stab s i ti j = (if ti < length (inst.tabs i) then stab_cl_ind s ((inst.tabs i)!ti) j
                        else None)"

definition stab_ind :: "inst \<Rightarrow> i \<Rightarrow> nat option" where
  "stab_ind i ti = (if ti < length (inst.tabs i) then Some ((inst.tabs i)!ti)
                        else None)"

definition update_glob :: "global list \<Rightarrow> inst \<Rightarrow> nat \<Rightarrow> v \<Rightarrow> global list" where
  "update_glob gs i j v =  (let k = sglob_ind i j in gs[k:=(gs!k)\<lparr>g_val := v\<rparr>])"

definition supdate_glob :: "s \<Rightarrow> inst \<Rightarrow> nat \<Rightarrow> v \<Rightarrow> s" where
  "supdate_glob s i j v = s\<lparr>globs := (update_glob (globs s) i j v)\<rparr>"

definition is_const :: "e \<Rightarrow> bool" where
  "is_const e = (case e of Basic (EConstNum _) \<Rightarrow> True
                         | Basic (EConstVec _) \<Rightarrow> True
                         | Ref _ \<Rightarrow> True
                         | _ \<Rightarrow> False)"

definition const_list :: "e list \<Rightarrow> bool" where
  "const_list xs = list_all is_const xs"

definition tab_extension :: "tabinst \<Rightarrow> tabinst \<Rightarrow> bool" where
  "tab_extension t1 t2 \<equiv> tab_size t1 \<le> tab_size t2 \<and>
                         tab_max t1 = tab_max t2 \<and>
                         tab_subtyping (fst t2) (fst t1)"

definition mem_extension :: "mem \<Rightarrow> mem \<Rightarrow> bool" where
  "mem_extension m1 m2 \<equiv> mem_size m1 \<le> mem_size m2 \<and>
                         (mem_max m1) = (mem_max m2) \<and>
                         mem_subtyping (fst m2) (fst m1)"

definition global_extension :: "global \<Rightarrow> global \<Rightarrow> bool" where
  "global_extension g1 g2 \<equiv> (g_mut g1 = g_mut g2) \<and> (typeof (g_val g1) = typeof (g_val g2)) \<and> (g_mut g1 = T_immut \<longrightarrow> g_val g1 = g_val g2)"

definition elem_extension :: "eleminst \<Rightarrow> eleminst \<Rightarrow> bool" where
  "elem_extension e1 e2 \<equiv> (fst e1 = fst e2 \<and> (snd e1 = snd e2 \<or> length (snd e2) = 0))"

definition data_extension :: "datainst \<Rightarrow> datainst \<Rightarrow> bool" where
  "data_extension d1 d2 \<equiv> (d1 = d2 \<or> length d2 = 0)"

inductive store_extension :: "s \<Rightarrow> s \<Rightarrow> bool" where
"\<lbrakk>fs = fs'; list_all2 tab_extension tclss tclss'; list_all2 mem_extension bss bss'; list_all2 global_extension gs gs'; list_all2 elem_extension es es'; list_all2 data_extension ds ds'\<rbrakk>
  \<Longrightarrow> store_extension \<lparr>s.funcs = fs, s.tabs = tclss, s.mems = bss, s.globs = gs, s.elems = es, s.datas = ds\<rparr>
                       \<lparr>s.funcs = fs'@fs'', s.tabs = tclss'@tclss'', s.mems = bss'@bss'', s.globs = gs'@gs'', s.elems = es'@es'', s.datas = ds'@dss''\<rparr>"

abbreviation to_e_list :: "b_e list \<Rightarrow> e list" ("$* _" 60) where
  "to_e_list b_es \<equiv> map Basic b_es"

definition v_to_e :: "v \<Rightarrow> e" ("$C _" 60) where
  "v_to_e ve \<equiv> (case ve of
    V_num x \<Rightarrow>  $ EConstNum x |
    V_vec v \<Rightarrow> $ EConstVec v |
    V_ref r \<Rightarrow> Ref r
)"

abbreviation v_to_e_list :: "v list \<Rightarrow> e list" ("$C* _" 60) where
  "v_to_e_list ves \<equiv> map (\<lambda>x. $C x) ves"

inductive Lfilled :: "nat \<Rightarrow> Lholed \<Rightarrow> e list \<Rightarrow> e list \<Rightarrow> bool" where
  L0:"\<lbrakk>lholed = (LBase vs es')\<rbrakk> \<Longrightarrow> Lfilled 0 lholed es (($C* vs) @ es @ es')"
| LN:"\<lbrakk>lholed = (LRec vs n es' l es''); Lfilled k l es lfilledk\<rbrakk> \<Longrightarrow> Lfilled (k+1) lholed es (($C* vs) @ [Label n es' lfilledk] @ es'')"

inductive Lfilled_exact :: "nat \<Rightarrow> Lholed \<Rightarrow> e list \<Rightarrow> e list \<Rightarrow> bool" where
  L0:"\<lbrakk>lholed = (LBase [] [])\<rbrakk> \<Longrightarrow> Lfilled_exact 0 lholed es es"
| LN:"\<lbrakk>lholed = (LRec vs n es' l es''); Lfilled_exact k l es lfilledk\<rbrakk> \<Longrightarrow> Lfilled_exact (k+1) lholed es (($C* vs) @ [Label n es' lfilledk] @ es'')"

definition load_store_t_bounds :: "a \<Rightarrow> tp_num option \<Rightarrow> t_num \<Rightarrow> bool" where
  "load_store_t_bounds a tp t = (case tp of
                                   None \<Rightarrow> 2^a \<le> t_num_length t
                                 | Some tp \<Rightarrow> 2^a \<le> tp_num_length tp \<and> tp_num_length tp < t_num_length t \<and>  is_int_t_num t)"

definition load_vec_t_bounds :: "loadop_vec \<Rightarrow> a \<Rightarrow> bool" where
  "load_vec_t_bounds lv a = (case lv of
                              Load_packed_vec tp sx \<Rightarrow> 2^a \<le> (tp_vec_length tp) * (tp_vec_num tp)
                            | Load_splat svi \<Rightarrow> 2^a \<le> (vec_i_length svi)
                            | _ \<Rightarrow> 2^a \<le> (t_vec_length T_v128))"

definition store_vec_t_bounds :: "storeop_vec \<Rightarrow> a \<Rightarrow> bool" where
  "store_vec_t_bounds sv a = (case sv of
                               Store_lane svi i \<Rightarrow> i < vec_i_num svi \<and> 2^a \<le> (vec_i_length svi)
                             | _ \<Rightarrow> 2^a \<le> (t_vec_length T_v128))"

definition cvt_i32 :: "(sat \<times> sx) option \<Rightarrow> v_num \<Rightarrow> i32 option" where
  "cvt_i32 sat_sx v = (case v of
                         ConstInt32 c \<Rightarrow> None
                       | ConstInt64 c \<Rightarrow> Some (wasm_wrap c)
                       | ConstFloat32 c \<Rightarrow> (case sat_sx of
                                              Some (Nonsat, U) \<Rightarrow> ui32_trunc_f32 c
                                            | Some (Nonsat, S) \<Rightarrow> si32_trunc_f32 c
                                            | Some (Sat, U) \<Rightarrow> Some (ui32_trunc_sat_f32 c)
                                            | Some (Sat, S) \<Rightarrow> Some (si32_trunc_sat_f32 c)
                                            | None \<Rightarrow> None)
                       | ConstFloat64 c \<Rightarrow> (case sat_sx of
                                              Some (Nonsat, U) \<Rightarrow> ui32_trunc_f64 c
                                            | Some (Nonsat, S) \<Rightarrow> si32_trunc_f64 c
                                            | Some (Sat, U) \<Rightarrow> Some (ui32_trunc_sat_f64 c)
                                            | Some (Sat, S) \<Rightarrow> Some (si32_trunc_sat_f64 c)
                                        | None \<Rightarrow> None))"

definition cvt_i64 :: "(sat \<times> sx) option \<Rightarrow> v_num \<Rightarrow> i64 option" where
  "cvt_i64 sat_sx v = (case v of
                         ConstInt32 c \<Rightarrow> (case sat_sx of
                                              Some (_, U) \<Rightarrow> Some (wasm_extend_u c)
                                            | Some (_, S) \<Rightarrow> Some (wasm_extend_s c)
                                            | None \<Rightarrow> None)
                       | ConstInt64 c \<Rightarrow> None
                       | ConstFloat32 c \<Rightarrow> (case sat_sx of
                                              Some (Nonsat, U) \<Rightarrow> ui64_trunc_f32 c
                                            | Some (Nonsat, S) \<Rightarrow> si64_trunc_f32 c
                                            | Some (Sat, U) \<Rightarrow> Some (ui64_trunc_sat_f32 c)
                                            | Some (Sat, S) \<Rightarrow> Some (si64_trunc_sat_f32 c)
                                            | None \<Rightarrow> None)
                       | ConstFloat64 c \<Rightarrow> (case sat_sx of
                                              Some (Nonsat, U) \<Rightarrow> ui64_trunc_f64 c
                                            | Some (Nonsat, S) \<Rightarrow> si64_trunc_f64 c
                                            | Some (Sat, U) \<Rightarrow> Some (ui64_trunc_sat_f64 c)
                                            | Some (Sat, S) \<Rightarrow> Some (si64_trunc_sat_f64 c)
                                            | None \<Rightarrow> None))"

definition cvt_f32 :: "(sat \<times> sx) option \<Rightarrow> v_num \<Rightarrow> f32 option" where
  "cvt_f32 sat_sx v = (case v of
                         ConstInt32 c \<Rightarrow> (case sat_sx of
                                            Some (_, U) \<Rightarrow> Some (f32_convert_ui32 c)
                                          | Some (_, S) \<Rightarrow> Some (f32_convert_si32 c)
                                          | _ \<Rightarrow> None)
                       | ConstInt64 c \<Rightarrow> (case sat_sx of
                                            Some (_, U) \<Rightarrow> Some (f32_convert_ui64 c)
                                          | Some (_, S) \<Rightarrow> Some (f32_convert_si64 c)
                                          | _ \<Rightarrow> None)
                       | ConstFloat32 c \<Rightarrow> None
                       | ConstFloat64 c \<Rightarrow> Some (wasm_demote c))"

definition cvt_f64 :: "(sat \<times> sx) option \<Rightarrow> v_num \<Rightarrow> f64 option" where
  "cvt_f64 sat_sx v = (case v of
                         ConstInt32 c \<Rightarrow> (case sat_sx of
                                            Some (_, U) \<Rightarrow> Some (f64_convert_ui32 c)
                                          | Some (_, S) \<Rightarrow> Some (f64_convert_si32 c)
                                          | _ \<Rightarrow> None)
                       | ConstInt64 c \<Rightarrow> (case sat_sx of
                                            Some (_, U) \<Rightarrow> Some (f64_convert_ui64 c)
                                          | Some (_, S) \<Rightarrow> Some (f64_convert_si64 c)
                                          | _ \<Rightarrow> None)
                       | ConstFloat32 c \<Rightarrow> Some (wasm_promote c)
                       | ConstFloat64 c \<Rightarrow> None)"

definition cvt :: "t_num \<Rightarrow> (sat \<times> sx) option \<Rightarrow> v_num \<Rightarrow> v_num option" where
  "cvt t sat_sx v = (case t of
                       T_i32 \<Rightarrow> (case (cvt_i32 sat_sx v) of Some c \<Rightarrow> Some (ConstInt32 c) | None \<Rightarrow> None)
                     | T_i64 \<Rightarrow> (case (cvt_i64 sat_sx v) of Some c \<Rightarrow> Some (ConstInt64 c) | None \<Rightarrow> None)
                     | T_f32 \<Rightarrow> (case (cvt_f32 sat_sx v) of Some c \<Rightarrow> Some (ConstFloat32 c) | None \<Rightarrow> None)
                     | T_f64 \<Rightarrow> (case (cvt_f64 sat_sx v) of Some c \<Rightarrow> Some (ConstFloat64 c) | None \<Rightarrow> None))"

definition wasm_reinterpret :: "t_num \<Rightarrow> v_num \<Rightarrow> v_num" where
  "wasm_reinterpret t v = (wasm_deserialise_num (bits_num v) t)"

lemma is_int_t_exists:
  assumes "is_int_t_num t"
  shows "t = T_i32 \<or> t = T_i64"
  using assms
  by (cases t) (auto simp add: is_int_t_num_def)

lemma is_float_t_exists:
  assumes "is_float_t_num t"
  shows "t = T_f32 \<or> t = T_f64"
  using assms
  by (cases t) (auto simp add: is_float_t_num_def)


lemma int_float_disjoint: "is_int_t_num t = -(is_float_t_num t)"
  by simp (metis is_float_t_num_def is_int_t_num_def t_num.exhaust t_num.simps(13-16))

lemma stab_unfold:
  assumes "stab s i ti j = Some (ConstRefFunc i_cl)"
  shows "\<exists>k. length (inst.tabs i) > ti \<and>
                     k =(inst.tabs i)!ti \<and>
                     length (snd ((tabs s)!k)) > j \<and>
                     (snd ((tabs s)!k))!j = (ConstRefFunc i_cl)"
  using assms
  unfolding stab_def stab_cl_ind_def tab_cl_ind_def
  by (simp add: Let_def split: list.splits if_splits option.splits)

lemma inj_basic: "inj Basic"
  by (meson e.inject(1) injI)

lemma inj_basic_econst: "inj (\<lambda>v. $C v)"
  by (simp add: inj_def v_to_e_def split: v.splits)

lemma to_e_list_1:"[$ a] = $* [a]"
  by simp

lemma to_e_list_2:"[$ a, $ b] = $* [a, b]"
  by simp

lemma to_e_list_3:"[$ a, $ b, $ c] = $* [a, b, c]"
  by simp

lemma Lfilled_exact_imp_Lfilled:
  assumes "Lfilled_exact n lholed es LI"
  shows "Lfilled n lholed es LI"
  using assms
proof (induction rule: Lfilled_exact.induct)
  case (L0 lholed es)
  thus ?case
    using const_list_def Lfilled.intros(1)
    by fastforce
next
  case (LN vs lholed n es' l es'' k es lfilledk)
  thus ?case
    using Lfilled.intros(2)
    by fastforce
qed

lemma Lfilled_exact_app_imp_exists_Lfilled:
  assumes "Lfilled_exact n lholed (($C* vs)@es) LI"
  shows "\<exists>lholed'. Lfilled n lholed' es LI"
  using assms
proof (induction "(($C* vs)@es)" LI rule: Lfilled_exact.induct)
  case (L0 lholed)
  thus ?case
    using Lfilled.intros(1)
    by force
next
  case (LN vs lholed n es' l es'' k lfilledk)
  thus ?case
    using Lfilled.intros(2)
    by fastforce
qed

lemma Lfilled_imp_exists_Lfilled_exact:
  assumes "Lfilled n lholed es LI"
  shows "\<exists>lholed' vs es_c. Lfilled_exact n lholed' (($C* vs)@es@es_c) LI"
  using assms Lfilled_exact.intros
  by (induction rule: Lfilled.induct) fastforce+

lemma bitzero_typeof:
  assumes "bitzero t = Some v"
  shows "typeof v = t"
proof(cases t)
  case (T_num x1)
  then show ?thesis using assms unfolding bitzero_def
    by (metis (mono_tags, lifting) bitzero_num_def option.sel t.simps(16) t_num.case(1) t_num.case(2) t_num.case(3) t_num.case(4) t_num.exhaust typeof_def typeof_num_def v.simps(10) v_num.case(2) v_num.case(3) v_num.case(4) v_num.simps(17))
next
  case (T_vec x2)
  then show ?thesis using assms unfolding bitzero_def typeof_def
    using typeof_vec_def bitzero_vec_def
    by (metis (mono_tags, lifting) option.sel t.simps(17) t_vec.exhaust v.simps(11))
next
  case (T_ref x3)
  then show ?thesis using bitzero_def assms
    by (metis (mono_tags, lifting) bitzero_ref_def option.sel t.simps(18) t_ref.exhaust t_ref.simps(3) t_ref.simps(4) typeof_def typeof_ref_def v.simps(12) v_ref.simps(10))
next
  case T_bot
  then show ?thesis using bitzero_def assms by fastforce
qed

lemma n_zeros_typeof:
  "n_zeros ts = Some vs  \<Longrightarrow> (ts = map typeof vs)"
proof (induction ts arbitrary: vs)
  case Nil
  thus ?case
    unfolding n_zeros_def
    by simp
next
  case (Cons t ts)
  then obtain vs' where "n_zeros ts = Some vs'"
    using n_zeros_def those.simps bitzero_def
    by auto (simp split: option.splits t.splits)
  moreover
  obtain v' where "bitzero t = Some v'" "typeof v' = t"
    using Cons n_zeros_def bitzero_def bitzero_typeof
    by (simp split: option.splits t.splits)   
  ultimately
  show ?case
    using Cons
    unfolding n_zeros_def
    by auto
qed

end

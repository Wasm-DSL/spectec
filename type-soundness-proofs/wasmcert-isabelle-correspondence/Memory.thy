(* Memory: loads and stores of numbers (plain and packed) in the reduction
   simulation.  Port of the load/store part of ../wasmcert-rocq/reduction.v.

   SpecTec's byte builtins [nbytes_] and [ibytes_] are axiomatised, and
   WasmCert-Isabelle's float and vector (de)serialisation is only specified up
   to its length; the locale [mem_bytes] relates them (see its comment).
   Integer serialisation is concrete in WasmCert, and its little-endian layout
   ([le_bytes]) and round trip are proved here.

   Premises left to the typing invariant: the address operand is a 32-bit
   value, the memory address is in the store, and, for packed accesses, the
   width is that of a valid packed load or store ([ext_width_ok]).  Stores
   also require the access to be in bounds: out of bounds, SpecTec may write
   partially where WasmCert traps ([Oob_store] in the Rocq bridge). *)
theory Memory
  imports Reduction
begin

section \<open>Little-endian byte encodings\<close>

(* The [k] low bytes of [x], least significant first.  The Rocq bridge's
   [Memdata.encode_int]. *)
definition le_bytes :: "nat \<Rightarrow> nat \<Rightarrow> Wasm_Ast.byte list" where
  "le_bytes k x = map (\<lambda>j. byte_of_nat (x div 2 ^ (8 * j))) [0..<k]"

lemma length_le_bytes[simp]: "length (le_bytes k x) = k"
  by (simp add: le_bytes_def)

lemma nth_le_bytes: "j < k \<Longrightarrow> le_bytes k x ! j = byte_of_nat (x div 2 ^ (8 * j))"
  by (simp add: le_bytes_def)

lemma Rep_byte_of_nat: "Rep_uint8 (byte_of_nat n) = word_of_nat n"
  by (simp add: byte_of_nat_def uint8_of_nat.abs_eq Abs_uint8_inverse)

lemma bit_byte_of_nat_div:
  "bit (Rep_uint8 (byte_of_nat (x div 2 ^ (8 * j)))) m \<longleftrightarrow> m < 8 \<and> bit x (8 * j + m)"
  by (simp add: Rep_byte_of_nat bit_of_nat_iff drop_bit_eq_div[symmetric] bit_drop_bit_eq)

lemma byte_eqI: "(\<And>m. m < 8 \<Longrightarrow> bit (Rep_uint8 a) m = bit (Rep_uint8 b) m) \<Longrightarrow> a = b"
  by (subst Rep_uint8_inject[symmetric], rule bit_word_eqI) simp

lemma le_bytes_eqI:
  assumes "\<And>n. n < 8 * k \<Longrightarrow> bit x n = bit y n"
  shows "le_bytes k x = le_bytes k y"
proof (rule nth_equalityI)
  fix j assume "j < length (le_bytes k x)"
  then have j: "j < k" by simp
  show "le_bytes k x ! j = le_bytes k y ! j"
  proof (simp add: nth_le_bytes j, rule byte_eqI)
    fix m :: nat assume "m < 8"
    then have "8 * j + m < 8 * k" using j by linarith
    then show "bit (Rep_uint8 (byte_of_nat (x div 2 ^ (8 * j)))) m = bit (Rep_uint8 (byte_of_nat (y div 2 ^ (8 * j)))) m"
      by (simp add: bit_byte_of_nat_div assms)
  qed
qed simp

lemma le_bytes_mod: "le_bytes k (x mod 2 ^ (8 * k)) = le_bytes k x"
  by (rule le_bytes_eqI) (simp add: take_bit_eq_mod[symmetric] bit_take_bit_iff)

lemma take_le_bytes: "j \<le> k \<Longrightarrow> take j (le_bytes k x) = le_bytes j x"
  by (simp add: le_bytes_def take_map)

(* Reading [k] little-endian bytes back as a word. *)
lemma word_rcat_rev_le_bytes:
  "(word_rcat_rev (map Rep_uint8 (le_bytes k x)) :: 'a::len word) = word_of_nat (x mod 2 ^ (8 * k))"
proof (rule bit_word_eqI)
  fix n assume n: "n < LENGTH('a)"
  have r: "bit (word_rcat_rev (map Rep_uint8 (le_bytes k x)) :: 'a word) n =
           (n < LENGTH('a) \<and> n div 8 < k \<and> bit (map Rep_uint8 (le_bytes k x) ! (n div 8)) (n mod 8))"
    using bit_rcat_rev_iff[OF HOL.refl, where ws = "map Rep_uint8 (le_bytes k x)" and n = n] by simp
  have "n div 8 < k \<longleftrightarrow> n < 8 * k" by auto
  moreover have "8 * (n div 8) + n mod 8 = n" by simp
  ultimately show "bit (word_rcat_rev (map Rep_uint8 (le_bytes k x)) :: 'a word) n = bit (word_of_nat (x mod 2 ^ (8 * k)) :: 'a word) n"
    using r n by (auto simp: nth_le_bytes bit_byte_of_nat_div bit_of_nat_iff take_bit_eq_mod[symmetric] bit_take_bit_iff)
qed

lemma Abs_Rep_uint8[simp]: "Abs_uint8' (Rep_uint8 b) = b"
  by (simp add: Abs_uint8'_def Rep_uint8_inverse)

(* Serialising a word of [k] bytes gives its little-endian encoding. *)
lemma rsplit_rev_le_bytes:
  fixes w :: "'a::len word"
  assumes "LENGTH('a) = 8 * k"
  shows "map Abs_uint8' (word_rsplit_rev w :: 8 word list) = le_bytes k (unat w)"
proof -
  let ?ws = "map Rep_uint8 (le_bytes k (unat w))"
  have c: "(word_rcat_rev ?ws :: 'a word) = w"
    using word_rcat_rev_le_bytes[of k "unat w", where 'a = 'a] assms
    by (simp add: unat_lt2p[of w, unfolded assms] )
  have "(word_rsplit_rev (word_rcat_rev ?ws :: 'a word) :: 8 word list) = ?ws"
    by (rule word_split_rcat_rev_size) (simp add: word_size assms)
  then show ?thesis using c by (simp add: comp_def)
qed

lemma serialise_i32_tr: "un i < 2 ^ 32 \<Longrightarrow> serialise_i32 (tr_i32 i) = le_bytes 4 (un i)"
  using rsplit_rev_le_bytes[where w = "word_of_nat (un i) :: 32 word" and k = 4]
  by (simp add: serialise_i32_def tr_i32_def Abs_i32_inverse unat_of_nat take_bit_eq_mod)

lemma serialise_i64_tr: "un i < 2 ^ 64 \<Longrightarrow> serialise_i64 (tr_i64 i) = le_bytes 8 (un i)"
  using rsplit_rev_le_bytes[where w = "word_of_nat (un i) :: 64 word" and k = 8]
  by (simp add: serialise_i64_def tr_i64_def Abs_i64_inverse unat_of_nat take_bit_eq_mod)

lemma deserialise_i32_le_bytes: "deserialise_i32 (le_bytes 4 x) = tr_i32 (mk_uN x)"
  using word_rcat_rev_le_bytes[of 4 x, where 'a = 32]
  by (simp add: deserialise_i32_def tr_i32_def Rep_uint8'_def comp_def of_nat_mod_32)

lemma deserialise_i64_le_bytes: "deserialise_i64 (le_bytes 8 x) = tr_i64 (mk_uN x)"
  using word_rcat_rev_le_bytes[of 8 x, where 'a = 64]
  by (simp add: deserialise_i64_def tr_i64_def Rep_uint8'_def comp_def of_nat_mod_64)

lemma takefill_exact: "length bs = n \<Longrightarrow> takefill b n bs = bs"
  by (induct n arbitrary: bs) (auto simp: length_Suc_conv)

lemma takefill_take: "n \<le> length bs \<Longrightarrow> takefill b n bs = take n bs"
  by (induct n arbitrary: bs) (auto simp: Suc_le_length_iff)

(* Zero-extending a little-endian encoding. *)
lemma takefill_le_bytes:
  assumes "k \<le> l" "x < 2 ^ (8 * k)"
  shows "takefill zero_byte l (le_bytes k x) = le_bytes l x"
proof (rule nth_equalityI)
  fix j assume "j < length (takefill zero_byte l (le_bytes k x))"
  then have j: "j < l" by simp
  show "takefill zero_byte l (le_bytes k x) ! j = le_bytes l x ! j"
  proof (cases "j < k")
    case False
    have "(2::nat) ^ (8 * k) \<le> 2 ^ (8 * j)" using False by simp
    then have "x div 2 ^ (8 * j) = 0" using assms(2) by (intro div_less) linarith
    then show ?thesis using j False by (simp add: nth_takefill nth_le_bytes)
  qed (use j in \<open>simp add: nth_takefill nth_le_bytes\<close>)
qed simp

section \<open>Memory contents\<close>

lemma list_slice_take_drop: "list_slice xs n m = take m (drop n xs)"
  by (induction xs n m rule: list_slice.induct) auto

lemma list_slice_update_eq:
  "length ul = m \<Longrightarrow> n + m \<le> length l \<Longrightarrow> list_slice_update l n m ul = take n l @ ul @ drop (n + m) l"
  by (induction l n m ul rule: list_slice_update.induct) auto

(* A slice of the requested length lies within the list. *)
lemma list_slice_bound: "length (list_slice xs n m) = m \<Longrightarrow> 0 < m \<Longrightarrow> n + m \<le> length xs"
  by (simp add: list_slice_take_drop)

lemma read_bytes_tr:
  "read_bytes (tr_meminst mi) n l = map tr_byte (list_slice (BYTES mi) n l)"
  by (simp add: read_bytes_def tr_meminst_def mem_rep_read_bytes.abs_eq list_slice_take_drop take_map drop_map)

lemma write_bytes_tr:
  "length bs = l \<Longrightarrow> n + l \<le> length (BYTES mi) \<Longrightarrow>
   write_bytes (tr_meminst mi) n (map tr_byte bs) = tr_meminst (mi\<lparr>BYTES := list_slice_update (BYTES mi) n l bs\<rparr>)"
  by (simp add: write_bytes_def tr_meminst_def mem_rep_write_bytes.abs_eq list_slice_update_eq take_map drop_map)

lemma nat_floor_div8[simp]: "nat \<lfloor>rat_of_nat n / 8\<rfloor> = n div 8"
  by (metis floor_divide_of_nat_eq nat_int of_nat_numeral)

lemma tp_num_length_tp_of_bits:
  "ext_width_ok nt n \<Longrightarrow> tp_num_length (tp_of_bits n) = n div 8"
  by (auto simp: ext_width_ok_def tp_of_bits_def tp_num_length_def)

lemma t_num_length_tr: "t_num_length (tr_numtype nt) = the (size (valtype_numtype nt)) div 8"
  by (cases nt) (simp_all add: t_num_length_def)

lemma t_num_length_pos: "0 < t_num_length t"
  by (cases t) (simp_all add: t_num_length_def)

section \<open>Byte encodings of SpecTec numbers\<close>

(* SpecTec's [nbytes_] and [ibytes_] are axiomatised.  As in the Rocq bridge
   ([nbytes_tr], [ibytes_tr]), they are assumed to agree with WasmCert's
   serialisation and with the little-endian encoding.  WasmCert-Isabelle's float
   and vector serialisation is itself only specified up to its length
   ([serialise_f32_len], ...) and its deserialisation not at all, so the locale
   also assumes that deserialisation inverts serialisation; this holds for the
   IEEE 754 bit layout, which satisfies [serialise_f32_len].  Integer
   serialisation is concrete, and its round trip is proved
   ([deserialise_serialise]). *)
locale mem_bytes = builtins +
  assumes nbytes_tr: "\<And>nt c. wf_num_underscore nt c \<Longrightarrow> map tr_byte (nbytes_underscore nt c) = bits_num (tr_num c)"
    and ibytes_tr: "\<And>N i. wf_uN N i \<Longrightarrow> map tr_byte (ibytes_underscore N i) = le_bytes (N div 8) (un i)"
    and f32_roundtrip: "\<And>x. deserialise_f32 (serialise_f32 x) = x"
    and f64_roundtrip: "\<And>x. deserialise_f64 (serialise_f64 x) = x"
    and v128_roundtrip: "\<And>x. deserialise_v128 (serialise_v128 x) = x"

lemma deserialise_i32_serialise: "deserialise_i32 (serialise_i32 c) = c"
  by (simp add: serialise_i32_def deserialise_i32_def comp_def Abs_uint8'.rep_eq Rep_uint8'_def
                word_rcat_rsplit_rev Rep_i32_inverse)

lemma deserialise_i64_serialise: "deserialise_i64 (serialise_i64 c) = c"
  by (simp add: serialise_i64_def deserialise_i64_def comp_def Abs_uint8'.rep_eq Rep_uint8'_def
                word_rcat_rsplit_rev Rep_i64_inverse)

lemma (in mem_bytes) deserialise_serialise:
  "wasm_deserialise_num (bits_num v) (typeof_num v) = v"
  by (cases v) (simp_all add: wasm_deserialise_num_def bits_num_def typeof_num_def
                  deserialise_i32_serialise deserialise_i64_serialise f32_roundtrip f64_roundtrip)

lemma length_bits_num: "length (bits_num v) = t_num_length (typeof_num v)"
  by (cases v) (simp_all add: bits_num_def typeof_num_def t_num_length_def serialise_f32_len serialise_f64_len
     serialise_i32_def serialise_i64_def length_word_rsplit_rev_even)

lemma (in mem_bytes) length_nbytes:
  "wf_num_underscore nt c \<Longrightarrow> length (nbytes_underscore nt c) = t_num_length (tr_numtype nt)"
  using arg_cong[OF nbytes_tr, of nt c length] by (simp add: length_bits_num typeof_tr_num)

section \<open>Packed loads and stores\<close>

lemma size_Inn: "the (size (valtype_Inn t)) = isz t"
  by (cases t) simp_all

lemma bits_num_ival: "iok t c \<Longrightarrow> bits_num (ival t c) = le_bytes (t_num_length (tr_numtype (numtype_Inn t))) (un c)"
  by (cases t) (simp_all add: ival_def bits_num_def t_num_length_def serialise_i32_tr serialise_i64_tr)

lemma ext_width_bytes:
  assumes "ext_width_ok (numtype_Inn t) n"
  shows "n = 8 * (n div 8)" "0 < n div 8" "n div 8 \<le> t_num_length (tr_numtype (numtype_Inn t))" "n < isz t"
  using assms by (cases t; auto simp: ext_width_ok_def t_num_length_def)+

(* A packed load: WasmCert sign- or zero-extends the loaded bytes. *)
lemma (in builtins) load_packed_val:
  assumes e: "ext_width_ok (numtype_Inn t) n" and c: "wf_uN n c"
  shows "wasm_deserialise_num (sign_extend (tr_sx sx) (t_num_length (tr_numtype (numtype_Inn t))) (le_bytes (n div 8) (un c)))
           (tr_numtype (numtype_Inn t)) =
         ival t (extend__underscore n (the (size (valtype_Inn t))) sx c)"
proof -
  note w = ext_width_bytes[OF e]
  have cn: "un c < 2 ^ n" using c by (simp add: wf_uN_iff)
  have ck: "un c < 2 ^ (8 * (n div 8))" using cn w(1) by simp
  have ok: "iok t c" using less_trans[OF cn, of "2 ^ isz t"] w(4) by simp
  show ?thesis
  proof (cases sx)
    case U
    have "takefill zero_byte (t_num_length (tr_numtype (numtype_Inn t))) (le_bytes (n div 8) (un c)) =
          le_bytes (t_num_length (tr_numtype (numtype_Inn t))) (un c)"
      by (rule takefill_le_bytes[OF w(3) ck])
    then show ?thesis using U
      by (cases t) (simp_all add: sign_extend_def bytes_takefill_def wasm_deserialise_num_def t_num_length_def
                      deserialise_i32_le_bytes deserialise_i64_le_bytes extend_def ival_def)
  next
    case S
    have tk: "le_bytes (n div 8) (un c) = take (tp_num_length (tp_of_bits n)) (bits_num (ival t c))"
      using bits_num_ival[OF ok] tp_num_length_tp_of_bits[OF e] w(3) by (simp add: take_le_bytes)
    have ty: "typeof_num (ival t c) = tr_numtype (numtype_Inn t)"
      by (cases t) (simp_all add: ival_def typeof_num_def)
    have "wasm_deserialise_num (sign_extend Wasm_Ast.S (t_num_length (tr_numtype (numtype_Inn t))) (le_bytes (n div 8) (un c)))
            (tr_numtype (numtype_Inn t)) = app_unop (Extend_s (tp_of_bits n)) (ival t c)"
      by (simp add: app_unop_def app_extend_s_def tk ty)
    also have "\<dots> = ival t (extend__underscore n (isz t) isabelle_reference_output_wasm2.S (wrap__underscore (isz t) n c))"
      by (rule extend_unop_wc[OF ok e])
    also have "wrap__underscore (isz t) n c = c"
      using cn by (cases c) (simp add: wrap_def)
    finally show ?thesis using S by (simp add: size_Inn)
  qed
qed

(* The bytes of a packed store are the low bytes of the serialised number. *)
lemma (in mem_bytes) ibytes_wrap:
  assumes e: "ext_width_ok (numtype_Inn t) n" and ok: "iok t c"
  shows "map tr_byte (ibytes_underscore n (wrap__underscore (the (size (valtype_Inn t))) n c)) =
         take (tp_num_length (tp_of_bits n)) (bits_num (ival t c))"
proof -
  note w = ext_width_bytes[OF e]
  have "wf_uN n (wrap__underscore (the (size (valtype_Inn t))) n c)" by (simp add: wrap_def wf_uN_iff)
  then have "map tr_byte (ibytes_underscore n (wrap__underscore (the (size (valtype_Inn t))) n c)) =
             le_bytes (n div 8) (un c mod 2 ^ n)"
    by (simp add: ibytes_tr wrap_def)
  also have "\<dots> = le_bytes (n div 8) (un c)"
    using le_bytes_mod[of "n div 8" "un c"] w(1) by simp
  finally show ?thesis
    using bits_num_ival[OF ok] tp_num_length_tp_of_bits[OF e] w(3) by (simp add: take_le_bytes)
qed

section \<open>Load and store simulations\<close>

lemma tr_loadop_pack: "tr_loadop (Some (mk_loadop__0 t (mk_loadop_Inn (mk_sz n) sx))) = Some (tp_of_bits n, tr_sx sx)"
  by (simp add: tr_tp_def)

lemma (in mem_bytes) sim_load_num:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32" and c: "wf_num_underscore nt c"
    and b: "nbytes_underscore nt c = list_slice (BYTES mi) (un u + un (OFFSET ao))
              (nat \<lfloor>rat_of_nat (the (size (valtype_numtype nt))) / rat_of_nat 8\<rfloor>)"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc6 (admininstr_st6_LOAD nt None ao)])
             (mk_config (mk_state s f) [admininstr_sc1 (admininstr_st1_CONST nt c)])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  let ?L = "t_num_length (tr_numtype nt)"
  let ?p = "un u + un (OFFSET ao)"
  have b': "list_slice (BYTES mi) ?p ?L = nbytes_underscore nt c"
    using b by (simp add: nat_floor_div8 t_num_length_tr)
  have len: "length (nbytes_underscore nt c) = ?L" by (rule length_nbytes[OF c])
  have bd: "?p + ?L \<le> length (BYTES mi)"
    using list_slice_bound[of "BYTES mi" ?p ?L] b' len t_num_length_pos by simp
  have ld: "load (s.mems (tr_store s) ! (MEMS (frame_MODULE f) ! 0)) (nat_of_int (tr_i32 u)) (tr_offset ao) ?L =
              Some (bits_num (tr_num c))"
    using x1 bd u b' nbytes_tr[OF c] by (simp add: load_def nat_of_int_tr_i32 tr_offset_def read_bytes_tr)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $Load (tr_numtype nt) None (tr_align ao) (tr_offset ao)]
              (tr_store s) (tr_frame f) [$EConstNum (tr_num c)]"
    using reduce.load_Some[OF smem_ind_tr[OF x1(2)] HOL.refl ld] deserialise_serialise[of "tr_num c"]
          typeof_tr_num[OF c] by simp
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

lemma sim_load_num_trap:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32"
    and b: "length (BYTES mi) < un u + un (OFFSET ao) + nat \<lfloor>rat_of_nat (the (size (valtype_numtype nt))) / rat_of_nat 8\<rfloor>"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc6 (admininstr_st6_LOAD nt None ao)])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have ld: "load (s.mems (tr_store s) ! (MEMS (frame_MODULE f) ! 0)) (nat_of_int (tr_i32 u)) (tr_offset ao)
              (t_num_length (tr_numtype nt)) = None"
    using x1 b u by (simp add: load_def nat_of_int_tr_i32 tr_offset_def nat_floor_div8 t_num_length_tr)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $Load (tr_numtype nt) None (tr_align ao) (tr_offset ao)]
              (tr_store s) (tr_frame f) [Trap]"
    by (rule reduce.load_None[OF smem_ind_tr[OF x1(2)] HOL.refl ld])
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

lemma (in mem_bytes) sim_load_pack:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32"
    and e: "ext_width_ok (numtype_Inn t) n" and c: "wf_uN n c"
    and b: "ibytes_underscore n c = list_slice (BYTES mi) (un u + un (OFFSET ao)) (nat \<lfloor>rat_of_nat n / rat_of_nat 8\<rfloor>)"
  shows "sim (mk_config (mk_state s f)
                [i32c u, admininstr_sc6 (admininstr_st6_LOAD (numtype_Inn t) (Some (mk_loadop__0 t (mk_loadop_Inn (mk_sz n) sx))) ao)])
             (mk_config (mk_state s f)
                [admininstr_sc1 (admininstr_st1_CONST (numtype_Inn t) (mk_num__0 t (extend__underscore n (the (size (valtype_Inn t))) sx c)))])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  note w = ext_width_bytes[OF e]
  let ?k = "n div 8"
  let ?p = "un u + un (OFFSET ao)"
  let ?T = "tr_numtype (numtype_Inn t)"
  have b': "list_slice (BYTES mi) ?p ?k = ibytes_underscore n c"
    using b by (simp add: nat_floor_div8)
  have len: "length (ibytes_underscore n c) = ?k"
    using arg_cong[OF ibytes_tr[OF c], of length] by simp
  have bd: "?p + ?k \<le> length (BYTES mi)"
    using list_slice_bound[of "BYTES mi" ?p ?k] b' len w(2) by simp
  have ld: "load_packed (tr_sx sx) (s.mems (tr_store s) ! (MEMS (frame_MODULE f) ! 0)) (nat_of_int (tr_i32 u)) (tr_offset ao)
              (tp_num_length (tp_of_bits n)) (t_num_length ?T) =
            Some (sign_extend (tr_sx sx) (t_num_length ?T) (le_bytes ?k (un c)))"
    using x1 bd u b' ibytes_tr[OF c]
    by (simp add: load_packed_def load_def nat_of_int_tr_i32 tr_offset_def read_bytes_tr tp_num_length_tp_of_bits[OF e])
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $Load ?T (Some (tp_of_bits n, tr_sx sx)) (tr_align ao) (tr_offset ao)]
              (tr_store s) (tr_frame f) [$EConstNum (ival t (extend__underscore n (the (size (valtype_Inn t))) sx c))]"
    using reduce.load_packed_Some[OF smem_ind_tr[OF x1(2)] HOL.refl ld] load_packed_val[OF e c, of sx] by simp
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]]
    by (simp add: tr_tp_def ival_def)
qed

lemma sim_load_pack_trap:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32" and e: "ext_width_ok (numtype_Inn t) n"
    and b: "length (BYTES mi) < un u + un (OFFSET ao) + nat \<lfloor>rat_of_nat n / rat_of_nat 8\<rfloor>"
  shows "sim (mk_config (mk_state s f)
                [i32c u, admininstr_sc6 (admininstr_st6_LOAD (numtype_Inn t) (Some (mk_loadop__0 t (mk_loadop_Inn (mk_sz n) sx))) ao)])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have ld: "load_packed (tr_sx sx) (s.mems (tr_store s) ! (MEMS (frame_MODULE f) ! 0)) (nat_of_int (tr_i32 u)) (tr_offset ao)
              (tp_num_length (tp_of_bits n)) (t_num_length (tr_numtype (numtype_Inn t))) = None"
    using x1 b u by (simp add: load_packed_def load_def nat_of_int_tr_i32 tr_offset_def nat_floor_div8 tp_num_length_tp_of_bits[OF e])
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $Load (tr_numtype (numtype_Inn t)) (Some (tp_of_bits n, tr_sx sx)) (tr_align ao) (tr_offset ao)]
              (tr_store s) (tr_frame f) [Trap]"
    by (rule reduce.load_packed_None[OF smem_ind_tr[OF x1(2)] HOL.refl ld])
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by (simp add: tr_tp_def)
qed

(* An in-bounds store.  SpecTec's [store_num_val] has no bounds premise: out of
   bounds, [list_slice_update] writes a prefix of the bytes (or none), while
   WasmCert traps.  That is the disagreement [Oob_store] of the Rocq bridge; the
   premise [bd] excludes it.  The memory address is in the store by store
   validity. *)
lemma (in mem_bytes) sim_store_num:
  assumes a: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)"
    and u: "un u < 2 ^ 32" and c: "wf_num_underscore nt c"
    and bd: "un u + un (OFFSET ao) + t_num_length (tr_numtype nt) \<le> length (BYTES (store_MEMS s ! (MEMS (frame_MODULE f) ! 0)))"
    and w: "fun_with_mem (mk_state s f) (mk_uN 0) (un u + un (OFFSET ao))
              (nat \<lfloor>rat_of_nat (the (size (valtype_numtype nt))) / rat_of_nat 8\<rfloor>) (nbytes_underscore nt c) z'"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc1 (admininstr_st1_CONST nt c), admininstr_sc6 (admininstr_st6_STORE nt None ao)])
             (mk_config z' [])"
proof -
  let ?a = "MEMS (frame_MODULE f) ! 0"
  let ?mi = "store_MEMS s ! ?a"
  let ?p = "un u + un (OFFSET ao)"
  let ?L = "t_num_length (tr_numtype nt)"
  let ?bs = "nbytes_underscore nt c"
  let ?mi' = "?mi\<lparr>BYTES := list_slice_update (BYTES ?mi) ?p ?L ?bs\<rparr>"
  let ?s' = "s\<lparr>store_MEMS := list_update_func (store_MEMS s) ?a (\<lambda>m. m\<lparr>BYTES := list_slice_update (BYTES m) ?p ?L ?bs\<rparr>)\<rparr>"
  have z: "z' = mk_state ?s' f" using w by (auto elim!: fun_with_mem.cases simp: t_num_length_tr)
  have m0: "0 < length (MEMS (frame_MODULE f))" using w by (auto elim: fun_with_mem.cases)
  have len: "length ?bs = ?L" by (rule length_nbytes[OF c])
  have sv: "store (s.mems (tr_store s) ! ?a) (nat_of_int (tr_i32 u)) (tr_offset ao) (bits_num (tr_num c)) ?L =
              Some (tr_meminst ?mi')"
    using a bd u len write_bytes_tr[OF len bd]
    by (simp add: store_def nat_of_int_tr_i32 tr_offset_def bytes_takefill_def takefill_exact nbytes_tr[OF c, symmetric])
  have upd: "(tr_store s)\<lparr>s.mems := (s.mems (tr_store s))[?a := tr_meminst ?mi']\<rparr> = tr_store ?s'"
    using a by (simp add: tr_store_def map_list_update_func)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $EConstNum (tr_num c), $Store (tr_numtype nt) None (tr_align ao) (tr_offset ao)]
              (tr_store ?s') (tr_frame f) []"
    using reduce.store_Some[OF typeof_tr_num[OF c] smem_ind_tr[OF m0] HOL.refl sv] upd by simp
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] z by simp
qed

lemma sim_store_num_trap:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32" and c: "wf_num_underscore nt c"
    and b: "length (BYTES mi) < un u + un (OFFSET ao) + nat \<lfloor>rat_of_nat (the (size (valtype_numtype nt))) / rat_of_nat 8\<rfloor>"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc1 (admininstr_st1_CONST nt c), admininstr_sc6 (admininstr_st6_STORE nt None ao)])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have sv: "store (s.mems (tr_store s) ! (MEMS (frame_MODULE f) ! 0)) (nat_of_int (tr_i32 u)) (tr_offset ao)
              (bits_num (tr_num c)) (t_num_length (tr_numtype nt)) = None"
    using x1 b u by (simp add: store_def nat_of_int_tr_i32 tr_offset_def t_num_length_tr)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $EConstNum (tr_num c), $Store (tr_numtype nt) None (tr_align ao) (tr_offset ao)]
              (tr_store s) (tr_frame f) [Trap]"
    by (rule reduce.store_None[OF typeof_tr_num[OF c] smem_ind_tr[OF x1(2)] HOL.refl sv])
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by simp
qed

lemma typeof_ival: "typeof_num (ival t c) = tr_numtype (numtype_Inn t)"
  by (cases t) (simp_all add: ival_def typeof_num_def)

(* An in-bounds packed store (out of bounds: [Oob_store], as above). *)
lemma (in mem_bytes) sim_store_pack:
  assumes a: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)"
    and u: "un u < 2 ^ 32" and e: "ext_width_ok (numtype_Inn t) n" and c: "iok t c"
    and bd: "un u + un (OFFSET ao) + n div 8 \<le> length (BYTES (store_MEMS s ! (MEMS (frame_MODULE f) ! 0)))"
    and w: "fun_with_mem (mk_state s f) (mk_uN 0) (un u + un (OFFSET ao)) (nat \<lfloor>rat_of_nat n / rat_of_nat 8\<rfloor>)
              (ibytes_underscore n (wrap__underscore (the (size (valtype_Inn t))) n c)) z'"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc1 (admininstr_st1_CONST (numtype_Inn t) (mk_num__0 t c)),
                                         admininstr_sc6 (admininstr_st6_STORE (numtype_Inn t) (Some (mk_sz n)) ao)])
             (mk_config z' [])"
proof -
  note wd = ext_width_bytes[OF e]
  let ?a = "MEMS (frame_MODULE f) ! 0"
  let ?mi = "store_MEMS s ! ?a"
  let ?p = "un u + un (OFFSET ao)"
  let ?k = "n div 8"
  let ?bs = "ibytes_underscore n (wrap__underscore (the (size (valtype_Inn t))) n c)"
  let ?mi' = "?mi\<lparr>BYTES := list_slice_update (BYTES ?mi) ?p ?k ?bs\<rparr>"
  let ?s' = "s\<lparr>store_MEMS := list_update_func (store_MEMS s) ?a (\<lambda>m. m\<lparr>BYTES := list_slice_update (BYTES m) ?p ?k ?bs\<rparr>)\<rparr>"
  have z: "z' = mk_state ?s' f" using w by (auto elim!: fun_with_mem.cases)
  have m0: "0 < length (MEMS (frame_MODULE f))" using w by (auto elim: fun_with_mem.cases)
  have ib: "map tr_byte ?bs = take ?k (bits_num (ival t c))"
    using ibytes_wrap[OF e c] tp_num_length_tp_of_bits[OF e] by simp
  have lb: "?k \<le> length (bits_num (ival t c))"
    using wd(3) by (simp add: length_bits_num typeof_ival)
  have len: "length ?bs = ?k"
    using arg_cong[OF ib, of length] lb by simp
  have sv: "store_packed (s.mems (tr_store s) ! ?a) (nat_of_int (tr_i32 u)) (tr_offset ao) (bits_num (ival t c))
              (tp_num_length (tp_of_bits n)) = Some (tr_meminst ?mi')"
    using a bd u lb write_bytes_tr[OF len bd] ib
    by (simp add: store_packed_def store_def nat_of_int_tr_i32 tr_offset_def bytes_takefill_def takefill_take
                  tp_num_length_tp_of_bits[OF e])
  have upd: "(tr_store s)\<lparr>s.mems := (s.mems (tr_store s))[?a := tr_meminst ?mi']\<rparr> = tr_store ?s'"
    using a by (simp add: tr_store_def map_list_update_func)
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $EConstNum (ival t c),
               $Store (tr_numtype (numtype_Inn t)) (Some (tp_of_bits n)) (tr_align ao) (tr_offset ao)]
              (tr_store ?s') (tr_frame f) []"
    using reduce.store_packed_Some[OF typeof_ival smem_ind_tr[OF m0] HOL.refl sv] upd by simp
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] z
    by (simp add: tr_tp_def ival_def)
qed

lemma sim_store_pack_trap:
  assumes m: "fun_mem (mk_state s f) (mk_uN 0) mi" and u: "un u < 2 ^ 32" and e: "ext_width_ok (numtype_Inn t) n"
    and b: "length (BYTES mi) < un u + un (OFFSET ao) + nat \<lfloor>rat_of_nat n / rat_of_nat 8\<rfloor>"
  shows "sim (mk_config (mk_state s f) [i32c u, admininstr_sc1 (admininstr_st1_CONST (numtype_Inn t) (mk_num__0 t c)),
                                         admininstr_sc6 (admininstr_st6_STORE (numtype_Inn t) (Some (mk_sz n)) ao)])
             (mk_config (mk_state s f) [admininstr_sc7 admininstr_st7_TRAP])"
proof -
  obtain x1: "MEMS (frame_MODULE f) ! 0 < length (store_MEMS s)" "0 < length (MEMS (frame_MODULE f))"
      "mi = store_MEMS s ! (MEMS (frame_MODULE f) ! 0)"
    using m by (rule fun_mem_E)
  have sv: "store_packed (s.mems (tr_store s) ! (MEMS (frame_MODULE f) ! 0)) (nat_of_int (tr_i32 u)) (tr_offset ao)
              (bits_num (ival t c)) (tp_num_length (tp_of_bits n)) = None"
    using x1 b u by (simp add: store_packed_def store_def nat_of_int_tr_i32 tr_offset_def tp_num_length_tp_of_bits[OF e])
  have st: "reduce (tr_store s) (tr_frame f)
              [$EConstNum (ConstInt32 (tr_i32 u)), $EConstNum (ival t c),
               $Store (tr_numtype (numtype_Inn t)) (Some (tp_of_bits n)) (tr_align ao) (tr_offset ao)]
              (tr_store s) (tr_frame f) [Trap]"
    by (rule reduce.store_packed_None[OF typeof_ival smem_ind_tr[OF x1(2)] HOL.refl sv])
  show ?thesis unfolding sim_def using wsim_step[OF st wsim_refl[OF nls_refl]] by (simp add: tr_tp_def ival_def)
qed

end

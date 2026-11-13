(* Agreement of the SpecTec numeric builtins with WasmCert-Isabelle.
   Port of ../wasmcert-rocq/builtins.v.

   The SpecTec theory declares the numeric primitives of 3-numerics.spectec that
   the Isabelle backend cannot define (iclz_, fadd_, wrap_, trunc_, ...) with
   [axiomatization]: uninterpreted constants whose only axioms say that their
   results are well-formed.  To relate SpecTec's numeric steps to WasmCert's we
   fix their meaning.  Where the Rocq bridge adds global axioms, this theory
   uses the locale [builtins], so no axiom is added to HOL:
   - [truncz], [wrap_] and [extend_] are given their definition in the
     specification, since they are used at many widths ([truncz] is WasmCert's
     [trunc], truncation towards zero);
   - every other builtin is assumed to agree with the WasmCert operation that
     implements it, through the translation.

   Each assumption constrains a single uninterpreted constant at well-formed
   arguments; taking each constant to be the WasmCert operation composed with
   the back-translation satisfies them (every WasmCert number is the translation
   of a well-formed SpecTec number: [nrep_int], [nrep_float]), so the locale is
   satisfiable.  They fix SpecTec's NaN nondeterminism to WasmCert's choice of NaN.

   SpecTec's own signed arithmetic ([$signed_], [$inv_signed_], [$idiv_], ...)
   is related to WasmCert's through WasmCert's specification of its integer
   operations ([wasm_int] class, stated with [signed], [signed_inv], [trunc]). *)
theory Builtins
  imports Completeness
begin

termination iadd_underscore by lexicographic_order
termination isub_underscore by lexicographic_order
termination imul_underscore by lexicographic_order
termination ieq_underscore by lexicographic_order
termination ine_underscore by lexicographic_order
termination ieqz_underscore by lexicographic_order
termination res_bool by lexicographic_order
termination list_underscore by lexicographic_order

section \<open>Notation\<close>

(* An integer or float of SpecTec's number type [t], translated. *)
definition ival :: "Inn \<Rightarrow> uN \<Rightarrow> v_num" where
  "ival t i = tr_num (mk_num__0 t i)"

definition fval :: "Fnn \<Rightarrow> fN \<Rightarrow> v_num" where
  "fval t x = tr_num (mk_num__1 t x)"

(* Well-formed numbers of type [t]. *)
definition iok :: "Inn \<Rightarrow> uN \<Rightarrow> bool" where
  "iok t i \<longleftrightarrow> wf_num_underscore (numtype_Inn t) (mk_num__0 t i)"

definition fok :: "Fnn \<Rightarrow> fN \<Rightarrow> bool" where
  "fok t x \<longleftrightarrow> wf_num_underscore (numtype_Fnn t) (mk_num__1 t x)"

(* The bit width SpecTec passes to the builtins at type [t]. *)
primrec isz :: "Inn \<Rightarrow> nat" where
  "isz Inn_I32 = 32"
| "isz Inn_I64 = 64"

primrec fsz :: "Fnn \<Rightarrow> nat" where
  "fsz Fnn_F32 = 32"
| "fsz Fnn_F64 = 64"

(* A WasmCert number that some well-formed SpecTec number of type [nt]
   translates to. *)
definition nrep :: "numtype \<Rightarrow> v_num \<Rightarrow> bool" where
  "nrep nt v \<longleftrightarrow> (\<exists>c. wf_num_underscore nt c \<and> tr_num c = v)"

(* A partial WasmCert result, as the list of results SpecTec uses. *)
definition olist :: "'a option \<Rightarrow> 'a list" where
  "olist x = (case x of Some y \<Rightarrow> [y] | None \<Rightarrow> [])"

lemma olist_simps[simp]: "olist (Some y) = [y]" "olist None = []"
  by (simp_all add: olist_def)

(* The float builtins by operator. *)
primrec fun1 :: "unop_Fnn \<Rightarrow> nat \<Rightarrow> fN \<Rightarrow> fN list" where
  "fun1 ABS = fabs_underscore"
| "fun1 unop_Fnn_NEG = fneg_underscore"
| "fun1 SQRT = fsqrt_underscore"
| "fun1 CEIL = fceil_underscore"
| "fun1 FLOOR = ffloor_underscore"
| "fun1 TRUNC = ftrunc_underscore"
| "fun1 NEAREST = fnearest_underscore"

primrec fun2 :: "binop_Fnn \<Rightarrow> nat \<Rightarrow> fN \<Rightarrow> fN \<Rightarrow> fN list" where
  "fun2 binop_Fnn_ADD = fadd_underscore"
| "fun2 binop_Fnn_SUB = fsub_underscore"
| "fun2 binop_Fnn_MUL = fmul_underscore"
| "fun2 binop_Fnn_DIV = fdiv_underscore"
| "fun2 res_MIN = fmin_underscore"
| "fun2 res_MAX = fmax_underscore"
| "fun2 COPYSIGN = fcopysign_underscore"

primrec frel :: "relop_Fnn \<Rightarrow> nat \<Rightarrow> fN \<Rightarrow> fN \<Rightarrow> uN" where
  "frel relop_Fnn_EQ = feq_underscore"
| "frel relop_Fnn_NE = fne_underscore"
| "frel relop_Fnn_LT = flt_underscore"
| "frel relop_Fnn_GT = fgt_underscore"
| "frel relop_Fnn_LE = fle_underscore"
| "frel relop_Fnn_GE = fge_underscore"

section \<open>Sizes and well-formedness\<close>

lemma fun_sizenn_iff[simp]:
  "fun_sizenn I32 n \<longleftrightarrow> n = 32" "fun_sizenn I64 n \<longleftrightarrow> n = 64"
  "fun_sizenn F32 n \<longleftrightarrow> n = 32" "fun_sizenn F64 n \<longleftrightarrow> n = 64"
  by (auto elim: fun_sizenn.cases intro: fun_sizenn.intros[of I32, simplified]
                 fun_sizenn.intros[of I64, simplified] fun_sizenn.intros[of F32, simplified]
                 fun_sizenn.intros[of F64, simplified])

lemma fun_sizenn1_iff[simp]:
  "fun_sizenn1 I32 n \<longleftrightarrow> n = 32" "fun_sizenn1 I64 n \<longleftrightarrow> n = 64"
  "fun_sizenn1 F32 n \<longleftrightarrow> n = 32" "fun_sizenn1 F64 n \<longleftrightarrow> n = 64"
  by (auto elim: fun_sizenn1.cases intro: fun_sizenn1.intros[of I32, simplified]
                 fun_sizenn1.intros[of I64, simplified] fun_sizenn1.intros[of F32, simplified]
                 fun_sizenn1.intros[of F64, simplified])

lemma fun_sizenn2_iff[simp]:
  "fun_sizenn2 I32 n \<longleftrightarrow> n = 32" "fun_sizenn2 I64 n \<longleftrightarrow> n = 64"
  "fun_sizenn2 F32 n \<longleftrightarrow> n = 32" "fun_sizenn2 F64 n \<longleftrightarrow> n = 64"
  by (auto elim: fun_sizenn2.cases intro: fun_sizenn2.intros[of I32, simplified]
                 fun_sizenn2.intros[of I64, simplified] fun_sizenn2.intros[of F32, simplified]
                 fun_sizenn2.intros[of F64, simplified])

lemma wf_uN_iff: "wf_uN N u \<longleftrightarrow> un u < 2 ^ N"
proof (cases u)
  case (mk_uN i)
  have "(0::nat) < 2 ^ N" by simp
  then have "i \<le> 2 ^ N - Suc 0 \<longleftrightarrow> i < 2 ^ N" by linarith
  then show ?thesis using mk_uN
    by (auto elim!: wf_uN.cases intro!: wf_uN.intros)
qed

lemma iok_iff[simp]: "iok t i \<longleftrightarrow> un i < 2 ^ isz t"
  by (cases t)
     (auto simp: iok_def wf_uN_iff elim!: wf_num_underscore.cases intro!: wf_num_underscore.intros)

lemma fok_iff[simp]: "fok t x \<longleftrightarrow> wf_fN (fsz t) x"
  by (cases t)
     (auto simp: fok_def elim!: wf_num_underscore.cases
           intro!: wf_num_underscore.intros(2)[of Fnn_F32 32, simplified]
                   wf_num_underscore.intros(2)[of Fnn_F64 64, simplified])

lemma ival_simps[simp]:
  "ival Inn_I32 i = ConstInt32 (tr_i32 i)" "ival Inn_I64 i = ConstInt64 (tr_i64 i)"
  by (simp_all add: ival_def)

lemma fval_simps[simp]:
  "fval Fnn_F32 x = ConstFloat32 (tr_f32 x)" "fval Fnn_F64 x = ConstFloat64 (tr_f64 x)"
  by (simp_all add: fval_def)

section \<open>The locale\<close>

locale builtins =
  (* builtins given their specification definition *)
  assumes truncz_def: "\<And>q. truncz q = trunc q"
    and wrap_def: "\<And>M N i. wrap__underscore M N i = mk_uN (un i mod 2 ^ N)"
    and extend_def: "\<And>M N sx i. extend__underscore M N sx i =
      mk_uN (case sx of isabelle_reference_output_wasm2.U \<Rightarrow> un i
             | isabelle_reference_output_wasm2.S \<Rightarrow>
                 if un i < 2 ^ (M - 1) then un i else un i + 2 ^ N - 2 ^ M)"
    (* integer builtins *)
    and iclz_tr: "\<And>t i. iok t i \<Longrightarrow>
      ival t (iclz_underscore (isz t) i) = app_unop (Unop_i Clz) (ival t i)"
    and ictz_tr: "\<And>t i. iok t i \<Longrightarrow>
      ival t (ictz_underscore (isz t) i) = app_unop (Unop_i Ctz) (ival t i)"
    and ipopcnt_tr: "\<And>t i. iok t i \<Longrightarrow>
      ival t (ipopcnt_underscore (isz t) i) = app_unop (Unop_i Popcnt) (ival t i)"
    and iand_tr: "\<And>t i j. iok t i \<Longrightarrow> iok t j \<Longrightarrow>
      app_binop (Binop_i And) (ival t i) (ival t j) = Some (ival t (iand_underscore (isz t) i j))"
    and ior_tr: "\<And>t i j. iok t i \<Longrightarrow> iok t j \<Longrightarrow>
      app_binop (Binop_i Or) (ival t i) (ival t j) = Some (ival t (ior_underscore (isz t) i j))"
    and ixor_tr: "\<And>t i j. iok t i \<Longrightarrow> iok t j \<Longrightarrow>
      app_binop (Binop_i Xor) (ival t i) (ival t j) = Some (ival t (ixor_underscore (isz t) i j))"
    and ishl_tr: "\<And>t i j. iok t i \<Longrightarrow> iok t j \<Longrightarrow>
      app_binop (Binop_i Shl) (ival t i) (ival t j) = Some (ival t (ishl_underscore (isz t) i j))"
    and ishr_tr: "\<And>t sx i j. iok t i \<Longrightarrow> iok t j \<Longrightarrow>
      app_binop (Binop_i (Shr (tr_sx sx))) (ival t i) (ival t j) =
        Some (ival t (ishr_underscore (isz t) sx i j))"
    and irotl_tr: "\<And>t i j. iok t i \<Longrightarrow> iok t j \<Longrightarrow>
      app_binop (Binop_i Rotl) (ival t i) (ival t j) = Some (ival t (irotl_underscore (isz t) i j))"
    and irotr_tr: "\<And>t i j. iok t i \<Longrightarrow> iok t j \<Longrightarrow>
      app_binop (Binop_i Rotr) (ival t i) (ival t j) = Some (ival t (irotr_underscore (isz t) i j))"
    (* float builtins: WasmCert's result, when representable, is SpecTec's only result *)
    and fun1_tr: "\<And>t op x. fok t x \<Longrightarrow>
      nrep (numtype_Fnn t) (app_unop (tr_unop (mk_unop__1 t op)) (fval t x)) \<Longrightarrow>
      map (fval t) (fun1 op (fsz t) x) = [app_unop (tr_unop (mk_unop__1 t op)) (fval t x)]"
    and fun2_tr: "\<And>t op x y v. fok t x \<Longrightarrow> fok t y \<Longrightarrow>
      app_binop (tr_binop (mk_binop__1 t op)) (fval t x) (fval t y) = Some v \<Longrightarrow>
      nrep (numtype_Fnn t) v \<Longrightarrow> map (fval t) (fun2 op (fsz t) x y) = [v]"
    and frel_tr: "\<And>t op x y. fok t x \<Longrightarrow> fok t y \<Longrightarrow>
      ival Inn_I32 (frel op (fsz t) x y) = app_relop (tr_relop (mk_relop__1 t op)) (fval t x) (fval t y)"
    (* conversions *)
    and convert_tr: "\<And>t1 t2 sx i v. iok t1 i \<Longrightarrow>
      cvt (tr_numtype (numtype_Fnn t2)) (Some (Nonsat, tr_sx sx)) (ival t1 i) = Some v \<Longrightarrow>
      nrep (numtype_Fnn t2) v \<Longrightarrow> fval t2 (convert__underscore (isz t1) (fsz t2) sx i) = v"
    and trunc_tr: "\<And>t1 t2 sx x. fok t1 x \<Longrightarrow>
      map_option (ival t2) (trunc__underscore (fsz t1) (isz t2) sx x) =
        cvt (tr_numtype (numtype_Inn t2)) (Some (Nonsat, tr_sx sx)) (fval t1 x)"
    and trunc_sat_tr: "\<And>t1 t2 sx x. fok t1 x \<Longrightarrow>
      map_option (ival t2) (trunc_sat__underscore (fsz t1) (isz t2) sx x) =
        cvt (tr_numtype (numtype_Inn t2)) (Some (Sat, tr_sx sx)) (fval t1 x)"
    and promote_tr: "\<And>t1 t2 x v. fok t1 x \<Longrightarrow>
      cvt (tr_numtype (numtype_Fnn t2)) None (fval t1 x) = Some v \<Longrightarrow>
      nrep (numtype_Fnn t2) v \<Longrightarrow> map (fval t2) (promote__underscore (fsz t1) (fsz t2) x) = [v]"
    and demote_tr: "\<And>t1 t2 x v. fok t1 x \<Longrightarrow>
      cvt (tr_numtype (numtype_Fnn t2)) None (fval t1 x) = Some v \<Longrightarrow>
      nrep (numtype_Fnn t2) v \<Longrightarrow> map (fval t2) (demote__underscore (fsz t1) (fsz t2) x) = [v]"
    and reinterpret_tr: "\<And>nt1 nt2 c. wf_num_underscore nt1 c \<Longrightarrow>
      nrep nt2 (wasm_reinterpret (tr_numtype nt2) (tr_num c)) \<Longrightarrow>
      tr_num (reinterpret__underscore nt1 nt2 c) = wasm_reinterpret (tr_numtype nt2) (tr_num c)"

section \<open>Words\<close>

(* WasmCert's integers are words; SpecTec's are naturals below [2^N]. *)
lemma of_nat_mod_word: "(of_nat (n mod 2 ^ LENGTH('a)) :: 'a::len word) = of_nat n"
  by (simp add: word_of_nat_eq_iff take_bit_eq_mod)

lemma unat_of_nat_lt: "n < 2 ^ LENGTH('a) \<Longrightarrow> unat (of_nat n :: 'a::len word) = n"
  by (simp add: unat_of_nat)

lemma of_nat_word_inj:
  "a < 2 ^ LENGTH('a) \<Longrightarrow> b < 2 ^ LENGTH('a) \<Longrightarrow> (of_nat a :: 'a::len word) = of_nat b \<longleftrightarrow> a = b"
  by (metis unat_of_nat_lt)

lemma of_nat_word_less:
  "a < 2 ^ LENGTH('a) \<Longrightarrow> b < 2 ^ LENGTH('a) \<Longrightarrow> (of_nat a :: 'a::len word) < of_nat b \<longleftrightarrow> a < b"
  by (simp add: word_less_nat_alt unat_of_nat_lt)

lemma of_nat_word_le:
  "a < 2 ^ LENGTH('a) \<Longrightarrow> b < 2 ^ LENGTH('a) \<Longrightarrow> (of_nat a :: 'a::len word) \<le> of_nat b \<longleftrightarrow> a \<le> b"
  by (simp add: word_le_nat_alt unat_of_nat_lt)

lemma of_nat_word_div:
  "a < 2 ^ LENGTH('a) \<Longrightarrow> b < 2 ^ LENGTH('a) \<Longrightarrow> (of_nat a :: 'a::len word) div of_nat b = of_nat (a div b)"
  by (rule word_unat_eq_iff[THEN iffD2])
     (simp add: unat_div unat_of_nat_lt order.strict_trans1[OF div_le_dividend])

lemma of_nat_word_mod:
  "a < 2 ^ LENGTH('a) \<Longrightarrow> b < 2 ^ LENGTH('a) \<Longrightarrow> (of_nat a :: 'a::len word) mod of_nat b = of_nat (a mod b)"
  by (rule word_unat_eq_iff[THEN iffD2])
     (simp add: unat_mod unat_of_nat_lt order.strict_trans1[OF mod_less_eq_dividend])

lemma of_nat_word_sub:
  "b < 2 ^ LENGTH('a) \<Longrightarrow> (of_nat ((2 ^ LENGTH('a) + a - b) mod 2 ^ LENGTH('a)) :: 'a::len word) =
     of_nat a - of_nat b"
proof -
  assume "b < 2 ^ LENGTH('a)"
  then have "(of_nat (2 ^ LENGTH('a) + a - b) :: 'a word) = of_nat (2 ^ LENGTH('a)) + of_nat a - of_nat b"
    by (simp add: of_nat_diff)
  then show ?thesis by (simp only: of_nat_mod_word) simp
qed

(* SpecTec's [isub_] computes [(2^N + a - b) mod 2^N] in [int]. *)
lemma word_of_int_sub_mod:
  "(word_of_int ((2 ^ LENGTH('a) + int a - int b) mod 2 ^ LENGTH('a)) :: 'a::len word) =
     of_nat a - of_nat b"
proof -
  have z: "(word_of_int (2 ^ LENGTH('a)) :: 'a word) = 0"
    using word_of_int_eq_iff[where 'a='a, of "2 ^ LENGTH('a)" 0] by (simp add: take_bit_eq_mod)
  have "(word_of_int ((2 ^ LENGTH('a) + int a - int b) mod 2 ^ LENGTH('a)) :: 'a word) =
        word_of_int (2 ^ LENGTH('a) + int a - int b)"
    by (simp add: word_of_int_eq_iff take_bit_eq_mod)
  also have "\<dots> = of_nat a - of_nat b"
    by (simp only: of_int_diff of_int_add z of_int_of_nat_eq) simp
  finally show ?thesis .
qed

lemma nat_minus_mult_div: "nat (int a - int b * int (a div b)) = a mod b"
proof -
  have "int b * int (a div b) = int (b * (a div b))" by simp
  then show ?thesis by (simp only: nat_int_diff minus_mult_div_eq_mod)
qed

lemma of_nat_mod_32: "(of_nat (n mod 4294967296) :: 32 word) = of_nat n"
  using of_nat_mod_word[where 'a=32, of n] by simp

lemma of_nat_mod_64: "(of_nat (n mod 18446744073709551616) :: 64 word) = of_nat n"
  using of_nat_mod_word[where 'a=64, of n] by simp

(* The i32/i64 typedefs over words. *)
lemma Rep_Abs_i32[simp]: "Rep_i32 (Abs_i32 x) = x"
  by (simp add: Abs_i32_inverse)

lemma Rep_Abs_i64[simp]: "Rep_i64 (Abs_i64 x) = x"
  by (simp add: Abs_i64_inverse)

lemma tr_i32_mod: "tr_i32 (mk_uN (n mod 2 ^ 32)) = Abs_i32 (of_nat n)"
  using of_nat_mod_word[where 'a=32, of n] by (simp add: tr_i32_def)

lemma tr_i64_mod: "tr_i64 (mk_uN (n mod 2 ^ 64)) = Abs_i64 (of_nat n)"
  using of_nat_mod_word[where 'a=64, of n] by (simp add: tr_i64_def)

lemma tr_i32_inj: "un i < 2 ^ 32 \<Longrightarrow> un j < 2 ^ 32 \<Longrightarrow> tr_i32 i = tr_i32 j \<longleftrightarrow> i = j"
  using of_nat_word_inj[where 'a=32, of "un i" "un j"]
  by (cases i, cases j) (auto simp: tr_i32_def Abs_i32_inject)

lemma tr_i64_inj: "un i < 2 ^ 64 \<Longrightarrow> un j < 2 ^ 64 \<Longrightarrow> tr_i64 i = tr_i64 j \<longleftrightarrow> i = j"
  using of_nat_word_inj[where 'a=64, of "un i" "un j"]
  by (cases i, cases j) (auto simp: tr_i64_def Abs_i64_inject)

section \<open>The integer operations SpecTec defines\<close>

lemma iadd_tr: "iok t i \<Longrightarrow> iok t j \<Longrightarrow>
  app_binop (Binop_i Add) (ival t i) (ival t j) = Some (ival t (iadd_underscore (isz t) i j))"
  by (cases t)
     (simp_all add: app_binop_def app_binop_i_v_def app_binop_i_def int_add_i32_def
        int_add_i64_def I32.int_add_def I64.int_add_def tr_i32_def tr_i64_def of_nat_mod_32 of_nat_mod_64)

lemma isub_tr: "iok t i \<Longrightarrow> iok t j \<Longrightarrow>
  app_binop (Binop_i Sub) (ival t i) (ival t j) = Some (ival t (isub_underscore (isz t) i j))"
  using word_of_int_sub_mod[where 'a=32, of "un i" "un j", simplified]
        word_of_int_sub_mod[where 'a=64, of "un i" "un j", simplified]
  by (cases t)
     (simp_all add: iok_iff app_binop_def app_binop_i_v_def app_binop_i_def int_sub_i32_def
        int_sub_i64_def I32.int_sub_def I64.int_sub_def tr_i32_def tr_i64_def)

lemma imul_tr: "iok t i \<Longrightarrow> iok t j \<Longrightarrow>
  app_binop (Binop_i Mul) (ival t i) (ival t j) = Some (ival t (imul_underscore (isz t) i j))"
  by (cases t)
     (simp_all add: app_binop_def app_binop_i_v_def app_binop_i_def int_mul_i32_def
        int_mul_i64_def I32.int_mul_def I64.int_mul_def tr_i32_def tr_i64_def of_nat_mod_32 of_nat_mod_64)

lemma wf_num0_iff[simp]:
  "wf_num_underscore nt (mk_num__0 t i) \<longleftrightarrow> nt = numtype_Inn t \<and> un i < 2 ^ isz t"
  by (cases t) (auto simp: wf_uN_iff elim!: wf_num_underscore.cases intro!: wf_num_underscore.intros)

lemma wf_num1_iff[simp]:
  "wf_num_underscore nt (mk_num__1 t x) \<longleftrightarrow> nt = numtype_Fnn t \<and> wf_fN (fsz t) x"
  by (cases t)
     (auto elim!: wf_num_underscore.cases
        intro!: wf_num_underscore.intros(2)[of Fnn_F32 32, simplified]
                wf_num_underscore.intros(2)[of Fnn_F64 64, simplified])

lemma of_nat_word_eq_0: "n < 2 ^ LENGTH('a) \<Longrightarrow> (of_nat n :: 'a::len word) = 0 \<longleftrightarrow> n = 0"
  using of_nat_word_inj[of n 0] by simp

lemma Rep_tr_i32[simp]: "Rep_i32 (tr_i32 i) = of_nat (un i)"
  by (simp add: tr_i32_def)

lemma Rep_tr_i64[simp]: "Rep_i64 (tr_i64 i) = of_nat (un i)"
  by (simp add: tr_i64_def)

(* Every WasmCert integer is the translation of a well-formed SpecTec one. *)
lemma nrep_int[simp]: "nrep I32 (ConstInt32 w)" "nrep I64 (ConstInt64 w')"
proof -
  have "tr_num (mk_num__0 Inn_I32 (mk_uN (unat (Rep_i32 w)))) = ConstInt32 w"
    by (simp add: tr_i32_def Rep_i32_inverse)
  moreover have "unat (Rep_i32 w) < 2 ^ 32"
    using unat_lt2p[of "Rep_i32 w"] by simp
  ultimately show "nrep I32 (ConstInt32 w)"
    unfolding nrep_def by (intro exI[of _ "mk_num__0 Inn_I32 (mk_uN (unat (Rep_i32 w)))"]) simp
  have "tr_num (mk_num__0 Inn_I64 (mk_uN (unat (Rep_i64 w')))) = ConstInt64 w'"
    by (simp add: tr_i64_def Rep_i64_inverse)
  moreover have "unat (Rep_i64 w') < 2 ^ 64"
    using unat_lt2p[of "Rep_i64 w'"] by simp
  ultimately show "nrep I64 (ConstInt64 w')"
    unfolding nrep_def by (intro exI[of _ "mk_num__0 Inn_I64 (mk_uN (unat (Rep_i64 w')))"]) simp
qed

lemma tr_i32_res_bool: "tr_i32 (mk_uN (res_bool b)) = wasm_bool b"
  by (cases b) (simp_all add: tr_i32_def wasm_bool.abs_eq)

section \<open>SpecTec's signed arithmetic\<close>

(* The two's-complement reading of an [N]-bit pattern, as SpecTec's [$signed_]
   and WasmCert's [signed] compute it. *)
definition sv :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "sv N a = (if a < 2 ^ (N - 1) then int a else int a - 2 ^ N)"

(* The value of a pattern read with signedness [sx]. *)
definition sval :: "sp_sx \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "sval sx N a = (case sx of isabelle_reference_output_wasm2.U \<Rightarrow> int a
                   | isabelle_reference_output_wasm2.S \<Rightarrow> sv N a)"

lemma fun_signed_eq: "fun_signed_underscore N a v \<Longrightarrow> v = sv N a"
  by (auto elim!: fun_signed_underscore.cases simp: sv_def)

lemma fun_inv_signed_eq: "fun_inv_signed_underscore N r v \<Longrightarrow>
  - (2 ^ (N - 1)) \<le> r \<and> r < 2 ^ (N - 1) \<and> v = nat (if 0 \<le> r then r else r + 2 ^ N)"
  by (auto elim!: fun_inv_signed_underscore.cases)

lemma fun_ilt_eq: "fun_ilt_underscore N sx i j r \<Longrightarrow>
  r = mk_uN (res_bool (sval sx N (un i) < sval sx N (un j)))"
  by (auto elim!: fun_ilt_underscore.cases dest!: fun_signed_eq simp: sval_def)

lemma fun_igt_eq: "fun_igt_underscore N sx i j r \<Longrightarrow>
  r = mk_uN (res_bool (sval sx N (un j) < sval sx N (un i)))"
  by (auto elim!: fun_igt_underscore.cases dest!: fun_signed_eq simp: sval_def)

lemma fun_ile_eq: "fun_ile_underscore N sx i j r \<Longrightarrow>
  r = mk_uN (res_bool (sval sx N (un i) \<le> sval sx N (un j)))"
  by (auto elim!: fun_ile_underscore.cases dest!: fun_signed_eq simp: sval_def)

lemma fun_ige_eq: "fun_ige_underscore N sx i j r \<Longrightarrow>
  r = mk_uN (res_bool (sval sx N (un j) \<le> sval sx N (un i)))"
  by (auto elim!: fun_ige_underscore.cases dest!: fun_signed_eq simp: sval_def)

lemma trunc_nat_div: "trunc (rat_of_nat a / rat_of_nat b) = int (a div b)"
  by (simp add: trunc floor_divide_of_nat_eq)

lemma trunc_of_int: "trunc (rat_of_int k) = k"
  by (simp add: trunc)

(* WasmCert's [trunc] of a quotient is signed division (truncation towards zero). *)
lemma trunc_sdiv: "trunc (rat_of_int a / rat_of_int b) = a sdiv b"
proof (cases "b = 0")
  case True then show ?thesis by (simp add: trunc sdiv_int_div_0)
next
  case False then show ?thesis by (simp add: I32.sdiv_trunc)
qed

(* The type-safety proof's axiom [truncz_spec] (../isabelle/Axioms.thy) and this
   theory's [truncz_def] say the same: a function on [rat] agrees with signed
   division on quotients exactly when it is [trunc]. *)
lemma truncz_spec_iff_trunc:
  fixes f :: "rat \<Rightarrow> int"
  shows "(\<forall>a b. f (rat_of_int a / rat_of_int b) = a sdiv b) \<longleftrightarrow> (\<forall>q. f q = trunc q)"
proof
  assume h: "\<forall>a b. f (rat_of_int a / rat_of_int b) = a sdiv b"
  show "\<forall>q. f q = trunc q"
  proof
    fix q :: rat
    obtain a b where "quotient_of q = (a, b)" by (cases "quotient_of q")
    then have q: "q = rat_of_int a / rat_of_int b" by (rule quotient_of_div)
    show "f q = trunc q" using h q by (simp add: trunc_sdiv)
  qed
next
  assume "\<forall>q. f q = trunc q"
  then show "\<forall>a b. f (rat_of_int a / rat_of_int b) = a sdiv b" by (simp add: trunc_sdiv)
qed

corollary (in builtins) truncz_spec: "truncz (rat_of_int a / rat_of_int b) = a sdiv b"
  by (simp add: truncz_def trunc_sdiv)

lemma (in builtins) fun_idiv_u:
  "fun_idiv_underscore N isabelle_reference_output_wasm2.U i j r \<Longrightarrow> un j \<noteq> 0 \<Longrightarrow>
   r = Some (mk_uN (un i div un j))"
  by (auto elim!: fun_idiv_underscore.cases simp: truncz_def trunc_nat_div)

lemma (in builtins) fun_irem_u:
  "fun_irem_underscore N isabelle_reference_output_wasm2.U i j r \<Longrightarrow> un j \<noteq> 0 \<Longrightarrow>
   r = Some (mk_uN (un i mod un j))"
  by (auto elim!: fun_irem_underscore.cases simp: truncz_def trunc_nat_div nat_minus_mult_div)

(* Signed division: no result when the quotient overflows, otherwise the
   truncated quotient encoded back. *)
lemma (in builtins) fun_idiv_s:
  assumes "fun_idiv_underscore N isabelle_reference_output_wasm2.S i j r" "un j \<noteq> 0"
  shows "(r = None \<and> rat_of_int (sv N (un i)) / rat_of_int (sv N (un j)) = 2 ^ (N - 1)) \<or>
         (\<exists>v. r = Some (mk_uN v) \<and>
            fun_inv_signed_underscore N (trunc (rat_of_int (sv N (un i)) / rat_of_int (sv N (un j)))) v)"
  using assms by (auto elim!: fun_idiv_underscore.cases dest!: fun_signed_eq simp: truncz_def)

lemma (in builtins) fun_irem_s:
  assumes "fun_irem_underscore N isabelle_reference_output_wasm2.S i j r" "un j \<noteq> 0"
  shows "\<exists>v. r = Some (mk_uN v) \<and>
     fun_inv_signed_underscore N (sv N (un i) - sv N (un j) *
       trunc (rat_of_int (sv N (un i)) / rat_of_int (sv N (un j)))) v"
  using assms by (auto elim!: fun_irem_underscore.cases dest!: fun_signed_eq simp: truncz_def)

section \<open>WasmCert's integer operations on translated numbers\<close>

(* WasmCert specifies its signed operations with [signed] and [signed_inv]
   ([wasm_int] class); the following hold for any instance. *)
lemma rep_int_s_inv:
  "fun_inv_signed_underscore LENGTH('a) x v \<Longrightarrow> (rep_int_s x :: 'a::wasm_int) = int_of_nat v"
  by (drule fun_inv_signed_eq) (simp add: signed_inv)

lemma div_s_generic:
  fixes c1 c2 :: "'a::wasm_int"
  assumes "abs_int_s c1 = sv LENGTH('a) a" "abs_int_s c2 = sv LENGTH('a) b" "c2 \<noteq> 0"
    and "(r = None \<and> rat_of_int (sv LENGTH('a) a) / rat_of_int (sv LENGTH('a) b) = 2 ^ (LENGTH('a) - 1)) \<or>
         (\<exists>v. r = Some (mk_uN v) \<and>
            fun_inv_signed_underscore LENGTH('a) (trunc (rat_of_int (sv LENGTH('a) a) / rat_of_int (sv LENGTH('a) b))) v)"
  shows "int_div_s c1 c2 = map_option (\<lambda>u. int_of_nat (un u)) r"
  using assms(4)
proof
  assume "r = None \<and> rat_of_int (sv LENGTH('a) a) / rat_of_int (sv LENGTH('a) b) = 2 ^ (LENGTH('a) - 1)"
  then show ?thesis using assms(1-3) by (simp add: wasm_int_class.div_s_nrep)
next
  let ?q = "rat_of_int (sv LENGTH('a) a) / rat_of_int (sv LENGTH('a) b)"
  assume "\<exists>v. r = Some (mk_uN v) \<and> fun_inv_signed_underscore LENGTH('a) (trunc ?q) v"
  then obtain v where v: "r = Some (mk_uN v)" "fun_inv_signed_underscore LENGTH('a) (trunc ?q) v"
    by blast
  have "?q \<noteq> 2 ^ (LENGTH('a) - 1)"
  proof
    assume "?q = 2 ^ (LENGTH('a) - 1)"
    then have "trunc ?q = 2 ^ (LENGTH('a) - 1)"
      using trunc_of_int[of "2 ^ (LENGTH('a) - 1)"] by simp
    then show False using fun_inv_signed_eq[OF v(2)] by simp
  qed
  then show ?thesis using assms(1-3) v by (simp add: wasm_int_class.div_s rep_int_s_inv)
qed

lemma rem_s_generic:
  fixes c1 c2 :: "'a::wasm_int"
  assumes "abs_int_s c1 = sv LENGTH('a) a" "abs_int_s c2 = sv LENGTH('a) b" "c2 \<noteq> 0"
    and "\<exists>v. r = Some (mk_uN v) \<and> fun_inv_signed_underscore LENGTH('a) (sv LENGTH('a) a - sv LENGTH('a) b *
       trunc (rat_of_int (sv LENGTH('a) a) / rat_of_int (sv LENGTH('a) b))) v"
  shows "int_rem_s c1 c2 = map_option (\<lambda>u. int_of_nat (un u)) r"
  using assms by (auto simp: wasm_int_class.rem_s rep_int_s_inv)

lemma abs_int_s_tr32: "un u < 2 ^ 32 \<Longrightarrow> abs_int_s (tr_i32 u) = sv LENGTH(Wasm_Ast.i32) (un u)"
  by (simp add: tr_i32_def nat_of_int_i32_def map_fun_def signed_def sv_def uint_nat unat_of_nat_lt)

lemma abs_int_s_tr64: "un u < 2 ^ 64 \<Longrightarrow> abs_int_s (tr_i64 u) = sv LENGTH(Wasm_Ast.i64) (un u)"
  by (simp add: tr_i64_def nat_of_int_i64_def map_fun_def signed_def sv_def uint_nat unat_of_nat_lt)

lemma int_of_nat_tr32: "(int_of_nat (un u) :: Wasm_Ast.i32) = tr_i32 u"
  by (simp add: int_of_nat_i32_def map_fun_def tr_i32_def)

lemma int_of_nat_tr64: "(int_of_nat (un u) :: Wasm_Ast.i64) = tr_i64 u"
  by (simp add: int_of_nat_i64_def map_fun_def tr_i64_def)

lemma tr_i32_eq_0: "un u < 2 ^ 32 \<Longrightarrow> tr_i32 u = 0 \<longleftrightarrow> un u = 0"
  by (simp add: tr_i32_def zero_i32_def Abs_i32_inject of_nat_word_eq_0)

lemma tr_i64_eq_0: "un u < 2 ^ 64 \<Longrightarrow> tr_i64 u = 0 \<longleftrightarrow> un u = 0"
  by (simp add: tr_i64_def zero_i64_def Abs_i64_inject of_nat_word_eq_0)

lemma un_inj: "un i = un j \<longleftrightarrow> i = j"
  by (cases i, cases j) simp

lemmas wc_int_defs = app_binop_def app_binop_i_v_def app_binop_i_def app_relop_def app_relop_i_v_def
  app_relop_i_def app_testop_def app_testop_i_def map_fun_def
  int_div_u_i32_def int_div_u_i64_def I32.int_div_u_def I64.int_div_u_def
  int_rem_u_i32_def int_rem_u_i64_def I32.int_rem_u_def I64.int_rem_u_def
  int_eq_i32_def int_eq_i64_def I32.int_eq_def I64.int_eq_def
  int_lt_u_i32_def int_lt_u_i64_def I32.int_lt_u_def I64.int_lt_u_def
  int_gt_u_i32_def int_gt_u_i64_def I32.int_gt_u_def I64.int_gt_u_def
  int_le_u_i32_def int_le_u_i64_def I32.int_le_u_def I64.int_le_u_def
  int_ge_u_i32_def int_ge_u_i64_def I32.int_ge_u_def I64.int_ge_u_def
  int_eqz_i32_def int_eqz_i64_def I32.int_eqz_def I64.int_eqz_def zero_i32_def zero_i64_def

lemma wc_div_u: "iok t i \<Longrightarrow> iok t j \<Longrightarrow>
  app_binop (Binop_i (Div Wasm_Ast.U)) (ival t i) (ival t j) =
    (if un j = 0 then None else Some (ival t (mk_uN (un i div un j))))"
  by (cases t) (auto simp: wc_int_defs tr_i32_def tr_i64_def of_nat_word_eq_0 of_nat_word_div)

lemma wc_rem_u: "iok t i \<Longrightarrow> iok t j \<Longrightarrow>
  app_binop (Binop_i (Rem Wasm_Ast.U)) (ival t i) (ival t j) =
    (if un j = 0 then None else Some (ival t (mk_uN (un i mod un j))))"
  by (cases t) (auto simp: wc_int_defs tr_i32_def tr_i64_def of_nat_word_eq_0 of_nat_word_mod)

lemma wc_testop: "iok t i \<Longrightarrow> app_testop Eqz (ival t i) = ConstInt32 (wasm_bool (un i = 0))"
  by (cases t) (auto simp: wc_int_defs tr_i32_def tr_i64_def Abs_i32_inject Abs_i64_inject
      of_nat_word_eq_0)

lemmas wc_binop_defs = app_binop_def app_binop_i_v_def app_binop_i_def

lemma (in builtins) div_s_case:
  assumes f: "fun_idiv_underscore (isz t) isabelle_reference_output_wasm2.S i j r"
    and ii: "iok t i" "iok t j" and z: "un j = 0 \<Longrightarrow> r = None"
  shows "app_binop (Binop_i (Div Wasm_Ast.S)) (ival t i) (ival t j) = map_option (ival t) r"
proof (cases "un j = 0")
  case True
  then show ?thesis using z ii
    by (cases t) (simp_all add: wc_binop_defs tr_i32_eq_0 tr_i64_eq_0 wasm_int_class.div_s_0)
next
  case False
  note o = fun_idiv_s[OF f False]
  show ?thesis
  proof (cases t)
    case Inn_I32
    have "int_div_s (tr_i32 i) (tr_i32 j) = map_option (\<lambda>u. int_of_nat (un u)) r"
      by (rule div_s_generic) (use o ii False Inn_I32 in \<open>simp_all add: abs_int_s_tr32 tr_i32_eq_0\<close>)
    then show ?thesis using Inn_I32
      by (simp add: wc_binop_defs option.map_comp comp_def int_of_nat_tr32 ival_def[abs_def])
  next
    case Inn_I64
    have "int_div_s (tr_i64 i) (tr_i64 j) = map_option (\<lambda>u. int_of_nat (un u)) r"
      by (rule div_s_generic) (use o ii False Inn_I64 in \<open>simp_all add: abs_int_s_tr64 tr_i64_eq_0\<close>)
    then show ?thesis using Inn_I64
      by (simp add: wc_binop_defs option.map_comp comp_def int_of_nat_tr64 ival_def[abs_def])
  qed
qed

lemma (in builtins) rem_s_case:
  assumes f: "fun_irem_underscore (isz t) isabelle_reference_output_wasm2.S i j r"
    and ii: "iok t i" "iok t j" and z: "un j = 0 \<Longrightarrow> r = None"
  shows "app_binop (Binop_i (Rem Wasm_Ast.S)) (ival t i) (ival t j) = map_option (ival t) r"
proof (cases "un j = 0")
  case True
  then show ?thesis using z ii
    by (cases t) (simp_all add: wc_binop_defs tr_i32_eq_0 tr_i64_eq_0 wasm_int_class.rem_s_0)
next
  case False
  note o = fun_irem_s[OF f False]
  show ?thesis
  proof (cases t)
    case Inn_I32
    have "int_rem_s (tr_i32 i) (tr_i32 j) = map_option (\<lambda>u. int_of_nat (un u)) r"
      by (rule rem_s_generic) (use o ii False Inn_I32 in \<open>simp_all add: abs_int_s_tr32 tr_i32_eq_0\<close>)
    then show ?thesis using Inn_I32
      by (simp add: wc_binop_defs option.map_comp comp_def int_of_nat_tr32 ival_def[abs_def])
  next
    case Inn_I64
    have "int_rem_s (tr_i64 i) (tr_i64 j) = map_option (\<lambda>u. int_of_nat (un u)) r"
      by (rule rem_s_generic) (use o ii False Inn_I64 in \<open>simp_all add: abs_int_s_tr64 tr_i64_eq_0\<close>)
    then show ?thesis using Inn_I64
      by (simp add: wc_binop_defs option.map_comp comp_def int_of_nat_tr64 ival_def[abs_def])
  qed
qed

(* SpecTec's integer comparisons, as functions. *)
fun irel :: "nat \<Rightarrow> relop_Inn \<Rightarrow> uN \<Rightarrow> uN \<Rightarrow> bool" where
  "irel N EQ i j = (i = j)"
| "irel N NE i j = (i \<noteq> j)"
| "irel N (LT sx) i j = (sval sx N (un i) < sval sx N (un j))"
| "irel N (GT sx) i j = (sval sx N (un j) < sval sx N (un i))"
| "irel N (LE sx) i j = (sval sx N (un i) \<le> sval sx N (un j))"
| "irel N (GE sx) i j = (sval sx N (un j) \<le> sval sx N (un i))"

lemmas wc_relop_s_defs = app_relop_def app_relop_i_v_def app_relop_i_def
  wasm_int_class.ilt_s wasm_int_class.igt_s wasm_int_class.ile_s wasm_int_class.ige_s

lemma wc_relop:
  assumes "iok t i" "iok t j"
  shows "app_relop (tr_relop (mk_relop__0 t op)) (ival t i) (ival t j) =
           ConstInt32 (wasm_bool (irel (isz t) op i j))"
proof (cases op)
  case (LT sx) then show ?thesis using assms
    by (cases t; cases sx)
       (auto simp: wc_int_defs wc_relop_s_defs tr_i32_def tr_i64_def sval_def of_nat_word_less
          abs_int_s_tr32[unfolded tr_i32_def] abs_int_s_tr64[unfolded tr_i64_def])
next
  case (GT sx) then show ?thesis using assms
    by (cases t; cases sx)
       (auto simp: wc_int_defs wc_relop_s_defs tr_i32_def tr_i64_def sval_def of_nat_word_less
          abs_int_s_tr32[unfolded tr_i32_def] abs_int_s_tr64[unfolded tr_i64_def])
next
  case (LE sx) then show ?thesis using assms
    by (cases t; cases sx)
       (auto simp: wc_int_defs wc_relop_s_defs tr_i32_def tr_i64_def sval_def of_nat_word_le
          abs_int_s_tr32[unfolded tr_i32_def] abs_int_s_tr64[unfolded tr_i64_def])
next
  case (GE sx) then show ?thesis using assms
    by (cases t; cases sx)
       (auto simp: wc_int_defs wc_relop_s_defs tr_i32_def tr_i64_def sval_def of_nat_word_le
          abs_int_s_tr32[unfolded tr_i32_def] abs_int_s_tr64[unfolded tr_i64_def])
qed (use assms in \<open>cases t; auto simp: wc_int_defs tr_i32_def tr_i64_def of_nat_word_inj un_inj\<close>)+

section \<open>Every WasmCert number is a translated SpecTec number\<close>

lemma fmag_of_bits_Some: "\<exists>y. fmag_of_bits M E b = Some y"
  by (auto simp: fmag_of_bits_def Let_def)

lemma fN_of_bits_Some: "\<exists>y. fN_of_bits M E b = Some y"
  by (auto simp: fN_of_bits_def fmag_of_bits_def Let_def)

lemma fmag_bits_of_bits:
  assumes "fmag_of_bits M E b = Some y"
  shows "fmag_bits M E y = b"
proof -
  define e m where "e = b div 2 ^ M" and "m = b mod 2 ^ M"
  have b: "b = e * 2 ^ M + m" unfolding e_def m_def by (rule div_mult_mod_eq[symmetric])
  show ?thesis
  proof (cases "e = 0")
    case True
    then have "y = SUBNORM m" using assms by (simp add: fmag_of_bits_def Let_def e_def m_def)
    then show ?thesis using b True by simp
  next
    case e0: False
    show ?thesis
    proof (cases "e = 2 ^ E - 1")
      case True
      then have "y = (if m = 0 then res_INF else NAN m)"
        using assms e0 by (auto simp: fmag_of_bits_def Let_def e_def m_def split: if_split_asm)
      then show ?thesis using b True by auto
    next
      case False
      then have "y = NORM m (int e - int (2 ^ (E - 1) - 1))"
        using assms e0 by (simp add: fmag_of_bits_def Let_def e_def m_def)
      then show ?thesis using b by simp
    qed
  qed
qed

lemma fN_bits_of_bits:
  assumes "fN_of_bits M E b = Some y" "b < 2 ^ Suc (M + E)"
  shows "fN_bits M E y = b"
proof -
  have d: "b div 2 ^ (M + E) < 2"
    using assms(2) by (simp add: less_mult_imp_div_less mult.commute)
  obtain z where z: "fmag_of_bits M E (b mod 2 ^ (M + E)) = Some z"
      "y = (if b div 2 ^ (M + E) = 0 then POS z else NEG z)"
    using assms(1) by (auto simp: fN_of_bits_def)
  have zb: "fmag_bits M E z = b mod 2 ^ (M + E)" by (rule fmag_bits_of_bits[OF z(1)])
  have "b = b div 2 ^ (M + E) * 2 ^ (M + E) + b mod 2 ^ (M + E)" by (rule div_mult_mod_eq[symmetric])
  then show ?thesis using zb z(2) d by (auto simp: less_2_cases_iff)
qed

lemma nrep_float[simp]: "nrep F32 (ConstFloat32 v)" "nrep F64 (ConstFloat64 v')"
proof -
  obtain y where y: "fN_of_bits 23 8 (unat (Rep_f32 v)) = Some y"
    using fN_of_bits_Some by blast
  have "wf_fN 32 y" by (rule fN_of_bits_wf[of 32 23 8 "unat (Rep_f32 v)" y]) (simp_all add: y)
  moreover have "fN_bits 23 8 y = unat (Rep_f32 v)"
    by (rule fN_bits_of_bits[OF y]) (use unat_lt2p[of "Rep_f32 v"] in simp)
  then have "tr_f32 y = v" by (simp add: tr_f32_def Rep_f32_inverse)
  ultimately show "nrep F32 (ConstFloat32 v)"
    unfolding nrep_def by (intro exI[of _ "mk_num__1 Fnn_F32 y"]) simp
next
  obtain y where y: "fN_of_bits 52 11 (unat (Rep_f64 v')) = Some y"
    using fN_of_bits_Some by blast
  have "wf_fN 64 y" by (rule fN_of_bits_wf[of 64 52 11 "unat (Rep_f64 v')" y]) (simp_all add: y)
  moreover have "fN_bits 52 11 y = unat (Rep_f64 v')"
    by (rule fN_bits_of_bits[OF y]) (use unat_lt2p[of "Rep_f64 v'"] in simp)
  then have "tr_f64 y = v'" by (simp add: tr_f64_def Rep_f64_inverse)
  ultimately show "nrep F64 (ConstFloat64 v')"
    unfolding nrep_def by (intro exI[of _ "mk_num__1 Fnn_F64 y"]) simp
qed

lemma nrep_typeof: "typeof_num v = tr_numtype nt \<Longrightarrow> nrep nt v"
  by (cases v; cases nt) (simp_all add: typeof_num_def)

lemma typeof_tr_num: "wf_num_underscore nt c \<Longrightarrow> typeof_num (tr_num c) = tr_numtype nt"
  by (cases c; rename_tac t x; case_tac t) (auto simp: typeof_num_def)

lemma typeof_app_unop: "typeof_num (app_unop op v) = typeof_num v"
  by (cases op; cases v)
     (simp_all add: app_unop_def app_unop_i_v_def app_unop_f_v_def app_extend_s_def
        wasm_deserialise_num_def typeof_num_def split: t_num.splits)

lemma typeof_app_binop: "app_binop op v1 v2 = Some v \<Longrightarrow> typeof_num v = typeof_num v1"
  by (cases op; cases v1; cases v2)
     (auto simp: app_binop_def app_binop_i_v_def app_binop_f_v_def typeof_num_def)

lemma typeof_cvt: "cvt t s v = Some v' \<Longrightarrow> typeof_num v' = t"
  by (auto simp: cvt_def typeof_num_def split: t_num.splits option.splits)

lemma typeof_reinterpret: "typeof_num (wasm_reinterpret t v) = t"
  by (cases t) (simp_all add: wasm_reinterpret_def wasm_deserialise_num_def typeof_num_def)

section \<open>Numeric operators\<close>

(* Division or remainder by zero.  SpecTec's [idiv_] and [irem_] have a clause
   for a zero divisor (no result) and a general clause, which also applies to a
   zero divisor ([x / 0 = 0] in [rat]), so SpecTec may produce a value where
   WasmCert traps.  The Rocq bridge has the same disagreement. *)
definition divzero :: "binop_underscore \<Rightarrow> num_underscore \<Rightarrow> bool" where
  "divzero op c2 \<longleftrightarrow>
     (\<exists>t sx. op = mk_binop__0 t (DIV sx) \<or> op = mk_binop__0 t (REM sx)) \<and>
     (\<exists>t. c2 = mk_num__0 t (mk_uN 0))"

theorem testop_tr:
  assumes "wf_num_underscore nt c1" "fun_testop_underscore nt op c1 (Some c)"
  shows "tr_num c = app_testop Eqz (tr_num c1)"
  using assms(2,1)
  by (cases rule: fun_testop_underscore.cases)
     (auto simp: wc_testop[of Inn_I32, simplified] wc_testop[of Inn_I64, simplified] tr_i32_res_bool)

lemma fun_relop_int:
  assumes "fun_relop_underscore nt (mk_relop__0 t op) c1 c2 (Some c)"
  shows "\<exists>i j. c1 = mk_num__0 t i \<and> c2 = mk_num__0 t j \<and> nt = numtype_Inn t \<and>
           c = mk_num__0 Inn_I32 (mk_uN (res_bool (irel (isz t) op i j)))"
  using assms
  by (cases rule: fun_relop_underscore.cases) (auto dest!: fun_ilt_eq fun_igt_eq fun_ile_eq fun_ige_eq)

lemma fun_relop_float:
  assumes "fun_relop_underscore nt (mk_relop__1 t op) c1 c2 (Some c)"
  shows "\<exists>x y. c1 = mk_num__1 t x \<and> c2 = mk_num__1 t y \<and> nt = numtype_Fnn t \<and>
           c = mk_num__0 Inn_I32 (frel op (fsz t) x y)"
  using assms by (cases rule: fun_relop_underscore.cases) auto

theorem (in builtins) relop_tr:
  assumes w: "wf_num_underscore nt c1" "wf_num_underscore nt c2"
    and f: "fun_relop_underscore nt op c1 c2 (Some c)"
  shows "tr_num c = app_relop (tr_relop op) (tr_num c1) (tr_num c2)"
proof (cases op)
  case (mk_relop__0 t rop)
  with f obtain i j where c: "c1 = mk_num__0 t i" "c2 = mk_num__0 t j" "nt = numtype_Inn t"
      "c = mk_num__0 Inn_I32 (mk_uN (res_bool (irel (isz t) rop i j)))"
    using fun_relop_int by blast
  have "app_relop (tr_relop (mk_relop__0 t rop)) (ival t i) (ival t j) =
          ConstInt32 (wasm_bool (irel (isz t) rop i j))"
    by (rule wc_relop) (use w c in auto)
  then show ?thesis using c mk_relop__0 by (simp add: ival_def tr_i32_res_bool)
next
  case (mk_relop__1 t rop)
  with f obtain x y where c: "c1 = mk_num__1 t x" "c2 = mk_num__1 t y" "nt = numtype_Fnn t"
      "c = mk_num__0 Inn_I32 (frel rop (fsz t) x y)"
    using fun_relop_float by blast
  have "ival Inn_I32 (frel rop (fsz t) x y) = app_relop (tr_relop (mk_relop__1 t rop)) (fval t x) (fval t y)"
    by (rule frel_tr) (use w c in auto)
  then show ?thesis using c mk_relop__1 by (simp add: ival_def fval_def)
qed

lemma (in builtins) div_case:
  assumes "fun_idiv_underscore (isz t) sx i j r" "iok t i" "iok t j"
    and "un j = 0 \<Longrightarrow> r = None"
  shows "app_binop (Binop_i (Div (tr_sx sx))) (ival t i) (ival t j) = map_option (ival t) r"
proof (cases sx)
  case U
  show ?thesis
  proof (cases "un j = 0")
    case True then show ?thesis using assms U by (simp add: wc_div_u)
  next
    case False
    then have "r = Some (mk_uN (un i div un j))" using fun_idiv_u assms U by blast
    then show ?thesis using assms U False by (simp add: wc_div_u)
  qed
next
  case S then show ?thesis using div_s_case assms by simp
qed

lemma (in builtins) rem_case:
  assumes "fun_irem_underscore (isz t) sx i j r" "iok t i" "iok t j"
    and "un j = 0 \<Longrightarrow> r = None"
  shows "app_binop (Binop_i (Rem (tr_sx sx))) (ival t i) (ival t j) = map_option (ival t) r"
proof (cases sx)
  case U
  show ?thesis
  proof (cases "un j = 0")
    case True then show ?thesis using assms U by (simp add: wc_rem_u)
  next
    case False
    then have "r = Some (mk_uN (un i mod un j))" using fun_irem_u assms U by blast
    then show ?thesis using assms U False by (simp add: wc_rem_u)
  qed
next
  case S then show ?thesis using rem_s_case assms by simp
qed

lemma list_underscore_Nil[simp]: "list_underscore x = [] \<longleftrightarrow> x = None"
  by (cases x) simp_all

lemma map_tr_num_list:"map tr_num (list_underscore (map_option (mk_num__0 t) r)) = olist (map_option (ival t) r)"
  by (cases r) (simp_all add: ival_def)

lemma fun_binop_int_args:
  assumes "fun_binop_underscore nt (mk_binop__0 t bop) c1 c2 (Some cs)"
  shows "\<exists>i j. c1 = mk_num__0 t i \<and> c2 = mk_num__0 t j \<and> nt = numtype_Inn t"
  using assms by (cases rule: fun_binop_underscore.cases) auto

theorem (in builtins) binop_int_tr:
  assumes f: "fun_binop_underscore nt (mk_binop__0 t bop) c1 c2 (Some cs)"
    and w: "wf_num_underscore nt c1" "wf_num_underscore nt c2"
    and dz: "divzero (mk_binop__0 t bop) c2 \<Longrightarrow> cs = []"
  shows "map tr_num cs = olist (app_binop (tr_binop (mk_binop__0 t bop)) (tr_num c1) (tr_num c2))"
proof -
  obtain i j where c: "c1 = mk_num__0 t i" "c2 = mk_num__0 t j" "nt = numtype_Inn t"
    using fun_binop_int_args[OF f] by blast
  have ii: "iok t i" "iok t j" using w c by auto
  have dz': "(\<exists>sx. bop = DIV sx \<or> bop = REM sx) \<Longrightarrow> un j = 0 \<Longrightarrow> cs = []"
    using dz c by (cases j) (auto simp: divzero_def)
  show ?thesis
  proof (cases bop)
    case ADD
    with f c have "cs = [mk_num__0 t (iadd_underscore (isz t) i j)]"
      by (cases t) (auto elim: fun_binop_underscore.cases)
    with iadd_tr[OF ii] ADD c show ?thesis by (simp add: ival_def)
  next
    case SUB
    with f c have "cs = [mk_num__0 t (isub_underscore (isz t) i j)]"
      by (cases t) (auto elim: fun_binop_underscore.cases)
    with isub_tr[OF ii] SUB c show ?thesis by (simp add: ival_def)
  next
    case MUL
    with f c have "cs = [mk_num__0 t (imul_underscore (isz t) i j)]"
      by (cases t) (auto elim: fun_binop_underscore.cases)
    with imul_tr[OF ii] MUL c show ?thesis by (simp add: ival_def)
  next
    case (DIV sx)
    with f c obtain r where r: "fun_idiv_underscore (isz t) sx i j r"
        "cs = list_underscore (map_option (mk_num__0 t) r)"
      by (cases t) (auto elim: fun_binop_underscore.cases)
    have "app_binop (Binop_i (Div (tr_sx sx))) (ival t i) (ival t j) = map_option (ival t) r"
      by (rule div_case[OF r(1) ii]) (use dz' r(2) DIV in \<open>auto split: option.splits\<close>)
    then show ?thesis using r(2) DIV c by (simp add: map_tr_num_list ival_def)
  next
    case (REM sx)
    with f c obtain r where r: "fun_irem_underscore (isz t) sx i j r"
        "cs = list_underscore (map_option (mk_num__0 t) r)"
      by (cases t) (auto elim: fun_binop_underscore.cases)
    have "app_binop (Binop_i (Rem (tr_sx sx))) (ival t i) (ival t j) = map_option (ival t) r"
      by (rule rem_case[OF r(1) ii]) (use dz' r(2) REM in \<open>auto split: option.splits\<close>)
    then show ?thesis using r(2) REM c by (simp add: map_tr_num_list ival_def)
  next
    case AND
    with f c have "cs = [mk_num__0 t (iand_underscore (isz t) i j)]"
      by (cases t) (auto elim: fun_binop_underscore.cases)
    with iand_tr[OF ii] AND c show ?thesis by (simp add: ival_def)
  next
    case OR
    with f c have "cs = [mk_num__0 t (ior_underscore (isz t) i j)]"
      by (cases t) (auto elim: fun_binop_underscore.cases)
    with ior_tr[OF ii] OR c show ?thesis by (simp add: ival_def)
  next
    case XOR
    with f c have "cs = [mk_num__0 t (ixor_underscore (isz t) i j)]"
      by (cases t) (auto elim: fun_binop_underscore.cases)
    with ixor_tr[OF ii] XOR c show ?thesis by (simp add: ival_def)
  next
    case SHL
    with f c have "cs = [mk_num__0 t (ishl_underscore (isz t) i j)]"
      by (cases t) (auto elim: fun_binop_underscore.cases)
    with ishl_tr[OF ii] SHL c show ?thesis by (simp add: ival_def)
  next
    case (SHR sx)
    with f c have "cs = [mk_num__0 t (ishr_underscore (isz t) sx i j)]"
      by (cases t) (auto elim: fun_binop_underscore.cases)
    with ishr_tr[OF ii] SHR c show ?thesis by (simp add: ival_def)
  next
    case ROTL
    with f c have "cs = [mk_num__0 t (irotl_underscore (isz t) i j)]"
      by (cases t) (auto elim: fun_binop_underscore.cases)
    with irotl_tr[OF ii] ROTL c show ?thesis by (simp add: ival_def)
  next
    case ROTR
    with f c have "cs = [mk_num__0 t (irotr_underscore (isz t) i j)]"
      by (cases t) (auto elim: fun_binop_underscore.cases)
    with irotr_tr[OF ii] ROTR c show ?thesis by (simp add: ival_def)
  qed
qed

lemma fun_binop_float:
  assumes "fun_binop_underscore nt (mk_binop__1 t fop) c1 c2 (Some cs)"
  shows "\<exists>x y. c1 = mk_num__1 t x \<and> c2 = mk_num__1 t y \<and> nt = numtype_Fnn t \<and>
           cs = map (mk_num__1 t) (fun2 fop (fsz t) x y)"
  using assms by (cases t; cases fop) (auto elim: fun_binop_underscore.cases)

lemma app_binop_float_some: "\<exists>v. app_binop (tr_binop (mk_binop__1 t fop)) (fval t x) (fval t y) = Some v"
  by (cases t; cases fop) (simp_all add: app_binop_def app_binop_f_v_def app_binop_f_def)

theorem (in builtins) binop_float_tr:
  assumes f: "fun_binop_underscore nt (mk_binop__1 t fop) c1 c2 (Some cs)"
    and w: "wf_num_underscore nt c1" "wf_num_underscore nt c2"
  shows "map tr_num cs = olist (app_binop (tr_binop (mk_binop__1 t fop)) (tr_num c1) (tr_num c2))"
proof -
  obtain x y where c: "c1 = mk_num__1 t x" "c2 = mk_num__1 t y" "nt = numtype_Fnn t"
      "cs = map (mk_num__1 t) (fun2 fop (fsz t) x y)"
    using fun_binop_float[OF f] by blast
  obtain v where v: "app_binop (tr_binop (mk_binop__1 t fop)) (fval t x) (fval t y) = Some v"
    using app_binop_float_some by blast
  have rv: "nrep (numtype_Fnn t) v"
    using typeof_app_binop[OF v] typeof_tr_num[OF w(1)] c by (intro nrep_typeof) (simp add: fval_def)
  have "map (fval t) (fun2 fop (fsz t) x y) = [v]"
    by (rule fun2_tr[OF _ _ v rv]) (use w c in \<open>auto simp: fval_def\<close>)
  then show ?thesis using c v by (simp add: fval_def[abs_def] comp_def)
qed

(* Every numeric step of SpecTec agrees with WasmCert, except a division by zero
   that SpecTec turns into a value. *)
theorem (in builtins) binop_tr:
  assumes "fun_binop_underscore nt op c1 c2 (Some cs)"
    and "wf_num_underscore nt c1" "wf_num_underscore nt c2"
    and "divzero op c2 \<Longrightarrow> cs = []"
  shows "map tr_num cs = olist (app_binop (tr_binop op) (tr_num c1) (tr_num c2))"
  using assms by (cases op) (auto intro: binop_int_tr binop_float_tr)

section \<open>Conversions\<close>

lemma of_nat_2p_len_word: "(of_nat (2 ^ LENGTH('a)) :: 'a::len word) = 0"
  by (simp add: word_of_nat_eq_iff take_bit_eq_mod)

lemma msb_of_nat: "a < 2 ^ LENGTH('a) \<Longrightarrow> msb (of_nat a :: 'a::len word) \<longleftrightarrow> 2 ^ (LENGTH('a) - 1) \<le> a"
  by (simp add: msb_big word_le_nat_alt unat_of_nat_lt)

lemma sint_of_nat_neg: "a < 2 ^ LENGTH('a) \<Longrightarrow> 2 ^ (LENGTH('a) - 1) \<le> a \<Longrightarrow>
   sint (of_nat a :: 'a::len word) = int a - 2 ^ LENGTH('a)"
  by (simp add: word_sint_msb_eq word_size msb_of_nat uint_nat unat_of_nat_lt)

(* Sign extension of a [LENGTH('c)]-bit number to [LENGTH('a)] bits, as SpecTec's
   [extend_] computes it on naturals. *)
lemma scast_of_nat:
  assumes "LENGTH('c::len) \<le> LENGTH('a::len)" "a < 2 ^ LENGTH('c)"
  shows "(scast (of_nat a :: 'c word) :: 'a word) =
     of_nat (if a < 2 ^ (LENGTH('c) - 1) then a else a + 2 ^ LENGTH('a) - 2 ^ LENGTH('c))"
proof (cases "a < 2 ^ (LENGTH('c) - 1)")
  case True then show ?thesis by (simp add: scast_eq int_eq_sint)
next
  case False
  have le: "(2::nat) ^ LENGTH('c) \<le> 2 ^ LENGTH('a)" using assms(1) by (simp add: power_increasing)
  have "sint (of_nat a :: 'c word) = int a - 2 ^ LENGTH('c)"
    using False assms(2) by (simp add: sint_of_nat_neg)
  then have "(scast (of_nat a :: 'c word) :: 'a word) = of_nat a - 2 ^ LENGTH('c)"
    by (simp add: scast_eq)
  also have "\<dots> = of_nat (a + 2 ^ LENGTH('a) - 2 ^ LENGTH('c))"
  proof -
    have "2 ^ LENGTH('c) \<le> a + 2 ^ LENGTH('a)" using le by linarith
    then have "(of_nat (a + 2 ^ LENGTH('a) - 2 ^ LENGTH('c)) :: 'a word) =
        of_nat a + of_nat (2 ^ LENGTH('a)) - of_nat (2 ^ LENGTH('c))"
      by (simp only: of_nat_diff of_nat_add)
    then show ?thesis by (simp add: of_nat_2p_len_word)
  qed
  finally show ?thesis using False by simp
qed

lemma ucast_of_nat: "(ucast (of_nat a :: 'c::len word) :: 'a::len word) = of_nat (a mod 2 ^ LENGTH('c))"
  by (metis unat_of_nat ucast_nat_def)

lemma (in builtins) extend_cvt:
  "un i < 2 ^ 32 \<Longrightarrow>
   cvt T_i64 (Some (Nonsat, tr_sx sx)) (ConstInt32 (tr_i32 i)) =
     Some (ConstInt64 (tr_i64 (extend__underscore 32 64 sx i)))"
  using scast_of_nat[where 'c=32 and 'a=64, of "un i"]
  by (cases sx)
     (simp_all add: cvt_def cvt_i64_def extend_def tr_i32_def tr_i64_def wasm_extend_u.abs_eq
        wasm_extend_s.abs_eq ucast_of_nat)

lemma (in builtins) wrap_cvt:
  "un i < 2 ^ 64 \<Longrightarrow>
   cvt T_i32 sat (ConstInt64 (tr_i64 i)) = Some (ConstInt32 (tr_i32 (wrap__underscore 64 32 i)))"
  by (simp add: cvt_def cvt_i32_def wrap_def tr_i32_def tr_i64_def wasm_wrap.abs_eq ucast_of_nat
      of_nat_mod_32)

(* WasmCert's conversion: [Convert] through [cvt], [Reinterpret] always succeeds. *)
definition wc_cvtop :: "numtype \<Rightarrow> cvtop__underscore \<Rightarrow> v_num \<Rightarrow> v_num option" where
  "wc_cvtop nt2 op v = (case fst (tr_cvtop op) of
      Convert \<Rightarrow> cvt (tr_numtype nt2) (snd (tr_cvtop op)) v
    | Reinterpret \<Rightarrow> Some (wasm_reinterpret (tr_numtype nt2) v))"

lemma fun_cvtop_ii:
  assumes "fun_cvtop__underscore nt1 nt2 (mk_cvtop___0 t1 t2 op) c1 (Some cs)"
    and "wf_cvtop__underscore nt1 nt2 (mk_cvtop___0 t1 t2 op)"
  shows "\<exists>i. c1 = mk_num__0 t1 i \<and> nt1 = numtype_Inn t1 \<and> nt2 = numtype_Inn t2 \<and>
    ((\<exists>sx. op = cvtop__Inn_1_Inn_2_EXTEND sx \<and> t1 = Inn_I32 \<and> t2 = Inn_I64 \<and>
           cs = [mk_num__0 Inn_I64 (extend__underscore 32 64 sx i)]) \<or>
     (op = WRAP \<and> t1 = Inn_I64 \<and> t2 = Inn_I32 \<and> cs = [mk_num__0 Inn_I32 (wrap__underscore 64 32 i)]))"
  using assms
  by (cases t1; cases t2; cases op)
     (auto elim!: wf_cvtop__underscore.cases wf_cvtop__Inn_1_Inn_2.cases fun_cvtop__underscore.cases)

lemma fun_cvtop_if:
  assumes "fun_cvtop__underscore nt1 nt2 (mk_cvtop___1 t1 t2 op) c1 (Some cs)"
    and "wf_cvtop__underscore nt1 nt2 (mk_cvtop___1 t1 t2 op)"
  shows "\<exists>i. c1 = mk_num__0 t1 i \<and> nt1 = numtype_Inn t1 \<and> nt2 = numtype_Fnn t2 \<and>
    ((\<exists>sx. op = CONVERT sx \<and> cs = [mk_num__1 t2 (convert__underscore (isz t1) (fsz t2) sx i)]) \<or>
     (op = REINTERPRET \<and> cs = [reinterpret__underscore nt1 nt2 c1]))"
  using assms
  by (cases t1; cases t2; cases op)
     (auto elim!: wf_cvtop__underscore.cases wf_cvtop__Inn_1_Fnn_2.cases fun_cvtop__underscore.cases)

lemma fun_cvtop_fi:
  assumes "fun_cvtop__underscore nt1 nt2 (mk_cvtop___2 t1 t2 op) c1 (Some cs)"
    and "wf_cvtop__underscore nt1 nt2 (mk_cvtop___2 t1 t2 op)"
  shows "\<exists>x. c1 = mk_num__1 t1 x \<and> nt1 = numtype_Fnn t1 \<and> nt2 = numtype_Inn t2 \<and>
    ((\<exists>sx. op = cvtop__Fnn_1_Inn_2_TRUNC sx \<and>
        cs = list_underscore (map_option (mk_num__0 t2) (trunc__underscore (fsz t1) (isz t2) sx x))) \<or>
     (\<exists>sx. op = TRUNC_SAT sx \<and>
        cs = list_underscore (map_option (mk_num__0 t2) (trunc_sat__underscore (fsz t1) (isz t2) sx x))) \<or>
     (op = cvtop__Fnn_1_Inn_2_REINTERPRET \<and> cs = [reinterpret__underscore nt1 nt2 c1]))"
  using assms
  by (cases t1; cases t2; cases op)
     (auto elim!: wf_cvtop__underscore.cases wf_cvtop__Fnn_1_Inn_2.cases fun_cvtop__underscore.cases)

lemma fun_cvtop_ff:
  assumes "fun_cvtop__underscore nt1 nt2 (mk_cvtop___3 t1 t2 op) c1 (Some cs)"
    and "wf_cvtop__underscore nt1 nt2 (mk_cvtop___3 t1 t2 op)"
  shows "\<exists>x. c1 = mk_num__1 t1 x \<and> nt1 = numtype_Fnn t1 \<and> nt2 = numtype_Fnn t2 \<and>
    ((op = PROMOTE \<and> cs = map (mk_num__1 t2) (promote__underscore (fsz t1) (fsz t2) x)) \<or>
     (op = DEMOTE \<and> cs = map (mk_num__1 t2) (demote__underscore (fsz t1) (fsz t2) x)))"
  using assms
  by (cases t1; cases t2; cases op)
     (auto elim!: wf_cvtop__underscore.cases wf_cvtop__Fnn_1_Fnn_2.cases fun_cvtop__underscore.cases)

lemma cvt_convert_some:
  "\<exists>v. cvt (tr_numtype (numtype_Fnn t2)) (Some (Nonsat, s)) (ival t1 i) = Some v"
  by (cases t1; cases t2; cases s) (simp_all add: cvt_def cvt_f32_def cvt_f64_def)

lemma cvt_float_some:
  "t1 \<noteq> t2 \<Longrightarrow> \<exists>v. cvt (tr_numtype (numtype_Fnn t2)) None (fval t1 x) = Some v"
  by (cases t1; cases t2) (simp_all add: cvt_def cvt_f32_def cvt_f64_def)

theorem (in builtins) cvtop_tr_aux:
  assumes w: "wf_num_underscore nt1 c1" and wo: "wf_cvtop__underscore nt1 nt2 op"
    and f: "fun_cvtop__underscore nt1 nt2 op c1 (Some cs)"
    and rp: "\<And>v. wc_cvtop nt2 op (tr_num c1) = Some v \<Longrightarrow> nrep nt2 v"
  shows "map tr_num cs = olist (wc_cvtop nt2 op (tr_num c1))"
proof (cases op)
  case (mk_cvtop___0 t1 t2 iop)
  from fun_cvtop_ii[OF f[unfolded mk_cvtop___0] wo[unfolded mk_cvtop___0]] obtain i where
    c: "c1 = mk_num__0 t1 i" "nt1 = numtype_Inn t1" "nt2 = numtype_Inn t2" and
    o: "(\<exists>sx. iop = cvtop__Inn_1_Inn_2_EXTEND sx \<and> t1 = Inn_I32 \<and> t2 = Inn_I64 \<and>
           cs = [mk_num__0 Inn_I64 (extend__underscore 32 64 sx i)]) \<or>
        (iop = WRAP \<and> t1 = Inn_I64 \<and> t2 = Inn_I32 \<and> cs = [mk_num__0 Inn_I32 (wrap__underscore 64 32 i)])"
    by blast
  show ?thesis using o w c mk_cvtop___0 by (auto simp: wc_cvtop_def extend_cvt wrap_cvt)
next
  case (mk_cvtop___1 t1 t2 iop)
  from fun_cvtop_if[OF f[unfolded mk_cvtop___1] wo[unfolded mk_cvtop___1]] obtain i where
    c: "c1 = mk_num__0 t1 i" "nt1 = numtype_Inn t1" "nt2 = numtype_Fnn t2" and
    o: "(\<exists>sx. iop = CONVERT sx \<and> cs = [mk_num__1 t2 (convert__underscore (isz t1) (fsz t2) sx i)]) \<or>
        (iop = REINTERPRET \<and> cs = [reinterpret__underscore nt1 nt2 c1])"
    by blast
  show ?thesis using o
  proof
    assume "\<exists>sx. iop = CONVERT sx \<and> cs = [mk_num__1 t2 (convert__underscore (isz t1) (fsz t2) sx i)]"
    then obtain sx where o': "iop = CONVERT sx" "cs = [mk_num__1 t2 (convert__underscore (isz t1) (fsz t2) sx i)]"
      by blast
    obtain v where v: "cvt (tr_numtype (numtype_Fnn t2)) (Some (Nonsat, tr_sx sx)) (ival t1 i) = Some v"
      using cvt_convert_some by blast
    have "fval t2 (convert__underscore (isz t1) (fsz t2) sx i) = v"
      by (rule convert_tr[OF _ v]) (use w c rp v mk_cvtop___1 o' in \<open>auto simp: wc_cvtop_def ival_def\<close>)
    then show ?thesis using v c mk_cvtop___1 o' by (simp add: wc_cvtop_def ival_def fval_def)
  next
    assume "iop = REINTERPRET \<and> cs = [reinterpret__underscore nt1 nt2 c1]"
    then show ?thesis using w rp mk_cvtop___1 by (simp add: wc_cvtop_def reinterpret_tr)
  qed
next
  case (mk_cvtop___2 t1 t2 iop)
  from fun_cvtop_fi[OF f[unfolded mk_cvtop___2] wo[unfolded mk_cvtop___2]] obtain x where
    c: "c1 = mk_num__1 t1 x" "nt1 = numtype_Fnn t1" "nt2 = numtype_Inn t2" and
    o: "(\<exists>sx. iop = cvtop__Fnn_1_Inn_2_TRUNC sx \<and>
          cs = list_underscore (map_option (mk_num__0 t2) (trunc__underscore (fsz t1) (isz t2) sx x))) \<or>
        (\<exists>sx. iop = TRUNC_SAT sx \<and>
          cs = list_underscore (map_option (mk_num__0 t2) (trunc_sat__underscore (fsz t1) (isz t2) sx x))) \<or>
        (iop = cvtop__Fnn_1_Inn_2_REINTERPRET \<and> cs = [reinterpret__underscore nt1 nt2 c1])"
    by blast
  have fx: "fok t1 x" using w c by simp
  show ?thesis using o
  proof (elim disjE exE conjE)
    fix sx assume "iop = cvtop__Fnn_1_Inn_2_TRUNC sx"
      "cs = list_underscore (map_option (mk_num__0 t2) (trunc__underscore (fsz t1) (isz t2) sx x))"
    then show ?thesis using trunc_tr[OF fx, of t2 sx] c mk_cvtop___2
      by (simp add: wc_cvtop_def map_tr_num_list fval_def)
  next
    fix sx assume "iop = TRUNC_SAT sx"
      "cs = list_underscore (map_option (mk_num__0 t2) (trunc_sat__underscore (fsz t1) (isz t2) sx x))"
    then show ?thesis using trunc_sat_tr[OF fx, of t2 sx] c mk_cvtop___2
      by (simp add: wc_cvtop_def map_tr_num_list fval_def)
  next
    assume "iop = cvtop__Fnn_1_Inn_2_REINTERPRET" "cs = [reinterpret__underscore nt1 nt2 c1]"
    then show ?thesis using w rp mk_cvtop___2 by (simp add: wc_cvtop_def reinterpret_tr)
  qed
next
  case (mk_cvtop___3 t1 t2 iop)
  from fun_cvtop_ff[OF f[unfolded mk_cvtop___3] wo[unfolded mk_cvtop___3]] obtain x where
    c: "c1 = mk_num__1 t1 x" "nt1 = numtype_Fnn t1" "nt2 = numtype_Fnn t2" and
    o: "(iop = PROMOTE \<and> cs = map (mk_num__1 t2) (promote__underscore (fsz t1) (fsz t2) x)) \<or>
        (iop = DEMOTE \<and> cs = map (mk_num__1 t2) (demote__underscore (fsz t1) (fsz t2) x))"
    by blast
  have fx: "fok t1 x" using w c by simp
  have ne: "t1 \<noteq> t2"
    using wo mk_cvtop___3 by (cases t1; cases t2) (auto elim!: wf_cvtop__underscore.cases wf_cvtop__Fnn_1_Fnn_2.cases)
  obtain v where v: "cvt (tr_numtype (numtype_Fnn t2)) None (fval t1 x) = Some v"
    using cvt_float_some[OF ne] by blast
  have rv: "nrep (numtype_Fnn t2) v"
    using rp c mk_cvtop___3 v o by (auto simp: wc_cvtop_def fval_def)
  show ?thesis using o
  proof
    assume "iop = PROMOTE \<and> cs = map (mk_num__1 t2) (promote__underscore (fsz t1) (fsz t2) x)"
    then show ?thesis using promote_tr[OF fx v rv] v c mk_cvtop___3
      by (simp add: wc_cvtop_def fval_def[abs_def] comp_def)
  next
    assume "iop = DEMOTE \<and> cs = map (mk_num__1 t2) (demote__underscore (fsz t1) (fsz t2) x)"
    then show ?thesis using demote_tr[OF fx v rv] v c mk_cvtop___3
      by (simp add: wc_cvtop_def fval_def[abs_def] comp_def)
  qed
qed

theorem (in builtins) cvtop_tr:
  assumes "wf_num_underscore nt1 c1" "wf_cvtop__underscore nt1 nt2 op"
    "fun_cvtop__underscore nt1 nt2 op c1 (Some cs)"
  shows "map tr_num cs = olist (wc_cvtop nt2 op (tr_num c1))"
  by (rule cvtop_tr_aux[OF assms])
     (auto simp: wc_cvtop_def typeof_reinterpret intro!: nrep_typeof dest!: typeof_cvt split: cvtop.splits)

section \<open>WasmCert's byte-level sign extension\<close>

(* [app_extend_s] sign-extends the low bytes of the serialised number; as words,
   it is [scast] after [ucast]. *)
lemma map_takefill: "map f (takefill b n xs) = takefill (f b) n (map f xs)"
  by (induct n arbitrary: xs) (auto split: list.splits)

lemma length_word_rsplit_rev_even:
  assumes "LENGTH('a::len) = m * LENGTH('b::len)"
  shows "length (word_rsplit_rev (w::'a word) :: 'b word list) = m"
proof -
  have "length (word_rsplit w :: 'b word list) = m"
    by (rule length_word_rsplit_even_size[OF HOL.refl]) (simp add: assms word_size)
  then show ?thesis
    by (simp add: word_rsplit_rev_is)
qed

lemma word_rcat_rev_take_rsplit_rev:
  fixes w :: "'a::len word"
  assumes ws: "ws = (word_rsplit_rev w :: 'b::len word list)"
      and len: "length ws * LENGTH('b) = LENGTH('a)"
      and c: "LENGTH('c::len) = k * LENGTH('b)"
      and k: "k \<le> length ws"
  shows "(word_rcat_rev (take k ws) :: 'c word) = ucast w"
proof (rule bit_word_eqI)
  fix n assume n: "n < LENGTH('c)"
  have w: "word_rcat_rev ws = w"
    using ws word_rcat_rsplit_rev by simp
  have nk: "n div LENGTH('b) < k"
    using n c by (simp add: less_mult_imp_div_less)
  have "k * LENGTH('b) \<le> length ws * LENGTH('b)"
    using k by simp
  hence nA: "n < LENGTH('a)"
    using n c len by linarith
  have l: "bit (word_rcat_rev (take k ws) :: 'c word) n =
           (n < LENGTH('c) \<and> n div LENGTH('b) < length (take k ws) \<and> bit (take k ws ! (n div LENGTH('b))) (n mod LENGTH('b)))"
    by (rule bit_rcat_rev_iff) (rule HOL.refl)
  have r: "bit w n = (n < LENGTH('a) \<and> n div LENGTH('b) < length ws \<and> bit (ws ! (n div LENGTH('b))) (n mod LENGTH('b)))"
    by (rule bit_rcat_rev_iff[OF w])
  show "bit (word_rcat_rev (take k ws) :: 'c word) n = bit (ucast w :: 'c word) n"
    using l r n nk nA k by (simp add: bit_word_ucast_iff)
qed

lemma word_rcat_rev_sign_extend_take_rsplit_rev:
  fixes w :: "'a::len word"
  assumes ws: "ws = (word_rsplit_rev w :: 'b::len word list)"
      and len: "length ws * LENGTH('b) = LENGTH('a)"
      and c: "LENGTH('c::len) = k * LENGTH('b)"
      and k: "k \<le> length ws"
  shows "(word_rcat_rev (word_list_sign_extend (length ws) (take k ws)) :: 'a word) = scast (ucast w :: 'c word)"
proof -
  have "k * LENGTH('b) \<le> length ws * LENGTH('b)"
    using k by simp
  hence "(scast (word_rcat_rev (take k ws) :: 'c word) :: 'a word) =
         word_rcat_rev (word_list_sign_extend (length ws) (take k ws))"
    using len c k
    by (intro scast_word_rcat_rev_is_word_rcat_rev_word_list_sign_extend) (simp_all add: min_absorb2)
  then show ?thesis
    using word_rcat_rev_take_rsplit_rev[OF ws len c k] by simp
qed

lemma map_Rep_sign_extend_S:
  assumes "bs \<noteq> []"
  shows "map Rep_uint8 (sign_extend Wasm_Ast.S l (map Abs_uint8' bs)) = word_list_sign_extend l bs"
proof -
  have "Rep_uint8 (if msb_byte (msbyte (map Abs_uint8' bs)) then negone_byte else zero_byte) =
        (if msb (last bs) then -1 else 0)"
    using assms
    by (simp add: msb_byte_def msbyte_def negone_byte_def zero_byte_def last_map msb_uint8.rep_eq
                  Abs_uint8'.rep_eq uminus_uint8.rep_eq one_uint8.rep_eq zero_uint8.rep_eq)
  then show ?thesis
    by (simp add: sign_extend_def Let_def bytes_takefill_def word_list_sign_extend_def map_takefill
                  comp_def Abs_uint8'.rep_eq)
qed

lemma app_extend_s_i32:
  assumes hc: "LENGTH('c::len) = tp_num_length tp * 8"
  shows "app_extend_s tp (ConstInt32 c) = ConstInt32 (Abs_i32 (scast (ucast (Rep_i32 c) :: 'c word)))"
proof -
  define ws where "ws = (word_rsplit_rev (Rep_i32 c) :: 8 word list)"
  have len: "length ws = 4"
    unfolding ws_def by (rule length_word_rsplit_rev_even) simp
  have k: "tp_num_length tp \<le> length ws" "0 < tp_num_length tp"
    using len by (simp_all add: tp_num_length_def split: tp_num.splits)
  have ne: "take (tp_num_length tp) ws \<noteq> []"
    using k len by (cases ws) simp_all
  have bits: "bits_num (ConstInt32 c) = map Abs_uint8' ws"
    by (simp add: bits_num_def serialise_i32_def ws_def)
  have len': "length ws * LENGTH(8) = LENGTH(32)"
    by (simp add: len)
  have hc': "LENGTH('c) = tp_num_length tp * LENGTH(8)"
    using hc by simp
  have "app_extend_s tp (ConstInt32 c) =
        ConstInt32 (Abs_i32 (word_rcat_rev (map Rep_uint8 (sign_extend Wasm_Ast.S 4 (map Abs_uint8' (take (tp_num_length tp) ws))))))"
    by (simp add: app_extend_s_def typeof_num_def t_num_length_def bits wasm_deserialise_num_def
                  deserialise_i32_def take_map)
  also have "\<dots> = ConstInt32 (Abs_i32 (word_rcat_rev (word_list_sign_extend (length ws) (take (tp_num_length tp) ws))))"
    by (simp add: map_Rep_sign_extend_S[OF ne] len)
  also have "\<dots> = ConstInt32 (Abs_i32 (scast (ucast (Rep_i32 c) :: 'c word)))"
    using word_rcat_rev_sign_extend_take_rsplit_rev[OF ws_def len' hc' k(1)] by simp
  finally show ?thesis .
qed

lemma app_extend_s_i64:
  assumes hc: "LENGTH('c::len) = tp_num_length tp * 8"
  shows "app_extend_s tp (ConstInt64 c) = ConstInt64 (Abs_i64 (scast (ucast (Rep_i64 c) :: 'c word)))"
proof -
  define ws where "ws = (word_rsplit_rev (Rep_i64 c) :: 8 word list)"
  have len: "length ws = 8"
    unfolding ws_def by (rule length_word_rsplit_rev_even) simp
  have k: "tp_num_length tp \<le> length ws" "0 < tp_num_length tp"
    using len by (simp_all add: tp_num_length_def split: tp_num.splits)
  have ne: "take (tp_num_length tp) ws \<noteq> []"
    using k len by (cases ws) simp_all
  have bits: "bits_num (ConstInt64 c) = map Abs_uint8' ws"
    by (simp add: bits_num_def serialise_i64_def ws_def)
  have len': "length ws * LENGTH(8) = LENGTH(64)"
    by (simp add: len)
  have hc': "LENGTH('c) = tp_num_length tp * LENGTH(8)"
    using hc by simp
  have "app_extend_s tp (ConstInt64 c) =
        ConstInt64 (Abs_i64 (word_rcat_rev (map Rep_uint8 (sign_extend Wasm_Ast.S 8 (map Abs_uint8' (take (tp_num_length tp) ws))))))"
    by (simp add: app_extend_s_def typeof_num_def t_num_length_def bits wasm_deserialise_num_def
                  deserialise_i64_def take_map)
  also have "\<dots> = ConstInt64 (Abs_i64 (word_rcat_rev (word_list_sign_extend (length ws) (take (tp_num_length tp) ws))))"
    by (simp add: map_Rep_sign_extend_S[OF ne] len)
  also have "\<dots> = ConstInt64 (Abs_i64 (scast (ucast (Rep_i64 c) :: 'c word)))"
    using word_rcat_rev_sign_extend_take_rsplit_rev[OF ws_def len' hc' k(1)] by simp
  finally show ?thesis .
qed

lemma app_extend_s_i32_i8:
  "app_extend_s Tp_i8 (ConstInt32 c) = ConstInt32 (Abs_i32 (scast (ucast (Rep_i32 c) :: 8 word)))"
  by (rule app_extend_s_i32) (simp add: tp_num_length_def)

lemma app_extend_s_i32_i16:
  "app_extend_s Tp_i16 (ConstInt32 c) = ConstInt32 (Abs_i32 (scast (ucast (Rep_i32 c) :: 16 word)))"
  by (rule app_extend_s_i32) (simp add: tp_num_length_def)

lemma app_extend_s_i64_i8:
  "app_extend_s Tp_i8 (ConstInt64 c) = ConstInt64 (Abs_i64 (scast (ucast (Rep_i64 c) :: 8 word)))"
  by (rule app_extend_s_i64) (simp add: tp_num_length_def)

lemma app_extend_s_i64_i16:
  "app_extend_s Tp_i16 (ConstInt64 c) = ConstInt64 (Abs_i64 (scast (ucast (Rep_i64 c) :: 16 word)))"
  by (rule app_extend_s_i64) (simp add: tp_num_length_def)

lemma app_extend_s_i64_i32:
  "app_extend_s Tp_i32 (ConstInt64 c) = ConstInt64 (Abs_i64 (scast (ucast (Rep_i64 c) :: 32 word)))"
  by (rule app_extend_s_i64) (simp add: tp_num_length_def)

lemma ucast_of_nat_down:
  "LENGTH('a) \<le> LENGTH('c) \<Longrightarrow>
   (ucast (of_nat a :: 'c::len word) :: 'a::len word) = of_nat (a mod 2 ^ LENGTH('a))"
  by (simp add: ucast_of_nat word_of_nat_eq_iff take_bit_eq_mod mod_mod_cancel le_imp_power_dvd)

(* SpecTec's [EXTEND M] wraps to [M] bits and sign-extends back; WasmCert's
   [Extend_s] sign-extends the low bytes. *)
lemma (in builtins) extend_unop_wc:
  assumes "iok t i" "ext_width_ok (numtype_Inn t) M"
  shows "app_unop (Extend_s (tp_of_bits M)) (ival t i) =
    ival t (extend__underscore M (isz t) isabelle_reference_output_wasm2.S (wrap__underscore (isz t) M i))"
  using assms
  by (cases t)
     (auto simp: ext_width_ok_def tp_of_bits_def app_unop_def extend_def wrap_def tr_i32_def tr_i64_def
        app_extend_s_i32_i8 app_extend_s_i32_i16 app_extend_s_i64_i8 app_extend_s_i64_i16 app_extend_s_i64_i32 ucast_of_nat_down scast_of_nat)

lemma fun_unop_int:
  assumes "fun_unop_underscore nt (mk_unop__0 t uop) c1 (Some cs)"
  shows "\<exists>i. c1 = mk_num__0 t i \<and> nt = numtype_Inn t \<and>
     cs = [mk_num__0 t (case uop of CLZ \<Rightarrow> iclz_underscore (isz t) i | CTZ \<Rightarrow> ictz_underscore (isz t) i
       | POPCNT \<Rightarrow> ipopcnt_underscore (isz t) i
       | EXTEND M \<Rightarrow> extend__underscore M (isz t) isabelle_reference_output_wasm2.S (wrap__underscore (isz t) M i))]"
  using assms by (cases t; cases uop) (auto elim: fun_unop_underscore.cases)

lemma fun_unop_float:
  assumes "fun_unop_underscore nt (mk_unop__1 t fop) c1 (Some cs)"
  shows "\<exists>x. c1 = mk_num__1 t x \<and> nt = numtype_Fnn t \<and> cs = map (mk_num__1 t) (fun1 fop (fsz t) x)"
  using assms by (cases t; cases fop) (auto elim: fun_unop_underscore.cases)

theorem (in builtins) unop_tr_aux:
  assumes w: "wf_num_underscore nt c1" and f: "fun_unop_underscore nt op c1 (Some cs)"
    and e: "unop_ext_ok nt op"
    and rp: "nrep nt (app_unop (tr_unop op) (tr_num c1))"
  shows "map tr_num cs = [app_unop (tr_unop op) (tr_num c1)]"
proof (cases op)
  case (mk_unop__0 t uop)
  from fun_unop_int[OF f[unfolded mk_unop__0]] obtain i where c: "c1 = mk_num__0 t i" "nt = numtype_Inn t"
    and cs: "cs = [mk_num__0 t (case uop of CLZ \<Rightarrow> iclz_underscore (isz t) i | CTZ \<Rightarrow> ictz_underscore (isz t) i
       | POPCNT \<Rightarrow> ipopcnt_underscore (isz t) i
       | EXTEND M \<Rightarrow> extend__underscore M (isz t) isabelle_reference_output_wasm2.S (wrap__underscore (isz t) M i))]"
    by blast
  have ii: "iok t i" using w c by simp
  show ?thesis
  proof (cases uop)
    case CLZ then show ?thesis using iclz_tr[OF ii] c cs mk_unop__0 by (simp add: ival_def)
  next
    case CTZ then show ?thesis using ictz_tr[OF ii] c cs mk_unop__0 by (simp add: ival_def)
  next
    case POPCNT then show ?thesis using ipopcnt_tr[OF ii] c cs mk_unop__0 by (simp add: ival_def)
  next
    case (EXTEND M)
    have "ext_width_ok (numtype_Inn t) M" using e c mk_unop__0 EXTEND by simp
    from extend_unop_wc[OF ii this] show ?thesis using c cs mk_unop__0 EXTEND by (simp add: ival_def)
  qed
next
  case (mk_unop__1 t fop)
  from fun_unop_float[OF f[unfolded mk_unop__1]] obtain x where
    c: "c1 = mk_num__1 t x" "nt = numtype_Fnn t" "cs = map (mk_num__1 t) (fun1 fop (fsz t) x)"
    by blast
  have "map (fval t) (fun1 fop (fsz t) x) = [app_unop (tr_unop (mk_unop__1 t fop)) (fval t x)]"
    by (rule fun1_tr) (use w rp c mk_unop__1 in \<open>auto simp: fval_def\<close>)
  then show ?thesis using c mk_unop__1 by (simp add: fval_def[abs_def] comp_def)
qed

theorem (in builtins) unop_tr:
  assumes "wf_num_underscore nt c1" "fun_unop_underscore nt op c1 (Some cs)" "unop_ext_ok nt op"
  shows "map tr_num cs = [app_unop (tr_unop op) (tr_num c1)]"
  by (rule unop_tr_aux[OF assms])
     (use typeof_tr_num[OF assms(1)] in \<open>simp add: nrep_typeof typeof_app_unop\<close>)

end

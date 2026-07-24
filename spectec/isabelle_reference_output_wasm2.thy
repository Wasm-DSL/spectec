theory isabelle_reference_output_wasm2
(* Imported Code *)
	imports Main
begin

inductive list_all3 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> bool" where
	list_all3_nil : "list_all3 R [] [] []" |
	list_all3_cons: "R a b c \<Longrightarrow> list_all3 R as bs cs \<Longrightarrow> list_all3 R (a # as) (b # bs) (c # cs)"

inductive list_all4 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'd list \<Rightarrow> bool" where
	list_all4_nil : "list_all4 R [] [] [] []" |
	list_all4_cons: "R a b c d \<Longrightarrow> list_all4 R as bs cs ds \<Longrightarrow> list_all4 R (a # as) (b # bs) (c # cs) (d # ds)"

definition list_zipWith :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list" where
	"list_zipWith f xs ys = map (\<lambda> (x, y). f x y) (zip xs ys)"

definition list_map3 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'd list" where
	"list_map3 f xs ys zs = map (\<lambda> (x, (y, z)). f x y z) (zip xs (zip ys zs))"

definition list_map4 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'd list \<Rightarrow> 'e list" where
	"list_map4 f xs ys zs ws = map (\<lambda> (x, (y, (z, w))). f x y z w) (zip xs (zip ys (zip zs ws)))"

inductive foralli_help :: "(nat \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool" where
	foralli_nil : "foralli_help f n []" |
	foralli_cons : "f n x \<Longrightarrow> foralli_help f (n + 1) l \<Longrightarrow> foralli_help f n (x # l)"

definition list_foralli :: "(nat \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
	"list_foralli f xs = foralli_help f 0 xs"

fun option_zipWith :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> 'c option" where
	"option_zipWith f (Some x) (Some y) = Some (f x y)" |
	"option_zipWith _ _ _ = None"

fun option_map3 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> 'c option \<Rightarrow> 'd option" where
	"option_map3 f (Some x) (Some y) (Some z) = Some (f x y z)" |
	"option_map3 f _ _ _ = None"

fun option_map4 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> 'c option \<Rightarrow> 'd option \<Rightarrow> 'e option" where
	"option_map4 f (Some x) (Some y) (Some z) (Some w) = Some (f x y z w)" |
	"option_map4 f _ _ _ _ = None"

fun option_to_list :: "'a option \<Rightarrow>'a list" where
	"option_to_list None = []" |
	"option_to_list (Some a) = [a]"

fun list_slice :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
	"list_slice [] _ _ = []" |
	"list_slice (x # l) 0 0 = []" |
	"list_slice (x # l) (Suc n) 0 = []" |
	"list_slice (x # l) 0 (Suc m) = x # list_slice l 0 m" |
	"list_slice (x # l) (Suc n) m = list_slice l n m"

fun mkseq :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow>'a list" where
	"mkseq _ 0 = []" |
	"mkseq f (Suc n) = mkseq f n @ [f n]"

fun repeat :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
	"repeat 0 _ = []" |
	"repeat (Suc n) x = x # repeat n x"

fun list_update_func :: "'a list \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a list" where
	"list_update_func [] _ _ = []" |
	"list_update_func (x # l) 0 y = (y x) # l" |
	"list_update_func (x # l) (Suc n) y = x # list_update_func l n y"

fun list_slice_update :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
	"list_slice_update [] _ _ _ = []" |
	"list_slice_update l _ _ [] = l" |
	"list_slice_update (x # l) _ 0 _ = []" |
	"list_slice_update (x # l) 0 (Suc m) (y # ul) = y # list_slice_update l 0 m ul" |
	"list_slice_update (x # l) (Suc n) m ul = x # list_slice_update l n m ul"

fun option_append :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" (infixl "@@@" 70) where
	"option_append (Some x) _ = Some x" |
	"option_append None y = y"

fun list_alli_aux :: "(nat \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool" where
	"list_alli_aux f n [] = True" |
	"list_alli_aux f n (x # q) = (f n x \<and> list_alli_aux f (Suc n) q)"

definition list_alli :: "(nat \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
	"list_alli f l = list_alli_aux f 0 l"

definition holds_upto :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
	"holds_upto P n \<equiv> \<forall> i < n. P i"

(* Generated Code *)
(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:162.14-162.17 *)
datatype r_MUT =
	  MUT
	

(* Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:7.1-7.15 *)
type_synonym N = "nat"

(* Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:8.1-8.15 *)
type_synonym M = "nat"

(* Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:9.1-9.15 *)
type_synonym n = "nat"

(* Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:10.1-10.15 *)
type_synonym m = "nat"

(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:15.1-15.14 *)
definition Ki :: "nat" where
	"Ki = 1024"

(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:21.1-21.25 *)
function (sequential, domintros) min :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
		  "min i j = (if (i \<le> j) then i else j)"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:25.1-25.21 *)
inductive fun_sum :: "(nat list) \<Rightarrow> nat \<Rightarrow> bool" where
	  fun_sum_case_0 :
		"fun_sum [] 0"
	| fun_sum_case_1 :
		"(fun_sum n'_lst var_0) \<Longrightarrow>
		 fun_sum ([v_n] @ n'_lst) (v_n + var_0)"

(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:32.1-32.58 *)
function (sequential, domintros) opt_underscore :: "('X list) \<Rightarrow> (('X option) option)" where
		  "opt_underscore  [] = (Some None)"
		| "opt_underscore  [w] = (Some (Some w))"
		| "opt_underscore  x1 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:36.1-36.45 *)
function (sequential, domintros) list_underscore :: "('X option) \<Rightarrow> ('X list)" where
		  "list_underscore  None = []"
		| "list_underscore  (Some w) = [w]"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:40.1-40.86 *)
function (sequential, domintros) concat_underscore :: "(('X list) list) \<Rightarrow> ('X list)" where
		  "concat_underscore  [] = []"
		| "concat_underscore  (w_lst # w'_lst_lst) = (w_lst @ (concat_underscore  w'_lst_lst))"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-2.0/0-aux.spectec:44.1-44.39 *)
axiomatization inv_concat_underscore :: "('X list) \<Rightarrow> (('X list) list)"

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:51.1-51.46 *)
function (sequential, domintros) setproduct2_underscore :: "'X \<Rightarrow> (('X list) list) \<Rightarrow> (('X list) list)" where
		  "setproduct2_underscore  w_1 [] = []"
		| "setproduct2_underscore  w_1 (w'_lst # w_lst_lst) = ([([w_1] @ w'_lst)] @ (setproduct2_underscore  w_1 w_lst_lst))"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:50.1-50.47 *)
function (sequential, domintros) setproduct1_underscore :: "('X list) \<Rightarrow> (('X list) list) \<Rightarrow> (('X list) list)" where
		  "setproduct1_underscore  [] w_lst_lst = []"
		| "setproduct1_underscore  (w_1 # w'_lst) w_lst_lst = ((setproduct2_underscore  w_1 w_lst_lst) @ (setproduct1_underscore  w'_lst w_lst_lst))"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:49.1-49.84 *)
function (sequential, domintros) setproduct_underscore :: "(('X list) list) \<Rightarrow> (('X list) list)" where
		  "setproduct_underscore  [] = [[]]"
		| "setproduct_underscore  (w_1_lst # w_lst_lst) = (setproduct1_underscore  w_1_lst (setproduct_underscore  w_lst_lst))"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-2.0/0-aux.spectec:60.1-60.78 *)
function (sequential, domintros) disjoint_underscore :: "('X list) \<Rightarrow> bool" where
		  "disjoint_underscore  [] = True"
		| "disjoint_underscore  (w # w'_lst) = ((~ (w \<in> set w'_lst)) \<and> (disjoint_underscore  w'_lst))"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:6.1-6.49 *)
datatype 'X res_list  =
	  mk_list "('X list)"
	

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:6.1-6.49 *)
function (sequential, domintros) proj_list_0 :: "('X res_list) \<Rightarrow> (('X list))" where
		  "proj_list_0  (mk_list v_X_list_0) = (v_X_list_0)"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:15.1-15.36 *)
datatype bit =
	  mk_bit "nat"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:15.8-15.11 *)
inductive wf_bit :: "bit \<Rightarrow> bool" where
	  bit_case_0 :
		"((i = 0) \<or> (i = 1)) \<Longrightarrow>
		 wf_bit (mk_bit i)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.1-16.50 *)
datatype byte =
	  mk_byte "nat"
	

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.1-16.50 *)
function (sequential, domintros) proj_byte_0 :: "byte \<Rightarrow> (nat)" where
		  "proj_byte_0 (mk_byte v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.8-16.12 *)
inductive wf_byte :: "byte \<Rightarrow> bool" where
	  byte_case_0 :
		"((i \<ge> 0) \<and> (i \<le> 255)) \<Longrightarrow>
		 wf_byte (mk_byte i)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.1-19.25 *)
datatype uN =
	  mk_uN "nat"
	

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.1-19.25 *)
function (sequential, domintros) proj_uN_0 :: "uN \<Rightarrow> (nat)" where
		  "proj_uN_0 (mk_uN v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.8-18.11 *)
inductive wf_uN :: "N \<Rightarrow> uN \<Rightarrow> bool" where
	  uN_case_0 :
		"((i \<ge> 0) \<and> (i \<le> ((((2 ^ v_N) :: nat) - (1 :: nat)) :: nat))) \<Longrightarrow>
		 wf_uN v_N (mk_uN i)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.1-21.49 *)
datatype sN =
	  mk_sN "nat"
	

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.1-21.49 *)
function (sequential, domintros) proj_sN_0 :: "sN \<Rightarrow> (nat)" where
		  "proj_sN_0 (mk_sN v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.8-20.11 *)
inductive wf_sN :: "N \<Rightarrow> sN \<Rightarrow> bool" where
	  sN_case_0 :
		"((((i \<ge> (0 - ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat))) \<and> (i \<le> (0 - (1 :: nat)))) \<or> (i = (0 :: nat))) \<or> ((i \<ge> ((1 :: nat))) \<and> (i \<le> (((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat) - (1 :: nat))))) \<Longrightarrow>
		 wf_sN v_N (mk_sN i)"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:22.1-23.8 *)
type_synonym iN = "uN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:25.1-25.18 *)
type_synonym u8 = "uN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:26.1-26.20 *)
type_synonym u16 = "uN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:27.1-27.20 *)
type_synonym u31 = "uN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:28.1-28.20 *)
type_synonym u32 = "uN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:29.1-29.20 *)
type_synonym u64 = "uN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:30.1-30.20 *)
type_synonym s33 = "sN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:31.1-31.20 *)
type_synonym i32 = "iN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:32.1-32.20 *)
type_synonym i64 = "iN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:33.1-33.22 *)
type_synonym i128 = "iN"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:40.1-40.35 *)
function (sequential, domintros) signif :: "N \<Rightarrow> (nat option)" where
		  "signif (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some 23)"
		| "signif (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some 52)"
		| "signif x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:44.1-44.34 *)
function (sequential, domintros) expon :: "N \<Rightarrow> (nat option)" where
		  "expon (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some 8)"
		| "expon (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some 11)"
		| "expon x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:48.1-48.30 *)
function (sequential, domintros) fun_M :: "N \<Rightarrow> nat" where
		  "fun_M v_N = (the ((signif v_N)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:51.1-51.30 *)
function (sequential, domintros) E :: "N \<Rightarrow> nat" where
		  "E v_N = (the ((expon v_N)))"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:58.1-58.30 *)
type_synonym exp = "nat"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:59.1-63.84 *)
datatype fNmag =
	  NORM "m" "exp"
	| SUBNORM "m"
	| res_INF
	| NAN "m"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:59.8-59.14 *)
inductive wf_fNmag :: "N \<Rightarrow> fNmag \<Rightarrow> bool" where
	  fNmag_case_0 :
		"((v_m < (2 ^ (fun_M v_N))) \<and> ((((2 :: nat) - ((2 ^ ((((E v_N) :: nat) - (1 :: nat)) :: nat)) :: nat)) \<le> v_exp) \<and> (v_exp \<le> (((2 ^ ((((E v_N) :: nat) - (1 :: nat)) :: nat)) :: nat) - (1 :: nat))))) \<Longrightarrow>
		 wf_fNmag v_N (NORM v_m v_exp)"
	| fNmag_case_1 :
		"((v_m < (2 ^ (fun_M v_N))) \<and> (((2 :: nat) - ((2 ^ ((((E v_N) :: nat) - (1 :: nat)) :: nat)) :: nat)) = v_exp)) \<Longrightarrow>
		 wf_fNmag v_N (SUBNORM v_m)"
	| fNmag_case_2 :
		"wf_fNmag v_N res_INF"
	| fNmag_case_3 :
		"((1 \<le> v_m) \<and> (v_m < (2 ^ (fun_M v_N)))) \<Longrightarrow>
		 wf_fNmag v_N (NAN v_m)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:54.1-56.35 *)
datatype fN =
	  POS "fNmag"
	| NEG "fNmag"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:54.8-54.11 *)
inductive wf_fN :: "N \<Rightarrow> fN \<Rightarrow> bool" where
	  fN_case_0 :
		"(wf_fNmag v_N var_0) \<Longrightarrow>
		 wf_fN v_N (POS var_0)"
	| fN_case_1 :
		"(wf_fNmag v_N var_0) \<Longrightarrow>
		 wf_fN v_N (NEG var_0)"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:65.1-65.20 *)
type_synonym f32 = "fN"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:66.1-66.20 *)
type_synonym f64 = "fN"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:68.1-68.39 *)
function (sequential, domintros) fzero :: "N \<Rightarrow> fN" where
		  "fzero v_N = (POS (SUBNORM 0))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:68.6-68.12 *)
lemma fzero_is_wf :
	"(ret_val = (fzero v_N)) \<Longrightarrow>
	 (wf_fN v_N ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:71.1-71.39 *)
function (sequential, domintros) fone :: "N \<Rightarrow> fN" where
		  "fone v_N = (POS (NORM 1 (0 :: nat)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:71.6-71.11 *)
lemma fone_is_wf :
	"(ret_val = (fone v_N)) \<Longrightarrow>
	 (wf_fN v_N ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:74.1-74.21 *)
function (sequential, domintros) canon_underscore :: "N \<Rightarrow> nat" where
		  "canon_underscore v_N = (2 ^ ((((the ((signif v_N))) :: nat) - (1 :: nat)) :: nat))"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:80.1-81.8 *)
type_synonym vN = "iN"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.1-88.85 *)
datatype res_char =
	  mk_char "nat"
	

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.1-88.85 *)
function (sequential, domintros) proj_char_0 :: "res_char \<Rightarrow> (nat)" where
		  "proj_char_0 (mk_char v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.8-88.12 *)
inductive wf_char :: "res_char \<Rightarrow> bool" where
	  char_case_0 :
		"(((i \<ge> 0) \<and> (i \<le> 55295)) \<or> ((i \<ge> 57344) \<and> (i \<le> 1114111))) \<Longrightarrow>
		 wf_char (mk_char i)"

(* Mutual Recursion at: ../specification/wasm-2.0/1-syntax.spectec:90.1-90.25 *)
inductive fun_utf8 :: "(res_char list) \<Rightarrow> (byte list) \<Rightarrow> bool" where
	  fun_utf8_case_0 :
		"(((proj_char_0 ch) < 128) \<and> ((mk_byte (proj_char_0 ch)) = b)) \<Longrightarrow>
		 (wf_byte (mk_byte (proj_char_0 ch))) \<Longrightarrow>
		 fun_utf8 [ch] [b]"
	| fun_utf8_case_1 :
		"(((128 \<le> (proj_char_0 ch)) \<and> ((proj_char_0 ch) < 2048)) \<and> ((proj_char_0 ch) = (((2 ^ 6) * ((((proj_byte_0 b_1) :: nat) - (192 :: nat)) :: nat)) + ((((proj_byte_0 b_2) :: nat) - (128 :: nat)) :: nat)))) \<Longrightarrow>
		 fun_utf8 [ch] [b_1, b_2]"
	| fun_utf8_case_2 :
		"((((2048 \<le> (proj_char_0 ch)) \<and> ((proj_char_0 ch) < 55296)) \<or> ((57344 \<le> (proj_char_0 ch)) \<and> ((proj_char_0 ch) < 65536))) \<and> ((proj_char_0 ch) = ((((2 ^ 12) * ((((proj_byte_0 b_1) :: nat) - (224 :: nat)) :: nat)) + ((2 ^ 6) * ((((proj_byte_0 b_2) :: nat) - (128 :: nat)) :: nat))) + ((((proj_byte_0 b_3) :: nat) - (128 :: nat)) :: nat)))) \<Longrightarrow>
		 fun_utf8 [ch] [b_1, b_2, b_3]"
	| fun_utf8_case_3 :
		"(((65536 \<le> (proj_char_0 ch)) \<and> ((proj_char_0 ch) < 69632)) \<and> ((proj_char_0 ch) = (((((2 ^ 18) * ((((proj_byte_0 b_1) :: nat) - (240 :: nat)) :: nat)) + ((2 ^ 12) * ((((proj_byte_0 b_2) :: nat) - (128 :: nat)) :: nat))) + ((2 ^ 6) * ((((proj_byte_0 b_3) :: nat) - (128 :: nat)) :: nat))) + ((((proj_byte_0 b_4) :: nat) - (128 :: nat)) :: nat)))) \<Longrightarrow>
		 fun_utf8 [ch] [b_1, b_2, b_3, b_4]"
	| fun_utf8_case_4 :
		"((length var_0_lst) = (length ch_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (var_0 :: (byte list)) (ch :: res_char). (fun_utf8 [ch] var_0)) var_0_lst ch_lst \<Longrightarrow>
		 fun_utf8 ch_lst (concat_underscore  var_0_lst)"

(* Mutual Recursion at: ../specification/wasm-2.0/1-syntax.spectec:90.1-90.25 *)
inductive utf8_is_wf :: "(res_char list) \<Rightarrow> (byte list) \<Rightarrow> bool" where
	  utf8_is_wf_0 :
		"(fun_utf8 var_0_lst var_0) \<Longrightarrow>
		 list_all (\<lambda> (var_0 :: res_char). (wf_char var_0)) var_0_lst \<Longrightarrow>
		 (ret_val_lst = var_0) \<Longrightarrow>
		 list_all (\<lambda> (ret_val :: byte). (wf_byte ret_val)) ret_val_lst \<Longrightarrow>
		 utf8_is_wf var_0_lst ret_val_lst"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:92.1-92.70 *)
datatype name =
	  mk_name "(res_char list)"
	

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:92.1-92.70 *)
function (sequential, domintros) proj_name_0 :: "name \<Rightarrow> ((res_char list))" where
		  "proj_name_0 (mk_name v_char_list_0) = (v_char_list_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:92.8-92.12 *)
inductive wf_name :: "name \<Rightarrow> bool" where
	  name_case_0 :
		"(fun_utf8 char_lst var_0) \<Longrightarrow>
		 list_all (\<lambda> (v_char :: res_char). (wf_char v_char)) char_lst \<Longrightarrow>
		 ((length var_0) < (2 ^ 32)) \<Longrightarrow>
		 wf_name (mk_name char_lst)"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:101.1-101.36 *)
type_synonym idx = "u32"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:102.1-102.44 *)
type_synonym laneidx = "u8"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:104.1-104.45 *)
type_synonym typeidx = "idx"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:105.1-105.49 *)
type_synonym funcidx = "idx"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:106.1-106.49 *)
type_synonym globalidx = "idx"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:107.1-107.47 *)
type_synonym tableidx = "idx"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:108.1-108.46 *)
type_synonym memidx = "idx"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:109.1-109.45 *)
type_synonym elemidx = "idx"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:110.1-110.45 *)
type_synonym dataidx = "idx"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:111.1-111.47 *)
type_synonym labelidx = "idx"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:112.1-112.47 *)
type_synonym localidx = "idx"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:126.1-127.26 *)
datatype numtype =
	  I32
	| I64
	| F32
	| F64

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:129.1-130.9 *)
datatype vectype =
	  V128
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:132.1-133.22 *)
datatype consttype =
	  consttype_I32
	| consttype_I64
	| consttype_F32
	| consttype_F64
	| consttype_V128

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:135.1-136.24 *)
datatype reftype =
	  FUNCREF
	| EXTERNREF

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:138.1-139.38 *)
datatype valtype =
	  valtype_I32
	| valtype_I64
	| valtype_F32
	| valtype_F64
	| valtype_V128
	| valtype_FUNCREF
	| valtype_EXTERNREF
	| BOT

(* Auxiliary Definition at:  *)
function (sequential, domintros) valtype_numtype :: "numtype \<Rightarrow> valtype" where
		  "valtype_numtype I32 = valtype_I32"
		| "valtype_numtype I64 = valtype_I64"
		| "valtype_numtype F32 = valtype_F32"
		| "valtype_numtype F64 = valtype_F64"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential, domintros) valtype_reftype :: "reftype \<Rightarrow> valtype" where
		  "valtype_reftype FUNCREF = valtype_FUNCREF"
		| "valtype_reftype EXTERNREF = valtype_EXTERNREF"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential, domintros) valtype_vectype :: "vectype \<Rightarrow> valtype" where
		  "valtype_vectype V128 = valtype_V128"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:141.1-141.38 *)
datatype Inn =
	  Inn_I32
	| Inn_I64

(* Auxiliary Definition at:  *)
function (sequential, domintros) numtype_Inn :: "Inn \<Rightarrow> numtype" where
		  "numtype_Inn Inn_I32 = I32"
		| "numtype_Inn Inn_I64 = I64"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential, domintros) valtype_Inn :: "Inn \<Rightarrow> valtype" where
		  "valtype_Inn Inn_I32 = valtype_I32"
		| "valtype_Inn Inn_I64 = valtype_I64"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:142.1-142.38 *)
datatype Fnn =
	  Fnn_F32
	| Fnn_F64

(* Auxiliary Definition at:  *)
function (sequential, domintros) numtype_Fnn :: "Fnn \<Rightarrow> numtype" where
		  "numtype_Fnn Fnn_F32 = F32"
		| "numtype_Fnn Fnn_F64 = F64"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential, domintros) valtype_Fnn :: "Fnn \<Rightarrow> valtype" where
		  "valtype_Fnn Fnn_F32 = valtype_F32"
		| "valtype_Fnn Fnn_F64 = valtype_F64"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:143.1-143.36 *)
type_synonym Vnn = "vectype"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:146.1-147.16 *)
type_synonym resulttype = "(valtype res_list)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:152.1-152.52 *)
datatype packtype =
	  I8
	| I16

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:153.1-153.60 *)
datatype lanetype =
	  lanetype_I32
	| lanetype_I64
	| lanetype_F32
	| lanetype_F64
	| lanetype_I8
	| lanetype_I16

(* Auxiliary Definition at:  *)
function (sequential, domintros) lanetype_Fnn :: "Fnn \<Rightarrow> lanetype" where
		  "lanetype_Fnn Fnn_F32 = lanetype_F32"
		| "lanetype_Fnn Fnn_F64 = lanetype_F64"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential, domintros) lanetype_Inn :: "Inn \<Rightarrow> lanetype" where
		  "lanetype_Inn Inn_I32 = lanetype_I32"
		| "lanetype_Inn Inn_I64 = lanetype_I64"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential, domintros) lanetype_numtype :: "numtype \<Rightarrow> lanetype" where
		  "lanetype_numtype I32 = lanetype_I32"
		| "lanetype_numtype I64 = lanetype_I64"
		| "lanetype_numtype F32 = lanetype_F32"
		| "lanetype_numtype F64 = lanetype_F64"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential, domintros) lanetype_packtype :: "packtype \<Rightarrow> lanetype" where
		  "lanetype_packtype I8 = lanetype_I8"
		| "lanetype_packtype I16 = lanetype_I16"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:155.1-155.37 *)
type_synonym Pnn = "packtype"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:156.1-156.38 *)
datatype Jnn =
	  Jnn_I32
	| Jnn_I64
	| Jnn_I8
	| Jnn_I16

(* Auxiliary Definition at:  *)
function (sequential, domintros) lanetype_Jnn :: "Jnn \<Rightarrow> lanetype" where
		  "lanetype_Jnn Jnn_I32 = lanetype_I32"
		| "lanetype_Jnn Jnn_I64 = lanetype_I64"
		| "lanetype_Jnn Jnn_I8 = lanetype_I8"
		| "lanetype_Jnn Jnn_I16 = lanetype_I16"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential, domintros) Jnn_packtype :: "packtype \<Rightarrow> Jnn" where
		  "Jnn_packtype I8 = Jnn_I8"
		| "Jnn_packtype I16 = Jnn_I16"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:157.1-157.37 *)
type_synonym Lnn = "lanetype"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:162.1-162.18 *)
type_synonym mut = "(r_MUT option)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:164.1-165.17 *)
datatype limits =
	  mk_limits "u32" "(u32 option)"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:164.8-164.14 *)
inductive wf_limits :: "limits \<Rightarrow> bool" where
	  limits_case_0 :
		"(wf_uN 32 v_u32) \<Longrightarrow>
		 list_all (\<lambda> (v_u32 :: u32). (wf_uN 32 v_u32)) (option_to_list u32_opt) \<Longrightarrow>
		 wf_limits (mk_limits v_u32 u32_opt)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:167.1-168.14 *)
datatype globaltype =
	  mk_globaltype "mut" "valtype"
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:169.1-170.27 *)
datatype functype =
	  mk_functype "resulttype" "resulttype"
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:171.1-172.17 *)
datatype tabletype =
	  mk_tabletype "limits" "reftype"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:171.8-171.17 *)
inductive wf_tabletype :: "tabletype \<Rightarrow> bool" where
	  tabletype_case_0 :
		"(wf_limits v_limits) \<Longrightarrow>
		 wf_tabletype (mk_tabletype v_limits v_reftype)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:173.1-174.14 *)
datatype memtype =
	  PAGE "limits"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:173.8-173.15 *)
inductive wf_memtype :: "memtype \<Rightarrow> bool" where
	  memtype_case_0 :
		"(wf_limits v_limits) \<Longrightarrow>
		 wf_memtype (PAGE v_limits)"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:175.1-176.10 *)
type_synonym elemtype = "reftype"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:177.1-178.5 *)
datatype res_datatype =
	  OK
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:179.1-180.70 *)
datatype externtype =
	  FUNC "functype"
	| GLOBAL "globaltype"
	| TABLE "tabletype"
	| MEM "memtype"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:179.8-179.18 *)
inductive wf_externtype :: "externtype \<Rightarrow> bool" where
	  externtype_case_0 :
		"wf_externtype (FUNC v_functype)"
	| externtype_case_1 :
		"wf_externtype (GLOBAL v_globaltype)"
	| externtype_case_2 :
		"(wf_tabletype v_tabletype) \<Longrightarrow>
		 wf_externtype (TABLE v_tabletype)"
	| externtype_case_3 :
		"(wf_memtype v_memtype) \<Longrightarrow>
		 wf_externtype (MEM v_memtype)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:323.1-323.60 *)
datatype dim =
	  mk_dim "nat"
	

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:323.1-323.60 *)
function (sequential, domintros) proj_dim_0 :: "dim \<Rightarrow> (nat)" where
		  "proj_dim_0 (mk_dim v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:323.8-323.11 *)
inductive wf_dim :: "dim \<Rightarrow> bool" where
	  dim_case_0 :
		"(((((i = 1) \<or> (i = 2)) \<or> (i = 4)) \<or> (i = 8)) \<or> (i = 16)) \<Longrightarrow>
		 wf_dim (mk_dim i)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:324.1-324.69 *)
datatype shape =
	  X "lanetype" "dim"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:324.8-324.13 *)
inductive wf_shape :: "shape \<Rightarrow> bool" where
	  shape_case_0 :
		"(wf_dim v_dim) \<Longrightarrow>
		 wf_shape (X v_lanetype v_dim)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:206.1-206.32 *)
function (sequential, domintros) fun_lanetype :: "shape \<Rightarrow> lanetype" where
		  "fun_lanetype (X v_Lnn (mk_dim v_N)) = v_Lnn"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:208.1-208.59 *)
function (sequential, domintros) size :: "valtype \<Rightarrow> (nat option)" where
		  "size valtype_I32 = (Some 32)"
		| "size valtype_I64 = (Some 64)"
		| "size valtype_F32 = (Some 32)"
		| "size valtype_F64 = (Some 64)"
		| "size valtype_V128 = (Some 128)"
		| "size x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:209.1-209.45 *)
function (sequential, domintros) psize :: "packtype \<Rightarrow> nat" where
		  "psize I8 = 8"
		| "psize I16 = 16"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:210.1-210.45 *)
function (sequential, domintros) lsize :: "lanetype \<Rightarrow> nat" where
		  "lsize lanetype_I32 = (the ((size (valtype_numtype I32))))"
		| "lsize lanetype_I64 = (the ((size (valtype_numtype I64))))"
		| "lsize lanetype_F32 = (the ((size (valtype_numtype F32))))"
		| "lsize lanetype_F64 = (the ((size (valtype_numtype F64))))"
		| "lsize lanetype_I8 = (psize I8)"
		| "lsize lanetype_I16 = (psize I16)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:211.1-211.70 *)
function (sequential, domintros) isize :: "Inn \<Rightarrow> nat" where
		  "isize v_Inn = (the ((size (valtype_Inn v_Inn))))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:212.1-212.70 *)
function (sequential, domintros) jsize :: "Jnn \<Rightarrow> nat" where
		  "jsize v_Jnn = (lsize (lanetype_Jnn v_Jnn))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:213.1-213.70 *)
function (sequential, domintros) fsize :: "Fnn \<Rightarrow> nat" where
		  "fsize v_Fnn = (the ((size (valtype_Fnn v_Fnn))))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:231.1-231.63 *)
function (sequential, domintros) sizenn :: "numtype \<Rightarrow> nat" where
		  "sizenn nt = (the ((size (valtype_numtype nt))))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:232.1-232.63 *)
function (sequential, domintros) sizenn1 :: "numtype \<Rightarrow> nat" where
		  "sizenn1 nt = (the ((size (valtype_numtype nt))))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:233.1-233.63 *)
function (sequential, domintros) sizenn2 :: "numtype \<Rightarrow> nat" where
		  "sizenn2 nt = (the ((size (valtype_numtype nt))))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:238.1-238.63 *)
function (sequential, domintros) lsizenn :: "lanetype \<Rightarrow> nat" where
		  "lsizenn lt = (lsize lt)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:239.1-239.63 *)
function (sequential, domintros) lsizenn1 :: "lanetype \<Rightarrow> nat" where
		  "lsizenn1 lt = (lsize lt)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:240.1-240.63 *)
function (sequential, domintros) lsizenn2 :: "lanetype \<Rightarrow> nat" where
		  "lsizenn2 lt = (lsize lt)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:245.1-245.40 *)
function (sequential, domintros) inv_isize :: "nat \<Rightarrow> (Inn option)" where
		  "inv_isize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some Inn_I32)"
		| "inv_isize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some Inn_I64)"
		| "inv_isize x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:246.1-246.40 *)
function (sequential, domintros) inv_jsize :: "nat \<Rightarrow> (Jnn option)" where
		  "inv_jsize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))) = (Some Jnn_I8)"
		| "inv_jsize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))) = (Some Jnn_I16)"
		| "inv_jsize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some Jnn_I32)"
		| "inv_jsize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some Jnn_I64)"
		| "inv_jsize x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:247.1-247.40 *)
function (sequential, domintros) inv_fsize :: "nat \<Rightarrow> (Fnn option)" where
		  "inv_fsize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some Fnn_F32)"
		| "inv_fsize (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some Fnn_F64)"
		| "inv_fsize x0 = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.1-259.21 *)
datatype num_underscore =
	  mk_num__0 "Inn" "iN"
	| mk_num__1 "Fnn" "fN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.8-259.13 *)
inductive wf_num_underscore :: "numtype \<Rightarrow> num_underscore \<Rightarrow> bool" where
	  num__case_0 :
		"((size (valtype_Inn v_Inn)) \<noteq> None) \<Longrightarrow>
		 (wf_uN (the ((size (valtype_Inn v_Inn)))) var_x) \<Longrightarrow>
		 (v_numtype = (numtype_Inn v_Inn)) \<Longrightarrow>
		 wf_num_underscore v_numtype (mk_num__0 v_Inn var_x)"
	| num__case_1 :
		"(wf_fN (sizenn (numtype_Fnn v_Fnn)) var_x) \<Longrightarrow>
		 (v_numtype = (numtype_Fnn v_Fnn)) \<Longrightarrow>
		 wf_num_underscore v_numtype (mk_num__1 v_Fnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.1-259.21 *)
function (sequential, domintros) proj_num__0 :: "num_underscore \<Rightarrow> (iN option)" where
		  "proj_num__0 (mk_num__0 v_Inn var_x) = (Some var_x)"
		| "proj_num__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.1-259.21 *)
function (sequential, domintros) proj_num__1 :: "num_underscore \<Rightarrow> (fN option)" where
		  "proj_num__1 (mk_num__1 v_Fnn var_x) = (Some var_x)"
		| "proj_num__1 var_x = None"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:263.1-263.36 *)
type_synonym pack_underscore = "iN"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 *)
datatype lane_underscore =
	  mk_lane__0 "numtype" "num_underscore"
	| mk_lane__1 "packtype" "pack_underscore"
	| mk_lane__2 "Jnn" "iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.8-265.14 *)
inductive wf_lane_underscore :: "lanetype \<Rightarrow> lane_underscore \<Rightarrow> bool" where
	  lane__case_0 :
		"(wf_num_underscore v_numtype var_x) \<Longrightarrow>
		 (v_lanetype = (lanetype_numtype v_numtype)) \<Longrightarrow>
		 wf_lane_underscore v_lanetype (mk_lane__0 v_numtype var_x)"
	| lane__case_1 :
		"(wf_uN (psize v_packtype) var_x) \<Longrightarrow>
		 (v_lanetype = (lanetype_packtype v_packtype)) \<Longrightarrow>
		 wf_lane_underscore v_lanetype (mk_lane__1 v_packtype var_x)"
	| lane__case_2 :
		"(wf_uN (lsize (lanetype_Jnn v_Jnn)) var_x) \<Longrightarrow>
		 (v_lanetype = (lanetype_Jnn v_Jnn)) \<Longrightarrow>
		 wf_lane_underscore v_lanetype (mk_lane__2 v_Jnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 *)
function (sequential, domintros) proj_lane__0 :: "lane_underscore \<Rightarrow> (num_underscore option)" where
		  "proj_lane__0 (mk_lane__0 v_numtype var_x) = (Some var_x)"
		| "proj_lane__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 *)
function (sequential, domintros) proj_lane__1 :: "lane_underscore \<Rightarrow> (pack_underscore option)" where
		  "proj_lane__1 (mk_lane__1 v_packtype var_x) = (Some var_x)"
		| "proj_lane__1 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 *)
function (sequential, domintros) proj_lane__2 :: "lane_underscore \<Rightarrow> (iN option)" where
		  "proj_lane__2 (mk_lane__2 v_Jnn var_x) = (Some var_x)"
		| "proj_lane__2 var_x = None"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:270.1-270.34 *)
type_synonym vec_underscore = "vN"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:272.1-272.35 *)
function (sequential, domintros) fun_zero :: "numtype \<Rightarrow> num_underscore" where
		  "fun_zero I32 = (mk_num__0 Inn_I32 (mk_uN 0))"
		| "fun_zero I64 = (mk_num__0 Inn_I64 (mk_uN 0))"
		| "fun_zero F32 = (mk_num__1 Fnn_F32 (fzero (the ((size (valtype_Fnn Fnn_F32))))))"
		| "fun_zero F64 = (mk_num__1 Fnn_F64 (fzero (the ((size (valtype_Fnn Fnn_F64))))))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:272.6-272.11 *)
lemma zero_is_wf :
	"(ret_val = (fun_zero v_numtype)) \<Longrightarrow>
	 (wf_num_underscore v_numtype ret_val)"
sorry

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:279.1-279.42 *)
datatype sx =
	  U
	| S

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.1-280.56 *)
datatype sz =
	  mk_sz "nat"
	

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.1-280.56 *)
function (sequential, domintros) proj_sz_0 :: "sz \<Rightarrow> (nat)" where
		  "proj_sz_0 (mk_sz v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.8-280.10 *)
inductive wf_sz :: "sz \<Rightarrow> bool" where
	  sz_case_0 :
		"((((i = 8) \<or> (i = 16)) \<or> (i = 32)) \<or> (i = 64)) \<Longrightarrow>
		 wf_sz (mk_sz i)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 *)
datatype unop_Inn =
	  CLZ
	| CTZ
	| POPCNT
	| EXTEND "n"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 *)
datatype unop_Fnn =
	  ABS
	| unop_Fnn_NEG
	| SQRT
	| CEIL
	| FLOOR
	| TRUNC
	| NEAREST

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 *)
datatype unop_underscore =
	  mk_unop__0 "Inn" "unop_Inn"
	| mk_unop__1 "Fnn" "unop_Fnn"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.8-282.14 *)
inductive wf_unop_underscore :: "numtype \<Rightarrow> unop_underscore \<Rightarrow> bool" where
	  unop__case_0 :
		"(v_numtype = (numtype_Inn v_Inn)) \<Longrightarrow>
		 wf_unop_underscore v_numtype (mk_unop__0 v_Inn var_x)"
	| unop__case_1 :
		"(v_numtype = (numtype_Fnn v_Fnn)) \<Longrightarrow>
		 wf_unop_underscore v_numtype (mk_unop__1 v_Fnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 *)
function (sequential, domintros) proj_unop__0 :: "unop_underscore \<Rightarrow> (unop_Inn option)" where
		  "proj_unop__0 (mk_unop__0 v_Inn var_x) = (Some var_x)"
		| "proj_unop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 *)
function (sequential, domintros) proj_unop__1 :: "unop_underscore \<Rightarrow> (unop_Fnn option)" where
		  "proj_unop__1 (mk_unop__1 v_Fnn var_x) = (Some var_x)"
		| "proj_unop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 *)
datatype binop_Inn =
	  ADD
	| SUB
	| MUL
	| DIV "sx"
	| REM "sx"
	| AND
	| OR
	| XOR
	| SHL
	| SHR "sx"
	| ROTL
	| ROTR

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 *)
datatype binop_Fnn =
	  binop_Fnn_ADD
	| binop_Fnn_SUB
	| binop_Fnn_MUL
	| binop_Fnn_DIV
	| res_MIN
	| res_MAX
	| COPYSIGN

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 *)
datatype binop_underscore =
	  mk_binop__0 "Inn" "binop_Inn"
	| mk_binop__1 "Fnn" "binop_Fnn"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.8-286.15 *)
inductive wf_binop_underscore :: "numtype \<Rightarrow> binop_underscore \<Rightarrow> bool" where
	  binop__case_0 :
		"(v_numtype = (numtype_Inn v_Inn)) \<Longrightarrow>
		 wf_binop_underscore v_numtype (mk_binop__0 v_Inn var_x)"
	| binop__case_1 :
		"(v_numtype = (numtype_Fnn v_Fnn)) \<Longrightarrow>
		 wf_binop_underscore v_numtype (mk_binop__1 v_Fnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 *)
function (sequential, domintros) proj_binop__0 :: "binop_underscore \<Rightarrow> (binop_Inn option)" where
		  "proj_binop__0 (mk_binop__0 v_Inn var_x) = (Some var_x)"
		| "proj_binop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 *)
function (sequential, domintros) proj_binop__1 :: "binop_underscore \<Rightarrow> (binop_Fnn option)" where
		  "proj_binop__1 (mk_binop__1 v_Fnn var_x) = (Some var_x)"
		| "proj_binop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.24 *)
datatype testop_Inn =
	  EQZ
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.24 *)
datatype testop_underscore =
	  mk_testop__0 "Inn" "testop_Inn"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.8-293.16 *)
inductive wf_testop_underscore :: "numtype \<Rightarrow> testop_underscore \<Rightarrow> bool" where
	  testop__case_0 :
		"(v_numtype = (numtype_Inn v_Inn)) \<Longrightarrow>
		 wf_testop_underscore v_numtype (mk_testop__0 v_Inn var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.24 *)
function (sequential, domintros) proj_testop__0 :: "testop_underscore \<Rightarrow> testop_Inn" where
		  "proj_testop__0 (mk_testop__0 v_Inn var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 *)
datatype relop_Inn =
	  EQ
	| NE
	| LT "sx"
	| GT "sx"
	| LE "sx"
	| GE "sx"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 *)
datatype relop_Fnn =
	  relop_Fnn_EQ
	| relop_Fnn_NE
	| relop_Fnn_LT
	| relop_Fnn_GT
	| relop_Fnn_LE
	| relop_Fnn_GE

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 *)
datatype relop_underscore =
	  mk_relop__0 "Inn" "relop_Inn"
	| mk_relop__1 "Fnn" "relop_Fnn"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.8-297.15 *)
inductive wf_relop_underscore :: "numtype \<Rightarrow> relop_underscore \<Rightarrow> bool" where
	  relop__case_0 :
		"(v_numtype = (numtype_Inn v_Inn)) \<Longrightarrow>
		 wf_relop_underscore v_numtype (mk_relop__0 v_Inn var_x)"
	| relop__case_1 :
		"(v_numtype = (numtype_Fnn v_Fnn)) \<Longrightarrow>
		 wf_relop_underscore v_numtype (mk_relop__1 v_Fnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 *)
function (sequential, domintros) proj_relop__0 :: "relop_underscore \<Rightarrow> (relop_Inn option)" where
		  "proj_relop__0 (mk_relop__0 v_Inn var_x) = (Some var_x)"
		| "proj_relop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 *)
function (sequential, domintros) proj_relop__1 :: "relop_underscore \<Rightarrow> (relop_Fnn option)" where
		  "proj_relop__1 (mk_relop__1 v_Fnn var_x) = (Some var_x)"
		| "proj_relop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 *)
datatype cvtop__Inn_1_Inn_2 =
	  cvtop__Inn_1_Inn_2_EXTEND "sx"
	| WRAP

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.8-305.16 *)
inductive wf_cvtop__Inn_1_Inn_2 :: "Inn \<Rightarrow> Inn \<Rightarrow> cvtop__Inn_1_Inn_2 \<Rightarrow> bool" where
	  cvtop__Inn_1_Inn_2_case_0 :
		"((sizenn1 (numtype_Inn Inn_1)) < (sizenn2 (numtype_Inn Inn_2))) \<Longrightarrow>
		 wf_cvtop__Inn_1_Inn_2 Inn_1 Inn_2 (cvtop__Inn_1_Inn_2_EXTEND v_sx)"
	| cvtop__Inn_1_Inn_2_case_1 :
		"((sizenn1 (numtype_Inn Inn_1)) > (sizenn2 (numtype_Inn Inn_2))) \<Longrightarrow>
		 wf_cvtop__Inn_1_Inn_2 Inn_1 Inn_2 WRAP"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 *)
datatype cvtop__Inn_1_Fnn_2 =
	  CONVERT "sx"
	| REINTERPRET

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.8-305.16 *)
inductive wf_cvtop__Inn_1_Fnn_2 :: "Inn \<Rightarrow> Fnn \<Rightarrow> cvtop__Inn_1_Fnn_2 \<Rightarrow> bool" where
	  cvtop__Inn_1_Fnn_2_case_0 :
		"wf_cvtop__Inn_1_Fnn_2 Inn_1 Fnn_2 (CONVERT v_sx)"
	| cvtop__Inn_1_Fnn_2_case_1 :
		"((sizenn1 (numtype_Inn Inn_1)) = (sizenn2 (numtype_Fnn Fnn_2))) \<Longrightarrow>
		 wf_cvtop__Inn_1_Fnn_2 Inn_1 Fnn_2 REINTERPRET"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 *)
datatype cvtop__Fnn_1_Inn_2 =
	  cvtop__Fnn_1_Inn_2_TRUNC "sx"
	| TRUNC_SAT "sx"
	| cvtop__Fnn_1_Inn_2_REINTERPRET

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.8-305.16 *)
inductive wf_cvtop__Fnn_1_Inn_2 :: "Fnn \<Rightarrow> Inn \<Rightarrow> cvtop__Fnn_1_Inn_2 \<Rightarrow> bool" where
	  cvtop__Fnn_1_Inn_2_case_0 :
		"wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 (cvtop__Fnn_1_Inn_2_TRUNC v_sx)"
	| cvtop__Fnn_1_Inn_2_case_1 :
		"wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 (TRUNC_SAT v_sx)"
	| cvtop__Fnn_1_Inn_2_case_2 :
		"((sizenn1 (numtype_Fnn Fnn_1)) = (sizenn2 (numtype_Inn Inn_2))) \<Longrightarrow>
		 wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 cvtop__Fnn_1_Inn_2_REINTERPRET"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 *)
datatype cvtop__Fnn_1_Fnn_2 =
	  PROMOTE
	| DEMOTE

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.8-305.16 *)
inductive wf_cvtop__Fnn_1_Fnn_2 :: "Fnn \<Rightarrow> Fnn \<Rightarrow> cvtop__Fnn_1_Fnn_2 \<Rightarrow> bool" where
	  cvtop__Fnn_1_Fnn_2_case_0 :
		"((sizenn1 (numtype_Fnn Fnn_1)) < (sizenn2 (numtype_Fnn Fnn_2))) \<Longrightarrow>
		 wf_cvtop__Fnn_1_Fnn_2 Fnn_1 Fnn_2 PROMOTE"
	| cvtop__Fnn_1_Fnn_2_case_1 :
		"((sizenn1 (numtype_Fnn Fnn_1)) > (sizenn2 (numtype_Fnn Fnn_2))) \<Longrightarrow>
		 wf_cvtop__Fnn_1_Fnn_2 Fnn_1 Fnn_2 DEMOTE"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 *)
datatype cvtop__underscore =
	  mk_cvtop___0 "Inn" "Inn" "cvtop__Inn_1_Inn_2"
	| mk_cvtop___1 "Inn" "Fnn" "cvtop__Inn_1_Fnn_2"
	| mk_cvtop___2 "Fnn" "Inn" "cvtop__Fnn_1_Inn_2"
	| mk_cvtop___3 "Fnn" "Fnn" "cvtop__Fnn_1_Fnn_2"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.8-305.16 *)
inductive wf_cvtop__underscore :: "numtype \<Rightarrow> numtype \<Rightarrow> cvtop__underscore \<Rightarrow> bool" where
	  cvtop___case_0 :
		"(wf_cvtop__Inn_1_Inn_2 Inn_1 Inn_2 var_x) \<Longrightarrow>
		 (numtype_1 = (numtype_Inn Inn_1)) \<Longrightarrow>
		 (numtype_2 = (numtype_Inn Inn_2)) \<Longrightarrow>
		 wf_cvtop__underscore numtype_1 numtype_2 (mk_cvtop___0 Inn_1 Inn_2 var_x)"
	| cvtop___case_1 :
		"(wf_cvtop__Inn_1_Fnn_2 Inn_1 Fnn_2 var_x) \<Longrightarrow>
		 (numtype_1 = (numtype_Inn Inn_1)) \<Longrightarrow>
		 (numtype_2 = (numtype_Fnn Fnn_2)) \<Longrightarrow>
		 wf_cvtop__underscore numtype_1 numtype_2 (mk_cvtop___1 Inn_1 Fnn_2 var_x)"
	| cvtop___case_2 :
		"(wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 var_x) \<Longrightarrow>
		 (numtype_1 = (numtype_Fnn Fnn_1)) \<Longrightarrow>
		 (numtype_2 = (numtype_Inn Inn_2)) \<Longrightarrow>
		 wf_cvtop__underscore numtype_1 numtype_2 (mk_cvtop___2 Fnn_1 Inn_2 var_x)"
	| cvtop___case_3 :
		"(wf_cvtop__Fnn_1_Fnn_2 Fnn_1 Fnn_2 var_x) \<Longrightarrow>
		 (numtype_1 = (numtype_Fnn Fnn_1)) \<Longrightarrow>
		 (numtype_2 = (numtype_Fnn Fnn_2)) \<Longrightarrow>
		 wf_cvtop__underscore numtype_1 numtype_2 (mk_cvtop___3 Fnn_1 Fnn_2 var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 *)
function (sequential, domintros) proj_cvtop___0 :: "cvtop__underscore \<Rightarrow> (cvtop__Inn_1_Inn_2 option)" where
		  "proj_cvtop___0 (mk_cvtop___0 Inn_1 Inn_2 var_x) = (Some var_x)"
		| "proj_cvtop___0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 *)
function (sequential, domintros) proj_cvtop___1 :: "cvtop__underscore \<Rightarrow> (cvtop__Inn_1_Fnn_2 option)" where
		  "proj_cvtop___1 (mk_cvtop___1 Inn_1 Fnn_2 var_x) = (Some var_x)"
		| "proj_cvtop___1 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 *)
function (sequential, domintros) proj_cvtop___2 :: "cvtop__underscore \<Rightarrow> (cvtop__Fnn_1_Inn_2 option)" where
		  "proj_cvtop___2 (mk_cvtop___2 Fnn_1 Inn_2 var_x) = (Some var_x)"
		| "proj_cvtop___2 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 *)
function (sequential, domintros) proj_cvtop___3 :: "cvtop__underscore \<Rightarrow> (cvtop__Fnn_1_Fnn_2 option)" where
		  "proj_cvtop___3 (mk_cvtop___3 Fnn_1 Fnn_2 var_x) = (Some var_x)"
		| "proj_cvtop___3 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:325.1-325.69 *)
datatype ishape =
	  ishape_X "Jnn" "dim"
	

(* Auxiliary Definition at:  *)
function (sequential, domintros) shape_ishape :: "ishape \<Rightarrow> shape" where
		  "shape_ishape (ishape_X x0 x1) = (X (lanetype_Jnn x0) x1)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:325.8-325.14 *)
inductive wf_ishape :: "ishape \<Rightarrow> bool" where
	  ishape_case_0 :
		"(wf_dim v_dim) \<Longrightarrow>
		 wf_ishape (ishape_X v_Jnn v_dim)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:326.1-326.69 *)
datatype fshape =
	  fshape_X "Fnn" "dim"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:326.8-326.14 *)
inductive wf_fshape :: "fshape \<Rightarrow> bool" where
	  fshape_case_0 :
		"(wf_dim v_dim) \<Longrightarrow>
		 wf_fshape (fshape_X v_Fnn v_dim)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:327.1-327.69 *)
datatype pshape =
	  pshape_X "Pnn" "dim"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:327.8-327.14 *)
inductive wf_pshape :: "pshape \<Rightarrow> bool" where
	  pshape_case_0 :
		"(wf_dim v_dim) \<Longrightarrow>
		 wf_pshape (pshape_X v_Pnn v_dim)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:329.1-329.22 *)
function (sequential, domintros) fun_dim :: "shape \<Rightarrow> dim" where
		  "fun_dim (X v_Lnn (mk_dim v_N)) = (mk_dim v_N)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:329.6-329.10 *)
lemma dim_is_wf :
	"(wf_shape v_shape) \<Longrightarrow>
	 (ret_val = (fun_dim v_shape)) \<Longrightarrow>
	 (wf_dim ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:330.1-330.41 *)
function (sequential, domintros) shsize :: "shape \<Rightarrow> nat" where
		  "shsize (X v_Lnn (mk_dim v_N)) = ((lsize v_Lnn) * v_N)"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.20 *)
datatype vvunop =
	  NOT
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:333.1-333.41 *)
datatype vvbinop =
	  vvbinop_AND
	| ANDNOT
	| vvbinop_OR
	| vvbinop_XOR

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:334.1-334.28 *)
datatype vvternop =
	  BITSELECT
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:335.1-335.27 *)
datatype vvtestop =
	  ANY_TRUE
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.21 *)
datatype vunop_Jnn_N =
	  vunop_Jnn_N_ABS
	| vunop_Jnn_N_NEG
	| vunop_Jnn_N_POPCNT

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.8-337.15 *)
inductive wf_vunop_Jnn_N :: "Jnn \<Rightarrow> N \<Rightarrow> vunop_Jnn_N \<Rightarrow> bool" where
	  vunop_Jnn_N_case_0 :
		"wf_vunop_Jnn_N v_Jnn v_N vunop_Jnn_N_ABS"
	| vunop_Jnn_N_case_1 :
		"wf_vunop_Jnn_N v_Jnn v_N vunop_Jnn_N_NEG"
	| vunop_Jnn_N_case_2 :
		"(v_Jnn = Jnn_I8) \<Longrightarrow>
		 wf_vunop_Jnn_N v_Jnn v_N vunop_Jnn_N_POPCNT"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.21 *)
datatype vunop_Fnn_N =
	  vunop_Fnn_N_ABS
	| vunop_Fnn_N_NEG
	| vunop_Fnn_N_SQRT
	| vunop_Fnn_N_CEIL
	| vunop_Fnn_N_FLOOR
	| vunop_Fnn_N_TRUNC
	| vunop_Fnn_N_NEAREST

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.21 *)
datatype vunop_underscore =
	  mk_vunop__0 "Jnn" "N" "vunop_Jnn_N"
	| mk_vunop__1 "Fnn" "N" "vunop_Fnn_N"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.8-337.15 *)
inductive wf_vunop_underscore :: "shape \<Rightarrow> vunop_underscore \<Rightarrow> bool" where
	  vunop__case_0 :
		"(wf_vunop_Jnn_N v_Jnn v_N var_x) \<Longrightarrow>
		 (v_shape = (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) \<Longrightarrow>
		 wf_vunop_underscore v_shape (mk_vunop__0 v_Jnn v_N var_x)"
	| vunop__case_1 :
		"(v_shape = (X (lanetype_Fnn v_Fnn) (mk_dim v_N))) \<Longrightarrow>
		 wf_vunop_underscore v_shape (mk_vunop__1 v_Fnn v_N var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.21 *)
function (sequential, domintros) proj_vunop__0 :: "vunop_underscore \<Rightarrow> (vunop_Jnn_N option)" where
		  "proj_vunop__0 (mk_vunop__0 v_Jnn v_N var_x) = (Some var_x)"
		| "proj_vunop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.21 *)
function (sequential, domintros) proj_vunop__1 :: "vunop_underscore \<Rightarrow> (vunop_Fnn_N option)" where
		  "proj_vunop__1 (mk_vunop__1 v_Fnn v_N var_x) = (Some var_x)"
		| "proj_vunop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.1-342.22 *)
datatype vbinop_Jnn_N =
	  vbinop_Jnn_N_ADD
	| vbinop_Jnn_N_SUB
	| ADD_SAT "sx"
	| SUB_SAT "sx"
	| vbinop_Jnn_N_MUL
	| AVGRU
	| Q15MULR_SATS
	| vbinop_Jnn_N_MIN "sx"
	| vbinop_Jnn_N_MAX "sx"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.8-342.16 *)
inductive wf_vbinop_Jnn_N :: "Jnn \<Rightarrow> N \<Rightarrow> vbinop_Jnn_N \<Rightarrow> bool" where
	  vbinop_Jnn_N_case_0 :
		"wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N_ADD"
	| vbinop_Jnn_N_case_1 :
		"wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N_SUB"
	| vbinop_Jnn_N_case_2 :
		"((lsizenn (lanetype_Jnn v_Jnn)) \<le> 16) \<Longrightarrow>
		 wf_vbinop_Jnn_N v_Jnn v_N (ADD_SAT v_sx)"
	| vbinop_Jnn_N_case_3 :
		"((lsizenn (lanetype_Jnn v_Jnn)) \<le> 16) \<Longrightarrow>
		 wf_vbinop_Jnn_N v_Jnn v_N (SUB_SAT v_sx)"
	| vbinop_Jnn_N_case_4 :
		"((lsizenn (lanetype_Jnn v_Jnn)) \<ge> 16) \<Longrightarrow>
		 wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N_MUL"
	| vbinop_Jnn_N_case_5 :
		"((lsizenn (lanetype_Jnn v_Jnn)) \<le> 16) \<Longrightarrow>
		 wf_vbinop_Jnn_N v_Jnn v_N AVGRU"
	| vbinop_Jnn_N_case_6 :
		"((lsizenn (lanetype_Jnn v_Jnn)) = 16) \<Longrightarrow>
		 wf_vbinop_Jnn_N v_Jnn v_N Q15MULR_SATS"
	| vbinop_Jnn_N_case_7 :
		"((lsizenn (lanetype_Jnn v_Jnn)) \<le> 32) \<Longrightarrow>
		 wf_vbinop_Jnn_N v_Jnn v_N (vbinop_Jnn_N_MIN v_sx)"
	| vbinop_Jnn_N_case_8 :
		"((lsizenn (lanetype_Jnn v_Jnn)) \<le> 32) \<Longrightarrow>
		 wf_vbinop_Jnn_N v_Jnn v_N (vbinop_Jnn_N_MAX v_sx)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.1-342.22 *)
datatype vbinop_Fnn_N =
	  vbinop_Fnn_N_ADD
	| vbinop_Fnn_N_SUB
	| vbinop_Fnn_N_MUL
	| vbinop_Fnn_N_DIV
	| vbinop_Fnn_N_MIN
	| vbinop_Fnn_N_MAX
	| PMIN
	| PMAX

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.1-342.22 *)
datatype vbinop_underscore =
	  mk_vbinop__0 "Jnn" "N" "vbinop_Jnn_N"
	| mk_vbinop__1 "Fnn" "N" "vbinop_Fnn_N"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.8-342.16 *)
inductive wf_vbinop_underscore :: "shape \<Rightarrow> vbinop_underscore \<Rightarrow> bool" where
	  vbinop__case_0 :
		"(wf_vbinop_Jnn_N v_Jnn v_N var_x) \<Longrightarrow>
		 (v_shape = (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) \<Longrightarrow>
		 wf_vbinop_underscore v_shape (mk_vbinop__0 v_Jnn v_N var_x)"
	| vbinop__case_1 :
		"(v_shape = (X (lanetype_Fnn v_Fnn) (mk_dim v_N))) \<Longrightarrow>
		 wf_vbinop_underscore v_shape (mk_vbinop__1 v_Fnn v_N var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.1-342.22 *)
function (sequential, domintros) proj_vbinop__0 :: "vbinop_underscore \<Rightarrow> (vbinop_Jnn_N option)" where
		  "proj_vbinop__0 (mk_vbinop__0 v_Jnn v_N var_x) = (Some var_x)"
		| "proj_vbinop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.1-342.22 *)
function (sequential, domintros) proj_vbinop__1 :: "vbinop_underscore \<Rightarrow> (vbinop_Fnn_N option)" where
		  "proj_vbinop__1 (mk_vbinop__1 v_Fnn v_N var_x) = (Some var_x)"
		| "proj_vbinop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:355.1-355.23 *)
datatype vtestop_Jnn_N =
	  ALL_TRUE
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:355.1-355.23 *)
datatype vtestop_underscore =
	  mk_vtestop__0 "Jnn" "N" "vtestop_Jnn_N"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:355.8-355.17 *)
inductive wf_vtestop_underscore :: "shape \<Rightarrow> vtestop_underscore \<Rightarrow> bool" where
	  vtestop__case_0 :
		"(v_shape = (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) \<Longrightarrow>
		 wf_vtestop_underscore v_shape (mk_vtestop__0 v_Jnn v_N var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:355.1-355.23 *)
function (sequential, domintros) proj_vtestop__0 :: "vtestop_underscore \<Rightarrow> vtestop_Jnn_N" where
		  "proj_vtestop__0 (mk_vtestop__0 v_Jnn v_N var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:359.1-359.22 *)
datatype vrelop_Jnn_N =
	  vrelop_Jnn_N_EQ
	| vrelop_Jnn_N_NE
	| vrelop_Jnn_N_LT "sx"
	| vrelop_Jnn_N_GT "sx"
	| vrelop_Jnn_N_LE "sx"
	| vrelop_Jnn_N_GE "sx"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:359.8-359.16 *)
inductive wf_vrelop_Jnn_N :: "Jnn \<Rightarrow> N \<Rightarrow> vrelop_Jnn_N \<Rightarrow> bool" where
	  vrelop_Jnn_N_case_0 :
		"wf_vrelop_Jnn_N v_Jnn v_N vrelop_Jnn_N_EQ"
	| vrelop_Jnn_N_case_1 :
		"wf_vrelop_Jnn_N v_Jnn v_N vrelop_Jnn_N_NE"
	| vrelop_Jnn_N_case_2 :
		"(((lsizenn (lanetype_Jnn v_Jnn)) \<noteq> 64) \<or> (v_sx = S)) \<Longrightarrow>
		 wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N_LT v_sx)"
	| vrelop_Jnn_N_case_3 :
		"(((lsizenn (lanetype_Jnn v_Jnn)) \<noteq> 64) \<or> (v_sx = S)) \<Longrightarrow>
		 wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N_GT v_sx)"
	| vrelop_Jnn_N_case_4 :
		"(((lsizenn (lanetype_Jnn v_Jnn)) \<noteq> 64) \<or> (v_sx = S)) \<Longrightarrow>
		 wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N_LE v_sx)"
	| vrelop_Jnn_N_case_5 :
		"(((lsizenn (lanetype_Jnn v_Jnn)) \<noteq> 64) \<or> (v_sx = S)) \<Longrightarrow>
		 wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N_GE v_sx)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:359.1-359.22 *)
datatype vrelop_Fnn_N =
	  vrelop_Fnn_N_EQ
	| vrelop_Fnn_N_NE
	| vrelop_Fnn_N_LT
	| vrelop_Fnn_N_GT
	| vrelop_Fnn_N_LE
	| vrelop_Fnn_N_GE

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:359.1-359.22 *)
datatype vrelop_underscore =
	  mk_vrelop__0 "Jnn" "N" "vrelop_Jnn_N"
	| mk_vrelop__1 "Fnn" "N" "vrelop_Fnn_N"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:359.8-359.16 *)
inductive wf_vrelop_underscore :: "shape \<Rightarrow> vrelop_underscore \<Rightarrow> bool" where
	  vrelop__case_0 :
		"(wf_vrelop_Jnn_N v_Jnn v_N var_x) \<Longrightarrow>
		 (v_shape = (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) \<Longrightarrow>
		 wf_vrelop_underscore v_shape (mk_vrelop__0 v_Jnn v_N var_x)"
	| vrelop__case_1 :
		"(v_shape = (X (lanetype_Fnn v_Fnn) (mk_dim v_N))) \<Longrightarrow>
		 wf_vrelop_underscore v_shape (mk_vrelop__1 v_Fnn v_N var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:359.1-359.22 *)
function (sequential, domintros) proj_vrelop__0 :: "vrelop_underscore \<Rightarrow> (vrelop_Jnn_N option)" where
		  "proj_vrelop__0 (mk_vrelop__0 v_Jnn v_N var_x) = (Some var_x)"
		| "proj_vrelop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:359.1-359.22 *)
function (sequential, domintros) proj_vrelop__1 :: "vrelop_underscore \<Rightarrow> (vrelop_Fnn_N option)" where
		  "proj_vrelop__1 (mk_vrelop__1 v_Fnn v_N var_x) = (Some var_x)"
		| "proj_vrelop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:367.1-367.48 *)
datatype half =
	  LOW
	| HIGH

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:368.1-368.19 *)
datatype zero =
	  ZERO
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.1-370.99 *)
datatype vcvtop =
	  vcvtop_EXTEND "half" "sx"
	| vcvtop_TRUNC_SAT "sx" "(zero option)"
	| vcvtop_CONVERT "(half option)" "sx"
	| vcvtop_DEMOTE "zero"
	| PROMOTELOW

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:372.1-372.25 *)
datatype vshiftop_Jnn_N =
	  vshiftop_Jnn_N_SHL
	| vshiftop_Jnn_N_SHR "sx"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:372.1-372.25 *)
datatype vshiftop_underscore =
	  mk_vshiftop__0 "Jnn" "N" "vshiftop_Jnn_N"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:372.8-372.18 *)
inductive wf_vshiftop_underscore :: "ishape \<Rightarrow> vshiftop_underscore \<Rightarrow> bool" where
	  vshiftop__case_0 :
		"(v_ishape = (ishape_X v_Jnn (mk_dim v_N))) \<Longrightarrow>
		 wf_vshiftop_underscore v_ishape (mk_vshiftop__0 v_Jnn v_N var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:372.1-372.25 *)
function (sequential, domintros) proj_vshiftop__0 :: "vshiftop_underscore \<Rightarrow> vshiftop_Jnn_N" where
		  "proj_vshiftop__0 (mk_vshiftop__0 v_Jnn v_N var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:375.1-375.25 *)
datatype vextunop_Jnn_N =
	  EXTADD_PAIRWISE "sx"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:375.8-375.18 *)
inductive wf_vextunop_Jnn_N :: "Jnn \<Rightarrow> N \<Rightarrow> vextunop_Jnn_N \<Rightarrow> bool" where
	  vextunop_Jnn_N_case_0 :
		"((16 \<le> (lsizenn (lanetype_Jnn v_Jnn))) \<and> ((lsizenn (lanetype_Jnn v_Jnn)) \<le> 32)) \<Longrightarrow>
		 wf_vextunop_Jnn_N v_Jnn v_N (EXTADD_PAIRWISE v_sx)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:375.1-375.25 *)
datatype vextunop_underscore =
	  mk_vextunop__0 "Jnn" "N" "vextunop_Jnn_N"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:375.8-375.18 *)
inductive wf_vextunop_underscore :: "ishape \<Rightarrow> vextunop_underscore \<Rightarrow> bool" where
	  vextunop__case_0 :
		"(wf_vextunop_Jnn_N v_Jnn v_N var_x) \<Longrightarrow>
		 (v_ishape = (ishape_X v_Jnn (mk_dim v_N))) \<Longrightarrow>
		 wf_vextunop_underscore v_ishape (mk_vextunop__0 v_Jnn v_N var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:375.1-375.25 *)
function (sequential, domintros) proj_vextunop__0 :: "vextunop_underscore \<Rightarrow> vextunop_Jnn_N" where
		  "proj_vextunop__0 (mk_vextunop__0 v_Jnn v_N var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:378.1-378.26 *)
datatype vextbinop_Jnn_N =
	  EXTMUL "half" "sx"
	| DOTS

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:378.8-378.19 *)
inductive wf_vextbinop_Jnn_N :: "Jnn \<Rightarrow> N \<Rightarrow> vextbinop_Jnn_N \<Rightarrow> bool" where
	  vextbinop_Jnn_N_case_0 :
		"wf_vextbinop_Jnn_N v_Jnn v_N (EXTMUL v_half v_sx)"
	| vextbinop_Jnn_N_case_1 :
		"((lsizenn (lanetype_Jnn v_Jnn)) = 32) \<Longrightarrow>
		 wf_vextbinop_Jnn_N v_Jnn v_N DOTS"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:378.1-378.26 *)
datatype vextbinop_underscore =
	  mk_vextbinop__0 "Jnn" "N" "vextbinop_Jnn_N"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:378.8-378.19 *)
inductive wf_vextbinop_underscore :: "ishape \<Rightarrow> vextbinop_underscore \<Rightarrow> bool" where
	  vextbinop__case_0 :
		"(wf_vextbinop_Jnn_N v_Jnn v_N var_x) \<Longrightarrow>
		 (v_ishape = (ishape_X v_Jnn (mk_dim v_N))) \<Longrightarrow>
		 wf_vextbinop_underscore v_ishape (mk_vextbinop__0 v_Jnn v_N var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:378.1-378.26 *)
function (sequential, domintros) proj_vextbinop__0 :: "vextbinop_underscore \<Rightarrow> vextbinop_Jnn_N" where
		  "proj_vextbinop__0 (mk_vextbinop__0 v_Jnn v_N var_x) = var_x"
	by pat_completeness auto

(* Record Creation Definition at: ../specification/wasm-2.0/1-syntax.spectec:386.1-386.69 *)
record memarg =
	ALIGN :: "u32"
	OFFSET :: "u32"

definition append_memarg :: "memarg \<Rightarrow> memarg \<Rightarrow> memarg" where
	"append_memarg arg1 arg2 = \<lparr>
		ALIGN = ALIGN arg1,
		OFFSET = OFFSET arg1
	\<rparr>"



(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:386.8-386.14 *)
inductive wf_memarg :: "memarg \<Rightarrow> bool" where
	  memarg_case_underscore :
		"(wf_uN 32 var_0) \<Longrightarrow>
		 (wf_uN 32 var_1) \<Longrightarrow>
		 wf_memarg \<lparr> ALIGN = var_0, OFFSET = var_1 \<rparr>"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:390.1-390.24 *)
datatype loadop_Inn =
	  mk_loadop_Inn "sz" "sx"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:390.8-390.16 *)
inductive wf_loadop_Inn :: "Inn \<Rightarrow> loadop_Inn \<Rightarrow> bool" where
	  loadop_Inn_case_0 :
		"(wf_sz v_sz) \<Longrightarrow>
		 ((proj_sz_0 v_sz) < (sizenn (numtype_Inn v_Inn))) \<Longrightarrow>
		 wf_loadop_Inn v_Inn (mk_loadop_Inn v_sz v_sx)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:390.1-390.24 *)
datatype loadop_underscore =
	  mk_loadop__0 "Inn" "loadop_Inn"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:390.8-390.16 *)
inductive wf_loadop_underscore :: "numtype \<Rightarrow> loadop_underscore \<Rightarrow> bool" where
	  loadop__case_0 :
		"(wf_loadop_Inn v_Inn var_x) \<Longrightarrow>
		 (v_numtype = (numtype_Inn v_Inn)) \<Longrightarrow>
		 wf_loadop_underscore v_numtype (mk_loadop__0 v_Inn var_x)"

(* Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:390.1-390.24 *)
function (sequential, domintros) proj_loadop__0 :: "loadop_underscore \<Rightarrow> loadop_Inn" where
		  "proj_loadop__0 (mk_loadop__0 v_Inn var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:393.1-396.46 *)
datatype vloadop =
	  SHAPEX_underscore "nat" "nat" "sx"
	| SPLAT "nat"
	| vloadop_ZERO "nat"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:403.1-405.17 *)
datatype blocktype =
	  underscore_RESULT "(valtype option)"
	| underscore_IDX "typeidx"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:403.8-403.17 *)
inductive wf_blocktype :: "blocktype \<Rightarrow> bool" where
	  blocktype_case_0 :
		"wf_blocktype (underscore_RESULT valtype_opt)"
	| blocktype_case_1 :
		"(wf_uN 32 v_typeidx) \<Longrightarrow>
		 wf_blocktype (underscore_IDX v_typeidx)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:524.1-525.22 *)
datatype instr_st6 =
	  MEMORY_COPY
	| MEMORY_FILL
	| MEMORY_GROW
	| MEMORY_SIZE
	| VSTORE_LANE "vectype" "sz" "memarg" "laneidx"
	| VSTORE "vectype" "memarg"
	| VLOAD_LANE "vectype" "sz" "memarg" "laneidx"
	| VLOAD "vectype" "(vloadop option)" "memarg"
	| STORE "numtype" "(sz option)" "memarg"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:524.1-525.22 *)
datatype instr_st5 =
	  LOAD "numtype" "(loadop_underscore option)" "memarg"
	| ELEM_DROP "elemidx"
	| TABLE_INIT "tableidx" "elemidx"
	| TABLE_COPY "tableidx" "tableidx"
	| TABLE_FILL "tableidx"
	| TABLE_GROW "tableidx"
	| TABLE_SIZE "tableidx"
	| TABLE_SET "tableidx"
	| TABLE_GET "tableidx"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:524.1-525.22 *)
datatype instr_st4 =
	  GLOBAL_SET "globalidx"
	| GLOBAL_GET "globalidx"
	| LOCAL_TEE "localidx"
	| LOCAL_SET "localidx"
	| LOCAL_GET "localidx"
	| REF_IS_NULL
	| REF_FUNC "funcidx"
	| REF_NULL "reftype"
	| VCVTOP "shape" "shape" "vcvtop"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:524.1-525.22 *)
datatype instr_st3 =
	  VNARROW "ishape" "ishape" "sx"
	| VEXTBINOP "ishape" "ishape" "vextbinop_underscore"
	| VEXTUNOP "ishape" "ishape" "vextunop_underscore"
	| VREPLACE_LANE "shape" "laneidx"
	| VEXTRACT_LANE "shape" "(sx option)" "laneidx"
	| VSPLAT "shape"
	| VSHUFFLE "ishape" "(laneidx list)"
	| VSWIZZLE "ishape"
	| VBITMASK "ishape"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:524.1-525.22 *)
datatype instr_st2 =
	  VSHIFTOP "ishape" "vshiftop_underscore"
	| VRELOP "shape" "vrelop_underscore"
	| VTESTOP "shape" "vtestop_underscore"
	| VBINOP "shape" "vbinop_underscore"
	| VUNOP "shape" "vunop_underscore"
	| VVTESTOP "vectype" "vvtestop"
	| VVTERNOP "vectype" "vvternop"
	| VVBINOP "vectype" "vvbinop"
	| VVUNOP "vectype" "vvunop"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:524.1-525.22 *)
datatype instr_st1 =
	  VCONST "vectype" "vec_underscore"
	| instr_st1_EXTEND "numtype" "n"
	| CVTOP "numtype" "numtype" "cvtop__underscore"
	| RELOP "numtype" "relop_underscore"
	| TESTOP "numtype" "testop_underscore"
	| BINOP "numtype" "binop_underscore"
	| UNOP "numtype" "unop_underscore"
	| res_CONST "numtype" "num_underscore"
	| RETURN

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:524.1-525.22 *)
datatype instr_st0 =
	  CALL_INDIRECT "tableidx" "typeidx"
	| CALL "funcidx"
	| BR_TABLE "(labelidx list)" "labelidx"
	| BR_IF "labelidx"
	| BR "labelidx"
	| SELECT "((valtype list) option)"
	| DROP
	| UNREACHABLE
	| NOP

(* Mutual Recursion at: ../specification/wasm-2.0/1-syntax.spectec:524.1-525.22 *)
datatype instr =
	  instr_sc0 "instr_st0"
	| instr_sc1 "instr_st1"
	| instr_sc2 "instr_st2"
	| instr_sc3 "instr_st3"
	| instr_sc4 "instr_st4"
	| instr_sc5 "instr_st5"
	| instr_sc6 "instr_st6"
	| instr_sc7 "instr_st7"

and

instr_st7 =
	  IFELSE "blocktype" "(instr list)" "(instr list)"
	| LOOP "blocktype" "(instr list)"
	| BLOCK "blocktype" "(instr list)"
	| DATA_DROP "dataidx"
	| MEMORY_INIT "dataidx"

(* Mutual Recursion at: ../specification/wasm-2.0/1-syntax.spectec:524.1-525.22 *)
inductive wf_instr :: "instr \<Rightarrow> bool" where
	  instr_case_0 :
		"wf_instr (instr_sc0 NOP)"
	| instr_case_1 :
		"wf_instr (instr_sc0 UNREACHABLE)"
	| instr_case_2 :
		"wf_instr (instr_sc0 DROP)"
	| instr_case_3 :
		"wf_instr (instr_sc0 (SELECT valtype_lst_opt))"
	| instr_case_4 :
		"(wf_blocktype v_blocktype) \<Longrightarrow>
		 list_all (\<lambda> (v_instr :: instr). (wf_instr v_instr)) instr_lst \<Longrightarrow>
		 wf_instr (instr_sc7 (BLOCK v_blocktype instr_lst))"
	| instr_case_5 :
		"(wf_blocktype v_blocktype) \<Longrightarrow>
		 list_all (\<lambda> (v_instr :: instr). (wf_instr v_instr)) instr_lst \<Longrightarrow>
		 wf_instr (instr_sc7 (LOOP v_blocktype instr_lst))"
	| instr_case_6 :
		"(wf_blocktype v_blocktype) \<Longrightarrow>
		 list_all (\<lambda> (v_instr :: instr). (wf_instr v_instr)) instr_lst \<Longrightarrow>
		 list_all (\<lambda> (instr_lst_0 :: instr). (wf_instr instr_lst_0)) instr_lst_0_lst \<Longrightarrow>
		 wf_instr (instr_sc7 (IFELSE v_blocktype instr_lst instr_lst_0_lst))"
	| instr_case_7 :
		"(wf_uN 32 v_labelidx) \<Longrightarrow>
		 wf_instr (instr_sc0 (BR v_labelidx))"
	| instr_case_8 :
		"(wf_uN 32 v_labelidx) \<Longrightarrow>
		 wf_instr (instr_sc0 (BR_IF v_labelidx))"
	| instr_case_9 :
		"list_all (\<lambda> (v_labelidx :: labelidx). (wf_uN 32 v_labelidx)) labelidx_lst \<Longrightarrow>
		 (wf_uN 32 v_labelidx) \<Longrightarrow>
		 wf_instr (instr_sc0 (BR_TABLE labelidx_lst v_labelidx))"
	| instr_case_10 :
		"(wf_uN 32 v_funcidx) \<Longrightarrow>
		 wf_instr (instr_sc0 (CALL v_funcidx))"
	| instr_case_11 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 (wf_uN 32 v_typeidx) \<Longrightarrow>
		 wf_instr (instr_sc0 (CALL_INDIRECT v_tableidx v_typeidx))"
	| instr_case_12 :
		"wf_instr (instr_sc1 RETURN)"
	| instr_case_13 :
		"(wf_num_underscore v_numtype var_0) \<Longrightarrow>
		 wf_instr (instr_sc1 (res_CONST v_numtype var_0))"
	| instr_case_14 :
		"(wf_unop_underscore v_numtype var_0) \<Longrightarrow>
		 wf_instr (instr_sc1 (UNOP v_numtype var_0))"
	| instr_case_15 :
		"(wf_binop_underscore v_numtype var_0) \<Longrightarrow>
		 wf_instr (instr_sc1 (BINOP v_numtype var_0))"
	| instr_case_16 :
		"(wf_testop_underscore v_numtype var_0) \<Longrightarrow>
		 wf_instr (instr_sc1 (TESTOP v_numtype var_0))"
	| instr_case_17 :
		"(wf_relop_underscore v_numtype var_0) \<Longrightarrow>
		 wf_instr (instr_sc1 (RELOP v_numtype var_0))"
	| instr_case_18 :
		"(wf_cvtop__underscore numtype_2 numtype_1 var_0) \<Longrightarrow>
		 (numtype_1 \<noteq> numtype_2) \<Longrightarrow>
		 wf_instr (instr_sc1 (CVTOP numtype_1 numtype_2 var_0))"
	| instr_case_19 :
		"wf_instr (instr_sc1 (instr_st1_EXTEND v_numtype v_n))"
	| instr_case_20 :
		"((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
		 (wf_uN (the ((size (valtype_vectype v_vectype)))) var_0) \<Longrightarrow>
		 wf_instr (instr_sc1 (VCONST v_vectype var_0))"
	| instr_case_21 :
		"wf_instr (instr_sc2 (VVUNOP v_vectype v_vvunop))"
	| instr_case_22 :
		"wf_instr (instr_sc2 (VVBINOP v_vectype v_vvbinop))"
	| instr_case_23 :
		"wf_instr (instr_sc2 (VVTERNOP v_vectype v_vvternop))"
	| instr_case_24 :
		"wf_instr (instr_sc2 (VVTESTOP v_vectype v_vvtestop))"
	| instr_case_25 :
		"(wf_shape v_shape) \<Longrightarrow>
		 (wf_vunop_underscore v_shape var_0) \<Longrightarrow>
		 wf_instr (instr_sc2 (VUNOP v_shape var_0))"
	| instr_case_26 :
		"(wf_shape v_shape) \<Longrightarrow>
		 (wf_vbinop_underscore v_shape var_0) \<Longrightarrow>
		 wf_instr (instr_sc2 (VBINOP v_shape var_0))"
	| instr_case_27 :
		"(wf_shape v_shape) \<Longrightarrow>
		 (wf_vtestop_underscore v_shape var_0) \<Longrightarrow>
		 wf_instr (instr_sc2 (VTESTOP v_shape var_0))"
	| instr_case_28 :
		"(wf_shape v_shape) \<Longrightarrow>
		 (wf_vrelop_underscore v_shape var_0) \<Longrightarrow>
		 wf_instr (instr_sc2 (VRELOP v_shape var_0))"
	| instr_case_29 :
		"(wf_ishape v_ishape) \<Longrightarrow>
		 (wf_vshiftop_underscore v_ishape var_0) \<Longrightarrow>
		 wf_instr (instr_sc2 (VSHIFTOP v_ishape var_0))"
	| instr_case_30 :
		"(wf_ishape v_ishape) \<Longrightarrow>
		 wf_instr (instr_sc3 (VBITMASK v_ishape))"
	| instr_case_31 :
		"(wf_ishape v_ishape) \<Longrightarrow>
		 (v_ishape = (ishape_X Jnn_I8 (mk_dim 16))) \<Longrightarrow>
		 wf_instr (instr_sc3 (VSWIZZLE v_ishape))"
	| instr_case_32 :
		"(wf_ishape v_ishape) \<Longrightarrow>
		 list_all (\<lambda> (v_laneidx :: laneidx). (wf_uN 8 v_laneidx)) laneidx_lst \<Longrightarrow>
		 ((v_ishape = (ishape_X Jnn_I8 (mk_dim 16))) \<and> ((length laneidx_lst) = 16)) \<Longrightarrow>
		 wf_instr (instr_sc3 (VSHUFFLE v_ishape laneidx_lst))"
	| instr_case_33 :
		"(wf_shape v_shape) \<Longrightarrow>
		 wf_instr (instr_sc3 (VSPLAT v_shape))"
	| instr_case_34 :
		"(wf_shape v_shape) \<Longrightarrow>
		 (wf_uN 8 v_laneidx) \<Longrightarrow>
		 (((fun_lanetype v_shape) = (lanetype_numtype v_numtype)) \<longleftrightarrow> (sx_opt = None)) \<Longrightarrow>
		 wf_instr (instr_sc3 (VEXTRACT_LANE v_shape sx_opt v_laneidx))"
	| instr_case_35 :
		"(wf_shape v_shape) \<Longrightarrow>
		 (wf_uN 8 v_laneidx) \<Longrightarrow>
		 wf_instr (instr_sc3 (VREPLACE_LANE v_shape v_laneidx))"
	| instr_case_36 :
		"(wf_ishape ishape_1) \<Longrightarrow>
		 (wf_ishape ishape_2) \<Longrightarrow>
		 (wf_vextunop_underscore ishape_1 var_0) \<Longrightarrow>
		 ((lsize (fun_lanetype (shape_ishape ishape_1))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_2))))) \<Longrightarrow>
		 wf_instr (instr_sc3 (VEXTUNOP ishape_1 ishape_2 var_0))"
	| instr_case_37 :
		"(wf_ishape ishape_1) \<Longrightarrow>
		 (wf_ishape ishape_2) \<Longrightarrow>
		 (wf_vextbinop_underscore ishape_1 var_0) \<Longrightarrow>
		 ((lsize (fun_lanetype (shape_ishape ishape_1))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_2))))) \<Longrightarrow>
		 wf_instr (instr_sc3 (VEXTBINOP ishape_1 ishape_2 var_0))"
	| instr_case_38 :
		"(wf_ishape ishape_1) \<Longrightarrow>
		 (wf_ishape ishape_2) \<Longrightarrow>
		 (((lsize (fun_lanetype (shape_ishape ishape_2))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_1))))) \<and> ((2 * (lsize (fun_lanetype (shape_ishape ishape_1)))) \<le> 32)) \<Longrightarrow>
		 wf_instr (instr_sc3 (VNARROW ishape_1 ishape_2 v_sx))"
	| instr_case_39 :
		"(wf_shape v_shape) \<Longrightarrow>
		 (wf_shape shape_0) \<Longrightarrow>
		 wf_instr (instr_sc4 (VCVTOP v_shape shape_0 v_vcvtop))"
	| instr_case_40 :
		"wf_instr (instr_sc4 (REF_NULL v_reftype))"
	| instr_case_41 :
		"(wf_uN 32 v_funcidx) \<Longrightarrow>
		 wf_instr (instr_sc4 (REF_FUNC v_funcidx))"
	| instr_case_42 :
		"wf_instr (instr_sc4 REF_IS_NULL)"
	| instr_case_43 :
		"(wf_uN 32 v_localidx) \<Longrightarrow>
		 wf_instr (instr_sc4 (LOCAL_GET v_localidx))"
	| instr_case_44 :
		"(wf_uN 32 v_localidx) \<Longrightarrow>
		 wf_instr (instr_sc4 (LOCAL_SET v_localidx))"
	| instr_case_45 :
		"(wf_uN 32 v_localidx) \<Longrightarrow>
		 wf_instr (instr_sc4 (LOCAL_TEE v_localidx))"
	| instr_case_46 :
		"(wf_uN 32 v_globalidx) \<Longrightarrow>
		 wf_instr (instr_sc4 (GLOBAL_GET v_globalidx))"
	| instr_case_47 :
		"(wf_uN 32 v_globalidx) \<Longrightarrow>
		 wf_instr (instr_sc4 (GLOBAL_SET v_globalidx))"
	| instr_case_48 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 wf_instr (instr_sc5 (TABLE_GET v_tableidx))"
	| instr_case_49 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 wf_instr (instr_sc5 (TABLE_SET v_tableidx))"
	| instr_case_50 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 wf_instr (instr_sc5 (TABLE_SIZE v_tableidx))"
	| instr_case_51 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 wf_instr (instr_sc5 (TABLE_GROW v_tableidx))"
	| instr_case_52 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 wf_instr (instr_sc5 (TABLE_FILL v_tableidx))"
	| instr_case_53 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 (wf_uN 32 tableidx_0) \<Longrightarrow>
		 wf_instr (instr_sc5 (TABLE_COPY v_tableidx tableidx_0))"
	| instr_case_54 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 (wf_uN 32 v_elemidx) \<Longrightarrow>
		 wf_instr (instr_sc5 (TABLE_INIT v_tableidx v_elemidx))"
	| instr_case_55 :
		"(wf_uN 32 v_elemidx) \<Longrightarrow>
		 wf_instr (instr_sc5 (ELEM_DROP v_elemidx))"
	| instr_case_56 :
		"list_all (\<lambda> (var_0 :: loadop_underscore). (wf_loadop_underscore v_numtype var_0)) (option_to_list var_0_opt) \<Longrightarrow>
		 (wf_memarg v_memarg) \<Longrightarrow>
		 wf_instr (instr_sc5 (LOAD v_numtype var_0_opt v_memarg))"
	| instr_case_57 :
		"list_all (\<lambda> (v_sz :: sz). (wf_sz v_sz)) (option_to_list sz_opt) \<Longrightarrow>
		 (wf_memarg v_memarg) \<Longrightarrow>
		 ((Inn_opt = None) \<longleftrightarrow> (numtype_opt = None)) \<Longrightarrow>
		 ((Inn_opt = None) \<longleftrightarrow> (sz_opt = None)) \<Longrightarrow>
		 list_all3 (\<lambda> (v_Inn :: Inn) (v_numtype :: numtype) (v_sz :: sz). ((v_numtype = (numtype_Inn v_Inn)) \<and> ((proj_sz_0 v_sz) < (sizenn (numtype_Inn v_Inn))))) (option_to_list Inn_opt) (option_to_list numtype_opt) (option_to_list sz_opt) \<Longrightarrow>
		 wf_instr (instr_sc6 (STORE v_numtype sz_opt v_memarg))"
	| instr_case_58 :
		"(wf_memarg v_memarg) \<Longrightarrow>
		 wf_instr (instr_sc6 (VLOAD v_vectype vloadop_opt v_memarg))"
	| instr_case_59 :
		"(wf_sz v_sz) \<Longrightarrow>
		 (wf_memarg v_memarg) \<Longrightarrow>
		 (wf_uN 8 v_laneidx) \<Longrightarrow>
		 wf_instr (instr_sc6 (VLOAD_LANE v_vectype v_sz v_memarg v_laneidx))"
	| instr_case_60 :
		"(wf_memarg v_memarg) \<Longrightarrow>
		 wf_instr (instr_sc6 (VSTORE v_vectype v_memarg))"
	| instr_case_61 :
		"(wf_sz v_sz) \<Longrightarrow>
		 (wf_memarg v_memarg) \<Longrightarrow>
		 (wf_uN 8 v_laneidx) \<Longrightarrow>
		 wf_instr (instr_sc6 (VSTORE_LANE v_vectype v_sz v_memarg v_laneidx))"
	| instr_case_62 :
		"wf_instr (instr_sc6 MEMORY_SIZE)"
	| instr_case_63 :
		"wf_instr (instr_sc6 MEMORY_GROW)"
	| instr_case_64 :
		"wf_instr (instr_sc6 MEMORY_FILL)"
	| instr_case_65 :
		"wf_instr (instr_sc6 MEMORY_COPY)"
	| instr_case_66 :
		"(wf_uN 32 v_dataidx) \<Longrightarrow>
		 wf_instr (instr_sc7 (MEMORY_INIT v_dataidx))"
	| instr_case_67 :
		"(wf_uN 32 v_dataidx) \<Longrightarrow>
		 wf_instr (instr_sc7 (DATA_DROP v_dataidx))"

(* Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:528.1-529.9 *)
type_synonym expr = "(instr list)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:541.1-541.59 *)
datatype elemmode =
	  ACTIVE "tableidx" "expr"
	| PASSIVE
	| DECLARE

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:541.8-541.16 *)
inductive wf_elemmode :: "elemmode \<Rightarrow> bool" where
	  elemmode_case_0 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 list_all (\<lambda> (v_expr :: instr). (wf_instr v_expr)) v_expr \<Longrightarrow>
		 wf_elemmode (ACTIVE v_tableidx v_expr)"
	| elemmode_case_1 :
		"wf_elemmode PASSIVE"
	| elemmode_case_2 :
		"wf_elemmode DECLARE"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:542.1-542.47 *)
datatype datamode =
	  datamode_ACTIVE "memidx" "expr"
	| datamode_PASSIVE

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:542.8-542.16 *)
inductive wf_datamode :: "datamode \<Rightarrow> bool" where
	  datamode_case_0 :
		"(wf_uN 32 v_memidx) \<Longrightarrow>
		 list_all (\<lambda> (v_expr :: instr). (wf_instr v_expr)) v_expr \<Longrightarrow>
		 wf_datamode (datamode_ACTIVE v_memidx v_expr)"
	| datamode_case_1 :
		"wf_datamode datamode_PASSIVE"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:544.1-545.16 *)
datatype type =
	  res_TYPE "functype"
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:546.1-547.16 *)
datatype local =
	  LOCAL "valtype"
	

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:548.1-549.27 *)
datatype func =
	  func_FUNC "typeidx" "(local list)" "expr"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:548.8-548.12 *)
inductive wf_func :: "func \<Rightarrow> bool" where
	  func_case_0 :
		"(wf_uN 32 v_typeidx) \<Longrightarrow>
		 list_all (\<lambda> (v_expr :: instr). (wf_instr v_expr)) v_expr \<Longrightarrow>
		 wf_func (func_FUNC v_typeidx local_lst v_expr)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:550.1-551.25 *)
datatype global =
	  global_GLOBAL "globaltype" "expr"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:550.8-550.14 *)
inductive wf_global :: "global \<Rightarrow> bool" where
	  global_case_0 :
		"list_all (\<lambda> (v_expr :: instr). (wf_instr v_expr)) v_expr \<Longrightarrow>
		 wf_global (global_GLOBAL v_globaltype v_expr)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:552.1-553.18 *)
datatype table =
	  table_TABLE "tabletype"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:552.8-552.13 *)
inductive wf_table :: "table \<Rightarrow> bool" where
	  table_case_0 :
		"(wf_tabletype v_tabletype) \<Longrightarrow>
		 wf_table (table_TABLE v_tabletype)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:554.1-555.17 *)
datatype mem =
	  MEMORY "memtype"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:554.8-554.11 *)
inductive wf_mem :: "mem \<Rightarrow> bool" where
	  mem_case_0 :
		"(wf_memtype v_memtype) \<Longrightarrow>
		 wf_mem (MEMORY v_memtype)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:556.1-557.30 *)
datatype elem =
	  ELEM "reftype" "(expr list)" "elemmode"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:556.8-556.12 *)
inductive wf_elem :: "elem \<Rightarrow> bool" where
	  elem_case_0 :
		"list_all (\<lambda> (v_expr :: expr). list_all (\<lambda> (v_expr :: instr). (wf_instr v_expr)) v_expr) expr_lst \<Longrightarrow>
		 (wf_elemmode v_elemmode) \<Longrightarrow>
		 wf_elem (ELEM v_reftype expr_lst v_elemmode)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:558.1-559.22 *)
datatype data =
	  DATA "(byte list)" "datamode"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:558.8-558.12 *)
inductive wf_data :: "data \<Rightarrow> bool" where
	  data_case_0 :
		"list_all (\<lambda> (v_byte :: byte). (wf_byte v_byte)) byte_lst \<Longrightarrow>
		 (wf_datamode v_datamode) \<Longrightarrow>
		 wf_data (DATA byte_lst v_datamode)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:560.1-561.16 *)
datatype start =
	  START "funcidx"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:560.8-560.13 *)
inductive wf_start :: "start \<Rightarrow> bool" where
	  start_case_0 :
		"(wf_uN 32 v_funcidx) \<Longrightarrow>
		 wf_start (START v_funcidx)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:563.1-564.66 *)
datatype externidx =
	  externidx_FUNC "funcidx"
	| externidx_GLOBAL "globalidx"
	| externidx_TABLE "tableidx"
	| externidx_MEM "memidx"

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:563.8-563.17 *)
inductive wf_externidx :: "externidx \<Rightarrow> bool" where
	  externidx_case_0 :
		"(wf_uN 32 v_funcidx) \<Longrightarrow>
		 wf_externidx (externidx_FUNC v_funcidx)"
	| externidx_case_1 :
		"(wf_uN 32 v_globalidx) \<Longrightarrow>
		 wf_externidx (externidx_GLOBAL v_globalidx)"
	| externidx_case_2 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 wf_externidx (externidx_TABLE v_tableidx)"
	| externidx_case_3 :
		"(wf_uN 32 v_memidx) \<Longrightarrow>
		 wf_externidx (externidx_MEM v_memidx)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:565.1-566.24 *)
datatype export =
	  EXPORT "name" "externidx"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:565.8-565.14 *)
inductive wf_export :: "export \<Rightarrow> bool" where
	  export_case_0 :
		"(wf_name v_name) \<Longrightarrow>
		 (wf_externidx v_externidx) \<Longrightarrow>
		 wf_export (EXPORT v_name v_externidx)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:567.1-568.30 *)
datatype import =
	  IMPORT "name" "name" "externtype"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:567.8-567.14 *)
inductive wf_import :: "import \<Rightarrow> bool" where
	  import_case_0 :
		"(wf_name v_name) \<Longrightarrow>
		 (wf_name name_0) \<Longrightarrow>
		 (wf_externtype v_externtype) \<Longrightarrow>
		 wf_import (IMPORT v_name name_0 v_externtype)"

(* Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:570.1-571.76 *)
datatype module =
	  MODULE "(type list)" "(import list)" "(func list)" "(global list)" "(table list)" "(mem list)" "(elem list)" "(data list)" "(start option)" "(export list)"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:570.8-570.14 *)
inductive wf_module :: "module \<Rightarrow> bool" where
	  module_case_0 :
		"list_all (\<lambda> (v_import :: import). (wf_import v_import)) import_lst \<Longrightarrow>
		 list_all (\<lambda> (v_func :: func). (wf_func v_func)) func_lst \<Longrightarrow>
		 list_all (\<lambda> (v_global :: global). (wf_global v_global)) global_lst \<Longrightarrow>
		 list_all (\<lambda> (v_table :: table). (wf_table v_table)) table_lst \<Longrightarrow>
		 list_all (\<lambda> (v_mem :: mem). (wf_mem v_mem)) mem_lst \<Longrightarrow>
		 list_all (\<lambda> (v_elem :: elem). (wf_elem v_elem)) elem_lst \<Longrightarrow>
		 list_all (\<lambda> (v_data :: data). (wf_data v_data)) data_lst \<Longrightarrow>
		 list_all (\<lambda> (v_start :: start). (wf_start v_start)) (option_to_list start_opt) \<Longrightarrow>
		 list_all (\<lambda> (v_export :: export). (wf_export v_export)) export_lst \<Longrightarrow>
		 wf_module (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)"

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:7.1-7.59 *)
inductive fun_concat_bytes :: "((byte list) list) \<Rightarrow> (byte list) \<Rightarrow> bool" where
	  fun_concat_bytes_case_0 :
		"fun_concat_bytes [] []"
	| fun_concat_bytes_case_1 :
		"(fun_concat_bytes b'_lst_lst var_0) \<Longrightarrow>
		 fun_concat_bytes ([b_lst] @ b'_lst_lst) (b_lst @ var_0)"

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:7.1-7.59 *)
inductive concat_bytes_is_wf :: "((byte list) list) \<Rightarrow> (byte list) \<Rightarrow> bool" where
	  concat_bytes_is_wf_0 :
		"(fun_concat_bytes var_0_lst_lst var_0) \<Longrightarrow>
		 list_all (\<lambda> (var_0_lst :: (byte list)). list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst) var_0_lst_lst \<Longrightarrow>
		 (ret_val_lst = var_0) \<Longrightarrow>
		 list_all (\<lambda> (ret_val :: byte). (wf_byte ret_val)) ret_val_lst \<Longrightarrow>
		 concat_bytes_is_wf var_0_lst_lst ret_val_lst"

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:28.1-28.32 *)
function (sequential, domintros) unpack :: "lanetype \<Rightarrow> numtype" where
		  "unpack lanetype_I32 = I32"
		| "unpack lanetype_I64 = I64"
		| "unpack lanetype_F32 = F32"
		| "unpack lanetype_F64 = F64"
		| "unpack lanetype_I8 = I32"
		| "unpack lanetype_I16 = I32"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:44.1-44.54 *)
function (sequential, domintros) shunpack :: "shape \<Rightarrow> numtype" where
		  "shunpack (X v_Lnn (mk_dim v_N)) = (unpack v_Lnn)"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:51.1-51.64 *)
inductive fun_funcsxt :: "(externtype list) \<Rightarrow> (functype list) \<Rightarrow> bool" where
	  fun_funcsxt_case_0 :
		"fun_funcsxt [] []"
	| fun_funcsxt_case_1 :
		"(fun_funcsxt xt_lst var_0) \<Longrightarrow>
		 fun_funcsxt ([(FUNC ft)] @ xt_lst) ([ft] @ var_0)"
	| fun_funcsxt_case_2 :
		"(fun_funcsxt xt_lst var_0) \<Longrightarrow>
		 fun_funcsxt ([v_externtype] @ xt_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:52.1-52.66 *)
inductive fun_globalsxt :: "(externtype list) \<Rightarrow> (globaltype list) \<Rightarrow> bool" where
	  fun_globalsxt_case_0 :
		"fun_globalsxt [] []"
	| fun_globalsxt_case_1 :
		"(fun_globalsxt xt_lst var_0) \<Longrightarrow>
		 fun_globalsxt ([(GLOBAL gt)] @ xt_lst) ([gt] @ var_0)"
	| fun_globalsxt_case_2 :
		"(fun_globalsxt xt_lst var_0) \<Longrightarrow>
		 fun_globalsxt ([v_externtype] @ xt_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:53.1-53.65 *)
inductive fun_tablesxt :: "(externtype list) \<Rightarrow> (tabletype list) \<Rightarrow> bool" where
	  fun_tablesxt_case_0 :
		"fun_tablesxt [] []"
	| fun_tablesxt_case_1 :
		"(fun_tablesxt xt_lst var_0) \<Longrightarrow>
		 fun_tablesxt ([(TABLE tt)] @ xt_lst) ([tt] @ var_0)"
	| fun_tablesxt_case_2 :
		"(fun_tablesxt xt_lst var_0) \<Longrightarrow>
		 fun_tablesxt ([v_externtype] @ xt_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:53.1-53.65 *)
inductive tablesxt_is_wf :: "(externtype list) \<Rightarrow> (tabletype list) \<Rightarrow> bool" where
	  tablesxt_is_wf_0 :
		"(fun_tablesxt var_0_lst var_0) \<Longrightarrow>
		 list_all (\<lambda> (var_0 :: externtype). (wf_externtype var_0)) var_0_lst \<Longrightarrow>
		 (ret_val_lst = var_0) \<Longrightarrow>
		 list_all (\<lambda> (ret_val :: tabletype). (wf_tabletype ret_val)) ret_val_lst \<Longrightarrow>
		 tablesxt_is_wf var_0_lst ret_val_lst"

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:54.1-54.63 *)
inductive fun_memsxt :: "(externtype list) \<Rightarrow> (memtype list) \<Rightarrow> bool" where
	  fun_memsxt_case_0 :
		"fun_memsxt [] []"
	| fun_memsxt_case_1 :
		"(fun_memsxt xt_lst var_0) \<Longrightarrow>
		 fun_memsxt ([(MEM mt)] @ xt_lst) ([mt] @ var_0)"
	| fun_memsxt_case_2 :
		"(fun_memsxt xt_lst var_0) \<Longrightarrow>
		 fun_memsxt ([v_externtype] @ xt_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:54.1-54.63 *)
inductive memsxt_is_wf :: "(externtype list) \<Rightarrow> (memtype list) \<Rightarrow> bool" where
	  memsxt_is_wf_0 :
		"(fun_memsxt var_0_lst var_0) \<Longrightarrow>
		 list_all (\<lambda> (var_0 :: externtype). (wf_externtype var_0)) var_0_lst \<Longrightarrow>
		 (ret_val_lst = var_0) \<Longrightarrow>
		 list_all (\<lambda> (ret_val :: memtype). (wf_memtype ret_val)) ret_val_lst \<Longrightarrow>
		 memsxt_is_wf var_0_lst ret_val_lst"

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:80.1-80.61 *)
function (sequential, domintros) dataidx_instr :: "instr \<Rightarrow> (dataidx list)" where
		  "dataidx_instr (instr_sc7 (MEMORY_INIT x)) = [x]"
		| "dataidx_instr (instr_sc7 (DATA_DROP x)) = [x]"
		| "dataidx_instr res_in = []"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:80.6-80.20 *)
lemma dataidx_instr_is_wf :
	"(wf_instr v_instr) \<Longrightarrow>
	 (ret_val_lst = (dataidx_instr v_instr)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: dataidx). (wf_uN 32 ret_val)) ret_val_lst"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:85.1-85.63 *)
inductive fun_dataidx_instrs :: "(instr list) \<Rightarrow> (dataidx list) \<Rightarrow> bool" where
	  fun_dataidx_instrs_case_0 :
		"fun_dataidx_instrs [] []"
	| fun_dataidx_instrs_case_1 :
		"(fun_dataidx_instrs instr'_lst var_0) \<Longrightarrow>
		 fun_dataidx_instrs ([v_instr] @ instr'_lst) ((dataidx_instr v_instr) @ var_0)"

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:85.1-85.63 *)
inductive dataidx_instrs_is_wf :: "(instr list) \<Rightarrow> (dataidx list) \<Rightarrow> bool" where
	  dataidx_instrs_is_wf_0 :
		"(fun_dataidx_instrs var_0_lst var_0) \<Longrightarrow>
		 list_all (\<lambda> (var_0 :: instr). (wf_instr var_0)) var_0_lst \<Longrightarrow>
		 (ret_val_lst = var_0) \<Longrightarrow>
		 list_all (\<lambda> (ret_val :: dataidx). (wf_uN 32 ret_val)) ret_val_lst \<Longrightarrow>
		 dataidx_instrs_is_wf var_0_lst ret_val_lst"

(* Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:89.6-89.19 *)
inductive fun_dataidx_expr :: "expr \<Rightarrow> (dataidx list) \<Rightarrow> bool" where
	  fun_dataidx_expr_case_0 :
		"(fun_dataidx_instrs in_lst var_0) \<Longrightarrow>
		 fun_dataidx_expr in_lst var_0"

(* Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:89.6-89.19 *)
lemma dataidx_expr_is_wf :
	"(fun_dataidx_expr v_expr var_0) \<Longrightarrow>
	 list_all (\<lambda> (v_expr :: instr). (wf_instr v_expr)) v_expr \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: dataidx). (wf_uN 32 ret_val)) ret_val_lst"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:92.6-92.19 *)
inductive fun_dataidx_func :: "func \<Rightarrow> (dataidx list) \<Rightarrow> bool" where
	  fun_dataidx_func_case_0 :
		"(fun_dataidx_expr e var_0) \<Longrightarrow>
		 fun_dataidx_func (func_FUNC x loc_lst e) var_0"

(* Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:92.6-92.19 *)
lemma dataidx_func_is_wf :
	"(fun_dataidx_func v_func var_0) \<Longrightarrow>
	 (wf_func v_func) \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: dataidx). (wf_uN 32 ret_val)) ret_val_lst"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:95.1-95.61 *)
inductive fun_dataidx_funcs :: "(func list) \<Rightarrow> (dataidx list) \<Rightarrow> bool" where
	  fun_dataidx_funcs_case_0 :
		"fun_dataidx_funcs [] []"
	| fun_dataidx_funcs_case_1 :
		"(fun_dataidx_funcs func'_lst var_1) \<Longrightarrow>
		 (fun_dataidx_func v_func var_0) \<Longrightarrow>
		 fun_dataidx_funcs ([v_func] @ func'_lst) (var_0 @ var_1)"

(* Mutual Recursion at: ../specification/wasm-2.0/2-syntax-aux.spectec:95.1-95.61 *)
inductive dataidx_funcs_is_wf :: "(func list) \<Rightarrow> (dataidx list) \<Rightarrow> bool" where
	  dataidx_funcs_is_wf_0 :
		"(fun_dataidx_funcs var_0_lst var_0) \<Longrightarrow>
		 list_all (\<lambda> (var_0 :: func). (wf_func var_0)) var_0_lst \<Longrightarrow>
		 (ret_val_lst = var_0) \<Longrightarrow>
		 list_all (\<lambda> (ret_val :: dataidx). (wf_uN 32 ret_val)) ret_val_lst \<Longrightarrow>
		 dataidx_funcs_is_wf var_0_lst ret_val_lst"

(* Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:106.1-106.35 *)
definition memarg0 :: "memarg" where
	"memarg0 = \<lparr> ALIGN = (mk_uN 0), OFFSET = (mk_uN 0) \<rparr>"

(* Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:106.6-106.13 *)
lemma memarg0_is_wf :
	"(ret_val = (memarg0 )) \<Longrightarrow>
	 (wf_memarg ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:7.1-7.41 *)
axiomatization s33_to_u32 :: "s33 \<Rightarrow> u32"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:7.6-7.17 *)
lemma s33_to_u32_is_wf :
	"(wf_sN 33 v_s33) \<Longrightarrow>
	 (ret_val = (s33_to_u32 v_s33)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:9.1-9.22 *)
function (sequential, domintros) res_bool :: "bool \<Rightarrow> nat" where
		  "res_bool False = 0"
		| "res_bool True = 1"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:13.1-13.23 *)
axiomatization truncz :: "nat \<Rightarrow> nat"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:20.6-20.14 *)
inductive fun_signed_underscore :: "N \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
	  fun_signed__case_0 :
		"(i < (2 ^ (((v_N :: nat) - (1 :: nat)) :: nat))) \<Longrightarrow>
		 fun_signed_underscore v_N i (i :: nat)"
	| fun_signed__case_1 :
		"(((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) \<le> i) \<and> (i < (2 ^ v_N))) \<Longrightarrow>
		 fun_signed_underscore v_N i ((i :: nat) - ((2 ^ v_N) :: nat))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:24.6-24.18 *)
inductive fun_inv_signed_underscore :: "N \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
	  fun_inv_signed__case_0 :
		"(((0 :: nat) \<le> i) \<and> (i < ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat))) \<Longrightarrow>
		 fun_inv_signed_underscore v_N i (i :: nat)"
	| fun_inv_signed__case_1 :
		"(((0 - ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat)) \<le> i) \<and> (i < (0 :: nat))) \<Longrightarrow>
		 fun_inv_signed_underscore v_N i ((i + ((2 ^ v_N) :: nat)) :: nat)"

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:31.1-31.61 *)
function (sequential, domintros) sat_u_underscore :: "N \<Rightarrow> nat \<Rightarrow> nat" where
		  "sat_u_underscore v_N i = (if (i < (0 :: nat)) then 0 else (if (i > (((2 ^ v_N) :: nat) - (1 :: nat))) then ((((2 ^ v_N) :: nat) - (1 :: nat)) :: nat) else (i :: nat)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:36.1-36.61 *)
function (sequential, domintros) sat_s_underscore :: "N \<Rightarrow> nat \<Rightarrow> nat" where
		  "sat_s_underscore v_N i = (if (i < (0 - ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat))) then (0 - ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat)) else (if (i > (((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat) - (1 :: nat))) then (((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat) - (1 :: nat)) else i))"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:56.1-56.89 *)
axiomatization extend__underscore :: "M \<Rightarrow> N \<Rightarrow> sx \<Rightarrow> iN \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:56.6-56.15 *)
lemma extend___is_wf :
	"(wf_uN v_M v_iN) \<Longrightarrow>
	 (ret_val = (extend__underscore v_M v_N v_sx v_iN)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:224.1-224.30 *)
axiomatization fabs_underscore :: "N \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:224.6-224.12 *)
lemma fabs__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (ret_val_lst = (fabs_underscore v_N v_fN)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:227.1-227.31 *)
axiomatization fceil_underscore :: "N \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:227.6-227.13 *)
lemma fceil__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (ret_val_lst = (fceil_underscore v_N v_fN)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:228.1-228.32 *)
axiomatization ffloor_underscore :: "N \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:228.6-228.14 *)
lemma ffloor__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (ret_val_lst = (ffloor_underscore v_N v_fN)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:230.1-230.34 *)
axiomatization fnearest_underscore :: "N \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:230.6-230.16 *)
lemma fnearest__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (ret_val_lst = (fnearest_underscore v_N v_fN)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:225.1-225.30 *)
axiomatization fneg_underscore :: "N \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:225.6-225.12 *)
lemma fneg__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (ret_val_lst = (fneg_underscore v_N v_fN)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:226.1-226.31 *)
axiomatization fsqrt_underscore :: "N \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:226.6-226.13 *)
lemma fsqrt__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (ret_val_lst = (fsqrt_underscore v_N v_fN)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:229.1-229.32 *)
axiomatization ftrunc_underscore :: "N \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:229.6-229.14 *)
lemma ftrunc__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (ret_val_lst = (ftrunc_underscore v_N v_fN)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:120.1-120.29 *)
axiomatization iclz_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:120.6-120.12 *)
lemma iclz__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val = (iclz_underscore v_N v_iN)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:121.1-121.29 *)
axiomatization ictz_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:121.6-121.12 *)
lemma ictz__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val = (ictz_underscore v_N v_iN)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:122.1-122.32 *)
axiomatization ipopcnt_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:122.6-122.15 *)
lemma ipopcnt__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val = (ipopcnt_underscore v_N v_iN)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:55.1-55.33 *)
axiomatization wrap__underscore :: "M \<Rightarrow> N \<Rightarrow> iN \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:55.6-55.13 *)
lemma wrap___is_wf :
	"(wf_uN v_M v_iN) \<Longrightarrow>
	 (ret_val = (wrap__underscore v_M v_N v_iN)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.1-45.32 *)
function (sequential, domintros) fun_unop__I64 :: "unop_underscore \<Rightarrow> num_underscore \<Rightarrow> (num_underscore list)" where
		  "fun_unop__I64 (mk_unop__0 Inn_I64 CLZ) (mk_num__0 Inn_I64 v_iN) = [(mk_num__0 Inn_I64 (iclz_underscore (sizenn (numtype_Inn Inn_I64)) v_iN))]"
		| "fun_unop__I64 (mk_unop__0 Inn_I64 CTZ) (mk_num__0 Inn_I64 v_iN) = [(mk_num__0 Inn_I64 (ictz_underscore (sizenn (numtype_Inn Inn_I64)) v_iN))]"
		| "fun_unop__I64 (mk_unop__0 Inn_I64 POPCNT) (mk_num__0 Inn_I64 v_iN) = [(mk_num__0 Inn_I64 (ipopcnt_underscore (sizenn (numtype_Inn Inn_I64)) v_iN))]"
		| "fun_unop__I64 (mk_unop__0 Inn_I64 (EXTEND v_M)) (mk_num__0 Inn_I64 v_iN) = [(mk_num__0 Inn_I64 (extend__underscore v_M (sizenn (numtype_Inn Inn_I64)) S (wrap__underscore (sizenn (numtype_Inn Inn_I64)) v_M v_iN)))]"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.1-45.32 *)
function (sequential, domintros) fun_unop__I32 :: "unop_underscore \<Rightarrow> num_underscore \<Rightarrow> (num_underscore list)" where
		  "fun_unop__I32 (mk_unop__0 Inn_I32 CLZ) (mk_num__0 Inn_I32 v_iN) = [(mk_num__0 Inn_I32 (iclz_underscore (sizenn (numtype_Inn Inn_I32)) v_iN))]"
		| "fun_unop__I32 (mk_unop__0 Inn_I32 CTZ) (mk_num__0 Inn_I32 v_iN) = [(mk_num__0 Inn_I32 (ictz_underscore (sizenn (numtype_Inn Inn_I32)) v_iN))]"
		| "fun_unop__I32 (mk_unop__0 Inn_I32 POPCNT) (mk_num__0 Inn_I32 v_iN) = [(mk_num__0 Inn_I32 (ipopcnt_underscore (sizenn (numtype_Inn Inn_I32)) v_iN))]"
		| "fun_unop__I32 (mk_unop__0 Inn_I32 (EXTEND v_M)) (mk_num__0 Inn_I32 v_iN) = [(mk_num__0 Inn_I32 (extend__underscore v_M (sizenn (numtype_Inn Inn_I32)) S (wrap__underscore (sizenn (numtype_Inn Inn_I32)) v_M v_iN)))]"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.1-45.32 *)
function (sequential, domintros) fun_unop__F64 :: "unop_underscore \<Rightarrow> num_underscore \<Rightarrow> (num_underscore list)" where
		  "fun_unop__F64 (mk_unop__1 Fnn_F64 ABS) (mk_num__1 Fnn_F64 v_fN) = (map (\<lambda> (iter_0_2 :: fN). (mk_num__1 Fnn_F64 iter_0_2)) (fabs_underscore (sizenn (numtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 unop_Fnn_NEG) (mk_num__1 Fnn_F64 v_fN) = (map (\<lambda> (iter_0_4 :: fN). (mk_num__1 Fnn_F64 iter_0_4)) (fneg_underscore (sizenn (numtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 SQRT) (mk_num__1 Fnn_F64 v_fN) = (map (\<lambda> (iter_0_6 :: fN). (mk_num__1 Fnn_F64 iter_0_6)) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 CEIL) (mk_num__1 Fnn_F64 v_fN) = (map (\<lambda> (iter_0_8 :: fN). (mk_num__1 Fnn_F64 iter_0_8)) (fceil_underscore (sizenn (numtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 FLOOR) (mk_num__1 Fnn_F64 v_fN) = (map (\<lambda> (iter_0_10 :: fN). (mk_num__1 Fnn_F64 iter_0_10)) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 TRUNC) (mk_num__1 Fnn_F64 v_fN) = (map (\<lambda> (iter_0_12 :: fN). (mk_num__1 Fnn_F64 iter_0_12)) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 NEAREST) (mk_num__1 Fnn_F64 v_fN) = (map (\<lambda> (iter_0_14 :: fN). (mk_num__1 Fnn_F64 iter_0_14)) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F64)) v_fN))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.1-45.32 *)
function (sequential, domintros) fun_unop__F32 :: "unop_underscore \<Rightarrow> num_underscore \<Rightarrow> (num_underscore list)" where
		  "fun_unop__F32 (mk_unop__1 Fnn_F32 ABS) (mk_num__1 Fnn_F32 v_fN) = (map (\<lambda> (iter_0_1 :: fN). (mk_num__1 Fnn_F32 iter_0_1)) (fabs_underscore (sizenn (numtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 unop_Fnn_NEG) (mk_num__1 Fnn_F32 v_fN) = (map (\<lambda> (iter_0_3 :: fN). (mk_num__1 Fnn_F32 iter_0_3)) (fneg_underscore (sizenn (numtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 SQRT) (mk_num__1 Fnn_F32 v_fN) = (map (\<lambda> (iter_0_5 :: fN). (mk_num__1 Fnn_F32 iter_0_5)) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 CEIL) (mk_num__1 Fnn_F32 v_fN) = (map (\<lambda> (iter_0_7 :: fN). (mk_num__1 Fnn_F32 iter_0_7)) (fceil_underscore (sizenn (numtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 FLOOR) (mk_num__1 Fnn_F32 v_fN) = (map (\<lambda> (iter_0_9 :: fN). (mk_num__1 Fnn_F32 iter_0_9)) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 TRUNC) (mk_num__1 Fnn_F32 v_fN) = (map (\<lambda> (iter_0_11 :: fN). (mk_num__1 Fnn_F32 iter_0_11)) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 NEAREST) (mk_num__1 Fnn_F32 v_fN) = (map (\<lambda> (iter_0_13 :: fN). (mk_num__1 Fnn_F32 iter_0_13)) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F32)) v_fN))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.1-45.32 *)
function (sequential, domintros) fun_unop_underscore :: "numtype \<Rightarrow> unop_underscore \<Rightarrow> num_underscore \<Rightarrow> (num_underscore list)" where
		  "fun_unop_underscore I64 v_unop_underscore v_num_underscore = (fun_unop__I64 v_unop_underscore v_num_underscore)"
		| "fun_unop_underscore I32 v_unop_underscore v_num_underscore = (fun_unop__I32 v_unop_underscore v_num_underscore)"
		| "fun_unop_underscore F64 v_unop_underscore v_num_underscore = (fun_unop__F64 v_unop_underscore v_num_underscore)"
		| "fun_unop_underscore F32 v_unop_underscore v_num_underscore = (fun_unop__F32 v_unop_underscore v_num_underscore)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.6-44.12 *)
lemma unop__is_wf :
	"(wf_unop_underscore v_numtype v_unop_underscore) \<Longrightarrow>
	 (wf_num_underscore v_numtype v_num_underscore) \<Longrightarrow>
	 (ret_val_lst = (fun_unop_underscore v_numtype v_unop_underscore v_num_underscore)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: num_underscore). (wf_num_underscore v_numtype ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:215.1-215.37 *)
axiomatization fadd_underscore :: "N \<Rightarrow> fN \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:215.6-215.12 *)
lemma fadd__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (wf_fN v_N fN_0) \<Longrightarrow>
	 (ret_val_lst = (fadd_underscore v_N v_fN fN_0)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:223.1-223.42 *)
axiomatization fcopysign_underscore :: "N \<Rightarrow> fN \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:223.6-223.17 *)
lemma fcopysign__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (wf_fN v_N fN_0) \<Longrightarrow>
	 (ret_val_lst = (fcopysign_underscore v_N v_fN fN_0)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:218.1-218.37 *)
axiomatization fdiv_underscore :: "N \<Rightarrow> fN \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:218.6-218.12 *)
lemma fdiv__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (wf_fN v_N fN_0) \<Longrightarrow>
	 (ret_val_lst = (fdiv_underscore v_N v_fN fN_0)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:220.1-220.37 *)
axiomatization fmax_underscore :: "N \<Rightarrow> fN \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:220.6-220.12 *)
lemma fmax__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (wf_fN v_N fN_0) \<Longrightarrow>
	 (ret_val_lst = (fmax_underscore v_N v_fN fN_0)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:219.1-219.37 *)
axiomatization fmin_underscore :: "N \<Rightarrow> fN \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:219.6-219.12 *)
lemma fmin__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (wf_fN v_N fN_0) \<Longrightarrow>
	 (ret_val_lst = (fmin_underscore v_N v_fN fN_0)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:217.1-217.37 *)
axiomatization fmul_underscore :: "N \<Rightarrow> fN \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:217.6-217.12 *)
lemma fmul__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (wf_fN v_N fN_0) \<Longrightarrow>
	 (ret_val_lst = (fmul_underscore v_N v_fN fN_0)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:216.1-216.37 *)
axiomatization fsub_underscore :: "N \<Rightarrow> fN \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:216.6-216.12 *)
lemma fsub__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (wf_fN v_N fN_0) \<Longrightarrow>
	 (ret_val_lst = (fsub_underscore v_N v_fN fN_0)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:105.1-105.36 *)
function (sequential, domintros) iadd_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> iN" where
		  "iadd_underscore v_N i_1 i_2 = (mk_uN (((proj_uN_0 i_1) + (proj_uN_0 i_2)) mod (2 ^ v_N)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:105.6-105.12 *)
lemma iadd__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (iadd_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:112.1-112.36 *)
axiomatization iand_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:112.6-112.12 *)
lemma iand__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (iand_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:108.6-108.12 *)
inductive fun_idiv_underscore :: "N \<Rightarrow> sx \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> (iN option) \<Rightarrow> bool" where
	  fun_idiv__case_0 :
		"fun_idiv_underscore v_N U i_1 (mk_uN 0) None"
	| fun_idiv__case_1 :
		"fun_idiv_underscore v_N U i_1 i_2 (Some (mk_uN ((truncz (((proj_uN_0 i_1) :: nat) div ((proj_uN_0 i_2) :: nat))) :: nat)))"
	| fun_idiv__case_2 :
		"fun_idiv_underscore v_N S i_1 (mk_uN 0) None"
	| fun_idiv__case_3 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) \<Longrightarrow>
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) \<Longrightarrow>
		 (((var_0 :: nat) div (var_1 :: nat)) = ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat)) \<Longrightarrow>
		 fun_idiv_underscore v_N S i_1 i_2 None"
	| fun_idiv__case_4 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_2) \<Longrightarrow>
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_1) \<Longrightarrow>
		 (fun_inv_signed_underscore v_N (truncz ((var_1 :: nat) div (var_2 :: nat))) var_0) \<Longrightarrow>
		 fun_idiv_underscore v_N S i_1 i_2 (Some (mk_uN var_0))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:108.6-108.12 *)
lemma idiv__is_wf :
	"(fun_idiv_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val_opt = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: iN). (wf_uN v_N ret_val)) (option_to_list ret_val_opt)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:107.1-107.36 *)
function (sequential, domintros) imul_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> iN" where
		  "imul_underscore v_N i_1 i_2 = (mk_uN (((proj_uN_0 i_1) * (proj_uN_0 i_2)) mod (2 ^ v_N)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:107.6-107.12 *)
lemma imul__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (imul_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:114.1-114.35 *)
axiomatization ior_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:114.6-114.11 *)
lemma ior__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (ior_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:109.6-109.12 *)
inductive fun_irem_underscore :: "N \<Rightarrow> sx \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> (iN option) \<Rightarrow> bool" where
	  fun_irem__case_0 :
		"fun_irem_underscore v_N U i_1 (mk_uN 0) None"
	| fun_irem__case_1 :
		"fun_irem_underscore v_N U i_1 i_2 (Some (mk_uN ((((proj_uN_0 i_1) :: nat) - (((proj_uN_0 i_2) * ((truncz (((proj_uN_0 i_1) :: nat) div ((proj_uN_0 i_2) :: nat))) :: nat)) :: nat)) :: nat)))"
	| fun_irem__case_2 :
		"fun_irem_underscore v_N S i_1 (mk_uN 0) None"
	| fun_irem__case_3 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_2) \<Longrightarrow>
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_1) \<Longrightarrow>
		 (fun_inv_signed_underscore v_N (j_1 - (j_2 * (truncz ((j_1 :: nat) div (j_2 :: nat))))) var_0) \<Longrightarrow>
		 ((j_1 = var_1) \<and> (j_2 = var_2)) \<Longrightarrow>
		 fun_irem_underscore v_N S i_1 i_2 (Some (mk_uN var_0))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:109.6-109.12 *)
lemma irem__is_wf :
	"(fun_irem_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val_opt = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: iN). (wf_uN v_N ret_val)) (option_to_list ret_val_opt)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:118.1-118.37 *)
axiomatization irotl_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:118.6-118.13 *)
lemma irotl__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (irotl_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:119.1-119.37 *)
axiomatization irotr_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:119.6-119.13 *)
lemma irotr__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (irotr_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:116.1-116.34 *)
axiomatization ishl_underscore :: "N \<Rightarrow> iN \<Rightarrow> u32 \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:116.6-116.12 *)
lemma ishl__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN 32 v_u32) \<Longrightarrow>
	 (ret_val = (ishl_underscore v_N v_iN v_u32)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:117.1-117.74 *)
axiomatization ishr_underscore :: "N \<Rightarrow> sx \<Rightarrow> iN \<Rightarrow> u32 \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:117.6-117.12 *)
lemma ishr__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN 32 v_u32) \<Longrightarrow>
	 (ret_val = (ishr_underscore v_N v_sx v_iN v_u32)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:106.1-106.36 *)
function (sequential, domintros) isub_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> iN" where
		  "isub_underscore v_N i_1 i_2 = (mk_uN ((((((2 ^ v_N) + (proj_uN_0 i_1)) :: nat) - ((proj_uN_0 i_2) :: nat)) mod ((2 ^ v_N) :: nat)) :: nat))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:106.6-106.12 *)
lemma isub__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (isub_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:115.1-115.36 *)
axiomatization ixor_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:115.6-115.12 *)
lemma ixor__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (ixor_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:46.6-46.13 *)
inductive fun_binop_underscore :: "numtype \<Rightarrow> binop_underscore \<Rightarrow> num_underscore \<Rightarrow> num_underscore \<Rightarrow> (num_underscore list) \<Rightarrow> bool" where
	  fun_binop__case_0 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 ADD) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (iadd_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_1 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 ADD) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (iadd_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_2 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 SUB) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (isub_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_3 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 SUB) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (isub_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_4 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 MUL) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (imul_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_5 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 MUL) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (imul_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_6 :
		"(fun_idiv_underscore (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) \<Longrightarrow>
		 fun_binop_underscore I32 (mk_binop__0 Inn_I32 (DIV v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (list_underscore  (map_option (\<lambda> (iter_0_15 :: iN). (mk_num__0 Inn_I32 iter_0_15)) var_0))"
	| fun_binop__case_7 :
		"(fun_idiv_underscore (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) \<Longrightarrow>
		 fun_binop_underscore I64 (mk_binop__0 Inn_I64 (DIV v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (list_underscore  (map_option (\<lambda> (iter_0_16 :: iN). (mk_num__0 Inn_I64 iter_0_16)) var_0))"
	| fun_binop__case_8 :
		"(fun_irem_underscore (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) \<Longrightarrow>
		 fun_binop_underscore I32 (mk_binop__0 Inn_I32 (REM v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (list_underscore  (map_option (\<lambda> (iter_0_17 :: iN). (mk_num__0 Inn_I32 iter_0_17)) var_0))"
	| fun_binop__case_9 :
		"(fun_irem_underscore (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) \<Longrightarrow>
		 fun_binop_underscore I64 (mk_binop__0 Inn_I64 (REM v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (list_underscore  (map_option (\<lambda> (iter_0_18 :: iN). (mk_num__0 Inn_I64 iter_0_18)) var_0))"
	| fun_binop__case_10 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 AND) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (iand_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_11 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 AND) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (iand_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_12 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 OR) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (ior_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_13 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 OR) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (ior_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_14 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 XOR) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (ixor_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_15 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 XOR) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (ixor_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_16 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 SHL) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (ishl_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 (mk_uN (proj_uN_0 iN_2))))]"
	| fun_binop__case_17 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 SHL) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (ishl_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 (mk_uN (proj_uN_0 iN_2))))]"
	| fun_binop__case_18 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 (SHR v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (ishr_underscore (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 (mk_uN (proj_uN_0 iN_2))))]"
	| fun_binop__case_19 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 (SHR v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (ishr_underscore (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 (mk_uN (proj_uN_0 iN_2))))]"
	| fun_binop__case_20 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 ROTL) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (irotl_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_21 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 ROTL) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (irotl_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_22 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 ROTR) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) [(mk_num__0 Inn_I32 (irotr_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_23 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 ROTR) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) [(mk_num__0 Inn_I64 (irotr_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_24 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 binop_Fnn_ADD) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (map (\<lambda> (iter_0_19 :: fN). (mk_num__1 Fnn_F32 iter_0_19)) (fadd_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_25 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 binop_Fnn_ADD) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (map (\<lambda> (iter_0_20 :: fN). (mk_num__1 Fnn_F64 iter_0_20)) (fadd_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_26 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 binop_Fnn_SUB) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (map (\<lambda> (iter_0_21 :: fN). (mk_num__1 Fnn_F32 iter_0_21)) (fsub_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_27 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 binop_Fnn_SUB) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (map (\<lambda> (iter_0_22 :: fN). (mk_num__1 Fnn_F64 iter_0_22)) (fsub_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_28 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 binop_Fnn_MUL) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (map (\<lambda> (iter_0_23 :: fN). (mk_num__1 Fnn_F32 iter_0_23)) (fmul_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_29 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 binop_Fnn_MUL) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (map (\<lambda> (iter_0_24 :: fN). (mk_num__1 Fnn_F64 iter_0_24)) (fmul_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_30 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 binop_Fnn_DIV) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (map (\<lambda> (iter_0_25 :: fN). (mk_num__1 Fnn_F32 iter_0_25)) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_31 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 binop_Fnn_DIV) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (map (\<lambda> (iter_0_26 :: fN). (mk_num__1 Fnn_F64 iter_0_26)) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_32 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 res_MIN) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (map (\<lambda> (iter_0_27 :: fN). (mk_num__1 Fnn_F32 iter_0_27)) (fmin_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_33 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 res_MIN) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (map (\<lambda> (iter_0_28 :: fN). (mk_num__1 Fnn_F64 iter_0_28)) (fmin_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_34 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 res_MAX) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (map (\<lambda> (iter_0_29 :: fN). (mk_num__1 Fnn_F32 iter_0_29)) (fmax_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_35 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 res_MAX) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (map (\<lambda> (iter_0_30 :: fN). (mk_num__1 Fnn_F64 iter_0_30)) (fmax_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_36 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 COPYSIGN) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (map (\<lambda> (iter_0_31 :: fN). (mk_num__1 Fnn_F32 iter_0_31)) (fcopysign_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_37 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 COPYSIGN) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (map (\<lambda> (iter_0_32 :: fN). (mk_num__1 Fnn_F64 iter_0_32)) (fcopysign_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:46.6-46.13 *)
lemma binop__is_wf :
	"(fun_binop_underscore v_numtype v_binop_underscore v_num_underscore num__0 var_0) \<Longrightarrow>
	 (wf_binop_underscore v_numtype v_binop_underscore) \<Longrightarrow>
	 (wf_num_underscore v_numtype v_num_underscore) \<Longrightarrow>
	 (wf_num_underscore v_numtype num__0) \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: num_underscore). (wf_num_underscore v_numtype ret_val)) ret_val_lst"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:123.1-123.27 *)
function (sequential, domintros) ieqz_underscore :: "N \<Rightarrow> iN \<Rightarrow> u32" where
		  "ieqz_underscore v_N i_1 = (mk_uN (res_bool ((proj_uN_0 i_1) = 0)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:123.6-123.12 *)
lemma ieqz__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val = (ieqz_underscore v_N v_iN)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:48.1-49.32 *)
function (sequential, domintros) fun_testop_underscore :: "numtype \<Rightarrow> testop_underscore \<Rightarrow> num_underscore \<Rightarrow> num_underscore" where
		  "fun_testop_underscore I32 (mk_testop__0 Inn_I32 EQZ) (mk_num__0 Inn_I32 v_iN) = (mk_num__0 Inn_I32 (ieqz_underscore (sizenn (numtype_Inn Inn_I32)) v_iN))"
		| "fun_testop_underscore I64 (mk_testop__0 Inn_I64 EQZ) (mk_num__0 Inn_I64 v_iN) = (mk_num__0 Inn_I32 (ieqz_underscore (sizenn (numtype_Inn Inn_I64)) v_iN))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:48.6-48.14 *)
lemma testop__is_wf :
	"(wf_testop_underscore v_numtype v_testop_underscore) \<Longrightarrow>
	 (wf_num_underscore v_numtype v_num_underscore) \<Longrightarrow>
	 (ret_val = (fun_testop_underscore v_numtype v_testop_underscore v_num_underscore)) \<Longrightarrow>
	 (wf_num_underscore I32 ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:231.1-231.33 *)
axiomatization feq_underscore :: "N \<Rightarrow> fN \<Rightarrow> fN \<Rightarrow> u32"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:231.6-231.11 *)
lemma feq__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (wf_fN v_N fN_0) \<Longrightarrow>
	 (ret_val = (feq_underscore v_N v_fN fN_0)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:236.1-236.33 *)
axiomatization fge_underscore :: "N \<Rightarrow> fN \<Rightarrow> fN \<Rightarrow> u32"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:236.6-236.11 *)
lemma fge__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (wf_fN v_N fN_0) \<Longrightarrow>
	 (ret_val = (fge_underscore v_N v_fN fN_0)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:234.1-234.33 *)
axiomatization fgt_underscore :: "N \<Rightarrow> fN \<Rightarrow> fN \<Rightarrow> u32"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:234.6-234.11 *)
lemma fgt__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (wf_fN v_N fN_0) \<Longrightarrow>
	 (ret_val = (fgt_underscore v_N v_fN fN_0)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:235.1-235.33 *)
axiomatization fle_underscore :: "N \<Rightarrow> fN \<Rightarrow> fN \<Rightarrow> u32"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:235.6-235.11 *)
lemma fle__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (wf_fN v_N fN_0) \<Longrightarrow>
	 (ret_val = (fle_underscore v_N v_fN fN_0)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:233.1-233.33 *)
axiomatization flt_underscore :: "N \<Rightarrow> fN \<Rightarrow> fN \<Rightarrow> u32"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:233.6-233.11 *)
lemma flt__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (wf_fN v_N fN_0) \<Longrightarrow>
	 (ret_val = (flt_underscore v_N v_fN fN_0)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:232.1-232.33 *)
axiomatization fne_underscore :: "N \<Rightarrow> fN \<Rightarrow> fN \<Rightarrow> u32"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:232.6-232.11 *)
lemma fne__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (wf_fN v_N fN_0) \<Longrightarrow>
	 (ret_val = (fne_underscore v_N v_fN fN_0)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:125.1-125.33 *)
function (sequential, domintros) ieq_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> u32" where
		  "ieq_underscore v_N i_1 i_2 = (mk_uN (res_bool (i_1 = i_2)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:125.6-125.11 *)
lemma ieq__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (ieq_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:130.6-130.11 *)
inductive fun_ige_underscore :: "N \<Rightarrow> sx \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> u32 \<Rightarrow> bool" where
	  fun_ige__case_0 :
		"fun_ige_underscore v_N U i_1 i_2 (mk_uN (res_bool ((proj_uN_0 i_1) \<ge> (proj_uN_0 i_2))))"
	| fun_ige__case_1 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) \<Longrightarrow>
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) \<Longrightarrow>
		 fun_ige_underscore v_N S i_1 i_2 (mk_uN (res_bool (var_0 \<ge> var_1)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:130.6-130.11 *)
lemma ige__is_wf :
	"(fun_ige_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:128.6-128.11 *)
inductive fun_igt_underscore :: "N \<Rightarrow> sx \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> u32 \<Rightarrow> bool" where
	  fun_igt__case_0 :
		"fun_igt_underscore v_N U i_1 i_2 (mk_uN (res_bool ((proj_uN_0 i_1) > (proj_uN_0 i_2))))"
	| fun_igt__case_1 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) \<Longrightarrow>
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) \<Longrightarrow>
		 fun_igt_underscore v_N S i_1 i_2 (mk_uN (res_bool (var_0 > var_1)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:128.6-128.11 *)
lemma igt__is_wf :
	"(fun_igt_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:129.6-129.11 *)
inductive fun_ile_underscore :: "N \<Rightarrow> sx \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> u32 \<Rightarrow> bool" where
	  fun_ile__case_0 :
		"fun_ile_underscore v_N U i_1 i_2 (mk_uN (res_bool ((proj_uN_0 i_1) \<le> (proj_uN_0 i_2))))"
	| fun_ile__case_1 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) \<Longrightarrow>
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) \<Longrightarrow>
		 fun_ile_underscore v_N S i_1 i_2 (mk_uN (res_bool (var_0 \<le> var_1)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:129.6-129.11 *)
lemma ile__is_wf :
	"(fun_ile_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:127.6-127.11 *)
inductive fun_ilt_underscore :: "N \<Rightarrow> sx \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> u32 \<Rightarrow> bool" where
	  fun_ilt__case_0 :
		"fun_ilt_underscore v_N U i_1 i_2 (mk_uN (res_bool ((proj_uN_0 i_1) < (proj_uN_0 i_2))))"
	| fun_ilt__case_1 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) \<Longrightarrow>
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) \<Longrightarrow>
		 fun_ilt_underscore v_N S i_1 i_2 (mk_uN (res_bool (var_0 < var_1)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:127.6-127.11 *)
lemma ilt__is_wf :
	"(fun_ilt_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:126.1-126.33 *)
function (sequential, domintros) ine_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> u32" where
		  "ine_underscore v_N i_1 i_2 = (mk_uN (res_bool (i_1 \<noteq> i_2)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:126.6-126.11 *)
lemma ine__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (ine_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:50.6-50.13 *)
inductive fun_relop_underscore :: "numtype \<Rightarrow> relop_underscore \<Rightarrow> num_underscore \<Rightarrow> num_underscore \<Rightarrow> num_underscore \<Rightarrow> bool" where
	  fun_relop__case_0 :
		"fun_relop_underscore I32 (mk_relop__0 Inn_I32 EQ) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 (ieq_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))"
	| fun_relop__case_1 :
		"fun_relop_underscore I64 (mk_relop__0 Inn_I64 EQ) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 (ieq_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))"
	| fun_relop__case_2 :
		"fun_relop_underscore I32 (mk_relop__0 Inn_I32 NE) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 (ine_underscore (sizenn (numtype_Inn Inn_I32)) iN_1 iN_2))"
	| fun_relop__case_3 :
		"fun_relop_underscore I64 (mk_relop__0 Inn_I64 NE) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 (ine_underscore (sizenn (numtype_Inn Inn_I64)) iN_1 iN_2))"
	| fun_relop__case_4 :
		"(fun_ilt_underscore (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) \<Longrightarrow>
		 fun_relop_underscore I32 (mk_relop__0 Inn_I32 (LT v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 var_0)"
	| fun_relop__case_5 :
		"(fun_ilt_underscore (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) \<Longrightarrow>
		 fun_relop_underscore I64 (mk_relop__0 Inn_I64 (LT v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 var_0)"
	| fun_relop__case_6 :
		"(fun_igt_underscore (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) \<Longrightarrow>
		 fun_relop_underscore I32 (mk_relop__0 Inn_I32 (GT v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 var_0)"
	| fun_relop__case_7 :
		"(fun_igt_underscore (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) \<Longrightarrow>
		 fun_relop_underscore I64 (mk_relop__0 Inn_I64 (GT v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 var_0)"
	| fun_relop__case_8 :
		"(fun_ile_underscore (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) \<Longrightarrow>
		 fun_relop_underscore I32 (mk_relop__0 Inn_I32 (LE v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 var_0)"
	| fun_relop__case_9 :
		"(fun_ile_underscore (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) \<Longrightarrow>
		 fun_relop_underscore I64 (mk_relop__0 Inn_I64 (LE v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 var_0)"
	| fun_relop__case_10 :
		"(fun_ige_underscore (sizenn (numtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) \<Longrightarrow>
		 fun_relop_underscore I32 (mk_relop__0 Inn_I32 (GE v_sx)) (mk_num__0 Inn_I32 iN_1) (mk_num__0 Inn_I32 iN_2) (mk_num__0 Inn_I32 var_0)"
	| fun_relop__case_11 :
		"(fun_ige_underscore (sizenn (numtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) \<Longrightarrow>
		 fun_relop_underscore I64 (mk_relop__0 Inn_I64 (GE v_sx)) (mk_num__0 Inn_I64 iN_1) (mk_num__0 Inn_I64 iN_2) (mk_num__0 Inn_I32 var_0)"
	| fun_relop__case_12 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_EQ) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (feq_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_13 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_EQ) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (feq_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_relop__case_14 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_NE) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (fne_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_15 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_NE) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (fne_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_relop__case_16 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_LT) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (flt_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_17 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_LT) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (flt_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_relop__case_18 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_GT) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (fgt_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_19 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_GT) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (fgt_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_relop__case_20 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_LE) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (fle_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_21 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_LE) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (fle_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_relop__case_22 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_GE) (mk_num__1 Fnn_F32 fN_1) (mk_num__1 Fnn_F32 fN_2) (mk_num__0 Inn_I32 (fge_underscore (sizenn (numtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_23 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_GE) (mk_num__1 Fnn_F64 fN_1) (mk_num__1 Fnn_F64 fN_2) (mk_num__0 Inn_I32 (fge_underscore (sizenn (numtype_Fnn Fnn_F64)) fN_1 fN_2))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:50.6-50.13 *)
lemma relop__is_wf :
	"(fun_relop_underscore v_numtype v_relop_underscore v_num_underscore num__0 var_0) \<Longrightarrow>
	 (wf_relop_underscore v_numtype v_relop_underscore) \<Longrightarrow>
	 (wf_num_underscore v_numtype v_num_underscore) \<Longrightarrow>
	 (wf_num_underscore v_numtype num__0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_num_underscore I32 ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:61.1-61.90 *)
axiomatization convert__underscore :: "M \<Rightarrow> N \<Rightarrow> sx \<Rightarrow> iN \<Rightarrow> fN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:61.6-61.16 *)
lemma convert___is_wf :
	"(wf_uN v_M v_iN) \<Longrightarrow>
	 (ret_val = (convert__underscore v_M v_N v_sx v_iN)) \<Longrightarrow>
	 (wf_fN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:59.1-59.36 *)
axiomatization demote__underscore :: "M \<Rightarrow> N \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:59.6-59.15 *)
lemma demote___is_wf :
	"(wf_fN v_M v_fN) \<Longrightarrow>
	 (ret_val_lst = (demote__underscore v_M v_N v_fN)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:60.1-60.37 *)
axiomatization promote__underscore :: "M \<Rightarrow> N \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:60.6-60.16 *)
lemma promote___is_wf :
	"(wf_fN v_M v_fN) \<Longrightarrow>
	 (ret_val_lst = (promote__underscore v_M v_N v_fN)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:63.1-63.76 *)
axiomatization reinterpret__underscore :: "numtype \<Rightarrow> numtype \<Rightarrow> num_underscore \<Rightarrow> num_underscore"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:63.6-63.20 *)
lemma reinterpret___is_wf :
	"(wf_num_underscore numtype_1 v_num_underscore) \<Longrightarrow>
	 (ret_val = (reinterpret__underscore numtype_1 numtype_2 v_num_underscore)) \<Longrightarrow>
	 (wf_num_underscore numtype_2 ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:57.1-57.88 *)
axiomatization trunc__underscore :: "M \<Rightarrow> N \<Rightarrow> sx \<Rightarrow> fN \<Rightarrow> (iN option)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:57.6-57.14 *)
lemma trunc___is_wf :
	"(wf_fN v_M v_fN) \<Longrightarrow>
	 (ret_val_opt = (trunc__underscore v_M v_N v_sx v_fN)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: iN). (wf_uN v_N ret_val)) (option_to_list ret_val_opt)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:58.1-58.93 *)
axiomatization trunc_sat__underscore :: "M \<Rightarrow> N \<Rightarrow> sx \<Rightarrow> fN \<Rightarrow> (iN option)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:58.6-58.18 *)
lemma trunc_sat___is_wf :
	"(wf_fN v_M v_fN) \<Longrightarrow>
	 (ret_val_opt = (trunc_sat__underscore v_M v_N v_sx v_fN)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: iN). (wf_uN v_N ret_val)) (option_to_list ret_val_opt)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:52.6-52.14 *)
inductive fun_cvtop__underscore :: "numtype \<Rightarrow> numtype \<Rightarrow> cvtop__underscore \<Rightarrow> num_underscore \<Rightarrow> (num_underscore list) \<Rightarrow> bool" where
	  fun_cvtop___case_0 :
		"fun_cvtop__underscore I32 I32 (mk_cvtop___0 Inn_I32 Inn_I32 (cvtop__Inn_1_Inn_2_EXTEND v_sx)) (mk_num__0 Inn_I32 iN_1) [(mk_num__0 Inn_I32 (extend__underscore (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I32)) v_sx iN_1))]"
	| fun_cvtop___case_1 :
		"fun_cvtop__underscore I64 I32 (mk_cvtop___0 Inn_I64 Inn_I32 (cvtop__Inn_1_Inn_2_EXTEND v_sx)) (mk_num__0 Inn_I64 iN_1) [(mk_num__0 Inn_I32 (extend__underscore (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I32)) v_sx iN_1))]"
	| fun_cvtop___case_2 :
		"fun_cvtop__underscore I32 I64 (mk_cvtop___0 Inn_I32 Inn_I64 (cvtop__Inn_1_Inn_2_EXTEND v_sx)) (mk_num__0 Inn_I32 iN_1) [(mk_num__0 Inn_I64 (extend__underscore (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I64)) v_sx iN_1))]"
	| fun_cvtop___case_3 :
		"fun_cvtop__underscore I64 I64 (mk_cvtop___0 Inn_I64 Inn_I64 (cvtop__Inn_1_Inn_2_EXTEND v_sx)) (mk_num__0 Inn_I64 iN_1) [(mk_num__0 Inn_I64 (extend__underscore (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I64)) v_sx iN_1))]"
	| fun_cvtop___case_4 :
		"fun_cvtop__underscore I32 I32 (mk_cvtop___0 Inn_I32 Inn_I32 WRAP) (mk_num__0 Inn_I32 iN_1) [(mk_num__0 Inn_I32 (wrap__underscore (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I32)) iN_1))]"
	| fun_cvtop___case_5 :
		"fun_cvtop__underscore I64 I32 (mk_cvtop___0 Inn_I64 Inn_I32 WRAP) (mk_num__0 Inn_I64 iN_1) [(mk_num__0 Inn_I32 (wrap__underscore (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I32)) iN_1))]"
	| fun_cvtop___case_6 :
		"fun_cvtop__underscore I32 I64 (mk_cvtop___0 Inn_I32 Inn_I64 WRAP) (mk_num__0 Inn_I32 iN_1) [(mk_num__0 Inn_I64 (wrap__underscore (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Inn Inn_I64)) iN_1))]"
	| fun_cvtop___case_7 :
		"fun_cvtop__underscore I64 I64 (mk_cvtop___0 Inn_I64 Inn_I64 WRAP) (mk_num__0 Inn_I64 iN_1) [(mk_num__0 Inn_I64 (wrap__underscore (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Inn Inn_I64)) iN_1))]"
	| fun_cvtop___case_8 :
		"fun_cvtop__underscore F32 I32 (mk_cvtop___2 Fnn_F32 Inn_I32 (cvtop__Fnn_1_Inn_2_TRUNC v_sx)) (mk_num__1 Fnn_F32 fN_1) (list_underscore  (map_option (\<lambda> (iter_0_33 :: iN). (mk_num__0 Inn_I32 iter_0_33)) (trunc__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)))"
	| fun_cvtop___case_9 :
		"fun_cvtop__underscore F64 I32 (mk_cvtop___2 Fnn_F64 Inn_I32 (cvtop__Fnn_1_Inn_2_TRUNC v_sx)) (mk_num__1 Fnn_F64 fN_1) (list_underscore  (map_option (\<lambda> (iter_0_34 :: iN). (mk_num__0 Inn_I32 iter_0_34)) (trunc__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)))"
	| fun_cvtop___case_10 :
		"fun_cvtop__underscore F32 I64 (mk_cvtop___2 Fnn_F32 Inn_I64 (cvtop__Fnn_1_Inn_2_TRUNC v_sx)) (mk_num__1 Fnn_F32 fN_1) (list_underscore  (map_option (\<lambda> (iter_0_35 :: iN). (mk_num__0 Inn_I64 iter_0_35)) (trunc__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)))"
	| fun_cvtop___case_11 :
		"fun_cvtop__underscore F64 I64 (mk_cvtop___2 Fnn_F64 Inn_I64 (cvtop__Fnn_1_Inn_2_TRUNC v_sx)) (mk_num__1 Fnn_F64 fN_1) (list_underscore  (map_option (\<lambda> (iter_0_36 :: iN). (mk_num__0 Inn_I64 iter_0_36)) (trunc__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)))"
	| fun_cvtop___case_12 :
		"fun_cvtop__underscore F32 I32 (mk_cvtop___2 Fnn_F32 Inn_I32 (TRUNC_SAT v_sx)) (mk_num__1 Fnn_F32 fN_1) (list_underscore  (map_option (\<lambda> (iter_0_37 :: iN). (mk_num__0 Inn_I32 iter_0_37)) (trunc_sat__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)))"
	| fun_cvtop___case_13 :
		"fun_cvtop__underscore F64 I32 (mk_cvtop___2 Fnn_F64 Inn_I32 (TRUNC_SAT v_sx)) (mk_num__1 Fnn_F64 fN_1) (list_underscore  (map_option (\<lambda> (iter_0_38 :: iN). (mk_num__0 Inn_I32 iter_0_38)) (trunc_sat__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I32)) v_sx fN_1)))"
	| fun_cvtop___case_14 :
		"fun_cvtop__underscore F32 I64 (mk_cvtop___2 Fnn_F32 Inn_I64 (TRUNC_SAT v_sx)) (mk_num__1 Fnn_F32 fN_1) (list_underscore  (map_option (\<lambda> (iter_0_39 :: iN). (mk_num__0 Inn_I64 iter_0_39)) (trunc_sat__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)))"
	| fun_cvtop___case_15 :
		"fun_cvtop__underscore F64 I64 (mk_cvtop___2 Fnn_F64 Inn_I64 (TRUNC_SAT v_sx)) (mk_num__1 Fnn_F64 fN_1) (list_underscore  (map_option (\<lambda> (iter_0_40 :: iN). (mk_num__0 Inn_I64 iter_0_40)) (trunc_sat__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Inn Inn_I64)) v_sx fN_1)))"
	| fun_cvtop___case_16 :
		"fun_cvtop__underscore I32 F32 (mk_cvtop___1 Inn_I32 Fnn_F32 (CONVERT v_sx)) (mk_num__0 Inn_I32 iN_1) [(mk_num__1 Fnn_F32 (convert__underscore (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Fnn Fnn_F32)) v_sx iN_1))]"
	| fun_cvtop___case_17 :
		"fun_cvtop__underscore I64 F32 (mk_cvtop___1 Inn_I64 Fnn_F32 (CONVERT v_sx)) (mk_num__0 Inn_I64 iN_1) [(mk_num__1 Fnn_F32 (convert__underscore (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Fnn Fnn_F32)) v_sx iN_1))]"
	| fun_cvtop___case_18 :
		"fun_cvtop__underscore I32 F64 (mk_cvtop___1 Inn_I32 Fnn_F64 (CONVERT v_sx)) (mk_num__0 Inn_I32 iN_1) [(mk_num__1 Fnn_F64 (convert__underscore (sizenn1 (numtype_Inn Inn_I32)) (sizenn2 (numtype_Fnn Fnn_F64)) v_sx iN_1))]"
	| fun_cvtop___case_19 :
		"fun_cvtop__underscore I64 F64 (mk_cvtop___1 Inn_I64 Fnn_F64 (CONVERT v_sx)) (mk_num__0 Inn_I64 iN_1) [(mk_num__1 Fnn_F64 (convert__underscore (sizenn1 (numtype_Inn Inn_I64)) (sizenn2 (numtype_Fnn Fnn_F64)) v_sx iN_1))]"
	| fun_cvtop___case_20 :
		"fun_cvtop__underscore F32 F32 (mk_cvtop___3 Fnn_F32 Fnn_F32 PROMOTE) (mk_num__1 Fnn_F32 fN_1) (map (\<lambda> (iter_0_41 :: fN). (mk_num__1 Fnn_F32 iter_0_41)) (promote__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1))"
	| fun_cvtop___case_21 :
		"fun_cvtop__underscore F64 F32 (mk_cvtop___3 Fnn_F64 Fnn_F32 PROMOTE) (mk_num__1 Fnn_F64 fN_1) (map (\<lambda> (iter_0_42 :: fN). (mk_num__1 Fnn_F32 iter_0_42)) (promote__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1))"
	| fun_cvtop___case_22 :
		"fun_cvtop__underscore F32 F64 (mk_cvtop___3 Fnn_F32 Fnn_F64 PROMOTE) (mk_num__1 Fnn_F32 fN_1) (map (\<lambda> (iter_0_43 :: fN). (mk_num__1 Fnn_F64 iter_0_43)) (promote__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1))"
	| fun_cvtop___case_23 :
		"fun_cvtop__underscore F64 F64 (mk_cvtop___3 Fnn_F64 Fnn_F64 PROMOTE) (mk_num__1 Fnn_F64 fN_1) (map (\<lambda> (iter_0_44 :: fN). (mk_num__1 Fnn_F64 iter_0_44)) (promote__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1))"
	| fun_cvtop___case_24 :
		"fun_cvtop__underscore F32 F32 (mk_cvtop___3 Fnn_F32 Fnn_F32 DEMOTE) (mk_num__1 Fnn_F32 fN_1) (map (\<lambda> (iter_0_45 :: fN). (mk_num__1 Fnn_F32 iter_0_45)) (demote__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1))"
	| fun_cvtop___case_25 :
		"fun_cvtop__underscore F64 F32 (mk_cvtop___3 Fnn_F64 Fnn_F32 DEMOTE) (mk_num__1 Fnn_F64 fN_1) (map (\<lambda> (iter_0_46 :: fN). (mk_num__1 Fnn_F32 iter_0_46)) (demote__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F32)) fN_1))"
	| fun_cvtop___case_26 :
		"fun_cvtop__underscore F32 F64 (mk_cvtop___3 Fnn_F32 Fnn_F64 DEMOTE) (mk_num__1 Fnn_F32 fN_1) (map (\<lambda> (iter_0_47 :: fN). (mk_num__1 Fnn_F64 iter_0_47)) (demote__underscore (sizenn1 (numtype_Fnn Fnn_F32)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1))"
	| fun_cvtop___case_27 :
		"fun_cvtop__underscore F64 F64 (mk_cvtop___3 Fnn_F64 Fnn_F64 DEMOTE) (mk_num__1 Fnn_F64 fN_1) (map (\<lambda> (iter_0_48 :: fN). (mk_num__1 Fnn_F64 iter_0_48)) (demote__underscore (sizenn1 (numtype_Fnn Fnn_F64)) (sizenn2 (numtype_Fnn Fnn_F64)) fN_1))"
	| fun_cvtop___case_28 :
		"((size (valtype_Inn Inn_I32)) \<noteq> None) \<Longrightarrow>
		 ((size (valtype_Fnn Fnn_F32)) \<noteq> None) \<Longrightarrow>
		 ((the ((size (valtype_Inn Inn_I32)))) = (the ((size (valtype_Fnn Fnn_F32))))) \<Longrightarrow>
		 fun_cvtop__underscore I32 F32 (mk_cvtop___1 Inn_I32 Fnn_F32 REINTERPRET) (mk_num__0 Inn_I32 iN_1) [(reinterpret__underscore (numtype_Inn Inn_I32) (numtype_Fnn Fnn_F32) (mk_num__0 Inn_I32 iN_1))]"
	| fun_cvtop___case_29 :
		"((size (valtype_Inn Inn_I64)) \<noteq> None) \<Longrightarrow>
		 ((size (valtype_Fnn Fnn_F32)) \<noteq> None) \<Longrightarrow>
		 ((the ((size (valtype_Inn Inn_I64)))) = (the ((size (valtype_Fnn Fnn_F32))))) \<Longrightarrow>
		 fun_cvtop__underscore I64 F32 (mk_cvtop___1 Inn_I64 Fnn_F32 REINTERPRET) (mk_num__0 Inn_I64 iN_1) [(reinterpret__underscore (numtype_Inn Inn_I64) (numtype_Fnn Fnn_F32) (mk_num__0 Inn_I64 iN_1))]"
	| fun_cvtop___case_30 :
		"((size (valtype_Inn Inn_I32)) \<noteq> None) \<Longrightarrow>
		 ((size (valtype_Fnn Fnn_F64)) \<noteq> None) \<Longrightarrow>
		 ((the ((size (valtype_Inn Inn_I32)))) = (the ((size (valtype_Fnn Fnn_F64))))) \<Longrightarrow>
		 fun_cvtop__underscore I32 F64 (mk_cvtop___1 Inn_I32 Fnn_F64 REINTERPRET) (mk_num__0 Inn_I32 iN_1) [(reinterpret__underscore (numtype_Inn Inn_I32) (numtype_Fnn Fnn_F64) (mk_num__0 Inn_I32 iN_1))]"
	| fun_cvtop___case_31 :
		"((size (valtype_Inn Inn_I64)) \<noteq> None) \<Longrightarrow>
		 ((size (valtype_Fnn Fnn_F64)) \<noteq> None) \<Longrightarrow>
		 ((the ((size (valtype_Inn Inn_I64)))) = (the ((size (valtype_Fnn Fnn_F64))))) \<Longrightarrow>
		 fun_cvtop__underscore I64 F64 (mk_cvtop___1 Inn_I64 Fnn_F64 REINTERPRET) (mk_num__0 Inn_I64 iN_1) [(reinterpret__underscore (numtype_Inn Inn_I64) (numtype_Fnn Fnn_F64) (mk_num__0 Inn_I64 iN_1))]"
	| fun_cvtop___case_32 :
		"((size (valtype_Fnn Fnn_F32)) \<noteq> None) \<Longrightarrow>
		 ((size (valtype_Inn Inn_I32)) \<noteq> None) \<Longrightarrow>
		 ((the ((size (valtype_Fnn Fnn_F32)))) = (the ((size (valtype_Inn Inn_I32))))) \<Longrightarrow>
		 fun_cvtop__underscore F32 I32 (mk_cvtop___2 Fnn_F32 Inn_I32 cvtop__Fnn_1_Inn_2_REINTERPRET) (mk_num__1 Fnn_F32 fN_1) [(reinterpret__underscore (numtype_Fnn Fnn_F32) (numtype_Inn Inn_I32) (mk_num__1 Fnn_F32 fN_1))]"
	| fun_cvtop___case_33 :
		"((size (valtype_Fnn Fnn_F64)) \<noteq> None) \<Longrightarrow>
		 ((size (valtype_Inn Inn_I32)) \<noteq> None) \<Longrightarrow>
		 ((the ((size (valtype_Fnn Fnn_F64)))) = (the ((size (valtype_Inn Inn_I32))))) \<Longrightarrow>
		 fun_cvtop__underscore F64 I32 (mk_cvtop___2 Fnn_F64 Inn_I32 cvtop__Fnn_1_Inn_2_REINTERPRET) (mk_num__1 Fnn_F64 fN_1) [(reinterpret__underscore (numtype_Fnn Fnn_F64) (numtype_Inn Inn_I32) (mk_num__1 Fnn_F64 fN_1))]"
	| fun_cvtop___case_34 :
		"((size (valtype_Fnn Fnn_F32)) \<noteq> None) \<Longrightarrow>
		 ((size (valtype_Inn Inn_I64)) \<noteq> None) \<Longrightarrow>
		 ((the ((size (valtype_Fnn Fnn_F32)))) = (the ((size (valtype_Inn Inn_I64))))) \<Longrightarrow>
		 fun_cvtop__underscore F32 I64 (mk_cvtop___2 Fnn_F32 Inn_I64 cvtop__Fnn_1_Inn_2_REINTERPRET) (mk_num__1 Fnn_F32 fN_1) [(reinterpret__underscore (numtype_Fnn Fnn_F32) (numtype_Inn Inn_I64) (mk_num__1 Fnn_F32 fN_1))]"
	| fun_cvtop___case_35 :
		"((size (valtype_Fnn Fnn_F64)) \<noteq> None) \<Longrightarrow>
		 ((size (valtype_Inn Inn_I64)) \<noteq> None) \<Longrightarrow>
		 ((the ((size (valtype_Fnn Fnn_F64)))) = (the ((size (valtype_Inn Inn_I64))))) \<Longrightarrow>
		 fun_cvtop__underscore F64 I64 (mk_cvtop___2 Fnn_F64 Inn_I64 cvtop__Fnn_1_Inn_2_REINTERPRET) (mk_num__1 Fnn_F64 fN_1) [(reinterpret__underscore (numtype_Fnn Fnn_F64) (numtype_Inn Inn_I64) (mk_num__1 Fnn_F64 fN_1))]"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:52.6-52.14 *)
lemma cvtop___is_wf :
	"(fun_cvtop__underscore numtype_1 numtype_2 v_cvtop__underscore v_num_underscore var_0) \<Longrightarrow>
	 (wf_cvtop__underscore numtype_1 numtype_2 v_cvtop__underscore) \<Longrightarrow>
	 (wf_num_underscore numtype_1 v_num_underscore) \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: num_underscore). (wf_num_underscore numtype_2 ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:62.1-62.87 *)
axiomatization narrow__underscore :: "M \<Rightarrow> N \<Rightarrow> sx \<Rightarrow> iN \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:62.6-62.15 *)
lemma narrow___is_wf :
	"(wf_uN v_M v_iN) \<Longrightarrow>
	 (ret_val = (narrow__underscore v_M v_N v_sx v_iN)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:76.1-76.102 *)
axiomatization ibits_underscore :: "N \<Rightarrow> iN \<Rightarrow> (bit list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:76.6-76.13 *)
lemma ibits__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val_lst = (ibits_underscore v_N v_iN)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: bit). (wf_bit ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:77.1-77.102 *)
axiomatization fbits_underscore :: "N \<Rightarrow> fN \<Rightarrow> (bit list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:77.6-77.13 *)
lemma fbits__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (ret_val_lst = (fbits_underscore v_N v_fN)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: bit). (wf_bit ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:78.1-78.103 *)
axiomatization ibytes_underscore :: "N \<Rightarrow> iN \<Rightarrow> (byte list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:78.6-78.14 *)
lemma ibytes__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val_lst = (ibytes_underscore v_N v_iN)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: byte). (wf_byte ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:79.1-79.103 *)
axiomatization fbytes_underscore :: "N \<Rightarrow> fN \<Rightarrow> (byte list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:79.6-79.14 *)
lemma fbytes__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (ret_val_lst = (fbytes_underscore v_N v_fN)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: byte). (wf_byte ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:80.1-80.103 *)
axiomatization nbytes_underscore :: "numtype \<Rightarrow> num_underscore \<Rightarrow> (byte list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:80.6-80.14 *)
lemma nbytes__is_wf :
	"(wf_num_underscore v_numtype v_num_underscore) \<Longrightarrow>
	 (ret_val_lst = (nbytes_underscore v_numtype v_num_underscore)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: byte). (wf_byte ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:81.1-81.103 *)
axiomatization vbytes_underscore :: "vectype \<Rightarrow> vec_underscore \<Rightarrow> (byte list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:81.6-81.14 *)
lemma vbytes__is_wf :
	"((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) v_vec_underscore) \<Longrightarrow>
	 (ret_val_lst = (vbytes_underscore v_vectype v_vec_underscore)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: byte). (wf_byte ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:83.1-83.85 *)
axiomatization inv_ibits_underscore :: "N \<Rightarrow> (bit list) \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:83.6-83.17 *)
lemma inv_ibits__is_wf :
	"list_all (\<lambda> (var_0 :: bit). (wf_bit var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = (inv_ibits_underscore v_N var_0_lst)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:84.1-84.85 *)
axiomatization inv_fbits_underscore :: "N \<Rightarrow> (bit list) \<Rightarrow> fN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:84.6-84.17 *)
lemma inv_fbits__is_wf :
	"list_all (\<lambda> (var_0 :: bit). (wf_bit var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = (inv_fbits_underscore v_N var_0_lst)) \<Longrightarrow>
	 (wf_fN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:85.1-85.86 *)
axiomatization inv_ibytes_underscore :: "N \<Rightarrow> (byte list) \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:85.6-85.18 *)
lemma inv_ibytes__is_wf :
	"list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = (inv_ibytes_underscore v_N var_0_lst)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:86.1-86.86 *)
axiomatization inv_fbytes_underscore :: "N \<Rightarrow> (byte list) \<Rightarrow> fN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:86.6-86.18 *)
lemma inv_fbytes__is_wf :
	"list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = (inv_fbytes_underscore v_N var_0_lst)) \<Longrightarrow>
	 (wf_fN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:87.1-87.84 *)
axiomatization inv_nbytes_underscore :: "numtype \<Rightarrow> (byte list) \<Rightarrow> num_underscore"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:87.6-87.18 *)
lemma inv_nbytes__is_wf :
	"list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = (inv_nbytes_underscore v_numtype var_0_lst)) \<Longrightarrow>
	 (wf_num_underscore v_numtype ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:88.1-88.84 *)
axiomatization inv_vbytes_underscore :: "vectype \<Rightarrow> (byte list) \<Rightarrow> vec_underscore"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:88.6-88.18 *)
lemma inv_vbytes__is_wf :
	"list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = (inv_vbytes_underscore v_vectype var_0_lst)) \<Longrightarrow>
	 ((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:110.1-110.29 *)
axiomatization inot_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:110.6-110.12 *)
lemma inot__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val = (inot_underscore v_N v_iN)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:111.1-111.29 *)
axiomatization irev_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:111.6-111.12 *)
lemma irev__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val = (irev_underscore v_N v_iN)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:113.1-113.39 *)
axiomatization iandnot_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:113.6-113.15 *)
lemma iandnot__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (iandnot_underscore v_N v_iN iN_0)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:124.1-124.27 *)
function (sequential, domintros) inez_underscore :: "N \<Rightarrow> iN \<Rightarrow> u32" where
		  "inez_underscore v_N i_1 = (mk_uN (res_bool ((proj_uN_0 i_1) \<noteq> 0)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:124.6-124.12 *)
lemma inez__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val = (inez_underscore v_N v_iN)) \<Longrightarrow>
	 (wf_uN 32 ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:131.1-131.49 *)
axiomatization ibitselect_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:131.6-131.18 *)
lemma ibitselect__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (wf_uN v_N iN_1) \<Longrightarrow>
	 (ret_val = (ibitselect_underscore v_N v_iN iN_0 iN_1)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:133.1-133.29 *)
function (sequential, domintros) ineg_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN" where
		  "ineg_underscore v_N i_1 = (mk_uN (((((2 ^ v_N) :: nat) - ((proj_uN_0 i_1) :: nat)) mod ((2 ^ v_N) :: nat)) :: nat))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:133.6-133.12 *)
lemma ineg__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val = (ineg_underscore v_N v_iN)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:132.6-132.12 *)
inductive fun_iabs_underscore :: "N \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> bool" where
	  fun_iabs__case_0 :
		"(fun_signed_underscore v_N (proj_uN_0 i_1) var_0) \<Longrightarrow>
		 fun_iabs_underscore v_N i_1 (if (var_0 \<ge> (0 :: nat)) then i_1 else (ineg_underscore v_N i_1))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:132.6-132.12 *)
lemma iabs__is_wf :
	"(fun_iabs_underscore v_N v_iN var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:134.6-134.12 *)
inductive fun_imin_underscore :: "N \<Rightarrow> sx \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> bool" where
	  fun_imin__case_0 :
		"((proj_uN_0 i_1) \<le> (proj_uN_0 i_2)) \<Longrightarrow>
		 fun_imin_underscore v_N U i_1 i_2 i_1"
	| fun_imin__case_1 :
		"((proj_uN_0 i_1) > (proj_uN_0 i_2)) \<Longrightarrow>
		 fun_imin_underscore v_N U i_1 i_2 i_2"
	| fun_imin__case_2 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) \<Longrightarrow>
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) \<Longrightarrow>
		 fun_imin_underscore v_N S i_1 i_2 (if (var_0 \<le> var_1) then i_1 else i_2)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:134.6-134.12 *)
lemma imin__is_wf :
	"(fun_imin_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:135.6-135.12 *)
inductive fun_imax_underscore :: "N \<Rightarrow> sx \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> bool" where
	  fun_imax__case_0 :
		"((proj_uN_0 i_1) \<ge> (proj_uN_0 i_2)) \<Longrightarrow>
		 fun_imax_underscore v_N U i_1 i_2 i_1"
	| fun_imax__case_1 :
		"((proj_uN_0 i_1) < (proj_uN_0 i_2)) \<Longrightarrow>
		 fun_imax_underscore v_N U i_1 i_2 i_2"
	| fun_imax__case_2 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) \<Longrightarrow>
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) \<Longrightarrow>
		 fun_imax_underscore v_N S i_1 i_2 (if (var_0 \<ge> var_1) then i_1 else i_2)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:135.6-135.12 *)
lemma imax__is_wf :
	"(fun_imax_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:136.6-136.16 *)
inductive fun_iadd_sat_underscore :: "N \<Rightarrow> sx \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> bool" where
	  fun_iadd_sat__case_0 :
		"fun_iadd_sat_underscore v_N U i_1 i_2 (mk_uN (sat_u_underscore v_N (((proj_uN_0 i_1) + (proj_uN_0 i_2)) :: nat)))"
	| fun_iadd_sat__case_1 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_2) \<Longrightarrow>
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_1) \<Longrightarrow>
		 (fun_inv_signed_underscore v_N (sat_s_underscore v_N (var_1 + var_2)) var_0) \<Longrightarrow>
		 fun_iadd_sat_underscore v_N S i_1 i_2 (mk_uN var_0)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:136.6-136.16 *)
lemma iadd_sat__is_wf :
	"(fun_iadd_sat_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:137.6-137.16 *)
inductive fun_isub_sat_underscore :: "N \<Rightarrow> sx \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> bool" where
	  fun_isub_sat__case_0 :
		"fun_isub_sat_underscore v_N U i_1 i_2 (mk_uN (sat_u_underscore v_N (((proj_uN_0 i_1) :: nat) - ((proj_uN_0 i_2) :: nat))))"
	| fun_isub_sat__case_1 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_2) \<Longrightarrow>
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_1) \<Longrightarrow>
		 (fun_inv_signed_underscore v_N (sat_s_underscore v_N (var_1 - var_2)) var_0) \<Longrightarrow>
		 fun_isub_sat_underscore v_N S i_1 i_2 (mk_uN var_0)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:137.6-137.16 *)
lemma isub_sat__is_wf :
	"(fun_isub_sat_underscore v_N v_sx v_iN iN_0 var_0) \<Longrightarrow>
	 (wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:138.1-138.82 *)
axiomatization iavgr_underscore :: "N \<Rightarrow> sx \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:138.6-138.13 *)
lemma iavgr__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (iavgr_underscore v_N v_sx v_iN iN_0)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:139.1-139.90 *)
axiomatization iq15mulr_sat_underscore :: "N \<Rightarrow> sx \<Rightarrow> iN \<Rightarrow> iN \<Rightarrow> iN"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:139.6-139.20 *)
lemma iq15mulr_sat__is_wf :
	"(wf_uN v_N v_iN) \<Longrightarrow>
	 (wf_uN v_N iN_0) \<Longrightarrow>
	 (ret_val = (iq15mulr_sat_underscore v_N v_sx v_iN iN_0)) \<Longrightarrow>
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:221.1-221.38 *)
axiomatization fpmin_underscore :: "N \<Rightarrow> fN \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:221.6-221.13 *)
lemma fpmin__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (wf_fN v_N fN_0) \<Longrightarrow>
	 (ret_val_lst = (fpmin_underscore v_N v_fN fN_0)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:222.1-222.38 *)
axiomatization fpmax_underscore :: "N \<Rightarrow> fN \<Rightarrow> fN \<Rightarrow> (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:222.6-222.13 *)
lemma fpmax__is_wf :
	"(wf_fN v_N v_fN) \<Longrightarrow>
	 (wf_fN v_N fN_0) \<Longrightarrow>
	 (ret_val_lst = (fpmax_underscore v_N v_fN fN_0)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:323.1-324.27 *)
function (sequential, domintros) packnum_underscore :: "lanetype \<Rightarrow> num_underscore \<Rightarrow> lane_underscore" where
		  "packnum_underscore lanetype_I32 c = (mk_lane__0 I32 c)"
		| "packnum_underscore lanetype_I64 c = (mk_lane__0 I64 c)"
		| "packnum_underscore lanetype_F32 c = (mk_lane__0 F32 c)"
		| "packnum_underscore lanetype_F64 c = (mk_lane__0 F64 c)"
		| "packnum_underscore lanetype_I8 (mk_num__0 Inn_I32 c) = (mk_lane__1 I8 (wrap__underscore (the ((size (valtype_numtype (unpack (lanetype_packtype I8)))))) (psize I8) c))"
		| "packnum_underscore lanetype_I16 (mk_num__0 Inn_I32 c) = (mk_lane__1 I16 (wrap__underscore (the ((size (valtype_numtype (unpack (lanetype_packtype I16)))))) (psize I16) c))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:323.6-323.15 *)
lemma packnum__is_wf :
	"(wf_num_underscore (unpack v_lanetype) v_num_underscore) \<Longrightarrow>
	 (ret_val = (packnum_underscore v_lanetype v_num_underscore)) \<Longrightarrow>
	 (wf_lane_underscore v_lanetype ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:328.1-329.29 *)
function (sequential, domintros) unpacknum_underscore :: "lanetype \<Rightarrow> lane_underscore \<Rightarrow> num_underscore" where
		  "unpacknum_underscore lanetype_I32 (mk_lane__0 I32 c) = c"
		| "unpacknum_underscore lanetype_I64 (mk_lane__0 I64 c) = c"
		| "unpacknum_underscore lanetype_F32 (mk_lane__0 F32 c) = c"
		| "unpacknum_underscore lanetype_F64 (mk_lane__0 F64 c) = c"
		| "unpacknum_underscore lanetype_I8 (mk_lane__1 I8 c) = (mk_num__0 Inn_I32 (extend__underscore (psize I8) (the ((size (valtype_numtype (unpack (lanetype_packtype I8)))))) U c))"
		| "unpacknum_underscore lanetype_I16 (mk_lane__1 I16 c) = (mk_num__0 Inn_I32 (extend__underscore (psize I16) (the ((size (valtype_numtype (unpack (lanetype_packtype I16)))))) U c))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:328.6-328.17 *)
lemma unpacknum__is_wf :
	"(wf_lane_underscore v_lanetype v_lane_underscore) \<Longrightarrow>
	 (ret_val = (unpacknum_underscore v_lanetype v_lane_underscore)) \<Longrightarrow>
	 (wf_num_underscore (unpack v_lanetype) ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:336.1-336.84 *)
axiomatization lanes_underscore :: "shape \<Rightarrow> vec_underscore \<Rightarrow> (lane_underscore list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:336.6-336.13 *)
lemma lanes__is_wf :
	"(wf_shape v_shape) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (ret_val_lst = (lanes_underscore v_shape v_vec_underscore)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: lane_underscore). (wf_lane_underscore (fun_lanetype v_shape) ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:339.1-340.36 *)
axiomatization inv_lanes_underscore :: "shape \<Rightarrow> (lane_underscore list) \<Rightarrow> vec_underscore"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:339.6-339.17 *)
lemma inv_lanes__is_wf :
	"(wf_shape v_shape) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: lane_underscore). (wf_lane_underscore (fun_lanetype v_shape) var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = (inv_lanes_underscore v_shape var_0_lst)) \<Longrightarrow>
	 (wf_uN 128 ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:343.1-343.28 *)
function (sequential, domintros) zeroop :: "vcvtop \<Rightarrow> (zero option)" where
		  "zeroop (vcvtop_EXTEND v_half v_sx) = None"
		| "zeroop (vcvtop_CONVERT half_opt v_sx) = None"
		| "zeroop (vcvtop_TRUNC_SAT v_sx zero_opt) = zero_opt"
		| "zeroop (vcvtop_DEMOTE v_zero) = (Some v_zero)"
		| "zeroop PROMOTELOW = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:350.1-350.28 *)
function (sequential, domintros) halfop :: "vcvtop \<Rightarrow> (half option)" where
		  "halfop (vcvtop_EXTEND v_half v_sx) = (Some v_half)"
		| "halfop (vcvtop_CONVERT half_opt v_sx) = half_opt"
		| "halfop (vcvtop_TRUNC_SAT v_sx zero_opt) = None"
		| "halfop (vcvtop_DEMOTE v_zero) = None"
		| "halfop PROMOTELOW = (Some LOW)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:357.1-357.32 *)
function (sequential, domintros) fun_half :: "half \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
		  "fun_half LOW i j = i"
		| "fun_half HIGH i j = j"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:362.1-363.28 *)
function (sequential, domintros) vvunop_underscore :: "vectype \<Rightarrow> vvunop \<Rightarrow> vec_underscore \<Rightarrow> vec_underscore" where
		  "vvunop_underscore V128 NOT v128 = (inot_underscore (the ((size valtype_V128))) v128)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:362.6-362.14 *)
lemma vvunop__is_wf :
	"((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) v_vec_underscore) \<Longrightarrow>
	 (ret_val = (vvunop_underscore v_vectype v_vvunop v_vec_underscore)) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:364.1-365.31 *)
function (sequential, domintros) vvbinop_underscore :: "vectype \<Rightarrow> vvbinop \<Rightarrow> vec_underscore \<Rightarrow> vec_underscore \<Rightarrow> vec_underscore" where
		  "vvbinop_underscore V128 vvbinop_AND v128_1 v128_2 = (iand_underscore (the ((size valtype_V128))) v128_1 v128_2)"
		| "vvbinop_underscore V128 ANDNOT v128_1 v128_2 = (iandnot_underscore (the ((size valtype_V128))) v128_1 v128_2)"
		| "vvbinop_underscore V128 vvbinop_OR v128_1 v128_2 = (ior_underscore (the ((size valtype_V128))) v128_1 v128_2)"
		| "vvbinop_underscore V128 vvbinop_XOR v128_1 v128_2 = (ixor_underscore (the ((size valtype_V128))) v128_1 v128_2)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:364.6-364.15 *)
lemma vvbinop__is_wf :
	"((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) v_vec_underscore) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) vec__0) \<Longrightarrow>
	 (ret_val = (vvbinop_underscore v_vectype v_vvbinop v_vec_underscore vec__0)) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:366.1-367.34 *)
function (sequential, domintros) vvternop_underscore :: "vectype \<Rightarrow> vvternop \<Rightarrow> vec_underscore \<Rightarrow> vec_underscore \<Rightarrow> vec_underscore \<Rightarrow> vec_underscore" where
		  "vvternop_underscore V128 BITSELECT v128_1 v128_2 v128_3 = (ibitselect_underscore (the ((size valtype_V128))) v128_1 v128_2 v128_3)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:366.6-366.16 *)
lemma vvternop__is_wf :
	"((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) v_vec_underscore) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) vec__0) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) vec__1) \<Longrightarrow>
	 (ret_val = (vvternop_underscore v_vectype v_vvternop v_vec_underscore vec__0 vec__1)) \<Longrightarrow>
	 (wf_uN (the ((size (valtype_vectype v_vectype)))) ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:377.6-377.13 *)
inductive fun_vunop_underscore :: "shape \<Rightarrow> vunop_underscore \<Rightarrow> vec_underscore \<Rightarrow> (vec_underscore list) \<Rightarrow> bool" where
	  fun_vunop__case_0 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_3 :: lane_underscore). ((proj_lane__2 lane_1_3) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all2 (\<lambda> (var_1 :: uN) (lane_1_3 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_3))) var_1)) var_1_lst lane_1_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_2 :: lane_underscore). ((proj_lane__2 lane_1_2) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all2 (\<lambda> (var_0 :: uN) (lane_1_2 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_2))) var_0)) var_0_lst lane_1_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I32 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 M_0 vunop_Jnn_N_ABS) v128_1 [v128]"
	| fun_vunop__case_1 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_6 :: lane_underscore). ((proj_lane__2 lane_1_6) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all2 (\<lambda> (var_1 :: uN) (lane_1_6 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_6))) var_1)) var_1_lst lane_1_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_5 :: lane_underscore). ((proj_lane__2 lane_1_5) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all2 (\<lambda> (var_0 :: uN) (lane_1_5 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_5))) var_0)) var_0_lst lane_1_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I64 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 M_0 vunop_Jnn_N_ABS) v128_1 [v128]"
	| fun_vunop__case_2 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_9 :: lane_underscore). ((proj_lane__2 lane_1_9) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all2 (\<lambda> (var_1 :: uN) (lane_1_9 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_9))) var_1)) var_1_lst lane_1_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_8 :: lane_underscore). ((proj_lane__2 lane_1_8) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all2 (\<lambda> (var_0 :: uN) (lane_1_8 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_8))) var_0)) var_0_lst lane_1_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I8 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 M_0 vunop_Jnn_N_ABS) v128_1 [v128]"
	| fun_vunop__case_3 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_12 :: lane_underscore). ((proj_lane__2 lane_1_12) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all2 (\<lambda> (var_1 :: uN) (lane_1_12 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_12))) var_1)) var_1_lst lane_1_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_11 :: lane_underscore). ((proj_lane__2 lane_1_11) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all2 (\<lambda> (var_0 :: uN) (lane_1_11 :: lane_underscore). (fun_iabs_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_11))) var_0)) var_0_lst lane_1_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I16 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 M_0 vunop_Jnn_N_ABS) v128_1 [v128]"
	| fun_vunop__case_4 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_14 :: lane_underscore). ((proj_lane__2 lane_1_14) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (lane_1_14 :: lane_underscore). (mk_lane__2 Jnn_I32 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_14)))))) lane_1_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_15 :: lane_underscore). ((proj_lane__2 lane_1_15) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_15 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_15))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 M_0 vunop_Jnn_N_NEG) v128_1 [v128]"
	| fun_vunop__case_5 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_17 :: lane_underscore). ((proj_lane__2 lane_1_17) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (lane_1_17 :: lane_underscore). (mk_lane__2 Jnn_I64 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_17)))))) lane_1_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_18 :: lane_underscore). ((proj_lane__2 lane_1_18) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_18 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_18))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 M_0 vunop_Jnn_N_NEG) v128_1 [v128]"
	| fun_vunop__case_6 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_20 :: lane_underscore). ((proj_lane__2 lane_1_20) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (lane_1_20 :: lane_underscore). (mk_lane__2 Jnn_I8 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_20)))))) lane_1_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_21 :: lane_underscore). ((proj_lane__2 lane_1_21) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_21 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_21))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 M_0 vunop_Jnn_N_NEG) v128_1 [v128]"
	| fun_vunop__case_7 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_23 :: lane_underscore). ((proj_lane__2 lane_1_23) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (lane_1_23 :: lane_underscore). (mk_lane__2 Jnn_I16 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_23)))))) lane_1_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_24 :: lane_underscore). ((proj_lane__2 lane_1_24) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_24 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (ineg_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_24))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 M_0 vunop_Jnn_N_NEG) v128_1 [v128]"
	| fun_vunop__case_8 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_26 :: lane_underscore). ((proj_lane__2 lane_1_26) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (lane_1_26 :: lane_underscore). (mk_lane__2 Jnn_I32 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_26)))))) lane_1_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_27 :: lane_underscore). ((proj_lane__2 lane_1_27) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_27 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_27))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vunop__0 Jnn_I32 M_0 vunop_Jnn_N_POPCNT) v128_1 [v128]"
	| fun_vunop__case_9 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_29 :: lane_underscore). ((proj_lane__2 lane_1_29) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (lane_1_29 :: lane_underscore). (mk_lane__2 Jnn_I64 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_29)))))) lane_1_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_30 :: lane_underscore). ((proj_lane__2 lane_1_30) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_30 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_30))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vunop__0 Jnn_I64 M_0 vunop_Jnn_N_POPCNT) v128_1 [v128]"
	| fun_vunop__case_10 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_32 :: lane_underscore). ((proj_lane__2 lane_1_32) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (lane_1_32 :: lane_underscore). (mk_lane__2 Jnn_I8 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_32)))))) lane_1_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_33 :: lane_underscore). ((proj_lane__2 lane_1_33) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_33 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_33))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vunop__0 Jnn_I8 M_0 vunop_Jnn_N_POPCNT) v128_1 [v128]"
	| fun_vunop__case_11 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_35 :: lane_underscore). ((proj_lane__2 lane_1_35) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (lane_1_35 :: lane_underscore). (mk_lane__2 Jnn_I16 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_35)))))) lane_1_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_36 :: lane_underscore). ((proj_lane__2 lane_1_36) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_36 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (ipopcnt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_36))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vunop__0 Jnn_I16 M_0 vunop_Jnn_N_POPCNT) v128_1 [v128]"
	| fun_vunop__case_12 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (map (\<lambda> (lane_1_38 :: lane_underscore). (map (\<lambda> (iter_0_49 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_49))) (fabs_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_38))))))))) lane_1_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_2 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_2)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_39 :: lane_underscore). list_all (\<lambda> (iter_0_50 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_50)))) (fabs_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_39)))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_ABS) v128_1 v128_lst"
	| fun_vunop__case_13 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (map (\<lambda> (lane_1_41 :: lane_underscore). (map (\<lambda> (iter_0_51 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_51))) (fabs_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_41))))))))) lane_1_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_4 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_4)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_42 :: lane_underscore). list_all (\<lambda> (iter_0_52 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_52)))) (fabs_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_42)))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_ABS) v128_1 v128_lst"
	| fun_vunop__case_14 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (map (\<lambda> (lane_1_44 :: lane_underscore). (map (\<lambda> (iter_0_53 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_53))) (fneg_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_44))))))))) lane_1_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_6 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_6)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_45 :: lane_underscore). list_all (\<lambda> (iter_0_54 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_54)))) (fneg_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_45)))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_NEG) v128_1 v128_lst"
	| fun_vunop__case_15 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (map (\<lambda> (lane_1_47 :: lane_underscore). (map (\<lambda> (iter_0_55 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_55))) (fneg_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_47))))))))) lane_1_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_8 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_8)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_48 :: lane_underscore). list_all (\<lambda> (iter_0_56 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_56)))) (fneg_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_48)))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_NEG) v128_1 v128_lst"
	| fun_vunop__case_16 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (map (\<lambda> (lane_1_50 :: lane_underscore). (map (\<lambda> (iter_0_57 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_57))) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_50))))))))) lane_1_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_10 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_10)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_51 :: lane_underscore). list_all (\<lambda> (iter_0_58 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_58)))) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_51)))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_SQRT) v128_1 v128_lst"
	| fun_vunop__case_17 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (map (\<lambda> (lane_1_53 :: lane_underscore). (map (\<lambda> (iter_0_59 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_59))) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_53))))))))) lane_1_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_12 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_12)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_54 :: lane_underscore). list_all (\<lambda> (iter_0_60 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_60)))) (fsqrt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_54)))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_SQRT) v128_1 v128_lst"
	| fun_vunop__case_18 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (map (\<lambda> (lane_1_56 :: lane_underscore). (map (\<lambda> (iter_0_61 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_61))) (fceil_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_56))))))))) lane_1_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_14 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_14)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_57 :: lane_underscore). list_all (\<lambda> (iter_0_62 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_62)))) (fceil_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_57)))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_CEIL) v128_1 v128_lst"
	| fun_vunop__case_19 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (map (\<lambda> (lane_1_59 :: lane_underscore). (map (\<lambda> (iter_0_63 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_63))) (fceil_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_59))))))))) lane_1_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_16 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_16)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_60 :: lane_underscore). list_all (\<lambda> (iter_0_64 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_64)))) (fceil_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_60)))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_CEIL) v128_1 v128_lst"
	| fun_vunop__case_20 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (map (\<lambda> (lane_1_62 :: lane_underscore). (map (\<lambda> (iter_0_65 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_65))) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_62))))))))) lane_1_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_18 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_18)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_63 :: lane_underscore). list_all (\<lambda> (iter_0_66 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_66)))) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_63)))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_FLOOR) v128_1 v128_lst"
	| fun_vunop__case_21 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (map (\<lambda> (lane_1_65 :: lane_underscore). (map (\<lambda> (iter_0_67 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_67))) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_65))))))))) lane_1_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_20 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_20)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_66 :: lane_underscore). list_all (\<lambda> (iter_0_68 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_68)))) (ffloor_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_66)))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_FLOOR) v128_1 v128_lst"
	| fun_vunop__case_22 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (map (\<lambda> (lane_1_68 :: lane_underscore). (map (\<lambda> (iter_0_69 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_69))) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_68))))))))) lane_1_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_22 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_22)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_69 :: lane_underscore). list_all (\<lambda> (iter_0_70 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_70)))) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_69)))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_TRUNC) v128_1 v128_lst"
	| fun_vunop__case_23 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (map (\<lambda> (lane_1_71 :: lane_underscore). (map (\<lambda> (iter_0_71 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_71))) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_71))))))))) lane_1_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_24 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_24)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_72 :: lane_underscore). list_all (\<lambda> (iter_0_72 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_72)))) (ftrunc_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_72)))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_TRUNC) v128_1 v128_lst"
	| fun_vunop__case_24 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (map (\<lambda> (lane_1_74 :: lane_underscore). (map (\<lambda> (iter_0_73 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_73))) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_74))))))))) lane_1_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_26 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_26)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_75 :: lane_underscore). list_all (\<lambda> (iter_0_74 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_74)))) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_75)))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vunop__1 Fnn_F32 M_0 vunop_Fnn_N_NEAREST) v128_1 v128_lst"
	| fun_vunop__case_25 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (map (\<lambda> (lane_1_77 :: lane_underscore). (map (\<lambda> (iter_0_75 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_75))) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_77))))))))) lane_1_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_28 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_28)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_78 :: lane_underscore). list_all (\<lambda> (iter_0_76 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_76)))) (fnearest_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_78)))))))) lane_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vunop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vunop__1 Fnn_F64 M_0 vunop_Fnn_N_NEAREST) v128_1 v128_lst"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:377.6-377.13 *)
lemma vunop__is_wf :
	"(fun_vunop_underscore v_shape v_vunop_underscore v_vec_underscore var_0) \<Longrightarrow>
	 (wf_shape v_shape) \<Longrightarrow>
	 (wf_vunop_underscore v_shape v_vunop_underscore) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: vec_underscore). (wf_uN 128 ret_val)) ret_val_lst"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:379.6-379.14 *)
inductive fun_vbinop_underscore :: "shape \<Rightarrow> vbinop_underscore \<Rightarrow> vec_underscore \<Rightarrow> vec_underscore \<Rightarrow> (vec_underscore list) \<Rightarrow> bool" where
	  fun_vbinop__case_0 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_80 :: lane_underscore). ((proj_lane__2 lane_1_80) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_2 :: lane_underscore). ((proj_lane__2 lane_2_2) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_80 :: lane_underscore) (lane_2_2 :: lane_underscore). (mk_lane__2 Jnn_I32 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_80))) (the ((proj_lane__2 lane_2_2)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_81 :: lane_underscore). ((proj_lane__2 lane_1_81) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_3 :: lane_underscore). ((proj_lane__2 lane_2_3) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_81 :: lane_underscore) (lane_2_3 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_81))) (the ((proj_lane__2 lane_2_3))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 vbinop_Jnn_N_ADD) v128_1 v128_2 [v128]"
	| fun_vbinop__case_1 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_83 :: lane_underscore). ((proj_lane__2 lane_1_83) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_5 :: lane_underscore). ((proj_lane__2 lane_2_5) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_83 :: lane_underscore) (lane_2_5 :: lane_underscore). (mk_lane__2 Jnn_I64 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_83))) (the ((proj_lane__2 lane_2_5)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_84 :: lane_underscore). ((proj_lane__2 lane_1_84) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_6 :: lane_underscore). ((proj_lane__2 lane_2_6) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_84 :: lane_underscore) (lane_2_6 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_84))) (the ((proj_lane__2 lane_2_6))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 vbinop_Jnn_N_ADD) v128_1 v128_2 [v128]"
	| fun_vbinop__case_2 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_86 :: lane_underscore). ((proj_lane__2 lane_1_86) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_8 :: lane_underscore). ((proj_lane__2 lane_2_8) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_86 :: lane_underscore) (lane_2_8 :: lane_underscore). (mk_lane__2 Jnn_I8 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_86))) (the ((proj_lane__2 lane_2_8)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_87 :: lane_underscore). ((proj_lane__2 lane_1_87) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_9 :: lane_underscore). ((proj_lane__2 lane_2_9) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_87 :: lane_underscore) (lane_2_9 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_87))) (the ((proj_lane__2 lane_2_9))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 vbinop_Jnn_N_ADD) v128_1 v128_2 [v128]"
	| fun_vbinop__case_3 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_89 :: lane_underscore). ((proj_lane__2 lane_1_89) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_11 :: lane_underscore). ((proj_lane__2 lane_2_11) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_89 :: lane_underscore) (lane_2_11 :: lane_underscore). (mk_lane__2 Jnn_I16 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_89))) (the ((proj_lane__2 lane_2_11)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_90 :: lane_underscore). ((proj_lane__2 lane_1_90) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_12 :: lane_underscore). ((proj_lane__2 lane_2_12) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_90 :: lane_underscore) (lane_2_12 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (iadd_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_90))) (the ((proj_lane__2 lane_2_12))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 vbinop_Jnn_N_ADD) v128_1 v128_2 [v128]"
	| fun_vbinop__case_4 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_92 :: lane_underscore). ((proj_lane__2 lane_1_92) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_14 :: lane_underscore). ((proj_lane__2 lane_2_14) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_92 :: lane_underscore) (lane_2_14 :: lane_underscore). (mk_lane__2 Jnn_I32 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_92))) (the ((proj_lane__2 lane_2_14)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_93 :: lane_underscore). ((proj_lane__2 lane_1_93) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_15 :: lane_underscore). ((proj_lane__2 lane_2_15) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_93 :: lane_underscore) (lane_2_15 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_93))) (the ((proj_lane__2 lane_2_15))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 vbinop_Jnn_N_SUB) v128_1 v128_2 [v128]"
	| fun_vbinop__case_5 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_95 :: lane_underscore). ((proj_lane__2 lane_1_95) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_17 :: lane_underscore). ((proj_lane__2 lane_2_17) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_95 :: lane_underscore) (lane_2_17 :: lane_underscore). (mk_lane__2 Jnn_I64 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_95))) (the ((proj_lane__2 lane_2_17)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_96 :: lane_underscore). ((proj_lane__2 lane_1_96) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_18 :: lane_underscore). ((proj_lane__2 lane_2_18) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_96 :: lane_underscore) (lane_2_18 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_96))) (the ((proj_lane__2 lane_2_18))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 vbinop_Jnn_N_SUB) v128_1 v128_2 [v128]"
	| fun_vbinop__case_6 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_98 :: lane_underscore). ((proj_lane__2 lane_1_98) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_20 :: lane_underscore). ((proj_lane__2 lane_2_20) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_98 :: lane_underscore) (lane_2_20 :: lane_underscore). (mk_lane__2 Jnn_I8 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_98))) (the ((proj_lane__2 lane_2_20)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_99 :: lane_underscore). ((proj_lane__2 lane_1_99) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_21 :: lane_underscore). ((proj_lane__2 lane_2_21) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_99 :: lane_underscore) (lane_2_21 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_99))) (the ((proj_lane__2 lane_2_21))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 vbinop_Jnn_N_SUB) v128_1 v128_2 [v128]"
	| fun_vbinop__case_7 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_101 :: lane_underscore). ((proj_lane__2 lane_1_101) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_23 :: lane_underscore). ((proj_lane__2 lane_2_23) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_101 :: lane_underscore) (lane_2_23 :: lane_underscore). (mk_lane__2 Jnn_I16 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_101))) (the ((proj_lane__2 lane_2_23)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_102 :: lane_underscore). ((proj_lane__2 lane_1_102) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_24 :: lane_underscore). ((proj_lane__2 lane_2_24) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_102 :: lane_underscore) (lane_2_24 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (isub_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_102))) (the ((proj_lane__2 lane_2_24))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 vbinop_Jnn_N_SUB) v128_1 v128_2 [v128]"
	| fun_vbinop__case_8 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_105 :: lane_underscore). ((proj_lane__2 lane_1_105) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_27 :: lane_underscore). ((proj_lane__2 lane_2_27) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_105 :: lane_underscore) (lane_2_27 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_105))) (the ((proj_lane__2 lane_2_27))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_104 :: lane_underscore). ((proj_lane__2 lane_1_104) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_26 :: lane_underscore). ((proj_lane__2 lane_2_26) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_104 :: lane_underscore) (lane_2_26 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_104))) (the ((proj_lane__2 lane_2_26))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I32 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_9 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_108 :: lane_underscore). ((proj_lane__2 lane_1_108) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_30 :: lane_underscore). ((proj_lane__2 lane_2_30) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_108 :: lane_underscore) (lane_2_30 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_108))) (the ((proj_lane__2 lane_2_30))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_107 :: lane_underscore). ((proj_lane__2 lane_1_107) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_29 :: lane_underscore). ((proj_lane__2 lane_2_29) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_107 :: lane_underscore) (lane_2_29 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_107))) (the ((proj_lane__2 lane_2_29))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I64 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_10 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_111 :: lane_underscore). ((proj_lane__2 lane_1_111) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_33 :: lane_underscore). ((proj_lane__2 lane_2_33) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_111 :: lane_underscore) (lane_2_33 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_111))) (the ((proj_lane__2 lane_2_33))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_110 :: lane_underscore). ((proj_lane__2 lane_1_110) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_32 :: lane_underscore). ((proj_lane__2 lane_2_32) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_110 :: lane_underscore) (lane_2_32 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_110))) (the ((proj_lane__2 lane_2_32))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I8 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_11 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_114 :: lane_underscore). ((proj_lane__2 lane_1_114) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_36 :: lane_underscore). ((proj_lane__2 lane_2_36) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_114 :: lane_underscore) (lane_2_36 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_114))) (the ((proj_lane__2 lane_2_36))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_113 :: lane_underscore). ((proj_lane__2 lane_1_113) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_35 :: lane_underscore). ((proj_lane__2 lane_2_35) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_113 :: lane_underscore) (lane_2_35 :: lane_underscore). (fun_imin_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_113))) (the ((proj_lane__2 lane_2_35))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I16 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 (vbinop_Jnn_N_MIN v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_12 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_117 :: lane_underscore). ((proj_lane__2 lane_1_117) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_39 :: lane_underscore). ((proj_lane__2 lane_2_39) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_117 :: lane_underscore) (lane_2_39 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_117))) (the ((proj_lane__2 lane_2_39))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_116 :: lane_underscore). ((proj_lane__2 lane_1_116) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_38 :: lane_underscore). ((proj_lane__2 lane_2_38) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_116 :: lane_underscore) (lane_2_38 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_116))) (the ((proj_lane__2 lane_2_38))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I32 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_13 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_120 :: lane_underscore). ((proj_lane__2 lane_1_120) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_42 :: lane_underscore). ((proj_lane__2 lane_2_42) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_120 :: lane_underscore) (lane_2_42 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_120))) (the ((proj_lane__2 lane_2_42))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_119 :: lane_underscore). ((proj_lane__2 lane_1_119) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_41 :: lane_underscore). ((proj_lane__2 lane_2_41) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_119 :: lane_underscore) (lane_2_41 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_119))) (the ((proj_lane__2 lane_2_41))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I64 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_14 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_123 :: lane_underscore). ((proj_lane__2 lane_1_123) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_45 :: lane_underscore). ((proj_lane__2 lane_2_45) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_123 :: lane_underscore) (lane_2_45 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_123))) (the ((proj_lane__2 lane_2_45))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_122 :: lane_underscore). ((proj_lane__2 lane_1_122) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_44 :: lane_underscore). ((proj_lane__2 lane_2_44) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_122 :: lane_underscore) (lane_2_44 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_122))) (the ((proj_lane__2 lane_2_44))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I8 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_15 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_126 :: lane_underscore). ((proj_lane__2 lane_1_126) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_48 :: lane_underscore). ((proj_lane__2 lane_2_48) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_126 :: lane_underscore) (lane_2_48 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_126))) (the ((proj_lane__2 lane_2_48))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_125 :: lane_underscore). ((proj_lane__2 lane_1_125) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_47 :: lane_underscore). ((proj_lane__2 lane_2_47) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_125 :: lane_underscore) (lane_2_47 :: lane_underscore). (fun_imax_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_125))) (the ((proj_lane__2 lane_2_47))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I16 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 (vbinop_Jnn_N_MAX v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_16 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_129 :: lane_underscore). ((proj_lane__2 lane_1_129) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_51 :: lane_underscore). ((proj_lane__2 lane_2_51) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_129 :: lane_underscore) (lane_2_51 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_129))) (the ((proj_lane__2 lane_2_51))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_128 :: lane_underscore). ((proj_lane__2 lane_1_128) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_50 :: lane_underscore). ((proj_lane__2 lane_2_50) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_128 :: lane_underscore) (lane_2_50 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_128))) (the ((proj_lane__2 lane_2_50))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I32 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 (ADD_SAT v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_17 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_132 :: lane_underscore). ((proj_lane__2 lane_1_132) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_54 :: lane_underscore). ((proj_lane__2 lane_2_54) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_132 :: lane_underscore) (lane_2_54 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_132))) (the ((proj_lane__2 lane_2_54))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_131 :: lane_underscore). ((proj_lane__2 lane_1_131) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_53 :: lane_underscore). ((proj_lane__2 lane_2_53) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_131 :: lane_underscore) (lane_2_53 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_131))) (the ((proj_lane__2 lane_2_53))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I64 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 (ADD_SAT v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_18 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_135 :: lane_underscore). ((proj_lane__2 lane_1_135) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_57 :: lane_underscore). ((proj_lane__2 lane_2_57) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_135 :: lane_underscore) (lane_2_57 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_135))) (the ((proj_lane__2 lane_2_57))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_134 :: lane_underscore). ((proj_lane__2 lane_1_134) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_56 :: lane_underscore). ((proj_lane__2 lane_2_56) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_134 :: lane_underscore) (lane_2_56 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_134))) (the ((proj_lane__2 lane_2_56))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I8 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 (ADD_SAT v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_19 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_138 :: lane_underscore). ((proj_lane__2 lane_1_138) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_60 :: lane_underscore). ((proj_lane__2 lane_2_60) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_138 :: lane_underscore) (lane_2_60 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_138))) (the ((proj_lane__2 lane_2_60))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_137 :: lane_underscore). ((proj_lane__2 lane_1_137) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_59 :: lane_underscore). ((proj_lane__2 lane_2_59) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_137 :: lane_underscore) (lane_2_59 :: lane_underscore). (fun_iadd_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_137))) (the ((proj_lane__2 lane_2_59))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I16 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 (ADD_SAT v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_20 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_141 :: lane_underscore). ((proj_lane__2 lane_1_141) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_63 :: lane_underscore). ((proj_lane__2 lane_2_63) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_141 :: lane_underscore) (lane_2_63 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_141))) (the ((proj_lane__2 lane_2_63))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_140 :: lane_underscore). ((proj_lane__2 lane_1_140) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_62 :: lane_underscore). ((proj_lane__2 lane_2_62) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_140 :: lane_underscore) (lane_2_62 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_140))) (the ((proj_lane__2 lane_2_62))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I32 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 (SUB_SAT v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_21 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_144 :: lane_underscore). ((proj_lane__2 lane_1_144) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_66 :: lane_underscore). ((proj_lane__2 lane_2_66) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_144 :: lane_underscore) (lane_2_66 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_144))) (the ((proj_lane__2 lane_2_66))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_143 :: lane_underscore). ((proj_lane__2 lane_1_143) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_65 :: lane_underscore). ((proj_lane__2 lane_2_65) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_143 :: lane_underscore) (lane_2_65 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_143))) (the ((proj_lane__2 lane_2_65))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I64 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 (SUB_SAT v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_22 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_147 :: lane_underscore). ((proj_lane__2 lane_1_147) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_69 :: lane_underscore). ((proj_lane__2 lane_2_69) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_147 :: lane_underscore) (lane_2_69 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_147))) (the ((proj_lane__2 lane_2_69))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_146 :: lane_underscore). ((proj_lane__2 lane_1_146) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_68 :: lane_underscore). ((proj_lane__2 lane_2_68) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_146 :: lane_underscore) (lane_2_68 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_146))) (the ((proj_lane__2 lane_2_68))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I8 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 (SUB_SAT v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_23 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_150 :: lane_underscore). ((proj_lane__2 lane_1_150) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_72 :: lane_underscore). ((proj_lane__2 lane_2_72) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_150 :: lane_underscore) (lane_2_72 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_150))) (the ((proj_lane__2 lane_2_72))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_149 :: lane_underscore). ((proj_lane__2 lane_1_149) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_71 :: lane_underscore). ((proj_lane__2 lane_2_71) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_149 :: lane_underscore) (lane_2_71 :: lane_underscore). (fun_isub_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_149))) (the ((proj_lane__2 lane_2_71))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (var_0 :: uN). (mk_lane__2 Jnn_I16 var_0)) var_0_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 var_1))) var_1_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 (SUB_SAT v_sx)) v128_1 v128_2 [v128]"
	| fun_vbinop__case_24 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_152 :: lane_underscore). ((proj_lane__2 lane_1_152) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_74 :: lane_underscore). ((proj_lane__2 lane_2_74) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_152 :: lane_underscore) (lane_2_74 :: lane_underscore). (mk_lane__2 Jnn_I32 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_152))) (the ((proj_lane__2 lane_2_74)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_153 :: lane_underscore). ((proj_lane__2 lane_1_153) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_75 :: lane_underscore). ((proj_lane__2 lane_2_75) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_153 :: lane_underscore) (lane_2_75 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_153))) (the ((proj_lane__2 lane_2_75))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 vbinop_Jnn_N_MUL) v128_1 v128_2 [v128]"
	| fun_vbinop__case_25 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_155 :: lane_underscore). ((proj_lane__2 lane_1_155) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_77 :: lane_underscore). ((proj_lane__2 lane_2_77) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_155 :: lane_underscore) (lane_2_77 :: lane_underscore). (mk_lane__2 Jnn_I64 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_155))) (the ((proj_lane__2 lane_2_77)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_156 :: lane_underscore). ((proj_lane__2 lane_1_156) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_78 :: lane_underscore). ((proj_lane__2 lane_2_78) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_156 :: lane_underscore) (lane_2_78 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_156))) (the ((proj_lane__2 lane_2_78))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 vbinop_Jnn_N_MUL) v128_1 v128_2 [v128]"
	| fun_vbinop__case_26 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_158 :: lane_underscore). ((proj_lane__2 lane_1_158) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_80 :: lane_underscore). ((proj_lane__2 lane_2_80) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_158 :: lane_underscore) (lane_2_80 :: lane_underscore). (mk_lane__2 Jnn_I8 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_158))) (the ((proj_lane__2 lane_2_80)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_159 :: lane_underscore). ((proj_lane__2 lane_1_159) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_81 :: lane_underscore). ((proj_lane__2 lane_2_81) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_159 :: lane_underscore) (lane_2_81 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_159))) (the ((proj_lane__2 lane_2_81))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 vbinop_Jnn_N_MUL) v128_1 v128_2 [v128]"
	| fun_vbinop__case_27 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_161 :: lane_underscore). ((proj_lane__2 lane_1_161) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_83 :: lane_underscore). ((proj_lane__2 lane_2_83) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_161 :: lane_underscore) (lane_2_83 :: lane_underscore). (mk_lane__2 Jnn_I16 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_161))) (the ((proj_lane__2 lane_2_83)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_162 :: lane_underscore). ((proj_lane__2 lane_1_162) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_84 :: lane_underscore). ((proj_lane__2 lane_2_84) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_162 :: lane_underscore) (lane_2_84 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (imul_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_162))) (the ((proj_lane__2 lane_2_84))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 vbinop_Jnn_N_MUL) v128_1 v128_2 [v128]"
	| fun_vbinop__case_28 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_164 :: lane_underscore). ((proj_lane__2 lane_1_164) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_86 :: lane_underscore). ((proj_lane__2 lane_2_86) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_164 :: lane_underscore) (lane_2_86 :: lane_underscore). (mk_lane__2 Jnn_I32 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I32)) U (the ((proj_lane__2 lane_1_164))) (the ((proj_lane__2 lane_2_86)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_165 :: lane_underscore). ((proj_lane__2 lane_1_165) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_87 :: lane_underscore). ((proj_lane__2 lane_2_87) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_165 :: lane_underscore) (lane_2_87 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I32)) U (the ((proj_lane__2 lane_1_165))) (the ((proj_lane__2 lane_2_87))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 AVGRU) v128_1 v128_2 [v128]"
	| fun_vbinop__case_29 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_167 :: lane_underscore). ((proj_lane__2 lane_1_167) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_89 :: lane_underscore). ((proj_lane__2 lane_2_89) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_167 :: lane_underscore) (lane_2_89 :: lane_underscore). (mk_lane__2 Jnn_I64 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I64)) U (the ((proj_lane__2 lane_1_167))) (the ((proj_lane__2 lane_2_89)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_168 :: lane_underscore). ((proj_lane__2 lane_1_168) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_90 :: lane_underscore). ((proj_lane__2 lane_2_90) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_168 :: lane_underscore) (lane_2_90 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I64)) U (the ((proj_lane__2 lane_1_168))) (the ((proj_lane__2 lane_2_90))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 AVGRU) v128_1 v128_2 [v128]"
	| fun_vbinop__case_30 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_170 :: lane_underscore). ((proj_lane__2 lane_1_170) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_92 :: lane_underscore). ((proj_lane__2 lane_2_92) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_170 :: lane_underscore) (lane_2_92 :: lane_underscore). (mk_lane__2 Jnn_I8 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I8)) U (the ((proj_lane__2 lane_1_170))) (the ((proj_lane__2 lane_2_92)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_171 :: lane_underscore). ((proj_lane__2 lane_1_171) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_93 :: lane_underscore). ((proj_lane__2 lane_2_93) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_171 :: lane_underscore) (lane_2_93 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I8)) U (the ((proj_lane__2 lane_1_171))) (the ((proj_lane__2 lane_2_93))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 AVGRU) v128_1 v128_2 [v128]"
	| fun_vbinop__case_31 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_173 :: lane_underscore). ((proj_lane__2 lane_1_173) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_95 :: lane_underscore). ((proj_lane__2 lane_2_95) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_173 :: lane_underscore) (lane_2_95 :: lane_underscore). (mk_lane__2 Jnn_I16 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I16)) U (the ((proj_lane__2 lane_1_173))) (the ((proj_lane__2 lane_2_95)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_174 :: lane_underscore). ((proj_lane__2 lane_1_174) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_96 :: lane_underscore). ((proj_lane__2 lane_2_96) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_174 :: lane_underscore) (lane_2_96 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (iavgr_underscore (lsizenn (lanetype_Jnn Jnn_I16)) U (the ((proj_lane__2 lane_1_174))) (the ((proj_lane__2 lane_2_96))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 AVGRU) v128_1 v128_2 [v128]"
	| fun_vbinop__case_32 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_176 :: lane_underscore). ((proj_lane__2 lane_1_176) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_98 :: lane_underscore). ((proj_lane__2 lane_2_98) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_176 :: lane_underscore) (lane_2_98 :: lane_underscore). (mk_lane__2 Jnn_I32 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) S (the ((proj_lane__2 lane_1_176))) (the ((proj_lane__2 lane_2_98)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_177 :: lane_underscore). ((proj_lane__2 lane_1_177) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_99 :: lane_underscore). ((proj_lane__2 lane_2_99) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_177 :: lane_underscore) (lane_2_99 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I32)) S (the ((proj_lane__2 lane_1_177))) (the ((proj_lane__2 lane_2_99))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vbinop__0 Jnn_I32 M_0 Q15MULR_SATS) v128_1 v128_2 [v128]"
	| fun_vbinop__case_33 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_179 :: lane_underscore). ((proj_lane__2 lane_1_179) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_101 :: lane_underscore). ((proj_lane__2 lane_2_101) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_179 :: lane_underscore) (lane_2_101 :: lane_underscore). (mk_lane__2 Jnn_I64 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) S (the ((proj_lane__2 lane_1_179))) (the ((proj_lane__2 lane_2_101)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_180 :: lane_underscore). ((proj_lane__2 lane_1_180) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_102 :: lane_underscore). ((proj_lane__2 lane_2_102) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_180 :: lane_underscore) (lane_2_102 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I64)) S (the ((proj_lane__2 lane_1_180))) (the ((proj_lane__2 lane_2_102))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vbinop__0 Jnn_I64 M_0 Q15MULR_SATS) v128_1 v128_2 [v128]"
	| fun_vbinop__case_34 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_182 :: lane_underscore). ((proj_lane__2 lane_1_182) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_104 :: lane_underscore). ((proj_lane__2 lane_2_104) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_182 :: lane_underscore) (lane_2_104 :: lane_underscore). (mk_lane__2 Jnn_I8 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) S (the ((proj_lane__2 lane_1_182))) (the ((proj_lane__2 lane_2_104)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_183 :: lane_underscore). ((proj_lane__2 lane_1_183) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_105 :: lane_underscore). ((proj_lane__2 lane_2_105) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_183 :: lane_underscore) (lane_2_105 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I8)) S (the ((proj_lane__2 lane_1_183))) (the ((proj_lane__2 lane_2_105))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vbinop__0 Jnn_I8 M_0 Q15MULR_SATS) v128_1 v128_2 [v128]"
	| fun_vbinop__case_35 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_185 :: lane_underscore). ((proj_lane__2 lane_1_185) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_107 :: lane_underscore). ((proj_lane__2 lane_2_107) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (list_zipWith (\<lambda> (lane_1_185 :: lane_underscore) (lane_2_107 :: lane_underscore). (mk_lane__2 Jnn_I16 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) S (the ((proj_lane__2 lane_1_185))) (the ((proj_lane__2 lane_2_107)))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_186 :: lane_underscore). ((proj_lane__2 lane_1_186) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_108 :: lane_underscore). ((proj_lane__2 lane_2_108) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_186 :: lane_underscore) (lane_2_108 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 (iq15mulr_sat_underscore (lsizenn (lanetype_Jnn Jnn_I16)) S (the ((proj_lane__2 lane_1_186))) (the ((proj_lane__2 lane_2_108))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vbinop__0 Jnn_I16 M_0 Q15MULR_SATS) v128_1 v128_2 [v128]"
	| fun_vbinop__case_36 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (\<lambda> (lane_1_188 :: lane_underscore) (lane_2_110 :: lane_underscore). (map (\<lambda> (iter_0_77 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_77))) (fadd_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_188)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_110))))))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_30 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_30)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_189 :: lane_underscore) (lane_2_111 :: lane_underscore). list_all (\<lambda> (iter_0_78 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_78)))) (fadd_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_189)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_111)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_ADD) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_37 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (\<lambda> (lane_1_191 :: lane_underscore) (lane_2_113 :: lane_underscore). (map (\<lambda> (iter_0_79 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_79))) (fadd_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_191)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_113))))))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_32 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_32)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_192 :: lane_underscore) (lane_2_114 :: lane_underscore). list_all (\<lambda> (iter_0_80 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_80)))) (fadd_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_192)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_114)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_ADD) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_38 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (\<lambda> (lane_1_194 :: lane_underscore) (lane_2_116 :: lane_underscore). (map (\<lambda> (iter_0_81 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_81))) (fsub_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_194)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_116))))))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_34 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_34)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_195 :: lane_underscore) (lane_2_117 :: lane_underscore). list_all (\<lambda> (iter_0_82 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_82)))) (fsub_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_195)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_117)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_SUB) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_39 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (\<lambda> (lane_1_197 :: lane_underscore) (lane_2_119 :: lane_underscore). (map (\<lambda> (iter_0_83 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_83))) (fsub_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_197)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_119))))))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_36 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_36)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_198 :: lane_underscore) (lane_2_120 :: lane_underscore). list_all (\<lambda> (iter_0_84 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_84)))) (fsub_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_198)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_120)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_SUB) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_40 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (\<lambda> (lane_1_200 :: lane_underscore) (lane_2_122 :: lane_underscore). (map (\<lambda> (iter_0_85 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_85))) (fmul_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_200)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_122))))))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_38 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_38)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_201 :: lane_underscore) (lane_2_123 :: lane_underscore). list_all (\<lambda> (iter_0_86 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_86)))) (fmul_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_201)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_123)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_MUL) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_41 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (\<lambda> (lane_1_203 :: lane_underscore) (lane_2_125 :: lane_underscore). (map (\<lambda> (iter_0_87 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_87))) (fmul_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_203)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_125))))))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_40 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_40)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_204 :: lane_underscore) (lane_2_126 :: lane_underscore). list_all (\<lambda> (iter_0_88 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_88)))) (fmul_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_204)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_126)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_MUL) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_42 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (\<lambda> (lane_1_206 :: lane_underscore) (lane_2_128 :: lane_underscore). (map (\<lambda> (iter_0_89 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_89))) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_206)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_128))))))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_42 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_42)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_207 :: lane_underscore) (lane_2_129 :: lane_underscore). list_all (\<lambda> (iter_0_90 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_90)))) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_207)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_129)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_DIV) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_43 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (\<lambda> (lane_1_209 :: lane_underscore) (lane_2_131 :: lane_underscore). (map (\<lambda> (iter_0_91 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_91))) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_209)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_131))))))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_44 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_44)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_210 :: lane_underscore) (lane_2_132 :: lane_underscore). list_all (\<lambda> (iter_0_92 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_92)))) (fdiv_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_210)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_132)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_DIV) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_44 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (\<lambda> (lane_1_212 :: lane_underscore) (lane_2_134 :: lane_underscore). (map (\<lambda> (iter_0_93 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_93))) (fmin_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_212)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_134))))))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_46 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_46)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_213 :: lane_underscore) (lane_2_135 :: lane_underscore). list_all (\<lambda> (iter_0_94 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_94)))) (fmin_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_213)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_135)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_MIN) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_45 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (\<lambda> (lane_1_215 :: lane_underscore) (lane_2_137 :: lane_underscore). (map (\<lambda> (iter_0_95 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_95))) (fmin_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_215)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_137))))))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_48 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_48)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_216 :: lane_underscore) (lane_2_138 :: lane_underscore). list_all (\<lambda> (iter_0_96 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_96)))) (fmin_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_216)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_138)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_MIN) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_46 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (\<lambda> (lane_1_218 :: lane_underscore) (lane_2_140 :: lane_underscore). (map (\<lambda> (iter_0_97 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_97))) (fmax_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_218)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_140))))))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_50 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_50)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_219 :: lane_underscore) (lane_2_141 :: lane_underscore). list_all (\<lambda> (iter_0_98 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_98)))) (fmax_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_219)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_141)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 vbinop_Fnn_N_MAX) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_47 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (\<lambda> (lane_1_221 :: lane_underscore) (lane_2_143 :: lane_underscore). (map (\<lambda> (iter_0_99 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_99))) (fmax_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_221)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_143))))))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_52 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_52)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_222 :: lane_underscore) (lane_2_144 :: lane_underscore). list_all (\<lambda> (iter_0_100 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_100)))) (fmax_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_222)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_144)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 vbinop_Fnn_N_MAX) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_48 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (\<lambda> (lane_1_224 :: lane_underscore) (lane_2_146 :: lane_underscore). (map (\<lambda> (iter_0_101 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_101))) (fpmin_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_224)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_146))))))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_54 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_54)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_225 :: lane_underscore) (lane_2_147 :: lane_underscore). list_all (\<lambda> (iter_0_102 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_102)))) (fpmin_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_225)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_147)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 PMIN) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_49 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (\<lambda> (lane_1_227 :: lane_underscore) (lane_2_149 :: lane_underscore). (map (\<lambda> (iter_0_103 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_103))) (fpmin_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_227)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_149))))))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_56 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_56)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_228 :: lane_underscore) (lane_2_150 :: lane_underscore). list_all (\<lambda> (iter_0_104 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_104)))) (fpmin_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_228)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_150)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 PMIN) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_50 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (\<lambda> (lane_1_230 :: lane_underscore) (lane_2_152 :: lane_underscore). (map (\<lambda> (iter_0_105 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_105))) (fpmax_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_230)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_152))))))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_58 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) lane_lst_58)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_231 :: lane_underscore) (lane_2_153 :: lane_underscore). list_all (\<lambda> (iter_0_106 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F32) (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 iter_0_106)))) (fpmax_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_231)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_153)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vbinop__1 Fnn_F32 M_0 PMAX) v128_1 v128_2 v128_lst"
	| fun_vbinop__case_51 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_lst_lst = (setproduct_underscore  (list_zipWith (\<lambda> (lane_1_233 :: lane_underscore) (lane_2_155 :: lane_underscore). (map (\<lambda> (iter_0_107 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_107))) (fpmax_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_233)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_155))))))))) lane_1_lst lane_2_lst))) \<Longrightarrow>
		 (v128_lst = (map (\<lambda> (lane_lst_60 :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) lane_lst_60)) lane_lst_lst)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_234 :: lane_underscore) (lane_2_156 :: lane_underscore). list_all (\<lambda> (iter_0_108 :: fN). (wf_lane_underscore (lanetype_Fnn Fnn_F64) (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 iter_0_108)))) (fpmax_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_234)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_156)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vbinop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vbinop__1 Fnn_F64 M_0 PMAX) v128_1 v128_2 v128_lst"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:379.6-379.14 *)
lemma vbinop__is_wf :
	"(fun_vbinop_underscore v_shape v_vbinop_underscore v_vec_underscore vec__0 var_0) \<Longrightarrow>
	 (wf_shape v_shape) \<Longrightarrow>
	 (wf_vbinop_underscore v_shape v_vbinop_underscore) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (wf_uN 128 vec__0) \<Longrightarrow>
	 (ret_val_lst = var_0) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: vec_underscore). (wf_uN 128 ret_val)) ret_val_lst"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:381.6-381.14 *)
inductive fun_vrelop_underscore :: "shape \<Rightarrow> vrelop_underscore \<Rightarrow> vec_underscore \<Rightarrow> vec_underscore \<Rightarrow> vec_underscore \<Rightarrow> bool" where
	  fun_vrelop__case_0 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_236 :: lane_underscore). ((proj_lane__2 lane_1_236) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_158 :: lane_underscore). ((proj_lane__2 lane_2_158) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_236 :: lane_underscore) (lane_2_158 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_236))) (the ((proj_lane__2 lane_2_158)))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_2 :: iN). (mk_lane__2 Jnn_I32 lane_3_2)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_237 :: lane_underscore). ((proj_lane__2 lane_1_237) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_159 :: lane_underscore). ((proj_lane__2 lane_2_159) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_237 :: lane_underscore) (lane_2_159 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_237))) (the ((proj_lane__2 lane_2_159)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_3 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_3))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 vrelop_Jnn_N_EQ) v128_1 v128_2 v128"
	| fun_vrelop__case_1 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_239 :: lane_underscore). ((proj_lane__2 lane_1_239) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_161 :: lane_underscore). ((proj_lane__2 lane_2_161) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_239 :: lane_underscore) (lane_2_161 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_239))) (the ((proj_lane__2 lane_2_161)))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_5 :: iN). (mk_lane__2 Jnn_I64 lane_3_5)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_240 :: lane_underscore). ((proj_lane__2 lane_1_240) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_162 :: lane_underscore). ((proj_lane__2 lane_2_162) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_240 :: lane_underscore) (lane_2_162 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_240))) (the ((proj_lane__2 lane_2_162)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_6 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_6))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 vrelop_Jnn_N_EQ) v128_1 v128_2 v128"
	| fun_vrelop__case_2 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_242 :: lane_underscore). ((proj_lane__2 lane_1_242) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_164 :: lane_underscore). ((proj_lane__2 lane_2_164) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_242 :: lane_underscore) (lane_2_164 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_242))) (the ((proj_lane__2 lane_2_164)))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (lane_3_8 :: iN). (mk_lane__2 Jnn_I8 lane_3_8)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_243 :: lane_underscore). ((proj_lane__2 lane_1_243) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_165 :: lane_underscore). ((proj_lane__2 lane_2_165) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_243 :: lane_underscore) (lane_2_165 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_243))) (the ((proj_lane__2 lane_2_165)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_9 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_9))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 vrelop_Jnn_N_EQ) v128_1 v128_2 v128"
	| fun_vrelop__case_3 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_245 :: lane_underscore). ((proj_lane__2 lane_1_245) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_167 :: lane_underscore). ((proj_lane__2 lane_2_167) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_245 :: lane_underscore) (lane_2_167 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_245))) (the ((proj_lane__2 lane_2_167)))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (lane_3_11 :: iN). (mk_lane__2 Jnn_I16 lane_3_11)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_246 :: lane_underscore). ((proj_lane__2 lane_1_246) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_168 :: lane_underscore). ((proj_lane__2 lane_2_168) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_246 :: lane_underscore) (lane_2_168 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (ieq_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_246))) (the ((proj_lane__2 lane_2_168)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_12 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_12))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 vrelop_Jnn_N_EQ) v128_1 v128_2 v128"
	| fun_vrelop__case_4 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_248 :: lane_underscore). ((proj_lane__2 lane_1_248) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_170 :: lane_underscore). ((proj_lane__2 lane_2_170) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_248 :: lane_underscore) (lane_2_170 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_248))) (the ((proj_lane__2 lane_2_170)))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_14 :: iN). (mk_lane__2 Jnn_I32 lane_3_14)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_249 :: lane_underscore). ((proj_lane__2 lane_1_249) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_171 :: lane_underscore). ((proj_lane__2 lane_2_171) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_249 :: lane_underscore) (lane_2_171 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I32)) (the ((proj_lane__2 lane_1_249))) (the ((proj_lane__2 lane_2_171)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_15 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_15))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 vrelop_Jnn_N_NE) v128_1 v128_2 v128"
	| fun_vrelop__case_5 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_251 :: lane_underscore). ((proj_lane__2 lane_1_251) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_173 :: lane_underscore). ((proj_lane__2 lane_2_173) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_251 :: lane_underscore) (lane_2_173 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_251))) (the ((proj_lane__2 lane_2_173)))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_17 :: iN). (mk_lane__2 Jnn_I64 lane_3_17)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_252 :: lane_underscore). ((proj_lane__2 lane_1_252) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_174 :: lane_underscore). ((proj_lane__2 lane_2_174) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_252 :: lane_underscore) (lane_2_174 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I64)) (the ((proj_lane__2 lane_1_252))) (the ((proj_lane__2 lane_2_174)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_18 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_18))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 vrelop_Jnn_N_NE) v128_1 v128_2 v128"
	| fun_vrelop__case_6 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_254 :: lane_underscore). ((proj_lane__2 lane_1_254) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_176 :: lane_underscore). ((proj_lane__2 lane_2_176) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_254 :: lane_underscore) (lane_2_176 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_254))) (the ((proj_lane__2 lane_2_176)))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (lane_3_20 :: iN). (mk_lane__2 Jnn_I8 lane_3_20)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_255 :: lane_underscore). ((proj_lane__2 lane_1_255) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_177 :: lane_underscore). ((proj_lane__2 lane_2_177) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_255 :: lane_underscore) (lane_2_177 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I8)) (the ((proj_lane__2 lane_1_255))) (the ((proj_lane__2 lane_2_177)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_21 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_21))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 vrelop_Jnn_N_NE) v128_1 v128_2 v128"
	| fun_vrelop__case_7 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_257 :: lane_underscore). ((proj_lane__2 lane_1_257) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_179 :: lane_underscore). ((proj_lane__2 lane_2_179) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_257 :: lane_underscore) (lane_2_179 :: lane_underscore). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_257))) (the ((proj_lane__2 lane_2_179)))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (lane_3_23 :: iN). (mk_lane__2 Jnn_I16 lane_3_23)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_258 :: lane_underscore). ((proj_lane__2 lane_1_258) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_180 :: lane_underscore). ((proj_lane__2 lane_2_180) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_258 :: lane_underscore) (lane_2_180 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (ine_underscore (lsizenn (lanetype_Jnn Jnn_I16)) (the ((proj_lane__2 lane_1_258))) (the ((proj_lane__2 lane_2_180)))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_24 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_24))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 vrelop_Jnn_N_NE) v128_1 v128_2 v128"
	| fun_vrelop__case_8 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_261 :: lane_underscore). ((proj_lane__2 lane_1_261) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_183 :: lane_underscore). ((proj_lane__2 lane_2_183) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_261 :: lane_underscore) (lane_2_183 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_261))) (the ((proj_lane__2 lane_2_183))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_260 :: lane_underscore). ((proj_lane__2 lane_1_260) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_182 :: lane_underscore). ((proj_lane__2 lane_2_182) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_260 :: lane_underscore) (lane_2_182 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_260))) (the ((proj_lane__2 lane_2_182))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_3_lst = (map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_0)))) var_0_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_26 :: iN). (mk_lane__2 Jnn_I32 lane_3_26)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_27 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_27))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_9 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_264 :: lane_underscore). ((proj_lane__2 lane_1_264) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_186 :: lane_underscore). ((proj_lane__2 lane_2_186) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_264 :: lane_underscore) (lane_2_186 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_264))) (the ((proj_lane__2 lane_2_186))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_263 :: lane_underscore). ((proj_lane__2 lane_1_263) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_185 :: lane_underscore). ((proj_lane__2 lane_2_185) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_263 :: lane_underscore) (lane_2_185 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_263))) (the ((proj_lane__2 lane_2_185))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_3_lst = (map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_0)))) var_0_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_29 :: iN). (mk_lane__2 Jnn_I64 lane_3_29)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_30 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_30))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_10 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_267 :: lane_underscore). ((proj_lane__2 lane_1_267) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_189 :: lane_underscore). ((proj_lane__2 lane_2_189) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_267 :: lane_underscore) (lane_2_189 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_267))) (the ((proj_lane__2 lane_2_189))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_266 :: lane_underscore). ((proj_lane__2 lane_1_266) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_188 :: lane_underscore). ((proj_lane__2 lane_2_188) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_266 :: lane_underscore) (lane_2_188 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_266))) (the ((proj_lane__2 lane_2_188))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_3_lst = (map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_0)))) var_0_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (lane_3_32 :: iN). (mk_lane__2 Jnn_I8 lane_3_32)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_33 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_33))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_11 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_270 :: lane_underscore). ((proj_lane__2 lane_1_270) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_192 :: lane_underscore). ((proj_lane__2 lane_2_192) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_270 :: lane_underscore) (lane_2_192 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_270))) (the ((proj_lane__2 lane_2_192))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_269 :: lane_underscore). ((proj_lane__2 lane_1_269) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_191 :: lane_underscore). ((proj_lane__2 lane_2_191) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_269 :: lane_underscore) (lane_2_191 :: lane_underscore). (fun_ilt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_269))) (the ((proj_lane__2 lane_2_191))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_3_lst = (map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_0)))) var_0_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (lane_3_35 :: iN). (mk_lane__2 Jnn_I16 lane_3_35)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_36 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_36))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 (vrelop_Jnn_N_LT v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_12 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_273 :: lane_underscore). ((proj_lane__2 lane_1_273) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_195 :: lane_underscore). ((proj_lane__2 lane_2_195) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_273 :: lane_underscore) (lane_2_195 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_273))) (the ((proj_lane__2 lane_2_195))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_272 :: lane_underscore). ((proj_lane__2 lane_1_272) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_194 :: lane_underscore). ((proj_lane__2 lane_2_194) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_272 :: lane_underscore) (lane_2_194 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_272))) (the ((proj_lane__2 lane_2_194))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_3_lst = (map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_0)))) var_0_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_38 :: iN). (mk_lane__2 Jnn_I32 lane_3_38)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_39 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_39))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_13 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_276 :: lane_underscore). ((proj_lane__2 lane_1_276) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_198 :: lane_underscore). ((proj_lane__2 lane_2_198) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_276 :: lane_underscore) (lane_2_198 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_276))) (the ((proj_lane__2 lane_2_198))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_275 :: lane_underscore). ((proj_lane__2 lane_1_275) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_197 :: lane_underscore). ((proj_lane__2 lane_2_197) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_275 :: lane_underscore) (lane_2_197 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_275))) (the ((proj_lane__2 lane_2_197))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_3_lst = (map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_0)))) var_0_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_41 :: iN). (mk_lane__2 Jnn_I64 lane_3_41)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_42 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_42))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_14 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_279 :: lane_underscore). ((proj_lane__2 lane_1_279) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_201 :: lane_underscore). ((proj_lane__2 lane_2_201) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_279 :: lane_underscore) (lane_2_201 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_279))) (the ((proj_lane__2 lane_2_201))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_278 :: lane_underscore). ((proj_lane__2 lane_1_278) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_200 :: lane_underscore). ((proj_lane__2 lane_2_200) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_278 :: lane_underscore) (lane_2_200 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_278))) (the ((proj_lane__2 lane_2_200))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_3_lst = (map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_0)))) var_0_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (lane_3_44 :: iN). (mk_lane__2 Jnn_I8 lane_3_44)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_45 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_45))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_15 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_282 :: lane_underscore). ((proj_lane__2 lane_1_282) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_204 :: lane_underscore). ((proj_lane__2 lane_2_204) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_282 :: lane_underscore) (lane_2_204 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_282))) (the ((proj_lane__2 lane_2_204))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_281 :: lane_underscore). ((proj_lane__2 lane_1_281) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_203 :: lane_underscore). ((proj_lane__2 lane_2_203) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_281 :: lane_underscore) (lane_2_203 :: lane_underscore). (fun_igt_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_281))) (the ((proj_lane__2 lane_2_203))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_3_lst = (map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_0)))) var_0_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (lane_3_47 :: iN). (mk_lane__2 Jnn_I16 lane_3_47)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_48 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_48))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 (vrelop_Jnn_N_GT v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_16 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_285 :: lane_underscore). ((proj_lane__2 lane_1_285) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_207 :: lane_underscore). ((proj_lane__2 lane_2_207) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_285 :: lane_underscore) (lane_2_207 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_285))) (the ((proj_lane__2 lane_2_207))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_284 :: lane_underscore). ((proj_lane__2 lane_1_284) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_206 :: lane_underscore). ((proj_lane__2 lane_2_206) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_284 :: lane_underscore) (lane_2_206 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_284))) (the ((proj_lane__2 lane_2_206))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_3_lst = (map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_0)))) var_0_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_50 :: iN). (mk_lane__2 Jnn_I32 lane_3_50)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_51 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_51))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_17 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_288 :: lane_underscore). ((proj_lane__2 lane_1_288) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_210 :: lane_underscore). ((proj_lane__2 lane_2_210) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_288 :: lane_underscore) (lane_2_210 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_288))) (the ((proj_lane__2 lane_2_210))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_287 :: lane_underscore). ((proj_lane__2 lane_1_287) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_209 :: lane_underscore). ((proj_lane__2 lane_2_209) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_287 :: lane_underscore) (lane_2_209 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_287))) (the ((proj_lane__2 lane_2_209))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_3_lst = (map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_0)))) var_0_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_53 :: iN). (mk_lane__2 Jnn_I64 lane_3_53)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_54 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_54))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_18 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_291 :: lane_underscore). ((proj_lane__2 lane_1_291) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_213 :: lane_underscore). ((proj_lane__2 lane_2_213) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_291 :: lane_underscore) (lane_2_213 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_291))) (the ((proj_lane__2 lane_2_213))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_290 :: lane_underscore). ((proj_lane__2 lane_1_290) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_212 :: lane_underscore). ((proj_lane__2 lane_2_212) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_290 :: lane_underscore) (lane_2_212 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_290))) (the ((proj_lane__2 lane_2_212))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_3_lst = (map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_0)))) var_0_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (lane_3_56 :: iN). (mk_lane__2 Jnn_I8 lane_3_56)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_57 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_57))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_19 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_294 :: lane_underscore). ((proj_lane__2 lane_1_294) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_216 :: lane_underscore). ((proj_lane__2 lane_2_216) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_294 :: lane_underscore) (lane_2_216 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_294))) (the ((proj_lane__2 lane_2_216))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_293 :: lane_underscore). ((proj_lane__2 lane_1_293) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_215 :: lane_underscore). ((proj_lane__2 lane_2_215) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_293 :: lane_underscore) (lane_2_215 :: lane_underscore). (fun_ile_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_293))) (the ((proj_lane__2 lane_2_215))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_3_lst = (map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_0)))) var_0_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (lane_3_59 :: iN). (mk_lane__2 Jnn_I16 lane_3_59)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_60 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_60))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 (vrelop_Jnn_N_LE v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_20 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_297 :: lane_underscore). ((proj_lane__2 lane_1_297) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_219 :: lane_underscore). ((proj_lane__2 lane_2_219) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_297 :: lane_underscore) (lane_2_219 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_297))) (the ((proj_lane__2 lane_2_219))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_296 :: lane_underscore). ((proj_lane__2 lane_1_296) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_218 :: lane_underscore). ((proj_lane__2 lane_2_218) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_296 :: lane_underscore) (lane_2_218 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I32)) v_sx (the ((proj_lane__2 lane_1_296))) (the ((proj_lane__2 lane_2_218))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_3_lst = (map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I32)) S (mk_uN (proj_uN_0 var_0)))) var_0_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I32) (mk_dim v_M)) (map (\<lambda> (lane_3_62 :: iN). (mk_lane__2 Jnn_I32 lane_3_62)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_63 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I32) (mk_dim v_M))) (mk_lane__2 Jnn_I32 lane_3_63))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I32 (mk_dim v_M)) (mk_vrelop__0 Jnn_I32 M_0 (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_21 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_300 :: lane_underscore). ((proj_lane__2 lane_1_300) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_222 :: lane_underscore). ((proj_lane__2 lane_2_222) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_300 :: lane_underscore) (lane_2_222 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_300))) (the ((proj_lane__2 lane_2_222))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_299 :: lane_underscore). ((proj_lane__2 lane_1_299) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_221 :: lane_underscore). ((proj_lane__2 lane_2_221) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_299 :: lane_underscore) (lane_2_221 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I64)) v_sx (the ((proj_lane__2 lane_1_299))) (the ((proj_lane__2 lane_2_221))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_3_lst = (map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I64)) S (mk_uN (proj_uN_0 var_0)))) var_0_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I64) (mk_dim v_M)) (map (\<lambda> (lane_3_65 :: iN). (mk_lane__2 Jnn_I64 lane_3_65)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_66 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I64) (mk_dim v_M))) (mk_lane__2 Jnn_I64 lane_3_66))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I64 (mk_dim v_M)) (mk_vrelop__0 Jnn_I64 M_0 (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_22 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_303 :: lane_underscore). ((proj_lane__2 lane_1_303) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_225 :: lane_underscore). ((proj_lane__2 lane_2_225) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_303 :: lane_underscore) (lane_2_225 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_303))) (the ((proj_lane__2 lane_2_225))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_302 :: lane_underscore). ((proj_lane__2 lane_1_302) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_224 :: lane_underscore). ((proj_lane__2 lane_2_224) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_302 :: lane_underscore) (lane_2_224 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I8)) v_sx (the ((proj_lane__2 lane_1_302))) (the ((proj_lane__2 lane_2_224))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_3_lst = (map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I8)) S (mk_uN (proj_uN_0 var_0)))) var_0_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I8) (mk_dim v_M)) (map (\<lambda> (lane_3_68 :: iN). (mk_lane__2 Jnn_I8 lane_3_68)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_69 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I8) (mk_dim v_M))) (mk_lane__2 Jnn_I8 lane_3_69))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I8 (mk_dim v_M)) (mk_vrelop__0 Jnn_I8 M_0 (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_23 :
		"((length var_1_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_306 :: lane_underscore). ((proj_lane__2 lane_1_306) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_228 :: lane_underscore). ((proj_lane__2 lane_2_228) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_1 :: uN) (lane_1_306 :: lane_underscore) (lane_2_228 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_306))) (the ((proj_lane__2 lane_2_228))) var_1)) var_1_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 ((length var_0_lst) = (length lane_1_lst)) \<Longrightarrow>
		 ((length var_0_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_305 :: lane_underscore). ((proj_lane__2 lane_1_305) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_227 :: lane_underscore). ((proj_lane__2 lane_2_227) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all3 (\<lambda> (var_0 :: uN) (lane_1_305 :: lane_underscore) (lane_2_227 :: lane_underscore). (fun_ige_underscore (lsizenn (lanetype_Jnn Jnn_I16)) v_sx (the ((proj_lane__2 lane_1_305))) (the ((proj_lane__2 lane_2_227))) var_0)) var_0_lst lane_1_lst lane_2_lst \<Longrightarrow>
		 (lane_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 (lane_3_lst = (map (\<lambda> (var_0 :: uN). (extend__underscore (Suc 0) (lsizenn (lanetype_Jnn Jnn_I16)) S (mk_uN (proj_uN_0 var_0)))) var_0_lst)) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Jnn Jnn_I16) (mk_dim v_M)) (map (\<lambda> (lane_3_71 :: iN). (mk_lane__2 Jnn_I16 lane_3_71)) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: uN). (wf_uN 1 (mk_uN (proj_uN_0 var_1)))) var_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_3_72 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_I16) (mk_dim v_M))) (mk_lane__2 Jnn_I16 lane_3_72))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_I16 (mk_dim v_M)) (mk_vrelop__0 Jnn_I16 M_0 (vrelop_Jnn_N_GE v_sx)) v128_1 v128_2 v128"
	| fun_vrelop__case_24 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_308 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_308)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_308 :: lane_underscore). ((proj_lane__0 lane_1_308) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_230 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_230)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_230 :: lane_underscore). ((proj_lane__0 lane_2_230) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_308 :: lane_underscore) (lane_2_230 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (feq_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_308)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_230))))))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 ((size (valtype_Fnn Fnn_F32)) \<noteq> None) \<Longrightarrow>
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F32))))) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (\<lambda> (lane_3_74 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_74))))) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_309 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_309)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_309 :: lane_underscore). ((proj_lane__0 lane_1_309) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_231 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_231)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_231 :: lane_underscore). ((proj_lane__0 lane_2_231) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_309 :: lane_underscore) (lane_2_231 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (feq_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_309)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_231))))))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_3_75 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_75)))))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_EQ) v128_1 v128_2 v128"
	| fun_vrelop__case_25 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_311 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_311)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_311 :: lane_underscore). ((proj_lane__0 lane_1_311) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_233 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_233)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_233 :: lane_underscore). ((proj_lane__0 lane_2_233) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_311 :: lane_underscore) (lane_2_233 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (feq_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_311)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_233))))))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 ((size (valtype_Fnn Fnn_F64)) \<noteq> None) \<Longrightarrow>
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F64))))) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (\<lambda> (lane_3_77 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_77))))) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_312 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_312)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_312 :: lane_underscore). ((proj_lane__0 lane_1_312) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_234 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_234)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_234 :: lane_underscore). ((proj_lane__0 lane_2_234) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_312 :: lane_underscore) (lane_2_234 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (feq_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_312)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_234))))))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_3_78 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_78)))))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_EQ) v128_1 v128_2 v128"
	| fun_vrelop__case_26 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_314 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_314)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_314 :: lane_underscore). ((proj_lane__0 lane_1_314) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_236 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_236)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_236 :: lane_underscore). ((proj_lane__0 lane_2_236) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_314 :: lane_underscore) (lane_2_236 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fne_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_314)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_236))))))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 ((size (valtype_Fnn Fnn_F32)) \<noteq> None) \<Longrightarrow>
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F32))))) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (\<lambda> (lane_3_80 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_80))))) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_315 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_315)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_315 :: lane_underscore). ((proj_lane__0 lane_1_315) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_237 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_237)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_237 :: lane_underscore). ((proj_lane__0 lane_2_237) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_315 :: lane_underscore) (lane_2_237 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (fne_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_315)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_237))))))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_3_81 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_81)))))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_NE) v128_1 v128_2 v128"
	| fun_vrelop__case_27 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_317 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_317)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_317 :: lane_underscore). ((proj_lane__0 lane_1_317) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_239 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_239)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_239 :: lane_underscore). ((proj_lane__0 lane_2_239) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_317 :: lane_underscore) (lane_2_239 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fne_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_317)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_239))))))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 ((size (valtype_Fnn Fnn_F64)) \<noteq> None) \<Longrightarrow>
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F64))))) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (\<lambda> (lane_3_83 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_83))))) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_318 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_318)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_318 :: lane_underscore). ((proj_lane__0 lane_1_318) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_240 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_240)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_240 :: lane_underscore). ((proj_lane__0 lane_2_240) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_318 :: lane_underscore) (lane_2_240 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (fne_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_318)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_240))))))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_3_84 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_84)))))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_NE) v128_1 v128_2 v128"
	| fun_vrelop__case_28 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_320 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_320)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_320 :: lane_underscore). ((proj_lane__0 lane_1_320) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_242 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_242)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_242 :: lane_underscore). ((proj_lane__0 lane_2_242) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_320 :: lane_underscore) (lane_2_242 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (flt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_320)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_242))))))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 ((size (valtype_Fnn Fnn_F32)) \<noteq> None) \<Longrightarrow>
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F32))))) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (\<lambda> (lane_3_86 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_86))))) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_321 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_321)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_321 :: lane_underscore). ((proj_lane__0 lane_1_321) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_243 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_243)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_243 :: lane_underscore). ((proj_lane__0 lane_2_243) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_321 :: lane_underscore) (lane_2_243 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (flt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_321)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_243))))))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_3_87 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_87)))))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_LT) v128_1 v128_2 v128"
	| fun_vrelop__case_29 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_323 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_323)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_323 :: lane_underscore). ((proj_lane__0 lane_1_323) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_245 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_245)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_245 :: lane_underscore). ((proj_lane__0 lane_2_245) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_323 :: lane_underscore) (lane_2_245 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (flt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_323)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_245))))))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 ((size (valtype_Fnn Fnn_F64)) \<noteq> None) \<Longrightarrow>
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F64))))) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (\<lambda> (lane_3_89 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_89))))) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_324 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_324)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_324 :: lane_underscore). ((proj_lane__0 lane_1_324) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_246 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_246)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_246 :: lane_underscore). ((proj_lane__0 lane_2_246) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_324 :: lane_underscore) (lane_2_246 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (flt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_324)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_246))))))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_3_90 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_90)))))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_LT) v128_1 v128_2 v128"
	| fun_vrelop__case_30 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_326 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_326)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_326 :: lane_underscore). ((proj_lane__0 lane_1_326) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_248 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_248)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_248 :: lane_underscore). ((proj_lane__0 lane_2_248) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_326 :: lane_underscore) (lane_2_248 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fgt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_326)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_248))))))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 ((size (valtype_Fnn Fnn_F32)) \<noteq> None) \<Longrightarrow>
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F32))))) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (\<lambda> (lane_3_92 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_92))))) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_327 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_327)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_327 :: lane_underscore). ((proj_lane__0 lane_1_327) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_249 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_249)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_249 :: lane_underscore). ((proj_lane__0 lane_2_249) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_327 :: lane_underscore) (lane_2_249 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (fgt_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_327)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_249))))))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_3_93 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_93)))))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_GT) v128_1 v128_2 v128"
	| fun_vrelop__case_31 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_329 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_329)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_329 :: lane_underscore). ((proj_lane__0 lane_1_329) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_251 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_251)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_251 :: lane_underscore). ((proj_lane__0 lane_2_251) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_329 :: lane_underscore) (lane_2_251 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fgt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_329)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_251))))))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 ((size (valtype_Fnn Fnn_F64)) \<noteq> None) \<Longrightarrow>
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F64))))) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (\<lambda> (lane_3_95 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_95))))) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_330 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_330)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_330 :: lane_underscore). ((proj_lane__0 lane_1_330) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_252 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_252)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_252 :: lane_underscore). ((proj_lane__0 lane_2_252) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_330 :: lane_underscore) (lane_2_252 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (fgt_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_330)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_252))))))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_3_96 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_96)))))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_GT) v128_1 v128_2 v128"
	| fun_vrelop__case_32 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_332 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_332)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_332 :: lane_underscore). ((proj_lane__0 lane_1_332) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_254 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_254)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_254 :: lane_underscore). ((proj_lane__0 lane_2_254) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_332 :: lane_underscore) (lane_2_254 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fle_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_332)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_254))))))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 ((size (valtype_Fnn Fnn_F32)) \<noteq> None) \<Longrightarrow>
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F32))))) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (\<lambda> (lane_3_98 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_98))))) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_333 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_333)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_333 :: lane_underscore). ((proj_lane__0 lane_1_333) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_255 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_255)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_255 :: lane_underscore). ((proj_lane__0 lane_2_255) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_333 :: lane_underscore) (lane_2_255 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (fle_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_333)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_255))))))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_3_99 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_99)))))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_LE) v128_1 v128_2 v128"
	| fun_vrelop__case_33 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_335 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_335)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_335 :: lane_underscore). ((proj_lane__0 lane_1_335) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_257 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_257)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_257 :: lane_underscore). ((proj_lane__0 lane_2_257) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_335 :: lane_underscore) (lane_2_257 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fle_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_335)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_257))))))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 ((size (valtype_Fnn Fnn_F64)) \<noteq> None) \<Longrightarrow>
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F64))))) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (\<lambda> (lane_3_101 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_101))))) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_336 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_336)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_336 :: lane_underscore). ((proj_lane__0 lane_1_336) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_258 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_258)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_258 :: lane_underscore). ((proj_lane__0 lane_2_258) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_336 :: lane_underscore) (lane_2_258 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (fle_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_336)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_258))))))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_3_102 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_102)))))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_LE) v128_1 v128_2 v128"
	| fun_vrelop__case_34 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F32) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_338 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_338)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_338 :: lane_underscore). ((proj_lane__0 lane_1_338) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_260 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_260)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_260 :: lane_underscore). ((proj_lane__0 lane_2_260) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_338 :: lane_underscore) (lane_2_260 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F32)) S (mk_uN (proj_uN_0 (fge_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_338)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_260))))))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 ((size (valtype_Fnn Fnn_F32)) \<noteq> None) \<Longrightarrow>
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F32))))) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (\<lambda> (lane_3_104 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_104))))) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F32) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_339 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_339)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_339 :: lane_underscore). ((proj_lane__0 lane_1_339) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_261 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_261)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_261 :: lane_underscore). ((proj_lane__0 lane_2_261) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_339 :: lane_underscore) (lane_2_261 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (fge_underscore (sizenn (numtype_Fnn Fnn_F32)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_339)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_261))))))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_3_105 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_105)))))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_F32 (mk_dim v_M)) (mk_vrelop__1 Fnn_F32 M_0 vrelop_Fnn_N_GE) v128_1 v128_2 v128"
	| fun_vrelop__case_35 :
		"(lane_1_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_1)) \<Longrightarrow>
		 (lane_2_lst = (lanes_underscore (X (lanetype_Fnn Fnn_F64) (mk_dim v_M)) v128_2)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_341 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_341)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_341 :: lane_underscore). ((proj_lane__0 lane_1_341) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_263 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_263)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_263 :: lane_underscore). ((proj_lane__0 lane_2_263) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 (lane_3_lst = (list_zipWith (\<lambda> (lane_1_341 :: lane_underscore) (lane_2_263 :: lane_underscore). (extend__underscore (Suc 0) (sizenn (numtype_Fnn Fnn_F64)) S (mk_uN (proj_uN_0 (fge_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_341)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_263))))))))))) lane_1_lst lane_2_lst)) \<Longrightarrow>
		 ((size (valtype_Fnn Fnn_F64)) \<noteq> None) \<Longrightarrow>
		 ((isize v_Inn) = (the ((size (valtype_Fnn Fnn_F64))))) \<Longrightarrow>
		 (v128 = (inv_lanes_underscore (X (lanetype_Inn v_Inn) (mk_dim v_M)) (map (\<lambda> (lane_3_107 :: iN). (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_107))))) lane_3_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Fnn Fnn_F64) (mk_dim v_M))) \<Longrightarrow>
		 ((length lane_1_lst) = (length lane_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (lane_1_342 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_1_342)))) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_1_342 :: lane_underscore). ((proj_lane__0 lane_1_342) \<noteq> None)) lane_1_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_264 :: lane_underscore). ((proj_num__1 (the ((proj_lane__0 lane_2_264)))) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all (\<lambda> (lane_2_264 :: lane_underscore). ((proj_lane__0 lane_2_264) \<noteq> None)) lane_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (lane_1_342 :: lane_underscore) (lane_2_264 :: lane_underscore). (wf_uN 1 (mk_uN (proj_uN_0 (fge_underscore (sizenn (numtype_Fnn Fnn_F64)) (the ((proj_num__1 (the ((proj_lane__0 lane_1_342)))))) (the ((proj_num__1 (the ((proj_lane__0 lane_2_264))))))))))) lane_1_lst lane_2_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn v_Inn) (mk_dim v_M))) \<Longrightarrow>
		 list_all (\<lambda> (lane_3_108 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn v_Inn) (mk_dim v_M))) (mk_lane__0 (numtype_Inn v_Inn) (mk_num__0 v_Inn (mk_uN (proj_uN_0 lane_3_108)))))) lane_3_lst \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vrelop_underscore (X lanetype_F64 (mk_dim v_M)) (mk_vrelop__1 Fnn_F64 M_0 vrelop_Fnn_N_GE) v128_1 v128_2 v128"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:381.6-381.14 *)
lemma vrelop__is_wf :
	"(fun_vrelop_underscore v_shape v_vrelop_underscore v_vec_underscore vec__0 var_0) \<Longrightarrow>
	 (wf_shape v_shape) \<Longrightarrow>
	 (wf_vrelop_underscore v_shape v_vrelop_underscore) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (wf_uN 128 vec__0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN 128 ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I8_mkdim_X_I8 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I8_mkdim_X_I8 M_1 (mk_dim M_2) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I8 iN_1) = 
			 (let iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1) in 
			 [(mk_lane__2 Jnn_I8 iN_2)])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I8_mkdim_X_I64 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I8_mkdim_X_I64 M_1 (mk_dim M_2) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I8 iN_1) = 
			 (let iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1) in 
			 [(mk_lane__2 Jnn_I64 iN_2)])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I8_mkdim_X_I32 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I8_mkdim_X_I32 M_1 (mk_dim M_2) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I8 iN_1) = 
			 (let iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1) in 
			 [(mk_lane__2 Jnn_I32 iN_2)])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I8_mkdim_X_I16 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I8_mkdim_X_I16 M_1 (mk_dim M_2) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I8 iN_1) = 
			 (let iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1) in 
			 [(mk_lane__2 Jnn_I16 iN_2)])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I8_mkdim_X_F64 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I8_mkdim_X_F64 M_1 (mk_dim M_2) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I8 iN_1) = 
			 (let fN_2 = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1) in 
			 [(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I8_mkdim_X_F32 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I8_mkdim_X_F32 M_1 (mk_dim M_2) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I8 iN_1) = 
			 (let fN_2 = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I8)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1) in 
			 [(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I8_mkdim_X :: "nat \<Rightarrow> lanetype \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I8_mkdim_X mkdim_argument_0_0 lanetype_I8 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I8_mkdim_X_I8 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I8_mkdim_X mkdim_argument_0_0 lanetype_I64 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I8_mkdim_X_I64 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I8_mkdim_X mkdim_argument_0_0 lanetype_I32 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I8_mkdim_X_I32 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I8_mkdim_X mkdim_argument_0_0 lanetype_I16 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I8_mkdim_X_I16 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I8_mkdim_X mkdim_argument_0_0 lanetype_F64 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I8_mkdim_X_F64 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I8_mkdim_X mkdim_argument_0_0 lanetype_F32 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I8_mkdim_X_F32 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I8_mkdim :: "nat \<Rightarrow> shape \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I8_mkdim mkdim_argument_0_0 (X constructor_parameter_0 constructor_parameter_1) v_vcvtop v_lane_underscore = (vcvtop___X_I8_mkdim_X mkdim_argument_0_0 constructor_parameter_0 constructor_parameter_1 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I8 :: "dim \<Rightarrow> shape \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I8 (mk_dim constructor_parameter_0) shape_2 v_vcvtop v_lane_underscore = (vcvtop___X_I8_mkdim constructor_parameter_0 shape_2 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I64_mkdim_X_I8 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I64_mkdim_X_I8 M_1 (mk_dim M_2) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I64 iN_1) = 
			 (let iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1) in 
			 [(mk_lane__2 Jnn_I8 iN_2)])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I64_mkdim_X_I64 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I64_mkdim_X_I64 M_1 (mk_dim M_2) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I64 iN_1) = 
			 (let iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1) in 
			 [(mk_lane__2 Jnn_I64 iN_2)])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I64_mkdim_X_I32 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I64_mkdim_X_I32 M_1 (mk_dim M_2) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I64 iN_1) = 
			 (let iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1) in 
			 [(mk_lane__2 Jnn_I32 iN_2)])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I64_mkdim_X_I16 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I64_mkdim_X_I16 M_1 (mk_dim M_2) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I64 iN_1) = 
			 (let iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1) in 
			 [(mk_lane__2 Jnn_I16 iN_2)])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I64_mkdim_X_F64 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I64_mkdim_X_F64 M_1 (mk_dim M_2) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I64 iN_1) = 
			 (let fN_2 = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1) in 
			 [(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I64_mkdim_X_F32 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I64_mkdim_X_F32 M_1 (mk_dim M_2) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I64 iN_1) = 
			 (let fN_2 = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1) in 
			 [(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I64_mkdim_X :: "nat \<Rightarrow> lanetype \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I64_mkdim_X mkdim_argument_0_0 lanetype_I8 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I64_mkdim_X_I8 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I64_mkdim_X mkdim_argument_0_0 lanetype_I64 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I64_mkdim_X_I64 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I64_mkdim_X mkdim_argument_0_0 lanetype_I32 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I64_mkdim_X_I32 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I64_mkdim_X mkdim_argument_0_0 lanetype_I16 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I64_mkdim_X_I16 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I64_mkdim_X mkdim_argument_0_0 lanetype_F64 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I64_mkdim_X_F64 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I64_mkdim_X mkdim_argument_0_0 lanetype_F32 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I64_mkdim_X_F32 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I64_mkdim :: "nat \<Rightarrow> shape \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I64_mkdim mkdim_argument_0_0 (X constructor_parameter_0 constructor_parameter_1) v_vcvtop v_lane_underscore = (vcvtop___X_I64_mkdim_X mkdim_argument_0_0 constructor_parameter_0 constructor_parameter_1 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I64 :: "dim \<Rightarrow> shape \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I64 (mk_dim constructor_parameter_0) shape_2 v_vcvtop v_lane_underscore = (vcvtop___X_I64_mkdim constructor_parameter_0 shape_2 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I32_mkdim_X_I8 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I32_mkdim_X_I8 M_1 (mk_dim M_2) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I32 iN_1) = 
			 (let iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1) in 
			 [(mk_lane__2 Jnn_I8 iN_2)])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I32_mkdim_X_I64 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I32_mkdim_X_I64 M_1 (mk_dim M_2) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I32 iN_1) = 
			 (let iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1) in 
			 [(mk_lane__2 Jnn_I64 iN_2)])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I32_mkdim_X_I32 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I32_mkdim_X_I32 M_1 (mk_dim M_2) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I32 iN_1) = 
			 (let iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1) in 
			 [(mk_lane__2 Jnn_I32 iN_2)])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I32_mkdim_X_I16 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I32_mkdim_X_I16 M_1 (mk_dim M_2) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I32 iN_1) = 
			 (let iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1) in 
			 [(mk_lane__2 Jnn_I16 iN_2)])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I32_mkdim_X_F64 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I32_mkdim_X_F64 M_1 (mk_dim M_2) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I32 iN_1) = 
			 (let fN_2 = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1) in 
			 [(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I32_mkdim_X_F32 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I32_mkdim_X_F32 M_1 (mk_dim M_2) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I32 iN_1) = 
			 (let fN_2 = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1) in 
			 [(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I32_mkdim_X :: "nat \<Rightarrow> lanetype \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I32_mkdim_X mkdim_argument_0_0 lanetype_I8 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I32_mkdim_X_I8 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I32_mkdim_X mkdim_argument_0_0 lanetype_I64 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I32_mkdim_X_I64 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I32_mkdim_X mkdim_argument_0_0 lanetype_I32 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I32_mkdim_X_I32 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I32_mkdim_X mkdim_argument_0_0 lanetype_I16 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I32_mkdim_X_I16 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I32_mkdim_X mkdim_argument_0_0 lanetype_F64 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I32_mkdim_X_F64 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I32_mkdim_X mkdim_argument_0_0 lanetype_F32 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I32_mkdim_X_F32 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I32_mkdim :: "nat \<Rightarrow> shape \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I32_mkdim mkdim_argument_0_0 (X constructor_parameter_0 constructor_parameter_1) v_vcvtop v_lane_underscore = (vcvtop___X_I32_mkdim_X mkdim_argument_0_0 constructor_parameter_0 constructor_parameter_1 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I32 :: "dim \<Rightarrow> shape \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I32 (mk_dim constructor_parameter_0) shape_2 v_vcvtop v_lane_underscore = (vcvtop___X_I32_mkdim constructor_parameter_0 shape_2 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I16_mkdim_X_I8 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I16_mkdim_X_I8 M_1 (mk_dim M_2) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I16 iN_1) = 
			 (let iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I8)) v_sx iN_1) in 
			 [(mk_lane__2 Jnn_I8 iN_2)])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I16_mkdim_X_I64 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I16_mkdim_X_I64 M_1 (mk_dim M_2) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I16 iN_1) = 
			 (let iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I64)) v_sx iN_1) in 
			 [(mk_lane__2 Jnn_I64 iN_2)])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I16_mkdim_X_I32 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I16_mkdim_X_I32 M_1 (mk_dim M_2) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I16 iN_1) = 
			 (let iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I32)) v_sx iN_1) in 
			 [(mk_lane__2 Jnn_I32 iN_2)])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I16_mkdim_X_I16 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I16_mkdim_X_I16 M_1 (mk_dim M_2) (vcvtop_EXTEND v_half v_sx) (mk_lane__2 Jnn_I16 iN_1) = 
			 (let iN_2 = (extend__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Jnn Jnn_I16)) v_sx iN_1) in 
			 [(mk_lane__2 Jnn_I16 iN_2)])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I16_mkdim_X_F64 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I16_mkdim_X_F64 M_1 (mk_dim M_2) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I16 iN_1) = 
			 (let fN_2 = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Fnn Fnn_F64)) v_sx iN_1) in 
			 [(mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2))])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I16_mkdim_X_F32 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I16_mkdim_X_F32 M_1 (mk_dim M_2) (vcvtop_CONVERT half_opt v_sx) (mk_lane__2 Jnn_I16 iN_1) = 
			 (let fN_2 = (convert__underscore (lsizenn1 (lanetype_Jnn Jnn_I16)) (lsizenn2 (lanetype_Fnn Fnn_F32)) v_sx iN_1) in 
			 [(mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2))])"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I16_mkdim_X :: "nat \<Rightarrow> lanetype \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I16_mkdim_X mkdim_argument_0_0 lanetype_I8 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I16_mkdim_X_I8 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I16_mkdim_X mkdim_argument_0_0 lanetype_I64 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I16_mkdim_X_I64 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I16_mkdim_X mkdim_argument_0_0 lanetype_I32 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I16_mkdim_X_I32 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I16_mkdim_X mkdim_argument_0_0 lanetype_I16 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I16_mkdim_X_I16 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I16_mkdim_X mkdim_argument_0_0 lanetype_F64 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I16_mkdim_X_F64 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_I16_mkdim_X mkdim_argument_0_0 lanetype_F32 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_I16_mkdim_X_F32 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I16_mkdim :: "nat \<Rightarrow> shape \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I16_mkdim mkdim_argument_0_0 (X constructor_parameter_0 constructor_parameter_1) v_vcvtop v_lane_underscore = (vcvtop___X_I16_mkdim_X mkdim_argument_0_0 constructor_parameter_0 constructor_parameter_1 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_I16 :: "dim \<Rightarrow> shape \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_I16 (mk_dim constructor_parameter_0) shape_2 v_vcvtop v_lane_underscore = (vcvtop___X_I16_mkdim constructor_parameter_0 shape_2 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F64_mkdim_X_I64_mkdim_TRUNCSAT :: "nat \<Rightarrow> nat \<Rightarrow> sx \<Rightarrow> (zero option) \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F64_mkdim_X_I64_mkdim_TRUNCSAT M_1 M_2 v_sx zero_opt (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) = 
			 (let iN_2_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Inn Inn_I64)) v_sx fN_1) in 
			 (list_underscore  (map_option (\<lambda> (iN_2_8 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_2_8))) iN_2_opt)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F64_mkdim_X_I64_mkdim :: "nat \<Rightarrow> nat \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F64_mkdim_X_I64_mkdim mkdim_argument_0_0 mkdim_argument_1_0 (vcvtop_TRUNC_SAT constructor_parameter_0 constructor_parameter_1) v_lane_underscore = (vcvtop___X_F64_mkdim_X_I64_mkdim_TRUNCSAT mkdim_argument_0_0 mkdim_argument_1_0 constructor_parameter_0 constructor_parameter_1 v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F64_mkdim_X_I64 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F64_mkdim_X_I64 mkdim_argument_0_0 (mk_dim constructor_parameter_0) v_vcvtop v_lane_underscore = (vcvtop___X_F64_mkdim_X_I64_mkdim mkdim_argument_0_0 constructor_parameter_0 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F64_mkdim_X_I32_mkdim_TRUNCSAT :: "nat \<Rightarrow> nat \<Rightarrow> sx \<Rightarrow> (zero option) \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F64_mkdim_X_I32_mkdim_TRUNCSAT M_1 M_2 v_sx zero_opt (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) = 
			 (let iN_2_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Inn Inn_I32)) v_sx fN_1) in 
			 (list_underscore  (map_option (\<lambda> (iN_2_6 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_2_6))) iN_2_opt)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F64_mkdim_X_I32_mkdim :: "nat \<Rightarrow> nat \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F64_mkdim_X_I32_mkdim mkdim_argument_0_0 mkdim_argument_1_0 (vcvtop_TRUNC_SAT constructor_parameter_0 constructor_parameter_1) v_lane_underscore = (vcvtop___X_F64_mkdim_X_I32_mkdim_TRUNCSAT mkdim_argument_0_0 mkdim_argument_1_0 constructor_parameter_0 constructor_parameter_1 v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F64_mkdim_X_I32 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F64_mkdim_X_I32 mkdim_argument_0_0 (mk_dim constructor_parameter_0) v_vcvtop v_lane_underscore = (vcvtop___X_F64_mkdim_X_I32_mkdim mkdim_argument_0_0 constructor_parameter_0 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F64_mkdim_X_F64_mkdim_PROMOTELOW :: "nat \<Rightarrow> nat \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F64_mkdim_X_F64_mkdim_PROMOTELOW M_1 M_2 (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) = 
			 (let fN_2_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1) in 
			 (map (\<lambda> (fN_2_16 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_16))) fN_2_lst))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F64_mkdim_X_F64_mkdim_DEMOTE :: "nat \<Rightarrow> nat \<Rightarrow> zero \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F64_mkdim_X_F64_mkdim_DEMOTE M_1 M_2 ZERO (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) = 
			 (let fN_2_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1) in 
			 (map (\<lambda> (fN_2_8 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_8))) fN_2_lst))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F64_mkdim_X_F64_mkdim :: "nat \<Rightarrow> nat \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F64_mkdim_X_F64_mkdim mkdim_argument_0_0 mkdim_argument_1_0 PROMOTELOW v_lane_underscore = (vcvtop___X_F64_mkdim_X_F64_mkdim_PROMOTELOW mkdim_argument_0_0 mkdim_argument_1_0 v_lane_underscore)"
		| "vcvtop___X_F64_mkdim_X_F64_mkdim mkdim_argument_0_0 mkdim_argument_1_0 (vcvtop_DEMOTE constructor_parameter_0) v_lane_underscore = (vcvtop___X_F64_mkdim_X_F64_mkdim_DEMOTE mkdim_argument_0_0 mkdim_argument_1_0 constructor_parameter_0 v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F64_mkdim_X_F64 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F64_mkdim_X_F64 mkdim_argument_0_0 (mk_dim constructor_parameter_0) v_vcvtop v_lane_underscore = (vcvtop___X_F64_mkdim_X_F64_mkdim mkdim_argument_0_0 constructor_parameter_0 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F64_mkdim_X_F32_mkdim_PROMOTELOW :: "nat \<Rightarrow> nat \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F64_mkdim_X_F32_mkdim_PROMOTELOW M_1 M_2 (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) = 
			 (let fN_2_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1) in 
			 (map (\<lambda> (fN_2_14 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_14))) fN_2_lst))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F64_mkdim_X_F32_mkdim_DEMOTE :: "nat \<Rightarrow> nat \<Rightarrow> zero \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F64_mkdim_X_F32_mkdim_DEMOTE M_1 M_2 ZERO (mk_lane__0 F64 (mk_num__1 Fnn_F64 fN_1)) = 
			 (let fN_2_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F64)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1) in 
			 (map (\<lambda> (fN_2_6 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_6))) fN_2_lst))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F64_mkdim_X_F32_mkdim :: "nat \<Rightarrow> nat \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F64_mkdim_X_F32_mkdim mkdim_argument_0_0 mkdim_argument_1_0 PROMOTELOW v_lane_underscore = (vcvtop___X_F64_mkdim_X_F32_mkdim_PROMOTELOW mkdim_argument_0_0 mkdim_argument_1_0 v_lane_underscore)"
		| "vcvtop___X_F64_mkdim_X_F32_mkdim mkdim_argument_0_0 mkdim_argument_1_0 (vcvtop_DEMOTE constructor_parameter_0) v_lane_underscore = (vcvtop___X_F64_mkdim_X_F32_mkdim_DEMOTE mkdim_argument_0_0 mkdim_argument_1_0 constructor_parameter_0 v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F64_mkdim_X_F32 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F64_mkdim_X_F32 mkdim_argument_0_0 (mk_dim constructor_parameter_0) v_vcvtop v_lane_underscore = (vcvtop___X_F64_mkdim_X_F32_mkdim mkdim_argument_0_0 constructor_parameter_0 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F64_mkdim_X :: "nat \<Rightarrow> lanetype \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F64_mkdim_X mkdim_argument_0_0 lanetype_I64 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_F64_mkdim_X_I64 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_F64_mkdim_X mkdim_argument_0_0 lanetype_I32 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_F64_mkdim_X_I32 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_F64_mkdim_X mkdim_argument_0_0 lanetype_F64 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_F64_mkdim_X_F64 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_F64_mkdim_X mkdim_argument_0_0 lanetype_F32 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_F64_mkdim_X_F32 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F64_mkdim :: "nat \<Rightarrow> shape \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F64_mkdim mkdim_argument_0_0 (X constructor_parameter_0 constructor_parameter_1) v_vcvtop v_lane_underscore = (vcvtop___X_F64_mkdim_X mkdim_argument_0_0 constructor_parameter_0 constructor_parameter_1 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F64 :: "dim \<Rightarrow> shape \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F64 (mk_dim constructor_parameter_0) shape_2 v_vcvtop v_lane_underscore = (vcvtop___X_F64_mkdim constructor_parameter_0 shape_2 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F32_mkdim_X_I64_mkdim_TRUNCSAT :: "nat \<Rightarrow> nat \<Rightarrow> sx \<Rightarrow> (zero option) \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F32_mkdim_X_I64_mkdim_TRUNCSAT M_1 M_2 v_sx zero_opt (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) = 
			 (let iN_2_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Inn Inn_I64)) v_sx fN_1) in 
			 (list_underscore  (map_option (\<lambda> (iN_2_4 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 iN_2_4))) iN_2_opt)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F32_mkdim_X_I64_mkdim :: "nat \<Rightarrow> nat \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F32_mkdim_X_I64_mkdim mkdim_argument_0_0 mkdim_argument_1_0 (vcvtop_TRUNC_SAT constructor_parameter_0 constructor_parameter_1) v_lane_underscore = (vcvtop___X_F32_mkdim_X_I64_mkdim_TRUNCSAT mkdim_argument_0_0 mkdim_argument_1_0 constructor_parameter_0 constructor_parameter_1 v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F32_mkdim_X_I64 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F32_mkdim_X_I64 mkdim_argument_0_0 (mk_dim constructor_parameter_0) v_vcvtop v_lane_underscore = (vcvtop___X_F32_mkdim_X_I64_mkdim mkdim_argument_0_0 constructor_parameter_0 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F32_mkdim_X_I32_mkdim_TRUNCSAT :: "nat \<Rightarrow> nat \<Rightarrow> sx \<Rightarrow> (zero option) \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F32_mkdim_X_I32_mkdim_TRUNCSAT M_1 M_2 v_sx zero_opt (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) = 
			 (let iN_2_opt = (trunc_sat__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Inn Inn_I32)) v_sx fN_1) in 
			 (list_underscore  (map_option (\<lambda> (iN_2_2 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 iN_2_2))) iN_2_opt)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F32_mkdim_X_I32_mkdim :: "nat \<Rightarrow> nat \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F32_mkdim_X_I32_mkdim mkdim_argument_0_0 mkdim_argument_1_0 (vcvtop_TRUNC_SAT constructor_parameter_0 constructor_parameter_1) v_lane_underscore = (vcvtop___X_F32_mkdim_X_I32_mkdim_TRUNCSAT mkdim_argument_0_0 mkdim_argument_1_0 constructor_parameter_0 constructor_parameter_1 v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F32_mkdim_X_I32 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F32_mkdim_X_I32 mkdim_argument_0_0 (mk_dim constructor_parameter_0) v_vcvtop v_lane_underscore = (vcvtop___X_F32_mkdim_X_I32_mkdim mkdim_argument_0_0 constructor_parameter_0 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F32_mkdim_X_F64_mkdim_PROMOTELOW :: "nat \<Rightarrow> nat \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F32_mkdim_X_F64_mkdim_PROMOTELOW M_1 M_2 (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) = 
			 (let fN_2_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1) in 
			 (map (\<lambda> (fN_2_12 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_12))) fN_2_lst))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F32_mkdim_X_F64_mkdim_DEMOTE :: "nat \<Rightarrow> nat \<Rightarrow> zero \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F32_mkdim_X_F64_mkdim_DEMOTE M_1 M_2 ZERO (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) = 
			 (let fN_2_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F64)) fN_1) in 
			 (map (\<lambda> (fN_2_4 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F64) (mk_num__1 Fnn_F64 fN_2_4))) fN_2_lst))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F32_mkdim_X_F64_mkdim :: "nat \<Rightarrow> nat \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F32_mkdim_X_F64_mkdim mkdim_argument_0_0 mkdim_argument_1_0 PROMOTELOW v_lane_underscore = (vcvtop___X_F32_mkdim_X_F64_mkdim_PROMOTELOW mkdim_argument_0_0 mkdim_argument_1_0 v_lane_underscore)"
		| "vcvtop___X_F32_mkdim_X_F64_mkdim mkdim_argument_0_0 mkdim_argument_1_0 (vcvtop_DEMOTE constructor_parameter_0) v_lane_underscore = (vcvtop___X_F32_mkdim_X_F64_mkdim_DEMOTE mkdim_argument_0_0 mkdim_argument_1_0 constructor_parameter_0 v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F32_mkdim_X_F64 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F32_mkdim_X_F64 mkdim_argument_0_0 (mk_dim constructor_parameter_0) v_vcvtop v_lane_underscore = (vcvtop___X_F32_mkdim_X_F64_mkdim mkdim_argument_0_0 constructor_parameter_0 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F32_mkdim_X_F32_mkdim_PROMOTELOW :: "nat \<Rightarrow> nat \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F32_mkdim_X_F32_mkdim_PROMOTELOW M_1 M_2 (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) = 
			 (let fN_2_lst = (promote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1) in 
			 (map (\<lambda> (fN_2_10 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_10))) fN_2_lst))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F32_mkdim_X_F32_mkdim_DEMOTE :: "nat \<Rightarrow> nat \<Rightarrow> zero \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F32_mkdim_X_F32_mkdim_DEMOTE M_1 M_2 ZERO (mk_lane__0 F32 (mk_num__1 Fnn_F32 fN_1)) = 
			 (let fN_2_lst = (demote__underscore (lsizenn1 (lanetype_Fnn Fnn_F32)) (lsizenn2 (lanetype_Fnn Fnn_F32)) fN_1) in 
			 (map (\<lambda> (fN_2_2 :: fN). (mk_lane__0 (numtype_Fnn Fnn_F32) (mk_num__1 Fnn_F32 fN_2_2))) fN_2_lst))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F32_mkdim_X_F32_mkdim :: "nat \<Rightarrow> nat \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F32_mkdim_X_F32_mkdim mkdim_argument_0_0 mkdim_argument_1_0 PROMOTELOW v_lane_underscore = (vcvtop___X_F32_mkdim_X_F32_mkdim_PROMOTELOW mkdim_argument_0_0 mkdim_argument_1_0 v_lane_underscore)"
		| "vcvtop___X_F32_mkdim_X_F32_mkdim mkdim_argument_0_0 mkdim_argument_1_0 (vcvtop_DEMOTE constructor_parameter_0) v_lane_underscore = (vcvtop___X_F32_mkdim_X_F32_mkdim_DEMOTE mkdim_argument_0_0 mkdim_argument_1_0 constructor_parameter_0 v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F32_mkdim_X_F32 :: "nat \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F32_mkdim_X_F32 mkdim_argument_0_0 (mk_dim constructor_parameter_0) v_vcvtop v_lane_underscore = (vcvtop___X_F32_mkdim_X_F32_mkdim mkdim_argument_0_0 constructor_parameter_0 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F32_mkdim_X :: "nat \<Rightarrow> lanetype \<Rightarrow> dim \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F32_mkdim_X mkdim_argument_0_0 lanetype_I64 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_F32_mkdim_X_I64 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_F32_mkdim_X mkdim_argument_0_0 lanetype_I32 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_F32_mkdim_X_I32 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_F32_mkdim_X mkdim_argument_0_0 lanetype_F64 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_F32_mkdim_X_F64 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
		| "vcvtop___X_F32_mkdim_X mkdim_argument_0_0 lanetype_F32 X_argument_1_1 v_vcvtop v_lane_underscore = (vcvtop___X_F32_mkdim_X_F32 mkdim_argument_0_0 X_argument_1_1 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F32_mkdim :: "nat \<Rightarrow> shape \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F32_mkdim mkdim_argument_0_0 (X constructor_parameter_0 constructor_parameter_1) v_vcvtop v_lane_underscore = (vcvtop___X_F32_mkdim_X mkdim_argument_0_0 constructor_parameter_0 constructor_parameter_1 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X_F32 :: "dim \<Rightarrow> shape \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X_F32 (mk_dim constructor_parameter_0) shape_2 v_vcvtop v_lane_underscore = (vcvtop___X_F32_mkdim constructor_parameter_0 shape_2 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop___X :: "lanetype \<Rightarrow> dim \<Rightarrow> shape \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop___X lanetype_I8 X_argument_0_1 shape_2 v_vcvtop v_lane_underscore = (vcvtop___X_I8 X_argument_0_1 shape_2 v_vcvtop v_lane_underscore)"
		| "vcvtop___X lanetype_I64 X_argument_0_1 shape_2 v_vcvtop v_lane_underscore = (vcvtop___X_I64 X_argument_0_1 shape_2 v_vcvtop v_lane_underscore)"
		| "vcvtop___X lanetype_I32 X_argument_0_1 shape_2 v_vcvtop v_lane_underscore = (vcvtop___X_I32 X_argument_0_1 shape_2 v_vcvtop v_lane_underscore)"
		| "vcvtop___X lanetype_I16 X_argument_0_1 shape_2 v_vcvtop v_lane_underscore = (vcvtop___X_I16 X_argument_0_1 shape_2 v_vcvtop v_lane_underscore)"
		| "vcvtop___X lanetype_F64 X_argument_0_1 shape_2 v_vcvtop v_lane_underscore = (vcvtop___X_F64 X_argument_0_1 shape_2 v_vcvtop v_lane_underscore)"
		| "vcvtop___X lanetype_F32 X_argument_0_1 shape_2 v_vcvtop v_lane_underscore = (vcvtop___X_F32 X_argument_0_1 shape_2 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 *)
function (sequential, domintros) vcvtop__underscore :: "shape \<Rightarrow> shape \<Rightarrow> vcvtop \<Rightarrow> lane_underscore \<Rightarrow> (lane_underscore list)" where
		  "vcvtop__underscore (X constructor_parameter_0 constructor_parameter_1) shape_2 v_vcvtop v_lane_underscore = (vcvtop___X constructor_parameter_0 constructor_parameter_1 shape_2 v_vcvtop v_lane_underscore)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.6-383.15 *)
lemma vcvtop___is_wf :
	"(wf_shape shape_1) \<Longrightarrow>
	 (wf_shape shape_2) \<Longrightarrow>
	 (wf_lane_underscore (fun_lanetype shape_1) v_lane_underscore) \<Longrightarrow>
	 (ret_val_lst = (vcvtop__underscore shape_1 shape_2 v_vcvtop v_lane_underscore)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: lane_underscore). (wf_lane_underscore (fun_lanetype shape_2) ret_val)) ret_val_lst"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:583.6-583.17 *)
inductive fun_vextunop__underscore :: "ishape \<Rightarrow> ishape \<Rightarrow> vextunop_underscore \<Rightarrow> vec_underscore \<Rightarrow> vec_underscore \<Rightarrow> bool" where
	  fun_vextunop___case_0 :
		"(ci_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) \<Longrightarrow>
		 list_all (\<lambda> (ci_2 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2)))) \<noteq> None)) ci_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2 :: lane_underscore). ((proj_lane__0 ci_2) \<noteq> None)) ci_lst \<Longrightarrow>
		 ((concat_underscore  (list_zipWith (\<lambda> (cj_1_1 :: iN) (cj_2_1 :: iN). [cj_1_1, cj_2_1]) cj_1_lst cj_2_lst)) = (map (\<lambda> (ci_2 :: lane_underscore). (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2)))))))) ci_lst)) \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (\<lambda> (cj_1_2 :: iN) (cj_2_2 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_2 cj_2_2)))) cj_1_lst cj_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) \<Longrightarrow>
		 ((length cj_1_lst) = (length cj_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (cj_1_3 :: iN) (cj_2_3 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_3 cj_2_3))))) cj_1_lst cj_2_lst \<Longrightarrow>
		 (M_1 = M_1_0) \<Longrightarrow>
		 fun_vextunop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextunop__0 Jnn_I32 M_1_0 (EXTADD_PAIRWISE v_sx)) c_1 c"
	| fun_vextunop___case_1 :
		"(ci_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) \<Longrightarrow>
		 list_all (\<lambda> (ci_4 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_4)))) \<noteq> None)) ci_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_4 :: lane_underscore). ((proj_lane__0 ci_4) \<noteq> None)) ci_lst \<Longrightarrow>
		 ((concat_underscore  (list_zipWith (\<lambda> (cj_1_4 :: iN) (cj_2_4 :: iN). [cj_1_4, cj_2_4]) cj_1_lst cj_2_lst)) = (map (\<lambda> (ci_4 :: lane_underscore). (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_4)))))))) ci_lst)) \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (\<lambda> (cj_1_5 :: iN) (cj_2_5 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_5 cj_2_5)))) cj_1_lst cj_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) \<Longrightarrow>
		 ((length cj_1_lst) = (length cj_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (cj_1_6 :: iN) (cj_2_6 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_6 cj_2_6))))) cj_1_lst cj_2_lst \<Longrightarrow>
		 (M_1 = M_1_0) \<Longrightarrow>
		 fun_vextunop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextunop__0 Jnn_I32 M_1_0 (EXTADD_PAIRWISE v_sx)) c_1 c"
	| fun_vextunop___case_2 :
		"(ci_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) \<Longrightarrow>
		 list_all (\<lambda> (ci_6 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_6)))) \<noteq> None)) ci_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_6 :: lane_underscore). ((proj_lane__0 ci_6) \<noteq> None)) ci_lst \<Longrightarrow>
		 ((concat_underscore  (list_zipWith (\<lambda> (cj_1_7 :: iN) (cj_2_7 :: iN). [cj_1_7, cj_2_7]) cj_1_lst cj_2_lst)) = (map (\<lambda> (ci_6 :: lane_underscore). (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_6)))))))) ci_lst)) \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (\<lambda> (cj_1_8 :: iN) (cj_2_8 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_8 cj_2_8)))) cj_1_lst cj_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) \<Longrightarrow>
		 ((length cj_1_lst) = (length cj_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (cj_1_9 :: iN) (cj_2_9 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_9 cj_2_9))))) cj_1_lst cj_2_lst \<Longrightarrow>
		 (M_1 = M_1_0) \<Longrightarrow>
		 fun_vextunop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextunop__0 Jnn_I64 M_1_0 (EXTADD_PAIRWISE v_sx)) c_1 c"
	| fun_vextunop___case_3 :
		"(ci_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) \<Longrightarrow>
		 list_all (\<lambda> (ci_8 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_8)))) \<noteq> None)) ci_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_8 :: lane_underscore). ((proj_lane__0 ci_8) \<noteq> None)) ci_lst \<Longrightarrow>
		 ((concat_underscore  (list_zipWith (\<lambda> (cj_1_10 :: iN) (cj_2_10 :: iN). [cj_1_10, cj_2_10]) cj_1_lst cj_2_lst)) = (map (\<lambda> (ci_8 :: lane_underscore). (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_8)))))))) ci_lst)) \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (\<lambda> (cj_1_11 :: iN) (cj_2_11 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_11 cj_2_11)))) cj_1_lst cj_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) \<Longrightarrow>
		 ((length cj_1_lst) = (length cj_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (cj_1_12 :: iN) (cj_2_12 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_12 cj_2_12))))) cj_1_lst cj_2_lst \<Longrightarrow>
		 (M_1 = M_1_0) \<Longrightarrow>
		 fun_vextunop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextunop__0 Jnn_I64 M_1_0 (EXTADD_PAIRWISE v_sx)) c_1 c"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:583.6-583.17 *)
lemma vextunop___is_wf :
	"(fun_vextunop__underscore ishape_1 ishape_2 v_vextunop_underscore v_vec_underscore var_0) \<Longrightarrow>
	 (wf_ishape ishape_1) \<Longrightarrow>
	 (wf_ishape ishape_2) \<Longrightarrow>
	 (wf_vextunop_underscore ishape_1 v_vextunop_underscore) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN 128 ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:585.6-585.18 *)
inductive fun_vextbinop__underscore :: "ishape \<Rightarrow> ishape \<Rightarrow> vextbinop_underscore \<Rightarrow> vec_underscore \<Rightarrow> vec_underscore \<Rightarrow> vec_underscore \<Rightarrow> bool" where
	  fun_vextbinop___case_0 :
		"(ci_1_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) \<Longrightarrow>
		 (ci_2_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) \<Longrightarrow>
		 list_all (\<lambda> (ci_1_2 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_2)))) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_1_2 :: lane_underscore). ((proj_lane__0 ci_1_2) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_2 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_2)))) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_2 :: lane_underscore). ((proj_lane__0 ci_2_2) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (\<lambda> (ci_1_2 :: lane_underscore) (ci_2_2 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_2))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_2))))))))))) ci_1_lst ci_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) \<Longrightarrow>
		 ((length ci_1_lst) = (length ci_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (ci_1_3 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_3)))) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_1_3 :: lane_underscore). ((proj_lane__0 ci_1_3) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_3 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_3)))) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_3 :: lane_underscore). ((proj_lane__0 ci_2_3) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (ci_1_3 :: lane_underscore) (ci_2_3 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_3))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_3)))))))))))) ci_1_lst ci_2_lst \<Longrightarrow>
		 (M_1 = M_1_0) \<Longrightarrow>
		 fun_vextbinop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1_0 (EXTMUL v_half v_sx)) c_1 c_2 c"
	| fun_vextbinop___case_1 :
		"(ci_1_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) \<Longrightarrow>
		 (ci_2_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) \<Longrightarrow>
		 list_all (\<lambda> (ci_1_5 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_5)))) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_1_5 :: lane_underscore). ((proj_lane__0 ci_1_5) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_5 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_5)))) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_5 :: lane_underscore). ((proj_lane__0 ci_2_5) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (\<lambda> (ci_1_5 :: lane_underscore) (ci_2_5 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_5))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_5))))))))))) ci_1_lst ci_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) \<Longrightarrow>
		 ((length ci_1_lst) = (length ci_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (ci_1_6 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_6)))) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_1_6 :: lane_underscore). ((proj_lane__0 ci_1_6) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_6 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_6)))) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_6 :: lane_underscore). ((proj_lane__0 ci_2_6) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (ci_1_6 :: lane_underscore) (ci_2_6 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_6))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_6)))))))))))) ci_1_lst ci_2_lst \<Longrightarrow>
		 (M_1 = M_1_0) \<Longrightarrow>
		 fun_vextbinop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1_0 (EXTMUL v_half v_sx)) c_1 c_2 c"
	| fun_vextbinop___case_2 :
		"(ci_1_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) \<Longrightarrow>
		 (ci_2_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) \<Longrightarrow>
		 list_all (\<lambda> (ci_1_8 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_8)))) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_1_8 :: lane_underscore). ((proj_lane__0 ci_1_8) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_8 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_8)))) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_8 :: lane_underscore). ((proj_lane__0 ci_2_8) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (\<lambda> (ci_1_8 :: lane_underscore) (ci_2_8 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_8))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_8))))))))))) ci_1_lst ci_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) \<Longrightarrow>
		 ((length ci_1_lst) = (length ci_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (ci_1_9 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_9)))) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_1_9 :: lane_underscore). ((proj_lane__0 ci_1_9) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_9 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_9)))) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_9 :: lane_underscore). ((proj_lane__0 ci_2_9) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (ci_1_9 :: lane_underscore) (ci_2_9 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_9))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_9)))))))))))) ci_1_lst ci_2_lst \<Longrightarrow>
		 (M_1 = M_1_0) \<Longrightarrow>
		 fun_vextbinop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1_0 (EXTMUL v_half v_sx)) c_1 c_2 c"
	| fun_vextbinop___case_3 :
		"(ci_1_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) \<Longrightarrow>
		 (ci_2_lst = (list_slice (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) \<Longrightarrow>
		 list_all (\<lambda> (ci_1_11 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_11)))) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_1_11 :: lane_underscore). ((proj_lane__0 ci_1_11) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_11 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_11)))) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_11 :: lane_underscore). ((proj_lane__0 ci_2_11) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (\<lambda> (ci_1_11 :: lane_underscore) (ci_2_11 :: lane_underscore). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_11))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_11))))))))))) ci_1_lst ci_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) \<Longrightarrow>
		 ((length ci_1_lst) = (length ci_2_lst)) \<Longrightarrow>
		 list_all (\<lambda> (ci_1_12 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_12)))) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_1_12 :: lane_underscore). ((proj_lane__0 ci_1_12) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_12 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_12)))) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_12 :: lane_underscore). ((proj_lane__0 ci_2_12) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 list_all2 (\<lambda> (ci_1_12 :: lane_underscore) (ci_2_12 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_1_12))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) v_sx (the ((proj_num__0 (the ((proj_lane__0 ci_2_12)))))))))))) ci_1_lst ci_2_lst \<Longrightarrow>
		 (M_1 = M_1_0) \<Longrightarrow>
		 fun_vextbinop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1_0 (EXTMUL v_half v_sx)) c_1 c_2 c"
	| fun_vextbinop___case_4 :
		"(ci_1_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) \<Longrightarrow>
		 (ci_2_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2)) \<Longrightarrow>
		 list_all (\<lambda> (ci_1_14 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_14)))) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_1_14 :: lane_underscore). ((proj_lane__0 ci_1_14) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_14 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_14)))) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_14 :: lane_underscore). ((proj_lane__0 ci_2_14) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 ((concat_underscore  (list_zipWith (\<lambda> (cj_1_13 :: iN) (cj_2_13 :: iN). [cj_1_13, cj_2_13]) cj_1_lst cj_2_lst)) = (list_zipWith (\<lambda> (ci_1_14 :: lane_underscore) (ci_2_14 :: lane_underscore). (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_14))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_14))))))))) ci_1_lst ci_2_lst)) \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (\<lambda> (cj_1_14 :: iN) (cj_2_14 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_14 cj_2_14)))) cj_1_lst cj_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) \<Longrightarrow>
		 ((length cj_1_lst) = (length cj_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (cj_1_15 :: iN) (cj_2_15 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_15 cj_2_15))))) cj_1_lst cj_2_lst \<Longrightarrow>
		 (M_1 = M_1_0) \<Longrightarrow>
		 fun_vextbinop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1_0 DOTS) c_1 c_2 c"
	| fun_vextbinop___case_5 :
		"(ci_1_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) \<Longrightarrow>
		 (ci_2_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2)) \<Longrightarrow>
		 list_all (\<lambda> (ci_1_16 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_16)))) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_1_16 :: lane_underscore). ((proj_lane__0 ci_1_16) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_16 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_16)))) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_16 :: lane_underscore). ((proj_lane__0 ci_2_16) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 ((concat_underscore  (list_zipWith (\<lambda> (cj_1_16 :: iN) (cj_2_16 :: iN). [cj_1_16, cj_2_16]) cj_1_lst cj_2_lst)) = (list_zipWith (\<lambda> (ci_1_16 :: lane_underscore) (ci_2_16 :: lane_underscore). (imul_underscore (lsizenn1 (lanetype_Inn Inn_I32)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_16))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I32)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_16))))))))) ci_1_lst ci_2_lst)) \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_1)) (list_zipWith (\<lambda> (cj_1_17 :: iN) (cj_2_17 :: iN). (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_17 cj_2_17)))) cj_1_lst cj_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_1))) \<Longrightarrow>
		 ((length cj_1_lst) = (length cj_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (cj_1_18 :: iN) (cj_2_18 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I32) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I32) (mk_num__0 Inn_I32 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I32)) cj_1_18 cj_2_18))))) cj_1_lst cj_2_lst \<Longrightarrow>
		 (M_1 = M_1_0) \<Longrightarrow>
		 fun_vextbinop__underscore (ishape_X Jnn_I32 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I32 M_1_0 DOTS) c_1 c_2 c"
	| fun_vextbinop___case_6 :
		"(ci_1_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_1)) \<Longrightarrow>
		 (ci_2_lst = (lanes_underscore (X (lanetype_Inn Inn_I32) (mk_dim M_2)) c_2)) \<Longrightarrow>
		 list_all (\<lambda> (ci_1_18 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_18)))) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_1_18 :: lane_underscore). ((proj_lane__0 ci_1_18) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_18 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_18)))) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_18 :: lane_underscore). ((proj_lane__0 ci_2_18) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 ((concat_underscore  (list_zipWith (\<lambda> (cj_1_19 :: iN) (cj_2_19 :: iN). [cj_1_19, cj_2_19]) cj_1_lst cj_2_lst)) = (list_zipWith (\<lambda> (ci_1_18 :: lane_underscore) (ci_2_18 :: lane_underscore). (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_18))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I32)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_18))))))))) ci_1_lst ci_2_lst)) \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (\<lambda> (cj_1_20 :: iN) (cj_2_20 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_20 cj_2_20)))) cj_1_lst cj_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I32) (mk_dim M_2))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) \<Longrightarrow>
		 ((length cj_1_lst) = (length cj_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (cj_1_21 :: iN) (cj_2_21 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_21 cj_2_21))))) cj_1_lst cj_2_lst \<Longrightarrow>
		 (M_1 = M_1_0) \<Longrightarrow>
		 fun_vextbinop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I32 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1_0 DOTS) c_1 c_2 c"
	| fun_vextbinop___case_7 :
		"(ci_1_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_1)) \<Longrightarrow>
		 (ci_2_lst = (lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_2)) c_2)) \<Longrightarrow>
		 list_all (\<lambda> (ci_1_20 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_1_20)))) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_1_20 :: lane_underscore). ((proj_lane__0 ci_1_20) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_20 :: lane_underscore). ((proj_num__0 (the ((proj_lane__0 ci_2_20)))) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2_20 :: lane_underscore). ((proj_lane__0 ci_2_20) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 ((concat_underscore  (list_zipWith (\<lambda> (cj_1_22 :: iN) (cj_2_22 :: iN). [cj_1_22, cj_2_22]) cj_1_lst cj_2_lst)) = (list_zipWith (\<lambda> (ci_1_20 :: lane_underscore) (ci_2_20 :: lane_underscore). (imul_underscore (lsizenn1 (lanetype_Inn Inn_I64)) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_1_20))))))) (extend__underscore (lsizenn2 (lanetype_Inn Inn_I64)) (lsizenn1 (lanetype_Inn Inn_I64)) S (the ((proj_num__0 (the ((proj_lane__0 ci_2_20))))))))) ci_1_lst ci_2_lst)) \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_Inn Inn_I64) (mk_dim M_1)) (list_zipWith (\<lambda> (cj_1_23 :: iN) (cj_2_23 :: iN). (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_23 cj_2_23)))) cj_1_lst cj_2_lst))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_2))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Inn Inn_I64) (mk_dim M_1))) \<Longrightarrow>
		 ((length cj_1_lst) = (length cj_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (cj_1_24 :: iN) (cj_2_24 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Inn Inn_I64) (mk_dim M_1))) (mk_lane__0 (numtype_Inn Inn_I64) (mk_num__0 Inn_I64 (iadd_underscore (lsizenn1 (lanetype_Inn Inn_I64)) cj_1_24 cj_2_24))))) cj_1_lst cj_2_lst \<Longrightarrow>
		 (M_1 = M_1_0) \<Longrightarrow>
		 fun_vextbinop__underscore (ishape_X Jnn_I64 (mk_dim M_1)) (ishape_X Jnn_I64 (mk_dim M_2)) (mk_vextbinop__0 Jnn_I64 M_1_0 DOTS) c_1 c_2 c"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:585.6-585.18 *)
lemma vextbinop___is_wf :
	"(fun_vextbinop__underscore ishape_1 ishape_2 v_vextbinop_underscore v_vec_underscore vec__0 var_0) \<Longrightarrow>
	 (wf_ishape ishape_1) \<Longrightarrow>
	 (wf_ishape ishape_2) \<Longrightarrow>
	 (wf_vextbinop_underscore ishape_1 v_vextbinop_underscore) \<Longrightarrow>
	 (wf_uN 128 v_vec_underscore) \<Longrightarrow>
	 (wf_uN 128 vec__0) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_uN 128 ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:608.6-608.16 *)
inductive fun_vshiftop_underscore :: "ishape \<Rightarrow> vshiftop_underscore \<Rightarrow> lane_underscore \<Rightarrow> u32 \<Rightarrow> lane_underscore \<Rightarrow> bool" where
	  fun_vshiftop__case_0 :
		"(v_Jnn = Jnn_1) \<Longrightarrow>
		 (v_Jnn = Jnn_0) \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vshiftop_underscore (ishape_X v_Jnn (mk_dim v_M)) (mk_vshiftop__0 Jnn_0 M_0 vshiftop_Jnn_N_SHL) (mk_lane__2 Jnn_1 lane) (mk_uN v_n) (mk_lane__2 v_Jnn (ishl_underscore (lsizenn (lanetype_Jnn v_Jnn)) lane (mk_uN v_n)))"
	| fun_vshiftop__case_1 :
		"(v_Jnn = Jnn_1) \<Longrightarrow>
		 (v_Jnn = Jnn_0) \<Longrightarrow>
		 (v_M = M_0) \<Longrightarrow>
		 fun_vshiftop_underscore (ishape_X v_Jnn (mk_dim v_M)) (mk_vshiftop__0 Jnn_0 M_0 (vshiftop_Jnn_N_SHR v_sx)) (mk_lane__2 Jnn_1 lane) (mk_uN v_n) (mk_lane__2 v_Jnn (ishr_underscore (lsizenn (lanetype_Jnn v_Jnn)) v_sx lane (mk_uN v_n)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:608.6-608.16 *)
lemma vshiftop__is_wf :
	"(fun_vshiftop_underscore v_ishape v_vshiftop_underscore v_lane_underscore v_u32 var_0) \<Longrightarrow>
	 (wf_ishape v_ishape) \<Longrightarrow>
	 (wf_vshiftop_underscore v_ishape v_vshiftop_underscore) \<Longrightarrow>
	 (wf_lane_underscore (fun_lanetype (shape_ishape v_ishape)) v_lane_underscore) \<Longrightarrow>
	 (wf_uN 32 v_u32) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_lane_underscore (fun_lanetype (shape_ishape v_ishape)) ret_val)"
sorry

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:5.1-5.39 *)
type_synonym addr = "nat"

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:6.1-6.53 *)
type_synonym funcaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:7.1-7.53 *)
type_synonym globaladdr = "addr"

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:8.1-8.51 *)
type_synonym tableaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:9.1-9.50 *)
type_synonym memaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:10.1-10.49 *)
type_synonym elemaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:11.1-11.49 *)
type_synonym dataaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:12.1-12.49 *)
type_synonym hostaddr = "addr"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:25.1-26.70 *)
datatype externaddr =
	  externaddr_FUNC "funcaddr"
	| externaddr_GLOBAL "globaladdr"
	| externaddr_TABLE "tableaddr"
	| externaddr_MEM "memaddr"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:37.1-38.62 *)
datatype num =
	  num_CONST "numtype" "num_underscore"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:37.8-37.11 *)
inductive wf_num :: "num \<Rightarrow> bool" where
	  num_case_0 :
		"(wf_num_underscore v_numtype var_0) \<Longrightarrow>
		 wf_num (num_CONST v_numtype var_0)"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:39.1-40.62 *)
datatype vec =
	  vec_VCONST "vectype" "vec_underscore"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:39.8-39.11 *)
inductive wf_vec :: "vec \<Rightarrow> bool" where
	  vec_case_0 :
		"((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
		 (wf_uN (the ((size (valtype_vectype v_vectype)))) var_0) \<Longrightarrow>
		 wf_vec (vec_VCONST v_vectype var_0)"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:41.1-42.71 *)
datatype ref =
	  ref_REF_NULL "reftype"
	| REF_FUNC_ADDR "funcaddr"
	| REF_HOST_ADDR "hostaddr"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:43.1-44.20 *)
datatype val =
	  val_CONST "numtype" "num_underscore"
	| val_VCONST "vectype" "vec_underscore"
	| val_REF_NULL "reftype"
	| val_REF_FUNC_ADDR "funcaddr"
	| val_REF_HOST_ADDR "hostaddr"

(* Auxiliary Definition at:  *)
function (sequential, domintros) val_ref :: "ref \<Rightarrow> val" where
		  "val_ref (ref_REF_NULL x0) = (val_REF_NULL x0)"
		| "val_ref (REF_FUNC_ADDR x0) = (val_REF_FUNC_ADDR x0)"
		| "val_ref (REF_HOST_ADDR x0) = (val_REF_HOST_ADDR x0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:43.8-43.11 *)
inductive wf_val :: "val \<Rightarrow> bool" where
	  val_case_0 :
		"(wf_num_underscore v_numtype var_0) \<Longrightarrow>
		 wf_val (val_CONST v_numtype var_0)"
	| val_case_1 :
		"((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
		 (wf_uN (the ((size (valtype_vectype v_vectype)))) var_0) \<Longrightarrow>
		 wf_val (val_VCONST v_vectype var_0)"
	| val_case_2 :
		"wf_val (val_REF_NULL v_reftype)"
	| val_case_3 :
		"wf_val (val_REF_FUNC_ADDR v_funcaddr)"
	| val_case_4 :
		"wf_val (val_REF_HOST_ADDR v_hostaddr)"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:46.1-47.22 *)
datatype result =
	  underscore_VALS "(val list)"
	| TRAP

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:46.8-46.14 *)
inductive wf_result :: "result \<Rightarrow> bool" where
	  result_case_0 :
		"list_all (\<lambda> (v_val :: val). (wf_val v_val)) val_lst \<Longrightarrow>
		 wf_result (underscore_VALS val_lst)"
	| result_case_1 :
		"wf_result TRAP"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:78.1-80.22 *)
record exportinst =
	NAME :: "name"
	ADDR :: "externaddr"

definition append_exportinst :: "exportinst \<Rightarrow> exportinst \<Rightarrow> exportinst" where
	"append_exportinst arg1 arg2 = \<lparr>
		NAME = NAME arg1,
		ADDR = ADDR arg1
	\<rparr>"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:78.8-78.18 *)
inductive wf_exportinst :: "exportinst \<Rightarrow> bool" where
	  exportinst_case_underscore :
		"(wf_name var_0) \<Longrightarrow>
		 wf_exportinst \<lparr> NAME = var_0, ADDR = var_1 \<rparr>"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:82.1-90.26 *)
record moduleinst =
	TYPES :: "(functype list)"
	FUNCS :: "(funcaddr list)"
	GLOBALS :: "(globaladdr list)"
	TABLES :: "(tableaddr list)"
	MEMS :: "(memaddr list)"
	ELEMS :: "(elemaddr list)"
	DATAS :: "(dataaddr list)"
	EXPORTS :: "(exportinst list)"

definition append_moduleinst :: "moduleinst \<Rightarrow> moduleinst \<Rightarrow> moduleinst" where
	"append_moduleinst arg1 arg2 = \<lparr>
		TYPES = TYPES arg1 @ TYPES arg2,
		FUNCS = FUNCS arg1 @ FUNCS arg2,
		GLOBALS = GLOBALS arg1 @ GLOBALS arg2,
		TABLES = TABLES arg1 @ TABLES arg2,
		MEMS = MEMS arg1 @ MEMS arg2,
		ELEMS = ELEMS arg1 @ ELEMS arg2,
		DATAS = DATAS arg1 @ DATAS arg2,
		EXPORTS = EXPORTS arg1 @ EXPORTS arg2
	\<rparr>"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:82.8-82.18 *)
inductive wf_moduleinst :: "moduleinst \<Rightarrow> bool" where
	  moduleinst_case_underscore :
		"list_all (\<lambda> (var_7 :: exportinst). (wf_exportinst var_7)) var_7_lst \<Longrightarrow>
		 wf_moduleinst \<lparr> TYPES = var_0_lst, FUNCS = var_1_lst, GLOBALS = var_2_lst, TABLES = var_3_lst, MEMS = var_4_lst, ELEMS = var_5_lst, DATAS = var_6_lst, EXPORTS = var_7_lst \<rparr>"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:60.1-63.16 *)
record funcinst =
	funcinst_TYPE :: "functype"
	funcinst_MODULE :: "moduleinst"
	CODE :: "func"

definition append_funcinst :: "funcinst \<Rightarrow> funcinst \<Rightarrow> funcinst" where
	"append_funcinst arg1 arg2 = \<lparr>
		funcinst_TYPE = funcinst_TYPE arg1,
		funcinst_MODULE = append_moduleinst (funcinst_MODULE arg1) (funcinst_MODULE arg2),
		CODE = CODE arg1
	\<rparr>"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:60.8-60.16 *)
inductive wf_funcinst :: "funcinst \<Rightarrow> bool" where
	  funcinst_case_underscore :
		"(wf_moduleinst var_1) \<Longrightarrow>
		 (wf_func var_2) \<Longrightarrow>
		 wf_funcinst \<lparr> funcinst_TYPE = var_0, funcinst_MODULE = var_1, CODE = var_2 \<rparr>"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:64.1-66.16 *)
record globalinst =
	globalinst_TYPE :: "globaltype"
	VALUE :: "val"

definition append_globalinst :: "globalinst \<Rightarrow> globalinst \<Rightarrow> globalinst" where
	"append_globalinst arg1 arg2 = \<lparr>
		globalinst_TYPE = globalinst_TYPE arg1,
		VALUE = VALUE arg1
	\<rparr>"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:64.8-64.18 *)
inductive wf_globalinst :: "globalinst \<Rightarrow> bool" where
	  globalinst_case_underscore :
		"(wf_val var_1) \<Longrightarrow>
		 wf_globalinst \<lparr> globalinst_TYPE = var_0, VALUE = var_1 \<rparr>"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:67.1-69.16 *)
record tableinst =
	tableinst_TYPE :: "tabletype"
	REFS :: "(ref list)"

definition append_tableinst :: "tableinst \<Rightarrow> tableinst \<Rightarrow> tableinst" where
	"append_tableinst arg1 arg2 = \<lparr>
		tableinst_TYPE = tableinst_TYPE arg1,
		REFS = REFS arg1 @ REFS arg2
	\<rparr>"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:67.8-67.17 *)
inductive wf_tableinst :: "tableinst \<Rightarrow> bool" where
	  tableinst_case_underscore :
		"(wf_tabletype var_0) \<Longrightarrow>
		 wf_tableinst \<lparr> tableinst_TYPE = var_0, REFS = var_1_lst \<rparr>"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:70.1-72.18 *)
record meminst =
	meminst_TYPE :: "memtype"
	BYTES :: "(byte list)"

definition append_meminst :: "meminst \<Rightarrow> meminst \<Rightarrow> meminst" where
	"append_meminst arg1 arg2 = \<lparr>
		meminst_TYPE = meminst_TYPE arg1,
		BYTES = BYTES arg1 @ BYTES arg2
	\<rparr>"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:70.8-70.15 *)
inductive wf_meminst :: "meminst \<Rightarrow> bool" where
	  meminst_case_underscore :
		"(wf_memtype var_0) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: byte). (wf_byte var_1)) var_1_lst \<Longrightarrow>
		 wf_meminst \<lparr> meminst_TYPE = var_0, BYTES = var_1_lst \<rparr>"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:73.1-75.16 *)
record eleminst =
	eleminst_TYPE :: "elemtype"
	eleminst_REFS :: "(ref list)"

definition append_eleminst :: "eleminst \<Rightarrow> eleminst \<Rightarrow> eleminst" where
	"append_eleminst arg1 arg2 = \<lparr>
		eleminst_TYPE = eleminst_TYPE arg1,
		eleminst_REFS = eleminst_REFS arg1 @ eleminst_REFS arg2
	\<rparr>"



(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:76.1-77.18 *)
record datainst =
	datainst_BYTES :: "(byte list)"

definition append_datainst :: "datainst \<Rightarrow> datainst \<Rightarrow> datainst" where
	"append_datainst arg1 arg2 = \<lparr>
		datainst_BYTES = datainst_BYTES arg1 @ datainst_BYTES arg2
	\<rparr>"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:76.8-76.16 *)
inductive wf_datainst :: "datainst \<Rightarrow> bool" where
	  datainst_case_underscore :
		"list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst \<Longrightarrow>
		 wf_datainst \<lparr> datainst_BYTES = var_0_lst \<rparr>"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:104.1-110.22 *)
record store =
	store_FUNCS :: "(funcinst list)"
	store_GLOBALS :: "(globalinst list)"
	store_TABLES :: "(tableinst list)"
	store_MEMS :: "(meminst list)"
	store_ELEMS :: "(eleminst list)"
	store_DATAS :: "(datainst list)"

definition append_store :: "store \<Rightarrow> store \<Rightarrow> store" where
	"append_store arg1 arg2 = \<lparr>
		store_FUNCS = store_FUNCS arg1 @ store_FUNCS arg2,
		store_GLOBALS = store_GLOBALS arg1 @ store_GLOBALS arg2,
		store_TABLES = store_TABLES arg1 @ store_TABLES arg2,
		store_MEMS = store_MEMS arg1 @ store_MEMS arg2,
		store_ELEMS = store_ELEMS arg1 @ store_ELEMS arg2,
		store_DATAS = store_DATAS arg1 @ store_DATAS arg2
	\<rparr>"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:104.8-104.13 *)
inductive wf_store :: "store \<Rightarrow> bool" where
	  store_case_underscore :
		"list_all (\<lambda> (var_0 :: funcinst). (wf_funcinst var_0)) var_0_lst \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: globalinst). (wf_globalinst var_1)) var_1_lst \<Longrightarrow>
		 list_all (\<lambda> (var_2 :: tableinst). (wf_tableinst var_2)) var_2_lst \<Longrightarrow>
		 list_all (\<lambda> (var_3 :: meminst). (wf_meminst var_3)) var_3_lst \<Longrightarrow>
		 list_all (\<lambda> (var_5 :: datainst). (wf_datainst var_5)) var_5_lst \<Longrightarrow>
		 wf_store \<lparr> store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst, store_MEMS = var_3_lst, store_ELEMS = var_4_lst, store_DATAS = var_5_lst \<rparr>"

(* Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:112.1-114.24 *)
record frame =
	LOCALS :: "(val list)"
	frame_MODULE :: "moduleinst"

definition append_frame :: "frame \<Rightarrow> frame \<Rightarrow> frame" where
	"append_frame arg1 arg2 = \<lparr>
		LOCALS = LOCALS arg1 @ LOCALS arg2,
		frame_MODULE = append_moduleinst (frame_MODULE arg1) (frame_MODULE arg2)
	\<rparr>"



(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:112.8-112.13 *)
inductive wf_frame :: "frame \<Rightarrow> bool" where
	  frame_case_underscore :
		"list_all (\<lambda> (var_0 :: val). (wf_val var_0)) var_0_lst \<Longrightarrow>
		 (wf_moduleinst var_1) \<Longrightarrow>
		 wf_frame \<lparr> LOCALS = var_0_lst, frame_MODULE = var_1 \<rparr>"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:116.1-116.47 *)
datatype state =
	  mk_state "store" "frame"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:116.8-116.13 *)
inductive wf_state :: "state \<Rightarrow> bool" where
	  state_case_0 :
		"(wf_store v_store) \<Longrightarrow>
		 (wf_frame v_frame) \<Longrightarrow>
		 wf_state (mk_state v_store v_frame)"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr_st7 =
	  admininstr_st7_TRAP
	| CALL_ADDR "funcaddr"
	| admininstr_st7_REF_HOST_ADDR "hostaddr"
	| admininstr_st7_REF_FUNC_ADDR "funcaddr"
	| admininstr_st7_DATA_DROP "dataidx"
	| admininstr_st7_MEMORY_INIT "dataidx"
	| admininstr_st7_MEMORY_COPY
	| admininstr_st7_MEMORY_FILL
	| admininstr_st7_MEMORY_GROW

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr_st6 =
	  admininstr_st6_MEMORY_SIZE
	| admininstr_st6_VSTORE_LANE "vectype" "sz" "memarg" "laneidx"
	| admininstr_st6_VSTORE "vectype" "memarg"
	| admininstr_st6_VLOAD_LANE "vectype" "sz" "memarg" "laneidx"
	| admininstr_st6_VLOAD "vectype" "(vloadop option)" "memarg"
	| admininstr_st6_STORE "numtype" "(sz option)" "memarg"
	| admininstr_st6_LOAD "numtype" "(loadop_underscore option)" "memarg"
	| admininstr_st6_ELEM_DROP "elemidx"
	| admininstr_st6_TABLE_INIT "tableidx" "elemidx"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr_st5 =
	  admininstr_st5_TABLE_COPY "tableidx" "tableidx"
	| admininstr_st5_TABLE_FILL "tableidx"
	| admininstr_st5_TABLE_GROW "tableidx"
	| admininstr_st5_TABLE_SIZE "tableidx"
	| admininstr_st5_TABLE_SET "tableidx"
	| admininstr_st5_TABLE_GET "tableidx"
	| admininstr_st5_GLOBAL_SET "globalidx"
	| admininstr_st5_GLOBAL_GET "globalidx"
	| admininstr_st5_LOCAL_TEE "localidx"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr_st4 =
	  admininstr_st4_LOCAL_SET "localidx"
	| admininstr_st4_LOCAL_GET "localidx"
	| admininstr_st4_REF_IS_NULL
	| admininstr_st4_REF_FUNC "funcidx"
	| admininstr_st4_REF_NULL "reftype"
	| admininstr_st4_VCVTOP "shape" "shape" "vcvtop"
	| admininstr_st4_VNARROW "ishape" "ishape" "sx"
	| admininstr_st4_VEXTBINOP "ishape" "ishape" "vextbinop_underscore"
	| admininstr_st4_VEXTUNOP "ishape" "ishape" "vextunop_underscore"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr_st3 =
	  admininstr_st3_VREPLACE_LANE "shape" "laneidx"
	| admininstr_st3_VEXTRACT_LANE "shape" "(sx option)" "laneidx"
	| admininstr_st3_VSPLAT "shape"
	| admininstr_st3_VSHUFFLE "ishape" "(laneidx list)"
	| admininstr_st3_VSWIZZLE "ishape"
	| admininstr_st3_VBITMASK "ishape"
	| admininstr_st3_VSHIFTOP "ishape" "vshiftop_underscore"
	| admininstr_st3_VRELOP "shape" "vrelop_underscore"
	| admininstr_st3_VTESTOP "shape" "vtestop_underscore"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr_st2 =
	  admininstr_st2_VBINOP "shape" "vbinop_underscore"
	| admininstr_st2_VUNOP "shape" "vunop_underscore"
	| admininstr_st2_VVTESTOP "vectype" "vvtestop"
	| admininstr_st2_VVTERNOP "vectype" "vvternop"
	| admininstr_st2_VVBINOP "vectype" "vvbinop"
	| admininstr_st2_VVUNOP "vectype" "vvunop"
	| admininstr_st2_VCONST "vectype" "vec_underscore"
	| admininstr_st2_EXTEND "numtype" "n"
	| admininstr_st2_CVTOP "numtype" "numtype" "cvtop__underscore"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr_st1 =
	  admininstr_st1_RELOP "numtype" "relop_underscore"
	| admininstr_st1_TESTOP "numtype" "testop_underscore"
	| admininstr_st1_BINOP "numtype" "binop_underscore"
	| admininstr_st1_UNOP "numtype" "unop_underscore"
	| admininstr_st1_CONST "numtype" "num_underscore"
	| admininstr_st1_RETURN
	| admininstr_st1_CALL_INDIRECT "tableidx" "typeidx"
	| admininstr_st1_CALL "funcidx"
	| admininstr_st1_BR_TABLE "(labelidx list)" "labelidx"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr_st0 =
	  admininstr_st0_BR_IF "labelidx"
	| admininstr_st0_BR "labelidx"
	| admininstr_st0_IFELSE "blocktype" "(instr list)" "(instr list)"
	| admininstr_st0_LOOP "blocktype" "(instr list)"
	| admininstr_st0_BLOCK "blocktype" "(instr list)"
	| admininstr_st0_SELECT "((valtype list) option)"
	| admininstr_st0_DROP
	| admininstr_st0_UNREACHABLE
	| admininstr_st0_NOP

(* Mutual Recursion at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
datatype admininstr =
	  admininstr_sc0 "admininstr_st0"
	| admininstr_sc1 "admininstr_st1"
	| admininstr_sc2 "admininstr_st2"
	| admininstr_sc3 "admininstr_st3"
	| admininstr_sc4 "admininstr_st4"
	| admininstr_sc5 "admininstr_st5"
	| admininstr_sc6 "admininstr_st6"
	| admininstr_sc7 "admininstr_st7"
	| admininstr_sc8 "admininstr_st8"

and

admininstr_st8 =
	  FRAME_underscore "n" "frame" "(admininstr list)"
	| LABEL_underscore "n" "(instr list)" "(admininstr list)"

(* Auxiliary Definition at:  *)
function (sequential, domintros) admininstr_instr :: "instr \<Rightarrow> admininstr" where
		  "admininstr_instr (instr_sc0 NOP) = (admininstr_sc0 admininstr_st0_NOP)"
		| "admininstr_instr (instr_sc0 UNREACHABLE) = (admininstr_sc0 admininstr_st0_UNREACHABLE)"
		| "admininstr_instr (instr_sc0 DROP) = (admininstr_sc0 admininstr_st0_DROP)"
		| "admininstr_instr (instr_sc0 (SELECT x0)) = (admininstr_sc0 (admininstr_st0_SELECT x0))"
		| "admininstr_instr (instr_sc7 (BLOCK x0 x1)) = (admininstr_sc0 (admininstr_st0_BLOCK x0 x1))"
		| "admininstr_instr (instr_sc7 (LOOP x0 x1)) = (admininstr_sc0 (admininstr_st0_LOOP x0 x1))"
		| "admininstr_instr (instr_sc7 (IFELSE x0 x1 x2)) = (admininstr_sc0 (admininstr_st0_IFELSE x0 x1 x2))"
		| "admininstr_instr (instr_sc0 (BR x0)) = (admininstr_sc0 (admininstr_st0_BR x0))"
		| "admininstr_instr (instr_sc0 (BR_IF x0)) = (admininstr_sc0 (admininstr_st0_BR_IF x0))"
		| "admininstr_instr (instr_sc0 (BR_TABLE x0 x1)) = (admininstr_sc1 (admininstr_st1_BR_TABLE x0 x1))"
		| "admininstr_instr (instr_sc0 (CALL x0)) = (admininstr_sc1 (admininstr_st1_CALL x0))"
		| "admininstr_instr (instr_sc0 (CALL_INDIRECT x0 x1)) = (admininstr_sc1 (admininstr_st1_CALL_INDIRECT x0 x1))"
		| "admininstr_instr (instr_sc1 RETURN) = (admininstr_sc1 admininstr_st1_RETURN)"
		| "admininstr_instr (instr_sc1 (res_CONST x0 x1)) = (admininstr_sc1 (admininstr_st1_CONST x0 x1))"
		| "admininstr_instr (instr_sc1 (UNOP x0 x1)) = (admininstr_sc1 (admininstr_st1_UNOP x0 x1))"
		| "admininstr_instr (instr_sc1 (BINOP x0 x1)) = (admininstr_sc1 (admininstr_st1_BINOP x0 x1))"
		| "admininstr_instr (instr_sc1 (TESTOP x0 x1)) = (admininstr_sc1 (admininstr_st1_TESTOP x0 x1))"
		| "admininstr_instr (instr_sc1 (RELOP x0 x1)) = (admininstr_sc1 (admininstr_st1_RELOP x0 x1))"
		| "admininstr_instr (instr_sc1 (CVTOP x0 x1 x2)) = (admininstr_sc2 (admininstr_st2_CVTOP x0 x1 x2))"
		| "admininstr_instr (instr_sc1 (instr_st1_EXTEND x0 x1)) = (admininstr_sc2 (admininstr_st2_EXTEND x0 x1))"
		| "admininstr_instr (instr_sc1 (VCONST x0 x1)) = (admininstr_sc2 (admininstr_st2_VCONST x0 x1))"
		| "admininstr_instr (instr_sc2 (VVUNOP x0 x1)) = (admininstr_sc2 (admininstr_st2_VVUNOP x0 x1))"
		| "admininstr_instr (instr_sc2 (VVBINOP x0 x1)) = (admininstr_sc2 (admininstr_st2_VVBINOP x0 x1))"
		| "admininstr_instr (instr_sc2 (VVTERNOP x0 x1)) = (admininstr_sc2 (admininstr_st2_VVTERNOP x0 x1))"
		| "admininstr_instr (instr_sc2 (VVTESTOP x0 x1)) = (admininstr_sc2 (admininstr_st2_VVTESTOP x0 x1))"
		| "admininstr_instr (instr_sc2 (VUNOP x0 x1)) = (admininstr_sc2 (admininstr_st2_VUNOP x0 x1))"
		| "admininstr_instr (instr_sc2 (VBINOP x0 x1)) = (admininstr_sc2 (admininstr_st2_VBINOP x0 x1))"
		| "admininstr_instr (instr_sc2 (VTESTOP x0 x1)) = (admininstr_sc3 (admininstr_st3_VTESTOP x0 x1))"
		| "admininstr_instr (instr_sc2 (VRELOP x0 x1)) = (admininstr_sc3 (admininstr_st3_VRELOP x0 x1))"
		| "admininstr_instr (instr_sc2 (VSHIFTOP x0 x1)) = (admininstr_sc3 (admininstr_st3_VSHIFTOP x0 x1))"
		| "admininstr_instr (instr_sc3 (VBITMASK x0)) = (admininstr_sc3 (admininstr_st3_VBITMASK x0))"
		| "admininstr_instr (instr_sc3 (VSWIZZLE x0)) = (admininstr_sc3 (admininstr_st3_VSWIZZLE x0))"
		| "admininstr_instr (instr_sc3 (VSHUFFLE x0 x1)) = (admininstr_sc3 (admininstr_st3_VSHUFFLE x0 x1))"
		| "admininstr_instr (instr_sc3 (VSPLAT x0)) = (admininstr_sc3 (admininstr_st3_VSPLAT x0))"
		| "admininstr_instr (instr_sc3 (VEXTRACT_LANE x0 x1 x2)) = (admininstr_sc3 (admininstr_st3_VEXTRACT_LANE x0 x1 x2))"
		| "admininstr_instr (instr_sc3 (VREPLACE_LANE x0 x1)) = (admininstr_sc3 (admininstr_st3_VREPLACE_LANE x0 x1))"
		| "admininstr_instr (instr_sc3 (VEXTUNOP x0 x1 x2)) = (admininstr_sc4 (admininstr_st4_VEXTUNOP x0 x1 x2))"
		| "admininstr_instr (instr_sc3 (VEXTBINOP x0 x1 x2)) = (admininstr_sc4 (admininstr_st4_VEXTBINOP x0 x1 x2))"
		| "admininstr_instr (instr_sc3 (VNARROW x0 x1 x2)) = (admininstr_sc4 (admininstr_st4_VNARROW x0 x1 x2))"
		| "admininstr_instr (instr_sc4 (VCVTOP x0 x1 x2)) = (admininstr_sc4 (admininstr_st4_VCVTOP x0 x1 x2))"
		| "admininstr_instr (instr_sc4 (REF_NULL x0)) = (admininstr_sc4 (admininstr_st4_REF_NULL x0))"
		| "admininstr_instr (instr_sc4 (REF_FUNC x0)) = (admininstr_sc4 (admininstr_st4_REF_FUNC x0))"
		| "admininstr_instr (instr_sc4 REF_IS_NULL) = (admininstr_sc4 admininstr_st4_REF_IS_NULL)"
		| "admininstr_instr (instr_sc4 (LOCAL_GET x0)) = (admininstr_sc4 (admininstr_st4_LOCAL_GET x0))"
		| "admininstr_instr (instr_sc4 (LOCAL_SET x0)) = (admininstr_sc4 (admininstr_st4_LOCAL_SET x0))"
		| "admininstr_instr (instr_sc4 (LOCAL_TEE x0)) = (admininstr_sc5 (admininstr_st5_LOCAL_TEE x0))"
		| "admininstr_instr (instr_sc4 (GLOBAL_GET x0)) = (admininstr_sc5 (admininstr_st5_GLOBAL_GET x0))"
		| "admininstr_instr (instr_sc4 (GLOBAL_SET x0)) = (admininstr_sc5 (admininstr_st5_GLOBAL_SET x0))"
		| "admininstr_instr (instr_sc5 (TABLE_GET x0)) = (admininstr_sc5 (admininstr_st5_TABLE_GET x0))"
		| "admininstr_instr (instr_sc5 (TABLE_SET x0)) = (admininstr_sc5 (admininstr_st5_TABLE_SET x0))"
		| "admininstr_instr (instr_sc5 (TABLE_SIZE x0)) = (admininstr_sc5 (admininstr_st5_TABLE_SIZE x0))"
		| "admininstr_instr (instr_sc5 (TABLE_GROW x0)) = (admininstr_sc5 (admininstr_st5_TABLE_GROW x0))"
		| "admininstr_instr (instr_sc5 (TABLE_FILL x0)) = (admininstr_sc5 (admininstr_st5_TABLE_FILL x0))"
		| "admininstr_instr (instr_sc5 (TABLE_COPY x0 x1)) = (admininstr_sc5 (admininstr_st5_TABLE_COPY x0 x1))"
		| "admininstr_instr (instr_sc5 (TABLE_INIT x0 x1)) = (admininstr_sc6 (admininstr_st6_TABLE_INIT x0 x1))"
		| "admininstr_instr (instr_sc5 (ELEM_DROP x0)) = (admininstr_sc6 (admininstr_st6_ELEM_DROP x0))"
		| "admininstr_instr (instr_sc5 (LOAD x0 x1 x2)) = (admininstr_sc6 (admininstr_st6_LOAD x0 x1 x2))"
		| "admininstr_instr (instr_sc6 (STORE x0 x1 x2)) = (admininstr_sc6 (admininstr_st6_STORE x0 x1 x2))"
		| "admininstr_instr (instr_sc6 (VLOAD x0 x1 x2)) = (admininstr_sc6 (admininstr_st6_VLOAD x0 x1 x2))"
		| "admininstr_instr (instr_sc6 (VLOAD_LANE x0 x1 x2 x3)) = (admininstr_sc6 (admininstr_st6_VLOAD_LANE x0 x1 x2 x3))"
		| "admininstr_instr (instr_sc6 (VSTORE x0 x1)) = (admininstr_sc6 (admininstr_st6_VSTORE x0 x1))"
		| "admininstr_instr (instr_sc6 (VSTORE_LANE x0 x1 x2 x3)) = (admininstr_sc6 (admininstr_st6_VSTORE_LANE x0 x1 x2 x3))"
		| "admininstr_instr (instr_sc6 MEMORY_SIZE) = (admininstr_sc6 admininstr_st6_MEMORY_SIZE)"
		| "admininstr_instr (instr_sc6 MEMORY_GROW) = (admininstr_sc7 admininstr_st7_MEMORY_GROW)"
		| "admininstr_instr (instr_sc6 MEMORY_FILL) = (admininstr_sc7 admininstr_st7_MEMORY_FILL)"
		| "admininstr_instr (instr_sc6 MEMORY_COPY) = (admininstr_sc7 admininstr_st7_MEMORY_COPY)"
		| "admininstr_instr (instr_sc7 (MEMORY_INIT x0)) = (admininstr_sc7 (admininstr_st7_MEMORY_INIT x0))"
		| "admininstr_instr (instr_sc7 (DATA_DROP x0)) = (admininstr_sc7 (admininstr_st7_DATA_DROP x0))"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential, domintros) admininstr_ref :: "ref \<Rightarrow> admininstr" where
		  "admininstr_ref (ref_REF_NULL x0) = (admininstr_sc4 (admininstr_st4_REF_NULL x0))"
		| "admininstr_ref (REF_FUNC_ADDR x0) = (admininstr_sc7 (admininstr_st7_REF_FUNC_ADDR x0))"
		| "admininstr_ref (REF_HOST_ADDR x0) = (admininstr_sc7 (admininstr_st7_REF_HOST_ADDR x0))"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential, domintros) admininstr_val :: "val \<Rightarrow> admininstr" where
		  "admininstr_val (val_CONST x0 x1) = (admininstr_sc1 (admininstr_st1_CONST x0 x1))"
		| "admininstr_val (val_VCONST x0 x1) = (admininstr_sc2 (admininstr_st2_VCONST x0 x1))"
		| "admininstr_val (val_REF_NULL x0) = (admininstr_sc4 (admininstr_st4_REF_NULL x0))"
		| "admininstr_val (val_REF_FUNC_ADDR x0) = (admininstr_sc7 (admininstr_st7_REF_FUNC_ADDR x0))"
		| "admininstr_val (val_REF_HOST_ADDR x0) = (admininstr_sc7 (admininstr_st7_REF_HOST_ADDR x0))"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 *)
inductive wf_admininstr :: "admininstr \<Rightarrow> bool" where
	  admininstr_case_0 :
		"wf_admininstr (admininstr_sc0 admininstr_st0_NOP)"
	| admininstr_case_1 :
		"wf_admininstr (admininstr_sc0 admininstr_st0_UNREACHABLE)"
	| admininstr_case_2 :
		"wf_admininstr (admininstr_sc0 admininstr_st0_DROP)"
	| admininstr_case_3 :
		"wf_admininstr (admininstr_sc0 (admininstr_st0_SELECT valtype_lst_opt))"
	| admininstr_case_4 :
		"(wf_blocktype v_blocktype) \<Longrightarrow>
		 list_all (\<lambda> (v_instr :: instr). (wf_instr v_instr)) instr_lst \<Longrightarrow>
		 wf_admininstr (admininstr_sc0 (admininstr_st0_BLOCK v_blocktype instr_lst))"
	| admininstr_case_5 :
		"(wf_blocktype v_blocktype) \<Longrightarrow>
		 list_all (\<lambda> (v_instr :: instr). (wf_instr v_instr)) instr_lst \<Longrightarrow>
		 wf_admininstr (admininstr_sc0 (admininstr_st0_LOOP v_blocktype instr_lst))"
	| admininstr_case_6 :
		"(wf_blocktype v_blocktype) \<Longrightarrow>
		 list_all (\<lambda> (v_instr :: instr). (wf_instr v_instr)) instr_lst \<Longrightarrow>
		 list_all (\<lambda> (instr_lst_0 :: instr). (wf_instr instr_lst_0)) instr_lst_0_lst \<Longrightarrow>
		 wf_admininstr (admininstr_sc0 (admininstr_st0_IFELSE v_blocktype instr_lst instr_lst_0_lst))"
	| admininstr_case_7 :
		"(wf_uN 32 v_labelidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc0 (admininstr_st0_BR v_labelidx))"
	| admininstr_case_8 :
		"(wf_uN 32 v_labelidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc0 (admininstr_st0_BR_IF v_labelidx))"
	| admininstr_case_9 :
		"list_all (\<lambda> (v_labelidx :: labelidx). (wf_uN 32 v_labelidx)) labelidx_lst \<Longrightarrow>
		 (wf_uN 32 v_labelidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc1 (admininstr_st1_BR_TABLE labelidx_lst v_labelidx))"
	| admininstr_case_10 :
		"(wf_uN 32 v_funcidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc1 (admininstr_st1_CALL v_funcidx))"
	| admininstr_case_11 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 (wf_uN 32 v_typeidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc1 (admininstr_st1_CALL_INDIRECT v_tableidx v_typeidx))"
	| admininstr_case_12 :
		"wf_admininstr (admininstr_sc1 admininstr_st1_RETURN)"
	| admininstr_case_13 :
		"(wf_num_underscore v_numtype var_0) \<Longrightarrow>
		 wf_admininstr (admininstr_sc1 (admininstr_st1_CONST v_numtype var_0))"
	| admininstr_case_14 :
		"(wf_unop_underscore v_numtype var_0) \<Longrightarrow>
		 wf_admininstr (admininstr_sc1 (admininstr_st1_UNOP v_numtype var_0))"
	| admininstr_case_15 :
		"(wf_binop_underscore v_numtype var_0) \<Longrightarrow>
		 wf_admininstr (admininstr_sc1 (admininstr_st1_BINOP v_numtype var_0))"
	| admininstr_case_16 :
		"(wf_testop_underscore v_numtype var_0) \<Longrightarrow>
		 wf_admininstr (admininstr_sc1 (admininstr_st1_TESTOP v_numtype var_0))"
	| admininstr_case_17 :
		"(wf_relop_underscore v_numtype var_0) \<Longrightarrow>
		 wf_admininstr (admininstr_sc1 (admininstr_st1_RELOP v_numtype var_0))"
	| admininstr_case_18 :
		"(wf_cvtop__underscore numtype_2 numtype_1 var_0) \<Longrightarrow>
		 (numtype_1 \<noteq> numtype_2) \<Longrightarrow>
		 wf_admininstr (admininstr_sc2 (admininstr_st2_CVTOP numtype_1 numtype_2 var_0))"
	| admininstr_case_19 :
		"wf_admininstr (admininstr_sc2 (admininstr_st2_EXTEND v_numtype v_n))"
	| admininstr_case_20 :
		"((size (valtype_vectype v_vectype)) \<noteq> None) \<Longrightarrow>
		 (wf_uN (the ((size (valtype_vectype v_vectype)))) var_0) \<Longrightarrow>
		 wf_admininstr (admininstr_sc2 (admininstr_st2_VCONST v_vectype var_0))"
	| admininstr_case_21 :
		"wf_admininstr (admininstr_sc2 (admininstr_st2_VVUNOP v_vectype v_vvunop))"
	| admininstr_case_22 :
		"wf_admininstr (admininstr_sc2 (admininstr_st2_VVBINOP v_vectype v_vvbinop))"
	| admininstr_case_23 :
		"wf_admininstr (admininstr_sc2 (admininstr_st2_VVTERNOP v_vectype v_vvternop))"
	| admininstr_case_24 :
		"wf_admininstr (admininstr_sc2 (admininstr_st2_VVTESTOP v_vectype v_vvtestop))"
	| admininstr_case_25 :
		"(wf_shape v_shape) \<Longrightarrow>
		 (wf_vunop_underscore v_shape var_0) \<Longrightarrow>
		 wf_admininstr (admininstr_sc2 (admininstr_st2_VUNOP v_shape var_0))"
	| admininstr_case_26 :
		"(wf_shape v_shape) \<Longrightarrow>
		 (wf_vbinop_underscore v_shape var_0) \<Longrightarrow>
		 wf_admininstr (admininstr_sc2 (admininstr_st2_VBINOP v_shape var_0))"
	| admininstr_case_27 :
		"(wf_shape v_shape) \<Longrightarrow>
		 (wf_vtestop_underscore v_shape var_0) \<Longrightarrow>
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VTESTOP v_shape var_0))"
	| admininstr_case_28 :
		"(wf_shape v_shape) \<Longrightarrow>
		 (wf_vrelop_underscore v_shape var_0) \<Longrightarrow>
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VRELOP v_shape var_0))"
	| admininstr_case_29 :
		"(wf_ishape v_ishape) \<Longrightarrow>
		 (wf_vshiftop_underscore v_ishape var_0) \<Longrightarrow>
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VSHIFTOP v_ishape var_0))"
	| admininstr_case_30 :
		"(wf_ishape v_ishape) \<Longrightarrow>
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VBITMASK v_ishape))"
	| admininstr_case_31 :
		"(wf_ishape v_ishape) \<Longrightarrow>
		 (v_ishape = (ishape_X Jnn_I8 (mk_dim 16))) \<Longrightarrow>
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VSWIZZLE v_ishape))"
	| admininstr_case_32 :
		"(wf_ishape v_ishape) \<Longrightarrow>
		 list_all (\<lambda> (v_laneidx :: laneidx). (wf_uN 8 v_laneidx)) laneidx_lst \<Longrightarrow>
		 ((v_ishape = (ishape_X Jnn_I8 (mk_dim 16))) \<and> ((length laneidx_lst) = 16)) \<Longrightarrow>
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VSHUFFLE v_ishape laneidx_lst))"
	| admininstr_case_33 :
		"(wf_shape v_shape) \<Longrightarrow>
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VSPLAT v_shape))"
	| admininstr_case_34 :
		"(wf_shape v_shape) \<Longrightarrow>
		 (wf_uN 8 v_laneidx) \<Longrightarrow>
		 (((fun_lanetype v_shape) = (lanetype_numtype v_numtype)) \<longleftrightarrow> (sx_opt = None)) \<Longrightarrow>
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VEXTRACT_LANE v_shape sx_opt v_laneidx))"
	| admininstr_case_35 :
		"(wf_shape v_shape) \<Longrightarrow>
		 (wf_uN 8 v_laneidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc3 (admininstr_st3_VREPLACE_LANE v_shape v_laneidx))"
	| admininstr_case_36 :
		"(wf_ishape ishape_1) \<Longrightarrow>
		 (wf_ishape ishape_2) \<Longrightarrow>
		 (wf_vextunop_underscore ishape_1 var_0) \<Longrightarrow>
		 ((lsize (fun_lanetype (shape_ishape ishape_1))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_2))))) \<Longrightarrow>
		 wf_admininstr (admininstr_sc4 (admininstr_st4_VEXTUNOP ishape_1 ishape_2 var_0))"
	| admininstr_case_37 :
		"(wf_ishape ishape_1) \<Longrightarrow>
		 (wf_ishape ishape_2) \<Longrightarrow>
		 (wf_vextbinop_underscore ishape_1 var_0) \<Longrightarrow>
		 ((lsize (fun_lanetype (shape_ishape ishape_1))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_2))))) \<Longrightarrow>
		 wf_admininstr (admininstr_sc4 (admininstr_st4_VEXTBINOP ishape_1 ishape_2 var_0))"
	| admininstr_case_38 :
		"(wf_ishape ishape_1) \<Longrightarrow>
		 (wf_ishape ishape_2) \<Longrightarrow>
		 (((lsize (fun_lanetype (shape_ishape ishape_2))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_1))))) \<and> ((2 * (lsize (fun_lanetype (shape_ishape ishape_1)))) \<le> 32)) \<Longrightarrow>
		 wf_admininstr (admininstr_sc4 (admininstr_st4_VNARROW ishape_1 ishape_2 v_sx))"
	| admininstr_case_39 :
		"(wf_shape v_shape) \<Longrightarrow>
		 (wf_shape shape_0) \<Longrightarrow>
		 wf_admininstr (admininstr_sc4 (admininstr_st4_VCVTOP v_shape shape_0 v_vcvtop))"
	| admininstr_case_40 :
		"wf_admininstr (admininstr_sc4 (admininstr_st4_REF_NULL v_reftype))"
	| admininstr_case_41 :
		"(wf_uN 32 v_funcidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc4 (admininstr_st4_REF_FUNC v_funcidx))"
	| admininstr_case_42 :
		"wf_admininstr (admininstr_sc4 admininstr_st4_REF_IS_NULL)"
	| admininstr_case_43 :
		"(wf_uN 32 v_localidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc4 (admininstr_st4_LOCAL_GET v_localidx))"
	| admininstr_case_44 :
		"(wf_uN 32 v_localidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc4 (admininstr_st4_LOCAL_SET v_localidx))"
	| admininstr_case_45 :
		"(wf_uN 32 v_localidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc5 (admininstr_st5_LOCAL_TEE v_localidx))"
	| admininstr_case_46 :
		"(wf_uN 32 v_globalidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc5 (admininstr_st5_GLOBAL_GET v_globalidx))"
	| admininstr_case_47 :
		"(wf_uN 32 v_globalidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc5 (admininstr_st5_GLOBAL_SET v_globalidx))"
	| admininstr_case_48 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc5 (admininstr_st5_TABLE_GET v_tableidx))"
	| admininstr_case_49 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc5 (admininstr_st5_TABLE_SET v_tableidx))"
	| admininstr_case_50 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc5 (admininstr_st5_TABLE_SIZE v_tableidx))"
	| admininstr_case_51 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc5 (admininstr_st5_TABLE_GROW v_tableidx))"
	| admininstr_case_52 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc5 (admininstr_st5_TABLE_FILL v_tableidx))"
	| admininstr_case_53 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 (wf_uN 32 tableidx_0) \<Longrightarrow>
		 wf_admininstr (admininstr_sc5 (admininstr_st5_TABLE_COPY v_tableidx tableidx_0))"
	| admininstr_case_54 :
		"(wf_uN 32 v_tableidx) \<Longrightarrow>
		 (wf_uN 32 v_elemidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc6 (admininstr_st6_TABLE_INIT v_tableidx v_elemidx))"
	| admininstr_case_55 :
		"(wf_uN 32 v_elemidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc6 (admininstr_st6_ELEM_DROP v_elemidx))"
	| admininstr_case_56 :
		"list_all (\<lambda> (var_0 :: loadop_underscore). (wf_loadop_underscore v_numtype var_0)) (option_to_list var_0_opt) \<Longrightarrow>
		 (wf_memarg v_memarg) \<Longrightarrow>
		 wf_admininstr (admininstr_sc6 (admininstr_st6_LOAD v_numtype var_0_opt v_memarg))"
	| admininstr_case_57 :
		"list_all (\<lambda> (v_sz :: sz). (wf_sz v_sz)) (option_to_list sz_opt) \<Longrightarrow>
		 (wf_memarg v_memarg) \<Longrightarrow>
		 ((Inn_opt = None) \<longleftrightarrow> (numtype_opt = None)) \<Longrightarrow>
		 ((Inn_opt = None) \<longleftrightarrow> (sz_opt = None)) \<Longrightarrow>
		 list_all3 (\<lambda> (v_Inn :: Inn) (v_numtype :: numtype) (v_sz :: sz). ((v_numtype = (numtype_Inn v_Inn)) \<and> ((proj_sz_0 v_sz) < (sizenn (numtype_Inn v_Inn))))) (option_to_list Inn_opt) (option_to_list numtype_opt) (option_to_list sz_opt) \<Longrightarrow>
		 wf_admininstr (admininstr_sc6 (admininstr_st6_STORE v_numtype sz_opt v_memarg))"
	| admininstr_case_58 :
		"(wf_memarg v_memarg) \<Longrightarrow>
		 wf_admininstr (admininstr_sc6 (admininstr_st6_VLOAD v_vectype vloadop_opt v_memarg))"
	| admininstr_case_59 :
		"(wf_sz v_sz) \<Longrightarrow>
		 (wf_memarg v_memarg) \<Longrightarrow>
		 (wf_uN 8 v_laneidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc6 (admininstr_st6_VLOAD_LANE v_vectype v_sz v_memarg v_laneidx))"
	| admininstr_case_60 :
		"(wf_memarg v_memarg) \<Longrightarrow>
		 wf_admininstr (admininstr_sc6 (admininstr_st6_VSTORE v_vectype v_memarg))"
	| admininstr_case_61 :
		"(wf_sz v_sz) \<Longrightarrow>
		 (wf_memarg v_memarg) \<Longrightarrow>
		 (wf_uN 8 v_laneidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc6 (admininstr_st6_VSTORE_LANE v_vectype v_sz v_memarg v_laneidx))"
	| admininstr_case_62 :
		"wf_admininstr (admininstr_sc6 admininstr_st6_MEMORY_SIZE)"
	| admininstr_case_63 :
		"wf_admininstr (admininstr_sc7 admininstr_st7_MEMORY_GROW)"
	| admininstr_case_64 :
		"wf_admininstr (admininstr_sc7 admininstr_st7_MEMORY_FILL)"
	| admininstr_case_65 :
		"wf_admininstr (admininstr_sc7 admininstr_st7_MEMORY_COPY)"
	| admininstr_case_66 :
		"(wf_uN 32 v_dataidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc7 (admininstr_st7_MEMORY_INIT v_dataidx))"
	| admininstr_case_67 :
		"(wf_uN 32 v_dataidx) \<Longrightarrow>
		 wf_admininstr (admininstr_sc7 (admininstr_st7_DATA_DROP v_dataidx))"
	| admininstr_case_68 :
		"wf_admininstr (admininstr_sc7 (admininstr_st7_REF_FUNC_ADDR v_funcaddr))"
	| admininstr_case_69 :
		"wf_admininstr (admininstr_sc7 (admininstr_st7_REF_HOST_ADDR v_hostaddr))"
	| admininstr_case_70 :
		"wf_admininstr (admininstr_sc7 (CALL_ADDR v_funcaddr))"
	| admininstr_case_71 :
		"list_all (\<lambda> (v_instr :: instr). (wf_instr v_instr)) instr_lst \<Longrightarrow>
		 list_all (\<lambda> (v_admininstr :: admininstr). (wf_admininstr v_admininstr)) admininstr_lst \<Longrightarrow>
		 wf_admininstr (admininstr_sc8 (LABEL_underscore v_n instr_lst admininstr_lst))"
	| admininstr_case_72 :
		"(wf_frame v_frame) \<Longrightarrow>
		 list_all (\<lambda> (v_admininstr :: admininstr). (wf_admininstr v_admininstr)) admininstr_lst \<Longrightarrow>
		 wf_admininstr (admininstr_sc8 (FRAME_underscore v_n v_frame admininstr_lst))"
	| admininstr_case_73 :
		"wf_admininstr (admininstr_sc7 admininstr_st7_TRAP)"

(* Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:117.1-117.62 *)
datatype config =
	  mk_config "state" "(admininstr list)"
	

(* Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:117.8-117.14 *)
inductive wf_config :: "config \<Rightarrow> bool" where
	  config_case_0 :
		"(wf_state v_state) \<Longrightarrow>
		 list_all (\<lambda> (v_admininstr :: admininstr). (wf_admininstr v_admininstr)) admininstr_lst \<Longrightarrow>
		 wf_config (mk_config v_state admininstr_lst)"

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:7.1-7.43 *)
function (sequential, domintros) default_underscore :: "valtype \<Rightarrow> (val option)" where
		  "default_underscore valtype_I32 = (Some (val_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0))))"
		| "default_underscore valtype_I64 = (Some (val_CONST I64 (mk_num__0 Inn_I64 (mk_uN 0))))"
		| "default_underscore valtype_F32 = (Some (val_CONST F32 (mk_num__1 Fnn_F32 (fzero (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))))))))))))))))))))))))))))"
		| "default_underscore valtype_F64 = (Some (val_CONST F64 (mk_num__1 Fnn_F64 (fzero (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))"
		| "default_underscore valtype_V128 = (Some (val_VCONST V128 (mk_uN 0)))"
		| "default_underscore valtype_FUNCREF = (Some (val_REF_NULL FUNCREF))"
		| "default_underscore valtype_EXTERNREF = (Some (val_REF_NULL EXTERNREF))"
		| "default_underscore x0 = None"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:7.6-7.15 *)
lemma default__is_wf :
	"((default_underscore v_valtype) \<noteq> None) \<Longrightarrow>
	 (ret_val = (the ((default_underscore v_valtype)))) \<Longrightarrow>
	 (wf_val ret_val)"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/5-runtime-aux.spectec:20.1-20.63 *)
inductive fun_funcsxa :: "(externaddr list) \<Rightarrow> (funcaddr list) \<Rightarrow> bool" where
	  fun_funcsxa_case_0 :
		"fun_funcsxa [] []"
	| fun_funcsxa_case_1 :
		"(fun_funcsxa xv_lst var_0) \<Longrightarrow>
		 fun_funcsxa ([(externaddr_FUNC fa)] @ xv_lst) ([fa] @ var_0)"
	| fun_funcsxa_case_2 :
		"(fun_funcsxa xv_lst var_0) \<Longrightarrow>
		 fun_funcsxa ([v_externaddr] @ xv_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/5-runtime-aux.spectec:21.1-21.65 *)
inductive fun_globalsxa :: "(externaddr list) \<Rightarrow> (globaladdr list) \<Rightarrow> bool" where
	  fun_globalsxa_case_0 :
		"fun_globalsxa [] []"
	| fun_globalsxa_case_1 :
		"(fun_globalsxa xv_lst var_0) \<Longrightarrow>
		 fun_globalsxa ([(externaddr_GLOBAL ga)] @ xv_lst) ([ga] @ var_0)"
	| fun_globalsxa_case_2 :
		"(fun_globalsxa xv_lst var_0) \<Longrightarrow>
		 fun_globalsxa ([v_externaddr] @ xv_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/5-runtime-aux.spectec:22.1-22.64 *)
inductive fun_tablesxa :: "(externaddr list) \<Rightarrow> (tableaddr list) \<Rightarrow> bool" where
	  fun_tablesxa_case_0 :
		"fun_tablesxa [] []"
	| fun_tablesxa_case_1 :
		"(fun_tablesxa xv_lst var_0) \<Longrightarrow>
		 fun_tablesxa ([(externaddr_TABLE ta)] @ xv_lst) ([ta] @ var_0)"
	| fun_tablesxa_case_2 :
		"(fun_tablesxa xv_lst var_0) \<Longrightarrow>
		 fun_tablesxa ([v_externaddr] @ xv_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/5-runtime-aux.spectec:23.1-23.62 *)
inductive fun_memsxa :: "(externaddr list) \<Rightarrow> (memaddr list) \<Rightarrow> bool" where
	  fun_memsxa_case_0 :
		"fun_memsxa [] []"
	| fun_memsxa_case_1 :
		"(fun_memsxa xv_lst var_0) \<Longrightarrow>
		 fun_memsxa ([(externaddr_MEM ma)] @ xv_lst) ([ma] @ var_0)"
	| fun_memsxa_case_2 :
		"(fun_memsxa xv_lst var_0) \<Longrightarrow>
		 fun_memsxa ([v_externaddr] @ xv_lst) var_0"

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:48.1-48.57 *)
function (sequential, domintros) fun_store :: "state \<Rightarrow> store" where
		  "fun_store (mk_state s f) = s"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:48.6-48.12 *)
lemma store_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val = (fun_store v_state)) \<Longrightarrow>
	 (wf_store ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:49.1-49.57 *)
function (sequential, domintros) fun_frame :: "state \<Rightarrow> frame" where
		  "fun_frame (mk_state s f) = f"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:49.6-49.12 *)
lemma frame_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val = (fun_frame v_state)) \<Longrightarrow>
	 (wf_frame ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:55.1-55.64 *)
function (sequential, domintros) fun_funcaddr :: "state \<Rightarrow> (funcaddr list)" where
		  "fun_funcaddr (mk_state s f) = (FUNCS (frame_MODULE f))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:58.1-58.57 *)
function (sequential, domintros) fun_funcinst :: "state \<Rightarrow> (funcinst list)" where
		  "fun_funcinst (mk_state s f) = (store_FUNCS s)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:58.6-58.15 *)
lemma funcinst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val_lst = (fun_funcinst v_state)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: funcinst). (wf_funcinst ret_val)) ret_val_lst"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:59.1-59.59 *)
function (sequential, domintros) fun_globalinst :: "state \<Rightarrow> (globalinst list)" where
		  "fun_globalinst (mk_state s f) = (store_GLOBALS s)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:59.6-59.17 *)
lemma globalinst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val_lst = (fun_globalinst v_state)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: globalinst). (wf_globalinst ret_val)) ret_val_lst"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:60.1-60.58 *)
function (sequential, domintros) fun_tableinst :: "state \<Rightarrow> (tableinst list)" where
		  "fun_tableinst (mk_state s f) = (store_TABLES s)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:60.6-60.16 *)
lemma tableinst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val_lst = (fun_tableinst v_state)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: tableinst). (wf_tableinst ret_val)) ret_val_lst"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:61.1-61.56 *)
function (sequential, domintros) fun_meminst :: "state \<Rightarrow> (meminst list)" where
		  "fun_meminst (mk_state s f) = (store_MEMS s)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:61.6-61.14 *)
lemma meminst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val_lst = (fun_meminst v_state)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: meminst). (wf_meminst ret_val)) ret_val_lst"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:62.1-62.57 *)
function (sequential, domintros) fun_eleminst :: "state \<Rightarrow> (eleminst list)" where
		  "fun_eleminst (mk_state s f) = (store_ELEMS s)"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:63.1-63.57 *)
function (sequential, domintros) fun_datainst :: "state \<Rightarrow> (datainst list)" where
		  "fun_datainst (mk_state s f) = (store_DATAS s)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:63.6-63.15 *)
lemma datainst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val_lst = (fun_datainst v_state)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: datainst). (wf_datainst ret_val)) ret_val_lst"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:64.1-64.58 *)
function (sequential, domintros) fun_moduleinst :: "state \<Rightarrow> moduleinst" where
		  "fun_moduleinst (mk_state s f) = (frame_MODULE f)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:64.6-64.17 *)
lemma moduleinst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (ret_val = (fun_moduleinst v_state)) \<Longrightarrow>
	 (wf_moduleinst ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:74.1-74.66 *)
function (sequential, domintros) fun_type :: "state \<Rightarrow> typeidx \<Rightarrow> functype" where
		  "fun_type (mk_state s f) x = ((TYPES (frame_MODULE f)) ! (proj_uN_0 x))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:75.1-75.66 *)
function (sequential, domintros) fun_func :: "state \<Rightarrow> funcidx \<Rightarrow> funcinst" where
		  "fun_func (mk_state s f) x = ((store_FUNCS s) ! ((FUNCS (frame_MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:75.6-75.11 *)
lemma func_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_funcidx) \<Longrightarrow>
	 (ret_val = (fun_func v_state v_funcidx)) \<Longrightarrow>
	 (wf_funcinst ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:76.1-76.68 *)
function (sequential, domintros) fun_global :: "state \<Rightarrow> globalidx \<Rightarrow> globalinst" where
		  "fun_global (mk_state s f) x = ((store_GLOBALS s) ! ((GLOBALS (frame_MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:76.6-76.13 *)
lemma global_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_globalidx) \<Longrightarrow>
	 (ret_val = (fun_global v_state v_globalidx)) \<Longrightarrow>
	 (wf_globalinst ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:77.1-77.67 *)
function (sequential, domintros) fun_table :: "state \<Rightarrow> tableidx \<Rightarrow> tableinst" where
		  "fun_table (mk_state s f) x = ((store_TABLES s) ! ((TABLES (frame_MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:77.6-77.12 *)
lemma table_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_tableidx) \<Longrightarrow>
	 (ret_val = (fun_table v_state v_tableidx)) \<Longrightarrow>
	 (wf_tableinst ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:78.1-78.65 *)
function (sequential, domintros) fun_mem :: "state \<Rightarrow> memidx \<Rightarrow> meminst" where
		  "fun_mem (mk_state s f) x = ((store_MEMS s) ! ((MEMS (frame_MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:78.6-78.10 *)
lemma mem_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_memidx) \<Longrightarrow>
	 (ret_val = (fun_mem v_state v_memidx)) \<Longrightarrow>
	 (wf_meminst ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:79.1-79.66 *)
function (sequential, domintros) fun_elem :: "state \<Rightarrow> tableidx \<Rightarrow> eleminst" where
		  "fun_elem (mk_state s f) x = ((store_ELEMS s) ! ((ELEMS (frame_MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:80.1-80.66 *)
function (sequential, domintros) fun_data :: "state \<Rightarrow> dataidx \<Rightarrow> datainst" where
		  "fun_data (mk_state s f) x = ((store_DATAS s) ! ((DATAS (frame_MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:80.6-80.11 *)
lemma data_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_dataidx) \<Longrightarrow>
	 (ret_val = (fun_data v_state v_dataidx)) \<Longrightarrow>
	 (wf_datainst ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:81.1-81.67 *)
function (sequential, domintros) fun_local :: "state \<Rightarrow> localidx \<Rightarrow> val" where
		  "fun_local (mk_state s f) x = ((LOCALS f) ! (proj_uN_0 x))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:81.6-81.12 *)
lemma local_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_localidx) \<Longrightarrow>
	 (ret_val = (fun_local v_state v_localidx)) \<Longrightarrow>
	 (wf_val ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:95.1-95.89 *)
function (sequential, domintros) with_local :: "state \<Rightarrow> localidx \<Rightarrow> val \<Rightarrow> state" where
		  "with_local (mk_state s f) x v = (mk_state s (f \<lparr> LOCALS := (list_update_func (LOCALS f) (proj_uN_0 x) (\<lambda> (underscore_underscore :: val). v))  \<rparr>))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:95.6-95.17 *)
lemma with_local_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_localidx) \<Longrightarrow>
	 (wf_val v_val) \<Longrightarrow>
	 (ret_val = (with_local v_state v_localidx v_val)) \<Longrightarrow>
	 (wf_state ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:96.1-96.96 *)
function (sequential, domintros) with_global :: "state \<Rightarrow> globalidx \<Rightarrow> val \<Rightarrow> state" where
		  "with_global (mk_state s f) x v = (mk_state (s \<lparr> store_GLOBALS := (list_update_func (store_GLOBALS s) ((GLOBALS (frame_MODULE f)) ! (proj_uN_0 x)) (\<lambda> (var_1 :: globalinst). (var_1 \<lparr> VALUE := v  \<rparr>)))  \<rparr>) f)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:96.6-96.18 *)
lemma with_global_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_globalidx) \<Longrightarrow>
	 (wf_val v_val) \<Longrightarrow>
	 (ret_val = (with_global v_state v_globalidx v_val)) \<Longrightarrow>
	 (wf_state ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:97.1-97.97 *)
function (sequential, domintros) with_table :: "state \<Rightarrow> tableidx \<Rightarrow> nat \<Rightarrow> ref \<Rightarrow> state" where
		  "with_table (mk_state s f) x i r = (mk_state (s \<lparr> store_TABLES := (list_update_func (store_TABLES s) ((TABLES (frame_MODULE f)) ! (proj_uN_0 x)) (\<lambda> (var_1 :: tableinst). (var_1 \<lparr> REFS := (list_update_func (REFS var_1) i (\<lambda> (underscore_underscore :: ref). r))  \<rparr>)))  \<rparr>) f)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:97.6-97.17 *)
lemma with_table_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_tableidx) \<Longrightarrow>
	 (ret_val = (with_table v_state v_tableidx res_nat v_ref)) \<Longrightarrow>
	 (wf_state ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:98.1-98.89 *)
function (sequential, domintros) with_tableinst :: "state \<Rightarrow> tableidx \<Rightarrow> tableinst \<Rightarrow> state" where
		  "with_tableinst (mk_state s f) x ti = (mk_state (s \<lparr> store_TABLES := (list_update_func (store_TABLES s) ((TABLES (frame_MODULE f)) ! (proj_uN_0 x)) (\<lambda> (underscore_underscore :: tableinst). ti))  \<rparr>) f)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:98.6-98.21 *)
lemma with_tableinst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_tableidx) \<Longrightarrow>
	 (wf_tableinst v_tableinst) \<Longrightarrow>
	 (ret_val = (with_tableinst v_state v_tableidx v_tableinst)) \<Longrightarrow>
	 (wf_state ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:99.1-99.100 *)
function (sequential, domintros) with_mem :: "state \<Rightarrow> memidx \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (byte list) \<Rightarrow> state" where
		  "with_mem (mk_state s f) x i j b_lst = (mk_state (s \<lparr> store_MEMS := (list_update_func (store_MEMS s) ((MEMS (frame_MODULE f)) ! (proj_uN_0 x)) (\<lambda> (var_1 :: meminst). (var_1 \<lparr> BYTES := (list_slice_update (BYTES var_1) i j b_lst)  \<rparr>)))  \<rparr>) f)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:99.6-99.15 *)
lemma with_mem_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_memidx) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = (with_mem v_state v_memidx res_nat nat_0 var_0_lst)) \<Longrightarrow>
	 (wf_state ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:100.1-100.87 *)
function (sequential, domintros) with_meminst :: "state \<Rightarrow> memidx \<Rightarrow> meminst \<Rightarrow> state" where
		  "with_meminst (mk_state s f) x mi = (mk_state (s \<lparr> store_MEMS := (list_update_func (store_MEMS s) ((MEMS (frame_MODULE f)) ! (proj_uN_0 x)) (\<lambda> (underscore_underscore :: meminst). mi))  \<rparr>) f)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:100.6-100.19 *)
lemma with_meminst_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_memidx) \<Longrightarrow>
	 (wf_meminst v_meminst) \<Longrightarrow>
	 (ret_val = (with_meminst v_state v_memidx v_meminst)) \<Longrightarrow>
	 (wf_state ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:101.1-101.93 *)
function (sequential, domintros) with_elem :: "state \<Rightarrow> elemidx \<Rightarrow> (ref list) \<Rightarrow> state" where
		  "with_elem (mk_state s f) x r_lst = (mk_state (s \<lparr> store_ELEMS := (list_update_func (store_ELEMS s) ((ELEMS (frame_MODULE f)) ! (proj_uN_0 x)) (\<lambda> (var_1 :: eleminst). (var_1 \<lparr> eleminst_REFS := r_lst  \<rparr>)))  \<rparr>) f)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:101.6-101.16 *)
lemma with_elem_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_elemidx) \<Longrightarrow>
	 (ret_val = (with_elem v_state v_elemidx var_0_lst)) \<Longrightarrow>
	 (wf_state ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:102.1-102.94 *)
function (sequential, domintros) with_data :: "state \<Rightarrow> dataidx \<Rightarrow> (byte list) \<Rightarrow> state" where
		  "with_data (mk_state s f) x b_lst = (mk_state (s \<lparr> store_DATAS := (list_update_func (store_DATAS s) ((DATAS (frame_MODULE f)) ! (proj_uN_0 x)) (\<lambda> (var_1 :: datainst). (var_1 \<lparr> datainst_BYTES := b_lst  \<rparr>)))  \<rparr>) f)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:102.6-102.16 *)
lemma with_data_is_wf :
	"(wf_state v_state) \<Longrightarrow>
	 (wf_uN 32 v_dataidx) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = (with_data v_state v_dataidx var_0_lst)) \<Longrightarrow>
	 (wf_state ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:116.6-116.16 *)
inductive fun_growtable_before_fun_growtable_case_1 :: "tableinst \<Rightarrow> nat \<Rightarrow> ref \<Rightarrow> bool" where
	  fun_growtable_case_0 :
		"(\<lparr> tableinst_TYPE = (mk_tabletype (mk_limits i j_opt) rt), REFS = r'_lst \<rparr> = ti) \<Longrightarrow>
		 (i' = ((length r'_lst) + v_n)) \<Longrightarrow>
		 list_all (\<lambda> (j_2 :: u32). (i' \<le> (proj_uN_0 j_2))) (option_to_list j_opt) \<Longrightarrow>
		 (ti' = \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN i') j_opt) rt), REFS = (r'_lst @ (repeat v_n r)) \<rparr>) \<Longrightarrow>
		 (wf_tableinst \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits i j_opt) rt), REFS = r'_lst \<rparr>) \<Longrightarrow>
		 (wf_tableinst \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN i') j_opt) rt), REFS = (r'_lst @ (repeat v_n r)) \<rparr>) \<Longrightarrow>
		 fun_growtable_before_fun_growtable_case_1 ti v_n r"

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:116.6-116.16 *)
inductive fun_growtable :: "tableinst \<Rightarrow> nat \<Rightarrow> ref \<Rightarrow> (tableinst option) \<Rightarrow> bool" where
	  fun_growtable__fun_growtable_case_0 :
		"(\<lparr> tableinst_TYPE = (mk_tabletype (mk_limits i j_opt) rt), REFS = r'_lst \<rparr> = ti) \<Longrightarrow>
		 (i' = ((length r'_lst) + v_n)) \<Longrightarrow>
		 list_all (\<lambda> (j_2 :: u32). (i' \<le> (proj_uN_0 j_2))) (option_to_list j_opt) \<Longrightarrow>
		 (ti' = \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN i') j_opt) rt), REFS = (r'_lst @ (repeat v_n r)) \<rparr>) \<Longrightarrow>
		 (wf_tableinst \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits i j_opt) rt), REFS = r'_lst \<rparr>) \<Longrightarrow>
		 (wf_tableinst \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN i') j_opt) rt), REFS = (r'_lst @ (repeat v_n r)) \<rparr>) \<Longrightarrow>
		 fun_growtable ti v_n r (Some ti')"
	| fun_growtable_case_1 :
		"(~(fun_growtable_before_fun_growtable_case_1 x0 x1 x2)) \<Longrightarrow>
		 fun_growtable x0 x1 x2 None"

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:116.6-116.16 *)
lemma growtable_is_wf :
	"(fun_growtable v_tableinst res_nat v_ref var_0) \<Longrightarrow>
	 (wf_tableinst v_tableinst) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_tableinst ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:117.6-117.17 *)
inductive fun_growmemory_before_fun_growmemory_case_1 :: "meminst \<Rightarrow> nat \<Rightarrow> bool" where
	  fun_growmemory_case_0 :
		"(\<lparr> meminst_TYPE = (PAGE (mk_limits i j_opt)), BYTES = b_lst \<rparr> = mi) \<Longrightarrow>
		 (i' = ((((length b_lst) :: nat) div ((64 * (Ki )) :: nat)) + (v_n :: nat))) \<Longrightarrow>
		 list_all (\<lambda> (j_7 :: u32). (i' \<le> ((proj_uN_0 j_7) :: nat))) (option_to_list j_opt) \<Longrightarrow>
		 (mi' = \<lparr> meminst_TYPE = (PAGE (mk_limits (mk_uN (i' :: nat)) j_opt)), BYTES = (b_lst @ (repeat (v_n * (64 * (Ki ))) (mk_byte 0))) \<rparr>) \<Longrightarrow>
		 (wf_meminst \<lparr> meminst_TYPE = (PAGE (mk_limits i j_opt)), BYTES = b_lst \<rparr>) \<Longrightarrow>
		 (wf_meminst \<lparr> meminst_TYPE = (PAGE (mk_limits (mk_uN (i' :: nat)) j_opt)), BYTES = (b_lst @ (repeat (v_n * (64 * (Ki ))) (mk_byte 0))) \<rparr>) \<Longrightarrow>
		 fun_growmemory_before_fun_growmemory_case_1 mi v_n"

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:117.6-117.17 *)
inductive fun_growmemory :: "meminst \<Rightarrow> nat \<Rightarrow> (meminst option) \<Rightarrow> bool" where
	  fun_growmemory__fun_growmemory_case_0 :
		"(\<lparr> meminst_TYPE = (PAGE (mk_limits i j_opt)), BYTES = b_lst \<rparr> = mi) \<Longrightarrow>
		 (i' = ((((length b_lst) :: nat) div ((64 * (Ki )) :: nat)) + (v_n :: nat))) \<Longrightarrow>
		 list_all (\<lambda> (j_7 :: u32). (i' \<le> ((proj_uN_0 j_7) :: nat))) (option_to_list j_opt) \<Longrightarrow>
		 (mi' = \<lparr> meminst_TYPE = (PAGE (mk_limits (mk_uN (i' :: nat)) j_opt)), BYTES = (b_lst @ (repeat (v_n * (64 * (Ki ))) (mk_byte 0))) \<rparr>) \<Longrightarrow>
		 (wf_meminst \<lparr> meminst_TYPE = (PAGE (mk_limits i j_opt)), BYTES = b_lst \<rparr>) \<Longrightarrow>
		 (wf_meminst \<lparr> meminst_TYPE = (PAGE (mk_limits (mk_uN (i' :: nat)) j_opt)), BYTES = (b_lst @ (repeat (v_n * (64 * (Ki ))) (mk_byte 0))) \<rparr>) \<Longrightarrow>
		 fun_growmemory mi v_n (Some mi')"
	| fun_growmemory_case_1 :
		"(~(fun_growmemory_before_fun_growmemory_case_1 x0 x1)) \<Longrightarrow>
		 fun_growmemory x0 x1 None"

(* Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:117.6-117.17 *)
lemma growmemory_is_wf :
	"(fun_growmemory v_meminst res_nat var_0) \<Longrightarrow>
	 (wf_meminst v_meminst) \<Longrightarrow>
	 (var_0 \<noteq> None) \<Longrightarrow>
	 (ret_val = (the (var_0))) \<Longrightarrow>
	 (wf_meminst ret_val)"
sorry

(* Record Creation Definition at: ../specification/wasm-2.0/6-typing.spectec:5.1-9.62 *)
record res_context =
	context_TYPES :: "(functype list)"
	context_FUNCS :: "(functype list)"
	context_GLOBALS :: "(globaltype list)"
	context_TABLES :: "(tabletype list)"
	context_MEMS :: "(memtype list)"
	context_ELEMS :: "(elemtype list)"
	context_DATAS :: "(res_datatype list)"
	context_LOCALS :: "(valtype list)"
	LABELS :: "(resulttype list)"
	context_RETURN :: "(resulttype option)"

definition append_res_context :: "res_context \<Rightarrow> res_context \<Rightarrow> res_context" where
	"append_res_context arg1 arg2 = \<lparr>
		context_TYPES = context_TYPES arg1 @ context_TYPES arg2,
		context_FUNCS = context_FUNCS arg1 @ context_FUNCS arg2,
		context_GLOBALS = context_GLOBALS arg1 @ context_GLOBALS arg2,
		context_TABLES = context_TABLES arg1 @ context_TABLES arg2,
		context_MEMS = context_MEMS arg1 @ context_MEMS arg2,
		context_ELEMS = context_ELEMS arg1 @ context_ELEMS arg2,
		context_DATAS = context_DATAS arg1 @ context_DATAS arg2,
		context_LOCALS = context_LOCALS arg1 @ context_LOCALS arg2,
		LABELS = LABELS arg1 @ LABELS arg2,
		context_RETURN = context_RETURN arg1 @@@ context_RETURN arg2
	\<rparr>"



(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:5.8-5.15 *)
inductive wf_context :: "res_context \<Rightarrow> bool" where
	  context_case_underscore :
		"list_all (\<lambda> (var_3 :: tabletype). (wf_tabletype var_3)) var_3_lst \<Longrightarrow>
		 list_all (\<lambda> (var_4 :: memtype). (wf_memtype var_4)) var_4_lst \<Longrightarrow>
		 wf_context \<lparr> context_TYPES = var_0_lst, context_FUNCS = var_1_lst, context_GLOBALS = var_2_lst, context_TABLES = var_3_lst, context_MEMS = var_4_lst, context_ELEMS = var_5_lst, context_DATAS = var_6_lst, context_LOCALS = var_7_lst, LABELS = var_8_lst, context_RETURN = var_9_opt \<rparr>"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:19.1-19.66 *)
inductive Limits_ok :: "limits \<Rightarrow> nat \<Rightarrow> bool" where
	  mk_Limits_ok :
		"(v_n \<le> k) \<Longrightarrow>
		 list_all (\<lambda> (v_m :: nat). ((v_n \<le> v_m) \<and> (v_m \<le> k))) (option_to_list m_opt) \<Longrightarrow>
		 (wf_limits (mk_limits (mk_uN v_n) (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt))) \<Longrightarrow>
		 Limits_ok (mk_limits (mk_uN v_n) (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt)) k"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:20.1-20.64 *)
inductive Functype_ok :: "functype \<Rightarrow> bool" where
	  mk_Functype_ok :
		"Functype_ok (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:21.1-21.66 *)
inductive Globaltype_ok :: "globaltype \<Rightarrow> bool" where
	  mk_Globaltype_ok :
		"Globaltype_ok (mk_globaltype (Some MUT) t)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:22.1-22.65 *)
inductive Tabletype_ok :: "tabletype \<Rightarrow> bool" where
	  mk_Tabletype_ok :
		"(Limits_ok v_limits ((((2 ^ 32) :: nat) - (1 :: nat)) :: nat)) \<Longrightarrow>
		 (wf_tabletype (mk_tabletype v_limits v_reftype)) \<Longrightarrow>
		 Tabletype_ok (mk_tabletype v_limits v_reftype)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:23.1-23.63 *)
inductive Memtype_ok :: "memtype \<Rightarrow> bool" where
	  mk_Memtype_ok :
		"(Limits_ok v_limits (2 ^ 16)) \<Longrightarrow>
		 (wf_memtype (PAGE v_limits)) \<Longrightarrow>
		 Memtype_ok (PAGE v_limits)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:24.1-24.66 *)
inductive Externtype_ok :: "externtype \<Rightarrow> bool" where
	  Externtype_ok__func :
		"(Functype_ok v_functype) \<Longrightarrow>
		 (wf_externtype (FUNC v_functype)) \<Longrightarrow>
		 Externtype_ok (FUNC v_functype)"
	| Externtype_ok__global :
		"(Globaltype_ok v_globaltype) \<Longrightarrow>
		 (wf_externtype (GLOBAL v_globaltype)) \<Longrightarrow>
		 Externtype_ok (GLOBAL v_globaltype)"
	| Externtype_ok__table :
		"(Tabletype_ok v_tabletype) \<Longrightarrow>
		 (wf_externtype (TABLE v_tabletype)) \<Longrightarrow>
		 Externtype_ok (TABLE v_tabletype)"
	| Externtype_ok__mem :
		"(Memtype_ok v_memtype) \<Longrightarrow>
		 (wf_externtype (MEM v_memtype)) \<Longrightarrow>
		 Externtype_ok (MEM v_memtype)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:71.1-71.69 *)
inductive Valtype_sub :: "valtype \<Rightarrow> valtype \<Rightarrow> bool" where
	  refl :
		"Valtype_sub t t"
	| bot :
		"Valtype_sub BOT t"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:72.1-72.76 *)
inductive Resulttype_sub :: "resulttype \<Rightarrow> resulttype \<Rightarrow> bool" where
	  mk_Resulttype_sub :
		"((length t_1_lst) = (length t_2_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (t_1 :: valtype) (t_2 :: valtype). (Valtype_sub t_1 t_2)) t_1_lst t_2_lst \<Longrightarrow>
		 Resulttype_sub (mk_list t_1_lst) (mk_list t_2_lst)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:87.1-87.75 *)
inductive Limits_sub :: "limits \<Rightarrow> limits \<Rightarrow> bool" where
	  mk_Limits_sub :
		"(n_11 \<ge> n_21) \<Longrightarrow>
		 (n_12 \<le> n_22) \<Longrightarrow>
		 (wf_limits (mk_limits (mk_uN n_11) (Some (mk_uN n_12)))) \<Longrightarrow>
		 (wf_limits (mk_limits (mk_uN n_21) (Some (mk_uN n_22)))) \<Longrightarrow>
		 Limits_sub (mk_limits (mk_uN n_11) (Some (mk_uN n_12))) (mk_limits (mk_uN n_21) (Some (mk_uN n_22)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:88.1-88.73 *)
inductive Functype_sub :: "functype \<Rightarrow> functype \<Rightarrow> bool" where
	  mk_Functype_sub :
		"Functype_sub ft ft"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:89.1-89.75 *)
inductive Globaltype_sub :: "globaltype \<Rightarrow> globaltype \<Rightarrow> bool" where
	  mk_Globaltype_sub :
		"Globaltype_sub gt gt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:90.1-90.74 *)
inductive Tabletype_sub :: "tabletype \<Rightarrow> tabletype \<Rightarrow> bool" where
	  mk_Tabletype_sub :
		"(Limits_sub lim_1 lim_2) \<Longrightarrow>
		 (wf_tabletype (mk_tabletype lim_1 rt)) \<Longrightarrow>
		 (wf_tabletype (mk_tabletype lim_2 rt)) \<Longrightarrow>
		 Tabletype_sub (mk_tabletype lim_1 rt) (mk_tabletype lim_2 rt)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:91.1-91.72 *)
inductive Memtype_sub :: "memtype \<Rightarrow> memtype \<Rightarrow> bool" where
	  mk_Memtype_sub :
		"(Limits_sub lim_1 lim_2) \<Longrightarrow>
		 (wf_memtype (PAGE lim_1)) \<Longrightarrow>
		 (wf_memtype (PAGE lim_2)) \<Longrightarrow>
		 Memtype_sub (PAGE lim_1) (PAGE lim_2)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:92.1-92.75 *)
inductive Externtype_sub :: "externtype \<Rightarrow> externtype \<Rightarrow> bool" where
	  Externtype_sub__func :
		"(Functype_sub ft_1 ft_2) \<Longrightarrow>
		 (wf_externtype (FUNC ft_1)) \<Longrightarrow>
		 (wf_externtype (FUNC ft_2)) \<Longrightarrow>
		 Externtype_sub (FUNC ft_1) (FUNC ft_2)"
	| Externtype_sub__global :
		"(Globaltype_sub gt_1 gt_2) \<Longrightarrow>
		 (wf_externtype (GLOBAL gt_1)) \<Longrightarrow>
		 (wf_externtype (GLOBAL gt_2)) \<Longrightarrow>
		 Externtype_sub (GLOBAL gt_1) (GLOBAL gt_2)"
	| Externtype_sub__table :
		"(Tabletype_sub tt_1 tt_2) \<Longrightarrow>
		 (wf_externtype (TABLE tt_1)) \<Longrightarrow>
		 (wf_externtype (TABLE tt_2)) \<Longrightarrow>
		 Externtype_sub (TABLE tt_1) (TABLE tt_2)"
	| Externtype_sub__mem :
		"(Memtype_sub mt_1 mt_2) \<Longrightarrow>
		 (wf_externtype (MEM mt_1)) \<Longrightarrow>
		 (wf_externtype (MEM mt_2)) \<Longrightarrow>
		 Externtype_sub (MEM mt_1) (MEM mt_2)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:198.1-198.76 *)
inductive Blocktype_ok :: "res_context \<Rightarrow> blocktype \<Rightarrow> functype \<Rightarrow> bool" where
	  Blocktype_ok__valtype :
		"(wf_context C) \<Longrightarrow>
		 (wf_blocktype (underscore_RESULT valtype_opt)) \<Longrightarrow>
		 Blocktype_ok C (underscore_RESULT valtype_opt) (mk_functype (mk_list []) (mk_list (option_to_list valtype_opt)))"
	| Blocktype_ok__typeidx :
		"((proj_uN_0 v_typeidx) < (length (context_TYPES C))) \<Longrightarrow>
		 (((context_TYPES C) ! (proj_uN_0 v_typeidx)) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_blocktype (underscore_IDX v_typeidx)) \<Longrightarrow>
		 Blocktype_ok C (underscore_IDX v_typeidx) (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"

(* Mutual Recursion at: ../specification/wasm-2.0/6-typing.spectec:137.1-138.65 *)
inductive Instr_ok :: "res_context \<Rightarrow> instr \<Rightarrow> functype \<Rightarrow> bool"
and Instrs_ok :: "res_context \<Rightarrow> (instr list) \<Rightarrow> functype \<Rightarrow> bool" where
	  nop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc0 NOP)) \<Longrightarrow>
		 Instr_ok C (instr_sc0 NOP) (mk_functype (mk_list []) (mk_list []))"
	| unreachable :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc0 UNREACHABLE)) \<Longrightarrow>
		 Instr_ok C (instr_sc0 UNREACHABLE) (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"
	| drop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc0 DROP)) \<Longrightarrow>
		 Instr_ok C (instr_sc0 DROP) (mk_functype (mk_list [t]) (mk_list []))"
	| select_expl :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc0 (SELECT (Some [t])))) \<Longrightarrow>
		 Instr_ok C (instr_sc0 (SELECT (Some [t]))) (mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t]))"
	| select_impl :
		"(Valtype_sub t t') \<Longrightarrow>
		 ((t' = (valtype_numtype v_numtype)) \<or> (t' = (valtype_vectype v_vectype))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc0 (SELECT None))) \<Longrightarrow>
		 Instr_ok C (instr_sc0 (SELECT None)) (mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t]))"
	| block :
		"(Blocktype_ok C bt (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (Instrs_ok (append_res_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr> C) instr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc7 (BLOCK bt instr_lst))) \<Longrightarrow>
		 (wf_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr>) \<Longrightarrow>
		 Instr_ok C (instr_sc7 (BLOCK bt instr_lst)) (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"
	| loop :
		"(Blocktype_ok C bt (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (Instrs_ok (append_res_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_1_lst)], context_RETURN = None \<rparr> C) instr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc7 (LOOP bt instr_lst))) \<Longrightarrow>
		 (wf_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_1_lst)], context_RETURN = None \<rparr>) \<Longrightarrow>
		 Instr_ok C (instr_sc7 (LOOP bt instr_lst)) (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"
	| res_if :
		"(Blocktype_ok C bt (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (Instrs_ok (append_res_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr> C) instr_1_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (Instrs_ok (append_res_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr> C) instr_2_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc7 (IFELSE bt instr_1_lst instr_2_lst))) \<Longrightarrow>
		 (wf_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr>) \<Longrightarrow>
		 Instr_ok C (instr_sc7 (IFELSE bt instr_1_lst instr_2_lst)) (mk_functype (mk_list (t_1_lst @ [valtype_I32])) (mk_list t_2_lst))"
	| br :
		"((proj_uN_0 l) < (length (LABELS C))) \<Longrightarrow>
		 ((proj_list_0  ((LABELS C) ! (proj_uN_0 l))) = t_lst) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc0 (BR l))) \<Longrightarrow>
		 Instr_ok C (instr_sc0 (BR l)) (mk_functype (mk_list (t_1_lst @ t_lst)) (mk_list t_2_lst))"
	| br_if :
		"((proj_uN_0 l) < (length (LABELS C))) \<Longrightarrow>
		 ((proj_list_0  ((LABELS C) ! (proj_uN_0 l))) = t_lst) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc0 (BR_IF l))) \<Longrightarrow>
		 Instr_ok C (instr_sc0 (BR_IF l)) (mk_functype (mk_list (t_lst @ [valtype_I32])) (mk_list t_lst))"
	| br_table :
		"list_all (\<lambda> (l :: labelidx). ((proj_uN_0 l) < (length (LABELS C)))) l_lst \<Longrightarrow>
		 list_all (\<lambda> (l :: labelidx). (Resulttype_sub (mk_list t_lst) ((LABELS C) ! (proj_uN_0 l)))) l_lst \<Longrightarrow>
		 ((proj_uN_0 l') < (length (LABELS C))) \<Longrightarrow>
		 (Resulttype_sub (mk_list t_lst) ((LABELS C) ! (proj_uN_0 l'))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc0 (BR_TABLE l_lst l'))) \<Longrightarrow>
		 Instr_ok C (instr_sc0 (BR_TABLE l_lst l')) (mk_functype (mk_list (t_1_lst @ (t_lst @ [valtype_I32]))) (mk_list t_2_lst))"
	| call :
		"((proj_uN_0 x) < (length (context_FUNCS C))) \<Longrightarrow>
		 (((context_FUNCS C) ! (proj_uN_0 x)) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc0 (CALL x))) \<Longrightarrow>
		 Instr_ok C (instr_sc0 (CALL x)) (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"
	| call_indirect :
		"((proj_uN_0 x) < (length (context_TABLES C))) \<Longrightarrow>
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim FUNCREF)) \<Longrightarrow>
		 ((proj_uN_0 y) < (length (context_TYPES C))) \<Longrightarrow>
		 (((context_TYPES C) ! (proj_uN_0 y)) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc0 (CALL_INDIRECT x y))) \<Longrightarrow>
		 (wf_tabletype (mk_tabletype lim FUNCREF)) \<Longrightarrow>
		 Instr_ok C (instr_sc0 (CALL_INDIRECT x y)) (mk_functype (mk_list (t_1_lst @ [valtype_I32])) (mk_list t_2_lst))"
	| return :
		"((context_RETURN C) = (Some (mk_list t_lst))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc1 RETURN)) \<Longrightarrow>
		 Instr_ok C (instr_sc1 RETURN) (mk_functype (mk_list (t_1_lst @ t_lst)) (mk_list t_2_lst))"
	| const :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc1 (res_CONST nt c_nt))) \<Longrightarrow>
		 Instr_ok C (instr_sc1 (res_CONST nt c_nt)) (mk_functype (mk_list []) (mk_list [(valtype_numtype nt)]))"
	| unop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc1 (UNOP nt unop_nt))) \<Longrightarrow>
		 Instr_ok C (instr_sc1 (UNOP nt unop_nt)) (mk_functype (mk_list [(valtype_numtype nt)]) (mk_list [(valtype_numtype nt)]))"
	| binop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc1 (BINOP nt binop_nt))) \<Longrightarrow>
		 Instr_ok C (instr_sc1 (BINOP nt binop_nt)) (mk_functype (mk_list [(valtype_numtype nt), (valtype_numtype nt)]) (mk_list [(valtype_numtype nt)]))"
	| testop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc1 (TESTOP nt testop_nt))) \<Longrightarrow>
		 Instr_ok C (instr_sc1 (TESTOP nt testop_nt)) (mk_functype (mk_list [(valtype_numtype nt)]) (mk_list [valtype_I32]))"
	| relop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc1 (RELOP nt relop_nt))) \<Longrightarrow>
		 Instr_ok C (instr_sc1 (RELOP nt relop_nt)) (mk_functype (mk_list [(valtype_numtype nt), (valtype_numtype nt)]) (mk_list [valtype_I32]))"
	| cvtop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc1 (CVTOP nt_1 nt_2 cvtop))) \<Longrightarrow>
		 Instr_ok C (instr_sc1 (CVTOP nt_1 nt_2 cvtop)) (mk_functype (mk_list [(valtype_numtype nt_2)]) (mk_list [(valtype_numtype nt_1)]))"
	| ref_null :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc4 (REF_NULL rt))) \<Longrightarrow>
		 Instr_ok C (instr_sc4 (REF_NULL rt)) (mk_functype (mk_list []) (mk_list [(valtype_reftype rt)]))"
	| ref_func :
		"((proj_uN_0 x) < (length (context_FUNCS C))) \<Longrightarrow>
		 (((context_FUNCS C) ! (proj_uN_0 x)) = ft) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc4 (REF_FUNC x))) \<Longrightarrow>
		 Instr_ok C (instr_sc4 (REF_FUNC x)) (mk_functype (mk_list []) (mk_list [valtype_FUNCREF]))"
	| ref_is_null :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc4 REF_IS_NULL)) \<Longrightarrow>
		 Instr_ok C (instr_sc4 REF_IS_NULL) (mk_functype (mk_list [(valtype_reftype rt)]) (mk_list [valtype_I32]))"
	| vconst :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc1 (VCONST V128 c))) \<Longrightarrow>
		 Instr_ok C (instr_sc1 (VCONST V128 c)) (mk_functype (mk_list []) (mk_list [valtype_V128]))"
	| Instr_ok__vvunop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc2 (VVUNOP V128 v_vvunop))) \<Longrightarrow>
		 Instr_ok C (instr_sc2 (VVUNOP V128 v_vvunop)) (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]))"
	| Instr_ok__vvbinop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc2 (VVBINOP V128 v_vvbinop))) \<Longrightarrow>
		 Instr_ok C (instr_sc2 (VVBINOP V128 v_vvbinop)) (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
	| Instr_ok__vvternop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc2 (VVTERNOP V128 v_vvternop))) \<Longrightarrow>
		 Instr_ok C (instr_sc2 (VVTERNOP V128 v_vvternop)) (mk_functype (mk_list [valtype_V128, valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
	| Instr_ok__vvtestop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc2 (VVTESTOP V128 v_vvtestop))) \<Longrightarrow>
		 Instr_ok C (instr_sc2 (VVTESTOP V128 v_vvtestop)) (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32]))"
	| vunop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc2 (VUNOP sh vunop_sh))) \<Longrightarrow>
		 Instr_ok C (instr_sc2 (VUNOP sh vunop_sh)) (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]))"
	| vbinop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc2 (VBINOP sh vbinop_sh))) \<Longrightarrow>
		 Instr_ok C (instr_sc2 (VBINOP sh vbinop_sh)) (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
	| vtestop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc2 (VTESTOP sh vtestop_sh))) \<Longrightarrow>
		 Instr_ok C (instr_sc2 (VTESTOP sh vtestop_sh)) (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32]))"
	| vrelop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc2 (VRELOP sh vrelop_sh))) \<Longrightarrow>
		 Instr_ok C (instr_sc2 (VRELOP sh vrelop_sh)) (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
	| vshiftop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc2 (VSHIFTOP sh vshiftop_sh))) \<Longrightarrow>
		 Instr_ok C (instr_sc2 (VSHIFTOP sh vshiftop_sh)) (mk_functype (mk_list [valtype_V128, valtype_I32]) (mk_list [valtype_V128]))"
	| vbitmask :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc3 (VBITMASK sh))) \<Longrightarrow>
		 Instr_ok C (instr_sc3 (VBITMASK sh)) (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32]))"
	| vswizzle :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc3 (VSWIZZLE sh))) \<Longrightarrow>
		 Instr_ok C (instr_sc3 (VSWIZZLE sh)) (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
	| vshuffle :
		"list_all (\<lambda> (i :: laneidx). ((proj_uN_0 i) < (2 * (proj_dim_0 (fun_dim (shape_ishape sh)))))) i_lst \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_dim (fun_dim (shape_ishape sh))) \<Longrightarrow>
		 (wf_instr (instr_sc3 (VSHUFFLE sh i_lst))) \<Longrightarrow>
		 Instr_ok C (instr_sc3 (VSHUFFLE sh i_lst)) (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
	| vsplat :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc3 (VSPLAT sh))) \<Longrightarrow>
		 Instr_ok C (instr_sc3 (VSPLAT sh)) (mk_functype (mk_list [(valtype_numtype (shunpack sh))]) (mk_list [valtype_V128]))"
	| vextract_lane :
		"((proj_uN_0 i) < (proj_dim_0 (fun_dim sh))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_dim (fun_dim sh)) \<Longrightarrow>
		 (wf_instr (instr_sc3 (VEXTRACT_LANE sh sx_opt i))) \<Longrightarrow>
		 Instr_ok C (instr_sc3 (VEXTRACT_LANE sh sx_opt i)) (mk_functype (mk_list [valtype_V128]) (mk_list [(valtype_numtype (shunpack sh))]))"
	| vreplace_lane :
		"((proj_uN_0 i) < (proj_dim_0 (fun_dim sh))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_dim (fun_dim sh)) \<Longrightarrow>
		 (wf_instr (instr_sc3 (VREPLACE_LANE sh i))) \<Longrightarrow>
		 Instr_ok C (instr_sc3 (VREPLACE_LANE sh i)) (mk_functype (mk_list [valtype_V128, (valtype_numtype (shunpack sh))]) (mk_list [valtype_V128]))"
	| vextunop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc3 (VEXTUNOP sh_1 sh_2 vextunop))) \<Longrightarrow>
		 Instr_ok C (instr_sc3 (VEXTUNOP sh_1 sh_2 vextunop)) (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]))"
	| vextbinop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc3 (VEXTBINOP sh_1 sh_2 vextbinop))) \<Longrightarrow>
		 Instr_ok C (instr_sc3 (VEXTBINOP sh_1 sh_2 vextbinop)) (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
	| vnarrow :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc3 (VNARROW sh_1 sh_2 v_sx))) \<Longrightarrow>
		 Instr_ok C (instr_sc3 (VNARROW sh_1 sh_2 v_sx)) (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]))"
	| Instr_ok__vcvtop :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc4 (VCVTOP sh_1 sh_2 v_vcvtop))) \<Longrightarrow>
		 Instr_ok C (instr_sc4 (VCVTOP sh_1 sh_2 v_vcvtop)) (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]))"
	| local_get :
		"((proj_uN_0 x) < (length (context_LOCALS C))) \<Longrightarrow>
		 (((context_LOCALS C) ! (proj_uN_0 x)) = t) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc4 (LOCAL_GET x))) \<Longrightarrow>
		 Instr_ok C (instr_sc4 (LOCAL_GET x)) (mk_functype (mk_list []) (mk_list [t]))"
	| local_set :
		"((proj_uN_0 x) < (length (context_LOCALS C))) \<Longrightarrow>
		 (((context_LOCALS C) ! (proj_uN_0 x)) = t) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc4 (LOCAL_SET x))) \<Longrightarrow>
		 Instr_ok C (instr_sc4 (LOCAL_SET x)) (mk_functype (mk_list [t]) (mk_list []))"
	| local_tee :
		"((proj_uN_0 x) < (length (context_LOCALS C))) \<Longrightarrow>
		 (((context_LOCALS C) ! (proj_uN_0 x)) = t) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc4 (LOCAL_TEE x))) \<Longrightarrow>
		 Instr_ok C (instr_sc4 (LOCAL_TEE x)) (mk_functype (mk_list [t]) (mk_list [t]))"
	| global_get :
		"((proj_uN_0 x) < (length (context_GLOBALS C))) \<Longrightarrow>
		 (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype v_mut t)) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc4 (GLOBAL_GET x))) \<Longrightarrow>
		 Instr_ok C (instr_sc4 (GLOBAL_GET x)) (mk_functype (mk_list []) (mk_list [t]))"
	| global_set :
		"((proj_uN_0 x) < (length (context_GLOBALS C))) \<Longrightarrow>
		 (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype (Some MUT) t)) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc4 (GLOBAL_SET x))) \<Longrightarrow>
		 Instr_ok C (instr_sc4 (GLOBAL_SET x)) (mk_functype (mk_list [t]) (mk_list []))"
	| table_get :
		"((proj_uN_0 x) < (length (context_TABLES C))) \<Longrightarrow>
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc5 (TABLE_GET x))) \<Longrightarrow>
		 (wf_tabletype (mk_tabletype lim rt)) \<Longrightarrow>
		 Instr_ok C (instr_sc5 (TABLE_GET x)) (mk_functype (mk_list [valtype_I32]) (mk_list [(valtype_reftype rt)]))"
	| table_set :
		"((proj_uN_0 x) < (length (context_TABLES C))) \<Longrightarrow>
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc5 (TABLE_SET x))) \<Longrightarrow>
		 (wf_tabletype (mk_tabletype lim rt)) \<Longrightarrow>
		 Instr_ok C (instr_sc5 (TABLE_SET x)) (mk_functype (mk_list [valtype_I32, (valtype_reftype rt)]) (mk_list []))"
	| table_size :
		"((proj_uN_0 x) < (length (context_TABLES C))) \<Longrightarrow>
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc5 (TABLE_SIZE x))) \<Longrightarrow>
		 (wf_tabletype (mk_tabletype lim rt)) \<Longrightarrow>
		 Instr_ok C (instr_sc5 (TABLE_SIZE x)) (mk_functype (mk_list []) (mk_list [valtype_I32]))"
	| table_grow :
		"((proj_uN_0 x) < (length (context_TABLES C))) \<Longrightarrow>
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc5 (TABLE_GROW x))) \<Longrightarrow>
		 (wf_tabletype (mk_tabletype lim rt)) \<Longrightarrow>
		 Instr_ok C (instr_sc5 (TABLE_GROW x)) (mk_functype (mk_list [(valtype_reftype rt), valtype_I32]) (mk_list [valtype_I32]))"
	| table_fill :
		"((proj_uN_0 x) < (length (context_TABLES C))) \<Longrightarrow>
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc5 (TABLE_FILL x))) \<Longrightarrow>
		 (wf_tabletype (mk_tabletype lim rt)) \<Longrightarrow>
		 Instr_ok C (instr_sc5 (TABLE_FILL x)) (mk_functype (mk_list [valtype_I32, (valtype_reftype rt), valtype_I32]) (mk_list []))"
	| table_copy :
		"((proj_uN_0 x_1) < (length (context_TABLES C))) \<Longrightarrow>
		 (((context_TABLES C) ! (proj_uN_0 x_1)) = (mk_tabletype lim_1 rt)) \<Longrightarrow>
		 ((proj_uN_0 x_2) < (length (context_TABLES C))) \<Longrightarrow>
		 (((context_TABLES C) ! (proj_uN_0 x_2)) = (mk_tabletype lim_2 rt)) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc5 (TABLE_COPY x_1 x_2))) \<Longrightarrow>
		 (wf_tabletype (mk_tabletype lim_1 rt)) \<Longrightarrow>
		 (wf_tabletype (mk_tabletype lim_2 rt)) \<Longrightarrow>
		 Instr_ok C (instr_sc5 (TABLE_COPY x_1 x_2)) (mk_functype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list []))"
	| table_init :
		"((proj_uN_0 x_1) < (length (context_TABLES C))) \<Longrightarrow>
		 (((context_TABLES C) ! (proj_uN_0 x_1)) = (mk_tabletype lim rt)) \<Longrightarrow>
		 ((proj_uN_0 x_2) < (length (context_ELEMS C))) \<Longrightarrow>
		 (((context_ELEMS C) ! (proj_uN_0 x_2)) = rt) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc5 (TABLE_INIT x_1 x_2))) \<Longrightarrow>
		 (wf_tabletype (mk_tabletype lim rt)) \<Longrightarrow>
		 Instr_ok C (instr_sc5 (TABLE_INIT x_1 x_2)) (mk_functype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list []))"
	| elem_drop :
		"((proj_uN_0 x) < (length (context_ELEMS C))) \<Longrightarrow>
		 (((context_ELEMS C) ! (proj_uN_0 x)) = rt) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc5 (ELEM_DROP x))) \<Longrightarrow>
		 Instr_ok C (instr_sc5 (ELEM_DROP x)) (mk_functype (mk_list []) (mk_list []))"
	| memory_size :
		"(0 < (length (context_MEMS C))) \<Longrightarrow>
		 (((context_MEMS C) ! 0) = mt) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_memtype mt) \<Longrightarrow>
		 (wf_instr (instr_sc6 MEMORY_SIZE)) \<Longrightarrow>
		 Instr_ok C (instr_sc6 MEMORY_SIZE) (mk_functype (mk_list []) (mk_list [valtype_I32]))"
	| memory_grow :
		"(0 < (length (context_MEMS C))) \<Longrightarrow>
		 (((context_MEMS C) ! 0) = mt) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_memtype mt) \<Longrightarrow>
		 (wf_instr (instr_sc6 MEMORY_GROW)) \<Longrightarrow>
		 Instr_ok C (instr_sc6 MEMORY_GROW) (mk_functype (mk_list [valtype_I32]) (mk_list [valtype_I32]))"
	| memory_fill :
		"(0 < (length (context_MEMS C))) \<Longrightarrow>
		 (((context_MEMS C) ! 0) = mt) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_memtype mt) \<Longrightarrow>
		 (wf_instr (instr_sc6 MEMORY_FILL)) \<Longrightarrow>
		 Instr_ok C (instr_sc6 MEMORY_FILL) (mk_functype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list []))"
	| memory_copy :
		"(0 < (length (context_MEMS C))) \<Longrightarrow>
		 (((context_MEMS C) ! 0) = mt) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_memtype mt) \<Longrightarrow>
		 (wf_instr (instr_sc6 MEMORY_COPY)) \<Longrightarrow>
		 Instr_ok C (instr_sc6 MEMORY_COPY) (mk_functype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list []))"
	| memory_init :
		"(0 < (length (context_MEMS C))) \<Longrightarrow>
		 (((context_MEMS C) ! 0) = mt) \<Longrightarrow>
		 ((proj_uN_0 x) < (length (context_DATAS C))) \<Longrightarrow>
		 (((context_DATAS C) ! (proj_uN_0 x)) = OK) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_memtype mt) \<Longrightarrow>
		 (wf_instr (instr_sc7 (MEMORY_INIT x))) \<Longrightarrow>
		 Instr_ok C (instr_sc7 (MEMORY_INIT x)) (mk_functype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list []))"
	| data_drop :
		"((proj_uN_0 x) < (length (context_DATAS C))) \<Longrightarrow>
		 (((context_DATAS C) ! (proj_uN_0 x)) = OK) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc7 (DATA_DROP x))) \<Longrightarrow>
		 Instr_ok C (instr_sc7 (DATA_DROP x)) (mk_functype (mk_list []) (mk_list []))"
	| load_val :
		"(0 < (length (context_MEMS C))) \<Longrightarrow>
		 (((context_MEMS C) ! 0) = mt) \<Longrightarrow>
		 ((size (valtype_numtype nt)) \<noteq> None) \<Longrightarrow>
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> (((the ((size (valtype_numtype nt)))) :: nat) div (8 :: nat))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_memtype mt) \<Longrightarrow>
		 (wf_instr (instr_sc5 (LOAD nt None v_memarg))) \<Longrightarrow>
		 Instr_ok C (instr_sc5 (LOAD nt None v_memarg)) (mk_functype (mk_list [valtype_I32]) (mk_list [(valtype_numtype nt)]))"
	| load_pack :
		"(0 < (length (context_MEMS C))) \<Longrightarrow>
		 (((context_MEMS C) ! 0) = mt) \<Longrightarrow>
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_M :: nat) div (8 :: nat))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_memtype mt) \<Longrightarrow>
		 (wf_instr (instr_sc5 (LOAD (numtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_M) v_sx))) v_memarg))) \<Longrightarrow>
		 Instr_ok C (instr_sc5 (LOAD (numtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_M) v_sx))) v_memarg)) (mk_functype (mk_list [valtype_I32]) (mk_list [(valtype_Inn v_Inn)]))"
	| store_val :
		"(0 < (length (context_MEMS C))) \<Longrightarrow>
		 (((context_MEMS C) ! 0) = mt) \<Longrightarrow>
		 ((size (valtype_numtype nt)) \<noteq> None) \<Longrightarrow>
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> (((the ((size (valtype_numtype nt)))) :: nat) div (8 :: nat))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_memtype mt) \<Longrightarrow>
		 (wf_instr (instr_sc6 (STORE nt None v_memarg))) \<Longrightarrow>
		 Instr_ok C (instr_sc6 (STORE nt None v_memarg)) (mk_functype (mk_list [valtype_I32, (valtype_numtype nt)]) (mk_list []))"
	| store_pack :
		"(0 < (length (context_MEMS C))) \<Longrightarrow>
		 (((context_MEMS C) ! 0) = mt) \<Longrightarrow>
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_M :: nat) div (8 :: nat))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_memtype mt) \<Longrightarrow>
		 (wf_instr (instr_sc6 (STORE (numtype_Inn v_Inn) (Some (mk_sz v_M)) v_memarg))) \<Longrightarrow>
		 Instr_ok C (instr_sc6 (STORE (numtype_Inn v_Inn) (Some (mk_sz v_M)) v_memarg)) (mk_functype (mk_list [valtype_I32, (valtype_Inn v_Inn)]) (mk_list []))"
	| vload :
		"(0 < (length (context_MEMS C))) \<Longrightarrow>
		 (((context_MEMS C) ! 0) = mt) \<Longrightarrow>
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> (((v_M :: nat) div (8 :: nat)) * (v_N :: nat))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_memtype mt) \<Longrightarrow>
		 (wf_instr (instr_sc6 (VLOAD V128 (Some (SHAPEX_underscore v_M v_N v_sx)) v_memarg))) \<Longrightarrow>
		 Instr_ok C (instr_sc6 (VLOAD V128 (Some (SHAPEX_underscore v_M v_N v_sx)) v_memarg)) (mk_functype (mk_list [valtype_I32]) (mk_list [valtype_V128]))"
	| vload_splat :
		"(0 < (length (context_MEMS C))) \<Longrightarrow>
		 (((context_MEMS C) ! 0) = mt) \<Longrightarrow>
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_n :: nat) div (8 :: nat))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_memtype mt) \<Longrightarrow>
		 (wf_instr (instr_sc6 (VLOAD V128 (Some (SPLAT v_n)) v_memarg))) \<Longrightarrow>
		 Instr_ok C (instr_sc6 (VLOAD V128 (Some (SPLAT v_n)) v_memarg)) (mk_functype (mk_list [valtype_I32]) (mk_list [valtype_V128]))"
	| vload_zero :
		"(0 < (length (context_MEMS C))) \<Longrightarrow>
		 (((context_MEMS C) ! 0) = mt) \<Longrightarrow>
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_n :: nat) div (8 :: nat))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_memtype mt) \<Longrightarrow>
		 (wf_instr (instr_sc6 (VLOAD V128 (Some (vloadop_ZERO v_n)) v_memarg))) \<Longrightarrow>
		 Instr_ok C (instr_sc6 (VLOAD V128 (Some (vloadop_ZERO v_n)) v_memarg)) (mk_functype (mk_list [valtype_I32]) (mk_list [valtype_V128]))"
	| vload_lane :
		"(0 < (length (context_MEMS C))) \<Longrightarrow>
		 (((context_MEMS C) ! 0) = mt) \<Longrightarrow>
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_n :: nat) div (8 :: nat))) \<Longrightarrow>
		 (((proj_uN_0 v_laneidx) :: nat) < ((128 :: nat) div (v_n :: nat))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_memtype mt) \<Longrightarrow>
		 (wf_instr (instr_sc6 (VLOAD_LANE V128 (mk_sz v_n) v_memarg v_laneidx))) \<Longrightarrow>
		 Instr_ok C (instr_sc6 (VLOAD_LANE V128 (mk_sz v_n) v_memarg v_laneidx)) (mk_functype (mk_list [valtype_I32, valtype_V128]) (mk_list [valtype_V128]))"
	| vstore :
		"(0 < (length (context_MEMS C))) \<Longrightarrow>
		 (((context_MEMS C) ! 0) = mt) \<Longrightarrow>
		 ((size valtype_V128) \<noteq> None) \<Longrightarrow>
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> (((the ((size valtype_V128))) :: nat) div (8 :: nat))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_memtype mt) \<Longrightarrow>
		 (wf_instr (instr_sc6 (VSTORE V128 v_memarg))) \<Longrightarrow>
		 Instr_ok C (instr_sc6 (VSTORE V128 v_memarg)) (mk_functype (mk_list [valtype_I32, valtype_V128]) (mk_list []))"
	| vstore_lane :
		"(0 < (length (context_MEMS C))) \<Longrightarrow>
		 (((context_MEMS C) ! 0) = mt) \<Longrightarrow>
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_n :: nat) div (8 :: nat))) \<Longrightarrow>
		 (((proj_uN_0 v_laneidx) :: nat) < ((128 :: nat) div (v_n :: nat))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_memtype mt) \<Longrightarrow>
		 (wf_instr (instr_sc6 (VSTORE_LANE V128 (mk_sz v_n) v_memarg v_laneidx))) \<Longrightarrow>
		 Instr_ok C (instr_sc6 (VSTORE_LANE V128 (mk_sz v_n) v_memarg v_laneidx)) (mk_functype (mk_list [valtype_I32, valtype_V128]) (mk_list []))"
	| empty :
		"(wf_context C) \<Longrightarrow>
		 Instrs_ok C [] (mk_functype (mk_list []) (mk_list []))"
	| Instrs_ok__instr :
		"(Instr_ok C v_instr (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr v_instr) \<Longrightarrow>
		 Instrs_ok C [v_instr] (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"
	| seq :
		"(Instrs_ok C instr_1_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (Instrs_ok C instr_2_lst (mk_functype (mk_list t_2_lst) (mk_list t_3_lst))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 list_all (\<lambda> (instr_1 :: instr). (wf_instr instr_1)) instr_1_lst \<Longrightarrow>
		 list_all (\<lambda> (instr_2 :: instr). (wf_instr instr_2)) instr_2_lst \<Longrightarrow>
		 Instrs_ok C (instr_1_lst @ instr_2_lst) (mk_functype (mk_list t_1_lst) (mk_list t_3_lst))"
	| sub :
		"(Instrs_ok C instr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (Resulttype_sub (mk_list t'_1_lst) (mk_list t_1_lst)) \<Longrightarrow>
		 (Resulttype_sub (mk_list t_2_lst) (mk_list t'_2_lst)) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 list_all (\<lambda> (v_instr :: instr). (wf_instr v_instr)) instr_lst \<Longrightarrow>
		 Instrs_ok C instr_lst (mk_functype (mk_list t'_1_lst) (mk_list t'_2_lst))"
	| Instrs_ok__frame :
		"(Instrs_ok C instr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 list_all (\<lambda> (v_instr :: instr). (wf_instr v_instr)) instr_lst \<Longrightarrow>
		 Instrs_ok C instr_lst (mk_functype (mk_list (t_lst @ t_1_lst)) (mk_list (t_lst @ t_2_lst)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:139.1-139.69 *)
inductive Expr_ok :: "res_context \<Rightarrow> expr \<Rightarrow> resulttype \<Rightarrow> bool" where
	  mk_Expr_ok :
		"(Instrs_ok C instr_lst (mk_functype (mk_list []) (mk_list t_lst))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 list_all (\<lambda> (v_instr :: instr). (wf_instr v_instr)) instr_lst \<Longrightarrow>
		 Expr_ok C instr_lst (mk_list t_lst)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:523.1-523.78 *)
inductive Instr_const :: "res_context \<Rightarrow> instr \<Rightarrow> bool" where
	  Instr_const__const :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc1 (res_CONST nt c))) \<Longrightarrow>
		 Instr_const C (instr_sc1 (res_CONST nt c))"
	| Instr_const__vconst :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc1 (VCONST vt vc))) \<Longrightarrow>
		 Instr_const C (instr_sc1 (VCONST vt vc))"
	| Instr_const__ref_null :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc4 (REF_NULL rt))) \<Longrightarrow>
		 Instr_const C (instr_sc4 (REF_NULL rt))"
	| Instr_const__ref_func :
		"(wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc4 (REF_FUNC x))) \<Longrightarrow>
		 Instr_const C (instr_sc4 (REF_FUNC x))"
	| Instr_const__global_get :
		"((proj_uN_0 x) < (length (context_GLOBALS C))) \<Longrightarrow>
		 (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype None t)) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr (instr_sc4 (GLOBAL_GET x))) \<Longrightarrow>
		 Instr_const C (instr_sc4 (GLOBAL_GET x))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:524.1-524.77 *)
inductive Expr_const :: "res_context \<Rightarrow> expr \<Rightarrow> bool" where
	  mk_Expr_const :
		"list_all (\<lambda> (v_instr :: instr). (Instr_const C v_instr)) instr_lst \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 list_all (\<lambda> (v_instr :: instr). (wf_instr v_instr)) instr_lst \<Longrightarrow>
		 Expr_const C instr_lst"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:525.1-525.78 *)
inductive Expr_ok_const :: "res_context \<Rightarrow> expr \<Rightarrow> valtype \<Rightarrow> bool" where
	  mk_Expr_ok_const :
		"(Expr_ok C v_expr (mk_list [t])) \<Longrightarrow>
		 (Expr_const C v_expr) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 list_all (\<lambda> (v_expr :: instr). (wf_instr v_expr)) v_expr \<Longrightarrow>
		 Expr_ok_const C v_expr t"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:558.1-558.73 *)
inductive Type_ok :: "type \<Rightarrow> functype \<Rightarrow> bool" where
	  mk_Type_ok :
		"(Functype_ok ft) \<Longrightarrow>
		 Type_ok (res_TYPE ft) ft"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:559.1-559.73 *)
inductive Func_ok :: "res_context \<Rightarrow> func \<Rightarrow> functype \<Rightarrow> bool" where
	  mk_Func_ok :
		"((proj_uN_0 x) < (length (context_TYPES C))) \<Longrightarrow>
		 (((context_TYPES C) ! (proj_uN_0 x)) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 list_all (\<lambda> (t :: valtype). (t \<noteq> BOT)) t_lst \<Longrightarrow>
		 (Expr_ok (append_res_context C \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = (t_1_lst @ t_lst), LABELS = [(mk_list t_2_lst)], context_RETURN = (Some (mk_list t_2_lst)) \<rparr>) v_expr (mk_list t_2_lst)) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_func (func_FUNC x (map (\<lambda> (t :: valtype). (LOCAL t)) t_lst) v_expr)) \<Longrightarrow>
		 (wf_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = (t_1_lst @ t_lst), LABELS = [(mk_list t_2_lst)], context_RETURN = (Some (mk_list t_2_lst)) \<rparr>) \<Longrightarrow>
		 Func_ok C (func_FUNC x (map (\<lambda> (t :: valtype). (LOCAL t)) t_lst) v_expr) (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:560.1-560.75 *)
inductive Global_ok :: "res_context \<Rightarrow> global \<Rightarrow> globaltype \<Rightarrow> bool" where
	  mk_Global_ok :
		"(Globaltype_ok gt) \<Longrightarrow>
		 (gt = (mk_globaltype v_mut t)) \<Longrightarrow>
		 (Expr_ok_const C v_expr t) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_global (global_GLOBAL gt v_expr)) \<Longrightarrow>
		 Global_ok C (global_GLOBAL gt v_expr) gt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:561.1-561.74 *)
inductive Table_ok :: "res_context \<Rightarrow> table \<Rightarrow> tabletype \<Rightarrow> bool" where
	  mk_Table_ok :
		"(Tabletype_ok tt) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_table (table_TABLE tt)) \<Longrightarrow>
		 Table_ok C (table_TABLE tt) tt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:562.1-562.72 *)
inductive Mem_ok :: "res_context \<Rightarrow> mem \<Rightarrow> memtype \<Rightarrow> bool" where
	  mk_Mem_ok :
		"(Memtype_ok mt) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_mem (MEMORY mt)) \<Longrightarrow>
		 Mem_ok C (MEMORY mt) mt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:565.1-565.77 *)
inductive Elemmode_ok :: "res_context \<Rightarrow> elemmode \<Rightarrow> reftype \<Rightarrow> bool" where
	  active :
		"((proj_uN_0 x) < (length (context_TABLES C))) \<Longrightarrow>
		 (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<Longrightarrow>
		 (Expr_ok_const C v_expr valtype_I32) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_elemmode (ACTIVE x v_expr)) \<Longrightarrow>
		 (wf_tabletype (mk_tabletype lim rt)) \<Longrightarrow>
		 Elemmode_ok C (ACTIVE x v_expr) rt"
	| res_passive :
		"(wf_context C) \<Longrightarrow>
		 (wf_elemmode PASSIVE) \<Longrightarrow>
		 Elemmode_ok C PASSIVE rt"
	| res_declare :
		"(wf_context C) \<Longrightarrow>
		 (wf_elemmode DECLARE) \<Longrightarrow>
		 Elemmode_ok C DECLARE rt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:563.1-563.73 *)
inductive Elem_ok :: "res_context \<Rightarrow> elem \<Rightarrow> reftype \<Rightarrow> bool" where
	  mk_Elem_ok :
		"list_all (\<lambda> (v_expr :: expr). (Expr_ok_const C v_expr (valtype_reftype rt))) expr_lst \<Longrightarrow>
		 (Elemmode_ok C v_elemmode rt) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_elem (ELEM rt expr_lst v_elemmode)) \<Longrightarrow>
		 Elem_ok C (ELEM rt expr_lst v_elemmode) rt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:566.1-566.77 *)
inductive Datamode_ok :: "res_context \<Rightarrow> datamode \<Rightarrow> bool" where
	  Datamode_ok__active :
		"(0 < (length (context_MEMS C))) \<Longrightarrow>
		 (((context_MEMS C) ! 0) = mt) \<Longrightarrow>
		 (Expr_ok_const C v_expr valtype_I32) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_memtype mt) \<Longrightarrow>
		 (wf_datamode (datamode_ACTIVE (mk_uN 0) v_expr)) \<Longrightarrow>
		 Datamode_ok C (datamode_ACTIVE (mk_uN 0) v_expr)"
	| Datamode_ok__passive :
		"(wf_context C) \<Longrightarrow>
		 (wf_datamode datamode_PASSIVE) \<Longrightarrow>
		 Datamode_ok C datamode_PASSIVE"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:564.1-564.73 *)
inductive Data_ok :: "res_context \<Rightarrow> data \<Rightarrow> bool" where
	  mk_Data_ok :
		"(Datamode_ok C v_datamode) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_data (DATA b_lst v_datamode)) \<Longrightarrow>
		 Data_ok C (DATA b_lst v_datamode)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:567.1-567.74 *)
inductive Start_ok :: "res_context \<Rightarrow> start \<Rightarrow> bool" where
	  mk_Start_ok :
		"((proj_uN_0 x) < (length (context_FUNCS C))) \<Longrightarrow>
		 (((context_FUNCS C) ! (proj_uN_0 x)) = (mk_functype (mk_list []) (mk_list []))) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_start (START x)) \<Longrightarrow>
		 Start_ok C (START x)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:631.1-631.80 *)
inductive Import_ok :: "res_context \<Rightarrow> import \<Rightarrow> externtype \<Rightarrow> bool" where
	  mk_Import_ok :
		"(Externtype_ok xt) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_import (IMPORT name_1 name_2 xt)) \<Longrightarrow>
		 Import_ok C (IMPORT name_1 name_2 xt) xt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:633.1-633.83 *)
inductive Externidx_ok :: "res_context \<Rightarrow> externidx \<Rightarrow> externtype \<Rightarrow> bool" where
	  Externidx_ok__func :
		"((proj_uN_0 x) < (length (context_FUNCS C))) \<Longrightarrow>
		 (((context_FUNCS C) ! (proj_uN_0 x)) = ft) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_externidx (externidx_FUNC x)) \<Longrightarrow>
		 (wf_externtype (FUNC ft)) \<Longrightarrow>
		 Externidx_ok C (externidx_FUNC x) (FUNC ft)"
	| Externidx_ok__global :
		"((proj_uN_0 x) < (length (context_GLOBALS C))) \<Longrightarrow>
		 (((context_GLOBALS C) ! (proj_uN_0 x)) = gt) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_externidx (externidx_GLOBAL x)) \<Longrightarrow>
		 (wf_externtype (GLOBAL gt)) \<Longrightarrow>
		 Externidx_ok C (externidx_GLOBAL x) (GLOBAL gt)"
	| Externidx_ok__table :
		"((proj_uN_0 x) < (length (context_TABLES C))) \<Longrightarrow>
		 (((context_TABLES C) ! (proj_uN_0 x)) = tt) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_externidx (externidx_TABLE x)) \<Longrightarrow>
		 (wf_externtype (TABLE tt)) \<Longrightarrow>
		 Externidx_ok C (externidx_TABLE x) (TABLE tt)"
	| Externidx_ok__mem :
		"((proj_uN_0 x) < (length (context_MEMS C))) \<Longrightarrow>
		 (((context_MEMS C) ! (proj_uN_0 x)) = mt) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_externidx (externidx_MEM x)) \<Longrightarrow>
		 (wf_externtype (MEM mt)) \<Longrightarrow>
		 Externidx_ok C (externidx_MEM x) (MEM mt)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:632.1-632.80 *)
inductive Export_ok :: "res_context \<Rightarrow> export \<Rightarrow> externtype \<Rightarrow> bool" where
	  mk_Export_ok :
		"(Externidx_ok C v_externidx xt) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_externtype xt) \<Longrightarrow>
		 (wf_export (EXPORT v_name v_externidx)) \<Longrightarrow>
		 Export_ok C (EXPORT v_name v_externidx) xt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:663.1-663.62 *)
inductive Module_ok :: "module \<Rightarrow> bool" where
	  mk_Module_ok :
		"(fun_memsxt ixt_lst var_3) \<Longrightarrow>
		 (fun_tablesxt ixt_lst var_2) \<Longrightarrow>
		 (fun_globalsxt ixt_lst var_1) \<Longrightarrow>
		 (fun_funcsxt ixt_lst var_0) \<Longrightarrow>
		 ((length ft'_lst) = (length type_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (ft' :: functype) (v_type :: type). (Type_ok v_type ft')) ft'_lst type_lst \<Longrightarrow>
		 ((length import_lst) = (length ixt_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (v_import :: import) (ixt :: externtype). (Import_ok \<lparr> context_TYPES = ft'_lst, context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [], context_RETURN = None \<rparr> v_import ixt)) import_lst ixt_lst \<Longrightarrow>
		 ((length global_lst) = (length gt_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (v_global :: global) (gt :: globaltype). (Global_ok C' v_global gt)) global_lst gt_lst \<Longrightarrow>
		 ((length table_lst) = (length tt_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (v_table :: table) (tt :: tabletype). (Table_ok C' v_table tt)) table_lst tt_lst \<Longrightarrow>
		 ((length mem_lst) = (length mt_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (v_mem :: mem) (mt :: memtype). (Mem_ok C' v_mem mt)) mem_lst mt_lst \<Longrightarrow>
		 ((length elem_lst) = (length rt_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (v_elem :: elem) (rt :: reftype). (Elem_ok C' v_elem rt)) elem_lst rt_lst \<Longrightarrow>
		 list_all (\<lambda> (v_data :: data). (Data_ok C' v_data)) data_lst \<Longrightarrow>
		 ((length ft_lst) = (length func_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (ft :: functype) (v_func :: func). (Func_ok C v_func ft)) ft_lst func_lst \<Longrightarrow>
		 list_all (\<lambda> (v_start :: start). (Start_ok C v_start)) (option_to_list start_opt) \<Longrightarrow>
		 ((length export_lst) = (length xt_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (v_export :: export) (xt :: externtype). (Export_ok C v_export xt)) export_lst xt_lst \<Longrightarrow>
		 ((length mt_lst) \<le> 1) \<Longrightarrow>
		 (C = \<lparr> context_TYPES = ft'_lst, context_FUNCS = (ift_lst @ ft_lst), context_GLOBALS = (igt_lst @ gt_lst), context_TABLES = (itt_lst @ tt_lst), context_MEMS = (imt_lst @ mt_lst), context_ELEMS = rt_lst, context_DATAS = (repeat v_n OK), context_LOCALS = [], LABELS = [], context_RETURN = None \<rparr>) \<Longrightarrow>
		 (C' = \<lparr> context_TYPES = ft'_lst, context_FUNCS = (ift_lst @ ft_lst), context_GLOBALS = igt_lst, context_TABLES = (itt_lst @ tt_lst), context_MEMS = (imt_lst @ mt_lst), context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [], context_RETURN = None \<rparr>) \<Longrightarrow>
		 (ift_lst = var_0) \<Longrightarrow>
		 (igt_lst = var_1) \<Longrightarrow>
		 (itt_lst = var_2) \<Longrightarrow>
		 (imt_lst = var_3) \<Longrightarrow>
		 list_all (\<lambda> (ixt :: externtype). (wf_externtype ixt)) ixt_lst \<Longrightarrow>
		 (wf_context C') \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 list_all (\<lambda> (xt :: externtype). (wf_externtype xt)) xt_lst \<Longrightarrow>
		 list_all (\<lambda> (iter :: tabletype). (wf_tabletype iter)) var_2 \<Longrightarrow>
		 list_all (\<lambda> (iter :: memtype). (wf_memtype iter)) var_3 \<Longrightarrow>
		 (wf_module (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)) \<Longrightarrow>
		 (wf_context \<lparr> context_TYPES = ft'_lst, context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [], context_RETURN = None \<rparr>) \<Longrightarrow>
		 (wf_context \<lparr> context_TYPES = ft'_lst, context_FUNCS = (ift_lst @ ft_lst), context_GLOBALS = (igt_lst @ gt_lst), context_TABLES = (itt_lst @ tt_lst), context_MEMS = (imt_lst @ mt_lst), context_ELEMS = rt_lst, context_DATAS = (repeat v_n OK), context_LOCALS = [], LABELS = [], context_RETURN = None \<rparr>) \<Longrightarrow>
		 (wf_context \<lparr> context_TYPES = ft'_lst, context_FUNCS = (ift_lst @ ft_lst), context_GLOBALS = igt_lst, context_TABLES = (itt_lst @ tt_lst), context_MEMS = (imt_lst @ mt_lst), context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [], context_RETURN = None \<rparr>) \<Longrightarrow>
		 (v_n = (length data_lst)) \<Longrightarrow>
		 Module_ok (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:224.1-226.15 *)
inductive Step_pure_before_ref_is_null_false :: "(admininstr list) \<Rightarrow> bool" where
	  ref_is_null_true_0 :
		"(v_ref = (ref_REF_NULL rt)) \<Longrightarrow>
		 Step_pure_before_ref_is_null_false [(admininstr_ref v_ref), (admininstr_sc4 admininstr_st4_REF_IS_NULL)]"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:276.1-278.15 *)
inductive Step_pure_before_vtestop_false :: "(admininstr list) \<Rightarrow> bool" where
	  vtestop_true_0 :
		"(ci_1_lst = (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c)) \<Longrightarrow>
		 list_all (\<lambda> (ci_1 :: lane_underscore). ((proj_lane__2 ci_1) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_1 :: lane_underscore). ((proj_uN_0 (the ((proj_lane__2 ci_1)))) \<noteq> 0)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_1 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ci_1)) ci_1_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) \<Longrightarrow>
		 Step_pure_before_vtestop_false [(admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc3 (admininstr_st3_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (mk_vtestop__0 v_Jnn v_N ALL_TRUE)))]"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.1-6.109 *)
inductive Step_pure :: "(admininstr list) \<Rightarrow> (admininstr list) \<Rightarrow> bool" where
	  Step_pure__unreachable :
		"Step_pure [(admininstr_sc0 admininstr_st0_UNREACHABLE)] [(admininstr_sc7 admininstr_st7_TRAP)]"
	| Step_pure__nop :
		"Step_pure [(admininstr_sc0 admininstr_st0_NOP)] []"
	| Step_pure__drop :
		"Step_pure [(admininstr_val v_val), (admininstr_sc0 admininstr_st0_DROP)] []"
	| select_true :
		"((proj_num__0 c) \<noteq> None) \<Longrightarrow>
		 ((proj_uN_0 (the ((proj_num__0 c)))) \<noteq> 0) \<Longrightarrow>
		 Step_pure [(admininstr_val val_1), (admininstr_val val_2), (admininstr_sc1 (admininstr_st1_CONST I32 c)), (admininstr_sc0 (admininstr_st0_SELECT t_lst_opt))] [(admininstr_val val_1)]"
	| select_false :
		"((proj_num__0 c) \<noteq> None) \<Longrightarrow>
		 ((proj_uN_0 (the ((proj_num__0 c)))) = 0) \<Longrightarrow>
		 Step_pure [(admininstr_val val_1), (admininstr_val val_2), (admininstr_sc1 (admininstr_st1_CONST I32 c)), (admininstr_sc0 (admininstr_st0_SELECT t_lst_opt))] [(admininstr_val val_2)]"
	| if_true :
		"((proj_num__0 c) \<noteq> None) \<Longrightarrow>
		 ((proj_uN_0 (the ((proj_num__0 c)))) \<noteq> 0) \<Longrightarrow>
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST I32 c)), (admininstr_sc0 (admininstr_st0_IFELSE bt instr_1_lst instr_2_lst))] [(admininstr_sc0 (admininstr_st0_BLOCK bt instr_1_lst))]"
	| if_false :
		"((proj_num__0 c) \<noteq> None) \<Longrightarrow>
		 ((proj_uN_0 (the ((proj_num__0 c)))) = 0) \<Longrightarrow>
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST I32 c)), (admininstr_sc0 (admininstr_st0_IFELSE bt instr_1_lst instr_2_lst))] [(admininstr_sc0 (admininstr_st0_BLOCK bt instr_2_lst))]"
	| label_vals :
		"Step_pure [(admininstr_sc8 (LABEL_underscore v_n instr_lst (map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst)))] (map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst)"
	| br_zero :
		"(v_n = (length val_lst)) \<Longrightarrow>
		 Step_pure [(admininstr_sc8 (LABEL_underscore v_n instr'_lst ((((map (\<lambda> (val' :: val). (admininstr_val val')) val'_lst) @ (map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst)) @ [(admininstr_sc0 (admininstr_st0_BR (mk_uN 0)))]) @ (map (\<lambda> (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))))] ((map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst) @ (map (\<lambda> (instr' :: instr). (admininstr_instr instr')) instr'_lst))"
	| br_succ :
		"Step_pure [(admininstr_sc8 (LABEL_underscore v_n instr'_lst (((map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_sc0 (admininstr_st0_BR (mk_uN ((proj_uN_0 l) + 1))))]) @ (map (\<lambda> (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))))] ((map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_sc0 (admininstr_st0_BR l))])"
	| br_if_true :
		"((proj_num__0 c) \<noteq> None) \<Longrightarrow>
		 ((proj_uN_0 (the ((proj_num__0 c)))) \<noteq> 0) \<Longrightarrow>
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST I32 c)), (admininstr_sc0 (admininstr_st0_BR_IF l))] [(admininstr_sc0 (admininstr_st0_BR l))]"
	| br_if_false :
		"((proj_num__0 c) \<noteq> None) \<Longrightarrow>
		 ((proj_uN_0 (the ((proj_num__0 c)))) = 0) \<Longrightarrow>
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST I32 c)), (admininstr_sc0 (admininstr_st0_BR_IF l))] []"
	| br_table_lt :
		"((proj_uN_0 (the ((proj_num__0 i)))) < (length l_lst)) \<Longrightarrow>
		 ((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_BR_TABLE l_lst l'))] [(admininstr_sc0 (admininstr_st0_BR (l_lst ! (proj_uN_0 (the ((proj_num__0 i)))))))]"
	| br_table_ge :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_uN_0 (the ((proj_num__0 i)))) \<ge> (length l_lst)) \<Longrightarrow>
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_BR_TABLE l_lst l'))] [(admininstr_sc0 (admininstr_st0_BR l'))]"
	| frame_vals :
		"(v_n = (length val_lst)) \<Longrightarrow>
		 Step_pure [(admininstr_sc8 (FRAME_underscore v_n f (map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst)))] (map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst)"
	| return_frame :
		"(v_n = (length val_lst)) \<Longrightarrow>
		 Step_pure [(admininstr_sc8 (FRAME_underscore v_n f ((((map (\<lambda> (val' :: val). (admininstr_val val')) val'_lst) @ (map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst)) @ [(admininstr_sc1 admininstr_st1_RETURN)]) @ (map (\<lambda> (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))))] (map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst)"
	| return_label :
		"Step_pure [(admininstr_sc8 (LABEL_underscore v_n instr'_lst (((map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_sc1 admininstr_st1_RETURN)]) @ (map (\<lambda> (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))))] ((map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_sc1 admininstr_st1_RETURN)])"
	| trap_vals :
		"((val_lst \<noteq> []) \<or> (instr_lst \<noteq> [])) \<Longrightarrow>
		 Step_pure ((map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst) @ ([(admininstr_sc7 admininstr_st7_TRAP)] @ (map (\<lambda> (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| trap_label :
		"Step_pure [(admininstr_sc8 (LABEL_underscore v_n instr'_lst [(admininstr_sc7 admininstr_st7_TRAP)]))] [(admininstr_sc7 admininstr_st7_TRAP)]"
	| trap_frame :
		"Step_pure [(admininstr_sc8 (FRAME_underscore v_n f [(admininstr_sc7 admininstr_st7_TRAP)]))] [(admininstr_sc7 admininstr_st7_TRAP)]"
	| unop_val :
		"((length (fun_unop_underscore nt unop c_1)) > 0) \<Longrightarrow>
		 (c \<in> set (fun_unop_underscore nt unop c_1)) \<Longrightarrow>
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST nt c_1)), (admininstr_sc1 (admininstr_st1_UNOP nt unop))] [(admininstr_sc1 (admininstr_st1_CONST nt c))]"
	| unop_trap :
		"((fun_unop_underscore nt unop c_1) = []) \<Longrightarrow>
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST nt c_1)), (admininstr_sc1 (admininstr_st1_UNOP nt unop))] [(admininstr_sc7 admininstr_st7_TRAP)]"
	| binop_val :
		"(fun_binop_underscore nt binop c_1 c_2 var_0) \<Longrightarrow>
		 ((length var_0) > 0) \<Longrightarrow>
		 (c \<in> set var_0) \<Longrightarrow>
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST nt c_1)), (admininstr_sc1 (admininstr_st1_CONST nt c_2)), (admininstr_sc1 (admininstr_st1_BINOP nt binop))] [(admininstr_sc1 (admininstr_st1_CONST nt c))]"
	| binop_trap :
		"(fun_binop_underscore nt binop c_1 c_2 var_0) \<Longrightarrow>
		 (var_0 = []) \<Longrightarrow>
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST nt c_1)), (admininstr_sc1 (admininstr_st1_CONST nt c_2)), (admininstr_sc1 (admininstr_st1_BINOP nt binop))] [(admininstr_sc7 admininstr_st7_TRAP)]"
	| Step_pure__testop :
		"(c = (fun_testop_underscore nt testop c_1)) \<Longrightarrow>
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST nt c_1)), (admininstr_sc1 (admininstr_st1_TESTOP nt testop))] [(admininstr_sc1 (admininstr_st1_CONST I32 c))]"
	| Step_pure__relop :
		"(fun_relop_underscore nt relop c_1 c_2 var_0) \<Longrightarrow>
		 (c = var_0) \<Longrightarrow>
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST nt c_1)), (admininstr_sc1 (admininstr_st1_CONST nt c_2)), (admininstr_sc1 (admininstr_st1_RELOP nt relop))] [(admininstr_sc1 (admininstr_st1_CONST I32 c))]"
	| cvtop_val :
		"(fun_cvtop__underscore nt_1 nt_2 cvtop c_1 var_0) \<Longrightarrow>
		 ((length var_0) > 0) \<Longrightarrow>
		 (c \<in> set var_0) \<Longrightarrow>
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST nt_1 c_1)), (admininstr_sc2 (admininstr_st2_CVTOP nt_2 nt_1 cvtop))] [(admininstr_sc1 (admininstr_st1_CONST nt_2 c))]"
	| cvtop_trap :
		"(fun_cvtop__underscore nt_1 nt_2 cvtop c_1 var_0) \<Longrightarrow>
		 (var_0 = []) \<Longrightarrow>
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST nt_1 c_1)), (admininstr_sc2 (admininstr_st2_CVTOP nt_2 nt_1 cvtop))] [(admininstr_sc7 admininstr_st7_TRAP)]"
	| ref_is_null_true :
		"(v_ref = (ref_REF_NULL rt)) \<Longrightarrow>
		 Step_pure [(admininstr_ref v_ref), (admininstr_sc4 admininstr_st4_REF_IS_NULL)] [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN 1))))]"
	| ref_is_null_false :
		"(~(Step_pure_before_ref_is_null_false [(admininstr_ref v_ref), (admininstr_sc4 admininstr_st4_REF_IS_NULL)])) \<Longrightarrow>
		 Step_pure [(admininstr_ref v_ref), (admininstr_sc4 admininstr_st4_REF_IS_NULL)] [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0))))]"
	| Step_pure__vvunop :
		"(c = (vvunop_underscore V128 v_vvunop c_1)) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VVUNOP V128 v_vvunop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vvbinop :
		"(c = (vvbinop_underscore V128 v_vvbinop c_1 c_2)) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc2 (admininstr_st2_VVBINOP V128 v_vvbinop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vvternop :
		"(c = (vvternop_underscore V128 v_vvternop c_1 c_2 c_3)) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_3)), (admininstr_sc2 (admininstr_st2_VVTERNOP V128 v_vvternop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vvtestop :
		"((proj_num__0 c) \<noteq> None) \<Longrightarrow>
		 ((size valtype_V128) \<noteq> None) \<Longrightarrow>
		 ((the ((proj_num__0 c))) = (ine_underscore (the ((size valtype_V128))) c_1 (mk_uN 0))) \<Longrightarrow>
		 (wf_uN 128 (mk_uN 0)) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VVTESTOP V128 ANY_TRUE))] [(admininstr_sc1 (admininstr_st1_CONST I32 c))]"
	| Step_pure__vunop :
		"(fun_vunop_underscore sh vunop c_1 var_0) \<Longrightarrow>
		 ((length var_0) > 0) \<Longrightarrow>
		 (c \<in> set var_0) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VUNOP sh vunop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vunop_trap :
		"(fun_vunop_underscore sh vunop c_1 var_0) \<Longrightarrow>
		 (var_0 = []) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VUNOP sh vunop))] [(admininstr_sc7 admininstr_st7_TRAP)]"
	| vbinop_val :
		"(fun_vbinop_underscore sh vbinop c_1 c_2 var_0) \<Longrightarrow>
		 ((length var_0) > 0) \<Longrightarrow>
		 (c \<in> set var_0) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc2 (admininstr_st2_VBINOP sh vbinop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vbinop_trap :
		"(fun_vbinop_underscore sh vbinop c_1 c_2 var_0) \<Longrightarrow>
		 (var_0 = []) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc2 (admininstr_st2_VBINOP sh vbinop))] [(admininstr_sc7 admininstr_st7_TRAP)]"
	| vtestop_true :
		"(ci_1_lst = (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c)) \<Longrightarrow>
		 list_all (\<lambda> (ci_1 :: lane_underscore). ((proj_lane__2 ci_1) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_1 :: lane_underscore). ((proj_uN_0 (the ((proj_lane__2 ci_1)))) \<noteq> 0)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_1 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) ci_1)) ci_1_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc3 (admininstr_st3_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (mk_vtestop__0 v_Jnn v_N ALL_TRUE)))] [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN 1))))]"
	| vtestop_false :
		"(~(Step_pure_before_vtestop_false [(admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc3 (admininstr_st3_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (mk_vtestop__0 v_Jnn v_N ALL_TRUE)))])) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc3 (admininstr_st3_VTESTOP (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (mk_vtestop__0 v_Jnn v_N ALL_TRUE)))] [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0))))]"
	| Step_pure__vrelop :
		"(fun_vrelop_underscore sh vrelop c_1 c_2 var_0) \<Longrightarrow>
		 (var_0 = c) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc3 (admininstr_st3_VRELOP sh vrelop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vshiftop :
		"((length var_0_lst) = (length c'_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (var_0 :: lane_underscore) (c' :: lane_underscore). (fun_vshiftop_underscore (ishape_X v_Jnn (mk_dim v_N)) vshiftop c' (mk_uN v_n) var_0)) var_0_lst c'_lst \<Longrightarrow>
		 (c'_lst = (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c_1)) \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) var_0_lst)) \<Longrightarrow>
		 list_all (\<lambda> (c' :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) c')) c'_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) \<Longrightarrow>
		 (wf_ishape (ishape_X v_Jnn (mk_dim v_N))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN v_n)) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc3 (admininstr_st3_VSHIFTOP (ishape_X v_Jnn (mk_dim v_N)) vshiftop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vbitmask :
		"((length var_0_lst) = (length ci_1_lst)) \<Longrightarrow>
		 list_all (\<lambda> (ci_1 :: lane_underscore). ((proj_lane__2 ci_1) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 list_all2 (\<lambda> (var_0 :: uN) (ci_1 :: lane_underscore). (fun_ilt_underscore (lsize (lanetype_Jnn v_Jnn)) S (the ((proj_lane__2 ci_1))) (mk_uN 0) var_0)) var_0_lst ci_1_lst \<Longrightarrow>
		 (ci_1_lst = (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) c)) \<Longrightarrow>
		 ((ibits_underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) ci) = ((map (\<lambda> (var_0 :: uN). (mk_bit (proj_uN_0 var_0))) var_0_lst) @ (repeat (((32 :: nat) - (v_N :: nat)) :: nat) (mk_bit 0)))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) \<Longrightarrow>
		 list_all (\<lambda> (var_0 :: uN). (wf_bit (mk_bit (proj_uN_0 var_0)))) var_0_lst \<Longrightarrow>
		 (wf_bit (mk_bit 0)) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc3 (admininstr_st3_VBITMASK (ishape_X v_Jnn (mk_dim v_N))))] [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (irev_underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) ci))))]"
	| Step_pure__vswizzle :
		"(ci_lst = (lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_M)) c_2)) \<Longrightarrow>
		 list_all (\<lambda> (iter_0 :: lane_underscore). ((proj_lane__1 iter_0) \<noteq> None)) (lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_M)) c_1) \<Longrightarrow>
		 (c'_lst = ((map (\<lambda> (iter_0 :: lane_underscore). (the ((proj_lane__1 iter_0)))) (lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_M)) c_1)) @ (repeat (((256 :: nat) - (v_M :: nat)) :: nat) (mk_uN 0)))) \<Longrightarrow>
		 holds_upto (\<lambda> k. ((proj_uN_0 (the ((proj_lane__1 (ci_lst ! k))))) < (length c'_lst))) v_M \<Longrightarrow>
		 holds_upto (\<lambda> k. ((proj_lane__1 (ci_lst ! k)) \<noteq> None)) v_M \<Longrightarrow>
		 holds_upto (\<lambda> k. (k < (length ci_lst))) v_M \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_M)) (mkseq (\<lambda> k. (mk_lane__1 v_Pnn (c'_lst ! (proj_uN_0 (the ((proj_lane__1 (ci_lst ! k)))))))) v_M))) \<Longrightarrow>
		 (wf_shape (X (lanetype_packtype v_Pnn) (mk_dim v_M))) \<Longrightarrow>
		 (wf_uN (psize v_Pnn) (mk_uN 0)) \<Longrightarrow>
		 holds_upto (\<lambda> k. (wf_lane_underscore (fun_lanetype (X (lanetype_packtype v_Pnn) (mk_dim v_M))) (mk_lane__1 v_Pnn (c'_lst ! (proj_uN_0 (the ((proj_lane__1 (ci_lst ! k))))))))) v_M \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc3 (admininstr_st3_VSWIZZLE (ishape_X (Jnn_packtype v_Pnn) (mk_dim v_M))))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vshuffle :
		"((map (\<lambda> (c' :: iN). (mk_lane__1 v_Pnn c')) c'_lst) = ((lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_N)) c_1) @ (lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_N)) c_2))) \<Longrightarrow>
		 holds_upto (\<lambda> k. ((proj_uN_0 (i_lst ! k)) < (length c'_lst))) v_N \<Longrightarrow>
		 holds_upto (\<lambda> k. (k < (length i_lst))) v_N \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_packtype v_Pnn) (mk_dim v_N)) (mkseq (\<lambda> k. (mk_lane__1 v_Pnn (c'_lst ! (proj_uN_0 (i_lst ! k))))) v_N))) \<Longrightarrow>
		 list_all (\<lambda> (c' :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_packtype v_Pnn) (mk_dim v_N))) (mk_lane__1 v_Pnn c'))) c'_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_packtype v_Pnn) (mk_dim v_N))) \<Longrightarrow>
		 holds_upto (\<lambda> k. (wf_lane_underscore (fun_lanetype (X (lanetype_packtype v_Pnn) (mk_dim v_N))) (mk_lane__1 v_Pnn (c'_lst ! (proj_uN_0 (i_lst ! k)))))) v_N \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc3 (admininstr_st3_VSHUFFLE (ishape_X (Jnn_packtype v_Pnn) (mk_dim v_N)) i_lst))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vsplat :
		"(c = (inv_lanes_underscore (X v_Lnn (mk_dim v_N)) (repeat v_N (packnum_underscore v_Lnn c_1)))) \<Longrightarrow>
		 (wf_shape (X v_Lnn (mk_dim v_N))) \<Longrightarrow>
		 Step_pure [(admininstr_sc1 (admininstr_st1_CONST (unpack v_Lnn) c_1)), (admininstr_sc3 (admininstr_st3_VSPLAT (X v_Lnn (mk_dim v_N))))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vextract_lane_num :
		"((proj_uN_0 i) < (length (lanes_underscore (X (lanetype_numtype nt) (mk_dim v_N)) c_1))) \<Longrightarrow>
		 ((mk_lane__0 nt c_2) = ((lanes_underscore (X (lanetype_numtype nt) (mk_dim v_N)) c_1) ! (proj_uN_0 i))) \<Longrightarrow>
		 (wf_lane_underscore (fun_lanetype (X (lanetype_numtype nt) (mk_dim v_N))) (mk_lane__0 nt c_2)) \<Longrightarrow>
		 (wf_shape (X (lanetype_numtype nt) (mk_dim v_N))) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc3 (admininstr_st3_VEXTRACT_LANE (X (lanetype_numtype nt) (mk_dim v_N)) None i))] [(admininstr_sc1 (admininstr_st1_CONST nt c_2))]"
	| vextract_lane_pack :
		"((proj_num__0 c_2) \<noteq> None) \<Longrightarrow>
		 ((proj_lane__1 ((lanes_underscore (X (lanetype_packtype pt) (mk_dim v_N)) c_1) ! (proj_uN_0 i))) \<noteq> None) \<Longrightarrow>
		 ((proj_uN_0 i) < (length (lanes_underscore (X (lanetype_packtype pt) (mk_dim v_N)) c_1))) \<Longrightarrow>
		 ((the ((proj_num__0 c_2))) = (extend__underscore (psize pt) (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) v_sx (the ((proj_lane__1 ((lanes_underscore (X (lanetype_packtype pt) (mk_dim v_N)) c_1) ! (proj_uN_0 i))))))) \<Longrightarrow>
		 (wf_shape (X (lanetype_packtype pt) (mk_dim v_N))) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc3 (admininstr_st3_VEXTRACT_LANE (X (lanetype_packtype pt) (mk_dim v_N)) (Some v_sx) i))] [(admininstr_sc1 (admininstr_st1_CONST I32 c_2))]"
	| Step_pure__vreplace_lane :
		"(c = (inv_lanes_underscore (X v_Lnn (mk_dim v_N)) (list_update_func (lanes_underscore (X v_Lnn (mk_dim v_N)) c_1) (proj_uN_0 i) (\<lambda> (underscore_underscore :: lane_underscore). (packnum_underscore v_Lnn c_2))))) \<Longrightarrow>
		 (wf_shape (X v_Lnn (mk_dim v_N))) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc1 (admininstr_st1_CONST (unpack v_Lnn) c_2)), (admininstr_sc3 (admininstr_st3_VREPLACE_LANE (X v_Lnn (mk_dim v_N)) i))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vextunop :
		"(fun_vextunop__underscore sh_1 sh_2 vextunop c_1 var_0) \<Longrightarrow>
		 (var_0 = c) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc4 (admininstr_st4_VEXTUNOP sh_1 sh_2 vextunop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vextbinop :
		"(fun_vextbinop__underscore sh_1 sh_2 vextbinop c_1 c_2 var_0) \<Longrightarrow>
		 (var_0 = c) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc4 (admininstr_st4_VEXTBINOP sh_1 sh_2 vextbinop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__vnarrow :
		"(ci_1_lst = (lanes_underscore (X (lanetype_Jnn Jnn_1) (mk_dim N_1)) c_1)) \<Longrightarrow>
		 (ci_2_lst = (lanes_underscore (X (lanetype_Jnn Jnn_1) (mk_dim N_1)) c_2)) \<Longrightarrow>
		 list_all (\<lambda> (ci_1 :: lane_underscore). ((proj_lane__2 ci_1) \<noteq> None)) ci_1_lst \<Longrightarrow>
		 (cj_1_lst = (map (\<lambda> (ci_1 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_1)) (lsize (lanetype_Jnn Jnn_2)) v_sx (the ((proj_lane__2 ci_1))))) ci_1_lst)) \<Longrightarrow>
		 list_all (\<lambda> (ci_2 :: lane_underscore). ((proj_lane__2 ci_2) \<noteq> None)) ci_2_lst \<Longrightarrow>
		 (cj_2_lst = (map (\<lambda> (ci_2 :: lane_underscore). (narrow__underscore (lsize (lanetype_Jnn Jnn_1)) (lsize (lanetype_Jnn Jnn_2)) v_sx (the ((proj_lane__2 ci_2))))) ci_2_lst)) \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_Jnn Jnn_2) (mk_dim N_2)) ((map (\<lambda> (cj_1 :: iN). (mk_lane__2 Jnn_2 cj_1)) cj_1_lst) @ (map (\<lambda> (cj_2 :: iN). (mk_lane__2 Jnn_2 cj_2)) cj_2_lst)))) \<Longrightarrow>
		 list_all (\<lambda> (ci_1 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_1) (mk_dim N_1))) ci_1)) ci_1_lst \<Longrightarrow>
		 list_all (\<lambda> (ci_2 :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_1) (mk_dim N_1))) ci_2)) ci_2_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_1) (mk_dim N_1))) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn Jnn_2) (mk_dim N_2))) \<Longrightarrow>
		 list_all (\<lambda> (cj_1 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_2) (mk_dim N_2))) (mk_lane__2 Jnn_2 cj_1))) cj_1_lst \<Longrightarrow>
		 list_all (\<lambda> (cj_2 :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn Jnn_2) (mk_dim N_2))) (mk_lane__2 Jnn_2 cj_2))) cj_2_lst \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_2)), (admininstr_sc4 (admininstr_st4_VNARROW (ishape_X Jnn_2 (mk_dim N_2)) (ishape_X Jnn_1 (mk_dim N_1)) v_sx))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vcvtop_full :
		"(((halfop v_vcvtop) = None) \<and> ((zeroop v_vcvtop) = None)) \<Longrightarrow>
		 (ci_lst = (lanes_underscore (X Lnn_1 (mk_dim v_M)) c_1)) \<Longrightarrow>
		 (cj_lst_lst = (setproduct_underscore  (map (\<lambda> (ci :: lane_underscore). (vcvtop__underscore (X Lnn_1 (mk_dim v_M)) (X Lnn_2 (mk_dim v_M)) v_vcvtop ci)) ci_lst))) \<Longrightarrow>
		 ((length (map (\<lambda> (cj_lst :: (lane_underscore list)). (inv_lanes_underscore (X Lnn_2 (mk_dim v_M)) cj_lst)) cj_lst_lst)) > 0) \<Longrightarrow>
		 (c \<in> set (map (\<lambda> (cj_lst :: (lane_underscore list)). (inv_lanes_underscore (X Lnn_2 (mk_dim v_M)) cj_lst)) cj_lst_lst)) \<Longrightarrow>
		 list_all (\<lambda> (ci :: lane_underscore). (wf_lane_underscore (fun_lanetype (X Lnn_1 (mk_dim v_M))) ci)) ci_lst \<Longrightarrow>
		 list_all (\<lambda> (cj_lst :: (lane_underscore list)). list_all (\<lambda> (cj :: lane_underscore). (wf_lane_underscore Lnn_2 cj)) cj_lst) cj_lst_lst \<Longrightarrow>
		 (wf_shape (X Lnn_1 (mk_dim v_M))) \<Longrightarrow>
		 (wf_shape (X Lnn_2 (mk_dim v_M))) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc4 (admininstr_st4_VCVTOP (X Lnn_2 (mk_dim v_M)) (X Lnn_1 (mk_dim v_M)) v_vcvtop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vcvtop_half :
		"((halfop v_vcvtop) = (Some v_half)) \<Longrightarrow>
		 (ci_lst = (list_slice (lanes_underscore (X Lnn_1 (mk_dim M_1)) c_1) (fun_half v_half 0 M_2) M_2)) \<Longrightarrow>
		 (cj_lst_lst = (setproduct_underscore  (map (\<lambda> (ci :: lane_underscore). (vcvtop__underscore (X Lnn_1 (mk_dim M_1)) (X Lnn_2 (mk_dim M_2)) v_vcvtop ci)) ci_lst))) \<Longrightarrow>
		 ((length (map (\<lambda> (cj_lst :: (lane_underscore list)). (inv_lanes_underscore (X Lnn_2 (mk_dim M_2)) cj_lst)) cj_lst_lst)) > 0) \<Longrightarrow>
		 (c \<in> set (map (\<lambda> (cj_lst :: (lane_underscore list)). (inv_lanes_underscore (X Lnn_2 (mk_dim M_2)) cj_lst)) cj_lst_lst)) \<Longrightarrow>
		 list_all (\<lambda> (ci :: lane_underscore). (wf_lane_underscore (fun_lanetype (X Lnn_1 (mk_dim M_1))) ci)) ci_lst \<Longrightarrow>
		 list_all (\<lambda> (cj_lst :: (lane_underscore list)). list_all (\<lambda> (cj :: lane_underscore). (wf_lane_underscore Lnn_2 cj)) cj_lst) cj_lst_lst \<Longrightarrow>
		 (wf_shape (X Lnn_1 (mk_dim M_1))) \<Longrightarrow>
		 (wf_shape (X Lnn_2 (mk_dim M_2))) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc4 (admininstr_st4_VCVTOP (X Lnn_2 (mk_dim M_2)) (X Lnn_1 (mk_dim M_1)) v_vcvtop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vcvtop_zero :
		"((zeroop v_vcvtop) = (Some ZERO)) \<Longrightarrow>
		 (ci_lst = (lanes_underscore (X (lanetype_numtype nt_1) (mk_dim M_1)) c_1)) \<Longrightarrow>
		 (cj_lst_lst = (setproduct_underscore  ((map (\<lambda> (ci :: lane_underscore). (vcvtop__underscore (X (lanetype_numtype nt_1) (mk_dim M_1)) (X (lanetype_numtype nt_2) (mk_dim M_2)) v_vcvtop ci)) ci_lst) @ (repeat M_1 [(mk_lane__0 nt_2 (fun_zero nt_2))])))) \<Longrightarrow>
		 ((length (map (\<lambda> (cj_lst :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_numtype nt_2) (mk_dim M_2)) cj_lst)) cj_lst_lst)) > 0) \<Longrightarrow>
		 (c \<in> set (map (\<lambda> (cj_lst :: (lane_underscore list)). (inv_lanes_underscore (X (lanetype_numtype nt_2) (mk_dim M_2)) cj_lst)) cj_lst_lst)) \<Longrightarrow>
		 list_all (\<lambda> (ci :: lane_underscore). (wf_lane_underscore (fun_lanetype (X (lanetype_numtype nt_1) (mk_dim M_1))) ci)) ci_lst \<Longrightarrow>
		 list_all (\<lambda> (cj_lst :: (lane_underscore list)). list_all (\<lambda> (cj :: lane_underscore). (wf_lane_underscore (lanetype_numtype nt_2) cj)) cj_lst) cj_lst_lst \<Longrightarrow>
		 (wf_shape (X (lanetype_numtype nt_1) (mk_dim M_1))) \<Longrightarrow>
		 (wf_shape (X (lanetype_numtype nt_2) (mk_dim M_2))) \<Longrightarrow>
		 (wf_lane_underscore (lanetype_numtype nt_2) (mk_lane__0 nt_2 (fun_zero nt_2))) \<Longrightarrow>
		 Step_pure [(admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc4 (admininstr_st4_VCVTOP (X (lanetype_numtype nt_2) (mk_dim M_2)) (X (lanetype_numtype nt_1) (mk_dim M_1)) v_vcvtop))] [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_pure__local_tee :
		"Step_pure [(admininstr_val v_val), (admininstr_sc5 (admininstr_st5_LOCAL_TEE x))] [(admininstr_val v_val), (admininstr_val v_val), (admininstr_sc4 (admininstr_st4_LOCAL_SET x))]"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.10-6.19 *)
lemma Step_pure_is_wf :
	"list_all (\<lambda> (var_0 :: admininstr). (wf_admininstr var_0)) var_0 \<Longrightarrow>
	 (Step_pure var_0 var_1) \<Longrightarrow>
	 list_all (\<lambda> (var_1 :: admininstr). (wf_admininstr var_1)) var_1"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/8-reduction.spectec:63.1-63.73 *)
function (sequential, domintros) fun_blocktype :: "state \<Rightarrow> blocktype \<Rightarrow> functype" where
		  "fun_blocktype z (underscore_RESULT None) = (mk_functype (mk_list []) (mk_list []))"
		| "fun_blocktype z (underscore_RESULT (Some t)) = (mk_functype (mk_list []) (mk_list [t]))"
		| "fun_blocktype z (underscore_IDX x) = (fun_type z x)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:127.1-129.15 *)
inductive Step_read_before_call_indirect_trap :: "config \<Rightarrow> bool" where
	  call_indirect_call_0 :
		"((proj_uN_0 (the ((proj_num__0 i)))) < (length (REFS (fun_table z x)))) \<Longrightarrow>
		 ((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 (((REFS (fun_table z x)) ! (proj_uN_0 (the ((proj_num__0 i))))) = (REF_FUNC_ADDR a)) \<Longrightarrow>
		 (a < (length (fun_funcinst z))) \<Longrightarrow>
		 ((fun_type z y) = (funcinst_TYPE ((fun_funcinst z) ! a))) \<Longrightarrow>
		 Step_read_before_call_indirect_trap (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y))])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:436.1-439.14 *)
inductive Step_read_before_table_fill_zero :: "config \<Rightarrow> bool" where
	  table_fill_trap_0 :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (REFS (fun_table z x)))) \<Longrightarrow>
		 Step_read_before_table_fill_zero (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_FILL x))])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:452.1-455.14 *)
inductive Step_read_before_table_copy_zero :: "config \<Rightarrow> bool" where
	  table_copy_trap_0 :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (REFS (fun_table z y)))) \<or> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (REFS (fun_table z x))))) \<Longrightarrow>
		 Step_read_before_table_copy_zero (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:457.1-462.15 *)
inductive Step_read_before_table_copy_le :: "config \<Rightarrow> bool" where
	  table_copy_zero_0 :
		"(~(Step_read_before_table_copy_zero (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))]))) \<Longrightarrow>
		 (v_n = 0) \<Longrightarrow>
		 Step_read_before_table_copy_le (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))])"
	| table_copy_trap_1 :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (REFS (fun_table z y)))) \<or> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (REFS (fun_table z x))))) \<Longrightarrow>
		 Step_read_before_table_copy_le (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:475.1-478.14 *)
inductive Step_read_before_table_init_zero :: "config \<Rightarrow> bool" where
	  table_init_trap_0 :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (eleminst_REFS (fun_elem z y)))) \<or> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (REFS (fun_table z x))))) \<Longrightarrow>
		 Step_read_before_table_init_zero (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc6 (admininstr_st6_TABLE_INIT x y))])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:616.1-619.14 *)
inductive Step_read_before_memory_fill_zero :: "config \<Rightarrow> bool" where
	  memory_fill_trap_0 :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read_before_memory_fill_zero (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_FILL)])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:632.1-635.14 *)
inductive Step_read_before_memory_copy_zero :: "config \<Rightarrow> bool" where
	  memory_copy_trap_0 :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0))))) \<or> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0)))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read_before_memory_copy_zero (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:637.1-642.15 *)
inductive Step_read_before_memory_copy_le :: "config \<Rightarrow> bool" where
	  memory_copy_zero_0 :
		"(~(Step_read_before_memory_copy_zero (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)]))) \<Longrightarrow>
		 (v_n = 0) \<Longrightarrow>
		 Step_read_before_memory_copy_le (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)])"
	| memory_copy_trap_1 :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0))))) \<or> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0)))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read_before_memory_copy_le (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:655.1-658.14 *)
inductive Step_read_before_memory_init_zero :: "config \<Rightarrow> bool" where
	  memory_init_trap_0 :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (datainst_BYTES (fun_data z x)))) \<or> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0)))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read_before_memory_init_zero (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 (admininstr_st7_MEMORY_INIT x))])"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:7.1-7.109 *)
inductive Step_read :: "config \<Rightarrow> (admininstr list) \<Rightarrow> bool" where
	  Step_read__block :
		"((fun_blocktype z bt) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (k = (length val_lst)) \<Longrightarrow>
		 (k = (length t_1_lst)) \<Longrightarrow>
		 (v_n = (length t_2_lst)) \<Longrightarrow>
		 Step_read (mk_config z ((map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_sc0 (admininstr_st0_BLOCK bt instr_lst))])) [(admininstr_sc8 (LABEL_underscore v_n [] ((map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst) @ (map (\<lambda> (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))))]"
	| Step_read__loop :
		"((fun_blocktype z bt) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (k = (length val_lst)) \<Longrightarrow>
		 (k = (length t_1_lst)) \<Longrightarrow>
		 (v_n = (length t_2_lst)) \<Longrightarrow>
		 Step_read (mk_config z ((map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_sc0 (admininstr_st0_LOOP bt instr_lst))])) [(admininstr_sc8 (LABEL_underscore k [(instr_sc7 (LOOP bt instr_lst))] ((map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst) @ (map (\<lambda> (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))))]"
	| Step_read__call :
		"((proj_uN_0 x) < (length (fun_funcaddr z))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CALL x))]) [(admininstr_sc7 (CALL_ADDR ((fun_funcaddr z) ! (proj_uN_0 x))))]"
	| call_indirect_call :
		"((proj_uN_0 (the ((proj_num__0 i)))) < (length (REFS (fun_table z x)))) \<Longrightarrow>
		 ((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 (((REFS (fun_table z x)) ! (proj_uN_0 (the ((proj_num__0 i))))) = (REF_FUNC_ADDR a)) \<Longrightarrow>
		 (a < (length (fun_funcinst z))) \<Longrightarrow>
		 ((fun_type z y) = (funcinst_TYPE ((fun_funcinst z) ! a))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y))]) [(admininstr_sc7 (CALL_ADDR a))]"
	| call_indirect_trap :
		"(~(Step_read_before_call_indirect_trap (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y))]))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CALL_INDIRECT x y))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| call_addr :
		"(a < (length (fun_funcinst z))) \<Longrightarrow>
		 (((fun_funcinst z) ! a) = \<lparr> funcinst_TYPE = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst)), funcinst_MODULE = mm, CODE = v_func \<rparr>) \<Longrightarrow>
		 (v_func = (func_FUNC x (map (\<lambda> (t :: valtype). (LOCAL t)) t_lst) instr_lst)) \<Longrightarrow>
		 list_all (\<lambda> (t :: valtype). ((default_underscore t) \<noteq> None)) t_lst \<Longrightarrow>
		 (f = \<lparr> LOCALS = (val_lst @ (map (\<lambda> (t :: valtype). (the ((default_underscore t)))) t_lst)), frame_MODULE = mm \<rparr>) \<Longrightarrow>
		 (wf_funcinst \<lparr> funcinst_TYPE = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst)), funcinst_MODULE = mm, CODE = v_func \<rparr>) \<Longrightarrow>
		 (wf_func (func_FUNC x (map (\<lambda> (t :: valtype). (LOCAL t)) t_lst) instr_lst)) \<Longrightarrow>
		 (wf_frame \<lparr> LOCALS = (val_lst @ (map (\<lambda> (t :: valtype). (the ((default_underscore t)))) t_lst)), frame_MODULE = mm \<rparr>) \<Longrightarrow>
		 (k = (length val_lst)) \<Longrightarrow>
		 (k = (length t_1_lst)) \<Longrightarrow>
		 (v_n = (length t_2_lst)) \<Longrightarrow>
		 Step_read (mk_config z ((map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_sc7 (CALL_ADDR a))])) [(admininstr_sc8 (FRAME_underscore v_n f [(admininstr_sc8 (LABEL_underscore v_n [] (map (\<lambda> (v_instr :: instr). (admininstr_instr v_instr)) instr_lst)))]))]"
	| Step_read__ref_func :
		"((proj_uN_0 x) < (length (fun_funcaddr z))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc4 (admininstr_st4_REF_FUNC x))]) [(admininstr_sc7 (admininstr_st7_REF_FUNC_ADDR ((fun_funcaddr z) ! (proj_uN_0 x))))]"
	| Step_read__local_get :
		"Step_read (mk_config z [(admininstr_sc4 (admininstr_st4_LOCAL_GET x))]) [(admininstr_val (fun_local z x))]"
	| Step_read__global_get :
		"Step_read (mk_config z [(admininstr_sc5 (admininstr_st5_GLOBAL_GET x))]) [(admininstr_val (VALUE (fun_global z x)))]"
	| table_get_trap :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_uN_0 (the ((proj_num__0 i)))) \<ge> (length (REFS (fun_table z x)))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc5 (admininstr_st5_TABLE_GET x))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| table_get_val :
		"((proj_uN_0 (the ((proj_num__0 i)))) < (length (REFS (fun_table z x)))) \<Longrightarrow>
		 ((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc5 (admininstr_st5_TABLE_GET x))]) [(admininstr_ref ((REFS (fun_table z x)) ! (proj_uN_0 (the ((proj_num__0 i))))))]"
	| Step_read__table_size :
		"((length (REFS (fun_table z x))) = v_n) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc5 (admininstr_st5_TABLE_SIZE x))]) [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))))]"
	| table_fill_trap :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (REFS (fun_table z x)))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_FILL x))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| table_fill_zero :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) \<le> (length (REFS (fun_table z x)))) \<Longrightarrow>
		 (v_n = 0) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_FILL x))]) []"
	| table_fill_succ :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 (v_n \<noteq> 0) \<Longrightarrow>
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) \<le> (length (REFS (fun_table z x)))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_FILL x))]) [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc5 (admininstr_st5_TABLE_SET x)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc5 (admininstr_st5_TABLE_FILL x))]"
	| table_copy_trap :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (REFS (fun_table z y)))) \<or> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (REFS (fun_table z x))))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| table_copy_zero :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) \<le> (length (REFS (fun_table z y)))) \<and> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) \<le> (length (REFS (fun_table z x))))) \<Longrightarrow>
		 (v_n = 0) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))]) []"
	| table_copy_le :
		"((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 (v_n \<noteq> 0) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) \<le> (length (REFS (fun_table z y)))) \<and> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) \<le> (length (REFS (fun_table z x))))) \<Longrightarrow>
		 ((proj_uN_0 (the ((proj_num__0 j)))) \<le> (proj_uN_0 (the ((proj_num__0 i))))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))]) [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc5 (admininstr_st5_TABLE_GET y)), (admininstr_sc5 (admininstr_st5_TABLE_SET x)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 j)))) + 1))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))]"
	| table_copy_gt :
		"((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_uN_0 (the ((proj_num__0 j)))) > (proj_uN_0 (the ((proj_num__0 i))))) \<Longrightarrow>
		 (v_n \<noteq> 0) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) \<le> (length (REFS (fun_table z y)))) \<and> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) \<le> (length (REFS (fun_table z x))))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))]) [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((((proj_uN_0 (the ((proj_num__0 j)))) + v_n) :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc5 (admininstr_st5_TABLE_GET y)), (admininstr_sc5 (admininstr_st5_TABLE_SET x)), (admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc5 (admininstr_st5_TABLE_COPY x y))]"
	| table_init_trap :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (eleminst_REFS (fun_elem z y)))) \<or> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (REFS (fun_table z x))))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc6 (admininstr_st6_TABLE_INIT x y))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| table_init_zero :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) \<le> (length (eleminst_REFS (fun_elem z y)))) \<and> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) \<le> (length (REFS (fun_table z x))))) \<Longrightarrow>
		 (v_n = 0) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc6 (admininstr_st6_TABLE_INIT x y))]) []"
	| table_init_succ :
		"((proj_uN_0 (the ((proj_num__0 i)))) < (length (eleminst_REFS (fun_elem z y)))) \<Longrightarrow>
		 ((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 (v_n \<noteq> 0) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) \<le> (length (eleminst_REFS (fun_elem z y)))) \<and> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) \<le> (length (REFS (fun_table z x))))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc6 (admininstr_st6_TABLE_INIT x y))]) [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_ref ((eleminst_REFS (fun_elem z y)) ! (proj_uN_0 (the ((proj_num__0 i)))))), (admininstr_sc5 (admininstr_st5_TABLE_SET x)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 j)))) + 1))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc6 (admininstr_st6_TABLE_INIT x y))]"
	| load_num_trap :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((size (valtype_numtype nt)) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((the ((size (valtype_numtype nt)))) :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_LOAD nt None ao))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| load_num_val :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((size (valtype_numtype nt)) \<noteq> None) \<Longrightarrow>
		 ((nbytes_underscore nt c) = (list_slice (BYTES (fun_mem z (mk_uN 0))) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) ((((the ((size (valtype_numtype nt)))) :: nat) div (8 :: nat)) :: nat))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_LOAD nt None ao))]) [(admininstr_sc1 (admininstr_st1_CONST nt c))]"
	| load_pack_trap :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + (((v_n :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_LOAD (numtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) ao))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| load_pack_val :
		"((size (valtype_Inn v_Inn)) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((ibytes_underscore v_n c) = (list_slice (BYTES (fun_mem z (mk_uN 0))) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_n :: nat) div (8 :: nat)) :: nat))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_LOAD (numtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) ao))]) [(admininstr_sc1 (admininstr_st1_CONST (numtype_Inn v_Inn) (mk_num__0 v_Inn (extend__underscore v_n (the ((size (valtype_Inn v_Inn)))) v_sx c))))]"
	| vload_oob :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((size valtype_V128) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((the ((size valtype_V128))) :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_VLOAD V128 None ao))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| vload_val :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((size valtype_V128) \<noteq> None) \<Longrightarrow>
		 ((vbytes_underscore V128 c) = (list_slice (BYTES (fun_mem z (mk_uN 0))) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) ((((the ((size valtype_V128))) :: nat) div (8 :: nat)) :: nat))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_VLOAD V128 None ao))]) [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vload_shape_oob :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((v_M * v_N) :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SHAPEX_underscore v_M v_N v_sx)) ao))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| vload_shape_val :
		"holds_upto (\<lambda> k. ((proj_num__0 i) \<noteq> None)) v_N \<Longrightarrow>
		 list_alli (\<lambda> k (j :: iN). ((ibytes_underscore v_M j) = (list_slice (BYTES (fun_mem z (mk_uN 0))) (((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((k * v_M) :: nat) div (8 :: nat)) :: nat)) (((v_M :: nat) div (8 :: nat)) :: nat)))) j_lst \<Longrightarrow>
		 ((jsize v_Jnn) = (v_M * 2)) \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_N)) (map (\<lambda> (j :: iN). (mk_lane__2 v_Jnn (extend__underscore v_M (jsize v_Jnn) v_sx j))) j_lst))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) \<Longrightarrow>
		 list_all (\<lambda> (j :: iN). (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_N))) (mk_lane__2 v_Jnn (extend__underscore v_M (jsize v_Jnn) v_sx j)))) j_lst \<Longrightarrow>
		 (v_N = (length j_lst)) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SHAPEX_underscore v_M v_N v_sx)) ao))]) [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vload_splat_oob :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + (((v_N :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SPLAT v_N)) ao))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| vload_splat_val :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((ibytes_underscore v_N j) = (list_slice (BYTES (fun_mem z (mk_uN 0))) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_N :: nat) div (8 :: nat)) :: nat))) \<Longrightarrow>
		 (v_N = (jsize v_Jnn)) \<Longrightarrow>
		 ((v_M :: nat) = ((128 :: nat) div (v_N :: nat))) \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) (repeat v_M (mk_lane__2 v_Jnn (mk_uN (proj_uN_0 j)))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) \<Longrightarrow>
		 (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_lane__2 v_Jnn (mk_uN (proj_uN_0 j)))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (SPLAT v_N)) ao))]) [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vload_zero_oob :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + (((v_N :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (vloadop_ZERO v_N)) ao))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| vload_zero_val :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((ibytes_underscore v_N j) = (list_slice (BYTES (fun_mem z (mk_uN 0))) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_N :: nat) div (8 :: nat)) :: nat))) \<Longrightarrow>
		 (c = (extend__underscore v_N (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) U j)) \<Longrightarrow>
		 (wf_uN v_N j) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_VLOAD V128 (Some (vloadop_ZERO v_N)) ao))]) [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| vload_lane_oob :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + (((v_N :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc6 (admininstr_st6_VLOAD_LANE V128 (mk_sz v_N) ao j))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| vload_lane_val :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((ibytes_underscore v_N k) = (list_slice (BYTES (fun_mem z (mk_uN 0))) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_N :: nat) div (8 :: nat)) :: nat))) \<Longrightarrow>
		 (v_N = (jsize v_Jnn)) \<Longrightarrow>
		 ((v_M :: nat) = ((128 :: nat) div (v_N :: nat))) \<Longrightarrow>
		 (c = (inv_lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) (list_update_func (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c_1) (proj_uN_0 j) (\<lambda> (underscore_underscore :: lane_underscore). (mk_lane__2 v_Jnn (mk_uN (proj_uN_0 k))))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 (wf_shape (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) \<Longrightarrow>
		 (wf_lane_underscore (fun_lanetype (X (lanetype_Jnn v_Jnn) (mk_dim v_M))) (mk_lane__2 v_Jnn (mk_uN (proj_uN_0 k)))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc2 (admininstr_st2_VCONST V128 c_1)), (admininstr_sc6 (admininstr_st6_VLOAD_LANE V128 (mk_sz v_N) ao j))]) [(admininstr_sc2 (admininstr_st2_VCONST V128 c))]"
	| Step_read__memory_size :
		"(((v_n * 64) * (Ki )) = (length (BYTES (fun_mem z (mk_uN 0))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc6 admininstr_st6_MEMORY_SIZE)]) [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))))]"
	| memory_fill_trap :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_FILL)]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| memory_fill_zero :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) \<le> (length (BYTES (fun_mem z (mk_uN 0))))) \<Longrightarrow>
		 (v_n = 0) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_FILL)]) []"
	| memory_fill_succ :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 (v_n \<noteq> 0) \<Longrightarrow>
		 (((proj_uN_0 (the ((proj_num__0 i)))) + v_n) \<le> (length (BYTES (fun_mem z (mk_uN 0))))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_FILL)]) [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_val v_val), (admininstr_sc6 (admininstr_st6_STORE I32 (Some (mk_sz 8)) (memarg0 ))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (admininstr_val v_val), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc7 admininstr_st7_MEMORY_FILL)]"
	| memory_copy_trap :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0))))) \<or> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0)))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| memory_copy_zero :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) \<le> (length (BYTES (fun_mem z (mk_uN 0))))) \<and> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) \<le> (length (BYTES (fun_mem z (mk_uN 0)))))) \<Longrightarrow>
		 (v_n = 0) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)]) []"
	| memory_copy_le :
		"((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 (v_n \<noteq> 0) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) \<le> (length (BYTES (fun_mem z (mk_uN 0))))) \<and> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) \<le> (length (BYTES (fun_mem z (mk_uN 0)))))) \<Longrightarrow>
		 ((proj_uN_0 (the ((proj_num__0 j)))) \<le> (proj_uN_0 (the ((proj_num__0 i))))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)]) [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc6 (admininstr_st6_LOAD I32 (Some (mk_loadop__0 Inn_I32 (mk_loadop_Inn (mk_sz 8) U))) (memarg0 ))), (admininstr_sc6 (admininstr_st6_STORE I32 (Some (mk_sz 8)) (memarg0 ))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 j)))) + 1))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)]"
	| memory_copy_gt :
		"((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_uN_0 (the ((proj_num__0 j)))) > (proj_uN_0 (the ((proj_num__0 i))))) \<Longrightarrow>
		 (v_n \<noteq> 0) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) \<le> (length (BYTES (fun_mem z (mk_uN 0))))) \<and> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) \<le> (length (BYTES (fun_mem z (mk_uN 0)))))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)]) [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((((proj_uN_0 (the ((proj_num__0 j)))) + v_n) :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc6 (admininstr_st6_LOAD I32 (Some (mk_loadop__0 Inn_I32 (mk_loadop_Inn (mk_sz 8) U))) (memarg0 ))), (admininstr_sc6 (admininstr_st6_STORE I32 (Some (mk_sz 8)) (memarg0 ))), (admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc7 admininstr_st7_MEMORY_COPY)]"
	| memory_init_trap :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) > (length (datainst_BYTES (fun_data z x)))) \<or> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) > (length (BYTES (fun_mem z (mk_uN 0)))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 (admininstr_st7_MEMORY_INIT x))]) [(admininstr_sc7 admininstr_st7_TRAP)]"
	| memory_init_zero :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) \<le> (length (datainst_BYTES (fun_data z x)))) \<and> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) \<le> (length (BYTES (fun_mem z (mk_uN 0)))))) \<Longrightarrow>
		 (v_n = 0) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 (admininstr_st7_MEMORY_INIT x))]) []"
	| memory_init_succ :
		"((proj_uN_0 (the ((proj_num__0 i)))) < (length (datainst_BYTES (fun_data z x)))) \<Longrightarrow>
		 ((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 j) \<noteq> None) \<Longrightarrow>
		 (v_n \<noteq> 0) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + v_n) \<le> (length (datainst_BYTES (fun_data z x)))) \<and> (((proj_uN_0 (the ((proj_num__0 j)))) + v_n) \<le> (length (BYTES (fun_mem z (mk_uN 0)))))) \<Longrightarrow>
		 Step_read (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 (admininstr_st7_MEMORY_INIT x))]) [(admininstr_sc1 (admininstr_st1_CONST I32 j)), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (proj_byte_0 ((datainst_BYTES (fun_data z x)) ! (proj_uN_0 (the ((proj_num__0 i)))))))))), (admininstr_sc6 (admininstr_st6_STORE I32 (Some (mk_sz 8)) (memarg0 ))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 j)))) + 1))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((proj_uN_0 (the ((proj_num__0 i)))) + 1))))), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((v_n :: nat) - (1 :: nat)) :: nat))))), (admininstr_sc7 (admininstr_st7_MEMORY_INIT x))]"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:7.10-7.19 *)
lemma Step_read_is_wf :
	"(wf_config var_0) \<Longrightarrow>
	 (Step_read var_0 var_1) \<Longrightarrow>
	 list_all (\<lambda> (var_1 :: admininstr). (wf_admininstr var_1)) var_1"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/8-reduction.spectec:5.1-5.109 *)
inductive Step :: "config \<Rightarrow> config \<Rightarrow> bool" where
	  pure :
		"(Step_pure admininstr_lst admininstr'_lst) \<Longrightarrow>
		 Step (mk_config z admininstr_lst) (mk_config z admininstr'_lst)"
	| read :
		"(Step_read (mk_config z admininstr_lst) admininstr'_lst) \<Longrightarrow>
		 Step (mk_config z admininstr_lst) (mk_config z admininstr'_lst)"
	| ctxt_label :
		"(Step (mk_config z admininstr_lst) (mk_config z' admininstr'_lst)) \<Longrightarrow>
		 (wf_config (mk_config z admininstr_lst)) \<Longrightarrow>
		 (wf_config (mk_config z' admininstr'_lst)) \<Longrightarrow>
		 Step (mk_config z [(admininstr_sc8 (LABEL_underscore v_n instr_0_lst admininstr_lst))]) (mk_config z' [(admininstr_sc8 (LABEL_underscore v_n instr_0_lst admininstr'_lst))])"
	| ctxt_frame :
		"(Step (mk_config (mk_state s f') admininstr_lst) (mk_config (mk_state s' f'') admininstr'_lst)) \<Longrightarrow>
		 (wf_config (mk_config (mk_state s f') admininstr_lst)) \<Longrightarrow>
		 (wf_config (mk_config (mk_state s' f'') admininstr'_lst)) \<Longrightarrow>
		 Step (mk_config (mk_state s f) [(admininstr_sc8 (FRAME_underscore v_n f' admininstr_lst))]) (mk_config (mk_state s' f) [(admininstr_sc8 (FRAME_underscore v_n f'' admininstr'_lst))])"
	| ctxt_instrs :
		"(Step (mk_config z admininstr_lst) (mk_config z' admininstr'_lst)) \<Longrightarrow>
		 ((val_lst \<noteq> []) \<or> (admininstr_1_lst \<noteq> [])) \<Longrightarrow>
		 (wf_config (mk_config z admininstr_lst)) \<Longrightarrow>
		 (wf_config (mk_config z' admininstr'_lst)) \<Longrightarrow>
		 Step (mk_config z ((map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst) @ (admininstr_lst @ admininstr_1_lst))) (mk_config z' ((map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst) @ (admininstr'_lst @ admininstr_1_lst)))"
	| Step__local_set :
		"Step (mk_config z [(admininstr_val v_val), (admininstr_sc4 (admininstr_st4_LOCAL_SET x))]) (mk_config (with_local z x v_val) [])"
	| Step__global_set :
		"Step (mk_config z [(admininstr_val v_val), (admininstr_sc5 (admininstr_st5_GLOBAL_SET x))]) (mk_config (with_global z x v_val) [])"
	| table_set_trap :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_uN_0 (the ((proj_num__0 i)))) \<ge> (length (REFS (fun_table z x)))) \<Longrightarrow>
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_ref v_ref), (admininstr_sc5 (admininstr_st5_TABLE_SET x))]) (mk_config z [(admininstr_sc7 admininstr_st7_TRAP)])"
	| table_set_val :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((proj_uN_0 (the ((proj_num__0 i)))) < (length (REFS (fun_table z x)))) \<Longrightarrow>
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_ref v_ref), (admininstr_sc5 (admininstr_st5_TABLE_SET x))]) (mk_config (with_table z x (proj_uN_0 (the ((proj_num__0 i)))) v_ref) [])"
	| table_grow_succeed :
		"(fun_growtable (fun_table z x) v_n v_ref var_0) \<Longrightarrow>
		 (var_0 \<noteq> None) \<Longrightarrow>
		 ((the (var_0)) = ti) \<Longrightarrow>
		 Step (mk_config z [(admininstr_ref v_ref), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_GROW x))]) (mk_config (with_tableinst z x ti) [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN (length (REFS (fun_table z x)))))))])"
	| table_grow_fail :
		"(fun_inv_signed_underscore 32 (0 - (1 :: nat)) var_0) \<Longrightarrow>
		 Step (mk_config z [(admininstr_ref v_ref), (admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc5 (admininstr_st5_TABLE_GROW x))]) (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN var_0))))])"
	| Step__elem_drop :
		"Step (mk_config z [(admininstr_sc6 (admininstr_st6_ELEM_DROP x))]) (mk_config (with_elem z x []) [])"
	| store_num_trap :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((size (valtype_numtype nt)) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((the ((size (valtype_numtype nt)))) :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST nt c)), (admininstr_sc6 (admininstr_st6_STORE nt None ao))]) (mk_config z [(admininstr_sc7 admininstr_st7_TRAP)])"
	| store_num_val :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((size (valtype_numtype nt)) \<noteq> None) \<Longrightarrow>
		 (b_lst = (nbytes_underscore nt c)) \<Longrightarrow>
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST nt c)), (admininstr_sc6 (admininstr_st6_STORE nt None ao))]) (mk_config (with_mem z (mk_uN 0) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) ((((the ((size (valtype_numtype nt)))) :: nat) div (8 :: nat)) :: nat) b_lst) [])"
	| store_pack_trap :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + (((v_n :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST (numtype_Inn v_Inn) c)), (admininstr_sc6 (admininstr_st6_STORE (numtype_Inn v_Inn) (Some (mk_sz v_n)) ao))]) (mk_config z [(admininstr_sc7 admininstr_st7_TRAP)])"
	| store_pack_val :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((size (valtype_Inn v_Inn)) \<noteq> None) \<Longrightarrow>
		 ((proj_num__0 c) \<noteq> None) \<Longrightarrow>
		 (b_lst = (ibytes_underscore v_n (wrap__underscore (the ((size (valtype_Inn v_Inn)))) v_n (the ((proj_num__0 c)))))) \<Longrightarrow>
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc1 (admininstr_st1_CONST (numtype_Inn v_Inn) c)), (admininstr_sc6 (admininstr_st6_STORE (numtype_Inn v_Inn) (Some (mk_sz v_n)) ao))]) (mk_config (with_mem z (mk_uN 0) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_n :: nat) div (8 :: nat)) :: nat) b_lst) [])"
	| vstore_oob :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((size valtype_V128) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((the ((size valtype_V128))) :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc6 (admininstr_st6_VSTORE V128 ao))]) (mk_config z [(admininstr_sc7 admininstr_st7_TRAP)])"
	| vstore_val :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((size valtype_V128) \<noteq> None) \<Longrightarrow>
		 (b_lst = (vbytes_underscore V128 c)) \<Longrightarrow>
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc6 (admininstr_st6_VSTORE V128 ao))]) (mk_config (with_mem z (mk_uN 0) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) ((((the ((size valtype_V128))) :: nat) div (8 :: nat)) :: nat) b_lst) [])"
	| vstore_lane_oob :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 ((((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) + v_N) > (length (BYTES (fun_mem z (mk_uN 0))))) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc6 (admininstr_st6_VSTORE_LANE V128 (mk_sz v_N) ao j))]) (mk_config z [(admininstr_sc7 admininstr_st7_TRAP)])"
	| vstore_lane_val :
		"((proj_num__0 i) \<noteq> None) \<Longrightarrow>
		 (v_N = (jsize v_Jnn)) \<Longrightarrow>
		 ((v_M :: nat) = ((128 :: nat) div (v_N :: nat))) \<Longrightarrow>
		 ((proj_lane__2 ((lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c) ! (proj_uN_0 j))) \<noteq> None) \<Longrightarrow>
		 ((proj_uN_0 j) < (length (lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c))) \<Longrightarrow>
		 (b_lst = (ibytes_underscore v_N (mk_uN (proj_uN_0 (the ((proj_lane__2 ((lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c) ! (proj_uN_0 j))))))))) \<Longrightarrow>
		 (wf_uN v_N (mk_uN (proj_uN_0 (the ((proj_lane__2 ((lanes_underscore (X (lanetype_Jnn v_Jnn) (mk_dim v_M)) c) ! (proj_uN_0 j)))))))) \<Longrightarrow>
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 i)), (admininstr_sc2 (admininstr_st2_VCONST V128 c)), (admininstr_sc6 (admininstr_st6_VSTORE_LANE V128 (mk_sz v_N) ao j))]) (mk_config (with_mem z (mk_uN 0) ((proj_uN_0 (the ((proj_num__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_N :: nat) div (8 :: nat)) :: nat) b_lst) [])"
	| memory_grow_succeed :
		"(fun_growmemory (fun_mem z (mk_uN 0)) v_n var_0) \<Longrightarrow>
		 (var_0 \<noteq> None) \<Longrightarrow>
		 ((the (var_0)) = mi) \<Longrightarrow>
		 (wf_uN 32 (mk_uN 0)) \<Longrightarrow>
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_GROW)]) (mk_config (with_meminst z (mk_uN 0) mi) [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN ((((length (BYTES (fun_mem z (mk_uN 0)))) :: nat) div ((64 * (Ki )) :: nat)) :: nat)))))])"
	| memory_grow_fail :
		"(fun_inv_signed_underscore 32 (0 - (1 :: nat)) var_0) \<Longrightarrow>
		 Step (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (admininstr_sc7 admininstr_st7_MEMORY_GROW)]) (mk_config z [(admininstr_sc1 (admininstr_st1_CONST I32 (mk_num__0 Inn_I32 (mk_uN var_0))))])"
	| Step__data_drop :
		"Step (mk_config z [(admininstr_sc7 (admininstr_st7_DATA_DROP x))]) (mk_config (with_data z x []) [])"

(* Mutual Recursion at: ../specification/wasm-2.0/8-reduction.spectec:5.1-5.109 *)
inductive Step_is_wf :: "config \<Rightarrow> config \<Rightarrow> bool" where
	  Step_is_wf_0 :
		"(wf_config var_0) \<Longrightarrow>
		 (Step var_0 var_1) \<Longrightarrow>
		 (wf_config var_1) \<Longrightarrow>
		 Step_is_wf var_0 var_1"

(* Mutual Recursion at: ../specification/wasm-2.0/8-reduction.spectec:8.1-8.77 *)
inductive Steps :: "config \<Rightarrow> config \<Rightarrow> bool" where
	  Steps__refl :
		"(wf_config (mk_config z admininstr_lst)) \<Longrightarrow>
		 Steps (mk_config z admininstr_lst) (mk_config z admininstr_lst)"
	| trans :
		"(Step (mk_config z admininstr_lst) (mk_config z' admininstr'_lst)) \<Longrightarrow>
		 (Steps (mk_config z' admininstr'_lst) (mk_config z'' admininstr''_lst)) \<Longrightarrow>
		 (wf_config (mk_config z admininstr_lst)) \<Longrightarrow>
		 (wf_config (mk_config z'' admininstr''_lst)) \<Longrightarrow>
		 (wf_config (mk_config z' admininstr'_lst)) \<Longrightarrow>
		 Steps (mk_config z admininstr_lst) (mk_config z'' admininstr''_lst)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:29.1-29.83 *)
inductive Eval_expr :: "state \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> (val list) \<Rightarrow> bool" where
	  mk_Eval_expr :
		"(Steps (mk_config z (map (\<lambda> (v_instr :: instr). (admininstr_instr v_instr)) instr_lst)) (mk_config z' (map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst))) \<Longrightarrow>
		 (wf_config (mk_config z (map (\<lambda> (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))) \<Longrightarrow>
		 (wf_config (mk_config z' (map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst))) \<Longrightarrow>
		 Eval_expr z instr_lst z' val_lst"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:5.1-5.36 *)
inductive fun_funcs :: "(externaddr list) \<Rightarrow> (funcaddr list) \<Rightarrow> bool" where
	  fun_funcs_case_0 :
		"fun_funcs [] []"
	| fun_funcs_case_1 :
		"(fun_funcs externaddr'_lst var_0) \<Longrightarrow>
		 fun_funcs ([(externaddr_FUNC fa)] @ externaddr'_lst) ([fa] @ var_0)"
	| fun_funcs_case_2 :
		"(fun_funcs externaddr'_lst var_0) \<Longrightarrow>
		 fun_funcs ([v_externaddr] @ externaddr'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:11.1-11.40 *)
inductive fun_globals :: "(externaddr list) \<Rightarrow> (globaladdr list) \<Rightarrow> bool" where
	  fun_globals_case_0 :
		"fun_globals [] []"
	| fun_globals_case_1 :
		"(fun_globals externaddr'_lst var_0) \<Longrightarrow>
		 fun_globals ([(externaddr_GLOBAL ga)] @ externaddr'_lst) ([ga] @ var_0)"
	| fun_globals_case_2 :
		"(fun_globals externaddr'_lst var_0) \<Longrightarrow>
		 fun_globals ([v_externaddr] @ externaddr'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:17.1-17.38 *)
inductive fun_tables :: "(externaddr list) \<Rightarrow> (tableaddr list) \<Rightarrow> bool" where
	  fun_tables_case_0 :
		"fun_tables [] []"
	| fun_tables_case_1 :
		"(fun_tables externaddr'_lst var_0) \<Longrightarrow>
		 fun_tables ([(externaddr_TABLE ta)] @ externaddr'_lst) ([ta] @ var_0)"
	| fun_tables_case_2 :
		"(fun_tables externaddr'_lst var_0) \<Longrightarrow>
		 fun_tables ([v_externaddr] @ externaddr'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:23.1-23.34 *)
inductive fun_mems :: "(externaddr list) \<Rightarrow> (memaddr list) \<Rightarrow> bool" where
	  fun_mems_case_0 :
		"fun_mems [] []"
	| fun_mems_case_1 :
		"(fun_mems externaddr'_lst var_0) \<Longrightarrow>
		 fun_mems ([(externaddr_MEM ma)] @ externaddr'_lst) ([ma] @ var_0)"
	| fun_mems_case_2 :
		"(fun_mems externaddr'_lst var_0) \<Longrightarrow>
		 fun_mems ([v_externaddr] @ externaddr'_lst) var_0"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:36.6-36.16 *)
inductive fun_allocfunc :: "store \<Rightarrow> moduleinst \<Rightarrow> func \<Rightarrow> (store * funcaddr) \<Rightarrow> bool" where
	  fun_allocfunc_case_0 :
		"((proj_uN_0 x) < (length (TYPES v_moduleinst))) \<Longrightarrow>
		 (fi = \<lparr> funcinst_TYPE = ((TYPES v_moduleinst) ! (proj_uN_0 x)), funcinst_MODULE = v_moduleinst, CODE = v_func \<rparr>) \<Longrightarrow>
		 (v_func = (func_FUNC x local_lst v_expr)) \<Longrightarrow>
		 (wf_funcinst \<lparr> funcinst_TYPE = ((TYPES v_moduleinst) ! (proj_uN_0 x)), funcinst_MODULE = v_moduleinst, CODE = v_func \<rparr>) \<Longrightarrow>
		 (wf_func (func_FUNC x local_lst v_expr)) \<Longrightarrow>
		 fun_allocfunc s v_moduleinst v_func ((s \<lparr> store_FUNCS := ((store_FUNCS s) @ [fi])  \<rparr>), (length (store_FUNCS s)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:36.6-36.16 *)
lemma allocfunc_is_wf :
	"(fun_allocfunc v_store v_moduleinst v_func var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_moduleinst v_moduleinst) \<Longrightarrow>
	 (wf_func v_func) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:41.1-41.63 *)
inductive fun_allocfuncs :: "store \<Rightarrow> moduleinst \<Rightarrow> (func list) \<Rightarrow> (store * (funcaddr list)) \<Rightarrow> bool" where
	  fun_allocfuncs_case_0 :
		"fun_allocfuncs s v_moduleinst [] (s, [])"
	| fun_allocfuncs_case_1 :
		"(fun_allocfuncs s_1 v_moduleinst func'_lst var_1) \<Longrightarrow>
		 (fun_allocfunc s v_moduleinst v_func var_0) \<Longrightarrow>
		 ((s_1, fa) = var_0) \<Longrightarrow>
		 ((s_2, fa'_lst) = var_1) \<Longrightarrow>
		 fun_allocfuncs s v_moduleinst ([v_func] @ func'_lst) (s_2, ([fa] @ fa'_lst))"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:41.1-41.63 *)
inductive allocfuncs_is_wf :: "store \<Rightarrow> moduleinst \<Rightarrow> (func list) \<Rightarrow> (store * (funcaddr list)) \<Rightarrow> bool" where
	  allocfuncs_is_wf_0 :
		"(fun_allocfuncs v_store v_moduleinst var_0_lst var_0) \<Longrightarrow>
		 (wf_store v_store) \<Longrightarrow>
		 (wf_moduleinst v_moduleinst) \<Longrightarrow>
		 list_all (\<lambda> (var_0 :: func). (wf_func var_0)) var_0_lst \<Longrightarrow>
		 (ret_val = var_0) \<Longrightarrow>
		 (wf_store (fst ret_val)) \<Longrightarrow>
		 allocfuncs_is_wf v_store v_moduleinst var_0_lst ret_val"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:47.6-47.18 *)
inductive fun_allocglobal :: "store \<Rightarrow> globaltype \<Rightarrow> val \<Rightarrow> (store * globaladdr) \<Rightarrow> bool" where
	  fun_allocglobal_case_0 :
		"(gi = \<lparr> globalinst_TYPE = v_globaltype, VALUE = v_val \<rparr>) \<Longrightarrow>
		 (wf_globalinst \<lparr> globalinst_TYPE = v_globaltype, VALUE = v_val \<rparr>) \<Longrightarrow>
		 fun_allocglobal s v_globaltype v_val ((s \<lparr> store_GLOBALS := ((store_GLOBALS s) @ [gi])  \<rparr>), (length (store_GLOBALS s)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:47.6-47.18 *)
lemma allocglobal_is_wf :
	"(fun_allocglobal v_store v_globaltype v_val var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_val v_val) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:51.1-51.67 *)
inductive fun_allocglobals :: "store \<Rightarrow> (globaltype list) \<Rightarrow> (val list) \<Rightarrow> (store * (globaladdr list)) \<Rightarrow> bool" where
	  fun_allocglobals_case_0 :
		"fun_allocglobals s [] [] (s, [])"
	| fun_allocglobals_case_1 :
		"(fun_allocglobals s_1 globaltype'_lst val'_lst var_1) \<Longrightarrow>
		 (fun_allocglobal s v_globaltype v_val var_0) \<Longrightarrow>
		 ((s_1, ga) = var_0) \<Longrightarrow>
		 ((s_2, ga'_lst) = var_1) \<Longrightarrow>
		 fun_allocglobals s ([v_globaltype] @ globaltype'_lst) ([v_val] @ val'_lst) (s_2, ([ga] @ ga'_lst))"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:51.1-51.67 *)
inductive allocglobals_is_wf :: "store \<Rightarrow> (globaltype list) \<Rightarrow> (val list) \<Rightarrow> (store * (globaladdr list)) \<Rightarrow> bool" where
	  allocglobals_is_wf_0 :
		"(fun_allocglobals v_store var_0_lst var_1_lst var_0) \<Longrightarrow>
		 (wf_store v_store) \<Longrightarrow>
		 list_all (\<lambda> (var_1 :: val). (wf_val var_1)) var_1_lst \<Longrightarrow>
		 (ret_val = var_0) \<Longrightarrow>
		 (wf_store (fst ret_val)) \<Longrightarrow>
		 allocglobals_is_wf v_store var_0_lst var_1_lst ret_val"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:57.6-57.17 *)
inductive fun_alloctable :: "store \<Rightarrow> tabletype \<Rightarrow> (store * tableaddr) \<Rightarrow> bool" where
	  fun_alloctable_case_0 :
		"(ti = \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits i j_opt) rt), REFS = (repeat (proj_uN_0 i) (ref_REF_NULL rt)) \<rparr>) \<Longrightarrow>
		 (wf_tableinst \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits i j_opt) rt), REFS = (repeat (proj_uN_0 i) (ref_REF_NULL rt)) \<rparr>) \<Longrightarrow>
		 fun_alloctable s (mk_tabletype (mk_limits i j_opt) rt) ((s \<lparr> store_TABLES := ((store_TABLES s) @ [ti])  \<rparr>), (length (store_TABLES s)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:57.6-57.17 *)
lemma alloctable_is_wf :
	"(fun_alloctable v_store v_tabletype var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_tabletype v_tabletype) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:61.1-61.58 *)
inductive fun_alloctables :: "store \<Rightarrow> (tabletype list) \<Rightarrow> (store * (tableaddr list)) \<Rightarrow> bool" where
	  fun_alloctables_case_0 :
		"fun_alloctables s [] (s, [])"
	| fun_alloctables_case_1 :
		"(fun_alloctables s_1 tabletype'_lst var_1) \<Longrightarrow>
		 (fun_alloctable s v_tabletype var_0) \<Longrightarrow>
		 ((s_1, ta) = var_0) \<Longrightarrow>
		 ((s_2, ta'_lst) = var_1) \<Longrightarrow>
		 fun_alloctables s ([v_tabletype] @ tabletype'_lst) (s_2, ([ta] @ ta'_lst))"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:61.1-61.58 *)
inductive alloctables_is_wf :: "store \<Rightarrow> (tabletype list) \<Rightarrow> (store * (tableaddr list)) \<Rightarrow> bool" where
	  alloctables_is_wf_0 :
		"(fun_alloctables v_store var_0_lst var_0) \<Longrightarrow>
		 (wf_store v_store) \<Longrightarrow>
		 list_all (\<lambda> (var_0 :: tabletype). (wf_tabletype var_0)) var_0_lst \<Longrightarrow>
		 (ret_val = var_0) \<Longrightarrow>
		 (wf_store (fst ret_val)) \<Longrightarrow>
		 alloctables_is_wf v_store var_0_lst ret_val"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:67.6-67.15 *)
inductive fun_allocmem :: "store \<Rightarrow> memtype \<Rightarrow> (store * memaddr) \<Rightarrow> bool" where
	  fun_allocmem_case_0 :
		"(mi = \<lparr> meminst_TYPE = (PAGE (mk_limits i j_opt)), BYTES = (repeat ((proj_uN_0 i) * (64 * (Ki ))) (mk_byte 0)) \<rparr>) \<Longrightarrow>
		 (wf_meminst \<lparr> meminst_TYPE = (PAGE (mk_limits i j_opt)), BYTES = (repeat ((proj_uN_0 i) * (64 * (Ki ))) (mk_byte 0)) \<rparr>) \<Longrightarrow>
		 fun_allocmem s (PAGE (mk_limits i j_opt)) ((s \<lparr> store_MEMS := ((store_MEMS s) @ [mi])  \<rparr>), (length (store_MEMS s)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:67.6-67.15 *)
lemma allocmem_is_wf :
	"(fun_allocmem v_store v_memtype var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_memtype v_memtype) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:71.1-71.52 *)
inductive fun_allocmems :: "store \<Rightarrow> (memtype list) \<Rightarrow> (store * (memaddr list)) \<Rightarrow> bool" where
	  fun_allocmems_case_0 :
		"fun_allocmems s [] (s, [])"
	| fun_allocmems_case_1 :
		"(fun_allocmems s_1 memtype'_lst var_1) \<Longrightarrow>
		 (fun_allocmem s v_memtype var_0) \<Longrightarrow>
		 ((s_1, ma) = var_0) \<Longrightarrow>
		 ((s_2, ma'_lst) = var_1) \<Longrightarrow>
		 fun_allocmems s ([v_memtype] @ memtype'_lst) (s_2, ([ma] @ ma'_lst))"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:71.1-71.52 *)
inductive allocmems_is_wf :: "store \<Rightarrow> (memtype list) \<Rightarrow> (store * (memaddr list)) \<Rightarrow> bool" where
	  allocmems_is_wf_0 :
		"(fun_allocmems v_store var_0_lst var_0) \<Longrightarrow>
		 (wf_store v_store) \<Longrightarrow>
		 list_all (\<lambda> (var_0 :: memtype). (wf_memtype var_0)) var_0_lst \<Longrightarrow>
		 (ret_val = var_0) \<Longrightarrow>
		 (wf_store (fst ret_val)) \<Longrightarrow>
		 allocmems_is_wf v_store var_0_lst ret_val"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:77.6-77.16 *)
inductive fun_allocelem :: "store \<Rightarrow> reftype \<Rightarrow> (ref list) \<Rightarrow> (store * elemaddr) \<Rightarrow> bool" where
	  fun_allocelem_case_0 :
		"(ei = \<lparr> eleminst_TYPE = rt, eleminst_REFS = ref_lst \<rparr>) \<Longrightarrow>
		 fun_allocelem s rt ref_lst ((s \<lparr> store_ELEMS := ((store_ELEMS s) @ [ei])  \<rparr>), (length (store_ELEMS s)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:77.6-77.16 *)
lemma allocelem_is_wf :
	"(fun_allocelem v_store v_reftype var_0_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:81.1-81.63 *)
inductive fun_allocelems :: "store \<Rightarrow> (reftype list) \<Rightarrow> ((ref list) list) \<Rightarrow> (store * (elemaddr list)) \<Rightarrow> bool" where
	  fun_allocelems_case_0 :
		"fun_allocelems s [] [] (s, [])"
	| fun_allocelems_case_1 :
		"(fun_allocelems s_1 rt'_lst ref'_lst_lst var_1) \<Longrightarrow>
		 (fun_allocelem s rt ref_lst var_0) \<Longrightarrow>
		 ((s_1, ea) = var_0) \<Longrightarrow>
		 ((s_2, ea'_lst) = var_1) \<Longrightarrow>
		 fun_allocelems s ([rt] @ rt'_lst) ([ref_lst] @ ref'_lst_lst) (s_2, ([ea] @ ea'_lst))"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:81.1-81.63 *)
inductive allocelems_is_wf :: "store \<Rightarrow> (reftype list) \<Rightarrow> ((ref list) list) \<Rightarrow> (store * (elemaddr list)) \<Rightarrow> bool" where
	  allocelems_is_wf_0 :
		"(fun_allocelems v_store var_0_lst var_1_lst_lst var_0) \<Longrightarrow>
		 (wf_store v_store) \<Longrightarrow>
		 (ret_val = var_0) \<Longrightarrow>
		 (wf_store (fst ret_val)) \<Longrightarrow>
		 allocelems_is_wf v_store var_0_lst var_1_lst_lst ret_val"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:87.6-87.16 *)
inductive fun_allocdata :: "store \<Rightarrow> (byte list) \<Rightarrow> (store * dataaddr) \<Rightarrow> bool" where
	  fun_allocdata_case_0 :
		"(di = \<lparr> datainst_BYTES = byte_lst \<rparr>) \<Longrightarrow>
		 (wf_datainst \<lparr> datainst_BYTES = byte_lst \<rparr>) \<Longrightarrow>
		 fun_allocdata s byte_lst ((s \<lparr> store_DATAS := ((store_DATAS s) @ [di])  \<rparr>), (length (store_DATAS s)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:87.6-87.16 *)
lemma allocdata_is_wf :
	"(fun_allocdata v_store var_0_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val))"
sorry

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:91.1-91.54 *)
inductive fun_allocdatas :: "store \<Rightarrow> ((byte list) list) \<Rightarrow> (store * (dataaddr list)) \<Rightarrow> bool" where
	  fun_allocdatas_case_0 :
		"fun_allocdatas s [] (s, [])"
	| fun_allocdatas_case_1 :
		"(fun_allocdatas s_1 byte'_lst_lst var_1) \<Longrightarrow>
		 (fun_allocdata s byte_lst var_0) \<Longrightarrow>
		 ((s_1, da) = var_0) \<Longrightarrow>
		 ((s_2, da'_lst) = var_1) \<Longrightarrow>
		 fun_allocdatas s ([byte_lst] @ byte'_lst_lst) (s_2, ([da] @ da'_lst))"

(* Mutual Recursion at: ../specification/wasm-2.0/9-module.spectec:91.1-91.54 *)
inductive allocdatas_is_wf :: "store \<Rightarrow> ((byte list) list) \<Rightarrow> (store * (dataaddr list)) \<Rightarrow> bool" where
	  allocdatas_is_wf_0 :
		"(fun_allocdatas v_store var_0_lst_lst var_0) \<Longrightarrow>
		 (wf_store v_store) \<Longrightarrow>
		 list_all (\<lambda> (var_0_lst :: (byte list)). list_all (\<lambda> (var_0 :: byte). (wf_byte var_0)) var_0_lst) var_0_lst_lst \<Longrightarrow>
		 (ret_val = var_0) \<Longrightarrow>
		 (wf_store (fst ret_val)) \<Longrightarrow>
		 allocdatas_is_wf v_store var_0_lst_lst ret_val"

(* Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:100.1-100.83 *)
function (sequential, domintros) instexport :: "(funcaddr list) \<Rightarrow> (globaladdr list) \<Rightarrow> (tableaddr list) \<Rightarrow> (memaddr list) \<Rightarrow> export \<Rightarrow> exportinst" where
		  "instexport fa_lst ga_lst ta_lst ma_lst (EXPORT v_name (externidx_FUNC x)) = \<lparr> NAME = v_name, ADDR = (externaddr_FUNC (fa_lst ! (proj_uN_0 x))) \<rparr>"
		| "instexport fa_lst ga_lst ta_lst ma_lst (EXPORT v_name (externidx_GLOBAL x)) = \<lparr> NAME = v_name, ADDR = (externaddr_GLOBAL (ga_lst ! (proj_uN_0 x))) \<rparr>"
		| "instexport fa_lst ga_lst ta_lst ma_lst (EXPORT v_name (externidx_TABLE x)) = \<lparr> NAME = v_name, ADDR = (externaddr_TABLE (ta_lst ! (proj_uN_0 x))) \<rparr>"
		| "instexport fa_lst ga_lst ta_lst ma_lst (EXPORT v_name (externidx_MEM x)) = \<lparr> NAME = v_name, ADDR = (externaddr_MEM (ma_lst ! (proj_uN_0 x))) \<rparr>"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:100.6-100.17 *)
lemma instexport_is_wf :
	"(wf_export v_export) \<Longrightarrow>
	 (ret_val = (instexport var_0_lst var_1_lst var_2_lst var_3_lst v_export)) \<Longrightarrow>
	 (wf_exportinst ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:107.6-107.18 *)
inductive fun_allocmodule :: "store \<Rightarrow> module \<Rightarrow> (externaddr list) \<Rightarrow> (val list) \<Rightarrow> ((ref list) list) \<Rightarrow> (store * moduleinst) \<Rightarrow> bool" where
	  fun_allocmodule_case_0 :
		"(fun_allocdatas s_5 byte_lst_lst var_9) \<Longrightarrow>
		 (fun_allocelems s_4 rt_lst ref_lst_lst var_8) \<Longrightarrow>
		 (fun_allocmems s_3 memtype_lst var_7) \<Longrightarrow>
		 (fun_alloctables s_2 tabletype_lst var_6) \<Longrightarrow>
		 (fun_allocglobals s_1 globaltype_lst val_lst var_5) \<Longrightarrow>
		 (fun_allocfuncs s v_moduleinst func_lst var_4) \<Longrightarrow>
		 (fun_mems externaddr_lst var_3) \<Longrightarrow>
		 (fun_tables externaddr_lst var_2) \<Longrightarrow>
		 (fun_globals externaddr_lst var_1) \<Longrightarrow>
		 (fun_funcs externaddr_lst var_0) \<Longrightarrow>
		 (v_module = (MODULE (map (\<lambda> (ft_1 :: functype). (res_TYPE ft_1)) ft_lst) import_lst func_lst (list_zipWith (\<lambda> (expr_1_1 :: expr) (globaltype_195 :: globaltype). (global_GLOBAL globaltype_195 expr_1_1)) expr_1_lst globaltype_lst) (map (\<lambda> (tabletype_241 :: tabletype). (table_TABLE tabletype_241)) tabletype_lst) (map (\<lambda> (memtype_293 :: memtype). (MEMORY memtype_293)) memtype_lst) (list_map3 (\<lambda> (elemmode_397 :: elemmode) (expr_2_lst_1 :: (expr list)) (rt_1 :: reftype). (ELEM rt_1 expr_2_lst_1 elemmode_397)) elemmode_lst expr_2_lst_lst rt_lst) (list_zipWith (\<lambda> (byte_lst_419 :: (byte list)) (datamode_419 :: datamode). (DATA byte_lst_419 datamode_419)) byte_lst_lst datamode_lst) start_opt export_lst)) \<Longrightarrow>
		 (fa_ex_lst = var_0) \<Longrightarrow>
		 (ga_ex_lst = var_1) \<Longrightarrow>
		 (ta_ex_lst = var_2) \<Longrightarrow>
		 (ma_ex_lst = var_3) \<Longrightarrow>
		 (fa_lst = (mkseq (\<lambda> i_func_1. ((length (store_FUNCS s)) + i_func_1)) n_func)) \<Longrightarrow>
		 (ga_lst = (mkseq (\<lambda> i_global_1. ((length (store_GLOBALS s)) + i_global_1)) n_global)) \<Longrightarrow>
		 (ta_lst = (mkseq (\<lambda> i_table_1. ((length (store_TABLES s)) + i_table_1)) n_table)) \<Longrightarrow>
		 (ma_lst = (mkseq (\<lambda> i_mem_1. ((length (store_MEMS s)) + i_mem_1)) n_mem)) \<Longrightarrow>
		 (ea_lst = (mkseq (\<lambda> i_elem_1. ((length (store_ELEMS s)) + i_elem_1)) n_elem)) \<Longrightarrow>
		 (da_lst = (mkseq (\<lambda> i_data_1. ((length (store_DATAS s)) + i_data_1)) n_data)) \<Longrightarrow>
		 (xi_lst = (map (\<lambda> (export_2 :: export). (instexport (fa_ex_lst @ fa_lst) (ga_ex_lst @ ga_lst) (ta_ex_lst @ ta_lst) (ma_ex_lst @ ma_lst) export_2)) export_lst)) \<Longrightarrow>
		 (v_moduleinst = \<lparr> TYPES = ft_lst, FUNCS = (fa_ex_lst @ fa_lst), GLOBALS = (ga_ex_lst @ ga_lst), TABLES = (ta_ex_lst @ ta_lst), MEMS = (ma_ex_lst @ ma_lst), ELEMS = ea_lst, DATAS = da_lst, EXPORTS = xi_lst \<rparr>) \<Longrightarrow>
		 ((s_1, fa_lst) = var_4) \<Longrightarrow>
		 ((s_2, ga_lst) = var_5) \<Longrightarrow>
		 ((s_3, ta_lst) = var_6) \<Longrightarrow>
		 ((s_4, ma_lst) = var_7) \<Longrightarrow>
		 ((s_5, ea_lst) = var_8) \<Longrightarrow>
		 ((s_6, da_lst) = var_9) \<Longrightarrow>
		 (wf_store s_1) \<Longrightarrow>
		 (wf_store s_2) \<Longrightarrow>
		 (wf_store s_3) \<Longrightarrow>
		 (wf_store s_4) \<Longrightarrow>
		 (wf_store s_5) \<Longrightarrow>
		 (wf_module (MODULE (map (\<lambda> (ft_3 :: functype). (res_TYPE ft_3)) ft_lst) import_lst func_lst (list_zipWith (\<lambda> (expr_1_2 :: expr) (globaltype_198 :: globaltype). (global_GLOBAL globaltype_198 expr_1_2)) expr_1_lst globaltype_lst) (map (\<lambda> (tabletype_244 :: tabletype). (table_TABLE tabletype_244)) tabletype_lst) (map (\<lambda> (memtype_296 :: memtype). (MEMORY memtype_296)) memtype_lst) (list_map3 (\<lambda> (elemmode_399 :: elemmode) (expr_2_lst_2 :: (expr list)) (rt_3 :: reftype). (ELEM rt_3 expr_2_lst_2 elemmode_399)) elemmode_lst expr_2_lst_lst rt_lst) (list_zipWith (\<lambda> (byte_lst_422 :: (byte list)) (datamode_421 :: datamode). (DATA byte_lst_422 datamode_421)) byte_lst_lst datamode_lst) start_opt export_lst)) \<Longrightarrow>
		 (wf_moduleinst \<lparr> TYPES = ft_lst, FUNCS = (fa_ex_lst @ fa_lst), GLOBALS = (ga_ex_lst @ ga_lst), TABLES = (ta_ex_lst @ ta_lst), MEMS = (ma_ex_lst @ ma_lst), ELEMS = ea_lst, DATAS = da_lst, EXPORTS = xi_lst \<rparr>) \<Longrightarrow>
		 fun_allocmodule s v_module externaddr_lst val_lst ref_lst_lst (s_6, v_moduleinst)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:107.6-107.18 *)
lemma allocmodule_is_wf :
	"(fun_allocmodule v_store v_module var_0_lst var_1_lst var_2_lst_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_module v_module) \<Longrightarrow>
	 list_all (\<lambda> (var_1 :: val). (wf_val var_1)) var_1_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_store (fst ret_val)) \<Longrightarrow>
	 (wf_moduleinst (snd ret_val))"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:154.1-154.33 *)
function (sequential, domintros) runelem :: "elem \<Rightarrow> idx \<Rightarrow> (instr list)" where
		  "runelem (ELEM v_reftype expr_lst PASSIVE) i = []"
		| "runelem (ELEM v_reftype expr_lst DECLARE) i = [(instr_sc5 (ELEM_DROP i))]"
		| "runelem (ELEM v_reftype expr_lst (ACTIVE x instr_lst)) i = 
			 (let v_n = (length expr_lst) in 
			 (instr_lst @ [(instr_sc1 (res_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0)))), (instr_sc1 (res_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (instr_sc5 (TABLE_INIT x i)), (instr_sc5 (ELEM_DROP i))]))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:154.6-154.14 *)
lemma runelem_is_wf :
	"(wf_elem v_elem) \<Longrightarrow>
	 (wf_uN 32 v_idx) \<Longrightarrow>
	 (ret_val_lst = (runelem v_elem v_idx)) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: instr). (wf_instr ret_val)) ret_val_lst"
sorry

(* Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:161.1-161.47 *)
function (sequential, domintros) rundata :: "data \<Rightarrow> idx \<Rightarrow> ((instr list) option)" where
		  "rundata (DATA byte_lst datamode_PASSIVE) i = (Some [])"
		| "rundata (DATA byte_lst (datamode_ACTIVE (mk_uN 0) instr_lst)) i = 
			 (let v_n = (length byte_lst) in 
			 (Some (instr_lst @ [(instr_sc1 (res_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0)))), (instr_sc1 (res_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))), (instr_sc7 (MEMORY_INIT i)), (instr_sc7 (DATA_DROP i))])))"
		| "rundata x0 x1 = None"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:161.6-161.14 *)
lemma rundata_is_wf :
	"(wf_data v_data) \<Longrightarrow>
	 (wf_uN 32 v_idx) \<Longrightarrow>
	 ((rundata v_data v_idx) \<noteq> None) \<Longrightarrow>
	 (ret_val_lst = (the ((rundata v_data v_idx)))) \<Longrightarrow>
	 list_all (\<lambda> (ret_val :: instr). (wf_instr ret_val)) ret_val_lst"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:167.6-167.18 *)
inductive fun_instantiate :: "store \<Rightarrow> module \<Rightarrow> (externaddr list) \<Rightarrow> config \<Rightarrow> bool" where
	  fun_instantiate_case_0 :
		"(fun_globals externaddr_lst var_4) \<Longrightarrow>
		 (fun_funcs externaddr_lst var_3) \<Longrightarrow>
		 (fun_allocmodule s v_module externaddr_lst val_lst ref_lst_lst var_2) \<Longrightarrow>
		 (fun_globals externaddr_lst var_1) \<Longrightarrow>
		 (fun_funcs externaddr_lst var_0) \<Longrightarrow>
		 ((MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst) = v_module) \<Longrightarrow>
		 (type_lst = (map (\<lambda> (functype_49 :: functype). (res_TYPE functype_49)) functype_lst)) \<Longrightarrow>
		 (global_lst = (list_zipWith (\<lambda> (expr_G_1 :: expr) (globaltype_200 :: globaltype). (global_GLOBAL globaltype_200 expr_G_1)) expr_G_lst globaltype_lst)) \<Longrightarrow>
		 (elem_lst = (list_map3 (\<lambda> (elemmode_404 :: elemmode) (expr_E_lst_1 :: (expr list)) (reftype_611 :: reftype). (ELEM reftype_611 expr_E_lst_1 elemmode_404)) elemmode_lst expr_E_lst_lst reftype_lst)) \<Longrightarrow>
		 (start_opt = (map_option (\<lambda> (x_1 :: idx). (START x_1)) x_opt)) \<Longrightarrow>
		 (n_F = (length func_lst)) \<Longrightarrow>
		 (n_E = (length elem_lst)) \<Longrightarrow>
		 (n_D = (length data_lst)) \<Longrightarrow>
		 (moduleinst_init = \<lparr> TYPES = functype_lst, FUNCS = (var_0 @ (mkseq (\<lambda> i_F_1. ((length (store_FUNCS s)) + i_F_1)) n_F)), GLOBALS = var_1, TABLES = [], MEMS = [], ELEMS = [], DATAS = [], EXPORTS = [] \<rparr>) \<Longrightarrow>
		 (f_init = \<lparr> LOCALS = [], frame_MODULE = moduleinst_init \<rparr>) \<Longrightarrow>
		 (z = (mk_state s f_init)) \<Longrightarrow>
		 ((length expr_G_lst) = (length val_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (expr_G_2 :: expr) (val_3 :: val). (Eval_expr z expr_G_2 z [val_3])) expr_G_lst val_lst \<Longrightarrow>
		 ((length expr_E_lst_lst) = (length ref_lst_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (expr_E_lst_2 :: (expr list)) (ref_lst_3 :: (ref list)). ((length expr_E_lst_2) = (length ref_lst_3))) expr_E_lst_lst ref_lst_lst \<Longrightarrow>
		 list_all2 (\<lambda> (expr_E_lst_2 :: (expr list)) (ref_lst_3 :: (ref list)). list_all2 (\<lambda> (expr_E_2 :: expr) (ref_7 :: ref). (Eval_expr z expr_E_2 z [(val_ref ref_7)])) expr_E_lst_2 ref_lst_3) expr_E_lst_lst ref_lst_lst \<Longrightarrow>
		 ((s', v_moduleinst) = var_2) \<Longrightarrow>
		 (f = \<lparr> LOCALS = [], frame_MODULE = v_moduleinst \<rparr>) \<Longrightarrow>
		 holds_upto (\<lambda> i_71298. (i_71298 < (length elem_lst))) n_E \<Longrightarrow>
		 (instr_E_lst = (concat_underscore  (mkseq (\<lambda> i_71298. (runelem (elem_lst ! i_71298) (mk_uN i_71298))) n_E))) \<Longrightarrow>
		 holds_upto (\<lambda> j_17. ((rundata (data_lst ! j_17) (mk_uN j_17)) \<noteq> None)) n_D \<Longrightarrow>
		 holds_upto (\<lambda> j_17. (j_17 < (length data_lst))) n_D \<Longrightarrow>
		 (instr_D_lst = (concat_underscore  (mkseq (\<lambda> j_17. (the ((rundata (data_lst ! j_17) (mk_uN j_17))))) n_D))) \<Longrightarrow>
		 list_all (\<lambda> (val_5 :: val). (wf_val val_5)) val_lst \<Longrightarrow>
		 (wf_module (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)) \<Longrightarrow>
		 ((length expr_G_lst) = (length globaltype_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (expr_G_3 :: expr) (globaltype_202 :: globaltype). (wf_global (global_GLOBAL globaltype_202 expr_G_3))) expr_G_lst globaltype_lst \<Longrightarrow>
		 ((length elemmode_lst) = (length expr_E_lst_lst)) \<Longrightarrow>
		 ((length elemmode_lst) = (length reftype_lst)) \<Longrightarrow>
		 list_all3 (\<lambda> (elemmode_406 :: elemmode) (expr_E_lst_3 :: (expr list)) (reftype_613 :: reftype). (wf_elem (ELEM reftype_613 expr_E_lst_3 elemmode_406))) elemmode_lst expr_E_lst_lst reftype_lst \<Longrightarrow>
		 list_all (\<lambda> (x_2 :: idx). (wf_start (START x_2))) (option_to_list x_opt) \<Longrightarrow>
		 (wf_moduleinst \<lparr> TYPES = functype_lst, FUNCS = (var_3 @ (mkseq (\<lambda> i_F_2. ((length (store_FUNCS s)) + i_F_2)) n_F)), GLOBALS = var_4, TABLES = [], MEMS = [], ELEMS = [], DATAS = [], EXPORTS = [] \<rparr>) \<Longrightarrow>
		 (wf_frame \<lparr> LOCALS = [], frame_MODULE = moduleinst_init \<rparr>) \<Longrightarrow>
		 (wf_state (mk_state s f_init)) \<Longrightarrow>
		 (wf_frame \<lparr> LOCALS = [], frame_MODULE = v_moduleinst \<rparr>) \<Longrightarrow>
		 holds_upto (\<lambda> i_71301. (wf_uN 32 (mk_uN i_71301))) n_E \<Longrightarrow>
		 holds_upto (\<lambda> j_18. (wf_uN 32 (mk_uN j_18))) n_D \<Longrightarrow>
		 fun_instantiate s v_module externaddr_lst (mk_config (mk_state s' f) ((map (\<lambda> (instr_E :: instr). (admininstr_instr instr_E)) instr_E_lst) @ ((map (\<lambda> (instr_D :: instr). (admininstr_instr instr_D)) instr_D_lst) @ (option_to_list (map_option (\<lambda> (x :: idx). (admininstr_sc1 (admininstr_st1_CALL x))) x_opt)))))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:167.6-167.18 *)
lemma instantiate_is_wf :
	"(fun_instantiate v_store v_module var_0_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 (wf_module v_module) \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_config ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:196.6-196.13 *)
inductive fun_invoke :: "store \<Rightarrow> funcaddr \<Rightarrow> (val list) \<Rightarrow> config \<Rightarrow> bool" where
	  fun_invoke_case_0 :
		"(f = \<lparr> LOCALS = [], frame_MODULE = \<lparr> TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], EXPORTS = [] \<rparr> \<rparr>) \<Longrightarrow>
		 (fa < (length (fun_funcinst (mk_state s f)))) \<Longrightarrow>
		 ((funcinst_TYPE ((fun_funcinst (mk_state s f)) ! fa)) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (wf_frame \<lparr> LOCALS = [], frame_MODULE = \<lparr> TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], ELEMS = [], DATAS = [], EXPORTS = [] \<rparr> \<rparr>) \<Longrightarrow>
		 (wf_state (mk_state s f)) \<Longrightarrow>
		 (v_n = (length val_lst)) \<Longrightarrow>
		 fun_invoke s fa val_lst (mk_config (mk_state s f) ((map (\<lambda> (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_sc7 (CALL_ADDR fa))]))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:196.6-196.13 *)
lemma invoke_is_wf :
	"(fun_invoke v_store v_funcaddr var_0_lst var_0) \<Longrightarrow>
	 (wf_store v_store) \<Longrightarrow>
	 list_all (\<lambda> (var_0 :: val). (wf_val var_0)) var_0_lst \<Longrightarrow>
	 (ret_val = var_0) \<Longrightarrow>
	 (wf_config ret_val)"
sorry

(* Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:849.1-849.43 *)
type_synonym startopt = "(start list)"

(* Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:884.1-884.29 *)
type_synonym code = "((local list) * expr)"

(* Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:915.1-915.33 *)
type_synonym nopt = "(u32 list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:3.1-3.61 *)
inductive Context_ok :: "res_context \<Rightarrow> bool" where
	  mk_Context_ok :
		"(C = \<lparr> context_TYPES = ft_lst, context_FUNCS = ft_2_lst, context_GLOBALS = gt_lst, context_TABLES = tt_lst, context_MEMS = mt_lst, context_ELEMS = et_lst, context_DATAS = ok_lst, context_LOCALS = lct_lst, LABELS = [(mk_list (map (\<lambda> (rt :: reftype). (valtype_reftype rt)) rt_lst))], context_RETURN = (Some (mk_list (option_to_list (map_option (\<lambda> (rt' :: reftype). (valtype_reftype rt')) rt'_opt)))) \<rparr>) \<Longrightarrow>
		 list_all (\<lambda> (ft :: functype). (Functype_ok ft)) ft_lst \<Longrightarrow>
		 list_all (\<lambda> (gt :: globaltype). (Globaltype_ok gt)) gt_lst \<Longrightarrow>
		 list_all (\<lambda> (mt :: memtype). (Memtype_ok mt)) mt_lst \<Longrightarrow>
		 list_all (\<lambda> (tt :: tabletype). (Tabletype_ok tt)) tt_lst \<Longrightarrow>
		 list_all (\<lambda> (ft_2 :: functype). (Functype_ok ft_2)) ft_2_lst \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_context \<lparr> context_TYPES = ft_lst, context_FUNCS = ft_2_lst, context_GLOBALS = gt_lst, context_TABLES = tt_lst, context_MEMS = mt_lst, context_ELEMS = et_lst, context_DATAS = ok_lst, context_LOCALS = lct_lst, LABELS = [(mk_list (map (\<lambda> (rt :: reftype). (valtype_reftype rt)) rt_lst))], context_RETURN = (Some (mk_list (option_to_list (map_option (\<lambda> (rt' :: reftype). (valtype_reftype rt')) rt'_opt)))) \<rparr>) \<Longrightarrow>
		 Context_ok C"

(* Mutual Recursion at: ../specification/wasm-2.0/B-soundness.spectec:130.1-130.84 *)
inductive Externaddr_ok :: "store \<Rightarrow> externaddr \<Rightarrow> externtype \<Rightarrow> bool" where
	  Externaddr_ok__global :
		"(a < (length (store_GLOBALS s))) \<Longrightarrow>
		 (((store_GLOBALS s) ! a) = v_globalinst) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_externtype (GLOBAL (globalinst_TYPE v_globalinst))) \<Longrightarrow>
		 Externaddr_ok s (externaddr_GLOBAL a) (GLOBAL (globalinst_TYPE v_globalinst))"
	| Externaddr_ok__mem :
		"(a < (length (store_MEMS s))) \<Longrightarrow>
		 (((store_MEMS s) ! a) = v_meminst) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_externtype (MEM (meminst_TYPE v_meminst))) \<Longrightarrow>
		 Externaddr_ok s (externaddr_MEM a) (MEM (meminst_TYPE v_meminst))"
	| Externaddr_ok__table :
		"(a < (length (store_TABLES s))) \<Longrightarrow>
		 (((store_TABLES s) ! a) = v_tableinst) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_externtype (TABLE (tableinst_TYPE v_tableinst))) \<Longrightarrow>
		 Externaddr_ok s (externaddr_TABLE a) (TABLE (tableinst_TYPE v_tableinst))"
	| Externaddr_ok__func :
		"(a < (length (store_FUNCS s))) \<Longrightarrow>
		 (((store_FUNCS s) ! a) = v_funcinst) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_externtype (FUNC (funcinst_TYPE v_funcinst))) \<Longrightarrow>
		 Externaddr_ok s (externaddr_FUNC a) (FUNC (funcinst_TYPE v_funcinst))"
	| Externaddr_ok__sub :
		"(Externaddr_ok s v_externaddr xt') \<Longrightarrow>
		 (Externtype_sub xt' xt) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_externtype xt) \<Longrightarrow>
		 (wf_externtype xt') \<Longrightarrow>
		 Externaddr_ok s v_externaddr xt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:27.1-27.40 *)
inductive Ref_ok :: "store \<Rightarrow> ref \<Rightarrow> reftype \<Rightarrow> bool" where
	  null :
		"(wf_store s) \<Longrightarrow>
		 Ref_ok s (ref_REF_NULL rt) rt"
	| Ref_ok__func :
		"(Externaddr_ok s (externaddr_FUNC a) (FUNC ext)) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_externtype (FUNC ext)) \<Longrightarrow>
		 Ref_ok s (REF_FUNC_ADDR a) FUNCREF"
	| extern :
		"(wf_store s) \<Longrightarrow>
		 Ref_ok s (REF_HOST_ADDR a) EXTERNREF"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:41.1-41.40 *)
inductive Val_ok :: "store \<Rightarrow> val \<Rightarrow> valtype \<Rightarrow> bool" where
	  Val_ok__numtype :
		"(wf_store s) \<Longrightarrow>
		 (wf_val (val_CONST nt c_t)) \<Longrightarrow>
		 Val_ok s (val_CONST nt c_t) (valtype_numtype nt)"
	| Val_ok__vectype :
		"(wf_store s) \<Longrightarrow>
		 (wf_val (val_VCONST vt c_t)) \<Longrightarrow>
		 Val_ok s (val_VCONST vt c_t) (valtype_vectype vt)"
	| Val_ok__reftype :
		"(Ref_ok s r rt) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 Val_ok s (val_ref r) (valtype_reftype rt)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:55.1-55.47 *)
inductive Result_ok :: "store \<Rightarrow> result \<Rightarrow> (valtype list) \<Rightarrow> bool" where
	  Result_ok__result :
		"((length t_lst) = (length v_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (t :: valtype) (v :: val). (Val_ok s v t)) t_lst v_lst \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_result (underscore_VALS v_lst)) \<Longrightarrow>
		 Result_ok s (underscore_VALS v_lst) t_lst"
	| trap :
		"(wf_store s) \<Longrightarrow>
		 (wf_result TRAP) \<Longrightarrow>
		 Result_ok s TRAP t_lst"

(* Type Alias Definition at: ../specification/wasm-2.0/B-soundness.spectec:66.1-66.31 *)
type_synonym adminexpr = "(admininstr list)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:159.1-159.51 *)
inductive Datainst_ok :: "store \<Rightarrow> datainst \<Rightarrow> res_datatype \<Rightarrow> bool" where
	  mk_Datainst_ok :
		"(wf_store s) \<Longrightarrow>
		 (wf_datainst \<lparr> datainst_BYTES = b_lst \<rparr>) \<Longrightarrow>
		 Datainst_ok s \<lparr> datainst_BYTES = b_lst \<rparr> OK"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:160.1-160.51 *)
inductive Eleminst_ok :: "store \<Rightarrow> eleminst \<Rightarrow> elemtype \<Rightarrow> bool" where
	  mk_Eleminst_ok :
		"list_all (\<lambda> (v_ref :: ref). (Ref_ok s v_ref rt)) ref_lst \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 Eleminst_ok s \<lparr> eleminst_TYPE = rt, eleminst_REFS = ref_lst \<rparr> rt"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:161.1-161.49 *)
inductive Exportinst_ok :: "store \<Rightarrow> exportinst \<Rightarrow> bool" where
	  mk_Exportinst_ok :
		"(Externaddr_ok s xa xt) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_externtype xt) \<Longrightarrow>
		 (wf_exportinst \<lparr> NAME = nm, ADDR = xa \<rparr>) \<Longrightarrow>
		 Exportinst_ok s \<lparr> NAME = nm, ADDR = xa \<rparr>"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:199.1-199.54 *)
inductive Moduleinst_ok :: "store \<Rightarrow> moduleinst \<Rightarrow> res_context \<Rightarrow> bool" where
	  mk_Moduleinst_ok :
		"list_all (\<lambda> (v_functype :: functype). (Functype_ok v_functype)) functype_lst \<Longrightarrow>
		 ((length globaladdr_lst) = (length globaltype_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (v_globaladdr :: globaladdr) (v_globaltype :: globaltype). (Externaddr_ok s (externaddr_GLOBAL v_globaladdr) (GLOBAL v_globaltype))) globaladdr_lst globaltype_lst \<Longrightarrow>
		 ((length funcaddr_lst) = (length functype_F_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (v_funcaddr :: funcaddr) (functype_F :: functype). (Externaddr_ok s (externaddr_FUNC v_funcaddr) (FUNC functype_F))) funcaddr_lst functype_F_lst \<Longrightarrow>
		 ((length memaddr_lst) = (length memtype_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (v_memaddr :: memaddr) (v_memtype :: memtype). (Externaddr_ok s (externaddr_MEM v_memaddr) (MEM v_memtype))) memaddr_lst memtype_lst \<Longrightarrow>
		 ((length tableaddr_lst) = (length tabletype_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (v_tableaddr :: tableaddr) (v_tabletype :: tabletype). (Externaddr_ok s (externaddr_TABLE v_tableaddr) (TABLE v_tabletype))) tableaddr_lst tabletype_lst \<Longrightarrow>
		 list_all (\<lambda> (v_exportinst :: exportinst). (Exportinst_ok s v_exportinst)) exportinst_lst \<Longrightarrow>
		 ((length dataaddr_lst) = (length datatype_lst)) \<Longrightarrow>
		 list_all (\<lambda> (v_dataaddr :: nat). (v_dataaddr < (length (store_DATAS s)))) dataaddr_lst \<Longrightarrow>
		 list_all2 (\<lambda> (v_dataaddr :: nat) (v_datatype :: res_datatype). (Datainst_ok s ((store_DATAS s) ! v_dataaddr) v_datatype)) dataaddr_lst datatype_lst \<Longrightarrow>
		 ((length elemaddr_lst) = (length elemtype_lst)) \<Longrightarrow>
		 list_all (\<lambda> (v_elemaddr :: nat). (v_elemaddr < (length (store_ELEMS s)))) elemaddr_lst \<Longrightarrow>
		 list_all2 (\<lambda> (v_elemaddr :: nat) (v_elemtype :: elemtype). (Eleminst_ok s ((store_ELEMS s) ! v_elemaddr) v_elemtype)) elemaddr_lst elemtype_lst \<Longrightarrow>
		 (disjoint_underscore  (map (\<lambda> (v_exportinst :: exportinst). (NAME v_exportinst)) exportinst_lst)) \<Longrightarrow>
		 ((length ((map (\<lambda> (v_globaladdr :: globaladdr). (externaddr_GLOBAL v_globaladdr)) globaladdr_lst) @ ((map (\<lambda> (v_memaddr :: memaddr). (externaddr_MEM v_memaddr)) memaddr_lst) @ ((map (\<lambda> (v_tableaddr :: tableaddr). (externaddr_TABLE v_tableaddr)) tableaddr_lst) @ (map (\<lambda> (v_funcaddr :: funcaddr). (externaddr_FUNC v_funcaddr)) funcaddr_lst))))) > 0) \<Longrightarrow>
		 list_all (\<lambda> (v_exportinst :: exportinst). ((ADDR v_exportinst) \<in> set ((map (\<lambda> (v_globaladdr :: globaladdr). (externaddr_GLOBAL v_globaladdr)) globaladdr_lst) @ ((map (\<lambda> (v_memaddr :: memaddr). (externaddr_MEM v_memaddr)) memaddr_lst) @ ((map (\<lambda> (v_tableaddr :: tableaddr). (externaddr_TABLE v_tableaddr)) tableaddr_lst) @ (map (\<lambda> (v_funcaddr :: funcaddr). (externaddr_FUNC v_funcaddr)) funcaddr_lst)))))) exportinst_lst \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_moduleinst \<lparr> TYPES = functype_lst, FUNCS = funcaddr_lst, GLOBALS = globaladdr_lst, TABLES = tableaddr_lst, MEMS = memaddr_lst, ELEMS = elemaddr_lst, DATAS = dataaddr_lst, EXPORTS = exportinst_lst \<rparr>) \<Longrightarrow>
		 (wf_context \<lparr> context_TYPES = functype_lst, context_FUNCS = functype_F_lst, context_GLOBALS = globaltype_lst, context_TABLES = tabletype_lst, context_MEMS = memtype_lst, context_ELEMS = elemtype_lst, context_DATAS = datatype_lst, context_LOCALS = [], LABELS = [], context_RETURN = None \<rparr>) \<Longrightarrow>
		 list_all (\<lambda> (v_globaltype :: globaltype). (wf_externtype (GLOBAL v_globaltype))) globaltype_lst \<Longrightarrow>
		 list_all (\<lambda> (functype_F :: functype). (wf_externtype (FUNC functype_F))) functype_F_lst \<Longrightarrow>
		 list_all (\<lambda> (v_memtype :: memtype). (wf_externtype (MEM v_memtype))) memtype_lst \<Longrightarrow>
		 list_all (\<lambda> (v_tabletype :: tabletype). (wf_externtype (TABLE v_tabletype))) tabletype_lst \<Longrightarrow>
		 Moduleinst_ok s \<lparr> TYPES = functype_lst, FUNCS = funcaddr_lst, GLOBALS = globaladdr_lst, TABLES = tableaddr_lst, MEMS = memaddr_lst, ELEMS = elemaddr_lst, DATAS = dataaddr_lst, EXPORTS = exportinst_lst \<rparr> \<lparr> context_TYPES = functype_lst, context_FUNCS = functype_F_lst, context_GLOBALS = globaltype_lst, context_TABLES = tabletype_lst, context_MEMS = memtype_lst, context_ELEMS = elemtype_lst, context_DATAS = datatype_lst, context_LOCALS = [], LABELS = [], context_RETURN = None \<rparr>"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:293.1-293.44 *)
inductive Frame_ok :: "store \<Rightarrow> frame \<Rightarrow> res_context \<Rightarrow> bool" where
	  mk_Frame_ok :
		"(Moduleinst_ok s v_moduleinst C) \<Longrightarrow>
		 ((length t_lst) = (length val_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (t :: valtype) (v_val :: val). (Val_ok s v_val t)) t_lst val_lst \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_frame \<lparr> LOCALS = val_lst, frame_MODULE = v_moduleinst \<rparr>) \<Longrightarrow>
		 (wf_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = t_lst, LABELS = [], context_RETURN = None \<rparr>) \<Longrightarrow>
		 Frame_ok s \<lparr> LOCALS = val_lst, frame_MODULE = v_moduleinst \<rparr> (append_res_context C \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = t_lst, LABELS = [], context_RETURN = None \<rparr>)"

(* Mutual Recursion at: ../specification/wasm-2.0/B-soundness.spectec:68.1-73.36 *)
inductive Instr_ok2 :: "store \<Rightarrow> res_context \<Rightarrow> admininstr \<Rightarrow> functype \<Rightarrow> bool"
and Instrs_ok2 :: "store \<Rightarrow> res_context \<Rightarrow> (admininstr list) \<Rightarrow> functype \<Rightarrow> bool"
and Expr_ok2 :: "store \<Rightarrow> res_context \<Rightarrow> adminexpr \<Rightarrow> resulttype \<Rightarrow> bool" where
	  plain :
		"(Instr_ok C v_instr (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_instr v_instr) \<Longrightarrow>
		 Instr_ok2 s C (admininstr_instr v_instr) (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"
	| label :
		"(Instrs_ok2 s C (map (\<lambda> (instr' :: instr). (admininstr_instr instr')) instr'_lst) (mk_functype (mk_list t'_lst) (mk_list t_lst))) \<Longrightarrow>
		 (Instrs_ok2 s (append_res_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t'_lst)], context_RETURN = None \<rparr> C) admininstr_lst (mk_functype (mk_list []) (mk_list t_lst))) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_admininstr (admininstr_sc8 (LABEL_underscore v_n instr'_lst admininstr_lst))) \<Longrightarrow>
		 (wf_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t'_lst)], context_RETURN = None \<rparr>) \<Longrightarrow>
		 (v_n = (length t'_lst)) \<Longrightarrow>
		 Instr_ok2 s C (admininstr_sc8 (LABEL_underscore v_n instr'_lst admininstr_lst)) (mk_functype (mk_list []) (mk_list t_lst))"
	| Instr_ok2__frame :
		"(Frame_ok s f C') \<Longrightarrow>
		 ((context_RETURN C') = (Some (mk_list t_lst))) \<Longrightarrow>
		 (Expr_ok2 s C' admininstr_lst (mk_list t_lst)) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_context C') \<Longrightarrow>
		 (wf_admininstr (admininstr_sc8 (FRAME_underscore v_n f admininstr_lst))) \<Longrightarrow>
		 (v_n = (length t_lst)) \<Longrightarrow>
		 Instr_ok2 s C (admininstr_sc8 (FRAME_underscore v_n f admininstr_lst)) (mk_functype (mk_list []) (mk_list t_lst))"
	| Instr_ok2__call_addr :
		"(Externaddr_ok s (externaddr_FUNC v_funcaddr) (FUNC (mk_functype (mk_list t_1_lst) (mk_list t_2_lst)))) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_admininstr (admininstr_sc7 (CALL_ADDR v_funcaddr))) \<Longrightarrow>
		 (wf_externtype (FUNC (mk_functype (mk_list t_1_lst) (mk_list t_2_lst)))) \<Longrightarrow>
		 Instr_ok2 s C (admininstr_sc7 (CALL_ADDR v_funcaddr)) (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"
	| Instr_ok2__ref :
		"(Ref_ok s v_ref rt) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 Instr_ok2 s C (admininstr_ref v_ref) (mk_functype (mk_list []) (mk_list [(valtype_reftype rt)]))"
	| Instr_ok2__trap :
		"(wf_store s) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_admininstr (admininstr_sc7 admininstr_st7_TRAP)) \<Longrightarrow>
		 Instr_ok2 s C (admininstr_sc7 admininstr_st7_TRAP) (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"
	| Instrs_ok2__empty :
		"(wf_store s) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 Instrs_ok2 s C [] (mk_functype (mk_list []) (mk_list []))"
	| Instrs_ok2__instr :
		"(Instr_ok2 s C v_admininstr (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_admininstr v_admininstr) \<Longrightarrow>
		 Instrs_ok2 s C [v_admininstr] (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))"
	| Instrs_ok2__seq :
		"(Instrs_ok2 s C admininstr_1_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (Instrs_ok2 s C admininstr_2_lst (mk_functype (mk_list t_2_lst) (mk_list t_3_lst))) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 list_all (\<lambda> (admininstr_1 :: admininstr). (wf_admininstr admininstr_1)) admininstr_1_lst \<Longrightarrow>
		 list_all (\<lambda> (admininstr_2 :: admininstr). (wf_admininstr admininstr_2)) admininstr_2_lst \<Longrightarrow>
		 Instrs_ok2 s C (admininstr_1_lst @ admininstr_2_lst) (mk_functype (mk_list t_1_lst) (mk_list t_3_lst))"
	| Instrs_ok2__sub :
		"(Instrs_ok2 s C admininstr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (Resulttype_sub (mk_list t'_1_lst) (mk_list t_1_lst)) \<Longrightarrow>
		 (Resulttype_sub (mk_list t_2_lst) (mk_list t'_2_lst)) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 list_all (\<lambda> (v_admininstr :: admininstr). (wf_admininstr v_admininstr)) admininstr_lst \<Longrightarrow>
		 Instrs_ok2 s C admininstr_lst (mk_functype (mk_list t'_1_lst) (mk_list t'_2_lst))"
	| Instrs_ok2__frame :
		"(Instrs_ok2 s C admininstr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 list_all (\<lambda> (v_admininstr :: admininstr). (wf_admininstr v_admininstr)) admininstr_lst \<Longrightarrow>
		 Instrs_ok2 s C admininstr_lst (mk_functype (mk_list (t_lst @ t_1_lst)) (mk_list (t_lst @ t_2_lst)))"
	| mk_Expr_ok2 :
		"(Instrs_ok2 s C admininstr_lst (mk_functype (mk_list []) (mk_list t_lst))) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 list_all (\<lambda> (v_admininstr :: admininstr). (wf_admininstr v_admininstr)) admininstr_lst \<Longrightarrow>
		 Expr_ok2 s C admininstr_lst (mk_list t_lst)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:155.1-155.57 *)
inductive Globalinst_ok :: "store \<Rightarrow> globalinst \<Rightarrow> globaltype \<Rightarrow> bool" where
	  mk_Globalinst_ok :
		"(Globaltype_ok (mk_globaltype v_mut t)) \<Longrightarrow>
		 (Val_ok s v_val t) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_globalinst \<lparr> globalinst_TYPE = (mk_globaltype v_mut t), VALUE = v_val \<rparr>) \<Longrightarrow>
		 Globalinst_ok s \<lparr> globalinst_TYPE = (mk_globaltype v_mut t), VALUE = v_val \<rparr> (mk_globaltype v_mut t)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:156.1-156.48 *)
inductive Meminst_ok :: "store \<Rightarrow> meminst \<Rightarrow> memtype \<Rightarrow> bool" where
	  mk_Meminst_ok :
		"(Memtype_ok (PAGE (mk_limits (mk_uN v_n) (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt)))) \<Longrightarrow>
		 ((length b_lst) = (v_n * (64 * (Ki )))) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_meminst \<lparr> meminst_TYPE = (PAGE (mk_limits (mk_uN v_n) (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt))), BYTES = b_lst \<rparr>) \<Longrightarrow>
		 (wf_memtype (PAGE (mk_limits (mk_uN v_n) (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt)))) \<Longrightarrow>
		 Meminst_ok s \<lparr> meminst_TYPE = (PAGE (mk_limits (mk_uN v_n) (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt))), BYTES = b_lst \<rparr> (PAGE (mk_limits (mk_uN v_n) (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt)))"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:157.1-157.54 *)
inductive Tableinst_ok :: "store \<Rightarrow> tableinst \<Rightarrow> tabletype \<Rightarrow> bool" where
	  mk_Tableinst_ok :
		"(Tabletype_ok (mk_tabletype (mk_limits (mk_uN v_n) (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt)) rt)) \<Longrightarrow>
		 list_all (\<lambda> (v_ref :: ref). (Ref_ok s v_ref rt)) ref_lst \<Longrightarrow>
		 ((length ref_lst) = v_n) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_tableinst \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN v_n) (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt)) rt), REFS = ref_lst \<rparr>) \<Longrightarrow>
		 (wf_tabletype (mk_tabletype (mk_limits (mk_uN v_n) (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt)) rt)) \<Longrightarrow>
		 Tableinst_ok s \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN v_n) (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt)) rt), REFS = ref_lst \<rparr> (mk_tabletype (mk_limits (mk_uN v_n) (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt)) rt)"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:158.1-158.51 *)
inductive Funcinst_ok :: "store \<Rightarrow> funcinst \<Rightarrow> functype \<Rightarrow> bool" where
	  mk_Funcinst_ok :
		"(Functype_ok ft) \<Longrightarrow>
		 (Moduleinst_ok s v_moduleinst C) \<Longrightarrow>
		 (Func_ok C v_func ft) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_funcinst \<lparr> funcinst_TYPE = ft, funcinst_MODULE = v_moduleinst, CODE = v_func \<rparr>) \<Longrightarrow>
		 Funcinst_ok s \<lparr> funcinst_TYPE = ft, funcinst_MODULE = v_moduleinst, CODE = v_func \<rparr> ft"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:233.1-233.33 *)
inductive Store_ok :: "store \<Rightarrow> bool" where
	  mk_Store_ok :
		"((length globalinst_lst) = (length globaltype_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (v_globalinst :: globalinst) (v_globaltype :: globaltype). (Globalinst_ok s v_globalinst v_globaltype)) globalinst_lst globaltype_lst \<Longrightarrow>
		 ((length meminst_lst) = (length memtype_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (v_meminst :: meminst) (v_memtype :: memtype). (Meminst_ok s v_meminst v_memtype)) meminst_lst memtype_lst \<Longrightarrow>
		 ((length tableinst_lst) = (length tabletype_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (v_tableinst :: tableinst) (v_tabletype :: tabletype). (Tableinst_ok s v_tableinst v_tabletype)) tableinst_lst tabletype_lst \<Longrightarrow>
		 ((length funcinst_lst) = (length functype_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (v_funcinst :: funcinst) (v_functype :: functype). (Funcinst_ok s v_funcinst v_functype)) funcinst_lst functype_lst \<Longrightarrow>
		 ((length datainst_lst) = (length datatype_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (v_datainst :: datainst) (v_datatype :: res_datatype). (Datainst_ok s v_datainst v_datatype)) datainst_lst datatype_lst \<Longrightarrow>
		 ((length eleminst_lst) = (length elemtype_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (v_eleminst :: eleminst) (v_elemtype :: elemtype). (Eleminst_ok s v_eleminst v_elemtype)) eleminst_lst elemtype_lst \<Longrightarrow>
		 (s = \<lparr> store_FUNCS = funcinst_lst, store_GLOBALS = globalinst_lst, store_TABLES = tableinst_lst, store_MEMS = meminst_lst, store_ELEMS = eleminst_lst, store_DATAS = datainst_lst \<rparr>) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 list_all (\<lambda> (v_memtype :: memtype). (wf_memtype v_memtype)) memtype_lst \<Longrightarrow>
		 list_all (\<lambda> (v_tabletype :: tabletype). (wf_tabletype v_tabletype)) tabletype_lst \<Longrightarrow>
		 (wf_store \<lparr> store_FUNCS = funcinst_lst, store_GLOBALS = globalinst_lst, store_TABLES = tableinst_lst, store_MEMS = meminst_lst, store_ELEMS = eleminst_lst, store_DATAS = datainst_lst \<rparr>) \<Longrightarrow>
		 Store_ok s"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:249.1-249.54 *)
inductive Extend_globalinst :: "globalinst \<Rightarrow> globalinst \<Rightarrow> bool" where
	  mk_Extend_globalinst :
		"((v_mut = (Some MUT)) \<or> (v_val = val')) \<Longrightarrow>
		 (wf_globalinst \<lparr> globalinst_TYPE = (mk_globaltype v_mut t), VALUE = v_val \<rparr>) \<Longrightarrow>
		 (wf_globalinst \<lparr> globalinst_TYPE = (mk_globaltype v_mut t), VALUE = val' \<rparr>) \<Longrightarrow>
		 Extend_globalinst \<lparr> globalinst_TYPE = (mk_globaltype v_mut t), VALUE = v_val \<rparr> \<lparr> globalinst_TYPE = (mk_globaltype v_mut t), VALUE = val' \<rparr>"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:250.1-250.45 *)
inductive Extend_meminst :: "meminst \<Rightarrow> meminst \<Rightarrow> bool" where
	  mk_Extend_meminst :
		"(v_n \<le> n') \<Longrightarrow>
		 ((length b_lst) \<le> (length b'_lst)) \<Longrightarrow>
		 (wf_meminst \<lparr> meminst_TYPE = (PAGE (mk_limits (mk_uN v_n) (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt))), BYTES = b_lst \<rparr>) \<Longrightarrow>
		 (wf_meminst \<lparr> meminst_TYPE = (PAGE (mk_limits (mk_uN n') (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt))), BYTES = b'_lst \<rparr>) \<Longrightarrow>
		 Extend_meminst \<lparr> meminst_TYPE = (PAGE (mk_limits (mk_uN v_n) (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt))), BYTES = b_lst \<rparr> \<lparr> meminst_TYPE = (PAGE (mk_limits (mk_uN n') (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt))), BYTES = b'_lst \<rparr>"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:251.1-251.51 *)
inductive Extend_tableinst :: "tableinst \<Rightarrow> tableinst \<Rightarrow> bool" where
	  mk_Extend_tableinst :
		"(v_n \<le> n') \<Longrightarrow>
		 ((length ref_lst) \<le> (length ref'_lst)) \<Longrightarrow>
		 (wf_tableinst \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN v_n) (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt)) rt), REFS = ref_lst \<rparr>) \<Longrightarrow>
		 (wf_tableinst \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN n') (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt)) rt), REFS = ref'_lst \<rparr>) \<Longrightarrow>
		 Extend_tableinst \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN v_n) (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt)) rt), REFS = ref_lst \<rparr> \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN n') (map_option (\<lambda> (v_m :: m). (mk_uN v_m)) m_opt)) rt), REFS = ref'_lst \<rparr>"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:252.1-252.48 *)
inductive Extend_funcinst :: "funcinst \<Rightarrow> funcinst \<Rightarrow> bool" where
	  mk_Extend_funcinst :
		"(wf_funcinst \<lparr> funcinst_TYPE = ft, funcinst_MODULE = mm, CODE = fc \<rparr>) \<Longrightarrow>
		 Extend_funcinst \<lparr> funcinst_TYPE = ft, funcinst_MODULE = mm, CODE = fc \<rparr> \<lparr> funcinst_TYPE = ft, funcinst_MODULE = mm, CODE = fc \<rparr>"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:253.1-253.48 *)
inductive Extend_datainst :: "datainst \<Rightarrow> datainst \<Rightarrow> bool" where
	  mk_Extend_datainst :
		"((b_lst = b'_lst) \<or> (b'_lst = [])) \<Longrightarrow>
		 (wf_datainst \<lparr> datainst_BYTES = b_lst \<rparr>) \<Longrightarrow>
		 (wf_datainst \<lparr> datainst_BYTES = b'_lst \<rparr>) \<Longrightarrow>
		 Extend_datainst \<lparr> datainst_BYTES = b_lst \<rparr> \<lparr> datainst_BYTES = b'_lst \<rparr>"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:254.1-254.48 *)
inductive Extend_eleminst :: "eleminst \<Rightarrow> eleminst \<Rightarrow> bool" where
	  mk_Extend_eleminst :
		"((ref_lst = ref'_lst) \<or> (ref'_lst = [])) \<Longrightarrow>
		 Extend_eleminst \<lparr> eleminst_TYPE = rt, eleminst_REFS = ref_lst \<rparr> \<lparr> eleminst_TYPE = rt, eleminst_REFS = ref'_lst \<rparr>"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:255.1-255.39 *)
inductive Extend_store :: "store \<Rightarrow> store \<Rightarrow> bool" where
	  mk_Extend_store :
		"holds_upto (\<lambda> a. (a < (length (store_GLOBALS s)))) (length (store_GLOBALS s)) \<Longrightarrow>
		 holds_upto (\<lambda> a. (a < (length (store_GLOBALS s')))) (length (store_GLOBALS s)) \<Longrightarrow>
		 holds_upto (\<lambda> a. (Extend_globalinst ((store_GLOBALS s) ! a) ((store_GLOBALS s') ! a))) (length (store_GLOBALS s)) \<Longrightarrow>
		 holds_upto (\<lambda> a. (a < (length (store_MEMS s)))) (length (store_MEMS s)) \<Longrightarrow>
		 holds_upto (\<lambda> a. (a < (length (store_MEMS s')))) (length (store_MEMS s)) \<Longrightarrow>
		 holds_upto (\<lambda> a. (Extend_meminst ((store_MEMS s) ! a) ((store_MEMS s') ! a))) (length (store_MEMS s)) \<Longrightarrow>
		 holds_upto (\<lambda> a. (a < (length (store_TABLES s)))) (length (store_TABLES s)) \<Longrightarrow>
		 holds_upto (\<lambda> a. (a < (length (store_TABLES s')))) (length (store_TABLES s)) \<Longrightarrow>
		 holds_upto (\<lambda> a. (Extend_tableinst ((store_TABLES s) ! a) ((store_TABLES s') ! a))) (length (store_TABLES s)) \<Longrightarrow>
		 holds_upto (\<lambda> a. (a < (length (store_FUNCS s)))) (length (store_FUNCS s)) \<Longrightarrow>
		 holds_upto (\<lambda> a. (a < (length (store_FUNCS s')))) (length (store_FUNCS s)) \<Longrightarrow>
		 holds_upto (\<lambda> a. (Extend_funcinst ((store_FUNCS s) ! a) ((store_FUNCS s') ! a))) (length (store_FUNCS s)) \<Longrightarrow>
		 holds_upto (\<lambda> a. (a < (length (store_DATAS s)))) (length (store_DATAS s)) \<Longrightarrow>
		 holds_upto (\<lambda> a. (a < (length (store_DATAS s')))) (length (store_DATAS s)) \<Longrightarrow>
		 holds_upto (\<lambda> a. (Extend_datainst ((store_DATAS s) ! a) ((store_DATAS s') ! a))) (length (store_DATAS s)) \<Longrightarrow>
		 holds_upto (\<lambda> a. (a < (length (store_ELEMS s)))) (length (store_ELEMS s)) \<Longrightarrow>
		 holds_upto (\<lambda> a. (a < (length (store_ELEMS s')))) (length (store_ELEMS s)) \<Longrightarrow>
		 holds_upto (\<lambda> a. (Extend_eleminst ((store_ELEMS s) ! a) ((store_ELEMS s') ! a))) (length (store_ELEMS s)) \<Longrightarrow>
		 (wf_store s) \<Longrightarrow>
		 (wf_store s') \<Longrightarrow>
		 Extend_store s s'"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:294.1-294.38 *)
inductive State_ok :: "state \<Rightarrow> res_context \<Rightarrow> bool" where
	  mk_State_ok :
		"(Store_ok s) \<Longrightarrow>
		 (Frame_ok s f C) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_state (mk_state s f)) \<Longrightarrow>
		 State_ok (mk_state s f) C"

(* Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:295.1-295.43 *)
inductive Config_ok :: "config \<Rightarrow> resulttype \<Rightarrow> bool" where
	  mk_Config_ok :
		"(State_ok (mk_state s f) C) \<Longrightarrow>
		 (Expr_ok2 s C admininstr_lst (mk_list t_lst)) \<Longrightarrow>
		 (wf_context C) \<Longrightarrow>
		 (wf_config (mk_config (mk_state s f) admininstr_lst)) \<Longrightarrow>
		 (wf_state (mk_state s f)) \<Longrightarrow>
		 Config_ok (mk_config (mk_state s f) admininstr_lst) (mk_list t_lst)"

(* Auxiliary Definition at: isabelle/wasm-2.0/C-mech-aux.spectec:1.1-1.31 *)
function (sequential, domintros) is_val :: "admininstr \<Rightarrow> bool" where
		  "is_val (admininstr_sc7 (admininstr_st7_REF_HOST_ADDR v_hostaddr)) = True"
		| "is_val (admininstr_sc7 (admininstr_st7_REF_FUNC_ADDR v_funcaddr)) = True"
		| "is_val (admininstr_sc4 (admininstr_st4_REF_NULL v_reftype)) = True"
		| "is_val (admininstr_sc2 (admininstr_st2_VCONST v_vectype var_1)) = True"
		| "is_val (admininstr_sc1 (admininstr_st1_CONST v_numtype var_0)) = True"
		| "is_val v_admininstr = False"
	by pat_completeness auto

(* Auxiliary Definition at: isabelle/wasm-2.0/C-mech-aux.spectec:5.1-5.33 *)
function (sequential, domintros) is_instr :: "admininstr \<Rightarrow> bool" where
		  "is_instr (admininstr_sc7 (admininstr_st7_DATA_DROP dataidx_0)) = True"
		| "is_instr (admininstr_sc7 (admininstr_st7_MEMORY_INIT v_dataidx)) = True"
		| "is_instr (admininstr_sc7 admininstr_st7_MEMORY_COPY) = True"
		| "is_instr (admininstr_sc7 admininstr_st7_MEMORY_FILL) = True"
		| "is_instr (admininstr_sc7 admininstr_st7_MEMORY_GROW) = True"
		| "is_instr (admininstr_sc6 admininstr_st6_MEMORY_SIZE) = True"
		| "is_instr (admininstr_sc6 (admininstr_st6_VSTORE_LANE vectype_7 sz_0 memarg_4 laneidx_2)) = True"
		| "is_instr (admininstr_sc6 (admininstr_st6_VSTORE vectype_6 memarg_3)) = True"
		| "is_instr (admininstr_sc6 (admininstr_st6_VLOAD_LANE vectype_5 v_sz memarg_2 laneidx_1)) = True"
		| "is_instr (admininstr_sc6 (admininstr_st6_VLOAD vectype_4 vloadop_opt memarg_1)) = True"
		| "is_instr (admininstr_sc6 (admininstr_st6_STORE numtype_6 sz_opt memarg_0)) = True"
		| "is_instr (admininstr_sc6 (admininstr_st6_LOAD numtype_5 var_14_opt v_memarg)) = True"
		| "is_instr (admininstr_sc6 (admininstr_st6_ELEM_DROP elemidx_0)) = True"
		| "is_instr (admininstr_sc6 (admininstr_st6_TABLE_INIT tableidx_7 v_elemidx)) = True"
		| "is_instr (admininstr_sc5 (admininstr_st5_TABLE_COPY tableidx_5 tableidx_6)) = True"
		| "is_instr (admininstr_sc5 (admininstr_st5_TABLE_FILL tableidx_4)) = True"
		| "is_instr (admininstr_sc5 (admininstr_st5_TABLE_GROW tableidx_3)) = True"
		| "is_instr (admininstr_sc5 (admininstr_st5_TABLE_SIZE tableidx_2)) = True"
		| "is_instr (admininstr_sc5 (admininstr_st5_TABLE_SET tableidx_1)) = True"
		| "is_instr (admininstr_sc5 (admininstr_st5_TABLE_GET tableidx_0)) = True"
		| "is_instr (admininstr_sc5 (admininstr_st5_GLOBAL_SET globalidx_0)) = True"
		| "is_instr (admininstr_sc5 (admininstr_st5_GLOBAL_GET v_globalidx)) = True"
		| "is_instr (admininstr_sc5 (admininstr_st5_LOCAL_TEE localidx_1)) = True"
		| "is_instr (admininstr_sc4 (admininstr_st4_LOCAL_SET localidx_0)) = True"
		| "is_instr (admininstr_sc4 (admininstr_st4_LOCAL_GET v_localidx)) = True"
		| "is_instr (admininstr_sc4 admininstr_st4_REF_IS_NULL) = True"
		| "is_instr (admininstr_sc4 (admininstr_st4_REF_FUNC funcidx_0)) = True"
		| "is_instr (admininstr_sc4 (admininstr_st4_REF_NULL v_reftype)) = True"
		| "is_instr (admininstr_sc4 (admininstr_st4_VCVTOP shape_6 shape_7 v_vcvtop)) = True"
		| "is_instr (admininstr_sc4 (admininstr_st4_VNARROW ishape_1_2 ishape_2_2 v_sx)) = True"
		| "is_instr (admininstr_sc4 (admininstr_st4_VEXTBINOP ishape_1_1 ishape_2_1 var_13)) = True"
		| "is_instr (admininstr_sc4 (admininstr_st4_VEXTUNOP ishape_1_0 ishape_2_0 var_12)) = True"
		| "is_instr (admininstr_sc3 (admininstr_st3_VREPLACE_LANE shape_5 laneidx_0)) = True"
		| "is_instr (admininstr_sc3 (admininstr_st3_VEXTRACT_LANE shape_4 sx_opt v_laneidx)) = True"
		| "is_instr (admininstr_sc3 (admininstr_st3_VSPLAT shape_3)) = True"
		| "is_instr (admininstr_sc3 (admininstr_st3_VSHUFFLE ishape_2 laneidx_lst)) = True"
		| "is_instr (admininstr_sc3 (admininstr_st3_VSWIZZLE ishape_1)) = True"
		| "is_instr (admininstr_sc3 (admininstr_st3_VBITMASK ishape_0)) = True"
		| "is_instr (admininstr_sc3 (admininstr_st3_VSHIFTOP v_ishape var_11)) = True"
		| "is_instr (admininstr_sc3 (admininstr_st3_VRELOP shape_2 var_10)) = True"
		| "is_instr (admininstr_sc3 (admininstr_st3_VTESTOP shape_1 var_9)) = True"
		| "is_instr (admininstr_sc2 (admininstr_st2_VBINOP shape_0 var_8)) = True"
		| "is_instr (admininstr_sc2 (admininstr_st2_VUNOP v_shape var_7)) = True"
		| "is_instr (admininstr_sc2 (admininstr_st2_VVTESTOP vectype_3 v_vvtestop)) = True"
		| "is_instr (admininstr_sc2 (admininstr_st2_VVTERNOP vectype_2 v_vvternop)) = True"
		| "is_instr (admininstr_sc2 (admininstr_st2_VVBINOP vectype_1 v_vvbinop)) = True"
		| "is_instr (admininstr_sc2 (admininstr_st2_VVUNOP vectype_0 v_vvunop)) = True"
		| "is_instr (admininstr_sc2 (admininstr_st2_VCONST v_vectype var_6)) = True"
		| "is_instr (admininstr_sc2 (admininstr_st2_EXTEND numtype_4 v_n)) = True"
		| "is_instr (admininstr_sc2 (admininstr_st2_CVTOP numtype_1_0 numtype_2_0 var_5)) = True"
		| "is_instr (admininstr_sc1 (admininstr_st1_RELOP numtype_3 var_4)) = True"
		| "is_instr (admininstr_sc1 (admininstr_st1_TESTOP numtype_2 var_3)) = True"
		| "is_instr (admininstr_sc1 (admininstr_st1_BINOP numtype_1 var_2)) = True"
		| "is_instr (admininstr_sc1 (admininstr_st1_UNOP numtype_0 var_1)) = True"
		| "is_instr (admininstr_sc1 (admininstr_st1_CONST v_numtype var_0)) = True"
		| "is_instr (admininstr_sc1 admininstr_st1_RETURN) = True"
		| "is_instr (admininstr_sc1 (admininstr_st1_CALL_INDIRECT v_tableidx v_typeidx)) = True"
		| "is_instr (admininstr_sc1 (admininstr_st1_CALL v_funcidx)) = True"
		| "is_instr (admininstr_sc1 (admininstr_st1_BR_TABLE labelidx_lst labelidx_1)) = True"
		| "is_instr (admininstr_sc0 (admininstr_st0_BR_IF labelidx_0)) = True"
		| "is_instr (admininstr_sc0 (admininstr_st0_BR v_labelidx)) = True"
		| "is_instr (admininstr_sc0 (admininstr_st0_IFELSE blocktype_1 instr_lst_0_lst instr_lst_1_lst)) = True"
		| "is_instr (admininstr_sc0 (admininstr_st0_LOOP blocktype_0 instr_lst_0_lst)) = True"
		| "is_instr (admininstr_sc0 (admininstr_st0_BLOCK v_blocktype instr_lst)) = True"
		| "is_instr (admininstr_sc0 (admininstr_st0_SELECT valtype_lst_opt)) = True"
		| "is_instr (admininstr_sc0 admininstr_st0_DROP) = True"
		| "is_instr (admininstr_sc0 admininstr_st0_UNREACHABLE) = True"
		| "is_instr (admininstr_sc0 admininstr_st0_NOP) = True"
		| "is_instr v_admininstr = False"
	by pat_completeness auto

(* Auxiliary Definition at: isabelle/wasm-2.0/C-mech-aux.spectec:9.1-9.38 *)
function (sequential, domintros) is_admininstr :: "admininstr \<Rightarrow> bool" where
		  "is_admininstr (admininstr_sc7 (admininstr_st7_DATA_DROP dataidx_0)) = False"
		| "is_admininstr (admininstr_sc7 (admininstr_st7_MEMORY_INIT v_dataidx)) = False"
		| "is_admininstr (admininstr_sc7 admininstr_st7_MEMORY_COPY) = False"
		| "is_admininstr (admininstr_sc7 admininstr_st7_MEMORY_FILL) = False"
		| "is_admininstr (admininstr_sc7 admininstr_st7_MEMORY_GROW) = False"
		| "is_admininstr (admininstr_sc6 admininstr_st6_MEMORY_SIZE) = False"
		| "is_admininstr (admininstr_sc6 (admininstr_st6_VSTORE_LANE vectype_7 sz_0 memarg_4 laneidx_2)) = False"
		| "is_admininstr (admininstr_sc6 (admininstr_st6_VSTORE vectype_6 memarg_3)) = False"
		| "is_admininstr (admininstr_sc6 (admininstr_st6_VLOAD_LANE vectype_5 v_sz memarg_2 laneidx_1)) = False"
		| "is_admininstr (admininstr_sc6 (admininstr_st6_VLOAD vectype_4 vloadop_opt memarg_1)) = False"
		| "is_admininstr (admininstr_sc6 (admininstr_st6_STORE numtype_6 sz_opt memarg_0)) = False"
		| "is_admininstr (admininstr_sc6 (admininstr_st6_LOAD numtype_5 var_14_opt v_memarg)) = False"
		| "is_admininstr (admininstr_sc6 (admininstr_st6_ELEM_DROP elemidx_0)) = False"
		| "is_admininstr (admininstr_sc6 (admininstr_st6_TABLE_INIT tableidx_7 v_elemidx)) = False"
		| "is_admininstr (admininstr_sc5 (admininstr_st5_TABLE_COPY tableidx_5 tableidx_6)) = False"
		| "is_admininstr (admininstr_sc5 (admininstr_st5_TABLE_FILL tableidx_4)) = False"
		| "is_admininstr (admininstr_sc5 (admininstr_st5_TABLE_GROW tableidx_3)) = False"
		| "is_admininstr (admininstr_sc5 (admininstr_st5_TABLE_SIZE tableidx_2)) = False"
		| "is_admininstr (admininstr_sc5 (admininstr_st5_TABLE_SET tableidx_1)) = False"
		| "is_admininstr (admininstr_sc5 (admininstr_st5_TABLE_GET tableidx_0)) = False"
		| "is_admininstr (admininstr_sc5 (admininstr_st5_GLOBAL_SET globalidx_0)) = False"
		| "is_admininstr (admininstr_sc5 (admininstr_st5_GLOBAL_GET v_globalidx)) = False"
		| "is_admininstr (admininstr_sc5 (admininstr_st5_LOCAL_TEE localidx_1)) = False"
		| "is_admininstr (admininstr_sc4 (admininstr_st4_LOCAL_SET localidx_0)) = False"
		| "is_admininstr (admininstr_sc4 (admininstr_st4_LOCAL_GET v_localidx)) = False"
		| "is_admininstr (admininstr_sc4 admininstr_st4_REF_IS_NULL) = False"
		| "is_admininstr (admininstr_sc4 (admininstr_st4_REF_FUNC funcidx_0)) = False"
		| "is_admininstr (admininstr_sc4 (admininstr_st4_REF_NULL v_reftype)) = False"
		| "is_admininstr (admininstr_sc4 (admininstr_st4_VCVTOP shape_6 shape_7 v_vcvtop)) = False"
		| "is_admininstr (admininstr_sc4 (admininstr_st4_VNARROW ishape_1_2 ishape_2_2 v_sx)) = False"
		| "is_admininstr (admininstr_sc4 (admininstr_st4_VEXTBINOP ishape_1_1 ishape_2_1 var_13)) = False"
		| "is_admininstr (admininstr_sc4 (admininstr_st4_VEXTUNOP ishape_1_0 ishape_2_0 var_12)) = False"
		| "is_admininstr (admininstr_sc3 (admininstr_st3_VREPLACE_LANE shape_5 laneidx_0)) = False"
		| "is_admininstr (admininstr_sc3 (admininstr_st3_VEXTRACT_LANE shape_4 sx_opt v_laneidx)) = False"
		| "is_admininstr (admininstr_sc3 (admininstr_st3_VSPLAT shape_3)) = False"
		| "is_admininstr (admininstr_sc3 (admininstr_st3_VSHUFFLE ishape_2 laneidx_lst)) = False"
		| "is_admininstr (admininstr_sc3 (admininstr_st3_VSWIZZLE ishape_1)) = False"
		| "is_admininstr (admininstr_sc3 (admininstr_st3_VBITMASK ishape_0)) = False"
		| "is_admininstr (admininstr_sc3 (admininstr_st3_VSHIFTOP v_ishape var_11)) = False"
		| "is_admininstr (admininstr_sc3 (admininstr_st3_VRELOP shape_2 var_10)) = False"
		| "is_admininstr (admininstr_sc3 (admininstr_st3_VTESTOP shape_1 var_9)) = False"
		| "is_admininstr (admininstr_sc2 (admininstr_st2_VBINOP shape_0 var_8)) = False"
		| "is_admininstr (admininstr_sc2 (admininstr_st2_VUNOP v_shape var_7)) = False"
		| "is_admininstr (admininstr_sc2 (admininstr_st2_VVTESTOP vectype_3 v_vvtestop)) = False"
		| "is_admininstr (admininstr_sc2 (admininstr_st2_VVTERNOP vectype_2 v_vvternop)) = False"
		| "is_admininstr (admininstr_sc2 (admininstr_st2_VVBINOP vectype_1 v_vvbinop)) = False"
		| "is_admininstr (admininstr_sc2 (admininstr_st2_VVUNOP vectype_0 v_vvunop)) = False"
		| "is_admininstr (admininstr_sc2 (admininstr_st2_VCONST v_vectype var_6)) = False"
		| "is_admininstr (admininstr_sc2 (admininstr_st2_EXTEND numtype_4 v_n)) = False"
		| "is_admininstr (admininstr_sc2 (admininstr_st2_CVTOP numtype_1_0 numtype_2_0 var_5)) = False"
		| "is_admininstr (admininstr_sc1 (admininstr_st1_RELOP numtype_3 var_4)) = False"
		| "is_admininstr (admininstr_sc1 (admininstr_st1_TESTOP numtype_2 var_3)) = False"
		| "is_admininstr (admininstr_sc1 (admininstr_st1_BINOP numtype_1 var_2)) = False"
		| "is_admininstr (admininstr_sc1 (admininstr_st1_UNOP numtype_0 var_1)) = False"
		| "is_admininstr (admininstr_sc1 (admininstr_st1_CONST v_numtype var_0)) = False"
		| "is_admininstr (admininstr_sc1 admininstr_st1_RETURN) = False"
		| "is_admininstr (admininstr_sc1 (admininstr_st1_CALL_INDIRECT v_tableidx v_typeidx)) = False"
		| "is_admininstr (admininstr_sc1 (admininstr_st1_CALL v_funcidx)) = False"
		| "is_admininstr (admininstr_sc1 (admininstr_st1_BR_TABLE labelidx_lst labelidx_1)) = False"
		| "is_admininstr (admininstr_sc0 (admininstr_st0_BR_IF labelidx_0)) = False"
		| "is_admininstr (admininstr_sc0 (admininstr_st0_BR v_labelidx)) = False"
		| "is_admininstr (admininstr_sc0 (admininstr_st0_IFELSE blocktype_1 instr_lst_0_lst instr_lst_1_lst)) = False"
		| "is_admininstr (admininstr_sc0 (admininstr_st0_LOOP blocktype_0 instr_lst_0_lst)) = False"
		| "is_admininstr (admininstr_sc0 (admininstr_st0_BLOCK v_blocktype instr_lst)) = False"
		| "is_admininstr (admininstr_sc0 (admininstr_st0_SELECT valtype_lst_opt)) = False"
		| "is_admininstr (admininstr_sc0 admininstr_st0_DROP) = False"
		| "is_admininstr (admininstr_sc0 admininstr_st0_UNREACHABLE) = False"
		| "is_admininstr (admininstr_sc0 admininstr_st0_NOP) = False"
		| "is_admininstr v_admininstr = True"
	by pat_completeness auto

(* Inductive Type Definition at: isabelle/wasm-2.0/C-mech-aux.spectec:13.1-13.44 *)
datatype instrtype =
	  mk_instrtype "resulttype" "resulttype"
	

(* Inductive Relations Definition at: isabelle/wasm-2.0/C-mech-aux.spectec:15.1-15.50 *)
inductive Instrtype_sub :: "instrtype \<Rightarrow> instrtype \<Rightarrow> bool" where
	  mk_Instrtype_sub :
		"(t_21_lst = (t_lst @ t_11'_lst)) \<Longrightarrow>
		 (t_22_lst = (t'_lst @ t_12'_lst)) \<Longrightarrow>
		 (Resulttype_sub (mk_list t_lst) (mk_list t'_lst)) \<Longrightarrow>
		 (Resulttype_sub (mk_list t_11'_lst) (mk_list t_11_lst)) \<Longrightarrow>
		 (Resulttype_sub (mk_list t_12_lst) (mk_list t_12'_lst)) \<Longrightarrow>
		 Instrtype_sub (mk_instrtype (mk_list t_11_lst) (mk_list t_12_lst)) (mk_instrtype (mk_list t_21_lst) (mk_list t_22_lst))"

(* Auxiliary Definition at: isabelle/wasm-2.0/C-mech-aux.spectec:24.1-24.30 *)
function (sequential, domintros) typeofval :: "val \<Rightarrow> valtype" where
		  "typeofval (val_CONST v_numtype c) = (valtype_numtype v_numtype)"
		| "typeofval (val_VCONST v_vectype c) = (valtype_vectype v_vectype)"
		| "typeofval (val_REF_NULL v_reftype) = (valtype_reftype v_reftype)"
		| "typeofval (val_REF_FUNC_ADDR v_funcaddr) = valtype_FUNCREF"
		| "typeofval (val_REF_HOST_ADDR v_hostaddr) = valtype_EXTERNREF"
	by pat_completeness auto

(* Inductive Relations Definition at: isabelle/wasm-2.0/C-mech-aux.spectec:31.6-31.18 *)
inductive fun_typesofvals :: "(val list) \<Rightarrow> (valtype list) \<Rightarrow> bool" where
	  fun_typesofvals_case_0 :
		"((length val_lst) = (length valtype_lst)) \<Longrightarrow>
		 list_all2 (\<lambda> (val_8 :: val) (valtype_215 :: valtype). ((typeofval val_8) = valtype_215)) val_lst valtype_lst \<Longrightarrow>
		 fun_typesofvals val_lst valtype_lst"

end

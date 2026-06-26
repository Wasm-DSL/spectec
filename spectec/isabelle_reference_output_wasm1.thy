theory reference_isabelle_output_wasm1
(* Imported Code *)
	imports Main
begin

inductive list_all3 :: "('a ⇒ 'b ⇒ 'c ⇒ bool) ⇒ 'a list ⇒ 'b list ⇒ 'c list ⇒ bool" where
	list_all3_nil : "list_all3 R [] [] []" |
	list_all3_cons: "R a b c ⟹ list_all3 R as bs cs ⟹ list_all3 R (a # as) (b # bs) (c # cs)"

definition list_zipWith :: "('a ⇒ 'b ⇒ 'c) ⇒ 'a list ⇒ 'b list ⇒ 'c list" where
	"list_zipWith f xs ys = map (λ (x, y). f x y) (zip xs ys)"

definition list_map3 :: "('a ⇒ 'b ⇒ 'c ⇒ 'd) ⇒ 'a list ⇒ 'b list ⇒ 'c list ⇒ 'd list" where
	"list_map3 f xs ys zs = map (λ (x, (y, z)). f x y z) (zip xs (zip ys zs))"

inductive foralli_help :: "(nat ⇒ 'a ⇒ bool) ⇒ nat ⇒ 'a list ⇒ bool" where
	foralli_nil : "foralli_help f n []" |
	foralli_cons : "f n x ⟹ foralli_help f (n + 1) l ⟹ foralli_help f n (x # l)"

definition list_foralli :: "(nat ⇒ 'a ⇒ bool) ⇒ 'a list ⇒ bool" where
	"list_foralli f xs = foralli_help f 0 xs"

fun option_zipWith :: "('a ⇒ 'b ⇒ 'c) ⇒ 'a option ⇒ 'b option ⇒ 'c option" where
	"option_zipWith f (Some x) (Some y) = Some (f x y)" |
	"option_zipWith _ _ _ = None"

fun option_map3 :: "('a ⇒ 'b ⇒ 'c ⇒ 'd) ⇒ 'a option ⇒ 'b option ⇒ 'c option ⇒ 'd option" where
	"option_map3 f (Some x) (Some y) (Some z) = Some (f x y z)" |
	"option_map3 f _ _ _ = None"

fun option_to_list :: "'a option ⇒'a list" where
	"option_to_list None = []" |
	"option_to_list (Some a) = [a]"

fun list_slice :: "'a list ⇒ nat ⇒ nat ⇒ 'a list" where
	"list_slice [] _ _ = []" |
	"list_slice (x # l) 0 0 = []" |
	"list_slice (x # l) (Suc n) 0 = []" |
	"list_slice (x # l) 0 (Suc m) = x # list_slice l 0 m" |
	"list_slice (x # l) (Suc n) m = list_slice l n m"

fun mkseq :: "(nat ⇒ 'a) ⇒ nat ⇒'a list" where
	"mkseq _ 0 = []" |
	"mkseq f (Suc n) = mkseq f n @ [f n]"

fun repeat :: "nat ⇒ 'a ⇒ 'a list" where
	"repeat 0 _ = []" |
	"repeat (Suc n) x = x # repeat n x"

fun list_update_func :: "'a list ⇒ nat ⇒ ('a ⇒ 'a) ⇒ 'a list" where
	"list_update_func [] _ _ = []" |
	"list_update_func (x # l) 0 y = (y x) # l" |
	"list_update_func (x # l) (Suc n) y = x # list_update_func l n y"

fun list_slice_update :: "'a list ⇒ nat ⇒ nat ⇒ 'a list ⇒ 'a list" where
	"list_slice_update [] _ _ _ = []" |
	"list_slice_update l _ _ [] = l" |
	"list_slice_update (x # l) _ 0 _ = []" |
	"list_slice_update (x # l) 0 (Suc m) (y # ul) = y # list_slice_update l 0 m ul" |
	"list_slice_update (x # l) (Suc n) m ul = x # list_slice_update l n m ul"

fun option_append :: "'a option ⇒ 'a option ⇒ 'a option" (infixl "@@@" 70) where
	"option_append (Some x) _ = Some x" |
	"option_append None y = y"

fun list_alli_aux :: "(nat ⇒ 'a ⇒ bool) ⇒ nat ⇒ 'a list ⇒ bool" where
	"list_alli_aux f n [] = True" |
	"list_alli_aux f n (x # q) = (f n x ∧ list_alli_aux f (Suc n) q)"

definition list_alli :: "(nat ⇒ 'a ⇒ bool) ⇒ 'a list ⇒ bool" where
	"list_alli f l = list_alli_aux f 0 l"

definition holds_upto :: "(nat ⇒ bool) ⇒ nat ⇒ bool" where
	"holds_upto P n ≡ ∀ i < n. P i"

(* Generated Code *)
(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:119.14-119.17 *)
datatype r_MUT =
	  MUT
	

(* Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:7.1-7.27 *)
type_synonym N = "nat"

(* Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:8.1-8.27 *)
type_synonym M = "nat"

(* Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:9.1-9.27 *)
type_synonym n = "nat"

(* Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:10.1-10.27 *)
type_synonym m = "nat"

(* Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:15.1-15.14 *)
definition Ki :: "nat" where
	"Ki = 1024"

(* Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:21.1-21.25 *)
function (sequential) min :: "nat ⇒ nat ⇒ nat" where
		  "min i j = (if (i ≤ j) then i else j)"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-1.0/0-aux.spectec:25.1-25.21 *)
inductive fun_sum :: "(nat list) ⇒ nat ⇒ bool" where
	  fun_sum_case_0 :
		"fun_sum [] 0"
	| fun_sum_case_1 :
		"(fun_sum n'_lst var_0) ⟹
		 fun_sum ([v_n] @ n'_lst) (v_n + var_0)"

(* Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:32.1-32.58 *)
function (sequential) opt_underscore :: "('X list) ⇒ (('X option) option)" where
		  "opt_underscore  [] = (Some None)"
		| "opt_underscore  [w] = (Some (Some w))"
		| "opt_underscore  x1 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:36.1-36.45 *)
function (sequential) list_underscore :: "('X option) ⇒ ('X list)" where
		  "list_underscore  None = []"
		| "list_underscore  (Some w) = [w]"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-1.0/0-aux.spectec:40.1-40.59 *)
function (sequential) concat_underscore :: "(('X list) list) ⇒ ('X list)" where
		  "concat_underscore  [] = []"
		| "concat_underscore  (w_lst # w'_lst_lst) = (w_lst @ (concat_underscore  w'_lst_lst))"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-1.0/0-aux.spectec:44.1-44.78 *)
function (sequential) disjoint_underscore :: "('X list) ⇒ bool" where
		  "disjoint_underscore  [] = True"
		| "disjoint_underscore  (w # w'_lst) = ((~ (w ∈ set w'_lst)) ∧ (disjoint_underscore  w'_lst))"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:6.1-6.49 *)
datatype 'X res_list  =
	  mk_list "('X list)"
	

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:15.1-15.50 *)
datatype byte =
	  mk_byte "nat"
	

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:15.1-15.50 *)
function (sequential) proj_byte_0 :: "byte ⇒ (nat)" where
		  "proj_byte_0 (mk_byte v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:15.8-15.12 *)
inductive wf_byte :: "byte ⇒ bool" where
	  byte_case_0 :
		"((i ≥ 0) ∧ (i ≤ 255)) ⟹
		 wf_byte (mk_byte i)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:17.1-18.25 *)
datatype uN =
	  mk_uN "nat"
	

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:17.1-18.25 *)
function (sequential) proj_uN_0 :: "uN ⇒ (nat)" where
		  "proj_uN_0 (mk_uN v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:17.8-17.11 *)
inductive wf_uN :: "N ⇒ uN ⇒ bool" where
	  uN_case_0 :
		"((i ≥ 0) ∧ (i ≤ ((((2 ^ v_N) :: nat) - (1 :: nat)) :: nat))) ⟹
		 wf_uN v_N (mk_uN i)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:19.1-20.49 *)
datatype sN =
	  mk_sN "nat"
	

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:19.1-20.49 *)
function (sequential) proj_sN_0 :: "sN ⇒ (nat)" where
		  "proj_sN_0 (mk_sN v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:19.8-19.11 *)
inductive wf_sN :: "N ⇒ sN ⇒ bool" where
	  sN_case_0 :
		"((((i ≥ (0 - ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat))) ∧ (i ≤ (0 - (1 :: nat)))) ∨ (i = (0 :: nat))) ∨ ((i ≥ ((1 :: nat))) ∧ (i ≤ (((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat) - (1 :: nat))))) ⟹
		 wf_sN v_N (mk_sN i)"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:21.1-22.8 *)
type_synonym iN = "uN"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:24.1-24.20 *)
type_synonym u31 = "uN"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:25.1-25.20 *)
type_synonym u32 = "uN"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:26.1-26.20 *)
type_synonym u64 = "uN"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:28.1-28.20 *)
type_synonym i32 = "iN"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:29.1-29.20 *)
type_synonym i64 = "iN"

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:36.1-36.35 *)
function (sequential) signif :: "N ⇒ (nat option)" where
		  "signif (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some 23)"
		| "signif (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some 52)"
		| "signif x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:40.1-40.34 *)
function (sequential) expon :: "N ⇒ (nat option)" where
		  "expon (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) = (Some 8)"
		| "expon (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (Some 11)"
		| "expon x0 = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:44.1-44.30 *)
function (sequential) fun_M :: "N ⇒ nat" where
		  "fun_M v_N = (the ((signif v_N)))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:47.1-47.30 *)
function (sequential) E :: "N ⇒ nat" where
		  "E v_N = (the ((expon v_N)))"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:54.1-54.30 *)
type_synonym exp = "nat"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:55.1-59.84 *)
datatype fNmag =
	  NORM "m" "exp"
	| SUBNORM "m"
	| res_INF
	| NAN "m"

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:55.8-55.14 *)
inductive wf_fNmag :: "N ⇒ fNmag ⇒ bool" where
	  fNmag_case_0 :
		"((v_m < (2 ^ (fun_M v_N))) ∧ ((((2 :: nat) - ((2 ^ ((((E v_N) :: nat) - (1 :: nat)) :: nat)) :: nat)) ≤ v_exp) ∧ (v_exp ≤ (((2 ^ ((((E v_N) :: nat) - (1 :: nat)) :: nat)) :: nat) - (1 :: nat))))) ⟹
		 wf_fNmag v_N (NORM v_m v_exp)"
	| fNmag_case_1 :
		"((v_m < (2 ^ (fun_M v_N))) ∧ (((2 :: nat) - ((2 ^ ((((E v_N) :: nat) - (1 :: nat)) :: nat)) :: nat)) = v_exp)) ⟹
		 wf_fNmag v_N (SUBNORM v_m)"
	| fNmag_case_2 :
		"wf_fNmag v_N res_INF"
	| fNmag_case_3 :
		"((1 ≤ v_m) ∧ (v_m < (2 ^ (fun_M v_N)))) ⟹
		 wf_fNmag v_N (NAN v_m)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:50.1-52.35 *)
datatype fN =
	  POS "fNmag"
	| NEG "fNmag"

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:50.8-50.11 *)
inductive wf_fN :: "N ⇒ fN ⇒ bool" where
	  fN_case_0 :
		"(wf_fNmag v_N var_0) ⟹
		 wf_fN v_N (POS var_0)"
	| fN_case_1 :
		"(wf_fNmag v_N var_0) ⟹
		 wf_fN v_N (NEG var_0)"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:61.1-61.20 *)
type_synonym f32 = "fN"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:62.1-62.20 *)
type_synonym f64 = "fN"

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:64.1-64.39 *)
function (sequential) fzero :: "N ⇒ fN" where
		  "fzero v_N = (POS (SUBNORM 0))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:64.6-64.12 *)
lemma fzero_is_wf :
	"(ret_val = (fzero v_N)) ⟹
	 (wf_fN v_N ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:67.1-67.39 *)
function (sequential) fone :: "N ⇒ fN" where
		  "fone v_N = (POS (NORM 1 (0 :: nat)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:67.6-67.11 *)
lemma fone_is_wf :
	"(ret_val = (fone v_N)) ⟹
	 (wf_fN v_N ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:70.1-70.21 *)
function (sequential) canon_underscore :: "N ⇒ nat" where
		  "canon_underscore v_N = (2 ^ ((((the ((signif v_N))) :: nat) - (1 :: nat)) :: nat))"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:78.1-78.85 *)
datatype res_char =
	  mk_char "nat"
	

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:78.1-78.85 *)
function (sequential) proj_char_0 :: "res_char ⇒ (nat)" where
		  "proj_char_0 (mk_char v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:78.8-78.12 *)
inductive wf_char :: "res_char ⇒ bool" where
	  char_case_0 :
		"(((i ≥ 0) ∧ (i ≤ 55295)) ∨ ((i ≥ 57344) ∧ (i ≤ 1114111))) ⟹
		 wf_char (mk_char i)"

(* Mutual Recursion at: ../specification/wasm-1.0/1-syntax.spectec:80.1-80.25 *)
inductive fun_utf8 :: "(res_char list) ⇒ (byte list) ⇒ bool" where
	  fun_utf8_case_0 :
		"(((proj_char_0 ch) < 128) ∧ ((mk_byte (proj_char_0 ch)) = b)) ⟹
		 (wf_byte (mk_byte (proj_char_0 ch))) ⟹
		 fun_utf8 [ch] [b]"
	| fun_utf8_case_1 :
		"(((128 ≤ (proj_char_0 ch)) ∧ ((proj_char_0 ch) < 2048)) ∧ ((proj_char_0 ch) = (((2 ^ 6) * ((((proj_byte_0 b_1) :: nat) - (192 :: nat)) :: nat)) + ((((proj_byte_0 b_2) :: nat) - (128 :: nat)) :: nat)))) ⟹
		 fun_utf8 [ch] [b_1, b_2]"
	| fun_utf8_case_2 :
		"((((2048 ≤ (proj_char_0 ch)) ∧ ((proj_char_0 ch) < 55296)) ∨ ((57344 ≤ (proj_char_0 ch)) ∧ ((proj_char_0 ch) < 65536))) ∧ ((proj_char_0 ch) = ((((2 ^ 12) * ((((proj_byte_0 b_1) :: nat) - (224 :: nat)) :: nat)) + ((2 ^ 6) * ((((proj_byte_0 b_2) :: nat) - (128 :: nat)) :: nat))) + ((((proj_byte_0 b_3) :: nat) - (128 :: nat)) :: nat)))) ⟹
		 fun_utf8 [ch] [b_1, b_2, b_3]"
	| fun_utf8_case_3 :
		"(((65536 ≤ (proj_char_0 ch)) ∧ ((proj_char_0 ch) < 69632)) ∧ ((proj_char_0 ch) = (((((2 ^ 18) * ((((proj_byte_0 b_1) :: nat) - (240 :: nat)) :: nat)) + ((2 ^ 12) * ((((proj_byte_0 b_2) :: nat) - (128 :: nat)) :: nat))) + ((2 ^ 6) * ((((proj_byte_0 b_3) :: nat) - (128 :: nat)) :: nat))) + ((((proj_byte_0 b_4) :: nat) - (128 :: nat)) :: nat)))) ⟹
		 fun_utf8 [ch] [b_1, b_2, b_3, b_4]"
	| fun_utf8_case_4 :
		"((length var_0_lst) = (length ch_lst)) ⟹
		 list_all2 (λ (var_0 :: (byte list)) (ch :: res_char). (fun_utf8 [ch] var_0)) var_0_lst ch_lst ⟹
		 fun_utf8 ch_lst (concat_underscore  var_0_lst)"

(* Mutual Recursion at: ../specification/wasm-1.0/1-syntax.spectec:80.1-80.25 *)
inductive utf8_is_wf :: "(res_char list) ⇒ (byte list) ⇒ bool" where
	  utf8_is_wf_0 :
		"(fun_utf8 var_0_lst var_0) ⟹
		 list_all (λ (var_0 :: res_char). (wf_char var_0)) var_0_lst ⟹
		 (ret_val_lst = var_0) ⟹
		 list_all (λ (ret_val :: byte). (wf_byte ret_val)) ret_val_lst ⟹
		 utf8_is_wf var_0_lst ret_val_lst"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:82.1-82.70 *)
datatype name =
	  mk_name "(res_char list)"
	

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:82.1-82.70 *)
function (sequential) proj_name_0 :: "name ⇒ ((res_char list))" where
		  "proj_name_0 (mk_name v_char_list_0) = (v_char_list_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:82.8-82.12 *)
inductive wf_name :: "name ⇒ bool" where
	  name_case_0 :
		"(fun_utf8 char_lst var_0) ⟹
		 list_all (λ (v_char :: res_char). (wf_char v_char)) char_lst ⟹
		 ((length var_0) < (2 ^ 32)) ⟹
		 wf_name (mk_name char_lst)"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:91.1-91.36 *)
type_synonym idx = "u32"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:93.1-93.45 *)
type_synonym typeidx = "idx"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:94.1-94.49 *)
type_synonym funcidx = "idx"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:95.1-95.49 *)
type_synonym globalidx = "idx"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:96.1-96.47 *)
type_synonym tableidx = "idx"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:97.1-97.46 *)
type_synonym memidx = "idx"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:98.1-98.47 *)
type_synonym labelidx = "idx"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:99.1-99.47 *)
type_synonym localidx = "idx"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:108.1-109.26 *)
datatype valtype =
	  I32
	| I64
	| F32
	| F64

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:111.1-111.38 *)
datatype Inn =
	  Inn_I32
	| Inn_I64

(* Auxiliary Definition at:  *)
function (sequential) valtype_Inn :: "Inn ⇒ valtype" where
		  "valtype_Inn Inn_I32 = I32"
		| "valtype_Inn Inn_I64 = I64"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:112.1-112.38 *)
datatype Fnn =
	  Fnn_F32
	| Fnn_F64

(* Auxiliary Definition at:  *)
function (sequential) valtype_Fnn :: "Fnn ⇒ valtype" where
		  "valtype_Fnn Fnn_F32 = F32"
		| "valtype_Fnn Fnn_F64 = F64"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:116.1-117.11 *)
type_synonym resulttype = "(valtype option)"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:119.1-119.18 *)
type_synonym mut = "(r_MUT option)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:121.1-122.17 *)
datatype limits =
	  mk_limits "u32" "(u32 option)"
	

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:121.8-121.14 *)
inductive wf_limits :: "limits ⇒ bool" where
	  limits_case_0 :
		"(wf_uN 32 v_u32) ⟹
		 wf_limits (mk_limits v_u32 u32_opt)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:123.1-124.14 *)
datatype globaltype =
	  mk_globaltype "mut" "valtype"
	

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:125.1-126.23 *)
datatype functype =
	  mk_functype "(valtype list)" "(valtype list)"
	

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:127.1-128.9 *)
type_synonym tabletype = "limits"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:129.1-130.9 *)
type_synonym memtype = "limits"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:131.1-132.70 *)
datatype externtype =
	  FUNC "functype"
	| GLOBAL "globaltype"
	| TABLE "tabletype"
	| MEM "memtype"

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:131.8-131.18 *)
inductive wf_externtype :: "externtype ⇒ bool" where
	  externtype_case_0 :
		"wf_externtype (FUNC v_functype)"
	| externtype_case_1 :
		"wf_externtype (GLOBAL v_globaltype)"
	| externtype_case_2 :
		"(wf_limits v_tabletype) ⟹
		 wf_externtype (TABLE v_tabletype)"
	| externtype_case_3 :
		"(wf_limits v_memtype) ⟹
		 wf_externtype (MEM v_memtype)"

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:144.1-144.41 *)
function (sequential) size :: "valtype ⇒ nat" where
		  "size I32 = 32"
		| "size I64 = 64"
		| "size F32 = 32"
		| "size F64 = 64"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:146.1-146.21 *)
datatype val_underscore =
	  mk_val__0 "Inn" "iN"
	| mk_val__1 "Fnn" "fN"

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:146.8-146.13 *)
inductive wf_val_underscore :: "valtype ⇒ val_underscore ⇒ bool" where
	  val__case_0 :
		"(wf_uN (size (valtype_Inn v_Inn)) var_x) ⟹
		 (v_valtype = (valtype_Inn v_Inn)) ⟹
		 wf_val_underscore v_valtype (mk_val__0 v_Inn var_x)"
	| val__case_1 :
		"(wf_fN (size (valtype_Fnn v_Fnn)) var_x) ⟹
		 (v_valtype = (valtype_Fnn v_Fnn)) ⟹
		 wf_val_underscore v_valtype (mk_val__1 v_Fnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:146.1-146.21 *)
function (sequential) proj_val__0 :: "val_underscore ⇒ (iN option)" where
		  "proj_val__0 (mk_val__0 v_Inn var_x) = (Some var_x)"
		| "proj_val__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:146.1-146.21 *)
function (sequential) proj_val__1 :: "val_underscore ⇒ (fN option)" where
		  "proj_val__1 (mk_val__1 v_Fnn var_x) = (Some var_x)"
		| "proj_val__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:153.1-153.42 *)
datatype sx =
	  U
	| S

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:154.1-154.56 *)
datatype sz =
	  mk_sz "nat"
	

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:154.1-154.56 *)
function (sequential) proj_sz_0 :: "sz ⇒ (nat)" where
		  "proj_sz_0 (mk_sz v_num_0) = (v_num_0)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:154.8-154.10 *)
inductive wf_sz :: "sz ⇒ bool" where
	  sz_case_0 :
		"((((i = 8) ∨ (i = 16)) ∨ (i = 32)) ∨ (i = 64)) ⟹
		 wf_sz (mk_sz i)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22 *)
datatype unop_Inn =
	  CLZ
	| CTZ
	| POPCNT

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22 *)
datatype unop_Fnn =
	  ABS
	| unop_Fnn_NEG
	| SQRT
	| CEIL
	| FLOOR
	| TRUNC
	| NEAREST

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22 *)
datatype unop_underscore =
	  mk_unop__0 "Inn" "unop_Inn"
	| mk_unop__1 "Fnn" "unop_Fnn"

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.8-156.14 *)
inductive wf_unop_underscore :: "valtype ⇒ unop_underscore ⇒ bool" where
	  unop__case_0 :
		"(v_valtype = (valtype_Inn v_Inn)) ⟹
		 wf_unop_underscore v_valtype (mk_unop__0 v_Inn var_x)"
	| unop__case_1 :
		"(v_valtype = (valtype_Fnn v_Fnn)) ⟹
		 wf_unop_underscore v_valtype (mk_unop__1 v_Fnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22 *)
function (sequential) proj_unop__0 :: "unop_underscore ⇒ (unop_Inn option)" where
		  "proj_unop__0 (mk_unop__0 v_Inn var_x) = (Some var_x)"
		| "proj_unop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22 *)
function (sequential) proj_unop__1 :: "unop_underscore ⇒ (unop_Fnn option)" where
		  "proj_unop__1 (mk_unop__1 v_Fnn var_x) = (Some var_x)"
		| "proj_unop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23 *)
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

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23 *)
datatype binop_Fnn =
	  binop_Fnn_ADD
	| binop_Fnn_SUB
	| binop_Fnn_MUL
	| binop_Fnn_DIV
	| res_MIN
	| res_MAX
	| COPYSIGN

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23 *)
datatype binop_underscore =
	  mk_binop__0 "Inn" "binop_Inn"
	| mk_binop__1 "Fnn" "binop_Fnn"

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.8-160.15 *)
inductive wf_binop_underscore :: "valtype ⇒ binop_underscore ⇒ bool" where
	  binop__case_0 :
		"(v_valtype = (valtype_Inn v_Inn)) ⟹
		 wf_binop_underscore v_valtype (mk_binop__0 v_Inn var_x)"
	| binop__case_1 :
		"(v_valtype = (valtype_Fnn v_Fnn)) ⟹
		 wf_binop_underscore v_valtype (mk_binop__1 v_Fnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23 *)
function (sequential) proj_binop__0 :: "binop_underscore ⇒ (binop_Inn option)" where
		  "proj_binop__0 (mk_binop__0 v_Inn var_x) = (Some var_x)"
		| "proj_binop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23 *)
function (sequential) proj_binop__1 :: "binop_underscore ⇒ (binop_Fnn option)" where
		  "proj_binop__1 (mk_binop__1 v_Fnn var_x) = (Some var_x)"
		| "proj_binop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:167.1-167.24 *)
datatype testop_Inn =
	  EQZ
	

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:167.1-167.24 *)
datatype testop_underscore =
	  mk_testop__0 "Inn" "testop_Inn"
	

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:167.8-167.16 *)
inductive wf_testop_underscore :: "valtype ⇒ testop_underscore ⇒ bool" where
	  testop__case_0 :
		"(v_valtype = (valtype_Inn v_Inn)) ⟹
		 wf_testop_underscore v_valtype (mk_testop__0 v_Inn var_x)"

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:167.1-167.24 *)
function (sequential) proj_testop__0 :: "testop_underscore ⇒ testop_Inn" where
		  "proj_testop__0 (mk_testop__0 v_Inn var_x) = var_x"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23 *)
datatype relop_Inn =
	  EQ
	| NE
	| LT "sx"
	| GT "sx"
	| LE "sx"
	| GE "sx"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23 *)
datatype relop_Fnn =
	  relop_Fnn_EQ
	| relop_Fnn_NE
	| relop_Fnn_LT
	| relop_Fnn_GT
	| relop_Fnn_LE
	| relop_Fnn_GE

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23 *)
datatype relop_underscore =
	  mk_relop__0 "Inn" "relop_Inn"
	| mk_relop__1 "Fnn" "relop_Fnn"

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.8-171.15 *)
inductive wf_relop_underscore :: "valtype ⇒ relop_underscore ⇒ bool" where
	  relop__case_0 :
		"(v_valtype = (valtype_Inn v_Inn)) ⟹
		 wf_relop_underscore v_valtype (mk_relop__0 v_Inn var_x)"
	| relop__case_1 :
		"(v_valtype = (valtype_Fnn v_Fnn)) ⟹
		 wf_relop_underscore v_valtype (mk_relop__1 v_Fnn var_x)"

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23 *)
function (sequential) proj_relop__0 :: "relop_underscore ⇒ (relop_Inn option)" where
		  "proj_relop__0 (mk_relop__0 v_Inn var_x) = (Some var_x)"
		| "proj_relop__0 var_x = None"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23 *)
function (sequential) proj_relop__1 :: "relop_underscore ⇒ (relop_Fnn option)" where
		  "proj_relop__1 (mk_relop__1 v_Fnn var_x) = (Some var_x)"
		| "proj_relop__1 var_x = None"
	by pat_completeness auto

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:179.1-180.78 *)
datatype cvtop =
	  EXTEND "sx"
	| WRAP
	| CONVERT "sx"
	| cvtop_TRUNC "sx"
	| PROMOTE
	| DEMOTE
	| REINTERPRET

(* Record Creation Definition at: ../specification/wasm-1.0/1-syntax.spectec:185.1-185.69 *)
record memarg =
	ALIGN :: "u32"
	OFFSET :: "u32"

definition append_memarg :: "memarg ⇒ memarg ⇒ memarg" where
	"append_memarg arg1 arg2 = ⦇
		ALIGN = ALIGN arg1,
		OFFSET = OFFSET arg1
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:185.8-185.14 *)
inductive wf_memarg :: "memarg ⇒ bool" where
	  memarg_case_underscore :
		"(wf_uN 32 var_0) ⟹
		 (wf_uN 32 var_1) ⟹
		 wf_memarg ⦇ ALIGN = var_0, OFFSET = var_1 ⦈"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:189.1-189.24 *)
datatype loadop_Inn =
	  mk_loadop_Inn "sz" "sx"
	

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:189.8-189.16 *)
inductive wf_loadop_Inn :: "Inn ⇒ loadop_Inn ⇒ bool" where
	  loadop_Inn_case_0 :
		"(wf_sz v_sz) ⟹
		 ((proj_sz_0 v_sz) < (size (valtype_Inn v_Inn))) ⟹
		 wf_loadop_Inn v_Inn (mk_loadop_Inn v_sz v_sx)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:189.1-189.24 *)
datatype loadop_underscore =
	  mk_loadop__0 "Inn" "loadop_Inn"
	

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:189.8-189.16 *)
inductive wf_loadop_underscore :: "valtype ⇒ loadop_underscore ⇒ bool" where
	  loadop__case_0 :
		"(wf_loadop_Inn v_Inn var_x) ⟹
		 (v_valtype = (valtype_Inn v_Inn)) ⟹
		 wf_loadop_underscore v_valtype (mk_loadop__0 v_Inn var_x)"

(* Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:189.1-189.24 *)
function (sequential) proj_loadop__0 :: "loadop_underscore ⇒ loadop_Inn" where
		  "proj_loadop__0 (mk_loadop__0 v_Inn var_x) = var_x"
	by pat_completeness auto

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:195.1-195.52 *)
type_synonym blocktype = "(valtype option)"

(* Mutual Recursion at: ../specification/wasm-1.0/1-syntax.spectec:245.1-250.16 *)
datatype instr =
	  NOP
	| UNREACHABLE
	| DROP
	| SELECT
	| BLOCK "blocktype" "(instr list)"
	| LOOP "blocktype" "(instr list)"
	| IFELSE "blocktype" "(instr list)" "(instr list)"
	| BR "labelidx"
	| BR_IF "labelidx"
	| BR_TABLE "(labelidx list)" "labelidx"
	| CALL "funcidx"
	| CALL_INDIRECT "typeidx"
	| RETURN
	| res_CONST "valtype" "val_underscore"
	| UNOP "valtype" "unop_underscore"
	| BINOP "valtype" "binop_underscore"
	| TESTOP "valtype" "testop_underscore"
	| RELOP "valtype" "relop_underscore"
	| CVTOP "valtype" "valtype" "cvtop"
	| LOCAL_GET "localidx"
	| LOCAL_SET "localidx"
	| LOCAL_TEE "localidx"
	| GLOBAL_GET "globalidx"
	| GLOBAL_SET "globalidx"
	| LOAD "valtype" "(loadop_underscore option)" "memarg"
	| STORE "valtype" "(sz option)" "memarg"
	| MEMORY_SIZE
	| MEMORY_GROW

(* Mutual Recursion at: ../specification/wasm-1.0/1-syntax.spectec:245.1-250.16 *)
inductive wf_instr :: "instr ⇒ bool" where
	  instr_case_0 :
		"wf_instr NOP"
	| instr_case_1 :
		"wf_instr UNREACHABLE"
	| instr_case_2 :
		"wf_instr DROP"
	| instr_case_3 :
		"wf_instr SELECT"
	| instr_case_4 :
		"list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 wf_instr (BLOCK v_blocktype instr_lst)"
	| instr_case_5 :
		"list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 wf_instr (LOOP v_blocktype instr_lst)"
	| instr_case_6 :
		"list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 list_all (λ (instr_lst_0 :: instr). (wf_instr instr_lst_0)) instr_lst_0_lst ⟹
		 wf_instr (IFELSE v_blocktype instr_lst instr_lst_0_lst)"
	| instr_case_7 :
		"(wf_uN 32 v_labelidx) ⟹
		 wf_instr (BR v_labelidx)"
	| instr_case_8 :
		"(wf_uN 32 v_labelidx) ⟹
		 wf_instr (BR_IF v_labelidx)"
	| instr_case_9 :
		"list_all (λ (v_labelidx :: labelidx). (wf_uN 32 v_labelidx)) labelidx_lst ⟹
		 (wf_uN 32 v_labelidx) ⟹
		 wf_instr (BR_TABLE labelidx_lst v_labelidx)"
	| instr_case_10 :
		"(wf_uN 32 v_funcidx) ⟹
		 wf_instr (CALL v_funcidx)"
	| instr_case_11 :
		"(wf_uN 32 v_typeidx) ⟹
		 wf_instr (CALL_INDIRECT v_typeidx)"
	| instr_case_12 :
		"wf_instr RETURN"
	| instr_case_13 :
		"(wf_val_underscore v_valtype var_0) ⟹
		 wf_instr (res_CONST v_valtype var_0)"
	| instr_case_14 :
		"(wf_unop_underscore v_valtype var_0) ⟹
		 wf_instr (UNOP v_valtype var_0)"
	| instr_case_15 :
		"(wf_binop_underscore v_valtype var_0) ⟹
		 wf_instr (BINOP v_valtype var_0)"
	| instr_case_16 :
		"(wf_testop_underscore v_valtype var_0) ⟹
		 wf_instr (TESTOP v_valtype var_0)"
	| instr_case_17 :
		"(wf_relop_underscore v_valtype var_0) ⟹
		 wf_instr (RELOP v_valtype var_0)"
	| instr_case_18 :
		"(valtype_1 ≠ valtype_2) ⟹
		 wf_instr (CVTOP valtype_1 valtype_2 v_cvtop)"
	| instr_case_19 :
		"(wf_uN 32 v_localidx) ⟹
		 wf_instr (LOCAL_GET v_localidx)"
	| instr_case_20 :
		"(wf_uN 32 v_localidx) ⟹
		 wf_instr (LOCAL_SET v_localidx)"
	| instr_case_21 :
		"(wf_uN 32 v_localidx) ⟹
		 wf_instr (LOCAL_TEE v_localidx)"
	| instr_case_22 :
		"(wf_uN 32 v_globalidx) ⟹
		 wf_instr (GLOBAL_GET v_globalidx)"
	| instr_case_23 :
		"(wf_uN 32 v_globalidx) ⟹
		 wf_instr (GLOBAL_SET v_globalidx)"
	| instr_case_24 :
		"list_all (λ (var_0 :: loadop_underscore). (wf_loadop_underscore v_valtype var_0)) (option_to_list var_0_opt) ⟹
		 (wf_memarg v_memarg) ⟹
		 wf_instr (LOAD v_valtype var_0_opt v_memarg)"
	| instr_case_25 :
		"list_all (λ (v_sz :: sz). (wf_sz v_sz)) (option_to_list sz_opt) ⟹
		 (wf_memarg v_memarg) ⟹
		 ((Inn_opt = None) ⟷ (sz_opt = None)) ⟹
		 ((Inn_opt = None) ⟷ (valtype_opt = None)) ⟹
		 list_all3 (λ (v_Inn :: Inn) (v_sz :: sz) (v_valtype :: valtype). ((v_valtype = (valtype_Inn v_Inn)) ∧ ((proj_sz_0 v_sz) < (size (valtype_Inn v_Inn))))) (option_to_list Inn_opt) (option_to_list sz_opt) (option_to_list valtype_opt) ⟹
		 wf_instr (STORE v_valtype sz_opt v_memarg)"
	| instr_case_26 :
		"wf_instr MEMORY_SIZE"
	| instr_case_27 :
		"wf_instr MEMORY_GROW"

(* Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:252.1-253.9 *)
type_synonym expr = "(instr list)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:263.1-264.16 *)
datatype type =
	  res_TYPE "functype"
	

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:265.1-266.16 *)
datatype local =
	  LOCAL "valtype"
	

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:267.1-268.27 *)
datatype func =
	  func_FUNC "typeidx" "(local list)" "expr"
	

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:267.8-267.12 *)
inductive wf_func :: "func ⇒ bool" where
	  func_case_0 :
		"(wf_uN 32 v_typeidx) ⟹
		 list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 wf_func (func_FUNC v_typeidx local_lst v_expr)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:269.1-270.25 *)
datatype global =
	  global_GLOBAL "globaltype" "expr"
	

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:269.8-269.14 *)
inductive wf_global :: "global ⇒ bool" where
	  global_case_0 :
		"list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 wf_global (global_GLOBAL v_globaltype v_expr)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:271.1-272.18 *)
datatype table =
	  table_TABLE "tabletype"
	

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:271.8-271.13 *)
inductive wf_table :: "table ⇒ bool" where
	  table_case_0 :
		"(wf_limits v_tabletype) ⟹
		 wf_table (table_TABLE v_tabletype)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:273.1-274.17 *)
datatype mem =
	  MEMORY "memtype"
	

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:273.8-273.11 *)
inductive wf_mem :: "mem ⇒ bool" where
	  mem_case_0 :
		"(wf_limits v_memtype) ⟹
		 wf_mem (MEMORY v_memtype)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:275.1-276.21 *)
datatype elem =
	  ELEM "expr" "(funcidx list)"
	

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:275.8-275.12 *)
inductive wf_elem :: "elem ⇒ bool" where
	  elem_case_0 :
		"list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 list_all (λ (v_funcidx :: funcidx). (wf_uN 32 v_funcidx)) funcidx_lst ⟹
		 wf_elem (ELEM v_expr funcidx_lst)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:277.1-278.18 *)
datatype data =
	  DATA "expr" "(byte list)"
	

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:277.8-277.12 *)
inductive wf_data :: "data ⇒ bool" where
	  data_case_0 :
		"list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 list_all (λ (v_byte :: byte). (wf_byte v_byte)) byte_lst ⟹
		 wf_data (DATA v_expr byte_lst)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:279.1-280.16 *)
datatype start =
	  START "funcidx"
	

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:279.8-279.13 *)
inductive wf_start :: "start ⇒ bool" where
	  start_case_0 :
		"(wf_uN 32 v_funcidx) ⟹
		 wf_start (START v_funcidx)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:282.1-283.66 *)
datatype externidx =
	  externidx_FUNC "funcidx"
	| externidx_GLOBAL "globalidx"
	| externidx_TABLE "tableidx"
	| externidx_MEM "memidx"

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:282.8-282.17 *)
inductive wf_externidx :: "externidx ⇒ bool" where
	  externidx_case_0 :
		"(wf_uN 32 v_funcidx) ⟹
		 wf_externidx (externidx_FUNC v_funcidx)"
	| externidx_case_1 :
		"(wf_uN 32 v_globalidx) ⟹
		 wf_externidx (externidx_GLOBAL v_globalidx)"
	| externidx_case_2 :
		"(wf_uN 32 v_tableidx) ⟹
		 wf_externidx (externidx_TABLE v_tableidx)"
	| externidx_case_3 :
		"(wf_uN 32 v_memidx) ⟹
		 wf_externidx (externidx_MEM v_memidx)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:284.1-285.24 *)
datatype export =
	  EXPORT "name" "externidx"
	

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:284.8-284.14 *)
inductive wf_export :: "export ⇒ bool" where
	  export_case_0 :
		"(wf_name v_name) ⟹
		 (wf_externidx v_externidx) ⟹
		 wf_export (EXPORT v_name v_externidx)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:286.1-287.30 *)
datatype import =
	  IMPORT "name" "name" "externtype"
	

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:286.8-286.14 *)
inductive wf_import :: "import ⇒ bool" where
	  import_case_0 :
		"(wf_name v_name) ⟹
		 (wf_name name_0) ⟹
		 (wf_externtype v_externtype) ⟹
		 wf_import (IMPORT v_name name_0 v_externtype)"

(* Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:289.1-290.76 *)
datatype module =
	  MODULE "(type list)" "(import list)" "(func list)" "(global list)" "(table list)" "(mem list)" "(elem list)" "(data list)" "(start option)" "(export list)"
	

(* Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:289.8-289.14 *)
inductive wf_module :: "module ⇒ bool" where
	  module_case_0 :
		"list_all (λ (v_import :: import). (wf_import v_import)) import_lst ⟹
		 list_all (λ (v_func :: func). (wf_func v_func)) func_lst ⟹
		 list_all (λ (v_global :: global). (wf_global v_global)) global_lst ⟹
		 list_all (λ (v_table :: table). (wf_table v_table)) table_lst ⟹
		 list_all (λ (v_mem :: mem). (wf_mem v_mem)) mem_lst ⟹
		 list_all (λ (v_elem :: elem). (wf_elem v_elem)) elem_lst ⟹
		 list_all (λ (v_data :: data). (wf_data v_data)) data_lst ⟹
		 list_all (λ (v_start :: start). (wf_start v_start)) (option_to_list start_opt) ⟹
		 list_all (λ (v_export :: export). (wf_export v_export)) export_lst ⟹
		 wf_module (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)"

(* Mutual Recursion at: ../specification/wasm-1.0/2-syntax-aux.spectec:20.1-20.64 *)
inductive fun_funcsxt :: "(externtype list) ⇒ (functype list) ⇒ bool" where
	  fun_funcsxt_case_0 :
		"fun_funcsxt [] []"
	| fun_funcsxt_case_1 :
		"(fun_funcsxt xt_lst var_0) ⟹
		 fun_funcsxt ([(FUNC ft)] @ xt_lst) ([ft] @ var_0)"
	| fun_funcsxt_case_2 :
		"(fun_funcsxt xt_lst var_0) ⟹
		 fun_funcsxt ([v_externtype] @ xt_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-1.0/2-syntax-aux.spectec:21.1-21.66 *)
inductive fun_globalsxt :: "(externtype list) ⇒ (globaltype list) ⇒ bool" where
	  fun_globalsxt_case_0 :
		"fun_globalsxt [] []"
	| fun_globalsxt_case_1 :
		"(fun_globalsxt xt_lst var_0) ⟹
		 fun_globalsxt ([(GLOBAL gt)] @ xt_lst) ([gt] @ var_0)"
	| fun_globalsxt_case_2 :
		"(fun_globalsxt xt_lst var_0) ⟹
		 fun_globalsxt ([v_externtype] @ xt_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-1.0/2-syntax-aux.spectec:22.1-22.65 *)
inductive fun_tablesxt :: "(externtype list) ⇒ (tabletype list) ⇒ bool" where
	  fun_tablesxt_case_0 :
		"fun_tablesxt [] []"
	| fun_tablesxt_case_1 :
		"(fun_tablesxt xt_lst var_0) ⟹
		 fun_tablesxt ([(TABLE tt)] @ xt_lst) ([tt] @ var_0)"
	| fun_tablesxt_case_2 :
		"(fun_tablesxt xt_lst var_0) ⟹
		 fun_tablesxt ([v_externtype] @ xt_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-1.0/2-syntax-aux.spectec:22.1-22.65 *)
inductive tablesxt_is_wf :: "(externtype list) ⇒ (tabletype list) ⇒ bool" where
	  tablesxt_is_wf_0 :
		"(fun_tablesxt var_0_lst var_0) ⟹
		 list_all (λ (var_0 :: externtype). (wf_externtype var_0)) var_0_lst ⟹
		 (ret_val_lst = var_0) ⟹
		 list_all (λ (ret_val :: tabletype). (wf_limits ret_val)) ret_val_lst ⟹
		 tablesxt_is_wf var_0_lst ret_val_lst"

(* Mutual Recursion at: ../specification/wasm-1.0/2-syntax-aux.spectec:23.1-23.63 *)
inductive fun_memsxt :: "(externtype list) ⇒ (memtype list) ⇒ bool" where
	  fun_memsxt_case_0 :
		"fun_memsxt [] []"
	| fun_memsxt_case_1 :
		"(fun_memsxt xt_lst var_0) ⟹
		 fun_memsxt ([(MEM mt)] @ xt_lst) ([mt] @ var_0)"
	| fun_memsxt_case_2 :
		"(fun_memsxt xt_lst var_0) ⟹
		 fun_memsxt ([v_externtype] @ xt_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-1.0/2-syntax-aux.spectec:23.1-23.63 *)
inductive memsxt_is_wf :: "(externtype list) ⇒ (memtype list) ⇒ bool" where
	  memsxt_is_wf_0 :
		"(fun_memsxt var_0_lst var_0) ⟹
		 list_all (λ (var_0 :: externtype). (wf_externtype var_0)) var_0_lst ⟹
		 (ret_val_lst = var_0) ⟹
		 list_all (λ (ret_val :: memtype). (wf_limits ret_val)) ret_val_lst ⟹
		 memsxt_is_wf var_0_lst ret_val_lst"

(* Auxiliary Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:49.1-49.35 *)
definition memarg0 :: "memarg" where
	"memarg0 = ⦇ ALIGN = (mk_uN 0), OFFSET = (mk_uN 0) ⦈"

(* Inductive Relations Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:49.6-49.13 *)
lemma memarg0_is_wf :
	"(ret_val = (memarg0 )) ⟹
	 (wf_memarg ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:7.1-7.22 *)
function (sequential) res_bool :: "bool ⇒ nat" where
		  "res_bool False = 0"
		| "res_bool True = 1"
	by pat_completeness auto

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:11.1-11.23 *)
axiomatization truncz :: "nat ⇒ nat"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:18.6-18.14 *)
inductive fun_signed_underscore :: "N ⇒ nat ⇒ nat ⇒ bool" where
	  fun_signed__case_0 :
		"(i < (2 ^ (((v_N :: nat) - (1 :: nat)) :: nat))) ⟹
		 fun_signed_underscore v_N i (i :: nat)"
	| fun_signed__case_1 :
		"(((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) ≤ i) ∧ (i < (2 ^ v_N))) ⟹
		 fun_signed_underscore v_N i ((i :: nat) - ((2 ^ v_N) :: nat))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:22.6-22.18 *)
inductive fun_inv_signed_underscore :: "N ⇒ nat ⇒ nat ⇒ bool" where
	  fun_inv_signed__case_0 :
		"(((0 :: nat) ≤ i) ∧ (i < ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat))) ⟹
		 fun_inv_signed_underscore v_N i (i :: nat)"
	| fun_inv_signed__case_1 :
		"(((0 - ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat)) ≤ i) ∧ (i < (0 :: nat))) ⟹
		 fun_inv_signed_underscore v_N i ((i + ((2 ^ v_N) :: nat)) :: nat)"

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:152.1-152.30 *)
axiomatization fabs_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:152.6-152.12 *)
lemma fabs__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (ret_val_lst = (fabs_underscore v_N v_fN)) ⟹
	 list_all (λ (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:155.1-155.31 *)
axiomatization fceil_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:155.6-155.13 *)
lemma fceil__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (ret_val_lst = (fceil_underscore v_N v_fN)) ⟹
	 list_all (λ (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:156.1-156.32 *)
axiomatization ffloor_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:156.6-156.14 *)
lemma ffloor__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (ret_val_lst = (ffloor_underscore v_N v_fN)) ⟹
	 list_all (λ (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:158.1-158.34 *)
axiomatization fnearest_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:158.6-158.16 *)
lemma fnearest__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (ret_val_lst = (fnearest_underscore v_N v_fN)) ⟹
	 list_all (λ (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:153.1-153.30 *)
axiomatization fneg_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:153.6-153.12 *)
lemma fneg__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (ret_val_lst = (fneg_underscore v_N v_fN)) ⟹
	 list_all (λ (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:154.1-154.31 *)
axiomatization fsqrt_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:154.6-154.13 *)
lemma fsqrt__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (ret_val_lst = (fsqrt_underscore v_N v_fN)) ⟹
	 list_all (λ (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:157.1-157.32 *)
axiomatization ftrunc_underscore :: "N ⇒ fN ⇒ (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:157.6-157.14 *)
lemma ftrunc__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (ret_val_lst = (ftrunc_underscore v_N v_fN)) ⟹
	 list_all (λ (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:86.1-86.29 *)
axiomatization iclz_underscore :: "N ⇒ iN ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:86.6-86.12 *)
lemma iclz__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (ret_val = (iclz_underscore v_N v_iN)) ⟹
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:87.1-87.29 *)
axiomatization ictz_underscore :: "N ⇒ iN ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:87.6-87.12 *)
lemma ictz__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (ret_val = (ictz_underscore v_N v_iN)) ⟹
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:88.1-88.32 *)
axiomatization ipopcnt_underscore :: "N ⇒ iN ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:88.6-88.15 *)
lemma ipopcnt__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (ret_val = (ipopcnt_underscore v_N v_iN)) ⟹
	 (wf_uN v_N ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:28.1-29.32 *)
function (sequential) fun_unop__I64 :: "unop_underscore ⇒ val_underscore ⇒ (val_underscore list)" where
		  "fun_unop__I64 (mk_unop__0 Inn_I64 CLZ) (mk_val__0 Inn_I64 v_iN) = [(mk_val__0 Inn_I64 (iclz_underscore (size (valtype_Inn Inn_I64)) v_iN))]"
		| "fun_unop__I64 (mk_unop__0 Inn_I64 CTZ) (mk_val__0 Inn_I64 v_iN) = [(mk_val__0 Inn_I64 (ictz_underscore (size (valtype_Inn Inn_I64)) v_iN))]"
		| "fun_unop__I64 (mk_unop__0 Inn_I64 POPCNT) (mk_val__0 Inn_I64 v_iN) = [(mk_val__0 Inn_I64 (ipopcnt_underscore (size (valtype_Inn Inn_I64)) v_iN))]"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:28.1-29.32 *)
function (sequential) fun_unop__I32 :: "unop_underscore ⇒ val_underscore ⇒ (val_underscore list)" where
		  "fun_unop__I32 (mk_unop__0 Inn_I32 CLZ) (mk_val__0 Inn_I32 v_iN) = [(mk_val__0 Inn_I32 (iclz_underscore (size (valtype_Inn Inn_I32)) v_iN))]"
		| "fun_unop__I32 (mk_unop__0 Inn_I32 CTZ) (mk_val__0 Inn_I32 v_iN) = [(mk_val__0 Inn_I32 (ictz_underscore (size (valtype_Inn Inn_I32)) v_iN))]"
		| "fun_unop__I32 (mk_unop__0 Inn_I32 POPCNT) (mk_val__0 Inn_I32 v_iN) = [(mk_val__0 Inn_I32 (ipopcnt_underscore (size (valtype_Inn Inn_I32)) v_iN))]"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:28.1-29.32 *)
function (sequential) fun_unop__F64 :: "unop_underscore ⇒ val_underscore ⇒ (val_underscore list)" where
		  "fun_unop__F64 (mk_unop__1 Fnn_F64 ABS) (mk_val__1 Fnn_F64 v_fN) = (map (λ (iter_0_2 :: fN). (mk_val__1 Fnn_F64 iter_0_2)) (fabs_underscore (size (valtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 unop_Fnn_NEG) (mk_val__1 Fnn_F64 v_fN) = (map (λ (iter_0_4 :: fN). (mk_val__1 Fnn_F64 iter_0_4)) (fneg_underscore (size (valtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 SQRT) (mk_val__1 Fnn_F64 v_fN) = (map (λ (iter_0_6 :: fN). (mk_val__1 Fnn_F64 iter_0_6)) (fsqrt_underscore (size (valtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 CEIL) (mk_val__1 Fnn_F64 v_fN) = (map (λ (iter_0_8 :: fN). (mk_val__1 Fnn_F64 iter_0_8)) (fceil_underscore (size (valtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 FLOOR) (mk_val__1 Fnn_F64 v_fN) = (map (λ (iter_0_10 :: fN). (mk_val__1 Fnn_F64 iter_0_10)) (ffloor_underscore (size (valtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 TRUNC) (mk_val__1 Fnn_F64 v_fN) = (map (λ (iter_0_12 :: fN). (mk_val__1 Fnn_F64 iter_0_12)) (ftrunc_underscore (size (valtype_Fnn Fnn_F64)) v_fN))"
		| "fun_unop__F64 (mk_unop__1 Fnn_F64 NEAREST) (mk_val__1 Fnn_F64 v_fN) = (map (λ (iter_0_14 :: fN). (mk_val__1 Fnn_F64 iter_0_14)) (fnearest_underscore (size (valtype_Fnn Fnn_F64)) v_fN))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:28.1-29.32 *)
function (sequential) fun_unop__F32 :: "unop_underscore ⇒ val_underscore ⇒ (val_underscore list)" where
		  "fun_unop__F32 (mk_unop__1 Fnn_F32 ABS) (mk_val__1 Fnn_F32 v_fN) = (map (λ (iter_0_1 :: fN). (mk_val__1 Fnn_F32 iter_0_1)) (fabs_underscore (size (valtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 unop_Fnn_NEG) (mk_val__1 Fnn_F32 v_fN) = (map (λ (iter_0_3 :: fN). (mk_val__1 Fnn_F32 iter_0_3)) (fneg_underscore (size (valtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 SQRT) (mk_val__1 Fnn_F32 v_fN) = (map (λ (iter_0_5 :: fN). (mk_val__1 Fnn_F32 iter_0_5)) (fsqrt_underscore (size (valtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 CEIL) (mk_val__1 Fnn_F32 v_fN) = (map (λ (iter_0_7 :: fN). (mk_val__1 Fnn_F32 iter_0_7)) (fceil_underscore (size (valtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 FLOOR) (mk_val__1 Fnn_F32 v_fN) = (map (λ (iter_0_9 :: fN). (mk_val__1 Fnn_F32 iter_0_9)) (ffloor_underscore (size (valtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 TRUNC) (mk_val__1 Fnn_F32 v_fN) = (map (λ (iter_0_11 :: fN). (mk_val__1 Fnn_F32 iter_0_11)) (ftrunc_underscore (size (valtype_Fnn Fnn_F32)) v_fN))"
		| "fun_unop__F32 (mk_unop__1 Fnn_F32 NEAREST) (mk_val__1 Fnn_F32 v_fN) = (map (λ (iter_0_13 :: fN). (mk_val__1 Fnn_F32 iter_0_13)) (fnearest_underscore (size (valtype_Fnn Fnn_F32)) v_fN))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:28.1-29.32 *)
function (sequential) fun_unop_underscore :: "valtype ⇒ unop_underscore ⇒ val_underscore ⇒ (val_underscore list)" where
		  "fun_unop_underscore I64 v_unop_underscore v_val_underscore = (fun_unop__I64 v_unop_underscore v_val_underscore)"
		| "fun_unop_underscore I32 v_unop_underscore v_val_underscore = (fun_unop__I32 v_unop_underscore v_val_underscore)"
		| "fun_unop_underscore F64 v_unop_underscore v_val_underscore = (fun_unop__F64 v_unop_underscore v_val_underscore)"
		| "fun_unop_underscore F32 v_unop_underscore v_val_underscore = (fun_unop__F32 v_unop_underscore v_val_underscore)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12 *)
lemma unop__is_wf :
	"(wf_unop_underscore v_valtype v_unop_underscore) ⟹
	 (wf_val_underscore v_valtype v_val_underscore) ⟹
	 (ret_val_lst = (fun_unop_underscore v_valtype v_unop_underscore v_val_underscore)) ⟹
	 list_all (λ (ret_val :: val_underscore). (wf_val_underscore v_valtype ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:145.1-145.37 *)
axiomatization fadd_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:145.6-145.12 *)
lemma fadd__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (wf_fN v_N fN_0) ⟹
	 (ret_val_lst = (fadd_underscore v_N v_fN fN_0)) ⟹
	 list_all (λ (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:151.1-151.42 *)
axiomatization fcopysign_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:151.6-151.17 *)
lemma fcopysign__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (wf_fN v_N fN_0) ⟹
	 (ret_val_lst = (fcopysign_underscore v_N v_fN fN_0)) ⟹
	 list_all (λ (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:148.1-148.37 *)
axiomatization fdiv_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:148.6-148.12 *)
lemma fdiv__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (wf_fN v_N fN_0) ⟹
	 (ret_val_lst = (fdiv_underscore v_N v_fN fN_0)) ⟹
	 list_all (λ (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:150.1-150.37 *)
axiomatization fmax_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:150.6-150.12 *)
lemma fmax__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (wf_fN v_N fN_0) ⟹
	 (ret_val_lst = (fmax_underscore v_N v_fN fN_0)) ⟹
	 list_all (λ (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:149.1-149.37 *)
axiomatization fmin_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:149.6-149.12 *)
lemma fmin__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (wf_fN v_N fN_0) ⟹
	 (ret_val_lst = (fmin_underscore v_N v_fN fN_0)) ⟹
	 list_all (λ (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:147.1-147.37 *)
axiomatization fmul_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:147.6-147.12 *)
lemma fmul__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (wf_fN v_N fN_0) ⟹
	 (ret_val_lst = (fmul_underscore v_N v_fN fN_0)) ⟹
	 list_all (λ (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:146.1-146.37 *)
axiomatization fsub_underscore :: "N ⇒ fN ⇒ fN ⇒ (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:146.6-146.12 *)
lemma fsub__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (wf_fN v_N fN_0) ⟹
	 (ret_val_lst = (fsub_underscore v_N v_fN fN_0)) ⟹
	 list_all (λ (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:73.1-73.36 *)
function (sequential) iadd_underscore :: "N ⇒ iN ⇒ iN ⇒ iN" where
		  "iadd_underscore v_N i_1 i_2 = (mk_uN (((proj_uN_0 i_1) + (proj_uN_0 i_2)) mod (2 ^ v_N)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:73.6-73.12 *)
lemma iadd__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (wf_uN v_N iN_0) ⟹
	 (ret_val = (iadd_underscore v_N v_iN iN_0)) ⟹
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:79.1-79.36 *)
axiomatization iand_underscore :: "N ⇒ iN ⇒ iN ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:79.6-79.12 *)
lemma iand__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (wf_uN v_N iN_0) ⟹
	 (ret_val = (iand_underscore v_N v_iN iN_0)) ⟹
	 (wf_uN v_N ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:76.6-76.12 *)
inductive fun_idiv_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ (iN option) ⇒ bool" where
	  fun_idiv__case_0 :
		"fun_idiv_underscore v_N U i_1 (mk_uN 0) None"
	| fun_idiv__case_1 :
		"fun_idiv_underscore v_N U i_1 i_2 (Some (mk_uN ((truncz (((proj_uN_0 i_1) :: nat) div ((proj_uN_0 i_2) :: nat))) :: nat)))"
	| fun_idiv__case_2 :
		"fun_idiv_underscore v_N S i_1 (mk_uN 0) None"
	| fun_idiv__case_3 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) ⟹
		 (((var_0 :: nat) div (var_1 :: nat)) = ((2 ^ (((v_N :: nat) - (1 :: nat)) :: nat)) :: nat)) ⟹
		 fun_idiv_underscore v_N S i_1 i_2 None"
	| fun_idiv__case_4 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_2) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_1) ⟹
		 (fun_inv_signed_underscore v_N (truncz ((var_1 :: nat) div (var_2 :: nat))) var_0) ⟹
		 fun_idiv_underscore v_N S i_1 i_2 (Some (mk_uN var_0))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:76.6-76.12 *)
lemma idiv__is_wf :
	"(fun_idiv_underscore v_N v_sx v_iN iN_0 var_0) ⟹
	 (wf_uN v_N v_iN) ⟹
	 (wf_uN v_N iN_0) ⟹
	 (ret_val_opt = var_0) ⟹
	 list_all (λ (ret_val :: iN). (wf_uN v_N ret_val)) (option_to_list ret_val_opt)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:75.1-75.36 *)
function (sequential) imul_underscore :: "N ⇒ iN ⇒ iN ⇒ iN" where
		  "imul_underscore v_N i_1 i_2 = (mk_uN (((proj_uN_0 i_1) * (proj_uN_0 i_2)) mod (2 ^ v_N)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:75.6-75.12 *)
lemma imul__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (wf_uN v_N iN_0) ⟹
	 (ret_val = (imul_underscore v_N v_iN iN_0)) ⟹
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:80.1-80.35 *)
axiomatization ior_underscore :: "N ⇒ iN ⇒ iN ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:80.6-80.11 *)
lemma ior__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (wf_uN v_N iN_0) ⟹
	 (ret_val = (ior_underscore v_N v_iN iN_0)) ⟹
	 (wf_uN v_N ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:77.6-77.12 *)
inductive fun_irem_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ (iN option) ⇒ bool" where
	  fun_irem__case_0 :
		"fun_irem_underscore v_N U i_1 (mk_uN 0) None"
	| fun_irem__case_1 :
		"fun_irem_underscore v_N U i_1 i_2 (Some (mk_uN ((((proj_uN_0 i_1) :: nat) - (((proj_uN_0 i_2) * ((truncz (((proj_uN_0 i_1) :: nat) div ((proj_uN_0 i_2) :: nat))) :: nat)) :: nat)) :: nat)))"
	| fun_irem__case_2 :
		"fun_irem_underscore v_N S i_1 (mk_uN 0) None"
	| fun_irem__case_3 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_2) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_1) ⟹
		 (fun_inv_signed_underscore v_N (j_1 - (j_2 * (truncz ((j_1 :: nat) div (j_2 :: nat))))) var_0) ⟹
		 ((j_1 = var_1) ∧ (j_2 = var_2)) ⟹
		 fun_irem_underscore v_N S i_1 i_2 (Some (mk_uN var_0))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:77.6-77.12 *)
lemma irem__is_wf :
	"(fun_irem_underscore v_N v_sx v_iN iN_0 var_0) ⟹
	 (wf_uN v_N v_iN) ⟹
	 (wf_uN v_N iN_0) ⟹
	 (ret_val_opt = var_0) ⟹
	 list_all (λ (ret_val :: iN). (wf_uN v_N ret_val)) (option_to_list ret_val_opt)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:84.1-84.37 *)
axiomatization irotl_underscore :: "N ⇒ iN ⇒ iN ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:84.6-84.13 *)
lemma irotl__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (wf_uN v_N iN_0) ⟹
	 (ret_val = (irotl_underscore v_N v_iN iN_0)) ⟹
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:85.1-85.37 *)
axiomatization irotr_underscore :: "N ⇒ iN ⇒ iN ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:85.6-85.13 *)
lemma irotr__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (wf_uN v_N iN_0) ⟹
	 (ret_val = (irotr_underscore v_N v_iN iN_0)) ⟹
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:82.1-82.34 *)
axiomatization ishl_underscore :: "N ⇒ iN ⇒ u32 ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:82.6-82.12 *)
lemma ishl__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (wf_uN 32 v_u32) ⟹
	 (ret_val = (ishl_underscore v_N v_iN v_u32)) ⟹
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:83.1-83.74 *)
axiomatization ishr_underscore :: "N ⇒ sx ⇒ iN ⇒ u32 ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:83.6-83.12 *)
lemma ishr__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (wf_uN 32 v_u32) ⟹
	 (ret_val = (ishr_underscore v_N v_sx v_iN v_u32)) ⟹
	 (wf_uN v_N ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:74.1-74.36 *)
function (sequential) isub_underscore :: "N ⇒ iN ⇒ iN ⇒ iN" where
		  "isub_underscore v_N i_1 i_2 = (mk_uN ((((((2 ^ v_N) + (proj_uN_0 i_1)) :: nat) - ((proj_uN_0 i_2) :: nat)) mod ((2 ^ v_N) :: nat)) :: nat))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:74.6-74.12 *)
lemma isub__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (wf_uN v_N iN_0) ⟹
	 (ret_val = (isub_underscore v_N v_iN iN_0)) ⟹
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:81.1-81.36 *)
axiomatization ixor_underscore :: "N ⇒ iN ⇒ iN ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:81.6-81.12 *)
lemma ixor__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (wf_uN v_N iN_0) ⟹
	 (ret_val = (ixor_underscore v_N v_iN iN_0)) ⟹
	 (wf_uN v_N ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13 *)
inductive fun_binop_underscore :: "valtype ⇒ binop_underscore ⇒ val_underscore ⇒ val_underscore ⇒ (val_underscore list) ⇒ bool" where
	  fun_binop__case_0 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 ADD) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [(mk_val__0 Inn_I32 (iadd_underscore (size (valtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_1 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 ADD) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [(mk_val__0 Inn_I64 (iadd_underscore (size (valtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_2 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 SUB) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [(mk_val__0 Inn_I32 (isub_underscore (size (valtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_3 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 SUB) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [(mk_val__0 Inn_I64 (isub_underscore (size (valtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_4 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 MUL) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [(mk_val__0 Inn_I32 (imul_underscore (size (valtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_5 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 MUL) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [(mk_val__0 Inn_I64 (imul_underscore (size (valtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_6 :
		"(fun_idiv_underscore (size (valtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_binop_underscore I32 (mk_binop__0 Inn_I32 (DIV v_sx)) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) (list_underscore  (map_option (λ (iter_0_15 :: iN). (mk_val__0 Inn_I32 iter_0_15)) var_0))"
	| fun_binop__case_7 :
		"(fun_idiv_underscore (size (valtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_binop_underscore I64 (mk_binop__0 Inn_I64 (DIV v_sx)) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) (list_underscore  (map_option (λ (iter_0_16 :: iN). (mk_val__0 Inn_I64 iter_0_16)) var_0))"
	| fun_binop__case_8 :
		"(fun_irem_underscore (size (valtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_binop_underscore I32 (mk_binop__0 Inn_I32 (REM v_sx)) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) (list_underscore  (map_option (λ (iter_0_17 :: iN). (mk_val__0 Inn_I32 iter_0_17)) var_0))"
	| fun_binop__case_9 :
		"(fun_irem_underscore (size (valtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_binop_underscore I64 (mk_binop__0 Inn_I64 (REM v_sx)) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) (list_underscore  (map_option (λ (iter_0_18 :: iN). (mk_val__0 Inn_I64 iter_0_18)) var_0))"
	| fun_binop__case_10 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 AND) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [(mk_val__0 Inn_I32 (iand_underscore (size (valtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_11 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 AND) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [(mk_val__0 Inn_I64 (iand_underscore (size (valtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_12 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 OR) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [(mk_val__0 Inn_I32 (ior_underscore (size (valtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_13 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 OR) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [(mk_val__0 Inn_I64 (ior_underscore (size (valtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_14 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 XOR) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [(mk_val__0 Inn_I32 (ixor_underscore (size (valtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_15 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 XOR) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [(mk_val__0 Inn_I64 (ixor_underscore (size (valtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_16 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 SHL) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [(mk_val__0 Inn_I32 (ishl_underscore (size (valtype_Inn Inn_I32)) iN_1 (mk_uN (proj_uN_0 iN_2))))]"
	| fun_binop__case_17 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 SHL) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [(mk_val__0 Inn_I64 (ishl_underscore (size (valtype_Inn Inn_I64)) iN_1 (mk_uN (proj_uN_0 iN_2))))]"
	| fun_binop__case_18 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 (SHR v_sx)) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [(mk_val__0 Inn_I32 (ishr_underscore (size (valtype_Inn Inn_I32)) v_sx iN_1 (mk_uN (proj_uN_0 iN_2))))]"
	| fun_binop__case_19 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 (SHR v_sx)) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [(mk_val__0 Inn_I64 (ishr_underscore (size (valtype_Inn Inn_I64)) v_sx iN_1 (mk_uN (proj_uN_0 iN_2))))]"
	| fun_binop__case_20 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 ROTL) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [(mk_val__0 Inn_I32 (irotl_underscore (size (valtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_21 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 ROTL) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [(mk_val__0 Inn_I64 (irotl_underscore (size (valtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_22 :
		"fun_binop_underscore I32 (mk_binop__0 Inn_I32 ROTR) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) [(mk_val__0 Inn_I32 (irotr_underscore (size (valtype_Inn Inn_I32)) iN_1 iN_2))]"
	| fun_binop__case_23 :
		"fun_binop_underscore I64 (mk_binop__0 Inn_I64 ROTR) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) [(mk_val__0 Inn_I64 (irotr_underscore (size (valtype_Inn Inn_I64)) iN_1 iN_2))]"
	| fun_binop__case_24 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 binop_Fnn_ADD) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (map (λ (iter_0_19 :: fN). (mk_val__1 Fnn_F32 iter_0_19)) (fadd_underscore (size (valtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_25 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 binop_Fnn_ADD) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (map (λ (iter_0_20 :: fN). (mk_val__1 Fnn_F64 iter_0_20)) (fadd_underscore (size (valtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_26 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 binop_Fnn_SUB) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (map (λ (iter_0_21 :: fN). (mk_val__1 Fnn_F32 iter_0_21)) (fsub_underscore (size (valtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_27 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 binop_Fnn_SUB) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (map (λ (iter_0_22 :: fN). (mk_val__1 Fnn_F64 iter_0_22)) (fsub_underscore (size (valtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_28 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 binop_Fnn_MUL) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (map (λ (iter_0_23 :: fN). (mk_val__1 Fnn_F32 iter_0_23)) (fmul_underscore (size (valtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_29 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 binop_Fnn_MUL) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (map (λ (iter_0_24 :: fN). (mk_val__1 Fnn_F64 iter_0_24)) (fmul_underscore (size (valtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_30 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 binop_Fnn_DIV) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (map (λ (iter_0_25 :: fN). (mk_val__1 Fnn_F32 iter_0_25)) (fdiv_underscore (size (valtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_31 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 binop_Fnn_DIV) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (map (λ (iter_0_26 :: fN). (mk_val__1 Fnn_F64 iter_0_26)) (fdiv_underscore (size (valtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_32 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 res_MIN) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (map (λ (iter_0_27 :: fN). (mk_val__1 Fnn_F32 iter_0_27)) (fmin_underscore (size (valtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_33 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 res_MIN) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (map (λ (iter_0_28 :: fN). (mk_val__1 Fnn_F64 iter_0_28)) (fmin_underscore (size (valtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_34 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 res_MAX) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (map (λ (iter_0_29 :: fN). (mk_val__1 Fnn_F32 iter_0_29)) (fmax_underscore (size (valtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_35 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 res_MAX) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (map (λ (iter_0_30 :: fN). (mk_val__1 Fnn_F64 iter_0_30)) (fmax_underscore (size (valtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_binop__case_36 :
		"fun_binop_underscore F32 (mk_binop__1 Fnn_F32 COPYSIGN) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (map (λ (iter_0_31 :: fN). (mk_val__1 Fnn_F32 iter_0_31)) (fcopysign_underscore (size (valtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_binop__case_37 :
		"fun_binop_underscore F64 (mk_binop__1 Fnn_F64 COPYSIGN) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (map (λ (iter_0_32 :: fN). (mk_val__1 Fnn_F64 iter_0_32)) (fcopysign_underscore (size (valtype_Fnn Fnn_F64)) fN_1 fN_2))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13 *)
lemma binop__is_wf :
	"(fun_binop_underscore v_valtype v_binop_underscore v_val_underscore val__0 var_0) ⟹
	 (wf_binop_underscore v_valtype v_binop_underscore) ⟹
	 (wf_val_underscore v_valtype v_val_underscore) ⟹
	 (wf_val_underscore v_valtype val__0) ⟹
	 (ret_val_lst = var_0) ⟹
	 list_all (λ (ret_val :: val_underscore). (wf_val_underscore v_valtype ret_val)) ret_val_lst"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:89.1-89.27 *)
function (sequential) ieqz_underscore :: "N ⇒ iN ⇒ u32" where
		  "ieqz_underscore v_N i_1 = (mk_uN (res_bool ((proj_uN_0 i_1) = 0)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:89.6-89.12 *)
lemma ieqz__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (ret_val = (ieqz_underscore v_N v_iN)) ⟹
	 (wf_uN 32 ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:32.1-33.32 *)
function (sequential) fun_testop_underscore :: "valtype ⇒ testop_underscore ⇒ val_underscore ⇒ val_underscore" where
		  "fun_testop_underscore I32 (mk_testop__0 Inn_I32 EQZ) (mk_val__0 Inn_I32 v_iN) = (mk_val__0 Inn_I32 (ieqz_underscore (size (valtype_Inn Inn_I32)) v_iN))"
		| "fun_testop_underscore I64 (mk_testop__0 Inn_I64 EQZ) (mk_val__0 Inn_I64 v_iN) = (mk_val__0 Inn_I32 (ieqz_underscore (size (valtype_Inn Inn_I64)) v_iN))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:32.6-32.14 *)
lemma testop__is_wf :
	"(wf_testop_underscore v_valtype v_testop_underscore) ⟹
	 (wf_val_underscore v_valtype v_val_underscore) ⟹
	 (ret_val = (fun_testop_underscore v_valtype v_testop_underscore v_val_underscore)) ⟹
	 (wf_val_underscore I32 ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:159.1-159.33 *)
axiomatization feq_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:159.6-159.11 *)
lemma feq__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (wf_fN v_N fN_0) ⟹
	 (ret_val = (feq_underscore v_N v_fN fN_0)) ⟹
	 (wf_uN 32 ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:164.1-164.33 *)
axiomatization fge_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:164.6-164.11 *)
lemma fge__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (wf_fN v_N fN_0) ⟹
	 (ret_val = (fge_underscore v_N v_fN fN_0)) ⟹
	 (wf_uN 32 ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:162.1-162.33 *)
axiomatization fgt_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:162.6-162.11 *)
lemma fgt__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (wf_fN v_N fN_0) ⟹
	 (ret_val = (fgt_underscore v_N v_fN fN_0)) ⟹
	 (wf_uN 32 ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:163.1-163.33 *)
axiomatization fle_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:163.6-163.11 *)
lemma fle__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (wf_fN v_N fN_0) ⟹
	 (ret_val = (fle_underscore v_N v_fN fN_0)) ⟹
	 (wf_uN 32 ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:161.1-161.33 *)
axiomatization flt_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:161.6-161.11 *)
lemma flt__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (wf_fN v_N fN_0) ⟹
	 (ret_val = (flt_underscore v_N v_fN fN_0)) ⟹
	 (wf_uN 32 ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:160.1-160.33 *)
axiomatization fne_underscore :: "N ⇒ fN ⇒ fN ⇒ u32"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:160.6-160.11 *)
lemma fne__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (wf_fN v_N fN_0) ⟹
	 (ret_val = (fne_underscore v_N v_fN fN_0)) ⟹
	 (wf_uN 32 ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:91.1-91.33 *)
function (sequential) ieq_underscore :: "N ⇒ iN ⇒ iN ⇒ u32" where
		  "ieq_underscore v_N i_1 i_2 = (mk_uN (res_bool (i_1 = i_2)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:91.6-91.11 *)
lemma ieq__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (wf_uN v_N iN_0) ⟹
	 (ret_val = (ieq_underscore v_N v_iN iN_0)) ⟹
	 (wf_uN 32 ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:96.6-96.11 *)
inductive fun_ige_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ u32 ⇒ bool" where
	  fun_ige__case_0 :
		"fun_ige_underscore v_N U i_1 i_2 (mk_uN (res_bool ((proj_uN_0 i_1) ≥ (proj_uN_0 i_2))))"
	| fun_ige__case_1 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) ⟹
		 fun_ige_underscore v_N S i_1 i_2 (mk_uN (res_bool (var_0 ≥ var_1)))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:96.6-96.11 *)
lemma ige__is_wf :
	"(fun_ige_underscore v_N v_sx v_iN iN_0 var_0) ⟹
	 (wf_uN v_N v_iN) ⟹
	 (wf_uN v_N iN_0) ⟹
	 (ret_val = var_0) ⟹
	 (wf_uN 32 ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:94.6-94.11 *)
inductive fun_igt_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ u32 ⇒ bool" where
	  fun_igt__case_0 :
		"fun_igt_underscore v_N U i_1 i_2 (mk_uN (res_bool ((proj_uN_0 i_1) > (proj_uN_0 i_2))))"
	| fun_igt__case_1 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) ⟹
		 fun_igt_underscore v_N S i_1 i_2 (mk_uN (res_bool (var_0 > var_1)))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:94.6-94.11 *)
lemma igt__is_wf :
	"(fun_igt_underscore v_N v_sx v_iN iN_0 var_0) ⟹
	 (wf_uN v_N v_iN) ⟹
	 (wf_uN v_N iN_0) ⟹
	 (ret_val = var_0) ⟹
	 (wf_uN 32 ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:95.6-95.11 *)
inductive fun_ile_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ u32 ⇒ bool" where
	  fun_ile__case_0 :
		"fun_ile_underscore v_N U i_1 i_2 (mk_uN (res_bool ((proj_uN_0 i_1) ≤ (proj_uN_0 i_2))))"
	| fun_ile__case_1 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) ⟹
		 fun_ile_underscore v_N S i_1 i_2 (mk_uN (res_bool (var_0 ≤ var_1)))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:95.6-95.11 *)
lemma ile__is_wf :
	"(fun_ile_underscore v_N v_sx v_iN iN_0 var_0) ⟹
	 (wf_uN v_N v_iN) ⟹
	 (wf_uN v_N iN_0) ⟹
	 (ret_val = var_0) ⟹
	 (wf_uN 32 ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:93.6-93.11 *)
inductive fun_ilt_underscore :: "N ⇒ sx ⇒ iN ⇒ iN ⇒ u32 ⇒ bool" where
	  fun_ilt__case_0 :
		"fun_ilt_underscore v_N U i_1 i_2 (mk_uN (res_bool ((proj_uN_0 i_1) < (proj_uN_0 i_2))))"
	| fun_ilt__case_1 :
		"(fun_signed_underscore v_N (proj_uN_0 i_2) var_1) ⟹
		 (fun_signed_underscore v_N (proj_uN_0 i_1) var_0) ⟹
		 fun_ilt_underscore v_N S i_1 i_2 (mk_uN (res_bool (var_0 < var_1)))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:93.6-93.11 *)
lemma ilt__is_wf :
	"(fun_ilt_underscore v_N v_sx v_iN iN_0 var_0) ⟹
	 (wf_uN v_N v_iN) ⟹
	 (wf_uN v_N iN_0) ⟹
	 (ret_val = var_0) ⟹
	 (wf_uN 32 ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:92.1-92.33 *)
function (sequential) ine_underscore :: "N ⇒ iN ⇒ iN ⇒ u32" where
		  "ine_underscore v_N i_1 i_2 = (mk_uN (res_bool (i_1 ≠ i_2)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:92.6-92.11 *)
lemma ine__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (wf_uN v_N iN_0) ⟹
	 (ret_val = (ine_underscore v_N v_iN iN_0)) ⟹
	 (wf_uN 32 ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13 *)
inductive fun_relop_underscore :: "valtype ⇒ relop_underscore ⇒ val_underscore ⇒ val_underscore ⇒ val_underscore ⇒ bool" where
	  fun_relop__case_0 :
		"fun_relop_underscore I32 (mk_relop__0 Inn_I32 EQ) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) (mk_val__0 Inn_I32 (ieq_underscore (size (valtype_Inn Inn_I32)) iN_1 iN_2))"
	| fun_relop__case_1 :
		"fun_relop_underscore I64 (mk_relop__0 Inn_I64 EQ) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) (mk_val__0 Inn_I32 (ieq_underscore (size (valtype_Inn Inn_I64)) iN_1 iN_2))"
	| fun_relop__case_2 :
		"fun_relop_underscore I32 (mk_relop__0 Inn_I32 NE) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) (mk_val__0 Inn_I32 (ine_underscore (size (valtype_Inn Inn_I32)) iN_1 iN_2))"
	| fun_relop__case_3 :
		"fun_relop_underscore I64 (mk_relop__0 Inn_I64 NE) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) (mk_val__0 Inn_I32 (ine_underscore (size (valtype_Inn Inn_I64)) iN_1 iN_2))"
	| fun_relop__case_4 :
		"(fun_ilt_underscore (size (valtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_relop_underscore I32 (mk_relop__0 Inn_I32 (LT v_sx)) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) (mk_val__0 Inn_I32 var_0)"
	| fun_relop__case_5 :
		"(fun_ilt_underscore (size (valtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_relop_underscore I64 (mk_relop__0 Inn_I64 (LT v_sx)) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) (mk_val__0 Inn_I32 var_0)"
	| fun_relop__case_6 :
		"(fun_igt_underscore (size (valtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_relop_underscore I32 (mk_relop__0 Inn_I32 (GT v_sx)) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) (mk_val__0 Inn_I32 var_0)"
	| fun_relop__case_7 :
		"(fun_igt_underscore (size (valtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_relop_underscore I64 (mk_relop__0 Inn_I64 (GT v_sx)) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) (mk_val__0 Inn_I32 var_0)"
	| fun_relop__case_8 :
		"(fun_ile_underscore (size (valtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_relop_underscore I32 (mk_relop__0 Inn_I32 (LE v_sx)) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) (mk_val__0 Inn_I32 var_0)"
	| fun_relop__case_9 :
		"(fun_ile_underscore (size (valtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_relop_underscore I64 (mk_relop__0 Inn_I64 (LE v_sx)) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) (mk_val__0 Inn_I32 var_0)"
	| fun_relop__case_10 :
		"(fun_ige_underscore (size (valtype_Inn Inn_I32)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_relop_underscore I32 (mk_relop__0 Inn_I32 (GE v_sx)) (mk_val__0 Inn_I32 iN_1) (mk_val__0 Inn_I32 iN_2) (mk_val__0 Inn_I32 var_0)"
	| fun_relop__case_11 :
		"(fun_ige_underscore (size (valtype_Inn Inn_I64)) v_sx iN_1 iN_2 var_0) ⟹
		 fun_relop_underscore I64 (mk_relop__0 Inn_I64 (GE v_sx)) (mk_val__0 Inn_I64 iN_1) (mk_val__0 Inn_I64 iN_2) (mk_val__0 Inn_I32 var_0)"
	| fun_relop__case_12 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_EQ) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (mk_val__0 Inn_I32 (feq_underscore (size (valtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_13 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_EQ) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (mk_val__0 Inn_I32 (feq_underscore (size (valtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_relop__case_14 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_NE) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (mk_val__0 Inn_I32 (fne_underscore (size (valtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_15 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_NE) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (mk_val__0 Inn_I32 (fne_underscore (size (valtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_relop__case_16 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_LT) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (mk_val__0 Inn_I32 (flt_underscore (size (valtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_17 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_LT) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (mk_val__0 Inn_I32 (flt_underscore (size (valtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_relop__case_18 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_GT) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (mk_val__0 Inn_I32 (fgt_underscore (size (valtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_19 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_GT) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (mk_val__0 Inn_I32 (fgt_underscore (size (valtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_relop__case_20 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_LE) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (mk_val__0 Inn_I32 (fle_underscore (size (valtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_21 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_LE) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (mk_val__0 Inn_I32 (fle_underscore (size (valtype_Fnn Fnn_F64)) fN_1 fN_2))"
	| fun_relop__case_22 :
		"fun_relop_underscore F32 (mk_relop__1 Fnn_F32 relop_Fnn_GE) (mk_val__1 Fnn_F32 fN_1) (mk_val__1 Fnn_F32 fN_2) (mk_val__0 Inn_I32 (fge_underscore (size (valtype_Fnn Fnn_F32)) fN_1 fN_2))"
	| fun_relop__case_23 :
		"fun_relop_underscore F64 (mk_relop__1 Fnn_F64 relop_Fnn_GE) (mk_val__1 Fnn_F64 fN_1) (mk_val__1 Fnn_F64 fN_2) (mk_val__0 Inn_I32 (fge_underscore (size (valtype_Fnn Fnn_F64)) fN_1 fN_2))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13 *)
lemma relop__is_wf :
	"(fun_relop_underscore v_valtype v_relop_underscore v_val_underscore val__0 var_0) ⟹
	 (wf_relop_underscore v_valtype v_relop_underscore) ⟹
	 (wf_val_underscore v_valtype v_val_underscore) ⟹
	 (wf_val_underscore v_valtype val__0) ⟹
	 (ret_val = var_0) ⟹
	 (wf_val_underscore I32 ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:44.1-44.90 *)
axiomatization convert__underscore :: "M ⇒ N ⇒ sx ⇒ iN ⇒ fN"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:44.6-44.16 *)
lemma convert___is_wf :
	"(wf_uN v_M v_iN) ⟹
	 (ret_val = (convert__underscore v_M v_N v_sx v_iN)) ⟹
	 (wf_fN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:42.1-42.36 *)
axiomatization demote__underscore :: "M ⇒ N ⇒ fN ⇒ (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:42.6-42.15 *)
lemma demote___is_wf :
	"(wf_fN v_M v_fN) ⟹
	 (ret_val_lst = (demote__underscore v_M v_N v_fN)) ⟹
	 list_all (λ (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:40.1-40.89 *)
axiomatization extend__underscore :: "M ⇒ N ⇒ sx ⇒ iN ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:40.6-40.15 *)
lemma extend___is_wf :
	"(wf_uN v_M v_iN) ⟹
	 (ret_val = (extend__underscore v_M v_N v_sx v_iN)) ⟹
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:43.1-43.37 *)
axiomatization promote__underscore :: "M ⇒ N ⇒ fN ⇒ (fN list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:43.6-43.16 *)
lemma promote___is_wf :
	"(wf_fN v_M v_fN) ⟹
	 (ret_val_lst = (promote__underscore v_M v_N v_fN)) ⟹
	 list_all (λ (ret_val :: fN). (wf_fN v_N ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:45.1-45.76 *)
axiomatization reinterpret__underscore :: "valtype ⇒ valtype ⇒ val_underscore ⇒ val_underscore"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:45.6-45.20 *)
lemma reinterpret___is_wf :
	"(wf_val_underscore valtype_1 v_val_underscore) ⟹
	 (ret_val = (reinterpret__underscore valtype_1 valtype_2 v_val_underscore)) ⟹
	 (wf_val_underscore valtype_2 ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:41.1-41.88 *)
axiomatization trunc__underscore :: "M ⇒ N ⇒ sx ⇒ fN ⇒ (iN option)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:41.6-41.14 *)
lemma trunc___is_wf :
	"(wf_fN v_M v_fN) ⟹
	 (ret_val_opt = (trunc__underscore v_M v_N v_sx v_fN)) ⟹
	 list_all (λ (ret_val :: iN). (wf_uN v_N ret_val)) (option_to_list ret_val_opt)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:39.1-39.33 *)
axiomatization wrap__underscore :: "M ⇒ N ⇒ iN ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:39.6-39.13 *)
lemma wrap___is_wf :
	"(wf_uN v_M v_iN) ⟹
	 (ret_val = (wrap__underscore v_M v_N v_iN)) ⟹
	 (wf_uN v_N ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14 *)
inductive fun_cvtop__underscore :: "valtype ⇒ valtype ⇒ cvtop ⇒ val_underscore ⇒ (val_underscore list) ⇒ bool" where
	  fun_cvtop___case_0 :
		"fun_cvtop__underscore I32 I64 (EXTEND v_sx) (mk_val__0 Inn_I32 v_iN) [(mk_val__0 Inn_I64 (extend__underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) v_sx v_iN))]"
	| fun_cvtop___case_1 :
		"fun_cvtop__underscore I64 I32 WRAP (mk_val__0 Inn_I64 v_iN) [(mk_val__0 Inn_I32 (wrap__underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) v_iN))]"
	| fun_cvtop___case_2 :
		"fun_cvtop__underscore F32 I32 (cvtop_TRUNC v_sx) (mk_val__1 Fnn_F32 v_fN) (list_underscore  (map_option (λ (iter_0_33 :: iN). (mk_val__0 Inn_I32 iter_0_33)) (trunc__underscore (size (valtype_Fnn Fnn_F32)) (size (valtype_Inn Inn_I32)) v_sx v_fN)))"
	| fun_cvtop___case_3 :
		"fun_cvtop__underscore F64 I32 (cvtop_TRUNC v_sx) (mk_val__1 Fnn_F64 v_fN) (list_underscore  (map_option (λ (iter_0_34 :: iN). (mk_val__0 Inn_I32 iter_0_34)) (trunc__underscore (size (valtype_Fnn Fnn_F64)) (size (valtype_Inn Inn_I32)) v_sx v_fN)))"
	| fun_cvtop___case_4 :
		"fun_cvtop__underscore F32 I64 (cvtop_TRUNC v_sx) (mk_val__1 Fnn_F32 v_fN) (list_underscore  (map_option (λ (iter_0_35 :: iN). (mk_val__0 Inn_I64 iter_0_35)) (trunc__underscore (size (valtype_Fnn Fnn_F32)) (size (valtype_Inn Inn_I64)) v_sx v_fN)))"
	| fun_cvtop___case_5 :
		"fun_cvtop__underscore F64 I64 (cvtop_TRUNC v_sx) (mk_val__1 Fnn_F64 v_fN) (list_underscore  (map_option (λ (iter_0_36 :: iN). (mk_val__0 Inn_I64 iter_0_36)) (trunc__underscore (size (valtype_Fnn Fnn_F64)) (size (valtype_Inn Inn_I64)) v_sx v_fN)))"
	| fun_cvtop___case_6 :
		"fun_cvtop__underscore F32 F64 PROMOTE (mk_val__1 Fnn_F32 v_fN) (map (λ (iter_0 :: fN). (mk_val__1 Fnn_F64 iter_0)) (promote__underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) v_fN))"
	| fun_cvtop___case_7 :
		"fun_cvtop__underscore F64 F32 DEMOTE (mk_val__1 Fnn_F64 v_fN) (map (λ (iter_0 :: fN). (mk_val__1 Fnn_F32 iter_0)) (demote__underscore (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))) v_fN))"
	| fun_cvtop___case_8 :
		"fun_cvtop__underscore I32 F32 (CONVERT v_sx) (mk_val__0 Inn_I32 v_iN) [(mk_val__1 Fnn_F32 (convert__underscore (size (valtype_Inn Inn_I32)) (size (valtype_Fnn Fnn_F32)) v_sx v_iN))]"
	| fun_cvtop___case_9 :
		"fun_cvtop__underscore I64 F32 (CONVERT v_sx) (mk_val__0 Inn_I64 v_iN) [(mk_val__1 Fnn_F32 (convert__underscore (size (valtype_Inn Inn_I64)) (size (valtype_Fnn Fnn_F32)) v_sx v_iN))]"
	| fun_cvtop___case_10 :
		"fun_cvtop__underscore I32 F64 (CONVERT v_sx) (mk_val__0 Inn_I32 v_iN) [(mk_val__1 Fnn_F64 (convert__underscore (size (valtype_Inn Inn_I32)) (size (valtype_Fnn Fnn_F64)) v_sx v_iN))]"
	| fun_cvtop___case_11 :
		"fun_cvtop__underscore I64 F64 (CONVERT v_sx) (mk_val__0 Inn_I64 v_iN) [(mk_val__1 Fnn_F64 (convert__underscore (size (valtype_Inn Inn_I64)) (size (valtype_Fnn Fnn_F64)) v_sx v_iN))]"
	| fun_cvtop___case_12 :
		"((size (valtype_Inn Inn_I32)) = (size (valtype_Fnn Fnn_F32))) ⟹
		 fun_cvtop__underscore I32 F32 REINTERPRET (mk_val__0 Inn_I32 v_iN) [(reinterpret__underscore (valtype_Inn Inn_I32) (valtype_Fnn Fnn_F32) (mk_val__0 Inn_I32 v_iN))]"
	| fun_cvtop___case_13 :
		"((size (valtype_Inn Inn_I64)) = (size (valtype_Fnn Fnn_F32))) ⟹
		 fun_cvtop__underscore I64 F32 REINTERPRET (mk_val__0 Inn_I64 v_iN) [(reinterpret__underscore (valtype_Inn Inn_I64) (valtype_Fnn Fnn_F32) (mk_val__0 Inn_I64 v_iN))]"
	| fun_cvtop___case_14 :
		"((size (valtype_Inn Inn_I32)) = (size (valtype_Fnn Fnn_F64))) ⟹
		 fun_cvtop__underscore I32 F64 REINTERPRET (mk_val__0 Inn_I32 v_iN) [(reinterpret__underscore (valtype_Inn Inn_I32) (valtype_Fnn Fnn_F64) (mk_val__0 Inn_I32 v_iN))]"
	| fun_cvtop___case_15 :
		"((size (valtype_Inn Inn_I64)) = (size (valtype_Fnn Fnn_F64))) ⟹
		 fun_cvtop__underscore I64 F64 REINTERPRET (mk_val__0 Inn_I64 v_iN) [(reinterpret__underscore (valtype_Inn Inn_I64) (valtype_Fnn Fnn_F64) (mk_val__0 Inn_I64 v_iN))]"
	| fun_cvtop___case_16 :
		"((size (valtype_Inn Inn_I32)) = (size (valtype_Fnn Fnn_F32))) ⟹
		 fun_cvtop__underscore F32 I32 REINTERPRET (mk_val__1 Fnn_F32 v_fN) [(reinterpret__underscore (valtype_Fnn Fnn_F32) (valtype_Inn Inn_I32) (mk_val__1 Fnn_F32 v_fN))]"
	| fun_cvtop___case_17 :
		"((size (valtype_Inn Inn_I32)) = (size (valtype_Fnn Fnn_F64))) ⟹
		 fun_cvtop__underscore F64 I32 REINTERPRET (mk_val__1 Fnn_F64 v_fN) [(reinterpret__underscore (valtype_Fnn Fnn_F64) (valtype_Inn Inn_I32) (mk_val__1 Fnn_F64 v_fN))]"
	| fun_cvtop___case_18 :
		"((size (valtype_Inn Inn_I64)) = (size (valtype_Fnn Fnn_F32))) ⟹
		 fun_cvtop__underscore F32 I64 REINTERPRET (mk_val__1 Fnn_F32 v_fN) [(reinterpret__underscore (valtype_Fnn Fnn_F32) (valtype_Inn Inn_I64) (mk_val__1 Fnn_F32 v_fN))]"
	| fun_cvtop___case_19 :
		"((size (valtype_Inn Inn_I64)) = (size (valtype_Fnn Fnn_F64))) ⟹
		 fun_cvtop__underscore F64 I64 REINTERPRET (mk_val__1 Fnn_F64 v_fN) [(reinterpret__underscore (valtype_Fnn Fnn_F64) (valtype_Inn Inn_I64) (mk_val__1 Fnn_F64 v_fN))]"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14 *)
lemma cvtop___is_wf :
	"(fun_cvtop__underscore valtype_1 valtype_2 v_cvtop v_val_underscore var_0) ⟹
	 (wf_val_underscore valtype_1 v_val_underscore) ⟹
	 (ret_val_lst = var_0) ⟹
	 list_all (λ (ret_val :: val_underscore). (wf_val_underscore valtype_2 ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:56.1-56.102 *)
axiomatization ibytes_underscore :: "N ⇒ iN ⇒ (byte list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:56.6-56.14 *)
lemma ibytes__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (ret_val_lst = (ibytes_underscore v_N v_iN)) ⟹
	 list_all (λ (ret_val :: byte). (wf_byte ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:57.1-57.102 *)
axiomatization fbytes_underscore :: "N ⇒ fN ⇒ (byte list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:57.6-57.14 *)
lemma fbytes__is_wf :
	"(wf_fN v_N v_fN) ⟹
	 (ret_val_lst = (fbytes_underscore v_N v_fN)) ⟹
	 list_all (λ (ret_val :: byte). (wf_byte ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:58.1-58.75 *)
axiomatization bytes_underscore :: "valtype ⇒ val_underscore ⇒ (byte list)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:58.6-58.13 *)
lemma bytes__is_wf :
	"(wf_val_underscore v_valtype v_val_underscore) ⟹
	 (ret_val_lst = (bytes_underscore v_valtype v_val_underscore)) ⟹
	 list_all (λ (ret_val :: byte). (wf_byte ret_val)) ret_val_lst"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:60.1-60.75 *)
axiomatization inv_ibytes_underscore :: "N ⇒ (byte list) ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:60.6-60.18 *)
lemma inv_ibytes__is_wf :
	"list_all (λ (var_0 :: byte). (wf_byte var_0)) var_0_lst ⟹
	 (ret_val = (inv_ibytes_underscore v_N var_0_lst)) ⟹
	 (wf_uN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:61.1-61.75 *)
axiomatization inv_fbytes_underscore :: "N ⇒ (byte list) ⇒ fN"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:61.6-61.18 *)
lemma inv_fbytes__is_wf :
	"list_all (λ (var_0 :: byte). (wf_byte var_0)) var_0_lst ⟹
	 (ret_val = (inv_fbytes_underscore v_N var_0_lst)) ⟹
	 (wf_fN v_N ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:62.1-62.73 *)
axiomatization inv_bytes_underscore :: "valtype ⇒ (byte list) ⇒ val_underscore"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:62.6-62.17 *)
lemma inv_bytes__is_wf :
	"list_all (λ (var_0 :: byte). (wf_byte var_0)) var_0_lst ⟹
	 (ret_val = (inv_bytes_underscore v_valtype var_0_lst)) ⟹
	 (wf_val_underscore v_valtype ret_val)"
sorry

(* Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:78.1-78.29 *)
axiomatization inot_underscore :: "N ⇒ iN ⇒ iN"

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:78.6-78.12 *)
lemma inot__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (ret_val = (inot_underscore v_N v_iN)) ⟹
	 (wf_uN v_N ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:90.1-90.27 *)
function (sequential) inez_underscore :: "N ⇒ iN ⇒ u32" where
		  "inez_underscore v_N i_1 = (mk_uN (res_bool ((proj_uN_0 i_1) ≠ 0)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:90.6-90.12 *)
lemma inez__is_wf :
	"(wf_uN v_N v_iN) ⟹
	 (ret_val = (inez_underscore v_N v_iN)) ⟹
	 (wf_uN 32 ret_val)"
sorry

(* Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:5.1-5.39 *)
type_synonym addr = "nat"

(* Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:6.1-6.53 *)
type_synonym funcaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:7.1-7.53 *)
type_synonym globaladdr = "addr"

(* Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:8.1-8.51 *)
type_synonym tableaddr = "addr"

(* Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:9.1-9.50 *)
type_synonym memaddr = "addr"

(* Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:20.1-21.70 *)
datatype externaddr =
	  externaddr_FUNC "funcaddr"
	| externaddr_GLOBAL "globaladdr"
	| externaddr_TABLE "tableaddr"
	| externaddr_MEM "memaddr"

(* Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:32.1-33.55 *)
datatype val =
	  val_CONST "valtype" "val_underscore"
	

(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:32.8-32.11 *)
inductive wf_val :: "val ⇒ bool" where
	  val_case_0 :
		"(wf_val_underscore v_valtype var_0) ⟹
		 wf_val (val_CONST v_valtype var_0)"

(* Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:35.1-36.22 *)
datatype result =
	  underscore_VALS "(val list)"
	| TRAP

(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:35.8-35.14 *)
inductive wf_result :: "result ⇒ bool" where
	  result_case_0 :
		"list_all (λ (v_val :: val). (wf_val v_val)) val_lst ⟹
		 wf_result (underscore_VALS val_lst)"
	| result_case_1 :
		"wf_result TRAP"

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:61.1-63.22 *)
record exportinst =
	NAME :: "name"
	ADDR :: "externaddr"

definition append_exportinst :: "exportinst ⇒ exportinst ⇒ exportinst" where
	"append_exportinst arg1 arg2 = ⦇
		NAME = NAME arg1,
		ADDR = ADDR arg1
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:61.8-61.18 *)
inductive wf_exportinst :: "exportinst ⇒ bool" where
	  exportinst_case_underscore :
		"(wf_name var_0) ⟹
		 wf_exportinst ⦇ NAME = var_0, ADDR = var_1 ⦈"

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:65.1-71.26 *)
record moduleinst =
	TYPES :: "(functype list)"
	FUNCS :: "(funcaddr list)"
	GLOBALS :: "(globaladdr list)"
	TABLES :: "(tableaddr list)"
	MEMS :: "(memaddr list)"
	EXPORTS :: "(exportinst list)"

definition append_moduleinst :: "moduleinst ⇒ moduleinst ⇒ moduleinst" where
	"append_moduleinst arg1 arg2 = ⦇
		TYPES = TYPES arg1 @ TYPES arg2,
		FUNCS = FUNCS arg1 @ FUNCS arg2,
		GLOBALS = GLOBALS arg1 @ GLOBALS arg2,
		TABLES = TABLES arg1 @ TABLES arg2,
		MEMS = MEMS arg1 @ MEMS arg2,
		EXPORTS = EXPORTS arg1 @ EXPORTS arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:65.8-65.18 *)
inductive wf_moduleinst :: "moduleinst ⇒ bool" where
	  moduleinst_case_underscore :
		"list_all (λ (var_5 :: exportinst). (wf_exportinst var_5)) var_5_lst ⟹
		 wf_moduleinst ⦇ TYPES = var_0_lst, FUNCS = var_1_lst, GLOBALS = var_2_lst, TABLES = var_3_lst, MEMS = var_4_lst, EXPORTS = var_5_lst ⦈"

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:48.1-51.16 *)
record funcinst =
	funcinst_TYPE :: "functype"
	funcinst_MODULE :: "moduleinst"
	CODE :: "func"

definition append_funcinst :: "funcinst ⇒ funcinst ⇒ funcinst" where
	"append_funcinst arg1 arg2 = ⦇
		funcinst_TYPE = funcinst_TYPE arg1,
		funcinst_MODULE = append_moduleinst (funcinst_MODULE arg1) (funcinst_MODULE arg2),
		CODE = CODE arg1
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:48.8-48.16 *)
inductive wf_funcinst :: "funcinst ⇒ bool" where
	  funcinst_case_underscore :
		"(wf_moduleinst var_1) ⟹
		 (wf_func var_2) ⟹
		 wf_funcinst ⦇ funcinst_TYPE = var_0, funcinst_MODULE = var_1, CODE = var_2 ⦈"

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:52.1-54.16 *)
record globalinst =
	globalinst_TYPE :: "globaltype"
	VALUE :: "val"

definition append_globalinst :: "globalinst ⇒ globalinst ⇒ globalinst" where
	"append_globalinst arg1 arg2 = ⦇
		globalinst_TYPE = globalinst_TYPE arg1,
		VALUE = VALUE arg1
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:52.8-52.18 *)
inductive wf_globalinst :: "globalinst ⇒ bool" where
	  globalinst_case_underscore :
		"(wf_val var_1) ⟹
		 wf_globalinst ⦇ globalinst_TYPE = var_0, VALUE = var_1 ⦈"

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:55.1-57.24 *)
record tableinst =
	tableinst_TYPE :: "tabletype"
	REFS :: "((funcaddr option) list)"

definition append_tableinst :: "tableinst ⇒ tableinst ⇒ tableinst" where
	"append_tableinst arg1 arg2 = ⦇
		tableinst_TYPE = tableinst_TYPE arg1,
		REFS = REFS arg1 @ REFS arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:55.8-55.17 *)
inductive wf_tableinst :: "tableinst ⇒ bool" where
	  tableinst_case_underscore :
		"(wf_limits var_0) ⟹
		 wf_tableinst ⦇ tableinst_TYPE = var_0, REFS = var_1_opt_lst ⦈"

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:58.1-60.18 *)
record meminst =
	meminst_TYPE :: "memtype"
	BYTES :: "(byte list)"

definition append_meminst :: "meminst ⇒ meminst ⇒ meminst" where
	"append_meminst arg1 arg2 = ⦇
		meminst_TYPE = meminst_TYPE arg1,
		BYTES = BYTES arg1 @ BYTES arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:58.8-58.15 *)
inductive wf_meminst :: "meminst ⇒ bool" where
	  meminst_case_underscore :
		"(wf_limits var_0) ⟹
		 list_all (λ (var_1 :: byte). (wf_byte var_1)) var_1_lst ⟹
		 wf_meminst ⦇ meminst_TYPE = var_0, BYTES = var_1_lst ⦈"

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:83.1-87.20 *)
record store =
	store_FUNCS :: "(funcinst list)"
	store_GLOBALS :: "(globalinst list)"
	store_TABLES :: "(tableinst list)"
	store_MEMS :: "(meminst list)"

definition append_store :: "store ⇒ store ⇒ store" where
	"append_store arg1 arg2 = ⦇
		store_FUNCS = store_FUNCS arg1 @ store_FUNCS arg2,
		store_GLOBALS = store_GLOBALS arg1 @ store_GLOBALS arg2,
		store_TABLES = store_TABLES arg1 @ store_TABLES arg2,
		store_MEMS = store_MEMS arg1 @ store_MEMS arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:83.8-83.13 *)
inductive wf_store :: "store ⇒ bool" where
	  store_case_underscore :
		"list_all (λ (var_0 :: funcinst). (wf_funcinst var_0)) var_0_lst ⟹
		 list_all (λ (var_1 :: globalinst). (wf_globalinst var_1)) var_1_lst ⟹
		 list_all (λ (var_2 :: tableinst). (wf_tableinst var_2)) var_2_lst ⟹
		 list_all (λ (var_3 :: meminst). (wf_meminst var_3)) var_3_lst ⟹
		 wf_store ⦇ store_FUNCS = var_0_lst, store_GLOBALS = var_1_lst, store_TABLES = var_2_lst, store_MEMS = var_3_lst ⦈"

(* Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:89.1-91.24 *)
record frame =
	LOCALS :: "(val list)"
	frame_MODULE :: "moduleinst"

definition append_frame :: "frame ⇒ frame ⇒ frame" where
	"append_frame arg1 arg2 = ⦇
		LOCALS = LOCALS arg1 @ LOCALS arg2,
		frame_MODULE = append_moduleinst (frame_MODULE arg1) (frame_MODULE arg2)
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:89.8-89.13 *)
inductive wf_frame :: "frame ⇒ bool" where
	  frame_case_underscore :
		"list_all (λ (var_0 :: val). (wf_val var_0)) var_0_lst ⟹
		 (wf_moduleinst var_1) ⟹
		 wf_frame ⦇ LOCALS = var_0_lst, frame_MODULE = var_1 ⦈"

(* Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:93.1-93.47 *)
datatype state =
	  mk_state "store" "frame"
	

(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:93.8-93.13 *)
inductive wf_state :: "state ⇒ bool" where
	  state_case_0 :
		"(wf_store v_store) ⟹
		 (wf_frame v_frame) ⟹
		 wf_state (mk_state v_store v_frame)"

(* Mutual Recursion at: ../specification/wasm-1.0/4-runtime.spectec:105.1-110.9 *)
datatype admininstr =
	  admininstr_NOP
	| admininstr_UNREACHABLE
	| admininstr_DROP
	| admininstr_SELECT
	| admininstr_BLOCK "blocktype" "(instr list)"
	| admininstr_LOOP "blocktype" "(instr list)"
	| admininstr_IFELSE "blocktype" "(instr list)" "(instr list)"
	| admininstr_BR "labelidx"
	| admininstr_BR_IF "labelidx"
	| admininstr_BR_TABLE "(labelidx list)" "labelidx"
	| admininstr_CALL "funcidx"
	| admininstr_CALL_INDIRECT "typeidx"
	| admininstr_RETURN
	| admininstr_CONST "valtype" "val_underscore"
	| admininstr_UNOP "valtype" "unop_underscore"
	| admininstr_BINOP "valtype" "binop_underscore"
	| admininstr_TESTOP "valtype" "testop_underscore"
	| admininstr_RELOP "valtype" "relop_underscore"
	| admininstr_CVTOP "valtype" "valtype" "cvtop"
	| admininstr_LOCAL_GET "localidx"
	| admininstr_LOCAL_SET "localidx"
	| admininstr_LOCAL_TEE "localidx"
	| admininstr_GLOBAL_GET "globalidx"
	| admininstr_GLOBAL_SET "globalidx"
	| admininstr_LOAD "valtype" "(loadop_underscore option)" "memarg"
	| admininstr_STORE "valtype" "(sz option)" "memarg"
	| admininstr_MEMORY_SIZE
	| admininstr_MEMORY_GROW
	| CALL_ADDR "funcaddr"
	| LABEL_underscore "n" "(instr list)" "(admininstr list)"
	| FRAME_underscore "n" "frame" "(admininstr list)"
	| admininstr_TRAP

(* Auxiliary Definition at:  *)
function (sequential) admininstr_instr :: "instr ⇒ admininstr" where
		  "admininstr_instr NOP = admininstr_NOP"
		| "admininstr_instr UNREACHABLE = admininstr_UNREACHABLE"
		| "admininstr_instr DROP = admininstr_DROP"
		| "admininstr_instr SELECT = admininstr_SELECT"
		| "admininstr_instr (BLOCK x0 x1) = (admininstr_BLOCK x0 x1)"
		| "admininstr_instr (LOOP x0 x1) = (admininstr_LOOP x0 x1)"
		| "admininstr_instr (IFELSE x0 x1 x2) = (admininstr_IFELSE x0 x1 x2)"
		| "admininstr_instr (BR x0) = (admininstr_BR x0)"
		| "admininstr_instr (BR_IF x0) = (admininstr_BR_IF x0)"
		| "admininstr_instr (BR_TABLE x0 x1) = (admininstr_BR_TABLE x0 x1)"
		| "admininstr_instr (CALL x0) = (admininstr_CALL x0)"
		| "admininstr_instr (CALL_INDIRECT x0) = (admininstr_CALL_INDIRECT x0)"
		| "admininstr_instr RETURN = admininstr_RETURN"
		| "admininstr_instr (res_CONST x0 x1) = (admininstr_CONST x0 x1)"
		| "admininstr_instr (UNOP x0 x1) = (admininstr_UNOP x0 x1)"
		| "admininstr_instr (BINOP x0 x1) = (admininstr_BINOP x0 x1)"
		| "admininstr_instr (TESTOP x0 x1) = (admininstr_TESTOP x0 x1)"
		| "admininstr_instr (RELOP x0 x1) = (admininstr_RELOP x0 x1)"
		| "admininstr_instr (CVTOP x0 x1 x2) = (admininstr_CVTOP x0 x1 x2)"
		| "admininstr_instr (LOCAL_GET x0) = (admininstr_LOCAL_GET x0)"
		| "admininstr_instr (LOCAL_SET x0) = (admininstr_LOCAL_SET x0)"
		| "admininstr_instr (LOCAL_TEE x0) = (admininstr_LOCAL_TEE x0)"
		| "admininstr_instr (GLOBAL_GET x0) = (admininstr_GLOBAL_GET x0)"
		| "admininstr_instr (GLOBAL_SET x0) = (admininstr_GLOBAL_SET x0)"
		| "admininstr_instr (LOAD x0 x1 x2) = (admininstr_LOAD x0 x1 x2)"
		| "admininstr_instr (STORE x0 x1 x2) = (admininstr_STORE x0 x1 x2)"
		| "admininstr_instr MEMORY_SIZE = admininstr_MEMORY_SIZE"
		| "admininstr_instr MEMORY_GROW = admininstr_MEMORY_GROW"
	by pat_completeness auto

(* Auxiliary Definition at:  *)
function (sequential) admininstr_val :: "val ⇒ admininstr" where
		  "admininstr_val (val_CONST x0 x1) = (admininstr_CONST x0 x1)"
	by pat_completeness auto

(* Mutual Recursion at: ../specification/wasm-1.0/4-runtime.spectec:105.1-110.9 *)
inductive wf_admininstr :: "admininstr ⇒ bool" where
	  admininstr_case_0 :
		"wf_admininstr admininstr_NOP"
	| admininstr_case_1 :
		"wf_admininstr admininstr_UNREACHABLE"
	| admininstr_case_2 :
		"wf_admininstr admininstr_DROP"
	| admininstr_case_3 :
		"wf_admininstr admininstr_SELECT"
	| admininstr_case_4 :
		"list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 wf_admininstr (admininstr_BLOCK v_blocktype instr_lst)"
	| admininstr_case_5 :
		"list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 wf_admininstr (admininstr_LOOP v_blocktype instr_lst)"
	| admininstr_case_6 :
		"list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 list_all (λ (instr_lst_0 :: instr). (wf_instr instr_lst_0)) instr_lst_0_lst ⟹
		 wf_admininstr (admininstr_IFELSE v_blocktype instr_lst instr_lst_0_lst)"
	| admininstr_case_7 :
		"(wf_uN 32 v_labelidx) ⟹
		 wf_admininstr (admininstr_BR v_labelidx)"
	| admininstr_case_8 :
		"(wf_uN 32 v_labelidx) ⟹
		 wf_admininstr (admininstr_BR_IF v_labelidx)"
	| admininstr_case_9 :
		"list_all (λ (v_labelidx :: labelidx). (wf_uN 32 v_labelidx)) labelidx_lst ⟹
		 (wf_uN 32 v_labelidx) ⟹
		 wf_admininstr (admininstr_BR_TABLE labelidx_lst v_labelidx)"
	| admininstr_case_10 :
		"(wf_uN 32 v_funcidx) ⟹
		 wf_admininstr (admininstr_CALL v_funcidx)"
	| admininstr_case_11 :
		"(wf_uN 32 v_typeidx) ⟹
		 wf_admininstr (admininstr_CALL_INDIRECT v_typeidx)"
	| admininstr_case_12 :
		"wf_admininstr admininstr_RETURN"
	| admininstr_case_13 :
		"(wf_val_underscore v_valtype var_0) ⟹
		 wf_admininstr (admininstr_CONST v_valtype var_0)"
	| admininstr_case_14 :
		"(wf_unop_underscore v_valtype var_0) ⟹
		 wf_admininstr (admininstr_UNOP v_valtype var_0)"
	| admininstr_case_15 :
		"(wf_binop_underscore v_valtype var_0) ⟹
		 wf_admininstr (admininstr_BINOP v_valtype var_0)"
	| admininstr_case_16 :
		"(wf_testop_underscore v_valtype var_0) ⟹
		 wf_admininstr (admininstr_TESTOP v_valtype var_0)"
	| admininstr_case_17 :
		"(wf_relop_underscore v_valtype var_0) ⟹
		 wf_admininstr (admininstr_RELOP v_valtype var_0)"
	| admininstr_case_18 :
		"(valtype_1 ≠ valtype_2) ⟹
		 wf_admininstr (admininstr_CVTOP valtype_1 valtype_2 v_cvtop)"
	| admininstr_case_19 :
		"(wf_uN 32 v_localidx) ⟹
		 wf_admininstr (admininstr_LOCAL_GET v_localidx)"
	| admininstr_case_20 :
		"(wf_uN 32 v_localidx) ⟹
		 wf_admininstr (admininstr_LOCAL_SET v_localidx)"
	| admininstr_case_21 :
		"(wf_uN 32 v_localidx) ⟹
		 wf_admininstr (admininstr_LOCAL_TEE v_localidx)"
	| admininstr_case_22 :
		"(wf_uN 32 v_globalidx) ⟹
		 wf_admininstr (admininstr_GLOBAL_GET v_globalidx)"
	| admininstr_case_23 :
		"(wf_uN 32 v_globalidx) ⟹
		 wf_admininstr (admininstr_GLOBAL_SET v_globalidx)"
	| admininstr_case_24 :
		"list_all (λ (var_0 :: loadop_underscore). (wf_loadop_underscore v_valtype var_0)) (option_to_list var_0_opt) ⟹
		 (wf_memarg v_memarg) ⟹
		 wf_admininstr (admininstr_LOAD v_valtype var_0_opt v_memarg)"
	| admininstr_case_25 :
		"list_all (λ (v_sz :: sz). (wf_sz v_sz)) (option_to_list sz_opt) ⟹
		 (wf_memarg v_memarg) ⟹
		 ((Inn_opt = None) ⟷ (sz_opt = None)) ⟹
		 ((Inn_opt = None) ⟷ (valtype_opt = None)) ⟹
		 list_all3 (λ (v_Inn :: Inn) (v_sz :: sz) (v_valtype :: valtype). ((v_valtype = (valtype_Inn v_Inn)) ∧ ((proj_sz_0 v_sz) < (size (valtype_Inn v_Inn))))) (option_to_list Inn_opt) (option_to_list sz_opt) (option_to_list valtype_opt) ⟹
		 wf_admininstr (admininstr_STORE v_valtype sz_opt v_memarg)"
	| admininstr_case_26 :
		"wf_admininstr admininstr_MEMORY_SIZE"
	| admininstr_case_27 :
		"wf_admininstr admininstr_MEMORY_GROW"
	| admininstr_case_28 :
		"wf_admininstr (CALL_ADDR v_funcaddr)"
	| admininstr_case_29 :
		"list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 list_all (λ (v_admininstr :: admininstr). (wf_admininstr v_admininstr)) admininstr_lst ⟹
		 wf_admininstr (LABEL_underscore v_n instr_lst admininstr_lst)"
	| admininstr_case_30 :
		"(wf_frame v_frame) ⟹
		 list_all (λ (v_admininstr :: admininstr). (wf_admininstr v_admininstr)) admininstr_lst ⟹
		 wf_admininstr (FRAME_underscore v_n v_frame admininstr_lst)"
	| admininstr_case_31 :
		"wf_admininstr admininstr_TRAP"

(* Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:94.1-94.62 *)
datatype config =
	  mk_config "state" "(admininstr list)"
	

(* Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:94.8-94.14 *)
inductive wf_config :: "config ⇒ bool" where
	  config_case_0 :
		"(wf_state v_state) ⟹
		 list_all (λ (v_admininstr :: admininstr). (wf_admininstr v_admininstr)) admininstr_lst ⟹
		 wf_config (mk_config v_state admininstr_lst)"

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:7.1-7.29 *)
function (sequential) default_underscore :: "valtype ⇒ val" where
		  "default_underscore I32 = (val_CONST I32 (mk_val__0 Inn_I32 (mk_uN 0)))"
		| "default_underscore I64 = (val_CONST I64 (mk_val__0 Inn_I64 (mk_uN 0)))"
		| "default_underscore F32 = (val_CONST F32 (mk_val__1 Fnn_F32 (fzero (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))"
		| "default_underscore F64 = (val_CONST F64 (mk_val__1 Fnn_F64 (fzero (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:7.6-7.15 *)
lemma default__is_wf :
	"(ret_val = (default_underscore v_valtype)) ⟹
	 (wf_val ret_val)"
sorry

(* Mutual Recursion at: ../specification/wasm-1.0/5-runtime-aux.spectec:17.1-17.63 *)
inductive fun_funcsxa :: "(externaddr list) ⇒ (funcaddr list) ⇒ bool" where
	  fun_funcsxa_case_0 :
		"fun_funcsxa [] []"
	| fun_funcsxa_case_1 :
		"(fun_funcsxa xv_lst var_0) ⟹
		 fun_funcsxa ([(externaddr_FUNC fa)] @ xv_lst) ([fa] @ var_0)"
	| fun_funcsxa_case_2 :
		"(fun_funcsxa xv_lst var_0) ⟹
		 fun_funcsxa ([v_externaddr] @ xv_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-1.0/5-runtime-aux.spectec:18.1-18.65 *)
inductive fun_globalsxa :: "(externaddr list) ⇒ (globaladdr list) ⇒ bool" where
	  fun_globalsxa_case_0 :
		"fun_globalsxa [] []"
	| fun_globalsxa_case_1 :
		"(fun_globalsxa xv_lst var_0) ⟹
		 fun_globalsxa ([(externaddr_GLOBAL ga)] @ xv_lst) ([ga] @ var_0)"
	| fun_globalsxa_case_2 :
		"(fun_globalsxa xv_lst var_0) ⟹
		 fun_globalsxa ([v_externaddr] @ xv_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-1.0/5-runtime-aux.spectec:19.1-19.64 *)
inductive fun_tablesxa :: "(externaddr list) ⇒ (tableaddr list) ⇒ bool" where
	  fun_tablesxa_case_0 :
		"fun_tablesxa [] []"
	| fun_tablesxa_case_1 :
		"(fun_tablesxa xv_lst var_0) ⟹
		 fun_tablesxa ([(externaddr_TABLE ta)] @ xv_lst) ([ta] @ var_0)"
	| fun_tablesxa_case_2 :
		"(fun_tablesxa xv_lst var_0) ⟹
		 fun_tablesxa ([v_externaddr] @ xv_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-1.0/5-runtime-aux.spectec:20.1-20.62 *)
inductive fun_memsxa :: "(externaddr list) ⇒ (memaddr list) ⇒ bool" where
	  fun_memsxa_case_0 :
		"fun_memsxa [] []"
	| fun_memsxa_case_1 :
		"(fun_memsxa xv_lst var_0) ⟹
		 fun_memsxa ([(externaddr_MEM ma)] @ xv_lst) ([ma] @ var_0)"
	| fun_memsxa_case_2 :
		"(fun_memsxa xv_lst var_0) ⟹
		 fun_memsxa ([v_externaddr] @ xv_lst) var_0"

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:46.1-46.57 *)
function (sequential) fun_store :: "state ⇒ store" where
		  "fun_store (mk_state s f) = s"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:46.6-46.12 *)
lemma store_is_wf :
	"(wf_state v_state) ⟹
	 (ret_val = (fun_store v_state)) ⟹
	 (wf_store ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:47.1-47.57 *)
function (sequential) fun_frame :: "state ⇒ frame" where
		  "fun_frame (mk_state s f) = f"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:47.6-47.12 *)
lemma frame_is_wf :
	"(wf_state v_state) ⟹
	 (ret_val = (fun_frame v_state)) ⟹
	 (wf_frame ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:53.1-53.64 *)
function (sequential) fun_funcaddr :: "state ⇒ (funcaddr list)" where
		  "fun_funcaddr (mk_state s f) = (FUNCS (frame_MODULE f))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:56.1-56.57 *)
function (sequential) fun_funcinst :: "state ⇒ (funcinst list)" where
		  "fun_funcinst (mk_state s f) = (store_FUNCS s)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:56.6-56.15 *)
lemma funcinst_is_wf :
	"(wf_state v_state) ⟹
	 (ret_val_lst = (fun_funcinst v_state)) ⟹
	 list_all (λ (ret_val :: funcinst). (wf_funcinst ret_val)) ret_val_lst"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:57.1-57.59 *)
function (sequential) fun_globalinst :: "state ⇒ (globalinst list)" where
		  "fun_globalinst (mk_state s f) = (store_GLOBALS s)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:57.6-57.17 *)
lemma globalinst_is_wf :
	"(wf_state v_state) ⟹
	 (ret_val_lst = (fun_globalinst v_state)) ⟹
	 list_all (λ (ret_val :: globalinst). (wf_globalinst ret_val)) ret_val_lst"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:58.1-58.58 *)
function (sequential) fun_tableinst :: "state ⇒ (tableinst list)" where
		  "fun_tableinst (mk_state s f) = (store_TABLES s)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:58.6-58.16 *)
lemma tableinst_is_wf :
	"(wf_state v_state) ⟹
	 (ret_val_lst = (fun_tableinst v_state)) ⟹
	 list_all (λ (ret_val :: tableinst). (wf_tableinst ret_val)) ret_val_lst"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:59.1-59.56 *)
function (sequential) fun_meminst :: "state ⇒ (meminst list)" where
		  "fun_meminst (mk_state s f) = (store_MEMS s)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:59.6-59.14 *)
lemma meminst_is_wf :
	"(wf_state v_state) ⟹
	 (ret_val_lst = (fun_meminst v_state)) ⟹
	 list_all (λ (ret_val :: meminst). (wf_meminst ret_val)) ret_val_lst"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:60.1-60.58 *)
function (sequential) fun_moduleinst :: "state ⇒ moduleinst" where
		  "fun_moduleinst (mk_state s f) = (frame_MODULE f)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:60.6-60.17 *)
lemma moduleinst_is_wf :
	"(wf_state v_state) ⟹
	 (ret_val = (fun_moduleinst v_state)) ⟹
	 (wf_moduleinst ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:68.1-68.66 *)
function (sequential) fun_type :: "state ⇒ typeidx ⇒ functype" where
		  "fun_type (mk_state s f) x = ((TYPES (frame_MODULE f)) ! (proj_uN_0 x))"
	by pat_completeness auto

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:69.1-69.66 *)
function (sequential) fun_func :: "state ⇒ funcidx ⇒ funcinst" where
		  "fun_func (mk_state s f) x = ((store_FUNCS s) ! ((FUNCS (frame_MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:69.6-69.11 *)
lemma func_is_wf :
	"(wf_state v_state) ⟹
	 (wf_uN 32 v_funcidx) ⟹
	 (ret_val = (fun_func v_state v_funcidx)) ⟹
	 (wf_funcinst ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:70.1-70.68 *)
function (sequential) fun_global :: "state ⇒ globalidx ⇒ globalinst" where
		  "fun_global (mk_state s f) x = ((store_GLOBALS s) ! ((GLOBALS (frame_MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:70.6-70.13 *)
lemma global_is_wf :
	"(wf_state v_state) ⟹
	 (wf_uN 32 v_globalidx) ⟹
	 (ret_val = (fun_global v_state v_globalidx)) ⟹
	 (wf_globalinst ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:71.1-71.67 *)
function (sequential) fun_table :: "state ⇒ tableidx ⇒ tableinst" where
		  "fun_table (mk_state s f) x = ((store_TABLES s) ! ((TABLES (frame_MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:71.6-71.12 *)
lemma table_is_wf :
	"(wf_state v_state) ⟹
	 (wf_uN 32 v_tableidx) ⟹
	 (ret_val = (fun_table v_state v_tableidx)) ⟹
	 (wf_tableinst ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:72.1-72.65 *)
function (sequential) fun_mem :: "state ⇒ memidx ⇒ meminst" where
		  "fun_mem (mk_state s f) x = ((store_MEMS s) ! ((MEMS (frame_MODULE f)) ! (proj_uN_0 x)))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:72.6-72.10 *)
lemma mem_is_wf :
	"(wf_state v_state) ⟹
	 (wf_uN 32 v_memidx) ⟹
	 (ret_val = (fun_mem v_state v_memidx)) ⟹
	 (wf_meminst ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:73.1-73.67 *)
function (sequential) fun_local :: "state ⇒ localidx ⇒ val" where
		  "fun_local (mk_state s f) x = ((LOCALS f) ! (proj_uN_0 x))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:73.6-73.12 *)
lemma local_is_wf :
	"(wf_state v_state) ⟹
	 (wf_uN 32 v_localidx) ⟹
	 (ret_val = (fun_local v_state v_localidx)) ⟹
	 (wf_val ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:85.1-85.89 *)
function (sequential) with_local :: "state ⇒ localidx ⇒ val ⇒ state" where
		  "with_local (mk_state s f) x v = (mk_state s (f ⦇ LOCALS := (list_update_func (LOCALS f) (proj_uN_0 x) (λ (underscore_underscore :: val). v))  ⦈))"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:85.6-85.17 *)
lemma with_local_is_wf :
	"(wf_state v_state) ⟹
	 (wf_uN 32 v_localidx) ⟹
	 (wf_val v_val) ⟹
	 (ret_val = (with_local v_state v_localidx v_val)) ⟹
	 (wf_state ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:86.1-86.96 *)
function (sequential) with_global :: "state ⇒ globalidx ⇒ val ⇒ state" where
		  "with_global (mk_state s f) x v = (mk_state (s ⦇ store_GLOBALS := (list_update_func (store_GLOBALS s) ((GLOBALS (frame_MODULE f)) ! (proj_uN_0 x)) (λ (var_1 :: globalinst). (var_1 ⦇ VALUE := v  ⦈)))  ⦈) f)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:86.6-86.18 *)
lemma with_global_is_wf :
	"(wf_state v_state) ⟹
	 (wf_uN 32 v_globalidx) ⟹
	 (wf_val v_val) ⟹
	 (ret_val = (with_global v_state v_globalidx v_val)) ⟹
	 (wf_state ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:87.1-87.97 *)
function (sequential) with_table :: "state ⇒ tableidx ⇒ nat ⇒ funcaddr ⇒ state" where
		  "with_table (mk_state s f) x i a = (mk_state (s ⦇ store_TABLES := (list_update_func (store_TABLES s) ((TABLES (frame_MODULE f)) ! (proj_uN_0 x)) (λ (var_1 :: tableinst). (var_1 ⦇ REFS := (list_update_func (REFS var_1) i (λ (underscore_underscore :: (funcaddr option)). (Some a)))  ⦈)))  ⦈) f)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:87.6-87.17 *)
lemma with_table_is_wf :
	"(wf_state v_state) ⟹
	 (wf_uN 32 v_tableidx) ⟹
	 (ret_val = (with_table v_state v_tableidx res_nat v_funcaddr)) ⟹
	 (wf_state ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:88.1-88.89 *)
function (sequential) with_tableinst :: "state ⇒ tableidx ⇒ tableinst ⇒ state" where
		  "with_tableinst (mk_state s f) x ti = (mk_state (s ⦇ store_TABLES := (list_update_func (store_TABLES s) ((TABLES (frame_MODULE f)) ! (proj_uN_0 x)) (λ (underscore_underscore :: tableinst). ti))  ⦈) f)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:88.6-88.21 *)
lemma with_tableinst_is_wf :
	"(wf_state v_state) ⟹
	 (wf_uN 32 v_tableidx) ⟹
	 (wf_tableinst v_tableinst) ⟹
	 (ret_val = (with_tableinst v_state v_tableidx v_tableinst)) ⟹
	 (wf_state ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:89.1-89.100 *)
function (sequential) with_mem :: "state ⇒ memidx ⇒ nat ⇒ nat ⇒ (byte list) ⇒ state" where
		  "with_mem (mk_state s f) x i j b_lst = (mk_state (s ⦇ store_MEMS := (list_update_func (store_MEMS s) ((MEMS (frame_MODULE f)) ! (proj_uN_0 x)) (λ (var_1 :: meminst). (var_1 ⦇ BYTES := (list_slice_update (BYTES var_1) i j b_lst)  ⦈)))  ⦈) f)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:89.6-89.15 *)
lemma with_mem_is_wf :
	"(wf_state v_state) ⟹
	 (wf_uN 32 v_memidx) ⟹
	 list_all (λ (var_0 :: byte). (wf_byte var_0)) var_0_lst ⟹
	 (ret_val = (with_mem v_state v_memidx res_nat nat_0 var_0_lst)) ⟹
	 (wf_state ret_val)"
sorry

(* Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:90.1-90.87 *)
function (sequential) with_meminst :: "state ⇒ memidx ⇒ meminst ⇒ state" where
		  "with_meminst (mk_state s f) x mi = (mk_state (s ⦇ store_MEMS := (list_update_func (store_MEMS s) ((MEMS (frame_MODULE f)) ! (proj_uN_0 x)) (λ (underscore_underscore :: meminst). mi))  ⦈) f)"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:90.6-90.19 *)
lemma with_meminst_is_wf :
	"(wf_state v_state) ⟹
	 (wf_uN 32 v_memidx) ⟹
	 (wf_meminst v_meminst) ⟹
	 (ret_val = (with_meminst v_state v_memidx v_meminst)) ⟹
	 (wf_state ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:102.6-102.16 *)
inductive fun_growtable_before_fun_growtable_case_1 :: "tableinst ⇒ nat ⇒ bool" where
	  fun_growtable_case_0 :
		"(ti = ⦇ tableinst_TYPE = (mk_limits i j_opt), REFS = (map (λ (a_1 :: addr). (Some a_1)) a_lst) ⦈) ⟹
		 (i' = ((length a_lst) + v_n)) ⟹
		 (ti' = ⦇ tableinst_TYPE = (mk_limits (mk_uN i') j_opt), REFS = ((map (λ (a_3 :: addr). (Some a_3)) a_lst) @ (repeat v_n None)) ⦈) ⟹
		 list_all (λ (j_3 :: u32). (i' ≤ (proj_uN_0 j_3))) (option_to_list j_opt) ⟹
		 (wf_tableinst ⦇ tableinst_TYPE = (mk_limits i j_opt), REFS = (map (λ (a_4 :: addr). (Some a_4)) a_lst) ⦈) ⟹
		 (wf_tableinst ⦇ tableinst_TYPE = (mk_limits (mk_uN i') j_opt), REFS = ((map (λ (a_5 :: addr). (Some a_5)) a_lst) @ (repeat v_n None)) ⦈) ⟹
		 fun_growtable_before_fun_growtable_case_1 ti v_n"

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:102.6-102.16 *)
inductive fun_growtable :: "tableinst ⇒ nat ⇒ (tableinst option) ⇒ bool" where
	  fun_growtable__fun_growtable_case_0 :
		"(ti = ⦇ tableinst_TYPE = (mk_limits i j_opt), REFS = (map (λ (a_1 :: addr). (Some a_1)) a_lst) ⦈) ⟹
		 (i' = ((length a_lst) + v_n)) ⟹
		 (ti' = ⦇ tableinst_TYPE = (mk_limits (mk_uN i') j_opt), REFS = ((map (λ (a_3 :: addr). (Some a_3)) a_lst) @ (repeat v_n None)) ⦈) ⟹
		 list_all (λ (j_3 :: u32). (i' ≤ (proj_uN_0 j_3))) (option_to_list j_opt) ⟹
		 (wf_tableinst ⦇ tableinst_TYPE = (mk_limits i j_opt), REFS = (map (λ (a_4 :: addr). (Some a_4)) a_lst) ⦈) ⟹
		 (wf_tableinst ⦇ tableinst_TYPE = (mk_limits (mk_uN i') j_opt), REFS = ((map (λ (a_5 :: addr). (Some a_5)) a_lst) @ (repeat v_n None)) ⦈) ⟹
		 fun_growtable ti v_n (Some ti')"
	| fun_growtable_case_1 :
		"(~(fun_growtable_before_fun_growtable_case_1 x0 x1)) ⟹
		 fun_growtable x0 x1 None"

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:102.6-102.16 *)
lemma growtable_is_wf :
	"(fun_growtable v_tableinst res_nat var_0) ⟹
	 (wf_tableinst v_tableinst) ⟹
	 (var_0 ≠ None) ⟹
	 (ret_val = (the (var_0))) ⟹
	 (wf_tableinst ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:103.6-103.17 *)
inductive fun_growmemory_before_fun_growmemory_case_1 :: "meminst ⇒ nat ⇒ bool" where
	  fun_growmemory_case_0 :
		"(⦇ meminst_TYPE = (mk_limits i j_opt), BYTES = b_lst ⦈ = mi) ⟹
		 (i' = ((((length b_lst) :: nat) div ((64 * (Ki )) :: nat)) + (v_n :: nat))) ⟹
		 (mi' = ⦇ meminst_TYPE = (mk_limits (mk_uN (i' :: nat)) j_opt), BYTES = (b_lst @ (repeat (v_n * (64 * (Ki ))) (mk_byte 0))) ⦈) ⟹
		 list_all (λ (j_8 :: u32). (i' ≤ ((proj_uN_0 j_8) :: nat))) (option_to_list j_opt) ⟹
		 (wf_meminst ⦇ meminst_TYPE = (mk_limits i j_opt), BYTES = b_lst ⦈) ⟹
		 (wf_meminst ⦇ meminst_TYPE = (mk_limits (mk_uN (i' :: nat)) j_opt), BYTES = (b_lst @ (repeat (v_n * (64 * (Ki ))) (mk_byte 0))) ⦈) ⟹
		 fun_growmemory_before_fun_growmemory_case_1 mi v_n"

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:103.6-103.17 *)
inductive fun_growmemory :: "meminst ⇒ nat ⇒ (meminst option) ⇒ bool" where
	  fun_growmemory__fun_growmemory_case_0 :
		"(⦇ meminst_TYPE = (mk_limits i j_opt), BYTES = b_lst ⦈ = mi) ⟹
		 (i' = ((((length b_lst) :: nat) div ((64 * (Ki )) :: nat)) + (v_n :: nat))) ⟹
		 (mi' = ⦇ meminst_TYPE = (mk_limits (mk_uN (i' :: nat)) j_opt), BYTES = (b_lst @ (repeat (v_n * (64 * (Ki ))) (mk_byte 0))) ⦈) ⟹
		 list_all (λ (j_8 :: u32). (i' ≤ ((proj_uN_0 j_8) :: nat))) (option_to_list j_opt) ⟹
		 (wf_meminst ⦇ meminst_TYPE = (mk_limits i j_opt), BYTES = b_lst ⦈) ⟹
		 (wf_meminst ⦇ meminst_TYPE = (mk_limits (mk_uN (i' :: nat)) j_opt), BYTES = (b_lst @ (repeat (v_n * (64 * (Ki ))) (mk_byte 0))) ⦈) ⟹
		 fun_growmemory mi v_n (Some mi')"
	| fun_growmemory_case_1 :
		"(~(fun_growmemory_before_fun_growmemory_case_1 x0 x1)) ⟹
		 fun_growmemory x0 x1 None"

(* Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:103.6-103.17 *)
lemma growmemory_is_wf :
	"(fun_growmemory v_meminst res_nat var_0) ⟹
	 (wf_meminst v_meminst) ⟹
	 (var_0 ≠ None) ⟹
	 (ret_val = (the (var_0))) ⟹
	 (wf_meminst ret_val)"
sorry

(* Record Creation Definition at: ../specification/wasm-1.0/6-typing.spectec:5.1-8.62 *)
record res_context =
	context_TYPES :: "(functype list)"
	context_FUNCS :: "(functype list)"
	context_GLOBALS :: "(globaltype list)"
	context_TABLES :: "(tabletype list)"
	context_MEMS :: "(memtype list)"
	context_LOCALS :: "(valtype list)"
	LABELS :: "(resulttype list)"
	context_RETURN :: "(resulttype option)"

definition append_res_context :: "res_context ⇒ res_context ⇒ res_context" where
	"append_res_context arg1 arg2 = ⦇
		context_TYPES = context_TYPES arg1 @ context_TYPES arg2,
		context_FUNCS = context_FUNCS arg1 @ context_FUNCS arg2,
		context_GLOBALS = context_GLOBALS arg1 @ context_GLOBALS arg2,
		context_TABLES = context_TABLES arg1 @ context_TABLES arg2,
		context_MEMS = context_MEMS arg1 @ context_MEMS arg2,
		context_LOCALS = context_LOCALS arg1 @ context_LOCALS arg2,
		LABELS = LABELS arg1 @ LABELS arg2,
		context_RETURN = context_RETURN arg1 @@@ context_RETURN arg2
	⦈"



(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:5.8-5.15 *)
inductive wf_context :: "res_context ⇒ bool" where
	  context_case_underscore :
		"list_all (λ (var_3 :: tabletype). (wf_limits var_3)) var_3_lst ⟹
		 list_all (λ (var_4 :: memtype). (wf_limits var_4)) var_4_lst ⟹
		 wf_context ⦇ context_TYPES = var_0_lst, context_FUNCS = var_1_lst, context_GLOBALS = var_2_lst, context_TABLES = var_3_lst, context_MEMS = var_4_lst, context_LOCALS = var_5_lst, LABELS = var_6_lst, context_RETURN = var_7_opt ⦈"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:18.1-18.66 *)
inductive Limits_ok :: "limits ⇒ nat ⇒ bool" where
	  mk_Limits_ok :
		"(v_n ≤ k) ⟹
		 list_all (λ (v_m :: nat). ((v_n ≤ v_m) ∧ (v_m ≤ k))) (option_to_list m_opt) ⟹
		 (wf_limits (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt))) ⟹
		 Limits_ok (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt)) k"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:19.1-19.64 *)
inductive Functype_ok :: "functype ⇒ bool" where
	  mk_Functype_ok :
		"Functype_ok (mk_functype t_1_lst (option_to_list t_2_opt))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:20.1-20.66 *)
inductive Globaltype_ok :: "globaltype ⇒ bool" where
	  mk_Globaltype_ok :
		"Globaltype_ok (mk_globaltype (Some MUT) t)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:21.1-21.65 *)
inductive Tabletype_ok :: "tabletype ⇒ bool" where
	  mk_Tabletype_ok :
		"(Limits_ok v_limits ((((2 ^ 32) :: nat) - (1 :: nat)) :: nat)) ⟹
		 (wf_limits v_limits) ⟹
		 Tabletype_ok v_limits"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:22.1-22.63 *)
inductive Memtype_ok :: "memtype ⇒ bool" where
	  mk_Memtype_ok :
		"(Limits_ok v_limits (2 ^ 16)) ⟹
		 (wf_limits v_limits) ⟹
		 Memtype_ok v_limits"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:23.1-23.66 *)
inductive Externtype_ok :: "externtype ⇒ bool" where
	  Externtype_ok__func :
		"(Functype_ok v_functype) ⟹
		 (wf_externtype (FUNC v_functype)) ⟹
		 Externtype_ok (FUNC v_functype)"
	| Externtype_ok__global :
		"(Globaltype_ok v_globaltype) ⟹
		 (wf_externtype (GLOBAL v_globaltype)) ⟹
		 Externtype_ok (GLOBAL v_globaltype)"
	| Externtype_ok__table :
		"(Tabletype_ok v_tabletype) ⟹
		 (wf_externtype (TABLE v_tabletype)) ⟹
		 Externtype_ok (TABLE v_tabletype)"
	| Externtype_ok__mem :
		"(Memtype_ok v_memtype) ⟹
		 (wf_externtype (MEM v_memtype)) ⟹
		 Externtype_ok (MEM v_memtype)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:70.1-70.75 *)
inductive Limits_sub :: "limits ⇒ limits ⇒ bool" where
	  mk_Limits_sub :
		"(n_11 ≥ n_21) ⟹
		 (n_12 ≤ n_22) ⟹
		 (wf_limits (mk_limits (mk_uN n_11) (Some (mk_uN n_12)))) ⟹
		 (wf_limits (mk_limits (mk_uN n_21) (Some (mk_uN n_22)))) ⟹
		 Limits_sub (mk_limits (mk_uN n_11) (Some (mk_uN n_12))) (mk_limits (mk_uN n_21) (Some (mk_uN n_22)))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:71.1-71.73 *)
inductive Functype_sub :: "functype ⇒ functype ⇒ bool" where
	  mk_Functype_sub :
		"Functype_sub ft ft"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:72.1-72.75 *)
inductive Globaltype_sub :: "globaltype ⇒ globaltype ⇒ bool" where
	  mk_Globaltype_sub :
		"Globaltype_sub gt gt"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:73.1-73.74 *)
inductive Tabletype_sub :: "tabletype ⇒ tabletype ⇒ bool" where
	  mk_Tabletype_sub :
		"(Limits_sub lim_1 lim_2) ⟹
		 (wf_limits lim_1) ⟹
		 (wf_limits lim_2) ⟹
		 Tabletype_sub lim_1 lim_2"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:74.1-74.72 *)
inductive Memtype_sub :: "memtype ⇒ memtype ⇒ bool" where
	  mk_Memtype_sub :
		"(Limits_sub lim_1 lim_2) ⟹
		 (wf_limits lim_1) ⟹
		 (wf_limits lim_2) ⟹
		 Memtype_sub lim_1 lim_2"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:75.1-75.75 *)
inductive Externtype_sub :: "externtype ⇒ externtype ⇒ bool" where
	  Externtype_sub__func :
		"(Functype_sub ft_1 ft_2) ⟹
		 (wf_externtype (FUNC ft_1)) ⟹
		 (wf_externtype (FUNC ft_2)) ⟹
		 Externtype_sub (FUNC ft_1) (FUNC ft_2)"
	| Externtype_sub__global :
		"(Globaltype_sub gt_1 gt_2) ⟹
		 (wf_externtype (GLOBAL gt_1)) ⟹
		 (wf_externtype (GLOBAL gt_2)) ⟹
		 Externtype_sub (GLOBAL gt_1) (GLOBAL gt_2)"
	| Externtype_sub__table :
		"(Tabletype_sub tt_1 tt_2) ⟹
		 (wf_externtype (TABLE tt_1)) ⟹
		 (wf_externtype (TABLE tt_2)) ⟹
		 Externtype_sub (TABLE tt_1) (TABLE tt_2)"
	| Externtype_sub__mem :
		"(Memtype_sub mt_1 mt_2) ⟹
		 (wf_externtype (MEM mt_1)) ⟹
		 (wf_externtype (MEM mt_2)) ⟹
		 Externtype_sub (MEM mt_1) (MEM mt_2)"

(* Mutual Recursion at: ../specification/wasm-1.0/6-typing.spectec:120.1-121.65 *)
inductive Instr_ok :: "res_context ⇒ instr ⇒ functype ⇒ bool"
and Instrs_ok :: "res_context ⇒ (instr list) ⇒ functype ⇒ bool" where
	  nop :
		"(wf_context C) ⟹
		 (wf_instr NOP) ⟹
		 Instr_ok C NOP (mk_functype [] [])"
	| unreachable :
		"(wf_context C) ⟹
		 (wf_instr UNREACHABLE) ⟹
		 Instr_ok C UNREACHABLE (mk_functype t_1_lst t_2_lst)"
	| drop :
		"(wf_context C) ⟹
		 (wf_instr DROP) ⟹
		 Instr_ok C DROP (mk_functype [t] [])"
	| select :
		"(wf_context C) ⟹
		 (wf_instr SELECT) ⟹
		 Instr_ok C SELECT (mk_functype [t, t, I32] [t])"
	| block :
		"(Instrs_ok (append_res_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_LOCALS = [], LABELS = [t_opt], context_RETURN = None ⦈ C) instr_lst (mk_functype [] (option_to_list t_opt))) ⟹
		 (wf_context C) ⟹
		 (wf_instr (BLOCK t_opt instr_lst)) ⟹
		 (wf_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_LOCALS = [], LABELS = [t_opt], context_RETURN = None ⦈) ⟹
		 Instr_ok C (BLOCK t_opt instr_lst) (mk_functype [] (option_to_list t_opt))"
	| loop :
		"(Instrs_ok (append_res_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_LOCALS = [], LABELS = [None], context_RETURN = None ⦈ C) instr_lst (mk_functype [] [])) ⟹
		 (wf_context C) ⟹
		 (wf_instr (LOOP t_opt instr_lst)) ⟹
		 (wf_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_LOCALS = [], LABELS = [None], context_RETURN = None ⦈) ⟹
		 Instr_ok C (LOOP t_opt instr_lst) (mk_functype [] (option_to_list t_opt))"
	| res_if :
		"(Instrs_ok (append_res_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_LOCALS = [], LABELS = [t_opt], context_RETURN = None ⦈ C) instr_1_lst (mk_functype [] (option_to_list t_opt))) ⟹
		 (Instrs_ok (append_res_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_LOCALS = [], LABELS = [t_opt], context_RETURN = None ⦈ C) instr_2_lst (mk_functype [] (option_to_list t_opt))) ⟹
		 (wf_context C) ⟹
		 (wf_instr (IFELSE t_opt instr_1_lst instr_2_lst)) ⟹
		 (wf_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_LOCALS = [], LABELS = [t_opt], context_RETURN = None ⦈) ⟹
		 Instr_ok C (IFELSE t_opt instr_1_lst instr_2_lst) (mk_functype [I32] (option_to_list t_opt))"
	| br :
		"((proj_uN_0 l) < (length (LABELS C))) ⟹
		 (((LABELS C) ! (proj_uN_0 l)) = t_opt) ⟹
		 (wf_context C) ⟹
		 (wf_instr (BR l)) ⟹
		 Instr_ok C (BR l) (mk_functype (t_1_lst @ (option_to_list t_opt)) t_2_lst)"
	| br_if :
		"((proj_uN_0 l) < (length (LABELS C))) ⟹
		 (((LABELS C) ! (proj_uN_0 l)) = t_opt) ⟹
		 (wf_context C) ⟹
		 (wf_instr (BR_IF l)) ⟹
		 Instr_ok C (BR_IF l) (mk_functype ((option_to_list t_opt) @ [I32]) (option_to_list t_opt))"
	| br_table :
		"((proj_uN_0 l') < (length (LABELS C))) ⟹
		 (t_opt = ((LABELS C) ! (proj_uN_0 l'))) ⟹
		 list_all (λ (l :: labelidx). ((proj_uN_0 l) < (length (LABELS C)))) l_lst ⟹
		 list_all (λ (l :: labelidx). (t_opt = ((LABELS C) ! (proj_uN_0 l)))) l_lst ⟹
		 (wf_context C) ⟹
		 (wf_instr (BR_TABLE l_lst l')) ⟹
		 Instr_ok C (BR_TABLE l_lst l') (mk_functype (t_1_lst @ ((option_to_list t_opt) @ [I32])) t_2_lst)"
	| call :
		"((proj_uN_0 x) < (length (context_FUNCS C))) ⟹
		 (((context_FUNCS C) ! (proj_uN_0 x)) = (mk_functype t_1_lst (option_to_list t_2_opt))) ⟹
		 (wf_context C) ⟹
		 (wf_instr (CALL x)) ⟹
		 Instr_ok C (CALL x) (mk_functype t_1_lst (option_to_list t_2_opt))"
	| call_indirect :
		"((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (((context_TYPES C) ! (proj_uN_0 x)) = (mk_functype t_1_lst (option_to_list t_2_opt))) ⟹
		 (wf_context C) ⟹
		 (wf_instr (CALL_INDIRECT x)) ⟹
		 Instr_ok C (CALL_INDIRECT x) (mk_functype (t_1_lst @ [I32]) (option_to_list t_2_opt))"
	| return :
		"((context_RETURN C) = (Some t_opt)) ⟹
		 (wf_context C) ⟹
		 (wf_instr RETURN) ⟹
		 Instr_ok C RETURN (mk_functype (t_1_lst @ (option_to_list t_opt)) t_2_lst)"
	| const :
		"(wf_context C) ⟹
		 (wf_instr (res_CONST t c_t)) ⟹
		 Instr_ok C (res_CONST t c_t) (mk_functype [] [t])"
	| unop :
		"(wf_context C) ⟹
		 (wf_instr (UNOP t unop_t)) ⟹
		 Instr_ok C (UNOP t unop_t) (mk_functype [t] [t])"
	| binop :
		"(wf_context C) ⟹
		 (wf_instr (BINOP t binop_t)) ⟹
		 Instr_ok C (BINOP t binop_t) (mk_functype [t, t] [t])"
	| testop :
		"(wf_context C) ⟹
		 (wf_instr (TESTOP t testop_t)) ⟹
		 Instr_ok C (TESTOP t testop_t) (mk_functype [t] [I32])"
	| relop :
		"(wf_context C) ⟹
		 (wf_instr (RELOP t relop_t)) ⟹
		 Instr_ok C (RELOP t relop_t) (mk_functype [t, t] [I32])"
	| cvtop_reinterpret :
		"((size nt_1) = (size nt_2)) ⟹
		 (wf_context C) ⟹
		 (wf_instr (CVTOP nt_1 nt_2 REINTERPRET)) ⟹
		 Instr_ok C (CVTOP nt_1 nt_2 REINTERPRET) (mk_functype [nt_2] [nt_1])"
	| cvtop_convert :
		"(wf_context C) ⟹
		 (wf_instr (CVTOP nt_1 nt_2 v_cvtop)) ⟹
		 Instr_ok C (CVTOP nt_1 nt_2 v_cvtop) (mk_functype [nt_2] [nt_1])"
	| local_get :
		"((proj_uN_0 x) < (length (context_LOCALS C))) ⟹
		 (((context_LOCALS C) ! (proj_uN_0 x)) = t) ⟹
		 (wf_context C) ⟹
		 (wf_instr (LOCAL_GET x)) ⟹
		 Instr_ok C (LOCAL_GET x) (mk_functype [] [t])"
	| local_set :
		"((proj_uN_0 x) < (length (context_LOCALS C))) ⟹
		 (((context_LOCALS C) ! (proj_uN_0 x)) = t) ⟹
		 (wf_context C) ⟹
		 (wf_instr (LOCAL_SET x)) ⟹
		 Instr_ok C (LOCAL_SET x) (mk_functype [t] [])"
	| local_tee :
		"((proj_uN_0 x) < (length (context_LOCALS C))) ⟹
		 (((context_LOCALS C) ! (proj_uN_0 x)) = t) ⟹
		 (wf_context C) ⟹
		 (wf_instr (LOCAL_TEE x)) ⟹
		 Instr_ok C (LOCAL_TEE x) (mk_functype [t] [t])"
	| global_get :
		"((proj_uN_0 x) < (length (context_GLOBALS C))) ⟹
		 (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype v_mut t)) ⟹
		 (wf_context C) ⟹
		 (wf_instr (GLOBAL_GET x)) ⟹
		 Instr_ok C (GLOBAL_GET x) (mk_functype [] [t])"
	| global_set :
		"((proj_uN_0 x) < (length (context_GLOBALS C))) ⟹
		 (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype (Some MUT) t)) ⟹
		 (wf_context C) ⟹
		 (wf_instr (GLOBAL_SET x)) ⟹
		 Instr_ok C (GLOBAL_SET x) (mk_functype [t] [])"
	| memory_size :
		"(0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 (wf_context C) ⟹
		 (wf_limits mt) ⟹
		 (wf_instr MEMORY_SIZE) ⟹
		 Instr_ok C MEMORY_SIZE (mk_functype [] [I32])"
	| memory_grow :
		"(0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 (wf_context C) ⟹
		 (wf_limits mt) ⟹
		 (wf_instr MEMORY_GROW) ⟹
		 Instr_ok C MEMORY_GROW (mk_functype [I32] [I32])"
	| load_val :
		"(0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) ≤ (((size t) :: nat) div (8 :: nat))) ⟹
		 (wf_context C) ⟹
		 (wf_limits mt) ⟹
		 (wf_instr (LOAD t None v_memarg)) ⟹
		 Instr_ok C (LOAD t None v_memarg) (mk_functype [I32] [t])"
	| load_pack :
		"(0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) ≤ ((v_M :: nat) div (8 :: nat))) ⟹
		 (wf_context C) ⟹
		 (wf_limits mt) ⟹
		 (wf_instr (LOAD (valtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_M) v_sx))) v_memarg)) ⟹
		 Instr_ok C (LOAD (valtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_M) v_sx))) v_memarg) (mk_functype [I32] [(valtype_Inn v_Inn)])"
	| store_val :
		"(0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) ≤ (((size t) :: nat) div (8 :: nat))) ⟹
		 (wf_context C) ⟹
		 (wf_limits mt) ⟹
		 (wf_instr (STORE t None v_memarg)) ⟹
		 Instr_ok C (STORE t None v_memarg) (mk_functype [I32, t] [])"
	| store_pack :
		"(0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = mt) ⟹
		 (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) ≤ ((v_M :: nat) div (8 :: nat))) ⟹
		 (wf_context C) ⟹
		 (wf_limits mt) ⟹
		 (wf_instr (STORE (valtype_Inn v_Inn) (Some (mk_sz v_M)) v_memarg)) ⟹
		 Instr_ok C (STORE (valtype_Inn v_Inn) (Some (mk_sz v_M)) v_memarg) (mk_functype [I32, (valtype_Inn v_Inn)] [])"
	| empty :
		"(wf_context C) ⟹
		 Instrs_ok C [] (mk_functype [] [])"
	| seq :
		"(Instr_ok C instr_1 (mk_functype t_1_lst t_2_lst)) ⟹
		 (Instrs_ok C instr_2_lst (mk_functype t_2_lst t_3_lst)) ⟹
		 (wf_context C) ⟹
		 (wf_instr instr_1) ⟹
		 list_all (λ (instr_2 :: instr). (wf_instr instr_2)) instr_2_lst ⟹
		 Instrs_ok C ([instr_1] @ instr_2_lst) (mk_functype t_1_lst t_3_lst)"
	| Instrs_ok__frame :
		"(Instrs_ok C instr_lst (mk_functype t_1_lst t_2_lst)) ⟹
		 (wf_context C) ⟹
		 list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 Instrs_ok C instr_lst (mk_functype (t_lst @ t_1_lst) (t_lst @ t_2_lst))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:122.1-122.69 *)
inductive Expr_ok :: "res_context ⇒ expr ⇒ resulttype ⇒ bool" where
	  mk_Expr_ok :
		"(Instrs_ok C instr_lst (mk_functype [] (option_to_list t_opt))) ⟹
		 (wf_context C) ⟹
		 list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 Expr_ok C instr_lst t_opt"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:315.1-315.79 *)
inductive Instr_const :: "res_context ⇒ instr ⇒ bool" where
	  Instr_const__const :
		"(wf_context C) ⟹
		 (wf_instr (res_CONST t c)) ⟹
		 Instr_const C (res_CONST t c)"
	| Instr_const__global_get :
		"((proj_uN_0 x) < (length (context_GLOBALS C))) ⟹
		 (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype None t)) ⟹
		 (wf_context C) ⟹
		 (wf_instr (GLOBAL_GET x)) ⟹
		 Instr_const C (GLOBAL_GET x)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:316.1-316.78 *)
inductive Expr_const :: "res_context ⇒ expr ⇒ bool" where
	  mk_Expr_const :
		"list_all (λ (v_instr :: instr). (Instr_const C v_instr)) instr_lst ⟹
		 (wf_context C) ⟹
		 list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 Expr_const C instr_lst"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:317.1-317.79 *)
inductive Expr_ok_const :: "res_context ⇒ expr ⇒ (valtype option) ⇒ bool" where
	  mk_Expr_ok_const :
		"(Expr_ok C v_expr t_opt) ⟹
		 (Expr_const C v_expr) ⟹
		 (wf_context C) ⟹
		 list_all (λ (v_expr :: instr). (wf_instr v_expr)) v_expr ⟹
		 Expr_ok_const C v_expr t_opt"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:341.1-341.73 *)
inductive Type_ok :: "type ⇒ functype ⇒ bool" where
	  mk_Type_ok :
		"(Functype_ok ft) ⟹
		 Type_ok (res_TYPE ft) ft"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:342.1-342.73 *)
inductive Func_ok :: "res_context ⇒ func ⇒ functype ⇒ bool" where
	  mk_Func_ok :
		"((proj_uN_0 x) < (length (context_TYPES C))) ⟹
		 (((context_TYPES C) ! (proj_uN_0 x)) = (mk_functype t_1_lst (option_to_list t_2_opt))) ⟹
		 (Expr_ok (append_res_context C ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_LOCALS = (t_1_lst @ t_lst), LABELS = [t_2_opt], context_RETURN = (Some t_2_opt) ⦈) v_expr t_2_opt) ⟹
		 (wf_context C) ⟹
		 (wf_func (func_FUNC x (map (λ (t :: valtype). (LOCAL t)) t_lst) v_expr)) ⟹
		 (wf_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_LOCALS = (t_1_lst @ t_lst), LABELS = [t_2_opt], context_RETURN = (Some t_2_opt) ⦈) ⟹
		 Func_ok C (func_FUNC x (map (λ (t :: valtype). (LOCAL t)) t_lst) v_expr) (mk_functype t_1_lst (option_to_list t_2_opt))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:343.1-343.75 *)
inductive Global_ok :: "res_context ⇒ global ⇒ globaltype ⇒ bool" where
	  mk_Global_ok :
		"(Globaltype_ok gt) ⟹
		 (gt = (mk_globaltype v_mut t)) ⟹
		 (Expr_ok_const C v_expr (Some t)) ⟹
		 (wf_context C) ⟹
		 (wf_global (global_GLOBAL gt v_expr)) ⟹
		 Global_ok C (global_GLOBAL gt v_expr) gt"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:344.1-344.74 *)
inductive Table_ok :: "res_context ⇒ table ⇒ tabletype ⇒ bool" where
	  mk_Table_ok :
		"(Tabletype_ok tt) ⟹
		 (wf_context C) ⟹
		 (wf_table (table_TABLE tt)) ⟹
		 Table_ok C (table_TABLE tt) tt"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:345.1-345.72 *)
inductive Mem_ok :: "res_context ⇒ mem ⇒ memtype ⇒ bool" where
	  mk_Mem_ok :
		"(Memtype_ok mt) ⟹
		 (wf_context C) ⟹
		 (wf_mem (MEMORY mt)) ⟹
		 Mem_ok C (MEMORY mt) mt"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:346.1-346.73 *)
inductive Elem_ok :: "res_context ⇒ elem ⇒ bool" where
	  mk_Elem_ok :
		"(0 < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! 0) = lim) ⟹
		 (Expr_ok_const C v_expr (Some I32)) ⟹
		 ((length ft_lst) = (length x_lst)) ⟹
		 list_all (λ (x :: idx). ((proj_uN_0 x) < (length (context_FUNCS C)))) x_lst ⟹
		 list_all2 (λ (ft :: functype) (x :: idx). (((context_FUNCS C) ! (proj_uN_0 x)) = ft)) ft_lst x_lst ⟹
		 (wf_context C) ⟹
		 (wf_limits lim) ⟹
		 (wf_elem (ELEM v_expr x_lst)) ⟹
		 Elem_ok C (ELEM v_expr x_lst)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:347.1-347.73 *)
inductive Data_ok :: "res_context ⇒ data ⇒ bool" where
	  mk_Data_ok :
		"(0 < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! 0) = lim) ⟹
		 (Expr_ok_const C v_expr (Some I32)) ⟹
		 (wf_context C) ⟹
		 (wf_limits lim) ⟹
		 (wf_data (DATA v_expr b_lst)) ⟹
		 Data_ok C (DATA v_expr b_lst)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:348.1-348.74 *)
inductive Start_ok :: "res_context ⇒ start ⇒ bool" where
	  mk_Start_ok :
		"((proj_uN_0 x) < (length (context_FUNCS C))) ⟹
		 (((context_FUNCS C) ! (proj_uN_0 x)) = (mk_functype [] [])) ⟹
		 (wf_context C) ⟹
		 (wf_start (START x)) ⟹
		 Start_ok C (START x)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:396.1-396.80 *)
inductive Import_ok :: "res_context ⇒ import ⇒ externtype ⇒ bool" where
	  mk_Import_ok :
		"(Externtype_ok xt) ⟹
		 (wf_context C) ⟹
		 (wf_import (IMPORT name_1 name_2 xt)) ⟹
		 Import_ok C (IMPORT name_1 name_2 xt) xt"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:398.1-398.83 *)
inductive Externidx_ok :: "res_context ⇒ externidx ⇒ externtype ⇒ bool" where
	  Externidx_ok__func :
		"((proj_uN_0 x) < (length (context_FUNCS C))) ⟹
		 (((context_FUNCS C) ! (proj_uN_0 x)) = ft) ⟹
		 (wf_context C) ⟹
		 (wf_externidx (externidx_FUNC x)) ⟹
		 (wf_externtype (FUNC ft)) ⟹
		 Externidx_ok C (externidx_FUNC x) (FUNC ft)"
	| Externidx_ok__global :
		"((proj_uN_0 x) < (length (context_GLOBALS C))) ⟹
		 (((context_GLOBALS C) ! (proj_uN_0 x)) = gt) ⟹
		 (wf_context C) ⟹
		 (wf_externidx (externidx_GLOBAL x)) ⟹
		 (wf_externtype (GLOBAL gt)) ⟹
		 Externidx_ok C (externidx_GLOBAL x) (GLOBAL gt)"
	| Externidx_ok__table :
		"((proj_uN_0 x) < (length (context_TABLES C))) ⟹
		 (((context_TABLES C) ! (proj_uN_0 x)) = tt) ⟹
		 (wf_context C) ⟹
		 (wf_externidx (externidx_TABLE x)) ⟹
		 (wf_externtype (TABLE tt)) ⟹
		 Externidx_ok C (externidx_TABLE x) (TABLE tt)"
	| Externidx_ok__mem :
		"((proj_uN_0 x) < (length (context_MEMS C))) ⟹
		 (((context_MEMS C) ! (proj_uN_0 x)) = mt) ⟹
		 (wf_context C) ⟹
		 (wf_externidx (externidx_MEM x)) ⟹
		 (wf_externtype (MEM mt)) ⟹
		 Externidx_ok C (externidx_MEM x) (MEM mt)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:397.1-397.80 *)
inductive Export_ok :: "res_context ⇒ export ⇒ externtype ⇒ bool" where
	  mk_Export_ok :
		"(Externidx_ok C v_externidx xt) ⟹
		 (wf_context C) ⟹
		 (wf_externtype xt) ⟹
		 (wf_export (EXPORT v_name v_externidx)) ⟹
		 Export_ok C (EXPORT v_name v_externidx) xt"

(* Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:428.1-428.62 *)
inductive Module_ok :: "module ⇒ bool" where
	  mk_Module_ok :
		"(fun_memsxt ixt_lst var_3) ⟹
		 (fun_tablesxt ixt_lst var_2) ⟹
		 (fun_globalsxt ixt_lst var_1) ⟹
		 (fun_funcsxt ixt_lst var_0) ⟹
		 ((length ft'_lst) = (length type_lst)) ⟹
		 list_all2 (λ (ft' :: functype) (v_type :: type). (Type_ok v_type ft')) ft'_lst type_lst ⟹
		 ((length import_lst) = (length ixt_lst)) ⟹
		 list_all2 (λ (v_import :: import) (ixt :: externtype). (Import_ok ⦇ context_TYPES = ft'_lst, context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_LOCALS = [], LABELS = [], context_RETURN = None ⦈ v_import ixt)) import_lst ixt_lst ⟹
		 ((length global_lst) = (length gt_lst)) ⟹
		 list_all2 (λ (v_global :: global) (gt :: globaltype). (Global_ok C' v_global gt)) global_lst gt_lst ⟹
		 ((length ft_lst) = (length func_lst)) ⟹
		 list_all2 (λ (ft :: functype) (v_func :: func). (Func_ok C v_func ft)) ft_lst func_lst ⟹
		 ((length table_lst) = (length tt_lst)) ⟹
		 list_all2 (λ (v_table :: table) (tt :: tabletype). (Table_ok C v_table tt)) table_lst tt_lst ⟹
		 ((length mem_lst) = (length mt_lst)) ⟹
		 list_all2 (λ (v_mem :: mem) (mt :: memtype). (Mem_ok C v_mem mt)) mem_lst mt_lst ⟹
		 list_all (λ (v_elem :: elem). (Elem_ok C v_elem)) elem_lst ⟹
		 list_all (λ (v_data :: data). (Data_ok C v_data)) data_lst ⟹
		 list_all (λ (v_start :: start). (Start_ok C v_start)) (option_to_list start_opt) ⟹
		 ((length export_lst) = (length xt_lst)) ⟹
		 list_all2 (λ (v_export :: export) (xt :: externtype). (Export_ok C v_export xt)) export_lst xt_lst ⟹
		 ((length tt_lst) ≤ 1) ⟹
		 ((length mt_lst) ≤ 1) ⟹
		 (C = ⦇ context_TYPES = ft'_lst, context_FUNCS = (ift_lst @ ft_lst), context_GLOBALS = (igt_lst @ gt_lst), context_TABLES = (itt_lst @ tt_lst), context_MEMS = (imt_lst @ mt_lst), context_LOCALS = [], LABELS = [], context_RETURN = None ⦈) ⟹
		 (C' = ⦇ context_TYPES = ft'_lst, context_FUNCS = (ift_lst @ ft_lst), context_GLOBALS = igt_lst, context_TABLES = [], context_MEMS = [], context_LOCALS = [], LABELS = [], context_RETURN = None ⦈) ⟹
		 (ift_lst = var_0) ⟹
		 (igt_lst = var_1) ⟹
		 (itt_lst = var_2) ⟹
		 (imt_lst = var_3) ⟹
		 list_all (λ (ixt :: externtype). (wf_externtype ixt)) ixt_lst ⟹
		 (wf_context C') ⟹
		 (wf_context C) ⟹
		 list_all (λ (xt :: externtype). (wf_externtype xt)) xt_lst ⟹
		 list_all (λ (iter :: tabletype). (wf_limits iter)) var_2 ⟹
		 list_all (λ (iter :: memtype). (wf_limits iter)) var_3 ⟹
		 (wf_module (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)) ⟹
		 (wf_context ⦇ context_TYPES = ft'_lst, context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_LOCALS = [], LABELS = [], context_RETURN = None ⦈) ⟹
		 (wf_context ⦇ context_TYPES = ft'_lst, context_FUNCS = (ift_lst @ ft_lst), context_GLOBALS = (igt_lst @ gt_lst), context_TABLES = (itt_lst @ tt_lst), context_MEMS = (imt_lst @ mt_lst), context_LOCALS = [], LABELS = [], context_RETURN = None ⦈) ⟹
		 (wf_context ⦇ context_TYPES = ft'_lst, context_FUNCS = (ift_lst @ ft_lst), context_GLOBALS = igt_lst, context_TABLES = [], context_MEMS = [], context_LOCALS = [], LABELS = [], context_RETURN = None ⦈) ⟹
		 Module_ok (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:6.1-6.77 *)
inductive Step_pure :: "(admininstr list) ⇒ (admininstr list) ⇒ bool" where
	  Step_pure__unreachable :
		"(wf_admininstr admininstr_UNREACHABLE) ⟹
		 (wf_admininstr admininstr_TRAP) ⟹
		 Step_pure [admininstr_UNREACHABLE] [admininstr_TRAP]"
	| Step_pure__nop :
		"(wf_admininstr admininstr_NOP) ⟹
		 Step_pure [admininstr_NOP] []"
	| Step_pure__drop :
		"(wf_val v_val) ⟹
		 (wf_admininstr admininstr_DROP) ⟹
		 Step_pure [(admininstr_val v_val), admininstr_DROP] []"
	| select_true :
		"((proj_val__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_val__0 c)))) ≠ 0) ⟹
		 (wf_val val_1) ⟹
		 (wf_val val_2) ⟹
		 (wf_admininstr (admininstr_CONST I32 c)) ⟹
		 (wf_admininstr admininstr_SELECT) ⟹
		 Step_pure [(admininstr_val val_1), (admininstr_val val_2), (admininstr_CONST I32 c), admininstr_SELECT] [(admininstr_val val_1)]"
	| select_false :
		"((proj_val__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_val__0 c)))) = 0) ⟹
		 (wf_val val_1) ⟹
		 (wf_val val_2) ⟹
		 (wf_admininstr (admininstr_CONST I32 c)) ⟹
		 (wf_admininstr admininstr_SELECT) ⟹
		 Step_pure [(admininstr_val val_1), (admininstr_val val_2), (admininstr_CONST I32 c), admininstr_SELECT] [(admininstr_val val_2)]"
	| if_true :
		"((proj_val__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_val__0 c)))) ≠ 0) ⟹
		 (wf_admininstr (admininstr_CONST I32 c)) ⟹
		 (wf_admininstr (admininstr_IFELSE t_opt instr_1_lst instr_2_lst)) ⟹
		 (wf_admininstr (admininstr_BLOCK t_opt instr_1_lst)) ⟹
		 Step_pure [(admininstr_CONST I32 c), (admininstr_IFELSE t_opt instr_1_lst instr_2_lst)] [(admininstr_BLOCK t_opt instr_1_lst)]"
	| if_false :
		"((proj_val__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_val__0 c)))) = 0) ⟹
		 (wf_admininstr (admininstr_CONST I32 c)) ⟹
		 (wf_admininstr (admininstr_IFELSE t_opt instr_1_lst instr_2_lst)) ⟹
		 (wf_admininstr (admininstr_BLOCK t_opt instr_2_lst)) ⟹
		 Step_pure [(admininstr_CONST I32 c), (admininstr_IFELSE t_opt instr_1_lst instr_2_lst)] [(admininstr_BLOCK t_opt instr_2_lst)]"
	| label_vals :
		"(wf_admininstr (LABEL_underscore v_n instr_lst (map (λ (v_val :: val). (admininstr_val v_val)) val_lst))) ⟹
		 Step_pure [(LABEL_underscore v_n instr_lst (map (λ (v_val :: val). (admininstr_val v_val)) val_lst))] (map (λ (v_val :: val). (admininstr_val v_val)) val_lst)"
	| br_zero :
		"(wf_admininstr (LABEL_underscore v_n instr'_lst ((((map (λ (val' :: val). (admininstr_val val')) val'_lst) @ (map (λ (v_val :: val). (admininstr_val v_val)) val_lst)) @ [(admininstr_BR (mk_uN 0))]) @ (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst)))) ⟹
		 (v_n = (length val_lst)) ⟹
		 Step_pure [(LABEL_underscore v_n instr'_lst ((((map (λ (val' :: val). (admininstr_val val')) val'_lst) @ (map (λ (v_val :: val). (admininstr_val v_val)) val_lst)) @ [(admininstr_BR (mk_uN 0))]) @ (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst)))] ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ (map (λ (instr' :: instr). (admininstr_instr instr')) instr'_lst))"
	| br_succ :
		"(wf_admininstr (LABEL_underscore v_n instr'_lst (((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_BR (mk_uN ((proj_uN_0 l) + 1)))]) @ (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst)))) ⟹
		 (wf_admininstr (admininstr_BR l)) ⟹
		 Step_pure [(LABEL_underscore v_n instr'_lst (((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_BR (mk_uN ((proj_uN_0 l) + 1)))]) @ (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst)))] ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ [(admininstr_BR l)])"
	| br_if_true :
		"((proj_val__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_val__0 c)))) ≠ 0) ⟹
		 (wf_admininstr (admininstr_CONST I32 c)) ⟹
		 (wf_admininstr (admininstr_BR_IF l)) ⟹
		 (wf_admininstr (admininstr_BR l)) ⟹
		 Step_pure [(admininstr_CONST I32 c), (admininstr_BR_IF l)] [(admininstr_BR l)]"
	| br_if_false :
		"((proj_val__0 c) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_val__0 c)))) = 0) ⟹
		 (wf_admininstr (admininstr_CONST I32 c)) ⟹
		 (wf_admininstr (admininstr_BR_IF l)) ⟹
		 Step_pure [(admininstr_CONST I32 c), (admininstr_BR_IF l)] []"
	| br_table_lt :
		"((proj_uN_0 (the ((proj_val__0 i)))) < (length l_lst)) ⟹
		 ((proj_val__0 i) ≠ None) ⟹
		 (wf_admininstr (admininstr_CONST I32 i)) ⟹
		 (wf_admininstr (admininstr_BR_TABLE l_lst l')) ⟹
		 (wf_admininstr (admininstr_BR (l_lst ! (proj_uN_0 (the ((proj_val__0 i))))))) ⟹
		 Step_pure [(admininstr_CONST I32 i), (admininstr_BR_TABLE l_lst l')] [(admininstr_BR (l_lst ! (proj_uN_0 (the ((proj_val__0 i))))))]"
	| br_table_ge :
		"((proj_val__0 i) ≠ None) ⟹
		 ((proj_uN_0 (the ((proj_val__0 i)))) ≥ (length l_lst)) ⟹
		 (wf_admininstr (admininstr_CONST I32 i)) ⟹
		 (wf_admininstr (admininstr_BR_TABLE l_lst l')) ⟹
		 (wf_admininstr (admininstr_BR l')) ⟹
		 Step_pure [(admininstr_CONST I32 i), (admininstr_BR_TABLE l_lst l')] [(admininstr_BR l')]"
	| frame_vals :
		"(wf_admininstr (FRAME_underscore v_n f (map (λ (v_val :: val). (admininstr_val v_val)) val_lst))) ⟹
		 (v_n = (length val_lst)) ⟹
		 Step_pure [(FRAME_underscore v_n f (map (λ (v_val :: val). (admininstr_val v_val)) val_lst))] (map (λ (v_val :: val). (admininstr_val v_val)) val_lst)"
	| return_frame :
		"(wf_admininstr (FRAME_underscore v_n f ((((map (λ (val' :: val). (admininstr_val val')) val'_lst) @ (map (λ (v_val :: val). (admininstr_val v_val)) val_lst)) @ [admininstr_RETURN]) @ (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst)))) ⟹
		 (v_n = (length val_lst)) ⟹
		 Step_pure [(FRAME_underscore v_n f ((((map (λ (val' :: val). (admininstr_val val')) val'_lst) @ (map (λ (v_val :: val). (admininstr_val v_val)) val_lst)) @ [admininstr_RETURN]) @ (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst)))] (map (λ (v_val :: val). (admininstr_val v_val)) val_lst)"
	| return_label :
		"(wf_admininstr (LABEL_underscore v_n instr'_lst (((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ [admininstr_RETURN]) @ (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst)))) ⟹
		 (wf_admininstr admininstr_RETURN) ⟹
		 Step_pure [(LABEL_underscore v_n instr'_lst (((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ [admininstr_RETURN]) @ (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst)))] ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ [admininstr_RETURN])"
	| trap_vals :
		"((val_lst ≠ []) ∨ (instr_lst ≠ [])) ⟹
		 list_all (λ (v_val :: val). (wf_val v_val)) val_lst ⟹
		 list_all (λ (v_instr :: instr). (wf_instr v_instr)) instr_lst ⟹
		 (wf_admininstr admininstr_TRAP) ⟹
		 Step_pure ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ ([admininstr_TRAP] @ (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))) [admininstr_TRAP]"
	| trap_label :
		"(wf_admininstr (LABEL_underscore v_n instr'_lst [admininstr_TRAP])) ⟹
		 (wf_admininstr admininstr_TRAP) ⟹
		 Step_pure [(LABEL_underscore v_n instr'_lst [admininstr_TRAP])] [admininstr_TRAP]"
	| trap_frame :
		"(wf_admininstr (FRAME_underscore v_n f [admininstr_TRAP])) ⟹
		 (wf_admininstr admininstr_TRAP) ⟹
		 Step_pure [(FRAME_underscore v_n f [admininstr_TRAP])] [admininstr_TRAP]"
	| unop_val :
		"((length (fun_unop_underscore t unop c_1)) > 0) ⟹
		 (c ∈ set (fun_unop_underscore t unop c_1)) ⟹
		 list_all (λ (iter :: val_underscore). (wf_val_underscore t iter)) (fun_unop_underscore t unop c_1) ⟹
		 (wf_admininstr (admininstr_CONST t c_1)) ⟹
		 (wf_admininstr (admininstr_UNOP t unop)) ⟹
		 (wf_admininstr (admininstr_CONST t c)) ⟹
		 Step_pure [(admininstr_CONST t c_1), (admininstr_UNOP t unop)] [(admininstr_CONST t c)]"
	| unop_trap :
		"((fun_unop_underscore t unop c_1) = []) ⟹
		 list_all (λ (iter :: val_underscore). (wf_val_underscore t iter)) (fun_unop_underscore t unop c_1) ⟹
		 (wf_admininstr (admininstr_CONST t c_1)) ⟹
		 (wf_admininstr (admininstr_UNOP t unop)) ⟹
		 (wf_admininstr admininstr_TRAP) ⟹
		 Step_pure [(admininstr_CONST t c_1), (admininstr_UNOP t unop)] [admininstr_TRAP]"
	| binop_val :
		"(fun_binop_underscore t binop c_1 c_2 var_0) ⟹
		 ((length var_0) > 0) ⟹
		 (c ∈ set var_0) ⟹
		 list_all (λ (iter :: val_underscore). (wf_val_underscore t iter)) var_0 ⟹
		 (wf_admininstr (admininstr_CONST t c_1)) ⟹
		 (wf_admininstr (admininstr_CONST t c_2)) ⟹
		 (wf_admininstr (admininstr_BINOP t binop)) ⟹
		 (wf_admininstr (admininstr_CONST t c)) ⟹
		 Step_pure [(admininstr_CONST t c_1), (admininstr_CONST t c_2), (admininstr_BINOP t binop)] [(admininstr_CONST t c)]"
	| binop_trap :
		"(fun_binop_underscore t binop c_1 c_2 var_0) ⟹
		 (var_0 = []) ⟹
		 list_all (λ (iter :: val_underscore). (wf_val_underscore t iter)) var_0 ⟹
		 (wf_admininstr (admininstr_CONST t c_1)) ⟹
		 (wf_admininstr (admininstr_CONST t c_2)) ⟹
		 (wf_admininstr (admininstr_BINOP t binop)) ⟹
		 (wf_admininstr admininstr_TRAP) ⟹
		 Step_pure [(admininstr_CONST t c_1), (admininstr_CONST t c_2), (admininstr_BINOP t binop)] [admininstr_TRAP]"
	| Step_pure__testop :
		"(c = (fun_testop_underscore t testop c_1)) ⟹
		 (wf_val_underscore I32 (fun_testop_underscore t testop c_1)) ⟹
		 (wf_admininstr (admininstr_CONST t c_1)) ⟹
		 (wf_admininstr (admininstr_TESTOP t testop)) ⟹
		 (wf_admininstr (admininstr_CONST I32 c)) ⟹
		 Step_pure [(admininstr_CONST t c_1), (admininstr_TESTOP t testop)] [(admininstr_CONST I32 c)]"
	| Step_pure__relop :
		"(fun_relop_underscore t relop c_1 c_2 var_0) ⟹
		 (c = var_0) ⟹
		 (wf_val_underscore I32 var_0) ⟹
		 (wf_admininstr (admininstr_CONST t c_1)) ⟹
		 (wf_admininstr (admininstr_CONST t c_2)) ⟹
		 (wf_admininstr (admininstr_RELOP t relop)) ⟹
		 (wf_admininstr (admininstr_CONST I32 c)) ⟹
		 Step_pure [(admininstr_CONST t c_1), (admininstr_CONST t c_2), (admininstr_RELOP t relop)] [(admininstr_CONST I32 c)]"
	| cvtop_val :
		"(fun_cvtop__underscore t_1 t_2 v_cvtop c_1 var_0) ⟹
		 ((length var_0) > 0) ⟹
		 (c ∈ set var_0) ⟹
		 list_all (λ (iter :: val_underscore). (wf_val_underscore t_2 iter)) var_0 ⟹
		 (wf_admininstr (admininstr_CONST t_1 c_1)) ⟹
		 (wf_admininstr (admininstr_CVTOP t_2 t_1 v_cvtop)) ⟹
		 (wf_admininstr (admininstr_CONST t_2 c)) ⟹
		 Step_pure [(admininstr_CONST t_1 c_1), (admininstr_CVTOP t_2 t_1 v_cvtop)] [(admininstr_CONST t_2 c)]"
	| cvtop_trap :
		"(fun_cvtop__underscore t_1 t_2 v_cvtop c_1 var_0) ⟹
		 (var_0 = []) ⟹
		 list_all (λ (iter :: val_underscore). (wf_val_underscore t_2 iter)) var_0 ⟹
		 (wf_admininstr (admininstr_CONST t_1 c_1)) ⟹
		 (wf_admininstr (admininstr_CVTOP t_2 t_1 v_cvtop)) ⟹
		 (wf_admininstr admininstr_TRAP) ⟹
		 Step_pure [(admininstr_CONST t_1 c_1), (admininstr_CVTOP t_2 t_1 v_cvtop)] [admininstr_TRAP]"
	| Step_pure__local_tee :
		"(wf_val v_val) ⟹
		 (wf_admininstr (admininstr_LOCAL_TEE x)) ⟹
		 (wf_admininstr (admininstr_LOCAL_SET x)) ⟹
		 Step_pure [(admininstr_val v_val), (admininstr_LOCAL_TEE x)] [(admininstr_val v_val), (admininstr_val v_val), (admininstr_LOCAL_SET x)]"

(* Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:121.1-123.15 *)
inductive Step_read_before_call_indirect_trap :: "config ⇒ bool" where
	  call_indirect_call_0 :
		"((proj_uN_0 (the ((proj_val__0 i)))) < (length (REFS (fun_table z (mk_uN 0))))) ⟹
		 ((proj_val__0 i) ≠ None) ⟹
		 (((REFS (fun_table z (mk_uN 0))) ! (proj_uN_0 (the ((proj_val__0 i))))) = (Some a)) ⟹
		 (a < (length (fun_funcinst z))) ⟹
		 ((fun_type z x) = (funcinst_TYPE ((fun_funcinst z) ! a))) ⟹
		 (wf_tableinst (fun_table z (mk_uN 0))) ⟹
		 list_all (λ (iter :: funcinst). (wf_funcinst iter)) (fun_funcinst z) ⟹
		 (wf_config (mk_config z [(admininstr_CONST I32 i), (admininstr_CALL_INDIRECT x)])) ⟹
		 (wf_admininstr (CALL_ADDR a)) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 Step_read_before_call_indirect_trap (mk_config z [(admininstr_CONST I32 i), (admininstr_CALL_INDIRECT x)])"

(* Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:7.1-7.77 *)
inductive Step_read :: "config ⇒ (admininstr list) ⇒ bool" where
	  Step_read__block :
		"(((t_opt = None) ∧ (v_n = 0)) ∨ ((t_opt ≠ None) ∧ (v_n = 1))) ⟹
		 (wf_config (mk_config z [(admininstr_BLOCK t_opt instr_lst)])) ⟹
		 (wf_admininstr (LABEL_underscore v_n [] (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))) ⟹
		 Step_read (mk_config z [(admininstr_BLOCK t_opt instr_lst)]) [(LABEL_underscore v_n [] (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))]"
	| Step_read__loop :
		"(wf_config (mk_config z [(admininstr_LOOP t_opt instr_lst)])) ⟹
		 (wf_admininstr (LABEL_underscore 0 [(LOOP t_opt instr_lst)] (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))) ⟹
		 Step_read (mk_config z [(admininstr_LOOP t_opt instr_lst)]) [(LABEL_underscore 0 [(LOOP t_opt instr_lst)] (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))]"
	| Step_read__call :
		"((proj_uN_0 x) < (length (fun_funcaddr z))) ⟹
		 (wf_config (mk_config z [(admininstr_CALL x)])) ⟹
		 (wf_admininstr (CALL_ADDR ((fun_funcaddr z) ! (proj_uN_0 x)))) ⟹
		 Step_read (mk_config z [(admininstr_CALL x)]) [(CALL_ADDR ((fun_funcaddr z) ! (proj_uN_0 x)))]"
	| call_indirect_call :
		"((proj_uN_0 (the ((proj_val__0 i)))) < (length (REFS (fun_table z (mk_uN 0))))) ⟹
		 ((proj_val__0 i) ≠ None) ⟹
		 (((REFS (fun_table z (mk_uN 0))) ! (proj_uN_0 (the ((proj_val__0 i))))) = (Some a)) ⟹
		 (a < (length (fun_funcinst z))) ⟹
		 ((fun_type z x) = (funcinst_TYPE ((fun_funcinst z) ! a))) ⟹
		 (wf_tableinst (fun_table z (mk_uN 0))) ⟹
		 list_all (λ (iter :: funcinst). (wf_funcinst iter)) (fun_funcinst z) ⟹
		 (wf_config (mk_config z [(admininstr_CONST I32 i), (admininstr_CALL_INDIRECT x)])) ⟹
		 (wf_admininstr (CALL_ADDR a)) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 Step_read (mk_config z [(admininstr_CONST I32 i), (admininstr_CALL_INDIRECT x)]) [(CALL_ADDR a)]"
	| call_indirect_trap :
		"(~(Step_read_before_call_indirect_trap (mk_config z [(admininstr_CONST I32 i), (admininstr_CALL_INDIRECT x)]))) ⟹
		 (wf_config (mk_config z [(admininstr_CONST I32 i), (admininstr_CALL_INDIRECT x)])) ⟹
		 (wf_admininstr admininstr_TRAP) ⟹
		 Step_read (mk_config z [(admininstr_CONST I32 i), (admininstr_CALL_INDIRECT x)]) [admininstr_TRAP]"
	| call_addr :
		"(a < (length (fun_funcinst z))) ⟹
		 (((fun_funcinst z) ! a) = ⦇ funcinst_TYPE = (mk_functype t_1_lst t_2_lst), funcinst_MODULE = mm, CODE = v_func ⦈) ⟹
		 (v_func = (func_FUNC x (map (λ (t :: valtype). (LOCAL t)) t_lst) instr_lst)) ⟹
		 (f = ⦇ LOCALS = (val_lst @ (map (λ (t :: valtype). (default_underscore t)) t_lst)), frame_MODULE = mm ⦈) ⟹
		 list_all (λ (iter :: funcinst). (wf_funcinst iter)) (fun_funcinst z) ⟹
		 (wf_config (mk_config z ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ [(CALL_ADDR a)]))) ⟹
		 (wf_admininstr (FRAME_underscore v_n f [(LABEL_underscore v_n [] (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))])) ⟹
		 (wf_funcinst ⦇ funcinst_TYPE = (mk_functype t_1_lst t_2_lst), funcinst_MODULE = mm, CODE = v_func ⦈) ⟹
		 (wf_func (func_FUNC x (map (λ (t :: valtype). (LOCAL t)) t_lst) instr_lst)) ⟹
		 (wf_frame ⦇ LOCALS = (val_lst @ (map (λ (t :: valtype). (default_underscore t)) t_lst)), frame_MODULE = mm ⦈) ⟹
		 (k = (length val_lst)) ⟹
		 (k = (length t_1_lst)) ⟹
		 (v_n = (length t_2_lst)) ⟹
		 Step_read (mk_config z ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ [(CALL_ADDR a)])) [(FRAME_underscore v_n f [(LABEL_underscore v_n [] (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))])]"
	| Step_read__local_get :
		"(wf_val (fun_local z x)) ⟹
		 (wf_config (mk_config z [(admininstr_LOCAL_GET x)])) ⟹
		 Step_read (mk_config z [(admininstr_LOCAL_GET x)]) [(admininstr_val (fun_local z x))]"
	| Step_read__global_get :
		"(wf_globalinst (fun_global z x)) ⟹
		 (wf_config (mk_config z [(admininstr_GLOBAL_GET x)])) ⟹
		 Step_read (mk_config z [(admininstr_GLOBAL_GET x)]) [(admininstr_val (VALUE (fun_global z x)))]"
	| load_num_trap :
		"((proj_val__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_val__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((size t) :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_config (mk_config z [(admininstr_CONST I32 i), (admininstr_LOAD t None ao)])) ⟹
		 (wf_admininstr admininstr_TRAP) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 Step_read (mk_config z [(admininstr_CONST I32 i), (admininstr_LOAD t None ao)]) [admininstr_TRAP]"
	| load_num_val :
		"((proj_val__0 i) ≠ None) ⟹
		 ((bytes_underscore t c) = (list_slice (BYTES (fun_mem z (mk_uN 0))) ((proj_uN_0 (the ((proj_val__0 i)))) + (proj_uN_0 (OFFSET ao))) ((((size t) :: nat) div (8 :: nat)) :: nat))) ⟹
		 list_all (λ (iter :: byte). (wf_byte iter)) (bytes_underscore t c) ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_config (mk_config z [(admininstr_CONST I32 i), (admininstr_LOAD t None ao)])) ⟹
		 (wf_admininstr (admininstr_CONST t c)) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 Step_read (mk_config z [(admininstr_CONST I32 i), (admininstr_LOAD t None ao)]) [(admininstr_CONST t c)]"
	| load_pack_trap :
		"((proj_val__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_val__0 i)))) + (proj_uN_0 (OFFSET ao))) + (((v_n :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_config (mk_config z [(admininstr_CONST I32 i), (admininstr_LOAD (valtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) ao)])) ⟹
		 (wf_admininstr admininstr_TRAP) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 Step_read (mk_config z [(admininstr_CONST I32 i), (admininstr_LOAD (valtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) ao)]) [admininstr_TRAP]"
	| load_pack_val :
		"((proj_val__0 i) ≠ None) ⟹
		 ((ibytes_underscore v_n c) = (list_slice (BYTES (fun_mem z (mk_uN 0))) ((proj_uN_0 (the ((proj_val__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_n :: nat) div (8 :: nat)) :: nat))) ⟹
		 list_all (λ (iter :: byte). (wf_byte iter)) (ibytes_underscore v_n c) ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_config (mk_config z [(admininstr_CONST I32 i), (admininstr_LOAD (valtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) ao)])) ⟹
		 (wf_admininstr (admininstr_CONST (valtype_Inn v_Inn) (mk_val__0 v_Inn (extend__underscore v_n (size (valtype_Inn v_Inn)) v_sx c)))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 Step_read (mk_config z [(admininstr_CONST I32 i), (admininstr_LOAD (valtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_n) v_sx))) ao)]) [(admininstr_CONST (valtype_Inn v_Inn) (mk_val__0 v_Inn (extend__underscore v_n (size (valtype_Inn v_Inn)) v_sx c)))]"
	| Step_read__memory_size :
		"(((v_n * 64) * (Ki )) = (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_config (mk_config z [admininstr_MEMORY_SIZE])) ⟹
		 (wf_admininstr (admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN v_n)))) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 Step_read (mk_config z [admininstr_MEMORY_SIZE]) [(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN v_n)))]"

(* Mutual Recursion at: ../specification/wasm-1.0/8-reduction.spectec:5.1-5.77 *)
inductive Step :: "config ⇒ config ⇒ bool" where
	  pure :
		"(Step_pure admininstr_lst admininstr'_lst) ⟹
		 (wf_config (mk_config z admininstr_lst)) ⟹
		 (wf_config (mk_config z admininstr'_lst)) ⟹
		 Step (mk_config z admininstr_lst) (mk_config z admininstr'_lst)"
	| read :
		"(Step_read (mk_config z admininstr_lst) admininstr'_lst) ⟹
		 (wf_config (mk_config z admininstr_lst)) ⟹
		 (wf_config (mk_config z admininstr'_lst)) ⟹
		 Step (mk_config z admininstr_lst) (mk_config z admininstr'_lst)"
	| ctxt_label :
		"(Step (mk_config z admininstr_lst) (mk_config z' admininstr'_lst)) ⟹
		 (wf_config (mk_config z [(LABEL_underscore v_n instr_0_lst admininstr_lst)])) ⟹
		 (wf_config (mk_config z' [(LABEL_underscore v_n instr_0_lst admininstr'_lst)])) ⟹
		 (wf_config (mk_config z admininstr_lst)) ⟹
		 (wf_config (mk_config z' admininstr'_lst)) ⟹
		 Step (mk_config z [(LABEL_underscore v_n instr_0_lst admininstr_lst)]) (mk_config z' [(LABEL_underscore v_n instr_0_lst admininstr'_lst)])"
	| ctxt_frame :
		"(Step (mk_config (mk_state s f') admininstr_lst) (mk_config (mk_state s' f'') admininstr'_lst)) ⟹
		 (wf_config (mk_config (mk_state s f) [(FRAME_underscore v_n f' admininstr_lst)])) ⟹
		 (wf_config (mk_config (mk_state s' f) [(FRAME_underscore v_n f'' admininstr'_lst)])) ⟹
		 (wf_config (mk_config (mk_state s f') admininstr_lst)) ⟹
		 (wf_config (mk_config (mk_state s' f'') admininstr'_lst)) ⟹
		 Step (mk_config (mk_state s f) [(FRAME_underscore v_n f' admininstr_lst)]) (mk_config (mk_state s' f) [(FRAME_underscore v_n f'' admininstr'_lst)])"
	| ctxt_instrs :
		"(Step (mk_config z admininstr_lst) (mk_config z' admininstr'_lst)) ⟹
		 ((val_lst ≠ []) ∨ (admininstr_1_lst ≠ [])) ⟹
		 (wf_config (mk_config z ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ (admininstr_lst @ admininstr_1_lst)))) ⟹
		 (wf_config (mk_config z' ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ (admininstr'_lst @ admininstr_1_lst)))) ⟹
		 (wf_config (mk_config z admininstr_lst)) ⟹
		 (wf_config (mk_config z' admininstr'_lst)) ⟹
		 Step (mk_config z ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ (admininstr_lst @ admininstr_1_lst))) (mk_config z' ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ (admininstr'_lst @ admininstr_1_lst)))"
	| Step__local_set :
		"(wf_config (mk_config z [(admininstr_val v_val), (admininstr_LOCAL_SET x)])) ⟹
		 (wf_config (mk_config (with_local z x v_val) [])) ⟹
		 Step (mk_config z [(admininstr_val v_val), (admininstr_LOCAL_SET x)]) (mk_config (with_local z x v_val) [])"
	| Step__global_set :
		"(wf_config (mk_config z [(admininstr_val v_val), (admininstr_GLOBAL_SET x)])) ⟹
		 (wf_config (mk_config (with_global z x v_val) [])) ⟹
		 Step (mk_config z [(admininstr_val v_val), (admininstr_GLOBAL_SET x)]) (mk_config (with_global z x v_val) [])"
	| store_num_trap :
		"((proj_val__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_val__0 i)))) + (proj_uN_0 (OFFSET ao))) + ((((size t) :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_config (mk_config z [(admininstr_CONST I32 i), (admininstr_CONST t c), (admininstr_STORE t None ao)])) ⟹
		 (wf_config (mk_config z [admininstr_TRAP])) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 Step (mk_config z [(admininstr_CONST I32 i), (admininstr_CONST t c), (admininstr_STORE t None ao)]) (mk_config z [admininstr_TRAP])"
	| store_num_val :
		"((proj_val__0 i) ≠ None) ⟹
		 (b_lst = (bytes_underscore t c)) ⟹
		 list_all (λ (iter :: byte). (wf_byte iter)) (bytes_underscore t c) ⟹
		 (wf_config (mk_config z [(admininstr_CONST I32 i), (admininstr_CONST t c), (admininstr_STORE t None ao)])) ⟹
		 (wf_config (mk_config (with_mem z (mk_uN 0) ((proj_uN_0 (the ((proj_val__0 i)))) + (proj_uN_0 (OFFSET ao))) ((((size t) :: nat) div (8 :: nat)) :: nat) b_lst) [])) ⟹
		 Step (mk_config z [(admininstr_CONST I32 i), (admininstr_CONST t c), (admininstr_STORE t None ao)]) (mk_config (with_mem z (mk_uN 0) ((proj_uN_0 (the ((proj_val__0 i)))) + (proj_uN_0 (OFFSET ao))) ((((size t) :: nat) div (8 :: nat)) :: nat) b_lst) [])"
	| store_pack_trap :
		"((proj_val__0 i) ≠ None) ⟹
		 ((((proj_uN_0 (the ((proj_val__0 i)))) + (proj_uN_0 (OFFSET ao))) + (((v_n :: nat) div (8 :: nat)) :: nat)) > (length (BYTES (fun_mem z (mk_uN 0))))) ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_config (mk_config z [(admininstr_CONST I32 i), (admininstr_CONST (valtype_Inn v_Inn) c), (admininstr_STORE (valtype_Inn v_Inn) (Some (mk_sz v_n)) ao)])) ⟹
		 (wf_config (mk_config z [admininstr_TRAP])) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 Step (mk_config z [(admininstr_CONST I32 i), (admininstr_CONST (valtype_Inn v_Inn) c), (admininstr_STORE (valtype_Inn v_Inn) (Some (mk_sz v_n)) ao)]) (mk_config z [admininstr_TRAP])"
	| store_pack_val :
		"((proj_val__0 i) ≠ None) ⟹
		 ((proj_val__0 c) ≠ None) ⟹
		 (b_lst = (ibytes_underscore v_n (wrap__underscore (size (valtype_Inn v_Inn)) v_n (the ((proj_val__0 c)))))) ⟹
		 list_all (λ (iter :: byte). (wf_byte iter)) (ibytes_underscore v_n (wrap__underscore (size (valtype_Inn v_Inn)) v_n (the ((proj_val__0 c))))) ⟹
		 (wf_uN v_n (wrap__underscore (size (valtype_Inn v_Inn)) v_n (the ((proj_val__0 c))))) ⟹
		 (wf_config (mk_config z [(admininstr_CONST I32 i), (admininstr_CONST (valtype_Inn v_Inn) c), (admininstr_STORE (valtype_Inn v_Inn) (Some (mk_sz v_n)) ao)])) ⟹
		 (wf_config (mk_config (with_mem z (mk_uN 0) ((proj_uN_0 (the ((proj_val__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_n :: nat) div (8 :: nat)) :: nat) b_lst) [])) ⟹
		 Step (mk_config z [(admininstr_CONST I32 i), (admininstr_CONST (valtype_Inn v_Inn) c), (admininstr_STORE (valtype_Inn v_Inn) (Some (mk_sz v_n)) ao)]) (mk_config (with_mem z (mk_uN 0) ((proj_uN_0 (the ((proj_val__0 i)))) + (proj_uN_0 (OFFSET ao))) (((v_n :: nat) div (8 :: nat)) :: nat) b_lst) [])"
	| memory_grow_succeed :
		"(fun_growmemory (fun_mem z (mk_uN 0)) v_n var_0) ⟹
		 (var_0 ≠ None) ⟹
		 ((the (var_0)) = mi) ⟹
		 (wf_meminst (the (var_0))) ⟹
		 (wf_meminst (fun_mem z (mk_uN 0))) ⟹
		 (wf_config (mk_config z [(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN v_n))), admininstr_MEMORY_GROW])) ⟹
		 (wf_config (mk_config (with_meminst z (mk_uN 0) mi) [(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN ((((length (BYTES (fun_mem z (mk_uN 0)))) :: nat) div ((64 * (Ki )) :: nat)) :: nat))))])) ⟹
		 (wf_uN 32 (mk_uN 0)) ⟹
		 Step (mk_config z [(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN v_n))), admininstr_MEMORY_GROW]) (mk_config (with_meminst z (mk_uN 0) mi) [(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN ((((length (BYTES (fun_mem z (mk_uN 0)))) :: nat) div ((64 * (Ki )) :: nat)) :: nat))))])"
	| memory_grow_fail :
		"(fun_inv_signed_underscore 32 (0 - (1 :: nat)) var_0) ⟹
		 (wf_config (mk_config z [(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN v_n))), admininstr_MEMORY_GROW])) ⟹
		 (wf_config (mk_config z [(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN var_0)))])) ⟹
		 Step (mk_config z [(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN v_n))), admininstr_MEMORY_GROW]) (mk_config z [(admininstr_CONST I32 (mk_val__0 Inn_I32 (mk_uN var_0)))])"

(* Mutual Recursion at: ../specification/wasm-1.0/8-reduction.spectec:8.1-8.77 *)
inductive Steps :: "config ⇒ config ⇒ bool" where
	  refl :
		"(wf_config (mk_config z admininstr_lst)) ⟹
		 Steps (mk_config z admininstr_lst) (mk_config z admininstr_lst)"
	| trans :
		"(Step (mk_config z admininstr_lst) (mk_config z' admininstr'_lst)) ⟹
		 (Steps (mk_config z' admininstr'_lst) (mk_config z'' admininstr''_lst)) ⟹
		 (wf_config (mk_config z admininstr_lst)) ⟹
		 (wf_config (mk_config z'' admininstr''_lst)) ⟹
		 (wf_config (mk_config z' admininstr'_lst)) ⟹
		 Steps (mk_config z admininstr_lst) (mk_config z'' admininstr''_lst)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:29.1-29.83 *)
inductive Eval_expr :: "state ⇒ expr ⇒ state ⇒ (val list) ⇒ bool" where
	  mk_Eval_expr :
		"(Steps (mk_config z (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst)) (mk_config z' (map (λ (v_val :: val). (admininstr_val v_val)) val_lst))) ⟹
		 (wf_config (mk_config z (map (λ (v_instr :: instr). (admininstr_instr v_instr)) instr_lst))) ⟹
		 (wf_config (mk_config z' (map (λ (v_val :: val). (admininstr_val v_val)) val_lst))) ⟹
		 Eval_expr z instr_lst z' val_lst"

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:5.1-5.36 *)
inductive fun_funcs :: "(externaddr list) ⇒ (funcaddr list) ⇒ bool" where
	  fun_funcs_case_0 :
		"fun_funcs [] []"
	| fun_funcs_case_1 :
		"(fun_funcs externaddr'_lst var_0) ⟹
		 fun_funcs ([(externaddr_FUNC fa)] @ externaddr'_lst) ([fa] @ var_0)"
	| fun_funcs_case_2 :
		"(fun_funcs externaddr'_lst var_0) ⟹
		 fun_funcs ([v_externaddr] @ externaddr'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:11.1-11.40 *)
inductive fun_globals :: "(externaddr list) ⇒ (globaladdr list) ⇒ bool" where
	  fun_globals_case_0 :
		"fun_globals [] []"
	| fun_globals_case_1 :
		"(fun_globals externaddr'_lst var_0) ⟹
		 fun_globals ([(externaddr_GLOBAL ga)] @ externaddr'_lst) ([ga] @ var_0)"
	| fun_globals_case_2 :
		"(fun_globals externaddr'_lst var_0) ⟹
		 fun_globals ([v_externaddr] @ externaddr'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:17.1-17.38 *)
inductive fun_tables :: "(externaddr list) ⇒ (tableaddr list) ⇒ bool" where
	  fun_tables_case_0 :
		"fun_tables [] []"
	| fun_tables_case_1 :
		"(fun_tables externaddr'_lst var_0) ⟹
		 fun_tables ([(externaddr_TABLE ta)] @ externaddr'_lst) ([ta] @ var_0)"
	| fun_tables_case_2 :
		"(fun_tables externaddr'_lst var_0) ⟹
		 fun_tables ([v_externaddr] @ externaddr'_lst) var_0"

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:23.1-23.34 *)
inductive fun_mems :: "(externaddr list) ⇒ (memaddr list) ⇒ bool" where
	  fun_mems_case_0 :
		"fun_mems [] []"
	| fun_mems_case_1 :
		"(fun_mems externaddr'_lst var_0) ⟹
		 fun_mems ([(externaddr_MEM ma)] @ externaddr'_lst) ([ma] @ var_0)"
	| fun_mems_case_2 :
		"(fun_mems externaddr'_lst var_0) ⟹
		 fun_mems ([v_externaddr] @ externaddr'_lst) var_0"

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:36.6-36.16 *)
inductive fun_allocfunc :: "store ⇒ moduleinst ⇒ func ⇒ (store * funcaddr) ⇒ bool" where
	  fun_allocfunc_case_0 :
		"((proj_uN_0 x) < (length (TYPES v_moduleinst))) ⟹
		 (fi = ⦇ funcinst_TYPE = ((TYPES v_moduleinst) ! (proj_uN_0 x)), funcinst_MODULE = v_moduleinst, CODE = v_func ⦈) ⟹
		 (v_func = (func_FUNC x local_lst v_expr)) ⟹
		 (wf_funcinst ⦇ funcinst_TYPE = ((TYPES v_moduleinst) ! (proj_uN_0 x)), funcinst_MODULE = v_moduleinst, CODE = v_func ⦈) ⟹
		 (wf_func (func_FUNC x local_lst v_expr)) ⟹
		 fun_allocfunc s v_moduleinst v_func ((s ⦇ store_FUNCS := ((store_FUNCS s) @ [fi])  ⦈), (length (store_FUNCS s)))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:36.6-36.16 *)
lemma allocfunc_is_wf :
	"(fun_allocfunc v_store v_moduleinst v_func var_0) ⟹
	 (wf_store v_store) ⟹
	 (wf_moduleinst v_moduleinst) ⟹
	 (wf_func v_func) ⟹
	 (ret_val = var_0) ⟹
	 (wf_store (fst ret_val))"
sorry

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:41.1-41.63 *)
inductive fun_allocfuncs :: "store ⇒ moduleinst ⇒ (func list) ⇒ (store * (funcaddr list)) ⇒ bool" where
	  fun_allocfuncs_case_0 :
		"fun_allocfuncs s v_moduleinst [] (s, [])"
	| fun_allocfuncs_case_1 :
		"(fun_allocfuncs s_1 v_moduleinst func'_lst var_1) ⟹
		 (fun_allocfunc s v_moduleinst v_func var_0) ⟹
		 ((s_1, fa) = var_0) ⟹
		 ((s_2, fa'_lst) = var_1) ⟹
		 fun_allocfuncs s v_moduleinst ([v_func] @ func'_lst) (s_2, ([fa] @ fa'_lst))"

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:41.1-41.63 *)
inductive allocfuncs_is_wf :: "store ⇒ moduleinst ⇒ (func list) ⇒ (store * (funcaddr list)) ⇒ bool" where
	  allocfuncs_is_wf_0 :
		"(fun_allocfuncs v_store v_moduleinst var_0_lst var_0) ⟹
		 (wf_store v_store) ⟹
		 (wf_moduleinst v_moduleinst) ⟹
		 list_all (λ (var_0 :: func). (wf_func var_0)) var_0_lst ⟹
		 (ret_val = var_0) ⟹
		 (wf_store (fst ret_val)) ⟹
		 allocfuncs_is_wf v_store v_moduleinst var_0_lst ret_val"

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:47.6-47.18 *)
inductive fun_allocglobal :: "store ⇒ globaltype ⇒ val ⇒ (store * globaladdr) ⇒ bool" where
	  fun_allocglobal_case_0 :
		"(gi = ⦇ globalinst_TYPE = v_globaltype, VALUE = v_val ⦈) ⟹
		 (wf_globalinst ⦇ globalinst_TYPE = v_globaltype, VALUE = v_val ⦈) ⟹
		 fun_allocglobal s v_globaltype v_val ((s ⦇ store_GLOBALS := ((store_GLOBALS s) @ [gi])  ⦈), (length (store_GLOBALS s)))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:47.6-47.18 *)
lemma allocglobal_is_wf :
	"(fun_allocglobal v_store v_globaltype v_val var_0) ⟹
	 (wf_store v_store) ⟹
	 (wf_val v_val) ⟹
	 (ret_val = var_0) ⟹
	 (wf_store (fst ret_val))"
sorry

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:51.1-51.67 *)
inductive fun_allocglobals :: "store ⇒ (globaltype list) ⇒ (val list) ⇒ (store * (globaladdr list)) ⇒ bool" where
	  fun_allocglobals_case_0 :
		"fun_allocglobals s [] [] (s, [])"
	| fun_allocglobals_case_1 :
		"(fun_allocglobals s_1 globaltype'_lst val'_lst var_1) ⟹
		 (fun_allocglobal s v_globaltype v_val var_0) ⟹
		 ((s_1, ga) = var_0) ⟹
		 ((s_2, ga'_lst) = var_1) ⟹
		 fun_allocglobals s ([v_globaltype] @ globaltype'_lst) ([v_val] @ val'_lst) (s_2, ([ga] @ ga'_lst))"

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:51.1-51.67 *)
inductive allocglobals_is_wf :: "store ⇒ (globaltype list) ⇒ (val list) ⇒ (store * (globaladdr list)) ⇒ bool" where
	  allocglobals_is_wf_0 :
		"(fun_allocglobals v_store var_0_lst var_1_lst var_0) ⟹
		 (wf_store v_store) ⟹
		 list_all (λ (var_1 :: val). (wf_val var_1)) var_1_lst ⟹
		 (ret_val = var_0) ⟹
		 (wf_store (fst ret_val)) ⟹
		 allocglobals_is_wf v_store var_0_lst var_1_lst ret_val"

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:57.6-57.17 *)
inductive fun_alloctable :: "store ⇒ tabletype ⇒ (store * tableaddr) ⇒ bool" where
	  fun_alloctable_case_0 :
		"(ti = ⦇ tableinst_TYPE = (mk_limits i j_opt), REFS = (repeat (proj_uN_0 i) None) ⦈) ⟹
		 (wf_tableinst ⦇ tableinst_TYPE = (mk_limits i j_opt), REFS = (repeat (proj_uN_0 i) None) ⦈) ⟹
		 fun_alloctable s (mk_limits i j_opt) ((s ⦇ store_TABLES := ((store_TABLES s) @ [ti])  ⦈), (length (store_TABLES s)))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:57.6-57.17 *)
lemma alloctable_is_wf :
	"(fun_alloctable v_store v_tabletype var_0) ⟹
	 (wf_store v_store) ⟹
	 (wf_limits v_tabletype) ⟹
	 (ret_val = var_0) ⟹
	 (wf_store (fst ret_val))"
sorry

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:61.1-61.58 *)
inductive fun_alloctables :: "store ⇒ (tabletype list) ⇒ (store * (tableaddr list)) ⇒ bool" where
	  fun_alloctables_case_0 :
		"fun_alloctables s [] (s, [])"
	| fun_alloctables_case_1 :
		"(fun_alloctables s_1 tabletype'_lst var_1) ⟹
		 (fun_alloctable s v_tabletype var_0) ⟹
		 ((s_1, ta) = var_0) ⟹
		 ((s_2, ta'_lst) = var_1) ⟹
		 fun_alloctables s ([v_tabletype] @ tabletype'_lst) (s_2, ([ta] @ ta'_lst))"

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:61.1-61.58 *)
inductive alloctables_is_wf :: "store ⇒ (tabletype list) ⇒ (store * (tableaddr list)) ⇒ bool" where
	  alloctables_is_wf_0 :
		"(fun_alloctables v_store var_0_lst var_0) ⟹
		 (wf_store v_store) ⟹
		 list_all (λ (var_0 :: tabletype). (wf_limits var_0)) var_0_lst ⟹
		 (ret_val = var_0) ⟹
		 (wf_store (fst ret_val)) ⟹
		 alloctables_is_wf v_store var_0_lst ret_val"

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:67.6-67.15 *)
inductive fun_allocmem :: "store ⇒ memtype ⇒ (store * memaddr) ⇒ bool" where
	  fun_allocmem_case_0 :
		"(mi = ⦇ meminst_TYPE = (mk_limits i j_opt), BYTES = (repeat ((proj_uN_0 i) * (64 * (Ki ))) (mk_byte 0)) ⦈) ⟹
		 (wf_meminst ⦇ meminst_TYPE = (mk_limits i j_opt), BYTES = (repeat ((proj_uN_0 i) * (64 * (Ki ))) (mk_byte 0)) ⦈) ⟹
		 fun_allocmem s (mk_limits i j_opt) ((s ⦇ store_MEMS := ((store_MEMS s) @ [mi])  ⦈), (length (store_MEMS s)))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:67.6-67.15 *)
lemma allocmem_is_wf :
	"(fun_allocmem v_store v_memtype var_0) ⟹
	 (wf_store v_store) ⟹
	 (wf_limits v_memtype) ⟹
	 (ret_val = var_0) ⟹
	 (wf_store (fst ret_val))"
sorry

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:71.1-71.52 *)
inductive fun_allocmems :: "store ⇒ (memtype list) ⇒ (store * (memaddr list)) ⇒ bool" where
	  fun_allocmems_case_0 :
		"fun_allocmems s [] (s, [])"
	| fun_allocmems_case_1 :
		"(fun_allocmems s_1 memtype'_lst var_1) ⟹
		 (fun_allocmem s v_memtype var_0) ⟹
		 ((s_1, ma) = var_0) ⟹
		 ((s_2, ma'_lst) = var_1) ⟹
		 fun_allocmems s ([v_memtype] @ memtype'_lst) (s_2, ([ma] @ ma'_lst))"

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:71.1-71.52 *)
inductive allocmems_is_wf :: "store ⇒ (memtype list) ⇒ (store * (memaddr list)) ⇒ bool" where
	  allocmems_is_wf_0 :
		"(fun_allocmems v_store var_0_lst var_0) ⟹
		 (wf_store v_store) ⟹
		 list_all (λ (var_0 :: memtype). (wf_limits var_0)) var_0_lst ⟹
		 (ret_val = var_0) ⟹
		 (wf_store (fst ret_val)) ⟹
		 allocmems_is_wf v_store var_0_lst ret_val"

(* Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:80.1-80.83 *)
function (sequential) instexport :: "(funcaddr list) ⇒ (globaladdr list) ⇒ (tableaddr list) ⇒ (memaddr list) ⇒ export ⇒ exportinst" where
		  "instexport fa_lst ga_lst ta_lst ma_lst (EXPORT v_name (externidx_FUNC x)) = ⦇ NAME = v_name, ADDR = (externaddr_FUNC (fa_lst ! (proj_uN_0 x))) ⦈"
		| "instexport fa_lst ga_lst ta_lst ma_lst (EXPORT v_name (externidx_GLOBAL x)) = ⦇ NAME = v_name, ADDR = (externaddr_GLOBAL (ga_lst ! (proj_uN_0 x))) ⦈"
		| "instexport fa_lst ga_lst ta_lst ma_lst (EXPORT v_name (externidx_TABLE x)) = ⦇ NAME = v_name, ADDR = (externaddr_TABLE (ta_lst ! (proj_uN_0 x))) ⦈"
		| "instexport fa_lst ga_lst ta_lst ma_lst (EXPORT v_name (externidx_MEM x)) = ⦇ NAME = v_name, ADDR = (externaddr_MEM (ma_lst ! (proj_uN_0 x))) ⦈"
	by pat_completeness auto

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:80.6-80.17 *)
lemma instexport_is_wf :
	"(wf_export v_export) ⟹
	 (ret_val = (instexport var_0_lst var_1_lst var_2_lst var_3_lst v_export)) ⟹
	 (wf_exportinst ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:87.6-87.18 *)
inductive fun_allocmodule :: "store ⇒ module ⇒ (externaddr list) ⇒ (val list) ⇒ (store * moduleinst) ⇒ bool" where
	  fun_allocmodule_case_0 :
		"(fun_allocmems s_3 memtype_lst var_7) ⟹
		 (fun_alloctables s_2 tabletype_lst var_6) ⟹
		 (fun_allocglobals s_1 globaltype_lst val_lst var_5) ⟹
		 (fun_allocfuncs s v_moduleinst func_lst var_4) ⟹
		 (fun_mems externaddr_lst var_3) ⟹
		 (fun_tables externaddr_lst var_2) ⟹
		 (fun_globals externaddr_lst var_1) ⟹
		 (fun_funcs externaddr_lst var_0) ⟹
		 (v_module = (MODULE (map (λ (ft_1 :: functype). (res_TYPE ft_1)) ft_lst) import_lst func_lst (list_zipWith (λ (expr_1_1 :: expr) (globaltype_195 :: globaltype). (global_GLOBAL globaltype_195 expr_1_1)) expr_1_lst globaltype_lst) (map (λ (tabletype_241 :: tabletype). (table_TABLE tabletype_241)) tabletype_lst) (map (λ (memtype_293 :: memtype). (MEMORY memtype_293)) memtype_lst) elem_lst data_lst start_opt export_lst)) ⟹
		 (fa_ex_lst = var_0) ⟹
		 (ga_ex_lst = var_1) ⟹
		 (ta_ex_lst = var_2) ⟹
		 (ma_ex_lst = var_3) ⟹
		 (fa_lst = (mkseq (λ i_func_1. ((length (store_FUNCS s)) + i_func_1)) n_func)) ⟹
		 (ga_lst = (mkseq (λ i_global_1. ((length (store_GLOBALS s)) + i_global_1)) n_global)) ⟹
		 (ta_lst = (mkseq (λ i_table_1. ((length (store_TABLES s)) + i_table_1)) n_table)) ⟹
		 (ma_lst = (mkseq (λ i_mem_1. ((length (store_MEMS s)) + i_mem_1)) n_mem)) ⟹
		 (xi_lst = (map (λ (export_2 :: export). (instexport (fa_ex_lst @ fa_lst) (ga_ex_lst @ ga_lst) (ta_ex_lst @ ta_lst) (ma_ex_lst @ ma_lst) export_2)) export_lst)) ⟹
		 (v_moduleinst = ⦇ TYPES = ft_lst, FUNCS = (fa_ex_lst @ fa_lst), GLOBALS = (ga_ex_lst @ ga_lst), TABLES = (ta_ex_lst @ ta_lst), MEMS = (ma_ex_lst @ ma_lst), EXPORTS = xi_lst ⦈) ⟹
		 ((s_1, fa_lst) = var_4) ⟹
		 ((s_2, ga_lst) = var_5) ⟹
		 ((s_3, ta_lst) = var_6) ⟹
		 ((s_4, ma_lst) = var_7) ⟹
		 (wf_store s_1) ⟹
		 (wf_store s_2) ⟹
		 (wf_store s_3) ⟹
		 (wf_module (MODULE (map (λ (ft_3 :: functype). (res_TYPE ft_3)) ft_lst) import_lst func_lst (list_zipWith (λ (expr_1_2 :: expr) (globaltype_198 :: globaltype). (global_GLOBAL globaltype_198 expr_1_2)) expr_1_lst globaltype_lst) (map (λ (tabletype_244 :: tabletype). (table_TABLE tabletype_244)) tabletype_lst) (map (λ (memtype_296 :: memtype). (MEMORY memtype_296)) memtype_lst) elem_lst data_lst start_opt export_lst)) ⟹
		 (wf_moduleinst ⦇ TYPES = ft_lst, FUNCS = (fa_ex_lst @ fa_lst), GLOBALS = (ga_ex_lst @ ga_lst), TABLES = (ta_ex_lst @ ta_lst), MEMS = (ma_ex_lst @ ma_lst), EXPORTS = xi_lst ⦈) ⟹
		 fun_allocmodule s v_module externaddr_lst val_lst (s_4, v_moduleinst)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:87.6-87.18 *)
lemma allocmodule_is_wf :
	"(fun_allocmodule v_store v_module var_0_lst var_1_lst var_0) ⟹
	 (wf_store v_store) ⟹
	 (wf_module v_module) ⟹
	 list_all (λ (var_1 :: val). (wf_val var_1)) var_1_lst ⟹
	 (ret_val = var_0) ⟹
	 (wf_store (fst ret_val)) ⟹
	 (wf_moduleinst (snd ret_val))"
sorry

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:128.1-128.61 *)
inductive fun_initelem :: "store ⇒ moduleinst ⇒ (u32 list) ⇒ ((funcaddr list) list) ⇒ store ⇒ bool" where
	  fun_initelem_case_0 :
		"fun_initelem s v_moduleinst [] [] s"
	| fun_initelem_case_1 :
		"(fun_initelem s_1 v_moduleinst i'_lst a'_lst_lst var_0) ⟹
		 (0 < (length (TABLES v_moduleinst))) ⟹
		 (s_1 = (s ⦇ store_TABLES := (list_update_func (store_TABLES s) ((TABLES v_moduleinst) ! 0) (λ (var_1 :: tableinst). (var_1 ⦇ REFS := (list_slice_update (REFS var_1) (proj_uN_0 i) (length a_lst) (map (λ (a_7 :: addr). (Some a_7)) a_lst))  ⦈)))  ⦈)) ⟹
		 (s_2 = var_0) ⟹
		 (wf_store s_1) ⟹
		 fun_initelem s v_moduleinst ([i] @ i'_lst) ([a_lst] @ a'_lst_lst) s_2"

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:128.1-128.61 *)
inductive initelem_is_wf :: "store ⇒ moduleinst ⇒ (u32 list) ⇒ ((funcaddr list) list) ⇒ store ⇒ bool" where
	  initelem_is_wf_0 :
		"(fun_initelem v_store v_moduleinst var_0_lst var_1_lst_lst var_0) ⟹
		 (wf_store v_store) ⟹
		 (wf_moduleinst v_moduleinst) ⟹
		 list_all (λ (var_0 :: u32). (wf_uN 32 var_0)) var_0_lst ⟹
		 (ret_val = var_0) ⟹
		 (wf_store ret_val) ⟹
		 initelem_is_wf v_store v_moduleinst var_0_lst var_1_lst_lst ret_val"

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:134.1-134.57 *)
inductive fun_initdata :: "store ⇒ moduleinst ⇒ (u32 list) ⇒ ((byte list) list) ⇒ store ⇒ bool" where
	  fun_initdata_case_0 :
		"fun_initdata s v_moduleinst [] [] s"
	| fun_initdata_case_1 :
		"(fun_initdata s_1 v_moduleinst i'_lst b'_lst_lst var_0) ⟹
		 (0 < (length (MEMS v_moduleinst))) ⟹
		 (s_1 = (s ⦇ store_MEMS := (list_update_func (store_MEMS s) ((MEMS v_moduleinst) ! 0) (λ (var_1 :: meminst). (var_1 ⦇ BYTES := (list_slice_update (BYTES var_1) (proj_uN_0 i) (length b_lst) b_lst)  ⦈)))  ⦈)) ⟹
		 (s_2 = var_0) ⟹
		 fun_initdata s v_moduleinst ([i] @ i'_lst) ([b_lst] @ b'_lst_lst) s_2"

(* Mutual Recursion at: ../specification/wasm-1.0/9-module.spectec:134.1-134.57 *)
inductive initdata_is_wf :: "store ⇒ moduleinst ⇒ (u32 list) ⇒ ((byte list) list) ⇒ store ⇒ bool" where
	  initdata_is_wf_0 :
		"(fun_initdata v_store v_moduleinst var_0_lst var_1_lst_lst var_0) ⟹
		 (wf_store v_store) ⟹
		 (wf_moduleinst v_moduleinst) ⟹
		 list_all (λ (var_0 :: u32). (wf_uN 32 var_0)) var_0_lst ⟹
		 list_all (λ (var_1_lst :: (byte list)). list_all (λ (var_1 :: byte). (wf_byte var_1)) var_1_lst) var_1_lst_lst ⟹
		 (ret_val = var_0) ⟹
		 (wf_store ret_val) ⟹
		 initdata_is_wf v_store v_moduleinst var_0_lst var_1_lst_lst ret_val"

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:140.6-140.18 *)
inductive fun_instantiate :: "store ⇒ module ⇒ (externaddr list) ⇒ config ⇒ bool" where
	  fun_instantiate_case_0 :
		"(fun_globals externaddr_lst var_6) ⟹
		 (fun_funcs externaddr_lst var_5) ⟹
		 list_all (λ (i_D_2 :: val_underscore). ((proj_val__0 i_D_2) ≠ None)) i_D_lst ⟹
		 (fun_initdata s_2 v_moduleinst (map (λ (i_D_2 :: val_underscore). (the ((proj_val__0 i_D_2)))) i_D_lst) b_lst_lst var_4) ⟹
		 list_all (λ (i_E_2 :: val_underscore). ((proj_val__0 i_E_2) ≠ None)) i_E_lst ⟹
		 list_all (λ (x_lst_2 :: (idx list)). list_all (λ (x_2 :: idx). ((proj_uN_0 x_2) < (length (FUNCS v_moduleinst)))) x_lst_2) x_lst_lst ⟹
		 (fun_initelem s_1 v_moduleinst (map (λ (i_E_2 :: val_underscore). (the ((proj_val__0 i_E_2)))) i_E_lst) (map (λ (x_lst_2 :: (idx list)). (map (λ (x_2 :: idx). ((FUNCS v_moduleinst) ! (proj_uN_0 x_2))) x_lst_2)) x_lst_lst) var_3) ⟹
		 (fun_allocmodule s v_module externaddr_lst val_lst var_2) ⟹
		 (fun_globals externaddr_lst var_1) ⟹
		 (fun_funcs externaddr_lst var_0) ⟹
		 ((MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst) = v_module) ⟹
		 (type_lst = (map (λ (functype_49 :: functype). (res_TYPE functype_49)) functype_lst)) ⟹
		 (global_lst = (list_zipWith (λ (expr_G_1 :: expr) (globaltype_200 :: globaltype). (global_GLOBAL globaltype_200 expr_G_1)) expr_G_lst globaltype_lst)) ⟹
		 (elem_lst = (list_zipWith (λ (expr_E_1 :: expr) (x_lst_1 :: (idx list)). (ELEM expr_E_1 x_lst_1)) expr_E_lst x_lst_lst)) ⟹
		 (data_lst = (list_zipWith (λ (b_lst_1 :: (byte list)) (expr_D_1 :: expr). (DATA expr_D_1 b_lst_1)) b_lst_lst expr_D_lst)) ⟹
		 (start_opt = (map_option (λ (x'_1 :: idx). (START x'_1)) x'_opt)) ⟹
		 (n_F = (length func_lst)) ⟹
		 (moduleinst_init = ⦇ TYPES = functype_lst, FUNCS = (var_0 @ (mkseq (λ i_F_1. ((length (store_FUNCS s)) + i_F_1)) n_F)), GLOBALS = var_1, TABLES = [], MEMS = [], EXPORTS = [] ⦈) ⟹
		 (f_init = ⦇ LOCALS = [], frame_MODULE = moduleinst_init ⦈) ⟹
		 (z = (mk_state s f_init)) ⟹
		 ((length expr_G_lst) = (length val_lst)) ⟹
		 list_all2 (λ (expr_G_2 :: expr) (val_3 :: val). (Eval_expr z expr_G_2 z [val_3])) expr_G_lst val_lst ⟹
		 ((length expr_E_lst) = (length i_E_lst)) ⟹
		 list_all2 (λ (expr_E_2 :: expr) (i_E_1 :: val_underscore). (Eval_expr z expr_E_2 z [(val_CONST I32 i_E_1)])) expr_E_lst i_E_lst ⟹
		 ((length expr_D_lst) = (length i_D_lst)) ⟹
		 list_all2 (λ (expr_D_2 :: expr) (i_D_1 :: val_underscore). (Eval_expr z expr_D_2 z [(val_CONST I32 i_D_1)])) expr_D_lst i_D_lst ⟹
		 ((s_1, v_moduleinst) = var_2) ⟹
		 (s_2 = var_3) ⟹
		 (s_3 = var_4) ⟹
		 (f = ⦇ LOCALS = [], frame_MODULE = v_moduleinst ⦈) ⟹
		 list_all (λ (val_5 :: val). (wf_val val_5)) val_lst ⟹
		 (wf_module (MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)) ⟹
		 ((length expr_G_lst) = (length globaltype_lst)) ⟹
		 list_all2 (λ (expr_G_3 :: expr) (globaltype_202 :: globaltype). (wf_global (global_GLOBAL globaltype_202 expr_G_3))) expr_G_lst globaltype_lst ⟹
		 ((length expr_E_lst) = (length x_lst_lst)) ⟹
		 list_all2 (λ (expr_E_3 :: expr) (x_lst_3 :: (idx list)). (wf_elem (ELEM expr_E_3 x_lst_3))) expr_E_lst x_lst_lst ⟹
		 ((length b_lst_lst) = (length expr_D_lst)) ⟹
		 list_all2 (λ (b_lst_3 :: (byte list)) (expr_D_3 :: expr). (wf_data (DATA expr_D_3 b_lst_3))) b_lst_lst expr_D_lst ⟹
		 list_all (λ (x'_2 :: idx). (wf_start (START x'_2))) (option_to_list x'_opt) ⟹
		 (wf_moduleinst ⦇ TYPES = functype_lst, FUNCS = (var_5 @ (mkseq (λ i_F_2. ((length (store_FUNCS s)) + i_F_2)) n_F)), GLOBALS = var_6, TABLES = [], MEMS = [], EXPORTS = [] ⦈) ⟹
		 (wf_frame ⦇ LOCALS = [], frame_MODULE = moduleinst_init ⦈) ⟹
		 (wf_state (mk_state s f_init)) ⟹
		 list_all (λ (i_E_3 :: val_underscore). (wf_val (val_CONST I32 i_E_3))) i_E_lst ⟹
		 list_all (λ (i_D_3 :: val_underscore). (wf_val (val_CONST I32 i_D_3))) i_D_lst ⟹
		 (wf_frame ⦇ LOCALS = [], frame_MODULE = v_moduleinst ⦈) ⟹
		 fun_instantiate s v_module externaddr_lst (mk_config (mk_state s_3 f) (option_to_list (map_option (λ (x' :: idx). (admininstr_CALL x')) x'_opt)))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:140.6-140.18 *)
lemma instantiate_is_wf :
	"(fun_instantiate v_store v_module var_0_lst var_0) ⟹
	 (wf_store v_store) ⟹
	 (wf_module v_module) ⟹
	 (ret_val = var_0) ⟹
	 (wf_config ret_val)"
sorry

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:169.6-169.13 *)
inductive fun_invoke :: "store ⇒ funcaddr ⇒ (val list) ⇒ config ⇒ bool" where
	  fun_invoke_case_0 :
		"(f = ⦇ LOCALS = [], frame_MODULE = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], EXPORTS = [] ⦈ ⦈) ⟹
		 (fa < (length (fun_funcinst (mk_state s f)))) ⟹
		 ((funcinst_TYPE ((fun_funcinst (mk_state s f)) ! fa)) = (mk_functype t_1_lst t_2_lst)) ⟹
		 (wf_frame ⦇ LOCALS = [], frame_MODULE = ⦇ TYPES = [], FUNCS = [], GLOBALS = [], TABLES = [], MEMS = [], EXPORTS = [] ⦈ ⦈) ⟹
		 (wf_state (mk_state s f)) ⟹
		 (v_n = (length val_lst)) ⟹
		 fun_invoke s fa val_lst (mk_config (mk_state s f) ((map (λ (v_val :: val). (admininstr_val v_val)) val_lst) @ [(CALL_ADDR fa)]))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:169.6-169.13 *)
lemma invoke_is_wf :
	"(fun_invoke v_store v_funcaddr var_0_lst var_0) ⟹
	 (wf_store v_store) ⟹
	 list_all (λ (var_0 :: val). (wf_val var_0)) var_0_lst ⟹
	 (ret_val = var_0) ⟹
	 (wf_config ret_val)"
sorry

(* Type Alias Definition at: ../specification/wasm-1.0/A-binary.spectec:483.1-483.43 *)
type_synonym startopt = "(start list)"

(* Type Alias Definition at: ../specification/wasm-1.0/A-binary.spectec:500.1-500.29 *)
type_synonym code = "((local list) * expr)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:3.1-3.61 *)
inductive Context_ok :: "res_context ⇒ bool" where
	  mk_Context_ok :
		"(C = ⦇ context_TYPES = ft_lst, context_FUNCS = ft_2_lst, context_GLOBALS = gt_lst, context_TABLES = tt_lst, context_MEMS = mt_lst, context_LOCALS = lct_lst, LABELS = (map (λ (rt :: valtype). (Some rt)) rt_lst), context_RETURN = (Some rt'_opt) ⦈) ⟹
		 list_all (λ (ft :: functype). (Functype_ok ft)) ft_lst ⟹
		 list_all (λ (gt :: globaltype). (Globaltype_ok gt)) gt_lst ⟹
		 list_all (λ (mt :: memtype). (Memtype_ok mt)) mt_lst ⟹
		 list_all (λ (tt :: tabletype). (Tabletype_ok tt)) tt_lst ⟹
		 list_all (λ (ft_2 :: functype). (Functype_ok ft_2)) ft_2_lst ⟹
		 (wf_context C) ⟹
		 (wf_context ⦇ context_TYPES = ft_lst, context_FUNCS = ft_2_lst, context_GLOBALS = gt_lst, context_TABLES = tt_lst, context_MEMS = mt_lst, context_LOCALS = lct_lst, LABELS = (map (λ (rt :: valtype). (Some rt)) rt_lst), context_RETURN = (Some rt'_opt) ⦈) ⟹
		 Context_ok C"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:25.1-25.34 *)
inductive Val_ok :: "val ⇒ valtype ⇒ bool" where
	  mk_Val_ok :
		"(wf_val (val_CONST t c_t)) ⟹
		 Val_ok (val_CONST t c_t) t"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:33.1-33.41 *)
inductive Result_ok :: "result ⇒ (valtype list) ⇒ bool" where
	  Result_ok__result :
		"((length t_lst) = (length v_lst)) ⟹
		 list_all2 (λ (t :: valtype) (v :: val). (Val_ok v t)) t_lst v_lst ⟹
		 (wf_result (underscore_VALS v_lst)) ⟹
		 Result_ok (underscore_VALS v_lst) t_lst"
	| trap :
		"(wf_result TRAP) ⟹
		 Result_ok TRAP t_lst"

(* Type Alias Definition at: ../specification/wasm-1.0/B-soundness.spectec:44.1-44.31 *)
type_synonym adminexpr = "(admininstr list)"

(* Mutual Recursion at: ../specification/wasm-1.0/B-soundness.spectec:95.1-95.84 *)
inductive Externaddr_ok :: "store ⇒ externaddr ⇒ externtype ⇒ bool" where
	  Externaddr_ok__global :
		"(a < (length (store_GLOBALS s))) ⟹
		 (((store_GLOBALS s) ! a) = v_globalinst) ⟹
		 (wf_store s) ⟹
		 (wf_externtype (GLOBAL (globalinst_TYPE v_globalinst))) ⟹
		 Externaddr_ok s (externaddr_GLOBAL a) (GLOBAL (globalinst_TYPE v_globalinst))"
	| Externaddr_ok__mem :
		"(a < (length (store_MEMS s))) ⟹
		 (((store_MEMS s) ! a) = v_meminst) ⟹
		 (wf_store s) ⟹
		 (wf_externtype (MEM (meminst_TYPE v_meminst))) ⟹
		 Externaddr_ok s (externaddr_MEM a) (MEM (meminst_TYPE v_meminst))"
	| Externaddr_ok__table :
		"(a < (length (store_TABLES s))) ⟹
		 (((store_TABLES s) ! a) = v_tableinst) ⟹
		 (wf_store s) ⟹
		 (wf_externtype (TABLE (tableinst_TYPE v_tableinst))) ⟹
		 Externaddr_ok s (externaddr_TABLE a) (TABLE (tableinst_TYPE v_tableinst))"
	| Externaddr_ok__func :
		"(a < (length (store_FUNCS s))) ⟹
		 (((store_FUNCS s) ! a) = v_funcinst) ⟹
		 (wf_store s) ⟹
		 (wf_externtype (FUNC (funcinst_TYPE v_funcinst))) ⟹
		 Externaddr_ok s (externaddr_FUNC a) (FUNC (funcinst_TYPE v_funcinst))"
	| sub :
		"(Externaddr_ok s v_externaddr xt') ⟹
		 (Externtype_sub xt' xt) ⟹
		 (wf_store s) ⟹
		 (wf_externtype xt) ⟹
		 (wf_externtype xt') ⟹
		 Externaddr_ok s v_externaddr xt"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:124.1-124.49 *)
inductive Exportinst_ok :: "store ⇒ exportinst ⇒ bool" where
	  mk_Exportinst_ok :
		"(Externaddr_ok s xa xt) ⟹
		 (wf_store s) ⟹
		 (wf_externtype xt) ⟹
		 (wf_exportinst ⦇ NAME = nm, ADDR = xa ⦈) ⟹
		 Exportinst_ok s ⦇ NAME = nm, ADDR = xa ⦈"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:155.1-155.54 *)
inductive Moduleinst_ok :: "store ⇒ moduleinst ⇒ res_context ⇒ bool" where
	  mk_Moduleinst_ok :
		"list_all (λ (v_functype :: functype). (Functype_ok v_functype)) functype_lst ⟹
		 ((length globaladdr_lst) = (length globaltype_lst)) ⟹
		 list_all2 (λ (v_globaladdr :: globaladdr) (v_globaltype :: globaltype). (Externaddr_ok s (externaddr_GLOBAL v_globaladdr) (GLOBAL v_globaltype))) globaladdr_lst globaltype_lst ⟹
		 ((length funcaddr_lst) = (length functype_F_lst)) ⟹
		 list_all2 (λ (v_funcaddr :: funcaddr) (functype_F :: functype). (Externaddr_ok s (externaddr_FUNC v_funcaddr) (FUNC functype_F))) funcaddr_lst functype_F_lst ⟹
		 ((length memaddr_lst) = (length memtype_lst)) ⟹
		 list_all2 (λ (v_memaddr :: memaddr) (v_memtype :: memtype). (Externaddr_ok s (externaddr_MEM v_memaddr) (MEM v_memtype))) memaddr_lst memtype_lst ⟹
		 ((length tableaddr_lst) = (length tabletype_lst)) ⟹
		 list_all2 (λ (v_tableaddr :: tableaddr) (v_tabletype :: tabletype). (Externaddr_ok s (externaddr_TABLE v_tableaddr) (TABLE v_tabletype))) tableaddr_lst tabletype_lst ⟹
		 list_all (λ (v_exportinst :: exportinst). (Exportinst_ok s v_exportinst)) exportinst_lst ⟹
		 (disjoint_underscore  (map (λ (v_exportinst :: exportinst). (NAME v_exportinst)) exportinst_lst)) ⟹
		 ((length ((map (λ (v_globaladdr :: globaladdr). (externaddr_GLOBAL v_globaladdr)) globaladdr_lst) @ ((map (λ (v_memaddr :: memaddr). (externaddr_MEM v_memaddr)) memaddr_lst) @ ((map (λ (v_tableaddr :: tableaddr). (externaddr_TABLE v_tableaddr)) tableaddr_lst) @ (map (λ (v_funcaddr :: funcaddr). (externaddr_FUNC v_funcaddr)) funcaddr_lst))))) > 0) ⟹
		 list_all (λ (v_exportinst :: exportinst). ((ADDR v_exportinst) ∈ set ((map (λ (v_globaladdr :: globaladdr). (externaddr_GLOBAL v_globaladdr)) globaladdr_lst) @ ((map (λ (v_memaddr :: memaddr). (externaddr_MEM v_memaddr)) memaddr_lst) @ ((map (λ (v_tableaddr :: tableaddr). (externaddr_TABLE v_tableaddr)) tableaddr_lst) @ (map (λ (v_funcaddr :: funcaddr). (externaddr_FUNC v_funcaddr)) funcaddr_lst)))))) exportinst_lst ⟹
		 (wf_store s) ⟹
		 (wf_moduleinst ⦇ TYPES = functype_lst, FUNCS = funcaddr_lst, GLOBALS = globaladdr_lst, TABLES = tableaddr_lst, MEMS = memaddr_lst, EXPORTS = exportinst_lst ⦈) ⟹
		 (wf_context ⦇ context_TYPES = functype_lst, context_FUNCS = functype_F_lst, context_GLOBALS = globaltype_lst, context_TABLES = tabletype_lst, context_MEMS = memtype_lst, context_LOCALS = [], LABELS = [], context_RETURN = None ⦈) ⟹
		 list_all (λ (v_globaltype :: globaltype). (wf_externtype (GLOBAL v_globaltype))) globaltype_lst ⟹
		 list_all (λ (functype_F :: functype). (wf_externtype (FUNC functype_F))) functype_F_lst ⟹
		 list_all (λ (v_memtype :: memtype). (wf_externtype (MEM v_memtype))) memtype_lst ⟹
		 list_all (λ (v_tabletype :: tabletype). (wf_externtype (TABLE v_tabletype))) tabletype_lst ⟹
		 Moduleinst_ok s ⦇ TYPES = functype_lst, FUNCS = funcaddr_lst, GLOBALS = globaladdr_lst, TABLES = tableaddr_lst, MEMS = memaddr_lst, EXPORTS = exportinst_lst ⦈ ⦇ context_TYPES = functype_lst, context_FUNCS = functype_F_lst, context_GLOBALS = globaltype_lst, context_TABLES = tabletype_lst, context_MEMS = memtype_lst, context_LOCALS = [], LABELS = [], context_RETURN = None ⦈"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:228.1-228.44 *)
inductive Frame_ok :: "store ⇒ frame ⇒ res_context ⇒ bool" where
	  mk_Frame_ok :
		"(Moduleinst_ok s v_moduleinst C) ⟹
		 ((length t_lst) = (length val_lst)) ⟹
		 list_all2 (λ (t :: valtype) (v_val :: val). (Val_ok v_val t)) t_lst val_lst ⟹
		 (wf_store s) ⟹
		 (wf_context C) ⟹
		 (wf_frame ⦇ LOCALS = val_lst, frame_MODULE = v_moduleinst ⦈) ⟹
		 (wf_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_LOCALS = t_lst, LABELS = [], context_RETURN = None ⦈) ⟹
		 Frame_ok s ⦇ LOCALS = val_lst, frame_MODULE = v_moduleinst ⦈ (append_res_context C ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_LOCALS = t_lst, LABELS = [], context_RETURN = None ⦈)"

(* Mutual Recursion at: ../specification/wasm-1.0/B-soundness.spectec:46.1-51.36 *)
inductive Instr_ok2 :: "store ⇒ res_context ⇒ admininstr ⇒ functype ⇒ bool"
and Instrs_ok2 :: "store ⇒ res_context ⇒ (admininstr list) ⇒ functype ⇒ bool"
and Expr_ok2 :: "store ⇒ res_context ⇒ adminexpr ⇒ resulttype ⇒ bool" where
	  plain :
		"(Instr_ok C v_instr (mk_functype t_1_lst t_2_lst)) ⟹
		 (wf_store s) ⟹
		 (wf_context C) ⟹
		 (wf_instr v_instr) ⟹
		 Instr_ok2 s C (admininstr_instr v_instr) (mk_functype t_1_lst t_2_lst)"
	| label :
		"((length (option_to_list t'_opt)) = v_n) ⟹
		 (Instrs_ok2 s C (map (λ (instr' :: instr). (admininstr_instr instr')) instr'_lst) (mk_functype (option_to_list t'_opt) (option_to_list t_opt))) ⟹
		 (Instrs_ok2 s (append_res_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_LOCALS = [], LABELS = [t'_opt], context_RETURN = None ⦈ C) admininstr_lst (mk_functype [] (option_to_list t_opt))) ⟹
		 (wf_store s) ⟹
		 (wf_context C) ⟹
		 (wf_admininstr (LABEL_underscore v_n instr'_lst admininstr_lst)) ⟹
		 (wf_context ⦇ context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_LOCALS = [], LABELS = [t'_opt], context_RETURN = None ⦈) ⟹
		 Instr_ok2 s C (LABEL_underscore v_n instr'_lst admininstr_lst) (mk_functype [] (option_to_list t_opt))"
	| Instr_ok2__frame :
		"((length (option_to_list t_opt)) = v_n) ⟹
		 (Frame_ok s f C') ⟹
		 (Expr_ok2 s C' admininstr_lst t_opt) ⟹
		 (wf_store s) ⟹
		 (wf_context C) ⟹
		 (wf_context C') ⟹
		 (wf_admininstr (FRAME_underscore v_n f admininstr_lst)) ⟹
		 Instr_ok2 s C (FRAME_underscore v_n f admininstr_lst) (mk_functype [] (option_to_list t_opt))"
	| Instr_ok2__call_addr :
		"(Externaddr_ok s (externaddr_FUNC v_funcaddr) (FUNC (mk_functype t_1_lst t_2_lst))) ⟹
		 (wf_store s) ⟹
		 (wf_context C) ⟹
		 (wf_admininstr (CALL_ADDR v_funcaddr)) ⟹
		 (wf_externtype (FUNC (mk_functype t_1_lst t_2_lst))) ⟹
		 Instr_ok2 s C (CALL_ADDR v_funcaddr) (mk_functype t_1_lst t_2_lst)"
	| Instr_ok2__trap :
		"(wf_store s) ⟹
		 (wf_context C) ⟹
		 (wf_admininstr admininstr_TRAP) ⟹
		 Instr_ok2 s C admininstr_TRAP (mk_functype t_1_lst t_2_lst)"
	| Instrs_ok2__empty :
		"(wf_store s) ⟹
		 (wf_context C) ⟹
		 Instrs_ok2 s C [] (mk_functype [] [])"
	| Instrs_ok2__seq :
		"(Instr_ok2 s C admininstr_1 (mk_functype t_1_lst t_2_lst)) ⟹
		 (Instrs_ok2 s C admininstr_2_lst (mk_functype t_2_lst t_3_lst)) ⟹
		 (wf_store s) ⟹
		 (wf_context C) ⟹
		 (wf_admininstr admininstr_1) ⟹
		 list_all (λ (admininstr_2 :: admininstr). (wf_admininstr admininstr_2)) admininstr_2_lst ⟹
		 Instrs_ok2 s C ([admininstr_1] @ admininstr_2_lst) (mk_functype t_1_lst t_3_lst)"
	| Instrs_ok2__frame :
		"(Instrs_ok2 s C admininstr_lst (mk_functype t_1_lst t_2_lst)) ⟹
		 (wf_store s) ⟹
		 (wf_context C) ⟹
		 list_all (λ (v_admininstr :: admininstr). (wf_admininstr v_admininstr)) admininstr_lst ⟹
		 Instrs_ok2 s C admininstr_lst (mk_functype (t_lst @ t_1_lst) (t_lst @ t_2_lst))"
	| mk_Expr_ok2 :
		"(Instrs_ok2 s C admininstr_lst (mk_functype [] (option_to_list t_opt))) ⟹
		 (wf_store s) ⟹
		 (wf_context C) ⟹
		 list_all (λ (v_admininstr :: admininstr). (wf_admininstr v_admininstr)) admininstr_lst ⟹
		 Expr_ok2 s C admininstr_lst t_opt"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:120.1-120.57 *)
inductive Globalinst_ok :: "store ⇒ globalinst ⇒ globaltype ⇒ bool" where
	  mk_Globalinst_ok :
		"(Globaltype_ok (mk_globaltype v_mut t)) ⟹
		 (Val_ok v_val t) ⟹
		 (wf_store s) ⟹
		 (wf_globalinst ⦇ globalinst_TYPE = (mk_globaltype v_mut t), VALUE = v_val ⦈) ⟹
		 Globalinst_ok s ⦇ globalinst_TYPE = (mk_globaltype v_mut t), VALUE = v_val ⦈ (mk_globaltype v_mut t)"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:121.1-121.48 *)
inductive Meminst_ok :: "store ⇒ meminst ⇒ memtype ⇒ bool" where
	  mk_Meminst_ok :
		"(Memtype_ok (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt))) ⟹
		 ((length b_lst) = (v_n * (64 * (Ki )))) ⟹
		 (wf_store s) ⟹
		 (wf_meminst ⦇ meminst_TYPE = (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt)), BYTES = b_lst ⦈) ⟹
		 (wf_limits (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt))) ⟹
		 Meminst_ok s ⦇ meminst_TYPE = (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt)), BYTES = b_lst ⦈ (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:122.1-122.54 *)
inductive Tableinst_ok :: "store ⇒ tableinst ⇒ tabletype ⇒ bool" where
	  mk_Tableinst_ok :
		"(Tabletype_ok (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt))) ⟹
		 ((length fa_opt_lst) = (length ft_opt_lst)) ⟹
		 list_all2 (λ (fa_opt :: (funcaddr option)) (ft_opt :: (functype option)). ((fa_opt = None) ⟷ (ft_opt = None))) fa_opt_lst ft_opt_lst ⟹
		 list_all2 (λ (fa_opt :: (funcaddr option)) (ft_opt :: (functype option)). list_all2 (λ (fa :: funcaddr) (ft :: functype). (Externaddr_ok s (externaddr_FUNC fa) (FUNC ft))) (option_to_list fa_opt) (option_to_list ft_opt)) fa_opt_lst ft_opt_lst ⟹
		 ((length fa_opt_lst) = v_n) ⟹
		 (wf_store s) ⟹
		 (wf_tableinst ⦇ tableinst_TYPE = (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt)), REFS = fa_opt_lst ⦈) ⟹
		 (wf_limits (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt))) ⟹
		 list_all (λ (ft_opt :: (functype option)). list_all (λ (ft :: functype). (wf_externtype (FUNC ft))) (option_to_list ft_opt)) ft_opt_lst ⟹
		 Tableinst_ok s ⦇ tableinst_TYPE = (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt)), REFS = fa_opt_lst ⦈ (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt))"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:123.1-123.51 *)
inductive Funcinst_ok :: "store ⇒ funcinst ⇒ functype ⇒ bool" where
	  mk_Funcinst_ok :
		"(Functype_ok ft) ⟹
		 (Moduleinst_ok s v_moduleinst C) ⟹
		 (Func_ok C v_func ft) ⟹
		 (wf_store s) ⟹
		 (wf_context C) ⟹
		 (wf_funcinst ⦇ funcinst_TYPE = ft, funcinst_MODULE = v_moduleinst, CODE = v_func ⦈) ⟹
		 Funcinst_ok s ⦇ funcinst_TYPE = ft, funcinst_MODULE = v_moduleinst, CODE = v_func ⦈ ft"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:183.1-183.33 *)
inductive Store_ok :: "store ⇒ bool" where
	  mk_Store_ok :
		"((length globalinst_lst) = (length globaltype_lst)) ⟹
		 list_all2 (λ (v_globalinst :: globalinst) (v_globaltype :: globaltype). (Globalinst_ok s v_globalinst v_globaltype)) globalinst_lst globaltype_lst ⟹
		 ((length meminst_lst) = (length memtype_lst)) ⟹
		 list_all2 (λ (v_meminst :: meminst) (v_memtype :: memtype). (Meminst_ok s v_meminst v_memtype)) meminst_lst memtype_lst ⟹
		 ((length tableinst_lst) = (length tabletype_lst)) ⟹
		 list_all2 (λ (v_tableinst :: tableinst) (v_tabletype :: tabletype). (Tableinst_ok s v_tableinst v_tabletype)) tableinst_lst tabletype_lst ⟹
		 ((length funcinst_lst) = (length functype_lst)) ⟹
		 list_all2 (λ (v_funcinst :: funcinst) (v_functype :: functype). (Funcinst_ok s v_funcinst v_functype)) funcinst_lst functype_lst ⟹
		 (s = ⦇ store_FUNCS = funcinst_lst, store_GLOBALS = globalinst_lst, store_TABLES = tableinst_lst, store_MEMS = meminst_lst ⦈) ⟹
		 (wf_store s) ⟹
		 list_all (λ (v_memtype :: memtype). (wf_limits v_memtype)) memtype_lst ⟹
		 list_all (λ (v_tabletype :: tabletype). (wf_limits v_tabletype)) tabletype_lst ⟹
		 (wf_store ⦇ store_FUNCS = funcinst_lst, store_GLOBALS = globalinst_lst, store_TABLES = tableinst_lst, store_MEMS = meminst_lst ⦈) ⟹
		 Store_ok s"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:196.1-196.54 *)
inductive Extend_globalinst :: "globalinst ⇒ globalinst ⇒ bool" where
	  mk_Extend_globalinst :
		"((v_mut = (Some MUT)) ∨ (v_val = val')) ⟹
		 (wf_globalinst ⦇ globalinst_TYPE = (mk_globaltype v_mut t), VALUE = v_val ⦈) ⟹
		 (wf_globalinst ⦇ globalinst_TYPE = (mk_globaltype v_mut t), VALUE = val' ⦈) ⟹
		 Extend_globalinst ⦇ globalinst_TYPE = (mk_globaltype v_mut t), VALUE = v_val ⦈ ⦇ globalinst_TYPE = (mk_globaltype v_mut t), VALUE = val' ⦈"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:197.1-197.45 *)
inductive Extend_meminst :: "meminst ⇒ meminst ⇒ bool" where
	  mk_Extend_meminst :
		"(v_n ≤ n') ⟹
		 ((length b_lst) ≤ (length b'_lst)) ⟹
		 (wf_meminst ⦇ meminst_TYPE = (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt)), BYTES = b_lst ⦈) ⟹
		 (wf_meminst ⦇ meminst_TYPE = (mk_limits (mk_uN n') (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt)), BYTES = b'_lst ⦈) ⟹
		 Extend_meminst ⦇ meminst_TYPE = (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt)), BYTES = b_lst ⦈ ⦇ meminst_TYPE = (mk_limits (mk_uN n') (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt)), BYTES = b'_lst ⦈"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:198.1-198.51 *)
inductive Extend_tableinst :: "tableinst ⇒ tableinst ⇒ bool" where
	  mk_Extend_tableinst :
		"(v_n ≤ n') ⟹
		 ((length ref_lst) ≤ (length ref'_lst)) ⟹
		 (wf_tableinst ⦇ tableinst_TYPE = (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt)), REFS = (map (λ (ref :: funcaddr). (Some ref)) ref_lst) ⦈) ⟹
		 (wf_tableinst ⦇ tableinst_TYPE = (mk_limits (mk_uN n') (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt)), REFS = (map (λ (ref' :: funcaddr). (Some ref')) ref'_lst) ⦈) ⟹
		 Extend_tableinst ⦇ tableinst_TYPE = (mk_limits (mk_uN v_n) (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt)), REFS = (map (λ (ref :: funcaddr). (Some ref)) ref_lst) ⦈ ⦇ tableinst_TYPE = (mk_limits (mk_uN n') (map_option (λ (v_m :: m). (mk_uN v_m)) m_opt)), REFS = (map (λ (ref' :: funcaddr). (Some ref')) ref'_lst) ⦈"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:199.1-199.48 *)
inductive Extend_funcinst :: "funcinst ⇒ funcinst ⇒ bool" where
	  mk_Extend_funcinst :
		"(wf_funcinst ⦇ funcinst_TYPE = ft, funcinst_MODULE = mm, CODE = fc ⦈) ⟹
		 Extend_funcinst ⦇ funcinst_TYPE = ft, funcinst_MODULE = mm, CODE = fc ⦈ ⦇ funcinst_TYPE = ft, funcinst_MODULE = mm, CODE = fc ⦈"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:200.1-200.39 *)
inductive Extend_store :: "store ⇒ store ⇒ bool" where
	  mk_Extend_store :
		"holds_upto (λ a. (a < (length (store_GLOBALS s)))) (length (store_GLOBALS s)) ⟹
		 holds_upto (λ a. (a < (length (store_GLOBALS s')))) (length (store_GLOBALS s)) ⟹
		 holds_upto (λ a. (Extend_globalinst ((store_GLOBALS s) ! a) ((store_GLOBALS s') ! a))) (length (store_GLOBALS s)) ⟹
		 holds_upto (λ a. (a < (length (store_MEMS s)))) (length (store_MEMS s)) ⟹
		 holds_upto (λ a. (a < (length (store_MEMS s')))) (length (store_MEMS s)) ⟹
		 holds_upto (λ a. (Extend_meminst ((store_MEMS s) ! a) ((store_MEMS s') ! a))) (length (store_MEMS s)) ⟹
		 holds_upto (λ a. (a < (length (store_TABLES s)))) (length (store_TABLES s)) ⟹
		 holds_upto (λ a. (a < (length (store_TABLES s')))) (length (store_TABLES s)) ⟹
		 holds_upto (λ a. (Extend_tableinst ((store_TABLES s) ! a) ((store_TABLES s') ! a))) (length (store_TABLES s)) ⟹
		 holds_upto (λ a. (a < (length (store_FUNCS s)))) (length (store_FUNCS s)) ⟹
		 holds_upto (λ a. (a < (length (store_FUNCS s')))) (length (store_FUNCS s)) ⟹
		 holds_upto (λ a. (Extend_funcinst ((store_FUNCS s) ! a) ((store_FUNCS s') ! a))) (length (store_FUNCS s)) ⟹
		 (wf_store s) ⟹
		 (wf_store s') ⟹
		 Extend_store s s'"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:229.1-229.38 *)
inductive State_ok :: "state ⇒ res_context ⇒ bool" where
	  mk_State_ok :
		"(Store_ok s) ⟹
		 (Frame_ok s f C) ⟹
		 (wf_context C) ⟹
		 (wf_state (mk_state s f)) ⟹
		 State_ok (mk_state s f) C"

(* Inductive Relations Definition at: ../specification/wasm-1.0/B-soundness.spectec:230.1-230.43 *)
inductive Config_ok :: "config ⇒ resulttype ⇒ bool" where
	  mk_Config_ok :
		"(State_ok (mk_state s f) C) ⟹
		 (Expr_ok2 s C admininstr_lst t_opt) ⟹
		 (wf_context C) ⟹
		 (wf_config (mk_config (mk_state s f) admininstr_lst)) ⟹
		 (wf_state (mk_state s f)) ⟹
		 Config_ok (mk_config (mk_state s f) admininstr_lst) t_opt"

end

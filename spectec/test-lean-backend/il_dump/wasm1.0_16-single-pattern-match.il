
;; ../specification/wasm-1.0/1-syntax.spectec:119.14-119.17
syntax r_MUT = 
  | MUT

;; ../specification/wasm-1.0/0-aux.spectec:7.1-7.27
syntax N = nat

;; ../specification/wasm-1.0/0-aux.spectec:8.1-8.27
syntax M = nat

;; ../specification/wasm-1.0/0-aux.spectec:9.1-9.27
syntax n = nat

;; ../specification/wasm-1.0/0-aux.spectec:10.1-10.27
syntax m = nat

;; ../specification/wasm-1.0/0-aux.spectec:15.1-15.14
def $Ki : nat
  ;; ../specification/wasm-1.0/0-aux.spectec:16.1-16.15
  def $Ki = 1024

;; ../specification/wasm-1.0/0-aux.spectec:21.1-21.25
def $min(nat : nat, nat_0 : nat) : nat
  ;; ../specification/wasm-1.0/0-aux.spectec:22.1-22.36
  def $min{i : nat, j : nat}(i, j) = (if (i <= j) then i else j)

;; ../specification/wasm-1.0/0-aux.spectec:25.1-25.21
rec {

;; ../specification/wasm-1.0/0-aux.spectec:25.6-25.10
relation fun_sum: `%%`(nat*, nat)
  ;; ../specification/wasm-1.0/0-aux.spectec:25.6-25.10
  rule fun_sum_case_0:
    `%%`([], 0)

  ;; ../specification/wasm-1.0/0-aux.spectec:25.6-25.10
  rule fun_sum_case_1{v_n : nat, n'_lst : n*, var_0 : nat}:
    `%%`([v_n] ++ n'_lst, (v_n + var_0))
    -- fun_sum: `%%`(n'_lst, var_0)
}

;; ../specification/wasm-1.0/0-aux.spectec:32.1-32.58
def $opt_(syntax X, var_0_lst : X*) : X??
  ;; ../specification/wasm-1.0/0-aux.spectec:33.1-33.31
  def $opt_{syntax X}(syntax X, []) = ?(?())
  ;; ../specification/wasm-1.0/0-aux.spectec:34.1-34.27
  def $opt_{syntax X, w : X}(syntax X, [w]) = ?(?(w))
  def $opt_{syntax X, x1 : X*}(syntax X, x1) = ?()
    -- otherwise

;; ../specification/wasm-1.0/0-aux.spectec:36.1-36.45
def $list_(syntax X, var_0_opt : X?) : X*
  ;; ../specification/wasm-1.0/0-aux.spectec:37.1-37.32
  def $list_{syntax X}(syntax X, ?()) = []
  ;; ../specification/wasm-1.0/0-aux.spectec:38.1-38.28
  def $list_{syntax X, w : X}(syntax X, ?(w)) = [w]

;; ../specification/wasm-1.0/0-aux.spectec:40.1-40.59
rec {

;; ../specification/wasm-1.0/0-aux.spectec:40.1-40.59
def $concat_(syntax X, var_0_lst_lst : X**) : X*
  ;; ../specification/wasm-1.0/0-aux.spectec:41.1-41.34
  def $concat_{syntax X}(syntax X, []) = []
  ;; ../specification/wasm-1.0/0-aux.spectec:42.1-42.61
  def $concat_{syntax X, w_lst : X*, w'_lst_lst : X**}(syntax X, [w_lst] ++ w'_lst_lst) = w_lst ++ $concat_(syntax X, w'_lst_lst)
}

;; ../specification/wasm-1.0/0-aux.spectec:44.1-44.78
rec {

;; ../specification/wasm-1.0/0-aux.spectec:44.1-44.78
def $disjoint_(syntax X, var_0_lst : X*) : bool
  ;; ../specification/wasm-1.0/0-aux.spectec:45.1-45.37
  def $disjoint_{syntax X}(syntax X, []) = true
  ;; ../specification/wasm-1.0/0-aux.spectec:46.1-46.68
  def $disjoint_{syntax X, w : X, w'_lst : X*}(syntax X, [w] ++ w'_lst) = (~ (w <- w'_lst) /\ $disjoint_(syntax X, w'_lst))
}

;; ../specification/wasm-1.0/1-syntax.spectec:6.1-6.49
syntax list{syntax X}(syntax X) = 
  | mk_list(X_lst : X*)
    -- if (|X_lst| < (2 ^ 32))

;; ../specification/wasm-1.0/1-syntax.spectec:15.1-15.50
syntax byte = 
  | mk_byte(i : nat)

;; ../specification/wasm-1.0/1-syntax.spectec:15.1-15.50
def $proj_byte_0(x : byte) : (nat)
  ;; ../specification/wasm-1.0/1-syntax.spectec:15.1-15.50
  def $proj_byte_0{v_num_0 : nat}(mk_byte_byte(v_num_0)) = (v_num_0)

;; ../specification/wasm-1.0/1-syntax.spectec:15.8-15.12
relation wf_byte: `%`(byte)
  ;; ../specification/wasm-1.0/1-syntax.spectec:15.8-15.12
  rule byte_case_0{i : nat}:
    `%`(mk_byte_byte(i))
    -- if ((i >= 0) /\ (i <= 255))

;; ../specification/wasm-1.0/1-syntax.spectec:17.1-18.25
syntax uN = 
  | mk_uN(i : nat)

;; ../specification/wasm-1.0/1-syntax.spectec:17.1-18.25
def $proj_uN_0(x : uN) : (nat)
  ;; ../specification/wasm-1.0/1-syntax.spectec:17.1-18.25
  def $proj_uN_0{v_num_0 : nat}(mk_uN_uN(v_num_0)) = (v_num_0)

;; ../specification/wasm-1.0/1-syntax.spectec:17.8-17.11
relation wf_uN: `%%`(N, uN)
  ;; ../specification/wasm-1.0/1-syntax.spectec:17.8-17.11
  rule uN_case_0{v_N : N, i : nat}:
    `%%`(v_N, mk_uN_uN(i))
    -- if ((i >= 0) /\ (i <= ((((2 ^ v_N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))

;; ../specification/wasm-1.0/1-syntax.spectec:19.1-20.49
syntax sN = 
  | mk_sN(i : int)

;; ../specification/wasm-1.0/1-syntax.spectec:19.1-20.49
def $proj_sN_0(x : sN) : (int)
  ;; ../specification/wasm-1.0/1-syntax.spectec:19.1-20.49
  def $proj_sN_0{v_num_0 : int}(mk_sN_sN(v_num_0)) = (v_num_0)

;; ../specification/wasm-1.0/1-syntax.spectec:19.8-19.11
relation wf_sN: `%%`(N, sN)
  ;; ../specification/wasm-1.0/1-syntax.spectec:19.8-19.11
  rule sN_case_0{v_N : N, i : int}:
    `%%`(v_N, mk_sN_sN(i))
    -- if ((((i >= - ((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) /\ (i <= - (1 : nat <:> int))) \/ (i = (0 : nat <:> int))) \/ ((i >= + (1 : nat <:> int)) /\ (i <= (((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))

;; ../specification/wasm-1.0/1-syntax.spectec:21.1-22.8
syntax iN = uN

;; ../specification/wasm-1.0/1-syntax.spectec:24.1-24.20
syntax u31 = uN

;; ../specification/wasm-1.0/1-syntax.spectec:25.1-25.20
syntax u32 = uN

;; ../specification/wasm-1.0/1-syntax.spectec:26.1-26.20
syntax u64 = uN

;; ../specification/wasm-1.0/1-syntax.spectec:28.1-28.20
syntax i32 = iN

;; ../specification/wasm-1.0/1-syntax.spectec:29.1-29.20
syntax i64 = iN

;; ../specification/wasm-1.0/1-syntax.spectec:36.1-36.35
def $signif(v_N : N) : nat?
  ;; ../specification/wasm-1.0/1-syntax.spectec:37.1-37.21
  def $signif(32) = ?(23)
  ;; ../specification/wasm-1.0/1-syntax.spectec:38.1-38.21
  def $signif(64) = ?(52)
  def $signif{x0 : N}(x0) = ?()
    -- otherwise

;; ../specification/wasm-1.0/1-syntax.spectec:40.1-40.34
def $expon(v_N : N) : nat?
  ;; ../specification/wasm-1.0/1-syntax.spectec:41.1-41.19
  def $expon(32) = ?(8)
  ;; ../specification/wasm-1.0/1-syntax.spectec:42.1-42.20
  def $expon(64) = ?(11)
  def $expon{x0 : N}(x0) = ?()
    -- otherwise

;; ../specification/wasm-1.0/1-syntax.spectec:44.1-44.30
def $fun_M(v_N : N) : nat
  ;; ../specification/wasm-1.0/1-syntax.spectec:45.1-45.23
  def $fun_M{v_N : nat}(v_N) = !($signif(v_N))

;; ../specification/wasm-1.0/1-syntax.spectec:47.1-47.30
def $E(v_N : N) : nat
  ;; ../specification/wasm-1.0/1-syntax.spectec:48.1-48.22
  def $E{v_N : nat}(v_N) = !($expon(v_N))

;; ../specification/wasm-1.0/1-syntax.spectec:54.1-54.30
syntax exp = int

;; ../specification/wasm-1.0/1-syntax.spectec:55.1-59.84
syntax fNmag = 
  | NORM(v_m : m, v_exp : exp)
  | SUBNORM(v_m : m)
  | INF
  | NAN(v_m : m)

;; ../specification/wasm-1.0/1-syntax.spectec:55.8-55.14
relation wf_fNmag: `%%`(N, fNmag)
  ;; ../specification/wasm-1.0/1-syntax.spectec:55.8-55.14
  rule fNmag_case_0{v_N : N, v_m : m, v_exp : exp}:
    `%%`(v_N, NORM_fNmag(v_m, v_exp))
    -- if ((v_m < (2 ^ $fun_M(v_N))) /\ ((((2 : nat <:> int) - ((2 ^ ((($E(v_N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) <= v_exp) /\ (v_exp <= (((2 ^ ((($E(v_N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))

  ;; ../specification/wasm-1.0/1-syntax.spectec:55.8-55.14
  rule fNmag_case_1{v_N : N, v_exp : exp, v_m : m}:
    `%%`(v_N, SUBNORM_fNmag(v_m))
    -- if ((v_m < (2 ^ $fun_M(v_N))) /\ (((2 : nat <:> int) - ((2 ^ ((($E(v_N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) = v_exp))

  ;; ../specification/wasm-1.0/1-syntax.spectec:55.8-55.14
  rule fNmag_case_2{v_N : N}:
    `%%`(v_N, INF_fNmag)

  ;; ../specification/wasm-1.0/1-syntax.spectec:55.8-55.14
  rule fNmag_case_3{v_N : N, v_m : m}:
    `%%`(v_N, NAN_fNmag(v_m))
    -- if ((1 <= v_m) /\ (v_m < (2 ^ $fun_M(v_N))))

;; ../specification/wasm-1.0/1-syntax.spectec:50.1-52.35
syntax fN = 
  | POS(fNmag)
  | NEG(fNmag)

;; ../specification/wasm-1.0/1-syntax.spectec:50.8-50.11
relation wf_fN: `%%`(N, fN)
  ;; ../specification/wasm-1.0/1-syntax.spectec:50.8-50.11
  rule fN_case_0{v_N : N, var_0 : fNmag}:
    `%%`(v_N, POS_fN(var_0))
    -- wf_fNmag: `%%`(v_N, var_0)

  ;; ../specification/wasm-1.0/1-syntax.spectec:50.8-50.11
  rule fN_case_1{v_N : N, var_0 : fNmag}:
    `%%`(v_N, NEG_fN(var_0))
    -- wf_fNmag: `%%`(v_N, var_0)

;; ../specification/wasm-1.0/1-syntax.spectec:61.1-61.20
syntax f32 = fN

;; ../specification/wasm-1.0/1-syntax.spectec:62.1-62.20
syntax f64 = fN

;; ../specification/wasm-1.0/1-syntax.spectec:64.6-64.12
relation fun_fzero: `%%`(N, fN)
  ;; ../specification/wasm-1.0/1-syntax.spectec:64.6-64.12
  rule fun_fzero_case_0{v_N : nat}:
    `%%`(v_N, POS_fN(SUBNORM_fNmag(0)))
    -- wf_fN: `%%`(v_N, POS_fN(SUBNORM_fNmag(0)))

;; ../specification/wasm-1.0/1-syntax.spectec:67.6-67.11
relation fun_fone: `%%`(N, fN)
  ;; ../specification/wasm-1.0/1-syntax.spectec:67.6-67.11
  rule fun_fone_case_0{v_N : nat}:
    `%%`(v_N, POS_fN(NORM_fNmag(1, (0 : nat <:> int))))
    -- wf_fN: `%%`(v_N, POS_fN(NORM_fNmag(1, (0 : nat <:> int))))

;; ../specification/wasm-1.0/1-syntax.spectec:70.1-70.21
def $canon_(v_N : N) : nat
  ;; ../specification/wasm-1.0/1-syntax.spectec:71.1-71.37
  def $canon_{v_N : nat}(v_N) = (2 ^ (((!($signif(v_N)) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))

;; ../specification/wasm-1.0/1-syntax.spectec:78.1-78.85
syntax char = 
  | mk_char(i : nat)

;; ../specification/wasm-1.0/1-syntax.spectec:78.1-78.85
def $proj_char_0(x : char) : (nat)
  ;; ../specification/wasm-1.0/1-syntax.spectec:78.1-78.85
  def $proj_char_0{v_num_0 : nat}(mk_char_char(v_num_0)) = (v_num_0)

;; ../specification/wasm-1.0/1-syntax.spectec:78.8-78.12
relation wf_char: `%`(char)
  ;; ../specification/wasm-1.0/1-syntax.spectec:78.8-78.12
  rule char_case_0{i : nat}:
    `%`(mk_char_char(i))
    -- if (((i >= 0) /\ (i <= 55295)) \/ ((i >= 57344) /\ (i <= 1114111)))

;; ../specification/wasm-1.0/1-syntax.spectec:80.1-80.25
rec {

;; ../specification/wasm-1.0/1-syntax.spectec:80.6-80.11
relation fun_utf8: `%%`(char*, byte*)
  ;; ../specification/wasm-1.0/1-syntax.spectec:80.6-80.11
  rule fun_utf8_case_0{ch : char, b : byte}:
    `%%`([ch], [b])
    -- if (($proj_char_0(ch).0 < 128) /\ (mk_byte_byte($proj_char_0(ch).0) = b))
    -- wf_byte: `%`(b)
    -- wf_byte: `%`(mk_byte_byte($proj_char_0(ch).0))

  ;; ../specification/wasm-1.0/1-syntax.spectec:80.6-80.11
  rule fun_utf8_case_1{ch : char, b_1 : byte, b_2 : byte}:
    `%%`([ch], [b_1 b_2])
    -- if (((128 <= $proj_char_0(ch).0) /\ ($proj_char_0(ch).0 < 2048)) /\ ($proj_char_0(ch).0 = (((2 ^ 6) * ((($proj_byte_0(b_1).0 : nat <:> int) - (192 : nat <:> int)) : int <:> nat)) + ((($proj_byte_0(b_2).0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))))
    -- wf_byte: `%`(b_1)
    -- wf_byte: `%`(b_2)

  ;; ../specification/wasm-1.0/1-syntax.spectec:80.6-80.11
  rule fun_utf8_case_2{ch : char, b_1 : byte, b_2 : byte, b_3 : byte}:
    `%%`([ch], [b_1 b_2 b_3])
    -- if ((((2048 <= $proj_char_0(ch).0) /\ ($proj_char_0(ch).0 < 55296)) \/ ((57344 <= $proj_char_0(ch).0) /\ ($proj_char_0(ch).0 < 65536))) /\ ($proj_char_0(ch).0 = ((((2 ^ 12) * ((($proj_byte_0(b_1).0 : nat <:> int) - (224 : nat <:> int)) : int <:> nat)) + ((2 ^ 6) * ((($proj_byte_0(b_2).0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))) + ((($proj_byte_0(b_3).0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))))
    -- wf_byte: `%`(b_1)
    -- wf_byte: `%`(b_2)
    -- wf_byte: `%`(b_3)

  ;; ../specification/wasm-1.0/1-syntax.spectec:80.6-80.11
  rule fun_utf8_case_3{ch : char, b_1 : byte, b_2 : byte, b_3 : byte, b_4 : byte}:
    `%%`([ch], [b_1 b_2 b_3 b_4])
    -- if (((65536 <= $proj_char_0(ch).0) /\ ($proj_char_0(ch).0 < 69632)) /\ ($proj_char_0(ch).0 = (((((2 ^ 18) * ((($proj_byte_0(b_1).0 : nat <:> int) - (240 : nat <:> int)) : int <:> nat)) + ((2 ^ 12) * ((($proj_byte_0(b_2).0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))) + ((2 ^ 6) * ((($proj_byte_0(b_3).0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))) + ((($proj_byte_0(b_4).0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))))
    -- wf_byte: `%`(b_1)
    -- wf_byte: `%`(b_2)
    -- wf_byte: `%`(b_3)
    -- wf_byte: `%`(b_4)

  ;; ../specification/wasm-1.0/1-syntax.spectec:80.6-80.11
  rule fun_utf8_case_4{ch_lst : char*, var_2_lst : byte**, var_1_lst : byte**, var_0_lst : byte**}:
    `%%`(ch_lst, $concat_(syntax byte, var_0_lst))
    -- if (|var_2_lst| = |ch_lst|)
    -- (fun_utf8: `%%`([ch_3], var_2))*{var_2 <- var_2_lst, ch_3 <- ch_lst}
    -- if (|var_1_lst| = |ch_lst|)
    -- (fun_utf8: `%%`([ch_2], var_1))*{var_1 <- var_1_lst, ch_2 <- ch_lst}
    -- if (|var_0_lst| = |ch_lst|)
    -- (fun_utf8: `%%`([ch], var_0))*{var_0 <- var_0_lst, ch <- ch_lst}
    -- (wf_byte: `%`(iter_1))*{iter_1 <- $concat_(syntax byte, var_1_lst)}
    -- (wf_byte: `%`(iter_2))*{iter_2 <- var_2}*{var_2 <- var_2_lst}
}

;; ../specification/wasm-1.0/1-syntax.spectec:82.1-82.70
syntax name = 
  | mk_name(char_lst : char*)

;; ../specification/wasm-1.0/1-syntax.spectec:82.1-82.70
def $proj_name_0(x : name) : (char*)
  ;; ../specification/wasm-1.0/1-syntax.spectec:82.1-82.70
  def $proj_name_0{v_char_list_0 : char*}(mk_name_name(v_char_list_0)) = (v_char_list_0)

;; ../specification/wasm-1.0/1-syntax.spectec:82.8-82.12
relation wf_name: `%`(name)
  ;; ../specification/wasm-1.0/1-syntax.spectec:82.8-82.12
  rule name_case_0{char_lst : char*, var_0 : byte*}:
    `%`(mk_name_name(char_lst))
    -- fun_utf8: `%%`(char_lst, var_0)
    -- (wf_char: `%`(v_char))*{v_char <- char_lst}
    -- if (|var_0| < (2 ^ 32))

;; ../specification/wasm-1.0/1-syntax.spectec:91.1-91.36
syntax idx = u32

;; ../specification/wasm-1.0/1-syntax.spectec:93.1-93.45
syntax typeidx = idx

;; ../specification/wasm-1.0/1-syntax.spectec:94.1-94.49
syntax funcidx = idx

;; ../specification/wasm-1.0/1-syntax.spectec:95.1-95.49
syntax globalidx = idx

;; ../specification/wasm-1.0/1-syntax.spectec:96.1-96.47
syntax tableidx = idx

;; ../specification/wasm-1.0/1-syntax.spectec:97.1-97.46
syntax memidx = idx

;; ../specification/wasm-1.0/1-syntax.spectec:98.1-98.47
syntax labelidx = idx

;; ../specification/wasm-1.0/1-syntax.spectec:99.1-99.47
syntax localidx = idx

;; ../specification/wasm-1.0/1-syntax.spectec:108.1-109.26
syntax valtype = 
  | I32
  | I64
  | F32
  | F64

;; ../specification/wasm-1.0/1-syntax.spectec:111.1-111.38
syntax Inn = 
  | I32
  | I64

def $valtype_Inn(var_0 : Inn) : valtype
  def $valtype_Inn(I32_Inn) = I32_valtype
  def $valtype_Inn(I64_Inn) = I64_valtype

;; ../specification/wasm-1.0/1-syntax.spectec:112.1-112.38
syntax Fnn = 
  | F32
  | F64

def $valtype_Fnn(var_0 : Fnn) : valtype
  def $valtype_Fnn(F32_Fnn) = F32_valtype
  def $valtype_Fnn(F64_Fnn) = F64_valtype

;; ../specification/wasm-1.0/1-syntax.spectec:116.1-117.11
syntax resulttype = valtype?

;; ../specification/wasm-1.0/1-syntax.spectec:119.1-119.18
syntax mut = r_MUT?

;; ../specification/wasm-1.0/1-syntax.spectec:121.1-122.17
syntax limits = 
  | mk_limits(v_u32 : u32, u32_opt : u32?)

;; ../specification/wasm-1.0/1-syntax.spectec:121.8-121.14
relation wf_limits: `%`(limits)
  ;; ../specification/wasm-1.0/1-syntax.spectec:121.8-121.14
  rule limits_case_0{v_u32 : u32, u32_opt : u32?}:
    `%`(mk_limits_limits(v_u32, u32_opt))
    -- wf_uN: `%%`(32, v_u32)
    -- (wf_uN: `%%`(32, v_u32))?{v_u32 <- u32_opt}

;; ../specification/wasm-1.0/1-syntax.spectec:123.1-124.14
syntax globaltype = 
  | mk_globaltype(v_mut : mut, v_valtype : valtype)

;; ../specification/wasm-1.0/1-syntax.spectec:125.1-126.23
syntax functype = 
  | mk_functype(valtype_lst : valtype*, valtype_lst : valtype*)

;; ../specification/wasm-1.0/1-syntax.spectec:127.1-128.9
syntax tabletype = limits

;; ../specification/wasm-1.0/1-syntax.spectec:129.1-130.9
syntax memtype = limits

;; ../specification/wasm-1.0/1-syntax.spectec:131.1-132.70
syntax externtype = 
  | FUNC(v_functype : functype)
  | GLOBAL(v_globaltype : globaltype)
  | TABLE(v_tabletype : tabletype)
  | MEM(v_memtype : memtype)

;; ../specification/wasm-1.0/1-syntax.spectec:131.8-131.18
relation wf_externtype: `%`(externtype)
  ;; ../specification/wasm-1.0/1-syntax.spectec:131.8-131.18
  rule externtype_case_0{v_functype : functype}:
    `%`(FUNC_externtype(v_functype))

  ;; ../specification/wasm-1.0/1-syntax.spectec:131.8-131.18
  rule externtype_case_1{v_globaltype : globaltype}:
    `%`(GLOBAL_externtype(v_globaltype))

  ;; ../specification/wasm-1.0/1-syntax.spectec:131.8-131.18
  rule externtype_case_2{v_tabletype : tabletype}:
    `%`(TABLE_externtype(v_tabletype))
    -- wf_limits: `%`(v_tabletype)

  ;; ../specification/wasm-1.0/1-syntax.spectec:131.8-131.18
  rule externtype_case_3{v_memtype : memtype}:
    `%`(MEM_externtype(v_memtype))
    -- wf_limits: `%`(v_memtype)

;; ../specification/wasm-1.0/1-syntax.spectec:144.1-144.41
def $size(v_valtype : valtype) : nat
  ;; ../specification/wasm-1.0/2-syntax-aux.spectec:11.1-11.20
  def $size(I32_valtype) = 32
  ;; ../specification/wasm-1.0/2-syntax-aux.spectec:12.1-12.20
  def $size(I64_valtype) = 64
  ;; ../specification/wasm-1.0/2-syntax-aux.spectec:13.1-13.20
  def $size(F32_valtype) = 32
  ;; ../specification/wasm-1.0/2-syntax-aux.spectec:14.1-14.20
  def $size(F64_valtype) = 64

;; ../specification/wasm-1.0/1-syntax.spectec:146.1-146.21
syntax val_ = 
  | mk_val__0(v_Inn : Inn, var_x : iN)
  | mk_val__1(v_Fnn : Fnn, var_x : fN)

;; ../specification/wasm-1.0/1-syntax.spectec:146.8-146.13
relation wf_val_: `%%`(valtype, val_)
  ;; ../specification/wasm-1.0/1-syntax.spectec:146.8-146.13
  rule val__case_0{v_valtype : valtype, v_Inn : Inn, var_x : iN}:
    `%%`(v_valtype, mk_val__0_val_(v_Inn, var_x))
    -- wf_uN: `%%`($size($valtype_Inn(v_Inn)), var_x)
    -- if (v_valtype = $valtype_Inn(v_Inn))

  ;; ../specification/wasm-1.0/1-syntax.spectec:146.8-146.13
  rule val__case_1{v_valtype : valtype, v_Fnn : Fnn, var_x : fN}:
    `%%`(v_valtype, mk_val__1_val_(v_Fnn, var_x))
    -- wf_fN: `%%`($size($valtype_Fnn(v_Fnn)), var_x)
    -- if (v_valtype = $valtype_Fnn(v_Fnn))

;; ../specification/wasm-1.0/1-syntax.spectec:146.1-146.21
def $proj_val__0(var_x : val_) : iN?
  ;; ../specification/wasm-1.0/1-syntax.spectec:146.8-146.13
  def $proj_val__0{v_Inn : Inn, var_x : iN}(mk_val__0_val_(v_Inn, var_x)) = ?(var_x)
  ;; ../specification/wasm-1.0/1-syntax.spectec:146.8-146.13
  def $proj_val__0{var_x : val_}(var_x) = ?()

;; ../specification/wasm-1.0/1-syntax.spectec:146.1-146.21
def $proj_val__1(var_x : val_) : fN?
  ;; ../specification/wasm-1.0/1-syntax.spectec:146.8-146.13
  def $proj_val__1{v_Fnn : Fnn, var_x : fN}(mk_val__1_val_(v_Fnn, var_x)) = ?(var_x)
  ;; ../specification/wasm-1.0/1-syntax.spectec:146.8-146.13
  def $proj_val__1{var_x : val_}(var_x) = ?()

;; ../specification/wasm-1.0/1-syntax.spectec:153.1-153.42
syntax sx = 
  | U
  | S

;; ../specification/wasm-1.0/1-syntax.spectec:154.1-154.56
syntax sz = 
  | mk_sz(i : nat)

;; ../specification/wasm-1.0/1-syntax.spectec:154.1-154.56
def $proj_sz_0(x : sz) : (nat)
  ;; ../specification/wasm-1.0/1-syntax.spectec:154.1-154.56
  def $proj_sz_0{v_num_0 : nat}(mk_sz_sz(v_num_0)) = (v_num_0)

;; ../specification/wasm-1.0/1-syntax.spectec:154.8-154.10
relation wf_sz: `%`(sz)
  ;; ../specification/wasm-1.0/1-syntax.spectec:154.8-154.10
  rule sz_case_0{i : nat}:
    `%`(mk_sz_sz(i))
    -- if ((((i = 8) \/ (i = 16)) \/ (i = 32)) \/ (i = 64))

;; ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22
syntax unop_Inn = 
  | CLZ
  | CTZ
  | POPCNT

;; ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22
syntax unop_Fnn = 
  | ABS
  | NEG
  | SQRT
  | CEIL
  | FLOOR
  | TRUNC
  | NEAREST

;; ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22
syntax unop_ = 
  | mk_unop__0(v_Inn : Inn, var_x : unop_Inn)
  | mk_unop__1(v_Fnn : Fnn, var_x : unop_Fnn)

;; ../specification/wasm-1.0/1-syntax.spectec:156.8-156.14
relation wf_unop_: `%%`(valtype, unop_)
  ;; ../specification/wasm-1.0/1-syntax.spectec:156.8-156.14
  rule unop__case_0{v_valtype : valtype, v_Inn : Inn, var_x : unop_Inn}:
    `%%`(v_valtype, mk_unop__0_unop_(v_Inn, var_x))
    -- if (v_valtype = $valtype_Inn(v_Inn))

  ;; ../specification/wasm-1.0/1-syntax.spectec:156.8-156.14
  rule unop__case_1{v_valtype : valtype, v_Fnn : Fnn, var_x : unop_Fnn}:
    `%%`(v_valtype, mk_unop__1_unop_(v_Fnn, var_x))
    -- if (v_valtype = $valtype_Fnn(v_Fnn))

;; ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22
def $proj_unop__0(var_x : unop_) : unop_Inn?
  ;; ../specification/wasm-1.0/1-syntax.spectec:156.8-156.14
  def $proj_unop__0{v_Inn : Inn, var_x : unop_Inn}(mk_unop__0_unop_(v_Inn, var_x)) = ?(var_x)
  ;; ../specification/wasm-1.0/1-syntax.spectec:156.8-156.14
  def $proj_unop__0{var_x : unop_}(var_x) = ?()

;; ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22
def $proj_unop__1(var_x : unop_) : unop_Fnn?
  ;; ../specification/wasm-1.0/1-syntax.spectec:156.8-156.14
  def $proj_unop__1{v_Fnn : Fnn, var_x : unop_Fnn}(mk_unop__1_unop_(v_Fnn, var_x)) = ?(var_x)
  ;; ../specification/wasm-1.0/1-syntax.spectec:156.8-156.14
  def $proj_unop__1{var_x : unop_}(var_x) = ?()

;; ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23
syntax binop_Inn = 
  | ADD
  | SUB
  | MUL
  | DIV(v_sx : sx)
  | REM(v_sx : sx)
  | AND
  | OR
  | XOR
  | SHL
  | SHR(v_sx : sx)
  | ROTL
  | ROTR

;; ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23
syntax binop_Fnn = 
  | ADD
  | SUB
  | MUL
  | DIV
  | MIN
  | MAX
  | COPYSIGN

;; ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23
syntax binop_ = 
  | mk_binop__0(v_Inn : Inn, var_x : binop_Inn)
  | mk_binop__1(v_Fnn : Fnn, var_x : binop_Fnn)

;; ../specification/wasm-1.0/1-syntax.spectec:160.8-160.15
relation wf_binop_: `%%`(valtype, binop_)
  ;; ../specification/wasm-1.0/1-syntax.spectec:160.8-160.15
  rule binop__case_0{v_valtype : valtype, v_Inn : Inn, var_x : binop_Inn}:
    `%%`(v_valtype, mk_binop__0_binop_(v_Inn, var_x))
    -- if (v_valtype = $valtype_Inn(v_Inn))

  ;; ../specification/wasm-1.0/1-syntax.spectec:160.8-160.15
  rule binop__case_1{v_valtype : valtype, v_Fnn : Fnn, var_x : binop_Fnn}:
    `%%`(v_valtype, mk_binop__1_binop_(v_Fnn, var_x))
    -- if (v_valtype = $valtype_Fnn(v_Fnn))

;; ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23
def $proj_binop__0(var_x : binop_) : binop_Inn?
  ;; ../specification/wasm-1.0/1-syntax.spectec:160.8-160.15
  def $proj_binop__0{v_Inn : Inn, var_x : binop_Inn}(mk_binop__0_binop_(v_Inn, var_x)) = ?(var_x)
  ;; ../specification/wasm-1.0/1-syntax.spectec:160.8-160.15
  def $proj_binop__0{var_x : binop_}(var_x) = ?()

;; ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23
def $proj_binop__1(var_x : binop_) : binop_Fnn?
  ;; ../specification/wasm-1.0/1-syntax.spectec:160.8-160.15
  def $proj_binop__1{v_Fnn : Fnn, var_x : binop_Fnn}(mk_binop__1_binop_(v_Fnn, var_x)) = ?(var_x)
  ;; ../specification/wasm-1.0/1-syntax.spectec:160.8-160.15
  def $proj_binop__1{var_x : binop_}(var_x) = ?()

;; ../specification/wasm-1.0/1-syntax.spectec:167.1-167.24
syntax testop_Inn = 
  | EQZ

;; ../specification/wasm-1.0/1-syntax.spectec:167.1-167.24
syntax testop_ = 
  | mk_testop__0(v_Inn : Inn, var_x : testop_Inn)

;; ../specification/wasm-1.0/1-syntax.spectec:167.8-167.16
relation wf_testop_: `%%`(valtype, testop_)
  ;; ../specification/wasm-1.0/1-syntax.spectec:167.8-167.16
  rule testop__case_0{v_valtype : valtype, v_Inn : Inn, var_x : testop_Inn}:
    `%%`(v_valtype, mk_testop__0_testop_(v_Inn, var_x))
    -- if (v_valtype = $valtype_Inn(v_Inn))

;; ../specification/wasm-1.0/1-syntax.spectec:167.1-167.24
def $proj_testop__0(var_x : testop_) : testop_Inn
  ;; ../specification/wasm-1.0/1-syntax.spectec:167.8-167.16
  def $proj_testop__0{v_Inn : Inn, var_x : testop_Inn}(mk_testop__0_testop_(v_Inn, var_x)) = var_x

;; ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23
syntax relop_Inn = 
  | EQ
  | NE
  | LT(v_sx : sx)
  | GT(v_sx : sx)
  | LE(v_sx : sx)
  | GE(v_sx : sx)

;; ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23
syntax relop_Fnn = 
  | EQ
  | NE
  | LT
  | GT
  | LE
  | GE

;; ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23
syntax relop_ = 
  | mk_relop__0(v_Inn : Inn, var_x : relop_Inn)
  | mk_relop__1(v_Fnn : Fnn, var_x : relop_Fnn)

;; ../specification/wasm-1.0/1-syntax.spectec:171.8-171.15
relation wf_relop_: `%%`(valtype, relop_)
  ;; ../specification/wasm-1.0/1-syntax.spectec:171.8-171.15
  rule relop__case_0{v_valtype : valtype, v_Inn : Inn, var_x : relop_Inn}:
    `%%`(v_valtype, mk_relop__0_relop_(v_Inn, var_x))
    -- if (v_valtype = $valtype_Inn(v_Inn))

  ;; ../specification/wasm-1.0/1-syntax.spectec:171.8-171.15
  rule relop__case_1{v_valtype : valtype, v_Fnn : Fnn, var_x : relop_Fnn}:
    `%%`(v_valtype, mk_relop__1_relop_(v_Fnn, var_x))
    -- if (v_valtype = $valtype_Fnn(v_Fnn))

;; ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23
def $proj_relop__0(var_x : relop_) : relop_Inn?
  ;; ../specification/wasm-1.0/1-syntax.spectec:171.8-171.15
  def $proj_relop__0{v_Inn : Inn, var_x : relop_Inn}(mk_relop__0_relop_(v_Inn, var_x)) = ?(var_x)
  ;; ../specification/wasm-1.0/1-syntax.spectec:171.8-171.15
  def $proj_relop__0{var_x : relop_}(var_x) = ?()

;; ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23
def $proj_relop__1(var_x : relop_) : relop_Fnn?
  ;; ../specification/wasm-1.0/1-syntax.spectec:171.8-171.15
  def $proj_relop__1{v_Fnn : Fnn, var_x : relop_Fnn}(mk_relop__1_relop_(v_Fnn, var_x)) = ?(var_x)
  ;; ../specification/wasm-1.0/1-syntax.spectec:171.8-171.15
  def $proj_relop__1{var_x : relop_}(var_x) = ?()

;; ../specification/wasm-1.0/1-syntax.spectec:179.1-180.78
syntax cvtop = 
  | EXTEND(v_sx : sx)
  | WRAP
  | CONVERT(v_sx : sx)
  | TRUNC(v_sx : sx)
  | PROMOTE
  | DEMOTE
  | REINTERPRET

;; ../specification/wasm-1.0/1-syntax.spectec:185.1-185.69
syntax memarg = 
{
  ALIGN u32,
  OFFSET u32
}

;; ../specification/wasm-1.0/1-syntax.spectec:185.8-185.14
relation wf_memarg: `%`(memarg)
  ;; ../specification/wasm-1.0/1-syntax.spectec:185.8-185.14
  rule memarg_case_{var_0 : u32, var_1 : u32}:
    `%`({ALIGN var_0, OFFSET var_1})
    -- wf_uN: `%%`(32, var_0)
    -- wf_uN: `%%`(32, var_1)

;; ../specification/wasm-1.0/1-syntax.spectec:189.1-189.24
syntax loadop_Inn = 
  | mk_loadop_Inn(v_sz : sz, v_sx : sx)

;; ../specification/wasm-1.0/1-syntax.spectec:189.8-189.16
relation wf_loadop_Inn: `%%`(Inn, loadop_Inn)
  ;; ../specification/wasm-1.0/1-syntax.spectec:189.8-189.16
  rule loadop_Inn_case_0{v_Inn : Inn, v_sz : sz, v_sx : sx}:
    `%%`(v_Inn, mk_loadop_Inn_loadop_Inn(v_sz, v_sx))
    -- wf_sz: `%`(v_sz)
    -- if ($proj_sz_0(v_sz).0 < $size($valtype_Inn(v_Inn)))

;; ../specification/wasm-1.0/1-syntax.spectec:189.1-189.24
syntax loadop_ = 
  | mk_loadop__0(v_Inn : Inn, var_x : loadop_Inn)

;; ../specification/wasm-1.0/1-syntax.spectec:189.8-189.16
relation wf_loadop_: `%%`(valtype, loadop_)
  ;; ../specification/wasm-1.0/1-syntax.spectec:189.8-189.16
  rule loadop__case_0{v_valtype : valtype, v_Inn : Inn, var_x : loadop_Inn}:
    `%%`(v_valtype, mk_loadop__0_loadop_(v_Inn, var_x))
    -- wf_loadop_Inn: `%%`(v_Inn, var_x)
    -- if (v_valtype = $valtype_Inn(v_Inn))

;; ../specification/wasm-1.0/1-syntax.spectec:189.1-189.24
def $proj_loadop__0(var_x : loadop_) : loadop_Inn
  ;; ../specification/wasm-1.0/1-syntax.spectec:189.8-189.16
  def $proj_loadop__0{v_Inn : Inn, var_x : loadop_Inn}(mk_loadop__0_loadop_(v_Inn, var_x)) = var_x

;; ../specification/wasm-1.0/1-syntax.spectec:195.1-195.52
syntax blocktype = valtype?

;; ../specification/wasm-1.0/1-syntax.spectec:245.1-250.16
rec {

;; ../specification/wasm-1.0/1-syntax.spectec:245.1-250.16
syntax instr = 
  | NOP
  | UNREACHABLE
  | DROP
  | SELECT
  | BLOCK(v_blocktype : blocktype, instr_lst : instr*)
  | LOOP(v_blocktype : blocktype, instr_lst : instr*)
  | `IF%%ELSE%`(v_blocktype : blocktype, instr_lst : instr*, instr_lst : instr*)
  | BR(v_labelidx : labelidx)
  | BR_IF(v_labelidx : labelidx)
  | BR_TABLE(labelidx_lst : labelidx*, v_labelidx : labelidx)
  | CALL(v_funcidx : funcidx)
  | CALL_INDIRECT(v_typeidx : typeidx)
  | RETURN
  | CONST(v_valtype : valtype, val_)
  | UNOP(v_valtype : valtype, unop_)
  | BINOP(v_valtype : valtype, binop_)
  | TESTOP(v_valtype : valtype, testop_)
  | RELOP(v_valtype : valtype, relop_)
  | CVTOP(valtype_1 : valtype, valtype_2 : valtype, v_cvtop : cvtop)
  | LOCAL_GET(v_localidx : localidx)
  | LOCAL_SET(v_localidx : localidx)
  | LOCAL_TEE(v_localidx : localidx)
  | GLOBAL_GET(v_globalidx : globalidx)
  | GLOBAL_SET(v_globalidx : globalidx)
  | LOAD(v_valtype : valtype, loadop_?, v_memarg : memarg)
  | STORE(v_valtype : valtype, sz_opt : sz?, v_memarg : memarg)
  | MEMORY_SIZE
  | MEMORY_GROW
}

;; ../specification/wasm-1.0/1-syntax.spectec:245.1-250.16
rec {

;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
relation wf_instr: `%`(instr)
  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_0:
    `%`(NOP_instr)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_1:
    `%`(UNREACHABLE_instr)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_2:
    `%`(DROP_instr)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_3:
    `%`(SELECT_instr)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_4{v_blocktype : blocktype, instr_lst : instr*}:
    `%`(BLOCK_instr(v_blocktype, instr_lst))
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_5{v_blocktype : blocktype, instr_lst : instr*}:
    `%`(LOOP_instr(v_blocktype, instr_lst))
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_6{v_blocktype : blocktype, instr_lst : instr*, instr_lst_0_lst : instr*}:
    `%`(`IF%%ELSE%`_instr(v_blocktype, instr_lst, instr_lst_0_lst))
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}
    -- (wf_instr: `%`(instr_lst_0))*{instr_lst_0 <- instr_lst_0_lst}

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_7{v_labelidx : labelidx}:
    `%`(BR_instr(v_labelidx))
    -- wf_uN: `%%`(32, v_labelidx)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_8{v_labelidx : labelidx}:
    `%`(BR_IF_instr(v_labelidx))
    -- wf_uN: `%%`(32, v_labelidx)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_9{labelidx_lst : labelidx*, v_labelidx : labelidx}:
    `%`(BR_TABLE_instr(labelidx_lst, v_labelidx))
    -- (wf_uN: `%%`(32, v_labelidx))*{v_labelidx <- labelidx_lst}
    -- wf_uN: `%%`(32, v_labelidx)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_10{v_funcidx : funcidx}:
    `%`(CALL_instr(v_funcidx))
    -- wf_uN: `%%`(32, v_funcidx)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_11{v_typeidx : typeidx}:
    `%`(CALL_INDIRECT_instr(v_typeidx))
    -- wf_uN: `%%`(32, v_typeidx)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_12:
    `%`(RETURN_instr)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_13{v_valtype : valtype, var_0 : val_}:
    `%`(CONST_instr(v_valtype, var_0))
    -- wf_val_: `%%`(v_valtype, var_0)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_14{v_valtype : valtype, var_0 : unop_}:
    `%`(UNOP_instr(v_valtype, var_0))
    -- wf_unop_: `%%`(v_valtype, var_0)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_15{v_valtype : valtype, var_0 : binop_}:
    `%`(BINOP_instr(v_valtype, var_0))
    -- wf_binop_: `%%`(v_valtype, var_0)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_16{v_valtype : valtype, var_0 : testop_}:
    `%`(TESTOP_instr(v_valtype, var_0))
    -- wf_testop_: `%%`(v_valtype, var_0)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_17{v_valtype : valtype, var_0 : relop_}:
    `%`(RELOP_instr(v_valtype, var_0))
    -- wf_relop_: `%%`(v_valtype, var_0)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_18{valtype_1 : valtype, valtype_2 : valtype, v_cvtop : cvtop}:
    `%`(CVTOP_instr(valtype_1, valtype_2, v_cvtop))
    -- if (valtype_1 =/= valtype_2)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_19{v_localidx : localidx}:
    `%`(LOCAL_GET_instr(v_localidx))
    -- wf_uN: `%%`(32, v_localidx)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_20{v_localidx : localidx}:
    `%`(LOCAL_SET_instr(v_localidx))
    -- wf_uN: `%%`(32, v_localidx)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_21{v_localidx : localidx}:
    `%`(LOCAL_TEE_instr(v_localidx))
    -- wf_uN: `%%`(32, v_localidx)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_22{v_globalidx : globalidx}:
    `%`(GLOBAL_GET_instr(v_globalidx))
    -- wf_uN: `%%`(32, v_globalidx)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_23{v_globalidx : globalidx}:
    `%`(GLOBAL_SET_instr(v_globalidx))
    -- wf_uN: `%%`(32, v_globalidx)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_24{v_valtype : valtype, var_0_opt : loadop_?, v_memarg : memarg}:
    `%`(LOAD_instr(v_valtype, var_0_opt, v_memarg))
    -- (wf_loadop_: `%%`(v_valtype, var_0))?{var_0 <- var_0_opt}
    -- wf_memarg: `%`(v_memarg)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_25{Inn_opt : Inn?, v_valtype : valtype, sz_opt : sz?, v_memarg : memarg}:
    `%`(STORE_instr(v_valtype, sz_opt, v_memarg))
    -- (wf_sz: `%`(v_sz))?{v_sz <- sz_opt}
    -- wf_memarg: `%`(v_memarg)
    -- if ((Inn_opt = ?()) <=> (sz_opt = ?()))
    -- (if ((v_valtype = $valtype_Inn(v_Inn)) /\ ($proj_sz_0(v_sz).0 < $size($valtype_Inn(v_Inn)))))?{v_Inn <- Inn_opt, v_sz <- sz_opt}

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_26:
    `%`(MEMORY_SIZE_instr)

  ;; ../specification/wasm-1.0/1-syntax.spectec:245.8-245.13
  rule instr_case_27:
    `%`(MEMORY_GROW_instr)
}

;; ../specification/wasm-1.0/1-syntax.spectec:252.1-253.9
syntax expr = instr*

;; ../specification/wasm-1.0/1-syntax.spectec:263.1-264.16
syntax type = 
  | TYPE(v_functype : functype)

;; ../specification/wasm-1.0/1-syntax.spectec:265.1-266.16
syntax local = 
  | LOCAL(v_valtype : valtype)

;; ../specification/wasm-1.0/1-syntax.spectec:267.1-268.27
syntax func = 
  | FUNC(v_typeidx : typeidx, local_lst : local*, v_expr : expr)

;; ../specification/wasm-1.0/1-syntax.spectec:267.8-267.12
relation wf_func: `%`(func)
  ;; ../specification/wasm-1.0/1-syntax.spectec:267.8-267.12
  rule func_case_0{v_typeidx : typeidx, local_lst : local*, v_expr : expr}:
    `%`(FUNC_func(v_typeidx, local_lst, v_expr))
    -- wf_uN: `%%`(32, v_typeidx)
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}

;; ../specification/wasm-1.0/1-syntax.spectec:269.1-270.25
syntax global = 
  | GLOBAL(v_globaltype : globaltype, v_expr : expr)

;; ../specification/wasm-1.0/1-syntax.spectec:269.8-269.14
relation wf_global: `%`(global)
  ;; ../specification/wasm-1.0/1-syntax.spectec:269.8-269.14
  rule global_case_0{v_globaltype : globaltype, v_expr : expr}:
    `%`(GLOBAL_global(v_globaltype, v_expr))
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}

;; ../specification/wasm-1.0/1-syntax.spectec:271.1-272.18
syntax table = 
  | TABLE(v_tabletype : tabletype)

;; ../specification/wasm-1.0/1-syntax.spectec:271.8-271.13
relation wf_table: `%`(table)
  ;; ../specification/wasm-1.0/1-syntax.spectec:271.8-271.13
  rule table_case_0{v_tabletype : tabletype}:
    `%`(TABLE_table(v_tabletype))
    -- wf_limits: `%`(v_tabletype)

;; ../specification/wasm-1.0/1-syntax.spectec:273.1-274.17
syntax mem = 
  | MEMORY(v_memtype : memtype)

;; ../specification/wasm-1.0/1-syntax.spectec:273.8-273.11
relation wf_mem: `%`(mem)
  ;; ../specification/wasm-1.0/1-syntax.spectec:273.8-273.11
  rule mem_case_0{v_memtype : memtype}:
    `%`(MEMORY_mem(v_memtype))
    -- wf_limits: `%`(v_memtype)

;; ../specification/wasm-1.0/1-syntax.spectec:275.1-276.21
syntax elem = 
  | ELEM(v_expr : expr, funcidx_lst : funcidx*)

;; ../specification/wasm-1.0/1-syntax.spectec:275.8-275.12
relation wf_elem: `%`(elem)
  ;; ../specification/wasm-1.0/1-syntax.spectec:275.8-275.12
  rule elem_case_0{v_expr : expr, funcidx_lst : funcidx*}:
    `%`(ELEM_elem(v_expr, funcidx_lst))
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}
    -- (wf_uN: `%%`(32, v_funcidx))*{v_funcidx <- funcidx_lst}

;; ../specification/wasm-1.0/1-syntax.spectec:277.1-278.18
syntax data = 
  | DATA(v_expr : expr, byte_lst : byte*)

;; ../specification/wasm-1.0/1-syntax.spectec:277.8-277.12
relation wf_data: `%`(data)
  ;; ../specification/wasm-1.0/1-syntax.spectec:277.8-277.12
  rule data_case_0{v_expr : expr, byte_lst : byte*}:
    `%`(DATA_data(v_expr, byte_lst))
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}
    -- (wf_byte: `%`(v_byte))*{v_byte <- byte_lst}

;; ../specification/wasm-1.0/1-syntax.spectec:279.1-280.16
syntax start = 
  | START(v_funcidx : funcidx)

;; ../specification/wasm-1.0/1-syntax.spectec:279.8-279.13
relation wf_start: `%`(start)
  ;; ../specification/wasm-1.0/1-syntax.spectec:279.8-279.13
  rule start_case_0{v_funcidx : funcidx}:
    `%`(START_start(v_funcidx))
    -- wf_uN: `%%`(32, v_funcidx)

;; ../specification/wasm-1.0/1-syntax.spectec:282.1-283.66
syntax externidx = 
  | FUNC(v_funcidx : funcidx)
  | GLOBAL(v_globalidx : globalidx)
  | TABLE(v_tableidx : tableidx)
  | MEM(v_memidx : memidx)

;; ../specification/wasm-1.0/1-syntax.spectec:282.8-282.17
relation wf_externidx: `%`(externidx)
  ;; ../specification/wasm-1.0/1-syntax.spectec:282.8-282.17
  rule externidx_case_0{v_funcidx : funcidx}:
    `%`(FUNC_externidx(v_funcidx))
    -- wf_uN: `%%`(32, v_funcidx)

  ;; ../specification/wasm-1.0/1-syntax.spectec:282.8-282.17
  rule externidx_case_1{v_globalidx : globalidx}:
    `%`(GLOBAL_externidx(v_globalidx))
    -- wf_uN: `%%`(32, v_globalidx)

  ;; ../specification/wasm-1.0/1-syntax.spectec:282.8-282.17
  rule externidx_case_2{v_tableidx : tableidx}:
    `%`(TABLE_externidx(v_tableidx))
    -- wf_uN: `%%`(32, v_tableidx)

  ;; ../specification/wasm-1.0/1-syntax.spectec:282.8-282.17
  rule externidx_case_3{v_memidx : memidx}:
    `%`(MEM_externidx(v_memidx))
    -- wf_uN: `%%`(32, v_memidx)

;; ../specification/wasm-1.0/1-syntax.spectec:284.1-285.24
syntax export = 
  | EXPORT(v_name : name, v_externidx : externidx)

;; ../specification/wasm-1.0/1-syntax.spectec:284.8-284.14
relation wf_export: `%`(export)
  ;; ../specification/wasm-1.0/1-syntax.spectec:284.8-284.14
  rule export_case_0{v_name : name, v_externidx : externidx}:
    `%`(EXPORT_export(v_name, v_externidx))
    -- wf_name: `%`(v_name)
    -- wf_externidx: `%`(v_externidx)

;; ../specification/wasm-1.0/1-syntax.spectec:286.1-287.30
syntax import = 
  | IMPORT(v_name : name, v_name : name, v_externtype : externtype)

;; ../specification/wasm-1.0/1-syntax.spectec:286.8-286.14
relation wf_import: `%`(import)
  ;; ../specification/wasm-1.0/1-syntax.spectec:286.8-286.14
  rule import_case_0{v_name : name, name_0 : name, v_externtype : externtype}:
    `%`(IMPORT_import(v_name, name_0, v_externtype))
    -- wf_name: `%`(v_name)
    -- wf_name: `%`(name_0)
    -- wf_externtype: `%`(v_externtype)

;; ../specification/wasm-1.0/1-syntax.spectec:289.1-290.76
syntax module = 
  | MODULE(type_lst : type*, import_lst : import*, func_lst : func*, global_lst : global*, table_lst : table*, mem_lst : mem*, elem_lst : elem*, data_lst : data*, start_opt : start?, export_lst : export*)

;; ../specification/wasm-1.0/1-syntax.spectec:289.8-289.14
relation wf_module: `%`(module)
  ;; ../specification/wasm-1.0/1-syntax.spectec:289.8-289.14
  rule module_case_0{type_lst : type*, import_lst : import*, func_lst : func*, global_lst : global*, table_lst : table*, mem_lst : mem*, elem_lst : elem*, data_lst : data*, start_opt : start?, export_lst : export*}:
    `%`(MODULE_module(type_lst, import_lst, func_lst, global_lst, table_lst, mem_lst, elem_lst, data_lst, start_opt, export_lst))
    -- (wf_import: `%`(v_import))*{v_import <- import_lst}
    -- (wf_func: `%`(v_func))*{v_func <- func_lst}
    -- (wf_global: `%`(v_global))*{v_global <- global_lst}
    -- (wf_table: `%`(v_table))*{v_table <- table_lst}
    -- (wf_mem: `%`(v_mem))*{v_mem <- mem_lst}
    -- (wf_elem: `%`(v_elem))*{v_elem <- elem_lst}
    -- (wf_data: `%`(v_data))*{v_data <- data_lst}
    -- (wf_start: `%`(v_start))?{v_start <- start_opt}
    -- (wf_export: `%`(v_export))*{v_export <- export_lst}

;; ../specification/wasm-1.0/2-syntax-aux.spectec:20.1-20.64
rec {

;; ../specification/wasm-1.0/2-syntax-aux.spectec:20.6-20.14
relation fun_funcsxt: `%%`(externtype*, functype*)
  ;; ../specification/wasm-1.0/2-syntax-aux.spectec:20.6-20.14
  rule fun_funcsxt_case_0:
    `%%`([], [])

  ;; ../specification/wasm-1.0/2-syntax-aux.spectec:20.6-20.14
  rule fun_funcsxt_case_1{ft : functype, xt_lst : externtype*, var_0 : functype*}:
    `%%`([FUNC_externtype(ft)] ++ xt_lst, [ft] ++ var_0)
    -- fun_funcsxt: `%%`(xt_lst, var_0)

  ;; ../specification/wasm-1.0/2-syntax-aux.spectec:20.6-20.14
  rule fun_funcsxt_case_2{v_externtype : externtype, xt_lst : externtype*, var_0 : functype*}:
    `%%`([v_externtype] ++ xt_lst, var_0)
    -- fun_funcsxt: `%%`(xt_lst, var_0)
}

;; ../specification/wasm-1.0/2-syntax-aux.spectec:21.1-21.66
rec {

;; ../specification/wasm-1.0/2-syntax-aux.spectec:21.6-21.16
relation fun_globalsxt: `%%`(externtype*, globaltype*)
  ;; ../specification/wasm-1.0/2-syntax-aux.spectec:21.6-21.16
  rule fun_globalsxt_case_0:
    `%%`([], [])

  ;; ../specification/wasm-1.0/2-syntax-aux.spectec:21.6-21.16
  rule fun_globalsxt_case_1{gt : globaltype, xt_lst : externtype*, var_0 : globaltype*}:
    `%%`([GLOBAL_externtype(gt)] ++ xt_lst, [gt] ++ var_0)
    -- fun_globalsxt: `%%`(xt_lst, var_0)

  ;; ../specification/wasm-1.0/2-syntax-aux.spectec:21.6-21.16
  rule fun_globalsxt_case_2{v_externtype : externtype, xt_lst : externtype*, var_0 : globaltype*}:
    `%%`([v_externtype] ++ xt_lst, var_0)
    -- fun_globalsxt: `%%`(xt_lst, var_0)
}

;; ../specification/wasm-1.0/2-syntax-aux.spectec:22.1-22.65
rec {

;; ../specification/wasm-1.0/2-syntax-aux.spectec:22.6-22.15
relation fun_tablesxt: `%%`(externtype*, tabletype*)
  ;; ../specification/wasm-1.0/2-syntax-aux.spectec:22.6-22.15
  rule fun_tablesxt_case_0:
    `%%`([], [])

  ;; ../specification/wasm-1.0/2-syntax-aux.spectec:22.6-22.15
  rule fun_tablesxt_case_1{tt : limits, xt_lst : externtype*, var_1 : tabletype*, var_0 : tabletype*}:
    `%%`([TABLE_externtype(tt)] ++ xt_lst, [tt] ++ var_0)
    -- fun_tablesxt: `%%`(xt_lst, var_1)
    -- fun_tablesxt: `%%`(xt_lst, var_0)
    -- (wf_limits: `%`(iter_3))*{iter_3 <- var_1}

  ;; ../specification/wasm-1.0/2-syntax-aux.spectec:22.6-22.15
  rule fun_tablesxt_case_2{v_externtype : externtype, xt_lst : externtype*, var_1 : tabletype*, var_0 : tabletype*}:
    `%%`([v_externtype] ++ xt_lst, var_0)
    -- fun_tablesxt: `%%`(xt_lst, var_1)
    -- fun_tablesxt: `%%`(xt_lst, var_0)
    -- (wf_limits: `%`(iter_4))*{iter_4 <- var_1}
}

;; ../specification/wasm-1.0/2-syntax-aux.spectec:23.1-23.63
rec {

;; ../specification/wasm-1.0/2-syntax-aux.spectec:23.6-23.13
relation fun_memsxt: `%%`(externtype*, memtype*)
  ;; ../specification/wasm-1.0/2-syntax-aux.spectec:23.6-23.13
  rule fun_memsxt_case_0:
    `%%`([], [])

  ;; ../specification/wasm-1.0/2-syntax-aux.spectec:23.6-23.13
  rule fun_memsxt_case_1{mt : limits, xt_lst : externtype*, var_1 : memtype*, var_0 : memtype*}:
    `%%`([MEM_externtype(mt)] ++ xt_lst, [mt] ++ var_0)
    -- fun_memsxt: `%%`(xt_lst, var_1)
    -- fun_memsxt: `%%`(xt_lst, var_0)
    -- (wf_limits: `%`(iter_5))*{iter_5 <- var_1}

  ;; ../specification/wasm-1.0/2-syntax-aux.spectec:23.6-23.13
  rule fun_memsxt_case_2{v_externtype : externtype, xt_lst : externtype*, var_1 : memtype*, var_0 : memtype*}:
    `%%`([v_externtype] ++ xt_lst, var_0)
    -- fun_memsxt: `%%`(xt_lst, var_1)
    -- fun_memsxt: `%%`(xt_lst, var_0)
    -- (wf_limits: `%`(iter_6))*{iter_6 <- var_1}
}

;; ../specification/wasm-1.0/2-syntax-aux.spectec:49.6-49.13
relation fun_memarg0: `%`(memarg)
  ;; ../specification/wasm-1.0/2-syntax-aux.spectec:49.6-49.13
  rule fun_memarg0_case_0:
    `%`({ALIGN mk_uN_u32(0), OFFSET mk_uN_u32(0)})
    -- wf_memarg: `%`({ALIGN mk_uN_u32(0), OFFSET mk_uN_u32(0)})

;; ../specification/wasm-1.0/3-numerics.spectec:7.1-7.22
def $bool(v_bool : bool) : nat
  ;; ../specification/wasm-1.0/3-numerics.spectec:8.1-8.21
  def $bool(false) = 0
  ;; ../specification/wasm-1.0/3-numerics.spectec:9.1-9.20
  def $bool(true) = 1

;; ../specification/wasm-1.0/3-numerics.spectec:11.1-11.23
def $truncz(rat : rat) : int

;; ../specification/wasm-1.0/3-numerics.spectec:18.6-18.14
relation fun_signed_: `%%%`(N, nat, int)
  ;; ../specification/wasm-1.0/3-numerics.spectec:18.6-18.14
  rule fun_signed__case_0{v_N : nat, i : nat}:
    `%%%`(v_N, i, (i : nat <:> int))
    -- if (i < (2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:18.6-18.14
  rule fun_signed__case_1{v_N : nat, i : nat}:
    `%%%`(v_N, i, ((i : nat <:> int) - ((2 ^ v_N) : nat <:> int)))
    -- if (((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) <= i) /\ (i < (2 ^ v_N)))

;; ../specification/wasm-1.0/3-numerics.spectec:22.6-22.18
relation fun_inv_signed_: `%%%`(N, int, nat)
  ;; ../specification/wasm-1.0/3-numerics.spectec:22.6-22.18
  rule fun_inv_signed__case_0{v_N : nat, i : int}:
    `%%%`(v_N, i, (i : int <:> nat))
    -- if (((0 : nat <:> int) <= i) /\ (i < ((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:22.6-22.18
  rule fun_inv_signed__case_1{v_N : nat, i : int}:
    `%%%`(v_N, i, ((i + ((2 ^ v_N) : nat <:> int)) : int <:> nat))
    -- if ((- ((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) <= i) /\ (i < (0 : nat <:> int)))

;; ../specification/wasm-1.0/3-numerics.spectec:152.1-152.30
def $fabs_(v_N : N, v_fN : fN) : fN*

;; ../specification/wasm-1.0/3-numerics.spectec:155.1-155.31
def $fceil_(v_N : N, v_fN : fN) : fN*

;; ../specification/wasm-1.0/3-numerics.spectec:156.1-156.32
def $ffloor_(v_N : N, v_fN : fN) : fN*

;; ../specification/wasm-1.0/3-numerics.spectec:158.1-158.34
def $fnearest_(v_N : N, v_fN : fN) : fN*

;; ../specification/wasm-1.0/3-numerics.spectec:153.1-153.30
def $fneg_(v_N : N, v_fN : fN) : fN*

;; ../specification/wasm-1.0/3-numerics.spectec:154.1-154.31
def $fsqrt_(v_N : N, v_fN : fN) : fN*

;; ../specification/wasm-1.0/3-numerics.spectec:157.1-157.32
def $ftrunc_(v_N : N, v_fN : fN) : fN*

;; ../specification/wasm-1.0/3-numerics.spectec:86.1-86.29
def $iclz_(v_N : N, v_iN : iN) : iN

;; ../specification/wasm-1.0/3-numerics.spectec:87.1-87.29
def $ictz_(v_N : N, v_iN : iN) : iN

;; ../specification/wasm-1.0/3-numerics.spectec:88.1-88.32
def $ipopcnt_(v_N : N, v_iN : iN) : iN

;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
relation fun_unop__before_fun_unop__case_20: `%%%`(valtype, unop_, val_)
  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_19{v_fN : fN}:
    `%%%`(F64_valtype, mk_unop__1_unop_(F64_Fnn, NEAREST_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_20))*{iter_20 <- $fnearest_($size($valtype_Fnn(F64_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_27)))*{iter_0_27 <- $fnearest_($size($valtype_Fnn(F64_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_18{v_fN : fN}:
    `%%%`(F32_valtype, mk_unop__1_unop_(F32_Fnn, NEAREST_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_19))*{iter_19 <- $fnearest_($size($valtype_Fnn(F32_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_25)))*{iter_0_25 <- $fnearest_($size($valtype_Fnn(F32_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_17{v_fN : fN}:
    `%%%`(F64_valtype, mk_unop__1_unop_(F64_Fnn, TRUNC_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_18))*{iter_18 <- $ftrunc_($size($valtype_Fnn(F64_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_23)))*{iter_0_23 <- $ftrunc_($size($valtype_Fnn(F64_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_16{v_fN : fN}:
    `%%%`(F32_valtype, mk_unop__1_unop_(F32_Fnn, TRUNC_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_17))*{iter_17 <- $ftrunc_($size($valtype_Fnn(F32_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_21)))*{iter_0_21 <- $ftrunc_($size($valtype_Fnn(F32_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_15{v_fN : fN}:
    `%%%`(F64_valtype, mk_unop__1_unop_(F64_Fnn, FLOOR_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_16))*{iter_16 <- $ffloor_($size($valtype_Fnn(F64_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_19)))*{iter_0_19 <- $ffloor_($size($valtype_Fnn(F64_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_14{v_fN : fN}:
    `%%%`(F32_valtype, mk_unop__1_unop_(F32_Fnn, FLOOR_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_15))*{iter_15 <- $ffloor_($size($valtype_Fnn(F32_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_17)))*{iter_0_17 <- $ffloor_($size($valtype_Fnn(F32_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_13{v_fN : fN}:
    `%%%`(F64_valtype, mk_unop__1_unop_(F64_Fnn, CEIL_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_14))*{iter_14 <- $fceil_($size($valtype_Fnn(F64_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_15)))*{iter_0_15 <- $fceil_($size($valtype_Fnn(F64_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_12{v_fN : fN}:
    `%%%`(F32_valtype, mk_unop__1_unop_(F32_Fnn, CEIL_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_13))*{iter_13 <- $fceil_($size($valtype_Fnn(F32_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_13)))*{iter_0_13 <- $fceil_($size($valtype_Fnn(F32_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_11{v_fN : fN}:
    `%%%`(F64_valtype, mk_unop__1_unop_(F64_Fnn, SQRT_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_12))*{iter_12 <- $fsqrt_($size($valtype_Fnn(F64_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_11)))*{iter_0_11 <- $fsqrt_($size($valtype_Fnn(F64_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_10{v_fN : fN}:
    `%%%`(F32_valtype, mk_unop__1_unop_(F32_Fnn, SQRT_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_11))*{iter_11 <- $fsqrt_($size($valtype_Fnn(F32_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_9)))*{iter_0_9 <- $fsqrt_($size($valtype_Fnn(F32_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_9{v_fN : fN}:
    `%%%`(F64_valtype, mk_unop__1_unop_(F64_Fnn, NEG_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_10))*{iter_10 <- $fneg_($size($valtype_Fnn(F64_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_7)))*{iter_0_7 <- $fneg_($size($valtype_Fnn(F64_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_8{v_fN : fN}:
    `%%%`(F32_valtype, mk_unop__1_unop_(F32_Fnn, NEG_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_9))*{iter_9 <- $fneg_($size($valtype_Fnn(F32_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_5)))*{iter_0_5 <- $fneg_($size($valtype_Fnn(F32_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_7{v_fN : fN}:
    `%%%`(F64_valtype, mk_unop__1_unop_(F64_Fnn, ABS_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_8))*{iter_8 <- $fabs_($size($valtype_Fnn(F64_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_3)))*{iter_0_3 <- $fabs_($size($valtype_Fnn(F64_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_6{v_fN : fN}:
    `%%%`(F32_valtype, mk_unop__1_unop_(F32_Fnn, ABS_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_7))*{iter_7 <- $fabs_($size($valtype_Fnn(F32_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_1)))*{iter_0_1 <- $fabs_($size($valtype_Fnn(F32_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_5{v_iN : uN}:
    `%%%`(I64_valtype, mk_unop__0_unop_(I64_Inn, POPCNT_unop_Inn), mk_val__0_val_(I64_Inn, v_iN))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $ipopcnt_($size($valtype_Inn(I64_Inn)), v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_4{v_iN : uN}:
    `%%%`(I32_valtype, mk_unop__0_unop_(I32_Inn, POPCNT_unop_Inn), mk_val__0_val_(I32_Inn, v_iN))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $ipopcnt_($size($valtype_Inn(I32_Inn)), v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_3{v_iN : uN}:
    `%%%`(I64_valtype, mk_unop__0_unop_(I64_Inn, CTZ_unop_Inn), mk_val__0_val_(I64_Inn, v_iN))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $ictz_($size($valtype_Inn(I64_Inn)), v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_2{v_iN : uN}:
    `%%%`(I32_valtype, mk_unop__0_unop_(I32_Inn, CTZ_unop_Inn), mk_val__0_val_(I32_Inn, v_iN))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $ictz_($size($valtype_Inn(I32_Inn)), v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_1{v_iN : uN}:
    `%%%`(I64_valtype, mk_unop__0_unop_(I64_Inn, CLZ_unop_Inn), mk_val__0_val_(I64_Inn, v_iN))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $iclz_($size($valtype_Inn(I64_Inn)), v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_0{v_iN : uN}:
    `%%%`(I32_valtype, mk_unop__0_unop_(I32_Inn, CLZ_unop_Inn), mk_val__0_val_(I32_Inn, v_iN))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $iclz_($size($valtype_Inn(I32_Inn)), v_iN)))

;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
relation fun_unop_: `%%%%`(valtype, unop_, val_, val_*?)
  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_0{v_iN : uN}:
    `%%%%`(I32_valtype, mk_unop__0_unop_(I32_Inn, CLZ_unop_Inn), mk_val__0_val_(I32_Inn, v_iN), ?([mk_val__0_val_(I32_Inn, $iclz_($size($valtype_Inn(I32_Inn)), v_iN))]))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $iclz_($size($valtype_Inn(I32_Inn)), v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_1{v_iN : uN}:
    `%%%%`(I64_valtype, mk_unop__0_unop_(I64_Inn, CLZ_unop_Inn), mk_val__0_val_(I64_Inn, v_iN), ?([mk_val__0_val_(I64_Inn, $iclz_($size($valtype_Inn(I64_Inn)), v_iN))]))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $iclz_($size($valtype_Inn(I64_Inn)), v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_2{v_iN : uN}:
    `%%%%`(I32_valtype, mk_unop__0_unop_(I32_Inn, CTZ_unop_Inn), mk_val__0_val_(I32_Inn, v_iN), ?([mk_val__0_val_(I32_Inn, $ictz_($size($valtype_Inn(I32_Inn)), v_iN))]))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $ictz_($size($valtype_Inn(I32_Inn)), v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_3{v_iN : uN}:
    `%%%%`(I64_valtype, mk_unop__0_unop_(I64_Inn, CTZ_unop_Inn), mk_val__0_val_(I64_Inn, v_iN), ?([mk_val__0_val_(I64_Inn, $ictz_($size($valtype_Inn(I64_Inn)), v_iN))]))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $ictz_($size($valtype_Inn(I64_Inn)), v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_4{v_iN : uN}:
    `%%%%`(I32_valtype, mk_unop__0_unop_(I32_Inn, POPCNT_unop_Inn), mk_val__0_val_(I32_Inn, v_iN), ?([mk_val__0_val_(I32_Inn, $ipopcnt_($size($valtype_Inn(I32_Inn)), v_iN))]))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $ipopcnt_($size($valtype_Inn(I32_Inn)), v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_5{v_iN : uN}:
    `%%%%`(I64_valtype, mk_unop__0_unop_(I64_Inn, POPCNT_unop_Inn), mk_val__0_val_(I64_Inn, v_iN), ?([mk_val__0_val_(I64_Inn, $ipopcnt_($size($valtype_Inn(I64_Inn)), v_iN))]))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $ipopcnt_($size($valtype_Inn(I64_Inn)), v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_6{v_fN : fN}:
    `%%%%`(F32_valtype, mk_unop__1_unop_(F32_Fnn, ABS_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN), ?(mk_val__1_val_(F32_Fnn, iter_0_2)*{iter_0_2 <- $fabs_($size($valtype_Fnn(F32_Fnn)), v_fN)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_7))*{iter_7 <- $fabs_($size($valtype_Fnn(F32_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_1)))*{iter_0_1 <- $fabs_($size($valtype_Fnn(F32_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_7{v_fN : fN}:
    `%%%%`(F64_valtype, mk_unop__1_unop_(F64_Fnn, ABS_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN), ?(mk_val__1_val_(F64_Fnn, iter_0_4)*{iter_0_4 <- $fabs_($size($valtype_Fnn(F64_Fnn)), v_fN)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_8))*{iter_8 <- $fabs_($size($valtype_Fnn(F64_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_3)))*{iter_0_3 <- $fabs_($size($valtype_Fnn(F64_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_8{v_fN : fN}:
    `%%%%`(F32_valtype, mk_unop__1_unop_(F32_Fnn, NEG_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN), ?(mk_val__1_val_(F32_Fnn, iter_0_6)*{iter_0_6 <- $fneg_($size($valtype_Fnn(F32_Fnn)), v_fN)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_9))*{iter_9 <- $fneg_($size($valtype_Fnn(F32_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_5)))*{iter_0_5 <- $fneg_($size($valtype_Fnn(F32_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_9{v_fN : fN}:
    `%%%%`(F64_valtype, mk_unop__1_unop_(F64_Fnn, NEG_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN), ?(mk_val__1_val_(F64_Fnn, iter_0_8)*{iter_0_8 <- $fneg_($size($valtype_Fnn(F64_Fnn)), v_fN)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_10))*{iter_10 <- $fneg_($size($valtype_Fnn(F64_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_7)))*{iter_0_7 <- $fneg_($size($valtype_Fnn(F64_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_10{v_fN : fN}:
    `%%%%`(F32_valtype, mk_unop__1_unop_(F32_Fnn, SQRT_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN), ?(mk_val__1_val_(F32_Fnn, iter_0_10)*{iter_0_10 <- $fsqrt_($size($valtype_Fnn(F32_Fnn)), v_fN)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_11))*{iter_11 <- $fsqrt_($size($valtype_Fnn(F32_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_9)))*{iter_0_9 <- $fsqrt_($size($valtype_Fnn(F32_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_11{v_fN : fN}:
    `%%%%`(F64_valtype, mk_unop__1_unop_(F64_Fnn, SQRT_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN), ?(mk_val__1_val_(F64_Fnn, iter_0_12)*{iter_0_12 <- $fsqrt_($size($valtype_Fnn(F64_Fnn)), v_fN)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_12))*{iter_12 <- $fsqrt_($size($valtype_Fnn(F64_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_11)))*{iter_0_11 <- $fsqrt_($size($valtype_Fnn(F64_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_12{v_fN : fN}:
    `%%%%`(F32_valtype, mk_unop__1_unop_(F32_Fnn, CEIL_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN), ?(mk_val__1_val_(F32_Fnn, iter_0_14)*{iter_0_14 <- $fceil_($size($valtype_Fnn(F32_Fnn)), v_fN)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_13))*{iter_13 <- $fceil_($size($valtype_Fnn(F32_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_13)))*{iter_0_13 <- $fceil_($size($valtype_Fnn(F32_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_13{v_fN : fN}:
    `%%%%`(F64_valtype, mk_unop__1_unop_(F64_Fnn, CEIL_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN), ?(mk_val__1_val_(F64_Fnn, iter_0_16)*{iter_0_16 <- $fceil_($size($valtype_Fnn(F64_Fnn)), v_fN)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_14))*{iter_14 <- $fceil_($size($valtype_Fnn(F64_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_15)))*{iter_0_15 <- $fceil_($size($valtype_Fnn(F64_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_14{v_fN : fN}:
    `%%%%`(F32_valtype, mk_unop__1_unop_(F32_Fnn, FLOOR_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN), ?(mk_val__1_val_(F32_Fnn, iter_0_18)*{iter_0_18 <- $ffloor_($size($valtype_Fnn(F32_Fnn)), v_fN)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_15))*{iter_15 <- $ffloor_($size($valtype_Fnn(F32_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_17)))*{iter_0_17 <- $ffloor_($size($valtype_Fnn(F32_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_15{v_fN : fN}:
    `%%%%`(F64_valtype, mk_unop__1_unop_(F64_Fnn, FLOOR_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN), ?(mk_val__1_val_(F64_Fnn, iter_0_20)*{iter_0_20 <- $ffloor_($size($valtype_Fnn(F64_Fnn)), v_fN)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_16))*{iter_16 <- $ffloor_($size($valtype_Fnn(F64_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_19)))*{iter_0_19 <- $ffloor_($size($valtype_Fnn(F64_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_16{v_fN : fN}:
    `%%%%`(F32_valtype, mk_unop__1_unop_(F32_Fnn, TRUNC_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN), ?(mk_val__1_val_(F32_Fnn, iter_0_22)*{iter_0_22 <- $ftrunc_($size($valtype_Fnn(F32_Fnn)), v_fN)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_17))*{iter_17 <- $ftrunc_($size($valtype_Fnn(F32_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_21)))*{iter_0_21 <- $ftrunc_($size($valtype_Fnn(F32_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_17{v_fN : fN}:
    `%%%%`(F64_valtype, mk_unop__1_unop_(F64_Fnn, TRUNC_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN), ?(mk_val__1_val_(F64_Fnn, iter_0_24)*{iter_0_24 <- $ftrunc_($size($valtype_Fnn(F64_Fnn)), v_fN)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_18))*{iter_18 <- $ftrunc_($size($valtype_Fnn(F64_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_23)))*{iter_0_23 <- $ftrunc_($size($valtype_Fnn(F64_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_18{v_fN : fN}:
    `%%%%`(F32_valtype, mk_unop__1_unop_(F32_Fnn, NEAREST_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN), ?(mk_val__1_val_(F32_Fnn, iter_0_26)*{iter_0_26 <- $fnearest_($size($valtype_Fnn(F32_Fnn)), v_fN)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_19))*{iter_19 <- $fnearest_($size($valtype_Fnn(F32_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_25)))*{iter_0_25 <- $fnearest_($size($valtype_Fnn(F32_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_19{v_fN : fN}:
    `%%%%`(F64_valtype, mk_unop__1_unop_(F64_Fnn, NEAREST_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN), ?(mk_val__1_val_(F64_Fnn, iter_0_28)*{iter_0_28 <- $fnearest_($size($valtype_Fnn(F64_Fnn)), v_fN)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_20))*{iter_20 <- $fnearest_($size($valtype_Fnn(F64_Fnn)), v_fN)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_27)))*{iter_0_27 <- $fnearest_($size($valtype_Fnn(F64_Fnn)), v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12
  rule fun_unop__case_20{x0 : valtype, x1 : unop_, x2 : val_}:
    `%%%%`(x0, x1, x2, ?())
    -- ~ fun_unop__before_fun_unop__case_20: `%%%`(x0, x1, x2)

;; ../specification/wasm-1.0/3-numerics.spectec:145.1-145.37
def $fadd_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; ../specification/wasm-1.0/3-numerics.spectec:151.1-151.42
def $fcopysign_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; ../specification/wasm-1.0/3-numerics.spectec:148.1-148.37
def $fdiv_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; ../specification/wasm-1.0/3-numerics.spectec:150.1-150.37
def $fmax_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; ../specification/wasm-1.0/3-numerics.spectec:149.1-149.37
def $fmin_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; ../specification/wasm-1.0/3-numerics.spectec:147.1-147.37
def $fmul_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; ../specification/wasm-1.0/3-numerics.spectec:146.1-146.37
def $fsub_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; ../specification/wasm-1.0/3-numerics.spectec:73.6-73.12
relation fun_iadd_: `%%%%`(N, iN, iN, iN)
  ;; ../specification/wasm-1.0/3-numerics.spectec:73.6-73.12
  rule fun_iadd__case_0{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%`(v_N, i_1, i_2, mk_uN_iN((($proj_uN_0(i_1).0 + $proj_uN_0(i_2).0) \ (2 ^ v_N))))
    -- wf_uN: `%%`(v_N, mk_uN_uN((($proj_uN_0(i_1).0 + $proj_uN_0(i_2).0) \ (2 ^ v_N))))

;; ../specification/wasm-1.0/3-numerics.spectec:79.1-79.36
def $iand_(v_N : N, v_iN : iN, iN_0 : iN) : iN

;; ../specification/wasm-1.0/3-numerics.spectec:76.6-76.12
relation fun_idiv_: `%%%%%`(N, sx, iN, iN, iN?)
  ;; ../specification/wasm-1.0/3-numerics.spectec:76.6-76.12
  rule fun_idiv__case_0{v_N : nat, i_1 : uN}:
    `%%%%%`(v_N, U_sx, i_1, mk_uN_iN(0), ?())

  ;; ../specification/wasm-1.0/3-numerics.spectec:76.6-76.12
  rule fun_idiv__case_1{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%%`(v_N, U_sx, i_1, i_2, ?(mk_uN_iN(($truncz((($proj_uN_0(i_1).0 : nat <:> rat) / ($proj_uN_0(i_2).0 : nat <:> rat))) : int <:> nat))))
    -- wf_uN: `%%`(v_N, mk_uN_uN(($truncz((($proj_uN_0(i_1).0 : nat <:> rat) / ($proj_uN_0(i_2).0 : nat <:> rat))) : int <:> nat)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:76.6-76.12
  rule fun_idiv__case_2{v_N : nat, i_1 : uN}:
    `%%%%%`(v_N, S_sx, i_1, mk_uN_iN(0), ?())

  ;; ../specification/wasm-1.0/3-numerics.spectec:76.6-76.12
  rule fun_idiv__case_3{v_N : nat, i_1 : uN, i_2 : uN, var_1 : int, var_0 : int}:
    `%%%%%`(v_N, S_sx, i_1, i_2, ?())
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_1)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)
    -- if (((var_0 : int <:> rat) / (var_1 : int <:> rat)) = ((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> rat))

  ;; ../specification/wasm-1.0/3-numerics.spectec:76.6-76.12
  rule fun_idiv__case_4{v_N : nat, i_1 : uN, i_2 : uN, var_2 : int, var_1 : int, var_0 : nat}:
    `%%%%%`(v_N, S_sx, i_1, i_2, ?(mk_uN_iN(var_0)))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_2)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_1)
    -- fun_inv_signed_: `%%%`(v_N, $truncz(((var_1 : int <:> rat) / (var_2 : int <:> rat))), var_0)
    -- wf_uN: `%%`(v_N, mk_uN_uN(var_0))

;; ../specification/wasm-1.0/3-numerics.spectec:75.6-75.12
relation fun_imul_: `%%%%`(N, iN, iN, iN)
  ;; ../specification/wasm-1.0/3-numerics.spectec:75.6-75.12
  rule fun_imul__case_0{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%`(v_N, i_1, i_2, mk_uN_iN((($proj_uN_0(i_1).0 * $proj_uN_0(i_2).0) \ (2 ^ v_N))))
    -- wf_uN: `%%`(v_N, mk_uN_uN((($proj_uN_0(i_1).0 * $proj_uN_0(i_2).0) \ (2 ^ v_N))))

;; ../specification/wasm-1.0/3-numerics.spectec:80.1-80.35
def $ior_(v_N : N, v_iN : iN, iN_0 : iN) : iN

;; ../specification/wasm-1.0/3-numerics.spectec:77.6-77.12
relation fun_irem_: `%%%%%`(N, sx, iN, iN, iN?)
  ;; ../specification/wasm-1.0/3-numerics.spectec:77.6-77.12
  rule fun_irem__case_0{v_N : nat, i_1 : uN}:
    `%%%%%`(v_N, U_sx, i_1, mk_uN_iN(0), ?())

  ;; ../specification/wasm-1.0/3-numerics.spectec:77.6-77.12
  rule fun_irem__case_1{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%%`(v_N, U_sx, i_1, i_2, ?(mk_uN_iN(((($proj_uN_0(i_1).0 : nat <:> int) - (($proj_uN_0(i_2).0 * ($truncz((($proj_uN_0(i_1).0 : nat <:> rat) / ($proj_uN_0(i_2).0 : nat <:> rat))) : int <:> nat)) : nat <:> int)) : int <:> nat))))
    -- wf_uN: `%%`(v_N, mk_uN_uN(((($proj_uN_0(i_1).0 : nat <:> int) - (($proj_uN_0(i_2).0 * ($truncz((($proj_uN_0(i_1).0 : nat <:> rat) / ($proj_uN_0(i_2).0 : nat <:> rat))) : int <:> nat)) : nat <:> int)) : int <:> nat)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:77.6-77.12
  rule fun_irem__case_2{v_N : nat, i_1 : uN}:
    `%%%%%`(v_N, S_sx, i_1, mk_uN_iN(0), ?())

  ;; ../specification/wasm-1.0/3-numerics.spectec:77.6-77.12
  rule fun_irem__case_3{v_N : nat, i_1 : uN, i_2 : uN, j_1 : int, j_2 : int, var_2 : int, var_1 : int, var_0 : nat}:
    `%%%%%`(v_N, S_sx, i_1, i_2, ?(mk_uN_iN(var_0)))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_2)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_1)
    -- fun_inv_signed_: `%%%`(v_N, (j_1 - (j_2 * $truncz(((j_1 : int <:> rat) / (j_2 : int <:> rat))))), var_0)
    -- if ((j_1 = var_1) /\ (j_2 = var_2))
    -- wf_uN: `%%`(v_N, mk_uN_uN(var_0))

;; ../specification/wasm-1.0/3-numerics.spectec:84.1-84.37
def $irotl_(v_N : N, v_iN : iN, iN_0 : iN) : iN

;; ../specification/wasm-1.0/3-numerics.spectec:85.1-85.37
def $irotr_(v_N : N, v_iN : iN, iN_0 : iN) : iN

;; ../specification/wasm-1.0/3-numerics.spectec:82.1-82.34
def $ishl_(v_N : N, v_iN : iN, v_u32 : u32) : iN

;; ../specification/wasm-1.0/3-numerics.spectec:83.1-83.74
def $ishr_(v_N : N, v_sx : sx, v_iN : iN, v_u32 : u32) : iN

;; ../specification/wasm-1.0/3-numerics.spectec:74.6-74.12
relation fun_isub_: `%%%%`(N, iN, iN, iN)
  ;; ../specification/wasm-1.0/3-numerics.spectec:74.6-74.12
  rule fun_isub__case_0{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%`(v_N, i_1, i_2, mk_uN_iN(((((((2 ^ v_N) + $proj_uN_0(i_1).0) : nat <:> int) - ($proj_uN_0(i_2).0 : nat <:> int)) \ ((2 ^ v_N) : nat <:> int)) : int <:> nat)))
    -- wf_uN: `%%`(v_N, mk_uN_uN(((((((2 ^ v_N) + $proj_uN_0(i_1).0) : nat <:> int) - ($proj_uN_0(i_2).0 : nat <:> int)) \ ((2 ^ v_N) : nat <:> int)) : int <:> nat)))

;; ../specification/wasm-1.0/3-numerics.spectec:81.1-81.36
def $ixor_(v_N : N, v_iN : iN, iN_0 : iN) : iN

;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
relation fun_binop__before_fun_binop__case_38: `%%%%`(valtype, binop_, val_, val_)
  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_37{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, COPYSIGN_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_42))*{iter_42 <- $fcopysign_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_67)))*{iter_0_67 <- $fcopysign_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_36{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, COPYSIGN_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_41))*{iter_41 <- $fcopysign_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_65)))*{iter_0_65 <- $fcopysign_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_35{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, MAX_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_40))*{iter_40 <- $fmax_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_63)))*{iter_0_63 <- $fmax_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_34{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, MAX_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_39))*{iter_39 <- $fmax_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_61)))*{iter_0_61 <- $fmax_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_33{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, MIN_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_38))*{iter_38 <- $fmin_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_59)))*{iter_0_59 <- $fmin_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_32{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, MIN_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_37))*{iter_37 <- $fmin_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_57)))*{iter_0_57 <- $fmin_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_31{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, DIV_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_36))*{iter_36 <- $fdiv_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_55)))*{iter_0_55 <- $fdiv_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_30{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, DIV_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_35))*{iter_35 <- $fdiv_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_53)))*{iter_0_53 <- $fdiv_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_29{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, MUL_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_34))*{iter_34 <- $fmul_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_51)))*{iter_0_51 <- $fmul_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_28{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, MUL_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_33))*{iter_33 <- $fmul_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_49)))*{iter_0_49 <- $fmul_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_27{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, SUB_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_32))*{iter_32 <- $fsub_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_47)))*{iter_0_47 <- $fsub_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_26{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, SUB_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_31))*{iter_31 <- $fsub_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_45)))*{iter_0_45 <- $fsub_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_25{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, ADD_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_30))*{iter_30 <- $fadd_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_43)))*{iter_0_43 <- $fadd_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_24{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, ADD_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_29))*{iter_29 <- $fadd_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_41)))*{iter_0_41 <- $fadd_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_23{iN_1 : uN, iN_2 : uN}:
    `%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, ROTR_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $irotr_($size($valtype_Inn(I64_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_22{iN_1 : uN, iN_2 : uN}:
    `%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, ROTR_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $irotr_($size($valtype_Inn(I32_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_21{iN_1 : uN, iN_2 : uN}:
    `%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, ROTL_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $irotl_($size($valtype_Inn(I64_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_20{iN_1 : uN, iN_2 : uN}:
    `%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, ROTL_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $irotl_($size($valtype_Inn(I32_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_19{v_sx : sx, iN_1 : uN, iN_2 : uN}:
    `%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, SHR_binop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $ishr_($size($valtype_Inn(I64_Inn)), v_sx, iN_1, mk_uN_u32($proj_uN_0(iN_2).0))))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_18{v_sx : sx, iN_1 : uN, iN_2 : uN}:
    `%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, SHR_binop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $ishr_($size($valtype_Inn(I32_Inn)), v_sx, iN_1, mk_uN_u32($proj_uN_0(iN_2).0))))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_17{iN_1 : uN, iN_2 : uN}:
    `%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, SHL_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $ishl_($size($valtype_Inn(I64_Inn)), iN_1, mk_uN_u32($proj_uN_0(iN_2).0))))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_16{iN_1 : uN, iN_2 : uN}:
    `%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, SHL_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $ishl_($size($valtype_Inn(I32_Inn)), iN_1, mk_uN_u32($proj_uN_0(iN_2).0))))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_15{iN_1 : uN, iN_2 : uN}:
    `%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, XOR_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $ixor_($size($valtype_Inn(I64_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_14{iN_1 : uN, iN_2 : uN}:
    `%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, XOR_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $ixor_($size($valtype_Inn(I32_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_13{iN_1 : uN, iN_2 : uN}:
    `%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, OR_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $ior_($size($valtype_Inn(I64_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_12{iN_1 : uN, iN_2 : uN}:
    `%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, OR_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $ior_($size($valtype_Inn(I32_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_11{iN_1 : uN, iN_2 : uN}:
    `%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, AND_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $iand_($size($valtype_Inn(I64_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_10{iN_1 : uN, iN_2 : uN}:
    `%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, AND_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $iand_($size($valtype_Inn(I32_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_9{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : iN?}:
    `%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, REM_binop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- fun_irem_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)
    -- (wf_val_: `%%`($valtype_Inn(I64_Inn), iter_27))*{iter_27 <- $list_(syntax val_, mk_val__0_val_(I64_Inn, iter_0_38)?{iter_0_38 <- var_0})}
    -- (wf_uN: `%%`($size($valtype_Inn(I64_Inn)), iter_28))?{iter_28 <- var_0}
    -- (wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, iter_0_39)))?{iter_0_39 <- var_0}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_8{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : iN?}:
    `%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, REM_binop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- fun_irem_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)
    -- (wf_val_: `%%`($valtype_Inn(I32_Inn), iter_25))*{iter_25 <- $list_(syntax val_, mk_val__0_val_(I32_Inn, iter_0_35)?{iter_0_35 <- var_0})}
    -- (wf_uN: `%%`($size($valtype_Inn(I32_Inn)), iter_26))?{iter_26 <- var_0}
    -- (wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, iter_0_36)))?{iter_0_36 <- var_0}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_7{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : iN?}:
    `%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, DIV_binop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- fun_idiv_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)
    -- (wf_val_: `%%`($valtype_Inn(I64_Inn), iter_23))*{iter_23 <- $list_(syntax val_, mk_val__0_val_(I64_Inn, iter_0_32)?{iter_0_32 <- var_0})}
    -- (wf_uN: `%%`($size($valtype_Inn(I64_Inn)), iter_24))?{iter_24 <- var_0}
    -- (wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, iter_0_33)))?{iter_0_33 <- var_0}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_6{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : iN?}:
    `%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, DIV_binop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- fun_idiv_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)
    -- (wf_val_: `%%`($valtype_Inn(I32_Inn), iter_21))*{iter_21 <- $list_(syntax val_, mk_val__0_val_(I32_Inn, iter_0_29)?{iter_0_29 <- var_0})}
    -- (wf_uN: `%%`($size($valtype_Inn(I32_Inn)), iter_22))?{iter_22 <- var_0}
    -- (wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, iter_0_30)))?{iter_0_30 <- var_0}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_5{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, MUL_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- fun_imul_: `%%%%`($size($valtype_Inn(I64_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_4{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, MUL_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- fun_imul_: `%%%%`($size($valtype_Inn(I32_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_3{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, SUB_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- fun_isub_: `%%%%`($size($valtype_Inn(I64_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_2{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, SUB_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- fun_isub_: `%%%%`($size($valtype_Inn(I32_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_1{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, ADD_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- fun_iadd_: `%%%%`($size($valtype_Inn(I64_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_0{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, ADD_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- fun_iadd_: `%%%%`($size($valtype_Inn(I32_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, var_0))

;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
relation fun_binop_: `%%%%%`(valtype, binop_, val_, val_, val_*?)
  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_0{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, ADD_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?([mk_val__0_val_(I32_Inn, var_0)]))
    -- fun_iadd_: `%%%%`($size($valtype_Inn(I32_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_1{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, ADD_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?([mk_val__0_val_(I64_Inn, var_0)]))
    -- fun_iadd_: `%%%%`($size($valtype_Inn(I64_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_2{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, SUB_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?([mk_val__0_val_(I32_Inn, var_0)]))
    -- fun_isub_: `%%%%`($size($valtype_Inn(I32_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_3{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, SUB_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?([mk_val__0_val_(I64_Inn, var_0)]))
    -- fun_isub_: `%%%%`($size($valtype_Inn(I64_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_4{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, MUL_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?([mk_val__0_val_(I32_Inn, var_0)]))
    -- fun_imul_: `%%%%`($size($valtype_Inn(I32_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_5{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, MUL_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?([mk_val__0_val_(I64_Inn, var_0)]))
    -- fun_imul_: `%%%%`($size($valtype_Inn(I64_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_6{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : iN?}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, DIV_binop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?($list_(syntax val_, mk_val__0_val_(I32_Inn, iter_0_31)?{iter_0_31 <- var_0})))
    -- fun_idiv_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)
    -- (wf_val_: `%%`($valtype_Inn(I32_Inn), iter_21))*{iter_21 <- $list_(syntax val_, mk_val__0_val_(I32_Inn, iter_0_29)?{iter_0_29 <- var_0})}
    -- (wf_uN: `%%`($size($valtype_Inn(I32_Inn)), iter_22))?{iter_22 <- var_0}
    -- (wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, iter_0_30)))?{iter_0_30 <- var_0}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_7{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : iN?}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, DIV_binop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?($list_(syntax val_, mk_val__0_val_(I64_Inn, iter_0_34)?{iter_0_34 <- var_0})))
    -- fun_idiv_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)
    -- (wf_val_: `%%`($valtype_Inn(I64_Inn), iter_23))*{iter_23 <- $list_(syntax val_, mk_val__0_val_(I64_Inn, iter_0_32)?{iter_0_32 <- var_0})}
    -- (wf_uN: `%%`($size($valtype_Inn(I64_Inn)), iter_24))?{iter_24 <- var_0}
    -- (wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, iter_0_33)))?{iter_0_33 <- var_0}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_8{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : iN?}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, REM_binop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?($list_(syntax val_, mk_val__0_val_(I32_Inn, iter_0_37)?{iter_0_37 <- var_0})))
    -- fun_irem_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)
    -- (wf_val_: `%%`($valtype_Inn(I32_Inn), iter_25))*{iter_25 <- $list_(syntax val_, mk_val__0_val_(I32_Inn, iter_0_35)?{iter_0_35 <- var_0})}
    -- (wf_uN: `%%`($size($valtype_Inn(I32_Inn)), iter_26))?{iter_26 <- var_0}
    -- (wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, iter_0_36)))?{iter_0_36 <- var_0}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_9{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : iN?}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, REM_binop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?($list_(syntax val_, mk_val__0_val_(I64_Inn, iter_0_40)?{iter_0_40 <- var_0})))
    -- fun_irem_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)
    -- (wf_val_: `%%`($valtype_Inn(I64_Inn), iter_27))*{iter_27 <- $list_(syntax val_, mk_val__0_val_(I64_Inn, iter_0_38)?{iter_0_38 <- var_0})}
    -- (wf_uN: `%%`($size($valtype_Inn(I64_Inn)), iter_28))?{iter_28 <- var_0}
    -- (wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, iter_0_39)))?{iter_0_39 <- var_0}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_10{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, AND_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?([mk_val__0_val_(I32_Inn, $iand_($size($valtype_Inn(I32_Inn)), iN_1, iN_2))]))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $iand_($size($valtype_Inn(I32_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_11{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, AND_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?([mk_val__0_val_(I64_Inn, $iand_($size($valtype_Inn(I64_Inn)), iN_1, iN_2))]))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $iand_($size($valtype_Inn(I64_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_12{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, OR_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?([mk_val__0_val_(I32_Inn, $ior_($size($valtype_Inn(I32_Inn)), iN_1, iN_2))]))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $ior_($size($valtype_Inn(I32_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_13{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, OR_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?([mk_val__0_val_(I64_Inn, $ior_($size($valtype_Inn(I64_Inn)), iN_1, iN_2))]))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $ior_($size($valtype_Inn(I64_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_14{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, XOR_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?([mk_val__0_val_(I32_Inn, $ixor_($size($valtype_Inn(I32_Inn)), iN_1, iN_2))]))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $ixor_($size($valtype_Inn(I32_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_15{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, XOR_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?([mk_val__0_val_(I64_Inn, $ixor_($size($valtype_Inn(I64_Inn)), iN_1, iN_2))]))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $ixor_($size($valtype_Inn(I64_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_16{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, SHL_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?([mk_val__0_val_(I32_Inn, $ishl_($size($valtype_Inn(I32_Inn)), iN_1, mk_uN_u32($proj_uN_0(iN_2).0)))]))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $ishl_($size($valtype_Inn(I32_Inn)), iN_1, mk_uN_u32($proj_uN_0(iN_2).0))))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_17{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, SHL_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?([mk_val__0_val_(I64_Inn, $ishl_($size($valtype_Inn(I64_Inn)), iN_1, mk_uN_u32($proj_uN_0(iN_2).0)))]))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $ishl_($size($valtype_Inn(I64_Inn)), iN_1, mk_uN_u32($proj_uN_0(iN_2).0))))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_18{v_sx : sx, iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, SHR_binop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?([mk_val__0_val_(I32_Inn, $ishr_($size($valtype_Inn(I32_Inn)), v_sx, iN_1, mk_uN_u32($proj_uN_0(iN_2).0)))]))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $ishr_($size($valtype_Inn(I32_Inn)), v_sx, iN_1, mk_uN_u32($proj_uN_0(iN_2).0))))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_19{v_sx : sx, iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, SHR_binop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?([mk_val__0_val_(I64_Inn, $ishr_($size($valtype_Inn(I64_Inn)), v_sx, iN_1, mk_uN_u32($proj_uN_0(iN_2).0)))]))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $ishr_($size($valtype_Inn(I64_Inn)), v_sx, iN_1, mk_uN_u32($proj_uN_0(iN_2).0))))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_20{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, ROTL_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?([mk_val__0_val_(I32_Inn, $irotl_($size($valtype_Inn(I32_Inn)), iN_1, iN_2))]))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $irotl_($size($valtype_Inn(I32_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_21{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, ROTL_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?([mk_val__0_val_(I64_Inn, $irotl_($size($valtype_Inn(I64_Inn)), iN_1, iN_2))]))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $irotl_($size($valtype_Inn(I64_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_22{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, ROTR_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?([mk_val__0_val_(I32_Inn, $irotr_($size($valtype_Inn(I32_Inn)), iN_1, iN_2))]))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, $irotr_($size($valtype_Inn(I32_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_23{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, ROTR_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?([mk_val__0_val_(I64_Inn, $irotr_($size($valtype_Inn(I64_Inn)), iN_1, iN_2))]))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, $irotr_($size($valtype_Inn(I64_Inn)), iN_1, iN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_24{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, ADD_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), ?(mk_val__1_val_(F32_Fnn, iter_0_42)*{iter_0_42 <- $fadd_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_29))*{iter_29 <- $fadd_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_41)))*{iter_0_41 <- $fadd_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_25{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, ADD_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), ?(mk_val__1_val_(F64_Fnn, iter_0_44)*{iter_0_44 <- $fadd_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_30))*{iter_30 <- $fadd_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_43)))*{iter_0_43 <- $fadd_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_26{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, SUB_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), ?(mk_val__1_val_(F32_Fnn, iter_0_46)*{iter_0_46 <- $fsub_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_31))*{iter_31 <- $fsub_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_45)))*{iter_0_45 <- $fsub_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_27{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, SUB_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), ?(mk_val__1_val_(F64_Fnn, iter_0_48)*{iter_0_48 <- $fsub_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_32))*{iter_32 <- $fsub_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_47)))*{iter_0_47 <- $fsub_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_28{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, MUL_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), ?(mk_val__1_val_(F32_Fnn, iter_0_50)*{iter_0_50 <- $fmul_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_33))*{iter_33 <- $fmul_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_49)))*{iter_0_49 <- $fmul_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_29{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, MUL_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), ?(mk_val__1_val_(F64_Fnn, iter_0_52)*{iter_0_52 <- $fmul_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_34))*{iter_34 <- $fmul_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_51)))*{iter_0_51 <- $fmul_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_30{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, DIV_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), ?(mk_val__1_val_(F32_Fnn, iter_0_54)*{iter_0_54 <- $fdiv_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_35))*{iter_35 <- $fdiv_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_53)))*{iter_0_53 <- $fdiv_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_31{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, DIV_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), ?(mk_val__1_val_(F64_Fnn, iter_0_56)*{iter_0_56 <- $fdiv_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_36))*{iter_36 <- $fdiv_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_55)))*{iter_0_55 <- $fdiv_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_32{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, MIN_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), ?(mk_val__1_val_(F32_Fnn, iter_0_58)*{iter_0_58 <- $fmin_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_37))*{iter_37 <- $fmin_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_57)))*{iter_0_57 <- $fmin_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_33{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, MIN_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), ?(mk_val__1_val_(F64_Fnn, iter_0_60)*{iter_0_60 <- $fmin_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_38))*{iter_38 <- $fmin_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_59)))*{iter_0_59 <- $fmin_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_34{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, MAX_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), ?(mk_val__1_val_(F32_Fnn, iter_0_62)*{iter_0_62 <- $fmax_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_39))*{iter_39 <- $fmax_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_61)))*{iter_0_61 <- $fmax_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_35{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, MAX_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), ?(mk_val__1_val_(F64_Fnn, iter_0_64)*{iter_0_64 <- $fmax_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_40))*{iter_40 <- $fmax_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_63)))*{iter_0_63 <- $fmax_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_36{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, COPYSIGN_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), ?(mk_val__1_val_(F32_Fnn, iter_0_66)*{iter_0_66 <- $fcopysign_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F32_Fnn)), iter_41))*{iter_41 <- $fcopysign_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, iter_0_65)))*{iter_0_65 <- $fcopysign_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_37{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, COPYSIGN_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), ?(mk_val__1_val_(F64_Fnn, iter_0_68)*{iter_0_68 <- $fcopysign_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}))
    -- (wf_fN: `%%`($size($valtype_Fnn(F64_Fnn)), iter_42))*{iter_42 <- $fcopysign_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}
    -- (wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, iter_0_67)))*{iter_0_67 <- $fcopysign_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13
  rule fun_binop__case_38{x0 : valtype, x1 : binop_, x2 : val_, x3 : val_}:
    `%%%%%`(x0, x1, x2, x3, ?())
    -- ~ fun_binop__before_fun_binop__case_38: `%%%%`(x0, x1, x2, x3)

;; ../specification/wasm-1.0/3-numerics.spectec:89.6-89.12
relation fun_ieqz_: `%%%`(N, iN, u32)
  ;; ../specification/wasm-1.0/3-numerics.spectec:89.6-89.12
  rule fun_ieqz__case_0{v_N : nat, i_1 : uN}:
    `%%%`(v_N, i_1, mk_uN_u32($bool(($proj_uN_0(i_1).0 = 0))))
    -- wf_uN: `%%`(32, mk_uN_uN($bool(($proj_uN_0(i_1).0 = 0))))

;; ../specification/wasm-1.0/3-numerics.spectec:32.6-32.14
relation fun_testop__before_fun_testop__case_2: `%%%`(valtype, testop_, val_)
  ;; ../specification/wasm-1.0/3-numerics.spectec:32.6-32.14
  rule fun_testop__case_1{v_iN : uN, var_0 : uN}:
    `%%%`(I64_valtype, mk_testop__0_testop_(I64_Inn, EQZ_testop_Inn), mk_val__0_val_(I64_Inn, v_iN))
    -- fun_ieqz_: `%%%`($size($valtype_Inn(I64_Inn)), v_iN, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:32.6-32.14
  rule fun_testop__case_0{v_iN : uN, var_0 : uN}:
    `%%%`(I32_valtype, mk_testop__0_testop_(I32_Inn, EQZ_testop_Inn), mk_val__0_val_(I32_Inn, v_iN))
    -- fun_ieqz_: `%%%`($size($valtype_Inn(I32_Inn)), v_iN, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

;; ../specification/wasm-1.0/3-numerics.spectec:32.6-32.14
relation fun_testop_: `%%%%`(valtype, testop_, val_, val_?)
  ;; ../specification/wasm-1.0/3-numerics.spectec:32.6-32.14
  rule fun_testop__case_0{v_iN : uN, var_0 : uN}:
    `%%%%`(I32_valtype, mk_testop__0_testop_(I32_Inn, EQZ_testop_Inn), mk_val__0_val_(I32_Inn, v_iN), ?(mk_val__0_val_(I32_Inn, var_0)))
    -- fun_ieqz_: `%%%`($size($valtype_Inn(I32_Inn)), v_iN, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:32.6-32.14
  rule fun_testop__case_1{v_iN : uN, var_0 : uN}:
    `%%%%`(I64_valtype, mk_testop__0_testop_(I64_Inn, EQZ_testop_Inn), mk_val__0_val_(I64_Inn, v_iN), ?(mk_val__0_val_(I32_Inn, var_0)))
    -- fun_ieqz_: `%%%`($size($valtype_Inn(I64_Inn)), v_iN, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:32.6-32.14
  rule fun_testop__case_2{x0 : valtype, x1 : testop_, x2 : val_}:
    `%%%%`(x0, x1, x2, ?())
    -- ~ fun_testop__before_fun_testop__case_2: `%%%`(x0, x1, x2)

;; ../specification/wasm-1.0/3-numerics.spectec:159.1-159.33
def $feq_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; ../specification/wasm-1.0/3-numerics.spectec:164.1-164.33
def $fge_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; ../specification/wasm-1.0/3-numerics.spectec:162.1-162.33
def $fgt_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; ../specification/wasm-1.0/3-numerics.spectec:163.1-163.33
def $fle_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; ../specification/wasm-1.0/3-numerics.spectec:161.1-161.33
def $flt_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; ../specification/wasm-1.0/3-numerics.spectec:160.1-160.33
def $fne_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; ../specification/wasm-1.0/3-numerics.spectec:91.6-91.11
relation fun_ieq_: `%%%%`(N, iN, iN, u32)
  ;; ../specification/wasm-1.0/3-numerics.spectec:91.6-91.11
  rule fun_ieq__case_0{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%`(v_N, i_1, i_2, mk_uN_u32($bool((i_1 = i_2))))
    -- wf_uN: `%%`(32, mk_uN_uN($bool((i_1 = i_2))))

;; ../specification/wasm-1.0/3-numerics.spectec:96.6-96.11
relation fun_ige_: `%%%%%`(N, sx, iN, iN, u32)
  ;; ../specification/wasm-1.0/3-numerics.spectec:96.6-96.11
  rule fun_ige__case_0{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%%`(v_N, U_sx, i_1, i_2, mk_uN_u32($bool(($proj_uN_0(i_1).0 >= $proj_uN_0(i_2).0))))
    -- wf_uN: `%%`(32, mk_uN_uN($bool(($proj_uN_0(i_1).0 >= $proj_uN_0(i_2).0))))

  ;; ../specification/wasm-1.0/3-numerics.spectec:96.6-96.11
  rule fun_ige__case_1{v_N : nat, i_1 : uN, i_2 : uN, var_1 : int, var_0 : int}:
    `%%%%%`(v_N, S_sx, i_1, i_2, mk_uN_u32($bool((var_0 >= var_1))))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_1)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)
    -- wf_uN: `%%`(32, mk_uN_uN($bool((var_0 >= var_1))))

;; ../specification/wasm-1.0/3-numerics.spectec:94.6-94.11
relation fun_igt_: `%%%%%`(N, sx, iN, iN, u32)
  ;; ../specification/wasm-1.0/3-numerics.spectec:94.6-94.11
  rule fun_igt__case_0{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%%`(v_N, U_sx, i_1, i_2, mk_uN_u32($bool(($proj_uN_0(i_1).0 > $proj_uN_0(i_2).0))))
    -- wf_uN: `%%`(32, mk_uN_uN($bool(($proj_uN_0(i_1).0 > $proj_uN_0(i_2).0))))

  ;; ../specification/wasm-1.0/3-numerics.spectec:94.6-94.11
  rule fun_igt__case_1{v_N : nat, i_1 : uN, i_2 : uN, var_1 : int, var_0 : int}:
    `%%%%%`(v_N, S_sx, i_1, i_2, mk_uN_u32($bool((var_0 > var_1))))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_1)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)
    -- wf_uN: `%%`(32, mk_uN_uN($bool((var_0 > var_1))))

;; ../specification/wasm-1.0/3-numerics.spectec:95.6-95.11
relation fun_ile_: `%%%%%`(N, sx, iN, iN, u32)
  ;; ../specification/wasm-1.0/3-numerics.spectec:95.6-95.11
  rule fun_ile__case_0{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%%`(v_N, U_sx, i_1, i_2, mk_uN_u32($bool(($proj_uN_0(i_1).0 <= $proj_uN_0(i_2).0))))
    -- wf_uN: `%%`(32, mk_uN_uN($bool(($proj_uN_0(i_1).0 <= $proj_uN_0(i_2).0))))

  ;; ../specification/wasm-1.0/3-numerics.spectec:95.6-95.11
  rule fun_ile__case_1{v_N : nat, i_1 : uN, i_2 : uN, var_1 : int, var_0 : int}:
    `%%%%%`(v_N, S_sx, i_1, i_2, mk_uN_u32($bool((var_0 <= var_1))))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_1)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)
    -- wf_uN: `%%`(32, mk_uN_uN($bool((var_0 <= var_1))))

;; ../specification/wasm-1.0/3-numerics.spectec:93.6-93.11
relation fun_ilt_: `%%%%%`(N, sx, iN, iN, u32)
  ;; ../specification/wasm-1.0/3-numerics.spectec:93.6-93.11
  rule fun_ilt__case_0{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%%`(v_N, U_sx, i_1, i_2, mk_uN_u32($bool(($proj_uN_0(i_1).0 < $proj_uN_0(i_2).0))))
    -- wf_uN: `%%`(32, mk_uN_uN($bool(($proj_uN_0(i_1).0 < $proj_uN_0(i_2).0))))

  ;; ../specification/wasm-1.0/3-numerics.spectec:93.6-93.11
  rule fun_ilt__case_1{v_N : nat, i_1 : uN, i_2 : uN, var_1 : int, var_0 : int}:
    `%%%%%`(v_N, S_sx, i_1, i_2, mk_uN_u32($bool((var_0 < var_1))))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_1)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)
    -- wf_uN: `%%`(32, mk_uN_uN($bool((var_0 < var_1))))

;; ../specification/wasm-1.0/3-numerics.spectec:92.6-92.11
relation fun_ine_: `%%%%`(N, iN, iN, u32)
  ;; ../specification/wasm-1.0/3-numerics.spectec:92.6-92.11
  rule fun_ine__case_0{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%`(v_N, i_1, i_2, mk_uN_u32($bool((i_1 =/= i_2))))
    -- wf_uN: `%%`(32, mk_uN_uN($bool((i_1 =/= i_2))))

;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
relation fun_relop__before_fun_relop__case_24: `%%%%`(valtype, relop_, val_, val_)
  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_23{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, GE_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $fge_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_22{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, GE_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $fge_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_21{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, LE_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $fle_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_20{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, LE_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $fle_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_19{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, GT_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $fgt_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_18{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, GT_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $fgt_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_17{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, LT_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $flt_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_16{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, LT_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $flt_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_15{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, NE_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $fne_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_14{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, NE_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $fne_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_13{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, EQ_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $feq_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_12{fN_1 : fN, fN_2 : fN}:
    `%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, EQ_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $feq_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_11{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, GE_relop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- fun_ige_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_10{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, GE_relop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- fun_ige_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_9{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, LE_relop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- fun_ile_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_8{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, LE_relop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- fun_ile_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_7{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, GT_relop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- fun_igt_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_6{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, GT_relop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- fun_igt_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_5{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, LT_relop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- fun_ilt_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_4{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, LT_relop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- fun_ilt_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_3{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, NE_relop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- fun_ine_: `%%%%`($size($valtype_Inn(I64_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_2{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, NE_relop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- fun_ine_: `%%%%`($size($valtype_Inn(I32_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_1{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, EQ_relop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2))
    -- fun_ieq_: `%%%%`($size($valtype_Inn(I64_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_0{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, EQ_relop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2))
    -- fun_ieq_: `%%%%`($size($valtype_Inn(I32_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
relation fun_relop_: `%%%%%`(valtype, relop_, val_, val_, val_?)
  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_0{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, EQ_relop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?(mk_val__0_val_(I32_Inn, var_0)))
    -- fun_ieq_: `%%%%`($size($valtype_Inn(I32_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_1{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, EQ_relop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?(mk_val__0_val_(I32_Inn, var_0)))
    -- fun_ieq_: `%%%%`($size($valtype_Inn(I64_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_2{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, NE_relop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?(mk_val__0_val_(I32_Inn, var_0)))
    -- fun_ine_: `%%%%`($size($valtype_Inn(I32_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_3{iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, NE_relop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?(mk_val__0_val_(I32_Inn, var_0)))
    -- fun_ine_: `%%%%`($size($valtype_Inn(I64_Inn)), iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_4{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, LT_relop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?(mk_val__0_val_(I32_Inn, var_0)))
    -- fun_ilt_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_5{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, LT_relop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?(mk_val__0_val_(I32_Inn, var_0)))
    -- fun_ilt_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_6{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, GT_relop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?(mk_val__0_val_(I32_Inn, var_0)))
    -- fun_igt_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_7{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, GT_relop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?(mk_val__0_val_(I32_Inn, var_0)))
    -- fun_igt_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_8{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, LE_relop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?(mk_val__0_val_(I32_Inn, var_0)))
    -- fun_ile_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_9{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, LE_relop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?(mk_val__0_val_(I32_Inn, var_0)))
    -- fun_ile_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_10{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, GE_relop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), ?(mk_val__0_val_(I32_Inn, var_0)))
    -- fun_ige_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_11{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, GE_relop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), ?(mk_val__0_val_(I32_Inn, var_0)))
    -- fun_ige_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, var_0))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_12{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, EQ_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), ?(mk_val__0_val_(I32_Inn, $feq_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2))))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $feq_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_13{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, EQ_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), ?(mk_val__0_val_(I32_Inn, $feq_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2))))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $feq_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_14{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, NE_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), ?(mk_val__0_val_(I32_Inn, $fne_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2))))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $fne_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_15{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, NE_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), ?(mk_val__0_val_(I32_Inn, $fne_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2))))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $fne_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_16{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, LT_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), ?(mk_val__0_val_(I32_Inn, $flt_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2))))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $flt_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_17{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, LT_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), ?(mk_val__0_val_(I32_Inn, $flt_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2))))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $flt_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_18{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, GT_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), ?(mk_val__0_val_(I32_Inn, $fgt_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2))))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $fgt_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_19{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, GT_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), ?(mk_val__0_val_(I32_Inn, $fgt_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2))))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $fgt_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_20{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, LE_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), ?(mk_val__0_val_(I32_Inn, $fle_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2))))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $fle_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_21{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, LE_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), ?(mk_val__0_val_(I32_Inn, $fle_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2))))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $fle_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_22{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, GE_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), ?(mk_val__0_val_(I32_Inn, $fge_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2))))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $fge_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_23{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, GE_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), ?(mk_val__0_val_(I32_Inn, $fge_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2))))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $fge_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13
  rule fun_relop__case_24{x0 : valtype, x1 : relop_, x2 : val_, x3 : val_}:
    `%%%%%`(x0, x1, x2, x3, ?())
    -- ~ fun_relop__before_fun_relop__case_24: `%%%%`(x0, x1, x2, x3)

;; ../specification/wasm-1.0/3-numerics.spectec:44.1-44.90
def $convert__(v_M : M, v_N : N, v_sx : sx, v_iN : iN) : fN

;; ../specification/wasm-1.0/3-numerics.spectec:42.1-42.36
def $demote__(v_M : M, v_N : N, v_fN : fN) : fN*

;; ../specification/wasm-1.0/3-numerics.spectec:40.1-40.89
def $extend__(v_M : M, v_N : N, v_sx : sx, v_iN : iN) : iN

;; ../specification/wasm-1.0/3-numerics.spectec:43.1-43.37
def $promote__(v_M : M, v_N : N, v_fN : fN) : fN*

;; ../specification/wasm-1.0/3-numerics.spectec:45.1-45.76
def $reinterpret__(valtype_1 : valtype, valtype_2 : valtype, v_val_ : val_) : val_

;; ../specification/wasm-1.0/3-numerics.spectec:41.1-41.88
def $trunc__(v_M : M, v_N : N, v_sx : sx, v_fN : fN) : iN?

;; ../specification/wasm-1.0/3-numerics.spectec:39.1-39.33
def $wrap__(v_M : M, v_N : N, v_iN : iN) : iN

;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
relation fun_cvtop___before_fun_cvtop___case_20: `%%%%`(valtype, valtype, cvtop, val_)
  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_19{v_fN : fN}:
    `%%%%`(F64_valtype, I64_valtype, REINTERPRET_cvtop, mk_val__1_val_(F64_Fnn, v_fN))
    -- if ($size($valtype_Inn(I64_Inn)) = $size($valtype_Fnn(F64_Fnn)))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), $reinterpret__($valtype_Fnn(F64_Fnn), $valtype_Inn(I64_Inn), mk_val__1_val_(F64_Fnn, v_fN)))
    -- wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, v_fN))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_18{v_fN : fN}:
    `%%%%`(F32_valtype, I64_valtype, REINTERPRET_cvtop, mk_val__1_val_(F32_Fnn, v_fN))
    -- if ($size($valtype_Inn(I64_Inn)) = $size($valtype_Fnn(F32_Fnn)))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), $reinterpret__($valtype_Fnn(F32_Fnn), $valtype_Inn(I64_Inn), mk_val__1_val_(F32_Fnn, v_fN)))
    -- wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, v_fN))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_17{v_fN : fN}:
    `%%%%`(F64_valtype, I32_valtype, REINTERPRET_cvtop, mk_val__1_val_(F64_Fnn, v_fN))
    -- if ($size($valtype_Inn(I32_Inn)) = $size($valtype_Fnn(F64_Fnn)))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), $reinterpret__($valtype_Fnn(F64_Fnn), $valtype_Inn(I32_Inn), mk_val__1_val_(F64_Fnn, v_fN)))
    -- wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, v_fN))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_16{v_fN : fN}:
    `%%%%`(F32_valtype, I32_valtype, REINTERPRET_cvtop, mk_val__1_val_(F32_Fnn, v_fN))
    -- if ($size($valtype_Inn(I32_Inn)) = $size($valtype_Fnn(F32_Fnn)))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), $reinterpret__($valtype_Fnn(F32_Fnn), $valtype_Inn(I32_Inn), mk_val__1_val_(F32_Fnn, v_fN)))
    -- wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, v_fN))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_15{v_iN : uN}:
    `%%%%`(I64_valtype, F64_valtype, REINTERPRET_cvtop, mk_val__0_val_(I64_Inn, v_iN))
    -- if ($size($valtype_Inn(I64_Inn)) = $size($valtype_Fnn(F64_Fnn)))
    -- wf_val_: `%%`($valtype_Fnn(F64_Fnn), $reinterpret__($valtype_Inn(I64_Inn), $valtype_Fnn(F64_Fnn), mk_val__0_val_(I64_Inn, v_iN)))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, v_iN))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_14{v_iN : uN}:
    `%%%%`(I32_valtype, F64_valtype, REINTERPRET_cvtop, mk_val__0_val_(I32_Inn, v_iN))
    -- if ($size($valtype_Inn(I32_Inn)) = $size($valtype_Fnn(F64_Fnn)))
    -- wf_val_: `%%`($valtype_Fnn(F64_Fnn), $reinterpret__($valtype_Inn(I32_Inn), $valtype_Fnn(F64_Fnn), mk_val__0_val_(I32_Inn, v_iN)))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, v_iN))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_13{v_iN : uN}:
    `%%%%`(I64_valtype, F32_valtype, REINTERPRET_cvtop, mk_val__0_val_(I64_Inn, v_iN))
    -- if ($size($valtype_Inn(I64_Inn)) = $size($valtype_Fnn(F32_Fnn)))
    -- wf_val_: `%%`($valtype_Fnn(F32_Fnn), $reinterpret__($valtype_Inn(I64_Inn), $valtype_Fnn(F32_Fnn), mk_val__0_val_(I64_Inn, v_iN)))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, v_iN))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_12{v_iN : uN}:
    `%%%%`(I32_valtype, F32_valtype, REINTERPRET_cvtop, mk_val__0_val_(I32_Inn, v_iN))
    -- if ($size($valtype_Inn(I32_Inn)) = $size($valtype_Fnn(F32_Fnn)))
    -- wf_val_: `%%`($valtype_Fnn(F32_Fnn), $reinterpret__($valtype_Inn(I32_Inn), $valtype_Fnn(F32_Fnn), mk_val__0_val_(I32_Inn, v_iN)))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, v_iN))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_11{v_sx : sx, v_iN : uN}:
    `%%%%`(I64_valtype, F64_valtype, CONVERT_cvtop(v_sx), mk_val__0_val_(I64_Inn, v_iN))
    -- wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, $convert__($size($valtype_Inn(I64_Inn)), $size($valtype_Fnn(F64_Fnn)), v_sx, v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_10{v_sx : sx, v_iN : uN}:
    `%%%%`(I32_valtype, F64_valtype, CONVERT_cvtop(v_sx), mk_val__0_val_(I32_Inn, v_iN))
    -- wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, $convert__($size($valtype_Inn(I32_Inn)), $size($valtype_Fnn(F64_Fnn)), v_sx, v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_9{v_sx : sx, v_iN : uN}:
    `%%%%`(I64_valtype, F32_valtype, CONVERT_cvtop(v_sx), mk_val__0_val_(I64_Inn, v_iN))
    -- wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, $convert__($size($valtype_Inn(I64_Inn)), $size($valtype_Fnn(F32_Fnn)), v_sx, v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_8{v_sx : sx, v_iN : uN}:
    `%%%%`(I32_valtype, F32_valtype, CONVERT_cvtop(v_sx), mk_val__0_val_(I32_Inn, v_iN))
    -- wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, $convert__($size($valtype_Inn(I32_Inn)), $size($valtype_Fnn(F32_Fnn)), v_sx, v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_7{v_fN : fN}:
    `%%%%`(F64_valtype, F32_valtype, DEMOTE_cvtop, mk_val__1_val_(F64_Fnn, v_fN))
    -- (wf_fN: `%%`(32, iter_52))*{iter_52 <- $demote__(64, 32, v_fN)}
    -- (wf_val_: `%%`(F32_valtype, mk_val__1_val_(F32_Fnn, iter_0_82)))*{iter_0_82 <- $demote__(64, 32, v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_6{v_fN : fN}:
    `%%%%`(F32_valtype, F64_valtype, PROMOTE_cvtop, mk_val__1_val_(F32_Fnn, v_fN))
    -- (wf_fN: `%%`(64, iter_51))*{iter_51 <- $promote__(32, 64, v_fN)}
    -- (wf_val_: `%%`(F64_valtype, mk_val__1_val_(F64_Fnn, iter_0_81)))*{iter_0_81 <- $promote__(32, 64, v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_5{v_sx : sx, v_fN : fN}:
    `%%%%`(F64_valtype, I64_valtype, TRUNC_cvtop(v_sx), mk_val__1_val_(F64_Fnn, v_fN))
    -- (wf_val_: `%%`($valtype_Inn(I64_Inn), iter_49))*{iter_49 <- $list_(syntax val_, mk_val__0_val_(I64_Inn, iter_0_78)?{iter_0_78 <- $trunc__($size($valtype_Fnn(F64_Fnn)), $size($valtype_Inn(I64_Inn)), v_sx, v_fN)})}
    -- (wf_uN: `%%`($size($valtype_Inn(I64_Inn)), iter_50))?{iter_50 <- $trunc__($size($valtype_Fnn(F64_Fnn)), $size($valtype_Inn(I64_Inn)), v_sx, v_fN)}
    -- (wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, iter_0_79)))?{iter_0_79 <- $trunc__($size($valtype_Fnn(F64_Fnn)), $size($valtype_Inn(I64_Inn)), v_sx, v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_4{v_sx : sx, v_fN : fN}:
    `%%%%`(F32_valtype, I64_valtype, TRUNC_cvtop(v_sx), mk_val__1_val_(F32_Fnn, v_fN))
    -- (wf_val_: `%%`($valtype_Inn(I64_Inn), iter_47))*{iter_47 <- $list_(syntax val_, mk_val__0_val_(I64_Inn, iter_0_75)?{iter_0_75 <- $trunc__($size($valtype_Fnn(F32_Fnn)), $size($valtype_Inn(I64_Inn)), v_sx, v_fN)})}
    -- (wf_uN: `%%`($size($valtype_Inn(I64_Inn)), iter_48))?{iter_48 <- $trunc__($size($valtype_Fnn(F32_Fnn)), $size($valtype_Inn(I64_Inn)), v_sx, v_fN)}
    -- (wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, iter_0_76)))?{iter_0_76 <- $trunc__($size($valtype_Fnn(F32_Fnn)), $size($valtype_Inn(I64_Inn)), v_sx, v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_3{v_sx : sx, v_fN : fN}:
    `%%%%`(F64_valtype, I32_valtype, TRUNC_cvtop(v_sx), mk_val__1_val_(F64_Fnn, v_fN))
    -- (wf_val_: `%%`($valtype_Inn(I32_Inn), iter_45))*{iter_45 <- $list_(syntax val_, mk_val__0_val_(I32_Inn, iter_0_72)?{iter_0_72 <- $trunc__($size($valtype_Fnn(F64_Fnn)), $size($valtype_Inn(I32_Inn)), v_sx, v_fN)})}
    -- (wf_uN: `%%`($size($valtype_Inn(I32_Inn)), iter_46))?{iter_46 <- $trunc__($size($valtype_Fnn(F64_Fnn)), $size($valtype_Inn(I32_Inn)), v_sx, v_fN)}
    -- (wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, iter_0_73)))?{iter_0_73 <- $trunc__($size($valtype_Fnn(F64_Fnn)), $size($valtype_Inn(I32_Inn)), v_sx, v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_2{v_sx : sx, v_fN : fN}:
    `%%%%`(F32_valtype, I32_valtype, TRUNC_cvtop(v_sx), mk_val__1_val_(F32_Fnn, v_fN))
    -- (wf_val_: `%%`($valtype_Inn(I32_Inn), iter_43))*{iter_43 <- $list_(syntax val_, mk_val__0_val_(I32_Inn, iter_0_69)?{iter_0_69 <- $trunc__($size($valtype_Fnn(F32_Fnn)), $size($valtype_Inn(I32_Inn)), v_sx, v_fN)})}
    -- (wf_uN: `%%`($size($valtype_Inn(I32_Inn)), iter_44))?{iter_44 <- $trunc__($size($valtype_Fnn(F32_Fnn)), $size($valtype_Inn(I32_Inn)), v_sx, v_fN)}
    -- (wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, iter_0_70)))?{iter_0_70 <- $trunc__($size($valtype_Fnn(F32_Fnn)), $size($valtype_Inn(I32_Inn)), v_sx, v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_1{v_iN : uN}:
    `%%%%`(I64_valtype, I32_valtype, WRAP_cvtop, mk_val__0_val_(I64_Inn, v_iN))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $wrap__(64, 32, v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_0{v_sx : sx, v_iN : uN}:
    `%%%%`(I32_valtype, I64_valtype, EXTEND_cvtop(v_sx), mk_val__0_val_(I32_Inn, v_iN))
    -- wf_val_: `%%`(I64_valtype, mk_val__0_val_(I64_Inn, $extend__(32, 64, v_sx, v_iN)))

;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
relation fun_cvtop__: `%%%%%`(valtype, valtype, cvtop, val_, val_*?)
  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_0{v_sx : sx, v_iN : uN}:
    `%%%%%`(I32_valtype, I64_valtype, EXTEND_cvtop(v_sx), mk_val__0_val_(I32_Inn, v_iN), ?([mk_val__0_val_(I64_Inn, $extend__(32, 64, v_sx, v_iN))]))
    -- wf_val_: `%%`(I64_valtype, mk_val__0_val_(I64_Inn, $extend__(32, 64, v_sx, v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_1{v_iN : uN}:
    `%%%%%`(I64_valtype, I32_valtype, WRAP_cvtop, mk_val__0_val_(I64_Inn, v_iN), ?([mk_val__0_val_(I32_Inn, $wrap__(64, 32, v_iN))]))
    -- wf_val_: `%%`(I32_valtype, mk_val__0_val_(I32_Inn, $wrap__(64, 32, v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_2{v_sx : sx, v_fN : fN}:
    `%%%%%`(F32_valtype, I32_valtype, TRUNC_cvtop(v_sx), mk_val__1_val_(F32_Fnn, v_fN), ?($list_(syntax val_, mk_val__0_val_(I32_Inn, iter_0_71)?{iter_0_71 <- $trunc__($size($valtype_Fnn(F32_Fnn)), $size($valtype_Inn(I32_Inn)), v_sx, v_fN)})))
    -- (wf_val_: `%%`($valtype_Inn(I32_Inn), iter_43))*{iter_43 <- $list_(syntax val_, mk_val__0_val_(I32_Inn, iter_0_69)?{iter_0_69 <- $trunc__($size($valtype_Fnn(F32_Fnn)), $size($valtype_Inn(I32_Inn)), v_sx, v_fN)})}
    -- (wf_uN: `%%`($size($valtype_Inn(I32_Inn)), iter_44))?{iter_44 <- $trunc__($size($valtype_Fnn(F32_Fnn)), $size($valtype_Inn(I32_Inn)), v_sx, v_fN)}
    -- (wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, iter_0_70)))?{iter_0_70 <- $trunc__($size($valtype_Fnn(F32_Fnn)), $size($valtype_Inn(I32_Inn)), v_sx, v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_3{v_sx : sx, v_fN : fN}:
    `%%%%%`(F64_valtype, I32_valtype, TRUNC_cvtop(v_sx), mk_val__1_val_(F64_Fnn, v_fN), ?($list_(syntax val_, mk_val__0_val_(I32_Inn, iter_0_74)?{iter_0_74 <- $trunc__($size($valtype_Fnn(F64_Fnn)), $size($valtype_Inn(I32_Inn)), v_sx, v_fN)})))
    -- (wf_val_: `%%`($valtype_Inn(I32_Inn), iter_45))*{iter_45 <- $list_(syntax val_, mk_val__0_val_(I32_Inn, iter_0_72)?{iter_0_72 <- $trunc__($size($valtype_Fnn(F64_Fnn)), $size($valtype_Inn(I32_Inn)), v_sx, v_fN)})}
    -- (wf_uN: `%%`($size($valtype_Inn(I32_Inn)), iter_46))?{iter_46 <- $trunc__($size($valtype_Fnn(F64_Fnn)), $size($valtype_Inn(I32_Inn)), v_sx, v_fN)}
    -- (wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, iter_0_73)))?{iter_0_73 <- $trunc__($size($valtype_Fnn(F64_Fnn)), $size($valtype_Inn(I32_Inn)), v_sx, v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_4{v_sx : sx, v_fN : fN}:
    `%%%%%`(F32_valtype, I64_valtype, TRUNC_cvtop(v_sx), mk_val__1_val_(F32_Fnn, v_fN), ?($list_(syntax val_, mk_val__0_val_(I64_Inn, iter_0_77)?{iter_0_77 <- $trunc__($size($valtype_Fnn(F32_Fnn)), $size($valtype_Inn(I64_Inn)), v_sx, v_fN)})))
    -- (wf_val_: `%%`($valtype_Inn(I64_Inn), iter_47))*{iter_47 <- $list_(syntax val_, mk_val__0_val_(I64_Inn, iter_0_75)?{iter_0_75 <- $trunc__($size($valtype_Fnn(F32_Fnn)), $size($valtype_Inn(I64_Inn)), v_sx, v_fN)})}
    -- (wf_uN: `%%`($size($valtype_Inn(I64_Inn)), iter_48))?{iter_48 <- $trunc__($size($valtype_Fnn(F32_Fnn)), $size($valtype_Inn(I64_Inn)), v_sx, v_fN)}
    -- (wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, iter_0_76)))?{iter_0_76 <- $trunc__($size($valtype_Fnn(F32_Fnn)), $size($valtype_Inn(I64_Inn)), v_sx, v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_5{v_sx : sx, v_fN : fN}:
    `%%%%%`(F64_valtype, I64_valtype, TRUNC_cvtop(v_sx), mk_val__1_val_(F64_Fnn, v_fN), ?($list_(syntax val_, mk_val__0_val_(I64_Inn, iter_0_80)?{iter_0_80 <- $trunc__($size($valtype_Fnn(F64_Fnn)), $size($valtype_Inn(I64_Inn)), v_sx, v_fN)})))
    -- (wf_val_: `%%`($valtype_Inn(I64_Inn), iter_49))*{iter_49 <- $list_(syntax val_, mk_val__0_val_(I64_Inn, iter_0_78)?{iter_0_78 <- $trunc__($size($valtype_Fnn(F64_Fnn)), $size($valtype_Inn(I64_Inn)), v_sx, v_fN)})}
    -- (wf_uN: `%%`($size($valtype_Inn(I64_Inn)), iter_50))?{iter_50 <- $trunc__($size($valtype_Fnn(F64_Fnn)), $size($valtype_Inn(I64_Inn)), v_sx, v_fN)}
    -- (wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, iter_0_79)))?{iter_0_79 <- $trunc__($size($valtype_Fnn(F64_Fnn)), $size($valtype_Inn(I64_Inn)), v_sx, v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_6{v_fN : fN}:
    `%%%%%`(F32_valtype, F64_valtype, PROMOTE_cvtop, mk_val__1_val_(F32_Fnn, v_fN), ?(mk_val__1_val_(F64_Fnn, iter_0)*{iter_0 <- $promote__(32, 64, v_fN)}))
    -- (wf_fN: `%%`(64, iter_51))*{iter_51 <- $promote__(32, 64, v_fN)}
    -- (wf_val_: `%%`(F64_valtype, mk_val__1_val_(F64_Fnn, iter_0_81)))*{iter_0_81 <- $promote__(32, 64, v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_7{v_fN : fN}:
    `%%%%%`(F64_valtype, F32_valtype, DEMOTE_cvtop, mk_val__1_val_(F64_Fnn, v_fN), ?(mk_val__1_val_(F32_Fnn, iter_0)*{iter_0 <- $demote__(64, 32, v_fN)}))
    -- (wf_fN: `%%`(32, iter_52))*{iter_52 <- $demote__(64, 32, v_fN)}
    -- (wf_val_: `%%`(F32_valtype, mk_val__1_val_(F32_Fnn, iter_0_82)))*{iter_0_82 <- $demote__(64, 32, v_fN)}

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_8{v_sx : sx, v_iN : uN}:
    `%%%%%`(I32_valtype, F32_valtype, CONVERT_cvtop(v_sx), mk_val__0_val_(I32_Inn, v_iN), ?([mk_val__1_val_(F32_Fnn, $convert__($size($valtype_Inn(I32_Inn)), $size($valtype_Fnn(F32_Fnn)), v_sx, v_iN))]))
    -- wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, $convert__($size($valtype_Inn(I32_Inn)), $size($valtype_Fnn(F32_Fnn)), v_sx, v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_9{v_sx : sx, v_iN : uN}:
    `%%%%%`(I64_valtype, F32_valtype, CONVERT_cvtop(v_sx), mk_val__0_val_(I64_Inn, v_iN), ?([mk_val__1_val_(F32_Fnn, $convert__($size($valtype_Inn(I64_Inn)), $size($valtype_Fnn(F32_Fnn)), v_sx, v_iN))]))
    -- wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, $convert__($size($valtype_Inn(I64_Inn)), $size($valtype_Fnn(F32_Fnn)), v_sx, v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_10{v_sx : sx, v_iN : uN}:
    `%%%%%`(I32_valtype, F64_valtype, CONVERT_cvtop(v_sx), mk_val__0_val_(I32_Inn, v_iN), ?([mk_val__1_val_(F64_Fnn, $convert__($size($valtype_Inn(I32_Inn)), $size($valtype_Fnn(F64_Fnn)), v_sx, v_iN))]))
    -- wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, $convert__($size($valtype_Inn(I32_Inn)), $size($valtype_Fnn(F64_Fnn)), v_sx, v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_11{v_sx : sx, v_iN : uN}:
    `%%%%%`(I64_valtype, F64_valtype, CONVERT_cvtop(v_sx), mk_val__0_val_(I64_Inn, v_iN), ?([mk_val__1_val_(F64_Fnn, $convert__($size($valtype_Inn(I64_Inn)), $size($valtype_Fnn(F64_Fnn)), v_sx, v_iN))]))
    -- wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, $convert__($size($valtype_Inn(I64_Inn)), $size($valtype_Fnn(F64_Fnn)), v_sx, v_iN)))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_12{v_iN : uN}:
    `%%%%%`(I32_valtype, F32_valtype, REINTERPRET_cvtop, mk_val__0_val_(I32_Inn, v_iN), ?([$reinterpret__($valtype_Inn(I32_Inn), $valtype_Fnn(F32_Fnn), mk_val__0_val_(I32_Inn, v_iN))]))
    -- if ($size($valtype_Inn(I32_Inn)) = $size($valtype_Fnn(F32_Fnn)))
    -- wf_val_: `%%`($valtype_Fnn(F32_Fnn), $reinterpret__($valtype_Inn(I32_Inn), $valtype_Fnn(F32_Fnn), mk_val__0_val_(I32_Inn, v_iN)))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, v_iN))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_13{v_iN : uN}:
    `%%%%%`(I64_valtype, F32_valtype, REINTERPRET_cvtop, mk_val__0_val_(I64_Inn, v_iN), ?([$reinterpret__($valtype_Inn(I64_Inn), $valtype_Fnn(F32_Fnn), mk_val__0_val_(I64_Inn, v_iN))]))
    -- if ($size($valtype_Inn(I64_Inn)) = $size($valtype_Fnn(F32_Fnn)))
    -- wf_val_: `%%`($valtype_Fnn(F32_Fnn), $reinterpret__($valtype_Inn(I64_Inn), $valtype_Fnn(F32_Fnn), mk_val__0_val_(I64_Inn, v_iN)))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, v_iN))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_14{v_iN : uN}:
    `%%%%%`(I32_valtype, F64_valtype, REINTERPRET_cvtop, mk_val__0_val_(I32_Inn, v_iN), ?([$reinterpret__($valtype_Inn(I32_Inn), $valtype_Fnn(F64_Fnn), mk_val__0_val_(I32_Inn, v_iN))]))
    -- if ($size($valtype_Inn(I32_Inn)) = $size($valtype_Fnn(F64_Fnn)))
    -- wf_val_: `%%`($valtype_Fnn(F64_Fnn), $reinterpret__($valtype_Inn(I32_Inn), $valtype_Fnn(F64_Fnn), mk_val__0_val_(I32_Inn, v_iN)))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), mk_val__0_val_(I32_Inn, v_iN))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_15{v_iN : uN}:
    `%%%%%`(I64_valtype, F64_valtype, REINTERPRET_cvtop, mk_val__0_val_(I64_Inn, v_iN), ?([$reinterpret__($valtype_Inn(I64_Inn), $valtype_Fnn(F64_Fnn), mk_val__0_val_(I64_Inn, v_iN))]))
    -- if ($size($valtype_Inn(I64_Inn)) = $size($valtype_Fnn(F64_Fnn)))
    -- wf_val_: `%%`($valtype_Fnn(F64_Fnn), $reinterpret__($valtype_Inn(I64_Inn), $valtype_Fnn(F64_Fnn), mk_val__0_val_(I64_Inn, v_iN)))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), mk_val__0_val_(I64_Inn, v_iN))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_16{v_fN : fN}:
    `%%%%%`(F32_valtype, I32_valtype, REINTERPRET_cvtop, mk_val__1_val_(F32_Fnn, v_fN), ?([$reinterpret__($valtype_Fnn(F32_Fnn), $valtype_Inn(I32_Inn), mk_val__1_val_(F32_Fnn, v_fN))]))
    -- if ($size($valtype_Inn(I32_Inn)) = $size($valtype_Fnn(F32_Fnn)))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), $reinterpret__($valtype_Fnn(F32_Fnn), $valtype_Inn(I32_Inn), mk_val__1_val_(F32_Fnn, v_fN)))
    -- wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, v_fN))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_17{v_fN : fN}:
    `%%%%%`(F64_valtype, I32_valtype, REINTERPRET_cvtop, mk_val__1_val_(F64_Fnn, v_fN), ?([$reinterpret__($valtype_Fnn(F64_Fnn), $valtype_Inn(I32_Inn), mk_val__1_val_(F64_Fnn, v_fN))]))
    -- if ($size($valtype_Inn(I32_Inn)) = $size($valtype_Fnn(F64_Fnn)))
    -- wf_val_: `%%`($valtype_Inn(I32_Inn), $reinterpret__($valtype_Fnn(F64_Fnn), $valtype_Inn(I32_Inn), mk_val__1_val_(F64_Fnn, v_fN)))
    -- wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, v_fN))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_18{v_fN : fN}:
    `%%%%%`(F32_valtype, I64_valtype, REINTERPRET_cvtop, mk_val__1_val_(F32_Fnn, v_fN), ?([$reinterpret__($valtype_Fnn(F32_Fnn), $valtype_Inn(I64_Inn), mk_val__1_val_(F32_Fnn, v_fN))]))
    -- if ($size($valtype_Inn(I64_Inn)) = $size($valtype_Fnn(F32_Fnn)))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), $reinterpret__($valtype_Fnn(F32_Fnn), $valtype_Inn(I64_Inn), mk_val__1_val_(F32_Fnn, v_fN)))
    -- wf_val_: `%%`($valtype_Fnn(F32_Fnn), mk_val__1_val_(F32_Fnn, v_fN))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_19{v_fN : fN}:
    `%%%%%`(F64_valtype, I64_valtype, REINTERPRET_cvtop, mk_val__1_val_(F64_Fnn, v_fN), ?([$reinterpret__($valtype_Fnn(F64_Fnn), $valtype_Inn(I64_Inn), mk_val__1_val_(F64_Fnn, v_fN))]))
    -- if ($size($valtype_Inn(I64_Inn)) = $size($valtype_Fnn(F64_Fnn)))
    -- wf_val_: `%%`($valtype_Inn(I64_Inn), $reinterpret__($valtype_Fnn(F64_Fnn), $valtype_Inn(I64_Inn), mk_val__1_val_(F64_Fnn, v_fN)))
    -- wf_val_: `%%`($valtype_Fnn(F64_Fnn), mk_val__1_val_(F64_Fnn, v_fN))

  ;; ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14
  rule fun_cvtop___case_20{x0 : valtype, x1 : valtype, x2 : cvtop, x3 : val_}:
    `%%%%%`(x0, x1, x2, x3, ?())
    -- ~ fun_cvtop___before_fun_cvtop___case_20: `%%%%`(x0, x1, x2, x3)

;; ../specification/wasm-1.0/3-numerics.spectec:56.1-56.102
def $ibytes_(v_N : N, v_iN : iN) : byte*

;; ../specification/wasm-1.0/3-numerics.spectec:57.1-57.102
def $fbytes_(v_N : N, v_fN : fN) : byte*

;; ../specification/wasm-1.0/3-numerics.spectec:58.1-58.75
def $bytes_(v_valtype : valtype, v_val_ : val_) : byte*

;; ../specification/wasm-1.0/3-numerics.spectec:60.1-60.75
def $inv_ibytes_(v_N : N, var_0_lst : byte*) : iN

;; ../specification/wasm-1.0/3-numerics.spectec:61.1-61.75
def $inv_fbytes_(v_N : N, var_0_lst : byte*) : fN

;; ../specification/wasm-1.0/3-numerics.spectec:62.1-62.73
def $inv_bytes_(v_valtype : valtype, var_0_lst : byte*) : val_

;; ../specification/wasm-1.0/3-numerics.spectec:78.1-78.29
def $inot_(v_N : N, v_iN : iN) : iN

;; ../specification/wasm-1.0/3-numerics.spectec:90.6-90.12
relation fun_inez_: `%%%`(N, iN, u32)
  ;; ../specification/wasm-1.0/3-numerics.spectec:90.6-90.12
  rule fun_inez__case_0{v_N : nat, i_1 : uN}:
    `%%%`(v_N, i_1, mk_uN_u32($bool(($proj_uN_0(i_1).0 =/= 0))))
    -- wf_uN: `%%`(32, mk_uN_uN($bool(($proj_uN_0(i_1).0 =/= 0))))

;; ../specification/wasm-1.0/4-runtime.spectec:5.1-5.39
syntax addr = nat

;; ../specification/wasm-1.0/4-runtime.spectec:6.1-6.53
syntax funcaddr = addr

;; ../specification/wasm-1.0/4-runtime.spectec:7.1-7.53
syntax globaladdr = addr

;; ../specification/wasm-1.0/4-runtime.spectec:8.1-8.51
syntax tableaddr = addr

;; ../specification/wasm-1.0/4-runtime.spectec:9.1-9.50
syntax memaddr = addr

;; ../specification/wasm-1.0/4-runtime.spectec:20.1-21.70
syntax externaddr = 
  | FUNC(v_funcaddr : funcaddr)
  | GLOBAL(v_globaladdr : globaladdr)
  | TABLE(v_tableaddr : tableaddr)
  | MEM(v_memaddr : memaddr)

;; ../specification/wasm-1.0/4-runtime.spectec:32.1-33.55
syntax val = 
  | CONST(v_valtype : valtype, val_)

;; ../specification/wasm-1.0/4-runtime.spectec:32.8-32.11
relation wf_val: `%`(val)
  ;; ../specification/wasm-1.0/4-runtime.spectec:32.8-32.11
  rule val_case_0{v_valtype : valtype, var_0 : val_}:
    `%`(CONST_val(v_valtype, var_0))
    -- wf_val_: `%%`(v_valtype, var_0)

;; ../specification/wasm-1.0/4-runtime.spectec:35.1-36.22
syntax result = 
  | _VALS(val_lst : val*)
  | TRAP

;; ../specification/wasm-1.0/4-runtime.spectec:35.8-35.14
relation wf_result: `%`(result)
  ;; ../specification/wasm-1.0/4-runtime.spectec:35.8-35.14
  rule result_case_0{val_lst : val*}:
    `%`(_VALS_result(val_lst))
    -- (wf_val: `%`(v_val))*{v_val <- val_lst}

  ;; ../specification/wasm-1.0/4-runtime.spectec:35.8-35.14
  rule result_case_1:
    `%`(TRAP_result)

;; ../specification/wasm-1.0/4-runtime.spectec:61.1-63.22
syntax exportinst = 
{
  NAME name,
  ADDR externaddr
}

;; ../specification/wasm-1.0/4-runtime.spectec:61.8-61.18
relation wf_exportinst: `%`(exportinst)
  ;; ../specification/wasm-1.0/4-runtime.spectec:61.8-61.18
  rule exportinst_case_{var_0 : name, var_1 : externaddr}:
    `%`({NAME var_0, ADDR var_1})
    -- wf_name: `%`(var_0)

;; ../specification/wasm-1.0/4-runtime.spectec:65.1-71.26
syntax moduleinst = 
{
  TYPES functype*,
  FUNCS funcaddr*,
  GLOBALS globaladdr*,
  TABLES tableaddr*,
  MEMS memaddr*,
  EXPORTS exportinst*
}

;; ../specification/wasm-1.0/4-runtime.spectec:65.8-65.18
relation wf_moduleinst: `%`(moduleinst)
  ;; ../specification/wasm-1.0/4-runtime.spectec:65.8-65.18
  rule moduleinst_case_{var_0_lst : functype*, var_1_lst : funcaddr*, var_2_lst : globaladdr*, var_3_lst : tableaddr*, var_4_lst : memaddr*, var_5_lst : exportinst*}:
    `%`({TYPES var_0_lst, FUNCS var_1_lst, GLOBALS var_2_lst, TABLES var_3_lst, MEMS var_4_lst, EXPORTS var_5_lst})
    -- (wf_exportinst: `%`(var_5))*{var_5 <- var_5_lst}

;; ../specification/wasm-1.0/4-runtime.spectec:48.1-51.16
syntax funcinst = 
{
  TYPE functype,
  MODULE moduleinst,
  CODE func
}

;; ../specification/wasm-1.0/4-runtime.spectec:48.8-48.16
relation wf_funcinst: `%`(funcinst)
  ;; ../specification/wasm-1.0/4-runtime.spectec:48.8-48.16
  rule funcinst_case_{var_0 : functype, var_1 : moduleinst, var_2 : func}:
    `%`({TYPE var_0, MODULE var_1, CODE var_2})
    -- wf_moduleinst: `%`(var_1)
    -- wf_func: `%`(var_2)

;; ../specification/wasm-1.0/4-runtime.spectec:52.1-54.16
syntax globalinst = 
{
  TYPE globaltype,
  VALUE val
}

;; ../specification/wasm-1.0/4-runtime.spectec:52.8-52.18
relation wf_globalinst: `%`(globalinst)
  ;; ../specification/wasm-1.0/4-runtime.spectec:52.8-52.18
  rule globalinst_case_{var_0 : globaltype, var_1 : val}:
    `%`({TYPE var_0, VALUE var_1})
    -- wf_val: `%`(var_1)

;; ../specification/wasm-1.0/4-runtime.spectec:55.1-57.24
syntax tableinst = 
{
  TYPE tabletype,
  REFS funcaddr?*
}

;; ../specification/wasm-1.0/4-runtime.spectec:55.8-55.17
relation wf_tableinst: `%`(tableinst)
  ;; ../specification/wasm-1.0/4-runtime.spectec:55.8-55.17
  rule tableinst_case_{var_0 : tabletype, var_1_opt_lst : funcaddr?*}:
    `%`({TYPE var_0, REFS var_1_opt_lst})
    -- wf_limits: `%`(var_0)

;; ../specification/wasm-1.0/4-runtime.spectec:58.1-60.18
syntax meminst = 
{
  TYPE memtype,
  BYTES byte*
}

;; ../specification/wasm-1.0/4-runtime.spectec:58.8-58.15
relation wf_meminst: `%`(meminst)
  ;; ../specification/wasm-1.0/4-runtime.spectec:58.8-58.15
  rule meminst_case_{var_0 : memtype, var_1_lst : byte*}:
    `%`({TYPE var_0, BYTES var_1_lst})
    -- wf_limits: `%`(var_0)
    -- (wf_byte: `%`(var_1))*{var_1 <- var_1_lst}

;; ../specification/wasm-1.0/4-runtime.spectec:83.1-87.20
syntax store = 
{
  FUNCS funcinst*,
  GLOBALS globalinst*,
  TABLES tableinst*,
  MEMS meminst*
}

;; ../specification/wasm-1.0/4-runtime.spectec:83.8-83.13
relation wf_store: `%`(store)
  ;; ../specification/wasm-1.0/4-runtime.spectec:83.8-83.13
  rule store_case_{var_0_lst : funcinst*, var_1_lst : globalinst*, var_2_lst : tableinst*, var_3_lst : meminst*}:
    `%`({FUNCS var_0_lst, GLOBALS var_1_lst, TABLES var_2_lst, MEMS var_3_lst})
    -- (wf_funcinst: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_globalinst: `%`(var_1))*{var_1 <- var_1_lst}
    -- (wf_tableinst: `%`(var_2))*{var_2 <- var_2_lst}
    -- (wf_meminst: `%`(var_3))*{var_3 <- var_3_lst}

;; ../specification/wasm-1.0/4-runtime.spectec:89.1-91.24
syntax frame = 
{
  LOCALS val*,
  MODULE moduleinst
}

;; ../specification/wasm-1.0/4-runtime.spectec:89.8-89.13
relation wf_frame: `%`(frame)
  ;; ../specification/wasm-1.0/4-runtime.spectec:89.8-89.13
  rule frame_case_{var_0_lst : val*, var_1 : moduleinst}:
    `%`({LOCALS var_0_lst, MODULE var_1})
    -- (wf_val: `%`(var_0))*{var_0 <- var_0_lst}
    -- wf_moduleinst: `%`(var_1)

;; ../specification/wasm-1.0/4-runtime.spectec:93.1-93.47
syntax state = 
  | mk_state(v_store : store, v_frame : frame)

;; ../specification/wasm-1.0/4-runtime.spectec:93.8-93.13
relation wf_state: `%`(state)
  ;; ../specification/wasm-1.0/4-runtime.spectec:93.8-93.13
  rule state_case_0{v_store : store, v_frame : frame}:
    `%`(mk_state_state(v_store, v_frame))
    -- wf_store: `%`(v_store)
    -- wf_frame: `%`(v_frame)

;; ../specification/wasm-1.0/4-runtime.spectec:105.1-110.9
rec {

;; ../specification/wasm-1.0/4-runtime.spectec:105.1-110.9
syntax admininstr = 
  | NOP
  | UNREACHABLE
  | DROP
  | SELECT
  | BLOCK(v_blocktype : blocktype, instr_lst : instr*)
  | LOOP(v_blocktype : blocktype, instr_lst : instr*)
  | `IF%%ELSE%`(v_blocktype : blocktype, instr_lst : instr*, instr_lst : instr*)
  | BR(v_labelidx : labelidx)
  | BR_IF(v_labelidx : labelidx)
  | BR_TABLE(labelidx_lst : labelidx*, v_labelidx : labelidx)
  | CALL(v_funcidx : funcidx)
  | CALL_INDIRECT(v_typeidx : typeidx)
  | RETURN
  | CONST(v_valtype : valtype, val_)
  | UNOP(v_valtype : valtype, unop_)
  | BINOP(v_valtype : valtype, binop_)
  | TESTOP(v_valtype : valtype, testop_)
  | RELOP(v_valtype : valtype, relop_)
  | CVTOP(valtype_1 : valtype, valtype_2 : valtype, v_cvtop : cvtop)
  | LOCAL_GET(v_localidx : localidx)
  | LOCAL_SET(v_localidx : localidx)
  | LOCAL_TEE(v_localidx : localidx)
  | GLOBAL_GET(v_globalidx : globalidx)
  | GLOBAL_SET(v_globalidx : globalidx)
  | LOAD(v_valtype : valtype, loadop_?, v_memarg : memarg)
  | STORE(v_valtype : valtype, sz_opt : sz?, v_memarg : memarg)
  | MEMORY_SIZE
  | MEMORY_GROW
  | CALL_ADDR(v_funcaddr : funcaddr)
  | `LABEL_%{%}%`(v_n : n, instr_lst : instr*, admininstr_lst : admininstr*)
  | `FRAME_%{%}%`(v_n : n, v_frame : frame, admininstr_lst : admininstr*)
  | TRAP
}

def $admininstr_instr(var_0 : instr) : admininstr
  def $admininstr_instr(NOP_instr) = NOP_admininstr
  def $admininstr_instr(UNREACHABLE_instr) = UNREACHABLE_admininstr
  def $admininstr_instr(DROP_instr) = DROP_admininstr
  def $admininstr_instr(SELECT_instr) = SELECT_admininstr
  def $admininstr_instr{x0 : blocktype, x1 : instr*}(BLOCK_instr(x0, x1)) = BLOCK_admininstr(x0, x1)
  def $admininstr_instr{x0 : blocktype, x1 : instr*}(LOOP_instr(x0, x1)) = LOOP_admininstr(x0, x1)
  def $admininstr_instr{x0 : blocktype, x1 : instr*, x2 : instr*}(`IF%%ELSE%`_instr(x0, x1, x2)) = `IF%%ELSE%`_admininstr(x0, x1, x2)
  def $admininstr_instr{x0 : labelidx}(BR_instr(x0)) = BR_admininstr(x0)
  def $admininstr_instr{x0 : labelidx}(BR_IF_instr(x0)) = BR_IF_admininstr(x0)
  def $admininstr_instr{x0 : labelidx*, x1 : labelidx}(BR_TABLE_instr(x0, x1)) = BR_TABLE_admininstr(x0, x1)
  def $admininstr_instr{x0 : funcidx}(CALL_instr(x0)) = CALL_admininstr(x0)
  def $admininstr_instr{x0 : typeidx}(CALL_INDIRECT_instr(x0)) = CALL_INDIRECT_admininstr(x0)
  def $admininstr_instr(RETURN_instr) = RETURN_admininstr
  def $admininstr_instr{x0 : valtype, x1 : val_}(CONST_instr(x0, x1)) = CONST_admininstr(x0, x1)
  def $admininstr_instr{x0 : valtype, x1 : unop_}(UNOP_instr(x0, x1)) = UNOP_admininstr(x0, x1)
  def $admininstr_instr{x0 : valtype, x1 : binop_}(BINOP_instr(x0, x1)) = BINOP_admininstr(x0, x1)
  def $admininstr_instr{x0 : valtype, x1 : testop_}(TESTOP_instr(x0, x1)) = TESTOP_admininstr(x0, x1)
  def $admininstr_instr{x0 : valtype, x1 : relop_}(RELOP_instr(x0, x1)) = RELOP_admininstr(x0, x1)
  def $admininstr_instr{x0 : valtype, x1 : valtype, x2 : cvtop}(CVTOP_instr(x0, x1, x2)) = CVTOP_admininstr(x0, x1, x2)
  def $admininstr_instr{x0 : localidx}(LOCAL_GET_instr(x0)) = LOCAL_GET_admininstr(x0)
  def $admininstr_instr{x0 : localidx}(LOCAL_SET_instr(x0)) = LOCAL_SET_admininstr(x0)
  def $admininstr_instr{x0 : localidx}(LOCAL_TEE_instr(x0)) = LOCAL_TEE_admininstr(x0)
  def $admininstr_instr{x0 : globalidx}(GLOBAL_GET_instr(x0)) = GLOBAL_GET_admininstr(x0)
  def $admininstr_instr{x0 : globalidx}(GLOBAL_SET_instr(x0)) = GLOBAL_SET_admininstr(x0)
  def $admininstr_instr{x0 : valtype, x1 : loadop_?, x2 : memarg}(LOAD_instr(x0, x1, x2)) = LOAD_admininstr(x0, x1, x2)
  def $admininstr_instr{x0 : valtype, x1 : sz?, x2 : memarg}(STORE_instr(x0, x1, x2)) = STORE_admininstr(x0, x1, x2)
  def $admininstr_instr(MEMORY_SIZE_instr) = MEMORY_SIZE_admininstr
  def $admininstr_instr(MEMORY_GROW_instr) = MEMORY_GROW_admininstr

def $admininstr_val(var_0 : val) : admininstr
  def $admininstr_val{x0 : valtype, x1 : val_}(CONST_val(x0, x1)) = CONST_admininstr(x0, x1)

;; ../specification/wasm-1.0/4-runtime.spectec:105.1-110.9
rec {

;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
relation wf_admininstr: `%`(admininstr)
  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_0:
    `%`(NOP_admininstr)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_1:
    `%`(UNREACHABLE_admininstr)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_2:
    `%`(DROP_admininstr)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_3:
    `%`(SELECT_admininstr)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_4{v_blocktype : blocktype, instr_lst : instr*}:
    `%`(BLOCK_admininstr(v_blocktype, instr_lst))
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_5{v_blocktype : blocktype, instr_lst : instr*}:
    `%`(LOOP_admininstr(v_blocktype, instr_lst))
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_6{v_blocktype : blocktype, instr_lst : instr*, instr_lst_0_lst : instr*}:
    `%`(`IF%%ELSE%`_admininstr(v_blocktype, instr_lst, instr_lst_0_lst))
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}
    -- (wf_instr: `%`(instr_lst_0))*{instr_lst_0 <- instr_lst_0_lst}

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_7{v_labelidx : labelidx}:
    `%`(BR_admininstr(v_labelidx))
    -- wf_uN: `%%`(32, v_labelidx)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_8{v_labelidx : labelidx}:
    `%`(BR_IF_admininstr(v_labelidx))
    -- wf_uN: `%%`(32, v_labelidx)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_9{labelidx_lst : labelidx*, v_labelidx : labelidx}:
    `%`(BR_TABLE_admininstr(labelidx_lst, v_labelidx))
    -- (wf_uN: `%%`(32, v_labelidx))*{v_labelidx <- labelidx_lst}
    -- wf_uN: `%%`(32, v_labelidx)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_10{v_funcidx : funcidx}:
    `%`(CALL_admininstr(v_funcidx))
    -- wf_uN: `%%`(32, v_funcidx)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_11{v_typeidx : typeidx}:
    `%`(CALL_INDIRECT_admininstr(v_typeidx))
    -- wf_uN: `%%`(32, v_typeidx)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_12:
    `%`(RETURN_admininstr)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_13{v_valtype : valtype, var_0 : val_}:
    `%`(CONST_admininstr(v_valtype, var_0))
    -- wf_val_: `%%`(v_valtype, var_0)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_14{v_valtype : valtype, var_0 : unop_}:
    `%`(UNOP_admininstr(v_valtype, var_0))
    -- wf_unop_: `%%`(v_valtype, var_0)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_15{v_valtype : valtype, var_0 : binop_}:
    `%`(BINOP_admininstr(v_valtype, var_0))
    -- wf_binop_: `%%`(v_valtype, var_0)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_16{v_valtype : valtype, var_0 : testop_}:
    `%`(TESTOP_admininstr(v_valtype, var_0))
    -- wf_testop_: `%%`(v_valtype, var_0)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_17{v_valtype : valtype, var_0 : relop_}:
    `%`(RELOP_admininstr(v_valtype, var_0))
    -- wf_relop_: `%%`(v_valtype, var_0)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_18{valtype_1 : valtype, valtype_2 : valtype, v_cvtop : cvtop}:
    `%`(CVTOP_admininstr(valtype_1, valtype_2, v_cvtop))
    -- if (valtype_1 =/= valtype_2)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_19{v_localidx : localidx}:
    `%`(LOCAL_GET_admininstr(v_localidx))
    -- wf_uN: `%%`(32, v_localidx)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_20{v_localidx : localidx}:
    `%`(LOCAL_SET_admininstr(v_localidx))
    -- wf_uN: `%%`(32, v_localidx)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_21{v_localidx : localidx}:
    `%`(LOCAL_TEE_admininstr(v_localidx))
    -- wf_uN: `%%`(32, v_localidx)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_22{v_globalidx : globalidx}:
    `%`(GLOBAL_GET_admininstr(v_globalidx))
    -- wf_uN: `%%`(32, v_globalidx)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_23{v_globalidx : globalidx}:
    `%`(GLOBAL_SET_admininstr(v_globalidx))
    -- wf_uN: `%%`(32, v_globalidx)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_24{v_valtype : valtype, var_0_opt : loadop_?, v_memarg : memarg}:
    `%`(LOAD_admininstr(v_valtype, var_0_opt, v_memarg))
    -- (wf_loadop_: `%%`(v_valtype, var_0))?{var_0 <- var_0_opt}
    -- wf_memarg: `%`(v_memarg)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_25{Inn_opt : Inn?, v_valtype : valtype, sz_opt : sz?, v_memarg : memarg}:
    `%`(STORE_admininstr(v_valtype, sz_opt, v_memarg))
    -- (wf_sz: `%`(v_sz))?{v_sz <- sz_opt}
    -- wf_memarg: `%`(v_memarg)
    -- if ((Inn_opt = ?()) <=> (sz_opt = ?()))
    -- (if ((v_valtype = $valtype_Inn(v_Inn)) /\ ($proj_sz_0(v_sz).0 < $size($valtype_Inn(v_Inn)))))?{v_Inn <- Inn_opt, v_sz <- sz_opt}

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_26:
    `%`(MEMORY_SIZE_admininstr)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_27:
    `%`(MEMORY_GROW_admininstr)

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_28{v_funcaddr : funcaddr}:
    `%`(CALL_ADDR_admininstr(v_funcaddr))

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_29{v_n : n, instr_lst : instr*, admininstr_lst : admininstr*}:
    `%`(`LABEL_%{%}%`_admininstr(v_n, instr_lst, admininstr_lst))
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}
    -- (wf_admininstr: `%`(v_admininstr))*{v_admininstr <- admininstr_lst}

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_30{v_n : n, v_frame : frame, admininstr_lst : admininstr*}:
    `%`(`FRAME_%{%}%`_admininstr(v_n, v_frame, admininstr_lst))
    -- wf_frame: `%`(v_frame)
    -- (wf_admininstr: `%`(v_admininstr))*{v_admininstr <- admininstr_lst}

  ;; ../specification/wasm-1.0/4-runtime.spectec:105.8-105.18
  rule admininstr_case_31:
    `%`(TRAP_admininstr)
}

;; ../specification/wasm-1.0/4-runtime.spectec:94.1-94.62
syntax config = 
  | mk_config(v_state : state, admininstr_lst : admininstr*)

;; ../specification/wasm-1.0/4-runtime.spectec:94.8-94.14
relation wf_config: `%`(config)
  ;; ../specification/wasm-1.0/4-runtime.spectec:94.8-94.14
  rule config_case_0{v_state : state, admininstr_lst : admininstr*}:
    `%`(mk_config_config(v_state, admininstr_lst))
    -- wf_state: `%`(v_state)
    -- (wf_admininstr: `%`(v_admininstr))*{v_admininstr <- admininstr_lst}

;; ../specification/wasm-1.0/5-runtime-aux.spectec:7.6-7.15
relation fun_default_: `%%`(valtype, val)
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:7.6-7.15
  rule fun_default__case_0:
    `%%`(I32_valtype, CONST_val(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(0))))
    -- wf_val: `%`(CONST_val(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(0))))

  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:7.6-7.15
  rule fun_default__case_1:
    `%%`(I64_valtype, CONST_val(I64_valtype, mk_val__0_val_(I64_Inn, mk_uN_uN(0))))
    -- wf_val: `%`(CONST_val(I64_valtype, mk_val__0_val_(I64_Inn, mk_uN_uN(0))))

  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:7.6-7.15
  rule fun_default__case_2{var_0 : fN}:
    `%%`(F32_valtype, CONST_val(F32_valtype, mk_val__1_val_(F32_Fnn, var_0)))
    -- fun_fzero: `%%`(32, var_0)
    -- wf_val: `%`(CONST_val(F32_valtype, mk_val__1_val_(F32_Fnn, var_0)))

  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:7.6-7.15
  rule fun_default__case_3{var_0 : fN}:
    `%%`(F64_valtype, CONST_val(F64_valtype, mk_val__1_val_(F64_Fnn, var_0)))
    -- fun_fzero: `%%`(64, var_0)
    -- wf_val: `%`(CONST_val(F64_valtype, mk_val__1_val_(F64_Fnn, var_0)))

;; ../specification/wasm-1.0/5-runtime-aux.spectec:17.1-17.63
rec {

;; ../specification/wasm-1.0/5-runtime-aux.spectec:17.6-17.14
relation fun_funcsxa: `%%`(externaddr*, funcaddr*)
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:17.6-17.14
  rule fun_funcsxa_case_0:
    `%%`([], [])

  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:17.6-17.14
  rule fun_funcsxa_case_1{fa : nat, xv_lst : externaddr*, var_0 : funcaddr*}:
    `%%`([FUNC_externaddr(fa)] ++ xv_lst, [fa] ++ var_0)
    -- fun_funcsxa: `%%`(xv_lst, var_0)

  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:17.6-17.14
  rule fun_funcsxa_case_2{v_externaddr : externaddr, xv_lst : externaddr*, var_0 : funcaddr*}:
    `%%`([v_externaddr] ++ xv_lst, var_0)
    -- fun_funcsxa: `%%`(xv_lst, var_0)
}

;; ../specification/wasm-1.0/5-runtime-aux.spectec:18.1-18.65
rec {

;; ../specification/wasm-1.0/5-runtime-aux.spectec:18.6-18.16
relation fun_globalsxa: `%%`(externaddr*, globaladdr*)
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:18.6-18.16
  rule fun_globalsxa_case_0:
    `%%`([], [])

  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:18.6-18.16
  rule fun_globalsxa_case_1{ga : nat, xv_lst : externaddr*, var_0 : globaladdr*}:
    `%%`([GLOBAL_externaddr(ga)] ++ xv_lst, [ga] ++ var_0)
    -- fun_globalsxa: `%%`(xv_lst, var_0)

  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:18.6-18.16
  rule fun_globalsxa_case_2{v_externaddr : externaddr, xv_lst : externaddr*, var_0 : globaladdr*}:
    `%%`([v_externaddr] ++ xv_lst, var_0)
    -- fun_globalsxa: `%%`(xv_lst, var_0)
}

;; ../specification/wasm-1.0/5-runtime-aux.spectec:19.1-19.64
rec {

;; ../specification/wasm-1.0/5-runtime-aux.spectec:19.6-19.15
relation fun_tablesxa: `%%`(externaddr*, tableaddr*)
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:19.6-19.15
  rule fun_tablesxa_case_0:
    `%%`([], [])

  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:19.6-19.15
  rule fun_tablesxa_case_1{ta : nat, xv_lst : externaddr*, var_0 : tableaddr*}:
    `%%`([TABLE_externaddr(ta)] ++ xv_lst, [ta] ++ var_0)
    -- fun_tablesxa: `%%`(xv_lst, var_0)

  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:19.6-19.15
  rule fun_tablesxa_case_2{v_externaddr : externaddr, xv_lst : externaddr*, var_0 : tableaddr*}:
    `%%`([v_externaddr] ++ xv_lst, var_0)
    -- fun_tablesxa: `%%`(xv_lst, var_0)
}

;; ../specification/wasm-1.0/5-runtime-aux.spectec:20.1-20.62
rec {

;; ../specification/wasm-1.0/5-runtime-aux.spectec:20.6-20.13
relation fun_memsxa: `%%`(externaddr*, memaddr*)
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:20.6-20.13
  rule fun_memsxa_case_0:
    `%%`([], [])

  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:20.6-20.13
  rule fun_memsxa_case_1{ma : nat, xv_lst : externaddr*, var_0 : memaddr*}:
    `%%`([MEM_externaddr(ma)] ++ xv_lst, [ma] ++ var_0)
    -- fun_memsxa: `%%`(xv_lst, var_0)

  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:20.6-20.13
  rule fun_memsxa_case_2{v_externaddr : externaddr, xv_lst : externaddr*, var_0 : memaddr*}:
    `%%`([v_externaddr] ++ xv_lst, var_0)
    -- fun_memsxa: `%%`(xv_lst, var_0)
}

;; ../specification/wasm-1.0/5-runtime-aux.spectec:46.1-46.57
def $fun_store(v_state : state) : store
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:49.1-49.23
  def $fun_store{s : store, f : frame}(mk_state_state(s, f)) = s

;; ../specification/wasm-1.0/5-runtime-aux.spectec:47.1-47.57
def $fun_frame(v_state : state) : frame
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:50.1-50.23
  def $fun_frame{s : store, f : frame}(mk_state_state(s, f)) = f

;; ../specification/wasm-1.0/5-runtime-aux.spectec:53.1-53.64
def $fun_funcaddr(v_state : state) : funcaddr*
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:54.1-54.39
  def $fun_funcaddr{s : store, f : frame}(mk_state_state(s, f)) = f.MODULE_frame.FUNCS_moduleinst

;; ../specification/wasm-1.0/5-runtime-aux.spectec:56.1-56.57
def $fun_funcinst(v_state : state) : funcinst*
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:62.1-62.32
  def $fun_funcinst{s : store, f : frame}(mk_state_state(s, f)) = s.FUNCS_store

;; ../specification/wasm-1.0/5-runtime-aux.spectec:57.1-57.59
def $fun_globalinst(v_state : state) : globalinst*
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:63.1-63.36
  def $fun_globalinst{s : store, f : frame}(mk_state_state(s, f)) = s.GLOBALS_store

;; ../specification/wasm-1.0/5-runtime-aux.spectec:58.1-58.58
def $fun_tableinst(v_state : state) : tableinst*
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:64.1-64.34
  def $fun_tableinst{s : store, f : frame}(mk_state_state(s, f)) = s.TABLES_store

;; ../specification/wasm-1.0/5-runtime-aux.spectec:59.1-59.56
def $fun_meminst(v_state : state) : meminst*
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:65.1-65.30
  def $fun_meminst{s : store, f : frame}(mk_state_state(s, f)) = s.MEMS_store

;; ../specification/wasm-1.0/5-runtime-aux.spectec:60.1-60.58
def $fun_moduleinst(v_state : state) : moduleinst
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:66.1-66.35
  def $fun_moduleinst{s : store, f : frame}(mk_state_state(s, f)) = f.MODULE_frame

;; ../specification/wasm-1.0/5-runtime-aux.spectec:68.1-68.66
def $fun_type(v_state : state, v_typeidx : typeidx) : functype
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:75.1-75.41
  def $fun_type{s : store, f : frame, x : uN}(mk_state_state(s, f), x) = f.MODULE_frame.TYPES_moduleinst[$proj_uN_0(x).0]

;; ../specification/wasm-1.0/5-runtime-aux.spectec:69.1-69.66
def $fun_func(v_state : state, v_funcidx : funcidx) : funcinst
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:76.1-76.50
  def $fun_func{s : store, f : frame, x : uN}(mk_state_state(s, f), x) = s.FUNCS_store[f.MODULE_frame.FUNCS_moduleinst[$proj_uN_0(x).0]]

;; ../specification/wasm-1.0/5-runtime-aux.spectec:70.1-70.68
def $fun_global(v_state : state, v_globalidx : globalidx) : globalinst
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:77.1-77.56
  def $fun_global{s : store, f : frame, x : uN}(mk_state_state(s, f), x) = s.GLOBALS_store[f.MODULE_frame.GLOBALS_moduleinst[$proj_uN_0(x).0]]

;; ../specification/wasm-1.0/5-runtime-aux.spectec:71.1-71.67
def $fun_table(v_state : state, v_tableidx : tableidx) : tableinst
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:78.1-78.53
  def $fun_table{s : store, f : frame, x : uN}(mk_state_state(s, f), x) = s.TABLES_store[f.MODULE_frame.TABLES_moduleinst[$proj_uN_0(x).0]]

;; ../specification/wasm-1.0/5-runtime-aux.spectec:72.1-72.65
def $fun_mem(v_state : state, v_memidx : memidx) : meminst
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:79.1-79.47
  def $fun_mem{s : store, f : frame, x : uN}(mk_state_state(s, f), x) = s.MEMS_store[f.MODULE_frame.MEMS_moduleinst[$proj_uN_0(x).0]]

;; ../specification/wasm-1.0/5-runtime-aux.spectec:73.1-73.67
def $fun_local(v_state : state, v_localidx : localidx) : val
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:80.1-80.36
  def $fun_local{s : store, f : frame, x : uN}(mk_state_state(s, f), x) = f.LOCALS_frame[$proj_uN_0(x).0]

;; ../specification/wasm-1.0/5-runtime-aux.spectec:85.6-85.17
relation fun_with_local: `%%%%`(state, localidx, val, state)
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:85.6-85.17
  rule fun_with_local_case_0{s : store, f : frame, x : uN, v : val}:
    `%%%%`(mk_state_state(s, f), x, v, mk_state_state(s, f[LOCALS_frame[$proj_uN_0(x).0] = v]))
    -- wf_state: `%`(mk_state_state(s, f[LOCALS_frame[$proj_uN_0(x).0] = v]))

;; ../specification/wasm-1.0/5-runtime-aux.spectec:86.6-86.18
relation fun_with_global: `%%%%`(state, globalidx, val, state)
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:86.6-86.18
  rule fun_with_global_case_0{s : store, f : frame, x : uN, v : val}:
    `%%%%`(mk_state_state(s, f), x, v, mk_state_state(s[GLOBALS_store[f.MODULE_frame.GLOBALS_moduleinst[$proj_uN_0(x).0]].VALUE_globalinst = v], f))
    -- if ($proj_uN_0(x).0 < |f.MODULE_frame.GLOBALS_moduleinst|)
    -- wf_state: `%`(mk_state_state(s[GLOBALS_store[f.MODULE_frame.GLOBALS_moduleinst[$proj_uN_0(x).0]].VALUE_globalinst = v], f))

;; ../specification/wasm-1.0/5-runtime-aux.spectec:87.6-87.17
relation fun_with_table: `%%%%%`(state, tableidx, nat, funcaddr, state)
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:87.6-87.17
  rule fun_with_table_case_0{s : store, f : frame, x : uN, i : nat, a : nat}:
    `%%%%%`(mk_state_state(s, f), x, i, a, mk_state_state(s[TABLES_store[f.MODULE_frame.TABLES_moduleinst[$proj_uN_0(x).0]].REFS_tableinst[i] = ?(a)], f))
    -- if ($proj_uN_0(x).0 < |f.MODULE_frame.TABLES_moduleinst|)
    -- wf_state: `%`(mk_state_state(s[TABLES_store[f.MODULE_frame.TABLES_moduleinst[$proj_uN_0(x).0]].REFS_tableinst[i] = ?(a)], f))

;; ../specification/wasm-1.0/5-runtime-aux.spectec:88.6-88.21
relation fun_with_tableinst: `%%%%`(state, tableidx, tableinst, state)
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:88.6-88.21
  rule fun_with_tableinst_case_0{s : store, f : frame, x : uN, ti : tableinst}:
    `%%%%`(mk_state_state(s, f), x, ti, mk_state_state(s[TABLES_store[f.MODULE_frame.TABLES_moduleinst[$proj_uN_0(x).0]] = ti], f))
    -- if ($proj_uN_0(x).0 < |f.MODULE_frame.TABLES_moduleinst|)
    -- wf_state: `%`(mk_state_state(s[TABLES_store[f.MODULE_frame.TABLES_moduleinst[$proj_uN_0(x).0]] = ti], f))

;; ../specification/wasm-1.0/5-runtime-aux.spectec:89.6-89.15
relation fun_with_mem: `%%%%%%`(state, memidx, nat, nat, byte*, state)
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:89.6-89.15
  rule fun_with_mem_case_0{s : store, f : frame, x : uN, i : nat, j : nat, b_lst : byte*}:
    `%%%%%%`(mk_state_state(s, f), x, i, j, b_lst, mk_state_state(s[MEMS_store[f.MODULE_frame.MEMS_moduleinst[$proj_uN_0(x).0]].BYTES_meminst[i : j] = b_lst], f))
    -- if ($proj_uN_0(x).0 < |f.MODULE_frame.MEMS_moduleinst|)
    -- wf_state: `%`(mk_state_state(s[MEMS_store[f.MODULE_frame.MEMS_moduleinst[$proj_uN_0(x).0]].BYTES_meminst[i : j] = b_lst], f))

;; ../specification/wasm-1.0/5-runtime-aux.spectec:90.6-90.19
relation fun_with_meminst: `%%%%`(state, memidx, meminst, state)
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:90.6-90.19
  rule fun_with_meminst_case_0{s : store, f : frame, x : uN, mi : meminst}:
    `%%%%`(mk_state_state(s, f), x, mi, mk_state_state(s[MEMS_store[f.MODULE_frame.MEMS_moduleinst[$proj_uN_0(x).0]] = mi], f))
    -- if ($proj_uN_0(x).0 < |f.MODULE_frame.MEMS_moduleinst|)
    -- wf_state: `%`(mk_state_state(s[MEMS_store[f.MODULE_frame.MEMS_moduleinst[$proj_uN_0(x).0]] = mi], f))

;; ../specification/wasm-1.0/5-runtime-aux.spectec:102.6-102.16
relation fun_growtable_before_fun_growtable_case_1: `%%`(tableinst, nat)
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:102.6-102.16
  rule fun_growtable_case_0{ti : tableinst, v_n : nat, ti' : tableinst, i : uN, j_opt : u32?, a_lst : addr*, i' : nat}:
    `%%`(ti, v_n)
    -- if (ti = {TYPE mk_limits_tabletype(i, j_opt), REFS ?(a_1)*{a_1 <- a_lst}})
    -- if (i' = (|a_lst| + v_n))
    -- if (ti' = {TYPE mk_limits_tabletype(mk_uN_u32(i'), j_opt), REFS ?(a_3)*{a_3 <- a_lst} ++ ?()^v_n{}})
    -- (if (i' <= $proj_uN_0(j_3).0))?{j_3 <- j_opt}
    -- wf_tableinst: `%`(ti')
    -- wf_tableinst: `%`({TYPE mk_limits_tabletype(i, j_opt), REFS ?(a_4)*{a_4 <- a_lst}})
    -- wf_tableinst: `%`({TYPE mk_limits_tabletype(mk_uN_u32(i'), j_opt), REFS ?(a_5)*{a_5 <- a_lst} ++ ?()^v_n{}})

;; ../specification/wasm-1.0/5-runtime-aux.spectec:102.6-102.16
relation fun_growtable: `%%%`(tableinst, nat, tableinst?)
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:102.6-102.16
  rule fun_growtable_case_0{ti : tableinst, v_n : nat, ti' : tableinst, i : uN, j_opt : u32?, a_lst : addr*, i' : nat}:
    `%%%`(ti, v_n, ?(ti'))
    -- if (ti = {TYPE mk_limits_tabletype(i, j_opt), REFS ?(a_1)*{a_1 <- a_lst}})
    -- if (i' = (|a_lst| + v_n))
    -- if (ti' = {TYPE mk_limits_tabletype(mk_uN_u32(i'), j_opt), REFS ?(a_3)*{a_3 <- a_lst} ++ ?()^v_n{}})
    -- (if (i' <= $proj_uN_0(j_3).0))?{j_3 <- j_opt}
    -- wf_tableinst: `%`(ti')
    -- wf_tableinst: `%`({TYPE mk_limits_tabletype(i, j_opt), REFS ?(a_4)*{a_4 <- a_lst}})
    -- wf_tableinst: `%`({TYPE mk_limits_tabletype(mk_uN_u32(i'), j_opt), REFS ?(a_5)*{a_5 <- a_lst} ++ ?()^v_n{}})

  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:102.6-102.16
  rule fun_growtable_case_1{x0 : tableinst, x1 : nat}:
    `%%%`(x0, x1, ?())
    -- ~ fun_growtable_before_fun_growtable_case_1: `%%`(x0, x1)

;; ../specification/wasm-1.0/5-runtime-aux.spectec:103.6-103.17
relation fun_growmemory_before_fun_growmemory_case_1: `%%`(meminst, nat)
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:103.6-103.17
  rule fun_growmemory_case_0{mi : meminst, v_n : nat, mi' : meminst, i : u32, j_opt : u32?, b_lst : byte*, i' : rat}:
    `%%`(mi, v_n)
    -- if ({TYPE mk_limits_memtype(i, j_opt), BYTES b_lst} = mi)
    -- if (i' = (((|b_lst| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) + (v_n : nat <:> rat)))
    -- if (mi' = {TYPE mk_limits_memtype(mk_uN_u32((i' : rat <:> nat)), j_opt), BYTES b_lst ++ mk_byte_byte(0)^(v_n * (64 * $Ki)){}})
    -- (if (i' <= ($proj_uN_0(j_8).0 : nat <:> rat)))?{j_8 <- j_opt}
    -- wf_meminst: `%`(mi')
    -- wf_meminst: `%`({TYPE mk_limits_memtype(i, j_opt), BYTES b_lst})
    -- wf_meminst: `%`({TYPE mk_limits_memtype(mk_uN_u32((i' : rat <:> nat)), j_opt), BYTES b_lst ++ mk_byte_byte(0)^(v_n * (64 * $Ki)){}})

;; ../specification/wasm-1.0/5-runtime-aux.spectec:103.6-103.17
relation fun_growmemory: `%%%`(meminst, nat, meminst?)
  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:103.6-103.17
  rule fun_growmemory_case_0{mi : meminst, v_n : nat, mi' : meminst, i : u32, j_opt : u32?, b_lst : byte*, i' : rat}:
    `%%%`(mi, v_n, ?(mi'))
    -- if ({TYPE mk_limits_memtype(i, j_opt), BYTES b_lst} = mi)
    -- if (i' = (((|b_lst| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) + (v_n : nat <:> rat)))
    -- if (mi' = {TYPE mk_limits_memtype(mk_uN_u32((i' : rat <:> nat)), j_opt), BYTES b_lst ++ mk_byte_byte(0)^(v_n * (64 * $Ki)){}})
    -- (if (i' <= ($proj_uN_0(j_8).0 : nat <:> rat)))?{j_8 <- j_opt}
    -- wf_meminst: `%`(mi')
    -- wf_meminst: `%`({TYPE mk_limits_memtype(i, j_opt), BYTES b_lst})
    -- wf_meminst: `%`({TYPE mk_limits_memtype(mk_uN_u32((i' : rat <:> nat)), j_opt), BYTES b_lst ++ mk_byte_byte(0)^(v_n * (64 * $Ki)){}})

  ;; ../specification/wasm-1.0/5-runtime-aux.spectec:103.6-103.17
  rule fun_growmemory_case_1{x0 : meminst, x1 : nat}:
    `%%%`(x0, x1, ?())
    -- ~ fun_growmemory_before_fun_growmemory_case_1: `%%`(x0, x1)

;; ../specification/wasm-1.0/6-typing.spectec:5.1-8.62
syntax context = 
{
  TYPES functype*,
  FUNCS functype*,
  GLOBALS globaltype*,
  TABLES tabletype*,
  MEMS memtype*,
  LOCALS valtype*,
  LABELS resulttype*,
  RETURN resulttype?
}

;; ../specification/wasm-1.0/6-typing.spectec:5.8-5.15
relation wf_context: `%`(context)
  ;; ../specification/wasm-1.0/6-typing.spectec:5.8-5.15
  rule context_case_{var_0_lst : functype*, var_1_lst : functype*, var_2_lst : globaltype*, var_3_lst : tabletype*, var_4_lst : memtype*, var_5_lst : valtype*, var_6_lst : resulttype*, var_7_opt : resulttype?}:
    `%`({TYPES var_0_lst, FUNCS var_1_lst, GLOBALS var_2_lst, TABLES var_3_lst, MEMS var_4_lst, LOCALS var_5_lst, LABELS var_6_lst, RETURN var_7_opt})
    -- (wf_limits: `%`(var_3))*{var_3 <- var_3_lst}
    -- (wf_limits: `%`(var_4))*{var_4 <- var_4_lst}

;; ../specification/wasm-1.0/6-typing.spectec:18.1-18.66
relation Limits_ok: `|-%:%`(limits, nat)
  ;; ../specification/wasm-1.0/6-typing.spectec:26.1-29.23
  rule mk_Limits_ok{v_n : n, m_opt : m?, k : nat}:
    `|-%:%`(mk_limits_limits(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), k)
    -- if (v_n <= k)
    -- (if ((v_n <= v_m) /\ (v_m <= k)))?{v_m <- m_opt}
    -- wf_limits: `%`(mk_limits_limits(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}))

;; ../specification/wasm-1.0/6-typing.spectec:19.1-19.64
relation Functype_ok: `|-%:OK`(functype)
  ;; ../specification/wasm-1.0/6-typing.spectec:31.1-32.23
  rule mk_Functype_ok{t_1_lst : valtype*, t_2_opt : valtype?}:
    `|-%:OK`(mk_functype_functype(t_1_lst, lift(t_2_opt)))

;; ../specification/wasm-1.0/6-typing.spectec:20.1-20.66
relation Globaltype_ok: `|-%:OK`(globaltype)
  ;; ../specification/wasm-1.0/6-typing.spectec:34.1-35.17
  rule mk_Globaltype_ok{t : valtype}:
    `|-%:OK`(mk_globaltype_globaltype(?(MUT_r_MUT), t))

;; ../specification/wasm-1.0/6-typing.spectec:21.1-21.65
relation Tabletype_ok: `|-%:OK`(tabletype)
  ;; ../specification/wasm-1.0/6-typing.spectec:37.1-39.38
  rule mk_Tabletype_ok{v_limits : limits}:
    `|-%:OK`(v_limits)
    -- Limits_ok: `|-%:%`(v_limits, ((((2 ^ 32) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))
    -- wf_limits: `%`(v_limits)

;; ../specification/wasm-1.0/6-typing.spectec:22.1-22.63
relation Memtype_ok: `|-%:OK`(memtype)
  ;; ../specification/wasm-1.0/6-typing.spectec:41.1-43.36
  rule mk_Memtype_ok{v_limits : limits}:
    `|-%:OK`(v_limits)
    -- Limits_ok: `|-%:%`(v_limits, (2 ^ 16))
    -- wf_limits: `%`(v_limits)

;; ../specification/wasm-1.0/6-typing.spectec:23.1-23.66
relation Externtype_ok: `|-%:OK`(externtype)
  ;; ../specification/wasm-1.0/6-typing.spectec:46.1-48.35
  rule func{v_functype : functype}:
    `|-%:OK`(FUNC_externtype(v_functype))
    -- Functype_ok: `|-%:OK`(v_functype)
    -- wf_externtype: `%`(FUNC_externtype(v_functype))

  ;; ../specification/wasm-1.0/6-typing.spectec:50.1-52.39
  rule global{v_globaltype : globaltype}:
    `|-%:OK`(GLOBAL_externtype(v_globaltype))
    -- Globaltype_ok: `|-%:OK`(v_globaltype)
    -- wf_externtype: `%`(GLOBAL_externtype(v_globaltype))

  ;; ../specification/wasm-1.0/6-typing.spectec:54.1-56.37
  rule table{v_tabletype : tabletype}:
    `|-%:OK`(TABLE_externtype(v_tabletype))
    -- Tabletype_ok: `|-%:OK`(v_tabletype)
    -- wf_externtype: `%`(TABLE_externtype(v_tabletype))

  ;; ../specification/wasm-1.0/6-typing.spectec:58.1-60.33
  rule mem{v_memtype : memtype}:
    `|-%:OK`(MEM_externtype(v_memtype))
    -- Memtype_ok: `|-%:OK`(v_memtype)
    -- wf_externtype: `%`(MEM_externtype(v_memtype))

;; ../specification/wasm-1.0/6-typing.spectec:70.1-70.75
relation Limits_sub: `|-%<:%`(limits, limits)
  ;; ../specification/wasm-1.0/6-typing.spectec:78.1-81.22
  rule max{n_1 : n, m_1 : m, n_2 : n, m_2_opt : m?}:
    `|-%<:%`(mk_limits_limits(mk_uN_u32(n_1), ?(mk_uN_u32(m_1))), mk_limits_limits(mk_uN_u32(n_2), mk_uN_u32(m_2)?{m_2 <- m_2_opt}))
    -- if (n_1 >= n_2)
    -- (if (m_1 <= m_2))?{m_2 <- m_2_opt}
    -- wf_limits: `%`(mk_limits_limits(mk_uN_u32(n_1), ?(mk_uN_u32(m_1))))
    -- wf_limits: `%`(mk_limits_limits(mk_uN_u32(n_2), mk_uN_u32(m_2)?{m_2 <- m_2_opt}))

  ;; ../specification/wasm-1.0/6-typing.spectec:83.1-85.19
  rule eps{n_1 : n, n_2 : n}:
    `|-%<:%`(mk_limits_limits(mk_uN_u32(n_1), ?()), mk_limits_limits(mk_uN_u32(n_2), ?()))
    -- if (n_1 >= n_2)
    -- wf_limits: `%`(mk_limits_limits(mk_uN_u32(n_1), ?()))
    -- wf_limits: `%`(mk_limits_limits(mk_uN_u32(n_2), ?()))

;; ../specification/wasm-1.0/6-typing.spectec:71.1-71.73
relation Functype_sub: `|-%<:%`(functype, functype)
  ;; ../specification/wasm-1.0/6-typing.spectec:88.1-89.14
  rule mk_Functype_sub{ft : functype}:
    `|-%<:%`(ft, ft)

;; ../specification/wasm-1.0/6-typing.spectec:72.1-72.75
relation Globaltype_sub: `|-%<:%`(globaltype, globaltype)
  ;; ../specification/wasm-1.0/6-typing.spectec:91.1-92.14
  rule mk_Globaltype_sub{gt : globaltype}:
    `|-%<:%`(gt, gt)

;; ../specification/wasm-1.0/6-typing.spectec:73.1-73.74
relation Tabletype_sub: `|-%<:%`(tabletype, tabletype)
  ;; ../specification/wasm-1.0/6-typing.spectec:94.1-96.35
  rule mk_Tabletype_sub{lim_1 : limits, lim_2 : limits}:
    `|-%<:%`(lim_1, lim_2)
    -- Limits_sub: `|-%<:%`(lim_1, lim_2)
    -- wf_limits: `%`(lim_1)
    -- wf_limits: `%`(lim_2)

;; ../specification/wasm-1.0/6-typing.spectec:74.1-74.72
relation Memtype_sub: `|-%<:%`(memtype, memtype)
  ;; ../specification/wasm-1.0/6-typing.spectec:98.1-100.35
  rule mk_Memtype_sub{lim_1 : limits, lim_2 : limits}:
    `|-%<:%`(lim_1, lim_2)
    -- Limits_sub: `|-%<:%`(lim_1, lim_2)
    -- wf_limits: `%`(lim_1)
    -- wf_limits: `%`(lim_2)

;; ../specification/wasm-1.0/6-typing.spectec:75.1-75.75
relation Externtype_sub: `|-%<:%`(externtype, externtype)
  ;; ../specification/wasm-1.0/6-typing.spectec:103.1-105.35
  rule func{ft_1 : functype, ft_2 : functype}:
    `|-%<:%`(FUNC_externtype(ft_1), FUNC_externtype(ft_2))
    -- Functype_sub: `|-%<:%`(ft_1, ft_2)
    -- wf_externtype: `%`(FUNC_externtype(ft_1))
    -- wf_externtype: `%`(FUNC_externtype(ft_2))

  ;; ../specification/wasm-1.0/6-typing.spectec:107.1-109.37
  rule global{gt_1 : globaltype, gt_2 : globaltype}:
    `|-%<:%`(GLOBAL_externtype(gt_1), GLOBAL_externtype(gt_2))
    -- Globaltype_sub: `|-%<:%`(gt_1, gt_2)
    -- wf_externtype: `%`(GLOBAL_externtype(gt_1))
    -- wf_externtype: `%`(GLOBAL_externtype(gt_2))

  ;; ../specification/wasm-1.0/6-typing.spectec:111.1-113.36
  rule table{tt_1 : tabletype, tt_2 : tabletype}:
    `|-%<:%`(TABLE_externtype(tt_1), TABLE_externtype(tt_2))
    -- Tabletype_sub: `|-%<:%`(tt_1, tt_2)
    -- wf_externtype: `%`(TABLE_externtype(tt_1))
    -- wf_externtype: `%`(TABLE_externtype(tt_2))

  ;; ../specification/wasm-1.0/6-typing.spectec:115.1-117.34
  rule mem{mt_1 : memtype, mt_2 : memtype}:
    `|-%<:%`(MEM_externtype(mt_1), MEM_externtype(mt_2))
    -- Memtype_sub: `|-%<:%`(mt_1, mt_2)
    -- wf_externtype: `%`(MEM_externtype(mt_1))
    -- wf_externtype: `%`(MEM_externtype(mt_2))

;; ../specification/wasm-1.0/6-typing.spectec:125.1-126.65
rec {

;; ../specification/wasm-1.0/6-typing.spectec:125.1-125.64
relation Instr_ok: `%|-%:%`(context, instr, functype)
  ;; ../specification/wasm-1.0/6-typing.spectec:158.1-159.24
  rule nop{C : context}:
    `%|-%:%`(C, NOP_instr, mk_functype_functype([], []))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(NOP_instr)

  ;; ../specification/wasm-1.0/6-typing.spectec:161.1-162.34
  rule unreachable{C : context, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:%`(C, UNREACHABLE_instr, mk_functype_functype(t_1_lst, t_2_lst))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(UNREACHABLE_instr)

  ;; ../specification/wasm-1.0/6-typing.spectec:164.1-165.23
  rule drop{C : context, t : valtype}:
    `%|-%:%`(C, DROP_instr, mk_functype_functype([t], []))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(DROP_instr)

  ;; ../specification/wasm-1.0/6-typing.spectec:167.1-168.29
  rule select{C : context, t : valtype}:
    `%|-%:%`(C, SELECT_instr, mk_functype_functype([t t I32_valtype], [t]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(SELECT_instr)

  ;; ../specification/wasm-1.0/6-typing.spectec:173.1-175.57
  rule block{C : context, t_opt : valtype?, instr_lst : instr*}:
    `%|-%:%`(C, BLOCK_instr(t_opt, instr_lst), mk_functype_functype([], lift(t_opt)))
    -- Instrs_ok: `%|-%:%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t_opt], RETURN ?()} +++ C, instr_lst, mk_functype_functype([], lift(t_opt)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BLOCK_instr(t_opt, instr_lst))
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t_opt], RETURN ?()})

  ;; ../specification/wasm-1.0/6-typing.spectec:177.1-179.59
  rule loop{C : context, t_opt : valtype?, instr_lst : instr*}:
    `%|-%:%`(C, LOOP_instr(t_opt, instr_lst), mk_functype_functype([], lift(t_opt)))
    -- Instrs_ok: `%|-%:%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [?()], RETURN ?()} +++ C, instr_lst, mk_functype_functype([], []))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOOP_instr(t_opt, instr_lst))
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [?()], RETURN ?()})

  ;; ../specification/wasm-1.0/6-typing.spectec:181.1-184.59
  rule if{C : context, t_opt : valtype?, instr_1_lst : instr*, instr_2_lst : instr*}:
    `%|-%:%`(C, `IF%%ELSE%`_instr(t_opt, instr_1_lst, instr_2_lst), mk_functype_functype([I32_valtype], lift(t_opt)))
    -- Instrs_ok: `%|-%:%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t_opt], RETURN ?()} +++ C, instr_1_lst, mk_functype_functype([], lift(t_opt)))
    -- Instrs_ok: `%|-%:%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t_opt], RETURN ?()} +++ C, instr_2_lst, mk_functype_functype([], lift(t_opt)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`IF%%ELSE%`_instr(t_opt, instr_1_lst, instr_2_lst))
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t_opt], RETURN ?()})

  ;; ../specification/wasm-1.0/6-typing.spectec:189.1-191.25
  rule br{C : context, l : labelidx, t_1_lst : valtype*, t_opt : valtype?, t_2_lst : valtype*}:
    `%|-%:%`(C, BR_instr(l), mk_functype_functype(t_1_lst ++ lift(t_opt), t_2_lst))
    -- if ($proj_uN_0(l).0 < |C.LABELS_context|)
    -- if (C.LABELS_context[$proj_uN_0(l).0] = t_opt)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_instr(l))

  ;; ../specification/wasm-1.0/6-typing.spectec:193.1-195.25
  rule br_if{C : context, l : labelidx, t_opt : valtype?}:
    `%|-%:%`(C, BR_IF_instr(l), mk_functype_functype(lift(t_opt) ++ [I32_valtype], lift(t_opt)))
    -- if ($proj_uN_0(l).0 < |C.LABELS_context|)
    -- if (C.LABELS_context[$proj_uN_0(l).0] = t_opt)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_IF_instr(l))

  ;; ../specification/wasm-1.0/6-typing.spectec:197.1-200.28
  rule br_table{C : context, l_lst : labelidx*, l' : labelidx, t_1_lst : valtype*, t_opt : valtype?, t_2_lst : valtype*}:
    `%|-%:%`(C, BR_TABLE_instr(l_lst, l'), mk_functype_functype(t_1_lst ++ lift(t_opt) ++ [I32_valtype], t_2_lst))
    -- if ($proj_uN_0(l').0 < |C.LABELS_context|)
    -- if (t_opt = C.LABELS_context[$proj_uN_0(l').0])
    -- (if ($proj_uN_0(l).0 < |C.LABELS_context|))*{l <- l_lst}
    -- (if (t_opt = C.LABELS_context[$proj_uN_0(l).0]))*{l <- l_lst}
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_TABLE_instr(l_lst, l'))

  ;; ../specification/wasm-1.0/6-typing.spectec:205.1-207.34
  rule call{C : context, x : idx, t_1_lst : valtype*, t_2_opt : valtype?}:
    `%|-%:%`(C, CALL_instr(x), mk_functype_functype(t_1_lst, lift(t_2_opt)))
    -- if ($proj_uN_0(x).0 < |C.FUNCS_context|)
    -- if (C.FUNCS_context[$proj_uN_0(x).0] = mk_functype_functype(t_1_lst, lift(t_2_opt)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CALL_instr(x))

  ;; ../specification/wasm-1.0/6-typing.spectec:209.1-211.34
  rule call_indirect{C : context, x : idx, t_1_lst : valtype*, t_2_opt : valtype?}:
    `%|-%:%`(C, CALL_INDIRECT_instr(x), mk_functype_functype(t_1_lst ++ [I32_valtype], lift(t_2_opt)))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- if (C.TYPES_context[$proj_uN_0(x).0] = mk_functype_functype(t_1_lst, lift(t_2_opt)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CALL_INDIRECT_instr(x))

  ;; ../specification/wasm-1.0/6-typing.spectec:213.1-215.24
  rule return{C : context, t_1_lst : valtype*, t_opt : valtype?, t_2_lst : valtype*}:
    `%|-%:%`(C, RETURN_instr, mk_functype_functype(t_1_lst ++ lift(t_opt), t_2_lst))
    -- if (C.RETURN_context = ?(t_opt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(RETURN_instr)

  ;; ../specification/wasm-1.0/6-typing.spectec:220.1-221.30
  rule const{C : context, t : valtype, c_t : val_}:
    `%|-%:%`(C, CONST_instr(t, c_t), mk_functype_functype([], [t]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CONST_instr(t, c_t))

  ;; ../specification/wasm-1.0/6-typing.spectec:223.1-224.30
  rule unop{C : context, t : valtype, unop_t : unop_}:
    `%|-%:%`(C, UNOP_instr(t, unop_t), mk_functype_functype([t], [t]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(UNOP_instr(t, unop_t))

  ;; ../specification/wasm-1.0/6-typing.spectec:226.1-227.34
  rule binop{C : context, t : valtype, binop_t : binop_}:
    `%|-%:%`(C, BINOP_instr(t, binop_t), mk_functype_functype([t t], [t]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BINOP_instr(t, binop_t))

  ;; ../specification/wasm-1.0/6-typing.spectec:229.1-230.36
  rule testop{C : context, t : valtype, testop_t : testop_}:
    `%|-%:%`(C, TESTOP_instr(t, testop_t), mk_functype_functype([t], [I32_valtype]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(TESTOP_instr(t, testop_t))

  ;; ../specification/wasm-1.0/6-typing.spectec:232.1-233.36
  rule relop{C : context, t : valtype, relop_t : relop_}:
    `%|-%:%`(C, RELOP_instr(t, relop_t), mk_functype_functype([t t], [I32_valtype]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(RELOP_instr(t, relop_t))

  ;; ../specification/wasm-1.0/6-typing.spectec:237.1-239.34
  rule cvtop_reinterpret{C : context, nt_1 : valtype, nt_2 : valtype}:
    `%|-%:%`(C, CVTOP_instr(nt_1, nt_2, REINTERPRET_cvtop), mk_functype_functype([nt_2], [nt_1]))
    -- if ($size(nt_1) = $size(nt_2))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CVTOP_instr(nt_1, nt_2, REINTERPRET_cvtop))

  ;; ../specification/wasm-1.0/6-typing.spectec:241.1-242.44
  rule cvtop_convert{C : context, nt_1 : valtype, nt_2 : valtype, v_cvtop : cvtop}:
    `%|-%:%`(C, CVTOP_instr(nt_1, nt_2, v_cvtop), mk_functype_functype([nt_2], [nt_1]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CVTOP_instr(nt_1, nt_2, v_cvtop))

  ;; ../specification/wasm-1.0/6-typing.spectec:247.1-249.24
  rule local_get{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, LOCAL_GET_instr(x), mk_functype_functype([], [t]))
    -- if ($proj_uN_0(x).0 < |C.LOCALS_context|)
    -- if (C.LOCALS_context[$proj_uN_0(x).0] = t)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOCAL_GET_instr(x))

  ;; ../specification/wasm-1.0/6-typing.spectec:251.1-253.24
  rule local_set{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, LOCAL_SET_instr(x), mk_functype_functype([t], []))
    -- if ($proj_uN_0(x).0 < |C.LOCALS_context|)
    -- if (C.LOCALS_context[$proj_uN_0(x).0] = t)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOCAL_SET_instr(x))

  ;; ../specification/wasm-1.0/6-typing.spectec:255.1-257.24
  rule local_tee{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, LOCAL_TEE_instr(x), mk_functype_functype([t], [t]))
    -- if ($proj_uN_0(x).0 < |C.LOCALS_context|)
    -- if (C.LOCALS_context[$proj_uN_0(x).0] = t)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOCAL_TEE_instr(x))

  ;; ../specification/wasm-1.0/6-typing.spectec:262.1-264.29
  rule global_get{C : context, x : idx, t : valtype, v_mut : mut}:
    `%|-%:%`(C, GLOBAL_GET_instr(x), mk_functype_functype([], [t]))
    -- if ($proj_uN_0(x).0 < |C.GLOBALS_context|)
    -- if (C.GLOBALS_context[$proj_uN_0(x).0] = mk_globaltype_globaltype(v_mut, t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(GLOBAL_GET_instr(x))

  ;; ../specification/wasm-1.0/6-typing.spectec:266.1-268.29
  rule global_set{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, GLOBAL_SET_instr(x), mk_functype_functype([t], []))
    -- if ($proj_uN_0(x).0 < |C.GLOBALS_context|)
    -- if (C.GLOBALS_context[$proj_uN_0(x).0] = mk_globaltype_globaltype(?(MUT_r_MUT), t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(GLOBAL_SET_instr(x))

  ;; ../specification/wasm-1.0/6-typing.spectec:273.1-275.23
  rule memory_size{C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY_SIZE_instr, mk_functype_functype([], [I32_valtype]))
    -- if (0 < |C.MEMS_context|)
    -- if (C.MEMS_context[0] = mt)
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(MEMORY_SIZE_instr)

  ;; ../specification/wasm-1.0/6-typing.spectec:277.1-279.23
  rule memory_grow{C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY_GROW_instr, mk_functype_functype([I32_valtype], [I32_valtype]))
    -- if (0 < |C.MEMS_context|)
    -- if (C.MEMS_context[0] = mt)
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(MEMORY_GROW_instr)

  ;; ../specification/wasm-1.0/6-typing.spectec:290.1-293.42
  rule load_val{C : context, t : valtype, v_memarg : memarg, mt : memtype}:
    `%|-%:%`(C, LOAD_instr(t, ?(), v_memarg), mk_functype_functype([I32_valtype], [t]))
    -- if (0 < |C.MEMS_context|)
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ $proj_uN_0(v_memarg.ALIGN_memarg).0) : nat <:> rat) <= (($size(t) : nat <:> rat) / (8 : nat <:> rat)))
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(LOAD_instr(t, ?(), v_memarg))

  ;; ../specification/wasm-1.0/6-typing.spectec:295.1-298.35
  rule load_pack{C : context, v_Inn : Inn, v_M : M, v_sx : sx, v_memarg : memarg, mt : memtype}:
    `%|-%:%`(C, LOAD_instr($valtype_Inn(v_Inn), ?(mk_loadop__0_loadop_(v_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(v_M), v_sx))), v_memarg), mk_functype_functype([I32_valtype], [$valtype_Inn(v_Inn)]))
    -- if (0 < |C.MEMS_context|)
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ $proj_uN_0(v_memarg.ALIGN_memarg).0) : nat <:> rat) <= ((v_M : nat <:> rat) / (8 : nat <:> rat)))
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(LOAD_instr($valtype_Inn(v_Inn), ?(mk_loadop__0_loadop_(v_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(v_M), v_sx))), v_memarg))

  ;; ../specification/wasm-1.0/6-typing.spectec:309.1-312.42
  rule store_val{C : context, t : valtype, v_memarg : memarg, mt : memtype}:
    `%|-%:%`(C, STORE_instr(t, ?(), v_memarg), mk_functype_functype([I32_valtype t], []))
    -- if (0 < |C.MEMS_context|)
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ $proj_uN_0(v_memarg.ALIGN_memarg).0) : nat <:> rat) <= (($size(t) : nat <:> rat) / (8 : nat <:> rat)))
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(STORE_instr(t, ?(), v_memarg))

  ;; ../specification/wasm-1.0/6-typing.spectec:314.1-317.35
  rule store_pack{C : context, v_Inn : Inn, v_M : M, v_memarg : memarg, mt : memtype}:
    `%|-%:%`(C, STORE_instr($valtype_Inn(v_Inn), ?(mk_sz_sz(v_M)), v_memarg), mk_functype_functype([I32_valtype $valtype_Inn(v_Inn)], []))
    -- if (0 < |C.MEMS_context|)
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ $proj_uN_0(v_memarg.ALIGN_memarg).0) : nat <:> rat) <= ((v_M : nat <:> rat) / (8 : nat <:> rat)))
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(STORE_instr($valtype_Inn(v_Inn), ?(mk_sz_sz(v_M)), v_memarg))

;; ../specification/wasm-1.0/6-typing.spectec:126.1-126.65
relation Instrs_ok: `%|-%:%`(context, instr*, functype)
  ;; ../specification/wasm-1.0/6-typing.spectec:139.1-140.24
  rule empty{C : context}:
    `%|-%:%`(C, [], mk_functype_functype([], []))
    -- wf_context: `%`(C)

  ;; ../specification/wasm-1.0/6-typing.spectec:142.1-144.41
  rule instr{C : context, v_instr : instr, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:%`(C, [v_instr], mk_functype_functype(t_1_lst, t_2_lst))
    -- Instr_ok: `%|-%:%`(C, v_instr, mk_functype_functype(t_1_lst, t_2_lst))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(v_instr)

  ;; ../specification/wasm-1.0/6-typing.spectec:146.1-149.45
  rule seq{C : context, instr_1_lst : instr*, instr_2_lst : instr*, t_1_lst : valtype*, t_3_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:%`(C, instr_1_lst ++ instr_2_lst, mk_functype_functype(t_1_lst, t_3_lst))
    -- Instrs_ok: `%|-%:%`(C, instr_1_lst, mk_functype_functype(t_1_lst, t_2_lst))
    -- Instrs_ok: `%|-%:%`(C, instr_2_lst, mk_functype_functype(t_2_lst, t_3_lst))
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(instr_1))*{instr_1 <- instr_1_lst}
    -- (wf_instr: `%`(instr_2))*{instr_2 <- instr_2_lst}

  ;; ../specification/wasm-1.0/6-typing.spectec:151.1-153.43
  rule frame{C : context, instr_lst : instr*, t_lst : valtype*, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:%`(C, instr_lst, mk_functype_functype(t_lst ++ t_1_lst, t_lst ++ t_2_lst))
    -- Instrs_ok: `%|-%:%`(C, instr_lst, mk_functype_functype(t_1_lst, t_2_lst))
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}
}

;; ../specification/wasm-1.0/6-typing.spectec:127.1-127.69
relation Expr_ok: `%|-%:%`(context, expr, resulttype)
  ;; ../specification/wasm-1.0/6-typing.spectec:132.1-134.40
  rule mk_Expr_ok{C : context, instr_lst : instr*, t_opt : valtype?}:
    `%|-%:%`(C, instr_lst, t_opt)
    -- Instrs_ok: `%|-%:%`(C, instr_lst, mk_functype_functype([], lift(t_opt)))
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

;; ../specification/wasm-1.0/6-typing.spectec:324.1-324.79
relation Instr_const: `%|-%CONST`(context, instr)
  ;; ../specification/wasm-1.0/6-typing.spectec:328.1-329.25
  rule const{C : context, t : valtype, c : val_}:
    `%|-%CONST`(C, CONST_instr(t, c))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CONST_instr(t, c))

  ;; ../specification/wasm-1.0/6-typing.spectec:331.1-333.25
  rule global_get{C : context, x : idx, t : valtype}:
    `%|-%CONST`(C, GLOBAL_GET_instr(x))
    -- if ($proj_uN_0(x).0 < |C.GLOBALS_context|)
    -- if (C.GLOBALS_context[$proj_uN_0(x).0] = mk_globaltype_globaltype(?(), t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(GLOBAL_GET_instr(x))

;; ../specification/wasm-1.0/6-typing.spectec:325.1-325.78
relation Expr_const: `%|-%CONST`(context, expr)
  ;; ../specification/wasm-1.0/6-typing.spectec:336.1-337.38
  rule mk_Expr_const{C : context, instr_lst : instr*}:
    `%|-%CONST`(C, instr_lst)
    -- (Instr_const: `%|-%CONST`(C, v_instr))*{v_instr <- instr_lst}
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

;; ../specification/wasm-1.0/6-typing.spectec:326.1-326.79
relation Expr_ok_const: `%|-%:%CONST`(context, expr, valtype?)
  ;; ../specification/wasm-1.0/6-typing.spectec:340.1-343.33
  rule mk_Expr_ok_const{C : context, v_expr : expr, t_opt : valtype?}:
    `%|-%:%CONST`(C, v_expr, t_opt)
    -- Expr_ok: `%|-%:%`(C, v_expr, t_opt)
    -- Expr_const: `%|-%CONST`(C, v_expr)
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}

;; ../specification/wasm-1.0/6-typing.spectec:350.1-350.73
relation Type_ok: `|-%:%`(type, functype)
  ;; ../specification/wasm-1.0/6-typing.spectec:362.1-364.29
  rule mk_Type_ok{ft : functype}:
    `|-%:%`(TYPE_type(ft), ft)
    -- Functype_ok: `|-%:OK`(ft)

;; ../specification/wasm-1.0/6-typing.spectec:351.1-351.73
relation Func_ok: `%|-%:%`(context, func, functype)
  ;; ../specification/wasm-1.0/6-typing.spectec:366.1-369.81
  rule mk_Func_ok{C : context, x : idx, t_lst : valtype*, v_expr : expr, t_1_lst : valtype*, t_2_opt : valtype?}:
    `%|-%:%`(C, FUNC_func(x, LOCAL_local(t)*{t <- t_lst}, v_expr), mk_functype_functype(t_1_lst, lift(t_2_opt)))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- if (C.TYPES_context[$proj_uN_0(x).0] = mk_functype_functype(t_1_lst, lift(t_2_opt)))
    -- Expr_ok: `%|-%:%`(C +++ {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS t_1_lst ++ t_lst, LABELS [t_2_opt], RETURN ?(t_2_opt)}, v_expr, t_2_opt)
    -- wf_context: `%`(C)
    -- wf_func: `%`(FUNC_func(x, LOCAL_local(t)*{t <- t_lst}, v_expr))
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS t_1_lst ++ t_lst, LABELS [t_2_opt], RETURN ?(t_2_opt)})

;; ../specification/wasm-1.0/6-typing.spectec:352.1-352.75
relation Global_ok: `%|-%:%`(context, global, globaltype)
  ;; ../specification/wasm-1.0/6-typing.spectec:371.1-375.40
  rule mk_Global_ok{C : context, gt : globaltype, v_expr : expr, v_mut : mut, t : valtype}:
    `%|-%:%`(C, GLOBAL_global(gt, v_expr), gt)
    -- Globaltype_ok: `|-%:OK`(gt)
    -- if (gt = mk_globaltype_globaltype(v_mut, t))
    -- Expr_ok_const: `%|-%:%CONST`(C, v_expr, ?(t))
    -- wf_context: `%`(C)
    -- wf_global: `%`(GLOBAL_global(gt, v_expr))

;; ../specification/wasm-1.0/6-typing.spectec:353.1-353.74
relation Table_ok: `%|-%:%`(context, table, tabletype)
  ;; ../specification/wasm-1.0/6-typing.spectec:377.1-379.30
  rule mk_Table_ok{C : context, tt : tabletype}:
    `%|-%:%`(C, TABLE_table(tt), tt)
    -- Tabletype_ok: `|-%:OK`(tt)
    -- wf_context: `%`(C)
    -- wf_table: `%`(TABLE_table(tt))

;; ../specification/wasm-1.0/6-typing.spectec:354.1-354.72
relation Mem_ok: `%|-%:%`(context, mem, memtype)
  ;; ../specification/wasm-1.0/6-typing.spectec:381.1-383.28
  rule mk_Mem_ok{C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY_mem(mt), mt)
    -- Memtype_ok: `|-%:OK`(mt)
    -- wf_context: `%`(C)
    -- wf_mem: `%`(MEMORY_mem(mt))

;; ../specification/wasm-1.0/6-typing.spectec:355.1-355.73
relation Elem_ok: `%|-%:OK`(context, elem)
  ;; ../specification/wasm-1.0/6-typing.spectec:386.1-390.27
  rule mk_Elem_ok{C : context, v_expr : expr, x_lst : idx*, lim : limits, ft_lst : functype*}:
    `%|-%:OK`(C, ELEM_elem(v_expr, x_lst))
    -- if (0 < |C.TABLES_context|)
    -- if (C.TABLES_context[0] = lim)
    -- Expr_ok_const: `%|-%:%CONST`(C, v_expr, ?(I32_valtype))
    -- if (|ft_lst| = |x_lst|)
    -- (if ($proj_uN_0(x).0 < |C.FUNCS_context|))*{x <- x_lst}
    -- (if (C.FUNCS_context[$proj_uN_0(x).0] = ft))*{ft <- ft_lst, x <- x_lst}
    -- wf_context: `%`(C)
    -- wf_limits: `%`(lim)
    -- wf_elem: `%`(ELEM_elem(v_expr, x_lst))

;; ../specification/wasm-1.0/6-typing.spectec:356.1-356.73
relation Data_ok: `%|-%:OK`(context, data)
  ;; ../specification/wasm-1.0/6-typing.spectec:393.1-396.42
  rule mk_Data_ok{C : context, v_expr : expr, b_lst : byte*, lim : limits}:
    `%|-%:OK`(C, DATA_data(v_expr, b_lst))
    -- if (0 < |C.MEMS_context|)
    -- if (C.MEMS_context[0] = lim)
    -- Expr_ok_const: `%|-%:%CONST`(C, v_expr, ?(I32_valtype))
    -- wf_context: `%`(C)
    -- wf_limits: `%`(lim)
    -- wf_data: `%`(DATA_data(v_expr, b_lst))

;; ../specification/wasm-1.0/6-typing.spectec:357.1-357.74
relation Start_ok: `%|-%:OK`(context, start)
  ;; ../specification/wasm-1.0/6-typing.spectec:398.1-400.32
  rule mk_Start_ok{C : context, x : idx}:
    `%|-%:OK`(C, START_start(x))
    -- if ($proj_uN_0(x).0 < |C.FUNCS_context|)
    -- if (C.FUNCS_context[$proj_uN_0(x).0] = mk_functype_functype([], []))
    -- wf_context: `%`(C)
    -- wf_start: `%`(START_start(x))

;; ../specification/wasm-1.0/6-typing.spectec:405.1-405.80
relation Import_ok: `%|-%:%`(context, import, externtype)
  ;; ../specification/wasm-1.0/6-typing.spectec:409.1-411.31
  rule mk_Import_ok{C : context, name_1 : name, name_2 : name, xt : externtype}:
    `%|-%:%`(C, IMPORT_import(name_1, name_2, xt), xt)
    -- Externtype_ok: `|-%:OK`(xt)
    -- wf_context: `%`(C)
    -- wf_import: `%`(IMPORT_import(name_1, name_2, xt))

;; ../specification/wasm-1.0/6-typing.spectec:407.1-407.83
relation Externidx_ok: `%|-%:%`(context, externidx, externtype)
  ;; ../specification/wasm-1.0/6-typing.spectec:418.1-420.24
  rule func{C : context, x : idx, ft : functype}:
    `%|-%:%`(C, FUNC_externidx(x), FUNC_externtype(ft))
    -- if ($proj_uN_0(x).0 < |C.FUNCS_context|)
    -- if (C.FUNCS_context[$proj_uN_0(x).0] = ft)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(FUNC_externidx(x))
    -- wf_externtype: `%`(FUNC_externtype(ft))

  ;; ../specification/wasm-1.0/6-typing.spectec:422.1-424.26
  rule global{C : context, x : idx, gt : globaltype}:
    `%|-%:%`(C, GLOBAL_externidx(x), GLOBAL_externtype(gt))
    -- if ($proj_uN_0(x).0 < |C.GLOBALS_context|)
    -- if (C.GLOBALS_context[$proj_uN_0(x).0] = gt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(GLOBAL_externidx(x))
    -- wf_externtype: `%`(GLOBAL_externtype(gt))

  ;; ../specification/wasm-1.0/6-typing.spectec:426.1-428.25
  rule table{C : context, x : idx, tt : tabletype}:
    `%|-%:%`(C, TABLE_externidx(x), TABLE_externtype(tt))
    -- if ($proj_uN_0(x).0 < |C.TABLES_context|)
    -- if (C.TABLES_context[$proj_uN_0(x).0] = tt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(TABLE_externidx(x))
    -- wf_externtype: `%`(TABLE_externtype(tt))

  ;; ../specification/wasm-1.0/6-typing.spectec:430.1-432.23
  rule mem{C : context, x : idx, mt : memtype}:
    `%|-%:%`(C, MEM_externidx(x), MEM_externtype(mt))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = mt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(MEM_externidx(x))
    -- wf_externtype: `%`(MEM_externtype(mt))

;; ../specification/wasm-1.0/6-typing.spectec:406.1-406.80
relation Export_ok: `%|-%:%`(context, export, externtype)
  ;; ../specification/wasm-1.0/6-typing.spectec:413.1-415.39
  rule mk_Export_ok{C : context, v_name : name, v_externidx : externidx, xt : externtype}:
    `%|-%:%`(C, EXPORT_export(v_name, v_externidx), xt)
    -- Externidx_ok: `%|-%:%`(C, v_externidx, xt)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(xt)
    -- wf_export: `%`(EXPORT_export(v_name, v_externidx))

;; ../specification/wasm-1.0/6-typing.spectec:437.1-437.62
relation Module_ok: `|-%:OK`(module)
  ;; ../specification/wasm-1.0/6-typing.spectec:439.1-465.29
  rule mk_Module_ok{type_lst : type*, import_lst : import*, func_lst : func*, global_lst : global*, table_lst : table*, mem_lst : mem*, elem_lst : elem*, data_lst : data*, start_opt : start?, export_lst : export*, ft'_lst : functype*, ixt_lst : externtype*, C' : context, gt_lst : globaltype*, C : context, ft_lst : functype*, tt_lst : tabletype*, mt_lst : memtype*, xt_lst : externtype*, ift_lst : functype*, igt_lst : globaltype*, itt_lst : tabletype*, imt_lst : memtype*, var_3 : memtype*, var_2 : tabletype*, var_1 : globaltype*, var_0 : functype*}:
    `|-%:OK`(MODULE_module(type_lst, import_lst, func_lst, global_lst, table_lst, mem_lst, elem_lst, data_lst, start_opt, export_lst))
    -- fun_memsxt: `%%`(ixt_lst, var_3)
    -- fun_tablesxt: `%%`(ixt_lst, var_2)
    -- fun_globalsxt: `%%`(ixt_lst, var_1)
    -- fun_funcsxt: `%%`(ixt_lst, var_0)
    -- if (|ft'_lst| = |type_lst|)
    -- (Type_ok: `|-%:%`(v_type, ft'))*{ft' <- ft'_lst, v_type <- type_lst}
    -- if (|import_lst| = |ixt_lst|)
    -- (Import_ok: `%|-%:%`({TYPES ft'_lst, FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [], RETURN ?()}, v_import, ixt))*{v_import <- import_lst, ixt <- ixt_lst}
    -- if (|global_lst| = |gt_lst|)
    -- (Global_ok: `%|-%:%`(C', v_global, gt))*{v_global <- global_lst, gt <- gt_lst}
    -- if (|ft_lst| = |func_lst|)
    -- (Func_ok: `%|-%:%`(C, v_func, ft))*{ft <- ft_lst, v_func <- func_lst}
    -- if (|table_lst| = |tt_lst|)
    -- (Table_ok: `%|-%:%`(C, v_table, tt))*{v_table <- table_lst, tt <- tt_lst}
    -- if (|mem_lst| = |mt_lst|)
    -- (Mem_ok: `%|-%:%`(C, v_mem, mt))*{v_mem <- mem_lst, mt <- mt_lst}
    -- (Elem_ok: `%|-%:OK`(C, v_elem))*{v_elem <- elem_lst}
    -- (Data_ok: `%|-%:OK`(C, v_data))*{v_data <- data_lst}
    -- (Start_ok: `%|-%:OK`(C, v_start))?{v_start <- start_opt}
    -- if (|export_lst| = |xt_lst|)
    -- (Export_ok: `%|-%:%`(C, v_export, xt))*{v_export <- export_lst, xt <- xt_lst}
    -- if (|tt_lst| <= 1)
    -- if (|mt_lst| <= 1)
    -- if (C = {TYPES ft'_lst, FUNCS ift_lst ++ ft_lst, GLOBALS igt_lst ++ gt_lst, TABLES itt_lst ++ tt_lst, MEMS imt_lst ++ mt_lst, LOCALS [], LABELS [], RETURN ?()})
    -- if (C' = {TYPES ft'_lst, FUNCS ift_lst ++ ft_lst, GLOBALS igt_lst, TABLES [], MEMS [], LOCALS [], LABELS [], RETURN ?()})
    -- if (ift_lst = var_0)
    -- if (igt_lst = var_1)
    -- if (itt_lst = var_2)
    -- if (imt_lst = var_3)
    -- (wf_externtype: `%`(ixt))*{ixt <- ixt_lst}
    -- wf_context: `%`(C')
    -- wf_context: `%`(C)
    -- (wf_externtype: `%`(xt))*{xt <- xt_lst}
    -- (wf_limits: `%`(iter))*{iter <- var_2}
    -- (wf_limits: `%`(iter))*{iter <- var_3}
    -- wf_module: `%`(MODULE_module(type_lst, import_lst, func_lst, global_lst, table_lst, mem_lst, elem_lst, data_lst, start_opt, export_lst))
    -- wf_context: `%`({TYPES ft'_lst, FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [], RETURN ?()})
    -- wf_context: `%`({TYPES ft'_lst, FUNCS ift_lst ++ ft_lst, GLOBALS igt_lst ++ gt_lst, TABLES itt_lst ++ tt_lst, MEMS imt_lst ++ mt_lst, LOCALS [], LABELS [], RETURN ?()})
    -- wf_context: `%`({TYPES ft'_lst, FUNCS ift_lst ++ ft_lst, GLOBALS igt_lst, TABLES [], MEMS [], LOCALS [], LABELS [], RETURN ?()})

;; ../specification/wasm-1.0/8-reduction.spectec:6.1-6.77
relation Step_pure: `%~>%`(admininstr*, admininstr*)
  ;; ../specification/wasm-1.0/8-reduction.spectec:42.1-43.24
  rule unreachable:
    `%~>%`([UNREACHABLE_admininstr], [TRAP_admininstr])
    -- wf_admininstr: `%`(UNREACHABLE_admininstr)
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; ../specification/wasm-1.0/8-reduction.spectec:45.1-46.15
  rule nop:
    `%~>%`([NOP_admininstr], [])
    -- wf_admininstr: `%`(NOP_admininstr)

  ;; ../specification/wasm-1.0/8-reduction.spectec:48.1-49.20
  rule drop{v_val : val}:
    `%~>%`([$admininstr_val(v_val) DROP_admininstr], [])
    -- wf_val: `%`(v_val)
    -- wf_admininstr: `%`(DROP_admininstr)

  ;; ../specification/wasm-1.0/8-reduction.spectec:52.1-54.16
  rule select_true{val_1 : val, val_2 : val, c : val_}:
    `%~>%`([$admininstr_val(val_1) $admininstr_val(val_2) CONST_admininstr(I32_valtype, c) SELECT_admininstr], [$admininstr_val(val_1)])
    -- if ($proj_val__0(c) =/= ?())
    -- if ($proj_uN_0(!($proj_val__0(c))).0 =/= 0)
    -- wf_val: `%`(val_1)
    -- wf_val: `%`(val_2)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(SELECT_admininstr)

  ;; ../specification/wasm-1.0/8-reduction.spectec:56.1-58.14
  rule select_false{val_1 : val, val_2 : val, c : val_}:
    `%~>%`([$admininstr_val(val_1) $admininstr_val(val_2) CONST_admininstr(I32_valtype, c) SELECT_admininstr], [$admininstr_val(val_2)])
    -- if ($proj_val__0(c) =/= ?())
    -- if ($proj_uN_0(!($proj_val__0(c))).0 = 0)
    -- wf_val: `%`(val_1)
    -- wf_val: `%`(val_2)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(SELECT_admininstr)

  ;; ../specification/wasm-1.0/8-reduction.spectec:70.1-72.16
  rule if_true{c : val_, t_opt : valtype?, instr_1_lst : instr*, instr_2_lst : instr*}:
    `%~>%`([CONST_admininstr(I32_valtype, c) `IF%%ELSE%`_admininstr(t_opt, instr_1_lst, instr_2_lst)], [BLOCK_admininstr(t_opt, instr_1_lst)])
    -- if ($proj_val__0(c) =/= ?())
    -- if ($proj_uN_0(!($proj_val__0(c))).0 =/= 0)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(`IF%%ELSE%`_admininstr(t_opt, instr_1_lst, instr_2_lst))
    -- wf_admininstr: `%`(BLOCK_admininstr(t_opt, instr_1_lst))

  ;; ../specification/wasm-1.0/8-reduction.spectec:74.1-76.14
  rule if_false{c : val_, t_opt : valtype?, instr_1_lst : instr*, instr_2_lst : instr*}:
    `%~>%`([CONST_admininstr(I32_valtype, c) `IF%%ELSE%`_admininstr(t_opt, instr_1_lst, instr_2_lst)], [BLOCK_admininstr(t_opt, instr_2_lst)])
    -- if ($proj_val__0(c) =/= ?())
    -- if ($proj_uN_0(!($proj_val__0(c))).0 = 0)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(`IF%%ELSE%`_admininstr(t_opt, instr_1_lst, instr_2_lst))
    -- wf_admininstr: `%`(BLOCK_admininstr(t_opt, instr_2_lst))

  ;; ../specification/wasm-1.0/8-reduction.spectec:79.1-80.38
  rule label_vals{v_n : n, instr_lst : instr*, val_lst : val*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(v_n, instr_lst, $admininstr_val(v_val)*{v_val <- val_lst})], $admininstr_val(v_val)*{v_val <- val_lst})
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(v_n, instr_lst, $admininstr_val(v_val)*{v_val <- val_lst}))

  ;; ../specification/wasm-1.0/8-reduction.spectec:86.1-87.69
  rule br_zero{v_n : n, instr'_lst : instr*, val'_lst : val*, val_lst : val*, instr_lst : instr*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(v_n, instr'_lst, $admininstr_val(val')*{val' <- val'_lst} ++ $admininstr_val(v_val)^v_n{v_val <- val_lst} ++ [BR_admininstr(mk_uN_labelidx(0))] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst})], $admininstr_val(v_val)^v_n{v_val <- val_lst} ++ $admininstr_instr(instr')*{instr' <- instr'_lst})
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(v_n, instr'_lst, $admininstr_val(val')*{val' <- val'_lst} ++ $admininstr_val(v_val)^v_n{v_val <- val_lst} ++ [BR_admininstr(mk_uN_labelidx(0))] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst}))
    -- if (v_n = |val_lst|)

  ;; ../specification/wasm-1.0/8-reduction.spectec:89.1-90.65
  rule br_succ{v_n : n, instr'_lst : instr*, val_lst : val*, l : labelidx, instr_lst : instr*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(v_n, instr'_lst, $admininstr_val(v_val)*{v_val <- val_lst} ++ [BR_admininstr(mk_uN_labelidx(($proj_uN_0(l).0 + 1)))] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst})], $admininstr_val(v_val)*{v_val <- val_lst} ++ [BR_admininstr(l)])
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(v_n, instr'_lst, $admininstr_val(v_val)*{v_val <- val_lst} ++ [BR_admininstr(mk_uN_labelidx(($proj_uN_0(l).0 + 1)))] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst}))
    -- wf_admininstr: `%`(BR_admininstr(l))

  ;; ../specification/wasm-1.0/8-reduction.spectec:93.1-95.16
  rule br_if_true{c : val_, l : labelidx}:
    `%~>%`([CONST_admininstr(I32_valtype, c) BR_IF_admininstr(l)], [BR_admininstr(l)])
    -- if ($proj_val__0(c) =/= ?())
    -- if ($proj_uN_0(!($proj_val__0(c))).0 =/= 0)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(BR_IF_admininstr(l))
    -- wf_admininstr: `%`(BR_admininstr(l))

  ;; ../specification/wasm-1.0/8-reduction.spectec:97.1-99.14
  rule br_if_false{c : val_, l : labelidx}:
    `%~>%`([CONST_admininstr(I32_valtype, c) BR_IF_admininstr(l)], [])
    -- if ($proj_val__0(c) =/= ?())
    -- if ($proj_uN_0(!($proj_val__0(c))).0 = 0)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(BR_IF_admininstr(l))

  ;; ../specification/wasm-1.0/8-reduction.spectec:102.1-104.17
  rule br_table_lt{i : val_, l_lst : labelidx*, l' : labelidx}:
    `%~>%`([CONST_admininstr(I32_valtype, i) BR_TABLE_admininstr(l_lst, l')], [BR_admininstr(l_lst[$proj_uN_0(!($proj_val__0(i))).0])])
    -- if ($proj_uN_0(!($proj_val__0(i))).0 < |l_lst|)
    -- if ($proj_val__0(i) =/= ?())
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, i))
    -- wf_admininstr: `%`(BR_TABLE_admininstr(l_lst, l'))
    -- wf_admininstr: `%`(BR_admininstr(l_lst[$proj_uN_0(!($proj_val__0(i))).0]))

  ;; ../specification/wasm-1.0/8-reduction.spectec:106.1-108.18
  rule br_table_ge{i : val_, l_lst : labelidx*, l' : labelidx}:
    `%~>%`([CONST_admininstr(I32_valtype, i) BR_TABLE_admininstr(l_lst, l')], [BR_admininstr(l')])
    -- if ($proj_val__0(i) =/= ?())
    -- if ($proj_uN_0(!($proj_val__0(i))).0 >= |l_lst|)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, i))
    -- wf_admininstr: `%`(BR_TABLE_admininstr(l_lst, l'))
    -- wf_admininstr: `%`(BR_admininstr(l'))

  ;; ../specification/wasm-1.0/8-reduction.spectec:132.1-133.35
  rule frame_vals{v_n : n, f : frame, val_lst : val*}:
    `%~>%`([`FRAME_%{%}%`_admininstr(v_n, f, $admininstr_val(v_val)^v_n{v_val <- val_lst})], $admininstr_val(v_val)^v_n{v_val <- val_lst})
    -- wf_admininstr: `%`(`FRAME_%{%}%`_admininstr(v_n, f, $admininstr_val(v_val)^v_n{v_val <- val_lst}))
    -- if (v_n = |val_lst|)

  ;; ../specification/wasm-1.0/8-reduction.spectec:135.1-136.55
  rule return_frame{v_n : n, f : frame, val'_lst : val*, val_lst : val*, instr_lst : instr*}:
    `%~>%`([`FRAME_%{%}%`_admininstr(v_n, f, $admininstr_val(val')*{val' <- val'_lst} ++ $admininstr_val(v_val)^v_n{v_val <- val_lst} ++ [RETURN_admininstr] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst})], $admininstr_val(v_val)^v_n{v_val <- val_lst})
    -- wf_admininstr: `%`(`FRAME_%{%}%`_admininstr(v_n, f, $admininstr_val(val')*{val' <- val'_lst} ++ $admininstr_val(v_val)^v_n{v_val <- val_lst} ++ [RETURN_admininstr] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst}))
    -- if (v_n = |val_lst|)

  ;; ../specification/wasm-1.0/8-reduction.spectec:138.1-139.60
  rule return_label{v_n : n, instr'_lst : instr*, val_lst : val*, instr_lst : instr*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(v_n, instr'_lst, $admininstr_val(v_val)*{v_val <- val_lst} ++ [RETURN_admininstr] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst})], $admininstr_val(v_val)*{v_val <- val_lst} ++ [RETURN_admininstr])
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(v_n, instr'_lst, $admininstr_val(v_val)*{v_val <- val_lst} ++ [RETURN_admininstr] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst}))
    -- wf_admininstr: `%`(RETURN_admininstr)

  ;; ../specification/wasm-1.0/8-reduction.spectec:144.1-146.39
  rule trap_vals{val_lst : val*, instr_lst : instr*}:
    `%~>%`($admininstr_val(v_val)*{v_val <- val_lst} ++ [TRAP_admininstr] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst}, [TRAP_admininstr])
    -- if ((val_lst =/= []) \/ (instr_lst =/= []))
    -- (wf_val: `%`(v_val))*{v_val <- val_lst}
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; ../specification/wasm-1.0/8-reduction.spectec:148.1-149.39
  rule trap_label{v_n : n, instr'_lst : instr*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(v_n, instr'_lst, [TRAP_admininstr])], [TRAP_admininstr])
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(v_n, instr'_lst, [TRAP_admininstr]))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; ../specification/wasm-1.0/8-reduction.spectec:151.1-152.33
  rule trap_frame{v_n : n, f : frame}:
    `%~>%`([`FRAME_%{%}%`_admininstr(v_n, f, [TRAP_admininstr])], [TRAP_admininstr])
    -- wf_admininstr: `%`(`FRAME_%{%}%`_admininstr(v_n, f, [TRAP_admininstr]))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; ../specification/wasm-1.0/8-reduction.spectec:173.1-175.34
  rule unop_val{t : valtype, c_1 : val_, unop : unop_, c : val_, var_0 : val_*?}:
    `%~>%`([CONST_admininstr(t, c_1) UNOP_admininstr(t, unop)], [CONST_admininstr(t, c)])
    -- fun_unop_: `%%%%`(t, unop, c_1, var_0)
    -- if (|!(var_0)| > 0)
    -- if (var_0 =/= ?())
    -- if (c <- !(var_0))
    -- (wf_val_: `%%`(t, iter))*{iter <- !(var_0)}
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(UNOP_admininstr(t, unop))
    -- wf_admininstr: `%`(CONST_admininstr(t, c))

  ;; ../specification/wasm-1.0/8-reduction.spectec:177.1-179.35
  rule unop_trap{t : valtype, c_1 : val_, unop : unop_, var_0 : val_*?}:
    `%~>%`([CONST_admininstr(t, c_1) UNOP_admininstr(t, unop)], [TRAP_admininstr])
    -- fun_unop_: `%%%%`(t, unop, c_1, var_0)
    -- if (var_0 =/= ?())
    -- if (!(var_0) = [])
    -- (wf_val_: `%%`(t, iter))*{iter <- !(var_0)}
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(UNOP_admininstr(t, unop))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; ../specification/wasm-1.0/8-reduction.spectec:182.1-184.41
  rule binop_val{t : valtype, c_1 : val_, c_2 : val_, binop : binop_, c : val_, var_0 : val_*?}:
    `%~>%`([CONST_admininstr(t, c_1) CONST_admininstr(t, c_2) BINOP_admininstr(t, binop)], [CONST_admininstr(t, c)])
    -- fun_binop_: `%%%%%`(t, binop, c_1, c_2, var_0)
    -- if (|!(var_0)| > 0)
    -- if (var_0 =/= ?())
    -- if (c <- !(var_0))
    -- (wf_val_: `%%`(t, iter))*{iter <- !(var_0)}
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(CONST_admininstr(t, c_2))
    -- wf_admininstr: `%`(BINOP_admininstr(t, binop))
    -- wf_admininstr: `%`(CONST_admininstr(t, c))

  ;; ../specification/wasm-1.0/8-reduction.spectec:186.1-188.42
  rule binop_trap{t : valtype, c_1 : val_, c_2 : val_, binop : binop_, var_0 : val_*?}:
    `%~>%`([CONST_admininstr(t, c_1) CONST_admininstr(t, c_2) BINOP_admininstr(t, binop)], [TRAP_admininstr])
    -- fun_binop_: `%%%%%`(t, binop, c_1, c_2, var_0)
    -- if (var_0 =/= ?())
    -- if (!(var_0) = [])
    -- (wf_val_: `%%`(t, iter))*{iter <- !(var_0)}
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(CONST_admininstr(t, c_2))
    -- wf_admininstr: `%`(BINOP_admininstr(t, binop))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; ../specification/wasm-1.0/8-reduction.spectec:191.1-193.37
  rule testop{t : valtype, c_1 : val_, testop : testop_, c : val_, var_0 : val_?}:
    `%~>%`([CONST_admininstr(t, c_1) TESTOP_admininstr(t, testop)], [CONST_admininstr(I32_valtype, c)])
    -- fun_testop_: `%%%%`(t, testop, c_1, var_0)
    -- if (var_0 =/= ?())
    -- if (c = !(var_0))
    -- wf_val_: `%%`(I32_valtype, !(var_0))
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(TESTOP_admininstr(t, testop))
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))

  ;; ../specification/wasm-1.0/8-reduction.spectec:195.1-197.40
  rule relop{t : valtype, c_1 : val_, c_2 : val_, relop : relop_, c : val_, var_0 : val_?}:
    `%~>%`([CONST_admininstr(t, c_1) CONST_admininstr(t, c_2) RELOP_admininstr(t, relop)], [CONST_admininstr(I32_valtype, c)])
    -- fun_relop_: `%%%%%`(t, relop, c_1, c_2, var_0)
    -- if (var_0 =/= ?())
    -- if (c = !(var_0))
    -- wf_val_: `%%`(I32_valtype, !(var_0))
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(CONST_admininstr(t, c_2))
    -- wf_admininstr: `%`(RELOP_admininstr(t, relop))
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))

  ;; ../specification/wasm-1.0/8-reduction.spectec:200.1-202.44
  rule cvtop_val{t_1 : valtype, c_1 : val_, t_2 : valtype, v_cvtop : cvtop, c : val_, var_0 : val_*?}:
    `%~>%`([CONST_admininstr(t_1, c_1) CVTOP_admininstr(t_2, t_1, v_cvtop)], [CONST_admininstr(t_2, c)])
    -- fun_cvtop__: `%%%%%`(t_1, t_2, v_cvtop, c_1, var_0)
    -- if (|!(var_0)| > 0)
    -- if (var_0 =/= ?())
    -- if (c <- !(var_0))
    -- (wf_val_: `%%`(t_2, iter))*{iter <- !(var_0)}
    -- wf_admininstr: `%`(CONST_admininstr(t_1, c_1))
    -- wf_admininstr: `%`(CVTOP_admininstr(t_2, t_1, v_cvtop))
    -- wf_admininstr: `%`(CONST_admininstr(t_2, c))

  ;; ../specification/wasm-1.0/8-reduction.spectec:204.1-206.45
  rule cvtop_trap{t_1 : valtype, c_1 : val_, t_2 : valtype, v_cvtop : cvtop, var_0 : val_*?}:
    `%~>%`([CONST_admininstr(t_1, c_1) CVTOP_admininstr(t_2, t_1, v_cvtop)], [TRAP_admininstr])
    -- fun_cvtop__: `%%%%%`(t_1, t_2, v_cvtop, c_1, var_0)
    -- if (var_0 =/= ?())
    -- if (!(var_0) = [])
    -- (wf_val_: `%%`(t_2, iter))*{iter <- !(var_0)}
    -- wf_admininstr: `%`(CONST_admininstr(t_1, c_1))
    -- wf_admininstr: `%`(CVTOP_admininstr(t_2, t_1, v_cvtop))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; ../specification/wasm-1.0/8-reduction.spectec:217.1-218.47
  rule local_tee{v_val : val, x : idx}:
    `%~>%`([$admininstr_val(v_val) LOCAL_TEE_admininstr(x)], [$admininstr_val(v_val) $admininstr_val(v_val) LOCAL_SET_admininstr(x)])
    -- wf_val: `%`(v_val)
    -- wf_admininstr: `%`(LOCAL_TEE_admininstr(x))
    -- wf_admininstr: `%`(LOCAL_SET_admininstr(x))

;; ../specification/wasm-1.0/8-reduction.spectec:121.1-123.15
relation Step_read_before_call_indirect_trap: `%`(config)
  ;; ../specification/wasm-1.0/8-reduction.spectec:116.1-119.43
  rule call_indirect_call_0{z : state, i : val_, x : idx, a : addr}:
    `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]))
    -- if ($proj_uN_0(!($proj_val__0(i))).0 < |$fun_table(z, mk_uN_tableidx(0)).REFS_tableinst|)
    -- if ($proj_val__0(i) =/= ?())
    -- if ($fun_table(z, mk_uN_tableidx(0)).REFS_tableinst[$proj_uN_0(!($proj_val__0(i))).0] = ?(a))
    -- if (a < |$fun_funcinst(z)|)
    -- if ($fun_type(z, x) = $fun_funcinst(z)[a].TYPE_funcinst)
    -- wf_tableinst: `%`($fun_table(z, mk_uN_tableidx(0)))
    -- (wf_funcinst: `%`(iter))*{iter <- $fun_funcinst(z)}
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]))
    -- wf_admininstr: `%`(CALL_ADDR_admininstr(a))
    -- wf_uN: `%%`(32, mk_uN_uN(0))

;; ../specification/wasm-1.0/8-reduction.spectec:7.1-7.77
relation Step_read: `%~>%`(config, admininstr*)
  ;; ../specification/wasm-1.0/8-reduction.spectec:63.1-65.49
  rule block{z : state, t_opt : valtype?, instr_lst : instr*, v_n : n}:
    `%~>%`(mk_config_config(z, [BLOCK_admininstr(t_opt, instr_lst)]), [`LABEL_%{%}%`_admininstr(v_n, [], $admininstr_instr(v_instr)*{v_instr <- instr_lst})])
    -- if (((t_opt = ?()) /\ (v_n = 0)) \/ ((t_opt =/= ?()) /\ (v_n = 1)))
    -- wf_config: `%`(mk_config_config(z, [BLOCK_admininstr(t_opt, instr_lst)]))
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(v_n, [], $admininstr_instr(v_instr)*{v_instr <- instr_lst}))

  ;; ../specification/wasm-1.0/8-reduction.spectec:67.1-68.63
  rule loop{z : state, t_opt : valtype?, instr_lst : instr*}:
    `%~>%`(mk_config_config(z, [LOOP_admininstr(t_opt, instr_lst)]), [`LABEL_%{%}%`_admininstr(0, [LOOP_instr(t_opt, instr_lst)], $admininstr_instr(v_instr)*{v_instr <- instr_lst})])
    -- wf_config: `%`(mk_config_config(z, [LOOP_admininstr(t_opt, instr_lst)]))
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(0, [LOOP_instr(t_opt, instr_lst)], $admininstr_instr(v_instr)*{v_instr <- instr_lst}))

  ;; ../specification/wasm-1.0/8-reduction.spectec:113.1-114.47
  rule call{z : state, x : idx}:
    `%~>%`(mk_config_config(z, [CALL_admininstr(x)]), [CALL_ADDR_admininstr($fun_funcaddr(z)[$proj_uN_0(x).0])])
    -- if ($proj_uN_0(x).0 < |$fun_funcaddr(z)|)
    -- wf_config: `%`(mk_config_config(z, [CALL_admininstr(x)]))
    -- wf_admininstr: `%`(CALL_ADDR_admininstr($fun_funcaddr(z)[$proj_uN_0(x).0]))

  ;; ../specification/wasm-1.0/8-reduction.spectec:116.1-119.43
  rule call_indirect_call{z : state, i : val_, x : idx, a : addr}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]), [CALL_ADDR_admininstr(a)])
    -- if ($proj_uN_0(!($proj_val__0(i))).0 < |$fun_table(z, mk_uN_tableidx(0)).REFS_tableinst|)
    -- if ($proj_val__0(i) =/= ?())
    -- if ($fun_table(z, mk_uN_tableidx(0)).REFS_tableinst[$proj_uN_0(!($proj_val__0(i))).0] = ?(a))
    -- if (a < |$fun_funcinst(z)|)
    -- if ($fun_type(z, x) = $fun_funcinst(z)[a].TYPE_funcinst)
    -- wf_tableinst: `%`($fun_table(z, mk_uN_tableidx(0)))
    -- (wf_funcinst: `%`(iter))*{iter <- $fun_funcinst(z)}
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]))
    -- wf_admininstr: `%`(CALL_ADDR_admininstr(a))
    -- wf_uN: `%%`(32, mk_uN_uN(0))

  ;; ../specification/wasm-1.0/8-reduction.spectec:121.1-123.15
  rule call_indirect_trap{z : state, i : val_, x : idx}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]), [TRAP_admininstr])
    -- ~ Step_read_before_call_indirect_trap: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; ../specification/wasm-1.0/8-reduction.spectec:125.1-129.54
  rule call_addr{z : state, k : nat, val_lst : val*, a : addr, v_n : n, f : frame, instr_lst : instr*, t_1_lst : valtype*, t_2_lst : valtype*, mm : moduleinst, v_func : func, x : idx, t_lst : valtype*, var_0_lst : val*}:
    `%~>%`(mk_config_config(z, $admininstr_val(v_val)^k{v_val <- val_lst} ++ [CALL_ADDR_admininstr(a)]), [`FRAME_%{%}%`_admininstr(v_n, f, [`LABEL_%{%}%`_admininstr(v_n, [], $admininstr_instr(v_instr)*{v_instr <- instr_lst})])])
    -- if (|var_0_lst| = |t_lst|)
    -- (fun_default_: `%%`(t, var_0))*{var_0 <- var_0_lst, t <- t_lst}
    -- if (a < |$fun_funcinst(z)|)
    -- if ($fun_funcinst(z)[a] = {TYPE mk_functype_functype(t_1_lst, t_2_lst), MODULE mm, CODE v_func})
    -- if (v_func = FUNC_func(x, LOCAL_local(t)*{t <- t_lst}, instr_lst))
    -- if (f = {LOCALS val_lst ++ var_0_lst, MODULE mm})
    -- (wf_funcinst: `%`(iter))*{iter <- $fun_funcinst(z)}
    -- wf_config: `%`(mk_config_config(z, $admininstr_val(v_val)^k{v_val <- val_lst} ++ [CALL_ADDR_admininstr(a)]))
    -- wf_admininstr: `%`(`FRAME_%{%}%`_admininstr(v_n, f, [`LABEL_%{%}%`_admininstr(v_n, [], $admininstr_instr(v_instr)*{v_instr <- instr_lst})]))
    -- wf_funcinst: `%`({TYPE mk_functype_functype(t_1_lst, t_2_lst), MODULE mm, CODE v_func})
    -- wf_func: `%`(FUNC_func(x, LOCAL_local(t)*{t <- t_lst}, instr_lst))
    -- wf_frame: `%`({LOCALS val_lst ++ var_0_lst, MODULE mm})
    -- if (k = |val_lst|)
    -- if (k = |t_1_lst|)
    -- if (v_n = |t_2_lst|)

  ;; ../specification/wasm-1.0/8-reduction.spectec:211.1-212.37
  rule local_get{z : state, x : idx}:
    `%~>%`(mk_config_config(z, [LOCAL_GET_admininstr(x)]), [$admininstr_val($fun_local(z, x))])
    -- wf_val: `%`($fun_local(z, x))
    -- wf_config: `%`(mk_config_config(z, [LOCAL_GET_admininstr(x)]))

  ;; ../specification/wasm-1.0/8-reduction.spectec:223.1-224.45
  rule global_get{z : state, x : idx}:
    `%~>%`(mk_config_config(z, [GLOBAL_GET_admininstr(x)]), [$admininstr_val($fun_global(z, x).VALUE_globalinst)])
    -- wf_globalinst: `%`($fun_global(z, x))
    -- wf_config: `%`(mk_config_config(z, [GLOBAL_GET_admininstr(x)]))

  ;; ../specification/wasm-1.0/8-reduction.spectec:232.1-234.59
  rule load_num_trap{z : state, i : val_, t : valtype, ao : memarg}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr(t, ?(), ao)]), [TRAP_admininstr])
    -- if ($proj_val__0(i) =/= ?())
    -- if ((($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0) + ((($size(t) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$fun_mem(z, mk_uN_memidx(0)).BYTES_meminst|)
    -- wf_meminst: `%`($fun_mem(z, mk_uN_memidx(0)))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr(t, ?(), ao)]))
    -- wf_admininstr: `%`(TRAP_admininstr)
    -- wf_uN: `%%`(32, mk_uN_uN(0))

  ;; ../specification/wasm-1.0/8-reduction.spectec:236.1-238.69
  rule load_num_val{z : state, i : val_, t : valtype, ao : memarg, c : val_}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr(t, ?(), ao)]), [CONST_admininstr(t, c)])
    -- if ($proj_val__0(i) =/= ?())
    -- if ($bytes_(t, c) = $fun_mem(z, mk_uN_memidx(0)).BYTES_meminst[($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0) : ((($size(t) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])
    -- (wf_byte: `%`(iter))*{iter <- $bytes_(t, c)}
    -- wf_meminst: `%`($fun_mem(z, mk_uN_memidx(0)))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr(t, ?(), ao)]))
    -- wf_admininstr: `%`(CONST_admininstr(t, c))
    -- wf_uN: `%%`(32, mk_uN_uN(0))

  ;; ../specification/wasm-1.0/8-reduction.spectec:240.1-242.52
  rule load_pack_trap{z : state, i : val_, v_Inn : Inn, v_n : n, v_sx : sx, ao : memarg}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr($valtype_Inn(v_Inn), ?(mk_loadop__0_loadop_(v_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(v_n), v_sx))), ao)]), [TRAP_admininstr])
    -- if ($proj_val__0(i) =/= ?())
    -- if ((($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0) + (((v_n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$fun_mem(z, mk_uN_memidx(0)).BYTES_meminst|)
    -- wf_meminst: `%`($fun_mem(z, mk_uN_memidx(0)))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr($valtype_Inn(v_Inn), ?(mk_loadop__0_loadop_(v_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(v_n), v_sx))), ao)]))
    -- wf_admininstr: `%`(TRAP_admininstr)
    -- wf_uN: `%%`(32, mk_uN_uN(0))

  ;; ../specification/wasm-1.0/8-reduction.spectec:244.1-246.63
  rule load_pack_val{z : state, i : val_, v_Inn : Inn, v_n : n, v_sx : sx, ao : memarg, c : iN}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr($valtype_Inn(v_Inn), ?(mk_loadop__0_loadop_(v_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(v_n), v_sx))), ao)]), [CONST_admininstr($valtype_Inn(v_Inn), mk_val__0_val_(v_Inn, $extend__(v_n, $size($valtype_Inn(v_Inn)), v_sx, c)))])
    -- if ($proj_val__0(i) =/= ?())
    -- if ($ibytes_(v_n, c) = $fun_mem(z, mk_uN_memidx(0)).BYTES_meminst[($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0) : (((v_n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])
    -- (wf_byte: `%`(iter))*{iter <- $ibytes_(v_n, c)}
    -- wf_meminst: `%`($fun_mem(z, mk_uN_memidx(0)))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr($valtype_Inn(v_Inn), ?(mk_loadop__0_loadop_(v_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(v_n), v_sx))), ao)]))
    -- wf_admininstr: `%`(CONST_admininstr($valtype_Inn(v_Inn), mk_val__0_val_(v_Inn, $extend__(v_n, $size($valtype_Inn(v_Inn)), v_sx, c))))
    -- wf_uN: `%%`(32, mk_uN_uN(0))

  ;; ../specification/wasm-1.0/8-reduction.spectec:266.1-268.45
  rule memory_size{z : state, v_n : n}:
    `%~>%`(mk_config_config(z, [MEMORY_SIZE_admininstr]), [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(v_n)))])
    -- if (((v_n * 64) * $Ki) = |$fun_mem(z, mk_uN_memidx(0)).BYTES_meminst|)
    -- wf_meminst: `%`($fun_mem(z, mk_uN_memidx(0)))
    -- wf_config: `%`(mk_config_config(z, [MEMORY_SIZE_admininstr]))
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(v_n))))
    -- wf_uN: `%%`(32, mk_uN_uN(0))

;; ../specification/wasm-1.0/8-reduction.spectec:5.1-5.77
rec {

;; ../specification/wasm-1.0/8-reduction.spectec:5.1-5.77
relation Step: `%~>%`(config, config)
  ;; ../specification/wasm-1.0/8-reduction.spectec:10.1-12.44
  rule pure{z : state, admininstr_lst : admininstr*, admininstr'_lst : admininstr*}:
    `%~>%`(mk_config_config(z, admininstr_lst), mk_config_config(z, admininstr'_lst))
    -- Step_pure: `%~>%`(admininstr_lst, admininstr'_lst)
    -- wf_config: `%`(mk_config_config(z, admininstr_lst))
    -- wf_config: `%`(mk_config_config(z, admininstr'_lst))

  ;; ../specification/wasm-1.0/8-reduction.spectec:14.1-16.47
  rule read{z : state, admininstr_lst : admininstr*, admininstr'_lst : admininstr*}:
    `%~>%`(mk_config_config(z, admininstr_lst), mk_config_config(z, admininstr'_lst))
    -- Step_read: `%~>%`(mk_config_config(z, admininstr_lst), admininstr'_lst)
    -- wf_config: `%`(mk_config_config(z, admininstr_lst))
    -- wf_config: `%`(mk_config_config(z, admininstr'_lst))

  ;; ../specification/wasm-1.0/8-reduction.spectec:157.1-159.46
  rule ctxt_label{z : state, v_n : n, instr_0_lst : instr*, admininstr_lst : admininstr*, z' : state, admininstr'_lst : admininstr*}:
    `%~>%`(mk_config_config(z, [`LABEL_%{%}%`_admininstr(v_n, instr_0_lst, admininstr_lst)]), mk_config_config(z', [`LABEL_%{%}%`_admininstr(v_n, instr_0_lst, admininstr'_lst)]))
    -- Step: `%~>%`(mk_config_config(z, admininstr_lst), mk_config_config(z', admininstr'_lst))
    -- wf_config: `%`(mk_config_config(z, [`LABEL_%{%}%`_admininstr(v_n, instr_0_lst, admininstr_lst)]))
    -- wf_config: `%`(mk_config_config(z', [`LABEL_%{%}%`_admininstr(v_n, instr_0_lst, admininstr'_lst)]))
    -- wf_config: `%`(mk_config_config(z, admininstr_lst))
    -- wf_config: `%`(mk_config_config(z', admininstr'_lst))

  ;; ../specification/wasm-1.0/8-reduction.spectec:161.1-163.55
  rule ctxt_frame{s : store, f : frame, v_n : n, f' : frame, admininstr_lst : admininstr*, s' : store, f'' : frame, admininstr'_lst : admininstr*}:
    `%~>%`(mk_config_config(mk_state_state(s, f), [`FRAME_%{%}%`_admininstr(v_n, f', admininstr_lst)]), mk_config_config(mk_state_state(s', f), [`FRAME_%{%}%`_admininstr(v_n, f'', admininstr'_lst)]))
    -- Step: `%~>%`(mk_config_config(mk_state_state(s, f'), admininstr_lst), mk_config_config(mk_state_state(s', f''), admininstr'_lst))
    -- wf_config: `%`(mk_config_config(mk_state_state(s, f), [`FRAME_%{%}%`_admininstr(v_n, f', admininstr_lst)]))
    -- wf_config: `%`(mk_config_config(mk_state_state(s', f), [`FRAME_%{%}%`_admininstr(v_n, f'', admininstr'_lst)]))
    -- wf_config: `%`(mk_config_config(mk_state_state(s, f'), admininstr_lst))
    -- wf_config: `%`(mk_config_config(mk_state_state(s', f''), admininstr'_lst))

  ;; ../specification/wasm-1.0/8-reduction.spectec:165.1-168.46
  rule ctxt_instrs{z : state, val_lst : val*, admininstr_lst : admininstr*, admininstr_1_lst : admininstr*, z' : state, admininstr'_lst : admininstr*}:
    `%~>%`(mk_config_config(z, $admininstr_val(v_val)*{v_val <- val_lst} ++ admininstr_lst ++ admininstr_1_lst), mk_config_config(z', $admininstr_val(v_val)*{v_val <- val_lst} ++ admininstr'_lst ++ admininstr_1_lst))
    -- Step: `%~>%`(mk_config_config(z, admininstr_lst), mk_config_config(z', admininstr'_lst))
    -- if ((val_lst =/= []) \/ (admininstr_1_lst =/= []))
    -- wf_config: `%`(mk_config_config(z, $admininstr_val(v_val)*{v_val <- val_lst} ++ admininstr_lst ++ admininstr_1_lst))
    -- wf_config: `%`(mk_config_config(z', $admininstr_val(v_val)*{v_val <- val_lst} ++ admininstr'_lst ++ admininstr_1_lst))
    -- wf_config: `%`(mk_config_config(z, admininstr_lst))
    -- wf_config: `%`(mk_config_config(z', admininstr'_lst))

  ;; ../specification/wasm-1.0/8-reduction.spectec:214.1-215.56
  rule local_set{z : state, v_val : val, x : idx, var_0 : state}:
    `%~>%`(mk_config_config(z, [$admininstr_val(v_val) LOCAL_SET_admininstr(x)]), mk_config_config(var_0, []))
    -- fun_with_local: `%%%%`(z, x, v_val, var_0)
    -- wf_config: `%`(mk_config_config(z, [$admininstr_val(v_val) LOCAL_SET_admininstr(x)]))
    -- wf_config: `%`(mk_config_config(var_0, []))

  ;; ../specification/wasm-1.0/8-reduction.spectec:226.1-227.58
  rule global_set{z : state, v_val : val, x : idx, var_0 : state}:
    `%~>%`(mk_config_config(z, [$admininstr_val(v_val) GLOBAL_SET_admininstr(x)]), mk_config_config(var_0, []))
    -- fun_with_global: `%%%%`(z, x, v_val, var_0)
    -- wf_config: `%`(mk_config_config(z, [$admininstr_val(v_val) GLOBAL_SET_admininstr(x)]))
    -- wf_config: `%`(mk_config_config(var_0, []))

  ;; ../specification/wasm-1.0/8-reduction.spectec:249.1-251.59
  rule store_num_trap{z : state, i : val_, t : valtype, c : val_, ao : memarg}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr(t, c) STORE_admininstr(t, ?(), ao)]), mk_config_config(z, [TRAP_admininstr]))
    -- if ($proj_val__0(i) =/= ?())
    -- if ((($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0) + ((($size(t) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$fun_mem(z, mk_uN_memidx(0)).BYTES_meminst|)
    -- wf_meminst: `%`($fun_mem(z, mk_uN_memidx(0)))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr(t, c) STORE_admininstr(t, ?(), ao)]))
    -- wf_config: `%`(mk_config_config(z, [TRAP_admininstr]))
    -- wf_uN: `%%`(32, mk_uN_uN(0))

  ;; ../specification/wasm-1.0/8-reduction.spectec:253.1-255.27
  rule store_num_val{z : state, i : val_, t : valtype, c : val_, ao : memarg, b_lst : byte*, var_0 : state}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr(t, c) STORE_admininstr(t, ?(), ao)]), mk_config_config(var_0, []))
    -- if ($proj_val__0(i) =/= ?())
    -- fun_with_mem: `%%%%%%`(z, mk_uN_memidx(0), ($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0), ((($size(t) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b_lst, var_0)
    -- if (b_lst = $bytes_(t, c))
    -- (wf_byte: `%`(iter))*{iter <- $bytes_(t, c)}
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr(t, c) STORE_admininstr(t, ?(), ao)]))
    -- wf_config: `%`(mk_config_config(var_0, []))

  ;; ../specification/wasm-1.0/8-reduction.spectec:257.1-259.52
  rule store_pack_trap{z : state, i : val_, v_Inn : Inn, c : val_, v_n : n, ao : memarg}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr($valtype_Inn(v_Inn), c) STORE_admininstr($valtype_Inn(v_Inn), ?(mk_sz_sz(v_n)), ao)]), mk_config_config(z, [TRAP_admininstr]))
    -- if ($proj_val__0(i) =/= ?())
    -- if ((($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0) + (((v_n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$fun_mem(z, mk_uN_memidx(0)).BYTES_meminst|)
    -- wf_meminst: `%`($fun_mem(z, mk_uN_memidx(0)))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr($valtype_Inn(v_Inn), c) STORE_admininstr($valtype_Inn(v_Inn), ?(mk_sz_sz(v_n)), ao)]))
    -- wf_config: `%`(mk_config_config(z, [TRAP_admininstr]))
    -- wf_uN: `%%`(32, mk_uN_uN(0))

  ;; ../specification/wasm-1.0/8-reduction.spectec:261.1-263.52
  rule store_pack_val{z : state, i : val_, v_Inn : Inn, c : val_, v_n : n, ao : memarg, b_lst : byte*, var_0 : state}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr($valtype_Inn(v_Inn), c) STORE_admininstr($valtype_Inn(v_Inn), ?(mk_sz_sz(v_n)), ao)]), mk_config_config(var_0, []))
    -- if ($proj_val__0(i) =/= ?())
    -- fun_with_mem: `%%%%%%`(z, mk_uN_memidx(0), ($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0), (((v_n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b_lst, var_0)
    -- if ($proj_val__0(c) =/= ?())
    -- if (b_lst = $ibytes_(v_n, $wrap__($size($valtype_Inn(v_Inn)), v_n, !($proj_val__0(c)))))
    -- (wf_byte: `%`(iter))*{iter <- $ibytes_(v_n, $wrap__($size($valtype_Inn(v_Inn)), v_n, !($proj_val__0(c))))}
    -- wf_uN: `%%`(v_n, $wrap__($size($valtype_Inn(v_Inn)), v_n, !($proj_val__0(c))))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr($valtype_Inn(v_Inn), c) STORE_admininstr($valtype_Inn(v_Inn), ?(mk_sz_sz(v_n)), ao)]))
    -- wf_config: `%`(mk_config_config(var_0, []))

  ;; ../specification/wasm-1.0/8-reduction.spectec:271.1-273.40
  rule memory_grow_succeed{z : state, v_n : n, mi : meminst, var_1 : meminst?, var_0 : state}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(v_n))) MEMORY_GROW_admininstr]), mk_config_config(var_0, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN((((|$fun_mem(z, mk_uN_memidx(0)).BYTES_meminst| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) : rat <:> nat))))]))
    -- fun_growmemory: `%%%`($fun_mem(z, mk_uN_memidx(0)), v_n, var_1)
    -- fun_with_meminst: `%%%%`(z, mk_uN_memidx(0), mi, var_0)
    -- if (var_1 =/= ?())
    -- if (!(var_1) = mi)
    -- wf_meminst: `%`(!(var_1))
    -- wf_meminst: `%`($fun_mem(z, mk_uN_memidx(0)))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(v_n))) MEMORY_GROW_admininstr]))
    -- wf_config: `%`(mk_config_config(var_0, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN((((|$fun_mem(z, mk_uN_memidx(0)).BYTES_meminst| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) : rat <:> nat))))]))
    -- wf_uN: `%%`(32, mk_uN_uN(0))

  ;; ../specification/wasm-1.0/8-reduction.spectec:275.1-276.77
  rule memory_grow_fail{z : state, v_n : n, var_0 : nat}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(v_n))) MEMORY_GROW_admininstr]), mk_config_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(var_0)))]))
    -- fun_inv_signed_: `%%%`(32, - (1 : nat <:> int), var_0)
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(v_n))) MEMORY_GROW_admininstr]))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(var_0)))]))
}

;; ../specification/wasm-1.0/8-reduction.spectec:8.1-8.77
rec {

;; ../specification/wasm-1.0/8-reduction.spectec:8.1-8.77
relation Steps: `%~>*%`(config, config)
  ;; ../specification/wasm-1.0/8-reduction.spectec:18.1-19.36
  rule refl{z : state, admininstr_lst : admininstr*}:
    `%~>*%`(mk_config_config(z, admininstr_lst), mk_config_config(z, admininstr_lst))
    -- wf_config: `%`(mk_config_config(z, admininstr_lst))

  ;; ../specification/wasm-1.0/8-reduction.spectec:21.1-24.54
  rule trans{z : state, admininstr_lst : admininstr*, z'' : state, admininstr''_lst : admininstr*, z' : state, admininstr'_lst : admininstr*}:
    `%~>*%`(mk_config_config(z, admininstr_lst), mk_config_config(z'', admininstr''_lst))
    -- Step: `%~>%`(mk_config_config(z, admininstr_lst), mk_config_config(z', admininstr'_lst))
    -- Steps: `%~>*%`(mk_config_config(z', admininstr'_lst), mk_config_config(z'', admininstr''_lst))
    -- wf_config: `%`(mk_config_config(z, admininstr_lst))
    -- wf_config: `%`(mk_config_config(z'', admininstr''_lst))
    -- wf_config: `%`(mk_config_config(z', admininstr'_lst))
}

;; ../specification/wasm-1.0/8-reduction.spectec:29.1-29.83
relation Eval_expr: `%;%~>*%;%`(state, expr, state, val*)
  ;; ../specification/wasm-1.0/8-reduction.spectec:31.1-33.37
  rule mk_Eval_expr{z : state, instr_lst : instr*, z' : state, val_lst : val*}:
    `%;%~>*%;%`(z, instr_lst, z', val_lst)
    -- Steps: `%~>*%`(mk_config_config(z, $admininstr_instr(v_instr)*{v_instr <- instr_lst}), mk_config_config(z', $admininstr_val(v_val)*{v_val <- val_lst}))
    -- wf_config: `%`(mk_config_config(z, $admininstr_instr(v_instr)*{v_instr <- instr_lst}))
    -- wf_config: `%`(mk_config_config(z', $admininstr_val(v_val)*{v_val <- val_lst}))

;; ../specification/wasm-1.0/9-module.spectec:5.1-5.36
rec {

;; ../specification/wasm-1.0/9-module.spectec:5.6-5.12
relation fun_funcs: `%%`(externaddr*, funcaddr*)
  ;; ../specification/wasm-1.0/9-module.spectec:5.6-5.12
  rule fun_funcs_case_0:
    `%%`([], [])

  ;; ../specification/wasm-1.0/9-module.spectec:5.6-5.12
  rule fun_funcs_case_1{fa : nat, externaddr'_lst : externaddr*, var_0 : funcaddr*}:
    `%%`([FUNC_externaddr(fa)] ++ externaddr'_lst, [fa] ++ var_0)
    -- fun_funcs: `%%`(externaddr'_lst, var_0)

  ;; ../specification/wasm-1.0/9-module.spectec:5.6-5.12
  rule fun_funcs_case_2{v_externaddr : externaddr, externaddr'_lst : externaddr*, var_0 : funcaddr*}:
    `%%`([v_externaddr] ++ externaddr'_lst, var_0)
    -- fun_funcs: `%%`(externaddr'_lst, var_0)
}

;; ../specification/wasm-1.0/9-module.spectec:11.1-11.40
rec {

;; ../specification/wasm-1.0/9-module.spectec:11.6-11.14
relation fun_globals: `%%`(externaddr*, globaladdr*)
  ;; ../specification/wasm-1.0/9-module.spectec:11.6-11.14
  rule fun_globals_case_0:
    `%%`([], [])

  ;; ../specification/wasm-1.0/9-module.spectec:11.6-11.14
  rule fun_globals_case_1{ga : nat, externaddr'_lst : externaddr*, var_0 : globaladdr*}:
    `%%`([GLOBAL_externaddr(ga)] ++ externaddr'_lst, [ga] ++ var_0)
    -- fun_globals: `%%`(externaddr'_lst, var_0)

  ;; ../specification/wasm-1.0/9-module.spectec:11.6-11.14
  rule fun_globals_case_2{v_externaddr : externaddr, externaddr'_lst : externaddr*, var_0 : globaladdr*}:
    `%%`([v_externaddr] ++ externaddr'_lst, var_0)
    -- fun_globals: `%%`(externaddr'_lst, var_0)
}

;; ../specification/wasm-1.0/9-module.spectec:17.1-17.38
rec {

;; ../specification/wasm-1.0/9-module.spectec:17.6-17.13
relation fun_tables: `%%`(externaddr*, tableaddr*)
  ;; ../specification/wasm-1.0/9-module.spectec:17.6-17.13
  rule fun_tables_case_0:
    `%%`([], [])

  ;; ../specification/wasm-1.0/9-module.spectec:17.6-17.13
  rule fun_tables_case_1{ta : nat, externaddr'_lst : externaddr*, var_0 : tableaddr*}:
    `%%`([TABLE_externaddr(ta)] ++ externaddr'_lst, [ta] ++ var_0)
    -- fun_tables: `%%`(externaddr'_lst, var_0)

  ;; ../specification/wasm-1.0/9-module.spectec:17.6-17.13
  rule fun_tables_case_2{v_externaddr : externaddr, externaddr'_lst : externaddr*, var_0 : tableaddr*}:
    `%%`([v_externaddr] ++ externaddr'_lst, var_0)
    -- fun_tables: `%%`(externaddr'_lst, var_0)
}

;; ../specification/wasm-1.0/9-module.spectec:23.1-23.34
rec {

;; ../specification/wasm-1.0/9-module.spectec:23.6-23.11
relation fun_mems: `%%`(externaddr*, memaddr*)
  ;; ../specification/wasm-1.0/9-module.spectec:23.6-23.11
  rule fun_mems_case_0:
    `%%`([], [])

  ;; ../specification/wasm-1.0/9-module.spectec:23.6-23.11
  rule fun_mems_case_1{ma : nat, externaddr'_lst : externaddr*, var_0 : memaddr*}:
    `%%`([MEM_externaddr(ma)] ++ externaddr'_lst, [ma] ++ var_0)
    -- fun_mems: `%%`(externaddr'_lst, var_0)

  ;; ../specification/wasm-1.0/9-module.spectec:23.6-23.11
  rule fun_mems_case_2{v_externaddr : externaddr, externaddr'_lst : externaddr*, var_0 : memaddr*}:
    `%%`([v_externaddr] ++ externaddr'_lst, var_0)
    -- fun_mems: `%%`(externaddr'_lst, var_0)
}

;; ../specification/wasm-1.0/9-module.spectec:36.6-36.16
relation fun_allocfunc: `%%%%`(store, moduleinst, func, (store, funcaddr))
  ;; ../specification/wasm-1.0/9-module.spectec:36.6-36.16
  rule fun_allocfunc_case_0{s : store, v_moduleinst : moduleinst, v_func : func, fi : funcinst, x : uN, local_lst : local*, v_expr : instr*}:
    `%%%%`(s, v_moduleinst, v_func, (s[FUNCS_store =++ [fi]], |s.FUNCS_store|))
    -- if ($proj_uN_0(x).0 < |v_moduleinst.TYPES_moduleinst|)
    -- if (fi = {TYPE v_moduleinst.TYPES_moduleinst[$proj_uN_0(x).0], MODULE v_moduleinst, CODE v_func})
    -- if (v_func = FUNC_func(x, local_lst, v_expr))
    -- wf_funcinst: `%`(fi)
    -- wf_funcinst: `%`({TYPE v_moduleinst.TYPES_moduleinst[$proj_uN_0(x).0], MODULE v_moduleinst, CODE v_func})
    -- wf_func: `%`(FUNC_func(x, local_lst, v_expr))

;; ../specification/wasm-1.0/9-module.spectec:41.1-41.63
rec {

;; ../specification/wasm-1.0/9-module.spectec:41.6-41.17
relation fun_allocfuncs: `%%%%`(store, moduleinst, func*, (store, funcaddr*))
  ;; ../specification/wasm-1.0/9-module.spectec:41.6-41.17
  rule fun_allocfuncs_case_0{s : store, v_moduleinst : moduleinst}:
    `%%%%`(s, v_moduleinst, [], (s, []))

  ;; ../specification/wasm-1.0/9-module.spectec:41.6-41.17
  rule fun_allocfuncs_case_1{s : store, v_moduleinst : moduleinst, v_func : func, func'_lst : func*, fa : funcaddr, s_1 : store, s_2 : store, fa'_lst : funcaddr*, var_2 : (store, funcaddr*), var_1 : (store, funcaddr*), var_0 : (store, funcaddr)}:
    `%%%%`(s, v_moduleinst, [v_func] ++ func'_lst, (s_2, [fa] ++ fa'_lst))
    -- fun_allocfuncs: `%%%%`(s_1, v_moduleinst, func'_lst, var_2)
    -- fun_allocfuncs: `%%%%`(s_1, v_moduleinst, func'_lst, var_1)
    -- fun_allocfunc: `%%%%`(s, v_moduleinst, v_func, var_0)
    -- if ((s_1, fa) = var_0)
    -- if ((s_2, fa'_lst) = var_1)
    -- wf_store: `%`(var_0.0)
    -- wf_store: `%`(var_2.0)
}

;; ../specification/wasm-1.0/9-module.spectec:47.6-47.18
relation fun_allocglobal: `%%%%`(store, globaltype, val, (store, globaladdr))
  ;; ../specification/wasm-1.0/9-module.spectec:47.6-47.18
  rule fun_allocglobal_case_0{s : store, v_globaltype : globaltype, v_val : val, gi : globalinst}:
    `%%%%`(s, v_globaltype, v_val, (s[GLOBALS_store =++ [gi]], |s.GLOBALS_store|))
    -- if (gi = {TYPE v_globaltype, VALUE v_val})
    -- wf_globalinst: `%`(gi)
    -- wf_globalinst: `%`({TYPE v_globaltype, VALUE v_val})

;; ../specification/wasm-1.0/9-module.spectec:51.1-51.67
rec {

;; ../specification/wasm-1.0/9-module.spectec:51.6-51.19
relation fun_allocglobals: `%%%%`(store, globaltype*, val*, (store, globaladdr*))
  ;; ../specification/wasm-1.0/9-module.spectec:51.6-51.19
  rule fun_allocglobals_case_0{s : store}:
    `%%%%`(s, [], [], (s, []))

  ;; ../specification/wasm-1.0/9-module.spectec:51.6-51.19
  rule fun_allocglobals_case_1{s : store, v_globaltype : globaltype, globaltype'_lst : globaltype*, v_val : val, val'_lst : val*, ga : globaladdr, s_1 : store, s_2 : store, ga'_lst : globaladdr*, var_2 : (store, globaladdr*), var_1 : (store, globaladdr*), var_0 : (store, globaladdr)}:
    `%%%%`(s, [v_globaltype] ++ globaltype'_lst, [v_val] ++ val'_lst, (s_2, [ga] ++ ga'_lst))
    -- fun_allocglobals: `%%%%`(s_1, globaltype'_lst, val'_lst, var_2)
    -- fun_allocglobals: `%%%%`(s_1, globaltype'_lst, val'_lst, var_1)
    -- fun_allocglobal: `%%%%`(s, v_globaltype, v_val, var_0)
    -- if ((s_1, ga) = var_0)
    -- if ((s_2, ga'_lst) = var_1)
    -- wf_store: `%`(var_0.0)
    -- wf_store: `%`(var_2.0)
}

;; ../specification/wasm-1.0/9-module.spectec:57.6-57.17
relation fun_alloctable: `%%%`(store, tabletype, (store, tableaddr))
  ;; ../specification/wasm-1.0/9-module.spectec:57.6-57.17
  rule fun_alloctable_case_0{s : store, i : uN, j_opt : u32?, ti : tableinst}:
    `%%%`(s, mk_limits_tabletype(i, j_opt), (s[TABLES_store =++ [ti]], |s.TABLES_store|))
    -- if (ti = {TYPE mk_limits_tabletype(i, j_opt), REFS ?()^$proj_uN_0(i).0{}})
    -- wf_tableinst: `%`(ti)
    -- wf_tableinst: `%`({TYPE mk_limits_tabletype(i, j_opt), REFS ?()^$proj_uN_0(i).0{}})

;; ../specification/wasm-1.0/9-module.spectec:61.1-61.58
rec {

;; ../specification/wasm-1.0/9-module.spectec:61.6-61.18
relation fun_alloctables: `%%%`(store, tabletype*, (store, tableaddr*))
  ;; ../specification/wasm-1.0/9-module.spectec:61.6-61.18
  rule fun_alloctables_case_0{s : store}:
    `%%%`(s, [], (s, []))

  ;; ../specification/wasm-1.0/9-module.spectec:61.6-61.18
  rule fun_alloctables_case_1{s : store, v_tabletype : limits, tabletype'_lst : tabletype*, ta : tableaddr, s_1 : store, s_2 : store, ta'_lst : tableaddr*, var_2 : (store, tableaddr*), var_1 : (store, tableaddr*), var_0 : (store, tableaddr)}:
    `%%%`(s, [v_tabletype] ++ tabletype'_lst, (s_2, [ta] ++ ta'_lst))
    -- fun_alloctables: `%%%`(s_1, tabletype'_lst, var_2)
    -- fun_alloctables: `%%%`(s_1, tabletype'_lst, var_1)
    -- fun_alloctable: `%%%`(s, v_tabletype, var_0)
    -- if ((s_1, ta) = var_0)
    -- if ((s_2, ta'_lst) = var_1)
    -- wf_store: `%`(var_0.0)
    -- wf_store: `%`(var_2.0)
}

;; ../specification/wasm-1.0/9-module.spectec:67.6-67.15
relation fun_allocmem: `%%%`(store, memtype, (store, memaddr))
  ;; ../specification/wasm-1.0/9-module.spectec:67.6-67.15
  rule fun_allocmem_case_0{s : store, i : uN, j_opt : u32?, mi : meminst}:
    `%%%`(s, mk_limits_memtype(i, j_opt), (s[MEMS_store =++ [mi]], |s.MEMS_store|))
    -- if (mi = {TYPE mk_limits_memtype(i, j_opt), BYTES mk_byte_byte(0)^($proj_uN_0(i).0 * (64 * $Ki)){}})
    -- wf_meminst: `%`(mi)
    -- wf_meminst: `%`({TYPE mk_limits_memtype(i, j_opt), BYTES mk_byte_byte(0)^($proj_uN_0(i).0 * (64 * $Ki)){}})

;; ../specification/wasm-1.0/9-module.spectec:71.1-71.52
rec {

;; ../specification/wasm-1.0/9-module.spectec:71.6-71.16
relation fun_allocmems: `%%%`(store, memtype*, (store, memaddr*))
  ;; ../specification/wasm-1.0/9-module.spectec:71.6-71.16
  rule fun_allocmems_case_0{s : store}:
    `%%%`(s, [], (s, []))

  ;; ../specification/wasm-1.0/9-module.spectec:71.6-71.16
  rule fun_allocmems_case_1{s : store, v_memtype : limits, memtype'_lst : memtype*, ma : memaddr, s_1 : store, s_2 : store, ma'_lst : memaddr*, var_2 : (store, memaddr*), var_1 : (store, memaddr*), var_0 : (store, memaddr)}:
    `%%%`(s, [v_memtype] ++ memtype'_lst, (s_2, [ma] ++ ma'_lst))
    -- fun_allocmems: `%%%`(s_1, memtype'_lst, var_2)
    -- fun_allocmems: `%%%`(s_1, memtype'_lst, var_1)
    -- fun_allocmem: `%%%`(s, v_memtype, var_0)
    -- if ((s_1, ma) = var_0)
    -- if ((s_2, ma'_lst) = var_1)
    -- wf_store: `%`(var_0.0)
    -- wf_store: `%`(var_2.0)
}

;; ../specification/wasm-1.0/9-module.spectec:80.6-80.17
relation fun_instexport: `%%%%%%`(funcaddr*, globaladdr*, tableaddr*, memaddr*, export, exportinst)
  ;; ../specification/wasm-1.0/9-module.spectec:80.6-80.17
  rule fun_instexport_case_0{fa_lst : funcaddr*, ga_lst : globaladdr*, ta_lst : tableaddr*, ma_lst : memaddr*, v_name : name, x : uN}:
    `%%%%%%`(fa_lst, ga_lst, ta_lst, ma_lst, EXPORT_export(v_name, FUNC_externidx(x)), {NAME v_name, ADDR FUNC_externaddr(fa_lst[$proj_uN_0(x).0])})
    -- if ($proj_uN_0(x).0 < |fa_lst|)
    -- if ($proj_uN_0(x).0 < |fa_lst|)
    -- wf_exportinst: `%`({NAME v_name, ADDR FUNC_externaddr(fa_lst[$proj_uN_0(x).0])})

  ;; ../specification/wasm-1.0/9-module.spectec:80.6-80.17
  rule fun_instexport_case_1{fa_lst : funcaddr*, ga_lst : globaladdr*, ta_lst : tableaddr*, ma_lst : memaddr*, v_name : name, x : uN}:
    `%%%%%%`(fa_lst, ga_lst, ta_lst, ma_lst, EXPORT_export(v_name, GLOBAL_externidx(x)), {NAME v_name, ADDR GLOBAL_externaddr(ga_lst[$proj_uN_0(x).0])})
    -- if ($proj_uN_0(x).0 < |ga_lst|)
    -- if ($proj_uN_0(x).0 < |ga_lst|)
    -- wf_exportinst: `%`({NAME v_name, ADDR GLOBAL_externaddr(ga_lst[$proj_uN_0(x).0])})

  ;; ../specification/wasm-1.0/9-module.spectec:80.6-80.17
  rule fun_instexport_case_2{fa_lst : funcaddr*, ga_lst : globaladdr*, ta_lst : tableaddr*, ma_lst : memaddr*, v_name : name, x : uN}:
    `%%%%%%`(fa_lst, ga_lst, ta_lst, ma_lst, EXPORT_export(v_name, TABLE_externidx(x)), {NAME v_name, ADDR TABLE_externaddr(ta_lst[$proj_uN_0(x).0])})
    -- if ($proj_uN_0(x).0 < |ta_lst|)
    -- if ($proj_uN_0(x).0 < |ta_lst|)
    -- wf_exportinst: `%`({NAME v_name, ADDR TABLE_externaddr(ta_lst[$proj_uN_0(x).0])})

  ;; ../specification/wasm-1.0/9-module.spectec:80.6-80.17
  rule fun_instexport_case_3{fa_lst : funcaddr*, ga_lst : globaladdr*, ta_lst : tableaddr*, ma_lst : memaddr*, v_name : name, x : uN}:
    `%%%%%%`(fa_lst, ga_lst, ta_lst, ma_lst, EXPORT_export(v_name, MEM_externidx(x)), {NAME v_name, ADDR MEM_externaddr(ma_lst[$proj_uN_0(x).0])})
    -- if ($proj_uN_0(x).0 < |ma_lst|)
    -- if ($proj_uN_0(x).0 < |ma_lst|)
    -- wf_exportinst: `%`({NAME v_name, ADDR MEM_externaddr(ma_lst[$proj_uN_0(x).0])})

;; ../specification/wasm-1.0/9-module.spectec:87.6-87.18
relation fun_allocmodule: `%%%%%`(store, module, externaddr*, val*, (store, moduleinst))
  ;; ../specification/wasm-1.0/9-module.spectec:87.6-87.18
  rule fun_allocmodule_case_0{s : store, v_module : module, externaddr_lst : externaddr*, val_lst : val*, s_4 : store, v_moduleinst : moduleinst, ft_lst : functype*, import_lst : import*, n_func : nat, func_lst : func*, n_global : nat, expr_1_lst : expr*, globaltype_lst : globaltype*, n_table : nat, tabletype_lst : tabletype*, n_mem : nat, memtype_lst : memtype*, elem_lst : elem*, data_lst : data*, start_opt : start?, export_lst : export*, s_1 : store, s_2 : store, s_3 : store, fa_ex_lst : funcaddr*, ga_ex_lst : globaladdr*, ta_ex_lst : tableaddr*, ma_ex_lst : memaddr*, fa_lst : funcaddr*, ga_lst : globaladdr*, ta_lst : tableaddr*, ma_lst : memaddr*, xi_lst : exportinst*, var_13 : (store, memaddr*), var_12 : (store, tableaddr*), var_11 : (store, globaladdr*), var_10 : (store, funcaddr*), var_9_lst : exportinst*, var_8 : (store, memaddr*), var_7 : (store, tableaddr*), var_6 : (store, globaladdr*), var_5 : (store, funcaddr*), var_4_lst : exportinst*, var_3 : memaddr*, var_2 : tableaddr*, var_1 : globaladdr*, var_0 : funcaddr*}:
    `%%%%%`(s, v_module, externaddr_lst, val_lst, (s_4, v_moduleinst))
    -- fun_allocmems: `%%%`(s_3, memtype_lst, var_13)
    -- fun_alloctables: `%%%`(s_2, tabletype_lst, var_12)
    -- fun_allocglobals: `%%%%`(s_1, globaltype_lst, val_lst, var_11)
    -- fun_allocfuncs: `%%%%`(s, v_moduleinst, func_lst, var_10)
    -- if (|var_9_lst| = |export_lst|)
    -- (fun_instexport: `%%%%%%`(fa_ex_lst ++ fa_lst, ga_ex_lst ++ ga_lst, ta_ex_lst ++ ta_lst, ma_ex_lst ++ ma_lst, export_3, var_9))*{var_9 <- var_9_lst, export_3 <- export_lst}
    -- fun_allocmems: `%%%`(s_3, memtype_lst, var_8)
    -- fun_alloctables: `%%%`(s_2, tabletype_lst, var_7)
    -- fun_allocglobals: `%%%%`(s_1, globaltype_lst, val_lst, var_6)
    -- fun_allocfuncs: `%%%%`(s, v_moduleinst, func_lst, var_5)
    -- if (|var_4_lst| = |export_lst|)
    -- (fun_instexport: `%%%%%%`(fa_ex_lst ++ fa_lst, ga_ex_lst ++ ga_lst, ta_ex_lst ++ ta_lst, ma_ex_lst ++ ma_lst, export_2, var_4))*{var_4 <- var_4_lst, export_2 <- export_lst}
    -- fun_mems: `%%`(externaddr_lst, var_3)
    -- fun_tables: `%%`(externaddr_lst, var_2)
    -- fun_globals: `%%`(externaddr_lst, var_1)
    -- fun_funcs: `%%`(externaddr_lst, var_0)
    -- if (v_module = MODULE_module(TYPE_type(ft_1)*{ft_1 <- ft_lst}, import_lst, func_lst, GLOBAL_global(globaltype_195, expr_1_1)^n_global{expr_1_1 <- expr_1_lst, globaltype_195 <- globaltype_lst}, TABLE_table(tabletype_241)^n_table{tabletype_241 <- tabletype_lst}, MEMORY_mem(memtype_293)^n_mem{memtype_293 <- memtype_lst}, elem_lst, data_lst, start_opt, export_lst))
    -- if (fa_ex_lst = var_0)
    -- if (ga_ex_lst = var_1)
    -- if (ta_ex_lst = var_2)
    -- if (ma_ex_lst = var_3)
    -- if (fa_lst = (|s.FUNCS_store| + i_func_1)^(i_func_1<n_func){})
    -- if (ga_lst = (|s.GLOBALS_store| + i_global_1)^(i_global_1<n_global){})
    -- if (ta_lst = (|s.TABLES_store| + i_table_1)^(i_table_1<n_table){})
    -- if (ma_lst = (|s.MEMS_store| + i_mem_1)^(i_mem_1<n_mem){})
    -- if (xi_lst = var_4_lst)
    -- if (v_moduleinst = {TYPES ft_lst, FUNCS fa_ex_lst ++ fa_lst, GLOBALS ga_ex_lst ++ ga_lst, TABLES ta_ex_lst ++ ta_lst, MEMS ma_ex_lst ++ ma_lst, EXPORTS xi_lst})
    -- if ((s_1, fa_lst) = var_5)
    -- if ((s_2, ga_lst) = var_6)
    -- if ((s_3, ta_lst) = var_7)
    -- if ((s_4, ma_lst) = var_8)
    -- wf_store: `%`(s_4)
    -- wf_moduleinst: `%`(v_moduleinst)
    -- wf_store: `%`(s_1)
    -- wf_store: `%`(s_2)
    -- wf_store: `%`(s_3)
    -- (wf_exportinst: `%`(var_9))*{var_9 <- var_9_lst}
    -- wf_store: `%`(var_10.0)
    -- wf_store: `%`(var_11.0)
    -- wf_store: `%`(var_12.0)
    -- wf_store: `%`(var_13.0)
    -- wf_module: `%`(MODULE_module(TYPE_type(ft_3)*{ft_3 <- ft_lst}, import_lst, func_lst, GLOBAL_global(globaltype_199, expr_1_2)^n_global{expr_1_2 <- expr_1_lst, globaltype_199 <- globaltype_lst}, TABLE_table(tabletype_245)^n_table{tabletype_245 <- tabletype_lst}, MEMORY_mem(memtype_297)^n_mem{memtype_297 <- memtype_lst}, elem_lst, data_lst, start_opt, export_lst))
    -- wf_moduleinst: `%`({TYPES ft_lst, FUNCS fa_ex_lst ++ fa_lst, GLOBALS ga_ex_lst ++ ga_lst, TABLES ta_ex_lst ++ ta_lst, MEMS ma_ex_lst ++ ma_lst, EXPORTS xi_lst})

;; ../specification/wasm-1.0/9-module.spectec:128.1-128.61
rec {

;; ../specification/wasm-1.0/9-module.spectec:128.6-128.15
relation fun_initelem: `%%%%%`(store, moduleinst, u32*, funcaddr**, store)
  ;; ../specification/wasm-1.0/9-module.spectec:128.6-128.15
  rule fun_initelem_case_0{s : store, v_moduleinst : moduleinst}:
    `%%%%%`(s, v_moduleinst, [], [], s)

  ;; ../specification/wasm-1.0/9-module.spectec:128.6-128.15
  rule fun_initelem_case_1{s : store, v_moduleinst : moduleinst, i : uN, i'_lst : u32*, a_lst : addr*, a'_lst_lst : addr**, s_1 : store, s_2 : store, var_1 : store, var_0 : store}:
    `%%%%%`(s, v_moduleinst, [i] ++ i'_lst, [a_lst] ++ a'_lst_lst, s_2)
    -- fun_initelem: `%%%%%`(s_1, v_moduleinst, i'_lst, a'_lst_lst, var_1)
    -- fun_initelem: `%%%%%`(s_1, v_moduleinst, i'_lst, a'_lst_lst, var_0)
    -- if (0 < |v_moduleinst.TABLES_moduleinst|)
    -- if (s_1 = s[TABLES_store[v_moduleinst.TABLES_moduleinst[0]].REFS_tableinst[$proj_uN_0(i).0 : |a_lst|] = ?(a_7)*{a_7 <- a_lst}])
    -- if (s_2 = var_0)
    -- wf_store: `%`(s_1)
    -- wf_store: `%`(var_1)
}

;; ../specification/wasm-1.0/9-module.spectec:134.1-134.57
rec {

;; ../specification/wasm-1.0/9-module.spectec:134.6-134.15
relation fun_initdata: `%%%%%`(store, moduleinst, u32*, byte**, store)
  ;; ../specification/wasm-1.0/9-module.spectec:134.6-134.15
  rule fun_initdata_case_0{s : store, v_moduleinst : moduleinst}:
    `%%%%%`(s, v_moduleinst, [], [], s)

  ;; ../specification/wasm-1.0/9-module.spectec:134.6-134.15
  rule fun_initdata_case_1{s : store, v_moduleinst : moduleinst, i : uN, i'_lst : u32*, b_lst : byte*, b'_lst_lst : byte**, s_1 : store, s_2 : store, var_1 : store, var_0 : store}:
    `%%%%%`(s, v_moduleinst, [i] ++ i'_lst, [b_lst] ++ b'_lst_lst, s_2)
    -- fun_initdata: `%%%%%`(s_1, v_moduleinst, i'_lst, b'_lst_lst, var_1)
    -- fun_initdata: `%%%%%`(s_1, v_moduleinst, i'_lst, b'_lst_lst, var_0)
    -- if (0 < |v_moduleinst.MEMS_moduleinst|)
    -- if (s_1 = s[MEMS_store[v_moduleinst.MEMS_moduleinst[0]].BYTES_meminst[$proj_uN_0(i).0 : |b_lst|] = b_lst])
    -- if (s_2 = var_0)
    -- wf_store: `%`(var_1)
}

;; ../specification/wasm-1.0/9-module.spectec:140.6-140.18
relation fun_instantiate: `%%%%`(store, module, externaddr*, config)
  ;; ../specification/wasm-1.0/9-module.spectec:140.6-140.18
  rule fun_instantiate_case_0{s : store, v_module : module, externaddr_lst : externaddr*, f : frame, x'_opt : idx?, functype_lst : functype*, expr_G_lst : expr*, globaltype_lst : globaltype*, expr_E_lst : expr*, x_lst_lst : idx**, b_lst_lst : byte**, expr_D_lst : expr*, moduleinst_init : moduleinst, f_init : frame, val_lst : val*, i_E_lst : val_*, i_D_lst : val_*, type_lst : type*, import_lst : import*, func_lst : func*, global_lst : global*, table_lst : table*, mem_lst : mem*, elem_lst : elem*, data_lst : data*, start_opt : start?, export_lst : export*, n_F : n, z : state, s_1 : store, v_moduleinst : moduleinst, s_2 : store, s_3 : store, var_10 : globaladdr*, var_9 : funcaddr*, var_8 : store, var_7 : store, var_6 : (store, moduleinst), var_5 : (store, moduleinst), var_4 : store, var_3 : store, var_2 : (store, moduleinst), var_1 : globaladdr*, var_0 : funcaddr*}:
    `%%%%`(s, v_module, externaddr_lst, mk_config_config(mk_state_state(s_3, f), lift(CALL_admininstr(x')?{x' <- x'_opt})))
    -- fun_globals: `%%`(externaddr_lst, var_10)
    -- fun_funcs: `%%`(externaddr_lst, var_9)
    -- (if ($proj_val__0(i_D_3) =/= ?()))*{i_D_3 <- i_D_lst}
    -- fun_initdata: `%%%%%`(s_2, v_moduleinst, !($proj_val__0(i_D_3))*{i_D_3 <- i_D_lst}, b_lst_lst, var_8)
    -- (if ($proj_val__0(i_E_3) =/= ?()))*{i_E_3 <- i_E_lst}
    -- (if ($proj_uN_0(x_3).0 < |v_moduleinst.FUNCS_moduleinst|))*{x_3 <- x_lst_3}*{x_lst_3 <- x_lst_lst}
    -- fun_initelem: `%%%%%`(s_1, v_moduleinst, !($proj_val__0(i_E_3))*{i_E_3 <- i_E_lst}, v_moduleinst.FUNCS_moduleinst[$proj_uN_0(x_3).0]*{x_3 <- x_lst_3}*{x_lst_3 <- x_lst_lst}, var_7)
    -- fun_allocmodule: `%%%%%`(s, v_module, externaddr_lst, val_lst, var_6)
    -- fun_allocmodule: `%%%%%`(s, v_module, externaddr_lst, val_lst, var_5)
    -- (if ($proj_val__0(i_D_2) =/= ?()))*{i_D_2 <- i_D_lst}
    -- fun_initdata: `%%%%%`(s_2, v_moduleinst, !($proj_val__0(i_D_2))*{i_D_2 <- i_D_lst}, b_lst_lst, var_4)
    -- (if ($proj_val__0(i_E_2) =/= ?()))*{i_E_2 <- i_E_lst}
    -- (if ($proj_uN_0(x_2).0 < |v_moduleinst.FUNCS_moduleinst|))*{x_2 <- x_lst_2}*{x_lst_2 <- x_lst_lst}
    -- fun_initelem: `%%%%%`(s_1, v_moduleinst, !($proj_val__0(i_E_2))*{i_E_2 <- i_E_lst}, v_moduleinst.FUNCS_moduleinst[$proj_uN_0(x_2).0]*{x_2 <- x_lst_2}*{x_lst_2 <- x_lst_lst}, var_3)
    -- fun_allocmodule: `%%%%%`(s, v_module, externaddr_lst, val_lst, var_2)
    -- fun_globals: `%%`(externaddr_lst, var_1)
    -- fun_funcs: `%%`(externaddr_lst, var_0)
    -- if (MODULE_module(type_lst, import_lst, func_lst, global_lst, table_lst, mem_lst, elem_lst, data_lst, start_opt, export_lst) = v_module)
    -- if (type_lst = TYPE_type(functype_49)*{functype_49 <- functype_lst})
    -- if (global_lst = GLOBAL_global(globaltype_201, expr_G_1)*{expr_G_1 <- expr_G_lst, globaltype_201 <- globaltype_lst})
    -- if (elem_lst = ELEM_elem(expr_E_1, x_lst_1)*{expr_E_1 <- expr_E_lst, x_lst_1 <- x_lst_lst})
    -- if (data_lst = DATA_data(expr_D_1, b_lst_1)*{b_lst_1 <- b_lst_lst, expr_D_1 <- expr_D_lst})
    -- if (start_opt = START_start(x'_1)?{x'_1 <- x'_opt})
    -- if (n_F = |func_lst|)
    -- if (moduleinst_init = {TYPES functype_lst, FUNCS var_0 ++ (|s.FUNCS_store| + i_F_1)^(i_F_1<n_F){}, GLOBALS var_1, TABLES [], MEMS [], EXPORTS []})
    -- if (f_init = {LOCALS [], MODULE moduleinst_init})
    -- if (z = mk_state_state(s, f_init))
    -- if (|expr_G_lst| = |val_lst|)
    -- (Eval_expr: `%;%~>*%;%`(z, expr_G_2, z, [val_4]))*{expr_G_2 <- expr_G_lst, val_4 <- val_lst}
    -- if (|expr_E_lst| = |i_E_lst|)
    -- (Eval_expr: `%;%~>*%;%`(z, expr_E_2, z, [CONST_val(I32_valtype, i_E_1)]))*{expr_E_2 <- expr_E_lst, i_E_1 <- i_E_lst}
    -- if (|expr_D_lst| = |i_D_lst|)
    -- (Eval_expr: `%;%~>*%;%`(z, expr_D_2, z, [CONST_val(I32_valtype, i_D_1)]))*{expr_D_2 <- expr_D_lst, i_D_1 <- i_D_lst}
    -- if ((s_1, v_moduleinst) = var_2)
    -- if (s_2 = var_3)
    -- if (s_3 = var_4)
    -- if (f = {LOCALS [], MODULE v_moduleinst})
    -- (wf_val: `%`(val_6))*{val_6 <- val_lst}
    -- wf_store: `%`(var_5.0)
    -- wf_moduleinst: `%`(var_6.1)
    -- wf_store: `%`(var_7)
    -- wf_store: `%`(var_8)
    -- wf_config: `%`(mk_config_config(mk_state_state(s_3, f), lift(CALL_admininstr(x'_2)?{x'_2 <- x'_opt})))
    -- wf_module: `%`(MODULE_module(type_lst, import_lst, func_lst, global_lst, table_lst, mem_lst, elem_lst, data_lst, start_opt, export_lst))
    -- if (|expr_G_lst| = |globaltype_lst|)
    -- (wf_global: `%`(GLOBAL_global(globaltype_203, expr_G_3)))*{expr_G_3 <- expr_G_lst, globaltype_203 <- globaltype_lst}
    -- if (|expr_E_lst| = |x_lst_lst|)
    -- (wf_elem: `%`(ELEM_elem(expr_E_3, x_lst_4)))*{expr_E_3 <- expr_E_lst, x_lst_4 <- x_lst_lst}
    -- if (|b_lst_lst| = |expr_D_lst|)
    -- (wf_data: `%`(DATA_data(expr_D_3, b_lst_4)))*{b_lst_4 <- b_lst_lst, expr_D_3 <- expr_D_lst}
    -- (wf_start: `%`(START_start(x'_3)))?{x'_3 <- x'_opt}
    -- wf_moduleinst: `%`({TYPES functype_lst, FUNCS var_9 ++ (|s.FUNCS_store| + i_F_2)^(i_F_2<n_F){}, GLOBALS var_10, TABLES [], MEMS [], EXPORTS []})
    -- wf_frame: `%`({LOCALS [], MODULE moduleinst_init})
    -- wf_state: `%`(mk_state_state(s, f_init))
    -- (wf_val: `%`(CONST_val(I32_valtype, i_E_4)))*{i_E_4 <- i_E_lst}
    -- (wf_val: `%`(CONST_val(I32_valtype, i_D_4)))*{i_D_4 <- i_D_lst}
    -- wf_frame: `%`({LOCALS [], MODULE v_moduleinst})

;; ../specification/wasm-1.0/9-module.spectec:169.6-169.13
relation fun_invoke: `%%%%`(store, funcaddr, val*, config)
  ;; ../specification/wasm-1.0/9-module.spectec:169.6-169.13
  rule fun_invoke_case_0{s : store, fa : nat, v_n : nat, val_lst : val*, f : frame, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%%%%`(s, fa, val_lst, mk_config_config(mk_state_state(s, f), $admininstr_val(v_val)^v_n{v_val <- val_lst} ++ [CALL_ADDR_admininstr(fa)]))
    -- if (f = {LOCALS [], MODULE {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], EXPORTS []}})
    -- if (fa < |$fun_funcinst(mk_state_state(s, f))|)
    -- if ($fun_funcinst(mk_state_state(s, f))[fa].TYPE_funcinst = mk_functype_functype(t_1_lst, t_2_lst))
    -- (wf_funcinst: `%`(iter_53))*{iter_53 <- $fun_funcinst(mk_state_state(s, f))}
    -- wf_config: `%`(mk_config_config(mk_state_state(s, f), $admininstr_val(val_10)^v_n{val_10 <- val_lst} ++ [CALL_ADDR_admininstr(fa)]))
    -- wf_frame: `%`({LOCALS [], MODULE {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], EXPORTS []}})
    -- wf_state: `%`(mk_state_state(s, f))
    -- if (v_n = |val_lst|)

;; ../specification/wasm-1.0/A-binary.spectec:483.1-483.43
syntax startopt = start*

;; ../specification/wasm-1.0/A-binary.spectec:500.1-500.29
syntax code = (local*, expr)

;; ../specification/wasm-1.0/B-soundness.spectec:3.1-3.61
relation Context_ok: `|-%:OK`(context)
  ;; ../specification/wasm-1.0/B-soundness.spectec:5.1-21.34
  rule mk_Context_ok{C : context, ft_lst : functype*, ft_2_lst : functype*, gt_lst : globaltype*, tt_lst : tabletype*, mt_lst : memtype*, lct_lst : valtype*, rt_lst : valtype*, rt'_opt : valtype?}:
    `|-%:OK`(C)
    -- if (C = {TYPES ft_lst, FUNCS ft_2_lst, GLOBALS gt_lst, TABLES tt_lst, MEMS mt_lst, LOCALS lct_lst, LABELS ?(rt)*{rt <- rt_lst}, RETURN ?(rt'_opt)})
    -- (Functype_ok: `|-%:OK`(ft))*{ft <- ft_lst}
    -- (Globaltype_ok: `|-%:OK`(gt))*{gt <- gt_lst}
    -- (Memtype_ok: `|-%:OK`(mt))*{mt <- mt_lst}
    -- (Tabletype_ok: `|-%:OK`(tt))*{tt <- tt_lst}
    -- (Functype_ok: `|-%:OK`(ft_2))*{ft_2 <- ft_2_lst}
    -- wf_context: `%`(C)
    -- wf_context: `%`({TYPES ft_lst, FUNCS ft_2_lst, GLOBALS gt_lst, TABLES tt_lst, MEMS mt_lst, LOCALS lct_lst, LABELS ?(rt)*{rt <- rt_lst}, RETURN ?(rt'_opt)})

;; ../specification/wasm-1.0/B-soundness.spectec:25.1-25.34
relation Val_ok: `|-%:%`(val, valtype)
  ;; ../specification/wasm-1.0/B-soundness.spectec:27.1-28.21
  rule mk_Val_ok{t : valtype, c_t : val_}:
    `|-%:%`(CONST_val(t, c_t), t)
    -- wf_val: `%`(CONST_val(t, c_t))

;; ../specification/wasm-1.0/B-soundness.spectec:33.1-33.41
relation Result_ok: `|-%:%`(result, valtype*)
  ;; ../specification/wasm-1.0/B-soundness.spectec:35.1-37.25
  rule result{v_lst : val*, t_lst : valtype*}:
    `|-%:%`(_VALS_result(v_lst), t_lst)
    -- if (|t_lst| = |v_lst|)
    -- (Val_ok: `|-%:%`(v, t))*{t <- t_lst, v <- v_lst}
    -- wf_result: `%`(_VALS_result(v_lst))

  ;; ../specification/wasm-1.0/B-soundness.spectec:39.1-40.15
  rule trap{t_lst : valtype*}:
    `|-%:%`(TRAP_result, t_lst)
    -- wf_result: `%`(TRAP_result)

;; ../specification/wasm-1.0/B-soundness.spectec:44.1-44.31
syntax adminexpr = admininstr*

;; ../specification/wasm-1.0/B-soundness.spectec:99.1-99.84
rec {

;; ../specification/wasm-1.0/B-soundness.spectec:99.1-99.84
relation Externaddr_ok: `%|-%:%`(store, externaddr, externtype)
  ;; ../specification/wasm-1.0/B-soundness.spectec:101.1-103.34
  rule global{s : store, a : addr, v_globalinst : globalinst}:
    `%|-%:%`(s, GLOBAL_externaddr(a), GLOBAL_externtype(v_globalinst.TYPE_globalinst))
    -- if (a < |s.GLOBALS_store|)
    -- if (s.GLOBALS_store[a] = v_globalinst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(GLOBAL_externtype(v_globalinst.TYPE_globalinst))

  ;; ../specification/wasm-1.0/B-soundness.spectec:105.1-107.28
  rule mem{s : store, a : addr, v_meminst : meminst}:
    `%|-%:%`(s, MEM_externaddr(a), MEM_externtype(v_meminst.TYPE_meminst))
    -- if (a < |s.MEMS_store|)
    -- if (s.MEMS_store[a] = v_meminst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(MEM_externtype(v_meminst.TYPE_meminst))

  ;; ../specification/wasm-1.0/B-soundness.spectec:109.1-111.32
  rule table{s : store, a : addr, v_tableinst : tableinst}:
    `%|-%:%`(s, TABLE_externaddr(a), TABLE_externtype(v_tableinst.TYPE_tableinst))
    -- if (a < |s.TABLES_store|)
    -- if (s.TABLES_store[a] = v_tableinst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(TABLE_externtype(v_tableinst.TYPE_tableinst))

  ;; ../specification/wasm-1.0/B-soundness.spectec:113.1-115.30
  rule func{s : store, a : addr, v_funcinst : funcinst}:
    `%|-%:%`(s, FUNC_externaddr(a), FUNC_externtype(v_funcinst.TYPE_funcinst))
    -- if (a < |s.FUNCS_store|)
    -- if (s.FUNCS_store[a] = v_funcinst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(FUNC_externtype(v_funcinst.TYPE_funcinst))

  ;; ../specification/wasm-1.0/B-soundness.spectec:117.1-120.34
  rule sub{s : store, v_externaddr : externaddr, xt : externtype, xt' : externtype}:
    `%|-%:%`(s, v_externaddr, xt)
    -- Externaddr_ok: `%|-%:%`(s, v_externaddr, xt')
    -- Externtype_sub: `|-%<:%`(xt', xt)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(xt)
    -- wf_externtype: `%`(xt')
}

;; ../specification/wasm-1.0/B-soundness.spectec:128.1-128.49
relation Exportinst_ok: `%|-%:OK`(store, exportinst)
  ;; ../specification/wasm-1.0/B-soundness.spectec:152.1-154.33
  rule mk_Exportinst_ok{s : store, nm : name, xa : externaddr, xt : externtype}:
    `%|-%:OK`(s, {NAME nm, ADDR xa})
    -- Externaddr_ok: `%|-%:%`(s, xa, xt)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(xt)
    -- wf_exportinst: `%`({NAME nm, ADDR xa})

;; ../specification/wasm-1.0/B-soundness.spectec:159.1-159.54
relation Moduleinst_ok: `%|-%:%`(store, moduleinst, context)
  ;; ../specification/wasm-1.0/B-soundness.spectec:161.1-182.102
  rule mk_Moduleinst_ok{s : store, functype_lst : functype*, funcaddr_lst : funcaddr*, globaladdr_lst : globaladdr*, tableaddr_lst : tableaddr*, memaddr_lst : memaddr*, exportinst_lst : exportinst*, functype_F_lst : functype*, globaltype_lst : globaltype*, tabletype_lst : tabletype*, memtype_lst : memtype*}:
    `%|-%:%`(s, {TYPES functype_lst, FUNCS funcaddr_lst, GLOBALS globaladdr_lst, TABLES tableaddr_lst, MEMS memaddr_lst, EXPORTS exportinst_lst}, {TYPES functype_lst, FUNCS functype_F_lst, GLOBALS globaltype_lst, TABLES tabletype_lst, MEMS memtype_lst, LOCALS [], LABELS [], RETURN ?()})
    -- (Functype_ok: `|-%:OK`(v_functype))*{v_functype <- functype_lst}
    -- if (|globaladdr_lst| = |globaltype_lst|)
    -- (Externaddr_ok: `%|-%:%`(s, GLOBAL_externaddr(v_globaladdr), GLOBAL_externtype(v_globaltype)))*{v_globaladdr <- globaladdr_lst, v_globaltype <- globaltype_lst}
    -- if (|funcaddr_lst| = |functype_F_lst|)
    -- (Externaddr_ok: `%|-%:%`(s, FUNC_externaddr(v_funcaddr), FUNC_externtype(functype_F)))*{v_funcaddr <- funcaddr_lst, functype_F <- functype_F_lst}
    -- if (|memaddr_lst| = |memtype_lst|)
    -- (Externaddr_ok: `%|-%:%`(s, MEM_externaddr(v_memaddr), MEM_externtype(v_memtype)))*{v_memaddr <- memaddr_lst, v_memtype <- memtype_lst}
    -- if (|tableaddr_lst| = |tabletype_lst|)
    -- (Externaddr_ok: `%|-%:%`(s, TABLE_externaddr(v_tableaddr), TABLE_externtype(v_tabletype)))*{v_tableaddr <- tableaddr_lst, v_tabletype <- tabletype_lst}
    -- (Exportinst_ok: `%|-%:OK`(s, v_exportinst))*{v_exportinst <- exportinst_lst}
    -- if $disjoint_(syntax name, v_exportinst.NAME_exportinst*{v_exportinst <- exportinst_lst})
    -- if (|GLOBAL_externaddr(v_globaladdr)*{v_globaladdr <- globaladdr_lst} ++ MEM_externaddr(v_memaddr)*{v_memaddr <- memaddr_lst} ++ TABLE_externaddr(v_tableaddr)*{v_tableaddr <- tableaddr_lst} ++ FUNC_externaddr(v_funcaddr)*{v_funcaddr <- funcaddr_lst}| > 0)
    -- (if (v_exportinst.ADDR_exportinst <- GLOBAL_externaddr(v_globaladdr)*{v_globaladdr <- globaladdr_lst} ++ MEM_externaddr(v_memaddr)*{v_memaddr <- memaddr_lst} ++ TABLE_externaddr(v_tableaddr)*{v_tableaddr <- tableaddr_lst} ++ FUNC_externaddr(v_funcaddr)*{v_funcaddr <- funcaddr_lst}))*{v_exportinst <- exportinst_lst}
    -- wf_store: `%`(s)
    -- wf_moduleinst: `%`({TYPES functype_lst, FUNCS funcaddr_lst, GLOBALS globaladdr_lst, TABLES tableaddr_lst, MEMS memaddr_lst, EXPORTS exportinst_lst})
    -- wf_context: `%`({TYPES functype_lst, FUNCS functype_F_lst, GLOBALS globaltype_lst, TABLES tabletype_lst, MEMS memtype_lst, LOCALS [], LABELS [], RETURN ?()})
    -- (wf_externtype: `%`(GLOBAL_externtype(v_globaltype)))*{v_globaltype <- globaltype_lst}
    -- (wf_externtype: `%`(FUNC_externtype(functype_F)))*{functype_F <- functype_F_lst}
    -- (wf_externtype: `%`(MEM_externtype(v_memtype)))*{v_memtype <- memtype_lst}
    -- (wf_externtype: `%`(TABLE_externtype(v_tabletype)))*{v_tabletype <- tabletype_lst}

;; ../specification/wasm-1.0/B-soundness.spectec:232.1-232.44
relation Frame_ok: `%|-%:%`(store, frame, context)
  ;; ../specification/wasm-1.0/B-soundness.spectec:236.1-239.27
  rule mk_Frame_ok{s : store, val_lst : val*, v_moduleinst : moduleinst, C : context, t_lst : valtype*}:
    `%|-%:%`(s, {LOCALS val_lst, MODULE v_moduleinst}, C +++ {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS t_lst, LABELS [], RETURN ?()})
    -- Moduleinst_ok: `%|-%:%`(s, v_moduleinst, C)
    -- if (|t_lst| = |val_lst|)
    -- (Val_ok: `|-%:%`(v_val, t))*{t <- t_lst, v_val <- val_lst}
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_frame: `%`({LOCALS val_lst, MODULE v_moduleinst})
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS t_lst, LABELS [], RETURN ?()})

;; ../specification/wasm-1.0/B-soundness.spectec:46.1-51.36
rec {

;; ../specification/wasm-1.0/B-soundness.spectec:46.1-47.36
relation Instr_ok2: `%;%|-%:%`(store, context, admininstr, functype)
  ;; ../specification/wasm-1.0/B-soundness.spectec:53.1-55.41
  rule plain{s : store, C : context, v_instr : instr, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%;%|-%:%`(s, C, $admininstr_instr(v_instr), mk_functype_functype(t_1_lst, t_2_lst))
    -- Instr_ok: `%|-%:%`(C, v_instr, mk_functype_functype(t_1_lst, t_2_lst))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(v_instr)

  ;; ../specification/wasm-1.0/B-soundness.spectec:57.1-61.67
  rule label{s : store, C : context, v_n : n, instr'_lst : instr*, admininstr_lst : admininstr*, t_opt : valtype?, t'_opt : valtype?}:
    `%;%|-%:%`(s, C, `LABEL_%{%}%`_admininstr(v_n, instr'_lst, admininstr_lst), mk_functype_functype([], lift(t_opt)))
    -- if (|lift(t'_opt)| = v_n)
    -- Instrs_ok2: `%;%|-%:%`(s, C, $admininstr_instr(instr')*{instr' <- instr'_lst}, mk_functype_functype(lift(t'_opt), lift(t_opt)))
    -- Instrs_ok2: `%;%|-%:%`(s, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t'_opt], RETURN ?()} +++ C, admininstr_lst, mk_functype_functype([], lift(t_opt)))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(v_n, instr'_lst, admininstr_lst))
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t'_opt], RETURN ?()})

  ;; ../specification/wasm-1.0/B-soundness.spectec:63.1-67.56
  rule frame{s : store, C : context, v_n : n, f : frame, admininstr_lst : admininstr*, t_opt : valtype?, C' : context}:
    `%;%|-%:%`(s, C, `FRAME_%{%}%`_admininstr(v_n, f, admininstr_lst), mk_functype_functype([], lift(t_opt)))
    -- if (|lift(t_opt)| = v_n)
    -- Frame_ok: `%|-%:%`(s, f, C')
    -- Expr_ok2: `%;%|-%:%`(s, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [], RETURN ?(t_opt)} +++ C', admininstr_lst, t_opt)
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_context: `%`(C')
    -- wf_admininstr: `%`(`FRAME_%{%}%`_admininstr(v_n, f, admininstr_lst))
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [], RETURN ?(t_opt)})

  ;; ../specification/wasm-1.0/B-soundness.spectec:69.1-71.60
  rule call_addr{s : store, C : context, v_funcaddr : funcaddr, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%;%|-%:%`(s, C, CALL_ADDR_admininstr(v_funcaddr), mk_functype_functype(t_1_lst, t_2_lst))
    -- Externaddr_ok: `%|-%:%`(s, FUNC_externaddr(v_funcaddr), FUNC_externtype(mk_functype_functype(t_1_lst, t_2_lst)))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_admininstr: `%`(CALL_ADDR_admininstr(v_funcaddr))
    -- wf_externtype: `%`(FUNC_externtype(mk_functype_functype(t_1_lst, t_2_lst)))

  ;; ../specification/wasm-1.0/B-soundness.spectec:73.1-74.30
  rule trap{s : store, C : context, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%;%|-%:%`(s, C, TRAP_admininstr, mk_functype_functype(t_1_lst, t_2_lst))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_admininstr: `%`(TRAP_admininstr)

;; ../specification/wasm-1.0/B-soundness.spectec:48.1-49.36
relation Instrs_ok2: `%;%|-%:%`(store, context, admininstr*, functype)
  ;; ../specification/wasm-1.0/B-soundness.spectec:77.1-78.27
  rule empty{s : store, C : context}:
    `%;%|-%:%`(s, C, [], mk_functype_functype([], []))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)

  ;; ../specification/wasm-1.0/B-soundness.spectec:80.1-82.50
  rule instr{s : store, C : context, v_admininstr : admininstr, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%;%|-%:%`(s, C, [v_admininstr], mk_functype_functype(t_1_lst, t_2_lst))
    -- Instr_ok2: `%;%|-%:%`(s, C, v_admininstr, mk_functype_functype(t_1_lst, t_2_lst))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_admininstr: `%`(v_admininstr)

  ;; ../specification/wasm-1.0/B-soundness.spectec:84.1-87.54
  rule seq{s : store, C : context, admininstr_1_lst : admininstr*, admininstr_2_lst : admininstr*, t_1_lst : valtype*, t_3_lst : valtype*, t_2_lst : valtype*}:
    `%;%|-%:%`(s, C, admininstr_1_lst ++ admininstr_2_lst, mk_functype_functype(t_1_lst, t_3_lst))
    -- Instrs_ok2: `%;%|-%:%`(s, C, admininstr_1_lst, mk_functype_functype(t_1_lst, t_2_lst))
    -- Instrs_ok2: `%;%|-%:%`(s, C, admininstr_2_lst, mk_functype_functype(t_2_lst, t_3_lst))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- (wf_admininstr: `%`(admininstr_1))*{admininstr_1 <- admininstr_1_lst}
    -- (wf_admininstr: `%`(admininstr_2))*{admininstr_2 <- admininstr_2_lst}

  ;; ../specification/wasm-1.0/B-soundness.spectec:89.1-91.52
  rule frame{s : store, C : context, admininstr_lst : admininstr*, t_lst : valtype*, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%;%|-%:%`(s, C, admininstr_lst, mk_functype_functype(t_lst ++ t_1_lst, t_lst ++ t_2_lst))
    -- Instrs_ok2: `%;%|-%:%`(s, C, admininstr_lst, mk_functype_functype(t_1_lst, t_2_lst))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- (wf_admininstr: `%`(v_admininstr))*{v_admininstr <- admininstr_lst}

;; ../specification/wasm-1.0/B-soundness.spectec:50.1-51.36
relation Expr_ok2: `%;%|-%:%`(store, context, adminexpr, resulttype)
  ;; ../specification/wasm-1.0/B-soundness.spectec:93.1-95.49
  rule mk_Expr_ok2{s : store, C : context, admininstr_lst : admininstr*, t_opt : valtype?}:
    `%;%|-%:%`(s, C, admininstr_lst, t_opt)
    -- Instrs_ok2: `%;%|-%:%`(s, C, admininstr_lst, mk_functype_functype([], lift(t_opt)))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- (wf_admininstr: `%`(v_admininstr))*{v_admininstr <- admininstr_lst}
}

;; ../specification/wasm-1.0/B-soundness.spectec:124.1-124.57
relation Globalinst_ok: `%|-%:%`(store, globalinst, globaltype)
  ;; ../specification/wasm-1.0/B-soundness.spectec:130.1-133.24
  rule mk_Globalinst_ok{s : store, v_mut : mut, t : valtype, v_val : val}:
    `%|-%:%`(s, {TYPE mk_globaltype_globaltype(v_mut, t), VALUE v_val}, mk_globaltype_globaltype(v_mut, t))
    -- Globaltype_ok: `|-%:OK`(mk_globaltype_globaltype(v_mut, t))
    -- Val_ok: `|-%:%`(v_val, t)
    -- wf_store: `%`(s)
    -- wf_globalinst: `%`({TYPE mk_globaltype_globaltype(v_mut, t), VALUE v_val})

;; ../specification/wasm-1.0/B-soundness.spectec:125.1-125.48
relation Meminst_ok: `%|-%:%`(store, meminst, memtype)
  ;; ../specification/wasm-1.0/B-soundness.spectec:135.1-138.37
  rule mk_Meminst_ok{s : store, v_n : n, m_opt : m?, b_lst : byte*}:
    `%|-%:%`(s, {TYPE mk_limits_memtype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), BYTES b_lst}, mk_limits_memtype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}))
    -- Memtype_ok: `|-%:OK`(mk_limits_memtype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}))
    -- if (|b_lst| = (v_n * (64 * $Ki)))
    -- wf_store: `%`(s)
    -- wf_meminst: `%`({TYPE mk_limits_memtype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), BYTES b_lst})
    -- wf_limits: `%`(mk_limits_limits(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}))

;; ../specification/wasm-1.0/B-soundness.spectec:126.1-126.54
relation Tableinst_ok: `%|-%:%`(store, tableinst, tabletype)
  ;; ../specification/wasm-1.0/B-soundness.spectec:140.1-144.21
  rule mk_Tableinst_ok{s : store, v_n : n, m_opt : m?, fa_opt_lst : funcaddr?*, ft_opt_lst : functype?*}:
    `%|-%:%`(s, {TYPE mk_limits_tabletype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), REFS fa_opt_lst}, mk_limits_tabletype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}))
    -- Tabletype_ok: `|-%:OK`(mk_limits_tabletype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}))
    -- if (|fa_opt_lst| = |ft_opt_lst|)
    -- (if ((fa_opt = ?()) <=> (ft_opt = ?())))*{fa_opt <- fa_opt_lst, ft_opt <- ft_opt_lst}
    -- (Externaddr_ok: `%|-%:%`(s, FUNC_externaddr(fa), FUNC_externtype(ft)))?{fa <- fa_opt, ft <- ft_opt}*{fa_opt <- fa_opt_lst, ft_opt <- ft_opt_lst}
    -- if (|fa_opt_lst| = v_n)
    -- wf_store: `%`(s)
    -- wf_tableinst: `%`({TYPE mk_limits_tabletype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), REFS fa_opt_lst})
    -- wf_limits: `%`(mk_limits_limits(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}))
    -- (wf_externtype: `%`(FUNC_externtype(ft)))?{ft <- ft_opt}*{ft_opt <- ft_opt_lst}

;; ../specification/wasm-1.0/B-soundness.spectec:127.1-127.51
relation Funcinst_ok: `%|-%:%`(store, funcinst, functype)
  ;; ../specification/wasm-1.0/B-soundness.spectec:146.1-150.29
  rule mk_Funcinst_ok{s : store, ft : functype, v_moduleinst : moduleinst, v_func : func, C : context}:
    `%|-%:%`(s, {TYPE ft, MODULE v_moduleinst, CODE v_func}, ft)
    -- Functype_ok: `|-%:OK`(ft)
    -- Moduleinst_ok: `%|-%:%`(s, v_moduleinst, C)
    -- Func_ok: `%|-%:%`(C, v_func, ft)
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_funcinst: `%`({TYPE ft, MODULE v_moduleinst, CODE v_func})

;; ../specification/wasm-1.0/B-soundness.spectec:187.1-187.33
relation Store_ok: `|-%:OK`(store)
  ;; ../specification/wasm-1.0/B-soundness.spectec:189.1-196.85
  rule mk_Store_ok{s : store, globalinst_lst : globalinst*, globaltype_lst : globaltype*, meminst_lst : meminst*, memtype_lst : memtype*, tableinst_lst : tableinst*, tabletype_lst : tabletype*, funcinst_lst : funcinst*, functype_lst : functype*}:
    `|-%:OK`(s)
    -- if (|globalinst_lst| = |globaltype_lst|)
    -- (Globalinst_ok: `%|-%:%`(s, v_globalinst, v_globaltype))*{v_globalinst <- globalinst_lst, v_globaltype <- globaltype_lst}
    -- if (|meminst_lst| = |memtype_lst|)
    -- (Meminst_ok: `%|-%:%`(s, v_meminst, v_memtype))*{v_meminst <- meminst_lst, v_memtype <- memtype_lst}
    -- if (|tableinst_lst| = |tabletype_lst|)
    -- (Tableinst_ok: `%|-%:%`(s, v_tableinst, v_tabletype))*{v_tableinst <- tableinst_lst, v_tabletype <- tabletype_lst}
    -- if (|funcinst_lst| = |functype_lst|)
    -- (Funcinst_ok: `%|-%:%`(s, v_funcinst, v_functype))*{v_funcinst <- funcinst_lst, v_functype <- functype_lst}
    -- if (s = {FUNCS funcinst_lst, GLOBALS globalinst_lst, TABLES tableinst_lst, MEMS meminst_lst})
    -- wf_store: `%`(s)
    -- (wf_limits: `%`(v_memtype))*{v_memtype <- memtype_lst}
    -- (wf_limits: `%`(v_tabletype))*{v_tabletype <- tabletype_lst}
    -- wf_store: `%`({FUNCS funcinst_lst, GLOBALS globalinst_lst, TABLES tableinst_lst, MEMS meminst_lst})

;; ../specification/wasm-1.0/B-soundness.spectec:200.1-200.54
relation Extend_globalinst: `%<=%`(globalinst, globalinst)
  ;; ../specification/wasm-1.0/B-soundness.spectec:206.1-208.32
  rule mk_Extend_globalinst{v_mut : mut, t : valtype, v_val : val, val' : val}:
    `%<=%`({TYPE mk_globaltype_globaltype(v_mut, t), VALUE v_val}, {TYPE mk_globaltype_globaltype(v_mut, t), VALUE val'})
    -- if ((v_mut = ?(MUT_r_MUT)) \/ (v_val = val'))
    -- wf_globalinst: `%`({TYPE mk_globaltype_globaltype(v_mut, t), VALUE v_val})
    -- wf_globalinst: `%`({TYPE mk_globaltype_globaltype(v_mut, t), VALUE val'})

;; ../specification/wasm-1.0/B-soundness.spectec:201.1-201.45
relation Extend_meminst: `%<=%`(meminst, meminst)
  ;; ../specification/wasm-1.0/B-soundness.spectec:210.1-213.22
  rule mk_Extend_meminst{v_n : n, m_opt : m?, b_lst : byte*, n' : n, b'_lst : byte*}:
    `%<=%`({TYPE mk_limits_memtype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), BYTES b_lst}, {TYPE mk_limits_memtype(mk_uN_u32(n'), mk_uN_u32(v_m)?{v_m <- m_opt}), BYTES b'_lst})
    -- if (v_n <= n')
    -- if (|b_lst| <= |b'_lst|)
    -- wf_meminst: `%`({TYPE mk_limits_memtype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), BYTES b_lst})
    -- wf_meminst: `%`({TYPE mk_limits_memtype(mk_uN_u32(n'), mk_uN_u32(v_m)?{v_m <- m_opt}), BYTES b'_lst})

;; ../specification/wasm-1.0/B-soundness.spectec:202.1-202.51
relation Extend_tableinst: `%<=%`(tableinst, tableinst)
  ;; ../specification/wasm-1.0/B-soundness.spectec:215.1-218.26
  rule mk_Extend_tableinst{v_n : n, m_opt : m?, ref_lst : funcaddr*, n' : n, ref'_lst : funcaddr*}:
    `%<=%`({TYPE mk_limits_tabletype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), REFS ?(ref)*{ref <- ref_lst}}, {TYPE mk_limits_tabletype(mk_uN_u32(n'), mk_uN_u32(v_m)?{v_m <- m_opt}), REFS ?(ref')*{ref' <- ref'_lst}})
    -- if (v_n <= n')
    -- if (|ref_lst| <= |ref'_lst|)
    -- wf_tableinst: `%`({TYPE mk_limits_tabletype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), REFS ?(ref)*{ref <- ref_lst}})
    -- wf_tableinst: `%`({TYPE mk_limits_tabletype(mk_uN_u32(n'), mk_uN_u32(v_m)?{v_m <- m_opt}), REFS ?(ref')*{ref' <- ref'_lst}})

;; ../specification/wasm-1.0/B-soundness.spectec:203.1-203.48
relation Extend_funcinst: `%<=%`(funcinst, funcinst)
  ;; ../specification/wasm-1.0/B-soundness.spectec:220.1-221.66
  rule mk_Extend_funcinst{ft : functype, mm : moduleinst, fc : func}:
    `%<=%`({TYPE ft, MODULE mm, CODE fc}, {TYPE ft, MODULE mm, CODE fc})
    -- wf_funcinst: `%`({TYPE ft, MODULE mm, CODE fc})

;; ../specification/wasm-1.0/B-soundness.spectec:204.1-204.39
relation Extend_store: `%<=%`(store, store)
  ;; ../specification/wasm-1.0/B-soundness.spectec:223.1-228.66
  rule mk_Extend_store{s : store, s' : store}:
    `%<=%`(s, s')
    -- (if (a < |s.GLOBALS_store|))^(a<|s.GLOBALS_store|){}
    -- (if (a < |s'.GLOBALS_store|))^(a<|s.GLOBALS_store|){}
    -- (Extend_globalinst: `%<=%`(s.GLOBALS_store[a], s'.GLOBALS_store[a]))^(a<|s.GLOBALS_store|){}
    -- (if (a < |s.MEMS_store|))^(a<|s.MEMS_store|){}
    -- (if (a < |s'.MEMS_store|))^(a<|s.MEMS_store|){}
    -- (Extend_meminst: `%<=%`(s.MEMS_store[a], s'.MEMS_store[a]))^(a<|s.MEMS_store|){}
    -- (if (a < |s.TABLES_store|))^(a<|s.TABLES_store|){}
    -- (if (a < |s'.TABLES_store|))^(a<|s.TABLES_store|){}
    -- (Extend_tableinst: `%<=%`(s.TABLES_store[a], s'.TABLES_store[a]))^(a<|s.TABLES_store|){}
    -- (if (a < |s.FUNCS_store|))^(a<|s.FUNCS_store|){}
    -- (if (a < |s'.FUNCS_store|))^(a<|s.FUNCS_store|){}
    -- (Extend_funcinst: `%<=%`(s.FUNCS_store[a], s'.FUNCS_store[a]))^(a<|s.FUNCS_store|){}
    -- wf_store: `%`(s)
    -- wf_store: `%`(s')

;; ../specification/wasm-1.0/B-soundness.spectec:233.1-233.38
relation State_ok: `|-%:%`(state, context)
  ;; ../specification/wasm-1.0/B-soundness.spectec:241.1-244.26
  rule mk_State_ok{s : store, f : frame, C : context}:
    `|-%:%`(mk_state_state(s, f), C)
    -- Store_ok: `|-%:OK`(s)
    -- Frame_ok: `%|-%:%`(s, f, C)
    -- wf_context: `%`(C)
    -- wf_state: `%`(mk_state_state(s, f))

;; ../specification/wasm-1.0/B-soundness.spectec:234.1-234.43
relation Config_ok: `|-%:%`(config, resulttype)
  ;; ../specification/wasm-1.0/B-soundness.spectec:246.1-249.40
  rule mk_Config_ok{s : store, f : frame, admininstr_lst : admininstr*, t_opt : valtype?, C : context}:
    `|-%:%`(mk_config_config(mk_state_state(s, f), admininstr_lst), t_opt)
    -- State_ok: `|-%:%`(mk_state_state(s, f), C)
    -- Expr_ok2: `%;%|-%:%`(s, C, admininstr_lst, t_opt)
    -- wf_context: `%`(C)
    -- wf_config: `%`(mk_config_config(mk_state_state(s, f), admininstr_lst))
    -- wf_state: `%`(mk_state_state(s, f))

;; ../specification/wasm-1.0/A-binary.spectec:18.1-18.41
grammar Bbyte : byte
  ;; ../specification/wasm-1.0/A-binary.spectec:18.24-18.41
  prod{`<implicit_prod_result>` : nat} `<implicit_prod_result>`:(0x00 | ... | 0xFF) => mk_byte_byte(`<implicit_prod_result>`)

;; ../specification/wasm-1.0/A-binary.spectec:20.1-22.82
rec {

;; ../specification/wasm-1.0/A-binary.spectec:20.1-22.82
grammar BuN(v_N : N) : uN
  ;; ../specification/wasm-1.0/A-binary.spectec:21.5-21.83
  prod{v_n : n} mk_byte_byte(v_n):Bbyte => mk_uN_uN(v_n)
    -- if ((v_n < (2 ^ 7)) /\ (v_n < (2 ^ v_N)))
  ;; ../specification/wasm-1.0/A-binary.spectec:22.5-22.82
  prod{v_m : m, v_n : n} {{mk_byte_byte(v_n):Bbyte} {mk_uN_uN(v_m):BuN((((v_N : nat <:> int) - (7 : nat <:> int)) : int <:> nat))}} => mk_uN_uN((((2 ^ 7) * v_m) + (((v_n : nat <:> int) - ((2 ^ 7) : nat <:> int)) : int <:> nat)))
    -- if ((v_n >= (2 ^ 7)) /\ (v_N > 7))
}

;; ../specification/wasm-1.0/A-binary.spectec:37.1-37.29
grammar Bu32 : u32
  ;; ../specification/wasm-1.0/A-binary.spectec:37.22-37.29
  prod{`<implicit_prod_result>` : uN} `<implicit_prod_result>`:BuN(32) => `<implicit_prod_result>`

;; ../specification/wasm-1.0/A-binary.spectec:7.1-8.29
grammar Blist(syntax el, grammar BX : el) : el*
  ;; ../specification/wasm-1.0/A-binary.spectec:8.5-8.29
  prod{v_n : n, el_lst : el*} {{mk_uN_u32(v_n):Bu32} {el:BX^v_n{el <- el_lst}}} => el_lst

;; ../specification/wasm-1.0/A-binary.spectec:24.1-27.82
rec {

;; ../specification/wasm-1.0/A-binary.spectec:24.1-27.82
grammar BsN(v_N : N) : sN
  ;; ../specification/wasm-1.0/A-binary.spectec:25.5-25.87
  prod{v_n : n} mk_byte_byte(v_n):Bbyte => mk_sN_sN((v_n : nat <:> int))
    -- if ((v_n < (2 ^ 6)) /\ (v_n < (2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat))))
  ;; ../specification/wasm-1.0/A-binary.spectec:26.5-26.101
  prod{v_n : n} mk_byte_byte(v_n):Bbyte => mk_sN_sN(((v_n : nat <:> int) - ((2 ^ 7) : nat <:> int)))
    -- if ((((2 ^ 6) <= v_n) /\ (v_n < (2 ^ 7))) /\ ((v_n : nat <:> int) >= (((2 ^ 7) : nat <:> int) - ((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int))))
  ;; ../specification/wasm-1.0/A-binary.spectec:27.5-27.82
  prod{i : sN, v_n : n} {{mk_byte_byte(v_n):Bbyte} {i:BsN((((v_N : nat <:> int) - (7 : nat <:> int)) : int <:> nat))}} => mk_sN_sN(((((2 ^ 7) * ($proj_sN_0(i).0 : int <:> nat)) + (((v_n : nat <:> int) - ((2 ^ 7) : nat <:> int)) : int <:> nat)) : nat <:> int))
    -- if ((v_n >= (2 ^ 7)) /\ (v_N > 7))
}

;; ../specification/wasm-1.0/A-binary.spectec:29.1-30.50
grammar BiN(v_N : N) : iN
  ;; ../specification/wasm-1.0/A-binary.spectec:30.5-30.50
  prod{i : sN, var_0 : nat} i:BsN(v_N) => mk_uN_iN(var_0)
    -- fun_inv_signed_: `%%%`(v_N, $proj_sN_0(i).0, var_0)

;; ../specification/wasm-1.0/A-binary.spectec:33.1-34.43
grammar BfN(v_N : N) : fN
  ;; ../specification/wasm-1.0/A-binary.spectec:34.5-34.43
  prod{b_lst : byte*} b_lst:Bbyte^(((v_N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat){} => $inv_fbytes_(v_N, b_lst)

;; ../specification/wasm-1.0/A-binary.spectec:38.1-38.29
grammar Bu64 : u64
  ;; ../specification/wasm-1.0/A-binary.spectec:38.22-38.29
  prod{`<implicit_prod_result>` : uN} `<implicit_prod_result>`:BuN(64) => `<implicit_prod_result>`

;; ../specification/wasm-1.0/A-binary.spectec:40.1-40.29
grammar Bi32 : i32
  ;; ../specification/wasm-1.0/A-binary.spectec:40.22-40.29
  prod{`<implicit_prod_result>` : iN} `<implicit_prod_result>`:BiN(32) => `<implicit_prod_result>`

;; ../specification/wasm-1.0/A-binary.spectec:41.1-41.29
grammar Bi64 : i64
  ;; ../specification/wasm-1.0/A-binary.spectec:41.22-41.29
  prod{`<implicit_prod_result>` : iN} `<implicit_prod_result>`:BiN(64) => `<implicit_prod_result>`

;; ../specification/wasm-1.0/A-binary.spectec:43.1-43.29
grammar Bf32 : f32
  ;; ../specification/wasm-1.0/A-binary.spectec:43.22-43.29
  prod{`<implicit_prod_result>` : fN} `<implicit_prod_result>`:BfN(32) => `<implicit_prod_result>`

;; ../specification/wasm-1.0/A-binary.spectec:44.1-44.29
grammar Bf64 : f64
  ;; ../specification/wasm-1.0/A-binary.spectec:44.22-44.29
  prod{`<implicit_prod_result>` : fN} `<implicit_prod_result>`:BfN(64) => `<implicit_prod_result>`

;; ../specification/wasm-1.0/A-binary.spectec:58.1-59.52
grammar Bname : name
  ;; ../specification/wasm-1.0/A-binary.spectec:59.5-59.52
  prod{v_name : name, b_lst : byte*, var_0 : byte*} b_lst:Blist(syntax byte, grammar Bbyte) => v_name
    -- fun_utf8: `%%`($proj_name_0(v_name).0, var_0)
    -- if (var_0 = b_lst)

;; ../specification/wasm-1.0/A-binary.spectec:64.1-64.41
grammar Btypeidx : typeidx
  ;; ../specification/wasm-1.0/A-binary.spectec:64.30-64.41
  prod{x : idx} x:Bu32 => x

;; ../specification/wasm-1.0/A-binary.spectec:65.1-65.41
grammar Bfuncidx : funcidx
  ;; ../specification/wasm-1.0/A-binary.spectec:65.30-65.41
  prod{x : idx} x:Bu32 => x

;; ../specification/wasm-1.0/A-binary.spectec:66.1-66.45
grammar Bglobalidx : globalidx
  ;; ../specification/wasm-1.0/A-binary.spectec:66.34-66.45
  prod{x : idx} x:Bu32 => x

;; ../specification/wasm-1.0/A-binary.spectec:67.1-67.43
grammar Btableidx : tableidx
  ;; ../specification/wasm-1.0/A-binary.spectec:67.32-67.43
  prod{x : idx} x:Bu32 => x

;; ../specification/wasm-1.0/A-binary.spectec:68.1-68.39
grammar Bmemidx : memidx
  ;; ../specification/wasm-1.0/A-binary.spectec:68.28-68.39
  prod{x : idx} x:Bu32 => x

;; ../specification/wasm-1.0/A-binary.spectec:69.1-69.43
grammar Blocalidx : localidx
  ;; ../specification/wasm-1.0/A-binary.spectec:69.32-69.43
  prod{x : idx} x:Bu32 => x

;; ../specification/wasm-1.0/A-binary.spectec:70.1-70.43
grammar Blabelidx : labelidx
  ;; ../specification/wasm-1.0/A-binary.spectec:70.32-70.43
  prod{x : idx} x:Bu32 => x

;; ../specification/wasm-1.0/A-binary.spectec:72.1-76.34
grammar Bexternidx : externidx
  ;; ../specification/wasm-1.0/A-binary.spectec:73.5-73.30
  prod{x : idx} {{0x00} {x:Bfuncidx}} => FUNC_externidx(x)
  ;; ../specification/wasm-1.0/A-binary.spectec:74.5-74.32
  prod{x : idx} {{0x01} {x:Btableidx}} => TABLE_externidx(x)
  ;; ../specification/wasm-1.0/A-binary.spectec:75.5-75.28
  prod{x : idx} {{0x02} {x:Bmemidx}} => MEM_externidx(x)
  ;; ../specification/wasm-1.0/A-binary.spectec:76.5-76.34
  prod{x : idx} {{0x03} {x:Bglobalidx}} => GLOBAL_externidx(x)

;; ../specification/wasm-1.0/A-binary.spectec:85.1-89.16
grammar Bvaltype : valtype
  ;; ../specification/wasm-1.0/A-binary.spectec:86.5-86.16
  prod 0x7F => I32_valtype
  ;; ../specification/wasm-1.0/A-binary.spectec:87.5-87.16
  prod 0x7E => I64_valtype
  ;; ../specification/wasm-1.0/A-binary.spectec:88.5-88.16
  prod 0x7D => F32_valtype
  ;; ../specification/wasm-1.0/A-binary.spectec:89.5-89.16
  prod 0x7C => F64_valtype

;; ../specification/wasm-1.0/A-binary.spectec:92.1-93.29
grammar Bresulttype : valtype*
  ;; ../specification/wasm-1.0/A-binary.spectec:93.5-93.29
  prod{t_lst : valtype*} t_lst:Blist(syntax valtype, grammar Bvaltype) => t_lst

;; ../specification/wasm-1.0/A-binary.spectec:98.1-99.59
grammar Bfunctype : functype
  ;; ../specification/wasm-1.0/A-binary.spectec:99.5-99.59
  prod{t_1_lst : valtype*, t_2_lst : valtype*} {{0x60} {t_1_lst:Bresulttype} {t_2_lst:Bresulttype}} => mk_functype_functype(t_1_lst, t_2_lst)

;; ../specification/wasm-1.0/A-binary.spectec:104.1-106.16
grammar Bmut : mut
  ;; ../specification/wasm-1.0/A-binary.spectec:105.5-105.16
  prod 0x00 => ?()
  ;; ../specification/wasm-1.0/A-binary.spectec:106.5-106.16
  prod 0x01 => ?(MUT_r_MUT)

;; ../specification/wasm-1.0/A-binary.spectec:108.1-110.36
grammar Blimits : limits
  ;; ../specification/wasm-1.0/A-binary.spectec:109.5-109.31
  prod{v_n : n} {{0x00} {mk_uN_u32(v_n):Bu32}} => mk_limits_limits(mk_uN_u32(v_n), ?())
  ;; ../specification/wasm-1.0/A-binary.spectec:110.5-110.36
  prod{v_n : n, v_m : m} {{0x01} {mk_uN_u32(v_n):Bu32} {mk_uN_u32(v_m):Bu32}} => mk_limits_limits(mk_uN_u32(v_n), ?(mk_uN_u32(v_m)))

;; ../specification/wasm-1.0/A-binary.spectec:112.1-113.33
grammar Bglobaltype : globaltype
  ;; ../specification/wasm-1.0/A-binary.spectec:113.5-113.33
  prod{v_mut : mut, t : valtype} {{t:Bvaltype} {v_mut:Bmut}} => mk_globaltype_globaltype(v_mut, t)

;; ../specification/wasm-1.0/A-binary.spectec:115.1-116.28
grammar Btabletype : tabletype
  ;; ../specification/wasm-1.0/A-binary.spectec:116.5-116.28
  prod{lim : limits} {{0x70} {lim:Blimits}} => lim

;; ../specification/wasm-1.0/A-binary.spectec:118.1-119.23
grammar Bmemtype : memtype
  ;; ../specification/wasm-1.0/A-binary.spectec:119.5-119.23
  prod{lim : limits} lim:Blimits => lim

;; ../specification/wasm-1.0/A-binary.spectec:122.1-126.37
grammar Bexterntype : externtype
  ;; ../specification/wasm-1.0/A-binary.spectec:123.5-123.33
  prod{ft : functype} {{0x00} {ft:Bfunctype}} => FUNC_externtype(ft)
  ;; ../specification/wasm-1.0/A-binary.spectec:124.5-124.35
  prod{tt : tabletype} {{0x01} {tt:Btabletype}} => TABLE_externtype(tt)
  ;; ../specification/wasm-1.0/A-binary.spectec:125.5-125.31
  prod{mt : memtype} {{0x02} {mt:Bmemtype}} => MEM_externtype(mt)
  ;; ../specification/wasm-1.0/A-binary.spectec:126.5-126.37
  prod{gt : globaltype} {{0x03} {gt:Bglobaltype}} => GLOBAL_externtype(gt)

;; ../specification/wasm-1.0/A-binary.spectec:135.1-137.20
grammar Bblocktype : blocktype
  ;; ../specification/wasm-1.0/A-binary.spectec:136.5-136.16
  prod 0x40 => ?()
  ;; ../specification/wasm-1.0/A-binary.spectec:137.5-137.20
  prod{t : valtype} t:Bvaltype => ?(t)

;; ../specification/wasm-1.0/A-binary.spectec:179.1-180.41
grammar Bmemarg : memarg
  ;; ../specification/wasm-1.0/A-binary.spectec:180.5-180.41
  prod{v_n : n, v_m : m} {{mk_uN_u32(v_n):Bu32} {mk_uN_u32(v_m):Bu32}} => {ALIGN mk_uN_u32(v_n), OFFSET mk_uN_u32(v_m)}

;; ../specification/wasm-1.0/A-binary.spectec:361.1-386.38
rec {

;; ../specification/wasm-1.0/A-binary.spectec:361.1-386.38
grammar Binstr : instr
  ;; ../specification/wasm-1.0/A-binary.spectec:143.5-143.24
  prod 0x00 => UNREACHABLE_instr
  ;; ../specification/wasm-1.0/A-binary.spectec:144.5-144.16
  prod 0x01 => NOP_instr
  ;; ../specification/wasm-1.0/A-binary.spectec:145.5-145.57
  prod{bt : blocktype, in_lst : instr*} {{0x02} {bt:Bblocktype} {in:Binstr*{in <- in_lst}} {0x0B}} => BLOCK_instr(bt, in_lst)
  ;; ../specification/wasm-1.0/A-binary.spectec:146.5-146.56
  prod{bt : blocktype, in_lst : instr*} {{0x03} {bt:Bblocktype} {in:Binstr*{in <- in_lst}} {0x0B}} => LOOP_instr(bt, in_lst)
  ;; ../specification/wasm-1.0/A-binary.spectec:147.5-147.63
  prod{bt : blocktype, in_lst : instr*} {{0x04} {bt:Bblocktype} {in:Binstr*{in <- in_lst}} {0x0B}} => `IF%%ELSE%`_instr(bt, in_lst, [])
  ;; ../specification/wasm-1.0/A-binary.spectec:148.5-148.89
  prod{bt : blocktype, in_1_lst : instr*, in_2_lst : instr*} {{0x04} {bt:Bblocktype} {in_1:Binstr*{in_1 <- in_1_lst}} {0x05} {in_2:Binstr*{in_2 <- in_2_lst}} {0x0B}} => `IF%%ELSE%`_instr(bt, in_1_lst, in_2_lst)
  ;; ../specification/wasm-1.0/A-binary.spectec:149.5-149.29
  prod{l : labelidx} {{0x0C} {l:Blabelidx}} => BR_instr(l)
  ;; ../specification/wasm-1.0/A-binary.spectec:150.5-150.32
  prod{l : labelidx} {{0x0D} {l:Blabelidx}} => BR_IF_instr(l)
  ;; ../specification/wasm-1.0/A-binary.spectec:151.5-151.62
  prod{l_lst : labelidx*, l_N : labelidx} {{0x0E} {l_lst:Blist(syntax labelidx, grammar Blabelidx)} {l_N:Blabelidx}} => BR_TABLE_instr(l_lst, l_N)
  ;; ../specification/wasm-1.0/A-binary.spectec:152.5-152.19
  prod 0x0F => RETURN_instr
  ;; ../specification/wasm-1.0/A-binary.spectec:153.5-153.30
  prod{x : idx} {{0x10} {x:Bfuncidx}} => CALL_instr(x)
  ;; ../specification/wasm-1.0/A-binary.spectec:154.5-154.44
  prod{x : idx} {{0x11} {x:Btypeidx} {0x00}} => CALL_INDIRECT_instr(x)
  ;; ../specification/wasm-1.0/A-binary.spectec:161.5-161.17
  prod 0x1A => DROP_instr
  ;; ../specification/wasm-1.0/A-binary.spectec:162.5-162.19
  prod 0x1B => SELECT_instr
  ;; ../specification/wasm-1.0/A-binary.spectec:169.5-169.36
  prod{x : idx} {{0x20} {x:Blocalidx}} => LOCAL_GET_instr(x)
  ;; ../specification/wasm-1.0/A-binary.spectec:170.5-170.36
  prod{x : idx} {{0x21} {x:Blocalidx}} => LOCAL_SET_instr(x)
  ;; ../specification/wasm-1.0/A-binary.spectec:171.5-171.36
  prod{x : idx} {{0x22} {x:Blocalidx}} => LOCAL_TEE_instr(x)
  ;; ../specification/wasm-1.0/A-binary.spectec:172.5-172.38
  prod{x : idx} {{0x23} {x:Bglobalidx}} => GLOBAL_GET_instr(x)
  ;; ../specification/wasm-1.0/A-binary.spectec:173.5-173.38
  prod{x : idx} {{0x24} {x:Bglobalidx}} => GLOBAL_SET_instr(x)
  ;; ../specification/wasm-1.0/A-binary.spectec:183.5-183.35
  prod{ao : memarg} {{0x28} {ao:Bmemarg}} => LOAD_instr(I32_valtype, ?(), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:184.5-184.35
  prod{ao : memarg} {{0x29} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:185.5-185.35
  prod{ao : memarg} {{0x2A} {ao:Bmemarg}} => LOAD_instr(F32_valtype, ?(), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:186.5-186.35
  prod{ao : memarg} {{0x2B} {ao:Bmemarg}} => LOAD_instr(F64_valtype, ?(), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:187.5-187.43
  prod{ao : memarg} {{0x2C} {ao:Bmemarg}} => LOAD_instr(I32_valtype, ?(mk_loadop__0_loadop_(I32_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(8), S_sx))), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:188.5-188.43
  prod{ao : memarg} {{0x2D} {ao:Bmemarg}} => LOAD_instr(I32_valtype, ?(mk_loadop__0_loadop_(I32_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(8), U_sx))), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:189.5-189.44
  prod{ao : memarg} {{0x2E} {ao:Bmemarg}} => LOAD_instr(I32_valtype, ?(mk_loadop__0_loadop_(I32_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(16), S_sx))), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:190.5-190.44
  prod{ao : memarg} {{0x2F} {ao:Bmemarg}} => LOAD_instr(I32_valtype, ?(mk_loadop__0_loadop_(I32_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(16), U_sx))), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:191.5-191.43
  prod{ao : memarg} {{0x30} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(8), S_sx))), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:192.5-192.43
  prod{ao : memarg} {{0x31} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(8), U_sx))), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:193.5-193.44
  prod{ao : memarg} {{0x32} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(16), S_sx))), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:194.5-194.44
  prod{ao : memarg} {{0x33} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(16), U_sx))), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:195.5-195.44
  prod{ao : memarg} {{0x34} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(32), S_sx))), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:196.5-196.44
  prod{ao : memarg} {{0x35} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(32), U_sx))), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:197.5-197.36
  prod{ao : memarg} {{0x36} {ao:Bmemarg}} => STORE_instr(I32_valtype, ?(), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:198.5-198.36
  prod{ao : memarg} {{0x37} {ao:Bmemarg}} => STORE_instr(I64_valtype, ?(), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:199.5-199.36
  prod{ao : memarg} {{0x38} {ao:Bmemarg}} => STORE_instr(F32_valtype, ?(), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:200.5-200.36
  prod{ao : memarg} {{0x39} {ao:Bmemarg}} => STORE_instr(F64_valtype, ?(), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:201.5-201.38
  prod{ao : memarg} {{0x3A} {ao:Bmemarg}} => STORE_instr(I32_valtype, ?(mk_sz_sz(8)), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:202.5-202.39
  prod{ao : memarg} {{0x3B} {ao:Bmemarg}} => STORE_instr(I32_valtype, ?(mk_sz_sz(16)), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:203.5-203.38
  prod{ao : memarg} {{0x3C} {ao:Bmemarg}} => STORE_instr(I64_valtype, ?(mk_sz_sz(8)), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:204.5-204.39
  prod{ao : memarg} {{0x3D} {ao:Bmemarg}} => STORE_instr(I64_valtype, ?(mk_sz_sz(16)), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:205.5-205.39
  prod{ao : memarg} {{0x3E} {ao:Bmemarg}} => STORE_instr(I64_valtype, ?(mk_sz_sz(32)), ao)
  ;; ../specification/wasm-1.0/A-binary.spectec:206.5-206.29
  prod {{0x3F} {0x00}} => MEMORY_SIZE_instr
  ;; ../specification/wasm-1.0/A-binary.spectec:207.5-207.29
  prod {{0x40} {0x00}} => MEMORY_GROW_instr
  ;; ../specification/wasm-1.0/A-binary.spectec:215.5-215.31
  prod{i : i32} {{0x41} {i:Bi32}} => CONST_instr(I32_valtype, mk_val__0_val_(I32_Inn, i))
  ;; ../specification/wasm-1.0/A-binary.spectec:216.5-216.31
  prod{i : i64} {{0x42} {i:Bi64}} => CONST_instr(I64_valtype, mk_val__0_val_(I64_Inn, i))
  ;; ../specification/wasm-1.0/A-binary.spectec:217.5-217.31
  prod{p : f32} {{0x43} {p:Bf32}} => CONST_instr(F32_valtype, mk_val__1_val_(F32_Fnn, p))
  ;; ../specification/wasm-1.0/A-binary.spectec:218.5-218.31
  prod{p : f64} {{0x44} {p:Bf64}} => CONST_instr(F64_valtype, mk_val__1_val_(F64_Fnn, p))
  ;; ../specification/wasm-1.0/A-binary.spectec:222.5-222.27
  prod 0x45 => TESTOP_instr(I32_valtype, mk_testop__0_testop_(I32_Inn, EQZ_testop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:226.5-226.25
  prod 0x46 => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, EQ_relop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:227.5-227.25
  prod 0x47 => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, NE_relop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:228.5-228.29
  prod 0x48 => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, LT_relop_Inn(S_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:229.5-229.29
  prod 0x49 => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, LT_relop_Inn(U_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:230.5-230.29
  prod 0x4A => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, GT_relop_Inn(S_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:231.5-231.29
  prod 0x4B => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, GT_relop_Inn(U_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:232.5-232.29
  prod 0x4C => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, LE_relop_Inn(S_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:233.5-233.29
  prod 0x4D => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, LE_relop_Inn(U_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:234.5-234.29
  prod 0x4E => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, GE_relop_Inn(S_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:235.5-235.29
  prod 0x4F => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, GE_relop_Inn(U_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:239.5-239.27
  prod 0x50 => TESTOP_instr(I64_valtype, mk_testop__0_testop_(I64_Inn, EQZ_testop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:243.5-243.25
  prod 0x51 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, EQ_relop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:244.5-244.25
  prod 0x52 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, NE_relop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:245.5-245.29
  prod 0x53 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, LT_relop_Inn(S_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:246.5-246.29
  prod 0x54 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, LT_relop_Inn(U_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:247.5-247.29
  prod 0x55 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, GT_relop_Inn(S_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:248.5-248.29
  prod 0x56 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, GT_relop_Inn(U_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:249.5-249.29
  prod 0x57 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, LE_relop_Inn(S_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:250.5-250.29
  prod 0x58 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, LE_relop_Inn(U_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:251.5-251.29
  prod 0x59 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, GE_relop_Inn(S_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:252.5-252.29
  prod 0x5A => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, GE_relop_Inn(U_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:256.5-256.25
  prod 0x5B => RELOP_instr(F32_valtype, mk_relop__1_relop_(F32_Fnn, EQ_relop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:257.5-257.25
  prod 0x5C => RELOP_instr(F32_valtype, mk_relop__1_relop_(F32_Fnn, NE_relop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:258.5-258.25
  prod 0x5D => RELOP_instr(F32_valtype, mk_relop__1_relop_(F32_Fnn, LT_relop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:259.5-259.25
  prod 0x5E => RELOP_instr(F32_valtype, mk_relop__1_relop_(F32_Fnn, GT_relop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:260.5-260.25
  prod 0x5F => RELOP_instr(F32_valtype, mk_relop__1_relop_(F32_Fnn, LE_relop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:261.5-261.25
  prod 0x60 => RELOP_instr(F32_valtype, mk_relop__1_relop_(F32_Fnn, GE_relop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:265.5-265.25
  prod 0x61 => RELOP_instr(F64_valtype, mk_relop__1_relop_(F64_Fnn, EQ_relop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:266.5-266.25
  prod 0x62 => RELOP_instr(F64_valtype, mk_relop__1_relop_(F64_Fnn, NE_relop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:267.5-267.25
  prod 0x63 => RELOP_instr(F64_valtype, mk_relop__1_relop_(F64_Fnn, LT_relop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:268.5-268.25
  prod 0x64 => RELOP_instr(F64_valtype, mk_relop__1_relop_(F64_Fnn, GT_relop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:269.5-269.25
  prod 0x65 => RELOP_instr(F64_valtype, mk_relop__1_relop_(F64_Fnn, LE_relop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:270.5-270.25
  prod 0x66 => RELOP_instr(F64_valtype, mk_relop__1_relop_(F64_Fnn, GE_relop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:274.5-274.25
  prod 0x67 => UNOP_instr(I32_valtype, mk_unop__0_unop_(I32_Inn, CLZ_unop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:275.5-275.25
  prod 0x68 => UNOP_instr(I32_valtype, mk_unop__0_unop_(I32_Inn, CTZ_unop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:276.5-276.28
  prod 0x69 => UNOP_instr(I32_valtype, mk_unop__0_unop_(I32_Inn, POPCNT_unop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:280.5-280.26
  prod 0x6A => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, ADD_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:281.5-281.26
  prod 0x6B => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, SUB_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:282.5-282.26
  prod 0x6C => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, MUL_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:283.5-283.30
  prod 0x6D => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, DIV_binop_Inn(S_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:284.5-284.30
  prod 0x6E => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, DIV_binop_Inn(U_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:285.5-285.30
  prod 0x6F => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, REM_binop_Inn(S_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:286.5-286.30
  prod 0x70 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, REM_binop_Inn(U_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:287.5-287.26
  prod 0x71 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, AND_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:288.5-288.25
  prod 0x72 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, OR_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:289.5-289.26
  prod 0x73 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, XOR_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:290.5-290.26
  prod 0x74 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, SHL_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:291.5-291.30
  prod 0x75 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, SHR_binop_Inn(S_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:292.5-292.30
  prod 0x76 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, SHR_binop_Inn(U_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:293.5-293.27
  prod 0x77 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, ROTL_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:294.5-294.27
  prod 0x78 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, ROTR_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:298.5-298.25
  prod 0x79 => UNOP_instr(I64_valtype, mk_unop__0_unop_(I64_Inn, CLZ_unop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:299.5-299.25
  prod 0x7A => UNOP_instr(I64_valtype, mk_unop__0_unop_(I64_Inn, CTZ_unop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:300.5-300.28
  prod 0x7B => UNOP_instr(I64_valtype, mk_unop__0_unop_(I64_Inn, POPCNT_unop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:304.5-304.26
  prod 0x7C => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, ADD_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:305.5-305.26
  prod 0x7D => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, SUB_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:306.5-306.26
  prod 0x7E => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, MUL_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:307.5-307.30
  prod 0x7F => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, DIV_binop_Inn(S_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:308.5-308.30
  prod 0x80 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, DIV_binop_Inn(U_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:309.5-309.30
  prod 0x81 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, REM_binop_Inn(S_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:310.5-310.30
  prod 0x82 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, REM_binop_Inn(U_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:311.5-311.26
  prod 0x83 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, AND_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:312.5-312.25
  prod 0x84 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, OR_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:313.5-313.26
  prod 0x85 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, XOR_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:314.5-314.26
  prod 0x86 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, SHL_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:315.5-315.30
  prod 0x87 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, SHR_binop_Inn(S_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:316.5-316.30
  prod 0x88 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, SHR_binop_Inn(U_sx)))
  ;; ../specification/wasm-1.0/A-binary.spectec:317.5-317.27
  prod 0x89 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, ROTL_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:318.5-318.27
  prod 0x8A => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, ROTR_binop_Inn))
  ;; ../specification/wasm-1.0/A-binary.spectec:322.5-322.25
  prod 0x8B => UNOP_instr(F32_valtype, mk_unop__1_unop_(F32_Fnn, ABS_unop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:323.5-323.25
  prod 0x8C => UNOP_instr(F32_valtype, mk_unop__1_unop_(F32_Fnn, NEG_unop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:324.5-324.26
  prod 0x8D => UNOP_instr(F32_valtype, mk_unop__1_unop_(F32_Fnn, CEIL_unop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:325.5-325.27
  prod 0x8E => UNOP_instr(F32_valtype, mk_unop__1_unop_(F32_Fnn, FLOOR_unop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:326.5-326.27
  prod 0x8F => UNOP_instr(F32_valtype, mk_unop__1_unop_(F32_Fnn, TRUNC_unop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:327.5-327.29
  prod 0x90 => UNOP_instr(F32_valtype, mk_unop__1_unop_(F32_Fnn, NEAREST_unop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:328.5-328.26
  prod 0x91 => UNOP_instr(F32_valtype, mk_unop__1_unop_(F32_Fnn, SQRT_unop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:332.5-332.26
  prod 0x92 => BINOP_instr(F32_valtype, mk_binop__1_binop_(F32_Fnn, ADD_binop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:333.5-333.26
  prod 0x93 => BINOP_instr(F32_valtype, mk_binop__1_binop_(F32_Fnn, SUB_binop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:334.5-334.26
  prod 0x94 => BINOP_instr(F32_valtype, mk_binop__1_binop_(F32_Fnn, MUL_binop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:335.5-335.26
  prod 0x95 => BINOP_instr(F32_valtype, mk_binop__1_binop_(F32_Fnn, DIV_binop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:336.5-336.26
  prod 0x96 => BINOP_instr(F32_valtype, mk_binop__1_binop_(F32_Fnn, MIN_binop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:337.5-337.26
  prod 0x97 => BINOP_instr(F32_valtype, mk_binop__1_binop_(F32_Fnn, MAX_binop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:338.5-338.31
  prod 0x98 => BINOP_instr(F32_valtype, mk_binop__1_binop_(F32_Fnn, COPYSIGN_binop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:342.5-342.25
  prod 0x99 => UNOP_instr(F64_valtype, mk_unop__1_unop_(F64_Fnn, ABS_unop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:343.5-343.25
  prod 0x9A => UNOP_instr(F64_valtype, mk_unop__1_unop_(F64_Fnn, NEG_unop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:344.5-344.26
  prod 0x9B => UNOP_instr(F64_valtype, mk_unop__1_unop_(F64_Fnn, CEIL_unop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:345.5-345.27
  prod 0x9C => UNOP_instr(F64_valtype, mk_unop__1_unop_(F64_Fnn, FLOOR_unop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:346.5-346.27
  prod 0x9D => UNOP_instr(F64_valtype, mk_unop__1_unop_(F64_Fnn, TRUNC_unop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:347.5-347.29
  prod 0x9E => UNOP_instr(F64_valtype, mk_unop__1_unop_(F64_Fnn, NEAREST_unop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:348.5-348.26
  prod 0x9F => UNOP_instr(F64_valtype, mk_unop__1_unop_(F64_Fnn, SQRT_unop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:352.5-352.26
  prod 0xA0 => BINOP_instr(F64_valtype, mk_binop__1_binop_(F64_Fnn, ADD_binop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:353.5-353.26
  prod 0xA1 => BINOP_instr(F64_valtype, mk_binop__1_binop_(F64_Fnn, SUB_binop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:354.5-354.26
  prod 0xA2 => BINOP_instr(F64_valtype, mk_binop__1_binop_(F64_Fnn, MUL_binop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:355.5-355.26
  prod 0xA3 => BINOP_instr(F64_valtype, mk_binop__1_binop_(F64_Fnn, DIV_binop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:356.5-356.26
  prod 0xA4 => BINOP_instr(F64_valtype, mk_binop__1_binop_(F64_Fnn, MIN_binop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:357.5-357.26
  prod 0xA5 => BINOP_instr(F64_valtype, mk_binop__1_binop_(F64_Fnn, MAX_binop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:358.5-358.31
  prod 0xA6 => BINOP_instr(F64_valtype, mk_binop__1_binop_(F64_Fnn, COPYSIGN_binop_Fnn))
  ;; ../specification/wasm-1.0/A-binary.spectec:362.5-362.31
  prod 0xA7 => CVTOP_instr(I32_valtype, I64_valtype, WRAP_cvtop)
  ;; ../specification/wasm-1.0/A-binary.spectec:363.5-363.36
  prod 0xA8 => CVTOP_instr(I32_valtype, F32_valtype, TRUNC_cvtop(S_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:364.5-364.36
  prod 0xA9 => CVTOP_instr(I32_valtype, F32_valtype, TRUNC_cvtop(U_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:365.5-365.36
  prod 0xAA => CVTOP_instr(I32_valtype, F64_valtype, TRUNC_cvtop(S_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:366.5-366.36
  prod 0xAB => CVTOP_instr(I32_valtype, F64_valtype, TRUNC_cvtop(U_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:367.5-367.37
  prod 0xAC => CVTOP_instr(I64_valtype, I32_valtype, EXTEND_cvtop(S_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:368.5-368.37
  prod 0xAD => CVTOP_instr(I64_valtype, I32_valtype, EXTEND_cvtop(U_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:369.5-369.36
  prod 0xAE => CVTOP_instr(I64_valtype, F32_valtype, TRUNC_cvtop(S_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:370.5-370.36
  prod 0xAF => CVTOP_instr(I64_valtype, F32_valtype, TRUNC_cvtop(U_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:371.5-371.36
  prod 0xB0 => CVTOP_instr(I64_valtype, F64_valtype, TRUNC_cvtop(S_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:372.5-372.36
  prod 0xB1 => CVTOP_instr(I64_valtype, F64_valtype, TRUNC_cvtop(U_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:373.5-373.38
  prod 0xB2 => CVTOP_instr(F32_valtype, I32_valtype, CONVERT_cvtop(S_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:374.5-374.38
  prod 0xB3 => CVTOP_instr(F32_valtype, I32_valtype, CONVERT_cvtop(U_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:375.5-375.38
  prod 0xB4 => CVTOP_instr(F32_valtype, I64_valtype, CONVERT_cvtop(S_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:376.5-376.38
  prod 0xB5 => CVTOP_instr(F32_valtype, I64_valtype, CONVERT_cvtop(U_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:377.5-377.33
  prod 0xB6 => CVTOP_instr(F32_valtype, F64_valtype, DEMOTE_cvtop)
  ;; ../specification/wasm-1.0/A-binary.spectec:378.5-378.38
  prod 0xB7 => CVTOP_instr(F64_valtype, I32_valtype, CONVERT_cvtop(S_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:379.5-379.38
  prod 0xB8 => CVTOP_instr(F64_valtype, I32_valtype, CONVERT_cvtop(U_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:380.5-380.38
  prod 0xB9 => CVTOP_instr(F64_valtype, I64_valtype, CONVERT_cvtop(S_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:381.5-381.38
  prod 0xBA => CVTOP_instr(F64_valtype, I64_valtype, CONVERT_cvtop(U_sx))
  ;; ../specification/wasm-1.0/A-binary.spectec:382.5-382.34
  prod 0xBB => CVTOP_instr(F32_valtype, F64_valtype, PROMOTE_cvtop)
  ;; ../specification/wasm-1.0/A-binary.spectec:383.5-383.38
  prod 0xBC => CVTOP_instr(I32_valtype, F32_valtype, REINTERPRET_cvtop)
  ;; ../specification/wasm-1.0/A-binary.spectec:384.5-384.38
  prod 0xBD => CVTOP_instr(I64_valtype, F64_valtype, REINTERPRET_cvtop)
  ;; ../specification/wasm-1.0/A-binary.spectec:385.5-385.38
  prod 0xBE => CVTOP_instr(F32_valtype, I32_valtype, REINTERPRET_cvtop)
  ;; ../specification/wasm-1.0/A-binary.spectec:386.5-386.38
  prod 0xBF => CVTOP_instr(F64_valtype, I64_valtype, REINTERPRET_cvtop)
}

;; ../specification/wasm-1.0/A-binary.spectec:391.1-392.29
grammar Bexpr : expr
  ;; ../specification/wasm-1.0/A-binary.spectec:392.5-392.29
  prod{in_lst : instr*} {{in:Binstr*{in <- in_lst}} {0x0B}} => in_lst

;; ../specification/wasm-1.0/A-binary.spectec:404.1-406.15
grammar Bsection_(v_N : N, syntax en, grammar BX : en*) : en*
  ;; ../specification/wasm-1.0/A-binary.spectec:405.5-405.55
  prod{en_lst : en*, len : nat} {{mk_byte_byte(v_N):Bbyte} {mk_uN_u32(len):Bu32} {en_lst:BX}} => en_lst
    -- if (len = 0)
  ;; ../specification/wasm-1.0/A-binary.spectec:406.5-406.15
  prod eps => []

;; ../specification/wasm-1.0/A-binary.spectec:411.1-412.23
grammar Bcustom : ()*
  ;; ../specification/wasm-1.0/A-binary.spectec:412.5-412.23
  prod {{Bname} {Bbyte*{}}} => []

;; ../specification/wasm-1.0/A-binary.spectec:414.1-415.32
grammar Bcustomsec : ()
  ;; ../specification/wasm-1.0/A-binary.spectec:415.5-415.32
  prod Bsection_(0, syntax (), grammar Bcustom) => ((), ()).1

;; ../specification/wasm-1.0/A-binary.spectec:420.1-421.28
grammar Btype : type
  ;; ../specification/wasm-1.0/A-binary.spectec:421.5-421.28
  prod{ft : functype} ft:Bfunctype => TYPE_type(ft)

;; ../specification/wasm-1.0/A-binary.spectec:423.1-424.42
grammar Btypesec : type*
  ;; ../specification/wasm-1.0/A-binary.spectec:424.5-424.42
  prod{ty_lst : type*} ty_lst:Bsection_(1, syntax type, grammar Blist(syntax type, grammar Btype)) => ty_lst

;; ../specification/wasm-1.0/A-binary.spectec:429.1-430.64
grammar Bimport : import
  ;; ../specification/wasm-1.0/A-binary.spectec:430.5-430.64
  prod{nm_1 : name, nm_2 : name, xt : externtype} {{nm_1:Bname} {nm_2:Bname} {xt:Bexterntype}} => IMPORT_import(nm_1, nm_2, xt)

;; ../specification/wasm-1.0/A-binary.spectec:432.1-433.44
grammar Bimportsec : import*
  ;; ../specification/wasm-1.0/A-binary.spectec:433.5-433.44
  prod{im_lst : import*} im_lst:Bsection_(2, syntax import, grammar Blist(syntax import, grammar Bimport)) => im_lst

;; ../specification/wasm-1.0/A-binary.spectec:438.1-439.43
grammar Bfuncsec : typeidx*
  ;; ../specification/wasm-1.0/A-binary.spectec:439.5-439.43
  prod{x_lst : idx*} x_lst:Bsection_(3, syntax typeidx, grammar Blist(syntax typeidx, grammar Btypeidx)) => x_lst

;; ../specification/wasm-1.0/A-binary.spectec:444.1-445.30
grammar Btable : table
  ;; ../specification/wasm-1.0/A-binary.spectec:445.5-445.30
  prod{tt : tabletype} tt:Btabletype => TABLE_table(tt)

;; ../specification/wasm-1.0/A-binary.spectec:447.1-448.45
grammar Btablesec : table*
  ;; ../specification/wasm-1.0/A-binary.spectec:448.5-448.45
  prod{tab_lst : table*} tab_lst:Bsection_(4, syntax table, grammar Blist(syntax table, grammar Btable)) => tab_lst

;; ../specification/wasm-1.0/A-binary.spectec:453.1-454.29
grammar Bmem : mem
  ;; ../specification/wasm-1.0/A-binary.spectec:454.5-454.29
  prod{mt : memtype} mt:Bmemtype => MEMORY_mem(mt)

;; ../specification/wasm-1.0/A-binary.spectec:456.1-457.43
grammar Bmemsec : mem*
  ;; ../specification/wasm-1.0/A-binary.spectec:457.5-457.43
  prod{mem_lst : mem*} mem_lst:Bsection_(5, syntax mem, grammar Blist(syntax mem, grammar Bmem)) => mem_lst

;; ../specification/wasm-1.0/A-binary.spectec:462.1-463.42
grammar Bglobal : global
  ;; ../specification/wasm-1.0/A-binary.spectec:463.5-463.42
  prod{gt : globaltype, e : expr} {{gt:Bglobaltype} {e:Bexpr}} => GLOBAL_global(gt, e)

;; ../specification/wasm-1.0/A-binary.spectec:465.1-466.48
grammar Bglobalsec : global*
  ;; ../specification/wasm-1.0/A-binary.spectec:466.5-466.48
  prod{glob_lst : global*} glob_lst:Bsection_(6, syntax global, grammar Blist(syntax global, grammar Bglobal)) => glob_lst

;; ../specification/wasm-1.0/A-binary.spectec:471.1-472.43
grammar Bexport : export
  ;; ../specification/wasm-1.0/A-binary.spectec:472.5-472.43
  prod{nm : name, xx : externidx} {{nm:Bname} {xx:Bexternidx}} => EXPORT_export(nm, xx)

;; ../specification/wasm-1.0/A-binary.spectec:474.1-475.44
grammar Bexportsec : export*
  ;; ../specification/wasm-1.0/A-binary.spectec:475.5-475.44
  prod{ex_lst : export*} ex_lst:Bsection_(7, syntax export, grammar Blist(syntax export, grammar Bexport)) => ex_lst

;; ../specification/wasm-1.0/A-binary.spectec:480.1-481.28
grammar Bstart : start*
  ;; ../specification/wasm-1.0/A-binary.spectec:481.5-481.28
  prod{x : idx} x:Bfuncidx => [START_start(x)]

;; ../specification/wasm-1.0/A-binary.spectec:485.1-486.60
grammar Bstartsec : start?
  ;; ../specification/wasm-1.0/A-binary.spectec:486.5-486.60
  prod{v_startopt : startopt} v_startopt:Bsection_(8, syntax start, grammar Bstart) => !($opt_(syntax start, v_startopt))

;; ../specification/wasm-1.0/A-binary.spectec:491.1-492.49
grammar Belem : elem
  ;; ../specification/wasm-1.0/A-binary.spectec:492.5-492.49
  prod{e : expr, x_lst : idx*} {{0x00} {e:Bexpr} {x_lst:Blist(syntax funcidx, grammar Bfuncidx)}} => ELEM_elem(e, x_lst)

;; ../specification/wasm-1.0/A-binary.spectec:494.1-495.46
grammar Belemsec : elem*
  ;; ../specification/wasm-1.0/A-binary.spectec:495.5-495.46
  prod{elem_lst : elem*} elem_lst:Bsection_(9, syntax elem, grammar Blist(syntax elem, grammar Belem)) => elem_lst

;; ../specification/wasm-1.0/A-binary.spectec:502.1-503.37
grammar Blocals : local*
  ;; ../specification/wasm-1.0/A-binary.spectec:503.5-503.37
  prod{t : valtype, v_n : n} {{mk_uN_u32(v_n):Bu32} {t:Bvaltype}} => LOCAL_local(t)^v_n{}

;; ../specification/wasm-1.0/A-binary.spectec:505.1-506.74
grammar Bfunc : code
  ;; ../specification/wasm-1.0/A-binary.spectec:506.5-506.74
  prod{local_lst_lst : local**, v_expr : expr} {{local_lst_lst:Blist(syntax local*, grammar Blocals)} {v_expr:Bexpr}} => ($concat_(syntax local, local_lst_lst), v_expr)

;; ../specification/wasm-1.0/A-binary.spectec:508.1-509.55
grammar Bcode : code
  ;; ../specification/wasm-1.0/A-binary.spectec:509.5-509.55
  prod{v_code : code, len : nat} {{mk_uN_u32(len):Bu32} {v_code:Bfunc}} => v_code
    -- if (len = 0)

;; ../specification/wasm-1.0/A-binary.spectec:511.1-512.47
grammar Bcodesec : code*
  ;; ../specification/wasm-1.0/A-binary.spectec:512.5-512.47
  prod{code_lst : code*} code_lst:Bsection_(10, syntax code, grammar Blist(syntax code, grammar Bcode)) => code_lst

;; ../specification/wasm-1.0/A-binary.spectec:517.1-518.46
grammar Bdata : data
  ;; ../specification/wasm-1.0/A-binary.spectec:518.5-518.46
  prod{e : expr, b_lst : byte*} {{0x00} {e:Bexpr} {b_lst:Blist(syntax byte, grammar Bbyte)}} => DATA_data(e, b_lst)

;; ../specification/wasm-1.0/A-binary.spectec:520.1-521.47
grammar Bdatasec : data*
  ;; ../specification/wasm-1.0/A-binary.spectec:521.5-521.47
  prod{data_lst : data*} data_lst:Bsection_(11, syntax data, grammar Blist(syntax data, grammar Bdata)) => data_lst

;; ../specification/wasm-1.0/A-binary.spectec:526.1-541.45
grammar Bmodule : module
  ;; ../specification/wasm-1.0/A-binary.spectec:527.5-541.45
  prod{type_lst : type*, import_lst : import*, func_lst : func*, global_lst : global*, table_lst : table*, mem_lst : mem*, elem_lst : elem*, data_lst : data*, start_opt : start?, export_lst : export*, typeidx_lst : typeidx*, expr_lst : expr*, local_lst_lst : local**} {{0x00} {0x61} {0x73} {0x6D} {mk_uN_u32(1):Bu32} {Bcustomsec*{}} {type_lst:Btypesec} {Bcustomsec*{}} {import_lst:Bimportsec} {Bcustomsec*{}} {typeidx_lst:Bfuncsec} {Bcustomsec*{}} {table_lst:Btablesec} {Bcustomsec*{}} {mem_lst:Bmemsec} {Bcustomsec*{}} {global_lst:Bglobalsec} {Bcustomsec*{}} {export_lst:Bexportsec} {Bcustomsec*{}} {start_opt:Bstartsec} {Bcustomsec*{}} {elem_lst:Belemsec} {Bcustomsec*{}} {(local_lst, v_expr)*{v_expr <- expr_lst, local_lst <- local_lst_lst}:Bcodesec} {Bcustomsec*{}} {data_lst:Bdatasec} {Bcustomsec*{}}} => MODULE_module(type_lst, import_lst, func_lst, global_lst, table_lst, mem_lst, elem_lst, data_lst, start_opt, export_lst)
    -- (if (v_func = FUNC_func(v_typeidx, local_lst, v_expr)))*{v_expr <- expr_lst, v_func <- func_lst, local_lst <- local_lst_lst, v_typeidx <- typeidx_lst}


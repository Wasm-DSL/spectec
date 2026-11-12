
;; ../specification/wasm-2.0/1-syntax.spectec:162.14-162.17
syntax MUT = 
  | MUT

;; ../specification/wasm-2.0/0-aux.spectec:7.1-7.15
syntax N = nat

;; ../specification/wasm-2.0/0-aux.spectec:8.1-8.15
syntax M = nat

;; ../specification/wasm-2.0/0-aux.spectec:9.1-9.15
syntax n = nat

;; ../specification/wasm-2.0/0-aux.spectec:10.1-10.15
syntax m = nat

;; ../specification/wasm-2.0/0-aux.spectec:15.1-15.14
def $Ki : nat
  ;; ../specification/wasm-2.0/0-aux.spectec:16.1-16.15
  def $Ki = 1024

;; ../specification/wasm-2.0/0-aux.spectec:21.1-21.25
def $min(nat : nat, nat : nat) : nat
  ;; ../specification/wasm-2.0/0-aux.spectec:22.1-22.36
  def $min{i : nat, j : nat}(i, j) = i
    -- if (i <= j)
  ;; ../specification/wasm-2.0/0-aux.spectec:23.1-23.33
  def $min{i : nat, j : nat}(i, j) = j
    -- otherwise

;; ../specification/wasm-2.0/0-aux.spectec:25.1-25.21
rec {

;; ../specification/wasm-2.0/0-aux.spectec:25.1-25.21
def $sum(nat*) : nat
  ;; ../specification/wasm-2.0/0-aux.spectec:26.1-26.18
  def $sum([]) = 0
  ;; ../specification/wasm-2.0/0-aux.spectec:27.1-27.35
  def $sum{n : n, `n'*` : n*}([n] ++ n'*{n' <- `n'*`}) = (n + $sum(n'*{n' <- `n'*`}))
}

;; ../specification/wasm-2.0/0-aux.spectec:32.1-32.58
def $opt_(syntax X, X*) : X?
  ;; ../specification/wasm-2.0/0-aux.spectec:33.1-33.31
  def $opt_{syntax X}(syntax X, []) = ?()
  ;; ../specification/wasm-2.0/0-aux.spectec:34.1-34.27
  def $opt_{syntax X, w : X}(syntax X, [w]) = ?(w)

;; ../specification/wasm-2.0/0-aux.spectec:36.1-36.45
def $list_(syntax X, X?) : X*
  ;; ../specification/wasm-2.0/0-aux.spectec:37.1-37.32
  def $list_{syntax X}(syntax X, ?()) = []
  ;; ../specification/wasm-2.0/0-aux.spectec:38.1-38.28
  def $list_{syntax X, w : X}(syntax X, ?(w)) = [w]

;; ../specification/wasm-2.0/0-aux.spectec:40.1-40.86
rec {

;; ../specification/wasm-2.0/0-aux.spectec:40.1-40.86
def $concat_(syntax X, X**) : X*
  ;; ../specification/wasm-2.0/0-aux.spectec:41.1-41.34
  def $concat_{syntax X}(syntax X, []) = []
  ;; ../specification/wasm-2.0/0-aux.spectec:42.1-42.61
  def $concat_{syntax X, `w*` : X*, `w'**` : X**}(syntax X, [w*{w <- `w*`}] ++ w'*{w' <- `w'*`}*{`w'*` <- `w'**`}) = w*{w <- `w*`} ++ $concat_(syntax X, w'*{w' <- `w'*`}*{`w'*` <- `w'**`})
}

;; ../specification/wasm-2.0/0-aux.spectec:44.1-44.39
def $inv_concat_(syntax X, X*) : X**

;; ../specification/wasm-2.0/0-aux.spectec:51.1-51.46
rec {

;; ../specification/wasm-2.0/0-aux.spectec:51.1-51.46
def $setproduct2_(syntax X, X : X, X**) : X**
  ;; ../specification/wasm-2.0/0-aux.spectec:57.1-57.44
  def $setproduct2_{syntax X, w_1 : X}(syntax X, w_1, []) = []
  ;; ../specification/wasm-2.0/0-aux.spectec:58.1-58.90
  def $setproduct2_{syntax X, w_1 : X, `w'*` : X*, `w**` : X**}(syntax X, w_1, [w'*{w' <- `w'*`}] ++ w*{w <- `w*`}*{`w*` <- `w**`}) = [[w_1] ++ w'*{w' <- `w'*`}] ++ $setproduct2_(syntax X, w_1, w*{w <- `w*`}*{`w*` <- `w**`})
}

;; ../specification/wasm-2.0/0-aux.spectec:50.1-50.47
rec {

;; ../specification/wasm-2.0/0-aux.spectec:50.1-50.47
def $setproduct1_(syntax X, X*, X**) : X**
  ;; ../specification/wasm-2.0/0-aux.spectec:55.1-55.46
  def $setproduct1_{syntax X, `w**` : X**}(syntax X, [], w*{w <- `w*`}*{`w*` <- `w**`}) = []
  ;; ../specification/wasm-2.0/0-aux.spectec:56.1-56.107
  def $setproduct1_{syntax X, w_1 : X, `w'*` : X*, `w**` : X**}(syntax X, [w_1] ++ w'*{w' <- `w'*`}, w*{w <- `w*`}*{`w*` <- `w**`}) = $setproduct2_(syntax X, w_1, w*{w <- `w*`}*{`w*` <- `w**`}) ++ $setproduct1_(syntax X, w'*{w' <- `w'*`}, w*{w <- `w*`}*{`w*` <- `w**`})
}

;; ../specification/wasm-2.0/0-aux.spectec:49.1-49.84
rec {

;; ../specification/wasm-2.0/0-aux.spectec:49.1-49.84
def $setproduct_(syntax X, X**) : X**
  ;; ../specification/wasm-2.0/0-aux.spectec:53.1-53.40
  def $setproduct_{syntax X}(syntax X, []) = [[]]
  ;; ../specification/wasm-2.0/0-aux.spectec:54.1-54.90
  def $setproduct_{syntax X, `w_1*` : X*, `w**` : X**}(syntax X, [w_1*{w_1 <- `w_1*`}] ++ w*{w <- `w*`}*{`w*` <- `w**`}) = $setproduct1_(syntax X, w_1*{w_1 <- `w_1*`}, $setproduct_(syntax X, w*{w <- `w*`}*{`w*` <- `w**`}))
}

;; ../specification/wasm-2.0/0-aux.spectec:60.1-60.78
rec {

;; ../specification/wasm-2.0/0-aux.spectec:60.1-60.78
def $disjoint_(syntax X, X*) : bool
  ;; ../specification/wasm-2.0/0-aux.spectec:61.1-61.37
  def $disjoint_{syntax X}(syntax X, []) = true
  ;; ../specification/wasm-2.0/0-aux.spectec:62.1-62.68
  def $disjoint_{syntax X, w : X, `w'*` : X*}(syntax X, [w] ++ w'*{w' <- `w'*`}) = (~ (w <- w'*{w' <- `w'*`}) /\ $disjoint_(syntax X, w'*{w' <- `w'*`}))
}

;; ../specification/wasm-2.0/1-syntax.spectec:6.1-6.49
syntax list{syntax X}(syntax X) = 
  | `%`(`X*` : X*)
    -- if (|X*{X <- `X*`}| < (2 ^ 32))

;; ../specification/wasm-2.0/1-syntax.spectec:15.1-15.36
syntax bit = 
  | `%`(i : nat)
    -- if ((i = 0) \/ (i = 1))

;; ../specification/wasm-2.0/1-syntax.spectec:16.1-16.50
syntax byte = 
  | `%`(i : nat)
    -- if ((i >= 0) /\ (i <= 255))

;; ../specification/wasm-2.0/1-syntax.spectec:18.1-19.25
syntax uN{N : N}(N) = 
  | `%`(i : nat)
    -- if ((i >= 0) /\ (i <= ((((2 ^ N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))

;; ../specification/wasm-2.0/1-syntax.spectec:20.1-21.49
syntax sN{N : N}(N) = 
  | `%`(i : int)
    -- if ((((i >= - ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) /\ (i <= - (1 : nat <:> int))) \/ (i = (0 : nat <:> int))) \/ ((i >= + (1 : nat <:> int)) /\ (i <= (((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))

;; ../specification/wasm-2.0/1-syntax.spectec:22.1-23.8
syntax iN{N : N}(N) = uN(N)

;; ../specification/wasm-2.0/1-syntax.spectec:25.1-25.18
syntax u8 = uN(8)

;; ../specification/wasm-2.0/1-syntax.spectec:26.1-26.20
syntax u16 = uN(16)

;; ../specification/wasm-2.0/1-syntax.spectec:27.1-27.20
syntax u31 = uN(31)

;; ../specification/wasm-2.0/1-syntax.spectec:28.1-28.20
syntax u32 = uN(32)

;; ../specification/wasm-2.0/1-syntax.spectec:29.1-29.20
syntax u64 = uN(64)

;; ../specification/wasm-2.0/1-syntax.spectec:30.1-30.20
syntax s33 = sN(33)

;; ../specification/wasm-2.0/1-syntax.spectec:31.1-31.20
syntax i32 = iN(32)

;; ../specification/wasm-2.0/1-syntax.spectec:32.1-32.20
syntax i64 = iN(64)

;; ../specification/wasm-2.0/1-syntax.spectec:33.1-33.22
syntax i128 = iN(128)

;; ../specification/wasm-2.0/1-syntax.spectec:40.1-40.35
def $signif(N : N) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:41.1-41.21
  def $signif(32) = 23
  ;; ../specification/wasm-2.0/1-syntax.spectec:42.1-42.21
  def $signif(64) = 52

;; ../specification/wasm-2.0/1-syntax.spectec:44.1-44.34
def $expon(N : N) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:45.1-45.19
  def $expon(32) = 8
  ;; ../specification/wasm-2.0/1-syntax.spectec:46.1-46.20
  def $expon(64) = 11

;; ../specification/wasm-2.0/1-syntax.spectec:48.1-48.30
def $M(N : N) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:49.1-49.23
  def $M{N : N}(N) = $signif(N)

;; ../specification/wasm-2.0/1-syntax.spectec:51.1-51.30
def $E(N : N) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:52.1-52.22
  def $E{N : N}(N) = $expon(N)

;; ../specification/wasm-2.0/1-syntax.spectec:58.1-58.30
syntax exp = int

;; ../specification/wasm-2.0/1-syntax.spectec:59.1-63.84
syntax fNmag{N : N}(N) = 
  | NORM(m : m, exp : exp)
    -- if ((m < (2 ^ $M(N))) /\ ((((2 : nat <:> int) - ((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) <= exp) /\ (exp <= (((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))
  | SUBNORM(m : m) {exp : exp}
    -- if ((m < (2 ^ $M(N))) /\ (((2 : nat <:> int) - ((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) = exp))
  | INF
  | NAN(m : m)
    -- if ((1 <= m) /\ (m < (2 ^ $M(N))))

;; ../specification/wasm-2.0/1-syntax.spectec:54.1-56.35
syntax fN{N : N}(N) = 
  | POS(fNmag(N))
  | NEG(fNmag(N))

;; ../specification/wasm-2.0/1-syntax.spectec:65.1-65.20
syntax f32 = fN(32)

;; ../specification/wasm-2.0/1-syntax.spectec:66.1-66.20
syntax f64 = fN(64)

;; ../specification/wasm-2.0/1-syntax.spectec:68.1-68.39
def $fzero(N : N) : fN(N)
  ;; ../specification/wasm-2.0/1-syntax.spectec:69.1-69.32
  def $fzero{N : N}(N) = POS_fN(SUBNORM_fNmag(0))

;; ../specification/wasm-2.0/1-syntax.spectec:71.1-71.39
def $fone(N : N) : fN(N)
  ;; ../specification/wasm-2.0/1-syntax.spectec:72.1-72.30
  def $fone{N : N}(N) = POS_fN(NORM_fNmag(1, (0 : nat <:> int)))

;; ../specification/wasm-2.0/1-syntax.spectec:74.1-74.21
def $canon_(N : N) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:75.1-75.37
  def $canon_{N : N}(N) = (2 ^ ((($signif(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))

;; ../specification/wasm-2.0/1-syntax.spectec:80.1-81.8
syntax vN{N : N}(N) = iN(N)

;; ../specification/wasm-2.0/1-syntax.spectec:88.1-88.85
syntax char = 
  | `%`(i : nat)
    -- if (((i >= 0) /\ (i <= 55295)) \/ ((i >= 57344) /\ (i <= 1114111)))

;; ../specification/wasm-2.0/1-syntax.spectec:90.1-90.25
rec {

;; ../specification/wasm-2.0/1-syntax.spectec:90.1-90.25
def $utf8(char*) : byte*
  ;; ../specification/wasm-2.0/A-binary.spectec:54.1-54.47
  def $utf8{ch : char, b : byte}([ch]) = [b]
    -- if ((ch!`%`_char.0 < 128) /\ (`%`_byte(ch!`%`_char.0) = b))
  ;; ../specification/wasm-2.0/A-binary.spectec:55.1-55.96
  def $utf8{ch : char, b_1 : byte, b_2 : byte}([ch]) = [b_1 b_2]
    -- if (((128 <= ch!`%`_char.0) /\ (ch!`%`_char.0 < 2048)) /\ (ch!`%`_char.0 = (((2 ^ 6) * (((b_1!`%`_byte.0 : nat <:> int) - (192 : nat <:> int)) : int <:> nat)) + (((b_2!`%`_byte.0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))))
  ;; ../specification/wasm-2.0/A-binary.spectec:56.1-56.148
  def $utf8{ch : char, b_1 : byte, b_2 : byte, b_3 : byte}([ch]) = [b_1 b_2 b_3]
    -- if ((((2048 <= ch!`%`_char.0) /\ (ch!`%`_char.0 < 55296)) \/ ((57344 <= ch!`%`_char.0) /\ (ch!`%`_char.0 < 65536))) /\ (ch!`%`_char.0 = ((((2 ^ 12) * (((b_1!`%`_byte.0 : nat <:> int) - (224 : nat <:> int)) : int <:> nat)) + ((2 ^ 6) * (((b_2!`%`_byte.0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))) + (((b_3!`%`_byte.0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))))
  ;; ../specification/wasm-2.0/A-binary.spectec:57.1-57.148
  def $utf8{ch : char, b_1 : byte, b_2 : byte, b_3 : byte, b_4 : byte}([ch]) = [b_1 b_2 b_3 b_4]
    -- if (((65536 <= ch!`%`_char.0) /\ (ch!`%`_char.0 < 69632)) /\ (ch!`%`_char.0 = (((((2 ^ 18) * (((b_1!`%`_byte.0 : nat <:> int) - (240 : nat <:> int)) : int <:> nat)) + ((2 ^ 12) * (((b_2!`%`_byte.0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))) + ((2 ^ 6) * (((b_3!`%`_byte.0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))) + (((b_4!`%`_byte.0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))))
  ;; ../specification/wasm-2.0/A-binary.spectec:58.1-58.44
  def $utf8{`ch*` : char*}(ch*{ch <- `ch*`}) = $concat_(syntax byte, $utf8([ch])*{ch <- `ch*`})
}

;; ../specification/wasm-2.0/1-syntax.spectec:92.1-92.70
syntax name = 
  | `%`(`char*` : char*)
    -- if (|$utf8(char*{char <- `char*`})| < (2 ^ 32))

;; ../specification/wasm-2.0/1-syntax.spectec:101.1-101.36
syntax idx = u32

;; ../specification/wasm-2.0/1-syntax.spectec:102.1-102.44
syntax laneidx = u8

;; ../specification/wasm-2.0/1-syntax.spectec:104.1-104.45
syntax typeidx = idx

;; ../specification/wasm-2.0/1-syntax.spectec:105.1-105.49
syntax funcidx = idx

;; ../specification/wasm-2.0/1-syntax.spectec:106.1-106.49
syntax globalidx = idx

;; ../specification/wasm-2.0/1-syntax.spectec:107.1-107.47
syntax tableidx = idx

;; ../specification/wasm-2.0/1-syntax.spectec:108.1-108.46
syntax memidx = idx

;; ../specification/wasm-2.0/1-syntax.spectec:109.1-109.45
syntax elemidx = idx

;; ../specification/wasm-2.0/1-syntax.spectec:110.1-110.45
syntax dataidx = idx

;; ../specification/wasm-2.0/1-syntax.spectec:111.1-111.47
syntax labelidx = idx

;; ../specification/wasm-2.0/1-syntax.spectec:112.1-112.47
syntax localidx = idx

;; ../specification/wasm-2.0/1-syntax.spectec:126.1-127.26
syntax numtype = 
  | I32
  | I64
  | F32
  | F64

;; ../specification/wasm-2.0/1-syntax.spectec:129.1-130.9
syntax vectype = 
  | V128

;; ../specification/wasm-2.0/1-syntax.spectec:132.1-133.22
syntax consttype = 
  | I32
  | I64
  | F32
  | F64
  | V128

;; ../specification/wasm-2.0/1-syntax.spectec:135.1-136.24
syntax reftype = 
  | FUNCREF
  | EXTERNREF

;; ../specification/wasm-2.0/1-syntax.spectec:138.1-139.38
syntax valtype = 
  | I32
  | I64
  | F32
  | F64
  | V128
  | FUNCREF
  | EXTERNREF
  | BOT

;; ../specification/wasm-2.0/1-syntax.spectec:141.1-141.38
syntax Inn = 
  | I32
  | I64

;; ../specification/wasm-2.0/1-syntax.spectec:142.1-142.38
syntax Fnn = 
  | F32
  | F64

;; ../specification/wasm-2.0/1-syntax.spectec:143.1-143.36
syntax Vnn = vectype

;; ../specification/wasm-2.0/1-syntax.spectec:146.1-147.16
syntax resulttype = list(syntax valtype)

;; ../specification/wasm-2.0/1-syntax.spectec:152.1-152.52
syntax packtype = 
  | I8
  | I16

;; ../specification/wasm-2.0/1-syntax.spectec:153.1-153.60
syntax lanetype = 
  | I32
  | I64
  | F32
  | F64
  | I8
  | I16

;; ../specification/wasm-2.0/1-syntax.spectec:155.1-155.37
syntax Pnn = packtype

;; ../specification/wasm-2.0/1-syntax.spectec:156.1-156.38
syntax Jnn = 
  | I32
  | I64
  | I8
  | I16

;; ../specification/wasm-2.0/1-syntax.spectec:157.1-157.37
syntax Lnn = lanetype

;; ../specification/wasm-2.0/1-syntax.spectec:162.1-162.18
syntax mut = MUT?

;; ../specification/wasm-2.0/1-syntax.spectec:164.1-165.17
syntax limits = 
  | `[%..%]`(u32 : u32, `u32?` : u32?)

;; ../specification/wasm-2.0/1-syntax.spectec:167.1-168.14
syntax globaltype = 
  | `%%`(mut : mut, valtype : valtype)

;; ../specification/wasm-2.0/1-syntax.spectec:169.1-170.27
syntax functype = 
  | `%->%`(resulttype : resulttype, resulttype : resulttype)

;; ../specification/wasm-2.0/1-syntax.spectec:171.1-172.17
syntax tabletype = 
  | `%%`(limits : limits, reftype : reftype)

;; ../specification/wasm-2.0/1-syntax.spectec:173.1-174.14
syntax memtype = 
  | `%PAGE`(limits : limits)

;; ../specification/wasm-2.0/1-syntax.spectec:175.1-176.10
syntax elemtype = reftype

;; ../specification/wasm-2.0/1-syntax.spectec:177.1-178.5
syntax datatype = 
  | OK

;; ../specification/wasm-2.0/1-syntax.spectec:179.1-180.70
syntax externtype = 
  | FUNC(functype : functype)
  | GLOBAL(globaltype : globaltype)
  | TABLE(tabletype : tabletype)
  | MEM(memtype : memtype)

;; ../specification/wasm-2.0/1-syntax.spectec:332.1-332.60
syntax dim = 
  | `%`(i : nat)
    -- if (((((i = 1) \/ (i = 2)) \/ (i = 4)) \/ (i = 8)) \/ (i = 16))

;; ../specification/wasm-2.0/1-syntax.spectec:210.1-210.45
def $psize(packtype : packtype) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:224.1-224.19
  def $psize(I8_packtype) = 8
  ;; ../specification/wasm-2.0/1-syntax.spectec:225.1-225.21
  def $psize(I16_packtype) = 16

;; ../specification/wasm-2.0/1-syntax.spectec:208.1-208.59
def $size(valtype : valtype) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:216.1-216.20
  def $size(I32_valtype) = 32
  ;; ../specification/wasm-2.0/1-syntax.spectec:217.1-217.20
  def $size(I64_valtype) = 64
  ;; ../specification/wasm-2.0/1-syntax.spectec:218.1-218.20
  def $size(F32_valtype) = 32
  ;; ../specification/wasm-2.0/1-syntax.spectec:219.1-219.20
  def $size(F64_valtype) = 64
  ;; ../specification/wasm-2.0/1-syntax.spectec:220.1-220.22
  def $size(V128_valtype) = 128

;; ../specification/wasm-2.0/1-syntax.spectec:211.1-211.45
def $lsize(lanetype : lanetype) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:227.1-227.37
  def $lsize{numtype : numtype}((numtype : numtype <: lanetype)) = $size((numtype : numtype <: valtype))
  ;; ../specification/wasm-2.0/1-syntax.spectec:228.1-228.40
  def $lsize{packtype : packtype}((packtype : packtype <: lanetype)) = $psize(packtype)

;; ../specification/wasm-2.0/1-syntax.spectec:333.1-334.40
syntax shape = 
  | `%X%`(lanetype : lanetype, dim : dim)
    -- if (($lsize(lanetype) * dim!`%`_dim.0) = 128)

;; ../specification/wasm-2.0/1-syntax.spectec:206.1-206.32
def $lanetype(shape : shape) : lanetype
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:36.1-36.29
  def $lanetype{Lnn : Lnn, N : N}(`%X%`_shape(Lnn, `%`_dim(N))) = Lnn

;; ../specification/wasm-2.0/1-syntax.spectec:209.1-209.46
def $vsize(vectype : vectype) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:222.1-222.23
  def $vsize(V128_vectype) = 128

;; ../specification/wasm-2.0/1-syntax.spectec:212.1-212.70
def $isize(Inn : Inn) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:230.1-230.29
  def $isize{Inn : Inn}(Inn) = $size((Inn : Inn <: valtype))

;; ../specification/wasm-2.0/1-syntax.spectec:213.1-213.70
def $jsize(Jnn : Jnn) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:232.1-232.30
  def $jsize{Jnn : Jnn}(Jnn) = $lsize((Jnn : Jnn <: lanetype))

;; ../specification/wasm-2.0/1-syntax.spectec:214.1-214.70
def $fsize(Fnn : Fnn) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:231.1-231.29
  def $fsize{Fnn : Fnn}(Fnn) = $size((Fnn : Fnn <: valtype))

;; ../specification/wasm-2.0/1-syntax.spectec:234.1-234.63
def $sizenn(numtype : numtype) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:237.1-237.28
  def $sizenn{nt : numtype}(nt) = $size((nt : numtype <: valtype))

;; ../specification/wasm-2.0/1-syntax.spectec:235.1-235.63
def $sizenn1(numtype : numtype) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:238.1-238.29
  def $sizenn1{nt : numtype}(nt) = $size((nt : numtype <: valtype))

;; ../specification/wasm-2.0/1-syntax.spectec:236.1-236.63
def $sizenn2(numtype : numtype) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:239.1-239.29
  def $sizenn2{nt : numtype}(nt) = $size((nt : numtype <: valtype))

;; ../specification/wasm-2.0/1-syntax.spectec:241.1-241.63
def $lsizenn(lanetype : lanetype) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:244.1-244.30
  def $lsizenn{lt : lanetype}(lt) = $lsize(lt)

;; ../specification/wasm-2.0/1-syntax.spectec:242.1-242.63
def $lsizenn1(lanetype : lanetype) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:245.1-245.31
  def $lsizenn1{lt : lanetype}(lt) = $lsize(lt)

;; ../specification/wasm-2.0/1-syntax.spectec:243.1-243.63
def $lsizenn2(lanetype : lanetype) : nat
  ;; ../specification/wasm-2.0/1-syntax.spectec:246.1-246.31
  def $lsizenn2{lt : lanetype}(lt) = $lsize(lt)

;; ../specification/wasm-2.0/1-syntax.spectec:248.1-248.40
def $inv_isize(nat : nat) : Inn
  ;; ../specification/wasm-2.0/1-syntax.spectec:252.1-252.25
  def $inv_isize(32) = I32_Inn
  ;; ../specification/wasm-2.0/1-syntax.spectec:253.1-253.25
  def $inv_isize(64) = I64_Inn

;; ../specification/wasm-2.0/1-syntax.spectec:249.1-249.40
def $inv_jsize(nat : nat) : Jnn
  ;; ../specification/wasm-2.0/1-syntax.spectec:256.1-256.24
  def $inv_jsize(8) = I8_Jnn
  ;; ../specification/wasm-2.0/1-syntax.spectec:257.1-257.25
  def $inv_jsize(16) = I16_Jnn
  ;; ../specification/wasm-2.0/1-syntax.spectec:258.1-258.25
  def $inv_jsize(32) = I32_Jnn
  ;; ../specification/wasm-2.0/1-syntax.spectec:259.1-259.25
  def $inv_jsize(64) = I64_Jnn

;; ../specification/wasm-2.0/1-syntax.spectec:250.1-250.40
def $inv_fsize(nat : nat) : Fnn
  ;; ../specification/wasm-2.0/1-syntax.spectec:254.1-254.25
  def $inv_fsize(32) = F32_Fnn
  ;; ../specification/wasm-2.0/1-syntax.spectec:255.1-255.25
  def $inv_fsize(64) = F64_Fnn

;; ../specification/wasm-2.0/1-syntax.spectec:262.1-262.21
syntax num_(numtype : numtype)
  ;; ../specification/wasm-2.0/1-syntax.spectec:263.1-263.36
  syntax num_{Inn : Inn}((Inn : Inn <: numtype)) = iN($sizenn((Inn : Inn <: numtype)))


  ;; ../specification/wasm-2.0/1-syntax.spectec:264.1-264.36
  syntax num_{Fnn : Fnn}((Fnn : Fnn <: numtype)) = fN($sizenn((Fnn : Fnn <: numtype)))


;; ../specification/wasm-2.0/1-syntax.spectec:266.1-266.36
syntax pack_{Pnn : Pnn}(Pnn) = iN($psize(Pnn))

;; ../specification/wasm-2.0/1-syntax.spectec:275.1-275.23
syntax lane_(lanetype : lanetype)
  ;; ../specification/wasm-2.0/1-syntax.spectec:276.1-276.36
  syntax lane_{Jnn : Jnn}((Jnn : Jnn <: lanetype)) = iN($lsize((Jnn : Jnn <: lanetype)))


  ;; ../specification/wasm-2.0/1-syntax.spectec:277.1-277.37
  syntax lane_{Fnn : Fnn}((Fnn : Fnn <: lanetype)) = fN($sizenn((Fnn : Fnn <: numtype)))


;; ../specification/wasm-2.0/1-syntax.spectec:279.1-279.34
syntax vec_{Vnn : Vnn}(Vnn) = vN($size((Vnn : vectype <: valtype)))

;; ../specification/wasm-2.0/1-syntax.spectec:281.1-281.35
def $zero(numtype : numtype) : num_(numtype)
  ;; ../specification/wasm-2.0/1-syntax.spectec:282.1-282.19
  def $zero{Inn : Inn}((Inn : Inn <: numtype)) = `%`_num_(0)
  ;; ../specification/wasm-2.0/1-syntax.spectec:283.1-283.36
  def $zero{Fnn : Fnn}((Fnn : Fnn <: numtype)) = $fzero($size((Fnn : Fnn <: valtype)))

;; ../specification/wasm-2.0/1-syntax.spectec:288.1-288.42
syntax sx = 
  | U
  | S

;; ../specification/wasm-2.0/1-syntax.spectec:289.1-289.56
syntax sz = 
  | `%`(i : nat)
    -- if ((((i = 8) \/ (i = 16)) \/ (i = 32)) \/ (i = 64))

;; ../specification/wasm-2.0/1-syntax.spectec:291.1-291.22
syntax unop_(numtype : numtype)
  ;; ../specification/wasm-2.0/1-syntax.spectec:292.1-292.50
  syntax unop_{Inn : Inn}((Inn : Inn <: numtype)) = 
  | CLZ
  | CTZ
  | POPCNT
  | EXTEND(n : n)


  ;; ../specification/wasm-2.0/1-syntax.spectec:293.1-293.70
  syntax unop_{Fnn : Fnn}((Fnn : Fnn <: numtype)) = 
  | ABS
  | NEG
  | SQRT
  | CEIL
  | FLOOR
  | TRUNC
  | NEAREST


;; ../specification/wasm-2.0/1-syntax.spectec:295.1-295.23
syntax binop_(numtype : numtype)
  ;; ../specification/wasm-2.0/1-syntax.spectec:296.1-298.66
  syntax binop_{Inn : Inn}((Inn : Inn <: numtype)) = 
  | ADD
  | SUB
  | MUL
  | DIV(sx : sx)
  | REM(sx : sx)
  | AND
  | OR
  | XOR
  | SHL
  | SHR(sx : sx)
  | ROTL
  | ROTR


  ;; ../specification/wasm-2.0/1-syntax.spectec:299.1-300.49
  syntax binop_{Fnn : Fnn}((Fnn : Fnn <: numtype)) = 
  | ADD
  | SUB
  | MUL
  | DIV
  | MIN
  | MAX
  | COPYSIGN


;; ../specification/wasm-2.0/1-syntax.spectec:302.1-302.24
syntax testop_{Inn : Inn}((Inn : Inn <: numtype)) = 
  | EQZ

;; ../specification/wasm-2.0/1-syntax.spectec:306.1-306.23
syntax relop_(numtype : numtype)
  ;; ../specification/wasm-2.0/1-syntax.spectec:307.1-310.52
  syntax relop_{Inn : Inn}((Inn : Inn <: numtype)) = 
  | EQ
  | NE
  | LT(sx : sx)
  | GT(sx : sx)
  | LE(sx : sx)
  | GE(sx : sx)


  ;; ../specification/wasm-2.0/1-syntax.spectec:311.1-312.32
  syntax relop_{Fnn : Fnn}((Fnn : Fnn <: numtype)) = 
  | EQ
  | NE
  | LT
  | GT
  | LE
  | GE


;; ../specification/wasm-2.0/1-syntax.spectec:314.1-314.37
syntax cvtop__(numtype_1 : numtype, numtype_2 : numtype)
  ;; ../specification/wasm-2.0/1-syntax.spectec:315.1-317.57
  syntax cvtop__{Inn_1 : Inn, Inn_2 : Inn}((Inn_1 : Inn <: numtype), (Inn_2 : Inn <: numtype)) = 
  | EXTEND(sx : sx)
    -- if ($sizenn1((Inn_1 : Inn <: numtype)) < $sizenn2((Inn_2 : Inn <: numtype)))
  | WRAP
    -- if ($sizenn1((Inn_1 : Inn <: numtype)) > $sizenn2((Inn_2 : Inn <: numtype)))


  ;; ../specification/wasm-2.0/1-syntax.spectec:318.1-320.57
  syntax cvtop__{Inn_1 : Inn, Fnn_2 : Fnn}((Inn_1 : Inn <: numtype), (Fnn_2 : Fnn <: numtype)) = 
  | CONVERT(sx : sx)
  | REINTERPRET
    -- if ($sizenn1((Inn_1 : Inn <: numtype)) = $sizenn2((Fnn_2 : Fnn <: numtype)))


  ;; ../specification/wasm-2.0/1-syntax.spectec:321.1-324.57
  syntax cvtop__{Fnn_1 : Fnn, Inn_2 : Inn}((Fnn_1 : Fnn <: numtype), (Inn_2 : Inn <: numtype)) = 
  | TRUNC(sx : sx)
  | TRUNC_SAT(sx : sx)
  | REINTERPRET
    -- if ($sizenn1((Fnn_1 : Fnn <: numtype)) = $sizenn2((Inn_2 : Inn <: numtype)))


  ;; ../specification/wasm-2.0/1-syntax.spectec:325.1-327.57
  syntax cvtop__{Fnn_1 : Fnn, Fnn_2 : Fnn}((Fnn_1 : Fnn <: numtype), (Fnn_2 : Fnn <: numtype)) = 
  | PROMOTE
    -- if ($sizenn1((Fnn_1 : Fnn <: numtype)) < $sizenn2((Fnn_2 : Fnn <: numtype)))
  | DEMOTE
    -- if ($sizenn1((Fnn_1 : Fnn <: numtype)) > $sizenn2((Fnn_2 : Fnn <: numtype)))


;; ../specification/wasm-2.0/1-syntax.spectec:335.1-336.31
syntax ishape = 
  | `%`(shape : shape) {Jnn : Jnn}
    -- if ($lanetype(shape) = (Jnn : Jnn <: lanetype))

;; ../specification/wasm-2.0/1-syntax.spectec:337.1-338.31
syntax fshape = 
  | `%`(shape : shape) {Fnn : Fnn}
    -- if ($lanetype(shape) = (Fnn : Fnn <: lanetype))

;; ../specification/wasm-2.0/1-syntax.spectec:339.1-340.31
syntax pshape = 
  | `%`(shape : shape) {Pnn : Pnn}
    -- if ($lanetype(shape) = (Pnn : packtype <: lanetype))

;; ../specification/wasm-2.0/1-syntax.spectec:342.1-342.22
def $dim(shape : shape) : dim
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:39.1-39.22
  def $dim{Lnn : Lnn, N : N}(`%X%`_shape(Lnn, `%`_dim(N))) = `%`_dim(N)

;; ../specification/wasm-2.0/1-syntax.spectec:343.1-343.41
def $shsize(shape : shape) : nat
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:42.1-42.42
  def $shsize{Lnn : Lnn, N : N}(`%X%`_shape(Lnn, `%`_dim(N))) = ($lsize(Lnn) * N)

;; ../specification/wasm-2.0/1-syntax.spectec:345.1-345.20
syntax vvunop = 
  | NOT

;; ../specification/wasm-2.0/1-syntax.spectec:346.1-346.41
syntax vvbinop = 
  | AND
  | ANDNOT
  | OR
  | XOR

;; ../specification/wasm-2.0/1-syntax.spectec:347.1-347.28
syntax vvternop = 
  | BITSELECT

;; ../specification/wasm-2.0/1-syntax.spectec:348.1-348.27
syntax vvtestop = 
  | ANY_TRUE

;; ../specification/wasm-2.0/1-syntax.spectec:350.1-350.21
syntax vunop_(shape : shape)
  ;; ../specification/wasm-2.0/1-syntax.spectec:351.1-352.26
  syntax vunop_{Jnn : Jnn, N : N}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N))) = 
  | ABS
  | NEG
  | POPCNT
    -- if (Jnn = I8_Jnn)


  ;; ../specification/wasm-2.0/1-syntax.spectec:353.1-353.75
  syntax vunop_{Fnn : Fnn, N : N}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(N))) = 
  | ABS
  | NEG
  | SQRT
  | CEIL
  | FLOOR
  | TRUNC
  | NEAREST


;; ../specification/wasm-2.0/1-syntax.spectec:355.1-355.22
syntax vbinop_(shape : shape)
  ;; ../specification/wasm-2.0/1-syntax.spectec:356.1-365.70
  syntax vbinop_{Jnn : Jnn, N : N}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N))) = 
  | ADD
  | SUB
  | ADD_SAT(sx : sx)
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) <= 16)
  | SUB_SAT(sx : sx)
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) <= 16)
  | MUL
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) >= 16)
  | AVGRU
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) <= 16)
  | Q15MULR_SATS
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) = 16)
  | MIN(sx : sx)
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) <= 32)
  | MAX(sx : sx)
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) <= 32)


  ;; ../specification/wasm-2.0/1-syntax.spectec:366.1-366.74
  syntax vbinop_{Fnn : Fnn, N : N}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(N))) = 
  | ADD
  | SUB
  | MUL
  | DIV
  | MIN
  | MAX
  | PMIN
  | PMAX


;; ../specification/wasm-2.0/1-syntax.spectec:368.1-368.23
syntax vtestop_{Jnn : Jnn, N : N}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N))) = 
  | ALL_TRUE

;; ../specification/wasm-2.0/1-syntax.spectec:372.1-372.22
syntax vrelop_(shape : shape)
  ;; ../specification/wasm-2.0/1-syntax.spectec:373.1-377.49
  syntax vrelop_{Jnn : Jnn, N : N}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N))) = 
  | EQ
  | NE
  | LT(sx : sx)
    -- if (($lsizenn((Jnn : Jnn <: lanetype)) =/= 64) \/ (sx = S_sx))
  | GT(sx : sx)
    -- if (($lsizenn((Jnn : Jnn <: lanetype)) =/= 64) \/ (sx = S_sx))
  | LE(sx : sx)
    -- if (($lsizenn((Jnn : Jnn <: lanetype)) =/= 64) \/ (sx = S_sx))
  | GE(sx : sx)
    -- if (($lsizenn((Jnn : Jnn <: lanetype)) =/= 64) \/ (sx = S_sx))


  ;; ../specification/wasm-2.0/1-syntax.spectec:378.1-378.54
  syntax vrelop_{Fnn : Fnn, N : N}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(N))) = 
  | EQ
  | NE
  | LT
  | GT
  | LE
  | GE


;; ../specification/wasm-2.0/1-syntax.spectec:380.1-380.48
syntax half = 
  | LOW
  | HIGH

;; ../specification/wasm-2.0/1-syntax.spectec:381.1-381.19
syntax zero = 
  | ZERO

;; ../specification/wasm-2.0/1-syntax.spectec:383.1-383.55
syntax vcvtop__(shape_1 : shape, shape_2 : shape)
  ;; ../specification/wasm-2.0/1-syntax.spectec:384.1-386.53
  syntax vcvtop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))) = 
  | EXTEND(half : half, sx : sx)
    -- if ($lsizenn2((Jnn_2 : Jnn <: lanetype)) = (2 * $lsizenn1((Jnn_1 : Jnn <: lanetype))))


  ;; ../specification/wasm-2.0/1-syntax.spectec:387.1-390.67
  syntax vcvtop__{Jnn_1 : Jnn, M_1 : M, Fnn_2 : Fnn, M_2 : M}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2))) = 
  | CONVERT(`half?` : half?, sx : sx)
    -- if (((($sizenn2((Fnn_2 : Fnn <: numtype)) = $lsizenn1((Jnn_1 : Jnn <: lanetype))) /\ ($lsizenn1((Jnn_1 : Jnn <: lanetype)) = 32)) /\ (half?{half <- `half?`} = ?())) \/ (($sizenn2((Fnn_2 : Fnn <: numtype)) = (2 * $lsizenn1((Jnn_1 : Jnn <: lanetype)))) /\ (half?{half <- `half?`} = ?(LOW_half))))


  ;; ../specification/wasm-2.0/1-syntax.spectec:391.1-394.68
  syntax vcvtop__{Fnn_1 : Fnn, M_1 : M, Inn_2 : Inn, M_2 : M}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Inn_2 : Inn <: lanetype), `%`_dim(M_2))) = 
  | TRUNC_SAT(sx : sx, `zero?` : zero?)
    -- if (((($sizenn1((Fnn_1 : Fnn <: numtype)) = $lsizenn2((Inn_2 : Inn <: lanetype))) /\ ($lsizenn2((Inn_2 : Inn <: lanetype)) = 32)) /\ (zero?{zero <- `zero?`} = ?())) \/ (($sizenn1((Fnn_1 : Fnn <: numtype)) = (2 * $lsizenn2((Inn_2 : Inn <: lanetype)))) /\ (zero?{zero <- `zero?`} = ?(ZERO_zero))))


  ;; ../specification/wasm-2.0/1-syntax.spectec:395.1-399.51
  syntax vcvtop__{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2))) = 
  | DEMOTE(zero : zero)
    -- if ($sizenn1((Fnn_1 : Fnn <: numtype)) = (2 * $sizenn2((Fnn_2 : Fnn <: numtype))))
  | PROMOTELOW
    -- if ((2 * $sizenn1((Fnn_1 : Fnn <: numtype))) = $sizenn2((Fnn_2 : Fnn <: numtype)))


;; ../specification/wasm-2.0/1-syntax.spectec:401.1-401.25
syntax vshiftop_{Jnn : Jnn, N : N}(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N)))) = 
  | SHL
  | SHR(sx : sx)

;; ../specification/wasm-2.0/1-syntax.spectec:404.1-404.59
syntax vextunop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)))) = 
  | EXTADD_PAIRWISE(sx : sx)
    -- if ((16 <= (2 * $lsizenn1((Jnn_1 : Jnn <: lanetype)))) /\ (((2 * $lsizenn1((Jnn_1 : Jnn <: lanetype))) = $lsizenn2((Jnn_2 : Jnn <: lanetype))) /\ ($lsizenn2((Jnn_2 : Jnn <: lanetype)) <= 32)))

;; ../specification/wasm-2.0/1-syntax.spectec:408.1-408.60
syntax vextbinop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)))) = 
  | EXTMUL(half : half, sx : sx)
    -- if (((2 * $lsizenn1((Jnn_1 : Jnn <: lanetype))) = $lsizenn2((Jnn_2 : Jnn <: lanetype))) /\ ($lsizenn2((Jnn_2 : Jnn <: lanetype)) >= 16))
  | DOTS
    -- if (((2 * $lsizenn1((Jnn_1 : Jnn <: lanetype))) = $lsizenn2((Jnn_2 : Jnn <: lanetype))) /\ ($lsizenn2((Jnn_2 : Jnn <: lanetype)) = 32))

;; ../specification/wasm-2.0/1-syntax.spectec:418.1-418.69
syntax memarg = 
{
  ALIGN u32,
  OFFSET u32
}

;; ../specification/wasm-2.0/1-syntax.spectec:422.1-422.24
syntax loadop_{Inn : Inn}((Inn : Inn <: numtype)) = 
  | `%_%`(sz : sz, sx : sx)
    -- if (sz!`%`_sz.0 < $sizenn((Inn : Inn <: numtype)))

;; ../specification/wasm-2.0/1-syntax.spectec:425.1-428.61
syntax vloadop_{vectype : vectype}(vectype) = 
  | `SHAPE%X%_%`(sz : sz, M : M, sx : sx)
    -- if ((((sz!`%`_sz.0 * M) : nat <:> rat) = (($vsize(vectype) : nat <:> rat) / (2 : nat <:> rat))) /\ (M > 1))
  | SPLAT(sz : sz)
  | ZERO(sz : sz)
    -- if (sz!`%`_sz.0 >= 32)

;; ../specification/wasm-2.0/1-syntax.spectec:435.1-437.17
syntax blocktype = 
  | _RESULT(`valtype?` : valtype?)
  | _IDX(typeidx : typeidx)

;; ../specification/wasm-2.0/1-syntax.spectec:552.1-553.22
rec {

;; ../specification/wasm-2.0/1-syntax.spectec:552.1-553.22
syntax instr = 
  | NOP
  | UNREACHABLE
  | DROP
  | SELECT(`valtype*?` : valtype*?)
  | BLOCK(blocktype : blocktype, `instr*` : instr*)
  | LOOP(blocktype : blocktype, `instr*` : instr*)
  | `IF%%ELSE%`(blocktype : blocktype, `instr*` : instr*, `instr*` : instr*)
  | BR(labelidx : labelidx)
  | BR_IF(labelidx : labelidx)
  | BR_TABLE(`labelidx*` : labelidx*, labelidx : labelidx)
  | CALL(funcidx : funcidx)
  | CALL_INDIRECT(tableidx : tableidx, typeidx : typeidx)
  | RETURN
  | CONST(numtype : numtype, num_(numtype))
  | UNOP(numtype : numtype, unop_(numtype))
  | BINOP(numtype : numtype, binop_(numtype))
  | TESTOP(numtype : numtype, testop_(numtype))
  | RELOP(numtype : numtype, relop_(numtype))
  | CVTOP(numtype_1 : numtype, numtype_2 : numtype, cvtop__(numtype_2, numtype_1))
    -- if (numtype_1 =/= numtype_2)
  | EXTEND(numtype : numtype, n : n)
  | VCONST(vectype : vectype, vec_(vectype))
  | VVUNOP(vectype : vectype, vvunop : vvunop)
  | VVBINOP(vectype : vectype, vvbinop : vvbinop)
  | VVTERNOP(vectype : vectype, vvternop : vvternop)
  | VVTESTOP(vectype : vectype, vvtestop : vvtestop)
  | VUNOP(shape : shape, vunop_(shape))
  | VBINOP(shape : shape, vbinop_(shape))
  | VTESTOP(shape : shape, vtestop_(shape))
  | VRELOP(shape : shape, vrelop_(shape))
  | VSHIFTOP(ishape : ishape, vshiftop_(ishape))
  | VBITMASK(ishape : ishape)
  | VSWIZZLE(ishape : ishape)
    -- if (ishape = `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))))
  | VSHUFFLE(ishape : ishape, `laneidx*` : laneidx*)
    -- if ((ishape = `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16)))) /\ (|laneidx*{laneidx <- `laneidx*`}| = 16))
  | VSPLAT(shape : shape)
  | VEXTRACT_LANE(shape : shape, `sx?` : sx?, laneidx : laneidx)
    -- if (($lanetype(shape) <- [I32_lanetype I64_lanetype F32_lanetype F64_lanetype]) <=> (sx?{sx <- `sx?`} = ?()))
  | VREPLACE_LANE(shape : shape, laneidx : laneidx)
  | VEXTUNOP(ishape_1 : ishape, ishape_2 : ishape, vextunop__(ishape_2, ishape_1))
  | VEXTBINOP(ishape_1 : ishape, ishape_2 : ishape, vextbinop__(ishape_2, ishape_1))
  | VNARROW(ishape_1 : ishape, ishape_2 : ishape, sx : sx)
    -- if (($lsize($lanetype(ishape_2!`%`_ishape.0)) = (2 * $lsize($lanetype(ishape_1!`%`_ishape.0)))) /\ ((2 * $lsize($lanetype(ishape_1!`%`_ishape.0))) <= 32))
  | VCVTOP(shape_1 : shape, shape_2 : shape, vcvtop__(shape_2, shape_1))
  | `REF.NULL`(reftype : reftype)
  | `REF.FUNC`(funcidx : funcidx)
  | `REF.IS_NULL`
  | `LOCAL.GET`(localidx : localidx)
  | `LOCAL.SET`(localidx : localidx)
  | `LOCAL.TEE`(localidx : localidx)
  | `GLOBAL.GET`(globalidx : globalidx)
  | `GLOBAL.SET`(globalidx : globalidx)
  | `TABLE.GET`(tableidx : tableidx)
  | `TABLE.SET`(tableidx : tableidx)
  | `TABLE.SIZE`(tableidx : tableidx)
  | `TABLE.GROW`(tableidx : tableidx)
  | `TABLE.FILL`(tableidx : tableidx)
  | `TABLE.COPY`(tableidx : tableidx, tableidx : tableidx)
  | `TABLE.INIT`(tableidx : tableidx, elemidx : elemidx)
  | `ELEM.DROP`(elemidx : elemidx)
  | LOAD(numtype : numtype, loadop_(numtype)?, memarg : memarg)
  | STORE(numtype : numtype, `sz?` : sz?, memarg : memarg) {`Inn?` : Inn?}
    -- (if ((numtype = (Inn : Inn <: numtype)) /\ (sz!`%`_sz.0 < $sizenn((Inn : Inn <: numtype)))))?{Inn <- `Inn?`, sz <- `sz?`}
  | VLOAD(vectype : vectype, vloadop_(vectype)?, memarg : memarg)
  | VLOAD_LANE(vectype : vectype, sz : sz, memarg : memarg, laneidx : laneidx)
  | VSTORE(vectype : vectype, memarg : memarg)
  | VSTORE_LANE(vectype : vectype, sz : sz, memarg : memarg, laneidx : laneidx)
  | `MEMORY.SIZE`
  | `MEMORY.GROW`
  | `MEMORY.FILL`
  | `MEMORY.COPY`
  | `MEMORY.INIT`(dataidx : dataidx)
  | `DATA.DROP`(dataidx : dataidx)
}

;; ../specification/wasm-2.0/1-syntax.spectec:556.1-557.9
syntax expr = instr*

;; ../specification/wasm-2.0/1-syntax.spectec:569.1-569.59
syntax elemmode = 
  | ACTIVE(tableidx : tableidx, expr : expr)
  | PASSIVE
  | DECLARE

;; ../specification/wasm-2.0/1-syntax.spectec:570.1-570.47
syntax datamode = 
  | ACTIVE(memidx : memidx, expr : expr)
  | PASSIVE

;; ../specification/wasm-2.0/1-syntax.spectec:572.1-573.16
syntax type = 
  | TYPE(functype : functype)

;; ../specification/wasm-2.0/1-syntax.spectec:574.1-575.16
syntax local = 
  | LOCAL(valtype : valtype)

;; ../specification/wasm-2.0/1-syntax.spectec:576.1-577.27
syntax func = 
  | FUNC(typeidx : typeidx, `local*` : local*, expr : expr)

;; ../specification/wasm-2.0/1-syntax.spectec:578.1-579.25
syntax global = 
  | GLOBAL(globaltype : globaltype, expr : expr)

;; ../specification/wasm-2.0/1-syntax.spectec:580.1-581.18
syntax table = 
  | TABLE(tabletype : tabletype)

;; ../specification/wasm-2.0/1-syntax.spectec:582.1-583.17
syntax mem = 
  | MEMORY(memtype : memtype)

;; ../specification/wasm-2.0/1-syntax.spectec:584.1-585.30
syntax elem = 
  | ELEM(reftype : reftype, `expr*` : expr*, elemmode : elemmode)

;; ../specification/wasm-2.0/1-syntax.spectec:586.1-587.22
syntax data = 
  | DATA(`byte*` : byte*, datamode : datamode)

;; ../specification/wasm-2.0/1-syntax.spectec:588.1-589.16
syntax start = 
  | START(funcidx : funcidx)

;; ../specification/wasm-2.0/1-syntax.spectec:591.1-592.66
syntax externidx = 
  | FUNC(funcidx : funcidx)
  | GLOBAL(globalidx : globalidx)
  | TABLE(tableidx : tableidx)
  | MEM(memidx : memidx)

;; ../specification/wasm-2.0/1-syntax.spectec:593.1-594.24
syntax export = 
  | EXPORT(name : name, externidx : externidx)

;; ../specification/wasm-2.0/1-syntax.spectec:595.1-596.30
syntax import = 
  | IMPORT(name : name, name : name, externtype : externtype)

;; ../specification/wasm-2.0/1-syntax.spectec:598.1-599.76
syntax module = 
  | MODULE(`type*` : type*, `import*` : import*, `func*` : func*, `global*` : global*, `table*` : table*, `mem*` : mem*, `elem*` : elem*, `data*` : data*, `start?` : start?, `export*` : export*)

;; ../specification/wasm-2.0/2-syntax-aux.spectec:7.1-7.59
rec {

;; ../specification/wasm-2.0/2-syntax-aux.spectec:7.1-7.59
def $concat_bytes(byte**) : byte*
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:8.1-8.29
  def $concat_bytes([]) = []
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:9.1-9.58
  def $concat_bytes{`b*` : byte*, `b'**` : byte**}([b*{b <- `b*`}] ++ b'*{b' <- `b'*`}*{`b'*` <- `b'**`}) = b*{b <- `b*`} ++ $concat_bytes(b'*{b' <- `b'*`}*{`b'*` <- `b'**`})
}

;; ../specification/wasm-2.0/2-syntax-aux.spectec:28.1-28.32
def $unpack(lanetype : lanetype) : numtype
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:29.1-29.31
  def $unpack{numtype : numtype}((numtype : numtype <: lanetype)) = numtype
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:30.1-30.28
  def $unpack{packtype : packtype}((packtype : packtype <: lanetype)) = I32_numtype

;; ../specification/wasm-2.0/2-syntax-aux.spectec:44.1-44.54
def $shunpack(shape : shape) : numtype
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:45.1-45.38
  def $shunpack{Lnn : Lnn, N : N}(`%X%`_shape(Lnn, `%`_dim(N))) = $unpack(Lnn)

;; ../specification/wasm-2.0/2-syntax-aux.spectec:51.1-51.64
rec {

;; ../specification/wasm-2.0/2-syntax-aux.spectec:51.1-51.64
def $funcsxt(externtype*) : functype*
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:56.1-56.24
  def $funcsxt([]) = []
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:57.1-57.47
  def $funcsxt{ft : functype, `xt*` : externtype*}([FUNC_externtype(ft)] ++ xt*{xt <- `xt*`}) = [ft] ++ $funcsxt(xt*{xt <- `xt*`})
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:58.1-58.59
  def $funcsxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $funcsxt(xt*{xt <- `xt*`})
    -- otherwise
}

;; ../specification/wasm-2.0/2-syntax-aux.spectec:52.1-52.66
rec {

;; ../specification/wasm-2.0/2-syntax-aux.spectec:52.1-52.66
def $globalsxt(externtype*) : globaltype*
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:60.1-60.26
  def $globalsxt([]) = []
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:61.1-61.53
  def $globalsxt{gt : globaltype, `xt*` : externtype*}([GLOBAL_externtype(gt)] ++ xt*{xt <- `xt*`}) = [gt] ++ $globalsxt(xt*{xt <- `xt*`})
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:62.1-62.63
  def $globalsxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $globalsxt(xt*{xt <- `xt*`})
    -- otherwise
}

;; ../specification/wasm-2.0/2-syntax-aux.spectec:53.1-53.65
rec {

;; ../specification/wasm-2.0/2-syntax-aux.spectec:53.1-53.65
def $tablesxt(externtype*) : tabletype*
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:64.1-64.25
  def $tablesxt([]) = []
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:65.1-65.50
  def $tablesxt{tt : tabletype, `xt*` : externtype*}([TABLE_externtype(tt)] ++ xt*{xt <- `xt*`}) = [tt] ++ $tablesxt(xt*{xt <- `xt*`})
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:66.1-66.61
  def $tablesxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $tablesxt(xt*{xt <- `xt*`})
    -- otherwise
}

;; ../specification/wasm-2.0/2-syntax-aux.spectec:54.1-54.63
rec {

;; ../specification/wasm-2.0/2-syntax-aux.spectec:54.1-54.63
def $memsxt(externtype*) : memtype*
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:68.1-68.23
  def $memsxt([]) = []
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:69.1-69.44
  def $memsxt{mt : memtype, `xt*` : externtype*}([MEM_externtype(mt)] ++ xt*{xt <- `xt*`}) = [mt] ++ $memsxt(xt*{xt <- `xt*`})
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:70.1-70.57
  def $memsxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $memsxt(xt*{xt <- `xt*`})
    -- otherwise
}

;; ../specification/wasm-2.0/2-syntax-aux.spectec:80.1-80.61
def $dataidx_instr(instr : instr) : dataidx*
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:81.1-81.38
  def $dataidx_instr{x : idx}(`MEMORY.INIT`_instr(x)) = [x]
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:82.1-82.36
  def $dataidx_instr{x : idx}(`DATA.DROP`_instr(x)) = [x]
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:83.1-83.29
  def $dataidx_instr{in : instr}(in) = []

;; ../specification/wasm-2.0/2-syntax-aux.spectec:85.1-85.63
rec {

;; ../specification/wasm-2.0/2-syntax-aux.spectec:85.1-85.63
def $dataidx_instrs(instr*) : dataidx*
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:86.1-86.31
  def $dataidx_instrs([]) = []
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:87.1-87.84
  def $dataidx_instrs{instr : instr, `instr'*` : instr*}([instr] ++ instr'*{instr' <- `instr'*`}) = $dataidx_instr(instr) ++ $dataidx_instrs(instr'*{instr' <- `instr'*`})
}

;; ../specification/wasm-2.0/2-syntax-aux.spectec:89.1-89.59
def $dataidx_expr(expr : expr) : dataidx*
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:90.1-90.46
  def $dataidx_expr{`in*` : instr*}(in*{in <- `in*`}) = $dataidx_instrs(in*{in <- `in*`})

;; ../specification/wasm-2.0/2-syntax-aux.spectec:92.1-92.59
def $dataidx_func(func : func) : dataidx*
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:93.1-93.52
  def $dataidx_func{x : idx, `loc*` : local*, e : expr}(FUNC_func(x, loc*{loc <- `loc*`}, e)) = $dataidx_expr(e)

;; ../specification/wasm-2.0/2-syntax-aux.spectec:95.1-95.61
rec {

;; ../specification/wasm-2.0/2-syntax-aux.spectec:95.1-95.61
def $dataidx_funcs(func*) : dataidx*
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:96.1-96.30
  def $dataidx_funcs([]) = []
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:97.1-97.77
  def $dataidx_funcs{func : func, `func'*` : func*}([func] ++ func'*{func' <- `func'*`}) = $dataidx_func(func) ++ $dataidx_funcs(func'*{func' <- `func'*`})
}

;; ../specification/wasm-2.0/2-syntax-aux.spectec:106.1-106.35
def $memarg0 : memarg
  ;; ../specification/wasm-2.0/2-syntax-aux.spectec:107.1-107.35
  def $memarg0 = {ALIGN `%`_u32(0), OFFSET `%`_u32(0)}

;; ../specification/wasm-2.0/3-numerics.spectec:7.1-7.41
def $s33_to_u32(s33 : s33) : u32

;; ../specification/wasm-2.0/3-numerics.spectec:9.1-9.22
def $bool(bool : bool) : nat
  ;; ../specification/wasm-2.0/3-numerics.spectec:10.1-10.21
  def $bool(false) = 0
  ;; ../specification/wasm-2.0/3-numerics.spectec:11.1-11.20
  def $bool(true) = 1

;; ../specification/wasm-2.0/3-numerics.spectec:13.1-13.23
def $truncz(rat : rat) : int

;; ../specification/wasm-2.0/3-numerics.spectec:20.1-20.54
def $signed_(N : N, nat : nat) : int
  ;; ../specification/wasm-2.0/3-numerics.spectec:21.1-21.54
  def $signed_{N : N, i : nat}(N, i) = (i : nat <:> int)
    -- if (i < (2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))
  ;; ../specification/wasm-2.0/3-numerics.spectec:22.1-22.61
  def $signed_{N : N, i : nat}(N, i) = ((i : nat <:> int) - ((2 ^ N) : nat <:> int))
    -- if (((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) <= i) /\ (i < (2 ^ N)))

;; ../specification/wasm-2.0/3-numerics.spectec:24.1-24.70
def $inv_signed_(N : N, int : int) : nat
  ;; ../specification/wasm-2.0/3-numerics.spectec:25.1-25.62
  def $inv_signed_{N : N, i : int}(N, i) = (i : int <:> nat)
    -- if (((0 : nat <:> int) <= i) /\ (i < ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)))
  ;; ../specification/wasm-2.0/3-numerics.spectec:26.1-26.63
  def $inv_signed_{N : N, i : int}(N, i) = ((i + ((2 ^ N) : nat <:> int)) : int <:> nat)
    -- if ((- ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) <= i) /\ (i < (0 : nat <:> int)))

;; ../specification/wasm-2.0/3-numerics.spectec:31.1-31.61
def $sat_u_(N : N, int : int) : nat
  ;; ../specification/wasm-2.0/3-numerics.spectec:32.1-32.48
  def $sat_u_{N : N, i : int}(N, i) = 0
    -- if (i < (0 : nat <:> int))
  ;; ../specification/wasm-2.0/3-numerics.spectec:33.1-33.57
  def $sat_u_{N : N, i : int}(N, i) = ((((2 ^ N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)
    -- if (i > (((2 ^ N) : nat <:> int) - (1 : nat <:> int)))
  ;; ../specification/wasm-2.0/3-numerics.spectec:34.1-34.49
  def $sat_u_{N : N, i : int}(N, i) = (i : int <:> nat)
    -- otherwise

;; ../specification/wasm-2.0/3-numerics.spectec:36.1-36.61
def $sat_s_(N : N, int : int) : int
  ;; ../specification/wasm-2.0/3-numerics.spectec:37.1-37.58
  def $sat_s_{N : N, i : int}(N, i) = - ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)
    -- if (i < - ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int))
  ;; ../specification/wasm-2.0/3-numerics.spectec:38.1-38.61
  def $sat_s_{N : N, i : int}(N, i) = (((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int))
    -- if (i > (((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))
  ;; ../specification/wasm-2.0/3-numerics.spectec:39.1-39.49
  def $sat_s_{N : N, i : int}(N, i) = i
    -- otherwise

;; ../specification/wasm-2.0/3-numerics.spectec:56.1-56.89
def $extend__(M : M, N : N, sx : sx, iN : iN(M)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:224.1-224.30
def $fabs_(N : N, fN : fN(N)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:227.1-227.31
def $fceil_(N : N, fN : fN(N)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:228.1-228.32
def $ffloor_(N : N, fN : fN(N)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:230.1-230.34
def $fnearest_(N : N, fN : fN(N)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:225.1-225.30
def $fneg_(N : N, fN : fN(N)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:226.1-226.31
def $fsqrt_(N : N, fN : fN(N)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:229.1-229.32
def $ftrunc_(N : N, fN : fN(N)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:120.1-120.29
def $iclz_(N : N, iN : iN(N)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:121.1-121.29
def $ictz_(N : N, iN : iN(N)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:122.1-122.32
def $ipopcnt_(N : N, iN : iN(N)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:55.1-55.33
def $wrap__(M : M, N : N, iN : iN(M)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:44.1-45.32
def $unop_(numtype : numtype, unop_ : unop_(numtype), num_ : num_(numtype)) : num_(numtype)*
  ;; ../specification/wasm-2.0/3-numerics.spectec:275.1-275.52
  def $unop_{Inn : Inn, iN : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), CLZ_unop_, iN) = [$iclz_($sizenn((Inn : Inn <: numtype)), iN)]
  ;; ../specification/wasm-2.0/3-numerics.spectec:276.1-276.52
  def $unop_{Inn : Inn, iN : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), CTZ_unop_, iN) = [$ictz_($sizenn((Inn : Inn <: numtype)), iN)]
  ;; ../specification/wasm-2.0/3-numerics.spectec:277.1-277.58
  def $unop_{Inn : Inn, iN : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), POPCNT_unop_, iN) = [$ipopcnt_($sizenn((Inn : Inn <: numtype)), iN)]
  ;; ../specification/wasm-2.0/3-numerics.spectec:278.1-278.92
  def $unop_{Inn : Inn, M : M, iN : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), EXTEND_unop_(M), iN) = [$extend__(M, $sizenn((Inn : Inn <: numtype)), S_sx, $wrap__($sizenn((Inn : Inn <: numtype)), M, iN))]
  ;; ../specification/wasm-2.0/3-numerics.spectec:295.1-295.52
  def $unop_{Fnn : Fnn, fN : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), ABS_unop_, fN) = $fabs_($sizenn((Fnn : Fnn <: numtype)), fN)
  ;; ../specification/wasm-2.0/3-numerics.spectec:296.1-296.52
  def $unop_{Fnn : Fnn, fN : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), NEG_unop_, fN) = $fneg_($sizenn((Fnn : Fnn <: numtype)), fN)
  ;; ../specification/wasm-2.0/3-numerics.spectec:297.1-297.54
  def $unop_{Fnn : Fnn, fN : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), SQRT_unop_, fN) = $fsqrt_($sizenn((Fnn : Fnn <: numtype)), fN)
  ;; ../specification/wasm-2.0/3-numerics.spectec:298.1-298.54
  def $unop_{Fnn : Fnn, fN : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), CEIL_unop_, fN) = $fceil_($sizenn((Fnn : Fnn <: numtype)), fN)
  ;; ../specification/wasm-2.0/3-numerics.spectec:299.1-299.56
  def $unop_{Fnn : Fnn, fN : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), FLOOR_unop_, fN) = $ffloor_($sizenn((Fnn : Fnn <: numtype)), fN)
  ;; ../specification/wasm-2.0/3-numerics.spectec:300.1-300.56
  def $unop_{Fnn : Fnn, fN : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), TRUNC_unop_, fN) = $ftrunc_($sizenn((Fnn : Fnn <: numtype)), fN)
  ;; ../specification/wasm-2.0/3-numerics.spectec:301.1-301.60
  def $unop_{Fnn : Fnn, fN : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), NEAREST_unop_, fN) = $fnearest_($sizenn((Fnn : Fnn <: numtype)), fN)

;; ../specification/wasm-2.0/3-numerics.spectec:215.1-215.37
def $fadd_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:223.1-223.42
def $fcopysign_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:218.1-218.37
def $fdiv_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:220.1-220.37
def $fmax_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:219.1-219.37
def $fmin_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:217.1-217.37
def $fmul_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:216.1-216.37
def $fsub_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:105.1-105.36
def $iadd_(N : N, iN : iN(N), iN : iN(N)) : iN(N)
  ;; ../specification/wasm-2.0/3-numerics.spectec:141.1-141.47
  def $iadd_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, i_1, i_2) = `%`_iN(((i_1!`%`_iN.0 + i_2!`%`_iN.0) \ (2 ^ N)))

;; ../specification/wasm-2.0/3-numerics.spectec:112.1-112.36
def $iand_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:108.1-108.74
def $idiv_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)?
  ;; ../specification/wasm-2.0/3-numerics.spectec:145.1-145.33
  def $idiv_{N : N, i_1 : iN(N)}(N, U_sx, i_1, `%`_iN(0)) = ?()
  ;; ../specification/wasm-2.0/3-numerics.spectec:146.1-146.51
  def $idiv_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = ?(`%`_iN(($truncz(((i_1!`%`_iN.0 : nat <:> rat) / (i_2!`%`_iN.0 : nat <:> rat))) : int <:> nat)))
  ;; ../specification/wasm-2.0/3-numerics.spectec:147.1-147.33
  def $idiv_{N : N, i_1 : iN(N)}(N, S_sx, i_1, `%`_iN(0)) = ?()
  ;; ../specification/wasm-2.0/3-numerics.spectec:148.1-148.96
  def $idiv_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = ?()
    -- if ((($signed_(N, i_1!`%`_iN.0) : int <:> rat) / ($signed_(N, i_2!`%`_iN.0) : int <:> rat)) = ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> rat))
  ;; ../specification/wasm-2.0/3-numerics.spectec:149.1-149.94
  def $idiv_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = ?(`%`_iN($inv_signed_(N, $truncz((($signed_(N, i_1!`%`_iN.0) : int <:> rat) / ($signed_(N, i_2!`%`_iN.0) : int <:> rat))))))

;; ../specification/wasm-2.0/3-numerics.spectec:107.1-107.36
def $imul_(N : N, iN : iN(N), iN : iN(N)) : iN(N)
  ;; ../specification/wasm-2.0/3-numerics.spectec:143.1-143.47
  def $imul_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, i_1, i_2) = `%`_iN(((i_1!`%`_iN.0 * i_2!`%`_iN.0) \ (2 ^ N)))

;; ../specification/wasm-2.0/3-numerics.spectec:114.1-114.35
def $ior_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:109.1-109.74
def $irem_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)?
  ;; ../specification/wasm-2.0/3-numerics.spectec:151.1-151.33
  def $irem_{N : N, i_1 : iN(N)}(N, U_sx, i_1, `%`_iN(0)) = ?()
  ;; ../specification/wasm-2.0/3-numerics.spectec:152.1-152.66
  def $irem_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = ?(`%`_iN((((i_1!`%`_iN.0 : nat <:> int) - ((i_2!`%`_iN.0 * ($truncz(((i_1!`%`_iN.0 : nat <:> rat) / (i_2!`%`_iN.0 : nat <:> rat))) : int <:> nat)) : nat <:> int)) : int <:> nat)))
  ;; ../specification/wasm-2.0/3-numerics.spectec:153.1-153.33
  def $irem_{N : N, i_1 : iN(N)}(N, S_sx, i_1, `%`_iN(0)) = ?()
  ;; ../specification/wasm-2.0/3-numerics.spectec:154.1-155.84
  def $irem_{N : N, i_1 : iN(N), i_2 : iN(N), j_1 : int, j_2 : int}(N, S_sx, i_1, i_2) = ?(`%`_iN($inv_signed_(N, (j_1 - (j_2 * $truncz(((j_1 : int <:> rat) / (j_2 : int <:> rat))))))))
    -- if ((j_1 = $signed_(N, i_1!`%`_iN.0)) /\ (j_2 = $signed_(N, i_2!`%`_iN.0)))

;; ../specification/wasm-2.0/3-numerics.spectec:118.1-118.37
def $irotl_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:119.1-119.37
def $irotr_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:116.1-116.36
def $ishl_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:117.1-117.76
def $ishr_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:106.1-106.36
def $isub_(N : N, iN : iN(N), iN : iN(N)) : iN(N)
  ;; ../specification/wasm-2.0/3-numerics.spectec:142.1-142.53
  def $isub_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, i_1, i_2) = `%`_iN(((((((2 ^ N) + i_1!`%`_iN.0) : nat <:> int) - (i_2!`%`_iN.0 : nat <:> int)) \ ((2 ^ N) : nat <:> int)) : int <:> nat))

;; ../specification/wasm-2.0/3-numerics.spectec:115.1-115.36
def $ixor_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:46.1-47.34
def $binop_(numtype : numtype, binop_ : binop_(numtype), num_ : num_(numtype), num_ : num_(numtype)) : num_(numtype)*
  ;; ../specification/wasm-2.0/3-numerics.spectec:263.1-263.69
  def $binop_{Inn : Inn, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), ADD_binop_, iN_1, iN_2) = [$iadd_($sizenn((Inn : Inn <: numtype)), iN_1, iN_2)]
  ;; ../specification/wasm-2.0/3-numerics.spectec:264.1-264.69
  def $binop_{Inn : Inn, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), SUB_binop_, iN_1, iN_2) = [$isub_($sizenn((Inn : Inn <: numtype)), iN_1, iN_2)]
  ;; ../specification/wasm-2.0/3-numerics.spectec:265.1-265.69
  def $binop_{Inn : Inn, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), MUL_binop_, iN_1, iN_2) = [$imul_($sizenn((Inn : Inn <: numtype)), iN_1, iN_2)]
  ;; ../specification/wasm-2.0/3-numerics.spectec:266.1-266.95
  def $binop_{Inn : Inn, sx : sx, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), DIV_binop_(sx), iN_1, iN_2) = $list_(syntax num_((Inn : Inn <: numtype)), $idiv_($sizenn((Inn : Inn <: numtype)), sx, iN_1, iN_2))
  ;; ../specification/wasm-2.0/3-numerics.spectec:267.1-267.95
  def $binop_{Inn : Inn, sx : sx, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), REM_binop_(sx), iN_1, iN_2) = $list_(syntax num_((Inn : Inn <: numtype)), $irem_($sizenn((Inn : Inn <: numtype)), sx, iN_1, iN_2))
  ;; ../specification/wasm-2.0/3-numerics.spectec:268.1-268.69
  def $binop_{Inn : Inn, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), AND_binop_, iN_1, iN_2) = [$iand_($sizenn((Inn : Inn <: numtype)), iN_1, iN_2)]
  ;; ../specification/wasm-2.0/3-numerics.spectec:269.1-269.67
  def $binop_{Inn : Inn, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), OR_binop_, iN_1, iN_2) = [$ior_($sizenn((Inn : Inn <: numtype)), iN_1, iN_2)]
  ;; ../specification/wasm-2.0/3-numerics.spectec:270.1-270.69
  def $binop_{Inn : Inn, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), XOR_binop_, iN_1, iN_2) = [$ixor_($sizenn((Inn : Inn <: numtype)), iN_1, iN_2)]
  ;; ../specification/wasm-2.0/3-numerics.spectec:271.1-271.69
  def $binop_{Inn : Inn, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), SHL_binop_, iN_1, iN_2) = [$ishl_($sizenn((Inn : Inn <: numtype)), iN_1, iN_2)]
  ;; ../specification/wasm-2.0/3-numerics.spectec:272.1-272.76
  def $binop_{Inn : Inn, sx : sx, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), SHR_binop_(sx), iN_1, iN_2) = [$ishr_($sizenn((Inn : Inn <: numtype)), sx, iN_1, iN_2)]
  ;; ../specification/wasm-2.0/3-numerics.spectec:273.1-273.71
  def $binop_{Inn : Inn, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), ROTL_binop_, iN_1, iN_2) = [$irotl_($sizenn((Inn : Inn <: numtype)), iN_1, iN_2)]
  ;; ../specification/wasm-2.0/3-numerics.spectec:274.1-274.71
  def $binop_{Inn : Inn, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), ROTR_binop_, iN_1, iN_2) = [$irotr_($sizenn((Inn : Inn <: numtype)), iN_1, iN_2)]
  ;; ../specification/wasm-2.0/3-numerics.spectec:287.1-287.69
  def $binop_{Fnn : Fnn, fN_1 : num_((Fnn : Fnn <: numtype)), fN_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), ADD_binop_, fN_1, fN_2) = $fadd_($sizenn((Fnn : Fnn <: numtype)), fN_1, fN_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:288.1-288.69
  def $binop_{Fnn : Fnn, fN_1 : num_((Fnn : Fnn <: numtype)), fN_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), SUB_binop_, fN_1, fN_2) = $fsub_($sizenn((Fnn : Fnn <: numtype)), fN_1, fN_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:289.1-289.69
  def $binop_{Fnn : Fnn, fN_1 : num_((Fnn : Fnn <: numtype)), fN_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), MUL_binop_, fN_1, fN_2) = $fmul_($sizenn((Fnn : Fnn <: numtype)), fN_1, fN_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:290.1-290.69
  def $binop_{Fnn : Fnn, fN_1 : num_((Fnn : Fnn <: numtype)), fN_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), DIV_binop_, fN_1, fN_2) = $fdiv_($sizenn((Fnn : Fnn <: numtype)), fN_1, fN_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:291.1-291.69
  def $binop_{Fnn : Fnn, fN_1 : num_((Fnn : Fnn <: numtype)), fN_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), MIN_binop_, fN_1, fN_2) = $fmin_($sizenn((Fnn : Fnn <: numtype)), fN_1, fN_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:292.1-292.69
  def $binop_{Fnn : Fnn, fN_1 : num_((Fnn : Fnn <: numtype)), fN_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), MAX_binop_, fN_1, fN_2) = $fmax_($sizenn((Fnn : Fnn <: numtype)), fN_1, fN_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:293.1-293.79
  def $binop_{Fnn : Fnn, fN_1 : num_((Fnn : Fnn <: numtype)), fN_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), COPYSIGN_binop_, fN_1, fN_2) = $fcopysign_($sizenn((Fnn : Fnn <: numtype)), fN_1, fN_2)

;; ../specification/wasm-2.0/3-numerics.spectec:123.1-123.27
def $ieqz_(N : N, iN : iN(N)) : u32
  ;; ../specification/wasm-2.0/3-numerics.spectec:171.1-171.36
  def $ieqz_{N : N, i_1 : iN(N)}(N, i_1) = `%`_u32($bool((i_1!`%`_iN.0 = 0)))

;; ../specification/wasm-2.0/3-numerics.spectec:48.1-49.32
def $testop_(numtype : numtype, testop_ : testop_(numtype), num_ : num_(numtype)) : num_(I32_numtype)
  ;; ../specification/wasm-2.0/3-numerics.spectec:279.1-279.54
  def $testop_{Inn : Inn, iN : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), EQZ_testop_, iN) = $ieqz_($sizenn((Inn : Inn <: numtype)), iN)

;; ../specification/wasm-2.0/3-numerics.spectec:231.1-231.33
def $feq_(N : N, fN : fN(N), fN : fN(N)) : u32

;; ../specification/wasm-2.0/3-numerics.spectec:236.1-236.33
def $fge_(N : N, fN : fN(N), fN : fN(N)) : u32

;; ../specification/wasm-2.0/3-numerics.spectec:234.1-234.33
def $fgt_(N : N, fN : fN(N), fN : fN(N)) : u32

;; ../specification/wasm-2.0/3-numerics.spectec:235.1-235.33
def $fle_(N : N, fN : fN(N), fN : fN(N)) : u32

;; ../specification/wasm-2.0/3-numerics.spectec:233.1-233.33
def $flt_(N : N, fN : fN(N), fN : fN(N)) : u32

;; ../specification/wasm-2.0/3-numerics.spectec:232.1-232.33
def $fne_(N : N, fN : fN(N), fN : fN(N)) : u32

;; ../specification/wasm-2.0/3-numerics.spectec:125.1-125.33
def $ieq_(N : N, iN : iN(N), iN : iN(N)) : u32
  ;; ../specification/wasm-2.0/3-numerics.spectec:174.1-174.42
  def $ieq_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, i_1, i_2) = `%`_u32($bool((i_1 = i_2)))

;; ../specification/wasm-2.0/3-numerics.spectec:130.1-130.73
def $ige_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : u32
  ;; ../specification/wasm-2.0/3-numerics.spectec:186.1-186.46
  def $ige_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_iN.0 >= i_2!`%`_iN.0)))
  ;; ../specification/wasm-2.0/3-numerics.spectec:187.1-187.72
  def $ige_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_iN.0) >= $signed_(N, i_2!`%`_iN.0))))

;; ../specification/wasm-2.0/3-numerics.spectec:128.1-128.73
def $igt_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : u32
  ;; ../specification/wasm-2.0/3-numerics.spectec:180.1-180.45
  def $igt_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_iN.0 > i_2!`%`_iN.0)))
  ;; ../specification/wasm-2.0/3-numerics.spectec:181.1-181.71
  def $igt_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_iN.0) > $signed_(N, i_2!`%`_iN.0))))

;; ../specification/wasm-2.0/3-numerics.spectec:129.1-129.73
def $ile_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : u32
  ;; ../specification/wasm-2.0/3-numerics.spectec:183.1-183.46
  def $ile_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_iN.0 <= i_2!`%`_iN.0)))
  ;; ../specification/wasm-2.0/3-numerics.spectec:184.1-184.72
  def $ile_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_iN.0) <= $signed_(N, i_2!`%`_iN.0))))

;; ../specification/wasm-2.0/3-numerics.spectec:127.1-127.73
def $ilt_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : u32
  ;; ../specification/wasm-2.0/3-numerics.spectec:177.1-177.45
  def $ilt_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_iN.0 < i_2!`%`_iN.0)))
  ;; ../specification/wasm-2.0/3-numerics.spectec:178.1-178.71
  def $ilt_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_iN.0) < $signed_(N, i_2!`%`_iN.0))))

;; ../specification/wasm-2.0/3-numerics.spectec:126.1-126.33
def $ine_(N : N, iN : iN(N), iN : iN(N)) : u32
  ;; ../specification/wasm-2.0/3-numerics.spectec:175.1-175.44
  def $ine_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, i_1, i_2) = `%`_u32($bool((i_1 =/= i_2)))

;; ../specification/wasm-2.0/3-numerics.spectec:50.1-51.34
def $relop_(numtype : numtype, relop_ : relop_(numtype), num_ : num_(numtype), num_ : num_(numtype)) : num_(I32_numtype)
  ;; ../specification/wasm-2.0/3-numerics.spectec:280.1-280.67
  def $relop_{Inn : Inn, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), EQ_relop_, iN_1, iN_2) = $ieq_($sizenn((Inn : Inn <: numtype)), iN_1, iN_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:281.1-281.67
  def $relop_{Inn : Inn, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), NE_relop_, iN_1, iN_2) = $ine_($sizenn((Inn : Inn <: numtype)), iN_1, iN_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:282.1-282.74
  def $relop_{Inn : Inn, sx : sx, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), LT_relop_(sx), iN_1, iN_2) = $ilt_($sizenn((Inn : Inn <: numtype)), sx, iN_1, iN_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:283.1-283.74
  def $relop_{Inn : Inn, sx : sx, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), GT_relop_(sx), iN_1, iN_2) = $igt_($sizenn((Inn : Inn <: numtype)), sx, iN_1, iN_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:284.1-284.74
  def $relop_{Inn : Inn, sx : sx, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), LE_relop_(sx), iN_1, iN_2) = $ile_($sizenn((Inn : Inn <: numtype)), sx, iN_1, iN_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:285.1-285.74
  def $relop_{Inn : Inn, sx : sx, iN_1 : num_((Inn : Inn <: numtype)), iN_2 : num_((Inn : Inn <: numtype))}((Inn : Inn <: numtype), GE_relop_(sx), iN_1, iN_2) = $ige_($sizenn((Inn : Inn <: numtype)), sx, iN_1, iN_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:303.1-303.67
  def $relop_{Fnn : Fnn, fN_1 : num_((Fnn : Fnn <: numtype)), fN_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), EQ_relop_, fN_1, fN_2) = $feq_($sizenn((Fnn : Fnn <: numtype)), fN_1, fN_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:304.1-304.67
  def $relop_{Fnn : Fnn, fN_1 : num_((Fnn : Fnn <: numtype)), fN_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), NE_relop_, fN_1, fN_2) = $fne_($sizenn((Fnn : Fnn <: numtype)), fN_1, fN_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:305.1-305.67
  def $relop_{Fnn : Fnn, fN_1 : num_((Fnn : Fnn <: numtype)), fN_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), LT_relop_, fN_1, fN_2) = $flt_($sizenn((Fnn : Fnn <: numtype)), fN_1, fN_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:306.1-306.67
  def $relop_{Fnn : Fnn, fN_1 : num_((Fnn : Fnn <: numtype)), fN_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), GT_relop_, fN_1, fN_2) = $fgt_($sizenn((Fnn : Fnn <: numtype)), fN_1, fN_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:307.1-307.67
  def $relop_{Fnn : Fnn, fN_1 : num_((Fnn : Fnn <: numtype)), fN_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), LE_relop_, fN_1, fN_2) = $fle_($sizenn((Fnn : Fnn <: numtype)), fN_1, fN_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:308.1-308.67
  def $relop_{Fnn : Fnn, fN_1 : num_((Fnn : Fnn <: numtype)), fN_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), GE_relop_, fN_1, fN_2) = $fge_($sizenn((Fnn : Fnn <: numtype)), fN_1, fN_2)

;; ../specification/wasm-2.0/3-numerics.spectec:61.1-61.90
def $convert__(M : M, N : N, sx : sx, iN : iN(M)) : fN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:59.1-59.36
def $demote__(M : M, N : N, fN : fN(M)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:60.1-60.37
def $promote__(M : M, N : N, fN : fN(M)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:63.1-63.76
def $reinterpret__(numtype_1 : numtype, numtype_2 : numtype, num_ : num_(numtype_1)) : num_(numtype_2)

;; ../specification/wasm-2.0/3-numerics.spectec:57.1-57.88
def $trunc__(M : M, N : N, sx : sx, fN : fN(M)) : iN(N)?

;; ../specification/wasm-2.0/3-numerics.spectec:58.1-58.93
def $trunc_sat__(M : M, N : N, sx : sx, fN : fN(M)) : iN(N)?

;; ../specification/wasm-2.0/3-numerics.spectec:52.1-53.36
def $cvtop__(numtype_1 : numtype, numtype_2 : numtype, cvtop__ : cvtop__(numtype_1, numtype_2), num_ : num_(numtype_1)) : num_(numtype_2)*
  ;; ../specification/wasm-2.0/3-numerics.spectec:310.1-310.100
  def $cvtop__{Inn_1 : Inn, Inn_2 : Inn, sx : sx, iN_1 : num_((Inn_1 : Inn <: numtype))}((Inn_1 : Inn <: numtype), (Inn_2 : Inn <: numtype), EXTEND_cvtop__(sx), iN_1) = [$extend__($sizenn1((Inn_1 : Inn <: numtype)), $sizenn2((Inn_2 : Inn <: numtype)), sx, iN_1)]
  ;; ../specification/wasm-2.0/3-numerics.spectec:311.1-311.89
  def $cvtop__{Inn_1 : Inn, Inn_2 : Inn, iN_1 : num_((Inn_1 : Inn <: numtype))}((Inn_1 : Inn <: numtype), (Inn_2 : Inn <: numtype), WRAP_cvtop__, iN_1) = [$wrap__($sizenn1((Inn_1 : Inn <: numtype)), $sizenn2((Inn_2 : Inn <: numtype)), iN_1)]
  ;; ../specification/wasm-2.0/3-numerics.spectec:312.1-312.119
  def $cvtop__{Fnn_1 : Fnn, Inn_2 : Inn, sx : sx, fN_1 : num_((Fnn_1 : Fnn <: numtype))}((Fnn_1 : Fnn <: numtype), (Inn_2 : Inn <: numtype), TRUNC_cvtop__(sx), fN_1) = $list_(syntax num_((Inn_2 : Inn <: numtype)), $trunc__($sizenn1((Fnn_1 : Fnn <: numtype)), $sizenn2((Inn_2 : Inn <: numtype)), sx, fN_1))
  ;; ../specification/wasm-2.0/3-numerics.spectec:313.1-313.127
  def $cvtop__{Fnn_1 : Fnn, Inn_2 : Inn, sx : sx, fN_1 : num_((Fnn_1 : Fnn <: numtype))}((Fnn_1 : Fnn <: numtype), (Inn_2 : Inn <: numtype), TRUNC_SAT_cvtop__(sx), fN_1) = $list_(syntax num_((Inn_2 : Inn <: numtype)), $trunc_sat__($sizenn1((Fnn_1 : Fnn <: numtype)), $sizenn2((Inn_2 : Inn <: numtype)), sx, fN_1))
  ;; ../specification/wasm-2.0/3-numerics.spectec:314.1-314.102
  def $cvtop__{Inn_1 : Inn, Fnn_2 : Fnn, sx : sx, iN_1 : num_((Inn_1 : Inn <: numtype))}((Inn_1 : Inn <: numtype), (Fnn_2 : Fnn <: numtype), CONVERT_cvtop__(sx), iN_1) = [$convert__($sizenn1((Inn_1 : Inn <: numtype)), $sizenn2((Fnn_2 : Fnn <: numtype)), sx, iN_1)]
  ;; ../specification/wasm-2.0/3-numerics.spectec:315.1-315.95
  def $cvtop__{Fnn_1 : Fnn, Fnn_2 : Fnn, fN_1 : num_((Fnn_1 : Fnn <: numtype))}((Fnn_1 : Fnn <: numtype), (Fnn_2 : Fnn <: numtype), PROMOTE_cvtop__, fN_1) = $promote__($sizenn1((Fnn_1 : Fnn <: numtype)), $sizenn2((Fnn_2 : Fnn <: numtype)), fN_1)
  ;; ../specification/wasm-2.0/3-numerics.spectec:316.1-316.93
  def $cvtop__{Fnn_1 : Fnn, Fnn_2 : Fnn, fN_1 : num_((Fnn_1 : Fnn <: numtype))}((Fnn_1 : Fnn <: numtype), (Fnn_2 : Fnn <: numtype), DEMOTE_cvtop__, fN_1) = $demote__($sizenn1((Fnn_1 : Fnn <: numtype)), $sizenn2((Fnn_2 : Fnn <: numtype)), fN_1)
  ;; ../specification/wasm-2.0/3-numerics.spectec:317.1-317.117
  def $cvtop__{Inn_1 : Inn, Fnn_2 : Fnn, iN_1 : num_((Inn_1 : Inn <: numtype))}((Inn_1 : Inn <: numtype), (Fnn_2 : Fnn <: numtype), REINTERPRET_cvtop__, iN_1) = [$reinterpret__((Inn_1 : Inn <: numtype), (Fnn_2 : Fnn <: numtype), iN_1)]
    -- if ($size((Inn_1 : Inn <: valtype)) = $size((Fnn_2 : Fnn <: valtype)))
  ;; ../specification/wasm-2.0/3-numerics.spectec:318.1-318.117
  def $cvtop__{Fnn_1 : Fnn, Inn_2 : Inn, fN_1 : num_((Fnn_1 : Fnn <: numtype))}((Fnn_1 : Fnn <: numtype), (Inn_2 : Inn <: numtype), REINTERPRET_cvtop__, fN_1) = [$reinterpret__((Fnn_1 : Fnn <: numtype), (Inn_2 : Inn <: numtype), fN_1)]
    -- if ($size((Fnn_1 : Fnn <: valtype)) = $size((Inn_2 : Inn <: valtype)))

;; ../specification/wasm-2.0/3-numerics.spectec:62.1-62.87
def $narrow__(M : M, N : N, sx : sx, iN : iN(M)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:76.1-76.102
def $ibits_(N : N, iN : iN(N)) : bit*

;; ../specification/wasm-2.0/3-numerics.spectec:77.1-77.102
def $fbits_(N : N, fN : fN(N)) : bit*

;; ../specification/wasm-2.0/3-numerics.spectec:78.1-78.103
def $ibytes_(N : N, iN : iN(N)) : byte*

;; ../specification/wasm-2.0/3-numerics.spectec:79.1-79.103
def $fbytes_(N : N, fN : fN(N)) : byte*

;; ../specification/wasm-2.0/3-numerics.spectec:80.1-80.103
def $nbytes_(numtype : numtype, num_ : num_(numtype)) : byte*

;; ../specification/wasm-2.0/3-numerics.spectec:81.1-81.103
def $vbytes_(vectype : vectype, vec_ : vec_(vectype)) : byte*

;; ../specification/wasm-2.0/3-numerics.spectec:83.1-83.85
def $inv_ibits_(N : N, bit*) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:84.1-84.85
def $inv_fbits_(N : N, bit*) : fN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:85.1-85.86
def $inv_ibytes_(N : N, byte*) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:86.1-86.86
def $inv_fbytes_(N : N, byte*) : fN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:87.1-87.84
def $inv_nbytes_(numtype : numtype, byte*) : num_(numtype)

;; ../specification/wasm-2.0/3-numerics.spectec:88.1-88.84
def $inv_vbytes_(vectype : vectype, byte*) : vec_(vectype)

;; ../specification/wasm-2.0/3-numerics.spectec:110.1-110.29
def $inot_(N : N, iN : iN(N)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:111.1-111.29
def $irev_(N : N, iN : iN(N)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:113.1-113.39
def $iandnot_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:124.1-124.27
def $inez_(N : N, iN : iN(N)) : u32
  ;; ../specification/wasm-2.0/3-numerics.spectec:172.1-172.38
  def $inez_{N : N, i_1 : iN(N)}(N, i_1) = `%`_u32($bool((i_1!`%`_iN.0 =/= 0)))

;; ../specification/wasm-2.0/3-numerics.spectec:131.1-131.49
def $ibitselect_(N : N, iN : iN(N), iN : iN(N), iN : iN(N)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:133.1-133.29
def $ineg_(N : N, iN : iN(N)) : iN(N)
  ;; ../specification/wasm-2.0/3-numerics.spectec:204.1-204.42
  def $ineg_{N : N, i_1 : iN(N)}(N, i_1) = `%`_iN((((((2 ^ N) : nat <:> int) - (i_1!`%`_iN.0 : nat <:> int)) \ ((2 ^ N) : nat <:> int)) : int <:> nat))

;; ../specification/wasm-2.0/3-numerics.spectec:132.1-132.29
def $iabs_(N : N, iN : iN(N)) : iN(N)
  ;; ../specification/wasm-2.0/3-numerics.spectec:191.1-191.65
  def $iabs_{N : N, i_1 : iN(N)}(N, i_1) = i_1
    -- if ($signed_(N, i_1!`%`_iN.0) >= (0 : nat <:> int))
  ;; ../specification/wasm-2.0/3-numerics.spectec:192.1-192.50
  def $iabs_{N : N, i_1 : iN(N)}(N, i_1) = $ineg_(N, i_1)
    -- otherwise

;; ../specification/wasm-2.0/3-numerics.spectec:134.1-134.81
def $imin_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)
  ;; ../specification/wasm-2.0/3-numerics.spectec:194.1-194.51
  def $imin_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = i_1
    -- if (i_1!`%`_iN.0 <= i_2!`%`_iN.0)
  ;; ../specification/wasm-2.0/3-numerics.spectec:195.1-195.50
  def $imin_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = i_2
    -- if (i_1!`%`_iN.0 > i_2!`%`_iN.0)
  ;; ../specification/wasm-2.0/3-numerics.spectec:196.1-196.77
  def $imin_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = i_1
    -- if ($signed_(N, i_1!`%`_iN.0) <= $signed_(N, i_2!`%`_iN.0))
  ;; ../specification/wasm-2.0/3-numerics.spectec:197.1-197.47
  def $imin_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = i_2
    -- otherwise

;; ../specification/wasm-2.0/3-numerics.spectec:135.1-135.81
def $imax_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)
  ;; ../specification/wasm-2.0/3-numerics.spectec:199.1-199.51
  def $imax_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = i_1
    -- if (i_1!`%`_iN.0 >= i_2!`%`_iN.0)
  ;; ../specification/wasm-2.0/3-numerics.spectec:200.1-200.50
  def $imax_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = i_2
    -- if (i_1!`%`_iN.0 < i_2!`%`_iN.0)
  ;; ../specification/wasm-2.0/3-numerics.spectec:201.1-201.77
  def $imax_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = i_1
    -- if ($signed_(N, i_1!`%`_iN.0) >= $signed_(N, i_2!`%`_iN.0))
  ;; ../specification/wasm-2.0/3-numerics.spectec:202.1-202.47
  def $imax_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = i_2
    -- otherwise

;; ../specification/wasm-2.0/3-numerics.spectec:136.1-136.86
def $iadd_sat_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)
  ;; ../specification/wasm-2.0/3-numerics.spectec:206.1-206.58
  def $iadd_sat_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_iN($sat_u_(N, ((i_1!`%`_iN.0 + i_2!`%`_iN.0) : nat <:> int)))
  ;; ../specification/wasm-2.0/3-numerics.spectec:207.1-207.101
  def $iadd_sat_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_iN($inv_signed_(N, $sat_s_(N, ($signed_(N, i_1!`%`_iN.0) + $signed_(N, i_2!`%`_iN.0)))))

;; ../specification/wasm-2.0/3-numerics.spectec:137.1-137.86
def $isub_sat_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)
  ;; ../specification/wasm-2.0/3-numerics.spectec:209.1-209.58
  def $isub_sat_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_iN($sat_u_(N, ((i_1!`%`_iN.0 : nat <:> int) - (i_2!`%`_iN.0 : nat <:> int))))
  ;; ../specification/wasm-2.0/3-numerics.spectec:210.1-210.101
  def $isub_sat_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_iN($inv_signed_(N, $sat_s_(N, ($signed_(N, i_1!`%`_iN.0) - $signed_(N, i_2!`%`_iN.0)))))

;; ../specification/wasm-2.0/3-numerics.spectec:138.1-138.82
def $iavgr_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:139.1-139.90
def $iq15mulr_sat_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)

;; ../specification/wasm-2.0/3-numerics.spectec:221.1-221.38
def $fpmin_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:222.1-222.38
def $fpmax_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; ../specification/wasm-2.0/3-numerics.spectec:323.1-324.27
def $packnum_(lanetype : lanetype, num_ : num_($unpack(lanetype))) : lane_(lanetype)
  ;; ../specification/wasm-2.0/3-numerics.spectec:325.1-325.26
  def $packnum_{Inn : Inn, c : num_($unpack((Inn : Inn <: lanetype)))}((Inn : Inn <: lanetype), c) = c
  ;; ../specification/wasm-2.0/3-numerics.spectec:326.1-326.26
  def $packnum_{Fnn : Fnn, c : num_($unpack((Fnn : Fnn <: lanetype)))}((Fnn : Fnn <: lanetype), c) = c
  ;; ../specification/wasm-2.0/3-numerics.spectec:327.1-327.84
  def $packnum_{packtype : packtype, c : num_($unpack((packtype : packtype <: lanetype)))}((packtype : packtype <: lanetype), c) = $wrap__($size(($unpack((packtype : packtype <: lanetype)) : numtype <: valtype)), $psize(packtype), c)

;; ../specification/wasm-2.0/3-numerics.spectec:329.1-330.29
def $unpacknum_(lanetype : lanetype, lane_ : lane_(lanetype)) : num_($unpack(lanetype))
  ;; ../specification/wasm-2.0/3-numerics.spectec:331.1-331.28
  def $unpacknum_{Inn : Inn, c : lane_((Inn : Inn <: lanetype))}((Inn : Inn <: lanetype), c) = c
  ;; ../specification/wasm-2.0/3-numerics.spectec:332.1-332.28
  def $unpacknum_{Fnn : Fnn, c : lane_((Fnn : Fnn <: lanetype))}((Fnn : Fnn <: lanetype), c) = c
  ;; ../specification/wasm-2.0/3-numerics.spectec:333.1-333.91
  def $unpacknum_{packtype : packtype, c : lane_((packtype : packtype <: lanetype))}((packtype : packtype <: lanetype), c) = $extend__($psize(packtype), $size(($unpack((packtype : packtype <: lanetype)) : numtype <: valtype)), U_sx, c)

;; ../specification/wasm-2.0/3-numerics.spectec:338.1-338.84
def $lanes_(shape : shape, vec_ : vec_(V128_Vnn)) : lane_($lanetype(shape))*

;; ../specification/wasm-2.0/3-numerics.spectec:341.1-342.36
def $inv_lanes_(shape : shape, lane_($lanetype(shape))*) : vec_(V128_Vnn)

;; ../specification/wasm-2.0/3-numerics.spectec:345.1-345.66
def $zeroop(shape_1 : shape, shape_2 : shape, vcvtop__ : vcvtop__(shape_1, shape_2)) : zero?
  ;; ../specification/wasm-2.0/3-numerics.spectec:346.1-346.60
  def $zeroop{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, half : half, sx : sx}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), EXTEND_vcvtop__(half, sx)) = ?()
  ;; ../specification/wasm-2.0/3-numerics.spectec:347.1-347.62
  def $zeroop{Jnn_1 : Jnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, `half?` : half?, sx : sx}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), CONVERT_vcvtop__(half?{half <- `half?`}, sx)) = ?()
  ;; ../specification/wasm-2.0/3-numerics.spectec:348.1-348.66
  def $zeroop{Fnn_1 : Fnn, M_1 : M, Inn_2 : Inn, M_2 : M, sx : sx, `zero?` : zero?}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Inn_2 : Inn <: lanetype), `%`_dim(M_2)), TRUNC_SAT_vcvtop__(sx, zero?{zero <- `zero?`})) = zero?{zero <- `zero?`}
  ;; ../specification/wasm-2.0/3-numerics.spectec:349.1-349.58
  def $zeroop{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, zero : zero}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), DEMOTE_vcvtop__(zero)) = ?(zero)
  ;; ../specification/wasm-2.0/3-numerics.spectec:350.1-350.57
  def $zeroop{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), PROMOTELOW_vcvtop__) = ?()

;; ../specification/wasm-2.0/3-numerics.spectec:352.1-352.66
def $halfop(shape_1 : shape, shape_2 : shape, vcvtop__ : vcvtop__(shape_1, shape_2)) : half?
  ;; ../specification/wasm-2.0/3-numerics.spectec:353.1-353.61
  def $halfop{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, half : half, sx : sx}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), EXTEND_vcvtop__(half, sx)) = ?(half)
  ;; ../specification/wasm-2.0/3-numerics.spectec:354.1-354.64
  def $halfop{Jnn_1 : Jnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, `half?` : half?, sx : sx}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), CONVERT_vcvtop__(half?{half <- `half?`}, sx)) = half?{half <- `half?`}
  ;; ../specification/wasm-2.0/3-numerics.spectec:355.1-355.64
  def $halfop{Fnn_1 : Fnn, M_1 : M, Inn_2 : Inn, M_2 : M, sx : sx, `zero?` : zero?}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Inn_2 : Inn <: lanetype), `%`_dim(M_2)), TRUNC_SAT_vcvtop__(sx, zero?{zero <- `zero?`})) = ?()
  ;; ../specification/wasm-2.0/3-numerics.spectec:356.1-356.57
  def $halfop{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, zero : zero}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), DEMOTE_vcvtop__(zero)) = ?()
  ;; ../specification/wasm-2.0/3-numerics.spectec:357.1-357.57
  def $halfop{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), PROMOTELOW_vcvtop__) = ?(LOW_half)

;; ../specification/wasm-2.0/3-numerics.spectec:359.1-359.32
def $half(half : half, nat : nat, nat : nat) : nat
  ;; ../specification/wasm-2.0/3-numerics.spectec:360.1-360.25
  def $half{i : nat, j : nat}(LOW_half, i, j) = i
  ;; ../specification/wasm-2.0/3-numerics.spectec:361.1-361.26
  def $half{i : nat, j : nat}(HIGH_half, i, j) = j

;; ../specification/wasm-2.0/3-numerics.spectec:364.1-365.28
def $vvunop_(vectype : vectype, vvunop : vvunop, vec_ : vec_(vectype)) : vec_(vectype)
  ;; ../specification/wasm-2.0/3-numerics.spectec:371.1-371.58
  def $vvunop_{v128 : vec_(V128_Vnn)}(V128_vectype, NOT_vvunop, v128) = $inot_($size(V128_valtype), v128)

;; ../specification/wasm-2.0/3-numerics.spectec:366.1-367.31
def $vvbinop_(vectype : vectype, vvbinop : vvbinop, vec_ : vec_(vectype), vec_ : vec_(vectype)) : vec_(vectype)
  ;; ../specification/wasm-2.0/3-numerics.spectec:372.1-372.79
  def $vvbinop_{v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn)}(V128_vectype, AND_vvbinop, v128_1, v128_2) = $iand_($size(V128_valtype), v128_1, v128_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:373.1-373.85
  def $vvbinop_{v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn)}(V128_vectype, ANDNOT_vvbinop, v128_1, v128_2) = $iandnot_($size(V128_valtype), v128_1, v128_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:374.1-374.77
  def $vvbinop_{v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn)}(V128_vectype, OR_vvbinop, v128_1, v128_2) = $ior_($size(V128_valtype), v128_1, v128_2)
  ;; ../specification/wasm-2.0/3-numerics.spectec:375.1-375.79
  def $vvbinop_{v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn)}(V128_vectype, XOR_vvbinop, v128_1, v128_2) = $ixor_($size(V128_valtype), v128_1, v128_2)

;; ../specification/wasm-2.0/3-numerics.spectec:368.1-369.34
def $vvternop_(vectype : vectype, vvternop : vvternop, vec_ : vec_(vectype), vec_ : vec_(vectype), vec_ : vec_(vectype)) : vec_(vectype)
  ;; ../specification/wasm-2.0/3-numerics.spectec:376.1-376.108
  def $vvternop_{v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128_3 : vec_(V128_Vnn)}(V128_vectype, BITSELECT_vvternop, v128_1, v128_2, v128_3) = $ibitselect_($size(V128_valtype), v128_1, v128_2, v128_3)

;; ../specification/wasm-2.0/3-numerics.spectec:379.1-380.32
def $vunop_(shape : shape, vunop_ : vunop_(shape), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; ../specification/wasm-2.0/3-numerics.spectec:390.1-392.70
  def $vunop_{Jnn : Jnn, M : M, v128_1 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), ABS_vunop_, v128_1) = [v128]
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), $iabs_($lsizenn((Jnn : Jnn <: lanetype)), lane_1)*{lane_1 <- `lane_1*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:393.1-395.70
  def $vunop_{Jnn : Jnn, M : M, v128_1 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), NEG_vunop_, v128_1) = [v128]
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), $ineg_($lsizenn((Jnn : Jnn <: lanetype)), lane_1)*{lane_1 <- `lane_1*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:396.1-398.73
  def $vunop_{Jnn : Jnn, M : M, v128_1 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), POPCNT_vunop_, v128_1) = [v128]
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), $ipopcnt_($lsizenn((Jnn : Jnn <: lanetype)), lane_1)*{lane_1 <- `lane_1*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:468.1-471.47
  def $vunop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), `v128*` : vec_(V128_Vnn)*, `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane**` : lane_((Fnn : Fnn <: lanetype))**}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), ABS_vunop_, v128_1) = v128*{v128 <- `v128*`}
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane*{lane <- `lane*`}*{`lane*` <- `lane**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $fabs_($sizenn((Fnn : Fnn <: numtype)), lane_1)*{lane_1 <- `lane_1*`}))
    -- if (v128*{v128 <- `v128*`} = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), lane*{lane <- `lane*`})*{`lane*` <- `lane**`})
  ;; ../specification/wasm-2.0/3-numerics.spectec:472.1-475.47
  def $vunop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), `v128*` : vec_(V128_Vnn)*, `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane**` : lane_((Fnn : Fnn <: lanetype))**}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), NEG_vunop_, v128_1) = v128*{v128 <- `v128*`}
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane*{lane <- `lane*`}*{`lane*` <- `lane**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $fneg_($sizenn((Fnn : Fnn <: numtype)), lane_1)*{lane_1 <- `lane_1*`}))
    -- if (v128*{v128 <- `v128*`} = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), lane*{lane <- `lane*`})*{`lane*` <- `lane**`})
  ;; ../specification/wasm-2.0/3-numerics.spectec:476.1-479.47
  def $vunop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), `v128*` : vec_(V128_Vnn)*, `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane**` : lane_((Fnn : Fnn <: lanetype))**}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), SQRT_vunop_, v128_1) = v128*{v128 <- `v128*`}
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane*{lane <- `lane*`}*{`lane*` <- `lane**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $fsqrt_($sizenn((Fnn : Fnn <: numtype)), lane_1)*{lane_1 <- `lane_1*`}))
    -- if (v128*{v128 <- `v128*`} = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), lane*{lane <- `lane*`})*{`lane*` <- `lane**`})
  ;; ../specification/wasm-2.0/3-numerics.spectec:480.1-483.47
  def $vunop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), `v128*` : vec_(V128_Vnn)*, `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane**` : lane_((Fnn : Fnn <: lanetype))**}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), CEIL_vunop_, v128_1) = v128*{v128 <- `v128*`}
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane*{lane <- `lane*`}*{`lane*` <- `lane**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $fceil_($sizenn((Fnn : Fnn <: numtype)), lane_1)*{lane_1 <- `lane_1*`}))
    -- if (v128*{v128 <- `v128*`} = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), lane*{lane <- `lane*`})*{`lane*` <- `lane**`})
  ;; ../specification/wasm-2.0/3-numerics.spectec:484.1-487.47
  def $vunop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), `v128*` : vec_(V128_Vnn)*, `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane**` : lane_((Fnn : Fnn <: lanetype))**}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), FLOOR_vunop_, v128_1) = v128*{v128 <- `v128*`}
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane*{lane <- `lane*`}*{`lane*` <- `lane**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $ffloor_($sizenn((Fnn : Fnn <: numtype)), lane_1)*{lane_1 <- `lane_1*`}))
    -- if (v128*{v128 <- `v128*`} = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), lane*{lane <- `lane*`})*{`lane*` <- `lane**`})
  ;; ../specification/wasm-2.0/3-numerics.spectec:488.1-491.47
  def $vunop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), `v128*` : vec_(V128_Vnn)*, `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane**` : lane_((Fnn : Fnn <: lanetype))**}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), TRUNC_vunop_, v128_1) = v128*{v128 <- `v128*`}
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane*{lane <- `lane*`}*{`lane*` <- `lane**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $ftrunc_($sizenn((Fnn : Fnn <: numtype)), lane_1)*{lane_1 <- `lane_1*`}))
    -- if (v128*{v128 <- `v128*`} = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), lane*{lane <- `lane*`})*{`lane*` <- `lane**`})
  ;; ../specification/wasm-2.0/3-numerics.spectec:492.1-495.47
  def $vunop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), `v128*` : vec_(V128_Vnn)*, `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane**` : lane_((Fnn : Fnn <: lanetype))**}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), NEAREST_vunop_, v128_1) = v128*{v128 <- `v128*`}
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane*{lane <- `lane*`}*{`lane*` <- `lane**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $fnearest_($sizenn((Fnn : Fnn <: numtype)), lane_1)*{lane_1 <- `lane_1*`}))
    -- if (v128*{v128 <- `v128*`} = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), lane*{lane <- `lane*`})*{`lane*` <- `lane**`})

;; ../specification/wasm-2.0/3-numerics.spectec:381.1-382.34
def $vbinop_(shape : shape, vbinop_ : vbinop_(shape), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; ../specification/wasm-2.0/3-numerics.spectec:400.1-403.78
  def $vbinop_{Jnn : Jnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), ADD_vbinop_, v128_1, v128_2) = [v128]
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), $iadd_($lsizenn((Jnn : Jnn <: lanetype)), lane_1, lane_2)*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:404.1-407.78
  def $vbinop_{Jnn : Jnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), SUB_vbinop_, v128_1, v128_2) = [v128]
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), $isub_($lsizenn((Jnn : Jnn <: lanetype)), lane_1, lane_2)*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:408.1-411.82
  def $vbinop_{Jnn : Jnn, M : M, sx : sx, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), MIN_vbinop_(sx), v128_1, v128_2) = [v128]
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), $imin_($lsizenn((Jnn : Jnn <: lanetype)), sx, lane_1, lane_2)*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:412.1-415.82
  def $vbinop_{Jnn : Jnn, M : M, sx : sx, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), MAX_vbinop_(sx), v128_1, v128_2) = [v128]
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), $imax_($lsizenn((Jnn : Jnn <: lanetype)), sx, lane_1, lane_2)*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:416.1-419.86
  def $vbinop_{Jnn : Jnn, M : M, sx : sx, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), ADD_SAT_vbinop_(sx), v128_1, v128_2) = [v128]
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), $iadd_sat_($lsizenn((Jnn : Jnn <: lanetype)), sx, lane_1, lane_2)*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:420.1-423.86
  def $vbinop_{Jnn : Jnn, M : M, sx : sx, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), SUB_SAT_vbinop_(sx), v128_1, v128_2) = [v128]
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), $isub_sat_($lsizenn((Jnn : Jnn <: lanetype)), sx, lane_1, lane_2)*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:424.1-427.78
  def $vbinop_{Jnn : Jnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), MUL_vbinop_, v128_1, v128_2) = [v128]
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), $imul_($lsizenn((Jnn : Jnn <: lanetype)), lane_1, lane_2)*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:428.1-431.82
  def $vbinop_{Jnn : Jnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), AVGRU_vbinop_, v128_1, v128_2) = [v128]
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), $iavgr_($lsizenn((Jnn : Jnn <: lanetype)), U_sx, lane_1, lane_2)*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:432.1-435.89
  def $vbinop_{Jnn : Jnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), Q15MULR_SATS_vbinop_, v128_1, v128_2) = [v128]
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), $iq15mulr_sat_($lsizenn((Jnn : Jnn <: lanetype)), S_sx, lane_1, lane_2)*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:497.1-501.47
  def $vbinop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), `v128*` : vec_(V128_Vnn)*, `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane**` : lane_((Fnn : Fnn <: lanetype))**}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), ADD_vbinop_, v128_1, v128_2) = v128*{v128 <- `v128*`}
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane*{lane <- `lane*`}*{`lane*` <- `lane**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $fadd_($sizenn((Fnn : Fnn <: numtype)), lane_1, lane_2)*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`}))
    -- if (v128*{v128 <- `v128*`} = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), lane*{lane <- `lane*`})*{`lane*` <- `lane**`})
  ;; ../specification/wasm-2.0/3-numerics.spectec:502.1-506.47
  def $vbinop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), `v128*` : vec_(V128_Vnn)*, `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane**` : lane_((Fnn : Fnn <: lanetype))**}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), SUB_vbinop_, v128_1, v128_2) = v128*{v128 <- `v128*`}
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane*{lane <- `lane*`}*{`lane*` <- `lane**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $fsub_($sizenn((Fnn : Fnn <: numtype)), lane_1, lane_2)*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`}))
    -- if (v128*{v128 <- `v128*`} = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), lane*{lane <- `lane*`})*{`lane*` <- `lane**`})
  ;; ../specification/wasm-2.0/3-numerics.spectec:507.1-511.47
  def $vbinop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), `v128*` : vec_(V128_Vnn)*, `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane**` : lane_((Fnn : Fnn <: lanetype))**}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), MUL_vbinop_, v128_1, v128_2) = v128*{v128 <- `v128*`}
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane*{lane <- `lane*`}*{`lane*` <- `lane**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $fmul_($sizenn((Fnn : Fnn <: numtype)), lane_1, lane_2)*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`}))
    -- if (v128*{v128 <- `v128*`} = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), lane*{lane <- `lane*`})*{`lane*` <- `lane**`})
  ;; ../specification/wasm-2.0/3-numerics.spectec:512.1-516.47
  def $vbinop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), `v128*` : vec_(V128_Vnn)*, `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane**` : lane_((Fnn : Fnn <: lanetype))**}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), DIV_vbinop_, v128_1, v128_2) = v128*{v128 <- `v128*`}
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane*{lane <- `lane*`}*{`lane*` <- `lane**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $fdiv_($sizenn((Fnn : Fnn <: numtype)), lane_1, lane_2)*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`}))
    -- if (v128*{v128 <- `v128*`} = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), lane*{lane <- `lane*`})*{`lane*` <- `lane**`})
  ;; ../specification/wasm-2.0/3-numerics.spectec:517.1-521.47
  def $vbinop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), `v128*` : vec_(V128_Vnn)*, `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane**` : lane_((Fnn : Fnn <: lanetype))**}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), MIN_vbinop_, v128_1, v128_2) = v128*{v128 <- `v128*`}
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane*{lane <- `lane*`}*{`lane*` <- `lane**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $fmin_($sizenn((Fnn : Fnn <: numtype)), lane_1, lane_2)*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`}))
    -- if (v128*{v128 <- `v128*`} = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), lane*{lane <- `lane*`})*{`lane*` <- `lane**`})
  ;; ../specification/wasm-2.0/3-numerics.spectec:522.1-526.47
  def $vbinop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), `v128*` : vec_(V128_Vnn)*, `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane**` : lane_((Fnn : Fnn <: lanetype))**}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), MAX_vbinop_, v128_1, v128_2) = v128*{v128 <- `v128*`}
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane*{lane <- `lane*`}*{`lane*` <- `lane**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $fmax_($sizenn((Fnn : Fnn <: numtype)), lane_1, lane_2)*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`}))
    -- if (v128*{v128 <- `v128*`} = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), lane*{lane <- `lane*`})*{`lane*` <- `lane**`})
  ;; ../specification/wasm-2.0/3-numerics.spectec:527.1-531.47
  def $vbinop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), `v128*` : vec_(V128_Vnn)*, `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane**` : lane_((Fnn : Fnn <: lanetype))**}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), PMIN_vbinop_, v128_1, v128_2) = v128*{v128 <- `v128*`}
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane*{lane <- `lane*`}*{`lane*` <- `lane**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $fpmin_($sizenn((Fnn : Fnn <: numtype)), lane_1, lane_2)*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`}))
    -- if (v128*{v128 <- `v128*`} = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), lane*{lane <- `lane*`})*{`lane*` <- `lane**`})
  ;; ../specification/wasm-2.0/3-numerics.spectec:532.1-536.47
  def $vbinop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), `v128*` : vec_(V128_Vnn)*, `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane**` : lane_((Fnn : Fnn <: lanetype))**}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), PMAX_vbinop_, v128_1, v128_2) = v128*{v128 <- `v128*`}
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane*{lane <- `lane*`}*{`lane*` <- `lane**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $fpmax_($sizenn((Fnn : Fnn <: numtype)), lane_1, lane_2)*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`}))
    -- if (v128*{v128 <- `v128*`} = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), lane*{lane <- `lane*`})*{`lane*` <- `lane**`})

;; ../specification/wasm-2.0/3-numerics.spectec:383.1-384.34
def $vrelop_(shape : shape, vrelop_ : vrelop_(shape), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; ../specification/wasm-2.0/3-numerics.spectec:437.1-441.47
  def $vrelop_{Jnn : Jnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_3*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), EQ_vrelop_, v128_1, v128_2) = v128
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane_3*{lane_3 <- `lane_3*`} = $extend__(1, $lsizenn((Jnn : Jnn <: lanetype)), S_sx, `%`_iN($ieq_($lsizenn((Jnn : Jnn <: lanetype)), lane_1, lane_2)!`%`_u32.0))*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`})
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), lane_3*{lane_3 <- `lane_3*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:442.1-446.47
  def $vrelop_{Jnn : Jnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_3*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), NE_vrelop_, v128_1, v128_2) = v128
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane_3*{lane_3 <- `lane_3*`} = $extend__(1, $lsizenn((Jnn : Jnn <: lanetype)), S_sx, `%`_iN($ine_($lsizenn((Jnn : Jnn <: lanetype)), lane_1, lane_2)!`%`_u32.0))*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`})
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), lane_3*{lane_3 <- `lane_3*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:447.1-451.47
  def $vrelop_{Jnn : Jnn, M : M, sx : sx, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_3*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), LT_vrelop_(sx), v128_1, v128_2) = v128
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane_3*{lane_3 <- `lane_3*`} = $extend__(1, $lsizenn((Jnn : Jnn <: lanetype)), S_sx, `%`_iN($ilt_($lsizenn((Jnn : Jnn <: lanetype)), sx, lane_1, lane_2)!`%`_u32.0))*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`})
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), lane_3*{lane_3 <- `lane_3*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:452.1-456.47
  def $vrelop_{Jnn : Jnn, M : M, sx : sx, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_3*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), GT_vrelop_(sx), v128_1, v128_2) = v128
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane_3*{lane_3 <- `lane_3*`} = $extend__(1, $lsizenn((Jnn : Jnn <: lanetype)), S_sx, `%`_iN($igt_($lsizenn((Jnn : Jnn <: lanetype)), sx, lane_1, lane_2)!`%`_u32.0))*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`})
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), lane_3*{lane_3 <- `lane_3*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:457.1-461.47
  def $vrelop_{Jnn : Jnn, M : M, sx : sx, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_3*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), LE_vrelop_(sx), v128_1, v128_2) = v128
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane_3*{lane_3 <- `lane_3*`} = $extend__(1, $lsizenn((Jnn : Jnn <: lanetype)), S_sx, `%`_iN($ile_($lsizenn((Jnn : Jnn <: lanetype)), sx, lane_1, lane_2)!`%`_u32.0))*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`})
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), lane_3*{lane_3 <- `lane_3*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:462.1-466.47
  def $vrelop_{Jnn : Jnn, M : M, sx : sx, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `lane_3*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), GE_vrelop_(sx), v128_1, v128_2) = v128
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane_3*{lane_3 <- `lane_3*`} = $extend__(1, $lsizenn((Jnn : Jnn <: lanetype)), S_sx, `%`_iN($ige_($lsizenn((Jnn : Jnn <: lanetype)), sx, lane_1, lane_2)!`%`_u32.0))*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`})
    -- if (v128 = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), lane_3*{lane_3 <- `lane_3*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:538.1-543.47
  def $vrelop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_3*` : iN($sizenn((Fnn : Fnn <: numtype)))*, Inn : Inn}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), EQ_vrelop_, v128_1, v128_2) = v128
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane_3*{lane_3 <- `lane_3*`} = $extend__(1, $sizenn((Fnn : Fnn <: numtype)), S_sx, `%`_iN($feq_($sizenn((Fnn : Fnn <: numtype)), lane_1, lane_2)!`%`_u32.0))*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`})
    -- if ($isize(Inn) = $size((Fnn : Fnn <: valtype)))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Inn : Inn <: lanetype), `%`_dim(M)), `%`_lane_(lane_3!`%`_iN.0)*{lane_3 <- `lane_3*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:544.1-549.47
  def $vrelop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_3*` : iN($sizenn((Fnn : Fnn <: numtype)))*, Inn : Inn}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), NE_vrelop_, v128_1, v128_2) = v128
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane_3*{lane_3 <- `lane_3*`} = $extend__(1, $sizenn((Fnn : Fnn <: numtype)), S_sx, `%`_iN($fne_($sizenn((Fnn : Fnn <: numtype)), lane_1, lane_2)!`%`_u32.0))*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`})
    -- if ($isize(Inn) = $size((Fnn : Fnn <: valtype)))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Inn : Inn <: lanetype), `%`_dim(M)), `%`_lane_(lane_3!`%`_iN.0)*{lane_3 <- `lane_3*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:550.1-555.47
  def $vrelop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_3*` : iN($sizenn((Fnn : Fnn <: numtype)))*, Inn : Inn}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), LT_vrelop_, v128_1, v128_2) = v128
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane_3*{lane_3 <- `lane_3*`} = $extend__(1, $sizenn((Fnn : Fnn <: numtype)), S_sx, `%`_iN($flt_($sizenn((Fnn : Fnn <: numtype)), lane_1, lane_2)!`%`_u32.0))*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`})
    -- if ($isize(Inn) = $size((Fnn : Fnn <: valtype)))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Inn : Inn <: lanetype), `%`_dim(M)), `%`_lane_(lane_3!`%`_iN.0)*{lane_3 <- `lane_3*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:556.1-561.47
  def $vrelop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_3*` : iN($sizenn((Fnn : Fnn <: numtype)))*, Inn : Inn}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), GT_vrelop_, v128_1, v128_2) = v128
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane_3*{lane_3 <- `lane_3*`} = $extend__(1, $sizenn((Fnn : Fnn <: numtype)), S_sx, `%`_iN($fgt_($sizenn((Fnn : Fnn <: numtype)), lane_1, lane_2)!`%`_u32.0))*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`})
    -- if ($isize(Inn) = $size((Fnn : Fnn <: valtype)))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Inn : Inn <: lanetype), `%`_dim(M)), `%`_lane_(lane_3!`%`_iN.0)*{lane_3 <- `lane_3*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:562.1-567.47
  def $vrelop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_3*` : iN($sizenn((Fnn : Fnn <: numtype)))*, Inn : Inn}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), LE_vrelop_, v128_1, v128_2) = v128
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane_3*{lane_3 <- `lane_3*`} = $extend__(1, $sizenn((Fnn : Fnn <: numtype)), S_sx, `%`_iN($fle_($sizenn((Fnn : Fnn <: numtype)), lane_1, lane_2)!`%`_u32.0))*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`})
    -- if ($isize(Inn) = $size((Fnn : Fnn <: valtype)))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Inn : Inn <: lanetype), `%`_dim(M)), `%`_lane_(lane_3!`%`_iN.0)*{lane_3 <- `lane_3*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:568.1-573.47
  def $vrelop_{Fnn : Fnn, M : M, v128_1 : vec_(V128_Vnn), v128_2 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `lane_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `lane_3*` : iN($sizenn((Fnn : Fnn <: numtype)))*, Inn : Inn}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), GE_vrelop_, v128_1, v128_2) = v128
    -- if (lane_1*{lane_1 <- `lane_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_1))
    -- if (lane_2*{lane_2 <- `lane_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v128_2))
    -- if (lane_3*{lane_3 <- `lane_3*`} = $extend__(1, $sizenn((Fnn : Fnn <: numtype)), S_sx, `%`_iN($fge_($sizenn((Fnn : Fnn <: numtype)), lane_1, lane_2)!`%`_u32.0))*{lane_1 <- `lane_1*`, lane_2 <- `lane_2*`})
    -- if ($isize(Inn) = $size((Fnn : Fnn <: valtype)))
    -- if (v128 = $inv_lanes_(`%X%`_shape((Inn : Inn <: lanetype), `%`_dim(M)), `%`_lane_(lane_3!`%`_iN.0)*{lane_3 <- `lane_3*`}))

;; ../specification/wasm-2.0/3-numerics.spectec:385.1-386.41
def $lcvtop__(shape_1 : shape, shape_2 : shape, vcvtop__ : vcvtop__(shape_1, shape_2), lane_ : lane_($lanetype(shape_1))) : lane_($lanetype(shape_2))*
  ;; ../specification/wasm-2.0/3-numerics.spectec:575.1-576.73
  def $lcvtop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, half : half, sx : sx, iN_1 : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)))), iN_2 : iN($lsizenn2((Jnn_2 : Jnn <: lanetype)))}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), EXTEND_vcvtop__(half, sx), iN_1) = [iN_2]
    -- if (iN_2 = $extend__($lsizenn1((Jnn_1 : Jnn <: lanetype)), $lsizenn2((Jnn_2 : Jnn <: lanetype)), sx, iN_1))
  ;; ../specification/wasm-2.0/3-numerics.spectec:577.1-578.74
  def $lcvtop__{Jnn_1 : Jnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, `half?` : half?, sx : sx, iN_1 : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)))), fN_2 : fN($lsizenn2((Fnn_2 : Fnn <: lanetype)))}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), CONVERT_vcvtop__(half?{half <- `half?`}, sx), iN_1) = [fN_2]
    -- if (fN_2 = $convert__($lsizenn1((Jnn_1 : Jnn <: lanetype)), $lsizenn2((Fnn_2 : Fnn <: lanetype)), sx, iN_1))
  ;; ../specification/wasm-2.0/3-numerics.spectec:579.1-580.77
  def $lcvtop__{Fnn_1 : Fnn, M_1 : M, Inn_2 : Inn, M_2 : M, sx : sx, `zero?` : zero?, fN_1 : lane_($lanetype(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)))), `iN_2?` : iN($lsizenn2((Inn_2 : Inn <: lanetype)))?}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Inn_2 : Inn <: lanetype), `%`_dim(M_2)), TRUNC_SAT_vcvtop__(sx, zero?{zero <- `zero?`}), fN_1) = $list_(syntax lane_((Inn_2 : Inn <: lanetype)), iN_2?{iN_2 <- `iN_2?`})
    -- if (iN_2?{iN_2 <- `iN_2?`} = $trunc_sat__($lsizenn1((Fnn_1 : Fnn <: lanetype)), $lsizenn2((Inn_2 : Inn <: lanetype)), sx, fN_1))
  ;; ../specification/wasm-2.0/3-numerics.spectec:581.1-582.70
  def $lcvtop__{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, fN_1 : lane_($lanetype(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)))), `fN_2*` : fN($lsizenn2((Fnn_2 : Fnn <: lanetype)))*}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), DEMOTE_vcvtop__(ZERO_zero), fN_1) = fN_2*{fN_2 <- `fN_2*`}
    -- if (fN_2*{fN_2 <- `fN_2*`} = $demote__($lsizenn1((Fnn_1 : Fnn <: lanetype)), $lsizenn2((Fnn_2 : Fnn <: lanetype)), fN_1))
  ;; ../specification/wasm-2.0/3-numerics.spectec:583.1-584.71
  def $lcvtop__{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, fN_1 : lane_($lanetype(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)))), `fN_2*` : fN($lsizenn2((Fnn_2 : Fnn <: lanetype)))*}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), PROMOTELOW_vcvtop__, fN_1) = fN_2*{fN_2 <- `fN_2*`}
    -- if (fN_2*{fN_2 <- `fN_2*`} = $promote__($lsizenn1((Fnn_1 : Fnn <: lanetype)), $lsizenn2((Fnn_2 : Fnn <: lanetype)), fN_1))

;; ../specification/wasm-2.0/3-numerics.spectec:387.1-388.41
def $vcvtop__(shape_1 : shape, shape_2 : shape, vcvtop__ : vcvtop__(shape_1, shape_2), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; ../specification/wasm-2.0/3-numerics.spectec:586.1-590.46
  def $vcvtop__{Lnn_1 : Lnn, M : M, Lnn_2 : Lnn, vcvtop : vcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M))), v128_1 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `c_1*` : lane_($lanetype(`%X%`_shape(Lnn_1, `%`_dim(M))))*, `c**` : lane_(Lnn_2)**}(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M)), vcvtop, v128_1) = v128
    -- if (($halfop(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M)), vcvtop) = ?()) /\ ($zeroop(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M)), vcvtop) = ?()))
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape(Lnn_1, `%`_dim(M)), v128_1))
    -- if (c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_(Lnn_2), $lcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M)), vcvtop, c_1)*{c_1 <- `c_1*`}))
    -- if (v128 <- $inv_lanes_(`%X%`_shape(Lnn_2, `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`})
  ;; ../specification/wasm-2.0/3-numerics.spectec:591.1-595.48
  def $vcvtop__{Lnn_1 : Lnn, M_1 : M, Lnn_2 : Lnn, M_2 : M, vcvtop : vcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2))), v128_1 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), half : half, `c_1*` : lane_($lanetype(`%X%`_shape(Lnn_1, `%`_dim(M_1))))*, `c**` : lane_(Lnn_2)**}(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop, v128_1) = v128
    -- if ($halfop(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop) = ?(half))
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape(Lnn_1, `%`_dim(M_1)), v128_1)[$half(half, 0, M_2) : M_2])
    -- if (c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_(Lnn_2), $lcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop, c_1)*{c_1 <- `c_1*`}))
    -- if (v128 <- $inv_lanes_(`%X%`_shape(Lnn_2, `%`_dim(M_2)), c*{c <- `c*`})*{`c*` <- `c**`})
  ;; ../specification/wasm-2.0/3-numerics.spectec:596.1-600.48
  def $vcvtop__{Lnn_1 : Lnn, M_1 : M, Lnn_2 : Lnn, M_2 : M, vcvtop : vcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2))), v128_1 : vec_(V128_Vnn), v128 : vec_(V128_Vnn), `c_1*` : lane_($lanetype(`%X%`_shape(Lnn_1, `%`_dim(M_1))))*, `c**` : lane_(Lnn_2)**}(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop, v128_1) = v128
    -- if ($zeroop(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop) = ?(ZERO_zero))
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape(Lnn_1, `%`_dim(M_1)), v128_1))
    -- if (c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_(Lnn_2), $lcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop, c_1)*{c_1 <- `c_1*`} ++ [$packnum_(Lnn_2, $zero($unpack(Lnn_2)))]^M_1{}))
    -- if (v128 <- $inv_lanes_(`%X%`_shape(Lnn_2, `%`_dim(M_2)), c*{c <- `c*`})*{`c*` <- `c**`})

;; ../specification/wasm-2.0/3-numerics.spectec:603.1-604.42
def $vextunop__(ishape_1 : ishape, ishape_2 : ishape, vextunop__ : vextunop__(ishape_1, ishape_2), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; ../specification/wasm-2.0/3-numerics.spectec:608.1-613.76
  def $vextunop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, sx : sx, c_1 : vec_(V128_Vnn), c : vec_(V128_Vnn), `ci*` : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))))*, `cj_1*` : iN($lsize((Jnn_2 : Jnn <: lanetype)))*, `cj_2*` : iN($lsize((Jnn_2 : Jnn <: lanetype)))*}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))), EXTADD_PAIRWISE_vextunop__(sx), c_1) = c
    -- if (ci*{ci <- `ci*`} = $lanes_(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), c_1))
    -- if ($concat_(syntax iN($lsizenn1((Jnn_2 : Jnn <: lanetype))), [cj_1 cj_2]*{cj_1 <- `cj_1*`, cj_2 <- `cj_2*`}) = $extend__($lsizenn1((Jnn_1 : Jnn <: lanetype)), $lsizenn2((Jnn_2 : Jnn <: lanetype)), sx, ci)*{ci <- `ci*`})
    -- if (c = $inv_lanes_(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), $iadd_($lsizenn2((Jnn_2 : Jnn <: lanetype)), cj_1, cj_2)*{cj_1 <- `cj_1*`, cj_2 <- `cj_2*`}))

;; ../specification/wasm-2.0/3-numerics.spectec:605.1-606.45
def $vextbinop__(ishape_1 : ishape, ishape_2 : ishape, vextbinop__ : vextbinop__(ishape_1, ishape_2), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; ../specification/wasm-2.0/3-numerics.spectec:615.1-618.178
  def $vextbinop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, half : half, sx : sx, c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), c : vec_(V128_Vnn), `ci_1*` : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))))*, `ci_2*` : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))))*}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))), EXTMUL_vextbinop__(half, sx), c_1, c_2) = c
    -- if (ci_1*{ci_1 <- `ci_1*`} = $lanes_(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), c_1)[$half(half, 0, M_2) : M_2])
    -- if (ci_2*{ci_2 <- `ci_2*`} = $lanes_(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), c_2)[$half(half, 0, M_2) : M_2])
    -- if (c = $inv_lanes_(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), $imul_($lsizenn2((Jnn_2 : Jnn <: lanetype)), $extend__($lsizenn1((Jnn_1 : Jnn <: lanetype)), $lsizenn2((Jnn_2 : Jnn <: lanetype)), sx, ci_1), $extend__($lsizenn1((Jnn_1 : Jnn <: lanetype)), $lsizenn2((Jnn_2 : Jnn <: lanetype)), sx, ci_2))*{ci_1 <- `ci_1*`, ci_2 <- `ci_2*`}))
  ;; ../specification/wasm-2.0/3-numerics.spectec:620.1-626.76
  def $vextbinop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), c : vec_(V128_Vnn), `ci_1*` : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))))*, `ci_2*` : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))))*, `cj_1*` : iN($lsize((Jnn_2 : Jnn <: lanetype)))*, `cj_2*` : iN($lsize((Jnn_2 : Jnn <: lanetype)))*}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))), DOTS_vextbinop__, c_1, c_2) = c
    -- if (ci_1*{ci_1 <- `ci_1*`} = $lanes_(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), c_1))
    -- if (ci_2*{ci_2 <- `ci_2*`} = $lanes_(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), c_2))
    -- if ($concat_(syntax iN($lsizenn2((Jnn_2 : Jnn <: lanetype))), [cj_1 cj_2]*{cj_1 <- `cj_1*`, cj_2 <- `cj_2*`}) = $imul_($lsizenn2((Jnn_2 : Jnn <: lanetype)), $extend__($lsizenn1((Jnn_1 : Jnn <: lanetype)), $lsizenn2((Jnn_2 : Jnn <: lanetype)), S_sx, ci_1), $extend__($lsizenn1((Jnn_1 : Jnn <: lanetype)), $lsizenn2((Jnn_2 : Jnn <: lanetype)), S_sx, ci_2))*{ci_1 <- `ci_1*`, ci_2 <- `ci_2*`})
    -- if (c = $inv_lanes_(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), $iadd_($lsizenn2((Jnn_2 : Jnn <: lanetype)), cj_1, cj_2)*{cj_1 <- `cj_1*`, cj_2 <- `cj_2*`}))

;; ../specification/wasm-2.0/3-numerics.spectec:628.1-629.31
def $vshiftop_(ishape : ishape, vshiftop_ : vshiftop_(ishape), lane_ : lane_($lanetype(ishape!`%`_ishape.0)), u32 : u32) : lane_($lanetype(ishape!`%`_ishape.0))
  ;; ../specification/wasm-2.0/3-numerics.spectec:631.1-631.90
  def $vshiftop_{Jnn : Jnn, M : M, lane : lane_($lanetype(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)))!`%`_ishape.0)), n : n}(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))), SHL_vshiftop_, lane, `%`_u32(n)) = $ishl_($lsizenn((Jnn : Jnn <: lanetype)), lane, `%`_iN((n \ $lsizenn((Jnn : Jnn <: lanetype)))))
  ;; ../specification/wasm-2.0/3-numerics.spectec:632.1-632.97
  def $vshiftop_{Jnn : Jnn, M : M, sx : sx, lane : lane_($lanetype(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)))!`%`_ishape.0)), n : n}(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))), SHR_vshiftop_(sx), lane, `%`_u32(n)) = $ishr_($lsizenn((Jnn : Jnn <: lanetype)), sx, lane, `%`_iN((n \ $lsizenn((Jnn : Jnn <: lanetype)))))

;; ../specification/wasm-2.0/4-runtime.spectec:5.1-5.39
syntax addr = nat

;; ../specification/wasm-2.0/4-runtime.spectec:6.1-6.53
syntax funcaddr = addr

;; ../specification/wasm-2.0/4-runtime.spectec:7.1-7.53
syntax globaladdr = addr

;; ../specification/wasm-2.0/4-runtime.spectec:8.1-8.51
syntax tableaddr = addr

;; ../specification/wasm-2.0/4-runtime.spectec:9.1-9.50
syntax memaddr = addr

;; ../specification/wasm-2.0/4-runtime.spectec:10.1-10.49
syntax elemaddr = addr

;; ../specification/wasm-2.0/4-runtime.spectec:11.1-11.49
syntax dataaddr = addr

;; ../specification/wasm-2.0/4-runtime.spectec:12.1-12.49
syntax hostaddr = addr

;; ../specification/wasm-2.0/4-runtime.spectec:25.1-26.70
syntax externaddr = 
  | FUNC(funcaddr : funcaddr)
  | GLOBAL(globaladdr : globaladdr)
  | TABLE(tableaddr : tableaddr)
  | MEM(memaddr : memaddr)

;; ../specification/wasm-2.0/4-runtime.spectec:37.1-38.62
syntax num = 
  | CONST(numtype : numtype, num_(numtype))

;; ../specification/wasm-2.0/4-runtime.spectec:39.1-40.62
syntax vec = 
  | VCONST(vectype : vectype, vec_(vectype))

;; ../specification/wasm-2.0/4-runtime.spectec:41.1-42.71
syntax ref = 
  | `REF.NULL`(reftype : reftype)
  | `REF.FUNC_ADDR`(funcaddr : funcaddr)
  | `REF.HOST_ADDR`(hostaddr : hostaddr)

;; ../specification/wasm-2.0/4-runtime.spectec:43.1-44.20
syntax val = 
  | CONST(numtype : numtype, num_(numtype))
  | VCONST(vectype : vectype, vec_(vectype))
  | `REF.NULL`(reftype : reftype)
  | `REF.FUNC_ADDR`(funcaddr : funcaddr)
  | `REF.HOST_ADDR`(hostaddr : hostaddr)

;; ../specification/wasm-2.0/4-runtime.spectec:46.1-47.22
syntax result = 
  | _VALS(`val*` : val*)
  | TRAP

;; ../specification/wasm-2.0/4-runtime.spectec:78.1-80.22
syntax exportinst = 
{
  NAME name,
  ADDR externaddr
}

;; ../specification/wasm-2.0/4-runtime.spectec:82.1-90.26
syntax moduleinst = 
{
  TYPES functype*,
  FUNCS funcaddr*,
  GLOBALS globaladdr*,
  TABLES tableaddr*,
  MEMS memaddr*,
  ELEMS elemaddr*,
  DATAS dataaddr*,
  EXPORTS exportinst*
}

;; ../specification/wasm-2.0/4-runtime.spectec:60.1-63.16
syntax funcinst = 
{
  TYPE functype,
  MODULE moduleinst,
  CODE func
}

;; ../specification/wasm-2.0/4-runtime.spectec:64.1-66.16
syntax globalinst = 
{
  TYPE globaltype,
  VALUE val
}

;; ../specification/wasm-2.0/4-runtime.spectec:67.1-69.16
syntax tableinst = 
{
  TYPE tabletype,
  REFS ref*
}

;; ../specification/wasm-2.0/4-runtime.spectec:70.1-72.18
syntax meminst = 
{
  TYPE memtype,
  BYTES byte*
}

;; ../specification/wasm-2.0/4-runtime.spectec:73.1-75.16
syntax eleminst = 
{
  TYPE elemtype,
  REFS ref*
}

;; ../specification/wasm-2.0/4-runtime.spectec:76.1-77.18
syntax datainst = 
{
  BYTES byte*
}

;; ../specification/wasm-2.0/4-runtime.spectec:104.1-110.22
syntax store = 
{
  FUNCS funcinst*,
  GLOBALS globalinst*,
  TABLES tableinst*,
  MEMS meminst*,
  ELEMS eleminst*,
  DATAS datainst*
}

;; ../specification/wasm-2.0/4-runtime.spectec:112.1-114.24
syntax frame = 
{
  LOCALS val*,
  MODULE moduleinst
}

;; ../specification/wasm-2.0/4-runtime.spectec:116.1-116.47
syntax state = 
  | `%;%`(store : store, frame : frame)

;; ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9
rec {

;; ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9
syntax admininstr = 
  | NOP
  | UNREACHABLE
  | DROP
  | SELECT(`valtype*?` : valtype*?)
  | BLOCK(blocktype : blocktype, `instr*` : instr*)
  | LOOP(blocktype : blocktype, `instr*` : instr*)
  | `IF%%ELSE%`(blocktype : blocktype, `instr*` : instr*, `instr*` : instr*)
  | BR(labelidx : labelidx)
  | BR_IF(labelidx : labelidx)
  | BR_TABLE(`labelidx*` : labelidx*, labelidx : labelidx)
  | CALL(funcidx : funcidx)
  | CALL_INDIRECT(tableidx : tableidx, typeidx : typeidx)
  | RETURN
  | CONST(numtype : numtype, num_(numtype))
  | UNOP(numtype : numtype, unop_(numtype))
  | BINOP(numtype : numtype, binop_(numtype))
  | TESTOP(numtype : numtype, testop_(numtype))
  | RELOP(numtype : numtype, relop_(numtype))
  | CVTOP(numtype_1 : numtype, numtype_2 : numtype, cvtop__(numtype_2, numtype_1))
    -- if (numtype_1 =/= numtype_2)
  | EXTEND(numtype : numtype, n : n)
  | VCONST(vectype : vectype, vec_(vectype))
  | VVUNOP(vectype : vectype, vvunop : vvunop)
  | VVBINOP(vectype : vectype, vvbinop : vvbinop)
  | VVTERNOP(vectype : vectype, vvternop : vvternop)
  | VVTESTOP(vectype : vectype, vvtestop : vvtestop)
  | VUNOP(shape : shape, vunop_(shape))
  | VBINOP(shape : shape, vbinop_(shape))
  | VTESTOP(shape : shape, vtestop_(shape))
  | VRELOP(shape : shape, vrelop_(shape))
  | VSHIFTOP(ishape : ishape, vshiftop_(ishape))
  | VBITMASK(ishape : ishape)
  | VSWIZZLE(ishape : ishape)
    -- if (ishape = `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))))
  | VSHUFFLE(ishape : ishape, `laneidx*` : laneidx*)
    -- if ((ishape = `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16)))) /\ (|laneidx*{laneidx <- `laneidx*`}| = 16))
  | VSPLAT(shape : shape)
  | VEXTRACT_LANE(shape : shape, `sx?` : sx?, laneidx : laneidx)
    -- if (($lanetype(shape) <- [I32_lanetype I64_lanetype F32_lanetype F64_lanetype]) <=> (sx?{sx <- `sx?`} = ?()))
  | VREPLACE_LANE(shape : shape, laneidx : laneidx)
  | VEXTUNOP(ishape_1 : ishape, ishape_2 : ishape, vextunop__(ishape_2, ishape_1))
  | VEXTBINOP(ishape_1 : ishape, ishape_2 : ishape, vextbinop__(ishape_2, ishape_1))
  | VNARROW(ishape_1 : ishape, ishape_2 : ishape, sx : sx)
    -- if (($lsize($lanetype(ishape_2!`%`_ishape.0)) = (2 * $lsize($lanetype(ishape_1!`%`_ishape.0)))) /\ ((2 * $lsize($lanetype(ishape_1!`%`_ishape.0))) <= 32))
  | VCVTOP(shape_1 : shape, shape_2 : shape, vcvtop__(shape_2, shape_1))
  | `REF.NULL`(reftype : reftype)
  | `REF.FUNC`(funcidx : funcidx)
  | `REF.IS_NULL`
  | `LOCAL.GET`(localidx : localidx)
  | `LOCAL.SET`(localidx : localidx)
  | `LOCAL.TEE`(localidx : localidx)
  | `GLOBAL.GET`(globalidx : globalidx)
  | `GLOBAL.SET`(globalidx : globalidx)
  | `TABLE.GET`(tableidx : tableidx)
  | `TABLE.SET`(tableidx : tableidx)
  | `TABLE.SIZE`(tableidx : tableidx)
  | `TABLE.GROW`(tableidx : tableidx)
  | `TABLE.FILL`(tableidx : tableidx)
  | `TABLE.COPY`(tableidx : tableidx, tableidx : tableidx)
  | `TABLE.INIT`(tableidx : tableidx, elemidx : elemidx)
  | `ELEM.DROP`(elemidx : elemidx)
  | LOAD(numtype : numtype, loadop_(numtype)?, memarg : memarg)
  | STORE(numtype : numtype, `sz?` : sz?, memarg : memarg) {`Inn?` : Inn?}
    -- (if ((numtype = (Inn : Inn <: numtype)) /\ (sz!`%`_sz.0 < $sizenn((Inn : Inn <: numtype)))))?{Inn <- `Inn?`, sz <- `sz?`}
  | VLOAD(vectype : vectype, vloadop_(vectype)?, memarg : memarg)
  | VLOAD_LANE(vectype : vectype, sz : sz, memarg : memarg, laneidx : laneidx)
  | VSTORE(vectype : vectype, memarg : memarg)
  | VSTORE_LANE(vectype : vectype, sz : sz, memarg : memarg, laneidx : laneidx)
  | `MEMORY.SIZE`
  | `MEMORY.GROW`
  | `MEMORY.FILL`
  | `MEMORY.COPY`
  | `MEMORY.INIT`(dataidx : dataidx)
  | `DATA.DROP`(dataidx : dataidx)
  | `REF.FUNC_ADDR`(funcaddr : funcaddr)
  | `REF.HOST_ADDR`(hostaddr : hostaddr)
  | CALL_ADDR(funcaddr : funcaddr)
  | `LABEL_%{%}%`(n : n, `instr*` : instr*, `admininstr*` : admininstr*)
  | `FRAME_%{%}%`(n : n, frame : frame, `admininstr*` : admininstr*)
  | TRAP
}

;; ../specification/wasm-2.0/4-runtime.spectec:117.1-117.62
syntax config = 
  | `%;%`(state : state, `admininstr*` : admininstr*)

;; ../specification/wasm-2.0/5-runtime-aux.spectec:7.1-7.43
def $default_(valtype : valtype) : val
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:9.1-9.35
  def $default_(I32_valtype) = CONST_val(I32_numtype, `%`_num_(0))
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:10.1-10.35
  def $default_(I64_valtype) = CONST_val(I64_numtype, `%`_num_(0))
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:11.1-11.44
  def $default_(F32_valtype) = CONST_val(F32_numtype, $fzero(32))
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:12.1-12.44
  def $default_(F64_valtype) = CONST_val(F64_numtype, $fzero(64))
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:13.1-13.38
  def $default_(V128_valtype) = VCONST_val(V128_vectype, `%`_vec_(0))
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:14.1-14.44
  def $default_(FUNCREF_valtype) = `REF.NULL`_val(FUNCREF_reftype)
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:15.1-15.48
  def $default_(EXTERNREF_valtype) = `REF.NULL`_val(EXTERNREF_reftype)

;; ../specification/wasm-2.0/5-runtime-aux.spectec:20.1-20.63
rec {

;; ../specification/wasm-2.0/5-runtime-aux.spectec:20.1-20.63
def $funcsxa(externaddr*) : funcaddr*
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:25.1-25.24
  def $funcsxa([]) = []
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:26.1-26.47
  def $funcsxa{fa : funcaddr, `xv*` : externaddr*}([FUNC_externaddr(fa)] ++ xv*{xv <- `xv*`}) = [fa] ++ $funcsxa(xv*{xv <- `xv*`})
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:27.1-27.59
  def $funcsxa{externaddr : externaddr, `xv*` : externaddr*}([externaddr] ++ xv*{xv <- `xv*`}) = $funcsxa(xv*{xv <- `xv*`})
    -- otherwise
}

;; ../specification/wasm-2.0/5-runtime-aux.spectec:21.1-21.65
rec {

;; ../specification/wasm-2.0/5-runtime-aux.spectec:21.1-21.65
def $globalsxa(externaddr*) : globaladdr*
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:29.1-29.26
  def $globalsxa([]) = []
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:30.1-30.53
  def $globalsxa{ga : globaladdr, `xv*` : externaddr*}([GLOBAL_externaddr(ga)] ++ xv*{xv <- `xv*`}) = [ga] ++ $globalsxa(xv*{xv <- `xv*`})
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:31.1-31.63
  def $globalsxa{externaddr : externaddr, `xv*` : externaddr*}([externaddr] ++ xv*{xv <- `xv*`}) = $globalsxa(xv*{xv <- `xv*`})
    -- otherwise
}

;; ../specification/wasm-2.0/5-runtime-aux.spectec:22.1-22.64
rec {

;; ../specification/wasm-2.0/5-runtime-aux.spectec:22.1-22.64
def $tablesxa(externaddr*) : tableaddr*
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:33.1-33.25
  def $tablesxa([]) = []
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:34.1-34.50
  def $tablesxa{ta : tableaddr, `xv*` : externaddr*}([TABLE_externaddr(ta)] ++ xv*{xv <- `xv*`}) = [ta] ++ $tablesxa(xv*{xv <- `xv*`})
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:35.1-35.61
  def $tablesxa{externaddr : externaddr, `xv*` : externaddr*}([externaddr] ++ xv*{xv <- `xv*`}) = $tablesxa(xv*{xv <- `xv*`})
    -- otherwise
}

;; ../specification/wasm-2.0/5-runtime-aux.spectec:23.1-23.62
rec {

;; ../specification/wasm-2.0/5-runtime-aux.spectec:23.1-23.62
def $memsxa(externaddr*) : memaddr*
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:37.1-37.23
  def $memsxa([]) = []
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:38.1-38.44
  def $memsxa{ma : memaddr, `xv*` : externaddr*}([MEM_externaddr(ma)] ++ xv*{xv <- `xv*`}) = [ma] ++ $memsxa(xv*{xv <- `xv*`})
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:39.1-39.57
  def $memsxa{externaddr : externaddr, `xv*` : externaddr*}([externaddr] ++ xv*{xv <- `xv*`}) = $memsxa(xv*{xv <- `xv*`})
    -- otherwise
}

;; ../specification/wasm-2.0/5-runtime-aux.spectec:48.1-48.57
def $store(state : state) : store
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:51.1-51.23
  def $store{s : store, f : frame}(`%;%`_state(s, f)) = s

;; ../specification/wasm-2.0/5-runtime-aux.spectec:49.1-49.57
def $frame(state : state) : frame
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:52.1-52.23
  def $frame{s : store, f : frame}(`%;%`_state(s, f)) = f

;; ../specification/wasm-2.0/5-runtime-aux.spectec:55.1-55.64
def $funcaddr(state : state) : funcaddr*
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:56.1-56.39
  def $funcaddr{s : store, f : frame}(`%;%`_state(s, f)) = f.MODULE_frame.FUNCS_moduleinst

;; ../specification/wasm-2.0/5-runtime-aux.spectec:58.1-58.57
def $funcinst(state : state) : funcinst*
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:66.1-66.32
  def $funcinst{s : store, f : frame}(`%;%`_state(s, f)) = s.FUNCS_store

;; ../specification/wasm-2.0/5-runtime-aux.spectec:59.1-59.59
def $globalinst(state : state) : globalinst*
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:67.1-67.36
  def $globalinst{s : store, f : frame}(`%;%`_state(s, f)) = s.GLOBALS_store

;; ../specification/wasm-2.0/5-runtime-aux.spectec:60.1-60.58
def $tableinst(state : state) : tableinst*
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:68.1-68.34
  def $tableinst{s : store, f : frame}(`%;%`_state(s, f)) = s.TABLES_store

;; ../specification/wasm-2.0/5-runtime-aux.spectec:61.1-61.56
def $meminst(state : state) : meminst*
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:69.1-69.30
  def $meminst{s : store, f : frame}(`%;%`_state(s, f)) = s.MEMS_store

;; ../specification/wasm-2.0/5-runtime-aux.spectec:62.1-62.57
def $eleminst(state : state) : eleminst*
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:70.1-70.32
  def $eleminst{s : store, f : frame}(`%;%`_state(s, f)) = s.ELEMS_store

;; ../specification/wasm-2.0/5-runtime-aux.spectec:63.1-63.57
def $datainst(state : state) : datainst*
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:71.1-71.32
  def $datainst{s : store, f : frame}(`%;%`_state(s, f)) = s.DATAS_store

;; ../specification/wasm-2.0/5-runtime-aux.spectec:64.1-64.58
def $moduleinst(state : state) : moduleinst
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:72.1-72.35
  def $moduleinst{s : store, f : frame}(`%;%`_state(s, f)) = f.MODULE_frame

;; ../specification/wasm-2.0/5-runtime-aux.spectec:74.1-74.66
def $type(state : state, typeidx : typeidx) : functype
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:83.1-83.41
  def $type{s : store, f : frame, x : idx}(`%;%`_state(s, f), x) = f.MODULE_frame.TYPES_moduleinst[x!`%`_idx.0]

;; ../specification/wasm-2.0/5-runtime-aux.spectec:75.1-75.66
def $func(state : state, funcidx : funcidx) : funcinst
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:84.1-84.50
  def $func{s : store, f : frame, x : idx}(`%;%`_state(s, f), x) = s.FUNCS_store[f.MODULE_frame.FUNCS_moduleinst[x!`%`_idx.0]]

;; ../specification/wasm-2.0/5-runtime-aux.spectec:76.1-76.68
def $global(state : state, globalidx : globalidx) : globalinst
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:85.1-85.56
  def $global{s : store, f : frame, x : idx}(`%;%`_state(s, f), x) = s.GLOBALS_store[f.MODULE_frame.GLOBALS_moduleinst[x!`%`_idx.0]]

;; ../specification/wasm-2.0/5-runtime-aux.spectec:77.1-77.67
def $table(state : state, tableidx : tableidx) : tableinst
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:86.1-86.53
  def $table{s : store, f : frame, x : idx}(`%;%`_state(s, f), x) = s.TABLES_store[f.MODULE_frame.TABLES_moduleinst[x!`%`_idx.0]]

;; ../specification/wasm-2.0/5-runtime-aux.spectec:78.1-78.65
def $mem(state : state, memidx : memidx) : meminst
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:87.1-87.47
  def $mem{s : store, f : frame, x : idx}(`%;%`_state(s, f), x) = s.MEMS_store[f.MODULE_frame.MEMS_moduleinst[x!`%`_idx.0]]

;; ../specification/wasm-2.0/5-runtime-aux.spectec:79.1-79.66
def $elem(state : state, tableidx : tableidx) : eleminst
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:88.1-88.50
  def $elem{s : store, f : frame, x : idx}(`%;%`_state(s, f), x) = s.ELEMS_store[f.MODULE_frame.ELEMS_moduleinst[x!`%`_idx.0]]

;; ../specification/wasm-2.0/5-runtime-aux.spectec:80.1-80.66
def $data(state : state, dataidx : dataidx) : datainst
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:89.1-89.50
  def $data{s : store, f : frame, x : idx}(`%;%`_state(s, f), x) = s.DATAS_store[f.MODULE_frame.DATAS_moduleinst[x!`%`_idx.0]]

;; ../specification/wasm-2.0/5-runtime-aux.spectec:81.1-81.67
def $local(state : state, localidx : localidx) : val
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:90.1-90.36
  def $local{s : store, f : frame, x : idx}(`%;%`_state(s, f), x) = f.LOCALS_frame[x!`%`_idx.0]

;; ../specification/wasm-2.0/5-runtime-aux.spectec:95.1-95.89
def $with_local(state : state, localidx : localidx, val : val) : state
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:104.1-104.53
  def $with_local{s : store, f : frame, x : idx, v : val}(`%;%`_state(s, f), x, v) = `%;%`_state(s, f[LOCALS_frame[x!`%`_idx.0] = v])

;; ../specification/wasm-2.0/5-runtime-aux.spectec:96.1-96.96
def $with_global(state : state, globalidx : globalidx, val : val) : state
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:105.1-105.79
  def $with_global{s : store, f : frame, x : idx, v : val}(`%;%`_state(s, f), x, v) = `%;%`_state(s[GLOBALS_store[f.MODULE_frame.GLOBALS_moduleinst[x!`%`_idx.0]].VALUE_globalinst = v], f)

;; ../specification/wasm-2.0/5-runtime-aux.spectec:97.1-97.97
def $with_table(state : state, tableidx : tableidx, nat : nat, ref : ref) : state
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:106.1-106.81
  def $with_table{s : store, f : frame, x : idx, i : nat, r : ref}(`%;%`_state(s, f), x, i, r) = `%;%`_state(s[TABLES_store[f.MODULE_frame.TABLES_moduleinst[x!`%`_idx.0]].REFS_tableinst[i] = r], f)

;; ../specification/wasm-2.0/5-runtime-aux.spectec:98.1-98.89
def $with_tableinst(state : state, tableidx : tableidx, tableinst : tableinst) : state
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:107.1-107.76
  def $with_tableinst{s : store, f : frame, x : idx, ti : tableinst}(`%;%`_state(s, f), x, ti) = `%;%`_state(s[TABLES_store[f.MODULE_frame.TABLES_moduleinst[x!`%`_idx.0]] = ti], f)

;; ../specification/wasm-2.0/5-runtime-aux.spectec:99.1-99.100
def $with_mem(state : state, memidx : memidx, nat : nat, nat : nat, byte*) : state
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:108.1-108.85
  def $with_mem{s : store, f : frame, x : idx, i : nat, j : nat, `b*` : byte*}(`%;%`_state(s, f), x, i, j, b*{b <- `b*`}) = `%;%`_state(s[MEMS_store[f.MODULE_frame.MEMS_moduleinst[x!`%`_idx.0]].BYTES_meminst[i : j] = b*{b <- `b*`}], f)

;; ../specification/wasm-2.0/5-runtime-aux.spectec:100.1-100.87
def $with_meminst(state : state, memidx : memidx, meminst : meminst) : state
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:109.1-109.70
  def $with_meminst{s : store, f : frame, x : idx, mi : meminst}(`%;%`_state(s, f), x, mi) = `%;%`_state(s[MEMS_store[f.MODULE_frame.MEMS_moduleinst[x!`%`_idx.0]] = mi], f)

;; ../specification/wasm-2.0/5-runtime-aux.spectec:101.1-101.93
def $with_elem(state : state, elemidx : elemidx, ref*) : state
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:110.1-110.74
  def $with_elem{s : store, f : frame, x : idx, `r*` : ref*}(`%;%`_state(s, f), x, r*{r <- `r*`}) = `%;%`_state(s[ELEMS_store[f.MODULE_frame.ELEMS_moduleinst[x!`%`_idx.0]].REFS_eleminst = r*{r <- `r*`}], f)

;; ../specification/wasm-2.0/5-runtime-aux.spectec:102.1-102.94
def $with_data(state : state, dataidx : dataidx, byte*) : state
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:111.1-111.75
  def $with_data{s : store, f : frame, x : idx, `b*` : byte*}(`%;%`_state(s, f), x, b*{b <- `b*`}) = `%;%`_state(s[DATAS_store[f.MODULE_frame.DATAS_moduleinst[x!`%`_idx.0]].BYTES_datainst = b*{b <- `b*`}], f)

;; ../specification/wasm-2.0/5-runtime-aux.spectec:116.1-116.62
def $growtable(tableinst : tableinst, nat : nat, ref : ref) : tableinst
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:119.1-123.54
  def $growtable{ti : tableinst, n : n, r : ref, ti' : tableinst, i : u32, `j?` : u32?, rt : reftype, `r'*` : ref*, i' : nat}(ti, n, r) = ti'
    -- if (ti = {TYPE `%%`_tabletype(`[%..%]`_limits(i, j?{j <- `j?`}), rt), REFS r'*{r' <- `r'*`}})
    -- if (i' = (|r'*{r' <- `r'*`}| + n))
    -- (if (i' <= j!`%`_u32.0))?{j <- `j?`}
    -- if (ti' = {TYPE `%%`_tabletype(`[%..%]`_limits(`%`_u32(i'), j?{j <- `j?`}), rt), REFS r'*{r' <- `r'*`} ++ r^n{}})

;; ../specification/wasm-2.0/5-runtime-aux.spectec:117.1-117.62
def $growmemory(meminst : meminst, nat : nat) : meminst
  ;; ../specification/wasm-2.0/5-runtime-aux.spectec:125.1-130.75
  def $growmemory{mi : meminst, n : n, mi' : meminst, i : u32, `j?` : u32?, `b*` : byte*, i' : rat}(mi, n) = mi'
    -- if (mi = {TYPE `%PAGE`_memtype(`[%..%]`_limits(i, j?{j <- `j?`})), BYTES b*{b <- `b*`}})
    -- if (i' = (((|b*{b <- `b*`}| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) + (n : nat <:> rat)))
    -- (if (i' <= (j!`%`_u32.0 : nat <:> rat)))?{j <- `j?`}
    -- if (i' <= ((2 ^ 16) : nat <:> rat))
    -- if (mi' = {TYPE `%PAGE`_memtype(`[%..%]`_limits(`%`_u32((i' : rat <:> nat)), j?{j <- `j?`})), BYTES b*{b <- `b*`} ++ `%`_byte(0)^(n * (64 * $Ki)){}})

;; ../specification/wasm-2.0/6-typing.spectec:5.1-9.62
syntax context = 
{
  TYPES functype*,
  FUNCS functype*,
  GLOBALS globaltype*,
  TABLES tabletype*,
  MEMS memtype*,
  ELEMS elemtype*,
  DATAS datatype*,
  LOCALS valtype*,
  LABELS resulttype*,
  RETURN resulttype?
}

;; ../specification/wasm-2.0/6-typing.spectec:19.1-19.66
relation Limits_ok: `|-%:%`(limits, nat)
  ;; ../specification/wasm-2.0/6-typing.spectec:27.1-30.23
  rule _{n : n, `m?` : m?, k : nat}:
    `|-%:%`(`[%..%]`_limits(`%`_u32(n), `%`_u32(m)?{m <- `m?`}), k)
    -- if (n <= k)
    -- (if ((n <= m) /\ (m <= k)))?{m <- `m?`}

;; ../specification/wasm-2.0/6-typing.spectec:20.1-20.64
relation Functype_ok: `|-%:OK`(functype)
  ;; ../specification/wasm-2.0/6-typing.spectec:32.1-33.23
  rule _{`t_1*` : valtype*, `t_2*` : valtype*}:
    `|-%:OK`(`%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

;; ../specification/wasm-2.0/6-typing.spectec:21.1-21.66
relation Globaltype_ok: `|-%:OK`(globaltype)
  ;; ../specification/wasm-2.0/6-typing.spectec:35.1-36.17
  rule _{t : valtype}:
    `|-%:OK`(`%%`_globaltype(MUT_MUT?{}, t))

;; ../specification/wasm-2.0/6-typing.spectec:22.1-22.65
relation Tabletype_ok: `|-%:OK`(tabletype)
  ;; ../specification/wasm-2.0/6-typing.spectec:38.1-40.38
  rule _{limits : limits, reftype : reftype}:
    `|-%:OK`(`%%`_tabletype(limits, reftype))
    -- Limits_ok: `|-%:%`(limits, ((((2 ^ 32) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))

;; ../specification/wasm-2.0/6-typing.spectec:23.1-23.63
relation Memtype_ok: `|-%:OK`(memtype)
  ;; ../specification/wasm-2.0/6-typing.spectec:42.1-44.36
  rule _{limits : limits}:
    `|-%:OK`(`%PAGE`_memtype(limits))
    -- Limits_ok: `|-%:%`(limits, (2 ^ 16))

;; ../specification/wasm-2.0/6-typing.spectec:24.1-24.66
relation Externtype_ok: `|-%:OK`(externtype)
  ;; ../specification/wasm-2.0/6-typing.spectec:47.1-49.35
  rule func{functype : functype}:
    `|-%:OK`(FUNC_externtype(functype))
    -- Functype_ok: `|-%:OK`(functype)

  ;; ../specification/wasm-2.0/6-typing.spectec:51.1-53.39
  rule global{globaltype : globaltype}:
    `|-%:OK`(GLOBAL_externtype(globaltype))
    -- Globaltype_ok: `|-%:OK`(globaltype)

  ;; ../specification/wasm-2.0/6-typing.spectec:55.1-57.37
  rule table{tabletype : tabletype}:
    `|-%:OK`(TABLE_externtype(tabletype))
    -- Tabletype_ok: `|-%:OK`(tabletype)

  ;; ../specification/wasm-2.0/6-typing.spectec:59.1-61.33
  rule mem{memtype : memtype}:
    `|-%:OK`(MEM_externtype(memtype))
    -- Memtype_ok: `|-%:OK`(memtype)

;; ../specification/wasm-2.0/6-typing.spectec:71.1-71.69
relation Valtype_sub: `|-%<:%`(valtype, valtype)
  ;; ../specification/wasm-2.0/6-typing.spectec:74.1-75.12
  rule refl{t : valtype}:
    `|-%<:%`(t, t)

  ;; ../specification/wasm-2.0/6-typing.spectec:77.1-78.14
  rule bot{t : valtype}:
    `|-%<:%`(BOT_valtype, t)

;; ../specification/wasm-2.0/6-typing.spectec:72.1-72.76
relation Resulttype_sub: `|-%<:%`(resulttype, resulttype)
  ;; ../specification/wasm-2.0/6-typing.spectec:80.1-82.35
  rule _{`t_1*` : valtype*, `t_2*` : valtype*}:
    `|-%<:%`(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`}))
    -- (Valtype_sub: `|-%<:%`(t_1, t_2))*{t_1 <- `t_1*`, t_2 <- `t_2*`}

;; ../specification/wasm-2.0/6-typing.spectec:87.1-87.75
relation Limits_sub: `|-%<:%`(limits, limits)
  ;; ../specification/wasm-2.0/6-typing.spectec:95.1-98.22
  rule max{n_1 : n, m_1 : m, n_2 : n, `m_2?` : m?}:
    `|-%<:%`(`[%..%]`_limits(`%`_u32(n_1), ?(`%`_u32(m_1))), `[%..%]`_limits(`%`_u32(n_2), `%`_u32(m_2)?{m_2 <- `m_2?`}))
    -- if (n_1 >= n_2)
    -- (if (m_1 <= m_2))?{m_2 <- `m_2?`}

  ;; ../specification/wasm-2.0/6-typing.spectec:100.1-102.19
  rule eps{n_1 : n, n_2 : n}:
    `|-%<:%`(`[%..%]`_limits(`%`_u32(n_1), ?()), `[%..%]`_limits(`%`_u32(n_2), ?()))
    -- if (n_1 >= n_2)

;; ../specification/wasm-2.0/6-typing.spectec:88.1-88.73
relation Functype_sub: `|-%<:%`(functype, functype)
  ;; ../specification/wasm-2.0/6-typing.spectec:104.1-105.14
  rule _{ft : functype}:
    `|-%<:%`(ft, ft)

;; ../specification/wasm-2.0/6-typing.spectec:89.1-89.75
relation Globaltype_sub: `|-%<:%`(globaltype, globaltype)
  ;; ../specification/wasm-2.0/6-typing.spectec:107.1-108.14
  rule _{gt : globaltype}:
    `|-%<:%`(gt, gt)

;; ../specification/wasm-2.0/6-typing.spectec:90.1-90.74
relation Tabletype_sub: `|-%<:%`(tabletype, tabletype)
  ;; ../specification/wasm-2.0/6-typing.spectec:110.1-112.35
  rule _{lim_1 : limits, rt : reftype, lim_2 : limits}:
    `|-%<:%`(`%%`_tabletype(lim_1, rt), `%%`_tabletype(lim_2, rt))
    -- Limits_sub: `|-%<:%`(lim_1, lim_2)

;; ../specification/wasm-2.0/6-typing.spectec:91.1-91.72
relation Memtype_sub: `|-%<:%`(memtype, memtype)
  ;; ../specification/wasm-2.0/6-typing.spectec:114.1-116.35
  rule _{lim_1 : limits, lim_2 : limits}:
    `|-%<:%`(`%PAGE`_memtype(lim_1), `%PAGE`_memtype(lim_2))
    -- Limits_sub: `|-%<:%`(lim_1, lim_2)

;; ../specification/wasm-2.0/6-typing.spectec:92.1-92.75
relation Externtype_sub: `|-%<:%`(externtype, externtype)
  ;; ../specification/wasm-2.0/6-typing.spectec:119.1-121.35
  rule func{ft_1 : functype, ft_2 : functype}:
    `|-%<:%`(FUNC_externtype(ft_1), FUNC_externtype(ft_2))
    -- Functype_sub: `|-%<:%`(ft_1, ft_2)

  ;; ../specification/wasm-2.0/6-typing.spectec:123.1-125.37
  rule global{gt_1 : globaltype, gt_2 : globaltype}:
    `|-%<:%`(GLOBAL_externtype(gt_1), GLOBAL_externtype(gt_2))
    -- Globaltype_sub: `|-%<:%`(gt_1, gt_2)

  ;; ../specification/wasm-2.0/6-typing.spectec:127.1-129.36
  rule table{tt_1 : tabletype, tt_2 : tabletype}:
    `|-%<:%`(TABLE_externtype(tt_1), TABLE_externtype(tt_2))
    -- Tabletype_sub: `|-%<:%`(tt_1, tt_2)

  ;; ../specification/wasm-2.0/6-typing.spectec:131.1-133.34
  rule mem{mt_1 : memtype, mt_2 : memtype}:
    `|-%<:%`(MEM_externtype(mt_1), MEM_externtype(mt_2))
    -- Memtype_sub: `|-%<:%`(mt_1, mt_2)

;; ../specification/wasm-2.0/6-typing.spectec:202.1-202.76
relation Blocktype_ok: `%|-%:%`(context, blocktype, functype)
  ;; ../specification/wasm-2.0/6-typing.spectec:204.1-205.42
  rule valtype{C : context, `valtype?` : valtype?}:
    `%|-%:%`(C, _RESULT_blocktype(valtype?{valtype <- `valtype?`}), `%->%`_functype(`%`_resulttype([]), `%`_resulttype(lift(valtype?{valtype <- `valtype?`}))))

  ;; ../specification/wasm-2.0/6-typing.spectec:207.1-209.40
  rule typeidx{C : context, typeidx : typeidx, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, _IDX_blocktype(typeidx), `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.TYPES_context[typeidx!`%`_typeidx.0] = `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

;; ../specification/wasm-2.0/6-typing.spectec:141.1-142.65
rec {

;; ../specification/wasm-2.0/6-typing.spectec:141.1-141.64
relation Instr_ok: `%|-%:%`(context, instr, functype)
  ;; ../specification/wasm-2.0/6-typing.spectec:181.1-182.24
  rule nop{C : context}:
    `%|-%:%`(C, NOP_instr, `%->%`_functype(`%`_resulttype([]), `%`_resulttype([])))

  ;; ../specification/wasm-2.0/6-typing.spectec:184.1-185.34
  rule unreachable{C : context, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, UNREACHABLE_instr, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; ../specification/wasm-2.0/6-typing.spectec:187.1-188.23
  rule drop{C : context, t : valtype}:
    `%|-%:%`(C, DROP_instr, `%->%`_functype(`%`_resulttype([t]), `%`_resulttype([])))

  ;; ../specification/wasm-2.0/6-typing.spectec:191.1-192.31
  rule `select-expl`{C : context, t : valtype}:
    `%|-%:%`(C, SELECT_instr(?([t])), `%->%`_functype(`%`_resulttype([t t I32_valtype]), `%`_resulttype([t])))

  ;; ../specification/wasm-2.0/6-typing.spectec:194.1-197.37
  rule `select-impl`{C : context, t : valtype, t' : valtype, numtype : numtype, vectype : vectype}:
    `%|-%:%`(C, SELECT_instr(?()), `%->%`_functype(`%`_resulttype([t t I32_valtype]), `%`_resulttype([t])))
    -- Valtype_sub: `|-%<:%`(t, t')
    -- if ((t' = (numtype : numtype <: valtype)) \/ (t' = (vectype : vectype <: valtype)))

  ;; ../specification/wasm-2.0/6-typing.spectec:212.1-215.62
  rule block{C : context, bt : blocktype, `instr*` : instr*, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, BLOCK_instr(bt, instr*{instr <- `instr*`}), `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?()} +++ C, instr*{instr <- `instr*`}, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; ../specification/wasm-2.0/6-typing.spectec:217.1-220.62
  rule loop{C : context, bt : blocktype, `instr*` : instr*, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, LOOP_instr(bt, instr*{instr <- `instr*`}), `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [`%`_resulttype(t_1*{t_1 <- `t_1*`})], RETURN ?()} +++ C, instr*{instr <- `instr*`}, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; ../specification/wasm-2.0/6-typing.spectec:222.1-226.64
  rule if{C : context, bt : blocktype, `instr_1*` : instr*, `instr_2*` : instr*, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, `IF%%ELSE%`_instr(bt, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`}), `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [I32_valtype]), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?()} +++ C, instr_1*{instr_1 <- `instr_1*`}, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?()} +++ C, instr_2*{instr_2 <- `instr_2*`}, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; ../specification/wasm-2.0/6-typing.spectec:231.1-233.25
  rule br{C : context, l : labelidx, `t_1*` : valtype*, `t*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, BR_instr(l), `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.LABELS_context[l!`%`_labelidx.0]!`%`_resulttype.0 = t*{t <- `t*`})

  ;; ../specification/wasm-2.0/6-typing.spectec:235.1-237.25
  rule br_if{C : context, l : labelidx, `t*` : valtype*}:
    `%|-%:%`(C, BR_IF_instr(l), `%->%`_functype(`%`_resulttype(t*{t <- `t*`} ++ [I32_valtype]), `%`_resulttype(t*{t <- `t*`})))
    -- if (C.LABELS_context[l!`%`_labelidx.0]!`%`_resulttype.0 = t*{t <- `t*`})

  ;; ../specification/wasm-2.0/6-typing.spectec:239.1-242.43
  rule br_table{C : context, `l*` : labelidx*, l' : labelidx, `t_1*` : valtype*, `t*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, BR_TABLE_instr(l*{l <- `l*`}, l'), `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`} ++ [I32_valtype]), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (Resulttype_sub: `|-%<:%`(`%`_resulttype(t*{t <- `t*`}), C.LABELS_context[l!`%`_labelidx.0]))*{l <- `l*`}
    -- Resulttype_sub: `|-%<:%`(`%`_resulttype(t*{t <- `t*`}), C.LABELS_context[l'!`%`_labelidx.0])

  ;; ../specification/wasm-2.0/6-typing.spectec:247.1-249.34
  rule call{C : context, x : idx, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, CALL_instr(x), `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.FUNCS_context[x!`%`_idx.0] = `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; ../specification/wasm-2.0/6-typing.spectec:251.1-254.34
  rule call_indirect{C : context, x : idx, y : idx, `t_1*` : valtype*, `t_2*` : valtype*, lim : limits}:
    `%|-%:%`(C, CALL_INDIRECT_instr(x, y), `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [I32_valtype]), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%`_tabletype(lim, FUNCREF_reftype))
    -- if (C.TYPES_context[y!`%`_idx.0] = `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; ../specification/wasm-2.0/6-typing.spectec:256.1-258.24
  rule return{C : context, `t_1*` : valtype*, `t*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, RETURN_instr, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.RETURN_context = ?(`%`_resulttype(t*{t <- `t*`})))

  ;; ../specification/wasm-2.0/6-typing.spectec:263.1-264.33
  rule const{C : context, nt : numtype, c_nt : num_(nt)}:
    `%|-%:%`(C, CONST_instr(nt, c_nt), `%->%`_functype(`%`_resulttype([]), `%`_resulttype([(nt : numtype <: valtype)])))

  ;; ../specification/wasm-2.0/6-typing.spectec:266.1-267.34
  rule unop{C : context, nt : numtype, unop_nt : unop_(nt)}:
    `%|-%:%`(C, UNOP_instr(nt, unop_nt), `%->%`_functype(`%`_resulttype([(nt : numtype <: valtype)]), `%`_resulttype([(nt : numtype <: valtype)])))

  ;; ../specification/wasm-2.0/6-typing.spectec:269.1-270.39
  rule binop{C : context, nt : numtype, binop_nt : binop_(nt)}:
    `%|-%:%`(C, BINOP_instr(nt, binop_nt), `%->%`_functype(`%`_resulttype([(nt : numtype <: valtype) (nt : numtype <: valtype)]), `%`_resulttype([(nt : numtype <: valtype)])))

  ;; ../specification/wasm-2.0/6-typing.spectec:272.1-273.39
  rule testop{C : context, nt : numtype, testop_nt : testop_(nt)}:
    `%|-%:%`(C, TESTOP_instr(nt, testop_nt), `%->%`_functype(`%`_resulttype([(nt : numtype <: valtype)]), `%`_resulttype([I32_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:275.1-276.40
  rule relop{C : context, nt : numtype, relop_nt : relop_(nt)}:
    `%|-%:%`(C, RELOP_instr(nt, relop_nt), `%->%`_functype(`%`_resulttype([(nt : numtype <: valtype) (nt : numtype <: valtype)]), `%`_resulttype([I32_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:278.1-279.44
  rule cvtop{C : context, nt_1 : numtype, nt_2 : numtype, cvtop : cvtop__(nt_2, nt_1)}:
    `%|-%:%`(C, CVTOP_instr(nt_1, nt_2, cvtop), `%->%`_functype(`%`_resulttype([(nt_2 : numtype <: valtype)]), `%`_resulttype([(nt_1 : numtype <: valtype)])))

  ;; ../specification/wasm-2.0/6-typing.spectec:284.1-285.31
  rule `ref.null`{C : context, rt : reftype}:
    `%|-%:%`(C, `REF.NULL`_instr(rt), `%->%`_functype(`%`_resulttype([]), `%`_resulttype([(rt : reftype <: valtype)])))

  ;; ../specification/wasm-2.0/6-typing.spectec:287.1-289.24
  rule `ref.func`{C : context, x : idx, ft : functype}:
    `%|-%:%`(C, `REF.FUNC`_instr(x), `%->%`_functype(`%`_resulttype([]), `%`_resulttype([FUNCREF_valtype])))
    -- if (C.FUNCS_context[x!`%`_idx.0] = ft)

  ;; ../specification/wasm-2.0/6-typing.spectec:291.1-292.31
  rule `ref.is_null`{C : context, rt : reftype}:
    `%|-%:%`(C, `REF.IS_NULL`_instr, `%->%`_functype(`%`_resulttype([(rt : reftype <: valtype)]), `%`_resulttype([I32_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:297.1-298.35
  rule vconst{C : context, c : vec_(V128_Vnn)}:
    `%|-%:%`(C, VCONST_instr(V128_vectype, c), `%->%`_functype(`%`_resulttype([]), `%`_resulttype([V128_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:300.1-301.41
  rule vvunop{C : context, vvunop : vvunop}:
    `%|-%:%`(C, VVUNOP_instr(V128_vectype, vvunop), `%->%`_functype(`%`_resulttype([V128_valtype]), `%`_resulttype([V128_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:303.1-304.48
  rule vvbinop{C : context, vvbinop : vvbinop}:
    `%|-%:%`(C, VVBINOP_instr(V128_vectype, vvbinop), `%->%`_functype(`%`_resulttype([V128_valtype V128_valtype]), `%`_resulttype([V128_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:306.1-307.55
  rule vvternop{C : context, vvternop : vvternop}:
    `%|-%:%`(C, VVTERNOP_instr(V128_vectype, vvternop), `%->%`_functype(`%`_resulttype([V128_valtype V128_valtype V128_valtype]), `%`_resulttype([V128_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:309.1-310.44
  rule vvtestop{C : context, vvtestop : vvtestop}:
    `%|-%:%`(C, VVTESTOP_instr(V128_vectype, vvtestop), `%->%`_functype(`%`_resulttype([V128_valtype]), `%`_resulttype([I32_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:312.1-313.40
  rule vunop{C : context, sh : shape, vunop_sh : vunop_(sh)}:
    `%|-%:%`(C, VUNOP_instr(sh, vunop_sh), `%->%`_functype(`%`_resulttype([V128_valtype]), `%`_resulttype([V128_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:315.1-316.47
  rule vbinop{C : context, sh : shape, vbinop_sh : vbinop_(sh)}:
    `%|-%:%`(C, VBINOP_instr(sh, vbinop_sh), `%->%`_functype(`%`_resulttype([V128_valtype V128_valtype]), `%`_resulttype([V128_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:318.1-319.43
  rule vtestop{C : context, sh : shape, vtestop_sh : vtestop_(sh)}:
    `%|-%:%`(C, VTESTOP_instr(sh, vtestop_sh), `%->%`_functype(`%`_resulttype([V128_valtype]), `%`_resulttype([I32_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:321.1-322.47
  rule vrelop{C : context, sh : shape, vrelop_sh : vrelop_(sh)}:
    `%|-%:%`(C, VRELOP_instr(sh, vrelop_sh), `%->%`_functype(`%`_resulttype([V128_valtype V128_valtype]), `%`_resulttype([V128_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:324.1-325.50
  rule vshiftop{C : context, sh : ishape, vshiftop_sh : vshiftop_(sh)}:
    `%|-%:%`(C, VSHIFTOP_instr(sh, vshiftop_sh), `%->%`_functype(`%`_resulttype([V128_valtype I32_valtype]), `%`_resulttype([V128_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:327.1-328.33
  rule vbitmask{C : context, sh : ishape}:
    `%|-%:%`(C, VBITMASK_instr(sh), `%->%`_functype(`%`_resulttype([V128_valtype]), `%`_resulttype([I32_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:330.1-331.39
  rule vswizzle{C : context, sh : ishape}:
    `%|-%:%`(C, VSWIZZLE_instr(sh), `%->%`_functype(`%`_resulttype([V128_valtype V128_valtype]), `%`_resulttype([V128_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:333.1-335.29
  rule vshuffle{C : context, sh : ishape, `i*` : laneidx*}:
    `%|-%:%`(C, VSHUFFLE_instr(sh, i*{i <- `i*`}), `%->%`_functype(`%`_resulttype([V128_valtype V128_valtype]), `%`_resulttype([V128_valtype])))
    -- (if (i!`%`_laneidx.0 < (2 * $dim(sh!`%`_ishape.0)!`%`_dim.0)))*{i <- `i*`}

  ;; ../specification/wasm-2.0/6-typing.spectec:337.1-338.41
  rule vsplat{C : context, sh : shape}:
    `%|-%:%`(C, VSPLAT_instr(sh), `%->%`_functype(`%`_resulttype([($shunpack(sh) : numtype <: valtype)]), `%`_resulttype([V128_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:341.1-343.21
  rule vextract_lane{C : context, sh : shape, `sx?` : sx?, i : laneidx}:
    `%|-%:%`(C, VEXTRACT_LANE_instr(sh, sx?{sx <- `sx?`}, i), `%->%`_functype(`%`_resulttype([V128_valtype]), `%`_resulttype([($shunpack(sh) : numtype <: valtype)])))
    -- if (i!`%`_laneidx.0 < $dim(sh)!`%`_dim.0)

  ;; ../specification/wasm-2.0/6-typing.spectec:345.1-347.21
  rule vreplace_lane{C : context, sh : shape, i : laneidx}:
    `%|-%:%`(C, VREPLACE_LANE_instr(sh, i), `%->%`_functype(`%`_resulttype([V128_valtype ($shunpack(sh) : numtype <: valtype)]), `%`_resulttype([V128_valtype])))
    -- if (i!`%`_laneidx.0 < $dim(sh)!`%`_dim.0)

  ;; ../specification/wasm-2.0/6-typing.spectec:349.1-350.50
  rule vextunop{C : context, sh_1 : ishape, sh_2 : ishape, vextunop : vextunop__(sh_2, sh_1)}:
    `%|-%:%`(C, VEXTUNOP_instr(sh_1, sh_2, vextunop), `%->%`_functype(`%`_resulttype([V128_valtype]), `%`_resulttype([V128_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:352.1-353.57
  rule vextbinop{C : context, sh_1 : ishape, sh_2 : ishape, vextbinop : vextbinop__(sh_2, sh_1)}:
    `%|-%:%`(C, VEXTBINOP_instr(sh_1, sh_2, vextbinop), `%->%`_functype(`%`_resulttype([V128_valtype V128_valtype]), `%`_resulttype([V128_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:355.1-356.48
  rule vnarrow{C : context, sh_1 : ishape, sh_2 : ishape, sx : sx}:
    `%|-%:%`(C, VNARROW_instr(sh_1, sh_2, sx), `%->%`_functype(`%`_resulttype([V128_valtype V128_valtype]), `%`_resulttype([V128_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:358.1-359.46
  rule vcvtop{C : context, sh_1 : shape, sh_2 : shape, vcvtop : vcvtop__(sh_2, sh_1)}:
    `%|-%:%`(C, VCVTOP_instr(sh_1, sh_2, vcvtop), `%->%`_functype(`%`_resulttype([V128_valtype]), `%`_resulttype([V128_valtype])))

  ;; ../specification/wasm-2.0/6-typing.spectec:364.1-366.24
  rule `local.get`{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, `LOCAL.GET`_instr(x), `%->%`_functype(`%`_resulttype([]), `%`_resulttype([t])))
    -- if (C.LOCALS_context[x!`%`_idx.0] = t)

  ;; ../specification/wasm-2.0/6-typing.spectec:368.1-370.24
  rule `local.set`{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, `LOCAL.SET`_instr(x), `%->%`_functype(`%`_resulttype([t]), `%`_resulttype([])))
    -- if (C.LOCALS_context[x!`%`_idx.0] = t)

  ;; ../specification/wasm-2.0/6-typing.spectec:372.1-374.24
  rule `local.tee`{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, `LOCAL.TEE`_instr(x), `%->%`_functype(`%`_resulttype([t]), `%`_resulttype([t])))
    -- if (C.LOCALS_context[x!`%`_idx.0] = t)

  ;; ../specification/wasm-2.0/6-typing.spectec:379.1-381.29
  rule `global.get`{C : context, x : idx, t : valtype, mut : mut}:
    `%|-%:%`(C, `GLOBAL.GET`_instr(x), `%->%`_functype(`%`_resulttype([]), `%`_resulttype([t])))
    -- if (C.GLOBALS_context[x!`%`_idx.0] = `%%`_globaltype(mut, t))

  ;; ../specification/wasm-2.0/6-typing.spectec:383.1-385.29
  rule `global.set`{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, `GLOBAL.SET`_instr(x), `%->%`_functype(`%`_resulttype([t]), `%`_resulttype([])))
    -- if (C.GLOBALS_context[x!`%`_idx.0] = `%%`_globaltype(?(MUT_MUT), t))

  ;; ../specification/wasm-2.0/6-typing.spectec:390.1-392.29
  rule `table.get`{C : context, x : idx, rt : reftype, lim : limits}:
    `%|-%:%`(C, `TABLE.GET`_instr(x), `%->%`_functype(`%`_resulttype([I32_valtype]), `%`_resulttype([(rt : reftype <: valtype)])))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%`_tabletype(lim, rt))

  ;; ../specification/wasm-2.0/6-typing.spectec:394.1-396.29
  rule `table.set`{C : context, x : idx, rt : reftype, lim : limits}:
    `%|-%:%`(C, `TABLE.SET`_instr(x), `%->%`_functype(`%`_resulttype([I32_valtype (rt : reftype <: valtype)]), `%`_resulttype([])))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%`_tabletype(lim, rt))

  ;; ../specification/wasm-2.0/6-typing.spectec:398.1-400.29
  rule `table.size`{C : context, x : idx, lim : limits, rt : reftype}:
    `%|-%:%`(C, `TABLE.SIZE`_instr(x), `%->%`_functype(`%`_resulttype([]), `%`_resulttype([I32_valtype])))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%`_tabletype(lim, rt))

  ;; ../specification/wasm-2.0/6-typing.spectec:402.1-404.29
  rule `table.grow`{C : context, x : idx, rt : reftype, lim : limits}:
    `%|-%:%`(C, `TABLE.GROW`_instr(x), `%->%`_functype(`%`_resulttype([(rt : reftype <: valtype) I32_valtype]), `%`_resulttype([I32_valtype])))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%`_tabletype(lim, rt))

  ;; ../specification/wasm-2.0/6-typing.spectec:406.1-408.29
  rule `table.fill`{C : context, x : idx, rt : reftype, lim : limits}:
    `%|-%:%`(C, `TABLE.FILL`_instr(x), `%->%`_functype(`%`_resulttype([I32_valtype (rt : reftype <: valtype) I32_valtype]), `%`_resulttype([])))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%`_tabletype(lim, rt))

  ;; ../specification/wasm-2.0/6-typing.spectec:410.1-413.33
  rule `table.copy`{C : context, x_1 : idx, x_2 : idx, lim_1 : limits, rt : reftype, lim_2 : limits}:
    `%|-%:%`(C, `TABLE.COPY`_instr(x_1, x_2), `%->%`_functype(`%`_resulttype([I32_valtype I32_valtype I32_valtype]), `%`_resulttype([])))
    -- if (C.TABLES_context[x_1!`%`_idx.0] = `%%`_tabletype(lim_1, rt))
    -- if (C.TABLES_context[x_2!`%`_idx.0] = `%%`_tabletype(lim_2, rt))

  ;; ../specification/wasm-2.0/6-typing.spectec:415.1-418.26
  rule `table.init`{C : context, x_1 : idx, x_2 : idx, lim : limits, rt : reftype}:
    `%|-%:%`(C, `TABLE.INIT`_instr(x_1, x_2), `%->%`_functype(`%`_resulttype([I32_valtype I32_valtype I32_valtype]), `%`_resulttype([])))
    -- if (C.TABLES_context[x_1!`%`_idx.0] = `%%`_tabletype(lim, rt))
    -- if (C.ELEMS_context[x_2!`%`_idx.0] = rt)

  ;; ../specification/wasm-2.0/6-typing.spectec:420.1-422.24
  rule `elem.drop`{C : context, x : idx, rt : reftype}:
    `%|-%:%`(C, `ELEM.DROP`_instr(x), `%->%`_functype(`%`_resulttype([]), `%`_resulttype([])))
    -- if (C.ELEMS_context[x!`%`_idx.0] = rt)

  ;; ../specification/wasm-2.0/6-typing.spectec:427.1-429.23
  rule `memory.size`{C : context, mt : memtype}:
    `%|-%:%`(C, `MEMORY.SIZE`_instr, `%->%`_functype(`%`_resulttype([]), `%`_resulttype([I32_valtype])))
    -- if (C.MEMS_context[0] = mt)

  ;; ../specification/wasm-2.0/6-typing.spectec:431.1-433.23
  rule `memory.grow`{C : context, mt : memtype}:
    `%|-%:%`(C, `MEMORY.GROW`_instr, `%->%`_functype(`%`_resulttype([I32_valtype]), `%`_resulttype([I32_valtype])))
    -- if (C.MEMS_context[0] = mt)

  ;; ../specification/wasm-2.0/6-typing.spectec:435.1-437.23
  rule `memory.fill`{C : context, mt : memtype}:
    `%|-%:%`(C, `MEMORY.FILL`_instr, `%->%`_functype(`%`_resulttype([I32_valtype I32_valtype I32_valtype]), `%`_resulttype([])))
    -- if (C.MEMS_context[0] = mt)

  ;; ../specification/wasm-2.0/6-typing.spectec:439.1-441.23
  rule `memory.copy`{C : context, mt : memtype}:
    `%|-%:%`(C, `MEMORY.COPY`_instr, `%->%`_functype(`%`_resulttype([I32_valtype I32_valtype I32_valtype]), `%`_resulttype([])))
    -- if (C.MEMS_context[0] = mt)

  ;; ../specification/wasm-2.0/6-typing.spectec:443.1-446.24
  rule `memory.init`{C : context, x : idx, mt : memtype}:
    `%|-%:%`(C, `MEMORY.INIT`_instr(x), `%->%`_functype(`%`_resulttype([I32_valtype I32_valtype I32_valtype]), `%`_resulttype([])))
    -- if (C.MEMS_context[0] = mt)
    -- if (C.DATAS_context[x!`%`_idx.0] = OK_datatype)

  ;; ../specification/wasm-2.0/6-typing.spectec:448.1-450.24
  rule `data.drop`{C : context, x : idx}:
    `%|-%:%`(C, `DATA.DROP`_instr(x), `%->%`_functype(`%`_resulttype([]), `%`_resulttype([])))
    -- if (C.DATAS_context[x!`%`_idx.0] = OK_datatype)

  ;; ../specification/wasm-2.0/6-typing.spectec:461.1-464.43
  rule `load-val`{C : context, nt : numtype, memarg : memarg, mt : memtype}:
    `%|-%:%`(C, LOAD_instr(nt, ?(), memarg), `%->%`_functype(`%`_resulttype([I32_valtype]), `%`_resulttype([(nt : numtype <: valtype)])))
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ memarg.ALIGN_memarg!`%`_u32.0) : nat <:> rat) <= (($size((nt : numtype <: valtype)) : nat <:> rat) / (8 : nat <:> rat)))

  ;; ../specification/wasm-2.0/6-typing.spectec:466.1-469.35
  rule `load-pack`{C : context, Inn : Inn, M : M, sx : sx, memarg : memarg, mt : memtype}:
    `%|-%:%`(C, LOAD_instr((Inn : Inn <: numtype), ?(`%_%`_loadop_(`%`_sz(M), sx)), memarg), `%->%`_functype(`%`_resulttype([I32_valtype]), `%`_resulttype([(Inn : Inn <: valtype)])))
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ memarg.ALIGN_memarg!`%`_u32.0) : nat <:> rat) <= ((M : nat <:> rat) / (8 : nat <:> rat)))

  ;; ../specification/wasm-2.0/6-typing.spectec:480.1-483.43
  rule `store-val`{C : context, nt : numtype, memarg : memarg, mt : memtype}:
    `%|-%:%`(C, STORE_instr(nt, ?(), memarg), `%->%`_functype(`%`_resulttype([I32_valtype (nt : numtype <: valtype)]), `%`_resulttype([])))
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ memarg.ALIGN_memarg!`%`_u32.0) : nat <:> rat) <= (($size((nt : numtype <: valtype)) : nat <:> rat) / (8 : nat <:> rat)))

  ;; ../specification/wasm-2.0/6-typing.spectec:485.1-488.35
  rule `store-pack`{C : context, Inn : Inn, M : M, memarg : memarg, mt : memtype}:
    `%|-%:%`(C, STORE_instr((Inn : Inn <: numtype), ?(`%`_sz(M)), memarg), `%->%`_functype(`%`_resulttype([I32_valtype (Inn : Inn <: valtype)]), `%`_resulttype([])))
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ memarg.ALIGN_memarg!`%`_u32.0) : nat <:> rat) <= ((M : nat <:> rat) / (8 : nat <:> rat)))

  ;; ../specification/wasm-2.0/6-typing.spectec:490.1-493.45
  rule `vload-val`{C : context, memarg : memarg, mt : memtype}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(), memarg), `%->%`_functype(`%`_resulttype([I32_valtype]), `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ memarg.ALIGN_memarg!`%`_u32.0) : nat <:> rat) <= (($size(V128_valtype) : nat <:> rat) / (8 : nat <:> rat)))

  ;; ../specification/wasm-2.0/6-typing.spectec:495.1-498.39
  rule `vload-pack`{C : context, M : M, N : N, sx : sx, memarg : memarg, mt : memtype}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(M), N, sx)), memarg), `%->%`_functype(`%`_resulttype([I32_valtype]), `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ memarg.ALIGN_memarg!`%`_u32.0) : nat <:> rat) <= (((M : nat <:> rat) / (8 : nat <:> rat)) * (N : nat <:> rat)))

  ;; ../specification/wasm-2.0/6-typing.spectec:500.1-503.35
  rule `vload-splat`{C : context, n : n, memarg : memarg, mt : memtype}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(n))), memarg), `%->%`_functype(`%`_resulttype([I32_valtype]), `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ memarg.ALIGN_memarg!`%`_u32.0) : nat <:> rat) <= ((n : nat <:> rat) / (8 : nat <:> rat)))

  ;; ../specification/wasm-2.0/6-typing.spectec:505.1-508.35
  rule `vload-zero`{C : context, n : n, memarg : memarg, mt : memtype}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(ZERO_vloadop_(`%`_sz(n))), memarg), `%->%`_functype(`%`_resulttype([I32_valtype]), `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ memarg.ALIGN_memarg!`%`_u32.0) : nat <:> rat) <= ((n : nat <:> rat) / (8 : nat <:> rat)))

  ;; ../specification/wasm-2.0/6-typing.spectec:510.1-514.29
  rule vload_lane{C : context, n : n, memarg : memarg, laneidx : laneidx, mt : memtype}:
    `%|-%:%`(C, VLOAD_LANE_instr(V128_vectype, `%`_sz(n), memarg, laneidx), `%->%`_functype(`%`_resulttype([I32_valtype V128_valtype]), `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ memarg.ALIGN_memarg!`%`_u32.0) : nat <:> rat) <= ((n : nat <:> rat) / (8 : nat <:> rat)))
    -- if ((laneidx!`%`_laneidx.0 : nat <:> rat) < ((128 : nat <:> rat) / (n : nat <:> rat)))

  ;; ../specification/wasm-2.0/6-typing.spectec:516.1-519.45
  rule vstore{C : context, memarg : memarg, mt : memtype}:
    `%|-%:%`(C, VSTORE_instr(V128_vectype, memarg), `%->%`_functype(`%`_resulttype([I32_valtype V128_valtype]), `%`_resulttype([])))
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ memarg.ALIGN_memarg!`%`_u32.0) : nat <:> rat) <= (($size(V128_valtype) : nat <:> rat) / (8 : nat <:> rat)))

  ;; ../specification/wasm-2.0/6-typing.spectec:521.1-525.29
  rule vstore_lane{C : context, n : n, memarg : memarg, laneidx : laneidx, mt : memtype}:
    `%|-%:%`(C, VSTORE_LANE_instr(V128_vectype, `%`_sz(n), memarg, laneidx), `%->%`_functype(`%`_resulttype([I32_valtype V128_valtype]), `%`_resulttype([])))
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ memarg.ALIGN_memarg!`%`_u32.0) : nat <:> rat) <= ((n : nat <:> rat) / (8 : nat <:> rat)))
    -- if ((laneidx!`%`_laneidx.0 : nat <:> rat) < ((128 : nat <:> rat) / (n : nat <:> rat)))

;; ../specification/wasm-2.0/6-typing.spectec:142.1-142.65
relation Instrs_ok: `%|-%:%`(context, instr*, functype)
  ;; ../specification/wasm-2.0/6-typing.spectec:155.1-156.24
  rule empty{C : context}:
    `%|-%:%`(C, [], `%->%`_functype(`%`_resulttype([]), `%`_resulttype([])))

  ;; ../specification/wasm-2.0/6-typing.spectec:158.1-160.41
  rule instr{C : context, instr : instr, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, [instr], `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instr_ok: `%|-%:%`(C, instr, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; ../specification/wasm-2.0/6-typing.spectec:162.1-165.45
  rule seq{C : context, `instr_1*` : instr*, `instr_2*` : instr*, `t_1*` : valtype*, `t_3*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, instr_1*{instr_1 <- `instr_1*`} ++ instr_2*{instr_2 <- `instr_2*`}, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_3*{t_3 <- `t_3*`})))
    -- Instrs_ok: `%|-%:%`(C, instr_1*{instr_1 <- `instr_1*`}, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`(C, instr_2*{instr_2 <- `instr_2*`}, `%->%`_functype(`%`_resulttype(t_2*{t_2 <- `t_2*`}), `%`_resulttype(t_3*{t_3 <- `t_3*`})))

  ;; ../specification/wasm-2.0/6-typing.spectec:167.1-172.38
  rule sub{C : context, `instr*` : instr*, `t'_1*` : valtype*, `t'_2*` : valtype*, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, instr*{instr <- `instr*`}, `%->%`_functype(`%`_resulttype(t'_1*{t'_1 <- `t'_1*`}), `%`_resulttype(t'_2*{t'_2 <- `t'_2*`})))
    -- Instrs_ok: `%|-%:%`(C, instr*{instr <- `instr*`}, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Resulttype_sub: `|-%<:%`(`%`_resulttype(t'_1*{t'_1 <- `t'_1*`}), `%`_resulttype(t_1*{t_1 <- `t_1*`}))
    -- Resulttype_sub: `|-%<:%`(`%`_resulttype(t_2*{t_2 <- `t_2*`}), `%`_resulttype(t'_2*{t'_2 <- `t'_2*`}))

  ;; ../specification/wasm-2.0/6-typing.spectec:174.1-176.43
  rule frame{C : context, `instr*` : instr*, `t*` : valtype*, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, instr*{instr <- `instr*`}, `%->%`_functype(`%`_resulttype(t*{t <- `t*`} ++ t_1*{t_1 <- `t_1*`}), `%`_resulttype(t*{t <- `t*`} ++ t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`(C, instr*{instr <- `instr*`}, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
}

;; ../specification/wasm-2.0/6-typing.spectec:143.1-143.69
relation Expr_ok: `%|-%:%`(context, expr, resulttype)
  ;; ../specification/wasm-2.0/6-typing.spectec:148.1-150.40
  rule _{C : context, `instr*` : instr*, `t*` : valtype*}:
    `%|-%:%`(C, instr*{instr <- `instr*`}, `%`_resulttype(t*{t <- `t*`}))
    -- Instrs_ok: `%|-%:%`(C, instr*{instr <- `instr*`}, `%->%`_functype(`%`_resulttype([]), `%`_resulttype(t*{t <- `t*`})))

;; ../specification/wasm-2.0/6-typing.spectec:532.1-532.78
relation Instr_const: `%|-%CONST`(context, instr)
  ;; ../specification/wasm-2.0/6-typing.spectec:536.1-537.26
  rule const{C : context, nt : numtype, c : num_(nt)}:
    `%|-%CONST`(C, CONST_instr(nt, c))

  ;; ../specification/wasm-2.0/6-typing.spectec:539.1-540.28
  rule vconst{C : context, vt : vectype, vc : vec_(vt)}:
    `%|-%CONST`(C, VCONST_instr(vt, vc))

  ;; ../specification/wasm-2.0/6-typing.spectec:542.1-543.27
  rule `ref.null`{C : context, rt : reftype}:
    `%|-%CONST`(C, `REF.NULL`_instr(rt))

  ;; ../specification/wasm-2.0/6-typing.spectec:545.1-546.26
  rule `ref.func`{C : context, x : idx}:
    `%|-%CONST`(C, `REF.FUNC`_instr(x))

  ;; ../specification/wasm-2.0/6-typing.spectec:548.1-550.25
  rule `global.get`{C : context, x : idx, t : valtype}:
    `%|-%CONST`(C, `GLOBAL.GET`_instr(x))
    -- if (C.GLOBALS_context[x!`%`_idx.0] = `%%`_globaltype(?(), t))

;; ../specification/wasm-2.0/6-typing.spectec:533.1-533.77
relation Expr_const: `%|-%CONST`(context, expr)
  ;; ../specification/wasm-2.0/6-typing.spectec:553.1-554.38
  rule _{C : context, `instr*` : instr*}:
    `%|-%CONST`(C, instr*{instr <- `instr*`})
    -- (Instr_const: `%|-%CONST`(C, instr))*{instr <- `instr*`}

;; ../specification/wasm-2.0/6-typing.spectec:534.1-534.78
relation Expr_ok_const: `%|-%:%CONST`(context, expr, valtype)
  ;; ../specification/wasm-2.0/6-typing.spectec:557.1-560.33
  rule _{C : context, expr : expr, t : valtype}:
    `%|-%:%CONST`(C, expr, t)
    -- Expr_ok: `%|-%:%`(C, expr, `%`_resulttype([t]))
    -- Expr_const: `%|-%CONST`(C, expr)

;; ../specification/wasm-2.0/6-typing.spectec:567.1-567.73
relation Type_ok: `|-%:%`(type, functype)
  ;; ../specification/wasm-2.0/6-typing.spectec:581.1-583.29
  rule _{ft : functype}:
    `|-%:%`(TYPE_type(ft), ft)
    -- Functype_ok: `|-%:OK`(ft)

;; ../specification/wasm-2.0/6-typing.spectec:568.1-568.73
relation Func_ok: `%|-%:%`(context, func, functype)
  ;; ../specification/wasm-2.0/6-typing.spectec:585.1-589.81
  rule _{C : context, x : idx, `t*` : valtype*, expr : expr, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, FUNC_func(x, LOCAL_local(t)*{t <- `t*`}, expr), `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.TYPES_context[x!`%`_idx.0] = `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (if (t =/= BOT_valtype))*{t <- `t*`}
    -- Expr_ok: `%|-%:%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`}, LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(`%`_resulttype(t_2*{t_2 <- `t_2*`}))} +++ C, expr, `%`_resulttype(t_2*{t_2 <- `t_2*`}))

;; ../specification/wasm-2.0/6-typing.spectec:569.1-569.75
relation Global_ok: `%|-%:%`(context, global, globaltype)
  ;; ../specification/wasm-2.0/6-typing.spectec:591.1-595.40
  rule _{C : context, gt : globaltype, expr : expr, mut : mut, t : valtype}:
    `%|-%:%`(C, GLOBAL_global(gt, expr), gt)
    -- Globaltype_ok: `|-%:OK`(gt)
    -- if (gt = `%%`_globaltype(mut, t))
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, t)

;; ../specification/wasm-2.0/6-typing.spectec:570.1-570.74
relation Table_ok: `%|-%:%`(context, table, tabletype)
  ;; ../specification/wasm-2.0/6-typing.spectec:597.1-599.30
  rule _{C : context, tt : tabletype}:
    `%|-%:%`(C, TABLE_table(tt), tt)
    -- Tabletype_ok: `|-%:OK`(tt)

;; ../specification/wasm-2.0/6-typing.spectec:571.1-571.72
relation Mem_ok: `%|-%:%`(context, mem, memtype)
  ;; ../specification/wasm-2.0/6-typing.spectec:601.1-603.28
  rule _{C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY_mem(mt), mt)
    -- Memtype_ok: `|-%:OK`(mt)

;; ../specification/wasm-2.0/6-typing.spectec:574.1-574.77
relation Elemmode_ok: `%|-%:%`(context, elemmode, reftype)
  ;; ../specification/wasm-2.0/6-typing.spectec:614.1-617.42
  rule active{C : context, x : idx, expr : expr, rt : reftype, lim : limits}:
    `%|-%:%`(C, ACTIVE_elemmode(x, expr), rt)
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%`_tabletype(lim, rt))
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, I32_valtype)

  ;; ../specification/wasm-2.0/6-typing.spectec:619.1-620.20
  rule passive{C : context, rt : reftype}:
    `%|-%:%`(C, PASSIVE_elemmode, rt)

  ;; ../specification/wasm-2.0/6-typing.spectec:622.1-623.20
  rule declare{C : context, rt : reftype}:
    `%|-%:%`(C, DECLARE_elemmode, rt)

;; ../specification/wasm-2.0/6-typing.spectec:572.1-572.73
relation Elem_ok: `%|-%:%`(context, elem, reftype)
  ;; ../specification/wasm-2.0/6-typing.spectec:605.1-608.37
  rule _{C : context, rt : reftype, `expr*` : expr*, elemmode : elemmode}:
    `%|-%:%`(C, ELEM_elem(rt, expr*{expr <- `expr*`}, elemmode), rt)
    -- (Expr_ok_const: `%|-%:%CONST`(C, expr, (rt : reftype <: valtype)))*{expr <- `expr*`}
    -- Elemmode_ok: `%|-%:%`(C, elemmode, rt)

;; ../specification/wasm-2.0/6-typing.spectec:575.1-575.77
relation Datamode_ok: `%|-%:OK`(context, datamode)
  ;; ../specification/wasm-2.0/6-typing.spectec:625.1-628.42
  rule active{C : context, expr : expr, mt : memtype}:
    `%|-%:OK`(C, ACTIVE_datamode(`%`_memidx(0), expr))
    -- if (C.MEMS_context[0] = mt)
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, I32_valtype)

  ;; ../specification/wasm-2.0/6-typing.spectec:630.1-631.20
  rule passive{C : context}:
    `%|-%:OK`(C, PASSIVE_datamode)

;; ../specification/wasm-2.0/6-typing.spectec:573.1-573.73
relation Data_ok: `%|-%:OK`(context, data)
  ;; ../specification/wasm-2.0/6-typing.spectec:610.1-612.37
  rule _{C : context, `b*` : byte*, datamode : datamode}:
    `%|-%:OK`(C, DATA_data(b*{b <- `b*`}, datamode))
    -- Datamode_ok: `%|-%:OK`(C, datamode)

;; ../specification/wasm-2.0/6-typing.spectec:576.1-576.74
relation Start_ok: `%|-%:OK`(context, start)
  ;; ../specification/wasm-2.0/6-typing.spectec:633.1-635.32
  rule _{C : context, x : idx}:
    `%|-%:OK`(C, START_start(x))
    -- if (C.FUNCS_context[x!`%`_idx.0] = `%->%`_functype(`%`_resulttype([]), `%`_resulttype([])))

;; ../specification/wasm-2.0/6-typing.spectec:640.1-640.80
relation Import_ok: `%|-%:%`(context, import, externtype)
  ;; ../specification/wasm-2.0/6-typing.spectec:644.1-646.31
  rule _{C : context, name_1 : name, name_2 : name, xt : externtype}:
    `%|-%:%`(C, IMPORT_import(name_1, name_2, xt), xt)
    -- Externtype_ok: `|-%:OK`(xt)

;; ../specification/wasm-2.0/6-typing.spectec:642.1-642.83
relation Externidx_ok: `%|-%:%`(context, externidx, externtype)
  ;; ../specification/wasm-2.0/6-typing.spectec:653.1-655.24
  rule func{C : context, x : idx, ft : functype}:
    `%|-%:%`(C, FUNC_externidx(x), FUNC_externtype(ft))
    -- if (C.FUNCS_context[x!`%`_idx.0] = ft)

  ;; ../specification/wasm-2.0/6-typing.spectec:657.1-659.26
  rule global{C : context, x : idx, gt : globaltype}:
    `%|-%:%`(C, GLOBAL_externidx(x), GLOBAL_externtype(gt))
    -- if (C.GLOBALS_context[x!`%`_idx.0] = gt)

  ;; ../specification/wasm-2.0/6-typing.spectec:661.1-663.25
  rule table{C : context, x : idx, tt : tabletype}:
    `%|-%:%`(C, TABLE_externidx(x), TABLE_externtype(tt))
    -- if (C.TABLES_context[x!`%`_idx.0] = tt)

  ;; ../specification/wasm-2.0/6-typing.spectec:665.1-667.23
  rule mem{C : context, x : idx, mt : memtype}:
    `%|-%:%`(C, MEM_externidx(x), MEM_externtype(mt))
    -- if (C.MEMS_context[x!`%`_idx.0] = mt)

;; ../specification/wasm-2.0/6-typing.spectec:641.1-641.80
relation Export_ok: `%|-%:%`(context, export, externtype)
  ;; ../specification/wasm-2.0/6-typing.spectec:648.1-650.39
  rule _{C : context, name : name, externidx : externidx, xt : externtype}:
    `%|-%:%`(C, EXPORT_export(name, externidx), xt)
    -- Externidx_ok: `%|-%:%`(C, externidx, xt)

;; ../specification/wasm-2.0/6-typing.spectec:672.1-672.62
relation Module_ok: `|-%:OK`(module)
  ;; ../specification/wasm-2.0/6-typing.spectec:675.1-701.29
  rule _{`type*` : type*, `import*` : import*, `func*` : func*, `global*` : global*, `table*` : table*, `mem*` : mem*, `elem*` : elem*, n : n, `data*` : data*, `start?` : start?, `export*` : export*, `ft'*` : functype*, `ixt*` : externtype*, C' : context, `gt*` : globaltype*, `tt*` : tabletype*, `mt*` : memtype*, `rt*` : reftype*, C : context, `ft*` : functype*, `xt*` : externtype*, `ift*` : functype*, `igt*` : globaltype*, `itt*` : tabletype*, `imt*` : memtype*}:
    `|-%:OK`(MODULE_module(type*{type <- `type*`}, import*{import <- `import*`}, func*{func <- `func*`}, global*{global <- `global*`}, table*{table <- `table*`}, mem*{mem <- `mem*`}, elem*{elem <- `elem*`}, data^n{data <- `data*`}, start?{start <- `start?`}, export*{export <- `export*`}))
    -- (Type_ok: `|-%:%`(type, ft'))*{ft' <- `ft'*`, type <- `type*`}
    -- (Import_ok: `%|-%:%`({TYPES ft'*{ft' <- `ft'*`}, FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], RETURN ?()}, import, ixt))*{import <- `import*`, ixt <- `ixt*`}
    -- (Global_ok: `%|-%:%`(C', global, gt))*{global <- `global*`, gt <- `gt*`}
    -- (Table_ok: `%|-%:%`(C', table, tt))*{table <- `table*`, tt <- `tt*`}
    -- (Mem_ok: `%|-%:%`(C', mem, mt))*{mem <- `mem*`, mt <- `mt*`}
    -- (Elem_ok: `%|-%:%`(C', elem, rt))*{elem <- `elem*`, rt <- `rt*`}
    -- (Data_ok: `%|-%:OK`(C', data))^n{data <- `data*`}
    -- (Func_ok: `%|-%:%`(C, func, ft))*{ft <- `ft*`, func <- `func*`}
    -- (Start_ok: `%|-%:OK`(C, start))?{start <- `start?`}
    -- (Export_ok: `%|-%:%`(C, export, xt))*{export <- `export*`, xt <- `xt*`}
    -- if (|mt*{mt <- `mt*`}| <= 1)
    -- if (C = {TYPES ft'*{ft' <- `ft'*`}, FUNCS ift*{ift <- `ift*`} ++ ft*{ft <- `ft*`}, GLOBALS igt*{igt <- `igt*`} ++ gt*{gt <- `gt*`}, TABLES itt*{itt <- `itt*`} ++ tt*{tt <- `tt*`}, MEMS imt*{imt <- `imt*`} ++ mt*{mt <- `mt*`}, ELEMS rt*{rt <- `rt*`}, DATAS OK_datatype^n{}, LOCALS [], LABELS [], RETURN ?()})
    -- if (C' = {TYPES ft'*{ft' <- `ft'*`}, FUNCS ift*{ift <- `ift*`} ++ ft*{ft <- `ft*`}, GLOBALS igt*{igt <- `igt*`}, TABLES itt*{itt <- `itt*`} ++ tt*{tt <- `tt*`}, MEMS imt*{imt <- `imt*`} ++ mt*{mt <- `mt*`}, ELEMS [], DATAS [], LOCALS [], LABELS [], RETURN ?()})
    -- if (ift*{ift <- `ift*`} = $funcsxt(ixt*{ixt <- `ixt*`}))
    -- if (igt*{igt <- `igt*`} = $globalsxt(ixt*{ixt <- `ixt*`}))
    -- if (itt*{itt <- `itt*`} = $tablesxt(ixt*{ixt <- `ixt*`}))
    -- if (imt*{imt <- `imt*`} = $memsxt(ixt*{ixt <- `ixt*`}))

;; ../specification/wasm-2.0/8-reduction.spectec:6.1-6.109
relation Step_pure: `%~>%`(admininstr*, admininstr*)
  ;; ../specification/wasm-2.0/8-reduction.spectec:42.1-43.24
  rule unreachable:
    `%~>%`([UNREACHABLE_admininstr], [TRAP_admininstr])

  ;; ../specification/wasm-2.0/8-reduction.spectec:45.1-46.15
  rule nop:
    `%~>%`([NOP_admininstr], [])

  ;; ../specification/wasm-2.0/8-reduction.spectec:48.1-49.20
  rule drop{val : val}:
    `%~>%`([(val : val <: admininstr) DROP_admininstr], [])

  ;; ../specification/wasm-2.0/8-reduction.spectec:52.1-54.16
  rule `select-true`{val_1 : val, val_2 : val, c : num_(I32_numtype), `t*?` : valtype*?}:
    `%~>%`([(val_1 : val <: admininstr) (val_2 : val <: admininstr) CONST_admininstr(I32_numtype, c) SELECT_admininstr(t*{t <- `t*`}?{`t*` <- `t*?`})], [(val_1 : val <: admininstr)])
    -- if (c!`%`_num_.0 =/= 0)

  ;; ../specification/wasm-2.0/8-reduction.spectec:56.1-58.14
  rule `select-false`{val_1 : val, val_2 : val, c : num_(I32_numtype), `t*?` : valtype*?}:
    `%~>%`([(val_1 : val <: admininstr) (val_2 : val <: admininstr) CONST_admininstr(I32_numtype, c) SELECT_admininstr(t*{t <- `t*`}?{`t*` <- `t*?`})], [(val_2 : val <: admininstr)])
    -- if (c!`%`_num_.0 = 0)

  ;; ../specification/wasm-2.0/8-reduction.spectec:76.1-78.16
  rule `if-true`{c : num_(I32_numtype), bt : blocktype, `instr_1*` : instr*, `instr_2*` : instr*}:
    `%~>%`([CONST_admininstr(I32_numtype, c) `IF%%ELSE%`_admininstr(bt, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`})], [BLOCK_admininstr(bt, instr_1*{instr_1 <- `instr_1*`})])
    -- if (c!`%`_num_.0 =/= 0)

  ;; ../specification/wasm-2.0/8-reduction.spectec:80.1-82.14
  rule `if-false`{c : num_(I32_numtype), bt : blocktype, `instr_1*` : instr*, `instr_2*` : instr*}:
    `%~>%`([CONST_admininstr(I32_numtype, c) `IF%%ELSE%`_admininstr(bt, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`})], [BLOCK_admininstr(bt, instr_2*{instr_2 <- `instr_2*`})])
    -- if (c!`%`_num_.0 = 0)

  ;; ../specification/wasm-2.0/8-reduction.spectec:85.1-86.38
  rule `label-vals`{n : n, `instr*` : instr*, `val*` : val*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(n, instr*{instr <- `instr*`}, (val : val <: admininstr)*{val <- `val*`})], (val : val <: admininstr)*{val <- `val*`})

  ;; ../specification/wasm-2.0/8-reduction.spectec:92.1-93.74
  rule `br-zero`{n : n, `instr'*` : instr*, `val'*` : val*, `val*` : val*, `admininstr*` : admininstr*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(n, instr'*{instr' <- `instr'*`}, (val' : val <: admininstr)*{val' <- `val'*`} ++ (val : val <: admininstr)^n{val <- `val*`} ++ [BR_admininstr(`%`_labelidx(0))] ++ admininstr*{admininstr <- `admininstr*`})], (val : val <: admininstr)^n{val <- `val*`} ++ (instr' : instr <: admininstr)*{instr' <- `instr'*`})

  ;; ../specification/wasm-2.0/8-reduction.spectec:95.1-96.70
  rule `br-succ`{n : n, `instr'*` : instr*, `val*` : val*, l : labelidx, `admininstr*` : admininstr*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(n, instr'*{instr' <- `instr'*`}, (val : val <: admininstr)*{val <- `val*`} ++ [BR_admininstr(`%`_labelidx((l!`%`_labelidx.0 + 1)))] ++ admininstr*{admininstr <- `admininstr*`})], (val : val <: admininstr)*{val <- `val*`} ++ [BR_admininstr(l)])

  ;; ../specification/wasm-2.0/8-reduction.spectec:99.1-101.16
  rule `br_if-true`{c : num_(I32_numtype), l : labelidx}:
    `%~>%`([CONST_admininstr(I32_numtype, c) BR_IF_admininstr(l)], [BR_admininstr(l)])
    -- if (c!`%`_num_.0 =/= 0)

  ;; ../specification/wasm-2.0/8-reduction.spectec:103.1-105.14
  rule `br_if-false`{c : num_(I32_numtype), l : labelidx}:
    `%~>%`([CONST_admininstr(I32_numtype, c) BR_IF_admininstr(l)], [])
    -- if (c!`%`_num_.0 = 0)

  ;; ../specification/wasm-2.0/8-reduction.spectec:108.1-110.17
  rule `br_table-lt`{i : num_(I32_numtype), `l*` : labelidx*, l' : labelidx}:
    `%~>%`([CONST_admininstr(I32_numtype, i) BR_TABLE_admininstr(l*{l <- `l*`}, l')], [BR_admininstr(l*{l <- `l*`}[i!`%`_num_.0])])
    -- if (i!`%`_num_.0 < |l*{l <- `l*`}|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:112.1-114.18
  rule `br_table-ge`{i : num_(I32_numtype), `l*` : labelidx*, l' : labelidx}:
    `%~>%`([CONST_admininstr(I32_numtype, i) BR_TABLE_admininstr(l*{l <- `l*`}, l')], [BR_admininstr(l')])
    -- if (i!`%`_num_.0 >= |l*{l <- `l*`}|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:138.1-139.35
  rule `frame-vals`{n : n, f : frame, `val*` : val*}:
    `%~>%`([`FRAME_%{%}%`_admininstr(n, f, (val : val <: admininstr)^n{val <- `val*`})], (val : val <: admininstr)^n{val <- `val*`})

  ;; ../specification/wasm-2.0/8-reduction.spectec:141.1-142.60
  rule `return-frame`{n : n, f : frame, `val'*` : val*, `val*` : val*, `admininstr*` : admininstr*}:
    `%~>%`([`FRAME_%{%}%`_admininstr(n, f, (val' : val <: admininstr)*{val' <- `val'*`} ++ (val : val <: admininstr)^n{val <- `val*`} ++ [RETURN_admininstr] ++ admininstr*{admininstr <- `admininstr*`})], (val : val <: admininstr)^n{val <- `val*`})

  ;; ../specification/wasm-2.0/8-reduction.spectec:144.1-145.65
  rule `return-label`{n : n, `instr'*` : instr*, `val*` : val*, `admininstr*` : admininstr*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(n, instr'*{instr' <- `instr'*`}, (val : val <: admininstr)*{val <- `val*`} ++ [RETURN_admininstr] ++ admininstr*{admininstr <- `admininstr*`})], (val : val <: admininstr)*{val <- `val*`} ++ [RETURN_admininstr])

  ;; ../specification/wasm-2.0/8-reduction.spectec:150.1-152.44
  rule `trap-vals`{`val*` : val*, `admininstr*` : admininstr*}:
    `%~>%`((val : val <: admininstr)*{val <- `val*`} ++ [TRAP_admininstr] ++ admininstr*{admininstr <- `admininstr*`}, [TRAP_admininstr])
    -- if ((val*{val <- `val*`} =/= []) \/ (admininstr*{admininstr <- `admininstr*`} =/= []))

  ;; ../specification/wasm-2.0/8-reduction.spectec:154.1-155.39
  rule `trap-label`{n : n, `instr'*` : instr*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(n, instr'*{instr' <- `instr'*`}, [TRAP_admininstr])], [TRAP_admininstr])

  ;; ../specification/wasm-2.0/8-reduction.spectec:157.1-158.33
  rule `trap-frame`{n : n, f : frame}:
    `%~>%`([`FRAME_%{%}%`_admininstr(n, f, [TRAP_admininstr])], [TRAP_admininstr])

  ;; ../specification/wasm-2.0/8-reduction.spectec:178.1-180.35
  rule `unop-val`{nt : numtype, c_1 : num_(nt), unop : unop_(nt), c : num_(nt)}:
    `%~>%`([CONST_admininstr(nt, c_1) UNOP_admininstr(nt, unop)], [CONST_admininstr(nt, c)])
    -- if (c <- $unop_(nt, unop, c_1))

  ;; ../specification/wasm-2.0/8-reduction.spectec:182.1-184.36
  rule `unop-trap`{nt : numtype, c_1 : num_(nt), unop : unop_(nt)}:
    `%~>%`([CONST_admininstr(nt, c_1) UNOP_admininstr(nt, unop)], [TRAP_admininstr])
    -- if ($unop_(nt, unop, c_1) = [])

  ;; ../specification/wasm-2.0/8-reduction.spectec:187.1-189.42
  rule `binop-val`{nt : numtype, c_1 : num_(nt), c_2 : num_(nt), binop : binop_(nt), c : num_(nt)}:
    `%~>%`([CONST_admininstr(nt, c_1) CONST_admininstr(nt, c_2) BINOP_admininstr(nt, binop)], [CONST_admininstr(nt, c)])
    -- if (c <- $binop_(nt, binop, c_1, c_2))

  ;; ../specification/wasm-2.0/8-reduction.spectec:191.1-193.43
  rule `binop-trap`{nt : numtype, c_1 : num_(nt), c_2 : num_(nt), binop : binop_(nt)}:
    `%~>%`([CONST_admininstr(nt, c_1) CONST_admininstr(nt, c_2) BINOP_admininstr(nt, binop)], [TRAP_admininstr])
    -- if ($binop_(nt, binop, c_1, c_2) = [])

  ;; ../specification/wasm-2.0/8-reduction.spectec:196.1-198.38
  rule testop{nt : numtype, c_1 : num_(nt), testop : testop_(nt), c : num_(I32_numtype)}:
    `%~>%`([CONST_admininstr(nt, c_1) TESTOP_admininstr(nt, testop)], [CONST_admininstr(I32_numtype, c)])
    -- if (c = $testop_(nt, testop, c_1))

  ;; ../specification/wasm-2.0/8-reduction.spectec:200.1-202.41
  rule relop{nt : numtype, c_1 : num_(nt), c_2 : num_(nt), relop : relop_(nt), c : num_(I32_numtype)}:
    `%~>%`([CONST_admininstr(nt, c_1) CONST_admininstr(nt, c_2) RELOP_admininstr(nt, relop)], [CONST_admininstr(I32_numtype, c)])
    -- if (c = $relop_(nt, relop, c_1, c_2))

  ;; ../specification/wasm-2.0/8-reduction.spectec:205.1-207.46
  rule `cvtop-val`{nt_1 : numtype, c_1 : num_(nt_1), nt_2 : numtype, cvtop : cvtop__(nt_1, nt_2), c : num_(nt_2)}:
    `%~>%`([CONST_admininstr(nt_1, c_1) CVTOP_admininstr(nt_2, nt_1, cvtop)], [CONST_admininstr(nt_2, c)])
    -- if (c <- $cvtop__(nt_1, nt_2, cvtop, c_1))

  ;; ../specification/wasm-2.0/8-reduction.spectec:209.1-211.47
  rule `cvtop-trap`{nt_1 : numtype, c_1 : num_(nt_1), nt_2 : numtype, cvtop : cvtop__(nt_1, nt_2)}:
    `%~>%`([CONST_admininstr(nt_1, c_1) CVTOP_admininstr(nt_2, nt_1, cvtop)], [TRAP_admininstr])
    -- if ($cvtop__(nt_1, nt_2, cvtop, c_1) = [])

  ;; ../specification/wasm-2.0/8-reduction.spectec:220.1-222.28
  rule `ref.is_null-true`{ref : ref, rt : reftype}:
    `%~>%`([(ref : ref <: admininstr) `REF.IS_NULL`_admininstr], [CONST_admininstr(I32_numtype, `%`_num_(1))])
    -- if (ref = `REF.NULL`_ref(rt))

  ;; ../specification/wasm-2.0/8-reduction.spectec:224.1-226.15
  rule `ref.is_null-false`{ref : ref}:
    `%~>%`([(ref : ref <: admininstr) `REF.IS_NULL`_admininstr], [CONST_admininstr(I32_numtype, `%`_num_(0))])
    -- otherwise

  ;; ../specification/wasm-2.0/8-reduction.spectec:231.1-233.40
  rule vvunop{c_1 : vec_(V128_Vnn), vvunop : vvunop, c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) VVUNOP_admininstr(V128_vectype, vvunop)], [VCONST_admininstr(V128_vectype, c)])
    -- if (c = $vvunop_(V128_vectype, vvunop, c_1))

  ;; ../specification/wasm-2.0/8-reduction.spectec:236.1-238.47
  rule vvbinop{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), vvbinop : vvbinop, c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) VCONST_admininstr(V128_vectype, c_2) VVBINOP_admininstr(V128_vectype, vvbinop)], [VCONST_admininstr(V128_vectype, c)])
    -- if (c = $vvbinop_(V128_vectype, vvbinop, c_1, c_2))

  ;; ../specification/wasm-2.0/8-reduction.spectec:241.1-244.54
  rule vvternop{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), c_3 : vec_(V128_Vnn), vvternop : vvternop, c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) VCONST_admininstr(V128_vectype, c_2) VCONST_admininstr(V128_vectype, c_3) VVTERNOP_admininstr(V128_vectype, vvternop)], [VCONST_admininstr(V128_vectype, c)])
    -- if (c = $vvternop_(V128_vectype, vvternop, c_1, c_2, c_3))

  ;; ../specification/wasm-2.0/8-reduction.spectec:247.1-249.39
  rule vvtestop{c_1 : vec_(V128_Vnn), c : num_(I32_numtype)}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) VVTESTOP_admininstr(V128_vectype, ANY_TRUE_vvtestop)], [CONST_admininstr(I32_numtype, c)])
    -- if (c = $ine_($size(V128_valtype), c_1, `%`_iN(0)))

  ;; ../specification/wasm-2.0/8-reduction.spectec:252.1-254.37
  rule vunop{c_1 : vec_(V128_Vnn), sh : shape, vunop : vunop_(sh), c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) VUNOP_admininstr(sh, vunop)], [VCONST_admininstr(V128_vectype, c)])
    -- if (c <- $vunop_(sh, vunop, c_1))

  ;; ../specification/wasm-2.0/8-reduction.spectec:256.1-258.38
  rule `vunop-trap`{c_1 : vec_(V128_Vnn), sh : shape, vunop : vunop_(sh)}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) VUNOP_admininstr(sh, vunop)], [TRAP_admininstr])
    -- if ($vunop_(sh, vunop, c_1) = [])

  ;; ../specification/wasm-2.0/8-reduction.spectec:261.1-263.44
  rule `vbinop-val`{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), sh : shape, vbinop : vbinop_(sh), c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) VCONST_admininstr(V128_vectype, c_2) VBINOP_admininstr(sh, vbinop)], [VCONST_admininstr(V128_vectype, c)])
    -- if (c <- $vbinop_(sh, vbinop, c_1, c_2))

  ;; ../specification/wasm-2.0/8-reduction.spectec:265.1-267.45
  rule `vbinop-trap`{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), sh : shape, vbinop : vbinop_(sh)}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) VCONST_admininstr(V128_vectype, c_2) VBINOP_admininstr(sh, vbinop)], [TRAP_admininstr])
    -- if ($vbinop_(sh, vbinop, c_1, c_2) = [])

  ;; ../specification/wasm-2.0/8-reduction.spectec:271.1-274.25
  rule `vtestop-true`{c : vec_(V128_Vnn), Jnn : Jnn, N : N, `ci_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N))))*}:
    `%~>%`([VCONST_admininstr(V128_vectype, c) VTESTOP_admininstr(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N)), ALL_TRUE_vtestop_)], [CONST_admininstr(I32_numtype, `%`_num_(1))])
    -- if (ci_1*{ci_1 <- `ci_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N)), c))
    -- (if (ci_1!`%`_lane_.0 =/= 0))*{ci_1 <- `ci_1*`}

  ;; ../specification/wasm-2.0/8-reduction.spectec:276.1-278.15
  rule `vtestop-false`{c : vec_(V128_Vnn), Jnn : Jnn, N : N}:
    `%~>%`([VCONST_admininstr(V128_vectype, c) VTESTOP_admininstr(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N)), ALL_TRUE_vtestop_)], [CONST_admininstr(I32_numtype, `%`_num_(0))])
    -- otherwise

  ;; ../specification/wasm-2.0/8-reduction.spectec:281.1-283.43
  rule vrelop{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), sh : shape, vrelop : vrelop_(sh), c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) VCONST_admininstr(V128_vectype, c_2) VRELOP_admininstr(sh, vrelop)], [VCONST_admininstr(V128_vectype, c)])
    -- if ($vrelop_(sh, vrelop, c_1, c_2) = c)

  ;; ../specification/wasm-2.0/8-reduction.spectec:291.1-294.72
  rule vshiftop{c_1 : vec_(V128_Vnn), n : n, Jnn : Jnn, N : N, vshiftop : vshiftop_(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N)))), c : vec_(V128_Vnn), `c'*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N))))*}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) CONST_admininstr(I32_numtype, `%`_num_(n)) VSHIFTOP_admininstr(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N))), vshiftop)], [VCONST_admininstr(V128_vectype, c)])
    -- if (c'*{c' <- `c'*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N)), c_1))
    -- if (c = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N)), $vshiftop_(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N))), vshiftop, c', `%`_u32(n))*{c' <- `c'*`}))

  ;; ../specification/wasm-2.0/8-reduction.spectec:297.1-300.69
  rule vbitmask{c : vec_(V128_Vnn), Jnn : Jnn, N : N, ci : iN(32), `ci_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N))))*}:
    `%~>%`([VCONST_admininstr(V128_vectype, c) VBITMASK_admininstr(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N))))], [CONST_admininstr(I32_numtype, $irev_(32, ci))])
    -- if (ci_1*{ci_1 <- `ci_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N)), c))
    -- if ($ibits_(32, ci) = `%`_bit($ilt_($lsize((Jnn : Jnn <: lanetype)), S_sx, ci_1, `%`_iN(0))!`%`_u32.0)*{ci_1 <- `ci_1*`} ++ `%`_bit(0)^(((32 : nat <:> int) - (N : nat <:> int)) : int <:> nat){})

  ;; ../specification/wasm-2.0/8-reduction.spectec:303.1-308.55
  rule vswizzle{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), Pnn : Pnn, M : M, c : vec_(V128_Vnn), `ci*` : lane_($lanetype(`%X%`_shape((Pnn : packtype <: lanetype), `%`_dim(M))))*, `c'*` : iN($lsize((Pnn : packtype <: lanetype)))*, k : nat}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) VCONST_admininstr(V128_vectype, c_2) VSWIZZLE_admininstr(`%`_ishape(`%X%`_shape((Pnn : packtype <: lanetype), `%`_dim(M))))], [VCONST_admininstr(V128_vectype, c)])
    -- if (ci*{ci <- `ci*`} = $lanes_(`%X%`_shape((Pnn : packtype <: lanetype), `%`_dim(M)), c_2))
    -- if (c'*{c' <- `c'*`} = $lanes_(`%X%`_shape((Pnn : packtype <: lanetype), `%`_dim(M)), c_1) ++ `%`_iN(0)^(((256 : nat <:> int) - (M : nat <:> int)) : int <:> nat){})
    -- if (c = $inv_lanes_(`%X%`_shape((Pnn : packtype <: lanetype), `%`_dim(M)), c'*{c' <- `c'*`}[ci*{ci <- `ci*`}[k]!`%`_lane_.0]^(k<M){}))

  ;; ../specification/wasm-2.0/8-reduction.spectec:311.1-315.54
  rule vshuffle{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), Pnn : Pnn, N : N, `i*` : laneidx*, c : vec_(V128_Vnn), `c'*` : iN($lsize((Pnn : packtype <: lanetype)))*, k : nat}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) VCONST_admininstr(V128_vectype, c_2) VSHUFFLE_admininstr(`%`_ishape(`%X%`_shape((Pnn : packtype <: lanetype), `%`_dim(N))), i*{i <- `i*`})], [VCONST_admininstr(V128_vectype, c)])
    -- if (c'*{c' <- `c'*`} = $lanes_(`%X%`_shape((Pnn : packtype <: lanetype), `%`_dim(N)), c_1) ++ $lanes_(`%X%`_shape((Pnn : packtype <: lanetype), `%`_dim(N)), c_2))
    -- if (c = $inv_lanes_(`%X%`_shape((Pnn : packtype <: lanetype), `%`_dim(N)), c'*{c' <- `c'*`}[i*{i <- `i*`}[k]!`%`_laneidx.0]^(k<N){}))

  ;; ../specification/wasm-2.0/8-reduction.spectec:318.1-320.56
  rule vsplat{Lnn : Lnn, c_1 : num_($unpack(Lnn)), N : N, c : vec_(V128_Vnn)}:
    `%~>%`([CONST_admininstr($unpack(Lnn), c_1) VSPLAT_admininstr(`%X%`_shape(Lnn, `%`_dim(N)))], [VCONST_admininstr(V128_vectype, c)])
    -- if (c = $inv_lanes_(`%X%`_shape(Lnn, `%`_dim(N)), $packnum_(Lnn, c_1)^N{}))

  ;; ../specification/wasm-2.0/8-reduction.spectec:323.1-325.55
  rule `vextract_lane-num`{c_1 : vec_(V128_Vnn), nt : numtype, N : N, i : laneidx, c_2 : num_(nt)}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) VEXTRACT_LANE_admininstr(`%X%`_shape((nt : numtype <: lanetype), `%`_dim(N)), ?(), i)], [CONST_admininstr(nt, c_2)])
    -- if (c_2 = $unpacknum_((nt : numtype <: lanetype), $lanes_(`%X%`_shape((nt : numtype <: lanetype), `%`_dim(N)), c_1)[i!`%`_laneidx.0]))

  ;; ../specification/wasm-2.0/8-reduction.spectec:328.1-330.69
  rule `vextract_lane-pack`{c_1 : vec_(V128_Vnn), pt : packtype, N : N, sx : sx, i : laneidx, c_2 : num_(I32_numtype)}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) VEXTRACT_LANE_admininstr(`%X%`_shape((pt : packtype <: lanetype), `%`_dim(N)), ?(sx), i)], [CONST_admininstr(I32_numtype, c_2)])
    -- if (c_2 = $extend__($psize(pt), 32, sx, $lanes_(`%X%`_shape((pt : packtype <: lanetype), `%`_dim(N)), c_1)[i!`%`_laneidx.0]))

  ;; ../specification/wasm-2.0/8-reduction.spectec:333.1-335.83
  rule vreplace_lane{c_1 : vec_(V128_Vnn), Lnn : Lnn, c_2 : num_($unpack(Lnn)), N : N, i : laneidx, c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) CONST_admininstr($unpack(Lnn), c_2) VREPLACE_LANE_admininstr(`%X%`_shape(Lnn, `%`_dim(N)), i)], [VCONST_admininstr(V128_vectype, c)])
    -- if (c = $inv_lanes_(`%X%`_shape(Lnn, `%`_dim(N)), $lanes_(`%X%`_shape(Lnn, `%`_dim(N)), c_1)[[i!`%`_laneidx.0] = $packnum_(Lnn, c_2)]))

  ;; ../specification/wasm-2.0/8-reduction.spectec:338.1-340.51
  rule vextunop{c_1 : vec_(V128_Vnn), sh_2 : ishape, sh_1 : ishape, vextunop : vextunop__(sh_1, sh_2), c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) VEXTUNOP_admininstr(sh_2, sh_1, vextunop)], [VCONST_admininstr(V128_vectype, c)])
    -- if ($vextunop__(sh_1, sh_2, vextunop, c_1) = c)

  ;; ../specification/wasm-2.0/8-reduction.spectec:343.1-345.58
  rule vextbinop{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), sh_2 : ishape, sh_1 : ishape, vextbinop : vextbinop__(sh_1, sh_2), c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) VCONST_admininstr(V128_vectype, c_2) VEXTBINOP_admininstr(sh_2, sh_1, vextbinop)], [VCONST_admininstr(V128_vectype, c)])
    -- if ($vextbinop__(sh_1, sh_2, vextbinop, c_1, c_2) = c)

  ;; ../specification/wasm-2.0/8-reduction.spectec:348.1-354.50
  rule vnarrow{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), Jnn_2 : Jnn, N_2 : N, Jnn_1 : Jnn, N_1 : N, sx : sx, c : vec_(V128_Vnn), `ci_1*` : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(N_1))))*, `ci_2*` : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(N_1))))*, `cj_1*` : iN($lsize((Jnn_2 : Jnn <: lanetype)))*, `cj_2*` : iN($lsize((Jnn_2 : Jnn <: lanetype)))*}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) VCONST_admininstr(V128_vectype, c_2) VNARROW_admininstr(`%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(N_2))), `%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(N_1))), sx)], [VCONST_admininstr(V128_vectype, c)])
    -- if (ci_1*{ci_1 <- `ci_1*`} = $lanes_(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(N_1)), c_1))
    -- if (ci_2*{ci_2 <- `ci_2*`} = $lanes_(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(N_1)), c_2))
    -- if (cj_1*{cj_1 <- `cj_1*`} = $narrow__($lsize((Jnn_1 : Jnn <: lanetype)), $lsize((Jnn_2 : Jnn <: lanetype)), sx, ci_1)*{ci_1 <- `ci_1*`})
    -- if (cj_2*{cj_2 <- `cj_2*`} = $narrow__($lsize((Jnn_1 : Jnn <: lanetype)), $lsize((Jnn_2 : Jnn <: lanetype)), sx, ci_2)*{ci_2 <- `ci_2*`})
    -- if (c = $inv_lanes_(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(N_2)), cj_1*{cj_1 <- `cj_1*`} ++ cj_2*{cj_2 <- `cj_2*`}))

  ;; ../specification/wasm-2.0/8-reduction.spectec:357.1-359.47
  rule vcvtop{c_1 : vec_(V128_Vnn), sh_2 : shape, sh_1 : shape, vcvtop : vcvtop__(sh_1, sh_2), c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_admininstr(V128_vectype, c_1) VCVTOP_admininstr(sh_2, sh_1, vcvtop)], [VCONST_admininstr(V128_vectype, c)])
    -- if (c = $vcvtop__(sh_1, sh_2, vcvtop, c_1))

  ;; ../specification/wasm-2.0/8-reduction.spectec:370.1-371.47
  rule `local.tee`{val : val, x : idx}:
    `%~>%`([(val : val <: admininstr) `LOCAL.TEE`_admininstr(x)], [(val : val <: admininstr) (val : val <: admininstr) `LOCAL.SET`_admininstr(x)])

;; ../specification/wasm-2.0/8-reduction.spectec:63.1-63.73
def $blocktype(state : state, blocktype : blocktype) : functype
  ;; ../specification/wasm-2.0/8-reduction.spectec:64.1-64.44
  def $blocktype{z : state}(z, _RESULT_blocktype(?())) = `%->%`_functype(`%`_resulttype([]), `%`_resulttype([]))
  ;; ../specification/wasm-2.0/8-reduction.spectec:65.1-65.40
  def $blocktype{z : state, t : valtype}(z, _RESULT_blocktype(?(t))) = `%->%`_functype(`%`_resulttype([]), `%`_resulttype([t]))
  ;; ../specification/wasm-2.0/8-reduction.spectec:66.1-66.40
  def $blocktype{z : state, x : idx}(z, _IDX_blocktype(x)) = $type(z, x)

;; ../specification/wasm-2.0/8-reduction.spectec:7.1-7.109
relation Step_read: `%~>%`(config, admininstr*)
  ;; ../specification/wasm-2.0/8-reduction.spectec:68.1-70.43
  rule block{z : state, k : nat, `val*` : val*, bt : blocktype, `instr*` : instr*, n : n, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%~>%`(`%;%`_config(z, (val : val <: admininstr)^k{val <- `val*`} ++ [BLOCK_admininstr(bt, instr*{instr <- `instr*`})]), [`LABEL_%{%}%`_admininstr(n, [], (val : val <: admininstr)^k{val <- `val*`} ++ (instr : instr <: admininstr)*{instr <- `instr*`})])
    -- if ($blocktype(z, bt) = `%->%`_functype(`%`_resulttype(t_1^k{t_1 <- `t_1*`}), `%`_resulttype(t_2^n{t_2 <- `t_2*`})))

  ;; ../specification/wasm-2.0/8-reduction.spectec:72.1-74.43
  rule loop{z : state, k : nat, `val*` : val*, bt : blocktype, `instr*` : instr*, `t_1*` : valtype*, n : n, `t_2*` : valtype*}:
    `%~>%`(`%;%`_config(z, (val : val <: admininstr)^k{val <- `val*`} ++ [LOOP_admininstr(bt, instr*{instr <- `instr*`})]), [`LABEL_%{%}%`_admininstr(k, [LOOP_instr(bt, instr*{instr <- `instr*`})], (val : val <: admininstr)^k{val <- `val*`} ++ (instr : instr <: admininstr)*{instr <- `instr*`})])
    -- if ($blocktype(z, bt) = `%->%`_functype(`%`_resulttype(t_1^k{t_1 <- `t_1*`}), `%`_resulttype(t_2^n{t_2 <- `t_2*`})))

  ;; ../specification/wasm-2.0/8-reduction.spectec:119.1-120.47
  rule call{z : state, x : idx}:
    `%~>%`(`%;%`_config(z, [CALL_admininstr(x)]), [CALL_ADDR_admininstr($funcaddr(z)[x!`%`_idx.0])])

  ;; ../specification/wasm-2.0/8-reduction.spectec:122.1-125.43
  rule `call_indirect-call`{z : state, i : num_(I32_numtype), x : idx, y : idx, a : addr}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) CALL_INDIRECT_admininstr(x, y)]), [CALL_ADDR_admininstr(a)])
    -- if ($table(z, x).REFS_tableinst[i!`%`_num_.0] = `REF.FUNC_ADDR`_ref(a))
    -- if ($type(z, y) = $funcinst(z)[a].TYPE_funcinst)

  ;; ../specification/wasm-2.0/8-reduction.spectec:127.1-129.15
  rule `call_indirect-trap`{z : state, i : num_(I32_numtype), x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) CALL_INDIRECT_admininstr(x, y)]), [TRAP_admininstr])
    -- otherwise

  ;; ../specification/wasm-2.0/8-reduction.spectec:131.1-135.54
  rule call_addr{z : state, k : nat, `val*` : val*, a : addr, n : n, f : frame, `instr*` : instr*, `t_1*` : valtype*, `t_2*` : valtype*, mm : moduleinst, func : func, x : idx, `t*` : valtype*}:
    `%~>%`(`%;%`_config(z, (val : val <: admininstr)^k{val <- `val*`} ++ [CALL_ADDR_admininstr(a)]), [`FRAME_%{%}%`_admininstr(n, f, [`LABEL_%{%}%`_admininstr(n, [], (instr : instr <: admininstr)*{instr <- `instr*`})])])
    -- if ($funcinst(z)[a] = {TYPE `%->%`_functype(`%`_resulttype(t_1^k{t_1 <- `t_1*`}), `%`_resulttype(t_2^n{t_2 <- `t_2*`})), MODULE mm, CODE func})
    -- if (func = FUNC_func(x, LOCAL_local(t)*{t <- `t*`}, instr*{instr <- `instr*`}))
    -- if (f = {LOCALS val^k{val <- `val*`} ++ $default_(t)*{t <- `t*`}, MODULE mm})

  ;; ../specification/wasm-2.0/8-reduction.spectec:216.1-217.53
  rule `ref.func`{z : state, x : idx}:
    `%~>%`(`%;%`_config(z, [`REF.FUNC`_admininstr(x)]), [`REF.FUNC_ADDR`_admininstr($funcaddr(z)[x!`%`_idx.0])])

  ;; ../specification/wasm-2.0/8-reduction.spectec:364.1-365.37
  rule `local.get`{z : state, x : idx}:
    `%~>%`(`%;%`_config(z, [`LOCAL.GET`_admininstr(x)]), [($local(z, x) : val <: admininstr)])

  ;; ../specification/wasm-2.0/8-reduction.spectec:376.1-377.45
  rule `global.get`{z : state, x : idx}:
    `%~>%`(`%;%`_config(z, [`GLOBAL.GET`_admininstr(x)]), [($global(z, x).VALUE_globalinst : val <: admininstr)])

  ;; ../specification/wasm-2.0/8-reduction.spectec:385.1-387.33
  rule `table.get-trap`{z : state, i : num_(I32_numtype), x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) `TABLE.GET`_admininstr(x)]), [TRAP_admininstr])
    -- if (i!`%`_num_.0 >= |$table(z, x).REFS_tableinst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:389.1-391.32
  rule `table.get-val`{z : state, i : num_(I32_numtype), x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) `TABLE.GET`_admininstr(x)]), [($table(z, x).REFS_tableinst[i!`%`_num_.0] : ref <: admininstr)])
    -- if (i!`%`_num_.0 < |$table(z, x).REFS_tableinst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:402.1-404.32
  rule `table.size`{z : state, x : idx, n : n}:
    `%~>%`(`%;%`_config(z, [`TABLE.SIZE`_admininstr(x)]), [CONST_admininstr(I32_numtype, `%`_num_(n))])
    -- if (|$table(z, x).REFS_tableinst| = n)

  ;; ../specification/wasm-2.0/8-reduction.spectec:415.1-417.39
  rule `table.fill-trap`{z : state, i : num_(I32_numtype), val : val, n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) (val : val <: admininstr) CONST_admininstr(I32_numtype, `%`_num_(n)) `TABLE.FILL`_admininstr(x)]), [TRAP_admininstr])
    -- if ((i!`%`_num_.0 + n) > |$table(z, x).REFS_tableinst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:419.1-422.14
  rule `table.fill-zero`{z : state, i : num_(I32_numtype), val : val, n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) (val : val <: admininstr) CONST_admininstr(I32_numtype, `%`_num_(n)) `TABLE.FILL`_admininstr(x)]), [])
    -- otherwise
    -- if (n = 0)

  ;; ../specification/wasm-2.0/8-reduction.spectec:424.1-428.15
  rule `table.fill-succ`{z : state, i : num_(I32_numtype), val : val, n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) (val : val <: admininstr) CONST_admininstr(I32_numtype, `%`_num_(n)) `TABLE.FILL`_admininstr(x)]), [CONST_admininstr(I32_numtype, i) (val : val <: admininstr) `TABLE.SET`_admininstr(x) CONST_admininstr(I32_numtype, `%`_num_((i!`%`_num_.0 + 1))) (val : val <: admininstr) CONST_admininstr(I32_numtype, `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `TABLE.FILL`_admininstr(x)])
    -- otherwise

  ;; ../specification/wasm-2.0/8-reduction.spectec:431.1-433.73
  rule `table.copy-trap`{z : state, j : num_(I32_numtype), i : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, `%`_num_(n)) `TABLE.COPY`_admininstr(x, y)]), [TRAP_admininstr])
    -- if (((i!`%`_num_.0 + n) > |$table(z, y).REFS_tableinst|) \/ ((j!`%`_num_.0 + n) > |$table(z, x).REFS_tableinst|))

  ;; ../specification/wasm-2.0/8-reduction.spectec:435.1-438.14
  rule `table.copy-zero`{z : state, j : num_(I32_numtype), i : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, `%`_num_(n)) `TABLE.COPY`_admininstr(x, y)]), [])
    -- otherwise
    -- if (n = 0)

  ;; ../specification/wasm-2.0/8-reduction.spectec:440.1-445.15
  rule `table.copy-le`{z : state, j : num_(I32_numtype), i : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, `%`_num_(n)) `TABLE.COPY`_admininstr(x, y)]), [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) `TABLE.GET`_admininstr(y) `TABLE.SET`_admininstr(x) CONST_admininstr(I32_numtype, `%`_num_((j!`%`_num_.0 + 1))) CONST_admininstr(I32_numtype, `%`_num_((i!`%`_num_.0 + 1))) CONST_admininstr(I32_numtype, `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `TABLE.COPY`_admininstr(x, y)])
    -- otherwise
    -- if (j!`%`_num_.0 <= i!`%`_num_.0)

  ;; ../specification/wasm-2.0/8-reduction.spectec:447.1-451.15
  rule `table.copy-gt`{z : state, j : num_(I32_numtype), i : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, `%`_num_(n)) `TABLE.COPY`_admininstr(x, y)]), [CONST_admininstr(I32_numtype, `%`_num_(((((j!`%`_num_.0 + n) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) CONST_admininstr(I32_numtype, `%`_num_(((((i!`%`_num_.0 + n) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `TABLE.GET`_admininstr(y) `TABLE.SET`_admininstr(x) CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `TABLE.COPY`_admininstr(x, y)])
    -- otherwise

  ;; ../specification/wasm-2.0/8-reduction.spectec:454.1-456.72
  rule `table.init-trap`{z : state, j : num_(I32_numtype), i : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, `%`_num_(n)) `TABLE.INIT`_admininstr(x, y)]), [TRAP_admininstr])
    -- if (((i!`%`_num_.0 + n) > |$elem(z, y).REFS_eleminst|) \/ ((j!`%`_num_.0 + n) > |$table(z, x).REFS_tableinst|))

  ;; ../specification/wasm-2.0/8-reduction.spectec:458.1-461.14
  rule `table.init-zero`{z : state, j : num_(I32_numtype), i : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, `%`_num_(n)) `TABLE.INIT`_admininstr(x, y)]), [])
    -- otherwise
    -- if (n = 0)

  ;; ../specification/wasm-2.0/8-reduction.spectec:463.1-467.15
  rule `table.init-succ`{z : state, j : num_(I32_numtype), i : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, `%`_num_(n)) `TABLE.INIT`_admininstr(x, y)]), [CONST_admininstr(I32_numtype, j) ($elem(z, y).REFS_eleminst[i!`%`_num_.0] : ref <: admininstr) `TABLE.SET`_admininstr(x) CONST_admininstr(I32_numtype, `%`_num_((j!`%`_num_.0 + 1))) CONST_admininstr(I32_numtype, `%`_num_((i!`%`_num_.0 + 1))) CONST_admininstr(I32_numtype, `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `TABLE.INIT`_admininstr(x, y)])
    -- otherwise

  ;; ../specification/wasm-2.0/8-reduction.spectec:476.1-478.60
  rule `load-num-trap`{z : state, i : num_(I32_numtype), nt : numtype, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) LOAD_admininstr(nt, ?(), ao)]), [TRAP_admininstr])
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) + ((($size((nt : numtype <: valtype)) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, `%`_memidx(0)).BYTES_meminst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:480.1-482.72
  rule `load-num-val`{z : state, i : num_(I32_numtype), nt : numtype, ao : memarg, c : num_(nt)}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) LOAD_admininstr(nt, ?(), ao)]), [CONST_admininstr(nt, c)])
    -- if ($nbytes_(nt, c) = $mem(z, `%`_memidx(0)).BYTES_meminst[(i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) : ((($size((nt : numtype <: valtype)) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])

  ;; ../specification/wasm-2.0/8-reduction.spectec:484.1-486.52
  rule `load-pack-trap`{z : state, i : num_(I32_numtype), Inn : Inn, n : n, sx : sx, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) LOAD_admininstr((Inn : Inn <: numtype), ?(`%_%`_loadop_(`%`_sz(n), sx)), ao)]), [TRAP_admininstr])
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) + (((n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, `%`_memidx(0)).BYTES_meminst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:488.1-490.63
  rule `load-pack-val`{z : state, i : num_(I32_numtype), Inn : Inn, n : n, sx : sx, ao : memarg, c : iN(n)}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) LOAD_admininstr((Inn : Inn <: numtype), ?(`%_%`_loadop_(`%`_sz(n), sx)), ao)]), [CONST_admininstr((Inn : Inn <: numtype), $extend__(n, $size((Inn : Inn <: valtype)), sx, c))])
    -- if ($ibytes_(n, c) = $mem(z, `%`_memidx(0)).BYTES_meminst[(i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) : (((n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])

  ;; ../specification/wasm-2.0/8-reduction.spectec:492.1-494.62
  rule `vload-oob`{z : state, i : num_(I32_numtype), ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) VLOAD_admininstr(V128_vectype, ?(), ao)]), [TRAP_admininstr])
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) + ((($size(V128_valtype) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, `%`_memidx(0)).BYTES_meminst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:496.1-498.76
  rule `vload-val`{z : state, i : num_(I32_numtype), ao : memarg, c : vec_(V128_Vnn)}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) VLOAD_admininstr(V128_vectype, ?(), ao)]), [VCONST_admininstr(V128_vectype, c)])
    -- if ($vbytes_(V128_vectype, c) = $mem(z, `%`_memidx(0)).BYTES_meminst[(i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) : ((($size(V128_valtype) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])

  ;; ../specification/wasm-2.0/8-reduction.spectec:501.1-503.56
  rule `vload-shape-oob`{z : state, i : num_(I32_numtype), M : M, N : N, sx : sx, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) VLOAD_admininstr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(M), N, sx)), ao)]), [TRAP_admininstr])
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) + ((((M * N) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, `%`_memidx(0)).BYTES_meminst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:505.1-509.69
  rule `vload-shape-val`{z : state, i : num_(I32_numtype), M : M, N : N, sx : sx, ao : memarg, c : vec_(V128_Vnn), `j*` : iN(M)*, Jnn : Jnn}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) VLOAD_admininstr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(M), N, sx)), ao)]), [VCONST_admininstr(V128_vectype, c)])
    -- (if ($ibytes_(M, j) = $mem(z, `%`_memidx(0)).BYTES_meminst[((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) + ((((k * M) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) : (((M : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)]))^(k<N){j <- `j*`}
    -- if ($jsize(Jnn) = (M * 2))
    -- if (c = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(N)), $extend__(M, $jsize(Jnn), sx, j)^N{j <- `j*`}))

  ;; ../specification/wasm-2.0/8-reduction.spectec:512.1-514.52
  rule `vload-splat-oob`{z : state, i : num_(I32_numtype), N : N, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) VLOAD_admininstr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(N))), ao)]), [TRAP_admininstr])
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) + (((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, `%`_memidx(0)).BYTES_meminst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:516.1-521.38
  rule `vload-splat-val`{z : state, i : num_(I32_numtype), N : N, ao : memarg, c : vec_(V128_Vnn), j : iN(N), Jnn : Jnn, M : M}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) VLOAD_admininstr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(N))), ao)]), [VCONST_admininstr(V128_vectype, c)])
    -- if ($ibytes_(N, j) = $mem(z, `%`_memidx(0)).BYTES_meminst[(i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) : (((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])
    -- if (N = $jsize(Jnn))
    -- if ((M : nat <:> rat) = ((128 : nat <:> rat) / (N : nat <:> rat)))
    -- if (c = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), `%`_lane_(j!`%`_iN.0)^M{}))

  ;; ../specification/wasm-2.0/8-reduction.spectec:524.1-526.52
  rule `vload-zero-oob`{z : state, i : num_(I32_numtype), N : N, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) VLOAD_admininstr(V128_vectype, ?(ZERO_vloadop_(`%`_sz(N))), ao)]), [TRAP_admininstr])
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) + (((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, `%`_memidx(0)).BYTES_meminst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:528.1-531.36
  rule `vload-zero-val`{z : state, i : num_(I32_numtype), N : N, ao : memarg, c : vec_(V128_Vnn), j : iN(N)}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) VLOAD_admininstr(V128_vectype, ?(ZERO_vloadop_(`%`_sz(N))), ao)]), [VCONST_admininstr(V128_vectype, c)])
    -- if ($ibytes_(N, j) = $mem(z, `%`_memidx(0)).BYTES_meminst[(i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) : (((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])
    -- if (c = $extend__(N, 128, U_sx, j))

  ;; ../specification/wasm-2.0/8-reduction.spectec:534.1-536.52
  rule `vload_lane-oob`{z : state, i : num_(I32_numtype), c_1 : vec_(V128_Vnn), N : N, ao : memarg, j : laneidx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) VCONST_admininstr(V128_vectype, c_1) VLOAD_LANE_admininstr(V128_vectype, `%`_sz(N), ao, j)]), [TRAP_admininstr])
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) + (((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, `%`_memidx(0)).BYTES_meminst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:538.1-543.65
  rule `vload_lane-val`{z : state, i : num_(I32_numtype), c_1 : vec_(V128_Vnn), N : N, ao : memarg, j : laneidx, c : vec_(V128_Vnn), k : iN(N), Jnn : Jnn, M : M}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) VCONST_admininstr(V128_vectype, c_1) VLOAD_LANE_admininstr(V128_vectype, `%`_sz(N), ao, j)]), [VCONST_admininstr(V128_vectype, c)])
    -- if ($ibytes_(N, k) = $mem(z, `%`_memidx(0)).BYTES_meminst[(i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) : (((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])
    -- if (N = $jsize(Jnn))
    -- if ((M : nat <:> rat) = ((128 : nat <:> rat) / (N : nat <:> rat)))
    -- if (c = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c_1)[[j!`%`_laneidx.0] = `%`_lane_(k!`%`_iN.0)]))

  ;; ../specification/wasm-2.0/8-reduction.spectec:582.1-584.45
  rule `memory.size`{z : state, n : n}:
    `%~>%`(`%;%`_config(z, [`MEMORY.SIZE`_admininstr]), [CONST_admininstr(I32_numtype, `%`_num_(n))])
    -- if (((n * 64) * $Ki) = |$mem(z, `%`_memidx(0)).BYTES_meminst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:595.1-597.38
  rule `memory.fill-trap`{z : state, i : num_(I32_numtype), val : val, n : n}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) (val : val <: admininstr) CONST_admininstr(I32_numtype, `%`_num_(n)) `MEMORY.FILL`_admininstr]), [TRAP_admininstr])
    -- if ((i!`%`_num_.0 + n) > |$mem(z, `%`_memidx(0)).BYTES_meminst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:599.1-602.14
  rule `memory.fill-zero`{z : state, i : num_(I32_numtype), val : val, n : n}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) (val : val <: admininstr) CONST_admininstr(I32_numtype, `%`_num_(n)) `MEMORY.FILL`_admininstr]), [])
    -- otherwise
    -- if (n = 0)

  ;; ../specification/wasm-2.0/8-reduction.spectec:604.1-608.15
  rule `memory.fill-succ`{z : state, i : num_(I32_numtype), val : val, n : n}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) (val : val <: admininstr) CONST_admininstr(I32_numtype, `%`_num_(n)) `MEMORY.FILL`_admininstr]), [CONST_admininstr(I32_numtype, i) (val : val <: admininstr) STORE_admininstr(I32_numtype, ?(`%`_sz(8)), $memarg0) CONST_admininstr(I32_numtype, $iadd_(32, i, `%`_iN(1))) (val : val <: admininstr) CONST_admininstr(I32_numtype, `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `MEMORY.FILL`_admininstr])
    -- otherwise

  ;; ../specification/wasm-2.0/8-reduction.spectec:611.1-613.71
  rule `memory.copy-trap`{z : state, j : num_(I32_numtype), i : num_(I32_numtype), n : n}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, `%`_num_(n)) `MEMORY.COPY`_admininstr]), [TRAP_admininstr])
    -- if (((i!`%`_num_.0 + n) > |$mem(z, `%`_memidx(0)).BYTES_meminst|) \/ ((j!`%`_num_.0 + n) > |$mem(z, `%`_memidx(0)).BYTES_meminst|))

  ;; ../specification/wasm-2.0/8-reduction.spectec:615.1-618.14
  rule `memory.copy-zero`{z : state, j : num_(I32_numtype), i : num_(I32_numtype), n : n}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, `%`_num_(n)) `MEMORY.COPY`_admininstr]), [])
    -- otherwise
    -- if (n = 0)

  ;; ../specification/wasm-2.0/8-reduction.spectec:620.1-625.15
  rule `memory.copy-le`{z : state, j : num_(I32_numtype), i : num_(I32_numtype), n : n}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, `%`_num_(n)) `MEMORY.COPY`_admininstr]), [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) LOAD_admininstr(I32_numtype, ?(`%_%`_loadop_(`%`_sz(8), U_sx)), $memarg0) STORE_admininstr(I32_numtype, ?(`%`_sz(8)), $memarg0) CONST_admininstr(I32_numtype, $iadd_(32, j, `%`_iN(1))) CONST_admininstr(I32_numtype, $iadd_(32, i, `%`_iN(1))) CONST_admininstr(I32_numtype, `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `MEMORY.COPY`_admininstr])
    -- otherwise
    -- if (j!`%`_num_.0 <= i!`%`_num_.0)

  ;; ../specification/wasm-2.0/8-reduction.spectec:627.1-631.15
  rule `memory.copy-gt`{z : state, j : num_(I32_numtype), i : num_(I32_numtype), n : n}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, `%`_num_(n)) `MEMORY.COPY`_admininstr]), [CONST_admininstr(I32_numtype, `%`_num_(((((j!`%`_num_.0 + n) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) CONST_admininstr(I32_numtype, `%`_num_(((((i!`%`_num_.0 + n) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) LOAD_admininstr(I32_numtype, ?(`%_%`_loadop_(`%`_sz(8), U_sx)), $memarg0) STORE_admininstr(I32_numtype, ?(`%`_sz(8)), $memarg0) CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `MEMORY.COPY`_admininstr])
    -- otherwise

  ;; ../specification/wasm-2.0/8-reduction.spectec:634.1-636.72
  rule `memory.init-trap`{z : state, j : num_(I32_numtype), i : num_(I32_numtype), n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, `%`_num_(n)) `MEMORY.INIT`_admininstr(x)]), [TRAP_admininstr])
    -- if (((i!`%`_num_.0 + n) > |$data(z, x).BYTES_datainst|) \/ ((j!`%`_num_.0 + n) > |$mem(z, `%`_memidx(0)).BYTES_meminst|))

  ;; ../specification/wasm-2.0/8-reduction.spectec:638.1-641.14
  rule `memory.init-zero`{z : state, j : num_(I32_numtype), i : num_(I32_numtype), n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, `%`_num_(n)) `MEMORY.INIT`_admininstr(x)]), [])
    -- otherwise
    -- if (n = 0)

  ;; ../specification/wasm-2.0/8-reduction.spectec:643.1-647.15
  rule `memory.init-succ`{z : state, j : num_(I32_numtype), i : num_(I32_numtype), n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, `%`_num_(n)) `MEMORY.INIT`_admininstr(x)]), [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, `%`_num_($data(z, x).BYTES_datainst[i!`%`_num_.0]!`%`_byte.0)) STORE_admininstr(I32_numtype, ?(`%`_sz(8)), $memarg0) CONST_admininstr(I32_numtype, $iadd_(32, j, `%`_iN(1))) CONST_admininstr(I32_numtype, $iadd_(32, i, `%`_iN(1))) CONST_admininstr(I32_numtype, `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `MEMORY.INIT`_admininstr(x)])
    -- otherwise

;; ../specification/wasm-2.0/8-reduction.spectec:5.1-5.109
rec {

;; ../specification/wasm-2.0/8-reduction.spectec:5.1-5.109
relation Step: `%~>%`(config, config)
  ;; ../specification/wasm-2.0/8-reduction.spectec:10.1-12.44
  rule pure{z : state, `admininstr*` : admininstr*, `admininstr'*` : admininstr*}:
    `%~>%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}), `%;%`_config(z, admininstr'*{admininstr' <- `admininstr'*`}))
    -- Step_pure: `%~>%`(admininstr*{admininstr <- `admininstr*`}, admininstr'*{admininstr' <- `admininstr'*`})

  ;; ../specification/wasm-2.0/8-reduction.spectec:14.1-16.47
  rule read{z : state, `admininstr*` : admininstr*, `admininstr'*` : admininstr*}:
    `%~>%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}), `%;%`_config(z, admininstr'*{admininstr' <- `admininstr'*`}))
    -- Step_read: `%~>%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}), admininstr'*{admininstr' <- `admininstr'*`})

  ;; ../specification/wasm-2.0/8-reduction.spectec:163.1-165.46
  rule `ctxt-label`{z : state, n : n, `instr_0*` : instr*, `admininstr*` : admininstr*, z' : state, `admininstr'*` : admininstr*}:
    `%~>%`(`%;%`_config(z, [`LABEL_%{%}%`_admininstr(n, instr_0*{instr_0 <- `instr_0*`}, admininstr*{admininstr <- `admininstr*`})]), `%;%`_config(z', [`LABEL_%{%}%`_admininstr(n, instr_0*{instr_0 <- `instr_0*`}, admininstr'*{admininstr' <- `admininstr'*`})]))
    -- Step: `%~>%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}), `%;%`_config(z', admininstr'*{admininstr' <- `admininstr'*`}))

  ;; ../specification/wasm-2.0/8-reduction.spectec:167.1-169.55
  rule `ctxt-frame`{s : store, f : frame, n : n, f' : frame, `admininstr*` : admininstr*, s' : store, f'' : frame, `admininstr'*` : admininstr*}:
    `%~>%`(`%;%`_config(`%;%`_state(s, f), [`FRAME_%{%}%`_admininstr(n, f', admininstr*{admininstr <- `admininstr*`})]), `%;%`_config(`%;%`_state(s', f), [`FRAME_%{%}%`_admininstr(n, f'', admininstr'*{admininstr' <- `admininstr'*`})]))
    -- Step: `%~>%`(`%;%`_config(`%;%`_state(s, f'), admininstr*{admininstr <- `admininstr*`}), `%;%`_config(`%;%`_state(s', f''), admininstr'*{admininstr' <- `admininstr'*`}))

  ;; ../specification/wasm-2.0/8-reduction.spectec:171.1-174.46
  rule `ctxt-instrs`{z : state, `val*` : val*, `admininstr*` : admininstr*, `admininstr_1*` : admininstr*, z' : state, `admininstr'*` : admininstr*}:
    `%~>%`(`%;%`_config(z, (val : val <: admininstr)*{val <- `val*`} ++ admininstr*{admininstr <- `admininstr*`} ++ admininstr_1*{admininstr_1 <- `admininstr_1*`}), `%;%`_config(z', (val : val <: admininstr)*{val <- `val*`} ++ admininstr'*{admininstr' <- `admininstr'*`} ++ admininstr_1*{admininstr_1 <- `admininstr_1*`}))
    -- Step: `%~>%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}), `%;%`_config(z', admininstr'*{admininstr' <- `admininstr'*`}))
    -- if ((val*{val <- `val*`} =/= []) \/ (admininstr_1*{admininstr_1 <- `admininstr_1*`} =/= []))

  ;; ../specification/wasm-2.0/8-reduction.spectec:367.1-368.56
  rule `local.set`{z : state, val : val, x : idx}:
    `%~>%`(`%;%`_config(z, [(val : val <: admininstr) `LOCAL.SET`_admininstr(x)]), `%;%`_config($with_local(z, x, val), []))

  ;; ../specification/wasm-2.0/8-reduction.spectec:379.1-380.58
  rule `global.set`{z : state, val : val, x : idx}:
    `%~>%`(`%;%`_config(z, [(val : val <: admininstr) `GLOBAL.SET`_admininstr(x)]), `%;%`_config($with_global(z, x, val), []))

  ;; ../specification/wasm-2.0/8-reduction.spectec:393.1-395.33
  rule `table.set-trap`{z : state, i : num_(I32_numtype), ref : ref, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) (ref : ref <: admininstr) `TABLE.SET`_admininstr(x)]), `%;%`_config(z, [TRAP_admininstr]))
    -- if (i!`%`_num_.0 >= |$table(z, x).REFS_tableinst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:397.1-399.32
  rule `table.set-val`{z : state, i : num_(I32_numtype), ref : ref, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) (ref : ref <: admininstr) `TABLE.SET`_admininstr(x)]), `%;%`_config($with_table(z, x, i!`%`_num_.0, ref), []))
    -- if (i!`%`_num_.0 < |$table(z, x).REFS_tableinst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:407.1-409.46
  rule `table.grow-succeed`{z : state, ref : ref, n : n, x : idx, ti : tableinst}:
    `%~>%`(`%;%`_config(z, [(ref : ref <: admininstr) CONST_admininstr(I32_numtype, `%`_num_(n)) `TABLE.GROW`_admininstr(x)]), `%;%`_config($with_tableinst(z, x, ti), [CONST_admininstr(I32_numtype, `%`_num_(|$table(z, x).REFS_tableinst|))]))
    -- if ($growtable($table(z, x), n, ref) = ti)

  ;; ../specification/wasm-2.0/8-reduction.spectec:411.1-412.82
  rule `table.grow-fail`{z : state, ref : ref, n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [(ref : ref <: admininstr) CONST_admininstr(I32_numtype, `%`_num_(n)) `TABLE.GROW`_admininstr(x)]), `%;%`_config(z, [CONST_admininstr(I32_numtype, `%`_num_($inv_signed_(32, - (1 : nat <:> int))))]))

  ;; ../specification/wasm-2.0/8-reduction.spectec:470.1-471.51
  rule `elem.drop`{z : state, x : idx}:
    `%~>%`(`%;%`_config(z, [`ELEM.DROP`_admininstr(x)]), `%;%`_config($with_elem(z, x, []), []))

  ;; ../specification/wasm-2.0/8-reduction.spectec:546.1-548.60
  rule `store-num-trap`{z : state, i : num_(I32_numtype), nt : numtype, c : num_(nt), ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) CONST_admininstr(nt, c) STORE_admininstr(nt, ?(), ao)]), `%;%`_config(z, [TRAP_admininstr]))
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) + ((($size((nt : numtype <: valtype)) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, `%`_memidx(0)).BYTES_meminst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:550.1-552.29
  rule `store-num-val`{z : state, i : num_(I32_numtype), nt : numtype, c : num_(nt), ao : memarg, `b*` : byte*}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) CONST_admininstr(nt, c) STORE_admininstr(nt, ?(), ao)]), `%;%`_config($with_mem(z, `%`_memidx(0), (i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0), ((($size((nt : numtype <: valtype)) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b*{b <- `b*`}), []))
    -- if (b*{b <- `b*`} = $nbytes_(nt, c))

  ;; ../specification/wasm-2.0/8-reduction.spectec:554.1-556.52
  rule `store-pack-trap`{z : state, i : num_(I32_numtype), Inn : Inn, c : num_((Inn : Inn <: numtype)), n : n, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) CONST_admininstr((Inn : Inn <: numtype), c) STORE_admininstr((Inn : Inn <: numtype), ?(`%`_sz(n)), ao)]), `%;%`_config(z, [TRAP_admininstr]))
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) + (((n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, `%`_memidx(0)).BYTES_meminst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:558.1-560.52
  rule `store-pack-val`{z : state, i : num_(I32_numtype), Inn : Inn, c : num_((Inn : Inn <: numtype)), n : n, ao : memarg, `b*` : byte*}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) CONST_admininstr((Inn : Inn <: numtype), c) STORE_admininstr((Inn : Inn <: numtype), ?(`%`_sz(n)), ao)]), `%;%`_config($with_mem(z, `%`_memidx(0), (i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0), (((n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b*{b <- `b*`}), []))
    -- if (b*{b <- `b*`} = $ibytes_(n, $wrap__($size((Inn : Inn <: valtype)), n, c)))

  ;; ../specification/wasm-2.0/8-reduction.spectec:562.1-564.62
  rule `vstore-oob`{z : state, i : num_(I32_numtype), c : vec_(V128_Vnn), ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) VCONST_admininstr(V128_vectype, c) VSTORE_admininstr(V128_vectype, ao)]), `%;%`_config(z, [TRAP_admininstr]))
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) + ((($size(V128_valtype) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, `%`_memidx(0)).BYTES_meminst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:566.1-568.31
  rule `vstore-val`{z : state, i : num_(I32_numtype), c : vec_(V128_Vnn), ao : memarg, `b*` : byte*}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) VCONST_admininstr(V128_vectype, c) VSTORE_admininstr(V128_vectype, ao)]), `%;%`_config($with_mem(z, `%`_memidx(0), (i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0), ((($size(V128_valtype) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b*{b <- `b*`}), []))
    -- if (b*{b <- `b*`} = $vbytes_(V128_vectype, c))

  ;; ../specification/wasm-2.0/8-reduction.spectec:571.1-573.50
  rule `vstore_lane-oob`{z : state, i : num_(I32_numtype), c : vec_(V128_Vnn), N : N, ao : memarg, j : laneidx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) VCONST_admininstr(V128_vectype, c) VSTORE_LANE_admininstr(V128_vectype, `%`_sz(N), ao, j)]), `%;%`_config(z, [TRAP_admininstr]))
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0) + N) > |$mem(z, `%`_memidx(0)).BYTES_meminst|)

  ;; ../specification/wasm-2.0/8-reduction.spectec:575.1-579.49
  rule `vstore_lane-val`{z : state, i : num_(I32_numtype), c : vec_(V128_Vnn), N : N, ao : memarg, j : laneidx, `b*` : byte*, Jnn : Jnn, M : M}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, i) VCONST_admininstr(V128_vectype, c) VSTORE_LANE_admininstr(V128_vectype, `%`_sz(N), ao, j)]), `%;%`_config($with_mem(z, `%`_memidx(0), (i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u32.0), (((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b*{b <- `b*`}), []))
    -- if (N = $jsize(Jnn))
    -- if ((M : nat <:> rat) = ((128 : nat <:> rat) / (N : nat <:> rat)))
    -- if (b*{b <- `b*`} = $ibytes_(N, `%`_iN($lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c)[j!`%`_laneidx.0]!`%`_lane_.0)))

  ;; ../specification/wasm-2.0/8-reduction.spectec:587.1-589.40
  rule `memory.grow-succeed`{z : state, n : n, mi : meminst}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, `%`_num_(n)) `MEMORY.GROW`_admininstr]), `%;%`_config($with_meminst(z, `%`_memidx(0), mi), [CONST_admininstr(I32_numtype, `%`_num_((((|$mem(z, `%`_memidx(0)).BYTES_meminst| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) : rat <:> nat)))]))
    -- if ($growmemory($mem(z, `%`_memidx(0)), n) = mi)

  ;; ../specification/wasm-2.0/8-reduction.spectec:591.1-592.77
  rule `memory.grow-fail`{z : state, n : n}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_numtype, `%`_num_(n)) `MEMORY.GROW`_admininstr]), `%;%`_config(z, [CONST_admininstr(I32_numtype, `%`_num_($inv_signed_(32, - (1 : nat <:> int))))]))

  ;; ../specification/wasm-2.0/8-reduction.spectec:650.1-651.51
  rule `data.drop`{z : state, x : idx}:
    `%~>%`(`%;%`_config(z, [`DATA.DROP`_admininstr(x)]), `%;%`_config($with_data(z, x, []), []))
}

;; ../specification/wasm-2.0/8-reduction.spectec:8.1-8.77
rec {

;; ../specification/wasm-2.0/8-reduction.spectec:8.1-8.77
relation Steps: `%~>*%`(config, config)
  ;; ../specification/wasm-2.0/8-reduction.spectec:18.1-19.36
  rule refl{z : state, `admininstr*` : admininstr*}:
    `%~>*%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}), `%;%`_config(z, admininstr*{admininstr <- `admininstr*`}))

  ;; ../specification/wasm-2.0/8-reduction.spectec:21.1-24.54
  rule trans{z : state, `admininstr*` : admininstr*, z'' : state, `admininstr''*` : admininstr*, z' : state, `admininstr'*` : admininstr*}:
    `%~>*%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}), `%;%`_config(z'', admininstr''*{admininstr'' <- `admininstr''*`}))
    -- Step: `%~>%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}), `%;%`_config(z', admininstr'*{admininstr' <- `admininstr'*`}))
    -- Steps: `%~>*%`(`%;%`_config(z', admininstr'*{admininstr' <- `admininstr'*`}), `%;%`_config(z'', admininstr''*{admininstr'' <- `admininstr''*`}))
}

;; ../specification/wasm-2.0/8-reduction.spectec:29.1-29.83
relation Eval_expr: `%;%~>*%;%`(state, expr, state, val*)
  ;; ../specification/wasm-2.0/8-reduction.spectec:31.1-33.37
  rule _{z : state, `instr*` : instr*, z' : state, `val*` : val*}:
    `%;%~>*%;%`(z, instr*{instr <- `instr*`}, z', val*{val <- `val*`})
    -- Steps: `%~>*%`(`%;%`_config(z, (instr : instr <: admininstr)*{instr <- `instr*`}), `%;%`_config(z', (val : val <: admininstr)*{val <- `val*`}))

;; ../specification/wasm-2.0/9-module.spectec:5.1-5.36
rec {

;; ../specification/wasm-2.0/9-module.spectec:5.1-5.36
def $funcs(externaddr*) : funcaddr*
  ;; ../specification/wasm-2.0/9-module.spectec:6.1-6.22
  def $funcs([]) = []
  ;; ../specification/wasm-2.0/9-module.spectec:7.1-7.61
  def $funcs{fa : funcaddr, `externaddr'*` : externaddr*}([FUNC_externaddr(fa)] ++ externaddr'*{externaddr' <- `externaddr'*`}) = [fa] ++ $funcs(externaddr'*{externaddr' <- `externaddr'*`})
  ;; ../specification/wasm-2.0/9-module.spectec:8.1-9.15
  def $funcs{externaddr : externaddr, `externaddr'*` : externaddr*}([externaddr] ++ externaddr'*{externaddr' <- `externaddr'*`}) = $funcs(externaddr'*{externaddr' <- `externaddr'*`})
    -- otherwise
}

;; ../specification/wasm-2.0/9-module.spectec:11.1-11.40
rec {

;; ../specification/wasm-2.0/9-module.spectec:11.1-11.40
def $globals(externaddr*) : globaladdr*
  ;; ../specification/wasm-2.0/9-module.spectec:12.1-12.24
  def $globals([]) = []
  ;; ../specification/wasm-2.0/9-module.spectec:13.1-13.67
  def $globals{ga : globaladdr, `externaddr'*` : externaddr*}([GLOBAL_externaddr(ga)] ++ externaddr'*{externaddr' <- `externaddr'*`}) = [ga] ++ $globals(externaddr'*{externaddr' <- `externaddr'*`})
  ;; ../specification/wasm-2.0/9-module.spectec:14.1-15.15
  def $globals{externaddr : externaddr, `externaddr'*` : externaddr*}([externaddr] ++ externaddr'*{externaddr' <- `externaddr'*`}) = $globals(externaddr'*{externaddr' <- `externaddr'*`})
    -- otherwise
}

;; ../specification/wasm-2.0/9-module.spectec:17.1-17.38
rec {

;; ../specification/wasm-2.0/9-module.spectec:17.1-17.38
def $tables(externaddr*) : tableaddr*
  ;; ../specification/wasm-2.0/9-module.spectec:18.1-18.23
  def $tables([]) = []
  ;; ../specification/wasm-2.0/9-module.spectec:19.1-19.64
  def $tables{ta : tableaddr, `externaddr'*` : externaddr*}([TABLE_externaddr(ta)] ++ externaddr'*{externaddr' <- `externaddr'*`}) = [ta] ++ $tables(externaddr'*{externaddr' <- `externaddr'*`})
  ;; ../specification/wasm-2.0/9-module.spectec:20.1-21.15
  def $tables{externaddr : externaddr, `externaddr'*` : externaddr*}([externaddr] ++ externaddr'*{externaddr' <- `externaddr'*`}) = $tables(externaddr'*{externaddr' <- `externaddr'*`})
    -- otherwise
}

;; ../specification/wasm-2.0/9-module.spectec:23.1-23.34
rec {

;; ../specification/wasm-2.0/9-module.spectec:23.1-23.34
def $mems(externaddr*) : memaddr*
  ;; ../specification/wasm-2.0/9-module.spectec:24.1-24.21
  def $mems([]) = []
  ;; ../specification/wasm-2.0/9-module.spectec:25.1-25.58
  def $mems{ma : memaddr, `externaddr'*` : externaddr*}([MEM_externaddr(ma)] ++ externaddr'*{externaddr' <- `externaddr'*`}) = [ma] ++ $mems(externaddr'*{externaddr' <- `externaddr'*`})
  ;; ../specification/wasm-2.0/9-module.spectec:26.1-27.15
  def $mems{externaddr : externaddr, `externaddr'*` : externaddr*}([externaddr] ++ externaddr'*{externaddr' <- `externaddr'*`}) = $mems(externaddr'*{externaddr' <- `externaddr'*`})
    -- otherwise
}

;; ../specification/wasm-2.0/9-module.spectec:36.1-36.60
def $allocfunc(store : store, moduleinst : moduleinst, func : func) : (store, funcaddr)
  ;; ../specification/wasm-2.0/9-module.spectec:37.1-39.34
  def $allocfunc{s : store, moduleinst : moduleinst, func : func, fi : funcinst, x : idx, `local*` : local*, expr : expr}(s, moduleinst, func) = (s[FUNCS_store =++ [fi]], |s.FUNCS_store|)
    -- if (fi = {TYPE moduleinst.TYPES_moduleinst[x!`%`_idx.0], MODULE moduleinst, CODE func})
    -- if (func = FUNC_func(x, local*{local <- `local*`}, expr))

;; ../specification/wasm-2.0/9-module.spectec:41.1-41.63
rec {

;; ../specification/wasm-2.0/9-module.spectec:41.1-41.63
def $allocfuncs(store : store, moduleinst : moduleinst, func*) : (store, funcaddr*)
  ;; ../specification/wasm-2.0/9-module.spectec:42.1-42.47
  def $allocfuncs{s : store, moduleinst : moduleinst}(s, moduleinst, []) = (s, [])
  ;; ../specification/wasm-2.0/9-module.spectec:43.1-45.59
  def $allocfuncs{s : store, moduleinst : moduleinst, func : func, `func'*` : func*, s_2 : store, fa : funcaddr, `fa'*` : funcaddr*, s_1 : store}(s, moduleinst, [func] ++ func'*{func' <- `func'*`}) = (s_2, [fa] ++ fa'*{fa' <- `fa'*`})
    -- if ((s_1, fa) = $allocfunc(s, moduleinst, func))
    -- if ((s_2, fa'*{fa' <- `fa'*`}) = $allocfuncs(s_1, moduleinst, func'*{func' <- `func'*`}))
}

;; ../specification/wasm-2.0/9-module.spectec:47.1-47.63
def $allocglobal(store : store, globaltype : globaltype, val : val) : (store, globaladdr)
  ;; ../specification/wasm-2.0/9-module.spectec:48.1-49.44
  def $allocglobal{s : store, globaltype : globaltype, val : val, gi : globalinst}(s, globaltype, val) = (s[GLOBALS_store =++ [gi]], |s.GLOBALS_store|)
    -- if (gi = {TYPE globaltype, VALUE val})

;; ../specification/wasm-2.0/9-module.spectec:51.1-51.67
rec {

;; ../specification/wasm-2.0/9-module.spectec:51.1-51.67
def $allocglobals(store : store, globaltype*, val*) : (store, globaladdr*)
  ;; ../specification/wasm-2.0/9-module.spectec:52.1-52.42
  def $allocglobals{s : store}(s, [], []) = (s, [])
  ;; ../specification/wasm-2.0/9-module.spectec:53.1-55.62
  def $allocglobals{s : store, globaltype : globaltype, `globaltype'*` : globaltype*, val : val, `val'*` : val*, s_2 : store, ga : globaladdr, `ga'*` : globaladdr*, s_1 : store}(s, [globaltype] ++ globaltype'*{globaltype' <- `globaltype'*`}, [val] ++ val'*{val' <- `val'*`}) = (s_2, [ga] ++ ga'*{ga' <- `ga'*`})
    -- if ((s_1, ga) = $allocglobal(s, globaltype, val))
    -- if ((s_2, ga'*{ga' <- `ga'*`}) = $allocglobals(s_1, globaltype'*{globaltype' <- `globaltype'*`}, val'*{val' <- `val'*`}))
}

;; ../specification/wasm-2.0/9-module.spectec:57.1-57.55
def $alloctable(store : store, tabletype : tabletype) : (store, tableaddr)
  ;; ../specification/wasm-2.0/9-module.spectec:58.1-59.60
  def $alloctable{s : store, i : u32, `j?` : u32?, rt : reftype, ti : tableinst}(s, `%%`_tabletype(`[%..%]`_limits(i, j?{j <- `j?`}), rt)) = (s[TABLES_store =++ [ti]], |s.TABLES_store|)
    -- if (ti = {TYPE `%%`_tabletype(`[%..%]`_limits(i, j?{j <- `j?`}), rt), REFS `REF.NULL`_ref(rt)^i!`%`_u32.0{}})

;; ../specification/wasm-2.0/9-module.spectec:61.1-61.58
rec {

;; ../specification/wasm-2.0/9-module.spectec:61.1-61.58
def $alloctables(store : store, tabletype*) : (store, tableaddr*)
  ;; ../specification/wasm-2.0/9-module.spectec:62.1-62.36
  def $alloctables{s : store}(s, []) = (s, [])
  ;; ../specification/wasm-2.0/9-module.spectec:63.1-65.53
  def $alloctables{s : store, tabletype : tabletype, `tabletype'*` : tabletype*, s_2 : store, ta : tableaddr, `ta'*` : tableaddr*, s_1 : store}(s, [tabletype] ++ tabletype'*{tabletype' <- `tabletype'*`}) = (s_2, [ta] ++ ta'*{ta' <- `ta'*`})
    -- if ((s_1, ta) = $alloctable(s, tabletype))
    -- if ((s_2, ta'*{ta' <- `ta'*`}) = $alloctables(s_1, tabletype'*{tabletype' <- `tabletype'*`}))
}

;; ../specification/wasm-2.0/9-module.spectec:67.1-67.49
def $allocmem(store : store, memtype : memtype) : (store, memaddr)
  ;; ../specification/wasm-2.0/9-module.spectec:68.1-69.70
  def $allocmem{s : store, i : u32, `j?` : u32?, mi : meminst}(s, `%PAGE`_memtype(`[%..%]`_limits(i, j?{j <- `j?`}))) = (s[MEMS_store =++ [mi]], |s.MEMS_store|)
    -- if (mi = {TYPE `%PAGE`_memtype(`[%..%]`_limits(i, j?{j <- `j?`})), BYTES `%`_byte(0)^(i!`%`_u32.0 * (64 * $Ki)){}})

;; ../specification/wasm-2.0/9-module.spectec:71.1-71.52
rec {

;; ../specification/wasm-2.0/9-module.spectec:71.1-71.52
def $allocmems(store : store, memtype*) : (store, memaddr*)
  ;; ../specification/wasm-2.0/9-module.spectec:72.1-72.34
  def $allocmems{s : store}(s, []) = (s, [])
  ;; ../specification/wasm-2.0/9-module.spectec:73.1-75.49
  def $allocmems{s : store, memtype : memtype, `memtype'*` : memtype*, s_2 : store, ma : memaddr, `ma'*` : memaddr*, s_1 : store}(s, [memtype] ++ memtype'*{memtype' <- `memtype'*`}) = (s_2, [ma] ++ ma'*{ma' <- `ma'*`})
    -- if ((s_1, ma) = $allocmem(s, memtype))
    -- if ((s_2, ma'*{ma' <- `ma'*`}) = $allocmems(s_1, memtype'*{memtype' <- `memtype'*`}))
}

;; ../specification/wasm-2.0/9-module.spectec:77.1-77.57
def $allocelem(store : store, reftype : reftype, ref*) : (store, elemaddr)
  ;; ../specification/wasm-2.0/9-module.spectec:78.1-79.36
  def $allocelem{s : store, rt : reftype, `ref*` : ref*, ei : eleminst}(s, rt, ref*{ref <- `ref*`}) = (s[ELEMS_store =++ [ei]], |s.ELEMS_store|)
    -- if (ei = {TYPE rt, REFS ref*{ref <- `ref*`}})

;; ../specification/wasm-2.0/9-module.spectec:81.1-81.63
rec {

;; ../specification/wasm-2.0/9-module.spectec:81.1-81.63
def $allocelems(store : store, reftype*, ref**) : (store, elemaddr*)
  ;; ../specification/wasm-2.0/9-module.spectec:82.1-82.40
  def $allocelems{s : store}(s, [], []) = (s, [])
  ;; ../specification/wasm-2.0/9-module.spectec:83.1-85.55
  def $allocelems{s : store, rt : reftype, `rt'*` : reftype*, `ref*` : ref*, `ref'**` : ref**, s_2 : store, ea : elemaddr, `ea'*` : elemaddr*, s_1 : store}(s, [rt] ++ rt'*{rt' <- `rt'*`}, [ref*{ref <- `ref*`}] ++ ref'*{ref' <- `ref'*`}*{`ref'*` <- `ref'**`}) = (s_2, [ea] ++ ea'*{ea' <- `ea'*`})
    -- if ((s_1, ea) = $allocelem(s, rt, ref*{ref <- `ref*`}))
    -- if ((s_2, ea'*{ea' <- `ea'*`}) = $allocelems(s_1, rt'*{rt' <- `rt'*`}, ref'*{ref' <- `ref'*`}*{`ref'*` <- `ref'**`}))
}

;; ../specification/wasm-2.0/9-module.spectec:87.1-87.49
def $allocdata(store : store, byte*) : (store, dataaddr)
  ;; ../specification/wasm-2.0/9-module.spectec:88.1-89.29
  def $allocdata{s : store, `byte*` : byte*, di : datainst}(s, byte*{byte <- `byte*`}) = (s[DATAS_store =++ [di]], |s.DATAS_store|)
    -- if (di = {BYTES byte*{byte <- `byte*`}})

;; ../specification/wasm-2.0/9-module.spectec:91.1-91.54
rec {

;; ../specification/wasm-2.0/9-module.spectec:91.1-91.54
def $allocdatas(store : store, byte**) : (store, dataaddr*)
  ;; ../specification/wasm-2.0/9-module.spectec:92.1-92.35
  def $allocdatas{s : store}(s, []) = (s, [])
  ;; ../specification/wasm-2.0/9-module.spectec:93.1-95.50
  def $allocdatas{s : store, `byte*` : byte*, `byte'**` : byte**, s_2 : store, da : dataaddr, `da'*` : dataaddr*, s_1 : store}(s, [byte*{byte <- `byte*`}] ++ byte'*{byte' <- `byte'*`}*{`byte'*` <- `byte'**`}) = (s_2, [da] ++ da'*{da' <- `da'*`})
    -- if ((s_1, da) = $allocdata(s, byte*{byte <- `byte*`}))
    -- if ((s_2, da'*{da' <- `da'*`}) = $allocdatas(s_1, byte'*{byte' <- `byte'*`}*{`byte'*` <- `byte'**`}))
}

;; ../specification/wasm-2.0/9-module.spectec:100.1-100.83
def $instexport(funcaddr*, globaladdr*, tableaddr*, memaddr*, export : export) : exportinst
  ;; ../specification/wasm-2.0/9-module.spectec:101.1-101.94
  def $instexport{`fa*` : funcaddr*, `ga*` : globaladdr*, `ta*` : tableaddr*, `ma*` : memaddr*, name : name, x : idx}(fa*{fa <- `fa*`}, ga*{ga <- `ga*`}, ta*{ta <- `ta*`}, ma*{ma <- `ma*`}, EXPORT_export(name, FUNC_externidx(x))) = {NAME name, ADDR FUNC_externaddr(fa*{fa <- `fa*`}[x!`%`_idx.0])}
  ;; ../specification/wasm-2.0/9-module.spectec:102.1-102.98
  def $instexport{`fa*` : funcaddr*, `ga*` : globaladdr*, `ta*` : tableaddr*, `ma*` : memaddr*, name : name, x : idx}(fa*{fa <- `fa*`}, ga*{ga <- `ga*`}, ta*{ta <- `ta*`}, ma*{ma <- `ma*`}, EXPORT_export(name, GLOBAL_externidx(x))) = {NAME name, ADDR GLOBAL_externaddr(ga*{ga <- `ga*`}[x!`%`_idx.0])}
  ;; ../specification/wasm-2.0/9-module.spectec:103.1-103.96
  def $instexport{`fa*` : funcaddr*, `ga*` : globaladdr*, `ta*` : tableaddr*, `ma*` : memaddr*, name : name, x : idx}(fa*{fa <- `fa*`}, ga*{ga <- `ga*`}, ta*{ta <- `ta*`}, ma*{ma <- `ma*`}, EXPORT_export(name, TABLE_externidx(x))) = {NAME name, ADDR TABLE_externaddr(ta*{ta <- `ta*`}[x!`%`_idx.0])}
  ;; ../specification/wasm-2.0/9-module.spectec:104.1-104.92
  def $instexport{`fa*` : funcaddr*, `ga*` : globaladdr*, `ta*` : tableaddr*, `ma*` : memaddr*, name : name, x : idx}(fa*{fa <- `fa*`}, ga*{ga <- `ga*`}, ta*{ta <- `ta*`}, ma*{ma <- `ma*`}, EXPORT_export(name, MEM_externidx(x))) = {NAME name, ADDR MEM_externaddr(ma*{ma <- `ma*`}[x!`%`_idx.0])}

;; ../specification/wasm-2.0/9-module.spectec:107.1-107.82
def $allocmodule(store : store, module : module, externaddr*, val*, ref**) : (store, moduleinst)
  ;; ../specification/wasm-2.0/9-module.spectec:108.1-147.54
  def $allocmodule{s : store, module : module, `externaddr*` : externaddr*, `val*` : val*, `ref**` : ref**, s_6 : store, moduleinst : moduleinst, `ft*` : functype*, `import*` : import*, n_func : n, `func*` : func*, n_global : n, `expr_1*` : expr*, `globaltype*` : globaltype*, n_table : n, `tabletype*` : tabletype*, n_mem : n, `memtype*` : memtype*, n_elem : n, `elemmode*` : elemmode*, `expr_2**` : expr**, `rt*` : reftype*, n_data : n, `byte**` : byte**, `datamode*` : datamode*, `start?` : start?, `export*` : export*, `fa_ex*` : funcaddr*, `ga_ex*` : globaladdr*, `ta_ex*` : tableaddr*, `ma_ex*` : memaddr*, `fa*` : funcaddr*, `ga*` : globaladdr*, `ta*` : tableaddr*, `ma*` : memaddr*, `ea*` : elemaddr*, `da*` : dataaddr*, `xi*` : exportinst*, s_1 : store, s_2 : store, s_3 : store, s_4 : store, s_5 : store}(s, module, externaddr*{externaddr <- `externaddr*`}, val*{val <- `val*`}, ref*{ref <- `ref*`}*{`ref*` <- `ref**`}) = (s_6, moduleinst)
    -- if (module = MODULE_module(TYPE_type(ft)*{ft <- `ft*`}, import*{import <- `import*`}, func^n_func{func <- `func*`}, GLOBAL_global(globaltype, expr_1)^n_global{expr_1 <- `expr_1*`, globaltype <- `globaltype*`}, TABLE_table(tabletype)^n_table{tabletype <- `tabletype*`}, MEMORY_mem(memtype)^n_mem{memtype <- `memtype*`}, ELEM_elem(rt, expr_2*{expr_2 <- `expr_2*`}, elemmode)^n_elem{elemmode <- `elemmode*`, `expr_2*` <- `expr_2**`, rt <- `rt*`}, DATA_data(byte*{byte <- `byte*`}, datamode)^n_data{`byte*` <- `byte**`, datamode <- `datamode*`}, start?{start <- `start?`}, export*{export <- `export*`}))
    -- if (fa_ex*{fa_ex <- `fa_ex*`} = $funcs(externaddr*{externaddr <- `externaddr*`}))
    -- if (ga_ex*{ga_ex <- `ga_ex*`} = $globals(externaddr*{externaddr <- `externaddr*`}))
    -- if (ta_ex*{ta_ex <- `ta_ex*`} = $tables(externaddr*{externaddr <- `externaddr*`}))
    -- if (ma_ex*{ma_ex <- `ma_ex*`} = $mems(externaddr*{externaddr <- `externaddr*`}))
    -- if (fa*{fa <- `fa*`} = (|s.FUNCS_store| + i_func)^(i_func<n_func){})
    -- if (ga*{ga <- `ga*`} = (|s.GLOBALS_store| + i_global)^(i_global<n_global){})
    -- if (ta*{ta <- `ta*`} = (|s.TABLES_store| + i_table)^(i_table<n_table){})
    -- if (ma*{ma <- `ma*`} = (|s.MEMS_store| + i_mem)^(i_mem<n_mem){})
    -- if (ea*{ea <- `ea*`} = (|s.ELEMS_store| + i_elem)^(i_elem<n_elem){})
    -- if (da*{da <- `da*`} = (|s.DATAS_store| + i_data)^(i_data<n_data){})
    -- if (xi*{xi <- `xi*`} = $instexport(fa_ex*{fa_ex <- `fa_ex*`} ++ fa*{fa <- `fa*`}, ga_ex*{ga_ex <- `ga_ex*`} ++ ga*{ga <- `ga*`}, ta_ex*{ta_ex <- `ta_ex*`} ++ ta*{ta <- `ta*`}, ma_ex*{ma_ex <- `ma_ex*`} ++ ma*{ma <- `ma*`}, export)*{export <- `export*`})
    -- if (moduleinst = {TYPES ft*{ft <- `ft*`}, FUNCS fa_ex*{fa_ex <- `fa_ex*`} ++ fa*{fa <- `fa*`}, GLOBALS ga_ex*{ga_ex <- `ga_ex*`} ++ ga*{ga <- `ga*`}, TABLES ta_ex*{ta_ex <- `ta_ex*`} ++ ta*{ta <- `ta*`}, MEMS ma_ex*{ma_ex <- `ma_ex*`} ++ ma*{ma <- `ma*`}, ELEMS ea*{ea <- `ea*`}, DATAS da*{da <- `da*`}, EXPORTS xi*{xi <- `xi*`}})
    -- if ((s_1, fa*{fa <- `fa*`}) = $allocfuncs(s, moduleinst, func^n_func{func <- `func*`}))
    -- if ((s_2, ga*{ga <- `ga*`}) = $allocglobals(s_1, globaltype^n_global{globaltype <- `globaltype*`}, val*{val <- `val*`}))
    -- if ((s_3, ta*{ta <- `ta*`}) = $alloctables(s_2, tabletype^n_table{tabletype <- `tabletype*`}))
    -- if ((s_4, ma*{ma <- `ma*`}) = $allocmems(s_3, memtype^n_mem{memtype <- `memtype*`}))
    -- if ((s_5, ea*{ea <- `ea*`}) = $allocelems(s_4, rt^n_elem{rt <- `rt*`}, ref*{ref <- `ref*`}*{`ref*` <- `ref**`}))
    -- if ((s_6, da*{da <- `da*`}) = $allocdatas(s_5, byte*{byte <- `byte*`}^n_data{`byte*` <- `byte**`}))

;; ../specification/wasm-2.0/9-module.spectec:154.1-154.33
def $runelem(elem : elem, idx : idx) : instr*
  ;; ../specification/wasm-2.0/9-module.spectec:155.1-155.52
  def $runelem{reftype : reftype, `expr*` : expr*, i : idx}(ELEM_elem(reftype, expr*{expr <- `expr*`}, PASSIVE_elemmode), i) = []
  ;; ../specification/wasm-2.0/9-module.spectec:156.1-156.62
  def $runelem{reftype : reftype, `expr*` : expr*, i : idx}(ELEM_elem(reftype, expr*{expr <- `expr*`}, DECLARE_elemmode), i) = [`ELEM.DROP`_instr(i)]
  ;; ../specification/wasm-2.0/9-module.spectec:157.1-159.20
  def $runelem{reftype : reftype, `expr*` : expr*, x : idx, `instr*` : instr*, i : idx, n : n}(ELEM_elem(reftype, expr*{expr <- `expr*`}, ACTIVE_elemmode(x, instr*{instr <- `instr*`})), i) = instr*{instr <- `instr*`} ++ [CONST_instr(I32_numtype, `%`_num_(0)) CONST_instr(I32_numtype, `%`_num_(n)) `TABLE.INIT`_instr(x, i) `ELEM.DROP`_instr(i)]
    -- if (n = |expr*{expr <- `expr*`}|)

;; ../specification/wasm-2.0/9-module.spectec:161.1-161.47
def $rundata(data : data, idx : idx) : instr*
  ;; ../specification/wasm-2.0/9-module.spectec:162.1-162.44
  def $rundata{`byte*` : byte*, i : idx}(DATA_data(byte*{byte <- `byte*`}, PASSIVE_datamode), i) = []
  ;; ../specification/wasm-2.0/9-module.spectec:163.1-165.20
  def $rundata{`byte*` : byte*, `instr*` : instr*, i : idx, n : n}(DATA_data(byte*{byte <- `byte*`}, ACTIVE_datamode(`%`_memidx(0), instr*{instr <- `instr*`})), i) = instr*{instr <- `instr*`} ++ [CONST_instr(I32_numtype, `%`_num_(0)) CONST_instr(I32_numtype, `%`_num_(n)) `MEMORY.INIT`_instr(i) `DATA.DROP`_instr(i)]
    -- if (n = |byte*{byte <- `byte*`}|)

;; ../specification/wasm-2.0/9-module.spectec:167.1-167.54
def $instantiate(store : store, module : module, externaddr*) : config
  ;; ../specification/wasm-2.0/9-module.spectec:168.1-189.66
  def $instantiate{s : store, module : module, `externaddr*` : externaddr*, s' : store, f : frame, `instr_E*` : instr*, `instr_D*` : instr*, `x?` : idx?, `type*` : type*, `import*` : import*, `func*` : func*, `global*` : global*, `table*` : table*, `mem*` : mem*, `elem*` : elem*, `data*` : data*, `start?` : start?, `export*` : export*, `functype*` : functype*, `expr_G*` : expr*, `globaltype*` : globaltype*, `elemmode*` : elemmode*, `expr_E**` : expr**, `reftype*` : reftype*, n_F : n, n_E : n, n_D : n, moduleinst_init : moduleinst, f_init : frame, z : state, `val*` : val*, `ref**` : ref**, moduleinst : moduleinst, i : nat, j : nat}(s, module, externaddr*{externaddr <- `externaddr*`}) = `%;%`_config(`%;%`_state(s', f), (instr_E : instr <: admininstr)*{instr_E <- `instr_E*`} ++ (instr_D : instr <: admininstr)*{instr_D <- `instr_D*`} ++ lift(CALL_admininstr(x)?{x <- `x?`}))
    -- if (module = MODULE_module(type*{type <- `type*`}, import*{import <- `import*`}, func*{func <- `func*`}, global*{global <- `global*`}, table*{table <- `table*`}, mem*{mem <- `mem*`}, elem*{elem <- `elem*`}, data*{data <- `data*`}, start?{start <- `start?`}, export*{export <- `export*`}))
    -- if (type*{type <- `type*`} = TYPE_type(functype)*{functype <- `functype*`})
    -- if (global*{global <- `global*`} = GLOBAL_global(globaltype, expr_G)*{expr_G <- `expr_G*`, globaltype <- `globaltype*`})
    -- if (elem*{elem <- `elem*`} = ELEM_elem(reftype, expr_E*{expr_E <- `expr_E*`}, elemmode)*{elemmode <- `elemmode*`, `expr_E*` <- `expr_E**`, reftype <- `reftype*`})
    -- if (start?{start <- `start?`} = START_start(x)?{x <- `x?`})
    -- if (n_F = |func*{func <- `func*`}|)
    -- if (n_E = |elem*{elem <- `elem*`}|)
    -- if (n_D = |data*{data <- `data*`}|)
    -- if (moduleinst_init = {TYPES functype*{functype <- `functype*`}, FUNCS $funcs(externaddr*{externaddr <- `externaddr*`}) ++ (|s.FUNCS_store| + i_F)^(i_F<n_F){}, GLOBALS $globals(externaddr*{externaddr <- `externaddr*`}), TABLES [], MEMS [], ELEMS [], DATAS [], EXPORTS []})
    -- if (f_init = {LOCALS [], MODULE moduleinst_init})
    -- if (z = `%;%`_state(s, f_init))
    -- (Eval_expr: `%;%~>*%;%`(z, expr_G, z, [val]))*{expr_G <- `expr_G*`, val <- `val*`}
    -- (Eval_expr: `%;%~>*%;%`(z, expr_E, z, [(ref : ref <: val)]))*{expr_E <- `expr_E*`, ref <- `ref*`}*{`expr_E*` <- `expr_E**`, `ref*` <- `ref**`}
    -- if ((s', moduleinst) = $allocmodule(s, module, externaddr*{externaddr <- `externaddr*`}, val*{val <- `val*`}, ref*{ref <- `ref*`}*{`ref*` <- `ref**`}))
    -- if (f = {LOCALS [], MODULE moduleinst})
    -- if (instr_E*{instr_E <- `instr_E*`} = $concat_(syntax instr, $runelem(elem*{elem <- `elem*`}[i], `%`_idx(i))^(i<n_E){}))
    -- if (instr_D*{instr_D <- `instr_D*`} = $concat_(syntax instr, $rundata(data*{data <- `data*`}[j], `%`_idx(j))^(j<n_D){}))

;; ../specification/wasm-2.0/9-module.spectec:196.1-196.44
def $invoke(store : store, funcaddr : funcaddr, val*) : config
  ;; ../specification/wasm-2.0/9-module.spectec:197.1-199.51
  def $invoke{s : store, fa : funcaddr, n : n, `val*` : val*, f : frame, `t_1*` : valtype*, `t_2*` : valtype*}(s, fa, val^n{val <- `val*`}) = `%;%`_config(`%;%`_state(s, f), (val : val <: admininstr)^n{val <- `val*`} ++ [CALL_ADDR_admininstr(fa)])
    -- if (f = {LOCALS [], MODULE {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], EXPORTS []}})
    -- if ($funcinst(`%;%`_state(s, f))[fa].TYPE_funcinst = `%->%`_functype(`%`_resulttype(t_1^n{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

;; ../specification/wasm-2.0/A-binary.spectec:849.1-849.43
syntax startopt = start*

;; ../specification/wasm-2.0/A-binary.spectec:884.1-884.29
syntax code = (local*, expr)

;; ../specification/wasm-2.0/A-binary.spectec:915.1-915.33
syntax nopt = u32*

;; ../specification/wasm-2.0/B-soundness.spectec:3.1-3.61
relation Context_ok: `|-%:OK`(context)
  ;; ../specification/wasm-2.0/B-soundness.spectec:5.1-23.34
  rule _{C : context, `ft*` : functype*, `ft_2*` : functype*, `gt*` : globaltype*, `tt*` : tabletype*, `mt*` : memtype*, `et*` : elemtype*, `ok*` : datatype*, `lct*` : valtype*, `rt*` : reftype*, `rt'?` : reftype?}:
    `|-%:OK`(C)
    -- if (C = {TYPES ft*{ft <- `ft*`}, FUNCS ft_2*{ft_2 <- `ft_2*`}, GLOBALS gt*{gt <- `gt*`}, TABLES tt*{tt <- `tt*`}, MEMS mt*{mt <- `mt*`}, ELEMS et*{et <- `et*`}, DATAS ok*{ok <- `ok*`}, LOCALS lct*{lct <- `lct*`}, LABELS [`%`_resulttype((rt : reftype <: valtype)*{rt <- `rt*`})], RETURN ?(`%`_resulttype(lift((rt' : reftype <: valtype)?{rt' <- `rt'?`})))})
    -- (Functype_ok: `|-%:OK`(ft))*{ft <- `ft*`}
    -- (Globaltype_ok: `|-%:OK`(gt))*{gt <- `gt*`}
    -- (Memtype_ok: `|-%:OK`(mt))*{mt <- `mt*`}
    -- (Tabletype_ok: `|-%:OK`(tt))*{tt <- `tt*`}
    -- (Functype_ok: `|-%:OK`(ft_2))*{ft_2 <- `ft_2*`}

;; ../specification/wasm-2.0/B-soundness.spectec:129.1-129.84
rec {

;; ../specification/wasm-2.0/B-soundness.spectec:129.1-129.84
relation Externaddr_ok: `%|-%:%`(store, externaddr, externtype)
  ;; ../specification/wasm-2.0/B-soundness.spectec:131.1-133.34
  rule global{s : store, a : addr, globalinst : globalinst}:
    `%|-%:%`(s, GLOBAL_externaddr(a), GLOBAL_externtype(globalinst.TYPE_globalinst))
    -- if (s.GLOBALS_store[a] = globalinst)

  ;; ../specification/wasm-2.0/B-soundness.spectec:135.1-137.28
  rule mem{s : store, a : addr, meminst : meminst}:
    `%|-%:%`(s, MEM_externaddr(a), MEM_externtype(meminst.TYPE_meminst))
    -- if (s.MEMS_store[a] = meminst)

  ;; ../specification/wasm-2.0/B-soundness.spectec:139.1-141.32
  rule table{s : store, a : addr, tableinst : tableinst}:
    `%|-%:%`(s, TABLE_externaddr(a), TABLE_externtype(tableinst.TYPE_tableinst))
    -- if (s.TABLES_store[a] = tableinst)

  ;; ../specification/wasm-2.0/B-soundness.spectec:143.1-145.30
  rule func{s : store, a : addr, funcinst : funcinst}:
    `%|-%:%`(s, FUNC_externaddr(a), FUNC_externtype(funcinst.TYPE_funcinst))
    -- if (s.FUNCS_store[a] = funcinst)

  ;; ../specification/wasm-2.0/B-soundness.spectec:147.1-150.34
  rule sub{s : store, externaddr : externaddr, xt : externtype, xt' : externtype}:
    `%|-%:%`(s, externaddr, xt)
    -- Externaddr_ok: `%|-%:%`(s, externaddr, xt')
    -- Externtype_sub: `|-%<:%`(xt', xt)
}

;; ../specification/wasm-2.0/B-soundness.spectec:27.1-27.40
relation Ref_ok: `%|-%:%`(store, ref, reftype)
  ;; ../specification/wasm-2.0/B-soundness.spectec:29.1-30.24
  rule null{s : store, rt : reftype}:
    `%|-%:%`(s, `REF.NULL`_ref(rt), rt)

  ;; ../specification/wasm-2.0/B-soundness.spectec:32.1-34.43
  rule func{s : store, a : addr, ext : functype}:
    `%|-%:%`(s, `REF.FUNC_ADDR`_ref(a), FUNCREF_reftype)
    -- Externaddr_ok: `%|-%:%`(s, FUNC_externaddr(a), FUNC_externtype(ext))

  ;; ../specification/wasm-2.0/B-soundness.spectec:36.1-37.35
  rule extern{s : store, a : addr}:
    `%|-%:%`(s, `REF.HOST_ADDR`_ref(a), EXTERNREF_reftype)

;; ../specification/wasm-2.0/B-soundness.spectec:41.1-41.40
relation Val_ok: `%|-%:%`(store, val, valtype)
  ;; ../specification/wasm-2.0/B-soundness.spectec:43.1-44.25
  rule numtype{s : store, nt : numtype, c_t : num_(nt)}:
    `%|-%:%`(s, CONST_val(nt, c_t), (nt : numtype <: valtype))

  ;; ../specification/wasm-2.0/B-soundness.spectec:46.1-47.26
  rule vectype{s : store, vt : vectype, c_t : vec_(vt)}:
    `%|-%:%`(s, VCONST_val(vt, c_t), (vt : vectype <: valtype))

  ;; ../specification/wasm-2.0/B-soundness.spectec:49.1-51.26
  rule reftype{s : store, r : ref, rt : reftype}:
    `%|-%:%`(s, (r : ref <: val), (rt : reftype <: valtype))
    -- Ref_ok: `%|-%:%`(s, r, rt)

;; ../specification/wasm-2.0/B-soundness.spectec:55.1-55.47
relation Result_ok: `%|-%:%`(store, result, valtype*)
  ;; ../specification/wasm-2.0/B-soundness.spectec:57.1-59.27
  rule result{s : store, `v*` : val*, `t*` : valtype*}:
    `%|-%:%`(s, _VALS_result(v*{v <- `v*`}), t*{t <- `t*`})
    -- (Val_ok: `%|-%:%`(s, v, t))*{t <- `t*`, v <- `v*`}

  ;; ../specification/wasm-2.0/B-soundness.spectec:61.1-62.17
  rule trap{s : store, `t*` : valtype*}:
    `%|-%:%`(s, TRAP_result, t*{t <- `t*`})

;; ../specification/wasm-2.0/B-soundness.spectec:66.1-66.31
syntax adminexpr = admininstr*

;; ../specification/wasm-2.0/B-soundness.spectec:158.1-158.51
relation Datainst_ok: `%|-%:%`(store, datainst, datatype)
  ;; ../specification/wasm-2.0/B-soundness.spectec:184.1-186.23
  rule _{s : store, `b*` : byte*}:
    `%|-%:%`(s, {BYTES b*{b <- `b*`}}, OK_datatype)
    -- if (|b*{b <- `b*`}| < (2 ^ 32))

;; ../specification/wasm-2.0/B-soundness.spectec:159.1-159.51
relation Eleminst_ok: `%|-%:%`(store, eleminst, elemtype)
  ;; ../specification/wasm-2.0/B-soundness.spectec:188.1-191.25
  rule _{s : store, rt : reftype, `ref*` : ref*}:
    `%|-%:%`(s, {TYPE rt, REFS ref*{ref <- `ref*`}}, rt)
    -- (Ref_ok: `%|-%:%`(s, ref, rt))*{ref <- `ref*`}
    -- if (|ref*{ref <- `ref*`}| < (2 ^ 32))

;; ../specification/wasm-2.0/B-soundness.spectec:160.1-160.49
relation Exportinst_ok: `%|-%:OK`(store, exportinst)
  ;; ../specification/wasm-2.0/B-soundness.spectec:193.1-195.33
  rule _{s : store, nm : name, xa : externaddr, xt : externtype}:
    `%|-%:OK`(s, {NAME nm, ADDR xa})
    -- Externaddr_ok: `%|-%:%`(s, xa, xt)

;; ../specification/wasm-2.0/B-soundness.spectec:200.1-200.54
relation Moduleinst_ok: `%|-%:%`(store, moduleinst, context)
  ;; ../specification/wasm-2.0/B-soundness.spectec:202.1-230.102
  rule _{s : store, `functype*` : functype*, `funcaddr*` : funcaddr*, `globaladdr*` : globaladdr*, `tableaddr*` : tableaddr*, `memaddr*` : memaddr*, `elemaddr*` : elemaddr*, `dataaddr*` : dataaddr*, `exportinst*` : exportinst*, `functype_F*` : functype*, `globaltype*` : globaltype*, `tabletype*` : tabletype*, `memtype*` : memtype*, `elemtype*` : elemtype*, `datatype*` : datatype*}:
    `%|-%:%`(s, {TYPES functype*{functype <- `functype*`}, FUNCS funcaddr*{funcaddr <- `funcaddr*`}, GLOBALS globaladdr*{globaladdr <- `globaladdr*`}, TABLES tableaddr*{tableaddr <- `tableaddr*`}, MEMS memaddr*{memaddr <- `memaddr*`}, ELEMS elemaddr*{elemaddr <- `elemaddr*`}, DATAS dataaddr*{dataaddr <- `dataaddr*`}, EXPORTS exportinst*{exportinst <- `exportinst*`}}, {TYPES functype*{functype <- `functype*`}, FUNCS functype_F*{functype_F <- `functype_F*`}, GLOBALS globaltype*{globaltype <- `globaltype*`}, TABLES tabletype*{tabletype <- `tabletype*`}, MEMS memtype*{memtype <- `memtype*`}, ELEMS elemtype*{elemtype <- `elemtype*`}, DATAS datatype*{datatype <- `datatype*`}, LOCALS [], LABELS [], RETURN ?()})
    -- (Functype_ok: `|-%:OK`(functype))*{functype <- `functype*`}
    -- (Externaddr_ok: `%|-%:%`(s, GLOBAL_externaddr(globaladdr), GLOBAL_externtype(globaltype)))*{globaladdr <- `globaladdr*`, globaltype <- `globaltype*`}
    -- (Externaddr_ok: `%|-%:%`(s, FUNC_externaddr(funcaddr), FUNC_externtype(functype_F)))*{funcaddr <- `funcaddr*`, functype_F <- `functype_F*`}
    -- (Externaddr_ok: `%|-%:%`(s, MEM_externaddr(memaddr), MEM_externtype(memtype)))*{memaddr <- `memaddr*`, memtype <- `memtype*`}
    -- (Externaddr_ok: `%|-%:%`(s, TABLE_externaddr(tableaddr), TABLE_externtype(tabletype)))*{tableaddr <- `tableaddr*`, tabletype <- `tabletype*`}
    -- (Exportinst_ok: `%|-%:OK`(s, exportinst))*{exportinst <- `exportinst*`}
    -- (Datainst_ok: `%|-%:%`(s, s.DATAS_store[dataaddr], datatype))*{dataaddr <- `dataaddr*`, datatype <- `datatype*`}
    -- (Eleminst_ok: `%|-%:%`(s, s.ELEMS_store[elemaddr], elemtype))*{elemaddr <- `elemaddr*`, elemtype <- `elemtype*`}
    -- if $disjoint_(syntax name, exportinst.NAME_exportinst*{exportinst <- `exportinst*`})
    -- (if (exportinst.ADDR_exportinst <- GLOBAL_externaddr(globaladdr)*{globaladdr <- `globaladdr*`} ++ MEM_externaddr(memaddr)*{memaddr <- `memaddr*`} ++ TABLE_externaddr(tableaddr)*{tableaddr <- `tableaddr*`} ++ FUNC_externaddr(funcaddr)*{funcaddr <- `funcaddr*`}))*{exportinst <- `exportinst*`}

;; ../specification/wasm-2.0/B-soundness.spectec:294.1-294.44
relation Frame_ok: `%|-%:%`(store, frame, context)
  ;; ../specification/wasm-2.0/B-soundness.spectec:298.1-301.29
  rule _{s : store, `val*` : val*, moduleinst : moduleinst, `t*` : valtype*, C : context}:
    `%|-%:%`(s, {LOCALS val*{val <- `val*`}, MODULE moduleinst}, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS t*{t <- `t*`}, LABELS [], RETURN ?()} +++ C)
    -- Moduleinst_ok: `%|-%:%`(s, moduleinst, C)
    -- (Val_ok: `%|-%:%`(s, val, t))*{t <- `t*`, val <- `val*`}

;; ../specification/wasm-2.0/B-soundness.spectec:68.1-73.36
rec {

;; ../specification/wasm-2.0/B-soundness.spectec:68.1-69.36
relation Instr_ok2: `%;%|-%:%`(store, context, admininstr, functype)
  ;; ../specification/wasm-2.0/B-soundness.spectec:75.1-77.41
  rule plain{s : store, C : context, instr : instr, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%;%|-%:%`(s, C, (instr : instr <: admininstr), `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instr_ok: `%|-%:%`(C, instr, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; ../specification/wasm-2.0/B-soundness.spectec:79.1-82.68
  rule label{s : store, C : context, n : n, `instr'*` : instr*, `admininstr*` : admininstr*, `t*` : valtype*, `t'*` : valtype*}:
    `%;%|-%:%`(s, C, `LABEL_%{%}%`_admininstr(n, instr'*{instr' <- `instr'*`}, admininstr*{admininstr <- `admininstr*`}), `%->%`_functype(`%`_resulttype([]), `%`_resulttype(t*{t <- `t*`})))
    -- Instrs_ok2: `%;%|-%:%`(s, C, (instr' : instr <: admininstr)*{instr' <- `instr'*`}, `%->%`_functype(`%`_resulttype(t'^n{t' <- `t'*`}), `%`_resulttype(t*{t <- `t*`})))
    -- Instrs_ok2: `%;%|-%:%`(s, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [`%`_resulttype(t'^n{t' <- `t'*`})], RETURN ?()} +++ C, admininstr*{admininstr <- `admininstr*`}, `%->%`_functype(`%`_resulttype([]), `%`_resulttype(t*{t <- `t*`})))

  ;; ../specification/wasm-2.0/B-soundness.spectec:84.1-87.58
  rule frame{s : store, C : context, n : n, f : frame, `admininstr*` : admininstr*, `t*` : valtype*, C' : context}:
    `%;%|-%:%`(s, C, `FRAME_%{%}%`_admininstr(n, f, admininstr*{admininstr <- `admininstr*`}), `%->%`_functype(`%`_resulttype([]), `%`_resulttype(t^n{t <- `t*`})))
    -- Frame_ok: `%|-%:%`(s, f, C')
    -- Expr_ok2: `%;%|-%:%`(s, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], RETURN ?(`%`_resulttype(t^n{t <- `t*`}))} +++ C', admininstr*{admininstr <- `admininstr*`}, `%`_resulttype(t^n{t <- `t*`}))

  ;; ../specification/wasm-2.0/B-soundness.spectec:89.1-91.60
  rule call_addr{s : store, C : context, funcaddr : funcaddr, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%;%|-%:%`(s, C, CALL_ADDR_admininstr(funcaddr), `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Externaddr_ok: `%|-%:%`(s, FUNC_externaddr(funcaddr), FUNC_externtype(`%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`}))))

  ;; ../specification/wasm-2.0/B-soundness.spectec:93.1-95.27
  rule ref{s : store, C : context, ref : ref, rt : reftype}:
    `%;%|-%:%`(s, C, (ref : ref <: admininstr), `%->%`_functype(`%`_resulttype([]), `%`_resulttype([(rt : reftype <: valtype)])))
    -- Ref_ok: `%|-%:%`(s, ref, rt)

  ;; ../specification/wasm-2.0/B-soundness.spectec:97.1-98.30
  rule trap{s : store, C : context, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%;%|-%:%`(s, C, TRAP_admininstr, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

;; ../specification/wasm-2.0/B-soundness.spectec:70.1-71.36
relation Instrs_ok2: `%;%|-%:%`(store, context, admininstr*, functype)
  ;; ../specification/wasm-2.0/B-soundness.spectec:101.1-102.27
  rule empty{s : store, C : context}:
    `%;%|-%:%`(s, C, [], `%->%`_functype(`%`_resulttype([]), `%`_resulttype([])))

  ;; ../specification/wasm-2.0/B-soundness.spectec:104.1-106.50
  rule instr{s : store, C : context, admininstr : admininstr, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%;%|-%:%`(s, C, [admininstr], `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instr_ok2: `%;%|-%:%`(s, C, admininstr, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; ../specification/wasm-2.0/B-soundness.spectec:108.1-111.54
  rule seq{s : store, C : context, `admininstr_1*` : admininstr*, `admininstr_2*` : admininstr*, `t_1*` : valtype*, `t_3*` : valtype*, `t_2*` : valtype*}:
    `%;%|-%:%`(s, C, admininstr_1*{admininstr_1 <- `admininstr_1*`} ++ admininstr_2*{admininstr_2 <- `admininstr_2*`}, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_3*{t_3 <- `t_3*`})))
    -- Instrs_ok2: `%;%|-%:%`(s, C, admininstr_1*{admininstr_1 <- `admininstr_1*`}, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok2: `%;%|-%:%`(s, C, admininstr_2*{admininstr_2 <- `admininstr_2*`}, `%->%`_functype(`%`_resulttype(t_2*{t_2 <- `t_2*`}), `%`_resulttype(t_3*{t_3 <- `t_3*`})))

  ;; ../specification/wasm-2.0/B-soundness.spectec:113.1-117.38
  rule sub{s : store, C : context, `admininstr*` : admininstr*, `t'_1*` : valtype*, `t'_2*` : valtype*, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%;%|-%:%`(s, C, admininstr*{admininstr <- `admininstr*`}, `%->%`_functype(`%`_resulttype(t'_1*{t'_1 <- `t'_1*`}), `%`_resulttype(t'_2*{t'_2 <- `t'_2*`})))
    -- Instrs_ok2: `%;%|-%:%`(s, C, admininstr*{admininstr <- `admininstr*`}, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Resulttype_sub: `|-%<:%`(`%`_resulttype(t'_1*{t'_1 <- `t'_1*`}), `%`_resulttype(t_1*{t_1 <- `t_1*`}))
    -- Resulttype_sub: `|-%<:%`(`%`_resulttype(t_2*{t_2 <- `t_2*`}), `%`_resulttype(t'_2*{t'_2 <- `t'_2*`}))

  ;; ../specification/wasm-2.0/B-soundness.spectec:119.1-121.52
  rule frame{s : store, C : context, `admininstr*` : admininstr*, `t*` : valtype*, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%;%|-%:%`(s, C, admininstr*{admininstr <- `admininstr*`}, `%->%`_functype(`%`_resulttype(t*{t <- `t*`} ++ t_1*{t_1 <- `t_1*`}), `%`_resulttype(t*{t <- `t*`} ++ t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok2: `%;%|-%:%`(s, C, admininstr*{admininstr <- `admininstr*`}, `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

;; ../specification/wasm-2.0/B-soundness.spectec:72.1-73.36
relation Expr_ok2: `%;%|-%:%`(store, context, adminexpr, resulttype)
  ;; ../specification/wasm-2.0/B-soundness.spectec:123.1-125.49
  rule _{s : store, C : context, `admininstr*` : admininstr*, `t*` : valtype*}:
    `%;%|-%:%`(s, C, admininstr*{admininstr <- `admininstr*`}, `%`_resulttype(t*{t <- `t*`}))
    -- Instrs_ok2: `%;%|-%:%`(s, C, admininstr*{admininstr <- `admininstr*`}, `%->%`_functype(`%`_resulttype([]), `%`_resulttype(t*{t <- `t*`})))
}

;; ../specification/wasm-2.0/B-soundness.spectec:154.1-154.57
relation Globalinst_ok: `%|-%:%`(store, globalinst, globaltype)
  ;; ../specification/wasm-2.0/B-soundness.spectec:162.1-165.26
  rule _{s : store, mut : mut, t : valtype, val : val}:
    `%|-%:%`(s, {TYPE `%%`_globaltype(mut, t), VALUE val}, `%%`_globaltype(mut, t))
    -- Globaltype_ok: `|-%:OK`(`%%`_globaltype(mut, t))
    -- Val_ok: `%|-%:%`(s, val, t)

;; ../specification/wasm-2.0/B-soundness.spectec:155.1-155.48
relation Meminst_ok: `%|-%:%`(store, meminst, memtype)
  ;; ../specification/wasm-2.0/B-soundness.spectec:167.1-170.37
  rule _{s : store, n : n, `m?` : m?, `b*` : byte*}:
    `%|-%:%`(s, {TYPE `%PAGE`_memtype(`[%..%]`_limits(`%`_u32(n), `%`_u32(m)?{m <- `m?`})), BYTES b*{b <- `b*`}}, `%PAGE`_memtype(`[%..%]`_limits(`%`_u32(n), `%`_u32(m)?{m <- `m?`})))
    -- Memtype_ok: `|-%:OK`(`%PAGE`_memtype(`[%..%]`_limits(`%`_u32(n), `%`_u32(m)?{m <- `m?`})))
    -- if (|b*{b <- `b*`}| = (n * (64 * $Ki)))

;; ../specification/wasm-2.0/B-soundness.spectec:156.1-156.54
relation Tableinst_ok: `%|-%:%`(store, tableinst, tabletype)
  ;; ../specification/wasm-2.0/B-soundness.spectec:172.1-176.19
  rule _{s : store, n : n, `m?` : m?, rt : reftype, `ref*` : ref*}:
    `%|-%:%`(s, {TYPE `%%`_tabletype(`[%..%]`_limits(`%`_u32(n), `%`_u32(m)?{m <- `m?`}), rt), REFS ref*{ref <- `ref*`}}, `%%`_tabletype(`[%..%]`_limits(`%`_u32(n), `%`_u32(m)?{m <- `m?`}), rt))
    -- Tabletype_ok: `|-%:OK`(`%%`_tabletype(`[%..%]`_limits(`%`_u32(n), `%`_u32(m)?{m <- `m?`}), rt))
    -- (Ref_ok: `%|-%:%`(s, ref, rt))*{ref <- `ref*`}
    -- if (|ref*{ref <- `ref*`}| = n)

;; ../specification/wasm-2.0/B-soundness.spectec:157.1-157.51
relation Funcinst_ok: `%|-%:%`(store, funcinst, functype)
  ;; ../specification/wasm-2.0/B-soundness.spectec:178.1-182.29
  rule _{s : store, ft : functype, moduleinst : moduleinst, func : func, C : context}:
    `%|-%:%`(s, {TYPE ft, MODULE moduleinst, CODE func}, ft)
    -- Functype_ok: `|-%:OK`(ft)
    -- Moduleinst_ok: `%|-%:%`(s, moduleinst, C)
    -- Func_ok: `%|-%:%`(C, func, ft)

;; ../specification/wasm-2.0/B-soundness.spectec:234.1-234.33
relation Store_ok: `|-%:OK`(store)
  ;; ../specification/wasm-2.0/B-soundness.spectec:236.1-246.64
  rule _{s : store, `globalinst*` : globalinst*, `globaltype*` : globaltype*, `meminst*` : meminst*, `memtype*` : memtype*, `tableinst*` : tableinst*, `tabletype*` : tabletype*, `funcinst*` : funcinst*, `functype*` : functype*, `datainst*` : datainst*, `datatype*` : datatype*, `eleminst*` : eleminst*, `elemtype*` : elemtype*}:
    `|-%:OK`(s)
    -- (Globalinst_ok: `%|-%:%`(s, globalinst, globaltype))*{globalinst <- `globalinst*`, globaltype <- `globaltype*`}
    -- (Meminst_ok: `%|-%:%`(s, meminst, memtype))*{meminst <- `meminst*`, memtype <- `memtype*`}
    -- (Tableinst_ok: `%|-%:%`(s, tableinst, tabletype))*{tableinst <- `tableinst*`, tabletype <- `tabletype*`}
    -- (Funcinst_ok: `%|-%:%`(s, funcinst, functype))*{funcinst <- `funcinst*`, functype <- `functype*`}
    -- (Datainst_ok: `%|-%:%`(s, datainst, datatype))*{datainst <- `datainst*`, datatype <- `datatype*`}
    -- (Eleminst_ok: `%|-%:%`(s, eleminst, elemtype))*{eleminst <- `eleminst*`, elemtype <- `elemtype*`}
    -- if (s = {FUNCS funcinst*{funcinst <- `funcinst*`}, GLOBALS globalinst*{globalinst <- `globalinst*`}, TABLES tableinst*{tableinst <- `tableinst*`}, MEMS meminst*{meminst <- `meminst*`}, ELEMS eleminst*{eleminst <- `eleminst*`}, DATAS datainst*{datainst <- `datainst*`}})

;; ../specification/wasm-2.0/B-soundness.spectec:250.1-250.54
relation Extend_globalinst: `%<=%`(globalinst, globalinst)
  ;; ../specification/wasm-2.0/B-soundness.spectec:258.1-260.32
  rule _{mut : mut, t : valtype, val : val, val' : val}:
    `%<=%`({TYPE `%%`_globaltype(mut, t), VALUE val}, {TYPE `%%`_globaltype(mut, t), VALUE val'})
    -- if ((mut = ?(MUT_MUT)) \/ (val = val'))

;; ../specification/wasm-2.0/B-soundness.spectec:251.1-251.45
relation Extend_meminst: `%<=%`(meminst, meminst)
  ;; ../specification/wasm-2.0/B-soundness.spectec:262.1-265.22
  rule _{n : n, `m?` : m?, `b*` : byte*, n' : n, `b'*` : byte*}:
    `%<=%`({TYPE `%PAGE`_memtype(`[%..%]`_limits(`%`_u32(n), `%`_u32(m)?{m <- `m?`})), BYTES b*{b <- `b*`}}, {TYPE `%PAGE`_memtype(`[%..%]`_limits(`%`_u32(n'), `%`_u32(m)?{m <- `m?`})), BYTES b'*{b' <- `b'*`}})
    -- if (n <= n')
    -- if (|b*{b <- `b*`}| <= |b'*{b' <- `b'*`}|)

;; ../specification/wasm-2.0/B-soundness.spectec:252.1-252.51
relation Extend_tableinst: `%<=%`(tableinst, tableinst)
  ;; ../specification/wasm-2.0/B-soundness.spectec:267.1-270.26
  rule _{n : n, `m?` : m?, rt : reftype, `ref*` : ref*, n' : n, `ref'*` : ref*}:
    `%<=%`({TYPE `%%`_tabletype(`[%..%]`_limits(`%`_u32(n), `%`_u32(m)?{m <- `m?`}), rt), REFS ref*{ref <- `ref*`}}, {TYPE `%%`_tabletype(`[%..%]`_limits(`%`_u32(n'), `%`_u32(m)?{m <- `m?`}), rt), REFS ref'*{ref' <- `ref'*`}})
    -- if (n <= n')
    -- if (|ref*{ref <- `ref*`}| <= |ref'*{ref' <- `ref'*`}|)

;; ../specification/wasm-2.0/B-soundness.spectec:253.1-253.48
relation Extend_funcinst: `%<=%`(funcinst, funcinst)
  ;; ../specification/wasm-2.0/B-soundness.spectec:272.1-273.66
  rule _{ft : functype, mm : moduleinst, fc : func}:
    `%<=%`({TYPE ft, MODULE mm, CODE fc}, {TYPE ft, MODULE mm, CODE fc})

;; ../specification/wasm-2.0/B-soundness.spectec:254.1-254.48
relation Extend_datainst: `%<=%`(datainst, datainst)
  ;; ../specification/wasm-2.0/B-soundness.spectec:275.1-277.30
  rule _{`b*` : byte*, `b'*` : byte*}:
    `%<=%`({BYTES b*{b <- `b*`}}, {BYTES b'*{b' <- `b'*`}})
    -- if ((b*{b <- `b*`} = b'*{b' <- `b'*`}) \/ (b'*{b' <- `b'*`} = []))

;; ../specification/wasm-2.0/B-soundness.spectec:255.1-255.48
relation Extend_eleminst: `%<=%`(eleminst, eleminst)
  ;; ../specification/wasm-2.0/B-soundness.spectec:279.1-281.36
  rule _{rt : reftype, `ref*` : ref*, `ref'*` : ref*}:
    `%<=%`({TYPE rt, REFS ref*{ref <- `ref*`}}, {TYPE rt, REFS ref'*{ref' <- `ref'*`}})
    -- if ((ref*{ref <- `ref*`} = ref'*{ref' <- `ref'*`}) \/ (ref'*{ref' <- `ref'*`} = []))

;; ../specification/wasm-2.0/B-soundness.spectec:256.1-256.39
relation Extend_store: `%<=%`(store, store)
  ;; ../specification/wasm-2.0/B-soundness.spectec:283.1-290.66
  rule _{s : store, s' : store}:
    `%<=%`(s, s')
    -- (Extend_globalinst: `%<=%`(s.GLOBALS_store[a], s'.GLOBALS_store[a]))^(a<|s.GLOBALS_store|){}
    -- (Extend_meminst: `%<=%`(s.MEMS_store[a], s'.MEMS_store[a]))^(a<|s.MEMS_store|){}
    -- (Extend_tableinst: `%<=%`(s.TABLES_store[a], s'.TABLES_store[a]))^(a<|s.TABLES_store|){}
    -- (Extend_funcinst: `%<=%`(s.FUNCS_store[a], s'.FUNCS_store[a]))^(a<|s.FUNCS_store|){}
    -- (Extend_datainst: `%<=%`(s.DATAS_store[a], s'.DATAS_store[a]))^(a<|s.DATAS_store|){}
    -- (Extend_eleminst: `%<=%`(s.ELEMS_store[a], s'.ELEMS_store[a]))^(a<|s.ELEMS_store|){}

;; ../specification/wasm-2.0/B-soundness.spectec:295.1-295.38
relation State_ok: `|-%:%`(state, context)
  ;; ../specification/wasm-2.0/B-soundness.spectec:303.1-306.26
  rule _{s : store, f : frame, C : context}:
    `|-%:%`(`%;%`_state(s, f), C)
    -- Store_ok: `|-%:OK`(s)
    -- Frame_ok: `%|-%:%`(s, f, C)

;; ../specification/wasm-2.0/B-soundness.spectec:296.1-296.43
relation Config_ok: `|-%:%`(config, resulttype)
  ;; ../specification/wasm-2.0/B-soundness.spectec:308.1-311.40
  rule _{s : store, f : frame, `admininstr*` : admininstr*, `t*` : valtype*, C : context}:
    `|-%:%`(`%;%`_config(`%;%`_state(s, f), admininstr*{admininstr <- `admininstr*`}), `%`_resulttype(t*{t <- `t*`}))
    -- State_ok: `|-%:%`(`%;%`_state(s, f), C)
    -- Expr_ok2: `%;%|-%:%`(s, C, admininstr*{admininstr <- `admininstr*`}, `%`_resulttype(t*{t <- `t*`}))

;; ../specification/wasm-2.0/A-binary.spectec:18.1-18.41
grammar Bbyte : byte
  ;; ../specification/wasm-2.0/A-binary.spectec:18.24-18.41
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:(0x00 | ... | 0xFF) => `%`_byte(`<implicit-prod-result>`)

;; ../specification/wasm-2.0/A-binary.spectec:20.1-22.82
rec {

;; ../specification/wasm-2.0/A-binary.spectec:20.1-22.82
grammar BuN(N : N) : uN(N)
  ;; ../specification/wasm-2.0/A-binary.spectec:21.5-21.83
  prod{n : n} `%`_byte(n):Bbyte => `%`_uN(n)
    -- if ((n < (2 ^ 7)) /\ (n < (2 ^ N)))
  ;; ../specification/wasm-2.0/A-binary.spectec:22.5-22.82
  prod{m : m, n : n} {{`%`_byte(n):Bbyte} {`%`_uN(m):BuN((((N : nat <:> int) - (7 : nat <:> int)) : int <:> nat))}} => `%`_uN((((2 ^ 7) * m) + (((n : nat <:> int) - ((2 ^ 7) : nat <:> int)) : int <:> nat)))
    -- if ((n >= (2 ^ 7)) /\ (N > 7))
}

;; ../specification/wasm-2.0/A-binary.spectec:37.1-37.29
grammar Bu32 : u32
  ;; ../specification/wasm-2.0/A-binary.spectec:37.22-37.29
  prod{`<implicit-prod-result>` : uN(32)} `<implicit-prod-result>`:BuN(32) => `<implicit-prod-result>`

;; ../specification/wasm-2.0/A-binary.spectec:7.1-8.29
grammar Blist(syntax el, grammar BX : el) : el*
  ;; ../specification/wasm-2.0/A-binary.spectec:8.5-8.29
  prod{n : n, `el*` : el*} {{`%`_u32(n):Bu32} {el:BX^n{el <- `el*`}}} => el^n{el <- `el*`}

;; ../specification/wasm-2.0/A-binary.spectec:24.1-27.82
rec {

;; ../specification/wasm-2.0/A-binary.spectec:24.1-27.82
grammar BsN(N : N) : sN(N)
  ;; ../specification/wasm-2.0/A-binary.spectec:25.5-25.87
  prod{n : n} `%`_byte(n):Bbyte => `%`_sN((n : nat <:> int))
    -- if ((n < (2 ^ 6)) /\ (n < (2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat))))
  ;; ../specification/wasm-2.0/A-binary.spectec:26.5-26.101
  prod{n : n} `%`_byte(n):Bbyte => `%`_sN(((n : nat <:> int) - ((2 ^ 7) : nat <:> int)))
    -- if ((((2 ^ 6) <= n) /\ (n < (2 ^ 7))) /\ ((n : nat <:> int) >= (((2 ^ 7) : nat <:> int) - ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int))))
  ;; ../specification/wasm-2.0/A-binary.spectec:27.5-27.82
  prod{i : sN((((N : nat <:> int) - (7 : nat <:> int)) : int <:> nat)), n : n} {{`%`_byte(n):Bbyte} {i:BsN((((N : nat <:> int) - (7 : nat <:> int)) : int <:> nat))}} => `%`_sN(((((2 ^ 7) * (i!`%`_sN.0 : int <:> nat)) + (((n : nat <:> int) - ((2 ^ 7) : nat <:> int)) : int <:> nat)) : nat <:> int))
    -- if ((n >= (2 ^ 7)) /\ (N > 7))
}

;; ../specification/wasm-2.0/A-binary.spectec:29.1-30.50
grammar BiN(N : N) : iN(N)
  ;; ../specification/wasm-2.0/A-binary.spectec:30.5-30.50
  prod{i : sN(N)} i:BsN(N) => `%`_iN($inv_signed_(N, i!`%`_sN.0))

;; ../specification/wasm-2.0/A-binary.spectec:33.1-34.43
grammar BfN(N : N) : fN(N)
  ;; ../specification/wasm-2.0/A-binary.spectec:34.5-34.43
  prod{`b*` : byte*} b*{b <- `b*`}:Bbyte^(((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat){} => $inv_fbytes_(N, b*{b <- `b*`})

;; ../specification/wasm-2.0/A-binary.spectec:38.1-38.29
grammar Bu64 : u64
  ;; ../specification/wasm-2.0/A-binary.spectec:38.22-38.29
  prod{`<implicit-prod-result>` : uN(64)} `<implicit-prod-result>`:BuN(64) => `<implicit-prod-result>`

;; ../specification/wasm-2.0/A-binary.spectec:40.1-40.29
grammar Bs33 : s33
  ;; ../specification/wasm-2.0/A-binary.spectec:40.22-40.29
  prod{`<implicit-prod-result>` : sN(33)} `<implicit-prod-result>`:BsN(33) => `<implicit-prod-result>`

;; ../specification/wasm-2.0/A-binary.spectec:42.1-42.29
grammar Bi32 : i32
  ;; ../specification/wasm-2.0/A-binary.spectec:42.22-42.29
  prod{`<implicit-prod-result>` : iN(32)} `<implicit-prod-result>`:BiN(32) => `<implicit-prod-result>`

;; ../specification/wasm-2.0/A-binary.spectec:43.1-43.29
grammar Bi64 : i64
  ;; ../specification/wasm-2.0/A-binary.spectec:43.22-43.29
  prod{`<implicit-prod-result>` : iN(64)} `<implicit-prod-result>`:BiN(64) => `<implicit-prod-result>`

;; ../specification/wasm-2.0/A-binary.spectec:45.1-45.29
grammar Bf32 : f32
  ;; ../specification/wasm-2.0/A-binary.spectec:45.22-45.29
  prod{`<implicit-prod-result>` : fN(32)} `<implicit-prod-result>`:BfN(32) => `<implicit-prod-result>`

;; ../specification/wasm-2.0/A-binary.spectec:46.1-46.29
grammar Bf64 : f64
  ;; ../specification/wasm-2.0/A-binary.spectec:46.22-46.29
  prod{`<implicit-prod-result>` : fN(64)} `<implicit-prod-result>`:BfN(64) => `<implicit-prod-result>`

;; ../specification/wasm-2.0/A-binary.spectec:60.1-61.52
grammar Bname : name
  ;; ../specification/wasm-2.0/A-binary.spectec:61.5-61.52
  prod{name : name, `b*` : byte*} b*{b <- `b*`}:Blist(syntax byte, grammar Bbyte) => name
    -- if ($utf8(name!`%`_name.0) = b*{b <- `b*`})

;; ../specification/wasm-2.0/A-binary.spectec:66.1-66.41
grammar Btypeidx : typeidx
  ;; ../specification/wasm-2.0/A-binary.spectec:66.30-66.41
  prod{x : idx} x:Bu32 => x

;; ../specification/wasm-2.0/A-binary.spectec:67.1-67.41
grammar Bfuncidx : funcidx
  ;; ../specification/wasm-2.0/A-binary.spectec:67.30-67.41
  prod{x : idx} x:Bu32 => x

;; ../specification/wasm-2.0/A-binary.spectec:68.1-68.45
grammar Bglobalidx : globalidx
  ;; ../specification/wasm-2.0/A-binary.spectec:68.34-68.45
  prod{x : idx} x:Bu32 => x

;; ../specification/wasm-2.0/A-binary.spectec:69.1-69.43
grammar Btableidx : tableidx
  ;; ../specification/wasm-2.0/A-binary.spectec:69.32-69.43
  prod{x : idx} x:Bu32 => x

;; ../specification/wasm-2.0/A-binary.spectec:70.1-70.39
grammar Bmemidx : memidx
  ;; ../specification/wasm-2.0/A-binary.spectec:70.28-70.39
  prod{x : idx} x:Bu32 => x

;; ../specification/wasm-2.0/A-binary.spectec:71.1-71.41
grammar Belemidx : elemidx
  ;; ../specification/wasm-2.0/A-binary.spectec:71.30-71.41
  prod{x : idx} x:Bu32 => x

;; ../specification/wasm-2.0/A-binary.spectec:72.1-72.41
grammar Bdataidx : dataidx
  ;; ../specification/wasm-2.0/A-binary.spectec:72.30-72.41
  prod{x : idx} x:Bu32 => x

;; ../specification/wasm-2.0/A-binary.spectec:73.1-73.43
grammar Blocalidx : localidx
  ;; ../specification/wasm-2.0/A-binary.spectec:73.32-73.43
  prod{x : idx} x:Bu32 => x

;; ../specification/wasm-2.0/A-binary.spectec:74.1-74.43
grammar Blabelidx : labelidx
  ;; ../specification/wasm-2.0/A-binary.spectec:74.32-74.43
  prod{x : idx} x:Bu32 => x

;; ../specification/wasm-2.0/A-binary.spectec:76.1-80.34
grammar Bexternidx : externidx
  ;; ../specification/wasm-2.0/A-binary.spectec:77.5-77.30
  prod{x : idx} {{0x00} {x:Bfuncidx}} => FUNC_externidx(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:78.5-78.32
  prod{x : idx} {{0x01} {x:Btableidx}} => TABLE_externidx(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:79.5-79.28
  prod{x : idx} {{0x02} {x:Bmemidx}} => MEM_externidx(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:80.5-80.34
  prod{x : idx} {{0x03} {x:Bglobalidx}} => GLOBAL_externidx(x)

;; ../specification/wasm-2.0/A-binary.spectec:89.1-93.16
grammar Bnumtype : numtype
  ;; ../specification/wasm-2.0/A-binary.spectec:90.5-90.16
  prod 0x7F => I32_numtype
  ;; ../specification/wasm-2.0/A-binary.spectec:91.5-91.16
  prod 0x7E => I64_numtype
  ;; ../specification/wasm-2.0/A-binary.spectec:92.5-92.16
  prod 0x7D => F32_numtype
  ;; ../specification/wasm-2.0/A-binary.spectec:93.5-93.16
  prod 0x7C => F64_numtype

;; ../specification/wasm-2.0/A-binary.spectec:95.1-96.17
grammar Bvectype : vectype
  ;; ../specification/wasm-2.0/A-binary.spectec:96.5-96.17
  prod 0x7B => V128_vectype

;; ../specification/wasm-2.0/A-binary.spectec:98.1-100.22
grammar Breftype : reftype
  ;; ../specification/wasm-2.0/A-binary.spectec:99.5-99.20
  prod 0x70 => FUNCREF_reftype
  ;; ../specification/wasm-2.0/A-binary.spectec:100.5-100.22
  prod 0x6F => EXTERNREF_reftype

;; ../specification/wasm-2.0/A-binary.spectec:102.1-105.22
grammar Bvaltype : valtype
  ;; ../specification/wasm-2.0/A-binary.spectec:103.5-103.22
  prod{nt : numtype} nt:Bnumtype => (nt : numtype <: valtype)
  ;; ../specification/wasm-2.0/A-binary.spectec:104.5-104.22
  prod{vt : vectype} vt:Bvectype => (vt : vectype <: valtype)
  ;; ../specification/wasm-2.0/A-binary.spectec:105.5-105.22
  prod{rt : reftype} rt:Breftype => (rt : reftype <: valtype)

;; ../specification/wasm-2.0/A-binary.spectec:108.1-109.29
grammar Bresulttype : resulttype
  ;; ../specification/wasm-2.0/A-binary.spectec:109.5-109.29
  prod{`t*` : valtype*} t*{t <- `t*`}:Blist(syntax valtype, grammar Bvaltype) => `%`_resulttype(t*{t <- `t*`})

;; ../specification/wasm-2.0/A-binary.spectec:114.1-115.59
grammar Bfunctype : functype
  ;; ../specification/wasm-2.0/A-binary.spectec:115.5-115.59
  prod{`t_1*` : valtype*, `t_2*` : valtype*} {{0x60} {`%`_resulttype(t_1*{t_1 <- `t_1*`}):Bresulttype} {`%`_resulttype(t_2*{t_2 <- `t_2*`}):Bresulttype}} => `%->%`_functype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`}))

;; ../specification/wasm-2.0/A-binary.spectec:120.1-122.16
grammar Bmut : mut
  ;; ../specification/wasm-2.0/A-binary.spectec:121.5-121.16
  prod 0x00 => ?()
  ;; ../specification/wasm-2.0/A-binary.spectec:122.5-122.16
  prod 0x01 => ?(MUT_MUT)

;; ../specification/wasm-2.0/A-binary.spectec:124.1-126.36
grammar Blimits : limits
  ;; ../specification/wasm-2.0/A-binary.spectec:125.5-125.31
  prod{n : n} {{0x00} {`%`_u32(n):Bu32}} => `[%..%]`_limits(`%`_u32(n), ?())
  ;; ../specification/wasm-2.0/A-binary.spectec:126.5-126.36
  prod{n : n, m : m} {{0x01} {`%`_u32(n):Bu32} {`%`_u32(m):Bu32}} => `[%..%]`_limits(`%`_u32(n), ?(`%`_u32(m)))

;; ../specification/wasm-2.0/A-binary.spectec:128.1-129.33
grammar Bglobaltype : globaltype
  ;; ../specification/wasm-2.0/A-binary.spectec:129.5-129.33
  prod{mut : mut, t : valtype} {{t:Bvaltype} {mut:Bmut}} => `%%`_globaltype(mut, t)

;; ../specification/wasm-2.0/A-binary.spectec:131.1-132.38
grammar Btabletype : tabletype
  ;; ../specification/wasm-2.0/A-binary.spectec:132.5-132.38
  prod{lim : limits, rt : reftype} {{rt:Breftype} {lim:Blimits}} => `%%`_tabletype(lim, rt)

;; ../specification/wasm-2.0/A-binary.spectec:134.1-135.28
grammar Bmemtype : memtype
  ;; ../specification/wasm-2.0/A-binary.spectec:135.5-135.28
  prod{lim : limits} lim:Blimits => `%PAGE`_memtype(lim)

;; ../specification/wasm-2.0/A-binary.spectec:138.1-142.37
grammar Bexterntype : externtype
  ;; ../specification/wasm-2.0/A-binary.spectec:139.5-139.33
  prod{ft : functype} {{0x00} {ft:Bfunctype}} => FUNC_externtype(ft)
  ;; ../specification/wasm-2.0/A-binary.spectec:140.5-140.35
  prod{tt : tabletype} {{0x01} {tt:Btabletype}} => TABLE_externtype(tt)
  ;; ../specification/wasm-2.0/A-binary.spectec:141.5-141.31
  prod{mt : memtype} {{0x02} {mt:Bmemtype}} => MEM_externtype(mt)
  ;; ../specification/wasm-2.0/A-binary.spectec:142.5-142.37
  prod{gt : globaltype} {{0x03} {gt:Bglobaltype}} => GLOBAL_externtype(gt)

;; ../specification/wasm-2.0/A-binary.spectec:151.1-154.44
grammar Bblocktype : blocktype
  ;; ../specification/wasm-2.0/A-binary.spectec:152.5-152.24
  prod 0x40 => _RESULT_blocktype(?())
  ;; ../specification/wasm-2.0/A-binary.spectec:153.5-153.28
  prod{t : valtype} t:Bvaltype => _RESULT_blocktype(?(t))
  ;; ../specification/wasm-2.0/A-binary.spectec:154.5-154.44
  prod{x : idx, i : s33} i:Bs33 => _IDX_blocktype(x)
    -- if ((i!`%`_s33.0 >= (0 : nat <:> int)) /\ (`%`_idx((i!`%`_s33.0 : int <:> nat)) = x))

;; ../specification/wasm-2.0/A-binary.spectec:220.1-221.41
grammar Bmemarg : memarg
  ;; ../specification/wasm-2.0/A-binary.spectec:221.5-221.41
  prod{n : n, m : m} {{`%`_u32(n):Bu32} {`%`_u32(m):Bu32}} => {ALIGN `%`_u32(n), OFFSET `%`_u32(m)}

;; ../specification/wasm-2.0/A-binary.spectec:456.1-457.17
grammar Blaneidx : laneidx
  ;; ../specification/wasm-2.0/A-binary.spectec:457.5-457.17
  prod{l : labelidx} `%`_byte(l!`%`_labelidx.0):Bbyte => `%`_laneidx(l!`%`_labelidx.0)

;; ../specification/wasm-2.0/A-binary.spectec:742.1-752.59
rec {

;; ../specification/wasm-2.0/A-binary.spectec:742.1-752.59
grammar Binstr : instr
  ;; ../specification/wasm-2.0/A-binary.spectec:160.5-160.24
  prod 0x00 => UNREACHABLE_instr
  ;; ../specification/wasm-2.0/A-binary.spectec:161.5-161.16
  prod 0x01 => NOP_instr
  ;; ../specification/wasm-2.0/A-binary.spectec:162.5-162.57
  prod{bt : blocktype, `in*` : instr*} {{0x02} {bt:Bblocktype} {in:Binstr*{in <- `in*`}} {0x0B}} => BLOCK_instr(bt, in*{in <- `in*`})
  ;; ../specification/wasm-2.0/A-binary.spectec:163.5-163.56
  prod{bt : blocktype, `in*` : instr*} {{0x03} {bt:Bblocktype} {in:Binstr*{in <- `in*`}} {0x0B}} => LOOP_instr(bt, in*{in <- `in*`})
  ;; ../specification/wasm-2.0/A-binary.spectec:164.5-164.63
  prod{bt : blocktype, `in*` : instr*} {{0x04} {bt:Bblocktype} {in:Binstr*{in <- `in*`}} {0x0B}} => `IF%%ELSE%`_instr(bt, in*{in <- `in*`}, [])
  ;; ../specification/wasm-2.0/A-binary.spectec:165.5-165.89
  prod{bt : blocktype, `in_1*` : instr*, `in_2*` : instr*} {{0x04} {bt:Bblocktype} {in_1:Binstr*{in_1 <- `in_1*`}} {0x05} {in_2:Binstr*{in_2 <- `in_2*`}} {0x0B}} => `IF%%ELSE%`_instr(bt, in_1*{in_1 <- `in_1*`}, in_2*{in_2 <- `in_2*`})
  ;; ../specification/wasm-2.0/A-binary.spectec:166.5-166.29
  prod{l : labelidx} {{0x0C} {l:Blabelidx}} => BR_instr(l)
  ;; ../specification/wasm-2.0/A-binary.spectec:167.5-167.32
  prod{l : labelidx} {{0x0D} {l:Blabelidx}} => BR_IF_instr(l)
  ;; ../specification/wasm-2.0/A-binary.spectec:168.5-168.62
  prod{`l*` : labelidx*, l_N : labelidx} {{0x0E} {l*{l <- `l*`}:Blist(syntax labelidx, grammar Blabelidx)} {l_N:Blabelidx}} => BR_TABLE_instr(l*{l <- `l*`}, l_N)
  ;; ../specification/wasm-2.0/A-binary.spectec:169.5-169.19
  prod 0x0F => RETURN_instr
  ;; ../specification/wasm-2.0/A-binary.spectec:170.5-170.30
  prod{x : idx} {{0x10} {x:Bfuncidx}} => CALL_instr(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:171.5-171.53
  prod{x : idx, y : idx} {{0x11} {y:Btypeidx} {x:Btableidx}} => CALL_INDIRECT_instr(x, y)
  ;; ../specification/wasm-2.0/A-binary.spectec:178.5-178.36
  prod{rt : reftype} {{0xD0} {rt:Breftype}} => `REF.NULL`_instr(rt)
  ;; ../specification/wasm-2.0/A-binary.spectec:179.5-179.24
  prod 0xD1 => `REF.IS_NULL`_instr
  ;; ../specification/wasm-2.0/A-binary.spectec:180.5-180.34
  prod{x : idx} {{0xD2} {x:Bfuncidx}} => `REF.FUNC`_instr(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:187.5-187.17
  prod 0x1A => DROP_instr
  ;; ../specification/wasm-2.0/A-binary.spectec:188.5-188.23
  prod 0x1B => SELECT_instr(?())
  ;; ../specification/wasm-2.0/A-binary.spectec:189.5-189.41
  prod{ts : valtype} {{0x1C} {[ts]:Blist(syntax valtype, grammar Bvaltype)}} => SELECT_instr(?([ts]))
  ;; ../specification/wasm-2.0/A-binary.spectec:196.5-196.36
  prod{x : idx} {{0x20} {x:Blocalidx}} => `LOCAL.GET`_instr(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:197.5-197.36
  prod{x : idx} {{0x21} {x:Blocalidx}} => `LOCAL.SET`_instr(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:198.5-198.36
  prod{x : idx} {{0x22} {x:Blocalidx}} => `LOCAL.TEE`_instr(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:199.5-199.38
  prod{x : idx} {{0x23} {x:Bglobalidx}} => `GLOBAL.GET`_instr(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:200.5-200.38
  prod{x : idx} {{0x24} {x:Bglobalidx}} => `GLOBAL.SET`_instr(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:207.5-207.36
  prod{x : idx} {{0x25} {x:Btableidx}} => `TABLE.GET`_instr(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:208.5-208.36
  prod{x : idx} {{0x26} {x:Btableidx}} => `TABLE.SET`_instr(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:209.5-209.58
  prod{x : idx, y : idx} {{0xFC} {`%`_u32(12):Bu32} {y:Belemidx} {x:Btableidx}} => `TABLE.INIT`_instr(x, y)
  ;; ../specification/wasm-2.0/A-binary.spectec:210.5-210.43
  prod{x : idx} {{0xFC} {`%`_u32(13):Bu32} {x:Belemidx}} => `ELEM.DROP`_instr(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:211.5-211.67
  prod{x_1 : idx, x_2 : idx} {{0xFC} {`%`_u32(14):Bu32} {x_1:Btableidx} {x_2:Btableidx}} => `TABLE.COPY`_instr(x_1, x_2)
  ;; ../specification/wasm-2.0/A-binary.spectec:212.5-212.45
  prod{x : idx} {{0xFC} {`%`_u32(15):Bu32} {x:Btableidx}} => `TABLE.GROW`_instr(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:213.5-213.45
  prod{x : idx} {{0xFC} {`%`_u32(16):Bu32} {x:Btableidx}} => `TABLE.SIZE`_instr(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:214.5-214.45
  prod{x : idx} {{0xFC} {`%`_u32(17):Bu32} {x:Btableidx}} => `TABLE.FILL`_instr(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:224.5-224.35
  prod{ao : memarg} {{0x28} {ao:Bmemarg}} => LOAD_instr(I32_numtype, ?(), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:225.5-225.35
  prod{ao : memarg} {{0x29} {ao:Bmemarg}} => LOAD_instr(I64_numtype, ?(), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:226.5-226.35
  prod{ao : memarg} {{0x2A} {ao:Bmemarg}} => LOAD_instr(F32_numtype, ?(), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:227.5-227.35
  prod{ao : memarg} {{0x2B} {ao:Bmemarg}} => LOAD_instr(F64_numtype, ?(), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:228.5-228.43
  prod{ao : memarg} {{0x2C} {ao:Bmemarg}} => LOAD_instr(I32_numtype, ?(`%_%`_loadop_(`%`_sz(8), S_sx)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:229.5-229.43
  prod{ao : memarg} {{0x2D} {ao:Bmemarg}} => LOAD_instr(I32_numtype, ?(`%_%`_loadop_(`%`_sz(8), U_sx)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:230.5-230.44
  prod{ao : memarg} {{0x2E} {ao:Bmemarg}} => LOAD_instr(I32_numtype, ?(`%_%`_loadop_(`%`_sz(16), S_sx)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:231.5-231.44
  prod{ao : memarg} {{0x2F} {ao:Bmemarg}} => LOAD_instr(I32_numtype, ?(`%_%`_loadop_(`%`_sz(16), U_sx)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:232.5-232.43
  prod{ao : memarg} {{0x30} {ao:Bmemarg}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(8), S_sx)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:233.5-233.43
  prod{ao : memarg} {{0x31} {ao:Bmemarg}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(8), U_sx)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:234.5-234.44
  prod{ao : memarg} {{0x32} {ao:Bmemarg}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(16), S_sx)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:235.5-235.44
  prod{ao : memarg} {{0x33} {ao:Bmemarg}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(16), U_sx)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:236.5-236.44
  prod{ao : memarg} {{0x34} {ao:Bmemarg}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(32), S_sx)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:237.5-237.44
  prod{ao : memarg} {{0x35} {ao:Bmemarg}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(32), U_sx)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:238.5-238.36
  prod{ao : memarg} {{0x36} {ao:Bmemarg}} => STORE_instr(I32_numtype, ?(), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:239.5-239.36
  prod{ao : memarg} {{0x37} {ao:Bmemarg}} => STORE_instr(I64_numtype, ?(), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:240.5-240.36
  prod{ao : memarg} {{0x38} {ao:Bmemarg}} => STORE_instr(F32_numtype, ?(), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:241.5-241.36
  prod{ao : memarg} {{0x39} {ao:Bmemarg}} => STORE_instr(F64_numtype, ?(), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:242.5-242.38
  prod{ao : memarg} {{0x3A} {ao:Bmemarg}} => STORE_instr(I32_numtype, ?(`%`_sz(8)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:243.5-243.39
  prod{ao : memarg} {{0x3B} {ao:Bmemarg}} => STORE_instr(I32_numtype, ?(`%`_sz(16)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:244.5-244.38
  prod{ao : memarg} {{0x3C} {ao:Bmemarg}} => STORE_instr(I64_numtype, ?(`%`_sz(8)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:245.5-245.39
  prod{ao : memarg} {{0x3D} {ao:Bmemarg}} => STORE_instr(I64_numtype, ?(`%`_sz(16)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:246.5-246.39
  prod{ao : memarg} {{0x3E} {ao:Bmemarg}} => STORE_instr(I64_numtype, ?(`%`_sz(32)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:247.5-247.29
  prod {{0x3F} {0x00}} => `MEMORY.SIZE`_instr
  ;; ../specification/wasm-2.0/A-binary.spectec:248.5-248.29
  prod {{0x40} {0x00}} => `MEMORY.GROW`_instr
  ;; ../specification/wasm-2.0/A-binary.spectec:249.5-249.49
  prod{x : idx} {{0xFC} {`%`_u32(8):Bu32} {x:Bdataidx} {0x00}} => `MEMORY.INIT`_instr(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:250.5-250.42
  prod{x : idx} {{0xFC} {`%`_u32(9):Bu32} {x:Bdataidx}} => `DATA.DROP`_instr(x)
  ;; ../specification/wasm-2.0/A-binary.spectec:251.5-251.42
  prod {{0xFC} {`%`_u32(10):Bu32} {0x00} {0x00}} => `MEMORY.COPY`_instr
  ;; ../specification/wasm-2.0/A-binary.spectec:252.5-252.37
  prod {{0xFC} {`%`_u32(11):Bu32} {0x00}} => `MEMORY.FILL`_instr
  ;; ../specification/wasm-2.0/A-binary.spectec:260.5-260.31
  prod{i : i32} {{0x41} {i:Bi32}} => CONST_instr(I32_numtype, i)
  ;; ../specification/wasm-2.0/A-binary.spectec:261.5-261.31
  prod{i : i64} {{0x42} {i:Bi64}} => CONST_instr(I64_numtype, i)
  ;; ../specification/wasm-2.0/A-binary.spectec:262.5-262.31
  prod{p : f32} {{0x43} {p:Bf32}} => CONST_instr(F32_numtype, p)
  ;; ../specification/wasm-2.0/A-binary.spectec:263.5-263.31
  prod{p : f64} {{0x44} {p:Bf64}} => CONST_instr(F64_numtype, p)
  ;; ../specification/wasm-2.0/A-binary.spectec:267.5-267.27
  prod 0x45 => TESTOP_instr(I32_numtype, EQZ_testop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:271.5-271.25
  prod 0x46 => RELOP_instr(I32_numtype, EQ_relop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:272.5-272.25
  prod 0x47 => RELOP_instr(I32_numtype, NE_relop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:273.5-273.29
  prod 0x48 => RELOP_instr(I32_numtype, LT_relop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:274.5-274.29
  prod 0x49 => RELOP_instr(I32_numtype, LT_relop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:275.5-275.29
  prod 0x4A => RELOP_instr(I32_numtype, GT_relop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:276.5-276.29
  prod 0x4B => RELOP_instr(I32_numtype, GT_relop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:277.5-277.29
  prod 0x4C => RELOP_instr(I32_numtype, LE_relop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:278.5-278.29
  prod 0x4D => RELOP_instr(I32_numtype, LE_relop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:279.5-279.29
  prod 0x4E => RELOP_instr(I32_numtype, GE_relop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:280.5-280.29
  prod 0x4F => RELOP_instr(I32_numtype, GE_relop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:284.5-284.27
  prod 0x50 => TESTOP_instr(I64_numtype, EQZ_testop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:288.5-288.25
  prod 0x51 => RELOP_instr(I64_numtype, EQ_relop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:289.5-289.25
  prod 0x52 => RELOP_instr(I64_numtype, NE_relop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:290.5-290.29
  prod 0x53 => RELOP_instr(I64_numtype, LT_relop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:291.5-291.29
  prod 0x54 => RELOP_instr(I64_numtype, LT_relop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:292.5-292.29
  prod 0x55 => RELOP_instr(I64_numtype, GT_relop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:293.5-293.29
  prod 0x56 => RELOP_instr(I64_numtype, GT_relop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:294.5-294.29
  prod 0x57 => RELOP_instr(I64_numtype, LE_relop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:295.5-295.29
  prod 0x58 => RELOP_instr(I64_numtype, LE_relop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:296.5-296.29
  prod 0x59 => RELOP_instr(I64_numtype, GE_relop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:297.5-297.29
  prod 0x5A => RELOP_instr(I64_numtype, GE_relop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:301.5-301.25
  prod 0x5B => RELOP_instr(F32_numtype, EQ_relop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:302.5-302.25
  prod 0x5C => RELOP_instr(F32_numtype, NE_relop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:303.5-303.25
  prod 0x5D => RELOP_instr(F32_numtype, LT_relop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:304.5-304.25
  prod 0x5E => RELOP_instr(F32_numtype, GT_relop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:305.5-305.25
  prod 0x5F => RELOP_instr(F32_numtype, LE_relop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:306.5-306.25
  prod 0x60 => RELOP_instr(F32_numtype, GE_relop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:310.5-310.25
  prod 0x61 => RELOP_instr(F64_numtype, EQ_relop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:311.5-311.25
  prod 0x62 => RELOP_instr(F64_numtype, NE_relop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:312.5-312.25
  prod 0x63 => RELOP_instr(F64_numtype, LT_relop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:313.5-313.25
  prod 0x64 => RELOP_instr(F64_numtype, GT_relop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:314.5-314.25
  prod 0x65 => RELOP_instr(F64_numtype, LE_relop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:315.5-315.25
  prod 0x66 => RELOP_instr(F64_numtype, GE_relop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:319.5-319.25
  prod 0x67 => UNOP_instr(I32_numtype, CLZ_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:320.5-320.25
  prod 0x68 => UNOP_instr(I32_numtype, CTZ_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:321.5-321.28
  prod 0x69 => UNOP_instr(I32_numtype, POPCNT_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:325.5-325.26
  prod 0x6A => BINOP_instr(I32_numtype, ADD_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:326.5-326.26
  prod 0x6B => BINOP_instr(I32_numtype, SUB_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:327.5-327.26
  prod 0x6C => BINOP_instr(I32_numtype, MUL_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:328.5-328.30
  prod 0x6D => BINOP_instr(I32_numtype, DIV_binop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:329.5-329.30
  prod 0x6E => BINOP_instr(I32_numtype, DIV_binop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:330.5-330.30
  prod 0x6F => BINOP_instr(I32_numtype, REM_binop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:331.5-331.30
  prod 0x70 => BINOP_instr(I32_numtype, REM_binop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:332.5-332.26
  prod 0x71 => BINOP_instr(I32_numtype, AND_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:333.5-333.25
  prod 0x72 => BINOP_instr(I32_numtype, OR_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:334.5-334.26
  prod 0x73 => BINOP_instr(I32_numtype, XOR_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:335.5-335.26
  prod 0x74 => BINOP_instr(I32_numtype, SHL_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:336.5-336.30
  prod 0x75 => BINOP_instr(I32_numtype, SHR_binop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:337.5-337.30
  prod 0x76 => BINOP_instr(I32_numtype, SHR_binop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:338.5-338.27
  prod 0x77 => BINOP_instr(I32_numtype, ROTL_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:339.5-339.27
  prod 0x78 => BINOP_instr(I32_numtype, ROTR_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:343.5-343.25
  prod 0x79 => UNOP_instr(I64_numtype, CLZ_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:344.5-344.25
  prod 0x7A => UNOP_instr(I64_numtype, CTZ_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:345.5-345.28
  prod 0x7B => UNOP_instr(I64_numtype, POPCNT_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:349.5-349.26
  prod 0x7C => BINOP_instr(I64_numtype, ADD_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:350.5-350.26
  prod 0x7D => BINOP_instr(I64_numtype, SUB_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:351.5-351.26
  prod 0x7E => BINOP_instr(I64_numtype, MUL_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:352.5-352.30
  prod 0x7F => BINOP_instr(I64_numtype, DIV_binop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:353.5-353.30
  prod 0x80 => BINOP_instr(I64_numtype, DIV_binop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:354.5-354.30
  prod 0x81 => BINOP_instr(I64_numtype, REM_binop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:355.5-355.30
  prod 0x82 => BINOP_instr(I64_numtype, REM_binop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:356.5-356.26
  prod 0x83 => BINOP_instr(I64_numtype, AND_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:357.5-357.25
  prod 0x84 => BINOP_instr(I64_numtype, OR_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:358.5-358.26
  prod 0x85 => BINOP_instr(I64_numtype, XOR_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:359.5-359.26
  prod 0x86 => BINOP_instr(I64_numtype, SHL_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:360.5-360.30
  prod 0x87 => BINOP_instr(I64_numtype, SHR_binop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:361.5-361.30
  prod 0x88 => BINOP_instr(I64_numtype, SHR_binop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:362.5-362.27
  prod 0x89 => BINOP_instr(I64_numtype, ROTL_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:363.5-363.27
  prod 0x8A => BINOP_instr(I64_numtype, ROTR_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:367.5-367.25
  prod 0x8B => UNOP_instr(F32_numtype, ABS_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:368.5-368.25
  prod 0x8C => UNOP_instr(F32_numtype, NEG_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:369.5-369.26
  prod 0x8D => UNOP_instr(F32_numtype, CEIL_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:370.5-370.27
  prod 0x8E => UNOP_instr(F32_numtype, FLOOR_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:371.5-371.27
  prod 0x8F => UNOP_instr(F32_numtype, TRUNC_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:372.5-372.29
  prod 0x90 => UNOP_instr(F32_numtype, NEAREST_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:373.5-373.26
  prod 0x91 => UNOP_instr(F32_numtype, SQRT_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:377.5-377.26
  prod 0x92 => BINOP_instr(F32_numtype, ADD_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:378.5-378.26
  prod 0x93 => BINOP_instr(F32_numtype, SUB_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:379.5-379.26
  prod 0x94 => BINOP_instr(F32_numtype, MUL_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:380.5-380.26
  prod 0x95 => BINOP_instr(F32_numtype, DIV_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:381.5-381.26
  prod 0x96 => BINOP_instr(F32_numtype, MIN_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:382.5-382.26
  prod 0x97 => BINOP_instr(F32_numtype, MAX_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:383.5-383.31
  prod 0x98 => BINOP_instr(F32_numtype, COPYSIGN_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:387.5-387.25
  prod 0x99 => UNOP_instr(F64_numtype, ABS_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:388.5-388.25
  prod 0x9A => UNOP_instr(F64_numtype, NEG_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:389.5-389.26
  prod 0x9B => UNOP_instr(F64_numtype, CEIL_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:390.5-390.27
  prod 0x9C => UNOP_instr(F64_numtype, FLOOR_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:391.5-391.27
  prod 0x9D => UNOP_instr(F64_numtype, TRUNC_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:392.5-392.29
  prod 0x9E => UNOP_instr(F64_numtype, NEAREST_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:393.5-393.26
  prod 0x9F => UNOP_instr(F64_numtype, SQRT_unop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:397.5-397.26
  prod 0xA0 => BINOP_instr(F64_numtype, ADD_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:398.5-398.26
  prod 0xA1 => BINOP_instr(F64_numtype, SUB_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:399.5-399.26
  prod 0xA2 => BINOP_instr(F64_numtype, MUL_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:400.5-400.26
  prod 0xA3 => BINOP_instr(F64_numtype, DIV_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:401.5-401.26
  prod 0xA4 => BINOP_instr(F64_numtype, MIN_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:402.5-402.26
  prod 0xA5 => BINOP_instr(F64_numtype, MAX_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:403.5-403.31
  prod 0xA6 => BINOP_instr(F64_numtype, COPYSIGN_binop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:407.5-407.31
  prod 0xA7 => CVTOP_instr(I32_numtype, I64_numtype, WRAP_cvtop__)
  ;; ../specification/wasm-2.0/A-binary.spectec:408.5-408.36
  prod 0xA8 => CVTOP_instr(I32_numtype, F32_numtype, TRUNC_cvtop__(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:409.5-409.36
  prod 0xA9 => CVTOP_instr(I32_numtype, F32_numtype, TRUNC_cvtop__(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:410.5-410.36
  prod 0xAA => CVTOP_instr(I32_numtype, F64_numtype, TRUNC_cvtop__(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:411.5-411.36
  prod 0xAB => CVTOP_instr(I32_numtype, F64_numtype, TRUNC_cvtop__(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:412.5-412.37
  prod 0xAC => CVTOP_instr(I64_numtype, I32_numtype, EXTEND_cvtop__(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:413.5-413.37
  prod 0xAD => CVTOP_instr(I64_numtype, I32_numtype, EXTEND_cvtop__(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:414.5-414.36
  prod 0xAE => CVTOP_instr(I64_numtype, F32_numtype, TRUNC_cvtop__(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:415.5-415.36
  prod 0xAF => CVTOP_instr(I64_numtype, F32_numtype, TRUNC_cvtop__(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:416.5-416.36
  prod 0xB0 => CVTOP_instr(I64_numtype, F64_numtype, TRUNC_cvtop__(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:417.5-417.36
  prod 0xB1 => CVTOP_instr(I64_numtype, F64_numtype, TRUNC_cvtop__(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:418.5-418.38
  prod 0xB2 => CVTOP_instr(F32_numtype, I32_numtype, CONVERT_cvtop__(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:419.5-419.38
  prod 0xB3 => CVTOP_instr(F32_numtype, I32_numtype, CONVERT_cvtop__(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:420.5-420.38
  prod 0xB4 => CVTOP_instr(F32_numtype, I64_numtype, CONVERT_cvtop__(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:421.5-421.38
  prod 0xB5 => CVTOP_instr(F32_numtype, I64_numtype, CONVERT_cvtop__(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:422.5-422.33
  prod 0xB6 => CVTOP_instr(F32_numtype, F64_numtype, DEMOTE_cvtop__)
  ;; ../specification/wasm-2.0/A-binary.spectec:423.5-423.38
  prod 0xB7 => CVTOP_instr(F64_numtype, I32_numtype, CONVERT_cvtop__(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:424.5-424.38
  prod 0xB8 => CVTOP_instr(F64_numtype, I32_numtype, CONVERT_cvtop__(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:425.5-425.38
  prod 0xB9 => CVTOP_instr(F64_numtype, I64_numtype, CONVERT_cvtop__(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:426.5-426.38
  prod 0xBA => CVTOP_instr(F64_numtype, I64_numtype, CONVERT_cvtop__(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:427.5-427.34
  prod 0xBB => CVTOP_instr(F32_numtype, F64_numtype, PROMOTE_cvtop__)
  ;; ../specification/wasm-2.0/A-binary.spectec:428.5-428.38
  prod 0xBC => CVTOP_instr(I32_numtype, F32_numtype, REINTERPRET_cvtop__)
  ;; ../specification/wasm-2.0/A-binary.spectec:429.5-429.38
  prod 0xBD => CVTOP_instr(I64_numtype, F64_numtype, REINTERPRET_cvtop__)
  ;; ../specification/wasm-2.0/A-binary.spectec:430.5-430.38
  prod 0xBE => CVTOP_instr(F32_numtype, I32_numtype, REINTERPRET_cvtop__)
  ;; ../specification/wasm-2.0/A-binary.spectec:431.5-431.38
  prod 0xBF => CVTOP_instr(F64_numtype, I64_numtype, REINTERPRET_cvtop__)
  ;; ../specification/wasm-2.0/A-binary.spectec:435.5-435.47
  prod {{0xFC} {`%`_u32(0):Bu32}} => CVTOP_instr(I32_numtype, F32_numtype, TRUNC_SAT_cvtop__(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:436.5-436.47
  prod {{0xFC} {`%`_u32(1):Bu32}} => CVTOP_instr(I32_numtype, F32_numtype, TRUNC_SAT_cvtop__(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:437.5-437.47
  prod {{0xFC} {`%`_u32(2):Bu32}} => CVTOP_instr(I32_numtype, F64_numtype, TRUNC_SAT_cvtop__(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:438.5-438.47
  prod {{0xFC} {`%`_u32(3):Bu32}} => CVTOP_instr(I32_numtype, F64_numtype, TRUNC_SAT_cvtop__(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:439.5-439.47
  prod {{0xFC} {`%`_u32(4):Bu32}} => CVTOP_instr(I64_numtype, F32_numtype, TRUNC_SAT_cvtop__(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:440.5-440.47
  prod {{0xFC} {`%`_u32(5):Bu32}} => CVTOP_instr(I64_numtype, F32_numtype, TRUNC_SAT_cvtop__(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:441.5-441.47
  prod {{0xFC} {`%`_u32(6):Bu32}} => CVTOP_instr(I64_numtype, F64_numtype, TRUNC_SAT_cvtop__(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:442.5-442.47
  prod {{0xFC} {`%`_u32(7):Bu32}} => CVTOP_instr(I64_numtype, F64_numtype, TRUNC_SAT_cvtop__(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:446.5-446.32
  prod 0xC0 => UNOP_instr(I32_numtype, EXTEND_unop_(8))
  ;; ../specification/wasm-2.0/A-binary.spectec:447.5-447.33
  prod 0xC1 => UNOP_instr(I32_numtype, EXTEND_unop_(16))
  ;; ../specification/wasm-2.0/A-binary.spectec:448.5-448.32
  prod 0xC2 => UNOP_instr(I64_numtype, EXTEND_unop_(8))
  ;; ../specification/wasm-2.0/A-binary.spectec:449.5-449.33
  prod 0xC3 => UNOP_instr(I64_numtype, EXTEND_unop_(16))
  ;; ../specification/wasm-2.0/A-binary.spectec:450.5-450.33
  prod 0xC4 => UNOP_instr(I64_numtype, EXTEND_unop_(32))
  ;; ../specification/wasm-2.0/A-binary.spectec:460.5-460.44
  prod{ao : memarg} {{0xFD} {`%`_u32(0):Bu32} {ao:Bmemarg}} => VLOAD_instr(V128_vectype, ?(), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:461.5-461.62
  prod{ao : memarg} {{0xFD} {`%`_u32(1):Bu32} {ao:Bmemarg}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(8), 8, S_sx)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:462.5-462.62
  prod{ao : memarg} {{0xFD} {`%`_u32(2):Bu32} {ao:Bmemarg}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(8), 8, U_sx)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:463.5-463.63
  prod{ao : memarg} {{0xFD} {`%`_u32(3):Bu32} {ao:Bmemarg}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(16), 4, S_sx)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:464.5-464.63
  prod{ao : memarg} {{0xFD} {`%`_u32(4):Bu32} {ao:Bmemarg}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(16), 4, U_sx)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:465.5-465.63
  prod{ao : memarg} {{0xFD} {`%`_u32(5):Bu32} {ao:Bmemarg}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(32), 2, S_sx)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:466.5-466.63
  prod{ao : memarg} {{0xFD} {`%`_u32(6):Bu32} {ao:Bmemarg}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(32), 2, U_sx)), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:467.5-467.54
  prod{ao : memarg} {{0xFD} {`%`_u32(7):Bu32} {ao:Bmemarg}} => VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(8))), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:468.5-468.55
  prod{ao : memarg} {{0xFD} {`%`_u32(8):Bu32} {ao:Bmemarg}} => VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(16))), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:469.5-469.55
  prod{ao : memarg} {{0xFD} {`%`_u32(9):Bu32} {ao:Bmemarg}} => VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(32))), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:470.5-470.56
  prod{ao : memarg} {{0xFD} {`%`_u32(10):Bu32} {ao:Bmemarg}} => VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(64))), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:471.5-471.55
  prod{ao : memarg} {{0xFD} {`%`_u32(92):Bu32} {ao:Bmemarg}} => VLOAD_instr(V128_vectype, ?(ZERO_vloadop_(`%`_sz(32))), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:472.5-472.55
  prod{ao : memarg} {{0xFD} {`%`_u32(92):Bu32} {ao:Bmemarg}} => VLOAD_instr(V128_vectype, ?(ZERO_vloadop_(`%`_sz(64))), ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:473.5-473.46
  prod{ao : memarg} {{0xFD} {`%`_u32(11):Bu32} {ao:Bmemarg}} => VSTORE_instr(V128_vectype, ao)
  ;; ../specification/wasm-2.0/A-binary.spectec:474.5-474.65
  prod{ao : memarg, l : labelidx} {{0xFD} {`%`_u32(84):Bu32} {ao:Bmemarg} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VLOAD_LANE_instr(V128_vectype, `%`_sz(8), ao, `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:475.5-475.66
  prod{ao : memarg, l : labelidx} {{0xFD} {`%`_u32(85):Bu32} {ao:Bmemarg} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VLOAD_LANE_instr(V128_vectype, `%`_sz(16), ao, `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:476.5-476.66
  prod{ao : memarg, l : labelidx} {{0xFD} {`%`_u32(86):Bu32} {ao:Bmemarg} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VLOAD_LANE_instr(V128_vectype, `%`_sz(32), ao, `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:477.5-477.66
  prod{ao : memarg, l : labelidx} {{0xFD} {`%`_u32(87):Bu32} {ao:Bmemarg} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VLOAD_LANE_instr(V128_vectype, `%`_sz(64), ao, `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:478.5-478.66
  prod{ao : memarg, l : labelidx} {{0xFD} {`%`_u32(88):Bu32} {ao:Bmemarg} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VSTORE_LANE_instr(V128_vectype, `%`_sz(8), ao, `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:479.5-479.67
  prod{ao : memarg, l : labelidx} {{0xFD} {`%`_u32(89):Bu32} {ao:Bmemarg} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VSTORE_LANE_instr(V128_vectype, `%`_sz(16), ao, `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:480.5-480.67
  prod{ao : memarg, l : labelidx} {{0xFD} {`%`_u32(90):Bu32} {ao:Bmemarg} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VSTORE_LANE_instr(V128_vectype, `%`_sz(32), ao, `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:481.5-481.67
  prod{ao : memarg, l : labelidx} {{0xFD} {`%`_u32(91):Bu32} {ao:Bmemarg} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VSTORE_LANE_instr(V128_vectype, `%`_sz(64), ao, `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:485.5-485.76
  prod{b' : byte, b : byte} {{0xFD} {`%`_u32(12):Bu32} {b:Bbyte^16{}}} => VCONST_instr(V128_vectype, `%`_vec_(b'!`%`_byte.0))
    -- if ($ibytes_(128, `%`_iN(b'!`%`_byte.0)) = [b])
  ;; ../specification/wasm-2.0/A-binary.spectec:489.5-489.57
  prod{l : labelidx} {{0xFD} {`%`_u32(13):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx^16{}}} => VSHUFFLE_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), [`%`_laneidx(l!`%`_labelidx.0)])
  ;; ../specification/wasm-2.0/A-binary.spectec:493.5-493.59
  prod{l : labelidx} {{0xFD} {`%`_u32(21):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ?(S_sx), `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:494.5-494.59
  prod{l : labelidx} {{0xFD} {`%`_u32(22):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ?(U_sx), `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:495.5-495.57
  prod{l : labelidx} {{0xFD} {`%`_u32(23):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:496.5-496.59
  prod{l : labelidx} {{0xFD} {`%`_u32(24):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ?(S_sx), `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:497.5-497.59
  prod{l : labelidx} {{0xFD} {`%`_u32(25):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ?(U_sx), `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:498.5-498.57
  prod{l : labelidx} {{0xFD} {`%`_u32(26):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:499.5-499.57
  prod{l : labelidx} {{0xFD} {`%`_u32(27):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), ?(), `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:500.5-500.57
  prod{l : labelidx} {{0xFD} {`%`_u32(28):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:501.5-501.57
  prod{l : labelidx} {{0xFD} {`%`_u32(29):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), ?(), `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:502.5-502.57
  prod{l : labelidx} {{0xFD} {`%`_u32(30):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:503.5-503.57
  prod{l : labelidx} {{0xFD} {`%`_u32(31):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), ?(), `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:504.5-504.57
  prod{l : labelidx} {{0xFD} {`%`_u32(32):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:505.5-505.57
  prod{l : labelidx} {{0xFD} {`%`_u32(33):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), ?(), `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:506.5-506.57
  prod{l : labelidx} {{0xFD} {`%`_u32(34):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), `%`_laneidx(l!`%`_labelidx.0))
  ;; ../specification/wasm-2.0/A-binary.spectec:510.5-510.39
  prod {{0xFD} {`%`_u32(14):Bu32}} => VSWIZZLE_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))))
  ;; ../specification/wasm-2.0/A-binary.spectec:514.5-514.37
  prod {{0xFD} {`%`_u32(15):Bu32}} => VSPLAT_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)))
  ;; ../specification/wasm-2.0/A-binary.spectec:515.5-515.37
  prod {{0xFD} {`%`_u32(16):Bu32}} => VSPLAT_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)))
  ;; ../specification/wasm-2.0/A-binary.spectec:516.5-516.37
  prod {{0xFD} {`%`_u32(17):Bu32}} => VSPLAT_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)))
  ;; ../specification/wasm-2.0/A-binary.spectec:517.5-517.37
  prod {{0xFD} {`%`_u32(18):Bu32}} => VSPLAT_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)))
  ;; ../specification/wasm-2.0/A-binary.spectec:518.5-518.37
  prod {{0xFD} {`%`_u32(19):Bu32}} => VSPLAT_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)))
  ;; ../specification/wasm-2.0/A-binary.spectec:519.5-519.37
  prod {{0xFD} {`%`_u32(20):Bu32}} => VSPLAT_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)))
  ;; ../specification/wasm-2.0/A-binary.spectec:523.5-523.40
  prod {{0xFD} {`%`_u32(35):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), EQ_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:524.5-524.40
  prod {{0xFD} {`%`_u32(36):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), NE_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:525.5-525.44
  prod {{0xFD} {`%`_u32(37):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), LT_vrelop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:526.5-526.44
  prod {{0xFD} {`%`_u32(38):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), LT_vrelop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:527.5-527.44
  prod {{0xFD} {`%`_u32(39):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), GT_vrelop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:528.5-528.44
  prod {{0xFD} {`%`_u32(40):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), GT_vrelop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:529.5-529.44
  prod {{0xFD} {`%`_u32(41):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), LE_vrelop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:530.5-530.44
  prod {{0xFD} {`%`_u32(42):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), LE_vrelop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:531.5-531.44
  prod {{0xFD} {`%`_u32(43):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), GE_vrelop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:532.5-532.44
  prod {{0xFD} {`%`_u32(44):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), GE_vrelop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:536.5-536.40
  prod {{0xFD} {`%`_u32(45):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), EQ_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:537.5-537.40
  prod {{0xFD} {`%`_u32(46):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), NE_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:538.5-538.44
  prod {{0xFD} {`%`_u32(47):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), LT_vrelop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:539.5-539.44
  prod {{0xFD} {`%`_u32(48):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), LT_vrelop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:540.5-540.44
  prod {{0xFD} {`%`_u32(49):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), GT_vrelop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:541.5-541.44
  prod {{0xFD} {`%`_u32(50):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), GT_vrelop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:542.5-542.44
  prod {{0xFD} {`%`_u32(51):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), LE_vrelop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:543.5-543.44
  prod {{0xFD} {`%`_u32(52):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), LE_vrelop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:544.5-544.44
  prod {{0xFD} {`%`_u32(53):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), GE_vrelop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:545.5-545.44
  prod {{0xFD} {`%`_u32(54):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), GE_vrelop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:549.5-549.40
  prod {{0xFD} {`%`_u32(55):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), EQ_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:550.5-550.40
  prod {{0xFD} {`%`_u32(56):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), NE_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:551.5-551.44
  prod {{0xFD} {`%`_u32(57):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), LT_vrelop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:552.5-552.44
  prod {{0xFD} {`%`_u32(58):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), LT_vrelop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:553.5-553.44
  prod {{0xFD} {`%`_u32(59):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), GT_vrelop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:554.5-554.44
  prod {{0xFD} {`%`_u32(60):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), GT_vrelop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:555.5-555.44
  prod {{0xFD} {`%`_u32(61):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), LE_vrelop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:556.5-556.44
  prod {{0xFD} {`%`_u32(62):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), LE_vrelop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:557.5-557.44
  prod {{0xFD} {`%`_u32(63):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), GE_vrelop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:558.5-558.44
  prod {{0xFD} {`%`_u32(64):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), GE_vrelop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:562.5-562.41
  prod {{0xFD} {`%`_u32(214):Bu32}} => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), EQ_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:563.5-563.41
  prod {{0xFD} {`%`_u32(215):Bu32}} => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), NE_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:564.5-564.45
  prod {{0xFD} {`%`_u32(216):Bu32}} => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), LT_vrelop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:565.5-565.45
  prod {{0xFD} {`%`_u32(217):Bu32}} => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), GT_vrelop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:566.5-566.45
  prod {{0xFD} {`%`_u32(218):Bu32}} => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), LE_vrelop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:567.5-567.45
  prod {{0xFD} {`%`_u32(219):Bu32}} => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), GE_vrelop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:571.5-571.40
  prod {{0xFD} {`%`_u32(65):Bu32}} => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), EQ_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:572.5-572.40
  prod {{0xFD} {`%`_u32(66):Bu32}} => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), NE_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:573.5-573.40
  prod {{0xFD} {`%`_u32(67):Bu32}} => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), LT_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:574.5-574.40
  prod {{0xFD} {`%`_u32(68):Bu32}} => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), GT_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:575.5-575.40
  prod {{0xFD} {`%`_u32(69):Bu32}} => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), LE_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:576.5-576.40
  prod {{0xFD} {`%`_u32(70):Bu32}} => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), GE_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:580.5-580.40
  prod {{0xFD} {`%`_u32(71):Bu32}} => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), EQ_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:581.5-581.40
  prod {{0xFD} {`%`_u32(72):Bu32}} => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), NE_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:582.5-582.40
  prod {{0xFD} {`%`_u32(73):Bu32}} => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), LT_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:583.5-583.40
  prod {{0xFD} {`%`_u32(74):Bu32}} => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), GT_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:584.5-584.40
  prod {{0xFD} {`%`_u32(75):Bu32}} => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), LE_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:585.5-585.40
  prod {{0xFD} {`%`_u32(76):Bu32}} => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), GE_vrelop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:589.5-589.36
  prod {{0xFD} {`%`_u32(77):Bu32}} => VVUNOP_instr(V128_vectype, NOT_vvunop)
  ;; ../specification/wasm-2.0/A-binary.spectec:590.5-590.37
  prod {{0xFD} {`%`_u32(78):Bu32}} => VVBINOP_instr(V128_vectype, AND_vvbinop)
  ;; ../specification/wasm-2.0/A-binary.spectec:591.5-591.40
  prod {{0xFD} {`%`_u32(79):Bu32}} => VVBINOP_instr(V128_vectype, ANDNOT_vvbinop)
  ;; ../specification/wasm-2.0/A-binary.spectec:592.5-592.36
  prod {{0xFD} {`%`_u32(80):Bu32}} => VVBINOP_instr(V128_vectype, OR_vvbinop)
  ;; ../specification/wasm-2.0/A-binary.spectec:593.5-593.37
  prod {{0xFD} {`%`_u32(81):Bu32}} => VVBINOP_instr(V128_vectype, XOR_vvbinop)
  ;; ../specification/wasm-2.0/A-binary.spectec:594.5-594.44
  prod {{0xFD} {`%`_u32(82):Bu32}} => VVTERNOP_instr(V128_vectype, BITSELECT_vvternop)
  ;; ../specification/wasm-2.0/A-binary.spectec:595.5-595.43
  prod {{0xFD} {`%`_u32(83):Bu32}} => VVTESTOP_instr(V128_vectype, ANY_TRUE_vvtestop)
  ;; ../specification/wasm-2.0/A-binary.spectec:599.5-599.40
  prod {{0xFD} {`%`_u32(96):Bu32}} => VUNOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ABS_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:600.5-600.40
  prod {{0xFD} {`%`_u32(97):Bu32}} => VUNOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), NEG_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:601.5-601.43
  prod {{0xFD} {`%`_u32(98):Bu32}} => VUNOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), POPCNT_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:602.5-602.47
  prod {{0xFD} {`%`_u32(99):Bu32}} => VTESTOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ALL_TRUE_vtestop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:603.5-603.40
  prod {{0xFD} {`%`_u32(100):Bu32}} => VBITMASK_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))))
  ;; ../specification/wasm-2.0/A-binary.spectec:604.5-604.51
  prod {{0xFD} {`%`_u32(101):Bu32}} => VNARROW_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), S_sx)
  ;; ../specification/wasm-2.0/A-binary.spectec:605.5-605.51
  prod {{0xFD} {`%`_u32(102):Bu32}} => VNARROW_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), U_sx)
  ;; ../specification/wasm-2.0/A-binary.spectec:606.5-606.44
  prod {{0xFD} {`%`_u32(107):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), SHL_vshiftop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:607.5-607.48
  prod {{0xFD} {`%`_u32(108):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), SHR_vshiftop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:608.5-608.48
  prod {{0xFD} {`%`_u32(109):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), SHR_vshiftop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:609.5-609.42
  prod {{0xFD} {`%`_u32(110):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ADD_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:610.5-610.50
  prod {{0xFD} {`%`_u32(111):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ADD_SAT_vbinop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:611.5-611.50
  prod {{0xFD} {`%`_u32(112):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ADD_SAT_vbinop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:612.5-612.42
  prod {{0xFD} {`%`_u32(113):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), SUB_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:613.5-613.50
  prod {{0xFD} {`%`_u32(114):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), SUB_SAT_vbinop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:614.5-614.50
  prod {{0xFD} {`%`_u32(115):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), SUB_SAT_vbinop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:615.5-615.46
  prod {{0xFD} {`%`_u32(118):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), MIN_vbinop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:616.5-616.46
  prod {{0xFD} {`%`_u32(119):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), MIN_vbinop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:617.5-617.46
  prod {{0xFD} {`%`_u32(120):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), MAX_vbinop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:618.5-618.46
  prod {{0xFD} {`%`_u32(121):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), MAX_vbinop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:619.5-619.47
  prod {{0xFD} {`%`_u32(123):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), AVGRU_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:623.5-623.70
  prod {{0xFD} {`%`_u32(124):Bu32}} => VEXTUNOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTADD_PAIRWISE_vextunop__(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:624.5-624.70
  prod {{0xFD} {`%`_u32(125):Bu32}} => VEXTUNOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTADD_PAIRWISE_vextunop__(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:625.5-625.41
  prod {{0xFD} {`%`_u32(128):Bu32}} => VUNOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ABS_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:626.5-626.41
  prod {{0xFD} {`%`_u32(129):Bu32}} => VUNOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), NEG_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:627.5-627.54
  prod {{0xFD} {`%`_u32(130):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), Q15MULR_SATS_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:628.5-628.48
  prod {{0xFD} {`%`_u32(131):Bu32}} => VTESTOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ALL_TRUE_vtestop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:629.5-629.40
  prod {{0xFD} {`%`_u32(132):Bu32}} => VBITMASK_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))))
  ;; ../specification/wasm-2.0/A-binary.spectec:630.5-630.51
  prod {{0xFD} {`%`_u32(133):Bu32}} => VNARROW_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), S_sx)
  ;; ../specification/wasm-2.0/A-binary.spectec:631.5-631.51
  prod {{0xFD} {`%`_u32(134):Bu32}} => VNARROW_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), U_sx)
  ;; ../specification/wasm-2.0/A-binary.spectec:632.5-632.63
  prod {{0xFD} {`%`_u32(135):Bu32}} => VCVTOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), `%X%`_shape(I8_lanetype, `%`_dim(16)), EXTEND_vcvtop__(LOW_half, S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:633.5-633.64
  prod {{0xFD} {`%`_u32(136):Bu32}} => VCVTOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), `%X%`_shape(I8_lanetype, `%`_dim(16)), EXTEND_vcvtop__(HIGH_half, S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:634.5-634.63
  prod {{0xFD} {`%`_u32(137):Bu32}} => VCVTOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), `%X%`_shape(I8_lanetype, `%`_dim(16)), EXTEND_vcvtop__(LOW_half, U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:635.5-635.64
  prod {{0xFD} {`%`_u32(138):Bu32}} => VCVTOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), `%X%`_shape(I8_lanetype, `%`_dim(16)), EXTEND_vcvtop__(HIGH_half, U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:636.5-636.44
  prod {{0xFD} {`%`_u32(139):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), SHL_vshiftop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:637.5-637.48
  prod {{0xFD} {`%`_u32(140):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), SHR_vshiftop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:638.5-638.48
  prod {{0xFD} {`%`_u32(141):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), SHR_vshiftop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:639.5-639.42
  prod {{0xFD} {`%`_u32(142):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ADD_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:640.5-640.50
  prod {{0xFD} {`%`_u32(143):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ADD_SAT_vbinop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:641.5-641.50
  prod {{0xFD} {`%`_u32(144):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ADD_SAT_vbinop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:642.5-642.42
  prod {{0xFD} {`%`_u32(145):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), SUB_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:643.5-643.50
  prod {{0xFD} {`%`_u32(146):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), SUB_SAT_vbinop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:644.5-644.50
  prod {{0xFD} {`%`_u32(147):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), SUB_SAT_vbinop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:645.5-645.42
  prod {{0xFD} {`%`_u32(149):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), MUL_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:646.5-646.46
  prod {{0xFD} {`%`_u32(150):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), MIN_vbinop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:647.5-647.46
  prod {{0xFD} {`%`_u32(151):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), MIN_vbinop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:648.5-648.46
  prod {{0xFD} {`%`_u32(152):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), MAX_vbinop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:649.5-649.46
  prod {{0xFD} {`%`_u32(153):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), MAX_vbinop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:650.5-650.47
  prod {{0xFD} {`%`_u32(155):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), AVGRU_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:651.5-651.66
  prod {{0xFD} {`%`_u32(156):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTMUL_vextbinop__(LOW_half, S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:652.5-652.67
  prod {{0xFD} {`%`_u32(157):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTMUL_vextbinop__(HIGH_half, S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:653.5-653.66
  prod {{0xFD} {`%`_u32(158):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTMUL_vextbinop__(LOW_half, U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:654.5-654.67
  prod {{0xFD} {`%`_u32(159):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTMUL_vextbinop__(HIGH_half, U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:658.5-658.70
  prod {{0xFD} {`%`_u32(126):Bu32}} => VEXTUNOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTADD_PAIRWISE_vextunop__(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:659.5-659.70
  prod {{0xFD} {`%`_u32(127):Bu32}} => VEXTUNOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTADD_PAIRWISE_vextunop__(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:660.5-660.41
  prod {{0xFD} {`%`_u32(160):Bu32}} => VUNOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), ABS_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:661.5-661.41
  prod {{0xFD} {`%`_u32(161):Bu32}} => VUNOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), NEG_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:662.5-662.48
  prod {{0xFD} {`%`_u32(163):Bu32}} => VTESTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), ALL_TRUE_vtestop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:663.5-663.40
  prod {{0xFD} {`%`_u32(164):Bu32}} => VBITMASK_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))))
  ;; ../specification/wasm-2.0/A-binary.spectec:664.5-664.63
  prod {{0xFD} {`%`_u32(167):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(I16_lanetype, `%`_dim(8)), EXTEND_vcvtop__(LOW_half, S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:665.5-665.64
  prod {{0xFD} {`%`_u32(168):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(I16_lanetype, `%`_dim(8)), EXTEND_vcvtop__(HIGH_half, S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:666.5-666.63
  prod {{0xFD} {`%`_u32(169):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(I16_lanetype, `%`_dim(8)), EXTEND_vcvtop__(LOW_half, U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:667.5-667.64
  prod {{0xFD} {`%`_u32(170):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(I16_lanetype, `%`_dim(8)), EXTEND_vcvtop__(HIGH_half, U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:668.5-668.44
  prod {{0xFD} {`%`_u32(171):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), SHL_vshiftop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:669.5-669.48
  prod {{0xFD} {`%`_u32(172):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), SHR_vshiftop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:670.5-670.48
  prod {{0xFD} {`%`_u32(173):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), SHR_vshiftop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:671.5-671.42
  prod {{0xFD} {`%`_u32(174):Bu32}} => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), ADD_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:672.5-672.42
  prod {{0xFD} {`%`_u32(177):Bu32}} => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), SUB_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:673.5-673.42
  prod {{0xFD} {`%`_u32(181):Bu32}} => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), MUL_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:674.5-674.46
  prod {{0xFD} {`%`_u32(182):Bu32}} => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), MIN_vbinop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:675.5-675.46
  prod {{0xFD} {`%`_u32(183):Bu32}} => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), MIN_vbinop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:676.5-676.46
  prod {{0xFD} {`%`_u32(184):Bu32}} => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), MAX_vbinop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:677.5-677.46
  prod {{0xFD} {`%`_u32(185):Bu32}} => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), MAX_vbinop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:678.5-678.59
  prod {{0xFD} {`%`_u32(186):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), DOTS_vextbinop__)
  ;; ../specification/wasm-2.0/A-binary.spectec:679.5-679.66
  prod {{0xFD} {`%`_u32(188):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTMUL_vextbinop__(LOW_half, S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:680.5-680.67
  prod {{0xFD} {`%`_u32(189):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTMUL_vextbinop__(HIGH_half, S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:681.5-681.66
  prod {{0xFD} {`%`_u32(190):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTMUL_vextbinop__(LOW_half, U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:682.5-682.67
  prod {{0xFD} {`%`_u32(191):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTMUL_vextbinop__(HIGH_half, U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:686.5-686.41
  prod {{0xFD} {`%`_u32(192):Bu32}} => VUNOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), ABS_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:687.5-687.41
  prod {{0xFD} {`%`_u32(193):Bu32}} => VUNOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), NEG_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:688.5-688.48
  prod {{0xFD} {`%`_u32(195):Bu32}} => VTESTOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), ALL_TRUE_vtestop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:689.5-689.40
  prod {{0xFD} {`%`_u32(196):Bu32}} => VBITMASK_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))))
  ;; ../specification/wasm-2.0/A-binary.spectec:690.5-690.63
  prod {{0xFD} {`%`_u32(199):Bu32}} => VCVTOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), EXTEND_vcvtop__(LOW_half, S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:691.5-691.64
  prod {{0xFD} {`%`_u32(200):Bu32}} => VCVTOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), EXTEND_vcvtop__(HIGH_half, S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:692.5-692.63
  prod {{0xFD} {`%`_u32(201):Bu32}} => VCVTOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), EXTEND_vcvtop__(LOW_half, U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:693.5-693.64
  prod {{0xFD} {`%`_u32(202):Bu32}} => VCVTOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), EXTEND_vcvtop__(HIGH_half, U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:694.5-694.44
  prod {{0xFD} {`%`_u32(203):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), SHL_vshiftop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:695.5-695.48
  prod {{0xFD} {`%`_u32(204):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), SHR_vshiftop_(S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:696.5-696.48
  prod {{0xFD} {`%`_u32(205):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), SHR_vshiftop_(U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:697.5-697.42
  prod {{0xFD} {`%`_u32(206):Bu32}} => VBINOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), ADD_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:698.5-698.42
  prod {{0xFD} {`%`_u32(209):Bu32}} => VBINOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), SUB_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:699.5-699.42
  prod {{0xFD} {`%`_u32(213):Bu32}} => VBINOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), MUL_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:700.5-700.66
  prod {{0xFD} {`%`_u32(220):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), EXTMUL_vextbinop__(LOW_half, S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:701.5-701.67
  prod {{0xFD} {`%`_u32(221):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), EXTMUL_vextbinop__(HIGH_half, S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:702.5-702.66
  prod {{0xFD} {`%`_u32(222):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), EXTMUL_vextbinop__(LOW_half, U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:703.5-703.67
  prod {{0xFD} {`%`_u32(223):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), EXTMUL_vextbinop__(HIGH_half, U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:707.5-707.42
  prod {{0xFD} {`%`_u32(103):Bu32}} => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), CEIL_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:708.5-708.43
  prod {{0xFD} {`%`_u32(104):Bu32}} => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), FLOOR_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:709.5-709.43
  prod {{0xFD} {`%`_u32(105):Bu32}} => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), TRUNC_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:710.5-710.45
  prod {{0xFD} {`%`_u32(106):Bu32}} => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), NEAREST_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:711.5-711.41
  prod {{0xFD} {`%`_u32(224):Bu32}} => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), ABS_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:712.5-712.41
  prod {{0xFD} {`%`_u32(225):Bu32}} => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), NEG_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:713.5-713.42
  prod {{0xFD} {`%`_u32(227):Bu32}} => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), SQRT_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:714.5-714.42
  prod {{0xFD} {`%`_u32(228):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), ADD_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:715.5-715.42
  prod {{0xFD} {`%`_u32(229):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), SUB_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:716.5-716.42
  prod {{0xFD} {`%`_u32(230):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), MUL_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:717.5-717.42
  prod {{0xFD} {`%`_u32(231):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), DIV_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:718.5-718.42
  prod {{0xFD} {`%`_u32(232):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), MIN_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:719.5-719.42
  prod {{0xFD} {`%`_u32(233):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), MAX_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:720.5-720.43
  prod {{0xFD} {`%`_u32(234):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), PMIN_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:721.5-721.43
  prod {{0xFD} {`%`_u32(235):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), PMAX_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:725.5-725.42
  prod {{0xFD} {`%`_u32(116):Bu32}} => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), CEIL_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:726.5-726.43
  prod {{0xFD} {`%`_u32(117):Bu32}} => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), FLOOR_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:727.5-727.43
  prod {{0xFD} {`%`_u32(122):Bu32}} => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), TRUNC_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:728.5-728.45
  prod {{0xFD} {`%`_u32(148):Bu32}} => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), NEAREST_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:729.5-729.41
  prod {{0xFD} {`%`_u32(236):Bu32}} => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), ABS_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:730.5-730.41
  prod {{0xFD} {`%`_u32(237):Bu32}} => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), NEG_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:731.5-731.42
  prod {{0xFD} {`%`_u32(239):Bu32}} => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), SQRT_vunop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:732.5-732.42
  prod {{0xFD} {`%`_u32(240):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), ADD_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:733.5-733.42
  prod {{0xFD} {`%`_u32(241):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), SUB_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:734.5-734.42
  prod {{0xFD} {`%`_u32(242):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), MUL_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:735.5-735.42
  prod {{0xFD} {`%`_u32(243):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), DIV_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:736.5-736.42
  prod {{0xFD} {`%`_u32(244):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), MIN_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:737.5-737.42
  prod {{0xFD} {`%`_u32(245):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), MAX_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:738.5-738.43
  prod {{0xFD} {`%`_u32(246):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), PMIN_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:739.5-739.43
  prod {{0xFD} {`%`_u32(247):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), PMAX_vbinop_)
  ;; ../specification/wasm-2.0/A-binary.spectec:743.5-743.62
  prod {{0xFD} {`%`_u32(248):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F32_lanetype, `%`_dim(4)), TRUNC_SAT_vcvtop__(S_sx, ?()))
  ;; ../specification/wasm-2.0/A-binary.spectec:744.5-744.62
  prod {{0xFD} {`%`_u32(249):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F32_lanetype, `%`_dim(4)), TRUNC_SAT_vcvtop__(U_sx, ?()))
  ;; ../specification/wasm-2.0/A-binary.spectec:745.5-745.60
  prod {{0xFD} {`%`_u32(250):Bu32}} => VCVTOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), `%X%`_shape(I32_lanetype, `%`_dim(4)), CONVERT_vcvtop__(?(), S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:746.5-746.60
  prod {{0xFD} {`%`_u32(251):Bu32}} => VCVTOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), `%X%`_shape(I32_lanetype, `%`_dim(4)), CONVERT_vcvtop__(?(), U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:747.5-747.67
  prod {{0xFD} {`%`_u32(252):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F64_lanetype, `%`_dim(2)), TRUNC_SAT_vcvtop__(S_sx, ?(ZERO_zero)))
  ;; ../specification/wasm-2.0/A-binary.spectec:748.5-748.67
  prod {{0xFD} {`%`_u32(253):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F64_lanetype, `%`_dim(2)), TRUNC_SAT_vcvtop__(U_sx, ?(ZERO_zero)))
  ;; ../specification/wasm-2.0/A-binary.spectec:749.5-749.64
  prod {{0xFD} {`%`_u32(254):Bu32}} => VCVTOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), CONVERT_vcvtop__(?(LOW_half), S_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:750.5-750.64
  prod {{0xFD} {`%`_u32(255):Bu32}} => VCVTOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), CONVERT_vcvtop__(?(LOW_half), U_sx))
  ;; ../specification/wasm-2.0/A-binary.spectec:751.5-751.59
  prod {{0xFD} {`%`_u32(94):Bu32}} => VCVTOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), `%X%`_shape(F64_lanetype, `%`_dim(2)), DEMOTE_vcvtop__(ZERO_zero))
  ;; ../specification/wasm-2.0/A-binary.spectec:752.5-752.59
  prod {{0xFD} {`%`_u32(95):Bu32}} => VCVTOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), `%X%`_shape(F32_lanetype, `%`_dim(4)), PROMOTELOW_vcvtop__)
}

;; ../specification/wasm-2.0/A-binary.spectec:757.1-758.29
grammar Bexpr : expr
  ;; ../specification/wasm-2.0/A-binary.spectec:758.5-758.29
  prod{`in*` : instr*} {{in:Binstr*{in <- `in*`}} {0x0B}} => in*{in <- `in*`}

;; ../specification/wasm-2.0/A-binary.spectec:770.1-772.15
grammar Bsection_(N : N, syntax en, grammar BX : en*) : en*
  ;; ../specification/wasm-2.0/A-binary.spectec:771.5-771.55
  prod{`en*` : en*, len : nat} {{`%`_byte(N):Bbyte} {`%`_u32(len):Bu32} {en*{en <- `en*`}:BX}} => en*{en <- `en*`}
    -- if (len = 0)
  ;; ../specification/wasm-2.0/A-binary.spectec:772.5-772.15
  prod eps => []

;; ../specification/wasm-2.0/A-binary.spectec:777.1-778.23
grammar Bcustom : ()*
  ;; ../specification/wasm-2.0/A-binary.spectec:778.5-778.23
  prod {{Bname} {Bbyte*{}}} => []

;; ../specification/wasm-2.0/A-binary.spectec:780.1-781.32
grammar Bcustomsec : ()
  ;; ../specification/wasm-2.0/A-binary.spectec:781.5-781.32
  prod Bsection_(0, syntax (), grammar Bcustom) => ((), ()).1

;; ../specification/wasm-2.0/A-binary.spectec:786.1-787.28
grammar Btype : type
  ;; ../specification/wasm-2.0/A-binary.spectec:787.5-787.28
  prod{ft : functype} ft:Bfunctype => TYPE_type(ft)

;; ../specification/wasm-2.0/A-binary.spectec:789.1-790.42
grammar Btypesec : type*
  ;; ../specification/wasm-2.0/A-binary.spectec:790.5-790.42
  prod{`ty*` : type*} ty*{ty <- `ty*`}:Bsection_(1, syntax type, grammar Blist(syntax type, grammar Btype)) => ty*{ty <- `ty*`}

;; ../specification/wasm-2.0/A-binary.spectec:795.1-796.64
grammar Bimport : import
  ;; ../specification/wasm-2.0/A-binary.spectec:796.5-796.64
  prod{nm_1 : name, nm_2 : name, xt : externtype} {{nm_1:Bname} {nm_2:Bname} {xt:Bexterntype}} => IMPORT_import(nm_1, nm_2, xt)

;; ../specification/wasm-2.0/A-binary.spectec:798.1-799.44
grammar Bimportsec : import*
  ;; ../specification/wasm-2.0/A-binary.spectec:799.5-799.44
  prod{`im*` : import*} im*{im <- `im*`}:Bsection_(2, syntax import, grammar Blist(syntax import, grammar Bimport)) => im*{im <- `im*`}

;; ../specification/wasm-2.0/A-binary.spectec:804.1-805.43
grammar Bfuncsec : typeidx*
  ;; ../specification/wasm-2.0/A-binary.spectec:805.5-805.43
  prod{`x*` : idx*} x*{x <- `x*`}:Bsection_(3, syntax typeidx, grammar Blist(syntax typeidx, grammar Btypeidx)) => x*{x <- `x*`}

;; ../specification/wasm-2.0/A-binary.spectec:810.1-811.30
grammar Btable : table
  ;; ../specification/wasm-2.0/A-binary.spectec:811.5-811.30
  prod{tt : tabletype} tt:Btabletype => TABLE_table(tt)

;; ../specification/wasm-2.0/A-binary.spectec:813.1-814.45
grammar Btablesec : table*
  ;; ../specification/wasm-2.0/A-binary.spectec:814.5-814.45
  prod{`tab*` : table*} tab*{tab <- `tab*`}:Bsection_(4, syntax table, grammar Blist(syntax table, grammar Btable)) => tab*{tab <- `tab*`}

;; ../specification/wasm-2.0/A-binary.spectec:819.1-820.29
grammar Bmem : mem
  ;; ../specification/wasm-2.0/A-binary.spectec:820.5-820.29
  prod{mt : memtype} mt:Bmemtype => MEMORY_mem(mt)

;; ../specification/wasm-2.0/A-binary.spectec:822.1-823.43
grammar Bmemsec : mem*
  ;; ../specification/wasm-2.0/A-binary.spectec:823.5-823.43
  prod{`mem*` : mem*} mem*{mem <- `mem*`}:Bsection_(5, syntax mem, grammar Blist(syntax mem, grammar Bmem)) => mem*{mem <- `mem*`}

;; ../specification/wasm-2.0/A-binary.spectec:828.1-829.42
grammar Bglobal : global
  ;; ../specification/wasm-2.0/A-binary.spectec:829.5-829.42
  prod{gt : globaltype, e : expr} {{gt:Bglobaltype} {e:Bexpr}} => GLOBAL_global(gt, e)

;; ../specification/wasm-2.0/A-binary.spectec:831.1-832.48
grammar Bglobalsec : global*
  ;; ../specification/wasm-2.0/A-binary.spectec:832.5-832.48
  prod{`glob*` : global*} glob*{glob <- `glob*`}:Bsection_(6, syntax global, grammar Blist(syntax global, grammar Bglobal)) => glob*{glob <- `glob*`}

;; ../specification/wasm-2.0/A-binary.spectec:837.1-838.43
grammar Bexport : export
  ;; ../specification/wasm-2.0/A-binary.spectec:838.5-838.43
  prod{nm : name, xx : externidx} {{nm:Bname} {xx:Bexternidx}} => EXPORT_export(nm, xx)

;; ../specification/wasm-2.0/A-binary.spectec:840.1-841.44
grammar Bexportsec : export*
  ;; ../specification/wasm-2.0/A-binary.spectec:841.5-841.44
  prod{`ex*` : export*} ex*{ex <- `ex*`}:Bsection_(7, syntax export, grammar Blist(syntax export, grammar Bexport)) => ex*{ex <- `ex*`}

;; ../specification/wasm-2.0/A-binary.spectec:846.1-847.28
grammar Bstart : start*
  ;; ../specification/wasm-2.0/A-binary.spectec:847.5-847.28
  prod{x : idx} x:Bfuncidx => [START_start(x)]

;; ../specification/wasm-2.0/A-binary.spectec:851.1-852.60
grammar Bstartsec : start?
  ;; ../specification/wasm-2.0/A-binary.spectec:852.5-852.60
  prod{startopt : startopt} startopt:Bsection_(8, syntax start, grammar Bstart) => $opt_(syntax start, startopt)

;; ../specification/wasm-2.0/A-binary.spectec:857.1-858.20
grammar Belemkind : reftype
  ;; ../specification/wasm-2.0/A-binary.spectec:858.5-858.20
  prod 0x00 => FUNCREF_reftype

;; ../specification/wasm-2.0/A-binary.spectec:860.1-876.25
grammar Belem : elem
  ;; ../specification/wasm-2.0/A-binary.spectec:861.5-862.48
  prod{`y*` : idx*, e_o : expr} {{`%`_u32(0):Bu32} {e_o:Bexpr} {y*{y <- `y*`}:Blist(syntax funcidx, grammar Bfuncidx)}} => ELEM_elem(FUNCREF_reftype, [`REF.FUNC`_instr(y)*{y <- `y*`}], ACTIVE_elemmode(`%`_tableidx(0), e_o))
  ;; ../specification/wasm-2.0/A-binary.spectec:863.5-864.36
  prod{rt : reftype, `y*` : idx*} {{`%`_u32(1):Bu32} {rt:Belemkind} {y*{y <- `y*`}:Blist(syntax funcidx, grammar Bfuncidx)}} => ELEM_elem(rt, [`REF.FUNC`_instr(y)*{y <- `y*`}], PASSIVE_elemmode)
  ;; ../specification/wasm-2.0/A-binary.spectec:865.5-866.44
  prod{rt : reftype, `y*` : idx*, x : idx, expr : expr} {{`%`_u32(2):Bu32} {x:Btableidx} {expr:Bexpr} {rt:Belemkind} {y*{y <- `y*`}:Blist(syntax funcidx, grammar Bfuncidx)}} => ELEM_elem(rt, [`REF.FUNC`_instr(y)*{y <- `y*`}], ACTIVE_elemmode(x, expr))
  ;; ../specification/wasm-2.0/A-binary.spectec:867.5-868.36
  prod{rt : reftype, `y*` : idx*} {{`%`_u32(3):Bu32} {rt:Belemkind} {y*{y <- `y*`}:Blist(syntax funcidx, grammar Bfuncidx)}} => ELEM_elem(rt, [`REF.FUNC`_instr(y)*{y <- `y*`}], DECLARE_elemmode)
  ;; ../specification/wasm-2.0/A-binary.spectec:869.5-870.37
  prod{`e*` : expr*, e_o : expr} {{`%`_u32(4):Bu32} {e_o:Bexpr} {e*{e <- `e*`}:Blist(syntax expr, grammar Bexpr)}} => ELEM_elem(FUNCREF_reftype, e*{e <- `e*`}, ACTIVE_elemmode(`%`_tableidx(0), e_o))
  ;; ../specification/wasm-2.0/A-binary.spectec:871.5-872.25
  prod{rt : reftype, `e*` : expr*} {{`%`_u32(5):Bu32} {rt:Breftype} {e*{e <- `e*`}:Blist(syntax expr, grammar Bexpr)}} => ELEM_elem(rt, e*{e <- `e*`}, PASSIVE_elemmode)
  ;; ../specification/wasm-2.0/A-binary.spectec:873.5-874.38
  prod{`e*` : expr*, x : idx, expr : expr} {{`%`_u32(6):Bu32} {x:Btableidx} {expr:Bexpr} {e*{e <- `e*`}:Blist(syntax expr, grammar Bexpr)}} => ELEM_elem(FUNCREF_reftype, e*{e <- `e*`}, ACTIVE_elemmode(x, expr))
  ;; ../specification/wasm-2.0/A-binary.spectec:875.5-876.25
  prod{rt : reftype, `e*` : expr*} {{`%`_u32(7):Bu32} {rt:Breftype} {e*{e <- `e*`}:Blist(syntax expr, grammar Bexpr)}} => ELEM_elem(rt, e*{e <- `e*`}, DECLARE_elemmode)

;; ../specification/wasm-2.0/A-binary.spectec:878.1-879.46
grammar Belemsec : elem*
  ;; ../specification/wasm-2.0/A-binary.spectec:879.5-879.46
  prod{`elem*` : elem*} elem*{elem <- `elem*`}:Bsection_(9, syntax elem, grammar Blist(syntax elem, grammar Belem)) => elem*{elem <- `elem*`}

;; ../specification/wasm-2.0/A-binary.spectec:886.1-887.37
grammar Blocals : local*
  ;; ../specification/wasm-2.0/A-binary.spectec:887.5-887.37
  prod{t : valtype, n : n} {{`%`_u32(n):Bu32} {t:Bvaltype}} => LOCAL_local(t)^n{}

;; ../specification/wasm-2.0/A-binary.spectec:889.1-890.74
grammar Bfunc : code
  ;; ../specification/wasm-2.0/A-binary.spectec:890.5-890.74
  prod{`local**` : local**, expr : expr} {{local*{local <- `local*`}*{`local*` <- `local**`}:Blist(syntax local*, grammar Blocals)} {expr:Bexpr}} => ($concat_(syntax local, local*{local <- `local*`}*{`local*` <- `local**`}), expr)

;; ../specification/wasm-2.0/A-binary.spectec:892.1-893.55
grammar Bcode : code
  ;; ../specification/wasm-2.0/A-binary.spectec:893.5-893.55
  prod{code : code, len : nat} {{`%`_u32(len):Bu32} {code:Bfunc}} => code
    -- if (len = 0)

;; ../specification/wasm-2.0/A-binary.spectec:895.1-896.47
grammar Bcodesec : code*
  ;; ../specification/wasm-2.0/A-binary.spectec:896.5-896.47
  prod{`code*` : code*} code*{code <- `code*`}:Bsection_(10, syntax code, grammar Blist(syntax code, grammar Bcode)) => code*{code <- `code*`}

;; ../specification/wasm-2.0/A-binary.spectec:901.1-904.69
grammar Bdata : data
  ;; ../specification/wasm-2.0/A-binary.spectec:902.5-902.59
  prod{`b*` : byte*, e : expr} {{`%`_u32(0):Bu32} {e:Bexpr} {b*{b <- `b*`}:Blist(syntax byte, grammar Bbyte)}} => DATA_data(b*{b <- `b*`}, ACTIVE_datamode(`%`_memidx(0), e))
  ;; ../specification/wasm-2.0/A-binary.spectec:903.5-903.46
  prod{`b*` : byte*} {{`%`_u32(1):Bu32} {b*{b <- `b*`}:Blist(syntax byte, grammar Bbyte)}} => DATA_data(b*{b <- `b*`}, PASSIVE_datamode)
  ;; ../specification/wasm-2.0/A-binary.spectec:904.5-904.69
  prod{`b*` : byte*, x : idx, e : expr} {{`%`_u32(2):Bu32} {x:Bmemidx} {e:Bexpr} {b*{b <- `b*`}:Blist(syntax byte, grammar Bbyte)}} => DATA_data(b*{b <- `b*`}, ACTIVE_datamode(x, e))

;; ../specification/wasm-2.0/A-binary.spectec:906.1-907.47
grammar Bdatasec : data*
  ;; ../specification/wasm-2.0/A-binary.spectec:907.5-907.47
  prod{`data*` : data*} data*{data <- `data*`}:Bsection_(11, syntax data, grammar Blist(syntax data, grammar Bdata)) => data*{data <- `data*`}

;; ../specification/wasm-2.0/A-binary.spectec:912.1-913.16
grammar Bdatacnt : u32*
  ;; ../specification/wasm-2.0/A-binary.spectec:913.5-913.16
  prod{n : n} `%`_u32(n):Bu32 => [`%`_u32(n)]

;; ../specification/wasm-2.0/A-binary.spectec:917.1-918.53
grammar Bdatacntsec : u32?
  ;; ../specification/wasm-2.0/A-binary.spectec:918.5-918.53
  prod{nopt : nopt} nopt:Bsection_(12, syntax u32, grammar Bdatacnt) => $opt_(syntax u32, nopt)

;; ../specification/wasm-2.0/A-binary.spectec:923.1-942.45
grammar Bmodule : module
  ;; ../specification/wasm-2.0/A-binary.spectec:924.5-942.45
  prod{`type*` : type*, `import*` : import*, `func*` : func*, `global*` : global*, `table*` : table*, `mem*` : mem*, `elem*` : elem*, `data*` : data*, `start?` : start?, `export*` : export*, `typeidx*` : typeidx*, `n?` : n?, `expr*` : expr*, `local**` : local**} {{0x00} {0x61} {0x73} {0x6D} {`%`_u32(1):Bu32} {Bcustomsec*{}} {type*{type <- `type*`}:Btypesec} {Bcustomsec*{}} {import*{import <- `import*`}:Bimportsec} {Bcustomsec*{}} {typeidx*{typeidx <- `typeidx*`}:Bfuncsec} {Bcustomsec*{}} {table*{table <- `table*`}:Btablesec} {Bcustomsec*{}} {mem*{mem <- `mem*`}:Bmemsec} {Bcustomsec*{}} {global*{global <- `global*`}:Bglobalsec} {Bcustomsec*{}} {export*{export <- `export*`}:Bexportsec} {Bcustomsec*{}} {start?{start <- `start?`}:Bstartsec} {Bcustomsec*{}} {elem*{elem <- `elem*`}:Belemsec} {Bcustomsec*{}} {`%`_u32(n)?{n <- `n?`}:Bdatacntsec} {Bcustomsec*{}} {(local*{local <- `local*`}, expr)*{expr <- `expr*`, `local*` <- `local**`}:Bcodesec} {Bcustomsec*{}} {data*{data <- `data*`}:Bdatasec} {Bcustomsec*{}}} => MODULE_module(type*{type <- `type*`}, import*{import <- `import*`}, func*{func <- `func*`}, global*{global <- `global*`}, table*{table <- `table*`}, mem*{mem <- `mem*`}, elem*{elem <- `elem*`}, data*{data <- `data*`}, start?{start <- `start?`}, export*{export <- `export*`})
    -- (if (n = |data*{data <- `data*`}|))?{n <- `n?`}
    -- if ((n?{n <- `n?`} =/= ?()) \/ ($dataidx_funcs(func*{func <- `func*`}) = []))
    -- (if (func = FUNC_func(typeidx, local*{local <- `local*`}, expr)))*{expr <- `expr*`, func <- `func*`, `local*` <- `local**`, typeidx <- `typeidx*`}



;; test.spectec:5.1-5.32
syntax N = nat

;; test.spectec:6.1-6.32
syntax M = nat

;; test.spectec:7.1-7.32
syntax K = nat

;; test.spectec:8.1-8.32
syntax n = nat

;; test.spectec:9.1-9.32
syntax m = nat

;; test.spectec:22.1-22.25
def $min(nat : nat, nat : nat) : nat
  ;; test.spectec:23.1-23.36
  def $min{i : nat, j : nat}(i, j) = (if (i <= j) then i else j)

;; test.spectec:26.1-26.56
rec {

;; test.spectec:26.1-26.56
def $sum(nat*) : nat
  ;; test.spectec:27.1-27.18
  def $sum([]) = 0
  ;; test.spectec:28.1-28.35
  def $sum{n : n, `n'*` : n*}([n] ++ n'*{n' <- `n'*`}) = (n + $sum(n'*{n' <- `n'*`}))
}

;; test.spectec:30.1-30.57
rec {

;; test.spectec:30.1-30.57
def $prod(nat*) : nat
  ;; test.spectec:31.1-31.19
  def $prod([]) = 1
  ;; test.spectec:32.1-32.37
  def $prod{n : n, `n'*` : n*}([n] ++ n'*{n' <- `n'*`}) = (n * $prod(n'*{n' <- `n'*`}))
}

;; test.spectec:47.1-47.58
def $opt_(syntax X, X*) : X?
  ;; test.spectec:48.1-48.31
  def $opt_{syntax X}(syntax X, []) = ?()
  ;; test.spectec:49.1-49.27
  def $opt_{syntax X, w : X}(syntax X, [w]) = ?(w)

;; test.spectec:54.1-54.82
rec {

;; test.spectec:54.1-54.82
def $concat_(syntax X, X**) : X*
  ;; test.spectec:55.1-55.34
  def $concat_{syntax X}(syntax X, []) = []
  ;; test.spectec:56.1-56.64
  def $concat_{syntax X, `w*` : X*, `w'**` : X**}(syntax X, [w*{w <- `w*`}] ++ w'*{w' <- `w'*`}*{`w'*` <- `w'**`}) = w*{w <- `w*`} ++ $concat_(syntax X, w'*{w' <- `w'*`}*{`w'*` <- `w'**`})
}

;; test.spectec:58.1-58.89
rec {

;; test.spectec:58.1-58.89
def $concatn_(syntax X, X**, nat : nat) : X*
  ;; test.spectec:59.1-59.38
  def $concatn_{syntax X, n : n}(syntax X, [], n) = []
  ;; test.spectec:60.1-60.73
  def $concatn_{syntax X, n : n, `w*` : X*, `w'**` : X**}(syntax X, [w^n{w <- `w*`}] ++ w'^n{w' <- `w'*`}*{`w'*` <- `w'**`}, n) = w^n{w <- `w*`} ++ $concatn_(syntax X, w'^n{w' <- `w'*`}*{`w'*` <- `w'**`}, n)
}

;; test.spectec:62.1-62.58
def $concatopt_(syntax X, X?*) : X*
  ;; test.spectec:63.1-63.37
  def $concatopt_{syntax X}(syntax X, []) = []
  ;; test.spectec:64.1-64.67
  def $concatopt_{syntax X, `w?` : X?, `w'?*` : X?*}(syntax X, [w?{w <- `w?`}] ++ w'?{w' <- `w'?`}*{`w'?` <- `w'?*`}) = lift(w?{w <- `w?`}) ++ $concat_(syntax X, lift(w'?{w' <- `w'?`})*{`w'?` <- `w'?*`})

;; test.spectec:66.1-66.39
def $inv_concat_(syntax X, X*) : X**

;; test.spectec:69.1-69.45
def $inv_concatn_(syntax X, nat : nat, X*) : X**

;; test.spectec:75.1-75.78
rec {

;; test.spectec:75.1-75.78
def $disjoint_(syntax X, X*) : bool
  ;; test.spectec:76.1-76.37
  def $disjoint_{syntax X}(syntax X, []) = true
  ;; test.spectec:77.1-77.68
  def $disjoint_{syntax X, w : X, `w'*` : X*}(syntax X, [w] ++ w'*{w' <- `w'*`}) = (~ (w <- w'*{w' <- `w'*`}) /\ $disjoint_(syntax X, w'*{w' <- `w'*`}))
}

;; test.spectec:80.1-80.38
rec {

;; test.spectec:80.1-80.38
def $setminus1_(syntax X, X : X, X*) : X*
  ;; test.spectec:84.1-84.38
  def $setminus1_{syntax X, w : X}(syntax X, w, []) = [w]
  ;; test.spectec:85.1-85.78
  def $setminus1_{syntax X, w : X, w_1 : X, `w'*` : X*}(syntax X, w, [w_1] ++ w'*{w' <- `w'*`}) = (if (w = w_1) then [] else $setminus1_(syntax X, w, w'*{w' <- `w'*`}))
}

;; test.spectec:79.1-79.56
rec {

;; test.spectec:79.1-79.56
def $setminus_(syntax X, X*, X*) : X*
  ;; test.spectec:82.1-82.40
  def $setminus_{syntax X, `w*` : X*}(syntax X, [], w*{w <- `w*`}) = []
  ;; test.spectec:83.1-83.90
  def $setminus_{syntax X, w_1 : X, `w'*` : X*, `w*` : X*}(syntax X, [w_1] ++ w'*{w' <- `w'*`}, w*{w <- `w*`}) = $setminus1_(syntax X, w_1, w*{w <- `w*`}) ++ $setminus_(syntax X, w'*{w' <- `w'*`}, w*{w <- `w*`})
}

;; test.spectec:91.1-91.46
rec {

;; test.spectec:91.1-91.46
def $setproduct2_(syntax X, X : X, X**) : X**
  ;; test.spectec:97.1-97.44
  def $setproduct2_{syntax X, w_1 : X}(syntax X, w_1, []) = []
  ;; test.spectec:98.1-98.90
  def $setproduct2_{syntax X, w_1 : X, `w'*` : X*, `w**` : X**}(syntax X, w_1, [w'*{w' <- `w'*`}] ++ w*{w <- `w*`}*{`w*` <- `w**`}) = [[w_1] ++ w'*{w' <- `w'*`}] ++ $setproduct2_(syntax X, w_1, w*{w <- `w*`}*{`w*` <- `w**`})
}

;; test.spectec:90.1-90.47
rec {

;; test.spectec:90.1-90.47
def $setproduct1_(syntax X, X*, X**) : X**
  ;; test.spectec:95.1-95.46
  def $setproduct1_{syntax X, `w**` : X**}(syntax X, [], w*{w <- `w*`}*{`w*` <- `w**`}) = []
  ;; test.spectec:96.1-96.107
  def $setproduct1_{syntax X, w_1 : X, `w'*` : X*, `w**` : X**}(syntax X, [w_1] ++ w'*{w' <- `w'*`}, w*{w <- `w*`}*{`w*` <- `w**`}) = $setproduct2_(syntax X, w_1, w*{w <- `w*`}*{`w*` <- `w**`}) ++ $setproduct1_(syntax X, w'*{w' <- `w'*`}, w*{w <- `w*`}*{`w*` <- `w**`})
}

;; test.spectec:89.1-89.84
rec {

;; test.spectec:89.1-89.84
def $setproduct_(syntax X, X**) : X**
  ;; test.spectec:93.1-93.40
  def $setproduct_{syntax X}(syntax X, []) = [[]]
  ;; test.spectec:94.1-94.90
  def $setproduct_{syntax X, `w_1*` : X*, `w**` : X**}(syntax X, [w_1*{w_1 <- `w_1*`}] ++ w*{w <- `w*`}*{`w*` <- `w**`}) = $setproduct1_(syntax X, w_1*{w_1 <- `w_1*`}, $setproduct_(syntax X, w*{w <- `w*`}*{`w*` <- `w**`}))
}

;; test.spectec:111.1-111.29
def $ND : bool

;; test.spectec:126.1-126.37
syntax bit = 
  | `%`(i : nat)
    -- if ((i = 0) \/ (i = 1))

;; test.spectec:127.1-127.50
syntax byte = 
  | `%`(i : nat)
    -- if ((i >= 0) /\ (i <= 255))

;; test.spectec:129.1-130.25
syntax uN{N : N}(N) = 
  | `%`(i : nat)
    -- if ((i >= 0) /\ (i <= ((((2 ^ N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))

;; test.spectec:131.1-132.50
syntax sN{N : N}(N) = 
  | `%`(i : int)
    -- if ((((i >= - ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) /\ (i <= - (1 : nat <:> int))) \/ (i = (0 : nat <:> int))) \/ ((i >= + (1 : nat <:> int)) /\ (i <= (+ ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))

;; test.spectec:133.1-134.8
syntax iN{N : N}(N) = uN(N)

;; test.spectec:136.1-136.20
syntax u8 = uN(8)

;; test.spectec:137.1-137.21
syntax u16 = uN(16)

;; test.spectec:138.1-138.21
syntax u31 = uN(31)

;; test.spectec:139.1-139.21
syntax u32 = uN(32)

;; test.spectec:140.1-140.21
syntax u64 = uN(64)

;; test.spectec:141.1-141.21
syntax s33 = sN(33)

;; test.spectec:142.1-142.21
syntax i32 = iN(32)

;; test.spectec:143.1-143.21
syntax i64 = iN(64)

;; test.spectec:144.1-144.23
syntax i128 = iN(128)

;; test.spectec:151.1-151.35
def $signif(N : N) : nat
  ;; test.spectec:152.1-152.21
  def $signif(32) = 23
  ;; test.spectec:153.1-153.21
  def $signif(64) = 52

;; test.spectec:155.1-155.34
def $expon(N : N) : nat
  ;; test.spectec:156.1-156.19
  def $expon(32) = 8
  ;; test.spectec:157.1-157.20
  def $expon(64) = 11

;; test.spectec:159.1-159.47
def $M(N : N) : nat
  ;; test.spectec:160.1-160.23
  def $M{N : N}(N) = $signif(N)

;; test.spectec:162.1-162.47
def $E(N : N) : nat
  ;; test.spectec:163.1-163.22
  def $E{N : N}(N) = $expon(N)

;; test.spectec:169.1-169.47
syntax exp = int

;; test.spectec:170.1-174.84
syntax fNmag{N : N}(N) = 
  | NORM(m : m, exp : exp)
    -- if ((m < (2 ^ $M(N))) /\ ((((2 : nat <:> int) - ((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) <= exp) /\ (exp <= (((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))
  | SUBNORM(m : m) {exp : exp}
    -- if ((m < (2 ^ $M(N))) /\ (((2 : nat <:> int) - ((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) = exp))
  | INF
  | NAN(m : m)
    -- if ((1 <= m) /\ (m < (2 ^ $M(N))))

;; test.spectec:165.1-167.35
syntax fN{N : N}(N) = 
  | POS(fNmag(N))
  | NEG(fNmag(N))

;; test.spectec:176.1-176.21
syntax f32 = fN(32)

;; test.spectec:177.1-177.21
syntax f64 = fN(64)

;; test.spectec:179.1-179.39
def $fzero(N : N) : fN(N)
  ;; test.spectec:180.1-180.32
  def $fzero{N : N}(N) = POS_fN(SUBNORM_fNmag(0))

;; test.spectec:182.1-182.45
def $fnat(N : N, nat : nat) : fN(N)
  ;; test.spectec:183.1-183.33
  def $fnat{N : N, n : n}(N, n) = POS_fN(NORM_fNmag(n, (0 : nat <:> int)))

;; test.spectec:185.1-185.39
def $fone(N : N) : fN(N)
  ;; test.spectec:186.1-186.30
  def $fone{N : N}(N) = POS_fN(NORM_fNmag(1, (0 : nat <:> int)))

;; test.spectec:188.1-188.21
def $canon_(N : N) : nat
  ;; test.spectec:189.1-189.37
  def $canon_{N : N}(N) = (2 ^ ((($signif(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))

;; test.spectec:194.1-195.8
syntax vN{N : N}(N) = uN(N)

;; test.spectec:197.1-197.23
syntax v128 = vN(128)

;; test.spectec:203.1-203.49
syntax list{syntax X}(syntax X) = 
  | `%`(`X*` : X*)
    -- if (|X*{X <- `X*`}| < (2 ^ 32))

;; test.spectec:208.1-208.85
syntax char = 
  | `%`(i : nat)
    -- if (((i >= 0) /\ (i <= 55295)) \/ ((i >= 57344) /\ (i <= 1114111)))

;; test.spectec:5990.1-5990.39
def $cont(byte : byte) : nat
  ;; test.spectec:5991.1-5991.51
  def $cont{b : byte}(b) = (((b!`%`_byte.0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat)
    -- if ((128 < b!`%`_byte.0) /\ (b!`%`_byte.0 < 192))

;; test.spectec:210.1-210.25
rec {

;; test.spectec:210.1-210.25
def $utf8(char*) : byte*
  ;; test.spectec:5994.1-5994.44
  def $utf8{`ch*` : char*}(ch*{ch <- `ch*`}) = $concat_(syntax byte, $utf8([ch])*{ch <- `ch*`})
  ;; test.spectec:5995.1-5997.15
  def $utf8{ch : char, b : byte}([ch]) = [b]
    -- if (ch!`%`_char.0 < 128)
    -- if (`%`_byte(ch!`%`_char.0) = b)
  ;; test.spectec:5998.1-6000.46
  def $utf8{ch : char, b_1 : byte, b_2 : byte}([ch]) = [b_1 b_2]
    -- if ((128 <= ch!`%`_char.0) /\ (ch!`%`_char.0 < 2048))
    -- if (ch!`%`_char.0 = (((2 ^ 6) * (((b_1!`%`_byte.0 : nat <:> int) - (192 : nat <:> int)) : int <:> nat)) + $cont(b_2)))
  ;; test.spectec:6001.1-6003.64
  def $utf8{ch : char, b_1 : byte, b_2 : byte, b_3 : byte}([ch]) = [b_1 b_2 b_3]
    -- if (((2048 <= ch!`%`_char.0) /\ (ch!`%`_char.0 < 55296)) \/ ((57344 <= ch!`%`_char.0) /\ (ch!`%`_char.0 < 65536)))
    -- if (ch!`%`_char.0 = ((((2 ^ 12) * (((b_1!`%`_byte.0 : nat <:> int) - (224 : nat <:> int)) : int <:> nat)) + ((2 ^ 6) * $cont(b_2))) + $cont(b_3)))
  ;; test.spectec:6004.1-6006.82
  def $utf8{ch : char, b_1 : byte, b_2 : byte, b_3 : byte, b_4 : byte}([ch]) = [b_1 b_2 b_3 b_4]
    -- if ((65536 <= ch!`%`_char.0) /\ (ch!`%`_char.0 < 69632))
    -- if (ch!`%`_char.0 = (((((2 ^ 18) * (((b_1!`%`_byte.0 : nat <:> int) - (240 : nat <:> int)) : int <:> nat)) + ((2 ^ 12) * $cont(b_2))) + ((2 ^ 6) * $cont(b_3))) + $cont(b_4)))
}

;; test.spectec:212.1-212.70
syntax name = 
  | `%`(`char*` : char*)
    -- if (|$utf8(char*{char <- `char*`})| < (2 ^ 32))

;; test.spectec:219.1-219.36
syntax idx = u32

;; test.spectec:220.1-220.44
syntax laneidx = u8

;; test.spectec:222.1-222.45
syntax typeidx = idx

;; test.spectec:223.1-223.49
syntax funcidx = idx

;; test.spectec:224.1-224.49
syntax globalidx = idx

;; test.spectec:225.1-225.47
syntax tableidx = idx

;; test.spectec:226.1-226.46
syntax memidx = idx

;; test.spectec:227.1-227.43
syntax tagidx = idx

;; test.spectec:228.1-228.45
syntax elemidx = idx

;; test.spectec:229.1-229.45
syntax dataidx = idx

;; test.spectec:230.1-230.47
syntax labelidx = idx

;; test.spectec:231.1-231.47
syntax localidx = idx

;; test.spectec:232.1-232.47
syntax fieldidx = idx

;; test.spectec:234.1-235.79
syntax externidx = 
  | FUNC(funcidx : funcidx)
  | GLOBAL(globalidx : globalidx)
  | TABLE(tableidx : tableidx)
  | MEM(memidx : memidx)
  | TAG(tagidx : tagidx)

;; test.spectec:248.1-248.86
rec {

;; test.spectec:248.1-248.86
def $funcsxx(externidx*) : typeidx*
  ;; test.spectec:254.1-254.24
  def $funcsxx([]) = []
  ;; test.spectec:255.1-255.45
  def $funcsxx{x : idx, `xx*` : externidx*}([FUNC_externidx(x)] ++ xx*{xx <- `xx*`}) = [x] ++ $funcsxx(xx*{xx <- `xx*`})
  ;; test.spectec:256.1-256.58
  def $funcsxx{externidx : externidx, `xx*` : externidx*}([externidx] ++ xx*{xx <- `xx*`}) = $funcsxx(xx*{xx <- `xx*`})
}

;; test.spectec:249.1-249.88
rec {

;; test.spectec:249.1-249.88
def $globalsxx(externidx*) : globalidx*
  ;; test.spectec:258.1-258.26
  def $globalsxx([]) = []
  ;; test.spectec:259.1-259.51
  def $globalsxx{x : idx, `xx*` : externidx*}([GLOBAL_externidx(x)] ++ xx*{xx <- `xx*`}) = [x] ++ $globalsxx(xx*{xx <- `xx*`})
  ;; test.spectec:260.1-260.62
  def $globalsxx{externidx : externidx, `xx*` : externidx*}([externidx] ++ xx*{xx <- `xx*`}) = $globalsxx(xx*{xx <- `xx*`})
}

;; test.spectec:250.1-250.87
rec {

;; test.spectec:250.1-250.87
def $tablesxx(externidx*) : tableidx*
  ;; test.spectec:262.1-262.25
  def $tablesxx([]) = []
  ;; test.spectec:263.1-263.48
  def $tablesxx{x : idx, `xx*` : externidx*}([TABLE_externidx(x)] ++ xx*{xx <- `xx*`}) = [x] ++ $tablesxx(xx*{xx <- `xx*`})
  ;; test.spectec:264.1-264.60
  def $tablesxx{externidx : externidx, `xx*` : externidx*}([externidx] ++ xx*{xx <- `xx*`}) = $tablesxx(xx*{xx <- `xx*`})
}

;; test.spectec:251.1-251.85
rec {

;; test.spectec:251.1-251.85
def $memsxx(externidx*) : memidx*
  ;; test.spectec:266.1-266.23
  def $memsxx([]) = []
  ;; test.spectec:267.1-267.42
  def $memsxx{x : idx, `xx*` : externidx*}([MEM_externidx(x)] ++ xx*{xx <- `xx*`}) = [x] ++ $memsxx(xx*{xx <- `xx*`})
  ;; test.spectec:268.1-268.56
  def $memsxx{externidx : externidx, `xx*` : externidx*}([externidx] ++ xx*{xx <- `xx*`}) = $memsxx(xx*{xx <- `xx*`})
}

;; test.spectec:252.1-252.85
rec {

;; test.spectec:252.1-252.85
def $tagsxx(externidx*) : tagidx*
  ;; test.spectec:270.1-270.23
  def $tagsxx([]) = []
  ;; test.spectec:271.1-271.42
  def $tagsxx{x : idx, `xx*` : externidx*}([TAG_externidx(x)] ++ xx*{xx <- `xx*`}) = [x] ++ $tagsxx(xx*{xx <- `xx*`})
  ;; test.spectec:272.1-272.56
  def $tagsxx{externidx : externidx, `xx*` : externidx*}([externidx] ++ xx*{xx <- `xx*`}) = $tagsxx(xx*{xx <- `xx*`})
}

;; test.spectec:277.1-288.4
syntax free = 
{
  TYPES typeidx*,
  FUNCS funcidx*,
  GLOBALS globalidx*,
  TABLES tableidx*,
  MEMS memidx*,
  ELEMS elemidx*,
  DATAS dataidx*,
  LOCALS localidx*,
  LABELS labelidx*,
  TAGS tagidx*
}

;; test.spectec:291.1-291.28
def $free_opt(free?) : free
  ;; test.spectec:294.1-294.24
  def $free_opt(?()) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:295.1-295.27
  def $free_opt{free : free}(?(free)) = free

;; test.spectec:292.1-292.29
rec {

;; test.spectec:292.1-292.29
def $free_list(free*) : free
  ;; test.spectec:297.1-297.25
  def $free_list([]) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:298.1-298.57
  def $free_list{free : free, `free'*` : free*}([free] ++ free'*{free' <- `free'*`}) = free +++ $free_list(free'*{free' <- `free'*`})
}

;; test.spectec:301.1-301.34
def $free_typeidx(typeidx : typeidx) : free
  ;; test.spectec:313.1-313.45
  def $free_typeidx{typeidx : typeidx}(typeidx) = {TYPES [typeidx], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:302.1-302.34
def $free_funcidx(funcidx : funcidx) : free
  ;; test.spectec:314.1-314.45
  def $free_funcidx{funcidx : funcidx}(funcidx) = {TYPES [], FUNCS [funcidx], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:303.1-303.38
def $free_globalidx(globalidx : globalidx) : free
  ;; test.spectec:315.1-315.53
  def $free_globalidx{globalidx : globalidx}(globalidx) = {TYPES [], FUNCS [], GLOBALS [globalidx], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:304.1-304.36
def $free_tableidx(tableidx : tableidx) : free
  ;; test.spectec:316.1-316.49
  def $free_tableidx{tableidx : tableidx}(tableidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [tableidx], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:305.1-305.32
def $free_memidx(memidx : memidx) : free
  ;; test.spectec:317.1-317.41
  def $free_memidx{memidx : memidx}(memidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [memidx], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:306.1-306.34
def $free_elemidx(elemidx : elemidx) : free
  ;; test.spectec:318.1-318.45
  def $free_elemidx{elemidx : elemidx}(elemidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [elemidx], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:307.1-307.34
def $free_dataidx(dataidx : dataidx) : free
  ;; test.spectec:319.1-319.45
  def $free_dataidx{dataidx : dataidx}(dataidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [dataidx], LOCALS [], LABELS [], TAGS []}

;; test.spectec:308.1-308.36
def $free_localidx(localidx : localidx) : free
  ;; test.spectec:320.1-320.49
  def $free_localidx{localidx : localidx}(localidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [localidx], LABELS [], TAGS []}

;; test.spectec:309.1-309.36
def $free_labelidx(labelidx : labelidx) : free
  ;; test.spectec:321.1-321.49
  def $free_labelidx{labelidx : labelidx}(labelidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [labelidx], TAGS []}

;; test.spectec:311.1-311.32
def $free_tagidx(tagidx : tagidx) : free
  ;; test.spectec:322.1-322.41
  def $free_tagidx{tagidx : tagidx}(tagidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS [tagidx]}

;; test.spectec:310.1-310.38
def $free_externidx(externidx : externidx) : free
  ;; test.spectec:324.1-324.59
  def $free_externidx{funcidx : funcidx}(FUNC_externidx(funcidx)) = $free_funcidx(funcidx)
  ;; test.spectec:325.1-325.67
  def $free_externidx{globalidx : globalidx}(GLOBAL_externidx(globalidx)) = $free_globalidx(globalidx)
  ;; test.spectec:326.1-326.63
  def $free_externidx{tableidx : tableidx}(TABLE_externidx(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:327.1-327.55
  def $free_externidx{memidx : memidx}(MEM_externidx(memidx)) = $free_memidx(memidx)
  ;; test.spectec:328.1-328.55
  def $free_externidx{tagidx : tagidx}(TAG_externidx(tagidx)) = $free_tagidx(tagidx)

;; test.spectec:344.1-344.55
syntax null = 
  | NULL

;; test.spectec:346.1-347.14
syntax addrtype = 
  | I32
  | I64

;; test.spectec:349.1-350.26
syntax numtype = 
  | I32
  | I64
  | F32
  | F64

;; test.spectec:352.1-353.9
syntax vectype = 
  | V128

;; test.spectec:355.1-356.22
syntax consttype = 
  | I32
  | I64
  | F32
  | F64
  | V128

;; test.spectec:364.1-365.14
syntax absheaptype = 
  | ANY
  | EQ
  | I31
  | STRUCT
  | ARRAY
  | NONE
  | FUNC
  | NOFUNC
  | EXN
  | NOEXN
  | EXTERN
  | NOEXTERN
  | BOT

;; test.spectec:445.1-445.54
syntax mut = 
  | MUT

;; test.spectec:446.1-446.60
syntax final = 
  | FINAL

;; test.spectec:373.1-459.22
rec {

;; test.spectec:373.1-374.43
syntax typeuse = 
  | _IDX(typeidx : typeidx)
  | _DEF(rectype : rectype, n : n)
  | REC(n : n)

;; test.spectec:379.1-380.26
syntax heaptype = 
  | ANY
  | EQ
  | I31
  | STRUCT
  | ARRAY
  | NONE
  | FUNC
  | NOFUNC
  | EXN
  | NOEXN
  | EXTERN
  | NOEXTERN
  | BOT
  | _IDX(typeidx : typeidx)
  | _DEF(rectype : rectype, n : n)
  | REC(n : n)

;; test.spectec:387.1-388.14
syntax valtype = 
  | I32
  | I64
  | F32
  | F64
  | V128
  | REF(`null?` : null?, heaptype : heaptype)
  | BOT

;; test.spectec:428.1-428.66
syntax storagetype = 
  | I32
  | I64
  | F32
  | F64
  | V128
  | REF(`null?` : null?, heaptype : heaptype)
  | BOT
  | I8
  | I16

;; test.spectec:438.1-439.16
syntax resulttype = list(syntax valtype)

;; test.spectec:448.1-448.61
syntax fieldtype = 
  | `%%`(`mut?` : mut?, storagetype : storagetype)

;; test.spectec:450.1-453.34
syntax comptype = 
  | STRUCT(list(syntax fieldtype))
  | ARRAY(fieldtype : fieldtype)
  | `FUNC%->%`(resulttype : resulttype, resulttype : resulttype)

;; test.spectec:455.1-456.33
syntax subtype = 
  | SUB(`final?` : final?, `typeuse*` : typeuse*, comptype : comptype)

;; test.spectec:458.1-459.22
syntax rectype = 
  | REC(list(syntax subtype))
}

;; test.spectec:368.1-369.34
syntax deftype = 
  | _DEF(rectype : rectype, n : n)

;; test.spectec:376.1-377.42
syntax typevar = 
  | _IDX(typeidx : typeidx)
  | REC(n : n)

;; test.spectec:382.1-383.23
syntax reftype = 
  | REF(`null?` : null?, heaptype : heaptype)

;; test.spectec:391.1-391.55
syntax Inn = addrtype

;; test.spectec:392.1-392.56
syntax Fnn = 
  | F32
  | F64

;; test.spectec:393.1-393.54
syntax Vnn = vectype

;; test.spectec:394.1-394.42
syntax Cnn = 
  | I32
  | I64
  | F32
  | F64
  | V128

;; test.spectec:397.1-397.43
def $ANYREF : reftype
  ;; test.spectec:410.1-410.32
  def $ANYREF = REF_reftype(?(NULL_null), ANY_heaptype)

;; test.spectec:398.1-398.42
def $EQREF : reftype
  ;; test.spectec:411.1-411.31
  def $EQREF = REF_reftype(?(NULL_null), EQ_heaptype)

;; test.spectec:399.1-399.43
def $I31REF : reftype
  ;; test.spectec:412.1-412.32
  def $I31REF = REF_reftype(?(NULL_null), I31_heaptype)

;; test.spectec:400.1-400.46
def $STRUCTREF : reftype
  ;; test.spectec:413.1-413.35
  def $STRUCTREF = REF_reftype(?(NULL_null), STRUCT_heaptype)

;; test.spectec:401.1-401.45
def $ARRAYREF : reftype
  ;; test.spectec:414.1-414.34
  def $ARRAYREF = REF_reftype(?(NULL_null), ARRAY_heaptype)

;; test.spectec:402.1-402.44
def $FUNCREF : reftype
  ;; test.spectec:415.1-415.33
  def $FUNCREF = REF_reftype(?(NULL_null), FUNC_heaptype)

;; test.spectec:403.1-403.43
def $EXNREF : reftype
  ;; test.spectec:416.1-416.32
  def $EXNREF = REF_reftype(?(NULL_null), EXN_heaptype)

;; test.spectec:404.1-404.46
def $EXTERNREF : reftype
  ;; test.spectec:417.1-417.35
  def $EXTERNREF = REF_reftype(?(NULL_null), EXTERN_heaptype)

;; test.spectec:405.1-405.44
def $NULLREF : reftype
  ;; test.spectec:418.1-418.33
  def $NULLREF = REF_reftype(?(NULL_null), NONE_heaptype)

;; test.spectec:406.1-406.50
def $NULLFUNCREF : reftype
  ;; test.spectec:419.1-419.37
  def $NULLFUNCREF = REF_reftype(?(NULL_null), NOFUNC_heaptype)

;; test.spectec:407.1-407.49
def $NULLEXNREF : reftype
  ;; test.spectec:420.1-420.36
  def $NULLEXNREF = REF_reftype(?(NULL_null), NOEXN_heaptype)

;; test.spectec:408.1-408.54
def $NULLEXTERNREF : reftype
  ;; test.spectec:421.1-421.41
  def $NULLEXTERNREF = REF_reftype(?(NULL_null), NOEXTERN_heaptype)

;; test.spectec:426.1-426.52
syntax packtype = 
  | I8
  | I16

;; test.spectec:427.1-427.60
syntax lanetype = 
  | I32
  | I64
  | F32
  | F64
  | I8
  | I16

;; test.spectec:431.1-431.55
syntax Pnn = packtype

;; test.spectec:432.1-432.56
syntax Jnn = 
  | I32
  | I64
  | I8
  | I16

;; test.spectec:433.1-433.55
syntax Lnn = lanetype

;; test.spectec:464.1-464.74
syntax limits = 
  | `[%..%]`(u64 : u64, `u64?` : u64?)

;; test.spectec:466.1-466.47
syntax tagtype = typeuse

;; test.spectec:467.1-467.58
syntax globaltype = 
  | `%%`(`mut?` : mut?, valtype : valtype)

;; test.spectec:468.1-468.63
syntax memtype = 
  | `%%PAGE`(addrtype : addrtype, limits : limits)

;; test.spectec:469.1-469.67
syntax tabletype = 
  | `%%%`(addrtype : addrtype, limits : limits, reftype : reftype)

;; test.spectec:470.1-470.64
syntax datatype = 
  | OK

;; test.spectec:471.1-471.52
syntax elemtype = reftype

;; test.spectec:473.1-474.83
syntax externtype = 
  | TAG(tagtype : tagtype)
  | GLOBAL(globaltype : globaltype)
  | MEM(memtype : memtype)
  | TABLE(tabletype : tabletype)
  | FUNC(typeuse : typeuse)

;; test.spectec:476.1-477.47
syntax moduletype = 
  | `%->%`(`externtype*` : externtype*, `externtype*` : externtype*)

;; test.spectec:515.1-515.65
def $IN(N : N) : Inn
  ;; test.spectec:516.1-516.18
  def $IN(32) = I32_Inn
  ;; test.spectec:517.1-517.18
  def $IN(64) = I64_Inn

;; test.spectec:519.1-519.65
def $FN(N : N) : Fnn
  ;; test.spectec:520.1-520.18
  def $FN(32) = F32_Fnn
  ;; test.spectec:521.1-521.18
  def $FN(64) = F64_Fnn

;; test.spectec:523.1-523.65
def $JN(N : N) : Jnn
  ;; test.spectec:524.1-524.16
  def $JN(8) = I8_Jnn
  ;; test.spectec:525.1-525.18
  def $JN(16) = I16_Jnn
  ;; test.spectec:526.1-526.18
  def $JN(32) = I32_Jnn
  ;; test.spectec:527.1-527.18
  def $JN(64) = I64_Jnn

;; test.spectec:532.1-532.46
def $size(numtype : numtype) : nat
  ;; test.spectec:541.1-541.20
  def $size(I32_numtype) = 32
  ;; test.spectec:542.1-542.20
  def $size(I64_numtype) = 64
  ;; test.spectec:543.1-543.20
  def $size(F32_numtype) = 32
  ;; test.spectec:544.1-544.20
  def $size(F64_numtype) = 64

;; test.spectec:533.1-533.46
def $vsize(vectype : vectype) : nat
  ;; test.spectec:546.1-546.23
  def $vsize(V128_vectype) = 128

;; test.spectec:534.1-534.46
def $psize(packtype : packtype) : nat
  ;; test.spectec:548.1-548.19
  def $psize(I8_packtype) = 8
  ;; test.spectec:549.1-549.21
  def $psize(I16_packtype) = 16

;; test.spectec:535.1-535.46
def $lsize(lanetype : lanetype) : nat
  ;; test.spectec:551.1-551.37
  def $lsize{numtype : numtype}((numtype : numtype <: lanetype)) = $size(numtype)
  ;; test.spectec:552.1-552.40
  def $lsize{packtype : packtype}((packtype : packtype <: lanetype)) = $psize(packtype)

;; test.spectec:536.1-536.60
def $zsize(storagetype : storagetype) : nat
  ;; test.spectec:554.1-554.37
  def $zsize{numtype : numtype}((numtype : numtype <: storagetype)) = $size(numtype)
  ;; test.spectec:555.1-555.38
  def $zsize{vectype : vectype}((vectype : vectype <: storagetype)) = $vsize(vectype)
  ;; test.spectec:556.1-556.40
  def $zsize{packtype : packtype}((packtype : packtype <: storagetype)) = $psize(packtype)

;; test.spectec:537.1-537.71
def $isize(Inn : Inn) : nat
  ;; test.spectec:558.1-558.29
  def $isize{Inn : Inn}(Inn) = $size((Inn : addrtype <: numtype))

;; test.spectec:538.1-538.71
def $jsize(Jnn : Jnn) : nat
  ;; test.spectec:560.1-560.30
  def $jsize{Jnn : Jnn}(Jnn) = $lsize((Jnn : Jnn <: lanetype))

;; test.spectec:539.1-539.71
def $fsize(Fnn : Fnn) : nat
  ;; test.spectec:559.1-559.29
  def $fsize{Fnn : Fnn}(Fnn) = $size((Fnn : Fnn <: numtype))

;; test.spectec:562.1-562.40
def $inv_isize(nat : nat) : Inn
  ;; test.spectec:566.1-566.25
  def $inv_isize(32) = I32_Inn
  ;; test.spectec:567.1-567.25
  def $inv_isize(64) = I64_Inn

;; test.spectec:563.1-563.40
def $inv_jsize(nat : nat) : Jnn
  ;; test.spectec:570.1-570.24
  def $inv_jsize(8) = I8_Jnn
  ;; test.spectec:571.1-571.25
  def $inv_jsize(16) = I16_Jnn
  ;; test.spectec:572.1-572.34
  def $inv_jsize{n : n}(n) = ($inv_isize(n) : addrtype <: Jnn)

;; test.spectec:564.1-564.40
def $inv_fsize(nat : nat) : Fnn
  ;; test.spectec:568.1-568.25
  def $inv_fsize(32) = F32_Fnn
  ;; test.spectec:569.1-569.25
  def $inv_fsize(64) = F64_Fnn

;; test.spectec:575.1-575.63
def $sizenn(numtype : numtype) : nat
  ;; test.spectec:578.1-578.28
  def $sizenn{nt : numtype}(nt) = $size(nt)

;; test.spectec:576.1-576.63
def $sizenn1(numtype : numtype) : nat
  ;; test.spectec:579.1-579.29
  def $sizenn1{nt : numtype}(nt) = $size(nt)

;; test.spectec:577.1-577.63
def $sizenn2(numtype : numtype) : nat
  ;; test.spectec:580.1-580.29
  def $sizenn2{nt : numtype}(nt) = $size(nt)

;; test.spectec:582.1-582.63
def $vsizenn(vectype : vectype) : nat
  ;; test.spectec:583.1-583.30
  def $vsizenn{vt : vectype}(vt) = $vsize(vt)

;; test.spectec:585.1-585.63
def $psizenn(packtype : packtype) : nat
  ;; test.spectec:586.1-586.30
  def $psizenn{pt : packtype}(pt) = $psize(pt)

;; test.spectec:588.1-588.63
def $lsizenn(lanetype : lanetype) : nat
  ;; test.spectec:591.1-591.30
  def $lsizenn{lt : lanetype}(lt) = $lsize(lt)

;; test.spectec:589.1-589.63
def $lsizenn1(lanetype : lanetype) : nat
  ;; test.spectec:592.1-592.31
  def $lsizenn1{lt : lanetype}(lt) = $lsize(lt)

;; test.spectec:590.1-590.63
def $lsizenn2(lanetype : lanetype) : nat
  ;; test.spectec:593.1-593.31
  def $lsizenn2{lt : lanetype}(lt) = $lsize(lt)

;; test.spectec:595.1-595.83
def $jsizenn(Jnn : Jnn) : nat
  ;; test.spectec:596.1-596.32
  def $jsizenn{Jnn : Jnn}(Jnn) = $lsize((Jnn : Jnn <: lanetype))

;; test.spectec:598.1-598.42
def $inv_jsizenn(nat : nat) : Jnn
  ;; test.spectec:599.1-599.36
  def $inv_jsizenn{n : n}(n) = $inv_jsize(n)

;; test.spectec:604.1-604.56
def $lunpack(lanetype : lanetype) : numtype
  ;; test.spectec:605.1-605.32
  def $lunpack{numtype : numtype}((numtype : numtype <: lanetype)) = numtype
  ;; test.spectec:606.1-606.29
  def $lunpack{packtype : packtype}((packtype : packtype <: lanetype)) = I32_numtype

;; test.spectec:608.1-608.35
def $unpack(storagetype : storagetype) : valtype
  ;; test.spectec:609.1-609.31
  def $unpack{valtype : valtype}((valtype : valtype <: storagetype)) = valtype
  ;; test.spectec:610.1-610.28
  def $unpack{packtype : packtype}((packtype : packtype <: storagetype)) = I32_valtype

;; test.spectec:612.1-612.73
def $nunpack(storagetype : storagetype) : numtype
  ;; test.spectec:613.1-613.32
  def $nunpack{numtype : numtype}((numtype : numtype <: storagetype)) = numtype
  ;; test.spectec:614.1-614.29
  def $nunpack{packtype : packtype}((packtype : packtype <: storagetype)) = I32_numtype

;; test.spectec:616.1-616.73
def $vunpack(storagetype : storagetype) : vectype
  ;; test.spectec:617.1-617.32
  def $vunpack{vectype : vectype}((vectype : vectype <: storagetype)) = vectype

;; test.spectec:619.1-619.74
def $cunpack(storagetype : storagetype) : consttype
  ;; test.spectec:620.1-620.36
  def $cunpack{consttype : consttype}((consttype : consttype <: storagetype)) = consttype
  ;; test.spectec:621.1-621.29
  def $cunpack{packtype : packtype}((packtype : packtype <: storagetype)) = I32_consttype
  ;; test.spectec:622.1-622.44
  def $cunpack{lanetype : lanetype}((lanetype : lanetype <: storagetype)) = ($lunpack(lanetype) : numtype <: consttype)

;; test.spectec:627.1-627.90
def $minat(addrtype : addrtype, addrtype : addrtype) : addrtype
  ;; test.spectec:628.1-628.64
  def $minat{at_1 : addrtype, at_2 : addrtype}(at_1, at_2) = (if ($size((at_1 : addrtype <: numtype)) <= $size((at_2 : addrtype <: numtype))) then at_1 else at_2)

;; test.spectec:631.1-631.82
def $diffrt(reftype : reftype, reftype : reftype) : reftype
  ;; test.spectec:632.1-632.62
  def $diffrt{`null_1?` : null?, ht_1 : heaptype, ht_2 : heaptype}(REF_reftype(null_1?{null_1 <- `null_1?`}, ht_1), REF_reftype(?(NULL_null), ht_2)) = REF_reftype(?(), ht_1)
  ;; test.spectec:633.1-633.65
  def $diffrt{`null_1?` : null?, ht_1 : heaptype, ht_2 : heaptype}(REF_reftype(null_1?{null_1 <- `null_1?`}, ht_1), REF_reftype(?(), ht_2)) = REF_reftype(null_1?{null_1 <- `null_1?`}, ht_1)

;; test.spectec:636.1-636.63
def $as_deftype(typeuse : typeuse) : deftype
  ;; test.spectec:637.1-637.25
  def $as_deftype{dt : deftype}((dt : deftype <: typeuse)) = dt

;; test.spectec:644.1-644.87
rec {

;; test.spectec:644.1-644.87
def $tagsxt(externtype*) : tagtype*
  ;; test.spectec:650.1-650.23
  def $tagsxt([]) = []
  ;; test.spectec:651.1-651.44
  def $tagsxt{jt : tagtype, `xt*` : externtype*}([TAG_externtype(jt)] ++ xt*{xt <- `xt*`}) = [jt] ++ $tagsxt(xt*{xt <- `xt*`})
  ;; test.spectec:652.1-652.57
  def $tagsxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $tagsxt(xt*{xt <- `xt*`})
}

;; test.spectec:645.1-645.90
rec {

;; test.spectec:645.1-645.90
def $globalsxt(externtype*) : globaltype*
  ;; test.spectec:654.1-654.26
  def $globalsxt([]) = []
  ;; test.spectec:655.1-655.53
  def $globalsxt{gt : globaltype, `xt*` : externtype*}([GLOBAL_externtype(gt)] ++ xt*{xt <- `xt*`}) = [gt] ++ $globalsxt(xt*{xt <- `xt*`})
  ;; test.spectec:656.1-656.63
  def $globalsxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $globalsxt(xt*{xt <- `xt*`})
}

;; test.spectec:646.1-646.87
rec {

;; test.spectec:646.1-646.87
def $memsxt(externtype*) : memtype*
  ;; test.spectec:658.1-658.23
  def $memsxt([]) = []
  ;; test.spectec:659.1-659.44
  def $memsxt{mt : memtype, `xt*` : externtype*}([MEM_externtype(mt)] ++ xt*{xt <- `xt*`}) = [mt] ++ $memsxt(xt*{xt <- `xt*`})
  ;; test.spectec:660.1-660.57
  def $memsxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $memsxt(xt*{xt <- `xt*`})
}

;; test.spectec:647.1-647.89
rec {

;; test.spectec:647.1-647.89
def $tablesxt(externtype*) : tabletype*
  ;; test.spectec:662.1-662.25
  def $tablesxt([]) = []
  ;; test.spectec:663.1-663.50
  def $tablesxt{tt : tabletype, `xt*` : externtype*}([TABLE_externtype(tt)] ++ xt*{xt <- `xt*`}) = [tt] ++ $tablesxt(xt*{xt <- `xt*`})
  ;; test.spectec:664.1-664.61
  def $tablesxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $tablesxt(xt*{xt <- `xt*`})
}

;; test.spectec:648.1-648.88
rec {

;; test.spectec:648.1-648.88
def $funcsxt(externtype*) : deftype*
  ;; test.spectec:666.1-666.24
  def $funcsxt([]) = []
  ;; test.spectec:667.1-667.47
  def $funcsxt{dt : deftype, `xt*` : externtype*}([FUNC_externtype((dt : deftype <: typeuse))] ++ xt*{xt <- `xt*`}) = [dt] ++ $funcsxt(xt*{xt <- `xt*`})
  ;; test.spectec:668.1-668.59
  def $funcsxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $funcsxt(xt*{xt <- `xt*`})
}

;; test.spectec:673.1-673.126
rec {

;; test.spectec:673.1-673.126
def $subst_typevar(typevar : typevar, typevar*, typeuse*) : typeuse
  ;; test.spectec:701.1-701.38
  def $subst_typevar{tv : typevar}(tv, [], []) = (tv : typevar <: typeuse)
  ;; test.spectec:702.1-702.95
  def $subst_typevar{tv : typevar, tv_1 : typevar, `tv'*` : typevar*, tu_1 : typeuse, `tu'*` : typeuse*}(tv, [tv_1] ++ tv'*{tv' <- `tv'*`}, [tu_1] ++ tu'*{tu' <- `tu'*`}) = (if (tv = tv_1) then tu_1 else $subst_typevar(tv, tv'*{tv' <- `tv'*`}, tu'*{tu' <- `tu'*`}))
}

;; test.spectec:737.1-737.87
rec {

;; test.spectec:737.1-737.87
def $minus_recs(typevar*, typeuse*) : (typevar*, typeuse*)
  ;; test.spectec:738.1-738.39
  def $minus_recs([], []) = ([], [])
  ;; test.spectec:739.1-739.63
  def $minus_recs{n : n, `tv*` : typevar*, tu_1 : typeuse, `tu*` : typeuse*}([REC_typevar(n)] ++ tv*{tv <- `tv*`}, [tu_1] ++ tu*{tu <- `tu*`}) = $minus_recs(tv*{tv <- `tv*`}, tu*{tu <- `tu*`})
  ;; test.spectec:740.1-741.45
  def $minus_recs{x : idx, `tv*` : typevar*, tu_1 : typeuse, `tu*` : typeuse*, `tv'*` : typevar*, `tu'*` : typeuse*}([_IDX_typevar(x)] ++ tv*{tv <- `tv*`}, [tu_1] ++ tu*{tu <- `tu*`}) = ([_IDX_typevar(x)] ++ tv'*{tv' <- `tv'*`}, [tu_1] ++ tu'*{tu' <- `tu'*`})
    -- if ((tv'*{tv' <- `tv'*`}, tu'*{tu' <- `tu'*`}) = $minus_recs(tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))
}

;; test.spectec:683.1-683.112
def $subst_packtype(packtype : packtype, typevar*, typeuse*) : packtype
  ;; test.spectec:723.1-723.39
  def $subst_packtype{pt : packtype, `tv*` : typevar*, `tu*` : typeuse*}(pt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = pt

;; test.spectec:677.1-677.112
def $subst_numtype(numtype : numtype, typevar*, typeuse*) : numtype
  ;; test.spectec:709.1-709.38
  def $subst_numtype{nt : numtype, `tv*` : typevar*, `tu*` : typeuse*}(nt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = nt

;; test.spectec:678.1-678.112
def $subst_vectype(vectype : vectype, typevar*, typeuse*) : vectype
  ;; test.spectec:710.1-710.38
  def $subst_vectype{vt : vectype, `tv*` : typevar*, `tu*` : typeuse*}(vt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = vt

;; test.spectec:674.1-690.112
rec {

;; test.spectec:674.1-674.112
def $subst_typeuse(typeuse : typeuse, typevar*, typeuse*) : typeuse
  ;; test.spectec:705.1-705.66
  def $subst_typeuse{tv' : typevar, `tv*` : typevar*, `tu*` : typeuse*}((tv' : typevar <: typeuse), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = $subst_typevar(tv', tv*{tv <- `tv*`}, tu*{tu <- `tu*`})
  ;; test.spectec:706.1-706.64
  def $subst_typeuse{dt : deftype, `tv*` : typevar*, `tu*` : typeuse*}((dt : deftype <: typeuse), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_deftype(dt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : deftype <: typeuse)

;; test.spectec:679.1-679.112
def $subst_heaptype(heaptype : heaptype, typevar*, typeuse*) : heaptype
  ;; test.spectec:712.1-712.67
  def $subst_heaptype{tv' : typevar, `tv*` : typevar*, `tu*` : typeuse*}((tv' : typevar <: heaptype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_typevar(tv', tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : typeuse <: heaptype)
  ;; test.spectec:713.1-713.65
  def $subst_heaptype{dt : deftype, `tv*` : typevar*, `tu*` : typeuse*}((dt : deftype <: heaptype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_deftype(dt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : deftype <: heaptype)
  ;; test.spectec:714.1-714.53
  def $subst_heaptype{ht : heaptype, `tv*` : typevar*, `tu*` : typeuse*}(ht, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ht

;; test.spectec:680.1-680.112
def $subst_reftype(reftype : reftype, typevar*, typeuse*) : reftype
  ;; test.spectec:716.1-716.87
  def $subst_reftype{`null?` : null?, ht : heaptype, `tv*` : typevar*, `tu*` : typeuse*}(REF_reftype(null?{null <- `null?`}, ht), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = REF_reftype(null?{null <- `null?`}, $subst_heaptype(ht, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:681.1-681.112
def $subst_valtype(valtype : valtype, typevar*, typeuse*) : valtype
  ;; test.spectec:718.1-718.64
  def $subst_valtype{nt : numtype, `tv*` : typevar*, `tu*` : typeuse*}((nt : numtype <: valtype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_numtype(nt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : numtype <: valtype)
  ;; test.spectec:719.1-719.64
  def $subst_valtype{vt : vectype, `tv*` : typevar*, `tu*` : typeuse*}((vt : vectype <: valtype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_vectype(vt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : vectype <: valtype)
  ;; test.spectec:720.1-720.64
  def $subst_valtype{rt : reftype, `tv*` : typevar*, `tu*` : typeuse*}((rt : reftype <: valtype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_reftype(rt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : reftype <: valtype)
  ;; test.spectec:721.1-721.40
  def $subst_valtype{`tv*` : typevar*, `tu*` : typeuse*}(BOT_valtype, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = BOT_valtype

;; test.spectec:684.1-684.112
def $subst_storagetype(storagetype : storagetype, typevar*, typeuse*) : storagetype
  ;; test.spectec:725.1-725.66
  def $subst_storagetype{t : valtype, `tv*` : typevar*, `tu*` : typeuse*}((t : valtype <: storagetype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_valtype(t, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : valtype <: storagetype)
  ;; test.spectec:726.1-726.69
  def $subst_storagetype{pt : packtype, `tv*` : typevar*, `tu*` : typeuse*}((pt : packtype <: storagetype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_packtype(pt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : packtype <: storagetype)

;; test.spectec:685.1-685.112
def $subst_fieldtype(fieldtype : fieldtype, typevar*, typeuse*) : fieldtype
  ;; test.spectec:728.1-728.82
  def $subst_fieldtype{`mut?` : mut?, zt : storagetype, `tv*` : typevar*, `tu*` : typeuse*}(`%%`_fieldtype(mut?{mut <- `mut?`}, zt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `%%`_fieldtype(mut?{mut <- `mut?`}, $subst_storagetype(zt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:687.1-687.112
def $subst_comptype(comptype : comptype, typevar*, typeuse*) : comptype
  ;; test.spectec:730.1-730.85
  def $subst_comptype{`ft*` : fieldtype*, `tv*` : typevar*, `tu*` : typeuse*}(STRUCT_comptype(`%`_list(ft*{ft <- `ft*`})), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = STRUCT_comptype(`%`_list($subst_fieldtype(ft, tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{ft <- `ft*`}))
  ;; test.spectec:731.1-731.81
  def $subst_comptype{ft : fieldtype, `tv*` : typevar*, `tu*` : typeuse*}(ARRAY_comptype(ft), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ARRAY_comptype($subst_fieldtype(ft, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))
  ;; test.spectec:732.1-732.123
  def $subst_comptype{`t_1*` : valtype*, `t_2*` : valtype*, `tv*` : typevar*, `tu*` : typeuse*}(`FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `FUNC%->%`_comptype(`%`_resulttype($subst_valtype(t_1, tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{t_1 <- `t_1*`}), `%`_resulttype($subst_valtype(t_2, tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{t_2 <- `t_2*`}))

;; test.spectec:688.1-688.112
def $subst_subtype(subtype : subtype, typevar*, typeuse*) : subtype
  ;; test.spectec:734.1-735.74
  def $subst_subtype{`final?` : final?, `tu'*` : typeuse*, ct : comptype, `tv*` : typevar*, `tu*` : typeuse*}(SUB_subtype(final?{final <- `final?`}, tu'*{tu' <- `tu'*`}, ct), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = SUB_subtype(final?{final <- `final?`}, $subst_typeuse(tu', tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{tu' <- `tu'*`}, $subst_comptype(ct, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:689.1-689.112
def $subst_rectype(rectype : rectype, typevar*, typeuse*) : rectype
  ;; test.spectec:743.1-744.45
  def $subst_rectype{`st*` : subtype*, `tv*` : typevar*, `tu*` : typeuse*, `tv'*` : typevar*, `tu'*` : typeuse*}(REC_rectype(`%`_list(st*{st <- `st*`})), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = REC_rectype(`%`_list($subst_subtype(st, tv'*{tv' <- `tv'*`}, tu'*{tu' <- `tu'*`})*{st <- `st*`}))
    -- if ((tv'*{tv' <- `tv'*`}, tu'*{tu' <- `tu'*`}) = $minus_recs(tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:690.1-690.112
def $subst_deftype(deftype : deftype, typevar*, typeuse*) : deftype
  ;; test.spectec:749.1-749.80
  def $subst_deftype{qt : rectype, i : n, `tv*` : typevar*, `tu*` : typeuse*}(_DEF_deftype(qt, i), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = _DEF_deftype($subst_rectype(qt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}), i)
}

;; test.spectec:676.1-676.112
def $subst_addrtype(addrtype : addrtype, typevar*, typeuse*) : addrtype
  ;; test.spectec:708.1-708.39
  def $subst_addrtype{at : addrtype, `tv*` : typevar*, `tu*` : typeuse*}(at, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = at

;; test.spectec:692.1-692.112
def $subst_tagtype(tagtype : tagtype, typevar*, typeuse*) : tagtype
  ;; test.spectec:751.1-751.66
  def $subst_tagtype{tu' : typeuse, `tv*` : typevar*, `tu*` : typeuse*}(tu', tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = $subst_typeuse(tu', tv*{tv <- `tv*`}, tu*{tu <- `tu*`})

;; test.spectec:693.1-693.112
def $subst_globaltype(globaltype : globaltype, typevar*, typeuse*) : globaltype
  ;; test.spectec:752.1-752.77
  def $subst_globaltype{`mut?` : mut?, t : valtype, `tv*` : typevar*, `tu*` : typeuse*}(`%%`_globaltype(mut?{mut <- `mut?`}, t), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `%%`_globaltype(mut?{mut <- `mut?`}, $subst_valtype(t, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:694.1-694.112
def $subst_memtype(memtype : memtype, typevar*, typeuse*) : memtype
  ;; test.spectec:753.1-753.58
  def $subst_memtype{at : addrtype, lim : limits, `tv*` : typevar*, `tu*` : typeuse*}(`%%PAGE`_memtype(at, lim), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `%%PAGE`_memtype(at, lim)

;; test.spectec:695.1-695.112
def $subst_tabletype(tabletype : tabletype, typevar*, typeuse*) : tabletype
  ;; test.spectec:754.1-754.82
  def $subst_tabletype{at : addrtype, lim : limits, rt : reftype, `tv*` : typevar*, `tu*` : typeuse*}(`%%%`_tabletype(at, lim, rt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `%%%`_tabletype(at, lim, $subst_reftype(rt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:697.1-697.112
def $subst_externtype(externtype : externtype, typevar*, typeuse*) : externtype
  ;; test.spectec:756.1-756.77
  def $subst_externtype{jt : tagtype, `tv*` : typevar*, `tu*` : typeuse*}(TAG_externtype(jt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = TAG_externtype($subst_tagtype(jt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))
  ;; test.spectec:757.1-757.86
  def $subst_externtype{gt : globaltype, `tv*` : typevar*, `tu*` : typeuse*}(GLOBAL_externtype(gt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = GLOBAL_externtype($subst_globaltype(gt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))
  ;; test.spectec:758.1-758.83
  def $subst_externtype{tt : tabletype, `tv*` : typevar*, `tu*` : typeuse*}(TABLE_externtype(tt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = TABLE_externtype($subst_tabletype(tt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))
  ;; test.spectec:759.1-759.77
  def $subst_externtype{mt : memtype, `tv*` : typevar*, `tu*` : typeuse*}(MEM_externtype(mt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = MEM_externtype($subst_memtype(mt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))
  ;; test.spectec:760.1-760.81
  def $subst_externtype{tu' : typeuse, `tv*` : typevar*, `tu*` : typeuse*}(FUNC_externtype(tu'), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = FUNC_externtype($subst_typeuse(tu', tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:698.1-698.112
def $subst_moduletype(moduletype : moduletype, typevar*, typeuse*) : moduletype
  ;; test.spectec:762.1-762.123
  def $subst_moduletype{`xt_1*` : externtype*, `xt_2*` : externtype*, `tv*` : typevar*, `tu*` : typeuse*}(`%->%`_moduletype(xt_1*{xt_1 <- `xt_1*`}, xt_2*{xt_2 <- `xt_2*`}), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `%->%`_moduletype($subst_externtype(xt_1, tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{xt_1 <- `xt_1*`}, $subst_externtype(xt_2, tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{xt_2 <- `xt_2*`})

;; test.spectec:767.1-767.94
def $subst_all_valtype(valtype : valtype, typeuse*) : valtype
  ;; test.spectec:777.1-777.74
  def $subst_all_valtype{t : valtype, n : n, `tu*` : typeuse*, i : nat}(t, tu^n{tu <- `tu*`}) = $subst_valtype(t, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:768.1-768.94
def $subst_all_reftype(reftype : reftype, typeuse*) : reftype
  ;; test.spectec:778.1-778.76
  def $subst_all_reftype{rt : reftype, n : n, `tu*` : typeuse*, i : nat}(rt, tu^n{tu <- `tu*`}) = $subst_reftype(rt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:769.1-769.94
def $subst_all_deftype(deftype : deftype, typeuse*) : deftype
  ;; test.spectec:779.1-779.76
  def $subst_all_deftype{dt : deftype, n : n, `tu*` : typeuse*, i : nat}(dt, tu^n{tu <- `tu*`}) = $subst_deftype(dt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:770.1-770.94
def $subst_all_tagtype(tagtype : tagtype, typeuse*) : tagtype
  ;; test.spectec:780.1-780.76
  def $subst_all_tagtype{jt : tagtype, n : n, `tu*` : typeuse*, i : nat}(jt, tu^n{tu <- `tu*`}) = $subst_tagtype(jt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:771.1-771.103
def $subst_all_globaltype(globaltype : globaltype, typeuse*) : globaltype
  ;; test.spectec:781.1-781.82
  def $subst_all_globaltype{gt : globaltype, n : n, `tu*` : typeuse*, i : nat}(gt, tu^n{tu <- `tu*`}) = $subst_globaltype(gt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:772.1-772.94
def $subst_all_memtype(memtype : memtype, typeuse*) : memtype
  ;; test.spectec:782.1-782.76
  def $subst_all_memtype{mt : memtype, n : n, `tu*` : typeuse*, i : nat}(mt, tu^n{tu <- `tu*`}) = $subst_memtype(mt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:773.1-773.100
def $subst_all_tabletype(tabletype : tabletype, typeuse*) : tabletype
  ;; test.spectec:783.1-783.80
  def $subst_all_tabletype{tt : tabletype, n : n, `tu*` : typeuse*, i : nat}(tt, tu^n{tu <- `tu*`}) = $subst_tabletype(tt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:774.1-774.103
def $subst_all_externtype(externtype : externtype, typeuse*) : externtype
  ;; test.spectec:784.1-784.82
  def $subst_all_externtype{xt : externtype, n : n, `tu*` : typeuse*, i : nat}(xt, tu^n{tu <- `tu*`}) = $subst_externtype(xt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:775.1-775.103
def $subst_all_moduletype(moduletype : moduletype, typeuse*) : moduletype
  ;; test.spectec:785.1-785.84
  def $subst_all_moduletype{mmt : moduletype, n : n, `tu*` : typeuse*, i : nat}(mmt, tu^n{tu <- `tu*`}) = $subst_moduletype(mmt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:787.1-787.97
rec {

;; test.spectec:787.1-787.97
def $subst_all_deftypes(deftype*, typeuse*) : deftype*
  ;; test.spectec:788.1-788.40
  def $subst_all_deftypes{`tu*` : typeuse*}([], tu*{tu <- `tu*`}) = []
  ;; test.spectec:789.1-789.101
  def $subst_all_deftypes{dt_1 : deftype, `dt*` : deftype*, `tu*` : typeuse*}([dt_1] ++ dt*{dt <- `dt*`}, tu*{tu <- `tu*`}) = [$subst_all_deftype(dt_1, tu*{tu <- `tu*`})] ++ $subst_all_deftypes(dt*{dt <- `dt*`}, tu*{tu <- `tu*`})
}

;; test.spectec:794.1-794.88
def $rollrt(typeidx : typeidx, rectype : rectype) : rectype
  ;; test.spectec:799.1-800.32
  def $rollrt{x : idx, rectype : rectype, i : nat, n : n, `subtype*` : subtype*}(x, rectype) = REC_rectype(`%`_list($subst_subtype(subtype, _IDX_typevar(`%`_typeidx((x!`%`_idx.0 + i)))^(i<n){}, REC_typeuse(i)^(i<n){})^n{subtype <- `subtype*`}))
    -- if (rectype = REC_rectype(`%`_list(subtype^n{subtype <- `subtype*`})))

;; test.spectec:795.1-795.90
def $unrollrt(rectype : rectype) : rectype
  ;; test.spectec:801.1-802.32
  def $unrollrt{rectype : rectype, i : nat, n : n, `subtype*` : subtype*}(rectype) = REC_rectype(`%`_list($subst_subtype(subtype, REC_typevar(i)^(i<n){}, _DEF_typeuse(rectype, i)^(i<n){})^n{subtype <- `subtype*`}))
    -- if (rectype = REC_rectype(`%`_list(subtype^n{subtype <- `subtype*`})))

;; test.spectec:796.1-796.90
def $rolldt(typeidx : typeidx, rectype : rectype) : deftype*
  ;; test.spectec:804.1-804.100
  def $rolldt{x : idx, rectype : rectype, n : n, `subtype*` : subtype*}(x, rectype) = _DEF_deftype(REC_rectype(`%`_list(subtype^n{subtype <- `subtype*`})), i)^(i<n){}
    -- if ($rollrt(x, rectype) = REC_rectype(`%`_list(subtype^n{subtype <- `subtype*`})))

;; test.spectec:797.1-797.90
def $unrolldt(deftype : deftype) : subtype
  ;; test.spectec:805.1-805.98
  def $unrolldt{rectype : rectype, i : n, `subtype*` : subtype*}(_DEF_deftype(rectype, i)) = subtype*{subtype <- `subtype*`}[i]
    -- if ($unrollrt(rectype) = REC_rectype(`%`_list(subtype*{subtype <- `subtype*`})))

;; test.spectec:810.1-810.36
def $free_addrtype(addrtype : addrtype) : free
  ;; test.spectec:840.1-840.34
  def $free_addrtype{addrtype : addrtype}(addrtype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:811.1-811.34
def $free_numtype(numtype : numtype) : free
  ;; test.spectec:842.1-842.32
  def $free_numtype{numtype : numtype}(numtype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:812.1-812.36
def $free_packtype(packtype : packtype) : free
  ;; test.spectec:844.1-844.34
  def $free_packtype{packtype : packtype}(packtype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:813.1-813.36
def $free_lanetype(lanetype : lanetype) : free
  ;; test.spectec:846.1-846.53
  def $free_lanetype{numtype : numtype}((numtype : numtype <: lanetype)) = $free_numtype(numtype)
  ;; test.spectec:847.1-847.56
  def $free_lanetype{packtype : packtype}((packtype : packtype <: lanetype)) = $free_packtype(packtype)

;; test.spectec:814.1-814.34
def $free_vectype(vectype : vectype) : free
  ;; test.spectec:849.1-849.32
  def $free_vectype{vectype : vectype}(vectype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:815.1-815.38
def $free_consttype(consttype : consttype) : free
  ;; test.spectec:851.1-851.54
  def $free_consttype{numtype : numtype}((numtype : numtype <: consttype)) = $free_numtype(numtype)
  ;; test.spectec:852.1-852.54
  def $free_consttype{vectype : vectype}((vectype : vectype <: consttype)) = $free_vectype(vectype)

;; test.spectec:816.1-816.42
def $free_absheaptype(absheaptype : absheaptype) : free
  ;; test.spectec:854.1-854.40
  def $free_absheaptype{absheaptype : absheaptype}(absheaptype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:819.1-819.34
def $free_typevar(typevar : typevar) : free
  ;; test.spectec:859.1-859.57
  def $free_typevar{typeidx : typeidx}(_IDX_typevar(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:860.1-860.30
  def $free_typevar{n : n}(REC_typevar(n)) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:817.1-856.34
rec {

;; test.spectec:817.1-817.36
def $free_heaptype(heaptype : heaptype) : free
  ;; test.spectec:865.1-865.65
  def $free_heaptype{absheaptype : absheaptype}((absheaptype : absheaptype <: heaptype)) = $free_absheaptype(absheaptype)
  ;; test.spectec:866.1-866.53
  def $free_heaptype{typeuse : typeuse}((typeuse : typeuse <: heaptype)) = $free_typeuse(typeuse)

;; test.spectec:818.1-818.34
def $free_reftype(reftype : reftype) : free
  ;; test.spectec:868.1-868.65
  def $free_reftype{`null?` : null?, heaptype : heaptype}(REF_reftype(null?{null <- `null?`}, heaptype)) = $free_heaptype(heaptype)

;; test.spectec:820.1-820.34
def $free_typeuse(typeuse : typeuse) : free
  ;; test.spectec:862.1-862.52
  def $free_typeuse{typevar : typevar}((typevar : typevar <: typeuse)) = $free_typevar(typevar)
  ;; test.spectec:863.1-863.52
  def $free_typeuse{deftype : deftype}((deftype : deftype <: typeuse)) = $free_deftype(deftype)

;; test.spectec:821.1-821.34
def $free_valtype(valtype : valtype) : free
  ;; test.spectec:870.1-870.52
  def $free_valtype{numtype : numtype}((numtype : numtype <: valtype)) = $free_numtype(numtype)
  ;; test.spectec:871.1-871.52
  def $free_valtype{vectype : vectype}((vectype : vectype <: valtype)) = $free_vectype(vectype)
  ;; test.spectec:872.1-872.52
  def $free_valtype{reftype : reftype}((reftype : reftype <: valtype)) = $free_reftype(reftype)
  ;; test.spectec:873.1-873.28
  def $free_valtype(BOT_valtype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:823.1-823.40
def $free_resulttype(resulttype : resulttype) : free
  ;; test.spectec:875.1-875.69
  def $free_resulttype{`valtype*` : valtype*}(`%`_resulttype(valtype*{valtype <- `valtype*`})) = $free_list($free_valtype(valtype)*{valtype <- `valtype*`})

;; test.spectec:824.1-824.42
def $free_storagetype(storagetype : storagetype) : free
  ;; test.spectec:877.1-877.56
  def $free_storagetype{valtype : valtype}((valtype : valtype <: storagetype)) = $free_valtype(valtype)
  ;; test.spectec:878.1-878.59
  def $free_storagetype{packtype : packtype}((packtype : packtype <: storagetype)) = $free_packtype(packtype)

;; test.spectec:825.1-825.38
def $free_fieldtype(fieldtype : fieldtype) : free
  ;; test.spectec:880.1-880.71
  def $free_fieldtype{`mut?` : mut?, storagetype : storagetype}(`%%`_fieldtype(mut?{mut <- `mut?`}, storagetype)) = $free_storagetype(storagetype)

;; test.spectec:826.1-826.36
def $free_comptype(comptype : comptype) : free
  ;; test.spectec:882.1-882.80
  def $free_comptype{`fieldtype*` : fieldtype*}(STRUCT_comptype(`%`_list(fieldtype*{fieldtype <- `fieldtype*`}))) = $free_list($free_fieldtype(fieldtype)*{fieldtype <- `fieldtype*`})
  ;; test.spectec:883.1-883.65
  def $free_comptype{fieldtype : fieldtype}(ARRAY_comptype(fieldtype)) = $free_fieldtype(fieldtype)
  ;; test.spectec:884.1-884.121
  def $free_comptype{resulttype_1 : resulttype, resulttype_2 : resulttype}(`FUNC%->%`_comptype(resulttype_1, resulttype_2)) = $free_resulttype(resulttype_1) +++ $free_resulttype(resulttype_2)

;; test.spectec:827.1-827.34
def $free_subtype(subtype : subtype) : free
  ;; test.spectec:886.1-887.66
  def $free_subtype{`final?` : final?, `typeuse*` : typeuse*, comptype : comptype}(SUB_subtype(final?{final <- `final?`}, typeuse*{typeuse <- `typeuse*`}, comptype)) = $free_list($free_typeuse(typeuse)*{typeuse <- `typeuse*`}) +++ $free_comptype(comptype)

;; test.spectec:828.1-828.34
def $free_rectype(rectype : rectype) : free
  ;; test.spectec:889.1-889.70
  def $free_rectype{`subtype*` : subtype*}(REC_rectype(`%`_list(subtype*{subtype <- `subtype*`}))) = $free_list($free_subtype(subtype)*{subtype <- `subtype*`})

;; test.spectec:856.1-856.34
def $free_deftype(deftype : deftype) : free
  ;; test.spectec:857.1-857.59
  def $free_deftype{rectype : rectype, n : n}(_DEF_deftype(rectype, n)) = $free_rectype(rectype)
}

;; test.spectec:830.1-830.34
def $free_tagtype(tagtype : tagtype) : free
  ;; test.spectec:891.1-891.52
  def $free_tagtype{deftype : deftype}((deftype : deftype <: typeuse)) = $free_deftype(deftype)

;; test.spectec:831.1-831.40
def $free_globaltype(globaltype : globaltype) : free
  ;; test.spectec:893.1-893.60
  def $free_globaltype{`mut?` : mut?, valtype : valtype}(`%%`_globaltype(mut?{mut <- `mut?`}, valtype)) = $free_valtype(valtype)

;; test.spectec:832.1-832.34
def $free_memtype(memtype : memtype) : free
  ;; test.spectec:895.1-895.67
  def $free_memtype{addrtype : addrtype, limits : limits}(`%%PAGE`_memtype(addrtype, limits)) = $free_addrtype(addrtype)

;; test.spectec:833.1-833.38
def $free_tabletype(tabletype : tabletype) : free
  ;; test.spectec:897.1-898.53
  def $free_tabletype{addrtype : addrtype, limits : limits, reftype : reftype}(`%%%`_tabletype(addrtype, limits, reftype)) = $free_addrtype(addrtype) +++ $free_reftype(reftype)

;; test.spectec:834.1-834.36
def $free_datatype(datatype : datatype) : free
  ;; test.spectec:900.1-900.28
  def $free_datatype(OK_datatype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:835.1-835.36
def $free_elemtype(elemtype : elemtype) : free
  ;; test.spectec:902.1-902.53
  def $free_elemtype{reftype : reftype}(reftype) = $free_reftype(reftype)

;; test.spectec:836.1-836.40
def $free_externtype(externtype : externtype) : free
  ;; test.spectec:904.1-904.59
  def $free_externtype{tagtype : tagtype}(TAG_externtype(tagtype)) = $free_tagtype(tagtype)
  ;; test.spectec:905.1-905.71
  def $free_externtype{globaltype : globaltype}(GLOBAL_externtype(globaltype)) = $free_globaltype(globaltype)
  ;; test.spectec:906.1-906.59
  def $free_externtype{memtype : memtype}(MEM_externtype(memtype)) = $free_memtype(memtype)
  ;; test.spectec:907.1-907.67
  def $free_externtype{tabletype : tabletype}(TABLE_externtype(tabletype)) = $free_tabletype(tabletype)
  ;; test.spectec:908.1-908.60
  def $free_externtype{typeuse : typeuse}(FUNC_externtype(typeuse)) = $free_typeuse(typeuse)

;; test.spectec:837.1-837.40
def $free_moduletype(moduletype : moduletype) : free
  ;; test.spectec:910.1-912.46
  def $free_moduletype{`externtype_1*` : externtype*, `externtype_2*` : externtype*}(`%->%`_moduletype(externtype_1*{externtype_1 <- `externtype_1*`}, externtype_2*{externtype_2 <- `externtype_2*`})) = $free_list($free_externtype(externtype_1)*{externtype_1 <- `externtype_1*`}) +++ $free_list($free_externtype(externtype_2)*{externtype_2 <- `externtype_2*`})

;; test.spectec:927.1-927.21
syntax num_(numtype : numtype)
  ;; test.spectec:928.1-928.36
  syntax num_{Inn : Inn}((Inn : addrtype <: numtype)) = iN($sizenn((Inn : addrtype <: numtype)))


  ;; test.spectec:929.1-929.36
  syntax num_{Fnn : Fnn}((Fnn : Fnn <: numtype)) = fN($sizenn((Fnn : Fnn <: numtype)))


;; test.spectec:931.1-931.38
syntax pack_{Pnn : Pnn}(Pnn) = iN($psizenn(Pnn))

;; test.spectec:933.1-933.23
syntax lane_(lanetype : lanetype)
  ;; test.spectec:934.1-934.38
  syntax lane_{numtype : numtype}((numtype : numtype <: lanetype)) = num_(numtype)


  ;; test.spectec:935.1-935.41
  syntax lane_{packtype : packtype}((packtype : packtype <: lanetype)) = pack_(packtype)


  ;; test.spectec:936.1-936.36
  syntax lane_{Jnn : Jnn}((Jnn : Jnn <: lanetype)) = iN($lsize((Jnn : Jnn <: lanetype)))


;; test.spectec:938.1-938.35
syntax vec_{Vnn : Vnn}(Vnn) = vN($vsize(Vnn))

;; test.spectec:940.1-940.25
syntax lit_(storagetype : storagetype)
  ;; test.spectec:941.1-941.37
  syntax lit_{numtype : numtype}((numtype : numtype <: storagetype)) = num_(numtype)


  ;; test.spectec:942.1-942.37
  syntax lit_{vectype : vectype}((vectype : vectype <: storagetype)) = vec_(vectype)


  ;; test.spectec:943.1-943.40
  syntax lit_{packtype : packtype}((packtype : packtype <: storagetype)) = pack_(packtype)


;; test.spectec:948.1-948.56
syntax sz = 
  | `%`(i : nat)
    -- if ((((i = 8) \/ (i = 16)) \/ (i = 32)) \/ (i = 64))

;; test.spectec:949.1-949.42
syntax sx = 
  | U
  | S

;; test.spectec:951.1-951.22
syntax unop_(numtype : numtype)
  ;; test.spectec:952.1-952.102
  syntax unop_{Inn : Inn}((Inn : addrtype <: numtype)) = 
  | CLZ
  | CTZ
  | POPCNT
  | EXTEND(sz : sz)
    -- if (sz!`%`_sz.0 < $sizenn((Inn : addrtype <: numtype)))


  ;; test.spectec:953.1-953.70
  syntax unop_{Fnn : Fnn}((Fnn : Fnn <: numtype)) = 
  | ABS
  | NEG
  | SQRT
  | CEIL
  | FLOOR
  | TRUNC
  | NEAREST


;; test.spectec:955.1-955.23
syntax binop_(numtype : numtype)
  ;; test.spectec:956.1-958.67
  syntax binop_{Inn : Inn}((Inn : addrtype <: numtype)) = 
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


  ;; test.spectec:959.1-960.87
  syntax binop_{Fnn : Fnn}((Fnn : Fnn <: numtype)) = 
  | ADD
  | SUB
  | MUL
  | DIV
  | MIN
  | MAX
  | COPYSIGN


;; test.spectec:962.1-962.24
syntax testop_{Inn : Inn}((Inn : addrtype <: numtype)) = 
  | EQZ

;; test.spectec:966.1-966.23
syntax relop_(numtype : numtype)
  ;; test.spectec:967.1-970.54
  syntax relop_{Inn : Inn}((Inn : addrtype <: numtype)) = 
  | EQ
  | NE
  | LT(sx : sx)
  | GT(sx : sx)
  | LE(sx : sx)
  | GE(sx : sx)


  ;; test.spectec:971.1-972.32
  syntax relop_{Fnn : Fnn}((Fnn : Fnn <: numtype)) = 
  | EQ
  | NE
  | LT
  | GT
  | LE
  | GE


;; test.spectec:975.1-975.37
syntax cvtop__(numtype_1 : numtype, numtype_2 : numtype)
  ;; test.spectec:976.1-978.57
  syntax cvtop__{Inn_1 : Inn, Inn_2 : Inn}((Inn_1 : addrtype <: numtype), (Inn_2 : addrtype <: numtype)) = 
  | EXTEND(sx : sx)
    -- if ($sizenn1((Inn_1 : addrtype <: numtype)) < $sizenn2((Inn_2 : addrtype <: numtype)))
  | WRAP
    -- if ($sizenn1((Inn_1 : addrtype <: numtype)) > $sizenn2((Inn_2 : addrtype <: numtype)))


  ;; test.spectec:979.1-981.57
  syntax cvtop__{Inn_1 : Inn, Fnn_2 : Fnn}((Inn_1 : addrtype <: numtype), (Fnn_2 : Fnn <: numtype)) = 
  | CONVERT(sx : sx)
  | REINTERPRET
    -- if ($sizenn1((Inn_1 : addrtype <: numtype)) = $sizenn2((Fnn_2 : Fnn <: numtype)))


  ;; test.spectec:982.1-985.57
  syntax cvtop__{Fnn_1 : Fnn, Inn_2 : Inn}((Fnn_1 : Fnn <: numtype), (Inn_2 : addrtype <: numtype)) = 
  | TRUNC(sx : sx)
  | TRUNC_SAT(sx : sx)
  | REINTERPRET
    -- if ($sizenn1((Fnn_1 : Fnn <: numtype)) = $sizenn2((Inn_2 : addrtype <: numtype)))


  ;; test.spectec:986.1-988.57
  syntax cvtop__{Fnn_1 : Fnn, Fnn_2 : Fnn}((Fnn_1 : Fnn <: numtype), (Fnn_2 : Fnn <: numtype)) = 
  | PROMOTE
    -- if ($sizenn1((Fnn_1 : Fnn <: numtype)) < $sizenn2((Fnn_2 : Fnn <: numtype)))
  | DEMOTE
    -- if ($sizenn1((Fnn_1 : Fnn <: numtype)) > $sizenn2((Fnn_2 : Fnn <: numtype)))


;; test.spectec:993.1-993.60
syntax dim = 
  | `%`(i : nat)
    -- if (((((i = 1) \/ (i = 2)) \/ (i = 4)) \/ (i = 8)) \/ (i = 16))

;; test.spectec:994.1-995.40
syntax shape = 
  | `%X%`(lanetype : lanetype, dim : dim)
    -- if (($lsize(lanetype) * dim!`%`_dim.0) = 128)

;; test.spectec:998.1-998.43
def $dim(shape : shape) : dim
  ;; test.spectec:999.1-999.22
  def $dim{Lnn : Lnn, N : N}(`%X%`_shape(Lnn, `%`_dim(N))) = `%`_dim(N)

;; test.spectec:1001.1-1001.58
def $lanetype(shape : shape) : lanetype
  ;; test.spectec:1002.1-1002.29
  def $lanetype{Lnn : Lnn, N : N}(`%X%`_shape(Lnn, `%`_dim(N))) = Lnn

;; test.spectec:1004.1-1004.57
def $unpackshape(shape : shape) : numtype
  ;; test.spectec:1005.1-1005.42
  def $unpackshape{Lnn : Lnn, N : N}(`%X%`_shape(Lnn, `%`_dim(N))) = $lunpack(Lnn)

;; test.spectec:1008.1-1008.78
syntax ishape = 
  | `%`(shape : shape) {Jnn : Jnn}
    -- if ($lanetype(shape) = (Jnn : Jnn <: lanetype))

;; test.spectec:1009.1-1009.77
syntax bshape = 
  | `%`(shape : shape)
    -- if ($lanetype(shape) = I8_lanetype)

;; test.spectec:1014.1-1014.19
syntax zero = 
  | ZERO

;; test.spectec:1015.1-1015.25
syntax half = 
  | LOW
  | HIGH

;; test.spectec:1017.1-1017.41
syntax vvunop = 
  | NOT

;; test.spectec:1018.1-1018.62
syntax vvbinop = 
  | AND
  | ANDNOT
  | OR
  | XOR

;; test.spectec:1019.1-1019.49
syntax vvternop = 
  | BITSELECT

;; test.spectec:1020.1-1020.48
syntax vvtestop = 
  | ANY_TRUE

;; test.spectec:1022.1-1022.42
syntax vunop_(shape : shape)
  ;; test.spectec:1023.1-1024.36
  syntax vunop_{Jnn : Jnn, M : M}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))) = 
  | ABS
  | NEG
  | POPCNT
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) = 8)


  ;; test.spectec:1025.1-1026.35
  syntax vunop_{Fnn : Fnn, M : M}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))) = 
  | ABS
  | NEG
  | SQRT
  | CEIL
  | FLOOR
  | TRUNC
  | NEAREST


;; test.spectec:1028.1-1028.43
syntax vbinop_(shape : shape)
  ;; test.spectec:1029.1-1039.72
  syntax vbinop_{Jnn : Jnn, M : M}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))) = 
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
  | RELAXED_Q15MULRS
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) = 16)
  | MIN(sx : sx)
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) <= 32)
  | MAX(sx : sx)
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) <= 32)


  ;; test.spectec:1040.1-1042.30
  syntax vbinop_{Fnn : Fnn, M : M}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))) = 
  | ADD
  | SUB
  | MUL
  | DIV
  | MIN
  | MAX
  | PMIN
  | PMAX
  | RELAXED_MIN
  | RELAXED_MAX


;; test.spectec:1044.1-1044.44
syntax vternop_(shape : shape)
  ;; test.spectec:1045.1-1045.46
  syntax vternop_{Jnn : Jnn, M : M}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))) = 
  | RELAXED_LANESELECT


  ;; test.spectec:1046.1-1046.56
  syntax vternop_{Fnn : Fnn, M : M}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))) = 
  | RELAXED_MADD
  | RELAXED_NMADD


;; test.spectec:1048.1-1048.44
syntax vtestop_{Jnn : Jnn, M : M}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))) = 
  | ALL_TRUE

;; test.spectec:1052.1-1052.43
syntax vrelop_(shape : shape)
  ;; test.spectec:1053.1-1057.67
  syntax vrelop_{Jnn : Jnn, M : M}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))) = 
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


  ;; test.spectec:1058.1-1058.54
  syntax vrelop_{Fnn : Fnn, M : M}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))) = 
  | EQ
  | NE
  | LT
  | GT
  | LE
  | GE


;; test.spectec:1060.1-1060.46
syntax vshiftop_{Jnn : Jnn, M : M}(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)))) = 
  | SHL
  | SHR(sx : sx)

;; test.spectec:1063.1-1063.47
syntax vswizzlop_{M : M}(`%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(M)))) = 
  | SWIZZLE
  | RELAXED_SWIZZLE

;; test.spectec:1066.1-1066.59
syntax vextunop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)))) = 
  | EXTADD_PAIRWISE(sx : sx)
    -- if ((16 <= (2 * $lsizenn1((Jnn_1 : Jnn <: lanetype)))) /\ (((2 * $lsizenn1((Jnn_1 : Jnn <: lanetype))) = $lsizenn2((Jnn_2 : Jnn <: lanetype))) /\ ($lsizenn2((Jnn_2 : Jnn <: lanetype)) <= 32)))

;; test.spectec:1071.1-1071.60
syntax vextbinop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)))) = 
  | EXTMUL(half : half, sx : sx)
    -- if (((2 * $lsizenn1((Jnn_1 : Jnn <: lanetype))) = $lsizenn2((Jnn_2 : Jnn <: lanetype))) /\ ($lsizenn2((Jnn_2 : Jnn <: lanetype)) >= 16))
  | DOTS
    -- if (((2 * $lsizenn1((Jnn_1 : Jnn <: lanetype))) = $lsizenn2((Jnn_2 : Jnn <: lanetype))) /\ ($lsizenn2((Jnn_2 : Jnn <: lanetype)) = 32))
  | RELAXED_DOTS
    -- if (((2 * $lsizenn1((Jnn_1 : Jnn <: lanetype))) = $lsizenn2((Jnn_2 : Jnn <: lanetype))) /\ ($lsizenn2((Jnn_2 : Jnn <: lanetype)) = 16))

;; test.spectec:1080.1-1080.61
syntax vextternop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)))) = 
  | RELAXED_DOT_ADDS
    -- if (((4 * $lsizenn1((Jnn_1 : Jnn <: lanetype))) = $lsizenn2((Jnn_2 : Jnn <: lanetype))) /\ ($lsizenn2((Jnn_2 : Jnn <: lanetype)) = 32))

;; test.spectec:1085.1-1085.55
syntax vcvtop__(shape_1 : shape, shape_2 : shape)
  ;; test.spectec:1086.1-1088.53
  syntax vcvtop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))) = 
  | EXTEND(half : half, sx : sx)
    -- if ($lsizenn2((Jnn_2 : Jnn <: lanetype)) = (2 * $lsizenn1((Jnn_1 : Jnn <: lanetype))))


  ;; test.spectec:1089.1-1092.67
  syntax vcvtop__{Jnn_1 : Jnn, M_1 : M, Fnn_2 : Fnn, M_2 : M}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2))) = 
  | CONVERT(`half?` : half?, sx : sx)
    -- if (((($sizenn2((Fnn_2 : Fnn <: numtype)) = $lsizenn1((Jnn_1 : Jnn <: lanetype))) /\ ($lsizenn1((Jnn_1 : Jnn <: lanetype)) = 32)) /\ (half?{half <- `half?`} = ?())) \/ (($sizenn2((Fnn_2 : Fnn <: numtype)) = (2 * $lsizenn1((Jnn_1 : Jnn <: lanetype)))) /\ (half?{half <- `half?`} = ?(LOW_half))))


  ;; test.spectec:1093.1-1099.68
  syntax vcvtop__{Fnn_1 : Fnn, M_1 : M, Jnn_2 : Jnn, M_2 : M}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))) = 
  | TRUNC_SAT(sx : sx, `zero?` : zero?)
    -- if (((($sizenn1((Fnn_1 : Fnn <: numtype)) = $lsizenn2((Jnn_2 : Jnn <: lanetype))) /\ ($lsizenn2((Jnn_2 : Jnn <: lanetype)) = 32)) /\ (zero?{zero <- `zero?`} = ?())) \/ (($sizenn1((Fnn_1 : Fnn <: numtype)) = (2 * $lsizenn2((Jnn_2 : Jnn <: lanetype)))) /\ (zero?{zero <- `zero?`} = ?(ZERO_zero))))
  | RELAXED_TRUNC(sx : sx, `zero?` : zero?)
    -- if (((($sizenn1((Fnn_1 : Fnn <: numtype)) = $lsizenn2((Jnn_2 : Jnn <: lanetype))) /\ ($lsizenn2((Jnn_2 : Jnn <: lanetype)) = 32)) /\ (zero?{zero <- `zero?`} = ?())) \/ (($sizenn1((Fnn_1 : Fnn <: numtype)) = (2 * $lsizenn2((Jnn_2 : Jnn <: lanetype)))) /\ (zero?{zero <- `zero?`} = ?(ZERO_zero))))


  ;; test.spectec:1100.1-1104.51
  syntax vcvtop__{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2))) = 
  | DEMOTE(zero : zero)
    -- if ($sizenn1((Fnn_1 : Fnn <: numtype)) = (2 * $sizenn2((Fnn_2 : Fnn <: numtype))))
  | PROMOTELOW
    -- if ((2 * $sizenn1((Fnn_1 : Fnn <: numtype))) = $sizenn2((Fnn_2 : Fnn <: numtype)))


;; test.spectec:1109.1-1109.69
syntax memarg = 
{
  ALIGN u32,
  OFFSET u64
}

;; test.spectec:1113.1-1113.24
syntax loadop_{Inn : Inn}((Inn : addrtype <: numtype)) = 
  | `%_%`(sz : sz, sx : sx)
    -- if (sz!`%`_sz.0 < $sizenn((Inn : addrtype <: numtype)))

;; test.spectec:1116.1-1116.25
syntax storeop_{Inn : Inn}((Inn : addrtype <: numtype)) = 
  | `%`(sz : sz)
    -- if (sz!`%`_sz.0 < $sizenn((Inn : addrtype <: numtype)))

;; test.spectec:1119.1-1122.59
syntax vloadop_{vectype : vectype}(vectype) = 
  | `SHAPE%X%_%`(sz : sz, M : M, sx : sx)
    -- if (((sz!`%`_sz.0 * M) : nat <:> rat) = (($vsize(vectype) : nat <:> rat) / (2 : nat <:> rat)))
  | SPLAT(sz : sz)
  | ZERO(sz : sz)
    -- if (sz!`%`_sz.0 >= 32)

;; test.spectec:1127.1-1129.17
syntax blocktype = 
  | _RESULT(`valtype?` : valtype?)
  | _IDX(typeidx : typeidx)

;; test.spectec:4106.1-4106.39
syntax addr = nat

;; test.spectec:4115.1-4115.51
syntax arrayaddr = addr

;; test.spectec:1177.1-1181.27
syntax catch = 
  | CATCH(tagidx : tagidx, labelidx : labelidx)
  | CATCH_REF(tagidx : tagidx, labelidx : labelidx)
  | CATCH_ALL(labelidx : labelidx)
  | CATCH_ALL_REF(labelidx : labelidx)

;; test.spectec:4116.1-4116.53
syntax exnaddr = addr

;; test.spectec:4112.1-4112.49
syntax dataaddr = addr

;; test.spectec:4113.1-4113.49
syntax elemaddr = addr

;; test.spectec:4111.1-4111.53
syntax funcaddr = addr

;; test.spectec:4108.1-4108.53
syntax globaladdr = addr

;; test.spectec:4109.1-4109.50
syntax memaddr = addr

;; test.spectec:4110.1-4110.51
syntax tableaddr = addr

;; test.spectec:4107.1-4107.47
syntax tagaddr = addr

;; test.spectec:4119.1-4120.84
syntax externaddr = 
  | TAG(tagaddr : tagaddr)
  | GLOBAL(globaladdr : globaladdr)
  | MEM(memaddr : memaddr)
  | TABLE(tableaddr : tableaddr)
  | FUNC(funcaddr : funcaddr)

;; test.spectec:4180.1-4181.33
syntax exportinst = 
{
  NAME name,
  ADDR externaddr
}

;; test.spectec:4200.1-4209.26
syntax moduleinst = 
{
  TYPES deftype*,
  TAGS tagaddr*,
  GLOBALS globaladdr*,
  MEMS memaddr*,
  TABLES tableaddr*,
  FUNCS funcaddr*,
  DATAS dataaddr*,
  ELEMS elemaddr*,
  EXPORTS exportinst*
}

;; test.spectec:4117.1-4117.49
syntax hostaddr = addr

;; test.spectec:4114.1-4114.56
syntax structaddr = addr

;; test.spectec:4134.1-4142.19
rec {

;; test.spectec:4134.1-4142.19
syntax ref = 
  | `REF.I31_NUM`(u31 : u31)
  | `REF.NULL_ADDR`
  | `REF.STRUCT_ADDR`(structaddr : structaddr)
  | `REF.ARRAY_ADDR`(arrayaddr : arrayaddr)
  | `REF.FUNC_ADDR`(funcaddr : funcaddr)
  | `REF.EXN_ADDR`(exnaddr : exnaddr)
  | `REF.HOST_ADDR`(hostaddr : hostaddr)
  | `REF.EXTERN`(ref : ref)
}

;; test.spectec:4144.1-4145.20
syntax val = 
  | CONST(numtype : numtype, num_(numtype))
  | VCONST(vectype : vectype, vec_(vectype))
  | `REF.I31_NUM`(u31 : u31)
  | `REF.NULL_ADDR`
  | `REF.STRUCT_ADDR`(structaddr : structaddr)
  | `REF.ARRAY_ADDR`(arrayaddr : arrayaddr)
  | `REF.FUNC_ADDR`(funcaddr : funcaddr)
  | `REF.EXN_ADDR`(exnaddr : exnaddr)
  | `REF.HOST_ADDR`(hostaddr : hostaddr)
  | `REF.EXTERN`(ref : ref)

;; test.spectec:4226.1-4227.40
syntax frame = 
{
  LOCALS val?*,
  MODULE moduleinst
}

;; test.spectec:4232.1-4238.9
rec {

;; test.spectec:4232.1-4238.9
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
  | BR_ON_NULL(labelidx : labelidx)
  | BR_ON_NON_NULL(labelidx : labelidx)
  | BR_ON_CAST(labelidx : labelidx, reftype : reftype, reftype : reftype)
  | BR_ON_CAST_FAIL(labelidx : labelidx, reftype : reftype, reftype : reftype)
  | CALL(funcidx : funcidx)
  | CALL_REF(typeuse : typeuse)
  | CALL_INDIRECT(tableidx : tableidx, typeuse : typeuse)
  | RETURN
  | RETURN_CALL(funcidx : funcidx)
  | RETURN_CALL_REF(typeuse : typeuse)
  | RETURN_CALL_INDIRECT(tableidx : tableidx, typeuse : typeuse)
  | THROW(tagidx : tagidx)
  | THROW_REF
  | TRY_TABLE(blocktype : blocktype, list(syntax catch), `instr*` : instr*)
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
  | LOAD(numtype : numtype, loadop_(numtype)?, memidx : memidx, memarg : memarg)
  | STORE(numtype : numtype, storeop_(numtype)?, memidx : memidx, memarg : memarg)
  | VLOAD(vectype : vectype, vloadop_(vectype)?, memidx : memidx, memarg : memarg)
  | VLOAD_LANE(vectype : vectype, sz : sz, memidx : memidx, memarg : memarg, laneidx : laneidx)
  | VSTORE(vectype : vectype, memidx : memidx, memarg : memarg)
  | VSTORE_LANE(vectype : vectype, sz : sz, memidx : memidx, memarg : memarg, laneidx : laneidx)
  | `MEMORY.SIZE`(memidx : memidx)
  | `MEMORY.GROW`(memidx : memidx)
  | `MEMORY.FILL`(memidx : memidx)
  | `MEMORY.COPY`(memidx : memidx, memidx : memidx)
  | `MEMORY.INIT`(memidx : memidx, dataidx : dataidx)
  | `DATA.DROP`(dataidx : dataidx)
  | `REF.NULL`(heaptype : heaptype)
  | `REF.IS_NULL`
  | `REF.AS_NON_NULL`
  | `REF.EQ`
  | `REF.TEST`(reftype : reftype)
  | `REF.CAST`(reftype : reftype)
  | `REF.FUNC`(funcidx : funcidx)
  | `REF.I31`
  | `I31.GET`(sx : sx)
  | `STRUCT.NEW`(typeidx : typeidx)
  | `STRUCT.NEW_DEFAULT`(typeidx : typeidx)
  | `STRUCT.GET`(`sx?` : sx?, typeidx : typeidx, fieldidx : fieldidx)
  | `STRUCT.SET`(typeidx : typeidx, fieldidx : fieldidx)
  | `ARRAY.NEW`(typeidx : typeidx)
  | `ARRAY.NEW_DEFAULT`(typeidx : typeidx)
  | `ARRAY.NEW_FIXED`(typeidx : typeidx, u32 : u32)
  | `ARRAY.NEW_DATA`(typeidx : typeidx, dataidx : dataidx)
  | `ARRAY.NEW_ELEM`(typeidx : typeidx, elemidx : elemidx)
  | `ARRAY.GET`(`sx?` : sx?, typeidx : typeidx)
  | `ARRAY.SET`(typeidx : typeidx)
  | `ARRAY.LEN`
  | `ARRAY.FILL`(typeidx : typeidx)
  | `ARRAY.COPY`(typeidx : typeidx, typeidx : typeidx)
  | `ARRAY.INIT_DATA`(typeidx : typeidx, dataidx : dataidx)
  | `ARRAY.INIT_ELEM`(typeidx : typeidx, elemidx : elemidx)
  | `EXTERN.CONVERT_ANY`
  | `ANY.CONVERT_EXTERN`
  | CONST(numtype : numtype, num_(numtype))
  | UNOP(numtype : numtype, unop_(numtype))
  | BINOP(numtype : numtype, binop_(numtype))
  | TESTOP(numtype : numtype, testop_(numtype))
  | RELOP(numtype : numtype, relop_(numtype))
  | CVTOP(numtype_1 : numtype, numtype_2 : numtype, cvtop__(numtype_2, numtype_1))
  | VCONST(vectype : vectype, vec_(vectype))
  | VVUNOP(vectype : vectype, vvunop : vvunop)
  | VVBINOP(vectype : vectype, vvbinop : vvbinop)
  | VVTERNOP(vectype : vectype, vvternop : vvternop)
  | VVTESTOP(vectype : vectype, vvtestop : vvtestop)
  | VUNOP(shape : shape, vunop_(shape))
  | VBINOP(shape : shape, vbinop_(shape))
  | VTERNOP(shape : shape, vternop_(shape))
  | VTESTOP(shape : shape, vtestop_(shape))
  | VRELOP(shape : shape, vrelop_(shape))
  | VSHIFTOP(ishape : ishape, vshiftop_(ishape))
  | VBITMASK(ishape : ishape)
  | VSWIZZLOP(bshape : bshape, vswizzlop_(bshape))
  | VSHUFFLE(bshape : bshape, `laneidx*` : laneidx*)
    -- if (`%`_dim(|laneidx*{laneidx <- `laneidx*`}|) = $dim(bshape!`%`_bshape.0))
  | VEXTUNOP(ishape_1 : ishape, ishape_2 : ishape, vextunop__(ishape_2, ishape_1))
  | VEXTBINOP(ishape_1 : ishape, ishape_2 : ishape, vextbinop__(ishape_2, ishape_1))
  | VEXTTERNOP(ishape_1 : ishape, ishape_2 : ishape, vextternop__(ishape_2, ishape_1))
  | VNARROW(ishape_1 : ishape, ishape_2 : ishape, sx : sx)
    -- if (($lsize($lanetype(ishape_2!`%`_ishape.0)) = (2 * $lsize($lanetype(ishape_1!`%`_ishape.0)))) /\ ((2 * $lsize($lanetype(ishape_1!`%`_ishape.0))) <= 32))
  | VCVTOP(shape_1 : shape, shape_2 : shape, vcvtop__(shape_2, shape_1))
  | VSPLAT(shape : shape)
  | VEXTRACT_LANE(shape : shape, `sx?` : sx?, laneidx : laneidx)
    -- if ((sx?{sx <- `sx?`} = ?()) <=> ($lanetype(shape) <- [I32_lanetype I64_lanetype F32_lanetype F64_lanetype]))
  | VREPLACE_LANE(shape : shape, laneidx : laneidx)
  | `REF.I31_NUM`(u31 : u31)
  | `REF.NULL_ADDR`
  | `REF.STRUCT_ADDR`(structaddr : structaddr)
  | `REF.ARRAY_ADDR`(arrayaddr : arrayaddr)
  | `REF.FUNC_ADDR`(funcaddr : funcaddr)
  | `REF.EXN_ADDR`(exnaddr : exnaddr)
  | `REF.HOST_ADDR`(hostaddr : hostaddr)
  | `REF.EXTERN`(ref : ref)
  | `LABEL_%{%}%`(n : n, `instr*` : instr*, `instr*` : instr*)
  | `FRAME_%{%}%`(n : n, frame : frame, `instr*` : instr*)
  | `HANDLER_%{%}%`(n : n, `catch*` : catch*, `instr*` : instr*)
  | TRAP
}

;; test.spectec:1314.1-1315.9
syntax expr = instr*

;; test.spectec:1326.1-1326.35
def $memarg0 : memarg
  ;; test.spectec:1327.1-1327.35
  def $memarg0 = {ALIGN `%`_u32(0), OFFSET `%`_u64(0)}

;; test.spectec:1329.1-1329.69
def $const(consttype : consttype, lit_ : lit_((consttype : consttype <: storagetype))) : instr
  ;; test.spectec:1330.1-1330.43
  def $const{numtype : numtype, c : lit_(((numtype : numtype <: consttype) : consttype <: storagetype))}((numtype : numtype <: consttype), c) = CONST_instr(numtype, c)
  ;; test.spectec:1331.1-1331.44
  def $const{vectype : vectype, c : lit_(((vectype : vectype <: consttype) : consttype <: storagetype))}((vectype : vectype <: consttype), c) = VCONST_instr(vectype, c)

;; test.spectec:1336.1-1336.30
def $free_shape(shape : shape) : free
  ;; test.spectec:1345.1-1345.59
  def $free_shape{lanetype : lanetype, dim : dim}(`%X%`_shape(lanetype, dim)) = $free_lanetype(lanetype)

;; test.spectec:1337.1-1337.38
def $free_blocktype(blocktype : blocktype) : free
  ;; test.spectec:1347.1-1347.75
  def $free_blocktype{`valtype?` : valtype?}(_RESULT_blocktype(valtype?{valtype <- `valtype?`})) = $free_opt($free_valtype(valtype)?{valtype <- `valtype?`})
  ;; test.spectec:1348.1-1348.59
  def $free_blocktype{typeidx : typeidx}(_IDX_blocktype(typeidx)) = $free_typeidx(typeidx)

;; test.spectec:1338.1-1338.30
def $free_catch(catch : catch) : free
  ;; test.spectec:1350.1-1350.90
  def $free_catch{tagidx : tagidx, labelidx : labelidx}(CATCH_catch(tagidx, labelidx)) = $free_tagidx(tagidx) +++ $free_labelidx(labelidx)
  ;; test.spectec:1351.1-1351.94
  def $free_catch{tagidx : tagidx, labelidx : labelidx}(CATCH_REF_catch(tagidx, labelidx)) = $free_tagidx(tagidx) +++ $free_labelidx(labelidx)
  ;; test.spectec:1352.1-1352.63
  def $free_catch{labelidx : labelidx}(CATCH_ALL_catch(labelidx)) = $free_labelidx(labelidx)
  ;; test.spectec:1353.1-1353.67
  def $free_catch{labelidx : labelidx}(CATCH_ALL_REF_catch(labelidx)) = $free_labelidx(labelidx)

;; test.spectec:1504.1-1504.44
rec {

;; test.spectec:1504.1-1504.44
def $shift_labelidxs(labelidx*) : labelidx*
  ;; test.spectec:1505.1-1505.32
  def $shift_labelidxs([]) = []
  ;; test.spectec:1506.1-1506.66
  def $shift_labelidxs{`labelidx'*` : labelidx*}([`%`_labelidx(0)] ++ labelidx'*{labelidx' <- `labelidx'*`}) = $shift_labelidxs(labelidx'*{labelidx' <- `labelidx'*`})
  ;; test.spectec:1507.1-1507.91
  def $shift_labelidxs{labelidx : labelidx, `labelidx'*` : labelidx*}([labelidx] ++ labelidx'*{labelidx' <- `labelidx'*`}) = [`%`_labelidx((((labelidx!`%`_labelidx.0 : nat <:> int) - (1 : nat <:> int)) : int <:> nat))] ++ $shift_labelidxs(labelidx'*{labelidx' <- `labelidx'*`})
}

;; test.spectec:1340.1-1341.31
rec {

;; test.spectec:1340.1-1340.30
def $free_instr(instr : instr) : free
  ;; test.spectec:1355.1-1355.26
  def $free_instr(NOP_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1356.1-1356.34
  def $free_instr(UNREACHABLE_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1357.1-1357.27
  def $free_instr(DROP_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1358.1-1358.86
  def $free_instr{`valtype*?` : valtype*?}(SELECT_instr(valtype*{valtype <- `valtype*`}?{`valtype*` <- `valtype*?`})) = $free_opt($free_list($free_valtype(valtype)*{valtype <- `valtype*`})?{`valtype*` <- `valtype*?`})
  ;; test.spectec:1360.1-1360.92
  def $free_instr{blocktype : blocktype, `instr*` : instr*}(BLOCK_instr(blocktype, instr*{instr <- `instr*`})) = $free_blocktype(blocktype) +++ $free_block(instr*{instr <- `instr*`})
  ;; test.spectec:1361.1-1361.91
  def $free_instr{blocktype : blocktype, `instr*` : instr*}(LOOP_instr(blocktype, instr*{instr <- `instr*`})) = $free_blocktype(blocktype) +++ $free_block(instr*{instr <- `instr*`})
  ;; test.spectec:1362.1-1363.79
  def $free_instr{blocktype : blocktype, `instr_1*` : instr*, `instr_2*` : instr*}(`IF%%ELSE%`_instr(blocktype, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`})) = $free_blocktype(blocktype) +++ $free_block(instr_1*{instr_1 <- `instr_1*`}) +++ $free_block(instr_2*{instr_2 <- `instr_2*`})
  ;; test.spectec:1365.1-1365.56
  def $free_instr{labelidx : labelidx}(BR_instr(labelidx)) = $free_labelidx(labelidx)
  ;; test.spectec:1366.1-1366.59
  def $free_instr{labelidx : labelidx}(BR_IF_instr(labelidx)) = $free_labelidx(labelidx)
  ;; test.spectec:1367.1-1368.69
  def $free_instr{`labelidx*` : labelidx*, labelidx' : labelidx}(BR_TABLE_instr(labelidx*{labelidx <- `labelidx*`}, labelidx')) = $free_list($free_labelidx(labelidx)*{labelidx <- `labelidx*`}) +++ $free_labelidx(labelidx')
  ;; test.spectec:1369.1-1369.64
  def $free_instr{labelidx : labelidx}(BR_ON_NULL_instr(labelidx)) = $free_labelidx(labelidx)
  ;; test.spectec:1370.1-1370.68
  def $free_instr{labelidx : labelidx}(BR_ON_NON_NULL_instr(labelidx)) = $free_labelidx(labelidx)
  ;; test.spectec:1371.1-1372.83
  def $free_instr{labelidx : labelidx, reftype_1 : reftype, reftype_2 : reftype}(BR_ON_CAST_instr(labelidx, reftype_1, reftype_2)) = $free_labelidx(labelidx) +++ $free_reftype(reftype_1) +++ $free_reftype(reftype_2)
  ;; test.spectec:1373.1-1374.83
  def $free_instr{labelidx : labelidx, reftype_1 : reftype, reftype_2 : reftype}(BR_ON_CAST_FAIL_instr(labelidx, reftype_1, reftype_2)) = $free_labelidx(labelidx) +++ $free_reftype(reftype_1) +++ $free_reftype(reftype_2)
  ;; test.spectec:1376.1-1376.55
  def $free_instr{funcidx : funcidx}(CALL_instr(funcidx)) = $free_funcidx(funcidx)
  ;; test.spectec:1377.1-1377.59
  def $free_instr{typeuse : typeuse}(CALL_REF_instr(typeuse)) = $free_typeuse(typeuse)
  ;; test.spectec:1378.1-1379.53
  def $free_instr{tableidx : tableidx, typeuse : typeuse}(CALL_INDIRECT_instr(tableidx, typeuse)) = $free_tableidx(tableidx) +++ $free_typeuse(typeuse)
  ;; test.spectec:1380.1-1380.29
  def $free_instr(RETURN_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1381.1-1381.62
  def $free_instr{funcidx : funcidx}(RETURN_CALL_instr(funcidx)) = $free_funcidx(funcidx)
  ;; test.spectec:1382.1-1382.66
  def $free_instr{typeuse : typeuse}(RETURN_CALL_REF_instr(typeuse)) = $free_typeuse(typeuse)
  ;; test.spectec:1383.1-1384.53
  def $free_instr{tableidx : tableidx, typeuse : typeuse}(RETURN_CALL_INDIRECT_instr(tableidx, typeuse)) = $free_tableidx(tableidx) +++ $free_typeuse(typeuse)
  ;; test.spectec:1386.1-1386.53
  def $free_instr{tagidx : tagidx}(THROW_instr(tagidx)) = $free_tagidx(tagidx)
  ;; test.spectec:1387.1-1387.32
  def $free_instr(THROW_REF_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1388.1-1389.99
  def $free_instr{blocktype : blocktype, `catch*` : catch*, `instr*` : instr*}(TRY_TABLE_instr(blocktype, `%`_list(catch*{catch <- `catch*`}), instr*{instr <- `instr*`})) = $free_blocktype(blocktype) +++ $free_list($free_catch(catch)*{catch <- `catch*`}) +++ $free_list($free_instr(instr)*{instr <- `instr*`})
  ;; test.spectec:1391.1-1391.63
  def $free_instr{numtype : numtype, numlit : num_(numtype)}(CONST_instr(numtype, numlit)) = $free_numtype(numtype)
  ;; test.spectec:1392.1-1392.60
  def $free_instr{numtype : numtype, unop : unop_(numtype)}(UNOP_instr(numtype, unop)) = $free_numtype(numtype)
  ;; test.spectec:1393.1-1393.62
  def $free_instr{numtype : numtype, binop : binop_(numtype)}(BINOP_instr(numtype, binop)) = $free_numtype(numtype)
  ;; test.spectec:1394.1-1394.64
  def $free_instr{numtype : numtype, testop : testop_(numtype)}(TESTOP_instr(numtype, testop)) = $free_numtype(numtype)
  ;; test.spectec:1395.1-1395.62
  def $free_instr{numtype : numtype, relop : relop_(numtype)}(RELOP_instr(numtype, relop)) = $free_numtype(numtype)
  ;; test.spectec:1396.1-1397.55
  def $free_instr{numtype_1 : numtype, numtype_2 : numtype, cvtop : cvtop__(numtype_2, numtype_1)}(CVTOP_instr(numtype_1, numtype_2, cvtop)) = $free_numtype(numtype_1) +++ $free_numtype(numtype_2)
  ;; test.spectec:1399.1-1399.64
  def $free_instr{vectype : vectype, veclit : vec_(vectype)}(VCONST_instr(vectype, veclit)) = $free_vectype(vectype)
  ;; test.spectec:1400.1-1400.64
  def $free_instr{vectype : vectype, vvunop : vvunop}(VVUNOP_instr(vectype, vvunop)) = $free_vectype(vectype)
  ;; test.spectec:1401.1-1401.66
  def $free_instr{vectype : vectype, vvbinop : vvbinop}(VVBINOP_instr(vectype, vvbinop)) = $free_vectype(vectype)
  ;; test.spectec:1402.1-1402.68
  def $free_instr{vectype : vectype, vvternop : vvternop}(VVTERNOP_instr(vectype, vvternop)) = $free_vectype(vectype)
  ;; test.spectec:1403.1-1403.68
  def $free_instr{vectype : vectype, vvtestop : vvtestop}(VVTESTOP_instr(vectype, vvtestop)) = $free_vectype(vectype)
  ;; test.spectec:1404.1-1404.56
  def $free_instr{shape : shape, vunop : vunop_(shape)}(VUNOP_instr(shape, vunop)) = $free_shape(shape)
  ;; test.spectec:1405.1-1405.58
  def $free_instr{shape : shape, vbinop : vbinop_(shape)}(VBINOP_instr(shape, vbinop)) = $free_shape(shape)
  ;; test.spectec:1406.1-1406.60
  def $free_instr{shape : shape, vternop : vternop_(shape)}(VTERNOP_instr(shape, vternop)) = $free_shape(shape)
  ;; test.spectec:1407.1-1407.60
  def $free_instr{shape : shape, vtestop : vtestop_(shape)}(VTESTOP_instr(shape, vtestop)) = $free_shape(shape)
  ;; test.spectec:1408.1-1408.58
  def $free_instr{shape : shape, vrelop : vrelop_(shape)}(VRELOP_instr(shape, vrelop)) = $free_shape(shape)
  ;; test.spectec:1409.1-1409.64
  def $free_instr{ishape : ishape, vshiftop : vshiftop_(ishape)}(VSHIFTOP_instr(ishape, vshiftop)) = $free_shape(ishape!`%`_ishape.0)
  ;; test.spectec:1410.1-1410.55
  def $free_instr{ishape : ishape}(VBITMASK_instr(ishape)) = $free_shape(ishape!`%`_ishape.0)
  ;; test.spectec:1411.1-1411.66
  def $free_instr{bshape : bshape, vswizzlop : vswizzlop_(bshape)}(VSWIZZLOP_instr(bshape, vswizzlop)) = $free_shape(bshape!`%`_bshape.0)
  ;; test.spectec:1412.1-1412.64
  def $free_instr{bshape : bshape, `laneidx*` : laneidx*}(VSHUFFLE_instr(bshape, laneidx*{laneidx <- `laneidx*`})) = $free_shape(bshape!`%`_bshape.0)
  ;; test.spectec:1413.1-1414.49
  def $free_instr{ishape_1 : ishape, ishape_2 : ishape, vextunop : vextunop__(ishape_2, ishape_1)}(VEXTUNOP_instr(ishape_1, ishape_2, vextunop)) = $free_shape(ishape_1!`%`_ishape.0) +++ $free_shape(ishape_2!`%`_ishape.0)
  ;; test.spectec:1415.1-1416.49
  def $free_instr{ishape_1 : ishape, ishape_2 : ishape, vextbinop : vextbinop__(ishape_2, ishape_1)}(VEXTBINOP_instr(ishape_1, ishape_2, vextbinop)) = $free_shape(ishape_1!`%`_ishape.0) +++ $free_shape(ishape_2!`%`_ishape.0)
  ;; test.spectec:1417.1-1418.49
  def $free_instr{ishape_1 : ishape, ishape_2 : ishape, vextternop : vextternop__(ishape_2, ishape_1)}(VEXTTERNOP_instr(ishape_1, ishape_2, vextternop)) = $free_shape(ishape_1!`%`_ishape.0) +++ $free_shape(ishape_2!`%`_ishape.0)
  ;; test.spectec:1419.1-1420.49
  def $free_instr{ishape_1 : ishape, ishape_2 : ishape, sx : sx}(VNARROW_instr(ishape_1, ishape_2, sx)) = $free_shape(ishape_1!`%`_ishape.0) +++ $free_shape(ishape_2!`%`_ishape.0)
  ;; test.spectec:1421.1-1422.47
  def $free_instr{shape_1 : shape, shape_2 : shape, vcvtop : vcvtop__(shape_2, shape_1)}(VCVTOP_instr(shape_1, shape_2, vcvtop)) = $free_shape(shape_1) +++ $free_shape(shape_2)
  ;; test.spectec:1423.1-1423.51
  def $free_instr{shape : shape}(VSPLAT_instr(shape)) = $free_shape(shape)
  ;; test.spectec:1424.1-1424.70
  def $free_instr{shape : shape, `sx?` : sx?, laneidx : laneidx}(VEXTRACT_LANE_instr(shape, sx?{sx <- `sx?`}, laneidx)) = $free_shape(shape)
  ;; test.spectec:1425.1-1425.66
  def $free_instr{shape : shape, laneidx : laneidx}(VREPLACE_LANE_instr(shape, laneidx)) = $free_shape(shape)
  ;; test.spectec:1427.1-1427.62
  def $free_instr{heaptype : heaptype}(`REF.NULL`_instr(heaptype)) = $free_heaptype(heaptype)
  ;; test.spectec:1428.1-1428.34
  def $free_instr(`REF.IS_NULL`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1429.1-1429.38
  def $free_instr(`REF.AS_NON_NULL`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1430.1-1430.29
  def $free_instr(`REF.EQ`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1431.1-1431.59
  def $free_instr{reftype : reftype}(`REF.TEST`_instr(reftype)) = $free_reftype(reftype)
  ;; test.spectec:1432.1-1432.59
  def $free_instr{reftype : reftype}(`REF.CAST`_instr(reftype)) = $free_reftype(reftype)
  ;; test.spectec:1433.1-1433.59
  def $free_instr{funcidx : funcidx}(`REF.FUNC`_instr(funcidx)) = $free_funcidx(funcidx)
  ;; test.spectec:1434.1-1434.30
  def $free_instr(`REF.I31`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1436.1-1436.33
  def $free_instr{sx : sx}(`I31.GET`_instr(sx)) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1438.1-1438.61
  def $free_instr{typeidx : typeidx}(`STRUCT.NEW`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1439.1-1439.69
  def $free_instr{typeidx : typeidx}(`STRUCT.NEW_DEFAULT`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1440.1-1440.69
  def $free_instr{`sx?` : sx?, typeidx : typeidx, u32 : u32}(`STRUCT.GET`_instr(sx?{sx <- `sx?`}, typeidx, u32)) = $free_typeidx(typeidx)
  ;; test.spectec:1441.1-1441.65
  def $free_instr{typeidx : typeidx, u32 : u32}(`STRUCT.SET`_instr(typeidx, u32)) = $free_typeidx(typeidx)
  ;; test.spectec:1443.1-1443.60
  def $free_instr{typeidx : typeidx}(`ARRAY.NEW`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1444.1-1444.68
  def $free_instr{typeidx : typeidx}(`ARRAY.NEW_DEFAULT`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1445.1-1445.70
  def $free_instr{typeidx : typeidx, u32 : u32}(`ARRAY.NEW_FIXED`_instr(typeidx, u32)) = $free_typeidx(typeidx)
  ;; test.spectec:1446.1-1447.51
  def $free_instr{typeidx : typeidx, dataidx : dataidx}(`ARRAY.NEW_DATA`_instr(typeidx, dataidx)) = $free_typeidx(typeidx) +++ $free_dataidx(dataidx)
  ;; test.spectec:1448.1-1449.51
  def $free_instr{typeidx : typeidx, elemidx : elemidx}(`ARRAY.NEW_ELEM`_instr(typeidx, elemidx)) = $free_typeidx(typeidx) +++ $free_elemidx(elemidx)
  ;; test.spectec:1450.1-1450.64
  def $free_instr{`sx?` : sx?, typeidx : typeidx}(`ARRAY.GET`_instr(sx?{sx <- `sx?`}, typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1451.1-1451.60
  def $free_instr{typeidx : typeidx}(`ARRAY.SET`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1452.1-1452.32
  def $free_instr(`ARRAY.LEN`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1453.1-1453.61
  def $free_instr{typeidx : typeidx}(`ARRAY.FILL`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1454.1-1455.55
  def $free_instr{typeidx_1 : typeidx, typeidx_2 : typeidx}(`ARRAY.COPY`_instr(typeidx_1, typeidx_2)) = $free_typeidx(typeidx_1) +++ $free_typeidx(typeidx_2)
  ;; test.spectec:1456.1-1457.51
  def $free_instr{typeidx : typeidx, dataidx : dataidx}(`ARRAY.INIT_DATA`_instr(typeidx, dataidx)) = $free_typeidx(typeidx) +++ $free_dataidx(dataidx)
  ;; test.spectec:1458.1-1459.51
  def $free_instr{typeidx : typeidx, elemidx : elemidx}(`ARRAY.INIT_ELEM`_instr(typeidx, elemidx)) = $free_typeidx(typeidx) +++ $free_elemidx(elemidx)
  ;; test.spectec:1461.1-1461.41
  def $free_instr(`EXTERN.CONVERT_ANY`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1462.1-1462.41
  def $free_instr(`ANY.CONVERT_EXTERN`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1464.1-1464.63
  def $free_instr{localidx : localidx}(`LOCAL.GET`_instr(localidx)) = $free_localidx(localidx)
  ;; test.spectec:1465.1-1465.63
  def $free_instr{localidx : localidx}(`LOCAL.SET`_instr(localidx)) = $free_localidx(localidx)
  ;; test.spectec:1466.1-1466.63
  def $free_instr{localidx : localidx}(`LOCAL.TEE`_instr(localidx)) = $free_localidx(localidx)
  ;; test.spectec:1468.1-1468.67
  def $free_instr{globalidx : globalidx}(`GLOBAL.GET`_instr(globalidx)) = $free_globalidx(globalidx)
  ;; test.spectec:1469.1-1469.67
  def $free_instr{globalidx : globalidx}(`GLOBAL.SET`_instr(globalidx)) = $free_globalidx(globalidx)
  ;; test.spectec:1471.1-1471.63
  def $free_instr{tableidx : tableidx}(`TABLE.GET`_instr(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:1472.1-1472.63
  def $free_instr{tableidx : tableidx}(`TABLE.SET`_instr(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:1473.1-1473.64
  def $free_instr{tableidx : tableidx}(`TABLE.SIZE`_instr(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:1474.1-1474.64
  def $free_instr{tableidx : tableidx}(`TABLE.GROW`_instr(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:1475.1-1475.64
  def $free_instr{tableidx : tableidx}(`TABLE.FILL`_instr(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:1476.1-1477.59
  def $free_instr{tableidx_1 : tableidx, tableidx_2 : tableidx}(`TABLE.COPY`_instr(tableidx_1, tableidx_2)) = $free_tableidx(tableidx_1) +++ $free_tableidx(tableidx_2)
  ;; test.spectec:1478.1-1479.53
  def $free_instr{tableidx : tableidx, elemidx : elemidx}(`TABLE.INIT`_instr(tableidx, elemidx)) = $free_tableidx(tableidx) +++ $free_elemidx(elemidx)
  ;; test.spectec:1480.1-1480.60
  def $free_instr{elemidx : elemidx}(`ELEM.DROP`_instr(elemidx)) = $free_elemidx(elemidx)
  ;; test.spectec:1482.1-1483.49
  def $free_instr{numtype : numtype, `loadop?` : loadop_(numtype)?, memidx : memidx, memarg : memarg}(LOAD_instr(numtype, loadop?{loadop <- `loadop?`}, memidx, memarg)) = $free_numtype(numtype) +++ $free_memidx(memidx)
  ;; test.spectec:1484.1-1485.49
  def $free_instr{numtype : numtype, `storeop?` : storeop_(numtype)?, memidx : memidx, memarg : memarg}(STORE_instr(numtype, storeop?{storeop <- `storeop?`}, memidx, memarg)) = $free_numtype(numtype) +++ $free_memidx(memidx)
  ;; test.spectec:1486.1-1487.49
  def $free_instr{vectype : vectype, `vloadop?` : vloadop_(vectype)?, memidx : memidx, memarg : memarg}(VLOAD_instr(vectype, vloadop?{vloadop <- `vloadop?`}, memidx, memarg)) = $free_vectype(vectype) +++ $free_memidx(memidx)
  ;; test.spectec:1488.1-1489.49
  def $free_instr{vectype : vectype, sz : sz, memidx : memidx, memarg : memarg, laneidx : laneidx}(VLOAD_LANE_instr(vectype, sz, memidx, memarg, laneidx)) = $free_vectype(vectype) +++ $free_memidx(memidx)
  ;; test.spectec:1490.1-1491.49
  def $free_instr{vectype : vectype, memidx : memidx, memarg : memarg}(VSTORE_instr(vectype, memidx, memarg)) = $free_vectype(vectype) +++ $free_memidx(memidx)
  ;; test.spectec:1492.1-1493.49
  def $free_instr{vectype : vectype, sz : sz, memidx : memidx, memarg : memarg, laneidx : laneidx}(VSTORE_LANE_instr(vectype, sz, memidx, memarg, laneidx)) = $free_vectype(vectype) +++ $free_memidx(memidx)
  ;; test.spectec:1494.1-1494.59
  def $free_instr{memidx : memidx}(`MEMORY.SIZE`_instr(memidx)) = $free_memidx(memidx)
  ;; test.spectec:1495.1-1495.59
  def $free_instr{memidx : memidx}(`MEMORY.GROW`_instr(memidx)) = $free_memidx(memidx)
  ;; test.spectec:1496.1-1496.59
  def $free_instr{memidx : memidx}(`MEMORY.FILL`_instr(memidx)) = $free_memidx(memidx)
  ;; test.spectec:1497.1-1498.51
  def $free_instr{memidx_1 : memidx, memidx_2 : memidx}(`MEMORY.COPY`_instr(memidx_1, memidx_2)) = $free_memidx(memidx_1) +++ $free_memidx(memidx_2)
  ;; test.spectec:1499.1-1500.49
  def $free_instr{memidx : memidx, dataidx : dataidx}(`MEMORY.INIT`_instr(memidx, dataidx)) = $free_memidx(memidx) +++ $free_dataidx(dataidx)
  ;; test.spectec:1501.1-1501.60
  def $free_instr{dataidx : dataidx}(`DATA.DROP`_instr(dataidx)) = $free_dataidx(dataidx)

;; test.spectec:1341.1-1341.31
def $free_block(instr*) : free
  ;; test.spectec:1509.1-1510.47
  def $free_block{`instr*` : instr*, free : free}(instr*{instr <- `instr*`}) = free[LABELS_free = $shift_labelidxs(free.LABELS_free)]
    -- if (free = $free_list($free_instr(instr)*{instr <- `instr*`}))
}

;; test.spectec:1342.1-1342.28
def $free_expr(expr : expr) : free
  ;; test.spectec:1513.1-1513.57
  def $free_expr{`instr*` : instr*}(instr*{instr <- `instr*`}) = $free_list($free_instr(instr)*{instr <- `instr*`})

;; test.spectec:1526.1-1527.43
syntax elemmode = 
  | ACTIVE(tableidx : tableidx, expr : expr)
  | PASSIVE
  | DECLARE

;; test.spectec:1528.1-1529.31
syntax datamode = 
  | ACTIVE(memidx : memidx, expr : expr)
  | PASSIVE

;; test.spectec:1531.1-1532.15
syntax type = 
  | TYPE(rectype : rectype)

;; test.spectec:1534.1-1535.14
syntax tag = 
  | TAG(tagtype : tagtype)

;; test.spectec:1537.1-1538.25
syntax global = 
  | GLOBAL(globaltype : globaltype, expr : expr)

;; test.spectec:1540.1-1541.17
syntax mem = 
  | MEMORY(memtype : memtype)

;; test.spectec:1543.1-1544.23
syntax table = 
  | TABLE(tabletype : tabletype, expr : expr)

;; test.spectec:1546.1-1547.22
syntax data = 
  | DATA(`byte*` : byte*, datamode : datamode)

;; test.spectec:1549.1-1550.16
syntax local = 
  | LOCAL(valtype : valtype)

;; test.spectec:1552.1-1553.27
syntax func = 
  | FUNC(typeidx : typeidx, `local*` : local*, expr : expr)

;; test.spectec:1555.1-1556.30
syntax elem = 
  | ELEM(reftype : reftype, `expr*` : expr*, elemmode : elemmode)

;; test.spectec:1558.1-1559.16
syntax start = 
  | START(funcidx : funcidx)

;; test.spectec:1561.1-1562.30
syntax import = 
  | IMPORT(name : name, name : name, externtype : externtype)

;; test.spectec:1564.1-1565.24
syntax export = 
  | EXPORT(name : name, externidx : externidx)

;; test.spectec:1567.1-1579.17
syntax module = 
  | MODULE(list(syntax type), list(syntax import), list(syntax tag), list(syntax global), list(syntax mem), list(syntax table), list(syntax func), list(syntax data), list(syntax elem), `start?` : start?, list(syntax export))

;; test.spectec:1594.1-1594.28
def $free_type(type : type) : free
  ;; test.spectec:1611.1-1611.54
  def $free_type{rectype : rectype}(TYPE_type(rectype)) = $free_rectype(rectype)

;; test.spectec:1595.1-1595.26
def $free_tag(tag : tag) : free
  ;; test.spectec:1613.1-1613.52
  def $free_tag{tagtype : tagtype}(TAG_tag(tagtype)) = $free_tagtype(tagtype)

;; test.spectec:1596.1-1596.32
def $free_global(global : global) : free
  ;; test.spectec:1615.1-1616.51
  def $free_global{globaltype : globaltype, expr : expr}(GLOBAL_global(globaltype, expr)) = $free_globaltype(globaltype) +++ $free_expr(expr)

;; test.spectec:1597.1-1597.26
def $free_mem(mem : mem) : free
  ;; test.spectec:1618.1-1618.55
  def $free_mem{memtype : memtype}(MEMORY_mem(memtype)) = $free_memtype(memtype)

;; test.spectec:1598.1-1598.30
def $free_table(table : table) : free
  ;; test.spectec:1620.1-1621.49
  def $free_table{tabletype : tabletype, expr : expr}(TABLE_table(tabletype, expr)) = $free_tabletype(tabletype) +++ $free_expr(expr)

;; test.spectec:1599.1-1599.30
def $free_local(local : local) : free
  ;; test.spectec:1623.1-1623.44
  def $free_local{t : valtype}(LOCAL_local(t)) = $free_valtype(t)

;; test.spectec:1600.1-1600.28
def $free_func(func : func) : free
  ;; test.spectec:1625.1-1627.35
  def $free_func{typeidx : typeidx, `local*` : local*, expr : expr}(FUNC_func(typeidx, local*{local <- `local*`}, expr)) = $free_typeidx(typeidx) +++ $free_list($free_local(local)*{local <- `local*`}) +++ $free_block(expr)[LOCALS_free = []]

;; test.spectec:1603.1-1603.36
def $free_datamode(datamode : datamode) : free
  ;; test.spectec:1639.1-1639.82
  def $free_datamode{memidx : memidx, expr : expr}(ACTIVE_datamode(memidx, expr)) = $free_memidx(memidx) +++ $free_expr(expr)
  ;; test.spectec:1640.1-1640.33
  def $free_datamode(PASSIVE_datamode) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:1601.1-1601.28
def $free_data(data : data) : free
  ;; test.spectec:1629.1-1629.63
  def $free_data{`byte*` : byte*, datamode : datamode}(DATA_data(byte*{byte <- `byte*`}, datamode)) = $free_datamode(datamode)

;; test.spectec:1604.1-1604.36
def $free_elemmode(elemmode : elemmode) : free
  ;; test.spectec:1635.1-1635.88
  def $free_elemmode{tableidx : tableidx, expr : expr}(ACTIVE_elemmode(tableidx, expr)) = $free_tableidx(tableidx) +++ $free_expr(expr)
  ;; test.spectec:1636.1-1636.33
  def $free_elemmode(PASSIVE_elemmode) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1637.1-1637.33
  def $free_elemmode(DECLARE_elemmode) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:1602.1-1602.28
def $free_elem(elem : elem) : free
  ;; test.spectec:1631.1-1633.27
  def $free_elem{reftype : reftype, `expr*` : expr*, elemmode : elemmode}(ELEM_elem(reftype, expr*{expr <- `expr*`}, elemmode)) = $free_reftype(reftype) +++ $free_list($free_expr(expr)*{expr <- `expr*`}) +++ $free_elemmode(elemmode)

;; test.spectec:1605.1-1605.30
def $free_start(start : start) : free
  ;; test.spectec:1642.1-1642.56
  def $free_start{funcidx : funcidx}(START_start(funcidx)) = $free_funcidx(funcidx)

;; test.spectec:1606.1-1606.32
def $free_import(import : import) : free
  ;; test.spectec:1644.1-1644.81
  def $free_import{name_1 : name, name_2 : name, externtype : externtype}(IMPORT_import(name_1, name_2, externtype)) = $free_externtype(externtype)

;; test.spectec:1607.1-1607.32
def $free_export(export : export) : free
  ;; test.spectec:1646.1-1646.69
  def $free_export{name : name, externidx : externidx}(EXPORT_export(name, externidx)) = $free_externidx(externidx)

;; test.spectec:1608.1-1608.32
def $free_module(module : module) : free
  ;; test.spectec:1648.1-1659.36
  def $free_module{`type*` : type*, `import*` : import*, `tag*` : tag*, `global*` : global*, `mem*` : mem*, `table*` : table*, `func*` : func*, `data*` : data*, `elem*` : elem*, `start?` : start?, `export*` : export*}(MODULE_module(`%`_list(type*{type <- `type*`}), `%`_list(import*{import <- `import*`}), `%`_list(tag*{tag <- `tag*`}), `%`_list(global*{global <- `global*`}), `%`_list(mem*{mem <- `mem*`}), `%`_list(table*{table <- `table*`}), `%`_list(func*{func <- `func*`}), `%`_list(data*{data <- `data*`}), `%`_list(elem*{elem <- `elem*`}), start?{start <- `start?`}, `%`_list(export*{export <- `export*`}))) = $free_list($free_type(type)*{type <- `type*`}) +++ $free_list($free_tag(tag)*{tag <- `tag*`}) +++ $free_list($free_global(global)*{global <- `global*`}) +++ $free_list($free_mem(mem)*{mem <- `mem*`}) +++ $free_list($free_table(table)*{table <- `table*`}) +++ $free_list($free_func(func)*{func <- `func*`}) +++ $free_list($free_data(data)*{data <- `data*`}) +++ $free_list($free_elem(elem)*{elem <- `elem*`}) +++ $free_opt($free_start(start)?{start <- `start?`}) +++ $free_list($free_import(import)*{import <- `import*`}) +++ $free_list($free_export(export)*{export <- `export*`})

;; test.spectec:1662.1-1662.89
def $funcidx_module(module : module) : funcidx*
  ;; test.spectec:1663.1-1663.57
  def $funcidx_module{module : module}(module) = $free_module(module).FUNCS_free

;; test.spectec:1665.1-1665.87
def $dataidx_funcs(func*) : dataidx*
  ;; test.spectec:1666.1-1666.64
  def $dataidx_funcs{`func*` : func*}(func*{func <- `func*`}) = $free_list($free_func(func)*{func <- `func*`}).DATAS_free

;; test.spectec:1682.1-1683.16
syntax init = 
  | SET
  | UNSET

;; test.spectec:1685.1-1686.15
syntax localtype = 
  | `%%`(init : init, valtype : valtype)

;; test.spectec:1688.1-1689.57
syntax instrtype = 
  | `%->_%%`(resulttype : resulttype, `localidx*` : localidx*, resulttype : resulttype)

;; test.spectec:1714.1-1715.58
syntax context = 
{
  TYPES deftype*,
  TAGS tagtype*,
  GLOBALS globaltype*,
  MEMS memtype*,
  TABLES tabletype*,
  FUNCS deftype*,
  DATAS datatype*,
  ELEMS elemtype*,
  LOCALS localtype*,
  LABELS resulttype*,
  RETURN resulttype?,
  REFS funcidx*,
  RECS subtype*
}

;; test.spectec:1723.1-1723.158
rec {

;; test.spectec:1723.1-1723.158
def $with_locals(context : context, localidx*, localtype*) : context
  ;; test.spectec:1725.1-1725.34
  def $with_locals{C : context}(C, [], []) = C
  ;; test.spectec:1726.1-1726.90
  def $with_locals{C : context, x_1 : idx, `x*` : idx*, lct_1 : localtype, `lct*` : localtype*}(C, [x_1] ++ x*{x <- `x*`}, [lct_1] ++ lct*{lct <- `lct*`}) = $with_locals(C[LOCALS_context[x_1!`%`_idx.0] = lct_1], x*{x <- `x*`}, lct*{lct <- `lct*`})
}

;; test.spectec:1736.1-1736.94
rec {

;; test.spectec:1736.1-1736.94
def $clos_deftypes(deftype*) : deftype*
  ;; test.spectec:1745.1-1745.30
  def $clos_deftypes([]) = []
  ;; test.spectec:1746.1-1746.101
  def $clos_deftypes{`dt*` : deftype*, dt_n : deftype, `dt'*` : deftype*}(dt*{dt <- `dt*`} ++ [dt_n]) = dt'*{dt' <- `dt'*`} ++ [$subst_all_deftype(dt_n, (dt' : deftype <: typeuse)*{dt' <- `dt'*`})]
    -- if (dt'*{dt' <- `dt'*`} = $clos_deftypes(dt*{dt <- `dt*`}))
}

;; test.spectec:1731.1-1731.93
def $clos_valtype(context : context, valtype : valtype) : valtype
  ;; test.spectec:1739.1-1739.89
  def $clos_valtype{C : context, t : valtype, `dt*` : deftype*}(C, t) = $subst_all_valtype(t, (dt : deftype <: typeuse)*{dt <- `dt*`})
    -- if (dt*{dt <- `dt*`} = $clos_deftypes(C.TYPES_context))

;; test.spectec:1732.1-1732.93
def $clos_deftype(context : context, deftype : deftype) : deftype
  ;; test.spectec:1740.1-1740.93
  def $clos_deftype{C : context, dt : deftype, `dt'*` : deftype*}(C, dt) = $subst_all_deftype(dt, (dt' : deftype <: typeuse)*{dt' <- `dt'*`})
    -- if (dt'*{dt' <- `dt'*`} = $clos_deftypes(C.TYPES_context))

;; test.spectec:1733.1-1733.93
def $clos_tagtype(context : context, tagtype : tagtype) : tagtype
  ;; test.spectec:1741.1-1741.91
  def $clos_tagtype{C : context, jt : tagtype, `dt*` : deftype*}(C, jt) = $subst_all_tagtype(jt, (dt : deftype <: typeuse)*{dt <- `dt*`})
    -- if (dt*{dt <- `dt*`} = $clos_deftypes(C.TYPES_context))

;; test.spectec:1734.1-1734.102
def $clos_externtype(context : context, externtype : externtype) : externtype
  ;; test.spectec:1742.1-1742.97
  def $clos_externtype{C : context, xt : externtype, `dt*` : deftype*}(C, xt) = $subst_all_externtype(xt, (dt : deftype <: typeuse)*{dt <- `dt*`})
    -- if (dt*{dt <- `dt*`} = $clos_deftypes(C.TYPES_context))

;; test.spectec:1735.1-1735.102
def $clos_moduletype(context : context, moduletype : moduletype) : moduletype
  ;; test.spectec:1743.1-1743.99
  def $clos_moduletype{C : context, mmt : moduletype, `dt*` : deftype*}(C, mmt) = $subst_all_moduletype(mmt, (dt : deftype <: typeuse)*{dt <- `dt*`})
    -- if (dt*{dt <- `dt*`} = $clos_deftypes(C.TYPES_context))

;; test.spectec:1761.1-1761.91
relation Numtype_ok: `%|-%:OK`(context, numtype)
  ;; test.spectec:1768.1-1769.20
  rule _{C : context, numtype : numtype}:
    `%|-%:OK`(C, numtype)

;; test.spectec:1762.1-1762.91
relation Vectype_ok: `%|-%:OK`(context, vectype)
  ;; test.spectec:1771.1-1772.20
  rule _{C : context, vectype : vectype}:
    `%|-%:OK`(C, vectype)

;; test.spectec:1842.1-1843.79
syntax oktypenat = 
  | OK(nat)

;; test.spectec:1845.1-1845.103
relation Packtype_ok: `%|-%:OK`(context, packtype)
  ;; test.spectec:1873.1-1874.21
  rule _{C : context, packtype : packtype}:
    `%|-%:OK`(C, packtype)

;; test.spectec:2168.1-2168.116
relation Packtype_sub: `%|-%<:%`(context, packtype, packtype)
  ;; test.spectec:2177.1-2178.28
  rule _{C : context, packtype : packtype}:
    `%|-%<:%`(C, packtype, packtype)

;; test.spectec:2026.1-2026.103
relation Numtype_sub: `%|-%<:%`(context, numtype, numtype)
  ;; test.spectec:2032.1-2033.26
  rule _{C : context, numtype : numtype}:
    `%|-%<:%`(C, numtype, numtype)

;; test.spectec:1827.1-1828.70
relation Expand: `%~~%`(deftype, comptype)
  ;; test.spectec:1832.1-1832.91
  rule _{deftype : deftype, comptype : comptype, `final?` : final?, `typeuse*` : typeuse*}:
    `%~~%`(deftype, comptype)
    -- if ($unrolldt(deftype) = SUB_subtype(final?{final <- `final?`}, typeuse*{typeuse <- `typeuse*`}, comptype))

;; test.spectec:2027.1-2027.103
relation Vectype_sub: `%|-%<:%`(context, vectype, vectype)
  ;; test.spectec:2035.1-2036.26
  rule _{C : context, vectype : vectype}:
    `%|-%<:%`(C, vectype, vectype)

;; test.spectec:1912.1-1912.70
def $before(typeuse : typeuse, nat : nat) : bool
  ;; test.spectec:1913.1-1913.30
  def $before{j : n, i : nat}(REC_typeuse(j), i) = (j < i)
  ;; test.spectec:1914.1-1914.45
  def $before{typeuse : typeuse, i : nat}(typeuse, i) = true

;; test.spectec:1916.1-1916.44
def $unrollht_(context : context, heaptype : heaptype) : subtype
  ;; test.spectec:1917.1-1917.48
  def $unrollht_{C : context, deftype : deftype}(C, (deftype : deftype <: heaptype)) = $unrolldt(deftype)
  ;; test.spectec:1918.1-1918.62
  def $unrollht_{C : context, typeidx : typeidx}(C, _IDX_heaptype(typeidx)) = $unrolldt(C.TYPES_context[typeidx!`%`_typeidx.0])
  ;; test.spectec:1919.1-1919.37
  def $unrollht_{C : context, i : n}(C, REC_heaptype(i)) = C.RECS_context[i]

;; test.spectec:1763.1-2170.117
rec {

;; test.spectec:1763.1-1763.92
relation Heaptype_ok: `%|-%:OK`(context, heaptype)
  ;; test.spectec:1774.1-1775.24
  rule abs{C : context, absheaptype : absheaptype}:
    `%|-%:OK`(C, (absheaptype : absheaptype <: heaptype))

  ;; test.spectec:1777.1-1779.35
  rule typeuse{C : context, typeuse : typeuse}:
    `%|-%:OK`(C, (typeuse : typeuse <: heaptype))
    -- Typeuse_ok: `%|-%:OK`(C, typeuse)

  ;; test.spectec:1781.1-1782.16
  rule bot{C : context}:
    `%|-%:OK`(C, BOT_heaptype)

;; test.spectec:1764.1-1764.91
relation Reftype_ok: `%|-%:OK`(context, reftype)
  ;; test.spectec:1784.1-1786.37
  rule _{C : context, heaptype : heaptype}:
    `%|-%:OK`(C, REF_reftype(NULL_null?{}, heaptype))
    -- Heaptype_ok: `%|-%:OK`(C, heaptype)

;; test.spectec:1765.1-1765.91
relation Valtype_ok: `%|-%:OK`(context, valtype)
  ;; test.spectec:1788.1-1790.35
  rule num{C : context, numtype : numtype}:
    `%|-%:OK`(C, (numtype : numtype <: valtype))
    -- Numtype_ok: `%|-%:OK`(C, numtype)

  ;; test.spectec:1792.1-1794.35
  rule vec{C : context, vectype : vectype}:
    `%|-%:OK`(C, (vectype : vectype <: valtype))
    -- Vectype_ok: `%|-%:OK`(C, vectype)

  ;; test.spectec:1796.1-1798.35
  rule ref{C : context, reftype : reftype}:
    `%|-%:OK`(C, (reftype : reftype <: valtype))
    -- Reftype_ok: `%|-%:OK`(C, reftype)

  ;; test.spectec:1800.1-1801.16
  rule bot{C : context}:
    `%|-%:OK`(C, BOT_valtype)

;; test.spectec:1766.1-1766.94
relation Typeuse_ok: `%|-%:OK`(context, typeuse)
  ;; test.spectec:1860.1-1862.30
  rule typeidx{C : context, typeidx : typeidx, dt : deftype}:
    `%|-%:OK`(C, _IDX_typeuse(typeidx))
    -- if (C.TYPES_context[typeidx!`%`_typeidx.0] = dt)

  ;; test.spectec:1864.1-1866.23
  rule rec{C : context, i : n, st : subtype}:
    `%|-%:OK`(C, REC_typeuse(i))
    -- if (C.RECS_context[i] = st)

  ;; test.spectec:1868.1-1870.35
  rule deftype{C : context, deftype : deftype}:
    `%|-%:OK`(C, (deftype : deftype <: typeuse))
    -- Deftype_ok: `%|-%:OK`(C, deftype)

;; test.spectec:1807.1-1807.100
relation Resulttype_ok: `%|-%:OK`(context, resulttype)
  ;; test.spectec:1814.1-1816.32
  rule _{C : context, `t*` : valtype*}:
    `%|-%:OK`(C, `%`_resulttype(t*{t <- `t*`}))
    -- (Valtype_ok: `%|-%:OK`(C, t))*{t <- `t*`}

;; test.spectec:1846.1-1846.104
relation Fieldtype_ok: `%|-%:OK`(context, fieldtype)
  ;; test.spectec:1884.1-1886.43
  rule _{C : context, storagetype : storagetype}:
    `%|-%:OK`(C, `%%`_fieldtype(MUT_mut?{}, storagetype))
    -- Storagetype_ok: `%|-%:OK`(C, storagetype)

;; test.spectec:1847.1-1847.106
relation Storagetype_ok: `%|-%:OK`(context, storagetype)
  ;; test.spectec:1876.1-1878.35
  rule val{C : context, valtype : valtype}:
    `%|-%:OK`(C, (valtype : valtype <: storagetype))
    -- Valtype_ok: `%|-%:OK`(C, valtype)

  ;; test.spectec:1880.1-1882.37
  rule pack{C : context, packtype : packtype}:
    `%|-%:OK`(C, (packtype : packtype <: storagetype))
    -- Packtype_ok: `%|-%:OK`(C, packtype)

;; test.spectec:1848.1-1848.103
relation Comptype_ok: `%|-%:OK`(context, comptype)
  ;; test.spectec:1889.1-1891.42
  rule struct{C : context, `fieldtype*` : fieldtype*}:
    `%|-%:OK`(C, STRUCT_comptype(`%`_list(fieldtype*{fieldtype <- `fieldtype*`})))
    -- (Fieldtype_ok: `%|-%:OK`(C, fieldtype))*{fieldtype <- `fieldtype*`}

  ;; test.spectec:1893.1-1895.39
  rule array{C : context, fieldtype : fieldtype}:
    `%|-%:OK`(C, ARRAY_comptype(fieldtype))
    -- Fieldtype_ok: `%|-%:OK`(C, fieldtype)

  ;; test.spectec:1897.1-1900.35
  rule func{C : context, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:OK`(C, `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Resulttype_ok: `%|-%:OK`(C, `%`_resulttype(t_1*{t_1 <- `t_1*`}))
    -- Resulttype_ok: `%|-%:OK`(C, `%`_resulttype(t_2*{t_2 <- `t_2*`}))

;; test.spectec:1851.1-1851.126
relation Subtype_ok2: `%|-%:%`(context, subtype, oktypenat)
  ;; test.spectec:1921.1-1930.49
  rule _{C : context, `typeuse*` : typeuse*, comptype : comptype, i : nat, `comptype'*` : comptype*, `typeuse'**` : typeuse**}:
    `%|-%:%`(C, SUB_subtype(FINAL_final?{}, typeuse*{typeuse <- `typeuse*`}, comptype), OK_oktypenat(i))
    -- if (|typeuse*{typeuse <- `typeuse*`}| <= 1)
    -- (Typeuse_ok: `%|-%:OK`(C, typeuse))*{typeuse <- `typeuse*`}
    -- (if $before(typeuse, i))*{typeuse <- `typeuse*`}
    -- (if ($unrollht_(C, (typeuse : typeuse <: heaptype)) = SUB_subtype(?(), typeuse'*{typeuse' <- `typeuse'*`}, comptype')))*{comptype' <- `comptype'*`, typeuse <- `typeuse*`, `typeuse'*` <- `typeuse'**`}
    -- Comptype_ok: `%|-%:OK`(C, comptype)
    -- (Comptype_sub: `%|-%<:%`(C, comptype, comptype'))*{comptype' <- `comptype'*`}

;; test.spectec:1852.1-1852.126
relation Rectype_ok2: `%|-%:%`(context, rectype, oktypenat)
  ;; test.spectec:1942.1-1943.23
  rule empty{C : context, i : nat}:
    `%|-%:%`(C, REC_rectype(`%`_list([])), OK_oktypenat(i))

  ;; test.spectec:1945.1-1948.49
  rule cons{C : context, subtype_1 : subtype, `subtype*` : subtype*, i : nat}:
    `%|-%:%`(C, REC_rectype(`%`_list([subtype_1] ++ subtype*{subtype <- `subtype*`})), OK_oktypenat(i))
    -- Subtype_ok2: `%|-%:%`(C, subtype_1, OK_oktypenat(i))
    -- Rectype_ok2: `%|-%:%`(C, REC_rectype(`%`_list(subtype*{subtype <- `subtype*`})), OK_oktypenat((i + 1)))

;; test.spectec:1853.1-1853.102
relation Deftype_ok: `%|-%:OK`(context, deftype)
  ;; test.spectec:1951.1-1955.14
  rule _{C : context, rectype : rectype, i : n, n : n, `subtype*` : subtype*}:
    `%|-%:OK`(C, _DEF_deftype(rectype, i))
    -- Rectype_ok2: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS subtype^n{subtype <- `subtype*`}} +++ C, rectype, OK_oktypenat(0))
    -- if (rectype = REC_rectype(`%`_list(subtype^n{subtype <- `subtype*`})))
    -- if (i < n)

;; test.spectec:1856.1-1856.108
relation Comptype_sub: `%|-%<:%`(context, comptype, comptype)
  ;; test.spectec:2200.1-2202.41
  rule struct{C : context, `ft_1*` : fieldtype*, `ft'_1*` : fieldtype*, `ft_2*` : fieldtype*}:
    `%|-%<:%`(C, STRUCT_comptype(`%`_list(ft_1*{ft_1 <- `ft_1*`} ++ ft'_1*{ft'_1 <- `ft'_1*`})), STRUCT_comptype(`%`_list(ft_2*{ft_2 <- `ft_2*`})))
    -- (Fieldtype_sub: `%|-%<:%`(C, ft_1, ft_2))*{ft_1 <- `ft_1*`, ft_2 <- `ft_2*`}

  ;; test.spectec:2204.1-2206.38
  rule array{C : context, ft_1 : fieldtype, ft_2 : fieldtype}:
    `%|-%<:%`(C, ARRAY_comptype(ft_1), ARRAY_comptype(ft_2))
    -- Fieldtype_sub: `%|-%<:%`(C, ft_1, ft_2)

  ;; test.spectec:2208.1-2211.41
  rule func{C : context, `t_11*` : valtype*, `t_12*` : valtype*, `t_21*` : valtype*, `t_22*` : valtype*}:
    `%|-%<:%`(C, `FUNC%->%`_comptype(`%`_resulttype(t_11*{t_11 <- `t_11*`}), `%`_resulttype(t_12*{t_12 <- `t_12*`})), `FUNC%->%`_comptype(`%`_resulttype(t_21*{t_21 <- `t_21*`}), `%`_resulttype(t_22*{t_22 <- `t_22*`})))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_21*{t_21 <- `t_21*`}), `%`_resulttype(t_11*{t_11 <- `t_11*`}))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_12*{t_12 <- `t_12*`}), `%`_resulttype(t_22*{t_22 <- `t_22*`}))

;; test.spectec:1857.1-1857.107
relation Deftype_sub: `%|-%<:%`(context, deftype, deftype)
  ;; test.spectec:2214.1-2216.66
  rule refl{C : context, deftype_1 : deftype, deftype_2 : deftype}:
    `%|-%<:%`(C, deftype_1, deftype_2)
    -- if ($clos_deftype(C, deftype_1) = $clos_deftype(C, deftype_2))

  ;; test.spectec:2218.1-2221.49
  rule super{C : context, deftype_1 : deftype, deftype_2 : deftype, `final?` : final?, `typeuse*` : typeuse*, ct : comptype, i : nat}:
    `%|-%<:%`(C, deftype_1, deftype_2)
    -- if ($unrolldt(deftype_1) = SUB_subtype(final?{final <- `final?`}, typeuse*{typeuse <- `typeuse*`}, ct))
    -- Heaptype_sub: `%|-%<:%`(C, (typeuse*{typeuse <- `typeuse*`}[i] : typeuse <: heaptype), (deftype_2 : deftype <: heaptype))

;; test.spectec:2028.1-2028.104
relation Heaptype_sub: `%|-%<:%`(context, heaptype, heaptype)
  ;; test.spectec:2039.1-2040.28
  rule refl{C : context, heaptype : heaptype}:
    `%|-%<:%`(C, heaptype, heaptype)

  ;; test.spectec:2042.1-2046.48
  rule trans{C : context, heaptype_1 : heaptype, heaptype_2 : heaptype, heaptype' : heaptype}:
    `%|-%<:%`(C, heaptype_1, heaptype_2)
    -- Heaptype_ok: `%|-%:OK`(C, heaptype')
    -- Heaptype_sub: `%|-%<:%`(C, heaptype_1, heaptype')
    -- Heaptype_sub: `%|-%<:%`(C, heaptype', heaptype_2)

  ;; test.spectec:2048.1-2049.17
  rule `eq-any`{C : context}:
    `%|-%<:%`(C, EQ_heaptype, ANY_heaptype)

  ;; test.spectec:2051.1-2052.17
  rule `i31-eq`{C : context}:
    `%|-%<:%`(C, I31_heaptype, EQ_heaptype)

  ;; test.spectec:2054.1-2055.20
  rule `struct-eq`{C : context}:
    `%|-%<:%`(C, STRUCT_heaptype, EQ_heaptype)

  ;; test.spectec:2057.1-2058.19
  rule `array-eq`{C : context}:
    `%|-%<:%`(C, ARRAY_heaptype, EQ_heaptype)

  ;; test.spectec:2060.1-2062.42
  rule struct{C : context, deftype : deftype, `fieldtype*` : fieldtype*}:
    `%|-%<:%`(C, (deftype : deftype <: heaptype), STRUCT_heaptype)
    -- Expand: `%~~%`(deftype, STRUCT_comptype(`%`_list(fieldtype*{fieldtype <- `fieldtype*`})))

  ;; test.spectec:2064.1-2066.40
  rule array{C : context, deftype : deftype, fieldtype : fieldtype}:
    `%|-%<:%`(C, (deftype : deftype <: heaptype), ARRAY_heaptype)
    -- Expand: `%~~%`(deftype, ARRAY_comptype(fieldtype))

  ;; test.spectec:2068.1-2070.42
  rule func{C : context, deftype : deftype, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%<:%`(C, (deftype : deftype <: heaptype), FUNC_heaptype)
    -- Expand: `%~~%`(deftype, `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2072.1-2074.46
  rule def{C : context, deftype_1 : deftype, deftype_2 : deftype}:
    `%|-%<:%`(C, (deftype_1 : deftype <: heaptype), (deftype_2 : deftype <: heaptype))
    -- Deftype_sub: `%|-%<:%`(C, deftype_1, deftype_2)

  ;; test.spectec:2076.1-2078.53
  rule `typeidx-l`{C : context, typeidx : typeidx, heaptype : heaptype}:
    `%|-%<:%`(C, _IDX_heaptype(typeidx), heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, (C.TYPES_context[typeidx!`%`_typeidx.0] : deftype <: heaptype), heaptype)

  ;; test.spectec:2080.1-2082.53
  rule `typeidx-r`{C : context, heaptype : heaptype, typeidx : typeidx}:
    `%|-%<:%`(C, heaptype, _IDX_heaptype(typeidx))
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, (C.TYPES_context[typeidx!`%`_typeidx.0] : deftype <: heaptype))

  ;; test.spectec:2084.1-2086.51
  rule `rec-struct`{C : context, i : n, `final?` : final?, `fieldtype*` : fieldtype*}:
    `%|-%<:%`(C, REC_heaptype(i), STRUCT_heaptype)
    -- if (C.RECS_context[i] = SUB_subtype(final?{final <- `final?`}, [], STRUCT_comptype(`%`_list(fieldtype*{fieldtype <- `fieldtype*`}))))

  ;; test.spectec:2088.1-2090.49
  rule `rec-array`{C : context, i : n, `final?` : final?, fieldtype : fieldtype}:
    `%|-%<:%`(C, REC_heaptype(i), ARRAY_heaptype)
    -- if (C.RECS_context[i] = SUB_subtype(final?{final <- `final?`}, [], ARRAY_comptype(fieldtype)))

  ;; test.spectec:2092.1-2094.51
  rule `rec-func`{C : context, i : n, `final?` : final?, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%<:%`(C, REC_heaptype(i), FUNC_heaptype)
    -- if (C.RECS_context[i] = SUB_subtype(final?{final <- `final?`}, [], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`}))))

  ;; test.spectec:2096.1-2098.43
  rule `rec-sub`{C : context, i : n, `typeuse*` : typeuse*, j : nat, `final?` : final?, ct : comptype}:
    `%|-%<:%`(C, REC_heaptype(i), (typeuse*{typeuse <- `typeuse*`}[j] : typeuse <: heaptype))
    -- if (C.RECS_context[i] = SUB_subtype(final?{final <- `final?`}, typeuse*{typeuse <- `typeuse*`}, ct))

  ;; test.spectec:2100.1-2103.25
  rule none{C : context, heaptype : heaptype}:
    `%|-%<:%`(C, NONE_heaptype, heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, ANY_heaptype)
    -- if (heaptype =/= BOT_heaptype)

  ;; test.spectec:2105.1-2108.25
  rule nofunc{C : context, heaptype : heaptype}:
    `%|-%<:%`(C, NOFUNC_heaptype, heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, FUNC_heaptype)
    -- if (heaptype =/= BOT_heaptype)

  ;; test.spectec:2110.1-2113.25
  rule noexn{C : context, heaptype : heaptype}:
    `%|-%<:%`(C, NOEXN_heaptype, heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, EXN_heaptype)
    -- if (heaptype =/= BOT_heaptype)

  ;; test.spectec:2115.1-2118.25
  rule noextern{C : context, heaptype : heaptype}:
    `%|-%<:%`(C, NOEXTERN_heaptype, heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, EXTERN_heaptype)
    -- if (heaptype =/= BOT_heaptype)

  ;; test.spectec:2120.1-2121.23
  rule bot{C : context, heaptype : heaptype}:
    `%|-%<:%`(C, BOT_heaptype, heaptype)

;; test.spectec:2029.1-2029.103
relation Reftype_sub: `%|-%<:%`(context, reftype, reftype)
  ;; test.spectec:2124.1-2126.37
  rule nonnull{C : context, ht_1 : heaptype, ht_2 : heaptype}:
    `%|-%<:%`(C, REF_reftype(?(), ht_1), REF_reftype(?(), ht_2))
    -- Heaptype_sub: `%|-%<:%`(C, ht_1, ht_2)

  ;; test.spectec:2128.1-2130.37
  rule null{C : context, ht_1 : heaptype, ht_2 : heaptype}:
    `%|-%<:%`(C, REF_reftype(NULL_null?{}, ht_1), REF_reftype(?(NULL_null), ht_2))
    -- Heaptype_sub: `%|-%<:%`(C, ht_1, ht_2)

;; test.spectec:2030.1-2030.103
relation Valtype_sub: `%|-%<:%`(context, valtype, valtype)
  ;; test.spectec:2133.1-2135.46
  rule num{C : context, numtype_1 : numtype, numtype_2 : numtype}:
    `%|-%<:%`(C, (numtype_1 : numtype <: valtype), (numtype_2 : numtype <: valtype))
    -- Numtype_sub: `%|-%<:%`(C, numtype_1, numtype_2)

  ;; test.spectec:2137.1-2139.46
  rule vec{C : context, vectype_1 : vectype, vectype_2 : vectype}:
    `%|-%<:%`(C, (vectype_1 : vectype <: valtype), (vectype_2 : vectype <: valtype))
    -- Vectype_sub: `%|-%<:%`(C, vectype_1, vectype_2)

  ;; test.spectec:2141.1-2143.46
  rule ref{C : context, reftype_1 : reftype, reftype_2 : reftype}:
    `%|-%<:%`(C, (reftype_1 : reftype <: valtype), (reftype_2 : reftype <: valtype))
    -- Reftype_sub: `%|-%<:%`(C, reftype_1, reftype_2)

  ;; test.spectec:2145.1-2146.22
  rule bot{C : context, valtype : valtype}:
    `%|-%<:%`(C, BOT_valtype, valtype)

;; test.spectec:2151.1-2151.115
relation Resulttype_sub: `%|-%<:%`(context, resulttype, resulttype)
  ;; test.spectec:2154.1-2156.37
  rule _{C : context, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%<:%`(C, `%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`}))
    -- (Valtype_sub: `%|-%<:%`(C, t_1, t_2))*{t_1 <- `t_1*`, t_2 <- `t_2*`}

;; test.spectec:2169.1-2169.119
relation Storagetype_sub: `%|-%<:%`(context, storagetype, storagetype)
  ;; test.spectec:2181.1-2183.46
  rule val{C : context, valtype_1 : valtype, valtype_2 : valtype}:
    `%|-%<:%`(C, (valtype_1 : valtype <: storagetype), (valtype_2 : valtype <: storagetype))
    -- Valtype_sub: `%|-%<:%`(C, valtype_1, valtype_2)

  ;; test.spectec:2185.1-2187.49
  rule pack{C : context, packtype_1 : packtype, packtype_2 : packtype}:
    `%|-%<:%`(C, (packtype_1 : packtype <: storagetype), (packtype_2 : packtype <: storagetype))
    -- Packtype_sub: `%|-%<:%`(C, packtype_1, packtype_2)

;; test.spectec:2170.1-2170.117
relation Fieldtype_sub: `%|-%<:%`(context, fieldtype, fieldtype)
  ;; test.spectec:2190.1-2192.40
  rule const{C : context, zt_1 : storagetype, zt_2 : storagetype}:
    `%|-%<:%`(C, `%%`_fieldtype(?(), zt_1), `%%`_fieldtype(?(), zt_2))
    -- Storagetype_sub: `%|-%<:%`(C, zt_1, zt_2)

  ;; test.spectec:2194.1-2197.40
  rule var{C : context, zt_1 : storagetype, zt_2 : storagetype}:
    `%|-%<:%`(C, `%%`_fieldtype(?(MUT_mut), zt_1), `%%`_fieldtype(?(MUT_mut), zt_2))
    -- Storagetype_sub: `%|-%<:%`(C, zt_1, zt_2)
    -- Storagetype_sub: `%|-%<:%`(C, zt_2, zt_1)
}

;; test.spectec:1806.1-1806.96
relation Localtype_ok: `%|-%:OK`(context, localtype)
  ;; test.spectec:1810.1-1812.29
  rule _{C : context, init : init, t : valtype}:
    `%|-%:OK`(C, `%%`_localtype(init, t))
    -- Valtype_ok: `%|-%:OK`(C, t)

;; test.spectec:1808.1-1808.99
relation Instrtype_ok: `%|-%:OK`(context, instrtype)
  ;; test.spectec:1818.1-1822.29
  rule _{C : context, `t_1*` : valtype*, `x*` : idx*, `t_2*` : valtype*, `lct*` : localtype*}:
    `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Resulttype_ok: `%|-%:OK`(C, `%`_resulttype(t_1*{t_1 <- `t_1*`}))
    -- Resulttype_ok: `%|-%:OK`(C, `%`_resulttype(t_2*{t_2 <- `t_2*`}))
    -- (if (C.LOCALS_context[x!`%`_idx.0] = lct))*{lct <- `lct*`, x <- `x*`}

;; test.spectec:1829.1-1830.70
relation Expand_use: `%~~_%%`(typeuse, context, comptype)
  ;; test.spectec:1834.1-1834.84
  rule deftype{deftype : deftype, C : context, comptype : comptype}:
    `%~~_%%`((deftype : deftype <: typeuse), C, comptype)
    -- Expand: `%~~%`(deftype, comptype)

  ;; test.spectec:1835.1-1835.93
  rule typeidx{typeidx : typeidx, C : context, comptype : comptype}:
    `%~~_%%`(_IDX_typeuse(typeidx), C, comptype)
    -- Expand: `%~~%`(C.TYPES_context[typeidx!`%`_typeidx.0], comptype)

;; test.spectec:1840.1-1841.76
syntax oktypeidx = 
  | OK(typeidx : typeidx)

;; test.spectec:1849.1-1849.126
relation Subtype_ok: `%|-%:%`(context, subtype, oktypeidx)
  ;; test.spectec:1903.1-1910.49
  rule _{C : context, `x*` : idx*, comptype : comptype, x_0 : idx, `comptype'*` : comptype*, `yy**` : typeuse**}:
    `%|-%:%`(C, SUB_subtype(FINAL_final?{}, _IDX_typeuse(x)*{x <- `x*`}, comptype), OK_oktypeidx(x_0))
    -- if (|x*{x <- `x*`}| <= 1)
    -- (if (x!`%`_idx.0 < x_0!`%`_idx.0))*{x <- `x*`}
    -- (if ($unrolldt(C.TYPES_context[x!`%`_idx.0]) = SUB_subtype(?(), yy*{yy <- `yy*`}, comptype')))*{comptype' <- `comptype'*`, x <- `x*`, `yy*` <- `yy**`}
    -- Comptype_ok: `%|-%:OK`(C, comptype)
    -- (Comptype_sub: `%|-%<:%`(C, comptype, comptype'))*{comptype' <- `comptype'*`}

;; test.spectec:1850.1-1850.126
rec {

;; test.spectec:1850.1-1850.126
relation Rectype_ok: `%|-%:%`(context, rectype, oktypeidx)
  ;; test.spectec:1933.1-1934.23
  rule empty{C : context, x : idx}:
    `%|-%:%`(C, REC_rectype(`%`_list([])), OK_oktypeidx(x))

  ;; test.spectec:1936.1-1939.48
  rule cons{C : context, subtype_1 : subtype, `subtype*` : subtype*, x : idx}:
    `%|-%:%`(C, REC_rectype(`%`_list([subtype_1] ++ subtype*{subtype <- `subtype*`})), OK_oktypeidx(x))
    -- Subtype_ok: `%|-%:%`(C, subtype_1, OK_oktypeidx(x))
    -- Rectype_ok: `%|-%:%`(C, REC_rectype(`%`_list(subtype*{subtype <- `subtype*`})), OK_oktypeidx(`%`_typeidx((x!`%`_idx.0 + 1))))
}

;; test.spectec:1960.1-1960.120
relation Limits_ok: `%|-%:%`(context, limits, nat)
  ;; test.spectec:1968.1-1971.23
  rule _{C : context, n : n, `m?` : m?, k : nat}:
    `%|-%:%`(C, `[%..%]`_limits(`%`_u64(n), `%`_u64(m)?{m <- `m?`}), k)
    -- if (n <= k)
    -- (if ((n <= m) /\ (m <= k)))?{m <- `m?`}

;; test.spectec:1961.1-1961.97
relation Tagtype_ok: `%|-%:OK`(context, tagtype)
  ;; test.spectec:1973.1-1976.54
  rule _{C : context, typeuse : typeuse, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:OK`(C, typeuse)
    -- Typeuse_ok: `%|-%:OK`(C, typeuse)
    -- Expand_use: `%~~_%%`(typeuse, C, `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

;; test.spectec:1962.1-1962.100
relation Globaltype_ok: `%|-%:OK`(context, globaltype)
  ;; test.spectec:1978.1-1980.29
  rule _{C : context, t : valtype}:
    `%|-%:OK`(C, `%%`_globaltype(MUT_mut?{}, t))
    -- Valtype_ok: `%|-%:OK`(C, t)

;; test.spectec:1963.1-1963.97
relation Memtype_ok: `%|-%:OK`(context, memtype)
  ;; test.spectec:1982.1-1984.58
  rule _{C : context, addrtype : addrtype, limits : limits}:
    `%|-%:OK`(C, `%%PAGE`_memtype(addrtype, limits))
    -- Limits_ok: `%|-%:%`(C, limits, (2 ^ ((($size((addrtype : addrtype <: numtype)) : nat <:> int) - (16 : nat <:> int)) : int <:> nat)))

;; test.spectec:1964.1-1964.99
relation Tabletype_ok: `%|-%:OK`(context, tabletype)
  ;; test.spectec:1986.1-1989.35
  rule _{C : context, addrtype : addrtype, limits : limits, reftype : reftype}:
    `%|-%:OK`(C, `%%%`_tabletype(addrtype, limits, reftype))
    -- Limits_ok: `%|-%:%`(C, limits, ((((2 ^ $size((addrtype : addrtype <: numtype))) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))
    -- Reftype_ok: `%|-%:OK`(C, reftype)

;; test.spectec:1965.1-1965.100
relation Externtype_ok: `%|-%:OK`(context, externtype)
  ;; test.spectec:1992.1-1994.35
  rule tag{C : context, tagtype : tagtype}:
    `%|-%:OK`(C, TAG_externtype(tagtype))
    -- Tagtype_ok: `%|-%:OK`(C, tagtype)

  ;; test.spectec:1996.1-1998.41
  rule global{C : context, globaltype : globaltype}:
    `%|-%:OK`(C, GLOBAL_externtype(globaltype))
    -- Globaltype_ok: `%|-%:OK`(C, globaltype)

  ;; test.spectec:2000.1-2002.35
  rule mem{C : context, memtype : memtype}:
    `%|-%:OK`(C, MEM_externtype(memtype))
    -- Memtype_ok: `%|-%:OK`(C, memtype)

  ;; test.spectec:2004.1-2006.39
  rule table{C : context, tabletype : tabletype}:
    `%|-%:OK`(C, TABLE_externtype(tabletype))
    -- Tabletype_ok: `%|-%:OK`(C, tabletype)

  ;; test.spectec:2008.1-2011.54
  rule func{C : context, typeuse : typeuse, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:OK`(C, FUNC_externtype(typeuse))
    -- Typeuse_ok: `%|-%:OK`(C, typeuse)
    -- Expand_use: `%~~_%%`(typeuse, C, `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

;; test.spectec:2152.1-2152.114
relation Instrtype_sub: `%|-%<:%`(context, instrtype, instrtype)
  ;; test.spectec:2158.1-2163.31
  rule _{C : context, `t_11*` : valtype*, `x_1*` : idx*, `t_12*` : valtype*, `t_21*` : valtype*, `x_2*` : idx*, `t_22*` : valtype*, `x*` : idx*, `t*` : valtype*}:
    `%|-%<:%`(C, `%->_%%`_instrtype(`%`_resulttype(t_11*{t_11 <- `t_11*`}), x_1*{x_1 <- `x_1*`}, `%`_resulttype(t_12*{t_12 <- `t_12*`})), `%->_%%`_instrtype(`%`_resulttype(t_21*{t_21 <- `t_21*`}), x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_22*{t_22 <- `t_22*`})))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_21*{t_21 <- `t_21*`}), `%`_resulttype(t_11*{t_11 <- `t_11*`}))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_12*{t_12 <- `t_12*`}), `%`_resulttype(t_22*{t_22 <- `t_22*`}))
    -- if (x*{x <- `x*`} = $setminus_(syntax localidx, x_2*{x_2 <- `x_2*`}, x_1*{x_1 <- `x_1*`}))
    -- (if (C.LOCALS_context[x!`%`_idx.0] = `%%`_localtype(SET_init, t)))*{t <- `t*`, x <- `x*`}

;; test.spectec:2226.1-2226.110
relation Limits_sub: `%|-%<:%`(context, limits, limits)
  ;; test.spectec:2234.1-2237.22
  rule max{C : context, n_1 : n, m_1 : m, n_2 : n, `m_2?` : m?}:
    `%|-%<:%`(C, `[%..%]`_limits(`%`_u64(n_1), ?(`%`_u64(m_1))), `[%..%]`_limits(`%`_u64(n_2), `%`_u64(m_2)?{m_2 <- `m_2?`}))
    -- if (n_1 >= n_2)
    -- (if (m_1 <= m_2))?{m_2 <- `m_2?`}

  ;; test.spectec:2239.1-2241.19
  rule eps{C : context, n_1 : n, n_2 : n}:
    `%|-%<:%`(C, `[%..%]`_limits(`%`_u64(n_1), ?()), `[%..%]`_limits(`%`_u64(n_2), ?()))
    -- if (n_1 >= n_2)

;; test.spectec:2227.1-2227.111
relation Tagtype_sub: `%|-%<:%`(context, tagtype, tagtype)
  ;; test.spectec:2244.1-2247.46
  rule _{C : context, deftype_1 : deftype, deftype_2 : deftype}:
    `%|-%<:%`(C, (deftype_1 : deftype <: typeuse), (deftype_2 : deftype <: typeuse))
    -- Deftype_sub: `%|-%<:%`(C, deftype_1, deftype_2)
    -- Deftype_sub: `%|-%<:%`(C, deftype_2, deftype_1)

;; test.spectec:2228.1-2228.114
relation Globaltype_sub: `%|-%<:%`(context, globaltype, globaltype)
  ;; test.spectec:2249.1-2251.46
  rule const{C : context, valtype_1 : valtype, valtype_2 : valtype}:
    `%|-%<:%`(C, `%%`_globaltype(?(), valtype_1), `%%`_globaltype(?(), valtype_2))
    -- Valtype_sub: `%|-%<:%`(C, valtype_1, valtype_2)

  ;; test.spectec:2253.1-2256.46
  rule var{C : context, valtype_1 : valtype, valtype_2 : valtype}:
    `%|-%<:%`(C, `%%`_globaltype(?(MUT_mut), valtype_1), `%%`_globaltype(?(MUT_mut), valtype_2))
    -- Valtype_sub: `%|-%<:%`(C, valtype_1, valtype_2)
    -- Valtype_sub: `%|-%<:%`(C, valtype_2, valtype_1)

;; test.spectec:2229.1-2229.111
relation Memtype_sub: `%|-%<:%`(context, memtype, memtype)
  ;; test.spectec:2258.1-2260.43
  rule _{C : context, addrtype : addrtype, limits_1 : limits, limits_2 : limits}:
    `%|-%<:%`(C, `%%PAGE`_memtype(addrtype, limits_1), `%%PAGE`_memtype(addrtype, limits_2))
    -- Limits_sub: `%|-%<:%`(C, limits_1, limits_2)

;; test.spectec:2230.1-2230.113
relation Tabletype_sub: `%|-%<:%`(context, tabletype, tabletype)
  ;; test.spectec:2262.1-2266.46
  rule _{C : context, addrtype : addrtype, limits_1 : limits, reftype_1 : reftype, limits_2 : limits, reftype_2 : reftype}:
    `%|-%<:%`(C, `%%%`_tabletype(addrtype, limits_1, reftype_1), `%%%`_tabletype(addrtype, limits_2, reftype_2))
    -- Limits_sub: `%|-%<:%`(C, limits_1, limits_2)
    -- Reftype_sub: `%|-%<:%`(C, reftype_1, reftype_2)
    -- Reftype_sub: `%|-%<:%`(C, reftype_2, reftype_1)

;; test.spectec:2231.1-2231.114
relation Externtype_sub: `%|-%<:%`(context, externtype, externtype)
  ;; test.spectec:2269.1-2271.46
  rule tag{C : context, tagtype_1 : tagtype, tagtype_2 : tagtype}:
    `%|-%<:%`(C, TAG_externtype(tagtype_1), TAG_externtype(tagtype_2))
    -- Tagtype_sub: `%|-%<:%`(C, tagtype_1, tagtype_2)

  ;; test.spectec:2273.1-2275.55
  rule global{C : context, globaltype_1 : globaltype, globaltype_2 : globaltype}:
    `%|-%<:%`(C, GLOBAL_externtype(globaltype_1), GLOBAL_externtype(globaltype_2))
    -- Globaltype_sub: `%|-%<:%`(C, globaltype_1, globaltype_2)

  ;; test.spectec:2277.1-2279.46
  rule mem{C : context, memtype_1 : memtype, memtype_2 : memtype}:
    `%|-%<:%`(C, MEM_externtype(memtype_1), MEM_externtype(memtype_2))
    -- Memtype_sub: `%|-%<:%`(C, memtype_1, memtype_2)

  ;; test.spectec:2281.1-2283.52
  rule table{C : context, tabletype_1 : tabletype, tabletype_2 : tabletype}:
    `%|-%<:%`(C, TABLE_externtype(tabletype_1), TABLE_externtype(tabletype_2))
    -- Tabletype_sub: `%|-%<:%`(C, tabletype_1, tabletype_2)

  ;; test.spectec:2285.1-2287.46
  rule func{C : context, deftype_1 : deftype, deftype_2 : deftype}:
    `%|-%<:%`(C, FUNC_externtype((deftype_1 : deftype <: typeuse)), FUNC_externtype((deftype_2 : deftype <: typeuse)))
    -- Deftype_sub: `%|-%<:%`(C, deftype_1, deftype_2)

;; test.spectec:2337.1-2337.121
relation Blocktype_ok: `%|-%:%`(context, blocktype, instrtype)
  ;; test.spectec:2339.1-2341.38
  rule valtype{C : context, `valtype?` : valtype?}:
    `%|-%:%`(C, _RESULT_blocktype(valtype?{valtype <- `valtype?`}), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype(lift(valtype?{valtype <- `valtype?`}))))
    -- (Valtype_ok: `%|-%:OK`(C, valtype))?{valtype <- `valtype?`}

  ;; test.spectec:2343.1-2345.51
  rule typeidx{C : context, typeidx : typeidx, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, _IDX_blocktype(typeidx), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Expand: `%~~%`(C.TYPES_context[typeidx!`%`_typeidx.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

;; test.spectec:2459.1-2459.77
relation Catch_ok: `%|-%:OK`(context, catch)
  ;; test.spectec:2476.1-2479.44
  rule catch{C : context, x : idx, l : labelidx, `t*` : valtype*}:
    `%|-%:OK`(C, CATCH_catch(x, l))
    -- Expand: `%~~%`($as_deftype(C.TAGS_context[x!`%`_idx.0]), `FUNC%->%`_comptype(`%`_resulttype(t*{t <- `t*`}), `%`_resulttype([])))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t*{t <- `t*`}), C.LABELS_context[l!`%`_labelidx.0])

  ;; test.spectec:2481.1-2484.54
  rule catch_ref{C : context, x : idx, l : labelidx, `t*` : valtype*}:
    `%|-%:OK`(C, CATCH_REF_catch(x, l))
    -- Expand: `%~~%`($as_deftype(C.TAGS_context[x!`%`_idx.0]), `FUNC%->%`_comptype(`%`_resulttype(t*{t <- `t*`}), `%`_resulttype([])))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(?(), EXN_heaptype)]), C.LABELS_context[l!`%`_labelidx.0])

  ;; test.spectec:2486.1-2488.45
  rule catch_all{C : context, l : labelidx}:
    `%|-%:OK`(C, CATCH_ALL_catch(l))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype([]), C.LABELS_context[l!`%`_labelidx.0])

  ;; test.spectec:2490.1-2492.51
  rule catch_all_ref{C : context, l : labelidx}:
    `%|-%:OK`(C, CATCH_ALL_REF_catch(l))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype([REF_valtype(?(), EXN_heaptype)]), C.LABELS_context[l!`%`_labelidx.0])

;; test.spectec:4445.1-4445.44
def $default_(valtype : valtype) : val?
  ;; test.spectec:4446.1-4446.35
  def $default_{Inn : Inn}((Inn : addrtype <: valtype)) = ?(CONST_val((Inn : addrtype <: numtype), `%`_num_(0)))
  ;; test.spectec:4447.1-4447.52
  def $default_{Fnn : Fnn}((Fnn : Fnn <: valtype)) = ?(CONST_val((Fnn : Fnn <: numtype), $fzero($size((Fnn : Fnn <: numtype)))))
  ;; test.spectec:4448.1-4448.36
  def $default_{Vnn : Vnn}((Vnn : vectype <: valtype)) = ?(VCONST_val(Vnn, `%`_vec_(0)))
  ;; test.spectec:4449.1-4449.43
  def $default_{ht : heaptype}(REF_valtype(?(NULL_null), ht)) = ?(`REF.NULL_ADDR`_val)
  ;; test.spectec:4450.1-4450.28
  def $default_{ht : heaptype}(REF_valtype(?(), ht)) = ?()

;; test.spectec:2304.1-2305.71
relation Defaultable: `|-%DEFAULTABLE`(valtype)
  ;; test.spectec:4453.1-4453.62
  rule _{t : valtype}:
    `|-%DEFAULTABLE`(t)
    -- if ($default_(t) =/= ?())

;; test.spectec:2703.1-2703.131
relation Memarg_ok: `|-%:%->%`(memarg, addrtype, N)
  ;; test.spectec:2705.1-2708.27
  rule _{n : n, m : m, at : addrtype, N : N}:
    `|-%:%->%`({ALIGN `%`_u32(n), OFFSET `%`_u64(m)}, at, N)
    -- if (((2 ^ n) : nat <:> rat) <= ((N : nat <:> rat) / (8 : nat <:> rat)))
    -- if (m < (2 ^ $size((at : addrtype <: numtype))))

;; test.spectec:2550.1-2550.111
def $is_packtype(storagetype : storagetype) : bool
  ;; test.spectec:2551.1-2551.42
  def $is_packtype{zt : storagetype}(zt) = (zt =/= ($unpack(zt) : valtype <: storagetype))

;; test.spectec:2300.1-2301.96
rec {

;; test.spectec:2300.1-2300.95
relation Instr_ok: `%|-%:%`(context, instr, instrtype)
  ;; test.spectec:2313.1-2314.24
  rule nop{C : context}:
    `%|-%:%`(C, NOP_instr, `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([])))

  ;; test.spectec:2316.1-2318.42
  rule unreachable{C : context, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, UNREACHABLE_instr, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2320.1-2322.29
  rule drop{C : context, t : valtype}:
    `%|-%:%`(C, DROP_instr, `%->_%%`_instrtype(`%`_resulttype([t]), [], `%`_resulttype([])))
    -- Valtype_ok: `%|-%:OK`(C, t)

  ;; test.spectec:2324.1-2326.29
  rule `select-expl`{C : context, t : valtype}:
    `%|-%:%`(C, SELECT_instr(?([t])), `%->_%%`_instrtype(`%`_resulttype([t t I32_valtype]), [], `%`_resulttype([t])))
    -- Valtype_ok: `%|-%:OK`(C, t)

  ;; test.spectec:2328.1-2332.37
  rule `select-impl`{C : context, t : valtype, t' : valtype, numtype : numtype, vectype : vectype}:
    `%|-%:%`(C, SELECT_instr(?()), `%->_%%`_instrtype(`%`_resulttype([t t I32_valtype]), [], `%`_resulttype([t])))
    -- Valtype_ok: `%|-%:OK`(C, t)
    -- Valtype_sub: `%|-%<:%`(C, t, t')
    -- if ((t' = (numtype : numtype <: valtype)) \/ (t' = (vectype : vectype <: valtype)))

  ;; test.spectec:2348.1-2351.67
  rule block{C : context, bt : blocktype, `instr*` : instr*, `t_1*` : valtype*, `t_2*` : valtype*, `x*` : idx*}:
    `%|-%:%`(C, BLOCK_instr(bt, instr*{instr <- `instr*`}), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(), REFS [], RECS []} +++ C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2353.1-2356.67
  rule loop{C : context, bt : blocktype, `instr*` : instr*, `t_1*` : valtype*, `t_2*` : valtype*, `x*` : idx*}:
    `%|-%:%`(C, LOOP_instr(bt, instr*{instr <- `instr*`}), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_1*{t_1 <- `t_1*`})], RETURN ?(), REFS [], RECS []} +++ C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2358.1-2362.71
  rule if{C : context, bt : blocktype, `instr_1*` : instr*, `instr_2*` : instr*, `t_1*` : valtype*, `t_2*` : valtype*, `x_1*` : idx*, `x_2*` : idx*}:
    `%|-%:%`(C, `IF%%ELSE%`_instr(bt, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`}), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [I32_valtype]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(), REFS [], RECS []} +++ C, instr_1*{instr_1 <- `instr_1*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_1*{x_1 <- `x_1*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(), REFS [], RECS []} +++ C, instr_2*{instr_2 <- `instr_2*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2367.1-2370.42
  rule br{C : context, l : labelidx, `t_1*` : valtype*, `t*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, BR_instr(l), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.LABELS_context[l!`%`_labelidx.0]!`%`_resulttype.0 = t*{t <- `t*`})
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2372.1-2374.25
  rule br_if{C : context, l : labelidx, `t*` : valtype*}:
    `%|-%:%`(C, BR_IF_instr(l), `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [I32_valtype]), [], `%`_resulttype(t*{t <- `t*`})))
    -- if (C.LABELS_context[l!`%`_labelidx.0]!`%`_resulttype.0 = t*{t <- `t*`})

  ;; test.spectec:2376.1-2380.49
  rule br_table{C : context, `l*` : labelidx*, l' : labelidx, `t_1*` : valtype*, `t*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, BR_TABLE_instr(l*{l <- `l*`}, l'), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`} ++ [I32_valtype]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t*{t <- `t*`}), C.LABELS_context[l!`%`_labelidx.0]))*{l <- `l*`}
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t*{t <- `t*`}), C.LABELS_context[l'!`%`_labelidx.0])
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`} ++ [I32_valtype]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2382.1-2385.31
  rule br_on_null{C : context, l : labelidx, `t*` : valtype*, ht : heaptype}:
    `%|-%:%`(C, BR_ON_NULL_instr(l), `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(?(NULL_null), ht)]), [], `%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(?(), ht)])))
    -- if (C.LABELS_context[l!`%`_labelidx.0]!`%`_resulttype.0 = t*{t <- `t*`})
    -- Heaptype_ok: `%|-%:OK`(C, ht)

  ;; test.spectec:2387.1-2389.40
  rule br_on_non_null{C : context, l : labelidx, `t*` : valtype*, ht : heaptype}:
    `%|-%:%`(C, BR_ON_NON_NULL_instr(l), `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(?(NULL_null), ht)]), [], `%`_resulttype(t*{t <- `t*`})))
    -- if (C.LABELS_context[l!`%`_labelidx.0] = `%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(NULL_null?{}, ht)]))

  ;; test.spectec:2391.1-2397.34
  rule br_on_cast{C : context, l : labelidx, rt_1 : reftype, rt_2 : reftype, `t*` : valtype*, rt : reftype}:
    `%|-%:%`(C, BR_ON_CAST_instr(l, rt_1, rt_2), `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [(rt_1 : reftype <: valtype)]), [], `%`_resulttype(t*{t <- `t*`} ++ [($diffrt(rt_1, rt_2) : reftype <: valtype)])))
    -- if (C.LABELS_context[l!`%`_labelidx.0] = `%`_resulttype(t*{t <- `t*`} ++ [(rt : reftype <: valtype)]))
    -- Reftype_ok: `%|-%:OK`(C, rt_1)
    -- Reftype_ok: `%|-%:OK`(C, rt_2)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt)

  ;; test.spectec:2399.1-2405.49
  rule br_on_cast_fail{C : context, l : labelidx, rt_1 : reftype, rt_2 : reftype, `t*` : valtype*, rt : reftype}:
    `%|-%:%`(C, BR_ON_CAST_FAIL_instr(l, rt_1, rt_2), `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [(rt_1 : reftype <: valtype)]), [], `%`_resulttype(t*{t <- `t*`} ++ [(rt_2 : reftype <: valtype)])))
    -- if (C.LABELS_context[l!`%`_labelidx.0] = `%`_resulttype(t*{t <- `t*`} ++ [(rt : reftype <: valtype)]))
    -- Reftype_ok: `%|-%:OK`(C, rt_1)
    -- Reftype_ok: `%|-%:OK`(C, rt_2)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)
    -- Reftype_sub: `%|-%<:%`(C, $diffrt(rt_1, rt_2), rt)

  ;; test.spectec:2410.1-2412.45
  rule call{C : context, x : idx, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, CALL_instr(x), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Expand: `%~~%`(C.FUNCS_context[x!`%`_idx.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2414.1-2416.45
  rule call_ref{C : context, x : idx, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, CALL_REF_instr(_IDX_typeuse(x)), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2418.1-2422.45
  rule call_indirect{C : context, x : idx, y : idx, `t_1*` : valtype*, at : addrtype, `t_2*` : valtype*, lim : limits, rt : reftype}:
    `%|-%:%`(C, CALL_INDIRECT_instr(x, _IDX_typeuse(y)), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [(at : addrtype <: valtype)]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt))
    -- Reftype_sub: `%|-%<:%`(C, rt, REF_reftype(?(NULL_null), FUNC_heaptype))
    -- Expand: `%~~%`(C.TYPES_context[y!`%`_idx.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2424.1-2427.42
  rule return{C : context, `t_1*` : valtype*, `t*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, RETURN_instr, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.RETURN_context = ?(`%`_resulttype(t*{t <- `t*`})))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2430.1-2435.42
  rule return_call{C : context, x : idx, `t_3*` : valtype*, `t_1*` : valtype*, `t_4*` : valtype*, `t_2*` : valtype*, `t'_2*` : valtype*}:
    `%|-%:%`(C, RETURN_CALL_instr(x), `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`} ++ t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))
    -- Expand: `%~~%`(C.FUNCS_context[x!`%`_idx.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.RETURN_context = ?(`%`_resulttype(t'_2*{t'_2 <- `t'_2*`})))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_2*{t_2 <- `t_2*`}), `%`_resulttype(t'_2*{t'_2 <- `t'_2*`}))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`}), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))

  ;; test.spectec:2438.1-2443.42
  rule return_call_ref{C : context, x : idx, `t_3*` : valtype*, `t_1*` : valtype*, `t_4*` : valtype*, `t_2*` : valtype*, `t'_2*` : valtype*}:
    `%|-%:%`(C, RETURN_CALL_REF_instr(_IDX_typeuse(x)), `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`} ++ t_1*{t_1 <- `t_1*`} ++ [REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.RETURN_context = ?(`%`_resulttype(t'_2*{t'_2 <- `t'_2*`})))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_2*{t_2 <- `t_2*`}), `%`_resulttype(t'_2*{t'_2 <- `t'_2*`}))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`}), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))

  ;; test.spectec:2446.1-2454.42
  rule return_call_indirect{C : context, x : idx, y : idx, `t_3*` : valtype*, `t_1*` : valtype*, at : addrtype, `t_4*` : valtype*, lim : limits, rt : reftype, `t_2*` : valtype*, `t'_2*` : valtype*}:
    `%|-%:%`(C, RETURN_CALL_INDIRECT_instr(x, _IDX_typeuse(y)), `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`} ++ t_1*{t_1 <- `t_1*`} ++ [(at : addrtype <: valtype)]), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt))
    -- Reftype_sub: `%|-%<:%`(C, rt, REF_reftype(?(NULL_null), FUNC_heaptype))
    -- Expand: `%~~%`(C.TYPES_context[y!`%`_idx.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.RETURN_context = ?(`%`_resulttype(t'_2*{t'_2 <- `t'_2*`})))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_2*{t_2 <- `t_2*`}), `%`_resulttype(t'_2*{t'_2 <- `t'_2*`}))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`}), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))

  ;; test.spectec:2461.1-2464.42
  rule throw{C : context, x : idx, `t_1*` : valtype*, `t*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, THROW_instr(x), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Expand: `%~~%`($as_deftype(C.TAGS_context[x!`%`_idx.0]), `FUNC%->%`_comptype(`%`_resulttype(t*{t <- `t*`}), `%`_resulttype([])))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2466.1-2468.42
  rule throw_ref{C : context, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, THROW_REF_instr, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [REF_valtype(?(NULL_null), EXN_heaptype)]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2470.1-2474.34
  rule try_table{C : context, bt : blocktype, `catch*` : catch*, `instr*` : instr*, `t_1*` : valtype*, `t_2*` : valtype*, `x*` : idx*}:
    `%|-%:%`(C, TRY_TABLE_instr(bt, `%`_list(catch*{catch <- `catch*`}), instr*{instr <- `instr*`}), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(), REFS [], RECS []} +++ C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (Catch_ok: `%|-%:OK`(C, catch))*{catch <- `catch*`}

  ;; test.spectec:2497.1-2499.31
  rule `ref.null`{C : context, ht : heaptype}:
    `%|-%:%`(C, `REF.NULL`_instr(ht), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([REF_valtype(?(NULL_null), ht)])))
    -- Heaptype_ok: `%|-%:OK`(C, ht)

  ;; test.spectec:2501.1-2504.20
  rule `ref.func`{C : context, x : idx, dt : deftype}:
    `%|-%:%`(C, `REF.FUNC`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([REF_valtype(?(), (dt : deftype <: heaptype))])))
    -- if (C.FUNCS_context[x!`%`_idx.0] = dt)
    -- if (x <- C.REFS_context)

  ;; test.spectec:2506.1-2507.34
  rule `ref.i31`{C : context}:
    `%|-%:%`(C, `REF.I31`_instr, `%->_%%`_instrtype(`%`_resulttype([I32_valtype]), [], `%`_resulttype([REF_valtype(?(), I31_heaptype)])))

  ;; test.spectec:2509.1-2511.31
  rule `ref.is_null`{C : context, ht : heaptype}:
    `%|-%:%`(C, `REF.IS_NULL`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), ht)]), [], `%`_resulttype([I32_valtype])))
    -- Heaptype_ok: `%|-%:OK`(C, ht)

  ;; test.spectec:2513.1-2515.31
  rule `ref.as_non_null`{C : context, ht : heaptype}:
    `%|-%:%`(C, `REF.AS_NON_NULL`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), ht)]), [], `%`_resulttype([REF_valtype(?(), ht)])))
    -- Heaptype_ok: `%|-%:OK`(C, ht)

  ;; test.spectec:2517.1-2518.51
  rule `ref.eq`{C : context}:
    `%|-%:%`(C, `REF.EQ`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), EQ_heaptype) REF_valtype(?(NULL_null), EQ_heaptype)]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2520.1-2524.33
  rule `ref.test`{C : context, rt : reftype, rt' : reftype}:
    `%|-%:%`(C, `REF.TEST`_instr(rt), `%->_%%`_instrtype(`%`_resulttype([(rt' : reftype <: valtype)]), [], `%`_resulttype([I32_valtype])))
    -- Reftype_ok: `%|-%:OK`(C, rt)
    -- Reftype_ok: `%|-%:OK`(C, rt')
    -- Reftype_sub: `%|-%<:%`(C, rt, rt')

  ;; test.spectec:2526.1-2530.33
  rule `ref.cast`{C : context, rt : reftype, rt' : reftype}:
    `%|-%:%`(C, `REF.CAST`_instr(rt), `%->_%%`_instrtype(`%`_resulttype([(rt' : reftype <: valtype)]), [], `%`_resulttype([(rt : reftype <: valtype)])))
    -- Reftype_ok: `%|-%:OK`(C, rt)
    -- Reftype_ok: `%|-%:OK`(C, rt')
    -- Reftype_sub: `%|-%<:%`(C, rt, rt')

  ;; test.spectec:2535.1-2536.42
  rule `i31.get`{C : context, sx : sx}:
    `%|-%:%`(C, `I31.GET`_instr(sx), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), I31_heaptype)]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2541.1-2543.45
  rule `struct.new`{C : context, x : idx, `zt*` : storagetype*, `mut?*` : mut?*}:
    `%|-%:%`(C, `STRUCT.NEW`_instr(x), `%->_%%`_instrtype(`%`_resulttype($unpack(zt)*{zt <- `zt*`}), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], STRUCT_comptype(`%`_list(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)*{`mut?` <- `mut?*`, zt <- `zt*`})))

  ;; test.spectec:2545.1-2548.48
  rule `struct.new_default`{C : context, x : idx, `mut?*` : mut?*, `zt*` : storagetype*}:
    `%|-%:%`(C, `STRUCT.NEW_DEFAULT`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], STRUCT_comptype(`%`_list(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)*{`mut?` <- `mut?*`, zt <- `zt*`})))
    -- (Defaultable: `|-%DEFAULTABLE`($unpack(zt)))*{zt <- `zt*`}

  ;; test.spectec:2553.1-2557.41
  rule `struct.get`{C : context, `sx?` : sx?, x : idx, i : fieldidx, zt : storagetype, `ft*` : fieldtype*, `mut?` : mut?}:
    `%|-%:%`(C, `STRUCT.GET`_instr(sx?{sx <- `sx?`}, x, i), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], `%`_resulttype([$unpack(zt)])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], STRUCT_comptype(`%`_list(ft*{ft <- `ft*`})))
    -- if (ft*{ft <- `ft*`}[i!`%`_fieldidx.0] = `%%`_fieldtype(mut?{mut <- `mut?`}, zt))
    -- if ((sx?{sx <- `sx?`} =/= ?()) <=> $is_packtype(zt))

  ;; test.spectec:2559.1-2562.24
  rule `struct.set`{C : context, x : idx, i : fieldidx, zt : storagetype, `ft*` : fieldtype*}:
    `%|-%:%`(C, `STRUCT.SET`_instr(x, i), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) $unpack(zt)]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], STRUCT_comptype(`%`_list(ft*{ft <- `ft*`})))
    -- if (ft*{ft <- `ft*`}[i!`%`_fieldidx.0] = `%%`_fieldtype(?(MUT_mut), zt))

  ;; test.spectec:2567.1-2569.43
  rule `array.new`{C : context, x : idx, zt : storagetype, `mut?` : mut?}:
    `%|-%:%`(C, `ARRAY.NEW`_instr(x), `%->_%%`_instrtype(`%`_resulttype([$unpack(zt) I32_valtype]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))

  ;; test.spectec:2571.1-2574.45
  rule `array.new_default`{C : context, x : idx, `mut?` : mut?, zt : storagetype}:
    `%|-%:%`(C, `ARRAY.NEW_DEFAULT`_instr(x), `%->_%%`_instrtype(`%`_resulttype([I32_valtype]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- Defaultable: `|-%DEFAULTABLE`($unpack(zt))

  ;; test.spectec:2576.1-2578.43
  rule `array.new_fixed`{C : context, x : idx, n : n, zt : storagetype, `mut?` : mut?}:
    `%|-%:%`(C, `ARRAY.NEW_FIXED`_instr(x, `%`_u32(n)), `%->_%%`_instrtype(`%`_resulttype($unpack(zt)^n{}), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))

  ;; test.spectec:2580.1-2583.40
  rule `array.new_elem`{C : context, x : idx, y : idx, `mut?` : mut?, rt : reftype}:
    `%|-%:%`(C, `ARRAY.NEW_ELEM`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([I32_valtype I32_valtype]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, (rt : reftype <: storagetype))))
    -- Reftype_sub: `%|-%<:%`(C, C.ELEMS_context[y!`%`_idx.0], rt)

  ;; test.spectec:2585.1-2589.24
  rule `array.new_data`{C : context, x : idx, y : idx, `mut?` : mut?, zt : storagetype, numtype : numtype, vectype : vectype}:
    `%|-%:%`(C, `ARRAY.NEW_DATA`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([I32_valtype I32_valtype]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- if (($unpack(zt) = (numtype : numtype <: valtype)) \/ ($unpack(zt) = (vectype : vectype <: valtype)))
    -- if (C.DATAS_context[y!`%`_idx.0] = OK_datatype)

  ;; test.spectec:2591.1-2594.41
  rule `array.get`{C : context, `sx?` : sx?, x : idx, zt : storagetype, `mut?` : mut?}:
    `%|-%:%`(C, `ARRAY.GET`_instr(sx?{sx <- `sx?`}, x), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype]), [], `%`_resulttype([$unpack(zt)])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- if ((sx?{sx <- `sx?`} =/= ?()) <=> $is_packtype(zt))

  ;; test.spectec:2596.1-2598.42
  rule `array.set`{C : context, x : idx, zt : storagetype}:
    `%|-%:%`(C, `ARRAY.SET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype $unpack(zt)]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt)))

  ;; test.spectec:2600.1-2601.43
  rule `array.len`{C : context}:
    `%|-%:%`(C, `ARRAY.LEN`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), ARRAY_heaptype)]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2603.1-2605.42
  rule `array.fill`{C : context, x : idx, zt : storagetype}:
    `%|-%:%`(C, `ARRAY.FILL`_instr(x), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype $unpack(zt) I32_valtype]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt)))

  ;; test.spectec:2607.1-2611.40
  rule `array.copy`{C : context, x_1 : idx, x_2 : idx, zt_1 : storagetype, `mut?` : mut?, zt_2 : storagetype}:
    `%|-%:%`(C, `ARRAY.COPY`_instr(x_1, x_2), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x_1)) I32_valtype REF_valtype(?(NULL_null), _IDX_heaptype(x_2)) I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x_1!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt_1)))
    -- Expand: `%~~%`(C.TYPES_context[x_2!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt_2)))
    -- Storagetype_sub: `%|-%<:%`(C, zt_2, zt_1)

  ;; test.spectec:2613.1-2616.44
  rule `array.init_elem`{C : context, x : idx, y : idx, zt : storagetype}:
    `%|-%:%`(C, `ARRAY.INIT_ELEM`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt)))
    -- Storagetype_sub: `%|-%<:%`(C, (C.ELEMS_context[y!`%`_idx.0] : reftype <: storagetype), zt)

  ;; test.spectec:2618.1-2622.24
  rule `array.init_data`{C : context, x : idx, y : idx, zt : storagetype, numtype : numtype, vectype : vectype}:
    `%|-%:%`(C, `ARRAY.INIT_DATA`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt)))
    -- if (($unpack(zt) = (numtype : numtype <: valtype)) \/ ($unpack(zt) = (vectype : vectype <: valtype)))
    -- if (C.DATAS_context[y!`%`_idx.0] = OK_datatype)

  ;; test.spectec:2627.1-2629.26
  rule `extern.convert_any`{C : context, `null_1?` : null?, `null_2?` : null?}:
    `%|-%:%`(C, `EXTERN.CONVERT_ANY`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(null_1?{null_1 <- `null_1?`}, ANY_heaptype)]), [], `%`_resulttype([REF_valtype(null_2?{null_2 <- `null_2?`}, EXTERN_heaptype)])))
    -- if (null_1?{null_1 <- `null_1?`} = null_2?{null_2 <- `null_2?`})

  ;; test.spectec:2631.1-2633.26
  rule `any.convert_extern`{C : context, `null_1?` : null?, `null_2?` : null?}:
    `%|-%:%`(C, `ANY.CONVERT_EXTERN`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(null_1?{null_1 <- `null_1?`}, EXTERN_heaptype)]), [], `%`_resulttype([REF_valtype(null_2?{null_2 <- `null_2?`}, ANY_heaptype)])))
    -- if (null_1?{null_1 <- `null_1?`} = null_2?{null_2 <- `null_2?`})

  ;; test.spectec:2638.1-2640.28
  rule `local.get`{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, `LOCAL.GET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([t])))
    -- if (C.LOCALS_context[x!`%`_idx.0] = `%%`_localtype(SET_init, t))

  ;; test.spectec:2642.1-2644.29
  rule `local.set`{C : context, x : idx, t : valtype, init : init}:
    `%|-%:%`(C, `LOCAL.SET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([t]), [x], `%`_resulttype([])))
    -- if (C.LOCALS_context[x!`%`_idx.0] = `%%`_localtype(init, t))

  ;; test.spectec:2646.1-2648.29
  rule `local.tee`{C : context, x : idx, t : valtype, init : init}:
    `%|-%:%`(C, `LOCAL.TEE`_instr(x), `%->_%%`_instrtype(`%`_resulttype([t]), [x], `%`_resulttype([t])))
    -- if (C.LOCALS_context[x!`%`_idx.0] = `%%`_localtype(init, t))

  ;; test.spectec:2653.1-2655.30
  rule `global.get`{C : context, x : idx, t : valtype, `mut?` : mut?}:
    `%|-%:%`(C, `GLOBAL.GET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([t])))
    -- if (C.GLOBALS_context[x!`%`_idx.0] = `%%`_globaltype(mut?{mut <- `mut?`}, t))

  ;; test.spectec:2657.1-2659.29
  rule `global.set`{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, `GLOBAL.SET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([t]), [], `%`_resulttype([])))
    -- if (C.GLOBALS_context[x!`%`_idx.0] = `%%`_globaltype(?(MUT_mut), t))

  ;; test.spectec:2664.1-2666.32
  rule `table.get`{C : context, x : idx, at : addrtype, rt : reftype, lim : limits}:
    `%|-%:%`(C, `TABLE.GET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype)]), [], `%`_resulttype([(rt : reftype <: valtype)])))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt))

  ;; test.spectec:2668.1-2670.32
  rule `table.set`{C : context, x : idx, at : addrtype, rt : reftype, lim : limits}:
    `%|-%:%`(C, `TABLE.SET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) (rt : reftype <: valtype)]), [], `%`_resulttype([])))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt))

  ;; test.spectec:2672.1-2674.32
  rule `table.size`{C : context, x : idx, at : addrtype, lim : limits, rt : reftype}:
    `%|-%:%`(C, `TABLE.SIZE`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([(at : addrtype <: valtype)])))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt))

  ;; test.spectec:2676.1-2678.32
  rule `table.grow`{C : context, x : idx, rt : reftype, at : addrtype, lim : limits}:
    `%|-%:%`(C, `TABLE.GROW`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(rt : reftype <: valtype) (at : addrtype <: valtype)]), [], `%`_resulttype([(at : addrtype <: valtype)])))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt))

  ;; test.spectec:2680.1-2682.32
  rule `table.fill`{C : context, x : idx, at : addrtype, rt : reftype, lim : limits}:
    `%|-%:%`(C, `TABLE.FILL`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) (rt : reftype <: valtype) (at : addrtype <: valtype)]), [], `%`_resulttype([])))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt))

  ;; test.spectec:2684.1-2688.36
  rule `table.copy`{C : context, x_1 : idx, x_2 : idx, at_1 : addrtype, at_2 : addrtype, lim_1 : limits, rt_1 : reftype, lim_2 : limits, rt_2 : reftype}:
    `%|-%:%`(C, `TABLE.COPY`_instr(x_1, x_2), `%->_%%`_instrtype(`%`_resulttype([(at_1 : addrtype <: valtype) (at_2 : addrtype <: valtype) ($minat(at_1, at_2) : addrtype <: valtype)]), [], `%`_resulttype([])))
    -- if (C.TABLES_context[x_1!`%`_idx.0] = `%%%`_tabletype(at_1, lim_1, rt_1))
    -- if (C.TABLES_context[x_2!`%`_idx.0] = `%%%`_tabletype(at_2, lim_2, rt_2))
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)

  ;; test.spectec:2690.1-2694.36
  rule `table.init`{C : context, x : idx, y : idx, at : addrtype, lim : limits, rt_1 : reftype, rt_2 : reftype}:
    `%|-%:%`(C, `TABLE.INIT`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt_1))
    -- if (C.ELEMS_context[y!`%`_idx.0] = rt_2)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)

  ;; test.spectec:2696.1-2698.24
  rule `elem.drop`{C : context, x : idx, rt : reftype}:
    `%|-%:%`(C, `ELEM.DROP`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([])))
    -- if (C.ELEMS_context[x!`%`_idx.0] = rt)

  ;; test.spectec:2711.1-2713.32
  rule `memory.size`{C : context, x : idx, at : addrtype, lim : limits}:
    `%|-%:%`(C, `MEMORY.SIZE`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([(at : addrtype <: valtype)])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))

  ;; test.spectec:2715.1-2717.32
  rule `memory.grow`{C : context, x : idx, at : addrtype, lim : limits}:
    `%|-%:%`(C, `MEMORY.GROW`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype)]), [], `%`_resulttype([(at : addrtype <: valtype)])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))

  ;; test.spectec:2719.1-2721.32
  rule `memory.fill`{C : context, x : idx, at : addrtype, lim : limits}:
    `%|-%:%`(C, `MEMORY.FILL`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) I32_valtype (at : addrtype <: valtype)]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))

  ;; test.spectec:2723.1-2726.38
  rule `memory.copy`{C : context, x_1 : idx, x_2 : idx, at_1 : addrtype, at_2 : addrtype, lim_1 : limits, lim_2 : limits}:
    `%|-%:%`(C, `MEMORY.COPY`_instr(x_1, x_2), `%->_%%`_instrtype(`%`_resulttype([(at_1 : addrtype <: valtype) (at_2 : addrtype <: valtype) ($minat(at_1, at_2) : addrtype <: valtype)]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x_1!`%`_idx.0] = `%%PAGE`_memtype(at_1, lim_1))
    -- if (C.MEMS_context[x_2!`%`_idx.0] = `%%PAGE`_memtype(at_2, lim_2))

  ;; test.spectec:2728.1-2731.24
  rule `memory.init`{C : context, x : idx, y : idx, at : addrtype, lim : limits}:
    `%|-%:%`(C, `MEMORY.INIT`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- if (C.DATAS_context[y!`%`_idx.0] = OK_datatype)

  ;; test.spectec:2733.1-2735.24
  rule `data.drop`{C : context, x : idx}:
    `%|-%:%`(C, `DATA.DROP`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([])))
    -- if (C.DATAS_context[x!`%`_idx.0] = OK_datatype)

  ;; test.spectec:2746.1-2749.44
  rule `load-val`{C : context, nt : numtype, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, LOAD_instr(nt, ?(), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype)]), [], `%`_resulttype([(nt : numtype <: valtype)])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, $size(nt))

  ;; test.spectec:2751.1-2754.36
  rule `load-pack`{C : context, Inn : Inn, M : M, sx : sx, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, LOAD_instr((Inn : addrtype <: numtype), ?(`%_%`_loadop_(`%`_sz(M), sx)), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype)]), [], `%`_resulttype([(Inn : addrtype <: valtype)])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, M)

  ;; test.spectec:2765.1-2768.44
  rule `store-val`{C : context, nt : numtype, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, STORE_instr(nt, ?(), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) (nt : numtype <: valtype)]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, $size(nt))

  ;; test.spectec:2770.1-2773.36
  rule `store-pack`{C : context, Inn : Inn, M : M, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, STORE_instr((Inn : addrtype <: numtype), ?(`%`_storeop_(`%`_sz(M))), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) (Inn : addrtype <: valtype)]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, M)

  ;; test.spectec:2775.1-2778.47
  rule `vload-val`{C : context, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype)]), [], `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, $vsize(V128_vectype))

  ;; test.spectec:2780.1-2783.41
  rule `vload-pack`{C : context, M : M, N : N, sx : sx, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(M), N, sx)), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype)]), [], `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, (M * N))

  ;; test.spectec:2785.1-2788.36
  rule `vload-splat`{C : context, N : N, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(N))), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype)]), [], `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, N)

  ;; test.spectec:2790.1-2793.36
  rule `vload-zero`{C : context, N : N, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(ZERO_vloadop_(`%`_sz(N))), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype)]), [], `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, N)

  ;; test.spectec:2795.1-2799.21
  rule vload_lane{C : context, N : N, x : idx, memarg : memarg, i : laneidx, at : addrtype, lim : limits}:
    `%|-%:%`(C, VLOAD_LANE_instr(V128_vectype, `%`_sz(N), x, memarg, i), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, N)
    -- if ((i!`%`_laneidx.0 : nat <:> rat) < ((128 : nat <:> rat) / (N : nat <:> rat)))

  ;; test.spectec:2801.1-2804.47
  rule vstore{C : context, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, VSTORE_instr(V128_vectype, x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) V128_valtype]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, $vsize(V128_vectype))

  ;; test.spectec:2806.1-2810.21
  rule vstore_lane{C : context, N : N, x : idx, memarg : memarg, i : laneidx, at : addrtype, lim : limits}:
    `%|-%:%`(C, VSTORE_LANE_instr(V128_vectype, `%`_sz(N), x, memarg, i), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) V128_valtype]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, N)
    -- if ((i!`%`_laneidx.0 : nat <:> rat) < ((128 : nat <:> rat) / (N : nat <:> rat)))

  ;; test.spectec:2815.1-2816.33
  rule const{C : context, nt : numtype, c_nt : num_(nt)}:
    `%|-%:%`(C, CONST_instr(nt, c_nt), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([(nt : numtype <: valtype)])))

  ;; test.spectec:2818.1-2819.34
  rule unop{C : context, nt : numtype, unop_nt : unop_(nt)}:
    `%|-%:%`(C, UNOP_instr(nt, unop_nt), `%->_%%`_instrtype(`%`_resulttype([(nt : numtype <: valtype)]), [], `%`_resulttype([(nt : numtype <: valtype)])))

  ;; test.spectec:2821.1-2822.39
  rule binop{C : context, nt : numtype, binop_nt : binop_(nt)}:
    `%|-%:%`(C, BINOP_instr(nt, binop_nt), `%->_%%`_instrtype(`%`_resulttype([(nt : numtype <: valtype) (nt : numtype <: valtype)]), [], `%`_resulttype([(nt : numtype <: valtype)])))

  ;; test.spectec:2824.1-2825.39
  rule testop{C : context, nt : numtype, testop_nt : testop_(nt)}:
    `%|-%:%`(C, TESTOP_instr(nt, testop_nt), `%->_%%`_instrtype(`%`_resulttype([(nt : numtype <: valtype)]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2827.1-2828.40
  rule relop{C : context, nt : numtype, relop_nt : relop_(nt)}:
    `%|-%:%`(C, RELOP_instr(nt, relop_nt), `%->_%%`_instrtype(`%`_resulttype([(nt : numtype <: valtype) (nt : numtype <: valtype)]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2830.1-2831.44
  rule cvtop{C : context, nt_1 : numtype, nt_2 : numtype, cvtop : cvtop__(nt_2, nt_1)}:
    `%|-%:%`(C, CVTOP_instr(nt_1, nt_2, cvtop), `%->_%%`_instrtype(`%`_resulttype([(nt_2 : numtype <: valtype)]), [], `%`_resulttype([(nt_1 : numtype <: valtype)])))

  ;; test.spectec:2836.1-2837.35
  rule vconst{C : context, c : vec_(V128_Vnn)}:
    `%|-%:%`(C, VCONST_instr(V128_vectype, c), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2839.1-2840.41
  rule vvunop{C : context, vvunop : vvunop}:
    `%|-%:%`(C, VVUNOP_instr(V128_vectype, vvunop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2842.1-2843.48
  rule vvbinop{C : context, vvbinop : vvbinop}:
    `%|-%:%`(C, VVBINOP_instr(V128_vectype, vvbinop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2845.1-2846.55
  rule vvternop{C : context, vvternop : vvternop}:
    `%|-%:%`(C, VVTERNOP_instr(V128_vectype, vvternop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2848.1-2849.44
  rule vvtestop{C : context, vvtestop : vvtestop}:
    `%|-%:%`(C, VVTESTOP_instr(V128_vectype, vvtestop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2851.1-2852.37
  rule vunop{C : context, sh : shape, vunop : vunop_(sh)}:
    `%|-%:%`(C, VUNOP_instr(sh, vunop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2854.1-2855.44
  rule vbinop{C : context, sh : shape, vbinop : vbinop_(sh)}:
    `%|-%:%`(C, VBINOP_instr(sh, vbinop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2857.1-2858.51
  rule vternop{C : context, sh : shape, vternop : vternop_(sh)}:
    `%|-%:%`(C, VTERNOP_instr(sh, vternop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2860.1-2861.40
  rule vtestop{C : context, sh : shape, vtestop : vtestop_(sh)}:
    `%|-%:%`(C, VTESTOP_instr(sh, vtestop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2863.1-2864.44
  rule vrelop{C : context, sh : shape, vrelop : vrelop_(sh)}:
    `%|-%:%`(C, VRELOP_instr(sh, vrelop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2866.1-2867.47
  rule vshiftop{C : context, sh : ishape, vshiftop : vshiftop_(sh)}:
    `%|-%:%`(C, VSHIFTOP_instr(sh, vshiftop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype I32_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2869.1-2870.33
  rule vbitmask{C : context, sh : ishape}:
    `%|-%:%`(C, VBITMASK_instr(sh), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2872.1-2873.50
  rule vswizzlop{C : context, sh : bshape, vswizzlop : vswizzlop_(sh)}:
    `%|-%:%`(C, VSWIZZLOP_instr(sh, vswizzlop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2875.1-2877.29
  rule vshuffle{C : context, sh : bshape, `i*` : laneidx*}:
    `%|-%:%`(C, VSHUFFLE_instr(sh, i*{i <- `i*`}), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- (if (i!`%`_laneidx.0 < (2 * $dim(sh!`%`_bshape.0)!`%`_dim.0)))*{i <- `i*`}

  ;; test.spectec:2879.1-2880.44
  rule vsplat{C : context, sh : shape}:
    `%|-%:%`(C, VSPLAT_instr(sh), `%->_%%`_instrtype(`%`_resulttype([($unpackshape(sh) : numtype <: valtype)]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2882.1-2884.21
  rule vextract_lane{C : context, sh : shape, `sx?` : sx?, i : laneidx}:
    `%|-%:%`(C, VEXTRACT_LANE_instr(sh, sx?{sx <- `sx?`}, i), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([($unpackshape(sh) : numtype <: valtype)])))
    -- if (i!`%`_laneidx.0 < $dim(sh)!`%`_dim.0)

  ;; test.spectec:2886.1-2888.21
  rule vreplace_lane{C : context, sh : shape, i : laneidx}:
    `%|-%:%`(C, VREPLACE_LANE_instr(sh, i), `%->_%%`_instrtype(`%`_resulttype([V128_valtype ($unpackshape(sh) : numtype <: valtype)]), [], `%`_resulttype([V128_valtype])))
    -- if (i!`%`_laneidx.0 < $dim(sh)!`%`_dim.0)

  ;; test.spectec:2890.1-2891.50
  rule vextunop{C : context, sh_1 : ishape, sh_2 : ishape, vextunop : vextunop__(sh_2, sh_1)}:
    `%|-%:%`(C, VEXTUNOP_instr(sh_1, sh_2, vextunop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2893.1-2894.57
  rule vextbinop{C : context, sh_1 : ishape, sh_2 : ishape, vextbinop : vextbinop__(sh_2, sh_1)}:
    `%|-%:%`(C, VEXTBINOP_instr(sh_1, sh_2, vextbinop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2896.1-2897.64
  rule vextternop{C : context, sh_1 : ishape, sh_2 : ishape, vextternop : vextternop__(sh_2, sh_1)}:
    `%|-%:%`(C, VEXTTERNOP_instr(sh_1, sh_2, vextternop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2899.1-2900.48
  rule vnarrow{C : context, sh_1 : ishape, sh_2 : ishape, sx : sx}:
    `%|-%:%`(C, VNARROW_instr(sh_1, sh_2, sx), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2902.1-2903.46
  rule vcvtop{C : context, sh_1 : shape, sh_2 : shape, vcvtop : vcvtop__(sh_2, sh_1)}:
    `%|-%:%`(C, VCVTOP_instr(sh_1, sh_2, vcvtop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([V128_valtype])))

;; test.spectec:2301.1-2301.96
relation Instrs_ok: `%|-%:%`(context, instr*, instrtype)
  ;; test.spectec:2908.1-2909.24
  rule empty{C : context}:
    `%|-%:%`(C, [], `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([])))

  ;; test.spectec:2911.1-2913.46
  rule instr{C : context, instr : instr, `t_1*` : valtype*, `x*` : idx*, `t_2*` : valtype*}:
    `%|-%:%`(C, [instr], `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instr_ok: `%|-%:%`(C, instr, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2916.1-2920.82
  rule seq{C : context, `instr_1*` : instr*, `instr_2*` : instr*, `t_1*` : valtype*, `x_1*` : idx*, `x_2*` : idx*, `t_3*` : valtype*, `t_2*` : valtype*, `init*` : init*, `t*` : valtype*}:
    `%|-%:%`(C, instr_1*{instr_1 <- `instr_1*`} ++ instr_2*{instr_2 <- `instr_2*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_1*{x_1 <- `x_1*`} ++ x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_3*{t_3 <- `t_3*`})))
    -- Instrs_ok: `%|-%:%`(C, instr_1*{instr_1 <- `instr_1*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_1*{x_1 <- `x_1*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (if (C.LOCALS_context[x_1!`%`_idx.0] = `%%`_localtype(init, t)))*{init <- `init*`, t <- `t*`, x_1 <- `x_1*`}
    -- Instrs_ok: `%|-%:%`($with_locals(C, x_1*{x_1 <- `x_1*`}, `%%`_localtype(SET_init, t)*{t <- `t*`}), instr_2*{instr_2 <- `instr_2*`}, `%->_%%`_instrtype(`%`_resulttype(t_2*{t_2 <- `t_2*`}), x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_3*{t_3 <- `t_3*`})))

  ;; test.spectec:2922.1-2926.33
  rule sub{C : context, `instr*` : instr*, it' : instrtype, it : instrtype}:
    `%|-%:%`(C, instr*{instr <- `instr*`}, it')
    -- Instrs_ok: `%|-%:%`(C, instr*{instr <- `instr*`}, it)
    -- Instrtype_sub: `%|-%<:%`(C, it, it')
    -- Instrtype_ok: `%|-%:OK`(C, it')

  ;; test.spectec:2929.1-2932.33
  rule frame{C : context, `instr*` : instr*, `t*` : valtype*, `t_1*` : valtype*, `x*` : idx*, `t_2*` : valtype*}:
    `%|-%:%`(C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t*{t <- `t*`} ++ t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`(C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Resulttype_ok: `%|-%:OK`(C, `%`_resulttype(t*{t <- `t*`}))
}

;; test.spectec:2302.1-2302.94
relation Expr_ok: `%|-%:%`(context, expr, resulttype)
  ;; test.spectec:2937.1-2939.40
  rule _{C : context, `instr*` : instr*, `t*` : valtype*}:
    `%|-%:%`(C, instr*{instr <- `instr*`}, `%`_resulttype(t*{t <- `t*`}))
    -- Instrs_ok: `%|-%:%`(C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype(t*{t <- `t*`})))

;; test.spectec:2307.1-2308.75
relation Nondefaultable: `|-%NONDEFAULTABLE`(valtype)
  ;; test.spectec:4456.1-4456.66
  rule _{t : valtype}:
    `|-%NONDEFAULTABLE`(t)
    -- if ($default_(t) = ?())

;; test.spectec:2944.1-2944.104
relation Instr_const: `%|-%CONST`(context, instr)
  ;; test.spectec:2948.1-2949.29
  rule const{C : context, nt : numtype, c_nt : num_(nt)}:
    `%|-%CONST`(C, CONST_instr(nt, c_nt))

  ;; test.spectec:2951.1-2952.30
  rule vconst{C : context, vt : vectype, c_vt : vec_(vt)}:
    `%|-%CONST`(C, VCONST_instr(vt, c_vt))

  ;; test.spectec:2954.1-2955.27
  rule `ref.null`{C : context, ht : heaptype}:
    `%|-%CONST`(C, `REF.NULL`_instr(ht))

  ;; test.spectec:2957.1-2958.23
  rule `ref.i31`{C : context}:
    `%|-%CONST`(C, `REF.I31`_instr)

  ;; test.spectec:2960.1-2961.26
  rule `ref.func`{C : context, x : idx}:
    `%|-%CONST`(C, `REF.FUNC`_instr(x))

  ;; test.spectec:2963.1-2964.28
  rule `struct.new`{C : context, x : idx}:
    `%|-%CONST`(C, `STRUCT.NEW`_instr(x))

  ;; test.spectec:2966.1-2967.36
  rule `struct.new_default`{C : context, x : idx}:
    `%|-%CONST`(C, `STRUCT.NEW_DEFAULT`_instr(x))

  ;; test.spectec:2969.1-2970.27
  rule `array.new`{C : context, x : idx}:
    `%|-%CONST`(C, `ARRAY.NEW`_instr(x))

  ;; test.spectec:2972.1-2973.35
  rule `array.new_default`{C : context, x : idx}:
    `%|-%CONST`(C, `ARRAY.NEW_DEFAULT`_instr(x))

  ;; test.spectec:2975.1-2976.35
  rule `array.new_fixed`{C : context, x : idx, n : n}:
    `%|-%CONST`(C, `ARRAY.NEW_FIXED`_instr(x, `%`_u32(n)))

  ;; test.spectec:2978.1-2979.34
  rule `any.convert_extern`{C : context}:
    `%|-%CONST`(C, `ANY.CONVERT_EXTERN`_instr)

  ;; test.spectec:2981.1-2982.34
  rule `extern.convert_any`{C : context}:
    `%|-%CONST`(C, `EXTERN.CONVERT_ANY`_instr)

  ;; test.spectec:2984.1-2986.25
  rule `global.get`{C : context, x : idx, t : valtype}:
    `%|-%CONST`(C, `GLOBAL.GET`_instr(x))
    -- if (C.GLOBALS_context[x!`%`_idx.0] = `%%`_globaltype(?(), t))

  ;; test.spectec:2988.1-2991.29
  rule binop{C : context, Inn : Inn, binop : binop_((Inn : addrtype <: numtype))}:
    `%|-%CONST`(C, BINOP_instr((Inn : addrtype <: numtype), binop))
    -- if (Inn <- [I32_Inn I64_Inn])
    -- if (binop <- [ADD_binop_ SUB_binop_ MUL_binop_])

;; test.spectec:2945.1-2945.103
relation Expr_const: `%|-%CONST`(context, expr)
  ;; test.spectec:2994.1-2995.38
  rule _{C : context, `instr*` : instr*}:
    `%|-%CONST`(C, instr*{instr <- `instr*`})
    -- (Instr_const: `%|-%CONST`(C, instr))*{instr <- `instr*`}

;; test.spectec:2946.1-2946.105
relation Expr_ok_const: `%|-%:%CONST`(context, expr, valtype)
  ;; test.spectec:2998.1-3001.33
  rule _{C : context, expr : expr, t : valtype}:
    `%|-%:%CONST`(C, expr, t)
    -- Expr_ok: `%|-%:%`(C, expr, `%`_resulttype([t]))
    -- Expr_const: `%|-%CONST`(C, expr)

;; test.spectec:3016.1-3016.97
relation Type_ok: `%|-%:%`(context, type, deftype*)
  ;; test.spectec:3029.1-3033.53
  rule _{C : context, rectype : rectype, `dt*` : deftype*, x : idx}:
    `%|-%:%`(C, TYPE_type(rectype), dt*{dt <- `dt*`})
    -- if (x!`%`_idx.0 = |C.TYPES_context|)
    -- if (dt*{dt <- `dt*`} = $rolldt(x, rectype))
    -- Rectype_ok: `%|-%:%`(C +++ {TYPES dt*{dt <- `dt*`}, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, rectype, OK_oktypeidx(x))

;; test.spectec:3017.1-3017.96
relation Tag_ok: `%|-%:%`(context, tag, tagtype)
  ;; test.spectec:3035.1-3037.35
  rule _{C : context, tagtype : tagtype}:
    `%|-%:%`(C, TAG_tag(tagtype), $clos_tagtype(C, tagtype))
    -- Tagtype_ok: `%|-%:OK`(C, tagtype)

;; test.spectec:3018.1-3018.99
relation Global_ok: `%|-%:%`(context, global, globaltype)
  ;; test.spectec:3039.1-3043.40
  rule _{C : context, globaltype : globaltype, expr : expr, t : valtype}:
    `%|-%:%`(C, GLOBAL_global(globaltype, expr), globaltype)
    -- Globaltype_ok: `%|-%:OK`(C, globaltype)
    -- if (globaltype = `%%`_globaltype(MUT_mut?{}, t))
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, t)

;; test.spectec:3019.1-3019.96
relation Mem_ok: `%|-%:%`(context, mem, memtype)
  ;; test.spectec:3045.1-3047.35
  rule _{C : context, memtype : memtype}:
    `%|-%:%`(C, MEMORY_mem(memtype), memtype)
    -- Memtype_ok: `%|-%:OK`(C, memtype)

;; test.spectec:3020.1-3020.98
relation Table_ok: `%|-%:%`(context, table, tabletype)
  ;; test.spectec:3049.1-3053.41
  rule _{C : context, tabletype : tabletype, expr : expr, at : addrtype, lim : limits, rt : reftype}:
    `%|-%:%`(C, TABLE_table(tabletype, expr), tabletype)
    -- Tabletype_ok: `%|-%:OK`(C, tabletype)
    -- if (tabletype = `%%%`_tabletype(at, lim, rt))
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, (rt : reftype <: valtype))

;; test.spectec:3027.1-3027.98
relation Local_ok: `%|-%:%`(context, local, localtype)
  ;; test.spectec:3055.1-3057.35
  rule set{C : context, t : valtype}:
    `%|-%:%`(C, LOCAL_local(t), `%%`_localtype(SET_init, t))
    -- Defaultable: `|-%DEFAULTABLE`(t)

  ;; test.spectec:3059.1-3061.41
  rule unset{C : context, t : valtype}:
    `%|-%:%`(C, LOCAL_local(t), `%%`_localtype(UNSET_init, t))
    -- Nondefaultable: `|-%NONDEFAULTABLE`(t)

;; test.spectec:3021.1-3021.97
relation Func_ok: `%|-%:%`(context, func, deftype)
  ;; test.spectec:3063.1-3068.89
  rule _{C : context, x : idx, `local*` : local*, expr : expr, `t_1*` : valtype*, `t_2*` : valtype*, `lct*` : localtype*}:
    `%|-%:%`(C, FUNC_func(x, local*{local <- `local*`}, expr), C.TYPES_context[x!`%`_idx.0])
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (Local_ok: `%|-%:%`(C, local, lct))*{lct <- `lct*`, local <- `local*`}
    -- Expr_ok: `%|-%:%`(C +++ {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS `%%`_localtype(SET_init, t_1)*{t_1 <- `t_1*`} ++ lct*{lct <- `lct*`}, LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(`%`_resulttype(t_2*{t_2 <- `t_2*`})), REFS [], RECS []}, expr, `%`_resulttype(t_2*{t_2 <- `t_2*`}))

;; test.spectec:3024.1-3024.118
relation Datamode_ok: `%|-%:%`(context, datamode, datatype)
  ;; test.spectec:3080.1-3081.20
  rule passive{C : context}:
    `%|-%:%`(C, PASSIVE_datamode, OK_datatype)

  ;; test.spectec:3083.1-3086.41
  rule active{C : context, x : idx, expr : expr, at : addrtype, lim : limits}:
    `%|-%:%`(C, ACTIVE_datamode(x, expr), OK_datatype)
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, (at : addrtype <: valtype))

;; test.spectec:3022.1-3022.115
relation Data_ok: `%|-%:%`(context, data, datatype)
  ;; test.spectec:3070.1-3072.37
  rule _{C : context, `b*` : byte*, datamode : datamode}:
    `%|-%:%`(C, DATA_data(b*{b <- `b*`}, datamode), OK_datatype)
    -- Datamode_ok: `%|-%:%`(C, datamode, OK_datatype)

;; test.spectec:3025.1-3025.101
relation Elemmode_ok: `%|-%:%`(context, elemmode, elemtype)
  ;; test.spectec:3088.1-3089.20
  rule passive{C : context, rt : reftype}:
    `%|-%:%`(C, PASSIVE_elemmode, rt)

  ;; test.spectec:3091.1-3092.20
  rule declare{C : context, rt : reftype}:
    `%|-%:%`(C, DECLARE_elemmode, rt)

  ;; test.spectec:3094.1-3098.41
  rule active{C : context, x : idx, expr : expr, rt : reftype, at : addrtype, lim : limits, rt' : reftype}:
    `%|-%:%`(C, ACTIVE_elemmode(x, expr), rt)
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt'))
    -- Reftype_sub: `%|-%<:%`(C, rt, rt')
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, (at : addrtype <: valtype))

;; test.spectec:3023.1-3023.97
relation Elem_ok: `%|-%:%`(context, elem, elemtype)
  ;; test.spectec:3074.1-3078.43
  rule _{C : context, elemtype : elemtype, `expr*` : expr*, elemmode : elemmode}:
    `%|-%:%`(C, ELEM_elem(elemtype, expr*{expr <- `expr*`}, elemmode), elemtype)
    -- Reftype_ok: `%|-%:OK`(C, elemtype)
    -- (Expr_ok_const: `%|-%:%CONST`(C, expr, (elemtype : reftype <: valtype)))*{expr <- `expr*`}
    -- Elemmode_ok: `%|-%:%`(C, elemmode, elemtype)

;; test.spectec:3026.1-3026.98
relation Start_ok: `%|-%:OK`(context, start)
  ;; test.spectec:3100.1-3102.43
  rule _{C : context, x : idx}:
    `%|-%:OK`(C, START_start(x))
    -- Expand: `%~~%`(C.FUNCS_context[x!`%`_idx.0], `FUNC%->%`_comptype(`%`_resulttype([]), `%`_resulttype([])))

;; test.spectec:3107.1-3107.105
relation Import_ok: `%|-%:%`(context, import, externtype)
  ;; test.spectec:3111.1-3113.33
  rule _{C : context, name_1 : name, name_2 : name, xt : externtype}:
    `%|-%:%`(C, IMPORT_import(name_1, name_2, xt), $clos_externtype(C, xt))
    -- Externtype_ok: `%|-%:OK`(C, xt)

;; test.spectec:3109.1-3109.108
relation Externidx_ok: `%|-%:%`(context, externidx, externtype)
  ;; test.spectec:3120.1-3122.23
  rule tag{C : context, x : idx, jt : tagtype}:
    `%|-%:%`(C, TAG_externidx(x), TAG_externtype(jt))
    -- if (C.TAGS_context[x!`%`_idx.0] = jt)

  ;; test.spectec:3124.1-3126.26
  rule global{C : context, x : idx, gt : globaltype}:
    `%|-%:%`(C, GLOBAL_externidx(x), GLOBAL_externtype(gt))
    -- if (C.GLOBALS_context[x!`%`_idx.0] = gt)

  ;; test.spectec:3128.1-3130.23
  rule mem{C : context, x : idx, mt : memtype}:
    `%|-%:%`(C, MEM_externidx(x), MEM_externtype(mt))
    -- if (C.MEMS_context[x!`%`_idx.0] = mt)

  ;; test.spectec:3132.1-3134.25
  rule table{C : context, x : idx, tt : tabletype}:
    `%|-%:%`(C, TABLE_externidx(x), TABLE_externtype(tt))
    -- if (C.TABLES_context[x!`%`_idx.0] = tt)

  ;; test.spectec:3136.1-3138.24
  rule func{C : context, x : idx, dt : deftype}:
    `%|-%:%`(C, FUNC_externidx(x), FUNC_externtype((dt : deftype <: typeuse)))
    -- if (C.FUNCS_context[x!`%`_idx.0] = dt)

;; test.spectec:3108.1-3108.105
relation Export_ok: `%|-%:%%`(context, export, name, externtype)
  ;; test.spectec:3115.1-3117.39
  rule _{C : context, name : name, externidx : externidx, xt : externtype}:
    `%|-%:%%`(C, EXPORT_export(name, externidx), name, xt)
    -- Externidx_ok: `%|-%:%`(C, externidx, xt)

;; test.spectec:3145.1-3145.100
rec {

;; test.spectec:3145.1-3145.100
relation Globals_ok: `%|-%:%`(context, global*, globaltype*)
  ;; test.spectec:3190.1-3191.17
  rule empty{C : context}:
    `%|-%:%`(C, [], [])

  ;; test.spectec:3193.1-3196.54
  rule cons{C : context, global_1 : global, `global*` : global*, gt_1 : globaltype, `gt*` : globaltype*}:
    `%|-%:%`(C, [global_1] ++ global*{global <- `global*`}, [gt_1] ++ gt*{gt <- `gt*`})
    -- Global_ok: `%|-%:%`(C, global_1, gt_1)
    -- Globals_ok: `%|-%:%`(C +++ {TYPES [], TAGS [], GLOBALS [gt_1], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, global*{global <- `global*`}, gt*{gt <- `gt*`})
}

;; test.spectec:3144.1-3144.98
rec {

;; test.spectec:3144.1-3144.98
relation Types_ok: `%|-%:%`(context, type*, deftype*)
  ;; test.spectec:3182.1-3183.17
  rule empty{C : context}:
    `%|-%:%`(C, [], [])

  ;; test.spectec:3185.1-3188.49
  rule cons{C : context, type_1 : type, `type*` : type*, `dt_1*` : deftype*, `dt*` : deftype*}:
    `%|-%:%`(C, [type_1] ++ type*{type <- `type*`}, dt_1*{dt_1 <- `dt_1*`} ++ dt*{dt <- `dt*`})
    -- Type_ok: `%|-%:%`(C, type_1, dt_1*{dt_1 <- `dt_1*`})
    -- Types_ok: `%|-%:%`(C +++ {TYPES dt_1*{dt_1 <- `dt_1*`}, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, type*{type <- `type*`}, dt*{dt <- `dt*`})
}

;; test.spectec:3148.1-3148.59
syntax nonfuncs = 
  | `%%%%%%`(`global*` : global*, `mem*` : mem*, `table*` : table*, `elem*` : elem*, `start?` : start?, `export*` : export*)

;; test.spectec:3149.1-3149.93
def $funcidx_nonfuncs(nonfuncs : nonfuncs) : funcidx*
  ;; test.spectec:3150.1-3151.87
  def $funcidx_nonfuncs{`global*` : global*, `mem*` : mem*, `table*` : table*, `elem*` : elem*, `start?` : start?, `export*` : export*}(`%%%%%%`_nonfuncs(global*{global <- `global*`}, mem*{mem <- `mem*`}, table*{table <- `table*`}, elem*{elem <- `elem*`}, start?{start <- `start?`}, export*{export <- `export*`})) = $funcidx_module(MODULE_module(`%`_list([]), `%`_list([]), `%`_list([]), `%`_list(global*{global <- `global*`}), `%`_list(mem*{mem <- `mem*`}), `%`_list(table*{table <- `table*`}), `%`_list([]), `%`_list([]), `%`_list(elem*{elem <- `elem*`}), start?{start <- `start?`}, `%`_list(export*{export <- `export*`})))

;; test.spectec:3143.1-3143.99
relation Module_ok: `|-%:%`(module, moduletype)
  ;; test.spectec:3153.1-3179.32
  rule _{`type*` : type*, `import*` : import*, `tag*` : tag*, `global*` : global*, `mem*` : mem*, `table*` : table*, `func*` : func*, `data*` : data*, `elem*` : elem*, `start?` : start?, `export*` : export*, C : context, `xt_I*` : externtype*, `xt_E*` : externtype*, `dt'*` : deftype*, C' : context, `jt*` : tagtype*, `gt*` : globaltype*, `mt*` : memtype*, `tt*` : tabletype*, `dt*` : deftype*, `ok*` : datatype*, `rt*` : reftype*, `nm*` : name*, `jt_I*` : tagtype*, `mt_I*` : memtype*, `tt_I*` : tabletype*, `gt_I*` : globaltype*, `dt_I*` : deftype*, `x*` : idx*}:
    `|-%:%`(MODULE_module(`%`_list(type*{type <- `type*`}), `%`_list(import*{import <- `import*`}), `%`_list(tag*{tag <- `tag*`}), `%`_list(global*{global <- `global*`}), `%`_list(mem*{mem <- `mem*`}), `%`_list(table*{table <- `table*`}), `%`_list(func*{func <- `func*`}), `%`_list(data*{data <- `data*`}), `%`_list(elem*{elem <- `elem*`}), start?{start <- `start?`}, `%`_list(export*{export <- `export*`})), $clos_moduletype(C, `%->%`_moduletype(xt_I*{xt_I <- `xt_I*`}, xt_E*{xt_E <- `xt_E*`})))
    -- Types_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, type*{type <- `type*`}, dt'*{dt' <- `dt'*`})
    -- (Import_ok: `%|-%:%`({TYPES dt'*{dt' <- `dt'*`}, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, import, xt_I))*{import <- `import*`, xt_I <- `xt_I*`}
    -- (Tag_ok: `%|-%:%`(C', tag, jt))*{jt <- `jt*`, tag <- `tag*`}
    -- Globals_ok: `%|-%:%`(C', global*{global <- `global*`}, gt*{gt <- `gt*`})
    -- (Mem_ok: `%|-%:%`(C', mem, mt))*{mem <- `mem*`, mt <- `mt*`}
    -- (Table_ok: `%|-%:%`(C', table, tt))*{table <- `table*`, tt <- `tt*`}
    -- (Func_ok: `%|-%:%`(C, func, dt))*{dt <- `dt*`, func <- `func*`}
    -- (Data_ok: `%|-%:%`(C, data, ok))*{data <- `data*`, ok <- `ok*`}
    -- (Elem_ok: `%|-%:%`(C, elem, rt))*{elem <- `elem*`, rt <- `rt*`}
    -- (Start_ok: `%|-%:OK`(C, start))?{start <- `start?`}
    -- (Export_ok: `%|-%:%%`(C, export, nm, xt_E))*{export <- `export*`, nm <- `nm*`, xt_E <- `xt_E*`}
    -- if $disjoint_(syntax name, nm*{nm <- `nm*`})
    -- if (C = C' +++ {TYPES [], TAGS jt_I*{jt_I <- `jt_I*`} ++ jt*{jt <- `jt*`}, GLOBALS gt*{gt <- `gt*`}, MEMS mt_I*{mt_I <- `mt_I*`} ++ mt*{mt <- `mt*`}, TABLES tt_I*{tt_I <- `tt_I*`} ++ tt*{tt <- `tt*`}, FUNCS [], DATAS ok*{ok <- `ok*`}, ELEMS rt*{rt <- `rt*`}, LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
    -- if (C' = {TYPES dt'*{dt' <- `dt'*`}, TAGS [], GLOBALS gt_I*{gt_I <- `gt_I*`}, MEMS [], TABLES [], FUNCS dt_I*{dt_I <- `dt_I*`} ++ dt*{dt <- `dt*`}, DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS x*{x <- `x*`}, RECS []})
    -- if (x*{x <- `x*`} = $funcidx_nonfuncs(`%%%%%%`_nonfuncs(global*{global <- `global*`}, mem*{mem <- `mem*`}, table*{table <- `table*`}, elem*{elem <- `elem*`}, start?{start <- `start?`}, export*{export <- `export*`})))
    -- if (jt_I*{jt_I <- `jt_I*`} = $tagsxt(xt_I*{xt_I <- `xt_I*`}))
    -- if (gt_I*{gt_I <- `gt_I*`} = $globalsxt(xt_I*{xt_I <- `xt_I*`}))
    -- if (mt_I*{mt_I <- `mt_I*`} = $memsxt(xt_I*{xt_I <- `xt_I*`}))
    -- if (tt_I*{tt_I <- `tt_I*`} = $tablesxt(xt_I*{xt_I <- `xt_I*`}))
    -- if (dt_I*{dt_I <- `dt_I*`} = $funcsxt(xt_I*{xt_I <- `xt_I*`}))

;; test.spectec:3209.1-3209.24
syntax relaxed2 = 
  | `%`(i : nat)
    -- if ((i = 0) \/ (i = 1))

;; test.spectec:3210.1-3210.32
syntax relaxed4 = 
  | `%`(i : nat)
    -- if ((((i = 0) \/ (i = 1)) \/ (i = 2)) \/ (i = 3))

;; test.spectec:3212.1-3212.83
def $relaxed2(relaxed2 : relaxed2, syntax X, X : X, X : X) : X
  ;; test.spectec:3215.1-3215.63
  def $relaxed2{i : relaxed2, syntax X, X_1 : X, X_2 : X}(i, syntax X, X_1, X_2) = (if $ND then [X_1 X_2][i!`%`_relaxed2.0] else [X_1 X_2][0])

;; test.spectec:3213.1-3213.89
def $relaxed4(relaxed4 : relaxed4, syntax X, X : X, X : X, X : X, X : X) : X
  ;; test.spectec:3218.1-3218.81
  def $relaxed4{i : relaxed4, syntax X, X_1 : X, X_2 : X, X_3 : X, X_4 : X}(i, syntax X, X_1, X_2, X_3, X_4) = (if $ND then [X_1 X_2 X_3 X_4][i!`%`_relaxed4.0] else [X_1 X_2 X_3 X_4][0])

;; test.spectec:3222.1-3222.43
def $R_fmadd : relaxed2

;; test.spectec:3223.1-3223.43
def $R_fmin : relaxed4

;; test.spectec:3224.1-3224.43
def $R_fmax : relaxed4

;; test.spectec:3225.1-3225.43
def $R_idot : relaxed2

;; test.spectec:3226.1-3226.43
def $R_iq15mulr : relaxed2

;; test.spectec:3227.1-3227.43
def $R_trunc_u : relaxed4

;; test.spectec:3228.1-3228.43
def $R_trunc_s : relaxed2

;; test.spectec:3229.1-3229.43
def $R_swizzle : relaxed2

;; test.spectec:3230.1-3230.43
def $R_laneselect : relaxed2

;; test.spectec:3245.1-3245.41
def $s33_to_u32(s33 : s33) : u32

;; test.spectec:3250.1-3250.107
def $ibits_(N : N, iN : iN(N)) : bit*

;; test.spectec:3251.1-3251.107
def $fbits_(N : N, fN : fN(N)) : bit*

;; test.spectec:3252.1-3252.109
def $ibytes_(N : N, iN : iN(N)) : byte*

;; test.spectec:3253.1-3253.109
def $fbytes_(N : N, fN : fN(N)) : byte*

;; test.spectec:3254.1-3254.104
def $nbytes_(numtype : numtype, num_ : num_(numtype)) : byte*

;; test.spectec:3255.1-3255.104
def $vbytes_(vectype : vectype, vec_ : vec_(vectype)) : byte*

;; test.spectec:3256.1-3256.104
def $zbytes_(storagetype : storagetype, lit_ : lit_(storagetype)) : byte*

;; test.spectec:3257.1-3257.104
def $cbytes_(Cnn : Cnn, lit_ : lit_((Cnn : Cnn <: storagetype))) : byte*

;; test.spectec:3259.1-3259.91
def $inv_ibits_(N : N, bit*) : iN(N)

;; test.spectec:3260.1-3260.91
def $inv_fbits_(N : N, bit*) : fN(N)

;; test.spectec:3261.1-3261.92
def $inv_ibytes_(N : N, byte*) : iN(N)

;; test.spectec:3262.1-3262.92
def $inv_fbytes_(N : N, byte*) : fN(N)

;; test.spectec:3263.1-3263.87
def $inv_nbytes_(numtype : numtype, byte*) : num_(numtype)

;; test.spectec:3264.1-3264.87
def $inv_vbytes_(vectype : vectype, byte*) : vec_(vectype)

;; test.spectec:3265.1-3265.92
def $inv_zbytes_(storagetype : storagetype, byte*) : lit_(storagetype)

;; test.spectec:3266.1-3266.87
def $inv_cbytes_(Cnn : Cnn, byte*) : lit_((Cnn : Cnn <: storagetype))

;; test.spectec:3290.1-3290.54
def $signed_(N : N, nat : nat) : int
  ;; test.spectec:3291.1-3291.54
  def $signed_{N : N, i : nat}(N, i) = (i : nat <:> int)
    -- if (i < (2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))
  ;; test.spectec:3292.1-3292.61
  def $signed_{N : N, i : nat}(N, i) = ((i : nat <:> int) - ((2 ^ N) : nat <:> int))
    -- if (((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) <= i) /\ (i < (2 ^ N)))

;; test.spectec:3294.1-3294.68
def $inv_signed_(N : N, int : int) : nat
  ;; test.spectec:3295.1-3295.62
  def $inv_signed_{N : N, i : int}(N, i) = (i : int <:> nat)
    -- if (((0 : nat <:> int) <= i) /\ (i < ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)))
  ;; test.spectec:3296.1-3296.63
  def $inv_signed_{N : N, i : int}(N, i) = ((i + ((2 ^ N) : nat <:> int)) : int <:> nat)
    -- if ((- ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) <= i) /\ (i < (0 : nat <:> int)))

;; test.spectec:3299.1-3299.60
def $sx(storagetype : storagetype) : sx?
  ;; test.spectec:3300.1-3300.25
  def $sx{consttype : consttype}((consttype : consttype <: storagetype)) = ?()
  ;; test.spectec:3301.1-3301.22
  def $sx{packtype : packtype}((packtype : packtype <: storagetype)) = ?(S_sx)

;; test.spectec:3306.1-3306.51
def $zero(lanetype : lanetype) : lane_(lanetype)
  ;; test.spectec:3307.1-3307.19
  def $zero{Jnn : Jnn}((Jnn : Jnn <: lanetype)) = `%`_lane_(0)
  ;; test.spectec:3308.1-3308.36
  def $zero{Fnn : Fnn}((Fnn : Fnn <: lanetype)) = $fzero($size((Fnn : Fnn <: numtype)))

;; test.spectec:3310.1-3310.22
def $bool(bool : bool) : nat
  ;; test.spectec:3311.1-3311.21
  def $bool(false) = 0
  ;; test.spectec:3312.1-3312.20
  def $bool(true) = 1

;; test.spectec:3314.1-3314.23
def $truncz(rat : rat) : int

;; test.spectec:3318.1-3318.59
def $ceilz(rat : rat) : int

;; test.spectec:3325.1-3325.61
def $sat_u_(N : N, int : int) : nat
  ;; test.spectec:3326.1-3326.48
  def $sat_u_{N : N, i : int}(N, i) = (if (i < (0 : nat <:> int)) then 0 else (if (i > (((2 ^ N) : nat <:> int) - (1 : nat <:> int))) then ((((2 ^ N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat) else (i : int <:> nat)))

;; test.spectec:3330.1-3330.61
def $sat_s_(N : N, int : int) : int
  ;; test.spectec:3331.1-3331.58
  def $sat_s_{N : N, i : int}(N, i) = (if (i < - ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) then - ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) else (if (i > (((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int))) then (((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)) else i))

;; test.spectec:3338.1-3338.29
def $ineg_(N : N, iN : iN(N)) : iN(N)
  ;; test.spectec:3385.1-3385.42
  def $ineg_{N : N, i_1 : iN(N)}(N, i_1) = `%`_iN((((((2 ^ N) : nat <:> int) - (i_1!`%`_iN.0 : nat <:> int)) \ ((2 ^ N) : nat <:> int)) : int <:> nat))

;; test.spectec:3339.1-3339.29
def $iabs_(N : N, iN : iN(N)) : iN(N)
  ;; test.spectec:3387.1-3387.65
  def $iabs_{N : N, i_1 : iN(N)}(N, i_1) = (if ($signed_(N, i_1!`%`_iN.0) >= (0 : nat <:> int)) then i_1 else $ineg_(N, i_1))

;; test.spectec:3340.1-3340.29
def $iclz_(N : N, iN : iN(N)) : iN(N)

;; test.spectec:3341.1-3341.29
def $ictz_(N : N, iN : iN(N)) : iN(N)

;; test.spectec:3342.1-3342.32
def $ipopcnt_(N : N, iN : iN(N)) : iN(N)

;; test.spectec:3343.1-3343.86
def $iextend_(N : N, M : M, sx : sx, iN : iN(N)) : iN(N)
  ;; test.spectec:3399.1-3399.39
  def $iextend_{N : N, M : M, i : iN(N)}(N, M, U_sx, i) = `%`_iN((i!`%`_iN.0 \ (2 ^ M)))
  ;; test.spectec:3400.1-3400.69
  def $iextend_{N : N, M : M, i : iN(N)}(N, M, S_sx, i) = `%`_iN($inv_signed_(N, $signed_(M, (i!`%`_iN.0 \ (2 ^ M)))))

;; test.spectec:3345.1-3345.36
def $iadd_(N : N, iN : iN(N), iN : iN(N)) : iN(N)
  ;; test.spectec:3403.1-3403.47
  def $iadd_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, i_1, i_2) = `%`_iN(((i_1!`%`_iN.0 + i_2!`%`_iN.0) \ (2 ^ N)))

;; test.spectec:3346.1-3346.36
def $isub_(N : N, iN : iN(N), iN : iN(N)) : iN(N)
  ;; test.spectec:3405.1-3405.53
  def $isub_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, i_1, i_2) = `%`_iN(((((((2 ^ N) + i_1!`%`_iN.0) : nat <:> int) - (i_2!`%`_iN.0 : nat <:> int)) \ ((2 ^ N) : nat <:> int)) : int <:> nat))

;; test.spectec:3347.1-3347.36
def $imul_(N : N, iN : iN(N), iN : iN(N)) : iN(N)
  ;; test.spectec:3407.1-3407.47
  def $imul_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, i_1, i_2) = `%`_iN(((i_1!`%`_iN.0 * i_2!`%`_iN.0) \ (2 ^ N)))

;; test.spectec:3348.1-3348.83
def $idiv_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)?
  ;; test.spectec:3409.1-3409.33
  def $idiv_{N : N, i_1 : iN(N)}(N, U_sx, i_1, `%`_iN(0)) = ?()
  ;; test.spectec:3410.1-3410.51
  def $idiv_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = ?(`%`_iN(($truncz(((i_1!`%`_iN.0 : nat <:> rat) / (i_2!`%`_iN.0 : nat <:> rat))) : int <:> nat)))
  ;; test.spectec:3411.1-3411.33
  def $idiv_{N : N, i_1 : iN(N)}(N, S_sx, i_1, `%`_iN(0)) = ?()
  ;; test.spectec:3412.1-3412.96
  def $idiv_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = ?()
    -- if ((($signed_(N, i_1!`%`_iN.0) : int <:> rat) / ($signed_(N, i_2!`%`_iN.0) : int <:> rat)) = ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> rat))
  ;; test.spectec:3413.1-3413.94
  def $idiv_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = ?(`%`_iN($inv_signed_(N, $truncz((($signed_(N, i_1!`%`_iN.0) : int <:> rat) / ($signed_(N, i_2!`%`_iN.0) : int <:> rat))))))

;; test.spectec:3349.1-3349.83
def $irem_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)?
  ;; test.spectec:3415.1-3415.33
  def $irem_{N : N, i_1 : iN(N)}(N, U_sx, i_1, `%`_iN(0)) = ?()
  ;; test.spectec:3416.1-3416.66
  def $irem_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = ?(`%`_iN((((i_1!`%`_iN.0 : nat <:> int) - ((i_2!`%`_iN.0 * ($truncz(((i_1!`%`_iN.0 : nat <:> rat) / (i_2!`%`_iN.0 : nat <:> rat))) : int <:> nat)) : nat <:> int)) : int <:> nat)))
  ;; test.spectec:3417.1-3417.33
  def $irem_{N : N, i_1 : iN(N)}(N, S_sx, i_1, `%`_iN(0)) = ?()
  ;; test.spectec:3418.1-3419.84
  def $irem_{N : N, i_1 : iN(N), i_2 : iN(N), j_1 : int, j_2 : int}(N, S_sx, i_1, i_2) = ?(`%`_iN($inv_signed_(N, (j_1 - (j_2 * $truncz(((j_1 : int <:> rat) / (j_2 : int <:> rat))))))))
    -- if ((j_1 = $signed_(N, i_1!`%`_iN.0)) /\ (j_2 = $signed_(N, i_2!`%`_iN.0)))

;; test.spectec:3350.1-3350.83
def $imin_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)
  ;; test.spectec:3421.1-3421.51
  def $imin_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = i_1
    -- if (i_1!`%`_iN.0 <= i_2!`%`_iN.0)
  ;; test.spectec:3422.1-3422.50
  def $imin_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = i_2
    -- if (i_1!`%`_iN.0 > i_2!`%`_iN.0)
  ;; test.spectec:3423.1-3423.77
  def $imin_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = (if ($signed_(N, i_1!`%`_iN.0) <= $signed_(N, i_2!`%`_iN.0)) then i_1 else i_2)

;; test.spectec:3351.1-3351.83
def $imax_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)
  ;; test.spectec:3426.1-3426.51
  def $imax_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = i_1
    -- if (i_1!`%`_iN.0 >= i_2!`%`_iN.0)
  ;; test.spectec:3427.1-3427.50
  def $imax_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = i_2
    -- if (i_1!`%`_iN.0 < i_2!`%`_iN.0)
  ;; test.spectec:3428.1-3428.77
  def $imax_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = (if ($signed_(N, i_1!`%`_iN.0) >= $signed_(N, i_2!`%`_iN.0)) then i_1 else i_2)

;; test.spectec:3352.1-3352.88
def $iadd_sat_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)
  ;; test.spectec:3431.1-3431.58
  def $iadd_sat_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_iN($sat_u_(N, ((i_1!`%`_iN.0 + i_2!`%`_iN.0) : nat <:> int)))
  ;; test.spectec:3432.1-3432.101
  def $iadd_sat_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_iN($inv_signed_(N, $sat_s_(N, ($signed_(N, i_1!`%`_iN.0) + $signed_(N, i_2!`%`_iN.0)))))

;; test.spectec:3353.1-3353.88
def $isub_sat_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)
  ;; test.spectec:3434.1-3434.58
  def $isub_sat_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_iN($sat_u_(N, ((i_1!`%`_iN.0 : nat <:> int) - (i_2!`%`_iN.0 : nat <:> int))))
  ;; test.spectec:3435.1-3435.101
  def $isub_sat_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_iN($inv_signed_(N, $sat_s_(N, ($signed_(N, i_1!`%`_iN.0) - $signed_(N, i_2!`%`_iN.0)))))

;; test.spectec:3354.1-3354.92
def $iq15mulr_sat_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3355.1-3355.101
def $irelaxed_q15mulr_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)*

;; test.spectec:3356.1-3356.84
def $iavgr_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3358.1-3358.29
def $inot_(N : N, iN : iN(N)) : iN(N)

;; test.spectec:3359.1-3359.29
def $irev_(N : N, iN : iN(N)) : iN(N)

;; test.spectec:3360.1-3360.36
def $iand_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3361.1-3361.39
def $iandnot_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3362.1-3362.35
def $ior_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3363.1-3363.36
def $ixor_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3364.1-3364.34
def $ishl_(N : N, iN : iN(N), u32 : u32) : iN(N)

;; test.spectec:3365.1-3365.76
def $ishr_(N : N, sx : sx, iN : iN(N), u32 : u32) : iN(N)

;; test.spectec:3366.1-3366.37
def $irotl_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3367.1-3367.37
def $irotr_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3369.1-3369.49
def $ibitselect_(N : N, iN : iN(N), iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3370.1-3370.59
def $irelaxed_laneselect_(N : N, iN : iN(N), iN : iN(N), iN : iN(N)) : iN(N)*

;; test.spectec:3372.1-3372.27
def $ieqz_(N : N, iN : iN(N)) : u32
  ;; test.spectec:3456.1-3456.36
  def $ieqz_{N : N, i_1 : iN(N)}(N, i_1) = `%`_u32($bool((i_1!`%`_iN.0 = 0)))

;; test.spectec:3373.1-3373.27
def $inez_(N : N, iN : iN(N)) : u32
  ;; test.spectec:3458.1-3458.38
  def $inez_{N : N, i_1 : iN(N)}(N, i_1) = `%`_u32($bool((i_1!`%`_iN.0 =/= 0)))

;; test.spectec:3375.1-3375.33
def $ieq_(N : N, iN : iN(N), iN : iN(N)) : u32
  ;; test.spectec:3461.1-3461.42
  def $ieq_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, i_1, i_2) = `%`_u32($bool((i_1 = i_2)))

;; test.spectec:3376.1-3376.33
def $ine_(N : N, iN : iN(N), iN : iN(N)) : u32
  ;; test.spectec:3463.1-3463.44
  def $ine_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, i_1, i_2) = `%`_u32($bool((i_1 =/= i_2)))

;; test.spectec:3377.1-3377.75
def $ilt_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : u32
  ;; test.spectec:3465.1-3465.45
  def $ilt_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_iN.0 < i_2!`%`_iN.0)))
  ;; test.spectec:3466.1-3466.71
  def $ilt_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_iN.0) < $signed_(N, i_2!`%`_iN.0))))

;; test.spectec:3378.1-3378.75
def $igt_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : u32
  ;; test.spectec:3468.1-3468.45
  def $igt_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_iN.0 > i_2!`%`_iN.0)))
  ;; test.spectec:3469.1-3469.71
  def $igt_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_iN.0) > $signed_(N, i_2!`%`_iN.0))))

;; test.spectec:3379.1-3379.75
def $ile_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : u32
  ;; test.spectec:3471.1-3471.46
  def $ile_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_iN.0 <= i_2!`%`_iN.0)))
  ;; test.spectec:3472.1-3472.72
  def $ile_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_iN.0) <= $signed_(N, i_2!`%`_iN.0))))

;; test.spectec:3380.1-3380.75
def $ige_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : u32
  ;; test.spectec:3474.1-3474.46
  def $ige_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_iN.0 >= i_2!`%`_iN.0)))
  ;; test.spectec:3475.1-3475.72
  def $ige_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_iN.0) >= $signed_(N, i_2!`%`_iN.0))))

;; test.spectec:3480.1-3480.30
def $fabs_(N : N, fN : fN(N)) : fN(N)*

;; test.spectec:3481.1-3481.30
def $fneg_(N : N, fN : fN(N)) : fN(N)*

;; test.spectec:3482.1-3482.31
def $fsqrt_(N : N, fN : fN(N)) : fN(N)*

;; test.spectec:3483.1-3483.31
def $fceil_(N : N, fN : fN(N)) : fN(N)*

;; test.spectec:3484.1-3484.32
def $ffloor_(N : N, fN : fN(N)) : fN(N)*

;; test.spectec:3485.1-3485.32
def $ftrunc_(N : N, fN : fN(N)) : fN(N)*

;; test.spectec:3486.1-3486.34
def $fnearest_(N : N, fN : fN(N)) : fN(N)*

;; test.spectec:3488.1-3488.37
def $fadd_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3489.1-3489.37
def $fsub_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3490.1-3490.37
def $fmul_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3491.1-3491.37
def $fdiv_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3492.1-3492.37
def $fmin_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3493.1-3493.37
def $fmax_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3494.1-3494.38
def $fpmin_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3495.1-3495.38
def $fpmax_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3496.1-3496.82
def $frelaxed_min_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3497.1-3497.82
def $frelaxed_max_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3498.1-3498.42
def $fcopysign_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3500.1-3500.33
def $feq_(N : N, fN : fN(N), fN : fN(N)) : u32

;; test.spectec:3501.1-3501.33
def $fne_(N : N, fN : fN(N), fN : fN(N)) : u32

;; test.spectec:3502.1-3502.33
def $flt_(N : N, fN : fN(N), fN : fN(N)) : u32

;; test.spectec:3503.1-3503.33
def $fgt_(N : N, fN : fN(N), fN : fN(N)) : u32

;; test.spectec:3504.1-3504.33
def $fle_(N : N, fN : fN(N), fN : fN(N)) : u32

;; test.spectec:3505.1-3505.33
def $fge_(N : N, fN : fN(N), fN : fN(N)) : u32

;; test.spectec:3507.1-3507.91
def $frelaxed_madd_(N : N, fN : fN(N), fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3508.1-3508.92
def $frelaxed_nmadd_(N : N, fN : fN(N), fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3546.1-3546.33
def $wrap__(M : M, N : N, iN : iN(M)) : iN(N)

;; test.spectec:3547.1-3547.90
def $extend__(M : M, N : N, sx : sx, iN : iN(M)) : iN(N)

;; test.spectec:3548.1-3548.89
def $trunc__(M : M, N : N, sx : sx, fN : fN(M)) : iN(N)?

;; test.spectec:3549.1-3549.94
def $trunc_sat__(M : M, N : N, sx : sx, fN : fN(M)) : iN(N)?

;; test.spectec:3550.1-3550.98
def $relaxed_trunc__(M : M, N : N, sx : sx, fN : fN(M)) : iN(N)?

;; test.spectec:3551.1-3551.36
def $demote__(M : M, N : N, fN : fN(M)) : fN(N)*

;; test.spectec:3552.1-3552.37
def $promote__(M : M, N : N, fN : fN(M)) : fN(N)*

;; test.spectec:3553.1-3553.91
def $convert__(M : M, N : N, sx : sx, iN : iN(M)) : fN(N)

;; test.spectec:3554.1-3554.88
def $narrow__(M : M, N : N, sx : sx, iN : iN(M)) : iN(N)

;; test.spectec:3556.1-3556.76
def $reinterpret__(numtype_1 : numtype, numtype_2 : numtype, num_ : num_(numtype_1)) : num_(numtype_2)

;; test.spectec:3576.1-3577.49
def $lpacknum_(lanetype : lanetype, num_ : num_($lunpack(lanetype))) : lane_(lanetype)
  ;; test.spectec:3581.1-3581.31
  def $lpacknum_{numtype : numtype, c : num_($lunpack((numtype : numtype <: lanetype)))}((numtype : numtype <: lanetype), c) = c
  ;; test.spectec:3582.1-3582.86
  def $lpacknum_{packtype : packtype, c : num_($lunpack((packtype : packtype <: lanetype)))}((packtype : packtype <: lanetype), c) = $wrap__($size($lunpack((packtype : packtype <: lanetype))), $psize(packtype), c)

;; test.spectec:3578.1-3579.49
def $cpacknum_(storagetype : storagetype, lit_ : lit_(($cunpack(storagetype) : consttype <: storagetype))) : lit_(storagetype)
  ;; test.spectec:3584.1-3584.33
  def $cpacknum_{consttype : consttype, c : lit_(($cunpack((consttype : consttype <: storagetype)) : consttype <: storagetype))}((consttype : consttype <: storagetype), c) = c
  ;; test.spectec:3585.1-3585.86
  def $cpacknum_{packtype : packtype, c : lit_(($cunpack((packtype : packtype <: storagetype)) : consttype <: storagetype))}((packtype : packtype <: storagetype), c) = $wrap__($size($lunpack((packtype : packtype <: lanetype))), $psize(packtype), c)

;; test.spectec:3588.1-3589.53
def $lunpacknum_(lanetype : lanetype, lane_ : lane_(lanetype)) : num_($lunpack(lanetype))
  ;; test.spectec:3593.1-3593.33
  def $lunpacknum_{numtype : numtype, c : lane_((numtype : numtype <: lanetype))}((numtype : numtype <: lanetype), c) = c
  ;; test.spectec:3594.1-3594.93
  def $lunpacknum_{packtype : packtype, c : lane_((packtype : packtype <: lanetype))}((packtype : packtype <: lanetype), c) = $extend__($psize(packtype), $size($lunpack((packtype : packtype <: lanetype))), U_sx, c)

;; test.spectec:3590.1-3591.53
def $cunpacknum_(storagetype : storagetype, lit_ : lit_(storagetype)) : lit_(($cunpack(storagetype) : consttype <: storagetype))
  ;; test.spectec:3596.1-3596.35
  def $cunpacknum_{consttype : consttype, c : lit_((consttype : consttype <: storagetype))}((consttype : consttype <: storagetype), c) = c
  ;; test.spectec:3597.1-3597.93
  def $cunpacknum_{packtype : packtype, c : lit_((packtype : packtype <: storagetype))}((packtype : packtype <: storagetype), c) = $extend__($psize(packtype), $size($lunpack((packtype : packtype <: lanetype))), U_sx, c)

;; test.spectec:3602.1-3603.28
def $unop_(numtype : numtype, unop_ : unop_(numtype), num_ : num_(numtype)) : num_(numtype)*
  ;; test.spectec:3613.1-3613.50
  def $unop_{Inn : Inn, i : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), CLZ_unop_, i) = [$iclz_($sizenn((Inn : addrtype <: numtype)), i)]
  ;; test.spectec:3614.1-3614.50
  def $unop_{Inn : Inn, i : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), CTZ_unop_, i) = [$ictz_($sizenn((Inn : addrtype <: numtype)), i)]
  ;; test.spectec:3615.1-3615.56
  def $unop_{Inn : Inn, i : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), POPCNT_unop_, i) = [$ipopcnt_($sizenn((Inn : addrtype <: numtype)), i)]
  ;; test.spectec:3616.1-3616.64
  def $unop_{Inn : Inn, M : M, i : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), EXTEND_unop_(`%`_sz(M)), i) = [$iextend_($sizenn((Inn : addrtype <: numtype)), M, S_sx, i)]
  ;; test.spectec:3618.1-3618.50
  def $unop_{Fnn : Fnn, f : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), ABS_unop_, f) = $fabs_($sizenn((Fnn : Fnn <: numtype)), f)
  ;; test.spectec:3619.1-3619.50
  def $unop_{Fnn : Fnn, f : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), NEG_unop_, f) = $fneg_($sizenn((Fnn : Fnn <: numtype)), f)
  ;; test.spectec:3620.1-3620.52
  def $unop_{Fnn : Fnn, f : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), SQRT_unop_, f) = $fsqrt_($sizenn((Fnn : Fnn <: numtype)), f)
  ;; test.spectec:3621.1-3621.52
  def $unop_{Fnn : Fnn, f : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), CEIL_unop_, f) = $fceil_($sizenn((Fnn : Fnn <: numtype)), f)
  ;; test.spectec:3622.1-3622.54
  def $unop_{Fnn : Fnn, f : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), FLOOR_unop_, f) = $ffloor_($sizenn((Fnn : Fnn <: numtype)), f)
  ;; test.spectec:3623.1-3623.54
  def $unop_{Fnn : Fnn, f : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), TRUNC_unop_, f) = $ftrunc_($sizenn((Fnn : Fnn <: numtype)), f)
  ;; test.spectec:3624.1-3624.58
  def $unop_{Fnn : Fnn, f : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), NEAREST_unop_, f) = $fnearest_($sizenn((Fnn : Fnn <: numtype)), f)

;; test.spectec:3604.1-3605.32
def $binop_(numtype : numtype, binop_ : binop_(numtype), num_ : num_(numtype), num_ : num_(numtype)) : num_(numtype)*
  ;; test.spectec:3626.1-3626.65
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), ADD_binop_, i_1, i_2) = [$iadd_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)]
  ;; test.spectec:3627.1-3627.65
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), SUB_binop_, i_1, i_2) = [$isub_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)]
  ;; test.spectec:3628.1-3628.65
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), MUL_binop_, i_1, i_2) = [$imul_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)]
  ;; test.spectec:3629.1-3629.72
  def $binop_{Inn : Inn, sx : sx, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), DIV_binop_(sx), i_1, i_2) = lift($idiv_($sizenn((Inn : addrtype <: numtype)), sx, i_1, i_2))
  ;; test.spectec:3630.1-3630.72
  def $binop_{Inn : Inn, sx : sx, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), REM_binop_(sx), i_1, i_2) = lift($irem_($sizenn((Inn : addrtype <: numtype)), sx, i_1, i_2))
  ;; test.spectec:3631.1-3631.65
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), AND_binop_, i_1, i_2) = [$iand_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)]
  ;; test.spectec:3632.1-3632.63
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), OR_binop_, i_1, i_2) = [$ior_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)]
  ;; test.spectec:3633.1-3633.65
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), XOR_binop_, i_1, i_2) = [$ixor_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)]
  ;; test.spectec:3634.1-3634.65
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), SHL_binop_, i_1, i_2) = [$ishl_($sizenn((Inn : addrtype <: numtype)), i_1, `%`_u32(i_2!`%`_num_.0))]
  ;; test.spectec:3635.1-3635.72
  def $binop_{Inn : Inn, sx : sx, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), SHR_binop_(sx), i_1, i_2) = [$ishr_($sizenn((Inn : addrtype <: numtype)), sx, i_1, `%`_u32(i_2!`%`_num_.0))]
  ;; test.spectec:3636.1-3636.67
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), ROTL_binop_, i_1, i_2) = [$irotl_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)]
  ;; test.spectec:3637.1-3637.67
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), ROTR_binop_, i_1, i_2) = [$irotr_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)]
  ;; test.spectec:3639.1-3639.65
  def $binop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), ADD_binop_, f_1, f_2) = $fadd_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3640.1-3640.65
  def $binop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), SUB_binop_, f_1, f_2) = $fsub_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3641.1-3641.65
  def $binop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), MUL_binop_, f_1, f_2) = $fmul_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3642.1-3642.65
  def $binop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), DIV_binop_, f_1, f_2) = $fdiv_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3643.1-3643.65
  def $binop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), MIN_binop_, f_1, f_2) = $fmin_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3644.1-3644.65
  def $binop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), MAX_binop_, f_1, f_2) = $fmax_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3645.1-3645.75
  def $binop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), COPYSIGN_binop_, f_1, f_2) = $fcopysign_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)

;; test.spectec:3606.1-3607.28
def $testop_(numtype : numtype, testop_ : testop_(numtype), num_ : num_(numtype)) : u32
  ;; test.spectec:3647.1-3647.52
  def $testop_{Inn : Inn, i : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), EQZ_testop_, i) = $ieqz_($sizenn((Inn : addrtype <: numtype)), i)

;; test.spectec:3608.1-3609.32
def $relop_(numtype : numtype, relop_ : relop_(numtype), num_ : num_(numtype), num_ : num_(numtype)) : u32
  ;; test.spectec:3649.1-3649.63
  def $relop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), EQ_relop_, i_1, i_2) = $ieq_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)
  ;; test.spectec:3650.1-3650.63
  def $relop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), NE_relop_, i_1, i_2) = $ine_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)
  ;; test.spectec:3651.1-3651.70
  def $relop_{Inn : Inn, sx : sx, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), LT_relop_(sx), i_1, i_2) = $ilt_($sizenn((Inn : addrtype <: numtype)), sx, i_1, i_2)
  ;; test.spectec:3652.1-3652.70
  def $relop_{Inn : Inn, sx : sx, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), GT_relop_(sx), i_1, i_2) = $igt_($sizenn((Inn : addrtype <: numtype)), sx, i_1, i_2)
  ;; test.spectec:3653.1-3653.70
  def $relop_{Inn : Inn, sx : sx, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), LE_relop_(sx), i_1, i_2) = $ile_($sizenn((Inn : addrtype <: numtype)), sx, i_1, i_2)
  ;; test.spectec:3654.1-3654.70
  def $relop_{Inn : Inn, sx : sx, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), GE_relop_(sx), i_1, i_2) = $ige_($sizenn((Inn : addrtype <: numtype)), sx, i_1, i_2)
  ;; test.spectec:3656.1-3656.63
  def $relop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), EQ_relop_, f_1, f_2) = $feq_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3657.1-3657.63
  def $relop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), NE_relop_, f_1, f_2) = $fne_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3658.1-3658.63
  def $relop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), LT_relop_, f_1, f_2) = $flt_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3659.1-3659.63
  def $relop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), GT_relop_, f_1, f_2) = $fgt_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3660.1-3660.63
  def $relop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), LE_relop_, f_1, f_2) = $fle_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3661.1-3661.63
  def $relop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), GE_relop_, f_1, f_2) = $fge_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)

;; test.spectec:3610.1-3611.32
def $cvtop__(numtype_1 : numtype, numtype_2 : numtype, cvtop__ : cvtop__(numtype_1, numtype_2), num_ : num_(numtype_1)) : num_(numtype_2)*
  ;; test.spectec:3663.1-3664.55
  def $cvtop__{Inn_1 : Inn, Inn_2 : Inn, sx : sx, i_1 : num_((Inn_1 : addrtype <: numtype))}((Inn_1 : addrtype <: numtype), (Inn_2 : addrtype <: numtype), EXTEND_cvtop__(sx), i_1) = [$extend__($sizenn1((Inn_1 : addrtype <: numtype)), $sizenn2((Inn_2 : addrtype <: numtype)), sx, i_1)]
  ;; test.spectec:3665.1-3666.49
  def $cvtop__{Inn_1 : Inn, Inn_2 : Inn, i_1 : num_((Inn_1 : addrtype <: numtype))}((Inn_1 : addrtype <: numtype), (Inn_2 : addrtype <: numtype), WRAP_cvtop__, i_1) = [$wrap__($sizenn1((Inn_1 : addrtype <: numtype)), $sizenn2((Inn_2 : addrtype <: numtype)), i_1)]
  ;; test.spectec:3667.1-3668.54
  def $cvtop__{Fnn_1 : Fnn, Inn_2 : Inn, sx : sx, f_1 : num_((Fnn_1 : Fnn <: numtype))}((Fnn_1 : Fnn <: numtype), (Inn_2 : addrtype <: numtype), TRUNC_cvtop__(sx), f_1) = lift($trunc__($sizenn1((Fnn_1 : Fnn <: numtype)), $sizenn2((Inn_2 : addrtype <: numtype)), sx, f_1))
  ;; test.spectec:3669.1-3670.58
  def $cvtop__{Fnn_1 : Fnn, Inn_2 : Inn, sx : sx, f_1 : num_((Fnn_1 : Fnn <: numtype))}((Fnn_1 : Fnn <: numtype), (Inn_2 : addrtype <: numtype), TRUNC_SAT_cvtop__(sx), f_1) = lift($trunc_sat__($sizenn1((Fnn_1 : Fnn <: numtype)), $sizenn2((Inn_2 : addrtype <: numtype)), sx, f_1))
  ;; test.spectec:3671.1-3672.56
  def $cvtop__{Inn_1 : Inn, Fnn_2 : Fnn, sx : sx, i_1 : num_((Inn_1 : addrtype <: numtype))}((Inn_1 : addrtype <: numtype), (Fnn_2 : Fnn <: numtype), CONVERT_cvtop__(sx), i_1) = [$convert__($sizenn1((Inn_1 : addrtype <: numtype)), $sizenn2((Fnn_2 : Fnn <: numtype)), sx, i_1)]
  ;; test.spectec:3673.1-3674.52
  def $cvtop__{Fnn_1 : Fnn, Fnn_2 : Fnn, f_1 : num_((Fnn_1 : Fnn <: numtype))}((Fnn_1 : Fnn <: numtype), (Fnn_2 : Fnn <: numtype), PROMOTE_cvtop__, f_1) = $promote__($sizenn1((Fnn_1 : Fnn <: numtype)), $sizenn2((Fnn_2 : Fnn <: numtype)), f_1)
  ;; test.spectec:3675.1-3676.51
  def $cvtop__{Fnn_1 : Fnn, Fnn_2 : Fnn, f_1 : num_((Fnn_1 : Fnn <: numtype))}((Fnn_1 : Fnn <: numtype), (Fnn_2 : Fnn <: numtype), DEMOTE_cvtop__, f_1) = $demote__($sizenn1((Fnn_1 : Fnn <: numtype)), $sizenn2((Fnn_2 : Fnn <: numtype)), f_1)
  ;; test.spectec:3677.1-3678.70
  def $cvtop__{Inn_1 : Inn, Fnn_2 : Fnn, i_1 : num_((Inn_1 : addrtype <: numtype))}((Inn_1 : addrtype <: numtype), (Fnn_2 : Fnn <: numtype), REINTERPRET_cvtop__, i_1) = [$reinterpret__((Inn_1 : addrtype <: numtype), (Fnn_2 : Fnn <: numtype), i_1)]
    -- if ($size((Inn_1 : addrtype <: numtype)) = $size((Fnn_2 : Fnn <: numtype)))
  ;; test.spectec:3679.1-3680.70
  def $cvtop__{Fnn_1 : Fnn, Inn_2 : Inn, f_1 : num_((Fnn_1 : Fnn <: numtype))}((Fnn_1 : Fnn <: numtype), (Inn_2 : addrtype <: numtype), REINTERPRET_cvtop__, f_1) = [$reinterpret__((Fnn_1 : Fnn <: numtype), (Inn_2 : addrtype <: numtype), f_1)]
    -- if ($size((Fnn_1 : Fnn <: numtype)) = $size((Inn_2 : addrtype <: numtype)))

;; test.spectec:3698.1-3698.84
def $lanes_(shape : shape, vec_ : vec_(V128_Vnn)) : lane_($lanetype(shape))*

;; test.spectec:3700.1-3701.37
def $inv_lanes_(shape : shape, lane_($lanetype(shape))*) : vec_(V128_Vnn)

;; test.spectec:3707.1-3707.66
def $zeroop(shape_1 : shape, shape_2 : shape, vcvtop__ : vcvtop__(shape_1, shape_2)) : zero?
  ;; test.spectec:3708.1-3708.60
  def $zeroop{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, half : half, sx : sx}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), EXTEND_vcvtop__(half, sx)) = ?()
  ;; test.spectec:3709.1-3709.62
  def $zeroop{Jnn_1 : Jnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, `half?` : half?, sx : sx}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), CONVERT_vcvtop__(half?{half <- `half?`}, sx)) = ?()
  ;; test.spectec:3710.1-3710.66
  def $zeroop{Fnn_1 : Fnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, sx : sx, `zero?` : zero?}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), TRUNC_SAT_vcvtop__(sx, zero?{zero <- `zero?`})) = zero?{zero <- `zero?`}
  ;; test.spectec:3711.1-3711.70
  def $zeroop{Fnn_1 : Fnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, sx : sx, `zero?` : zero?}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), RELAXED_TRUNC_vcvtop__(sx, zero?{zero <- `zero?`})) = zero?{zero <- `zero?`}
  ;; test.spectec:3712.1-3712.58
  def $zeroop{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, zero : zero}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), DEMOTE_vcvtop__(zero)) = ?(zero)
  ;; test.spectec:3713.1-3713.57
  def $zeroop{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), PROMOTELOW_vcvtop__) = ?()

;; test.spectec:3715.1-3715.66
def $halfop(shape_1 : shape, shape_2 : shape, vcvtop__ : vcvtop__(shape_1, shape_2)) : half?
  ;; test.spectec:3716.1-3716.61
  def $halfop{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, half : half, sx : sx}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), EXTEND_vcvtop__(half, sx)) = ?(half)
  ;; test.spectec:3717.1-3717.64
  def $halfop{Jnn_1 : Jnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, `half?` : half?, sx : sx}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), CONVERT_vcvtop__(half?{half <- `half?`}, sx)) = half?{half <- `half?`}
  ;; test.spectec:3718.1-3718.64
  def $halfop{Fnn_1 : Fnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, sx : sx, `zero?` : zero?}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), TRUNC_SAT_vcvtop__(sx, zero?{zero <- `zero?`})) = ?()
  ;; test.spectec:3719.1-3719.68
  def $halfop{Fnn_1 : Fnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, sx : sx, `zero?` : zero?}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), RELAXED_TRUNC_vcvtop__(sx, zero?{zero <- `zero?`})) = ?()
  ;; test.spectec:3720.1-3720.57
  def $halfop{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, zero : zero}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), DEMOTE_vcvtop__(zero)) = ?()
  ;; test.spectec:3721.1-3721.57
  def $halfop{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), PROMOTELOW_vcvtop__) = ?(LOW_half)

;; test.spectec:3723.1-3723.32
def $half(half : half, nat : nat, nat : nat) : nat
  ;; test.spectec:3724.1-3724.25
  def $half{i : nat, j : nat}(LOW_half, i, j) = i
  ;; test.spectec:3725.1-3725.26
  def $half{i : nat, j : nat}(HIGH_half, i, j) = j

;; test.spectec:3728.1-3728.46
def $iswizzle_lane_(N : N, iN(N)*, iN : iN(N)) : iN(N)
  ;; test.spectec:3731.1-3731.62
  def $iswizzle_lane_{N : N, `c*` : iN(N)*, i : iN(N)}(N, c*{c <- `c*`}, i) = (if (i!`%`_iN.0 < |c*{c <- `c*`}|) then c*{c <- `c*`}[i!`%`_iN.0] else `%`_iN(0))

;; test.spectec:3729.1-3729.54
def $irelaxed_swizzle_lane_(N : N, iN(N)*, iN : iN(N)) : iN(N)
  ;; test.spectec:3734.1-3734.62
  def $irelaxed_swizzle_lane_{N : N, `c*` : iN(N)*, i : iN(N)}(N, c*{c <- `c*`}, i) = (if (i!`%`_iN.0 < |c*{c <- `c*`}|) then c*{c <- `c*`}[i!`%`_iN.0] else (if ($signed_(N, i!`%`_iN.0) < (0 : nat <:> int)) then `%`_iN(0) else $relaxed2($R_swizzle, syntax iN(N), `%`_iN(0), c*{c <- `c*`}[(i!`%`_iN.0 \ |c*{c <- `c*`}|)])))

;; test.spectec:3742.1-3742.87
def $ivunop_(shape : shape, def $f_(N : N, iN : iN(N)) : iN(N), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3765.1-3767.40
  def $ivunop_{Jnn : Jnn, M : M, def $f_(N : N, iN : iN(N)) : iN(N), v_1 : vec_(V128_Vnn), `c*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*, `c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, v_1) = [$inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})]
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1))
    -- if (c*{c <- `c*`} = $f_($lsizenn((Jnn : Jnn <: lanetype)), c_1)*{c_1 <- `c_1*`})

;; test.spectec:3743.1-3743.74
def $fvunop_(shape : shape, def $f_(N : N, fN : fN(N)) : fN(N)*, vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3769.1-3771.66
  def $fvunop_{Fnn : Fnn, M : M, def $f_(N : N, fN : fN(N)) : fN(N)*, v_1 : vec_(V128_Vnn), `c**` : lane_((Fnn : Fnn <: lanetype))**, `c_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $f_, v_1) = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`}
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v_1))
    -- if (c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $f_($sizenn((Fnn : Fnn <: numtype)), c_1)*{c_1 <- `c_1*`}))

;; test.spectec:3745.1-3745.107
def $ivbinop_(shape : shape, def $f_(N : N, iN : iN(N), iN : iN(N)) : iN(N), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3774.1-3777.45
  def $ivbinop_{Jnn : Jnn, M : M, def $f_(N : N, iN : iN(N), iN : iN(N)) : iN(N), v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), `c*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*, `c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `c_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, v_1, v_2) = [$inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})]
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1))
    -- if (c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_2))
    -- if (c*{c <- `c*`} = $f_($lsizenn((Jnn : Jnn <: lanetype)), c_1, c_2)*{c_1 <- `c_1*`, c_2 <- `c_2*`})

;; test.spectec:3746.1-3746.117
def $ivbinopsx_(shape : shape, def $f_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N), sx : sx, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3779.1-3782.49
  def $ivbinopsx_{Jnn : Jnn, M : M, def $f_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N), sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), `c*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*, `c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `c_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, sx, v_1, v_2) = [$inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})]
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1))
    -- if (c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_2))
    -- if (c*{c <- `c*`} = $f_($lsizenn((Jnn : Jnn <: lanetype)), sx, c_1, c_2)*{c_1 <- `c_1*`, c_2 <- `c_2*`})

;; test.spectec:3747.1-3747.106
def $ivbinopsxnd_(shape : shape, def $f_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)*, sx : sx, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3784.1-3787.76
  def $ivbinopsxnd_{Jnn : Jnn, M : M, def $f_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)*, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), `c**` : lane_((Jnn : Jnn <: lanetype))**, `c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `c_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, sx, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`}
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1))
    -- if (c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_2))
    -- if (c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_((Jnn : Jnn <: lanetype)), $f_($lsizenn((Jnn : Jnn <: lanetype)), sx, c_1, c_2)*{c_1 <- `c_1*`, c_2 <- `c_2*`}))

;; test.spectec:3748.1-3748.94
def $fvbinop_(shape : shape, def $f_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3789.1-3792.71
  def $fvbinop_{Fnn : Fnn, M : M, def $f_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), `c**` : lane_((Fnn : Fnn <: lanetype))**, `c_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `c_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`}
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v_1))
    -- if (c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v_2))
    -- if (c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $f_($sizenn((Fnn : Fnn <: numtype)), c_1, c_2)*{c_1 <- `c_1*`, c_2 <- `c_2*`}))

;; test.spectec:3750.1-3750.116
def $ivternopnd_(shape : shape, def $f_(N : N, iN : iN(N), iN : iN(N), iN : iN(N)) : iN(N)*, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3795.1-3799.77
  def $ivternopnd_{Jnn : Jnn, M : M, def $f_(N : N, iN : iN(N), iN : iN(N), iN : iN(N)) : iN(N)*, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), v_3 : vec_(V128_Vnn), `c**` : lane_((Jnn : Jnn <: lanetype))**, `c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `c_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `c_3*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, v_1, v_2, v_3) = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`}
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1))
    -- if (c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_2))
    -- if (c_3*{c_3 <- `c_3*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_3))
    -- if (c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_((Jnn : Jnn <: lanetype)), $f_($lsizenn((Jnn : Jnn <: lanetype)), c_1, c_2, c_3)*{c_1 <- `c_1*`, c_2 <- `c_2*`, c_3 <- `c_3*`}))

;; test.spectec:3751.1-3751.114
def $fvternop_(shape : shape, def $f_(N : N, fN : fN(N), fN : fN(N), fN : fN(N)) : fN(N)*, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3801.1-3805.76
  def $fvternop_{Fnn : Fnn, M : M, def $f_(N : N, fN : fN(N), fN : fN(N), fN : fN(N)) : fN(N)*, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), v_3 : vec_(V128_Vnn), `c**` : lane_((Fnn : Fnn <: lanetype))**, `c_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `c_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `c_3*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $f_, v_1, v_2, v_3) = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`}
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v_1))
    -- if (c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v_2))
    -- if (c_3*{c_3 <- `c_3*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v_3))
    -- if (c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $f_($sizenn((Fnn : Fnn <: numtype)), c_1, c_2, c_3)*{c_1 <- `c_1*`, c_2 <- `c_2*`, c_3 <- `c_3*`}))

;; test.spectec:3753.1-3753.90
def $ivrelop_(shape : shape, def $f_(N : N, iN : iN(N), iN : iN(N)) : u32, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3808.1-3811.77
  def $ivrelop_{Jnn : Jnn, M : M, def $f_(N : N, iN : iN(N), iN : iN(N)) : u32, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), `c*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*, `c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `c_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1))
    -- if (c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_2))
    -- if (c*{c <- `c*`} = $extend__(1, $lsizenn((Jnn : Jnn <: lanetype)), S_sx, `%`_iN($f_($lsizenn((Jnn : Jnn <: lanetype)), c_1, c_2)!`%`_u32.0))*{c_1 <- `c_1*`, c_2 <- `c_2*`})

;; test.spectec:3754.1-3754.100
def $ivrelopsx_(shape : shape, def $f_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : u32, sx : sx, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3813.1-3816.81
  def $ivrelopsx_{Jnn : Jnn, M : M, def $f_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : u32, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), `c*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*, `c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `c_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, sx, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1))
    -- if (c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_2))
    -- if (c*{c <- `c*`} = $extend__(1, $lsizenn((Jnn : Jnn <: lanetype)), S_sx, `%`_iN($f_($lsizenn((Jnn : Jnn <: lanetype)), sx, c_1, c_2)!`%`_u32.0))*{c_1 <- `c_1*`, c_2 <- `c_2*`})

;; test.spectec:3755.1-3755.90
def $fvrelop_(shape : shape, def $f_(N : N, fN : fN(N), fN : fN(N)) : u32, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3818.1-3822.36
  def $fvrelop_{Fnn : Fnn, M : M, def $f_(N : N, fN : fN(N), fN : fN(N)) : u32, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), Inn : Inn, `c*` : iN($sizenn((Fnn : Fnn <: numtype)))*, `c_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*, `c_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape((Inn : addrtype <: lanetype), `%`_dim(M)), `%`_lane_(c!`%`_iN.0)*{c <- `c*`})
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v_1))
    -- if (c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v_2))
    -- if (c*{c <- `c*`} = $extend__(1, $sizenn((Fnn : Fnn <: numtype)), S_sx, `%`_iN($f_($sizenn((Fnn : Fnn <: numtype)), c_1, c_2)!`%`_u32.0))*{c_1 <- `c_1*`, c_2 <- `c_2*`})
    -- if ($isize(Inn) = $fsize(Fnn))

;; test.spectec:3757.1-3757.99
def $ivshiftop_(shape : shape, def $f_(N : N, iN : iN(N), u32 : u32) : iN(N), vec_ : vec_(V128_Vnn), u32 : u32) : vec_(V128_Vnn)
  ;; test.spectec:3825.1-3827.41
  def $ivshiftop_{Jnn : Jnn, M : M, def $f_(N : N, iN : iN(N), u32 : u32) : iN(N), v_1 : vec_(V128_Vnn), i : u32, `c*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*, `c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, v_1, i) = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1))
    -- if (c*{c <- `c*`} = $f_($lsizenn((Jnn : Jnn <: lanetype)), c_1, i)*{c_1 <- `c_1*`})

;; test.spectec:3758.1-3758.109
def $ivshiftopsx_(shape : shape, def $f_(N : N, sx : sx, iN : iN(N), u32 : u32) : iN(N), sx : sx, vec_ : vec_(V128_Vnn), u32 : u32) : vec_(V128_Vnn)
  ;; test.spectec:3829.1-3831.45
  def $ivshiftopsx_{Jnn : Jnn, M : M, def $f_(N : N, sx : sx, iN : iN(N), u32 : u32) : iN(N), sx : sx, v_1 : vec_(V128_Vnn), i : u32, `c*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*, `c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, sx, v_1, i) = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1))
    -- if (c*{c <- `c*`} = $f_($lsizenn((Jnn : Jnn <: lanetype)), sx, c_1, i)*{c_1 <- `c_1*`})

;; test.spectec:3760.1-3760.43
def $ivbitmaskop_(shape : shape, vec_ : vec_(V128_Vnn)) : u32
  ;; test.spectec:3834.1-3836.72
  def $ivbitmaskop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), c : iN(32), `c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1) = $irev_(32, c)
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1))
    -- if ($ibits_(32, c) = `%`_bit($ilt_($lsizenn((Jnn : Jnn <: lanetype)), S_sx, c_1, `%`_iN(0))!`%`_u32.0)*{c_1 <- `c_1*`} ++ `%`_bit(0)^(((32 : nat <:> int) - (M : nat <:> int)) : int <:> nat){})

;; test.spectec:3761.1-3761.110
def $ivswizzlop_(shape : shape, def $f_(N : N, iN(N)*, iN : iN(N)) : iN(N), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3839.1-3842.44
  def $ivswizzlop_{Jnn : Jnn, M : M, def $f_(N : N, iN(N)*, iN : iN(N)) : iN(N), v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), `c*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*, `c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `c_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1))
    -- if (c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_2))
    -- if (c*{c <- `c*`} = $f_($lsizenn((Jnn : Jnn <: lanetype)), c_1*{c_1 <- `c_1*`}, c_2)*{c_2 <- `c_2*`})

;; test.spectec:3762.1-3762.85
def $ivshufflop_(shape : shape, laneidx*, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3845.1-3848.34
  def $ivshufflop_{Jnn : Jnn, M : M, `i*` : laneidx*, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), `c*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*, `c_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), i*{i <- `i*`}, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1))
    -- if (c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_2))
    -- if (c*{c <- `c*`} = c_1*{c_1 <- `c_1*`} ++ c_2*{c_2 <- `c_2*`}[i!`%`_laneidx.0]*{i <- `i*`})

;; test.spectec:3853.1-3854.28
def $vvunop_(vectype : vectype, vvunop : vvunop, vec_ : vec_(vectype)) : vec_(vectype)*
  ;; test.spectec:3894.1-3894.53
  def $vvunop_{Vnn : Vnn, v : vec_(Vnn)}(Vnn, NOT_vvunop, v) = [$inot_($vsizenn(Vnn), v)]

;; test.spectec:3855.1-3856.31
def $vvbinop_(vectype : vectype, vvbinop : vvbinop, vec_ : vec_(vectype), vec_ : vec_(vectype)) : vec_(vectype)*
  ;; test.spectec:3896.1-3896.68
  def $vvbinop_{Vnn : Vnn, v_1 : vec_(Vnn), v_2 : vec_(Vnn)}(Vnn, AND_vvbinop, v_1, v_2) = [$iand_($vsizenn(Vnn), v_1, v_2)]
  ;; test.spectec:3897.1-3897.74
  def $vvbinop_{Vnn : Vnn, v_1 : vec_(Vnn), v_2 : vec_(Vnn)}(Vnn, ANDNOT_vvbinop, v_1, v_2) = [$iandnot_($vsizenn(Vnn), v_1, v_2)]
  ;; test.spectec:3898.1-3898.66
  def $vvbinop_{Vnn : Vnn, v_1 : vec_(Vnn), v_2 : vec_(Vnn)}(Vnn, OR_vvbinop, v_1, v_2) = [$ior_($vsizenn(Vnn), v_1, v_2)]
  ;; test.spectec:3899.1-3899.68
  def $vvbinop_{Vnn : Vnn, v_1 : vec_(Vnn), v_2 : vec_(Vnn)}(Vnn, XOR_vvbinop, v_1, v_2) = [$ixor_($vsizenn(Vnn), v_1, v_2)]

;; test.spectec:3857.1-3858.34
def $vvternop_(vectype : vectype, vvternop : vvternop, vec_ : vec_(vectype), vec_ : vec_(vectype), vec_ : vec_(vectype)) : vec_(vectype)*
  ;; test.spectec:3901.1-3901.91
  def $vvternop_{Vnn : Vnn, v_1 : vec_(Vnn), v_2 : vec_(Vnn), v_3 : vec_(Vnn)}(Vnn, BITSELECT_vvternop, v_1, v_2, v_3) = [$ibitselect_($vsizenn(Vnn), v_1, v_2, v_3)]

;; test.spectec:3860.1-3861.28
def $vunop_(shape : shape, vunop_ : vunop_(shape), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3903.1-3903.60
  def $vunop_{Fnn : Fnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), ABS_vunop_, v) = $fvunop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fabs_, v)
  ;; test.spectec:3904.1-3904.60
  def $vunop_{Fnn : Fnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), NEG_vunop_, v) = $fvunop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fneg_, v)
  ;; test.spectec:3905.1-3905.62
  def $vunop_{Fnn : Fnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), SQRT_vunop_, v) = $fvunop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fsqrt_, v)
  ;; test.spectec:3906.1-3906.62
  def $vunop_{Fnn : Fnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), CEIL_vunop_, v) = $fvunop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fceil_, v)
  ;; test.spectec:3907.1-3907.64
  def $vunop_{Fnn : Fnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), FLOOR_vunop_, v) = $fvunop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $ffloor_, v)
  ;; test.spectec:3908.1-3908.64
  def $vunop_{Fnn : Fnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), TRUNC_vunop_, v) = $fvunop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $ftrunc_, v)
  ;; test.spectec:3909.1-3909.68
  def $vunop_{Fnn : Fnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), NEAREST_vunop_, v) = $fvunop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fnearest_, v)
  ;; test.spectec:3911.1-3911.60
  def $vunop_{Jnn : Jnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), ABS_vunop_, v) = $ivunop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $iabs_, v)
  ;; test.spectec:3912.1-3912.60
  def $vunop_{Jnn : Jnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), NEG_vunop_, v) = $ivunop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ineg_, v)
  ;; test.spectec:3913.1-3913.66
  def $vunop_{Jnn : Jnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), POPCNT_vunop_, v) = $ivunop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ipopcnt_, v)

;; test.spectec:3862.1-3863.31
def $vbinop_(shape : shape, vbinop_ : vbinop_(shape), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3915.1-3915.76
  def $vbinop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), ADD_vbinop_, v_1, v_2) = $ivbinop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $iadd_, v_1, v_2)
  ;; test.spectec:3916.1-3916.76
  def $vbinop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), SUB_vbinop_, v_1, v_2) = $ivbinop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $isub_, v_1, v_2)
  ;; test.spectec:3917.1-3917.76
  def $vbinop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), MUL_vbinop_, v_1, v_2) = $ivbinop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $imul_, v_1, v_2)
  ;; test.spectec:3918.1-3918.93
  def $vbinop_{Jnn : Jnn, M : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), ADD_SAT_vbinop_(sx), v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $iadd_sat_, sx, v_1, v_2)
  ;; test.spectec:3919.1-3919.93
  def $vbinop_{Jnn : Jnn, M : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), SUB_SAT_vbinop_(sx), v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $isub_sat_, sx, v_1, v_2)
  ;; test.spectec:3920.1-3920.85
  def $vbinop_{Jnn : Jnn, M : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), MIN_vbinop_(sx), v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $imin_, sx, v_1, v_2)
  ;; test.spectec:3921.1-3921.85
  def $vbinop_{Jnn : Jnn, M : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), MAX_vbinop_(sx), v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $imax_, sx, v_1, v_2)
  ;; test.spectec:3922.1-3922.85
  def $vbinop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), AVGRU_vbinop_, v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $iavgr_, U_sx, v_1, v_2)
  ;; test.spectec:3923.1-3923.99
  def $vbinop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), Q15MULR_SATS_vbinop_, v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $iq15mulr_sat_, S_sx, v_1, v_2)
  ;; test.spectec:3924.1-3924.109
  def $vbinop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), RELAXED_Q15MULRS_vbinop_, v_1, v_2) = $ivbinopsxnd_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $irelaxed_q15mulr_, S_sx, v_1, v_2)
  ;; test.spectec:3926.1-3926.76
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), ADD_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fadd_, v_1, v_2)
  ;; test.spectec:3927.1-3927.76
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), SUB_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fsub_, v_1, v_2)
  ;; test.spectec:3928.1-3928.76
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), MUL_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fmul_, v_1, v_2)
  ;; test.spectec:3929.1-3929.76
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), DIV_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fdiv_, v_1, v_2)
  ;; test.spectec:3930.1-3930.76
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), MIN_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fmin_, v_1, v_2)
  ;; test.spectec:3931.1-3931.76
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), MAX_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fmax_, v_1, v_2)
  ;; test.spectec:3932.1-3932.78
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), PMIN_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fpmin_, v_1, v_2)
  ;; test.spectec:3933.1-3933.78
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), PMAX_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fpmax_, v_1, v_2)
  ;; test.spectec:3934.1-3934.92
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), RELAXED_MIN_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $frelaxed_min_, v_1, v_2)
  ;; test.spectec:3935.1-3935.92
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), RELAXED_MAX_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $frelaxed_max_, v_1, v_2)

;; test.spectec:3864.1-3865.34
def $vternop_(shape : shape, vternop_ : vternop_(shape), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3937.1-3937.120
  def $vternop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), v_3 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), RELAXED_LANESELECT_vternop_, v_1, v_2, v_3) = $ivternopnd_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $irelaxed_laneselect_, v_1, v_2, v_3)
  ;; test.spectec:3939.1-3939.106
  def $vternop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), v_3 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), RELAXED_MADD_vternop_, v_1, v_2, v_3) = $fvternop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $frelaxed_madd_, v_1, v_2, v_3)
  ;; test.spectec:3940.1-3940.108
  def $vternop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), v_3 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), RELAXED_NMADD_vternop_, v_1, v_2, v_3) = $fvternop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $frelaxed_nmadd_, v_1, v_2, v_3)

;; test.spectec:3866.1-3867.31
def $vrelop_(shape : shape, vrelop_ : vrelop_(shape), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3942.1-3942.74
  def $vrelop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), EQ_vrelop_, v_1, v_2) = $ivrelop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ieq_, v_1, v_2)
  ;; test.spectec:3943.1-3943.74
  def $vrelop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), NE_vrelop_, v_1, v_2) = $ivrelop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ine_, v_1, v_2)
  ;; test.spectec:3944.1-3944.83
  def $vrelop_{Jnn : Jnn, M : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), LT_vrelop_(sx), v_1, v_2) = $ivrelopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ilt_, sx, v_1, v_2)
  ;; test.spectec:3945.1-3945.83
  def $vrelop_{Jnn : Jnn, M : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), GT_vrelop_(sx), v_1, v_2) = $ivrelopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $igt_, sx, v_1, v_2)
  ;; test.spectec:3946.1-3946.83
  def $vrelop_{Jnn : Jnn, M : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), LE_vrelop_(sx), v_1, v_2) = $ivrelopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ile_, sx, v_1, v_2)
  ;; test.spectec:3947.1-3947.83
  def $vrelop_{Jnn : Jnn, M : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), GE_vrelop_(sx), v_1, v_2) = $ivrelopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ige_, sx, v_1, v_2)
  ;; test.spectec:3949.1-3949.74
  def $vrelop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), EQ_vrelop_, v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $feq_, v_1, v_2)
  ;; test.spectec:3950.1-3950.74
  def $vrelop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), NE_vrelop_, v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fne_, v_1, v_2)
  ;; test.spectec:3951.1-3951.74
  def $vrelop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), LT_vrelop_, v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $flt_, v_1, v_2)
  ;; test.spectec:3952.1-3952.74
  def $vrelop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), GT_vrelop_, v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fgt_, v_1, v_2)
  ;; test.spectec:3953.1-3953.74
  def $vrelop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), LE_vrelop_, v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fle_, v_1, v_2)
  ;; test.spectec:3954.1-3954.74
  def $vrelop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), GE_vrelop_, v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fge_, v_1, v_2)

;; test.spectec:3869.1-3870.41
def $lcvtop__(shape_1 : shape, shape_2 : shape, vcvtop__ : vcvtop__(shape_1, shape_2), lane_ : lane_($lanetype(shape_1))) : lane_($lanetype(shape_2))*
  ;; test.spectec:3966.1-3967.69
  def $lcvtop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, half : half, sx : sx, c_1 : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)))), c : iN($lsizenn2((Jnn_2 : Jnn <: lanetype)))}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), EXTEND_vcvtop__(half, sx), c_1) = [c]
    -- if (c = $extend__($lsizenn1((Jnn_1 : Jnn <: lanetype)), $lsizenn2((Jnn_2 : Jnn <: lanetype)), sx, c_1))
  ;; test.spectec:3968.1-3969.70
  def $lcvtop__{Jnn_1 : Jnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, `half?` : half?, sx : sx, c_1 : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)))), c : fN($lsizenn2((Fnn_2 : Fnn <: lanetype)))}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), CONVERT_vcvtop__(half?{half <- `half?`}, sx), c_1) = [c]
    -- if (c = $convert__($lsizenn1((Jnn_1 : Jnn <: lanetype)), $lsizenn2((Fnn_2 : Fnn <: lanetype)), sx, c_1))
  ;; test.spectec:3970.1-3971.73
  def $lcvtop__{Fnn_1 : Fnn, M_1 : M, Inn_2 : Inn, M_2 : M, sx : sx, `zero?` : zero?, c_1 : lane_($lanetype(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)))), `c?` : iN($lsizenn2((Inn_2 : addrtype <: lanetype)))?}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Inn_2 : addrtype <: lanetype), `%`_dim(M_2)), TRUNC_SAT_vcvtop__(sx, zero?{zero <- `zero?`}), c_1) = lift(c?{c <- `c?`})
    -- if (c?{c <- `c?`} = $trunc_sat__($lsizenn1((Fnn_1 : Fnn <: lanetype)), $lsizenn2((Inn_2 : addrtype <: lanetype)), sx, c_1))
  ;; test.spectec:3972.1-3973.77
  def $lcvtop__{Fnn_1 : Fnn, M_1 : M, Inn_2 : Inn, M_2 : M, sx : sx, `zero?` : zero?, c_1 : lane_($lanetype(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)))), `c?` : iN($lsizenn2((Inn_2 : addrtype <: lanetype)))?}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Inn_2 : addrtype <: lanetype), `%`_dim(M_2)), RELAXED_TRUNC_vcvtop__(sx, zero?{zero <- `zero?`}), c_1) = lift(c?{c <- `c?`})
    -- if (c?{c <- `c?`} = $relaxed_trunc__($lsizenn1((Fnn_1 : Fnn <: lanetype)), $lsizenn2((Inn_2 : addrtype <: lanetype)), sx, c_1))
  ;; test.spectec:3974.1-3975.66
  def $lcvtop__{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, c_1 : lane_($lanetype(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)))), `c*` : fN($lsizenn2((Fnn_2 : Fnn <: lanetype)))*}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), DEMOTE_vcvtop__(ZERO_zero), c_1) = c*{c <- `c*`}
    -- if (c*{c <- `c*`} = $demote__($lsizenn1((Fnn_1 : Fnn <: lanetype)), $lsizenn2((Fnn_2 : Fnn <: lanetype)), c_1))
  ;; test.spectec:3976.1-3977.67
  def $lcvtop__{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, c_1 : lane_($lanetype(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)))), `c*` : fN($lsizenn2((Fnn_2 : Fnn <: lanetype)))*}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), PROMOTELOW_vcvtop__, c_1) = c*{c <- `c*`}
    -- if (c*{c <- `c*`} = $promote__($lsizenn1((Fnn_1 : Fnn <: lanetype)), $lsizenn2((Fnn_2 : Fnn <: lanetype)), c_1))

;; test.spectec:3871.1-3872.41
def $vcvtop__(shape_1 : shape, shape_2 : shape, vcvtop__ : vcvtop__(shape_1, shape_2), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3979.1-3983.41
  def $vcvtop__{Lnn_1 : Lnn, M : M, Lnn_2 : Lnn, vcvtop : vcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M))), v_1 : vec_(V128_Vnn), v : vec_(V128_Vnn), `c_1*` : lane_($lanetype(`%X%`_shape(Lnn_1, `%`_dim(M))))*, `c**` : lane_(Lnn_2)**}(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M)), vcvtop, v_1) = v
    -- if (($halfop(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M)), vcvtop) = ?()) /\ ($zeroop(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M)), vcvtop) = ?()))
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape(Lnn_1, `%`_dim(M)), v_1))
    -- if (c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_(Lnn_2), $lcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M)), vcvtop, c_1)*{c_1 <- `c_1*`}))
    -- if (v <- $inv_lanes_(`%X%`_shape(Lnn_2, `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`})
  ;; test.spectec:3984.1-3988.43
  def $vcvtop__{Lnn_1 : Lnn, M_1 : M, Lnn_2 : Lnn, M_2 : M, vcvtop : vcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2))), v_1 : vec_(V128_Vnn), v : vec_(V128_Vnn), half : half, `c_1*` : lane_($lanetype(`%X%`_shape(Lnn_1, `%`_dim(M_1))))*, `c**` : lane_(Lnn_2)**}(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop, v_1) = v
    -- if ($halfop(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop) = ?(half))
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape(Lnn_1, `%`_dim(M_1)), v_1)[$half(half, 0, M_2) : M_2])
    -- if (c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_(Lnn_2), $lcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop, c_1)*{c_1 <- `c_1*`}))
    -- if (v <- $inv_lanes_(`%X%`_shape(Lnn_2, `%`_dim(M_2)), c*{c <- `c*`})*{`c*` <- `c**`})
  ;; test.spectec:3989.1-3993.43
  def $vcvtop__{Lnn_1 : Lnn, M_1 : M, Lnn_2 : Lnn, M_2 : M, vcvtop : vcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2))), v_1 : vec_(V128_Vnn), v : vec_(V128_Vnn), `c_1*` : lane_($lanetype(`%X%`_shape(Lnn_1, `%`_dim(M_1))))*, `c**` : lane_(Lnn_2)**}(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop, v_1) = v
    -- if ($zeroop(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop) = ?(ZERO_zero))
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape(Lnn_1, `%`_dim(M_1)), v_1))
    -- if (c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_(Lnn_2), $lcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop, c_1)*{c_1 <- `c_1*`} ++ [$zero(Lnn_2)]^M_1{}))
    -- if (v <- $inv_lanes_(`%X%`_shape(Lnn_2, `%`_dim(M_2)), c*{c <- `c*`})*{`c*` <- `c**`})

;; test.spectec:3874.1-3875.34
def $vshiftop_(ishape : ishape, vshiftop_ : vshiftop_(ishape), vec_ : vec_(V128_Vnn), u32 : u32) : vec_(V128_Vnn)
  ;; test.spectec:3956.1-3956.72
  def $vshiftop_{Jnn : Jnn, M : M, v : vec_(V128_Vnn), i : u32}(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))), SHL_vshiftop_, v, i) = $ivshiftop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ishl_, v, i)
  ;; test.spectec:3957.1-3957.81
  def $vshiftop_{Jnn : Jnn, M : M, sx : sx, v : vec_(V128_Vnn), i : u32}(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))), SHR_vshiftop_(sx), v, i) = $ivshiftopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ishr_, sx, v, i)

;; test.spectec:3876.1-3877.34
def $vbitmaskop_(ishape : ishape, vec_ : vec_(V128_Vnn)) : u32
  ;; test.spectec:3959.1-3959.57
  def $vbitmaskop_{Jnn : Jnn, M : M, v : vec_(V128_Vnn)}(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))), v) = $ivbitmaskop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v)

;; test.spectec:3878.1-3879.31
def $vswizzlop_(bshape : bshape, vswizzlop_ : vswizzlop_(bshape), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3961.1-3961.93
  def $vswizzlop_{M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(M))), SWIZZLE_vswizzlop_, v_1, v_2) = $ivswizzlop_(`%X%`_shape(I8_lanetype, `%`_dim(M)), def $iswizzle_lane_, v_1, v_2)
  ;; test.spectec:3962.1-3962.109
  def $vswizzlop_{M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(M))), RELAXED_SWIZZLE_vswizzlop_, v_1, v_2) = $ivswizzlop_(`%X%`_shape(I8_lanetype, `%`_dim(M)), def $irelaxed_swizzle_lane_, v_1, v_2)

;; test.spectec:3880.1-3881.40
def $vshufflop_(bshape : bshape, laneidx*, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3964.1-3964.75
  def $vshufflop_{M : M, `i*` : laneidx*, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(M))), i*{i <- `i*`}, v_1, v_2) = $ivshufflop_(`%X%`_shape(I8_lanetype, `%`_dim(M)), i*{i <- `i*`}, v_1, v_2)

;; test.spectec:3883.1-3884.49
def $vnarrowop__(shape_1 : shape, shape_2 : shape, sx : sx, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3995.1-4000.53
  def $vnarrowop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), v : vec_(V128_Vnn), `c_1*` : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))))*, `c_2*` : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))))*, `c'_1*` : iN($lsize((Jnn_2 : Jnn <: lanetype)))*, `c'_2*` : iN($lsize((Jnn_2 : Jnn <: lanetype)))*}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), sx, v_1, v_2) = v
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), v_1))
    -- if (c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), v_2))
    -- if (c'_1*{c'_1 <- `c'_1*`} = $narrow__($lsize((Jnn_1 : Jnn <: lanetype)), $lsize((Jnn_2 : Jnn <: lanetype)), sx, c_1)*{c_1 <- `c_1*`})
    -- if (c'_2*{c'_2 <- `c'_2*`} = $narrow__($lsize((Jnn_1 : Jnn <: lanetype)), $lsize((Jnn_2 : Jnn <: lanetype)), sx, c_2)*{c_2 <- `c_2*`})
    -- if (v = $inv_lanes_(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), c'_1*{c'_1 <- `c'_1*`} ++ c'_2*{c'_2 <- `c'_2*`}))

;; test.spectec:4044.1-4044.76
def $ivadd_pairwise_(N : N, iN(N)*) : iN(N)*
  ;; test.spectec:4045.1-4046.37
  def $ivadd_pairwise_{N : N, `i*` : iN(N)*, `j_1*` : N*, `j_2*` : N*}(N, i*{i <- `i*`}) = $iadd_(N, `%`_iN(j_1), `%`_iN(j_2))*{j_1 <- `j_1*`, j_2 <- `j_2*`}
    -- if ($concat_(syntax N, [j_1 j_2]*{j_1 <- `j_1*`, j_2 <- `j_2*`}) = i!`%`_iN.0*{i <- `i*`})

;; test.spectec:4030.1-4030.93
def $ivextunop__(shape_1 : shape, shape_2 : shape, def $f_(N : N, iN(N)*) : iN(N)*, sx : sx, vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:4031.1-4034.42
  def $ivextunop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, def $f_(N : N, iN(N)*) : iN(N)*, sx : sx, v_1 : vec_(V128_Vnn), `c*` : iN($lsizenn2((Jnn_2 : Jnn <: lanetype)))*, `c_1*` : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))))*, `c'_1*` : iN($lsizenn2((Jnn_2 : Jnn <: lanetype)))*}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), def $f_, sx, v_1) = $inv_lanes_(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), c*{c <- `c*`})
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), v_1))
    -- if (c'_1*{c'_1 <- `c'_1*`} = $extend__($lsizenn1((Jnn_1 : Jnn <: lanetype)), $lsizenn2((Jnn_2 : Jnn <: lanetype)), sx, c_1)*{c_1 <- `c_1*`})
    -- if (c*{c <- `c*`} = $f_($lsizenn2((Jnn_2 : Jnn <: lanetype)), c'_1*{c'_1 <- `c'_1*`}))

;; test.spectec:3886.1-3887.32
def $vextunop__(ishape_1 : ishape, ishape_2 : ishape, vextunop__ : vextunop__(ishape_1, ishape_2), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:4059.1-4060.70
  def $vextunop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, sx : sx, v_1 : vec_(V128_Vnn)}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))), EXTADD_PAIRWISE_vextunop__(sx), v_1) = $ivextunop__(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), def $ivadd_pairwise_, sx, v_1)

;; test.spectec:4051.1-4051.40
def $ivdot_(N : N, iN(N)*, iN(N)*) : iN(N)*
  ;; test.spectec:4052.1-4053.59
  def $ivdot_{N : N, `i_1*` : iN(N)*, `i_2*` : iN(N)*, `j_1*` : iN(N)*, `j_2*` : iN(N)*}(N, i_1*{i_1 <- `i_1*`}, i_2*{i_2 <- `i_2*`}) = $iadd_(N, j_1, j_2)*{j_1 <- `j_1*`, j_2 <- `j_2*`}
    -- if ($concat_(syntax iN(N), [j_1 j_2]*{j_1 <- `j_1*`, j_2 <- `j_2*`}) = $imul_(N, i_1, i_2)*{i_1 <- `i_1*`, i_2 <- `i_2*`})

;; test.spectec:4055.1-4055.76
def $ivdot_sat_(N : N, iN(N)*, iN(N)*) : iN(N)*
  ;; test.spectec:4056.1-4057.59
  def $ivdot_sat_{N : N, `i_1*` : iN(N)*, `i_2*` : iN(N)*, `j_1*` : iN(N)*, `j_2*` : iN(N)*}(N, i_1*{i_1 <- `i_1*`}, i_2*{i_2 <- `i_2*`}) = $iadd_sat_(N, S_sx, j_1, j_2)*{j_1 <- `j_1*`, j_2 <- `j_2*`}
    -- if ($concat_(syntax iN(N), [j_1 j_2]*{j_1 <- `j_1*`, j_2 <- `j_2*`}) = $imul_(N, i_1, i_2)*{i_1 <- `i_1*`, i_2 <- `i_2*`})

;; test.spectec:4036.1-4036.136
def $ivextbinop__(shape_1 : shape, shape_2 : shape, def $f_(N : N, iN(N)*, iN(N)*) : iN(N)*, sx : sx, sx : sx, laneidx : laneidx, laneidx : laneidx, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:4037.1-4042.49
  def $ivextbinop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, def $f_(N : N, iN(N)*, iN(N)*) : iN(N)*, sx_1 : sx, sx_2 : sx, i : laneidx, k : laneidx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), `c*` : iN($lsizenn2((Jnn_2 : Jnn <: lanetype)))*, `c_1*` : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))))*, `c_2*` : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))))*, `c'_1*` : iN($lsizenn2((Jnn_2 : Jnn <: lanetype)))*, `c'_2*` : iN($lsizenn2((Jnn_2 : Jnn <: lanetype)))*}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), c*{c <- `c*`})
    -- if (c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), v_1)[i!`%`_laneidx.0 : k!`%`_laneidx.0])
    -- if (c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), v_2)[i!`%`_laneidx.0 : k!`%`_laneidx.0])
    -- if (c'_1*{c'_1 <- `c'_1*`} = $extend__($lsizenn1((Jnn_1 : Jnn <: lanetype)), $lsizenn2((Jnn_2 : Jnn <: lanetype)), sx_1, c_1)*{c_1 <- `c_1*`})
    -- if (c'_2*{c'_2 <- `c'_2*`} = $extend__($lsizenn1((Jnn_1 : Jnn <: lanetype)), $lsizenn2((Jnn_2 : Jnn <: lanetype)), sx_2, c_2)*{c_2 <- `c_2*`})
    -- if (c*{c <- `c*`} = $f_($lsizenn2((Jnn_2 : Jnn <: lanetype)), c'_1*{c'_1 <- `c'_1*`}, c'_2*{c'_2 <- `c'_2*`}))

;; test.spectec:4048.1-4048.40
def $ivmul_(N : N, iN(N)*, iN(N)*) : iN(N)*
  ;; test.spectec:4049.1-4049.50
  def $ivmul_{N : N, `i_1*` : iN(N)*, `i_2*` : iN(N)*}(N, i_1*{i_1 <- `i_1*`}, i_2*{i_2 <- `i_2*`}) = $imul_(N, i_1, i_2)*{i_1 <- `i_1*`, i_2 <- `i_2*`}

;; test.spectec:3888.1-3889.35
def $vextbinop__(ishape_1 : ishape, ishape_2 : ishape, vextbinop__ : vextbinop__(ishape_1, ishape_2), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:4062.1-4063.97
  def $vextbinop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, half : half, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))), EXTMUL_vextbinop__(half, sx), v_1, v_2) = $ivextbinop__(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), def $ivmul_, sx, sx, `%`_laneidx($half(half, 0, M_2)), `%`_laneidx(M_2), v_1, v_2)
  ;; test.spectec:4064.1-4065.77
  def $vextbinop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))), DOTS_vextbinop__, v_1, v_2) = $ivextbinop__(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), def $ivdot_, S_sx, S_sx, `%`_laneidx(0), `%`_laneidx(M_1), v_1, v_2)
  ;; test.spectec:4066.1-4067.108
  def $vextbinop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))), RELAXED_DOTS_vextbinop__, v_1, v_2) = $ivextbinop__(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), def $ivdot_sat_, S_sx, $relaxed2($R_idot, syntax sx, S_sx, U_sx), `%`_laneidx(0), `%`_laneidx(M_1), v_1, v_2)

;; test.spectec:3890.1-3891.38
def $vextternop__(ishape_1 : ishape, ishape_2 : ishape, vextternop__ : vextternop__(ishape_1, ishape_2), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:4086.1-4091.50
  def $vextternop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), c_3 : vec_(V128_Vnn), c : vec_(V128_Vnn), Jnn : Jnn, M : M, c' : vec_(V128_Vnn), c'' : vec_(V128_Vnn)}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))), RELAXED_DOT_ADDS_vextternop__, c_1, c_2, c_3) = c
    -- if ($jsizenn(Jnn) = (2 * $lsizenn1((Jnn_1 : Jnn <: lanetype))))
    -- if (M = (2 * M_2))
    -- if (c' = $vextbinop__(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))), RELAXED_DOTS_vextbinop__, c_1, c_2))
    -- if (c'' = $vextunop__(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))), EXTADD_PAIRWISE_vextunop__(S_sx), c'))
    -- if (c <- $vbinop_(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), ADD_vbinop_, c'', c_3))

;; test.spectec:4128.1-4129.63
syntax num = 
  | CONST(numtype : numtype, num_(numtype))

;; test.spectec:4131.1-4132.87
syntax vec = 
  | VCONST(vectype : vectype, vec_(vectype))

;; test.spectec:4147.1-4148.58
syntax result = 
  | _VALS(`val*` : val*)
  | `(REF.EXN_ADDR%)THROW_REF`(exnaddr : exnaddr)
  | TRAP

;; test.spectec:4156.1-4156.72
syntax hostfunc = 
  | `...`

;; test.spectec:4157.1-4157.73
syntax funccode = 
  | FUNC(typeidx : typeidx, `local*` : local*, expr : expr)
  | `...`

;; test.spectec:4159.1-4160.19
syntax taginst = 
{
  TYPE tagtype
}

;; test.spectec:4162.1-4163.33
syntax globalinst = 
{
  TYPE globaltype,
  VALUE val
}

;; test.spectec:4165.1-4166.32
syntax meminst = 
{
  TYPE memtype,
  BYTES byte*
}

;; test.spectec:4168.1-4169.32
syntax tableinst = 
{
  TYPE tabletype,
  REFS ref*
}

;; test.spectec:4171.1-4172.53
syntax funcinst = 
{
  TYPE deftype,
  MODULE moduleinst,
  CODE funccode
}

;; test.spectec:4174.1-4175.18
syntax datainst = 
{
  BYTES byte*
}

;; test.spectec:4177.1-4178.31
syntax eleminst = 
{
  TYPE elemtype,
  REFS ref*
}

;; test.spectec:4184.1-4185.64
syntax packval = 
  | PACK(packtype : packtype, iN($psizenn(packtype)))

;; test.spectec:4187.1-4188.18
syntax fieldval = 
  | CONST(numtype : numtype, num_(numtype))
  | VCONST(vectype : vectype, vec_(vectype))
  | `REF.I31_NUM`(u31 : u31)
  | `REF.NULL_ADDR`
  | `REF.STRUCT_ADDR`(structaddr : structaddr)
  | `REF.ARRAY_ADDR`(arrayaddr : arrayaddr)
  | `REF.FUNC_ADDR`(funcaddr : funcaddr)
  | `REF.EXN_ADDR`(exnaddr : exnaddr)
  | `REF.HOST_ADDR`(hostaddr : hostaddr)
  | `REF.EXTERN`(ref : ref)
  | PACK(packtype : packtype, iN($psizenn(packtype)))

;; test.spectec:4190.1-4191.37
syntax structinst = 
{
  TYPE deftype,
  FIELDS fieldval*
}

;; test.spectec:4193.1-4194.37
syntax arrayinst = 
{
  TYPE deftype,
  FIELDS fieldval*
}

;; test.spectec:4196.1-4197.31
syntax exninst = 
{
  TAG tagaddr,
  FIELDS val*
}

;; test.spectec:4214.1-4224.20
syntax store = 
{
  TAGS taginst*,
  GLOBALS globalinst*,
  MEMS meminst*,
  TABLES tableinst*,
  FUNCS funcinst*,
  DATAS datainst*,
  ELEMS eleminst*,
  STRUCTS structinst*,
  ARRAYS arrayinst*,
  EXNS exninst*
}

;; test.spectec:4243.1-4243.47
syntax state = 
  | `%;%`(store : store, frame : frame)

;; test.spectec:4244.1-4244.57
syntax config = 
  | `%;%`(state : state, `instr*` : instr*)

;; test.spectec:4271.1-4271.31
def $Ki : nat
  ;; test.spectec:4272.1-4272.15
  def $Ki = 1024

;; test.spectec:4277.1-4277.114
def $packfield_(storagetype : storagetype, val : val) : fieldval
  ;; test.spectec:4280.1-4280.36
  def $packfield_{valtype : valtype, val : val}((valtype : valtype <: storagetype), val) = (val : val <: fieldval)
  ;; test.spectec:4281.1-4281.88
  def $packfield_{packtype : packtype, i : num_(I32_numtype)}((packtype : packtype <: storagetype), CONST_val(I32_numtype, i)) = PACK_fieldval(packtype, $wrap__(32, $psize(packtype), i))

;; test.spectec:4278.1-4278.126
def $unpackfield_(storagetype : storagetype, sx?, fieldval : fieldval) : val
  ;; test.spectec:4283.1-4283.43
  def $unpackfield_{valtype : valtype, val : val}((valtype : valtype <: storagetype), ?(), (val : val <: fieldval)) = val
  ;; test.spectec:4284.1-4284.100
  def $unpackfield_{packtype : packtype, sx : sx, i : iN($psizenn(packtype))}((packtype : packtype <: storagetype), ?(sx), PACK_fieldval(packtype, i)) = CONST_val(I32_numtype, $extend__($psize(packtype), 32, sx, i))

;; test.spectec:4289.1-4289.86
rec {

;; test.spectec:4289.1-4289.86
def $tagsxa(externaddr*) : tagaddr*
  ;; test.spectec:4295.1-4295.23
  def $tagsxa([]) = []
  ;; test.spectec:4296.1-4296.42
  def $tagsxa{a : addr, `xa*` : externaddr*}([TAG_externaddr(a)] ++ xa*{xa <- `xa*`}) = [a] ++ $tagsxa(xa*{xa <- `xa*`})
  ;; test.spectec:4297.1-4297.57
  def $tagsxa{externaddr : externaddr, `xa*` : externaddr*}([externaddr] ++ xa*{xa <- `xa*`}) = $tagsxa(xa*{xa <- `xa*`})
}

;; test.spectec:4290.1-4290.89
rec {

;; test.spectec:4290.1-4290.89
def $globalsxa(externaddr*) : globaladdr*
  ;; test.spectec:4299.1-4299.26
  def $globalsxa([]) = []
  ;; test.spectec:4300.1-4300.51
  def $globalsxa{a : addr, `xa*` : externaddr*}([GLOBAL_externaddr(a)] ++ xa*{xa <- `xa*`}) = [a] ++ $globalsxa(xa*{xa <- `xa*`})
  ;; test.spectec:4301.1-4301.63
  def $globalsxa{externaddr : externaddr, `xa*` : externaddr*}([externaddr] ++ xa*{xa <- `xa*`}) = $globalsxa(xa*{xa <- `xa*`})
}

;; test.spectec:4291.1-4291.86
rec {

;; test.spectec:4291.1-4291.86
def $memsxa(externaddr*) : memaddr*
  ;; test.spectec:4303.1-4303.23
  def $memsxa([]) = []
  ;; test.spectec:4304.1-4304.42
  def $memsxa{a : addr, `xa*` : externaddr*}([MEM_externaddr(a)] ++ xa*{xa <- `xa*`}) = [a] ++ $memsxa(xa*{xa <- `xa*`})
  ;; test.spectec:4305.1-4305.57
  def $memsxa{externaddr : externaddr, `xa*` : externaddr*}([externaddr] ++ xa*{xa <- `xa*`}) = $memsxa(xa*{xa <- `xa*`})
}

;; test.spectec:4292.1-4292.88
rec {

;; test.spectec:4292.1-4292.88
def $tablesxa(externaddr*) : tableaddr*
  ;; test.spectec:4307.1-4307.25
  def $tablesxa([]) = []
  ;; test.spectec:4308.1-4308.48
  def $tablesxa{a : addr, `xa*` : externaddr*}([TABLE_externaddr(a)] ++ xa*{xa <- `xa*`}) = [a] ++ $tablesxa(xa*{xa <- `xa*`})
  ;; test.spectec:4309.1-4309.61
  def $tablesxa{externaddr : externaddr, `xa*` : externaddr*}([externaddr] ++ xa*{xa <- `xa*`}) = $tablesxa(xa*{xa <- `xa*`})
}

;; test.spectec:4293.1-4293.87
rec {

;; test.spectec:4293.1-4293.87
def $funcsxa(externaddr*) : funcaddr*
  ;; test.spectec:4311.1-4311.24
  def $funcsxa([]) = []
  ;; test.spectec:4312.1-4312.45
  def $funcsxa{a : addr, `xa*` : externaddr*}([FUNC_externaddr(a)] ++ xa*{xa <- `xa*`}) = [a] ++ $funcsxa(xa*{xa <- `xa*`})
  ;; test.spectec:4313.1-4313.59
  def $funcsxa{externaddr : externaddr, `xa*` : externaddr*}([externaddr] ++ xa*{xa <- `xa*`}) = $funcsxa(xa*{xa <- `xa*`})
}

;; test.spectec:4318.1-4318.74
def $store(state : state) : store
  ;; test.spectec:4321.1-4321.23
  def $store{s : store, f : frame}(`%;%`_state(s, f)) = s

;; test.spectec:4319.1-4319.74
def $frame(state : state) : frame
  ;; test.spectec:4322.1-4322.23
  def $frame{s : store, f : frame}(`%;%`_state(s, f)) = f

;; test.spectec:4324.1-4324.80
def $tagaddr(state : state) : tagaddr*
  ;; test.spectec:4325.1-4325.37
  def $tagaddr{s : store, f : frame}(`%;%`_state(s, f)) = f.MODULE_frame.TAGS_moduleinst

;; test.spectec:4327.1-4327.76
def $moduleinst(state : state) : moduleinst
  ;; test.spectec:4339.1-4339.35
  def $moduleinst{s : store, f : frame}(`%;%`_state(s, f)) = f.MODULE_frame

;; test.spectec:4328.1-4328.76
def $taginst(state : state) : taginst*
  ;; test.spectec:4340.1-4340.30
  def $taginst{s : store, f : frame}(`%;%`_state(s, f)) = s.TAGS_store

;; test.spectec:4329.1-4329.76
def $globalinst(state : state) : globalinst*
  ;; test.spectec:4341.1-4341.36
  def $globalinst{s : store, f : frame}(`%;%`_state(s, f)) = s.GLOBALS_store

;; test.spectec:4330.1-4330.76
def $meminst(state : state) : meminst*
  ;; test.spectec:4342.1-4342.30
  def $meminst{s : store, f : frame}(`%;%`_state(s, f)) = s.MEMS_store

;; test.spectec:4331.1-4331.76
def $tableinst(state : state) : tableinst*
  ;; test.spectec:4343.1-4343.34
  def $tableinst{s : store, f : frame}(`%;%`_state(s, f)) = s.TABLES_store

;; test.spectec:4332.1-4332.76
def $funcinst(state : state) : funcinst*
  ;; test.spectec:4344.1-4344.32
  def $funcinst{s : store, f : frame}(`%;%`_state(s, f)) = s.FUNCS_store

;; test.spectec:4333.1-4333.76
def $datainst(state : state) : datainst*
  ;; test.spectec:4345.1-4345.32
  def $datainst{s : store, f : frame}(`%;%`_state(s, f)) = s.DATAS_store

;; test.spectec:4334.1-4334.76
def $eleminst(state : state) : eleminst*
  ;; test.spectec:4346.1-4346.32
  def $eleminst{s : store, f : frame}(`%;%`_state(s, f)) = s.ELEMS_store

;; test.spectec:4335.1-4335.76
def $structinst(state : state) : structinst*
  ;; test.spectec:4347.1-4347.36
  def $structinst{s : store, f : frame}(`%;%`_state(s, f)) = s.STRUCTS_store

;; test.spectec:4336.1-4336.76
def $arrayinst(state : state) : arrayinst*
  ;; test.spectec:4348.1-4348.34
  def $arrayinst{s : store, f : frame}(`%;%`_state(s, f)) = s.ARRAYS_store

;; test.spectec:4337.1-4337.76
def $exninst(state : state) : exninst*
  ;; test.spectec:4349.1-4349.30
  def $exninst{s : store, f : frame}(`%;%`_state(s, f)) = s.EXNS_store

;; test.spectec:4363.1-4363.38
def $fof(state : state) : frame
  ;; test.spectec:4366.1-4366.24
  def $fof{z : state}(z) = $frame(z)

;; test.spectec:4352.1-4352.85
def $type(state : state, typeidx : typeidx) : deftype
  ;; test.spectec:4368.1-4368.42
  def $type{z : state, x : idx}(z, x) = $fof(z).MODULE_frame.TYPES_moduleinst[x!`%`_idx.0]

;; test.spectec:4362.1-4362.38
def $sof(state : state) : store
  ;; test.spectec:4365.1-4365.24
  def $sof{z : state}(z) = $store(z)

;; test.spectec:4353.1-4353.85
def $tag(state : state, tagidx : tagidx) : taginst
  ;; test.spectec:4369.1-4369.54
  def $tag{z : state, x : idx}(z, x) = $sof(z).TAGS_store[$fof(z).MODULE_frame.TAGS_moduleinst[x!`%`_idx.0]]

;; test.spectec:4354.1-4354.85
def $global(state : state, globalidx : globalidx) : globalinst
  ;; test.spectec:4370.1-4370.63
  def $global{z : state, x : idx}(z, x) = $sof(z).GLOBALS_store[$fof(z).MODULE_frame.GLOBALS_moduleinst[x!`%`_idx.0]]

;; test.spectec:4355.1-4355.85
def $mem(state : state, memidx : memidx) : meminst
  ;; test.spectec:4371.1-4371.54
  def $mem{z : state, x : idx}(z, x) = $sof(z).MEMS_store[$fof(z).MODULE_frame.MEMS_moduleinst[x!`%`_idx.0]]

;; test.spectec:4356.1-4356.85
def $table(state : state, tableidx : tableidx) : tableinst
  ;; test.spectec:4372.1-4372.60
  def $table{z : state, x : idx}(z, x) = $sof(z).TABLES_store[$fof(z).MODULE_frame.TABLES_moduleinst[x!`%`_idx.0]]

;; test.spectec:4357.1-4357.85
def $func(state : state, funcidx : funcidx) : funcinst
  ;; test.spectec:4373.1-4373.57
  def $func{z : state, x : idx}(z, x) = $sof(z).FUNCS_store[$fof(z).MODULE_frame.FUNCS_moduleinst[x!`%`_idx.0]]

;; test.spectec:4358.1-4358.85
def $data(state : state, dataidx : dataidx) : datainst
  ;; test.spectec:4374.1-4374.57
  def $data{z : state, x : idx}(z, x) = $sof(z).DATAS_store[$fof(z).MODULE_frame.DATAS_moduleinst[x!`%`_idx.0]]

;; test.spectec:4359.1-4359.85
def $elem(state : state, tableidx : tableidx) : eleminst
  ;; test.spectec:4375.1-4375.57
  def $elem{z : state, x : idx}(z, x) = $sof(z).ELEMS_store[$fof(z).MODULE_frame.ELEMS_moduleinst[x!`%`_idx.0]]

;; test.spectec:4360.1-4360.85
def $local(state : state, localidx : localidx) : val?
  ;; test.spectec:4376.1-4376.37
  def $local{z : state, x : idx}(z, x) = $fof(z).LOCALS_frame[x!`%`_idx.0]

;; test.spectec:4381.1-4381.165
def $with_local(state : state, localidx : localidx, val : val) : state
  ;; test.spectec:4392.1-4392.60
  def $with_local{z : state, x : idx, v : val}(z, x, v) = `%;%`_state($sof(z), $fof(z)[LOCALS_frame[x!`%`_idx.0] = ?(v)])

;; test.spectec:4382.1-4382.172
def $with_global(state : state, globalidx : globalidx, val : val) : state
  ;; test.spectec:4393.1-4393.92
  def $with_global{z : state, x : idx, v : val}(z, x, v) = `%;%`_state($sof(z)[GLOBALS_store[$fof(z).MODULE_frame.GLOBALS_moduleinst[x!`%`_idx.0]].VALUE_globalinst = v], $fof(z))

;; test.spectec:4383.1-4383.174
def $with_table(state : state, tableidx : tableidx, nat : nat, ref : ref) : state
  ;; test.spectec:4394.1-4394.94
  def $with_table{z : state, x : idx, i : nat, r : ref}(z, x, i, r) = `%;%`_state($sof(z)[TABLES_store[$fof(z).MODULE_frame.TABLES_moduleinst[x!`%`_idx.0]].REFS_tableinst[i] = r], $fof(z))

;; test.spectec:4384.1-4384.165
def $with_tableinst(state : state, tableidx : tableidx, tableinst : tableinst) : state
  ;; test.spectec:4395.1-4395.89
  def $with_tableinst{z : state, x : idx, ti : tableinst}(z, x, ti) = `%;%`_state($sof(z)[TABLES_store[$fof(z).MODULE_frame.TABLES_moduleinst[x!`%`_idx.0]] = ti], $fof(z))

;; test.spectec:4385.1-4385.176
def $with_mem(state : state, memidx : memidx, nat : nat, nat : nat, byte*) : state
  ;; test.spectec:4396.1-4396.98
  def $with_mem{z : state, x : idx, i : nat, j : nat, `b*` : byte*}(z, x, i, j, b*{b <- `b*`}) = `%;%`_state($sof(z)[MEMS_store[$fof(z).MODULE_frame.MEMS_moduleinst[x!`%`_idx.0]].BYTES_meminst[i : j] = b*{b <- `b*`}], $fof(z))

;; test.spectec:4386.1-4386.167
def $with_meminst(state : state, memidx : memidx, meminst : meminst) : state
  ;; test.spectec:4397.1-4397.83
  def $with_meminst{z : state, x : idx, mi : meminst}(z, x, mi) = `%;%`_state($sof(z)[MEMS_store[$fof(z).MODULE_frame.MEMS_moduleinst[x!`%`_idx.0]] = mi], $fof(z))

;; test.spectec:4387.1-4387.169
def $with_elem(state : state, elemidx : elemidx, ref*) : state
  ;; test.spectec:4398.1-4398.87
  def $with_elem{z : state, x : idx, `r*` : ref*}(z, x, r*{r <- `r*`}) = `%;%`_state($sof(z)[ELEMS_store[$fof(z).MODULE_frame.ELEMS_moduleinst[x!`%`_idx.0]].REFS_eleminst = r*{r <- `r*`}], $fof(z))

;; test.spectec:4388.1-4388.170
def $with_data(state : state, dataidx : dataidx, byte*) : state
  ;; test.spectec:4399.1-4399.88
  def $with_data{z : state, x : idx, `b*` : byte*}(z, x, b*{b <- `b*`}) = `%;%`_state($sof(z)[DATAS_store[$fof(z).MODULE_frame.DATAS_moduleinst[x!`%`_idx.0]].BYTES_datainst = b*{b <- `b*`}], $fof(z))

;; test.spectec:4389.1-4389.181
def $with_struct(state : state, structaddr : structaddr, nat : nat, fieldval : fieldval) : state
  ;; test.spectec:4400.1-4400.77
  def $with_struct{z : state, a : addr, i : nat, fv : fieldval}(z, a, i, fv) = `%;%`_state($sof(z)[STRUCTS_store[a].FIELDS_structinst[i] = fv], $fof(z))

;; test.spectec:4390.1-4390.180
def $with_array(state : state, arrayaddr : arrayaddr, nat : nat, fieldval : fieldval) : state
  ;; test.spectec:4401.1-4401.75
  def $with_array{z : state, a : addr, i : nat, fv : fieldval}(z, a, i, fv) = `%;%`_state($sof(z)[ARRAYS_store[a].FIELDS_arrayinst[i] = fv], $fof(z))

;; test.spectec:4404.1-4404.140
def $add_structinst(state : state, structinst*) : state
  ;; test.spectec:4408.1-4408.65
  def $add_structinst{z : state, `si*` : structinst*}(z, si*{si <- `si*`}) = `%;%`_state($sof(z)[STRUCTS_store =++ si*{si <- `si*`}], $fof(z))

;; test.spectec:4405.1-4405.139
def $add_arrayinst(state : state, arrayinst*) : state
  ;; test.spectec:4409.1-4409.63
  def $add_arrayinst{z : state, `ai*` : arrayinst*}(z, ai*{ai <- `ai*`}) = `%;%`_state($sof(z)[ARRAYS_store =++ ai*{ai <- `ai*`}], $fof(z))

;; test.spectec:4406.1-4406.137
def $add_exninst(state : state, exninst*) : state
  ;; test.spectec:4410.1-4410.61
  def $add_exninst{z : state, `exn*` : exninst*}(z, exn*{exn <- `exn*`}) = `%;%`_state($sof(z)[EXNS_store =++ exn*{exn <- `exn*`}], $fof(z))

;; test.spectec:4415.1-4415.62
def $growtable(tableinst : tableinst, nat : nat, ref : ref) : tableinst
  ;; test.spectec:4418.1-4423.33
  def $growtable{tableinst : tableinst, n : n, r : ref, tableinst' : tableinst, at : addrtype, i : u64, `j?` : u64?, rt : reftype, `r'*` : ref*, i' : u64}(tableinst, n, r) = tableinst'
    -- if (tableinst = {TYPE `%%%`_tabletype(at, `[%..%]`_limits(i, j?{j <- `j?`}), rt), REFS r'*{r' <- `r'*`}})
    -- if (tableinst' = {TYPE `%%%`_tabletype(at, `[%..%]`_limits(i', j?{j <- `j?`}), rt), REFS r'*{r' <- `r'*`} ++ r^n{}})
    -- if (i'!`%`_u64.0 = (|r'*{r' <- `r'*`}| + n))
    -- (if (i'!`%`_u64.0 <= j!`%`_u64.0))?{j <- `j?`}
    -- if ((i'!`%`_u64.0 : nat <:> int) <= (((2 ^ $size((at : addrtype <: numtype))) : nat <:> int) - (1 : nat <:> int)))

;; test.spectec:4416.1-4416.62
def $growmem(meminst : meminst, nat : nat) : meminst
  ;; test.spectec:4425.1-4430.36
  def $growmem{meminst : meminst, n : n, meminst' : meminst, at : addrtype, i : u64, `j?` : u64?, `b*` : byte*, i' : u64}(meminst, n) = meminst'
    -- if (meminst = {TYPE `%%PAGE`_memtype(at, `[%..%]`_limits(i, j?{j <- `j?`})), BYTES b*{b <- `b*`}})
    -- if (meminst' = {TYPE `%%PAGE`_memtype(at, `[%..%]`_limits(i', j?{j <- `j?`})), BYTES b*{b <- `b*`} ++ `%`_byte(0)^(n * (64 * $Ki)){}})
    -- if ((i'!`%`_u64.0 : nat <:> rat) = (((|b*{b <- `b*`}| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) + (n : nat <:> rat)))
    -- (if (i'!`%`_u64.0 <= j!`%`_u64.0))?{j <- `j?`}
    -- if (i'!`%`_u64.0 <= (2 ^ ((($size((at : addrtype <: numtype)) : nat <:> int) - (16 : nat <:> int)) : int <:> nat)))

;; test.spectec:4461.1-4461.60
relation Num_ok: `%|-%:%`(store, num, numtype)
  ;; test.spectec:4466.1-4467.23
  rule _{s : store, nt : numtype, c : num_(nt)}:
    `%|-%:%`(s, CONST_num(nt, c), nt)

;; test.spectec:4462.1-4462.60
relation Vec_ok: `%|-%:%`(store, vec, vectype)
  ;; test.spectec:4469.1-4470.24
  rule _{s : store, vt : vectype, c : vec_(vt)}:
    `%|-%:%`(s, VCONST_vec(vt, c), vt)

;; test.spectec:4463.1-4463.60
rec {

;; test.spectec:4463.1-4463.60
relation Ref_ok: `%|-%:%`(store, ref, reftype)
  ;; test.spectec:4473.1-4474.36
  rule null{s : store}:
    `%|-%:%`(s, `REF.NULL_ADDR`_ref, REF_reftype(?(NULL_null), BOT_heaptype))

  ;; test.spectec:4476.1-4477.31
  rule i31{s : store, i : u31}:
    `%|-%:%`(s, `REF.I31_NUM`_ref(i), REF_reftype(?(), I31_heaptype))

  ;; test.spectec:4479.1-4481.31
  rule struct{s : store, a : addr, dt : deftype}:
    `%|-%:%`(s, `REF.STRUCT_ADDR`_ref(a), REF_reftype(?(), (dt : deftype <: heaptype)))
    -- if (s.STRUCTS_store[a].TYPE_structinst = dt)

  ;; test.spectec:4483.1-4485.30
  rule array{s : store, a : addr, dt : deftype}:
    `%|-%:%`(s, `REF.ARRAY_ADDR`_ref(a), REF_reftype(?(), (dt : deftype <: heaptype)))
    -- if (s.ARRAYS_store[a].TYPE_arrayinst = dt)

  ;; test.spectec:4487.1-4489.29
  rule func{s : store, a : addr, dt : deftype}:
    `%|-%:%`(s, `REF.FUNC_ADDR`_ref(a), REF_reftype(?(), (dt : deftype <: heaptype)))
    -- if (s.FUNCS_store[a].TYPE_funcinst = dt)

  ;; test.spectec:4491.1-4493.24
  rule exn{s : store, a : addr, exn : exninst}:
    `%|-%:%`(s, `REF.EXN_ADDR`_ref(a), REF_reftype(?(), EXN_heaptype))
    -- if (s.EXNS_store[a] = exn)

  ;; test.spectec:4495.1-4496.33
  rule host{s : store, a : addr}:
    `%|-%:%`(s, `REF.HOST_ADDR`_ref(a), REF_reftype(?(), ANY_heaptype))

  ;; test.spectec:4498.1-4501.30
  rule extern{s : store, ref : ref}:
    `%|-%:%`(s, `REF.EXTERN`_ref(ref), REF_reftype(?(), EXTERN_heaptype))
    -- Ref_ok: `%|-%:%`(s, ref, REF_reftype(?(), ANY_heaptype))
    -- if (ref =/= `REF.NULL_ADDR`_ref)

  ;; test.spectec:4503.1-4507.34
  rule sub{s : store, ref : ref, rt : reftype, rt' : reftype}:
    `%|-%:%`(s, ref, rt)
    -- Ref_ok: `%|-%:%`(s, ref, rt')
    -- Reftype_ok: `%|-%:OK`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, rt)
    -- Reftype_sub: `%|-%<:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, rt', rt)
}

;; test.spectec:4464.1-4464.60
relation Val_ok: `%|-%:%`(store, val, valtype)
  ;; test.spectec:4510.1-4512.27
  rule num{s : store, num : num, nt : numtype}:
    `%|-%:%`(s, (num : num <: val), (nt : numtype <: valtype))
    -- Num_ok: `%|-%:%`(s, num, nt)

  ;; test.spectec:4514.1-4516.27
  rule vec{s : store, vec : vec, vt : vectype}:
    `%|-%:%`(s, (vec : vec <: val), (vt : vectype <: valtype))
    -- Vec_ok: `%|-%:%`(s, vec, vt)

  ;; test.spectec:4518.1-4520.27
  rule ref{s : store, ref : ref, rt : reftype}:
    `%|-%:%`(s, (ref : ref <: val), (rt : reftype <: valtype))
    -- Ref_ok: `%|-%:%`(s, ref, rt)

;; test.spectec:4525.1-4525.49
relation Packval_ok: `%|-%:%`(store, packval, packtype)
  ;; test.spectec:4528.1-4529.22
  rule _{s : store, pt : packtype, c : iN($psizenn(pt))}:
    `%|-%:%`(s, PACK_packval(pt, c), pt)

;; test.spectec:4526.1-4526.54
relation Fieldval_ok: `%|-%:%`(store, fieldval, storagetype)
  ;; test.spectec:4531.1-4533.26
  rule val{s : store, val : val, t : valtype}:
    `%|-%:%`(s, (val : val <: fieldval), (t : valtype <: storagetype))
    -- Val_ok: `%|-%:%`(s, val, t)

  ;; test.spectec:4535.1-4537.35
  rule packval{s : store, packval : packval, pt : packtype}:
    `%|-%:%`(s, (packval : packval <: fieldval), (pt : packtype <: storagetype))
    -- Packval_ok: `%|-%:%`(s, packval, pt)

;; test.spectec:4542.1-4542.84
rec {

;; test.spectec:4542.1-4542.84
relation Externaddr_ok: `%|-%:%`(store, externaddr, externtype)
  ;; test.spectec:4544.1-4546.28
  rule tag{s : store, a : addr, taginst : taginst}:
    `%|-%:%`(s, TAG_externaddr(a), TAG_externtype(taginst.TYPE_taginst))
    -- if (s.TAGS_store[a] = taginst)

  ;; test.spectec:4548.1-4550.34
  rule global{s : store, a : addr, globalinst : globalinst}:
    `%|-%:%`(s, GLOBAL_externaddr(a), GLOBAL_externtype(globalinst.TYPE_globalinst))
    -- if (s.GLOBALS_store[a] = globalinst)

  ;; test.spectec:4552.1-4554.28
  rule mem{s : store, a : addr, meminst : meminst}:
    `%|-%:%`(s, MEM_externaddr(a), MEM_externtype(meminst.TYPE_meminst))
    -- if (s.MEMS_store[a] = meminst)

  ;; test.spectec:4556.1-4558.32
  rule table{s : store, a : addr, tableinst : tableinst}:
    `%|-%:%`(s, TABLE_externaddr(a), TABLE_externtype(tableinst.TYPE_tableinst))
    -- if (s.TABLES_store[a] = tableinst)

  ;; test.spectec:4560.1-4562.30
  rule func{s : store, a : addr, funcinst : funcinst}:
    `%|-%:%`(s, FUNC_externaddr(a), FUNC_externtype((funcinst.TYPE_funcinst : deftype <: typeuse)))
    -- if (s.FUNCS_store[a] = funcinst)

  ;; test.spectec:4564.1-4568.37
  rule sub{s : store, externaddr : externaddr, xt : externtype, xt' : externtype}:
    `%|-%:%`(s, externaddr, xt)
    -- Externaddr_ok: `%|-%:%`(s, externaddr, xt')
    -- Externtype_ok: `%|-%:OK`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, xt)
    -- Externtype_sub: `%|-%<:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, xt', xt)
}

;; test.spectec:4581.1-4581.96
def $inst_valtype(moduleinst : moduleinst, valtype : valtype) : valtype
  ;; test.spectec:4587.1-4587.75
  def $inst_valtype{moduleinst : moduleinst, t : valtype}(moduleinst, t) = $subst_all_valtype(t, (moduleinst.TYPES_moduleinst : deftype* <: typeuse*))

;; test.spectec:4582.1-4582.96
def $inst_reftype(moduleinst : moduleinst, reftype : reftype) : reftype
  ;; test.spectec:4588.1-4588.77
  def $inst_reftype{moduleinst : moduleinst, rt : reftype}(moduleinst, rt) = $subst_all_reftype(rt, (moduleinst.TYPES_moduleinst : deftype* <: typeuse*))

;; test.spectec:4583.1-4583.105
def $inst_globaltype(moduleinst : moduleinst, globaltype : globaltype) : globaltype
  ;; test.spectec:4589.1-4589.83
  def $inst_globaltype{moduleinst : moduleinst, gt : globaltype}(moduleinst, gt) = $subst_all_globaltype(gt, (moduleinst.TYPES_moduleinst : deftype* <: typeuse*))

;; test.spectec:4584.1-4584.96
def $inst_memtype(moduleinst : moduleinst, memtype : memtype) : memtype
  ;; test.spectec:4590.1-4590.77
  def $inst_memtype{moduleinst : moduleinst, mt : memtype}(moduleinst, mt) = $subst_all_memtype(mt, (moduleinst.TYPES_moduleinst : deftype* <: typeuse*))

;; test.spectec:4585.1-4585.102
def $inst_tabletype(moduleinst : moduleinst, tabletype : tabletype) : tabletype
  ;; test.spectec:4591.1-4591.81
  def $inst_tabletype{moduleinst : moduleinst, tt : tabletype}(moduleinst, tt) = $subst_all_tabletype(tt, (moduleinst.TYPES_moduleinst : deftype* <: typeuse*))

;; test.spectec:4605.1-4605.88
relation Step_pure: `%~>%`(instr*, instr*)
  ;; test.spectec:4651.1-4652.24
  rule unreachable:
    `%~>%`([UNREACHABLE_instr], [TRAP_instr])

  ;; test.spectec:4654.1-4655.15
  rule nop:
    `%~>%`([NOP_instr], [])

  ;; test.spectec:4657.1-4658.20
  rule drop{val : val}:
    `%~>%`([(val : val <: instr) DROP_instr], [])

  ;; test.spectec:4661.1-4663.16
  rule `select-true`{val_1 : val, val_2 : val, c : num_(I32_numtype), `t*?` : valtype*?}:
    `%~>%`([(val_1 : val <: instr) (val_2 : val <: instr) CONST_instr(I32_numtype, c) SELECT_instr(t*{t <- `t*`}?{`t*` <- `t*?`})], [(val_1 : val <: instr)])
    -- if (c!`%`_num_.0 =/= 0)

  ;; test.spectec:4665.1-4667.14
  rule `select-false`{val_1 : val, val_2 : val, c : num_(I32_numtype), `t*?` : valtype*?}:
    `%~>%`([(val_1 : val <: instr) (val_2 : val <: instr) CONST_instr(I32_numtype, c) SELECT_instr(t*{t <- `t*`}?{`t*` <- `t*?`})], [(val_2 : val <: instr)])
    -- if (c!`%`_num_.0 = 0)

  ;; test.spectec:4684.1-4686.16
  rule `if-true`{c : num_(I32_numtype), bt : blocktype, `instr_1*` : instr*, `instr_2*` : instr*}:
    `%~>%`([CONST_instr(I32_numtype, c) `IF%%ELSE%`_instr(bt, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`})], [BLOCK_instr(bt, instr_1*{instr_1 <- `instr_1*`})])
    -- if (c!`%`_num_.0 =/= 0)

  ;; test.spectec:4688.1-4690.14
  rule `if-false`{c : num_(I32_numtype), bt : blocktype, `instr_1*` : instr*, `instr_2*` : instr*}:
    `%~>%`([CONST_instr(I32_numtype, c) `IF%%ELSE%`_instr(bt, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`})], [BLOCK_instr(bt, instr_2*{instr_2 <- `instr_2*`})])
    -- if (c!`%`_num_.0 = 0)

  ;; test.spectec:4693.1-4694.38
  rule `label-vals`{n : n, `instr*` : instr*, `val*` : val*}:
    `%~>%`([`LABEL_%{%}%`_instr(n, instr*{instr <- `instr*`}, (val : val <: instr)*{val <- `val*`})], (val : val <: instr)*{val <- `val*`})

  ;; test.spectec:4700.1-4702.14
  rule `br-label-zero`{n : n, `instr'*` : instr*, `val'*` : val*, `val*` : val*, l : labelidx, `instr*` : instr*}:
    `%~>%`([`LABEL_%{%}%`_instr(n, instr'*{instr' <- `instr'*`}, (val' : val <: instr)*{val' <- `val'*`} ++ (val : val <: instr)^n{val <- `val*`} ++ [BR_instr(l)] ++ instr*{instr <- `instr*`})], (val : val <: instr)^n{val <- `val*`} ++ instr'*{instr' <- `instr'*`})
    -- if (l!`%`_labelidx.0 = 0)

  ;; test.spectec:4704.1-4706.14
  rule `br-label-succ`{n : n, `instr'*` : instr*, `val*` : val*, l : labelidx, `instr*` : instr*}:
    `%~>%`([`LABEL_%{%}%`_instr(n, instr'*{instr' <- `instr'*`}, (val : val <: instr)*{val <- `val*`} ++ [BR_instr(l)] ++ instr*{instr <- `instr*`})], (val : val <: instr)*{val <- `val*`} ++ [BR_instr(`%`_labelidx((((l!`%`_labelidx.0 : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))])
    -- if (l!`%`_labelidx.0 > 0)

  ;; test.spectec:4708.1-4709.61
  rule `br-handler`{n : n, `catch*` : catch*, `val*` : val*, l : labelidx, `instr*` : instr*}:
    `%~>%`([`HANDLER_%{%}%`_instr(n, catch*{catch <- `catch*`}, (val : val <: instr)*{val <- `val*`} ++ [BR_instr(l)] ++ instr*{instr <- `instr*`})], (val : val <: instr)*{val <- `val*`} ++ [BR_instr(l)])

  ;; test.spectec:4712.1-4714.16
  rule `br_if-true`{c : num_(I32_numtype), l : labelidx}:
    `%~>%`([CONST_instr(I32_numtype, c) BR_IF_instr(l)], [BR_instr(l)])
    -- if (c!`%`_num_.0 =/= 0)

  ;; test.spectec:4716.1-4718.14
  rule `br_if-false`{c : num_(I32_numtype), l : labelidx}:
    `%~>%`([CONST_instr(I32_numtype, c) BR_IF_instr(l)], [])
    -- if (c!`%`_num_.0 = 0)

  ;; test.spectec:4721.1-4723.17
  rule `br_table-lt`{i : num_(I32_numtype), `l*` : labelidx*, l' : labelidx}:
    `%~>%`([CONST_instr(I32_numtype, i) BR_TABLE_instr(l*{l <- `l*`}, l')], [BR_instr(l*{l <- `l*`}[i!`%`_num_.0])])
    -- if (i!`%`_num_.0 < |l*{l <- `l*`}|)

  ;; test.spectec:4725.1-4727.18
  rule `br_table-ge`{i : num_(I32_numtype), `l*` : labelidx*, l' : labelidx}:
    `%~>%`([CONST_instr(I32_numtype, i) BR_TABLE_instr(l*{l <- `l*`}, l')], [BR_instr(l')])
    -- if (i!`%`_num_.0 >= |l*{l <- `l*`}|)

  ;; test.spectec:4730.1-4732.28
  rule `br_on_null-null`{val : val, l : labelidx}:
    `%~>%`([(val : val <: instr) BR_ON_NULL_instr(l)], [BR_instr(l)])
    -- if (val = `REF.NULL_ADDR`_val)

  ;; test.spectec:4734.1-4736.15
  rule `br_on_null-addr`{val : val, l : labelidx}:
    `%~>%`([(val : val <: instr) BR_ON_NULL_instr(l)], [(val : val <: instr)])
    -- otherwise

  ;; test.spectec:4739.1-4741.28
  rule `br_on_non_null-null`{val : val, l : labelidx}:
    `%~>%`([(val : val <: instr) BR_ON_NON_NULL_instr(l)], [])
    -- if (val = `REF.NULL_ADDR`_val)

  ;; test.spectec:4743.1-4745.15
  rule `br_on_non_null-addr`{val : val, l : labelidx}:
    `%~>%`([(val : val <: instr) BR_ON_NON_NULL_instr(l)], [(val : val <: instr) BR_instr(l)])
    -- otherwise

  ;; test.spectec:4804.1-4805.81
  rule call_indirect{x : idx, yy : typeuse}:
    `%~>%`([CALL_INDIRECT_instr(x, yy)], [`TABLE.GET`_instr(x) `REF.CAST`_instr(REF_reftype(?(NULL_null), (yy : typeuse <: heaptype))) CALL_REF_instr(yy)])

  ;; test.spectec:4807.1-4808.95
  rule return_call_indirect{x : idx, yy : typeuse}:
    `%~>%`([RETURN_CALL_INDIRECT_instr(x, yy)], [`TABLE.GET`_instr(x) `REF.CAST`_instr(REF_reftype(?(NULL_null), (yy : typeuse <: heaptype))) RETURN_CALL_REF_instr(yy)])

  ;; test.spectec:4811.1-4812.35
  rule `frame-vals`{n : n, f : frame, `val*` : val*}:
    `%~>%`([`FRAME_%{%}%`_instr(n, f, (val : val <: instr)^n{val <- `val*`})], (val : val <: instr)^n{val <- `val*`})

  ;; test.spectec:4814.1-4815.55
  rule `return-frame`{n : n, f : frame, `val'*` : val*, `val*` : val*, `instr*` : instr*}:
    `%~>%`([`FRAME_%{%}%`_instr(n, f, (val' : val <: instr)*{val' <- `val'*`} ++ (val : val <: instr)^n{val <- `val*`} ++ [RETURN_instr] ++ instr*{instr <- `instr*`})], (val : val <: instr)^n{val <- `val*`})

  ;; test.spectec:4817.1-4818.60
  rule `return-label`{n : n, `instr'*` : instr*, `val*` : val*, `instr*` : instr*}:
    `%~>%`([`LABEL_%{%}%`_instr(n, instr'*{instr' <- `instr'*`}, (val : val <: instr)*{val <- `val*`} ++ [RETURN_instr] ++ instr*{instr <- `instr*`})], (val : val <: instr)*{val <- `val*`} ++ [RETURN_instr])

  ;; test.spectec:4820.1-4821.61
  rule `return-handler`{n : n, `catch*` : catch*, `val*` : val*, `instr*` : instr*}:
    `%~>%`([`HANDLER_%{%}%`_instr(n, catch*{catch <- `catch*`}, (val : val <: instr)*{val <- `val*`} ++ [RETURN_instr] ++ instr*{instr <- `instr*`})], (val : val <: instr)*{val <- `val*`} ++ [RETURN_instr])

  ;; test.spectec:4878.1-4879.40
  rule `handler-vals`{n : n, `catch*` : catch*, `val*` : val*}:
    `%~>%`([`HANDLER_%{%}%`_instr(n, catch*{catch <- `catch*`}, (val : val <: instr)*{val <- `val*`})], (val : val <: instr)*{val <- `val*`})

  ;; test.spectec:4884.1-4886.39
  rule `trap-instrs`{`val*` : val*, `instr*` : instr*}:
    `%~>%`((val : val <: instr)*{val <- `val*`} ++ [TRAP_instr] ++ instr*{instr <- `instr*`}, [TRAP_instr])
    -- if ((val*{val <- `val*`} =/= []) \/ (instr*{instr <- `instr*`} =/= []))

  ;; test.spectec:4888.1-4889.39
  rule `trap-label`{n : n, `instr'*` : instr*}:
    `%~>%`([`LABEL_%{%}%`_instr(n, instr'*{instr' <- `instr'*`}, [TRAP_instr])], [TRAP_instr])

  ;; test.spectec:4891.1-4892.40
  rule `trap-handler`{n : n, `catch*` : catch*}:
    `%~>%`([`HANDLER_%{%}%`_instr(n, catch*{catch <- `catch*`}, [TRAP_instr])], [TRAP_instr])

  ;; test.spectec:4894.1-4895.33
  rule `trap-frame`{n : n, f : frame}:
    `%~>%`([`FRAME_%{%}%`_instr(n, f, [TRAP_instr])], [TRAP_instr])

  ;; test.spectec:4907.1-4908.47
  rule `local.tee`{val : val, x : idx}:
    `%~>%`([(val : val <: instr) `LOCAL.TEE`_instr(x)], [(val : val <: instr) (val : val <: instr) `LOCAL.SET`_instr(x)])

  ;; test.spectec:5226.1-5227.62
  rule `ref.i31`{i : num_(I32_numtype)}:
    `%~>%`([CONST_instr(I32_numtype, i) `REF.I31`_instr], [`REF.I31_NUM`_instr($wrap__(32, 31, i))])

  ;; test.spectec:5230.1-5232.28
  rule `ref.is_null-true`{ref : ref}:
    `%~>%`([(ref : ref <: instr) `REF.IS_NULL`_instr], [CONST_instr(I32_numtype, `%`_num_(1))])
    -- if (ref = `REF.NULL_ADDR`_ref)

  ;; test.spectec:5234.1-5236.15
  rule `ref.is_null-false`{ref : ref}:
    `%~>%`([(ref : ref <: instr) `REF.IS_NULL`_instr], [CONST_instr(I32_numtype, `%`_num_(0))])
    -- otherwise

  ;; test.spectec:5239.1-5241.28
  rule `ref.as_non_null-null`{ref : ref}:
    `%~>%`([(ref : ref <: instr) `REF.AS_NON_NULL`_instr], [TRAP_instr])
    -- if (ref = `REF.NULL_ADDR`_ref)

  ;; test.spectec:5243.1-5245.15
  rule `ref.as_non_null-addr`{ref : ref}:
    `%~>%`([(ref : ref <: instr) `REF.AS_NON_NULL`_instr], [(ref : ref <: instr)])
    -- otherwise

  ;; test.spectec:5248.1-5250.55
  rule `ref.eq-null`{ref_1 : ref, ref_2 : ref}:
    `%~>%`([(ref_1 : ref <: instr) (ref_2 : ref <: instr) `REF.EQ`_instr], [CONST_instr(I32_numtype, `%`_num_(1))])
    -- if ((ref_1 = `REF.NULL_ADDR`_ref) /\ (ref_2 = `REF.NULL_ADDR`_ref))

  ;; test.spectec:5252.1-5255.22
  rule `ref.eq-true`{ref_1 : ref, ref_2 : ref}:
    `%~>%`([(ref_1 : ref <: instr) (ref_2 : ref <: instr) `REF.EQ`_instr], [CONST_instr(I32_numtype, `%`_num_(1))])
    -- otherwise
    -- if (ref_1 = ref_2)

  ;; test.spectec:5257.1-5259.15
  rule `ref.eq-false`{ref_1 : ref, ref_2 : ref}:
    `%~>%`([(ref_1 : ref <: instr) (ref_2 : ref <: instr) `REF.EQ`_instr], [CONST_instr(I32_numtype, `%`_num_(0))])
    -- otherwise

  ;; test.spectec:5282.1-5283.41
  rule `i31.get-null`{sx : sx}:
    `%~>%`([`REF.NULL_ADDR`_instr `I31.GET`_instr(sx)], [TRAP_instr])

  ;; test.spectec:5285.1-5286.73
  rule `i31.get-num`{i : u31, sx : sx}:
    `%~>%`([`REF.I31_NUM`_instr(i) `I31.GET`_instr(sx)], [CONST_instr(I32_numtype, $extend__(31, 32, sx, i))])

  ;; test.spectec:5323.1-5324.67
  rule `array.new`{val : val, n : n, x : idx}:
    `%~>%`([(val : val <: instr) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.NEW`_instr(x)], (val : val <: instr)^n{} ++ [`ARRAY.NEW_FIXED`_instr(x, `%`_u32(n))])

  ;; test.spectec:5521.1-5523.28
  rule `extern.convert_any-null`{ref : ref}:
    `%~>%`([(ref : ref <: instr) `EXTERN.CONVERT_ANY`_instr], [`REF.NULL_ADDR`_instr])
    -- if (ref = `REF.NULL_ADDR`_ref)

  ;; test.spectec:5525.1-5527.15
  rule `extern.convert_any-addr`{ref : ref}:
    `%~>%`([(ref : ref <: instr) `EXTERN.CONVERT_ANY`_instr], [`REF.EXTERN`_instr(ref)])
    -- otherwise

  ;; test.spectec:5530.1-5531.56
  rule `any.convert_extern-null`:
    `%~>%`([`REF.NULL_ADDR`_instr `ANY.CONVERT_EXTERN`_instr], [`REF.NULL_ADDR`_instr])

  ;; test.spectec:5533.1-5534.47
  rule `any.convert_extern-addr`{ref : ref}:
    `%~>%`([`REF.EXTERN`_instr(ref) `ANY.CONVERT_EXTERN`_instr], [(ref : ref <: instr)])

  ;; test.spectec:5539.1-5541.35
  rule `unop-val`{nt : numtype, c_1 : num_(nt), unop : unop_(nt), c : num_(nt)}:
    `%~>%`([CONST_instr(nt, c_1) UNOP_instr(nt, unop)], [CONST_instr(nt, c)])
    -- if (c <- $unop_(nt, unop, c_1))

  ;; test.spectec:5543.1-5545.36
  rule `unop-trap`{nt : numtype, c_1 : num_(nt), unop : unop_(nt)}:
    `%~>%`([CONST_instr(nt, c_1) UNOP_instr(nt, unop)], [TRAP_instr])
    -- if ($unop_(nt, unop, c_1) = [])

  ;; test.spectec:5548.1-5550.42
  rule `binop-val`{nt : numtype, c_1 : num_(nt), c_2 : num_(nt), binop : binop_(nt), c : num_(nt)}:
    `%~>%`([CONST_instr(nt, c_1) CONST_instr(nt, c_2) BINOP_instr(nt, binop)], [CONST_instr(nt, c)])
    -- if (c <- $binop_(nt, binop, c_1, c_2))

  ;; test.spectec:5552.1-5554.43
  rule `binop-trap`{nt : numtype, c_1 : num_(nt), c_2 : num_(nt), binop : binop_(nt)}:
    `%~>%`([CONST_instr(nt, c_1) CONST_instr(nt, c_2) BINOP_instr(nt, binop)], [TRAP_instr])
    -- if ($binop_(nt, binop, c_1, c_2) = [])

  ;; test.spectec:5557.1-5559.38
  rule testop{nt : numtype, c_1 : num_(nt), testop : testop_(nt), c : num_(I32_numtype)}:
    `%~>%`([CONST_instr(nt, c_1) TESTOP_instr(nt, testop)], [CONST_instr(I32_numtype, c)])
    -- if (c = $testop_(nt, testop, c_1))

  ;; test.spectec:5561.1-5563.41
  rule relop{nt : numtype, c_1 : num_(nt), c_2 : num_(nt), relop : relop_(nt), c : num_(I32_numtype)}:
    `%~>%`([CONST_instr(nt, c_1) CONST_instr(nt, c_2) RELOP_instr(nt, relop)], [CONST_instr(I32_numtype, c)])
    -- if (c = $relop_(nt, relop, c_1, c_2))

  ;; test.spectec:5566.1-5568.46
  rule `cvtop-val`{nt_1 : numtype, c_1 : num_(nt_1), nt_2 : numtype, cvtop : cvtop__(nt_1, nt_2), c : num_(nt_2)}:
    `%~>%`([CONST_instr(nt_1, c_1) CVTOP_instr(nt_2, nt_1, cvtop)], [CONST_instr(nt_2, c)])
    -- if (c <- $cvtop__(nt_1, nt_2, cvtop, c_1))

  ;; test.spectec:5570.1-5572.47
  rule `cvtop-trap`{nt_1 : numtype, c_1 : num_(nt_1), nt_2 : numtype, cvtop : cvtop__(nt_1, nt_2)}:
    `%~>%`([CONST_instr(nt_1, c_1) CVTOP_instr(nt_2, nt_1, cvtop)], [TRAP_instr])
    -- if ($cvtop__(nt_1, nt_2, cvtop, c_1) = [])

  ;; test.spectec:5577.1-5579.41
  rule vvunop{c_1 : vec_(V128_Vnn), vvunop : vvunop, c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VVUNOP_instr(V128_vectype, vvunop)], [VCONST_instr(V128_vectype, c)])
    -- if (c <- $vvunop_(V128_vectype, vvunop, c_1))

  ;; test.spectec:5582.1-5584.48
  rule vvbinop{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), vvbinop : vvbinop, c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VCONST_instr(V128_vectype, c_2) VVBINOP_instr(V128_vectype, vvbinop)], [VCONST_instr(V128_vectype, c)])
    -- if (c <- $vvbinop_(V128_vectype, vvbinop, c_1, c_2))

  ;; test.spectec:5587.1-5590.55
  rule vvternop{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), c_3 : vec_(V128_Vnn), vvternop : vvternop, c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VCONST_instr(V128_vectype, c_2) VCONST_instr(V128_vectype, c_3) VVTERNOP_instr(V128_vectype, vvternop)], [VCONST_instr(V128_vectype, c)])
    -- if (c <- $vvternop_(V128_vectype, vvternop, c_1, c_2, c_3))

  ;; test.spectec:5593.1-5595.38
  rule vvtestop{c_1 : vec_(V128_Vnn), c : num_(I32_numtype)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VVTESTOP_instr(V128_vectype, ANY_TRUE_vvtestop)], [CONST_instr(I32_numtype, c)])
    -- if (c = $inez_($vsize(V128_vectype), c_1))

  ;; test.spectec:5598.1-5600.37
  rule `vunop-val`{c_1 : vec_(V128_Vnn), sh : shape, vunop : vunop_(sh), c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VUNOP_instr(sh, vunop)], [VCONST_instr(V128_vectype, c)])
    -- if (c <- $vunop_(sh, vunop, c_1))

  ;; test.spectec:5602.1-5604.38
  rule `vunop-trap`{c_1 : vec_(V128_Vnn), sh : shape, vunop : vunop_(sh)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VUNOP_instr(sh, vunop)], [TRAP_instr])
    -- if ($vunop_(sh, vunop, c_1) = [])

  ;; test.spectec:5607.1-5609.44
  rule `vbinop-val`{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), sh : shape, vbinop : vbinop_(sh), c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VCONST_instr(V128_vectype, c_2) VBINOP_instr(sh, vbinop)], [VCONST_instr(V128_vectype, c)])
    -- if (c <- $vbinop_(sh, vbinop, c_1, c_2))

  ;; test.spectec:5611.1-5613.45
  rule `vbinop-trap`{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), sh : shape, vbinop : vbinop_(sh)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VCONST_instr(V128_vectype, c_2) VBINOP_instr(sh, vbinop)], [TRAP_instr])
    -- if ($vbinop_(sh, vbinop, c_1, c_2) = [])

  ;; test.spectec:5616.1-5618.51
  rule `vternop-val`{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), c_3 : vec_(V128_Vnn), sh : shape, vternop : vternop_(sh), c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VCONST_instr(V128_vectype, c_2) VCONST_instr(V128_vectype, c_3) VTERNOP_instr(sh, vternop)], [VCONST_instr(V128_vectype, c)])
    -- if (c <- $vternop_(sh, vternop, c_1, c_2, c_3))

  ;; test.spectec:5620.1-5622.52
  rule `vternop-trap`{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), c_3 : vec_(V128_Vnn), sh : shape, vternop : vternop_(sh)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VCONST_instr(V128_vectype, c_2) VCONST_instr(V128_vectype, c_3) VTERNOP_instr(sh, vternop)], [TRAP_instr])
    -- if ($vternop_(sh, vternop, c_1, c_2, c_3) = [])

  ;; test.spectec:5625.1-5628.47
  rule vtestop{c_1 : vec_(V128_Vnn), Jnn : Jnn, M : M, c : num_(I32_numtype), `i*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VTESTOP_instr(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), ALL_TRUE_vtestop_)], [CONST_instr(I32_numtype, c)])
    -- if (i*{i <- `i*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c_1))
    -- if (c!`%`_num_.0 = $prod($inez_($jsizenn(Jnn), i)!`%`_u32.0*{i <- `i*`}))

  ;; test.spectec:5631.1-5633.43
  rule vrelop{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), sh : shape, vrelop : vrelop_(sh), c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VCONST_instr(V128_vectype, c_2) VRELOP_instr(sh, vrelop)], [VCONST_instr(V128_vectype, c)])
    -- if (c = $vrelop_(sh, vrelop, c_1, c_2))

  ;; test.spectec:5636.1-5638.45
  rule vshiftop{c_1 : vec_(V128_Vnn), i : num_(I32_numtype), sh : ishape, vshiftop : vshiftop_(sh), c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) CONST_instr(I32_numtype, i) VSHIFTOP_instr(sh, vshiftop)], [VCONST_instr(V128_vectype, c)])
    -- if (c = $vshiftop_(sh, vshiftop, c_1, i))

  ;; test.spectec:5641.1-5643.34
  rule vbitmask{c_1 : vec_(V128_Vnn), sh : ishape, c : num_(I32_numtype)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VBITMASK_instr(sh)], [CONST_instr(I32_numtype, c)])
    -- if (c = $vbitmaskop_(sh, c_1))

  ;; test.spectec:5646.1-5648.48
  rule vswizzlop{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), sh : bshape, swizzlop : vswizzlop_(sh), c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VCONST_instr(V128_vectype, c_2) VSWIZZLOP_instr(sh, swizzlop)], [VCONST_instr(V128_vectype, c)])
    -- if (c = $vswizzlop_(sh, swizzlop, c_1, c_2))

  ;; test.spectec:5651.1-5653.42
  rule vshuffle{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), sh : bshape, `i*` : laneidx*, c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VCONST_instr(V128_vectype, c_2) VSHUFFLE_instr(sh, i*{i <- `i*`})], [VCONST_instr(V128_vectype, c)])
    -- if (c = $vshufflop_(sh, i*{i <- `i*`}, c_1, c_2))

  ;; test.spectec:5656.1-5658.57
  rule vsplat{Lnn : Lnn, c_1 : num_($lunpack(Lnn)), M : M, c : vec_(V128_Vnn)}:
    `%~>%`([CONST_instr($lunpack(Lnn), c_1) VSPLAT_instr(`%X%`_shape(Lnn, `%`_dim(M)))], [VCONST_instr(V128_vectype, c)])
    -- if (c = $inv_lanes_(`%X%`_shape(Lnn, `%`_dim(M)), $lpacknum_(Lnn, c_1)^M{}))

  ;; test.spectec:5661.1-5663.38
  rule `vextract_lane-num`{c_1 : vec_(V128_Vnn), nt : numtype, M : M, i : laneidx, c_2 : num_(nt)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VEXTRACT_LANE_instr(`%X%`_shape((nt : numtype <: lanetype), `%`_dim(M)), ?(), i)], [CONST_instr(nt, c_2)])
    -- if (c_2 = $lanes_(`%X%`_shape((nt : numtype <: lanetype), `%`_dim(M)), c_1)[i!`%`_laneidx.0])

  ;; test.spectec:5665.1-5667.69
  rule `vextract_lane-pack`{c_1 : vec_(V128_Vnn), pt : packtype, M : M, sx : sx, i : laneidx, c_2 : num_(I32_numtype)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VEXTRACT_LANE_instr(`%X%`_shape((pt : packtype <: lanetype), `%`_dim(M)), ?(sx), i)], [CONST_instr(I32_numtype, c_2)])
    -- if (c_2 = $extend__($psize(pt), 32, sx, $lanes_(`%X%`_shape((pt : packtype <: lanetype), `%`_dim(M)), c_1)[i!`%`_laneidx.0]))

  ;; test.spectec:5670.1-5673.84
  rule vreplace_lane{c_1 : vec_(V128_Vnn), Lnn : Lnn, c_2 : num_($lunpack(Lnn)), M : M, i : laneidx, c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) CONST_instr($lunpack(Lnn), c_2) VREPLACE_LANE_instr(`%X%`_shape(Lnn, `%`_dim(M)), i)], [VCONST_instr(V128_vectype, c)])
    -- if (c = $inv_lanes_(`%X%`_shape(Lnn, `%`_dim(M)), $lanes_(`%X%`_shape(Lnn, `%`_dim(M)), c_1)[[i!`%`_laneidx.0] = $lpacknum_(Lnn, c_2)]))

  ;; test.spectec:5676.1-5678.51
  rule vextunop{c_1 : vec_(V128_Vnn), sh_2 : ishape, sh_1 : ishape, vextunop : vextunop__(sh_1, sh_2), c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VEXTUNOP_instr(sh_2, sh_1, vextunop)], [VCONST_instr(V128_vectype, c)])
    -- if ($vextunop__(sh_1, sh_2, vextunop, c_1) = c)

  ;; test.spectec:5681.1-5683.58
  rule vextbinop{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), sh_2 : ishape, sh_1 : ishape, vextbinop : vextbinop__(sh_1, sh_2), c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VCONST_instr(V128_vectype, c_2) VEXTBINOP_instr(sh_2, sh_1, vextbinop)], [VCONST_instr(V128_vectype, c)])
    -- if ($vextbinop__(sh_1, sh_2, vextbinop, c_1, c_2) = c)

  ;; test.spectec:5686.1-5689.65
  rule vextternop{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), c_3 : vec_(V128_Vnn), sh_2 : ishape, sh_1 : ishape, vextternop : vextternop__(sh_1, sh_2), c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VCONST_instr(V128_vectype, c_2) VCONST_instr(V128_vectype, c_3) VEXTTERNOP_instr(sh_2, sh_1, vextternop)], [VCONST_instr(V128_vectype, c)])
    -- if ($vextternop__(sh_1, sh_2, vextternop, c_1, c_2, c_3) = c)

  ;; test.spectec:5692.1-5694.51
  rule vnarrow{c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), sh_2 : ishape, sh_1 : ishape, sx : sx, c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VCONST_instr(V128_vectype, c_2) VNARROW_instr(sh_2, sh_1, sx)], [VCONST_instr(V128_vectype, c)])
    -- if (c = $vnarrowop__(sh_1!`%`_ishape.0, sh_2!`%`_ishape.0, sx, c_1, c_2))

  ;; test.spectec:5697.1-5699.47
  rule vcvtop{c_1 : vec_(V128_Vnn), sh_2 : shape, sh_1 : shape, vcvtop : vcvtop__(sh_1, sh_2), c : vec_(V128_Vnn)}:
    `%~>%`([VCONST_instr(V128_vectype, c_1) VCVTOP_instr(sh_2, sh_1, vcvtop)], [VCONST_instr(V128_vectype, c)])
    -- if (c = $vcvtop__(sh_1, sh_2, vcvtop, c_1))

;; test.spectec:4672.1-4672.71
def $blocktype_(state : state, blocktype : blocktype) : instrtype
  ;; test.spectec:4673.1-4673.87
  def $blocktype_{z : state, x : idx, `t_1*` : valtype*, `t_2*` : valtype*}(z, _IDX_blocktype(x)) = `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`}))
    -- Expand: `%~~%`($type(z, x), `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
  ;; test.spectec:4674.1-4674.43
  def $blocktype_{z : state, `t?` : valtype?}(z, _RESULT_blocktype(t?{t <- `t?`})) = `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype(lift(t?{t <- `t?`})))

;; test.spectec:4606.1-4606.88
relation Step_read: `%~>%`(config, instr*)
  ;; test.spectec:4676.1-4678.44
  rule block{z : state, m : m, `val*` : val*, bt : blocktype, `instr*` : instr*, n : n, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%~>%`(`%;%`_config(z, (val : val <: instr)^m{val <- `val*`} ++ [BLOCK_instr(bt, instr*{instr <- `instr*`})]), [`LABEL_%{%}%`_instr(n, [], (val : val <: instr)^m{val <- `val*`} ++ instr*{instr <- `instr*`})])
    -- if ($blocktype_(z, bt) = `%->_%%`_instrtype(`%`_resulttype(t_1^m{t_1 <- `t_1*`}), [], `%`_resulttype(t_2^n{t_2 <- `t_2*`})))

  ;; test.spectec:4680.1-4682.44
  rule loop{z : state, m : m, `val*` : val*, bt : blocktype, `instr*` : instr*, `t_1*` : valtype*, n : n, `t_2*` : valtype*}:
    `%~>%`(`%;%`_config(z, (val : val <: instr)^m{val <- `val*`} ++ [LOOP_instr(bt, instr*{instr <- `instr*`})]), [`LABEL_%{%}%`_instr(m, [LOOP_instr(bt, instr*{instr <- `instr*`})], (val : val <: instr)^m{val <- `val*`} ++ instr*{instr <- `instr*`})])
    -- if ($blocktype_(z, bt) = `%->_%%`_instrtype(`%`_resulttype(t_1^m{t_1 <- `t_1*`}), [], `%`_resulttype(t_2^n{t_2 <- `t_2*`})))

  ;; test.spectec:4748.1-4750.54
  rule `br_on_cast-succeed`{s : store, f : frame, ref : ref, l : labelidx, rt_1 : reftype, rt_2 : reftype}:
    `%~>%`(`%;%`_config(`%;%`_state(s, f), [(ref : ref <: instr) BR_ON_CAST_instr(l, rt_1, rt_2)]), [(ref : ref <: instr) BR_instr(l)])
    -- Ref_ok: `%|-%:%`(s, ref, $inst_reftype(f.MODULE_frame, rt_2))

  ;; test.spectec:4752.1-4754.15
  rule `br_on_cast-fail`{s : store, f : frame, ref : ref, l : labelidx, rt_1 : reftype, rt_2 : reftype}:
    `%~>%`(`%;%`_config(`%;%`_state(s, f), [(ref : ref <: instr) BR_ON_CAST_instr(l, rt_1, rt_2)]), [(ref : ref <: instr)])
    -- otherwise

  ;; test.spectec:4757.1-4759.54
  rule `br_on_cast_fail-succeed`{s : store, f : frame, ref : ref, l : labelidx, rt_1 : reftype, rt_2 : reftype}:
    `%~>%`(`%;%`_config(`%;%`_state(s, f), [(ref : ref <: instr) BR_ON_CAST_FAIL_instr(l, rt_1, rt_2)]), [(ref : ref <: instr)])
    -- Ref_ok: `%|-%:%`(s, ref, $inst_reftype(f.MODULE_frame, rt_2))

  ;; test.spectec:4761.1-4763.15
  rule `br_on_cast_fail-fail`{s : store, f : frame, ref : ref, l : labelidx, rt_1 : reftype, rt_2 : reftype}:
    `%~>%`(`%;%`_config(`%;%`_state(s, f), [(ref : ref <: instr) BR_ON_CAST_FAIL_instr(l, rt_1, rt_2)]), [(ref : ref <: instr) BR_instr(l)])
    -- otherwise

  ;; test.spectec:4768.1-4770.36
  rule call{z : state, x : idx, a : addr}:
    `%~>%`(`%;%`_config(z, [CALL_instr(x)]), [`REF.FUNC_ADDR`_instr(a) CALL_REF_instr(($funcinst(z)[a].TYPE_funcinst : deftype <: typeuse))])
    -- if ($moduleinst(z).FUNCS_moduleinst[x!`%`_idx.0] = a)

  ;; test.spectec:4772.1-4773.45
  rule `call_ref-null`{z : state, yy : typeuse}:
    `%~>%`(`%;%`_config(z, [`REF.NULL_ADDR`_instr CALL_REF_instr(yy)]), [TRAP_instr])

  ;; test.spectec:4775.1-4781.61
  rule `call_ref-func`{z : state, n : n, `val*` : val*, a : addr, yy : typeuse, m : m, f : frame, `instr*` : instr*, fi : funcinst, `t_1*` : valtype*, `t_2*` : valtype*, x : idx, `t*` : valtype*}:
    `%~>%`(`%;%`_config(z, (val : val <: instr)^n{val <- `val*`} ++ [`REF.FUNC_ADDR`_instr(a) CALL_REF_instr(yy)]), [`FRAME_%{%}%`_instr(m, f, [`LABEL_%{%}%`_instr(m, [], instr*{instr <- `instr*`})])])
    -- if ($funcinst(z)[a] = fi)
    -- Expand: `%~~%`(fi.TYPE_funcinst, `FUNC%->%`_comptype(`%`_resulttype(t_1^n{t_1 <- `t_1*`}), `%`_resulttype(t_2^m{t_2 <- `t_2*`})))
    -- if (fi.CODE_funcinst = FUNC_funccode(x, LOCAL_local(t)*{t <- `t*`}, instr*{instr <- `instr*`}))
    -- if (f = {LOCALS ?(val)^n{val <- `val*`} ++ $default_(t)*{t <- `t*`}, MODULE fi.MODULE_funcinst})

  ;; test.spectec:4784.1-4786.36
  rule return_call{z : state, x : idx, a : addr}:
    `%~>%`(`%;%`_config(z, [RETURN_CALL_instr(x)]), [`REF.FUNC_ADDR`_instr(a) RETURN_CALL_REF_instr(($funcinst(z)[a].TYPE_funcinst : deftype <: typeuse))])
    -- if ($moduleinst(z).FUNCS_moduleinst[x!`%`_idx.0] = a)

  ;; test.spectec:4789.1-4790.91
  rule `return_call_ref-label`{z : state, k : n, `instr'*` : instr*, `val*` : val*, yy : typeuse, `instr*` : instr*}:
    `%~>%`(`%;%`_config(z, [`LABEL_%{%}%`_instr(k, instr'*{instr' <- `instr'*`}, (val : val <: instr)*{val <- `val*`} ++ [RETURN_CALL_REF_instr(yy)] ++ instr*{instr <- `instr*`})]), (val : val <: instr)*{val <- `val*`} ++ [RETURN_CALL_REF_instr(yy)])

  ;; test.spectec:4792.1-4793.92
  rule `return_call_ref-handler`{z : state, k : n, `catch*` : catch*, `val*` : val*, yy : typeuse, `instr*` : instr*}:
    `%~>%`(`%;%`_config(z, [`HANDLER_%{%}%`_instr(k, catch*{catch <- `catch*`}, (val : val <: instr)*{val <- `val*`} ++ [RETURN_CALL_REF_instr(yy)] ++ instr*{instr <- `instr*`})]), (val : val <: instr)*{val <- `val*`} ++ [RETURN_CALL_REF_instr(yy)])

  ;; test.spectec:4795.1-4796.80
  rule `return_call_ref-frame-null`{z : state, k : n, f : frame, `val*` : val*, yy : typeuse, `instr*` : instr*}:
    `%~>%`(`%;%`_config(z, [`FRAME_%{%}%`_instr(k, f, (val : val <: instr)*{val <- `val*`} ++ [`REF.NULL_ADDR`_instr] ++ [RETURN_CALL_REF_instr(yy)] ++ instr*{instr <- `instr*`})]), [TRAP_instr])

  ;; test.spectec:4798.1-4801.57
  rule `return_call_ref-frame-addr`{z : state, k : n, f : frame, `val'*` : val*, n : n, `val*` : val*, a : addr, yy : typeuse, `instr*` : instr*, `t_1*` : valtype*, m : m, `t_2*` : valtype*}:
    `%~>%`(`%;%`_config(z, [`FRAME_%{%}%`_instr(k, f, (val' : val <: instr)*{val' <- `val'*`} ++ (val : val <: instr)^n{val <- `val*`} ++ [`REF.FUNC_ADDR`_instr(a)] ++ [RETURN_CALL_REF_instr(yy)] ++ instr*{instr <- `instr*`})]), (val : val <: instr)^n{val <- `val*`} ++ [`REF.FUNC_ADDR`_instr(a) CALL_REF_instr(yy)])
    -- Expand: `%~~%`($funcinst(z)[a].TYPE_funcinst, `FUNC%->%`_comptype(`%`_resulttype(t_1^n{t_1 <- `t_1*`}), `%`_resulttype(t_2^m{t_2 <- `t_2*`})))

  ;; test.spectec:4832.1-4833.41
  rule `throw_ref-null`{z : state}:
    `%~>%`(`%;%`_config(z, [`REF.NULL_ADDR`_instr THROW_REF_instr]), [TRAP_instr])

  ;; test.spectec:4835.1-4838.39
  rule `throw_ref-instrs`{z : state, `val*` : val*, a : addr, `instr*` : instr*}:
    `%~>%`(`%;%`_config(z, (val : val <: instr)*{val <- `val*`} ++ [`REF.EXN_ADDR`_instr(a)] ++ [THROW_REF_instr] ++ instr*{instr <- `instr*`}), [`REF.EXN_ADDR`_instr(a) THROW_REF_instr])
    -- if ((val*{val <- `val*`} =/= []) \/ (instr*{instr <- `instr*`} =/= []))

  ;; test.spectec:4840.1-4841.86
  rule `throw_ref-label`{z : state, n : n, `instr'*` : instr*, a : addr}:
    `%~>%`(`%;%`_config(z, [`LABEL_%{%}%`_instr(n, instr'*{instr' <- `instr'*`}, [`REF.EXN_ADDR`_instr(a) THROW_REF_instr])]), [`REF.EXN_ADDR`_instr(a) THROW_REF_instr])

  ;; test.spectec:4843.1-4844.80
  rule `throw_ref-frame`{z : state, n : n, f : frame, a : addr}:
    `%~>%`(`%;%`_config(z, [`FRAME_%{%}%`_instr(n, f, [`REF.EXN_ADDR`_instr(a) THROW_REF_instr])]), [`REF.EXN_ADDR`_instr(a) THROW_REF_instr])

  ;; test.spectec:4846.1-4847.84
  rule `throw_ref-handler-empty`{z : state, n : n, a : addr}:
    `%~>%`(`%;%`_config(z, [`HANDLER_%{%}%`_instr(n, [], [`REF.EXN_ADDR`_instr(a) THROW_REF_instr])]), [`REF.EXN_ADDR`_instr(a) THROW_REF_instr])

  ;; test.spectec:4849.1-4853.37
  rule `throw_ref-handler-catch`{z : state, n : n, x : idx, l : labelidx, `catch'*` : catch*, a : addr, `val*` : val*}:
    `%~>%`(`%;%`_config(z, [`HANDLER_%{%}%`_instr(n, [CATCH_catch(x, l)] ++ catch'*{catch' <- `catch'*`}, [`REF.EXN_ADDR`_instr(a) THROW_REF_instr])]), (val : val <: instr)*{val <- `val*`} ++ [BR_instr(l)])
    -- if ($exninst(z)[a].TAG_exninst = $tagaddr(z)[x!`%`_idx.0])
    -- if (val*{val <- `val*`} = $exninst(z)[a].FIELDS_exninst)

  ;; test.spectec:4855.1-4859.37
  rule `throw_ref-handler-catch_ref`{z : state, n : n, x : idx, l : labelidx, `catch'*` : catch*, a : addr, `val*` : val*}:
    `%~>%`(`%;%`_config(z, [`HANDLER_%{%}%`_instr(n, [CATCH_REF_catch(x, l)] ++ catch'*{catch' <- `catch'*`}, [`REF.EXN_ADDR`_instr(a) THROW_REF_instr])]), (val : val <: instr)*{val <- `val*`} ++ [`REF.EXN_ADDR`_instr(a) BR_instr(l)])
    -- if ($exninst(z)[a].TAG_exninst = $tagaddr(z)[x!`%`_idx.0])
    -- if (val*{val <- `val*`} = $exninst(z)[a].FIELDS_exninst)

  ;; test.spectec:4861.1-4862.82
  rule `throw_ref-handler-catch_all`{z : state, n : n, l : labelidx, `catch'*` : catch*, a : addr}:
    `%~>%`(`%;%`_config(z, [`HANDLER_%{%}%`_instr(n, [CATCH_ALL_catch(l)] ++ catch'*{catch' <- `catch'*`}, [`REF.EXN_ADDR`_instr(a) THROW_REF_instr])]), [BR_instr(l)])

  ;; test.spectec:4864.1-4865.103
  rule `throw_ref-handler-catch_all_ref`{z : state, n : n, l : labelidx, `catch'*` : catch*, a : addr}:
    `%~>%`(`%;%`_config(z, [`HANDLER_%{%}%`_instr(n, [CATCH_ALL_REF_catch(l)] ++ catch'*{catch' <- `catch'*`}, [`REF.EXN_ADDR`_instr(a) THROW_REF_instr])]), [`REF.EXN_ADDR`_instr(a) BR_instr(l)])

  ;; test.spectec:4867.1-4870.15
  rule `throw_ref-handler-next`{z : state, n : n, catch : catch, `catch'*` : catch*, a : addr}:
    `%~>%`(`%;%`_config(z, [`HANDLER_%{%}%`_instr(n, [catch] ++ catch'*{catch' <- `catch'*`}, [`REF.EXN_ADDR`_instr(a) THROW_REF_instr])]), [`HANDLER_%{%}%`_instr(n, catch'*{catch' <- `catch'*`}, [`REF.EXN_ADDR`_instr(a) THROW_REF_instr])])
    -- otherwise

  ;; test.spectec:4872.1-4875.44
  rule try_table{z : state, m : m, `val*` : val*, bt : blocktype, `catch*` : catch*, `instr*` : instr*, n : n, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%~>%`(`%;%`_config(z, (val : val <: instr)^m{val <- `val*`} ++ [TRY_TABLE_instr(bt, `%`_list(catch*{catch <- `catch*`}), instr*{instr <- `instr*`})]), [`HANDLER_%{%}%`_instr(n, catch*{catch <- `catch*`}, [`LABEL_%{%}%`_instr(n, [], (val : val <: instr)^m{val <- `val*`} ++ instr*{instr <- `instr*`})])])
    -- if ($blocktype_(z, bt) = `%->_%%`_instrtype(`%`_resulttype(t_1^m{t_1 <- `t_1*`}), [], `%`_resulttype(t_2^n{t_2 <- `t_2*`})))

  ;; test.spectec:4900.1-4902.27
  rule `local.get`{z : state, x : idx, val : val}:
    `%~>%`(`%;%`_config(z, [`LOCAL.GET`_instr(x)]), [(val : val <: instr)])
    -- if ($local(z, x) = ?(val))

  ;; test.spectec:4913.1-4915.34
  rule `global.get`{z : state, x : idx, val : val}:
    `%~>%`(`%;%`_config(z, [`GLOBAL.GET`_instr(x)]), [(val : val <: instr)])
    -- if ($global(z, x).VALUE_globalinst = val)

  ;; test.spectec:4923.1-4925.33
  rule `table.get-oob`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) `TABLE.GET`_instr(x)]), [TRAP_instr])
    -- if (i!`%`_num_.0 >= |$table(z, x).REFS_tableinst|)

  ;; test.spectec:4927.1-4929.32
  rule `table.get-val`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) `TABLE.GET`_instr(x)]), [($table(z, x).REFS_tableinst[i!`%`_num_.0] : ref <: instr)])
    -- if (i!`%`_num_.0 < |$table(z, x).REFS_tableinst|)

  ;; test.spectec:4940.1-4943.38
  rule `table.size`{z : state, x : idx, at : addrtype, n : n, lim : limits, rt : reftype}:
    `%~>%`(`%;%`_config(z, [`TABLE.SIZE`_instr(x)]), [CONST_instr((at : addrtype <: numtype), `%`_num_(n))])
    -- if (|$table(z, x).REFS_tableinst| = n)
    -- if ($table(z, x).TYPE_tableinst = `%%%`_tabletype(at, lim, rt))

  ;; test.spectec:4955.1-4957.39
  rule `table.fill-oob`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), val : val, n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) (val : val <: instr) CONST_instr((at : addrtype <: numtype), `%`_num_(n)) `TABLE.FILL`_instr(x)]), [TRAP_instr])
    -- if ((i!`%`_num_.0 + n) > |$table(z, x).REFS_tableinst|)

  ;; test.spectec:4959.1-4962.14
  rule `table.fill-zero`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), val : val, n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) (val : val <: instr) CONST_instr((at : addrtype <: numtype), `%`_num_(n)) `TABLE.FILL`_instr(x)]), [])
    -- otherwise
    -- if (n = 0)

  ;; test.spectec:4964.1-4968.15
  rule `table.fill-succ`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), val : val, n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) (val : val <: instr) CONST_instr((at : addrtype <: numtype), `%`_num_(n)) `TABLE.FILL`_instr(x)]), [CONST_instr((at : addrtype <: numtype), i) (val : val <: instr) `TABLE.SET`_instr(x) CONST_instr((at : addrtype <: numtype), `%`_num_((i!`%`_num_.0 + 1))) (val : val <: instr) CONST_instr((at : addrtype <: numtype), `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `TABLE.FILL`_instr(x)])
    -- otherwise

  ;; test.spectec:4971.1-4974.81
  rule `table.copy-oob`{z : state, at_1 : addrtype, i_1 : num_((at_1 : addrtype <: numtype)), at_2 : addrtype, i_2 : num_((at_2 : addrtype <: numtype)), at' : addrtype, n : n, x_1 : idx, x_2 : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at_1 : addrtype <: numtype), i_1) CONST_instr((at_2 : addrtype <: numtype), i_2) CONST_instr((at' : addrtype <: numtype), `%`_num_(n)) `TABLE.COPY`_instr(x_1, x_2)]), [TRAP_instr])
    -- if (((i_1!`%`_num_.0 + n) > |$table(z, x_1).REFS_tableinst|) \/ ((i_2!`%`_num_.0 + n) > |$table(z, x_2).REFS_tableinst|))

  ;; test.spectec:4976.1-4979.14
  rule `table.copy-zero`{z : state, at_1 : addrtype, i_1 : num_((at_1 : addrtype <: numtype)), at_2 : addrtype, i_2 : num_((at_2 : addrtype <: numtype)), at' : addrtype, n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at_1 : addrtype <: numtype), i_1) CONST_instr((at_2 : addrtype <: numtype), i_2) CONST_instr((at' : addrtype <: numtype), `%`_num_(n)) `TABLE.COPY`_instr(x, y)]), [])
    -- otherwise
    -- if (n = 0)

  ;; test.spectec:4981.1-4986.19
  rule `table.copy-le`{z : state, at_1 : addrtype, i_1 : num_((at_1 : addrtype <: numtype)), at_2 : addrtype, i_2 : num_((at_2 : addrtype <: numtype)), at' : addrtype, n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at_1 : addrtype <: numtype), i_1) CONST_instr((at_2 : addrtype <: numtype), i_2) CONST_instr((at' : addrtype <: numtype), `%`_num_(n)) `TABLE.COPY`_instr(x, y)]), [CONST_instr((at_1 : addrtype <: numtype), i_1) CONST_instr((at_2 : addrtype <: numtype), i_2) `TABLE.GET`_instr(y) `TABLE.SET`_instr(x) CONST_instr((at_1 : addrtype <: numtype), `%`_num_((i_1!`%`_num_.0 + 1))) CONST_instr((at_2 : addrtype <: numtype), `%`_num_((i_2!`%`_num_.0 + 1))) CONST_instr((at' : addrtype <: numtype), `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `TABLE.COPY`_instr(x, y)])
    -- otherwise
    -- if (i_1!`%`_num_.0 <= i_2!`%`_num_.0)

  ;; test.spectec:4988.1-4992.15
  rule `table.copy-gt`{z : state, at_1 : addrtype, i_1 : num_((at_1 : addrtype <: numtype)), at_2 : addrtype, i_2 : num_((at_2 : addrtype <: numtype)), at' : addrtype, n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at_1 : addrtype <: numtype), i_1) CONST_instr((at_2 : addrtype <: numtype), i_2) CONST_instr((at' : addrtype <: numtype), `%`_num_(n)) `TABLE.COPY`_instr(x, y)]), [CONST_instr((at_1 : addrtype <: numtype), `%`_num_(((((i_1!`%`_num_.0 + n) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) CONST_instr((at_2 : addrtype <: numtype), `%`_num_(((((i_2!`%`_num_.0 + n) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `TABLE.GET`_instr(y) `TABLE.SET`_instr(x) CONST_instr((at_1 : addrtype <: numtype), i_1) CONST_instr((at_2 : addrtype <: numtype), i_2) CONST_instr((at' : addrtype <: numtype), `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `TABLE.COPY`_instr(x, y)])
    -- otherwise

  ;; test.spectec:4995.1-4998.72
  rule `table.init-oob`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), j : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) CONST_instr(I32_numtype, j) CONST_instr(I32_numtype, `%`_num_(n)) `TABLE.INIT`_instr(x, y)]), [TRAP_instr])
    -- if (((i!`%`_num_.0 + n) > |$table(z, x).REFS_tableinst|) \/ ((j!`%`_num_.0 + n) > |$elem(z, y).REFS_eleminst|))

  ;; test.spectec:5000.1-5003.14
  rule `table.init-zero`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), j : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) CONST_instr(I32_numtype, j) CONST_instr(I32_numtype, `%`_num_(n)) `TABLE.INIT`_instr(x, y)]), [])
    -- otherwise
    -- if (n = 0)

  ;; test.spectec:5005.1-5009.15
  rule `table.init-succ`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), j : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) CONST_instr(I32_numtype, j) CONST_instr(I32_numtype, `%`_num_(n)) `TABLE.INIT`_instr(x, y)]), [CONST_instr((at : addrtype <: numtype), i) ($elem(z, y).REFS_eleminst[j!`%`_num_.0] : ref <: instr) `TABLE.SET`_instr(x) CONST_instr((at : addrtype <: numtype), `%`_num_((i!`%`_num_.0 + 1))) CONST_instr(I32_numtype, `%`_num_((j!`%`_num_.0 + 1))) CONST_instr(I32_numtype, `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `TABLE.INIT`_instr(x, y)])
    -- otherwise

  ;; test.spectec:5018.1-5021.60
  rule `load-num-oob`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), nt : numtype, x : idx, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) LOAD_instr(nt, ?(), x, ao)]), [TRAP_instr])
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) + ((($size(nt) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, x).BYTES_meminst|)

  ;; test.spectec:5023.1-5026.72
  rule `load-num-val`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), nt : numtype, x : idx, ao : memarg, c : num_(nt)}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) LOAD_instr(nt, ?(), x, ao)]), [CONST_instr(nt, c)])
    -- if ($nbytes_(nt, c) = $mem(z, x).BYTES_meminst[(i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) : ((($size(nt) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])

  ;; test.spectec:5028.1-5031.52
  rule `load-pack-oob`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), Inn : Inn, n : n, sx : sx, x : idx, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) LOAD_instr((Inn : addrtype <: numtype), ?(`%_%`_loadop_(`%`_sz(n), sx)), x, ao)]), [TRAP_instr])
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) + (((n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, x).BYTES_meminst|)

  ;; test.spectec:5033.1-5036.63
  rule `load-pack-val`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), Inn : Inn, n : n, sx : sx, x : idx, ao : memarg, c : iN(n)}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) LOAD_instr((Inn : addrtype <: numtype), ?(`%_%`_loadop_(`%`_sz(n), sx)), x, ao)]), [CONST_instr((Inn : addrtype <: numtype), $extend__(n, $size((Inn : addrtype <: numtype)), sx, c))])
    -- if ($ibytes_(n, c) = $mem(z, x).BYTES_meminst[(i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) : (((n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])

  ;; test.spectec:5038.1-5040.63
  rule `vload-oob`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), x : idx, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) VLOAD_instr(V128_vectype, ?(), x, ao)]), [TRAP_instr])
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) + ((($vsize(V128_vectype) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, x).BYTES_meminst|)

  ;; test.spectec:5042.1-5044.77
  rule `vload-val`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), x : idx, ao : memarg, c : vec_(V128_Vnn)}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) VLOAD_instr(V128_vectype, ?(), x, ao)]), [VCONST_instr(V128_vectype, c)])
    -- if ($vbytes_(V128_vectype, c) = $mem(z, x).BYTES_meminst[(i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) : ((($vsize(V128_vectype) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])

  ;; test.spectec:5047.1-5049.56
  rule `vload-pack-oob`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), M : M, K : K, sx : sx, x : idx, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(M), K, sx)), x, ao)]), [TRAP_instr])
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) + ((((M * K) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, x).BYTES_meminst|)

  ;; test.spectec:5051.1-5056.33
  rule `vload-pack-val`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), M : M, K : K, sx : sx, x : idx, ao : memarg, c : vec_(V128_Vnn), `j*` : iN(M)*, Jnn : Jnn}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(M), K, sx)), x, ao)]), [VCONST_instr(V128_vectype, c)])
    -- (if ($ibytes_(M, j) = $mem(z, x).BYTES_meminst[((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) + ((((k * M) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) : (((M : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)]))^(k<K){j <- `j*`}
    -- if ((c = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(K)), $extend__(M, $jsizenn(Jnn), sx, j)^K{j <- `j*`})) /\ ($jsizenn(Jnn) = (M * 2)))

  ;; test.spectec:5059.1-5061.52
  rule `vload-splat-oob`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), N : N, x : idx, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(N))), x, ao)]), [TRAP_instr])
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) + (((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, x).BYTES_meminst|)

  ;; test.spectec:5063.1-5069.38
  rule `vload-splat-val`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), N : N, x : idx, ao : memarg, c : vec_(V128_Vnn), j : iN(N), Jnn : Jnn, M : M}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(N))), x, ao)]), [VCONST_instr(V128_vectype, c)])
    -- if ($ibytes_(N, j) = $mem(z, x).BYTES_meminst[(i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) : (((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])
    -- if (N = $jsize(Jnn))
    -- if ((M : nat <:> rat) = ((128 : nat <:> rat) / (N : nat <:> rat)))
    -- if (c = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), `%`_lane_(j!`%`_iN.0)^M{}))

  ;; test.spectec:5072.1-5074.52
  rule `vload-zero-oob`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), N : N, x : idx, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) VLOAD_instr(V128_vectype, ?(ZERO_vloadop_(`%`_sz(N))), x, ao)]), [TRAP_instr])
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) + (((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, x).BYTES_meminst|)

  ;; test.spectec:5076.1-5080.36
  rule `vload-zero-val`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), N : N, x : idx, ao : memarg, c : vec_(V128_Vnn), j : iN(N)}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) VLOAD_instr(V128_vectype, ?(ZERO_vloadop_(`%`_sz(N))), x, ao)]), [VCONST_instr(V128_vectype, c)])
    -- if ($ibytes_(N, j) = $mem(z, x).BYTES_meminst[(i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) : (((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])
    -- if (c = $extend__(N, 128, U_sx, j))

  ;; test.spectec:5083.1-5085.52
  rule `vload_lane-oob`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), c_1 : vec_(V128_Vnn), N : N, x : idx, ao : memarg, j : laneidx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) VCONST_instr(V128_vectype, c_1) VLOAD_LANE_instr(V128_vectype, `%`_sz(N), x, ao, j)]), [TRAP_instr])
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) + (((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, x).BYTES_meminst|)

  ;; test.spectec:5087.1-5093.65
  rule `vload_lane-val`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), c_1 : vec_(V128_Vnn), N : N, x : idx, ao : memarg, j : laneidx, c : vec_(V128_Vnn), k : iN(N), Jnn : Jnn, M : M}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) VCONST_instr(V128_vectype, c_1) VLOAD_LANE_instr(V128_vectype, `%`_sz(N), x, ao, j)]), [VCONST_instr(V128_vectype, c)])
    -- if ($ibytes_(N, k) = $mem(z, x).BYTES_meminst[(i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) : (((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])
    -- if (N = $jsize(Jnn))
    -- if ((M : nat <:> rat) = (($vsize(V128_vectype) : nat <:> rat) / (N : nat <:> rat)))
    -- if (c = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c_1)[[j!`%`_laneidx.0] = `%`_lane_(k!`%`_iN.0)]))

  ;; test.spectec:5142.1-5145.38
  rule `memory.size`{z : state, x : idx, at : addrtype, n : n, lim : limits}:
    `%~>%`(`%;%`_config(z, [`MEMORY.SIZE`_instr(x)]), [CONST_instr((at : addrtype <: numtype), `%`_num_(n))])
    -- if ((n * (64 * $Ki)) = |$mem(z, x).BYTES_meminst|)
    -- if ($mem(z, x).TYPE_meminst = `%%PAGE`_memtype(at, lim))

  ;; test.spectec:5157.1-5159.38
  rule `memory.fill-oob`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), val : val, n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) (val : val <: instr) CONST_instr((at : addrtype <: numtype), `%`_num_(n)) `MEMORY.FILL`_instr(x)]), [TRAP_instr])
    -- if ((i!`%`_num_.0 + n) > |$mem(z, x).BYTES_meminst|)

  ;; test.spectec:5161.1-5164.14
  rule `memory.fill-zero`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), val : val, n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) (val : val <: instr) CONST_instr((at : addrtype <: numtype), `%`_num_(n)) `MEMORY.FILL`_instr(x)]), [])
    -- otherwise
    -- if (n = 0)

  ;; test.spectec:5166.1-5170.15
  rule `memory.fill-succ`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), val : val, n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) (val : val <: instr) CONST_instr((at : addrtype <: numtype), `%`_num_(n)) `MEMORY.FILL`_instr(x)]), [CONST_instr((at : addrtype <: numtype), i) (val : val <: instr) STORE_instr(I32_numtype, ?(`%`_storeop_(`%`_sz(8))), x, $memarg0) CONST_instr((at : addrtype <: numtype), `%`_num_((i!`%`_num_.0 + 1))) (val : val <: instr) CONST_instr((at : addrtype <: numtype), `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `MEMORY.FILL`_instr(x)])
    -- otherwise

  ;; test.spectec:5173.1-5176.79
  rule `memory.copy-oob`{z : state, at_1 : addrtype, i_1 : num_((at_1 : addrtype <: numtype)), at_2 : addrtype, i_2 : num_((at_2 : addrtype <: numtype)), at' : addrtype, n : n, x_1 : idx, x_2 : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at_1 : addrtype <: numtype), i_1) CONST_instr((at_2 : addrtype <: numtype), i_2) CONST_instr((at' : addrtype <: numtype), `%`_num_(n)) `MEMORY.COPY`_instr(x_1, x_2)]), [TRAP_instr])
    -- if (((i_1!`%`_num_.0 + n) > |$mem(z, x_1).BYTES_meminst|) \/ ((i_2!`%`_num_.0 + n) > |$mem(z, x_2).BYTES_meminst|))

  ;; test.spectec:5178.1-5181.14
  rule `memory.copy-zero`{z : state, at_1 : addrtype, i_1 : num_((at_1 : addrtype <: numtype)), at_2 : addrtype, i_2 : num_((at_2 : addrtype <: numtype)), at' : addrtype, n : n, x_1 : idx, x_2 : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at_1 : addrtype <: numtype), i_1) CONST_instr((at_2 : addrtype <: numtype), i_2) CONST_instr((at' : addrtype <: numtype), `%`_num_(n)) `MEMORY.COPY`_instr(x_1, x_2)]), [])
    -- otherwise
    -- if (n = 0)

  ;; test.spectec:5183.1-5188.19
  rule `memory.copy-le`{z : state, at_1 : addrtype, i_1 : num_((at_1 : addrtype <: numtype)), at_2 : addrtype, i_2 : num_((at_2 : addrtype <: numtype)), at' : addrtype, n : n, x_1 : idx, x_2 : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at_1 : addrtype <: numtype), i_1) CONST_instr((at_2 : addrtype <: numtype), i_2) CONST_instr((at' : addrtype <: numtype), `%`_num_(n)) `MEMORY.COPY`_instr(x_1, x_2)]), [CONST_instr((at_1 : addrtype <: numtype), i_1) CONST_instr((at_2 : addrtype <: numtype), i_2) LOAD_instr(I32_numtype, ?(`%_%`_loadop_(`%`_sz(8), U_sx)), x_2, $memarg0) STORE_instr(I32_numtype, ?(`%`_storeop_(`%`_sz(8))), x_1, $memarg0) CONST_instr((at_1 : addrtype <: numtype), `%`_num_((i_1!`%`_num_.0 + 1))) CONST_instr((at_2 : addrtype <: numtype), `%`_num_((i_2!`%`_num_.0 + 1))) CONST_instr((at' : addrtype <: numtype), `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `MEMORY.COPY`_instr(x_1, x_2)])
    -- otherwise
    -- if (i_1!`%`_num_.0 <= i_2!`%`_num_.0)

  ;; test.spectec:5190.1-5194.15
  rule `memory.copy-gt`{z : state, at_1 : addrtype, i_1 : num_((at_1 : addrtype <: numtype)), at_2 : addrtype, i_2 : num_((at_2 : addrtype <: numtype)), at' : addrtype, n : n, x_1 : idx, x_2 : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at_1 : addrtype <: numtype), i_1) CONST_instr((at_2 : addrtype <: numtype), i_2) CONST_instr((at' : addrtype <: numtype), `%`_num_(n)) `MEMORY.COPY`_instr(x_1, x_2)]), [CONST_instr((at_1 : addrtype <: numtype), `%`_num_(((((i_1!`%`_num_.0 + n) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) CONST_instr((at_2 : addrtype <: numtype), `%`_num_(((((i_2!`%`_num_.0 + n) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) LOAD_instr(I32_numtype, ?(`%_%`_loadop_(`%`_sz(8), U_sx)), x_2, $memarg0) STORE_instr(I32_numtype, ?(`%`_storeop_(`%`_sz(8))), x_1, $memarg0) CONST_instr((at_1 : addrtype <: numtype), i_1) CONST_instr((at_2 : addrtype <: numtype), i_2) CONST_instr((at' : addrtype <: numtype), `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `MEMORY.COPY`_instr(x_1, x_2)])
    -- otherwise

  ;; test.spectec:5197.1-5200.72
  rule `memory.init-oob`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), j : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) CONST_instr(I32_numtype, j) CONST_instr(I32_numtype, `%`_num_(n)) `MEMORY.INIT`_instr(x, y)]), [TRAP_instr])
    -- if (((i!`%`_num_.0 + n) > |$mem(z, x).BYTES_meminst|) \/ ((j!`%`_num_.0 + n) > |$data(z, y).BYTES_datainst|))

  ;; test.spectec:5202.1-5205.14
  rule `memory.init-zero`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), j : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) CONST_instr(I32_numtype, j) CONST_instr(I32_numtype, `%`_num_(n)) `MEMORY.INIT`_instr(x, y)]), [])
    -- otherwise
    -- if (n = 0)

  ;; test.spectec:5207.1-5211.15
  rule `memory.init-succ`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), j : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) CONST_instr(I32_numtype, j) CONST_instr(I32_numtype, `%`_num_(n)) `MEMORY.INIT`_instr(x, y)]), [CONST_instr((at : addrtype <: numtype), i) CONST_instr(I32_numtype, `%`_num_($data(z, y).BYTES_datainst[j!`%`_num_.0]!`%`_byte.0)) STORE_instr(I32_numtype, ?(`%`_storeop_(`%`_sz(8))), x, $memarg0) CONST_instr((at : addrtype <: numtype), `%`_num_((i!`%`_num_.0 + 1))) CONST_instr(I32_numtype, `%`_num_((j!`%`_num_.0 + 1))) CONST_instr(I32_numtype, `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `MEMORY.INIT`_instr(x, y)])
    -- otherwise

  ;; test.spectec:5220.1-5221.38
  rule `ref.null`{z : state, ht : heaptype}:
    `%~>%`(`%;%`_config(z, [`REF.NULL`_instr(ht)]), [`REF.NULL_ADDR`_instr])

  ;; test.spectec:5223.1-5224.63
  rule `ref.func`{z : state, x : idx}:
    `%~>%`(`%;%`_config(z, [`REF.FUNC`_instr(x)]), [`REF.FUNC_ADDR`_instr($moduleinst(z).FUNCS_moduleinst[x!`%`_idx.0])])

  ;; test.spectec:5262.1-5264.52
  rule `ref.test-true`{s : store, f : frame, ref : ref, rt : reftype}:
    `%~>%`(`%;%`_config(`%;%`_state(s, f), [(ref : ref <: instr) `REF.TEST`_instr(rt)]), [CONST_instr(I32_numtype, `%`_num_(1))])
    -- Ref_ok: `%|-%:%`(s, ref, $inst_reftype(f.MODULE_frame, rt))

  ;; test.spectec:5266.1-5268.15
  rule `ref.test-false`{s : store, f : frame, ref : ref, rt : reftype}:
    `%~>%`(`%;%`_config(`%;%`_state(s, f), [(ref : ref <: instr) `REF.TEST`_instr(rt)]), [CONST_instr(I32_numtype, `%`_num_(0))])
    -- otherwise

  ;; test.spectec:5271.1-5273.52
  rule `ref.cast-succeed`{s : store, f : frame, ref : ref, rt : reftype}:
    `%~>%`(`%;%`_config(`%;%`_state(s, f), [(ref : ref <: instr) `REF.CAST`_instr(rt)]), [(ref : ref <: instr)])
    -- Ref_ok: `%|-%:%`(s, ref, $inst_reftype(f.MODULE_frame, rt))

  ;; test.spectec:5275.1-5277.15
  rule `ref.cast-fail`{s : store, f : frame, ref : ref, rt : reftype}:
    `%~>%`(`%;%`_config(`%;%`_state(s, f), [(ref : ref <: instr) `REF.CAST`_instr(rt)]), [TRAP_instr])
    -- otherwise

  ;; test.spectec:5297.1-5300.40
  rule `struct.new_default`{z : state, x : idx, `val*` : val*, `mut?*` : mut?*, `zt*` : storagetype*}:
    `%~>%`(`%;%`_config(z, [`STRUCT.NEW_DEFAULT`_instr(x)]), (val : val <: instr)*{val <- `val*`} ++ [`STRUCT.NEW`_instr(x)])
    -- Expand: `%~~%`($type(z, x), STRUCT_comptype(`%`_list(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)*{`mut?` <- `mut?*`, zt <- `zt*`})))
    -- (if ($default_($unpack(zt)) = ?(val)))*{val <- `val*`, zt <- `zt*`}

  ;; test.spectec:5303.1-5304.52
  rule `struct.get-null`{z : state, `sx?` : sx?, x : idx, i : fieldidx}:
    `%~>%`(`%;%`_config(z, [`REF.NULL_ADDR`_instr `STRUCT.GET`_instr(sx?{sx <- `sx?`}, x, i)]), [TRAP_instr])

  ;; test.spectec:5306.1-5309.46
  rule `struct.get-struct`{z : state, a : addr, `sx?` : sx?, x : idx, i : fieldidx, `zt*` : storagetype*, `mut?*` : mut?*}:
    `%~>%`(`%;%`_config(z, [`REF.STRUCT_ADDR`_instr(a) `STRUCT.GET`_instr(sx?{sx <- `sx?`}, x, i)]), [($unpackfield_(zt*{zt <- `zt*`}[i!`%`_fieldidx.0], sx?{sx <- `sx?`}, $structinst(z)[a].FIELDS_structinst[i!`%`_fieldidx.0]) : val <: instr)])
    -- Expand: `%~~%`($type(z, x), STRUCT_comptype(`%`_list(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)*{`mut?` <- `mut?*`, zt <- `zt*`})))

  ;; test.spectec:5326.1-5329.37
  rule `array.new_default`{z : state, n : n, x : idx, val : val, `mut?` : mut?, zt : storagetype}:
    `%~>%`(`%;%`_config(z, [CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.NEW_DEFAULT`_instr(x)]), (val : val <: instr)^n{} ++ [`ARRAY.NEW_FIXED`_instr(x, `%`_u32(n))])
    -- Expand: `%~~%`($type(z, x), ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- if ($default_($unpack(zt)) = ?(val))

  ;; test.spectec:5339.1-5341.38
  rule `array.new_elem-oob`{z : state, i : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr(I32_numtype, i) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.NEW_ELEM`_instr(x, y)]), [TRAP_instr])
    -- if ((i!`%`_num_.0 + n) > |$elem(z, y).REFS_eleminst|)

  ;; test.spectec:5343.1-5346.40
  rule `array.new_elem-alloc`{z : state, i : num_(I32_numtype), n : n, x : idx, y : idx, `ref*` : ref*}:
    `%~>%`(`%;%`_config(z, [CONST_instr(I32_numtype, i) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.NEW_ELEM`_instr(x, y)]), (ref : ref <: instr)^n{ref <- `ref*`} ++ [`ARRAY.NEW_FIXED`_instr(x, `%`_u32(n))])
    -- if (ref^n{ref <- `ref*`} = $elem(z, y).REFS_eleminst[i!`%`_num_.0 : n])

  ;; test.spectec:5349.1-5353.54
  rule `array.new_data-oob`{z : state, i : num_(I32_numtype), n : n, x : idx, y : idx, `mut?` : mut?, zt : storagetype}:
    `%~>%`(`%;%`_config(z, [CONST_instr(I32_numtype, i) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.NEW_DATA`_instr(x, y)]), [TRAP_instr])
    -- Expand: `%~~%`($type(z, x), ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- if ((i!`%`_num_.0 + ((((n * $zsize(zt)) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$data(z, y).BYTES_datainst|)

  ;; test.spectec:5356.1-5360.102
  rule `array.new_data-num`{z : state, i : num_(I32_numtype), n : n, x : idx, y : idx, zt : storagetype, `c*` : lit_(zt)*, `mut?` : mut?}:
    `%~>%`(`%;%`_config(z, [CONST_instr(I32_numtype, i) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.NEW_DATA`_instr(x, y)]), $const($cunpack(zt), $cunpacknum_(zt, c))^n{c <- `c*`} ++ [`ARRAY.NEW_FIXED`_instr(x, `%`_u32(n))])
    -- Expand: `%~~%`($type(z, x), ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- if ($concatn_(syntax byte, $zbytes_(zt, c)^n{c <- `c*`}, ((($zsize(zt) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) = $data(z, y).BYTES_datainst[i!`%`_num_.0 : ((((n * $zsize(zt)) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])

  ;; test.spectec:5363.1-5364.63
  rule `array.get-null`{z : state, i : num_(I32_numtype), `sx?` : sx?, x : idx}:
    `%~>%`(`%;%`_config(z, [`REF.NULL_ADDR`_instr CONST_instr(I32_numtype, i) `ARRAY.GET`_instr(sx?{sx <- `sx?`}, x)]), [TRAP_instr])

  ;; test.spectec:5366.1-5368.39
  rule `array.get-oob`{z : state, a : addr, i : num_(I32_numtype), `sx?` : sx?, x : idx}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) `ARRAY.GET`_instr(sx?{sx <- `sx?`}, x)]), [TRAP_instr])
    -- if (i!`%`_num_.0 >= |$arrayinst(z)[a].FIELDS_arrayinst|)

  ;; test.spectec:5370.1-5373.44
  rule `array.get-array`{z : state, a : addr, i : num_(I32_numtype), `sx?` : sx?, x : idx, zt : storagetype, `mut?` : mut?}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) `ARRAY.GET`_instr(sx?{sx <- `sx?`}, x)]), [($unpackfield_(zt, sx?{sx <- `sx?`}, $arrayinst(z)[a].FIELDS_arrayinst[i!`%`_num_.0]) : val <: instr)])
    -- Expand: `%~~%`($type(z, x), ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))

  ;; test.spectec:5389.1-5390.41
  rule `array.len-null`{z : state}:
    `%~>%`(`%;%`_config(z, [`REF.NULL_ADDR`_instr `ARRAY.LEN`_instr]), [TRAP_instr])

  ;; test.spectec:5392.1-5393.80
  rule `array.len-array`{z : state, a : addr}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a) `ARRAY.LEN`_instr]), [CONST_instr(I32_numtype, `%`_num_(|$arrayinst(z)[a].FIELDS_arrayinst|))])

  ;; test.spectec:5396.1-5397.78
  rule `array.fill-null`{z : state, i : num_(I32_numtype), val : val, n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [`REF.NULL_ADDR`_instr CONST_instr(I32_numtype, i) (val : val <: instr) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.FILL`_instr(x)]), [TRAP_instr])

  ;; test.spectec:5399.1-5401.45
  rule `array.fill-oob`{z : state, a : addr, i : num_(I32_numtype), val : val, n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) (val : val <: instr) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.FILL`_instr(x)]), [TRAP_instr])
    -- if ((i!`%`_num_.0 + n) > |$arrayinst(z)[a].FIELDS_arrayinst|)

  ;; test.spectec:5403.1-5406.14
  rule `array.fill-zero`{z : state, a : addr, i : num_(I32_numtype), val : val, n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) (val : val <: instr) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.FILL`_instr(x)]), [])
    -- otherwise
    -- if (n = 0)

  ;; test.spectec:5408.1-5412.15
  rule `array.fill-succ`{z : state, a : addr, i : num_(I32_numtype), val : val, n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) (val : val <: instr) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.FILL`_instr(x)]), [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) (val : val <: instr) `ARRAY.SET`_instr(x) `REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, `%`_num_((i!`%`_num_.0 + 1))) (val : val <: instr) CONST_instr(I32_numtype, `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `ARRAY.FILL`_instr(x)])
    -- otherwise

  ;; test.spectec:5414.1-5415.102
  rule `array.copy-null1`{z : state, i_1 : num_(I32_numtype), ref : ref, i_2 : num_(I32_numtype), n : n, x_1 : idx, x_2 : idx}:
    `%~>%`(`%;%`_config(z, [`REF.NULL_ADDR`_instr CONST_instr(I32_numtype, i_1) (ref : ref <: instr) CONST_instr(I32_numtype, i_2) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.COPY`_instr(x_1, x_2)]), [TRAP_instr])

  ;; test.spectec:5417.1-5418.102
  rule `array.copy-null2`{z : state, ref : ref, i_1 : num_(I32_numtype), i_2 : num_(I32_numtype), n : n, x_1 : idx, x_2 : idx}:
    `%~>%`(`%;%`_config(z, [(ref : ref <: instr) CONST_instr(I32_numtype, i_1) `REF.NULL_ADDR`_instr CONST_instr(I32_numtype, i_2) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.COPY`_instr(x_1, x_2)]), [TRAP_instr])

  ;; test.spectec:5420.1-5423.49
  rule `array.copy-oob1`{z : state, a_1 : addr, i_1 : num_(I32_numtype), a_2 : addr, i_2 : num_(I32_numtype), n : n, x_1 : idx, x_2 : idx}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a_1) CONST_instr(I32_numtype, i_1) `REF.ARRAY_ADDR`_instr(a_2) CONST_instr(I32_numtype, i_2) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.COPY`_instr(x_1, x_2)]), [TRAP_instr])
    -- if ((i_1!`%`_num_.0 + n) > |$arrayinst(z)[a_1].FIELDS_arrayinst|)

  ;; test.spectec:5425.1-5428.49
  rule `array.copy-oob2`{z : state, a_1 : addr, i_1 : num_(I32_numtype), a_2 : addr, i_2 : num_(I32_numtype), n : n, x_1 : idx, x_2 : idx}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a_1) CONST_instr(I32_numtype, i_1) `REF.ARRAY_ADDR`_instr(a_2) CONST_instr(I32_numtype, i_2) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.COPY`_instr(x_1, x_2)]), [TRAP_instr])
    -- if ((i_2!`%`_num_.0 + n) > |$arrayinst(z)[a_2].FIELDS_arrayinst|)

  ;; test.spectec:5430.1-5434.14
  rule `array.copy-zero`{z : state, a_1 : addr, i_1 : num_(I32_numtype), a_2 : addr, i_2 : num_(I32_numtype), n : n, x_1 : idx, x_2 : idx}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a_1) CONST_instr(I32_numtype, i_1) `REF.ARRAY_ADDR`_instr(a_2) CONST_instr(I32_numtype, i_2) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.COPY`_instr(x_1, x_2)]), [])
    -- otherwise
    -- if (n = 0)

  ;; test.spectec:5436.1-5446.24
  rule `array.copy-le`{z : state, a_1 : addr, i_1 : num_(I32_numtype), a_2 : addr, i_2 : num_(I32_numtype), n : n, x_1 : idx, x_2 : idx, `sx?` : sx?, `mut?` : mut?, zt_2 : storagetype}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a_1) CONST_instr(I32_numtype, i_1) `REF.ARRAY_ADDR`_instr(a_2) CONST_instr(I32_numtype, i_2) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.COPY`_instr(x_1, x_2)]), [`REF.ARRAY_ADDR`_instr(a_1) CONST_instr(I32_numtype, i_1) `REF.ARRAY_ADDR`_instr(a_2) CONST_instr(I32_numtype, i_2) `ARRAY.GET`_instr(sx?{sx <- `sx?`}, x_2) `ARRAY.SET`_instr(x_1) `REF.ARRAY_ADDR`_instr(a_1) CONST_instr(I32_numtype, `%`_num_((i_1!`%`_num_.0 + 1))) `REF.ARRAY_ADDR`_instr(a_2) CONST_instr(I32_numtype, `%`_num_((i_2!`%`_num_.0 + 1))) CONST_instr(I32_numtype, `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `ARRAY.COPY`_instr(x_1, x_2)])
    -- otherwise
    -- Expand: `%~~%`($type(z, x_2), ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt_2)))
    -- if ((i_1!`%`_num_.0 <= i_2!`%`_num_.0) /\ (sx?{sx <- `sx?`} = $sx(zt_2)))

  ;; test.spectec:5448.1-5457.24
  rule `array.copy-gt`{z : state, a_1 : addr, i_1 : num_(I32_numtype), a_2 : addr, i_2 : num_(I32_numtype), n : n, x_1 : idx, x_2 : idx, `sx?` : sx?, `mut?` : mut?, zt_2 : storagetype}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a_1) CONST_instr(I32_numtype, i_1) `REF.ARRAY_ADDR`_instr(a_2) CONST_instr(I32_numtype, i_2) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.COPY`_instr(x_1, x_2)]), [`REF.ARRAY_ADDR`_instr(a_1) CONST_instr(I32_numtype, `%`_num_(((((i_1!`%`_num_.0 + n) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `REF.ARRAY_ADDR`_instr(a_2) CONST_instr(I32_numtype, `%`_num_(((((i_2!`%`_num_.0 + n) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `ARRAY.GET`_instr(sx?{sx <- `sx?`}, x_2) `ARRAY.SET`_instr(x_1) `REF.ARRAY_ADDR`_instr(a_1) CONST_instr(I32_numtype, i_1) `REF.ARRAY_ADDR`_instr(a_2) CONST_instr(I32_numtype, i_2) CONST_instr(I32_numtype, `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `ARRAY.COPY`_instr(x_1, x_2)])
    -- otherwise
    -- Expand: `%~~%`($type(z, x_2), ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt_2)))
    -- if (sx?{sx <- `sx?`} = $sx(zt_2))

  ;; test.spectec:5460.1-5461.95
  rule `array.init_elem-null`{z : state, i : num_(I32_numtype), j : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [`REF.NULL_ADDR`_instr CONST_instr(I32_numtype, i) CONST_instr(I32_numtype, j) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.INIT_ELEM`_instr(x, y)]), [TRAP_instr])

  ;; test.spectec:5463.1-5466.45
  rule `array.init_elem-oob1`{z : state, a : addr, i : num_(I32_numtype), j : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) CONST_instr(I32_numtype, j) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.INIT_ELEM`_instr(x, y)]), [TRAP_instr])
    -- if ((i!`%`_num_.0 + n) > |$arrayinst(z)[a].FIELDS_arrayinst|)

  ;; test.spectec:5468.1-5471.38
  rule `array.init_elem-oob2`{z : state, a : addr, i : num_(I32_numtype), j : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) CONST_instr(I32_numtype, j) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.INIT_ELEM`_instr(x, y)]), [TRAP_instr])
    -- if ((j!`%`_num_.0 + n) > |$elem(z, y).REFS_eleminst|)

  ;; test.spectec:5473.1-5477.14
  rule `array.init_elem-zero`{z : state, a : addr, i : num_(I32_numtype), j : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) CONST_instr(I32_numtype, j) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.INIT_ELEM`_instr(x, y)]), [])
    -- otherwise
    -- if (n = 0)

  ;; test.spectec:5479.1-5485.34
  rule `array.init_elem-succ`{z : state, a : addr, i : num_(I32_numtype), j : num_(I32_numtype), n : n, x : idx, y : idx, ref : ref}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) CONST_instr(I32_numtype, j) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.INIT_ELEM`_instr(x, y)]), [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) (ref : ref <: instr) `ARRAY.SET`_instr(x) `REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, `%`_num_((i!`%`_num_.0 + 1))) CONST_instr(I32_numtype, `%`_num_((j!`%`_num_.0 + 1))) CONST_instr(I32_numtype, `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `ARRAY.INIT_ELEM`_instr(x, y)])
    -- otherwise
    -- if (ref = $elem(z, y).REFS_eleminst[j!`%`_num_.0])

  ;; test.spectec:5488.1-5489.95
  rule `array.init_data-null`{z : state, i : num_(I32_numtype), j : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [`REF.NULL_ADDR`_instr CONST_instr(I32_numtype, i) CONST_instr(I32_numtype, j) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.INIT_DATA`_instr(x, y)]), [TRAP_instr])

  ;; test.spectec:5491.1-5494.45
  rule `array.init_data-oob1`{z : state, a : addr, i : num_(I32_numtype), j : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) CONST_instr(I32_numtype, j) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.INIT_DATA`_instr(x, y)]), [TRAP_instr])
    -- if ((i!`%`_num_.0 + n) > |$arrayinst(z)[a].FIELDS_arrayinst|)

  ;; test.spectec:5496.1-5500.54
  rule `array.init_data-oob2`{z : state, a : addr, i : num_(I32_numtype), j : num_(I32_numtype), n : n, x : idx, y : idx, `mut?` : mut?, zt : storagetype}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) CONST_instr(I32_numtype, j) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.INIT_DATA`_instr(x, y)]), [TRAP_instr])
    -- Expand: `%~~%`($type(z, x), ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- if ((j!`%`_num_.0 + ((((n * $zsize(zt)) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$data(z, y).BYTES_datainst|)

  ;; test.spectec:5502.1-5506.14
  rule `array.init_data-zero`{z : state, a : addr, i : num_(I32_numtype), j : num_(I32_numtype), n : n, x : idx, y : idx}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) CONST_instr(I32_numtype, j) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.INIT_DATA`_instr(x, y)]), [])
    -- otherwise
    -- if (n = 0)

  ;; test.spectec:5509.1-5516.62
  rule `array.init_data-num`{z : state, a : addr, i : num_(I32_numtype), j : num_(I32_numtype), n : n, x : idx, y : idx, zt : storagetype, c : lit_(zt), `mut?` : mut?}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) CONST_instr(I32_numtype, j) CONST_instr(I32_numtype, `%`_num_(n)) `ARRAY.INIT_DATA`_instr(x, y)]), [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) $const($cunpack(zt), $cunpacknum_(zt, c)) `ARRAY.SET`_instr(x) `REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, `%`_num_((i!`%`_num_.0 + 1))) CONST_instr(I32_numtype, `%`_num_((j!`%`_num_.0 + ((($zsize(zt) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)))) CONST_instr(I32_numtype, `%`_num_((((n : nat <:> int) - (1 : nat <:> int)) : int <:> nat))) `ARRAY.INIT_DATA`_instr(x, y)])
    -- otherwise
    -- Expand: `%~~%`($type(z, x), ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- if ($zbytes_(zt, c) = $data(z, y).BYTES_datainst[j!`%`_num_.0 : ((($zsize(zt) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])

;; test.spectec:4604.1-4604.88
rec {

;; test.spectec:4604.1-4604.88
relation Step: `%~>%`(config, config)
  ;; test.spectec:4612.1-4614.34
  rule pure{z : state, `instr*` : instr*, `instr'*` : instr*}:
    `%~>%`(`%;%`_config(z, instr*{instr <- `instr*`}), `%;%`_config(z, instr'*{instr' <- `instr'*`}))
    -- Step_pure: `%~>%`(instr*{instr <- `instr*`}, instr'*{instr' <- `instr'*`})

  ;; test.spectec:4616.1-4618.37
  rule read{z : state, `instr*` : instr*, `instr'*` : instr*}:
    `%~>%`(`%;%`_config(z, instr*{instr <- `instr*`}), `%;%`_config(z, instr'*{instr' <- `instr'*`}))
    -- Step_read: `%~>%`(`%;%`_config(z, instr*{instr <- `instr*`}), instr'*{instr' <- `instr'*`})

  ;; test.spectec:4631.1-4634.41
  rule `ctxt-instrs`{z : state, `val*` : val*, `instr*` : instr*, `instr_1*` : instr*, z' : state, `instr'*` : instr*}:
    `%~>%`(`%;%`_config(z, (val : val <: instr)*{val <- `val*`} ++ instr*{instr <- `instr*`} ++ instr_1*{instr_1 <- `instr_1*`}), `%;%`_config(z', (val : val <: instr)*{val <- `val*`} ++ instr'*{instr' <- `instr'*`} ++ instr_1*{instr_1 <- `instr_1*`}))
    -- Step: `%~>%`(`%;%`_config(z, instr*{instr <- `instr*`}), `%;%`_config(z', instr'*{instr' <- `instr'*`}))
    -- if ((val*{val <- `val*`} =/= []) \/ (instr_1*{instr_1 <- `instr_1*`} =/= []))

  ;; test.spectec:4636.1-4638.36
  rule `ctxt-label`{z : state, n : n, `instr_0*` : instr*, `instr*` : instr*, z' : state, `instr'*` : instr*}:
    `%~>%`(`%;%`_config(z, [`LABEL_%{%}%`_instr(n, instr_0*{instr_0 <- `instr_0*`}, instr*{instr <- `instr*`})]), `%;%`_config(z', [`LABEL_%{%}%`_instr(n, instr_0*{instr_0 <- `instr_0*`}, instr'*{instr' <- `instr'*`})]))
    -- Step: `%~>%`(`%;%`_config(z, instr*{instr <- `instr*`}), `%;%`_config(z', instr'*{instr' <- `instr'*`}))

  ;; test.spectec:4640.1-4642.36
  rule `ctxt-handler`{z : state, n : n, `catch*` : catch*, `instr*` : instr*, z' : state, `instr'*` : instr*}:
    `%~>%`(`%;%`_config(z, [`HANDLER_%{%}%`_instr(n, catch*{catch <- `catch*`}, instr*{instr <- `instr*`})]), `%;%`_config(z', [`HANDLER_%{%}%`_instr(n, catch*{catch <- `catch*`}, instr'*{instr' <- `instr'*`})]))
    -- Step: `%~>%`(`%;%`_config(z, instr*{instr <- `instr*`}), `%;%`_config(z', instr'*{instr' <- `instr'*`}))

  ;; test.spectec:4644.1-4646.45
  rule `ctxt-frame`{s : store, f : frame, n : n, f' : frame, `instr*` : instr*, s' : store, f'' : frame, `instr'*` : instr*}:
    `%~>%`(`%;%`_config(`%;%`_state(s, f), [`FRAME_%{%}%`_instr(n, f', instr*{instr <- `instr*`})]), `%;%`_config(`%;%`_state(s', f), [`FRAME_%{%}%`_instr(n, f'', instr'*{instr' <- `instr'*`})]))
    -- Step: `%~>%`(`%;%`_config(`%;%`_state(s, f'), instr*{instr <- `instr*`}), `%;%`_config(`%;%`_state(s', f''), instr'*{instr' <- `instr'*`}))

  ;; test.spectec:4826.1-4830.49
  rule throw{z : state, n : n, `val*` : val*, x : idx, exn : exninst, a : addr, `t*` : valtype*}:
    `%~>%`(`%;%`_config(z, (val : val <: instr)^n{val <- `val*`} ++ [THROW_instr(x)]), `%;%`_config($add_exninst(z, [exn]), [`REF.EXN_ADDR`_instr(a) THROW_REF_instr]))
    -- Expand: `%~~%`($as_deftype($tag(z, x).TYPE_taginst), `FUNC%->%`_comptype(`%`_resulttype(t^n{t <- `t*`}), `%`_resulttype([])))
    -- if (a = |$exninst(z)|)
    -- if (exn = {TAG $tagaddr(z)[x!`%`_idx.0], FIELDS val^n{val <- `val*`}})

  ;; test.spectec:4904.1-4905.56
  rule `local.set`{z : state, val : val, x : idx}:
    `%~>%`(`%;%`_config(z, [(val : val <: instr) `LOCAL.SET`_instr(x)]), `%;%`_config($with_local(z, x, val), []))

  ;; test.spectec:4917.1-4918.58
  rule `global.set`{z : state, val : val, x : idx}:
    `%~>%`(`%;%`_config(z, [(val : val <: instr) `GLOBAL.SET`_instr(x)]), `%;%`_config($with_global(z, x, val), []))

  ;; test.spectec:4931.1-4933.33
  rule `table.set-oob`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), ref : ref, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) (ref : ref <: instr) `TABLE.SET`_instr(x)]), `%;%`_config(z, [TRAP_instr]))
    -- if (i!`%`_num_.0 >= |$table(z, x).REFS_tableinst|)

  ;; test.spectec:4935.1-4937.32
  rule `table.set-val`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), ref : ref, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) (ref : ref <: instr) `TABLE.SET`_instr(x)]), `%;%`_config($with_table(z, x, i!`%`_num_.0, ref), []))
    -- if (i!`%`_num_.0 < |$table(z, x).REFS_tableinst|)

  ;; test.spectec:4946.1-4949.46
  rule `table.grow-succeed`{z : state, ref : ref, at : addrtype, n : n, x : idx, ti : tableinst}:
    `%~>%`(`%;%`_config(z, [(ref : ref <: instr) CONST_instr((at : addrtype <: numtype), `%`_num_(n)) `TABLE.GROW`_instr(x)]), `%;%`_config($with_tableinst(z, x, ti), [CONST_instr((at : addrtype <: numtype), `%`_num_(|$table(z, x).REFS_tableinst|))]))
    -- if (ti = $growtable($table(z, x), n, ref))

  ;; test.spectec:4951.1-4952.87
  rule `table.grow-fail`{z : state, ref : ref, at : addrtype, n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [(ref : ref <: instr) CONST_instr((at : addrtype <: numtype), `%`_num_(n)) `TABLE.GROW`_instr(x)]), `%;%`_config(z, [CONST_instr((at : addrtype <: numtype), `%`_num_($inv_signed_($size((at : addrtype <: numtype)), - (1 : nat <:> int))))]))

  ;; test.spectec:5012.1-5013.51
  rule `elem.drop`{z : state, x : idx}:
    `%~>%`(`%;%`_config(z, [`ELEM.DROP`_instr(x)]), `%;%`_config($with_elem(z, x, []), []))

  ;; test.spectec:5096.1-5099.60
  rule `store-num-oob`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), nt : numtype, c : num_(nt), x : idx, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) CONST_instr(nt, c) STORE_instr(nt, ?(), x, ao)]), `%;%`_config(z, [TRAP_instr]))
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) + ((($size(nt) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, x).BYTES_meminst|)

  ;; test.spectec:5101.1-5105.29
  rule `store-num-val`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), nt : numtype, c : num_(nt), x : idx, ao : memarg, `b*` : byte*}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) CONST_instr(nt, c) STORE_instr(nt, ?(), x, ao)]), `%;%`_config($with_mem(z, x, (i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0), ((($size(nt) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b*{b <- `b*`}), []))
    -- if (b*{b <- `b*`} = $nbytes_(nt, c))

  ;; test.spectec:5107.1-5110.52
  rule `store-pack-oob`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), Inn : Inn, c : num_((Inn : addrtype <: numtype)), n : n, x : idx, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) CONST_instr((Inn : addrtype <: numtype), c) STORE_instr((Inn : addrtype <: numtype), ?(`%`_storeop_(`%`_sz(n))), x, ao)]), `%;%`_config(z, [TRAP_instr]))
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) + (((n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, x).BYTES_meminst|)

  ;; test.spectec:5112.1-5116.52
  rule `store-pack-val`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), Inn : Inn, c : num_((Inn : addrtype <: numtype)), n : n, x : idx, ao : memarg, `b*` : byte*}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) CONST_instr((Inn : addrtype <: numtype), c) STORE_instr((Inn : addrtype <: numtype), ?(`%`_storeop_(`%`_sz(n))), x, ao)]), `%;%`_config($with_mem(z, x, (i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0), (((n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b*{b <- `b*`}), []))
    -- if (b*{b <- `b*`} = $ibytes_(n, $wrap__($size((Inn : addrtype <: numtype)), n, c)))

  ;; test.spectec:5118.1-5121.63
  rule `vstore-oob`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), c : vec_(V128_Vnn), x : idx, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) VCONST_instr(V128_vectype, c) VSTORE_instr(V128_vectype, x, ao)]), `%;%`_config(z, [TRAP_instr]))
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) + ((($vsize(V128_vectype) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, x).BYTES_meminst|)

  ;; test.spectec:5123.1-5126.31
  rule `vstore-val`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), c : vec_(V128_Vnn), x : idx, ao : memarg, `b*` : byte*}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) VCONST_instr(V128_vectype, c) VSTORE_instr(V128_vectype, x, ao)]), `%;%`_config($with_mem(z, x, (i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0), ((($vsize(V128_vectype) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b*{b <- `b*`}), []))
    -- if (b*{b <- `b*`} = $vbytes_(V128_vectype, c))

  ;; test.spectec:5129.1-5132.50
  rule `vstore_lane-oob`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), c : vec_(V128_Vnn), N : N, x : idx, ao : memarg, j : laneidx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) VCONST_instr(V128_vectype, c) VSTORE_LANE_instr(V128_vectype, `%`_sz(N), x, ao, j)]), `%;%`_config(z, [TRAP_instr]))
    -- if (((i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0) + N) > |$mem(z, x).BYTES_meminst|)

  ;; test.spectec:5134.1-5139.49
  rule `vstore_lane-val`{z : state, at : addrtype, i : num_((at : addrtype <: numtype)), c : vec_(V128_Vnn), N : N, x : idx, ao : memarg, j : laneidx, `b*` : byte*, Jnn : Jnn, M : M}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), i) VCONST_instr(V128_vectype, c) VSTORE_LANE_instr(V128_vectype, `%`_sz(N), x, ao, j)]), `%;%`_config($with_mem(z, x, (i!`%`_num_.0 + ao.OFFSET_memarg!`%`_u64.0), (((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b*{b <- `b*`}), []))
    -- if (N = $jsize(Jnn))
    -- if ((M : nat <:> rat) = ((128 : nat <:> rat) / (N : nat <:> rat)))
    -- if (b*{b <- `b*`} = $ibytes_(N, `%`_iN($lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c)[j!`%`_laneidx.0]!`%`_lane_.0)))

  ;; test.spectec:5148.1-5151.37
  rule `memory.grow-succeed`{z : state, at : addrtype, n : n, x : idx, mi : meminst}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), `%`_num_(n)) `MEMORY.GROW`_instr(x)]), `%;%`_config($with_meminst(z, x, mi), [CONST_instr((at : addrtype <: numtype), `%`_num_((((|$mem(z, x).BYTES_meminst| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) : rat <:> nat)))]))
    -- if (mi = $growmem($mem(z, x), n))

  ;; test.spectec:5153.1-5154.84
  rule `memory.grow-fail`{z : state, at : addrtype, n : n, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_instr((at : addrtype <: numtype), `%`_num_(n)) `MEMORY.GROW`_instr(x)]), `%;%`_config(z, [CONST_instr((at : addrtype <: numtype), `%`_num_($inv_signed_($size((at : addrtype <: numtype)), - (1 : nat <:> int))))]))

  ;; test.spectec:5214.1-5215.51
  rule `data.drop`{z : state, x : idx}:
    `%~>%`(`%;%`_config(z, [`DATA.DROP`_instr(x)]), `%;%`_config($with_data(z, x, []), []))

  ;; test.spectec:5291.1-5295.65
  rule `struct.new`{z : state, n : n, `val*` : val*, x : idx, si : structinst, a : addr, `mut?*` : mut?*, `zt*` : storagetype*}:
    `%~>%`(`%;%`_config(z, (val : val <: instr)^n{val <- `val*`} ++ [`STRUCT.NEW`_instr(x)]), `%;%`_config($add_structinst(z, [si]), [`REF.STRUCT_ADDR`_instr(a)]))
    -- Expand: `%~~%`($type(z, x), STRUCT_comptype(`%`_list(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)^n{`mut?` <- `mut?*`, zt <- `zt*`})))
    -- if (a = |$structinst(z)|)
    -- if (si = {TYPE $type(z, x), FIELDS $packfield_(zt, val)^n{val <- `val*`, zt <- `zt*`}})

  ;; test.spectec:5312.1-5313.55
  rule `struct.set-null`{z : state, val : val, x : idx, i : fieldidx}:
    `%~>%`(`%;%`_config(z, [`REF.NULL_ADDR`_instr (val : val <: instr) `STRUCT.SET`_instr(x, i)]), `%;%`_config(z, [TRAP_instr]))

  ;; test.spectec:5315.1-5318.46
  rule `struct.set-struct`{z : state, a : addr, val : val, x : idx, i : fieldidx, `zt*` : storagetype*, `mut?*` : mut?*}:
    `%~>%`(`%;%`_config(z, [`REF.STRUCT_ADDR`_instr(a) (val : val <: instr) `STRUCT.SET`_instr(x, i)]), `%;%`_config($with_struct(z, a, i!`%`_fieldidx.0, $packfield_(zt*{zt <- `zt*`}[i!`%`_fieldidx.0], val)), []))
    -- Expand: `%~~%`($type(z, x), STRUCT_comptype(`%`_list(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)*{`mut?` <- `mut?*`, zt <- `zt*`})))

  ;; test.spectec:5331.1-5336.65
  rule `array.new_fixed`{z : state, n : n, `val*` : val*, x : idx, ai : arrayinst, a : addr, `mut?` : mut?, zt : storagetype}:
    `%~>%`(`%;%`_config(z, (val : val <: instr)^n{val <- `val*`} ++ [`ARRAY.NEW_FIXED`_instr(x, `%`_u32(n))]), `%;%`_config($add_arrayinst(z, [ai]), [`REF.ARRAY_ADDR`_instr(a)]))
    -- Expand: `%~~%`($type(z, x), ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- if ((a = |$arrayinst(z)|) /\ (ai = {TYPE $type(z, x), FIELDS $packfield_(zt, val)^n{val <- `val*`}}))

  ;; test.spectec:5376.1-5377.66
  rule `array.set-null`{z : state, i : num_(I32_numtype), val : val, x : idx}:
    `%~>%`(`%;%`_config(z, [`REF.NULL_ADDR`_instr CONST_instr(I32_numtype, i) (val : val <: instr) `ARRAY.SET`_instr(x)]), `%;%`_config(z, [TRAP_instr]))

  ;; test.spectec:5379.1-5381.39
  rule `array.set-oob`{z : state, a : addr, i : num_(I32_numtype), val : val, x : idx}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) (val : val <: instr) `ARRAY.SET`_instr(x)]), `%;%`_config(z, [TRAP_instr]))
    -- if (i!`%`_num_.0 >= |$arrayinst(z)[a].FIELDS_arrayinst|)

  ;; test.spectec:5383.1-5386.44
  rule `array.set-array`{z : state, a : addr, i : num_(I32_numtype), val : val, x : idx, zt : storagetype, `mut?` : mut?}:
    `%~>%`(`%;%`_config(z, [`REF.ARRAY_ADDR`_instr(a) CONST_instr(I32_numtype, i) (val : val <: instr) `ARRAY.SET`_instr(x)]), `%;%`_config($with_array(z, a, i!`%`_num_.0, $packfield_(zt, val)), []))
    -- Expand: `%~~%`($type(z, x), ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
}

;; test.spectec:4607.1-4607.92
rec {

;; test.spectec:4607.1-4607.92
relation Steps: `%~>*%`(config, config)
  ;; test.spectec:4620.1-4621.26
  rule refl{z : state, `instr*` : instr*}:
    `%~>*%`(`%;%`_config(z, instr*{instr <- `instr*`}), `%;%`_config(z, instr*{instr <- `instr*`}))

  ;; test.spectec:4623.1-4626.44
  rule trans{z : state, `instr*` : instr*, z'' : state, `instr''*` : instr*, z' : state, `instr'*` : instr*}:
    `%~>*%`(`%;%`_config(z, instr*{instr <- `instr*`}), `%;%`_config(z'', instr''*{instr'' <- `instr''*`}))
    -- Step: `%~>%`(`%;%`_config(z, instr*{instr <- `instr*`}), `%;%`_config(z', instr'*{instr' <- `instr'*`}))
    -- Steps: `%~>*%`(`%;%`_config(z', instr'*{instr' <- `instr'*`}), `%;%`_config(z'', instr''*{instr'' <- `instr''*`}))
}

;; test.spectec:5704.1-5704.108
relation Eval_expr: `%;%~>*%;%`(state, expr, state, val*)
  ;; test.spectec:5706.1-5708.37
  rule _{z : state, `instr*` : instr*, z' : state, `val*` : val*}:
    `%;%~>*%;%`(z, instr*{instr <- `instr*`}, z', val*{val <- `val*`})
    -- Steps: `%~>*%`(`%;%`_config(z, instr*{instr <- `instr*`}), `%;%`_config(z', (val : val <: instr)*{val <- `val*`}))

;; test.spectec:5723.1-5723.63
rec {

;; test.spectec:5723.1-5723.63
def $alloctypes(type*) : deftype*
  ;; test.spectec:5724.1-5724.27
  def $alloctypes([]) = []
  ;; test.spectec:5725.1-5729.24
  def $alloctypes{`type'*` : type*, type : type, `deftype'*` : deftype*, `deftype*` : deftype*, rectype : rectype, x : idx}(type'*{type' <- `type'*`} ++ [type]) = deftype'*{deftype' <- `deftype'*`} ++ deftype*{deftype <- `deftype*`}
    -- if (deftype'*{deftype' <- `deftype'*`} = $alloctypes(type'*{type' <- `type'*`}))
    -- if (type = TYPE_type(rectype))
    -- if (deftype*{deftype <- `deftype*`} = $subst_all_deftypes($rolldt(x, rectype), (deftype' : deftype <: typeuse)*{deftype' <- `deftype'*`}))
    -- if (x!`%`_idx.0 = |deftype'*{deftype' <- `deftype'*`}|)
}

;; test.spectec:5731.1-5731.49
def $alloctag(store : store, tagtype : tagtype) : (store, tagaddr)
  ;; test.spectec:5732.1-5734.35
  def $alloctag{s : store, tagtype : tagtype, taginst : taginst}(s, tagtype) = (s +++ {TAGS [taginst], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], STRUCTS [], ARRAYS [], EXNS []}, |s.TAGS_store|)
    -- if (taginst = {TYPE tagtype})

;; test.spectec:5736.1-5736.102
rec {

;; test.spectec:5736.1-5736.102
def $alloctags(store : store, tagtype*) : (store, tagaddr*)
  ;; test.spectec:5737.1-5737.34
  def $alloctags{s : store}(s, []) = (s, [])
  ;; test.spectec:5738.1-5740.49
  def $alloctags{s : store, tagtype : tagtype, `tagtype'*` : tagtype*, s_2 : store, ja : tagaddr, `ja'*` : tagaddr*, s_1 : store}(s, [tagtype] ++ tagtype'*{tagtype' <- `tagtype'*`}) = (s_2, [ja] ++ ja'*{ja' <- `ja'*`})
    -- if ((s_1, ja) = $alloctag(s, tagtype))
    -- if ((s_2, ja'*{ja' <- `ja'*`}) = $alloctags(s_1, tagtype'*{tagtype' <- `tagtype'*`}))
}

;; test.spectec:5742.1-5742.63
def $allocglobal(store : store, globaltype : globaltype, val : val) : (store, globaladdr)
  ;; test.spectec:5743.1-5745.52
  def $allocglobal{s : store, globaltype : globaltype, val : val, globalinst : globalinst}(s, globaltype, val) = (s +++ {TAGS [], GLOBALS [globalinst], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], STRUCTS [], ARRAYS [], EXNS []}, |s.GLOBALS_store|)
    -- if (globalinst = {TYPE globaltype, VALUE val})

;; test.spectec:5747.1-5747.122
rec {

;; test.spectec:5747.1-5747.122
def $allocglobals(store : store, globaltype*, val*) : (store, globaladdr*)
  ;; test.spectec:5748.1-5748.42
  def $allocglobals{s : store}(s, [], []) = (s, [])
  ;; test.spectec:5749.1-5751.62
  def $allocglobals{s : store, globaltype : globaltype, `globaltype'*` : globaltype*, val : val, `val'*` : val*, s_2 : store, ga : globaladdr, `ga'*` : globaladdr*, s_1 : store}(s, [globaltype] ++ globaltype'*{globaltype' <- `globaltype'*`}, [val] ++ val'*{val' <- `val'*`}) = (s_2, [ga] ++ ga'*{ga' <- `ga'*`})
    -- if ((s_1, ga) = $allocglobal(s, globaltype, val))
    -- if ((s_2, ga'*{ga' <- `ga'*`}) = $allocglobals(s_1, globaltype'*{globaltype' <- `globaltype'*`}, val'*{val' <- `val'*`}))
}

;; test.spectec:5753.1-5753.49
def $allocmem(store : store, memtype : memtype) : (store, memaddr)
  ;; test.spectec:5754.1-5756.83
  def $allocmem{s : store, at : addrtype, i : u64, `j?` : u64?, meminst : meminst}(s, `%%PAGE`_memtype(at, `[%..%]`_limits(i, j?{j <- `j?`}))) = (s +++ {TAGS [], GLOBALS [], MEMS [meminst], TABLES [], FUNCS [], DATAS [], ELEMS [], STRUCTS [], ARRAYS [], EXNS []}, |s.MEMS_store|)
    -- if (meminst = {TYPE `%%PAGE`_memtype(at, `[%..%]`_limits(i, j?{j <- `j?`})), BYTES `%`_byte(0)^(i!`%`_u64.0 * (64 * $Ki)){}})

;; test.spectec:5758.1-5758.102
rec {

;; test.spectec:5758.1-5758.102
def $allocmems(store : store, memtype*) : (store, memaddr*)
  ;; test.spectec:5759.1-5759.34
  def $allocmems{s : store}(s, []) = (s, [])
  ;; test.spectec:5760.1-5762.49
  def $allocmems{s : store, memtype : memtype, `memtype'*` : memtype*, s_2 : store, ma : memaddr, `ma'*` : memaddr*, s_1 : store}(s, [memtype] ++ memtype'*{memtype' <- `memtype'*`}) = (s_2, [ma] ++ ma'*{ma' <- `ma'*`})
    -- if ((s_1, ma) = $allocmem(s, memtype))
    -- if ((s_2, ma'*{ma' <- `ma'*`}) = $allocmems(s_1, memtype'*{memtype' <- `memtype'*`}))
}

;; test.spectec:5764.1-5764.60
def $alloctable(store : store, tabletype : tabletype, ref : ref) : (store, tableaddr)
  ;; test.spectec:5765.1-5767.60
  def $alloctable{s : store, at : addrtype, i : u64, `j?` : u64?, rt : reftype, ref : ref, tableinst : tableinst}(s, `%%%`_tabletype(at, `[%..%]`_limits(i, j?{j <- `j?`}), rt), ref) = (s +++ {TAGS [], GLOBALS [], MEMS [], TABLES [tableinst], FUNCS [], DATAS [], ELEMS [], STRUCTS [], ARRAYS [], EXNS []}, |s.TABLES_store|)
    -- if (tableinst = {TYPE `%%%`_tabletype(at, `[%..%]`_limits(i, j?{j <- `j?`}), rt), REFS ref^i!`%`_u64.0{}})

;; test.spectec:5769.1-5769.118
rec {

;; test.spectec:5769.1-5769.118
def $alloctables(store : store, tabletype*, ref*) : (store, tableaddr*)
  ;; test.spectec:5770.1-5770.41
  def $alloctables{s : store}(s, [], []) = (s, [])
  ;; test.spectec:5771.1-5773.60
  def $alloctables{s : store, tabletype : tabletype, `tabletype'*` : tabletype*, ref : ref, `ref'*` : ref*, s_2 : store, ta : tableaddr, `ta'*` : tableaddr*, s_1 : store}(s, [tabletype] ++ tabletype'*{tabletype' <- `tabletype'*`}, [ref] ++ ref'*{ref' <- `ref'*`}) = (s_2, [ta] ++ ta'*{ta' <- `ta'*`})
    -- if ((s_1, ta) = $alloctable(s, tabletype, ref))
    -- if ((s_2, ta'*{ta' <- `ta'*`}) = $alloctables(s_1, tabletype'*{tabletype' <- `tabletype'*`}, ref'*{ref' <- `ref'*`}))
}

;; test.spectec:5775.1-5775.73
def $allocfunc(store : store, deftype : deftype, funccode : funccode, moduleinst : moduleinst) : (store, funcaddr)
  ;; test.spectec:5776.1-5778.70
  def $allocfunc{s : store, deftype : deftype, funccode : funccode, moduleinst : moduleinst, funcinst : funcinst}(s, deftype, funccode, moduleinst) = (s +++ {TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [funcinst], DATAS [], ELEMS [], STRUCTS [], ARRAYS [], EXNS []}, |s.FUNCS_store|)
    -- if (funcinst = {TYPE deftype, MODULE moduleinst, CODE funccode})

;; test.spectec:5780.1-5780.133
rec {

;; test.spectec:5780.1-5780.133
def $allocfuncs(store : store, deftype*, funccode*, moduleinst*) : (store, funcaddr*)
  ;; test.spectec:5781.1-5781.45
  def $allocfuncs{s : store}(s, [], [], []) = (s, [])
  ;; test.spectec:5782.1-5784.71
  def $allocfuncs{s : store, dt : deftype, `dt'*` : deftype*, funccode : funccode, `funccode'*` : funccode*, moduleinst : moduleinst, `moduleinst'*` : moduleinst*, s_2 : store, fa : funcaddr, `fa'*` : funcaddr*, s_1 : store}(s, [dt] ++ dt'*{dt' <- `dt'*`}, [funccode] ++ funccode'*{funccode' <- `funccode'*`}, [moduleinst] ++ moduleinst'*{moduleinst' <- `moduleinst'*`}) = (s_2, [fa] ++ fa'*{fa' <- `fa'*`})
    -- if ((s_1, fa) = $allocfunc(s, dt, funccode, moduleinst))
    -- if ((s_2, fa'*{fa' <- `fa'*`}) = $allocfuncs(s_1, dt'*{dt' <- `dt'*`}, funccode'*{funccode' <- `funccode'*`}, moduleinst'*{moduleinst' <- `moduleinst'*`}))
}

;; test.spectec:5786.1-5786.59
def $allocdata(store : store, datatype : datatype, byte*) : (store, dataaddr)
  ;; test.spectec:5787.1-5789.35
  def $allocdata{s : store, `byte*` : byte*, datainst : datainst}(s, OK_datatype, byte*{byte <- `byte*`}) = (s +++ {TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [datainst], ELEMS [], STRUCTS [], ARRAYS [], EXNS []}, |s.DATAS_store|)
    -- if (datainst = {BYTES byte*{byte <- `byte*`}})

;; test.spectec:5791.1-5791.118
rec {

;; test.spectec:5791.1-5791.118
def $allocdatas(store : store, datatype*, byte**) : (store, dataaddr*)
  ;; test.spectec:5792.1-5792.40
  def $allocdatas{s : store}(s, [], []) = (s, [])
  ;; test.spectec:5793.1-5795.53
  def $allocdatas{s : store, ok : datatype, `ok'*` : datatype*, `b*` : byte*, `b'**` : byte**, s_2 : store, da : dataaddr, `da'*` : dataaddr*, s_1 : store}(s, [ok] ++ ok'*{ok' <- `ok'*`}, [b*{b <- `b*`}] ++ b'*{b' <- `b'*`}*{`b'*` <- `b'**`}) = (s_2, [da] ++ da'*{da' <- `da'*`})
    -- if ((s_1, da) = $allocdata(s, ok, b*{b <- `b*`}))
    -- if ((s_2, da'*{da' <- `da'*`}) = $allocdatas(s_1, ok'*{ok' <- `ok'*`}, b'*{b' <- `b'*`}*{`b'*` <- `b'**`}))
}

;; test.spectec:5797.1-5797.58
def $allocelem(store : store, elemtype : elemtype, ref*) : (store, elemaddr)
  ;; test.spectec:5798.1-5800.48
  def $allocelem{s : store, elemtype : elemtype, `ref*` : ref*, eleminst : eleminst}(s, elemtype, ref*{ref <- `ref*`}) = (s +++ {TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [eleminst], STRUCTS [], ARRAYS [], EXNS []}, |s.ELEMS_store|)
    -- if (eleminst = {TYPE elemtype, REFS ref*{ref <- `ref*`}})

;; test.spectec:5802.1-5802.117
rec {

;; test.spectec:5802.1-5802.117
def $allocelems(store : store, elemtype*, ref**) : (store, elemaddr*)
  ;; test.spectec:5803.1-5803.40
  def $allocelems{s : store}(s, [], []) = (s, [])
  ;; test.spectec:5804.1-5806.55
  def $allocelems{s : store, rt : reftype, `rt'*` : reftype*, `ref*` : ref*, `ref'**` : ref**, s_2 : store, ea : elemaddr, `ea'*` : elemaddr*, s_1 : store}(s, [rt] ++ rt'*{rt' <- `rt'*`}, [ref*{ref <- `ref*`}] ++ ref'*{ref' <- `ref'*`}*{`ref'*` <- `ref'**`}) = (s_2, [ea] ++ ea'*{ea' <- `ea'*`})
    -- if ((s_1, ea) = $allocelem(s, rt, ref*{ref <- `ref*`}))
    -- if ((s_2, ea'*{ea' <- `ea'*`}) = $allocelems(s_1, rt'*{rt' <- `rt'*`}, ref'*{ref' <- `ref'*`}*{`ref'*` <- `ref'**`}))
}

;; test.spectec:5808.1-5808.90
def $allocexport(moduleinst : moduleinst, export : export) : exportinst
  ;; test.spectec:5809.1-5809.97
  def $allocexport{moduleinst : moduleinst, name : name, x : idx}(moduleinst, EXPORT_export(name, TAG_externidx(x))) = {NAME name, ADDR TAG_externaddr(moduleinst.TAGS_moduleinst[x!`%`_idx.0])}
  ;; test.spectec:5810.1-5810.106
  def $allocexport{moduleinst : moduleinst, name : name, x : idx}(moduleinst, EXPORT_export(name, GLOBAL_externidx(x))) = {NAME name, ADDR GLOBAL_externaddr(moduleinst.GLOBALS_moduleinst[x!`%`_idx.0])}
  ;; test.spectec:5811.1-5811.97
  def $allocexport{moduleinst : moduleinst, name : name, x : idx}(moduleinst, EXPORT_export(name, MEM_externidx(x))) = {NAME name, ADDR MEM_externaddr(moduleinst.MEMS_moduleinst[x!`%`_idx.0])}
  ;; test.spectec:5812.1-5812.103
  def $allocexport{moduleinst : moduleinst, name : name, x : idx}(moduleinst, EXPORT_export(name, TABLE_externidx(x))) = {NAME name, ADDR TABLE_externaddr(moduleinst.TABLES_moduleinst[x!`%`_idx.0])}
  ;; test.spectec:5813.1-5813.100
  def $allocexport{moduleinst : moduleinst, name : name, x : idx}(moduleinst, EXPORT_export(name, FUNC_externidx(x))) = {NAME name, ADDR FUNC_externaddr(moduleinst.FUNCS_moduleinst[x!`%`_idx.0])}

;; test.spectec:5815.1-5815.104
def $allocexports(moduleinst : moduleinst, export*) : exportinst*
  ;; test.spectec:5816.1-5816.75
  def $allocexports{moduleinst : moduleinst, `export*` : export*}(moduleinst, export*{export <- `export*`}) = $allocexport(moduleinst, export)*{export <- `export*`}

;; test.spectec:5819.1-5819.88
def $allocmodule(store : store, module : module, externaddr*, val*, ref*, ref**) : (store, moduleinst)
  ;; test.spectec:5820.1-5859.6
  def $allocmodule{s : store, module : module, `externaddr*` : externaddr*, `val_G*` : val*, `ref_T*` : ref*, `ref_E**` : ref**, s_7 : store, moduleinst : moduleinst, `type*` : type*, `import*` : import*, `tag*` : tag*, `global*` : global*, `mem*` : mem*, `table*` : table*, `func*` : func*, `data*` : data*, `elem*` : elem*, `start?` : start?, `export*` : export*, `tagtype*` : tagtype*, `expr_G*` : expr*, `globaltype*` : globaltype*, `memtype*` : memtype*, `expr_T*` : expr*, `tabletype*` : tabletype*, `expr_F*` : expr*, `local**` : local**, `x*` : idx*, `byte**` : byte**, `datamode*` : datamode*, `elemmode*` : elemmode*, `elemtype*` : elemtype*, `expr_E**` : expr**, `aa_I*` : tagaddr*, `ga_I*` : globaladdr*, `ma_I*` : memaddr*, `ta_I*` : tableaddr*, `fa_I*` : funcaddr*, `dt*` : deftype*, `fa*` : nat*, s_1 : store, `aa*` : tagaddr*, s_2 : store, `ga*` : globaladdr*, s_3 : store, `ma*` : memaddr*, s_4 : store, `ta*` : tableaddr*, s_5 : store, `da*` : dataaddr*, s_6 : store, `ea*` : elemaddr*, `xi*` : exportinst*}(s, module, externaddr*{externaddr <- `externaddr*`}, val_G*{val_G <- `val_G*`}, ref_T*{ref_T <- `ref_T*`}, ref_E*{ref_E <- `ref_E*`}*{`ref_E*` <- `ref_E**`}) = (s_7, moduleinst)
    -- if (module = MODULE_module(`%`_list(type*{type <- `type*`}), `%`_list(import*{import <- `import*`}), `%`_list(tag*{tag <- `tag*`}), `%`_list(global*{global <- `global*`}), `%`_list(mem*{mem <- `mem*`}), `%`_list(table*{table <- `table*`}), `%`_list(func*{func <- `func*`}), `%`_list(data*{data <- `data*`}), `%`_list(elem*{elem <- `elem*`}), start?{start <- `start?`}, `%`_list(export*{export <- `export*`})))
    -- if (tag*{tag <- `tag*`} = TAG_tag(tagtype)*{tagtype <- `tagtype*`})
    -- if (global*{global <- `global*`} = GLOBAL_global(globaltype, expr_G)*{expr_G <- `expr_G*`, globaltype <- `globaltype*`})
    -- if (mem*{mem <- `mem*`} = MEMORY_mem(memtype)*{memtype <- `memtype*`})
    -- if (table*{table <- `table*`} = TABLE_table(tabletype, expr_T)*{expr_T <- `expr_T*`, tabletype <- `tabletype*`})
    -- if (func*{func <- `func*`} = FUNC_func(x, local*{local <- `local*`}, expr_F)*{expr_F <- `expr_F*`, `local*` <- `local**`, x <- `x*`})
    -- if (data*{data <- `data*`} = DATA_data(byte*{byte <- `byte*`}, datamode)*{`byte*` <- `byte**`, datamode <- `datamode*`})
    -- if (elem*{elem <- `elem*`} = ELEM_elem(elemtype, expr_E*{expr_E <- `expr_E*`}, elemmode)*{elemmode <- `elemmode*`, elemtype <- `elemtype*`, `expr_E*` <- `expr_E**`})
    -- if (aa_I*{aa_I <- `aa_I*`} = $tagsxa(externaddr*{externaddr <- `externaddr*`}))
    -- if (ga_I*{ga_I <- `ga_I*`} = $globalsxa(externaddr*{externaddr <- `externaddr*`}))
    -- if (ma_I*{ma_I <- `ma_I*`} = $memsxa(externaddr*{externaddr <- `externaddr*`}))
    -- if (ta_I*{ta_I <- `ta_I*`} = $tablesxa(externaddr*{externaddr <- `externaddr*`}))
    -- if (fa_I*{fa_I <- `fa_I*`} = $funcsxa(externaddr*{externaddr <- `externaddr*`}))
    -- if (dt*{dt <- `dt*`} = $alloctypes(type*{type <- `type*`}))
    -- if (fa*{fa <- `fa*`} = (|s.FUNCS_store| + i_F)^(i_F<|func*{func <- `func*`}|){})
    -- if ((s_1, aa*{aa <- `aa*`}) = $alloctags(s, $subst_all_tagtype(tagtype, (dt : deftype <: typeuse)*{dt <- `dt*`})*{tagtype <- `tagtype*`}))
    -- if ((s_2, ga*{ga <- `ga*`}) = $allocglobals(s_1, $subst_all_globaltype(globaltype, (dt : deftype <: typeuse)*{dt <- `dt*`})*{globaltype <- `globaltype*`}, val_G*{val_G <- `val_G*`}))
    -- if ((s_3, ma*{ma <- `ma*`}) = $allocmems(s_2, $subst_all_memtype(memtype, (dt : deftype <: typeuse)*{dt <- `dt*`})*{memtype <- `memtype*`}))
    -- if ((s_4, ta*{ta <- `ta*`}) = $alloctables(s_3, $subst_all_tabletype(tabletype, (dt : deftype <: typeuse)*{dt <- `dt*`})*{tabletype <- `tabletype*`}, ref_T*{ref_T <- `ref_T*`}))
    -- if ((s_5, da*{da <- `da*`}) = $allocdatas(s_4, OK_datatype^|data*{data <- `data*`}|{}, byte*{byte <- `byte*`}*{`byte*` <- `byte**`}))
    -- if ((s_6, ea*{ea <- `ea*`}) = $allocelems(s_5, $subst_all_reftype(elemtype, (dt : deftype <: typeuse)*{dt <- `dt*`})*{elemtype <- `elemtype*`}, ref_E*{ref_E <- `ref_E*`}*{`ref_E*` <- `ref_E**`}))
    -- if ((s_7, fa*{fa <- `fa*`}) = $allocfuncs(s_6, dt*{dt <- `dt*`}[x!`%`_idx.0]*{x <- `x*`}, FUNC_funccode(x, local*{local <- `local*`}, expr_F)*{expr_F <- `expr_F*`, `local*` <- `local**`, x <- `x*`}, moduleinst^|func*{func <- `func*`}|{}))
    -- if (xi*{xi <- `xi*`} = $allocexports({TYPES [], TAGS aa_I*{aa_I <- `aa_I*`} ++ aa*{aa <- `aa*`}, GLOBALS ga_I*{ga_I <- `ga_I*`} ++ ga*{ga <- `ga*`}, MEMS ma_I*{ma_I <- `ma_I*`} ++ ma*{ma <- `ma*`}, TABLES ta_I*{ta_I <- `ta_I*`} ++ ta*{ta <- `ta*`}, FUNCS fa_I*{fa_I <- `fa_I*`} ++ fa*{fa <- `fa*`}, DATAS [], ELEMS [], EXPORTS []}, export*{export <- `export*`}))
    -- if (moduleinst = {TYPES dt*{dt <- `dt*`}, TAGS aa_I*{aa_I <- `aa_I*`} ++ aa*{aa <- `aa*`}, GLOBALS ga_I*{ga_I <- `ga_I*`} ++ ga*{ga <- `ga*`}, MEMS ma_I*{ma_I <- `ma_I*`} ++ ma*{ma <- `ma*`}, TABLES ta_I*{ta_I <- `ta_I*`} ++ ta*{ta <- `ta*`}, FUNCS fa_I*{fa_I <- `fa_I*`} ++ fa*{fa <- `fa*`}, DATAS da*{da <- `da*`}, ELEMS ea*{ea <- `ea*`}, EXPORTS xi*{xi <- `xi*`}})

;; test.spectec:5864.1-5864.38
def $rundata_(dataidx : dataidx, data : data) : instr*
  ;; test.spectec:5865.1-5865.43
  def $rundata_{x : idx, n : n, `b*` : byte*}(x, DATA_data(b^n{b <- `b*`}, PASSIVE_datamode)) = []
  ;; test.spectec:5866.1-5867.69
  def $rundata_{x : idx, n : n, `b*` : byte*, y : idx, `instr*` : instr*}(x, DATA_data(b^n{b <- `b*`}, ACTIVE_datamode(y, instr*{instr <- `instr*`}))) = instr*{instr <- `instr*`} ++ [CONST_instr(I32_numtype, `%`_num_(0)) CONST_instr(I32_numtype, `%`_num_(n)) `MEMORY.INIT`_instr(y, x) `DATA.DROP`_instr(x)]

;; test.spectec:5869.1-5869.38
def $runelem_(elemidx : elemidx, elem : elem) : instr*
  ;; test.spectec:5870.1-5870.46
  def $runelem_{x : idx, rt : reftype, n : n, `e*` : expr*}(x, ELEM_elem(rt, e^n{e <- `e*`}, PASSIVE_elemmode)) = []
  ;; test.spectec:5871.1-5871.56
  def $runelem_{x : idx, rt : reftype, n : n, `e*` : expr*}(x, ELEM_elem(rt, e^n{e <- `e*`}, DECLARE_elemmode)) = [`ELEM.DROP`_instr(x)]
  ;; test.spectec:5872.1-5873.68
  def $runelem_{x : idx, rt : reftype, n : n, `e*` : expr*, y : idx, `instr*` : instr*}(x, ELEM_elem(rt, e^n{e <- `e*`}, ACTIVE_elemmode(y, instr*{instr <- `instr*`}))) = instr*{instr <- `instr*`} ++ [CONST_instr(I32_numtype, `%`_num_(0)) CONST_instr(I32_numtype, `%`_num_(n)) `TABLE.INIT`_instr(y, x) `ELEM.DROP`_instr(x)]

;; test.spectec:5876.1-5876.92
rec {

;; test.spectec:5876.1-5876.92
def $evalexprs(state : state, expr*) : (state, ref*)
  ;; test.spectec:5877.1-5877.34
  def $evalexprs{z : state}(z, []) = (z, [])
  ;; test.spectec:5878.1-5881.46
  def $evalexprs{z : state, expr : expr, `expr'*` : expr*, z'' : state, ref : ref, `ref'*` : ref*, z' : state}(z, [expr] ++ expr'*{expr' <- `expr'*`}) = (z'', [ref] ++ ref'*{ref' <- `ref'*`})
    -- Eval_expr: `%;%~>*%;%`(z, expr, z', [(ref : ref <: val)])
    -- if ((z'', ref'*{ref' <- `ref'*`}) = $evalexprs(z', expr'*{expr' <- `expr'*`}))
}

;; test.spectec:5883.1-5883.96
rec {

;; test.spectec:5883.1-5883.96
def $evalexprss(state : state, expr**) : (state, ref**)
  ;; test.spectec:5884.1-5884.35
  def $evalexprss{z : state}(z, []) = (z, [])
  ;; test.spectec:5885.1-5888.49
  def $evalexprss{z : state, `expr*` : expr*, `expr'**` : expr**, z'' : state, `ref*` : ref*, `ref'**` : ref**, z' : state}(z, [expr*{expr <- `expr*`}] ++ expr'*{expr' <- `expr'*`}*{`expr'*` <- `expr'**`}) = (z'', [ref*{ref <- `ref*`}] ++ ref'*{ref' <- `ref'*`}*{`ref'*` <- `ref'**`})
    -- if ((z', ref*{ref <- `ref*`}) = $evalexprs(z, expr*{expr <- `expr*`}))
    -- if ((z'', ref'*{ref' <- `ref'*`}*{`ref'*` <- `ref'**`}) = $evalexprss(z', expr'*{expr' <- `expr'*`}*{`expr'*` <- `expr'**`}))
}

;; test.spectec:5890.1-5890.111
rec {

;; test.spectec:5890.1-5890.111
def $evalglobals(state : state, globaltype*, expr*) : (state, val*)
  ;; test.spectec:5891.1-5891.41
  def $evalglobals{z : state}(z, [], []) = (z, [])
  ;; test.spectec:5892.1-5897.82
  def $evalglobals{z : state, gt : globaltype, `gt'*` : globaltype*, expr : expr, `expr'*` : expr*, z'' : state, val : val, `val'*` : val*, z' : state, s : store, f : frame, s' : store, a : addr}(z, [gt] ++ gt'*{gt' <- `gt'*`}, [expr] ++ expr'*{expr' <- `expr'*`}) = (z'', [val] ++ val'*{val' <- `val'*`})
    -- Eval_expr: `%;%~>*%;%`(z, expr, z', [val])
    -- if (z' = `%;%`_state(s, f))
    -- if ((s', a) = $allocglobal(s, gt, val))
    -- if ((z'', val'*{val' <- `val'*`}) = $evalglobals(`%;%`_state(s', f[MODULE_frame.GLOBALS_moduleinst =++ [a]]), gt'*{gt' <- `gt'*`}, expr'*{expr' <- `expr'*`}))
}

;; test.spectec:5899.1-5899.54
def $instantiate(store : store, module : module, externaddr*) : config
  ;; test.spectec:5900.1-5925.29
  def $instantiate{s : store, module : module, `externaddr*` : externaddr*, s'''' : store, moduleinst : moduleinst, `instr_E*` : instr*, `instr_D*` : instr*, `instr_S?` : instr?, `xt_I*` : externtype*, `xt_E*` : externtype*, `type*` : type*, `import*` : import*, `tag*` : tag*, `global*` : global*, `mem*` : mem*, `table*` : table*, `func*` : func*, `data*` : data*, `elem*` : elem*, `start?` : start?, `export*` : export*, `expr_G*` : expr*, `globaltype*` : globaltype*, `expr_T*` : expr*, `tabletype*` : tabletype*, `byte**` : byte**, `datamode*` : datamode*, `elemmode*` : elemmode*, `expr_E**` : expr**, `reftype*` : reftype*, `x?` : idx?, moduleinst_0 : moduleinst, z : state, z' : state, `val_G*` : val*, z'' : state, `ref_T*` : ref*, z''' : state, `ref_E**` : ref**, s''' : store, f : frame, i_D : nat, i_E : nat}(s, module, externaddr*{externaddr <- `externaddr*`}) = `%;%`_config(`%;%`_state(s'''', {LOCALS [], MODULE moduleinst}), instr_E*{instr_E <- `instr_E*`} ++ instr_D*{instr_D <- `instr_D*`} ++ lift(instr_S?{instr_S <- `instr_S?`}))
    -- Module_ok: `|-%:%`(module, `%->%`_moduletype(xt_I*{xt_I <- `xt_I*`}, xt_E*{xt_E <- `xt_E*`}))
    -- (Externaddr_ok: `%|-%:%`(s, externaddr, xt_I))*{externaddr <- `externaddr*`, xt_I <- `xt_I*`}
    -- if (module = MODULE_module(`%`_list(type*{type <- `type*`}), `%`_list(import*{import <- `import*`}), `%`_list(tag*{tag <- `tag*`}), `%`_list(global*{global <- `global*`}), `%`_list(mem*{mem <- `mem*`}), `%`_list(table*{table <- `table*`}), `%`_list(func*{func <- `func*`}), `%`_list(data*{data <- `data*`}), `%`_list(elem*{elem <- `elem*`}), start?{start <- `start?`}, `%`_list(export*{export <- `export*`})))
    -- if (global*{global <- `global*`} = GLOBAL_global(globaltype, expr_G)*{expr_G <- `expr_G*`, globaltype <- `globaltype*`})
    -- if (table*{table <- `table*`} = TABLE_table(tabletype, expr_T)*{expr_T <- `expr_T*`, tabletype <- `tabletype*`})
    -- if (data*{data <- `data*`} = DATA_data(byte*{byte <- `byte*`}, datamode)*{`byte*` <- `byte**`, datamode <- `datamode*`})
    -- if (elem*{elem <- `elem*`} = ELEM_elem(reftype, expr_E*{expr_E <- `expr_E*`}, elemmode)*{elemmode <- `elemmode*`, `expr_E*` <- `expr_E**`, reftype <- `reftype*`})
    -- if (start?{start <- `start?`} = START_start(x)?{x <- `x?`})
    -- if (moduleinst_0 = {TYPES $alloctypes(type*{type <- `type*`}), TAGS [], GLOBALS $globalsxa(externaddr*{externaddr <- `externaddr*`}), MEMS [], TABLES [], FUNCS $funcsxa(externaddr*{externaddr <- `externaddr*`}) ++ (|s.FUNCS_store| + i_F)^(i_F<|func*{func <- `func*`}|){}, DATAS [], ELEMS [], EXPORTS []})
    -- if (z = `%;%`_state(s, {LOCALS [], MODULE moduleinst_0}))
    -- if ((z', val_G*{val_G <- `val_G*`}) = $evalglobals(z, globaltype*{globaltype <- `globaltype*`}, expr_G*{expr_G <- `expr_G*`}))
    -- if ((z'', ref_T*{ref_T <- `ref_T*`}) = $evalexprs(z', expr_T*{expr_T <- `expr_T*`}))
    -- if ((z''', ref_E*{ref_E <- `ref_E*`}*{`ref_E*` <- `ref_E**`}) = $evalexprss(z'', expr_E*{expr_E <- `expr_E*`}*{`expr_E*` <- `expr_E**`}))
    -- if (z''' = `%;%`_state(s''', f))
    -- if ((s'''', moduleinst) = $allocmodule(s''', module, externaddr*{externaddr <- `externaddr*`}, val_G*{val_G <- `val_G*`}, ref_T*{ref_T <- `ref_T*`}, ref_E*{ref_E <- `ref_E*`}*{`ref_E*` <- `ref_E**`}))
    -- if (instr_D*{instr_D <- `instr_D*`} = $concat_(syntax instr, $rundata_(`%`_dataidx(i_D), data*{data <- `data*`}[i_D])^(i_D<|data*{data <- `data*`}|){}))
    -- if (instr_E*{instr_E <- `instr_E*`} = $concat_(syntax instr, $runelem_(`%`_elemidx(i_E), elem*{elem <- `elem*`}[i_E])^(i_E<|elem*{elem <- `elem*`}|){}))
    -- if (instr_S?{instr_S <- `instr_S?`} = CALL_instr(x)?{x <- `x?`})

;; test.spectec:5930.1-5930.44
def $invoke(store : store, funcaddr : funcaddr, val*) : config
  ;; test.spectec:5931.1-5934.31
  def $invoke{s : store, funcaddr : funcaddr, `val*` : val*, `t_1*` : valtype*, `t_2*` : valtype*}(s, funcaddr, val*{val <- `val*`}) = `%;%`_config(`%;%`_state(s, {LOCALS [], MODULE {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], EXPORTS []}}), (val : val <: instr)*{val <- `val*`} ++ [`REF.FUNC_ADDR`_instr(funcaddr) CALL_REF_instr((s.FUNCS_store[funcaddr].TYPE_funcinst : deftype <: typeuse))])
    -- Expand: `%~~%`(s.FUNCS_store[funcaddr].TYPE_funcinst, `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (Val_ok: `%|-%:%`(s, val, t_1))*{t_1 <- `t_1*`, val <- `val*`}

;; test.spectec:6172.1-6172.31
syntax castop = (null?, null?)

;; test.spectec:6252.1-6252.35
syntax memidxop = (memidx, memarg)

;; test.spectec:7064.1-7064.43
syntax startopt = start*

;; test.spectec:7099.1-7099.46
syntax code = (local*, expr)

;; test.spectec:7131.1-7131.33
syntax nopt = u32*

;; test.spectec:7314.1-7314.30
def $ieee_(N : N, rat : rat) : fNmag(N)

;; test.spectec:7396.1-7409.4
syntax idctxt = 
{
  TYPES name?*,
  TAGS name?*,
  GLOBALS name?*,
  MEMS name?*,
  TABLES name?*,
  FUNCS name?*,
  DATAS name?*,
  ELEMS name?*,
  LOCALS name?*,
  LABELS name?*,
  FIELDS name?**,
  TYPEDEFS deftype?*
}

;; test.spectec:7411.1-7411.18
syntax I = idctxt

;; test.spectec:7413.1-7413.56
rec {

;; test.spectec:7413.1-7413.56
def $concat_idctxt(idctxt*) : idctxt
  ;; test.spectec:7414.1-7414.29
  def $concat_idctxt([]) = {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []}
  ;; test.spectec:7415.1-7415.53
  def $concat_idctxt{I : I, `I'*` : I*}([I] ++ I'*{I' <- `I'*`}) = I +++ $concat_idctxt(I'*{I' <- `I'*`})
}

;; test.spectec:7418.1-7418.35
relation Idctxt_ok: `|-%:OK`(idctxt)
  ;; test.spectec:7420.1-7433.27
  rule _{I : I, `field**` : char**}:
    `|-%:OK`(I)
    -- if $disjoint_(syntax name, $concatopt_(syntax name, I.TYPES_I))
    -- if $disjoint_(syntax name, $concatopt_(syntax name, I.TAGS_I))
    -- if $disjoint_(syntax name, $concatopt_(syntax name, I.GLOBALS_I))
    -- if $disjoint_(syntax name, $concatopt_(syntax name, I.MEMS_I))
    -- if $disjoint_(syntax name, $concatopt_(syntax name, I.TABLES_I))
    -- if $disjoint_(syntax name, $concatopt_(syntax name, I.FUNCS_I))
    -- if $disjoint_(syntax name, $concatopt_(syntax name, I.DATAS_I))
    -- if $disjoint_(syntax name, $concatopt_(syntax name, I.ELEMS_I))
    -- if $disjoint_(syntax name, $concatopt_(syntax name, I.LOCALS_I))
    -- if $disjoint_(syntax name, $concatopt_(syntax name, I.LABELS_I))
    -- (if $disjoint_(syntax name, $concatopt_(syntax name, [?(`%`_name(field*{field <- `field*`}))])))*{`field*` <- `field**`}
    -- if ([?(`%`_name(field*{field <- `field*`}))*{`field*` <- `field**`}] = I.FIELDS_I)

;; test.spectec:8845.1-8845.31
def $dots : ()

;; test.spectec:8930.1-8931.83
syntax decl = 
  | TYPE(rectype : rectype)
  | IMPORT(name : name, name : name, externtype : externtype)
  | TAG(tagtype : tagtype)
  | GLOBAL(globaltype : globaltype, expr : expr)
  | MEMORY(memtype : memtype)
  | TABLE(tabletype : tabletype, expr : expr)
  | FUNC(typeidx : typeidx, `local*` : local*, expr : expr)
  | DATA(`byte*` : byte*, datamode : datamode)
  | ELEM(reftype : reftype, `expr*` : expr*, elemmode : elemmode)
  | START(funcidx : funcidx)
  | EXPORT(name : name, externidx : externidx)

;; test.spectec:8933.1-8933.76
rec {

;; test.spectec:8933.1-8933.76
def $typesd(decl*) : type*
  ;; test.spectec:8945.1-8945.23
  def $typesd([]) = []
  ;; test.spectec:8946.1-8946.48
  def $typesd{type : type, `decl'*` : decl*}([(type : type <: decl)] ++ decl'*{decl' <- `decl'*`}) = [type] ++ $typesd(decl'*{decl' <- `decl'*`})
  ;; test.spectec:8947.1-8947.57
  def $typesd{decl : decl, `decl'*` : decl*}([decl] ++ decl'*{decl' <- `decl'*`}) = $typesd(decl'*{decl' <- `decl'*`})
}

;; test.spectec:8934.1-8934.78
rec {

;; test.spectec:8934.1-8934.78
def $importsd(decl*) : import*
  ;; test.spectec:8949.1-8949.25
  def $importsd([]) = []
  ;; test.spectec:8950.1-8950.56
  def $importsd{import : import, `decl'*` : decl*}([(import : import <: decl)] ++ decl'*{decl' <- `decl'*`}) = [import] ++ $importsd(decl'*{decl' <- `decl'*`})
  ;; test.spectec:8951.1-8951.61
  def $importsd{decl : decl, `decl'*` : decl*}([decl] ++ decl'*{decl' <- `decl'*`}) = $importsd(decl'*{decl' <- `decl'*`})
}

;; test.spectec:8935.1-8935.75
rec {

;; test.spectec:8935.1-8935.75
def $tagsd(decl*) : tag*
  ;; test.spectec:8953.1-8953.22
  def $tagsd([]) = []
  ;; test.spectec:8954.1-8954.44
  def $tagsd{tag : tag, `decl'*` : decl*}([(tag : tag <: decl)] ++ decl'*{decl' <- `decl'*`}) = [tag] ++ $tagsd(decl'*{decl' <- `decl'*`})
  ;; test.spectec:8955.1-8955.55
  def $tagsd{decl : decl, `decl'*` : decl*}([decl] ++ decl'*{decl' <- `decl'*`}) = $tagsd(decl'*{decl' <- `decl'*`})
}

;; test.spectec:8936.1-8936.78
rec {

;; test.spectec:8936.1-8936.78
def $globalsd(decl*) : global*
  ;; test.spectec:8957.1-8957.25
  def $globalsd([]) = []
  ;; test.spectec:8958.1-8958.56
  def $globalsd{global : global, `decl'*` : decl*}([(global : global <: decl)] ++ decl'*{decl' <- `decl'*`}) = [global] ++ $globalsd(decl'*{decl' <- `decl'*`})
  ;; test.spectec:8959.1-8959.61
  def $globalsd{decl : decl, `decl'*` : decl*}([decl] ++ decl'*{decl' <- `decl'*`}) = $globalsd(decl'*{decl' <- `decl'*`})
}

;; test.spectec:8937.1-8937.75
rec {

;; test.spectec:8937.1-8937.75
def $memsd(decl*) : mem*
  ;; test.spectec:8961.1-8961.22
  def $memsd([]) = []
  ;; test.spectec:8962.1-8962.44
  def $memsd{mem : mem, `decl'*` : decl*}([(mem : mem <: decl)] ++ decl'*{decl' <- `decl'*`}) = [mem] ++ $memsd(decl'*{decl' <- `decl'*`})
  ;; test.spectec:8963.1-8963.55
  def $memsd{decl : decl, `decl'*` : decl*}([decl] ++ decl'*{decl' <- `decl'*`}) = $memsd(decl'*{decl' <- `decl'*`})
}

;; test.spectec:8938.1-8938.77
rec {

;; test.spectec:8938.1-8938.77
def $tablesd(decl*) : table*
  ;; test.spectec:8965.1-8965.24
  def $tablesd([]) = []
  ;; test.spectec:8966.1-8966.52
  def $tablesd{table : table, `decl'*` : decl*}([(table : table <: decl)] ++ decl'*{decl' <- `decl'*`}) = [table] ++ $tablesd(decl'*{decl' <- `decl'*`})
  ;; test.spectec:8967.1-8967.59
  def $tablesd{decl : decl, `decl'*` : decl*}([decl] ++ decl'*{decl' <- `decl'*`}) = $tablesd(decl'*{decl' <- `decl'*`})
}

;; test.spectec:8939.1-8939.76
rec {

;; test.spectec:8939.1-8939.76
def $funcsd(decl*) : func*
  ;; test.spectec:8969.1-8969.23
  def $funcsd([]) = []
  ;; test.spectec:8970.1-8970.48
  def $funcsd{func : func, `decl'*` : decl*}([(func : func <: decl)] ++ decl'*{decl' <- `decl'*`}) = [func] ++ $funcsd(decl'*{decl' <- `decl'*`})
  ;; test.spectec:8971.1-8971.57
  def $funcsd{decl : decl, `decl'*` : decl*}([decl] ++ decl'*{decl' <- `decl'*`}) = $funcsd(decl'*{decl' <- `decl'*`})
}

;; test.spectec:8940.1-8940.76
rec {

;; test.spectec:8940.1-8940.76
def $datasd(decl*) : data*
  ;; test.spectec:8973.1-8973.23
  def $datasd([]) = []
  ;; test.spectec:8974.1-8974.48
  def $datasd{data : data, `decl'*` : decl*}([(data : data <: decl)] ++ decl'*{decl' <- `decl'*`}) = [data] ++ $datasd(decl'*{decl' <- `decl'*`})
  ;; test.spectec:8975.1-8975.57
  def $datasd{decl : decl, `decl'*` : decl*}([decl] ++ decl'*{decl' <- `decl'*`}) = $datasd(decl'*{decl' <- `decl'*`})
}

;; test.spectec:8941.1-8941.76
rec {

;; test.spectec:8941.1-8941.76
def $elemsd(decl*) : elem*
  ;; test.spectec:8977.1-8977.23
  def $elemsd([]) = []
  ;; test.spectec:8978.1-8978.48
  def $elemsd{elem : elem, `decl'*` : decl*}([(elem : elem <: decl)] ++ decl'*{decl' <- `decl'*`}) = [elem] ++ $elemsd(decl'*{decl' <- `decl'*`})
  ;; test.spectec:8979.1-8979.57
  def $elemsd{decl : decl, `decl'*` : decl*}([decl] ++ decl'*{decl' <- `decl'*`}) = $elemsd(decl'*{decl' <- `decl'*`})
}

;; test.spectec:8942.1-8942.77
rec {

;; test.spectec:8942.1-8942.77
def $startsd(decl*) : start*
  ;; test.spectec:8981.1-8981.24
  def $startsd([]) = []
  ;; test.spectec:8982.1-8982.52
  def $startsd{start : start, `decl'*` : decl*}([(start : start <: decl)] ++ decl'*{decl' <- `decl'*`}) = [start] ++ $startsd(decl'*{decl' <- `decl'*`})
  ;; test.spectec:8983.1-8983.59
  def $startsd{decl : decl, `decl'*` : decl*}([decl] ++ decl'*{decl' <- `decl'*`}) = $startsd(decl'*{decl' <- `decl'*`})
}

;; test.spectec:8943.1-8943.78
rec {

;; test.spectec:8943.1-8943.78
def $exportsd(decl*) : export*
  ;; test.spectec:8985.1-8985.25
  def $exportsd([]) = []
  ;; test.spectec:8986.1-8986.56
  def $exportsd{export : export, `decl'*` : decl*}([(export : export <: decl)] ++ decl'*{decl' <- `decl'*`}) = [export] ++ $exportsd(decl'*{decl' <- `decl'*`})
  ;; test.spectec:8987.1-8987.61
  def $exportsd{decl : decl, `decl'*` : decl*}([decl] ++ decl'*{decl' <- `decl'*`}) = $exportsd(decl'*{decl' <- `decl'*`})
}

;; test.spectec:8989.1-8989.27
def $ordered(decl*) : bool
  ;; test.spectec:8990.1-8990.57
  def $ordered{`decl*` : decl*}(decl*{decl <- `decl*`}) = true
    -- if ($importsd(decl*{decl <- `decl*`}) = [])
  ;; test.spectec:8991.1-8994.52
  def $ordered{`decl_1*` : decl*, import : import, `decl_2*` : decl*}(decl_1*{decl_1 <- `decl_1*`} ++ [(import : import <: decl)] ++ decl_2*{decl_2 <- `decl_2*`}) = (((((($importsd(decl_1*{decl_1 <- `decl_1*`}) = []) /\ ($tagsd(decl_1*{decl_1 <- `decl_1*`}) = [])) /\ ($globalsd(decl_1*{decl_1 <- `decl_1*`}) = [])) /\ ($memsd(decl_1*{decl_1 <- `decl_1*`}) = [])) /\ ($tablesd(decl_1*{decl_1 <- `decl_1*`}) = [])) /\ ($funcsd(decl_1*{decl_1 <- `decl_1*`}) = []))

;; test.spectec:9036.1-9036.61
relation Context_ok: `|-%:OK`(context)
  ;; test.spectec:9038.1-9068.23
  rule _{C : context, n : n, `dt*` : deftype*, `jt*` : tagtype*, `gt*` : globaltype*, `mt*` : memtype*, `tt*` : tabletype*, `dt_F*` : deftype*, `ok*` : datatype*, `et*` : elemtype*, `lct*` : localtype*, `rt*` : reftype*, `rt'?` : reftype?, `x*` : idx*, m : m, `st*` : subtype*, C_0 : context, `t_1*` : valtype*, `t_2*` : valtype*}:
    `|-%:OK`(C)
    -- if (C = {TYPES dt^n{dt <- `dt*`}, TAGS jt*{jt <- `jt*`}, GLOBALS gt*{gt <- `gt*`}, MEMS mt*{mt <- `mt*`}, TABLES tt*{tt <- `tt*`}, FUNCS dt_F*{dt_F <- `dt_F*`}, DATAS ok*{ok <- `ok*`}, ELEMS et*{et <- `et*`}, LOCALS lct*{lct <- `lct*`}, LABELS [`%`_resulttype((rt : reftype <: valtype)*{rt <- `rt*`})], RETURN ?(`%`_resulttype(lift((rt' : reftype <: valtype)?{rt' <- `rt'?`}))), REFS x*{x <- `x*`}, RECS st^m{st <- `st*`}})
    -- if (C_0 = {TYPES dt^n{dt <- `dt*`}, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
    -- (Deftype_ok: `%|-%:OK`({TYPES dt^n{dt <- `dt*`}[0 : i], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, dt))^(i<n){dt <- `dt*`}
    -- (Subtype_ok2: `%|-%:%`({TYPES dt^n{dt <- `dt*`}, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS st^m{st <- `st*`}}, st, OK_oktypenat(i)))^(i<m){st <- `st*`}
    -- (Tagtype_ok: `%|-%:OK`(C_0, jt))*{jt <- `jt*`}
    -- (Globaltype_ok: `%|-%:OK`(C_0, gt))*{gt <- `gt*`}
    -- (Memtype_ok: `%|-%:OK`(C_0, mt))*{mt <- `mt*`}
    -- (Tabletype_ok: `%|-%:OK`(C_0, tt))*{tt <- `tt*`}
    -- (Deftype_ok: `%|-%:OK`(C_0, dt_F))*{dt_F <- `dt_F*`}
    -- (Expand: `%~~%`(dt_F, `FUNC%->%`_comptype(`%`_resulttype([t_1]), `%`_resulttype([t_2]))))*{dt_F <- `dt_F*`, t_1 <- `t_1*`, t_2 <- `t_2*`}
    -- (Reftype_ok: `%|-%:OK`(C_0, et))*{et <- `et*`}
    -- (Localtype_ok: `%|-%:OK`(C_0, lct))*{lct <- `lct*`}
    -- (Resulttype_ok: `%|-%:OK`(C_0, `%`_resulttype([(rt : reftype <: valtype)])))*{rt <- `rt*`}
    -- (Resulttype_ok: `%|-%:OK`(C_0, `%`_resulttype([(rt' : reftype <: valtype)])))?{rt' <- `rt'?`}
    -- (if (x!`%`_idx.0 < |dt_F*{dt_F <- `dt_F*`}|))*{x <- `x*`}

;; test.spectec:9399.1-9399.48
relation Localval_ok: `%|-%:%`(store, val?, localtype)
  ;; test.spectec:9404.1-9406.26
  rule set{s : store, val : val, t : valtype}:
    `%|-%:%`(s, ?(val), `%%`_localtype(SET_init, t))
    -- Val_ok: `%|-%:%`(s, val, t)

  ;; test.spectec:9408.1-9409.23
  rule unset{s : store}:
    `%|-%:%`(s, ?(), `%%`_localtype(UNSET_init, BOT_valtype))

;; test.spectec:9152.1-9152.51
relation Datainst_ok: `%|-%:%`(store, datainst, datatype)
  ;; test.spectec:9187.1-9188.23
  rule _{s : store, `b*` : byte*}:
    `%|-%:%`(s, {BYTES b*{b <- `b*`}}, OK_datatype)

;; test.spectec:9153.1-9153.51
relation Eleminst_ok: `%|-%:%`(store, eleminst, elemtype)
  ;; test.spectec:9190.1-9193.30
  rule _{s : store, rt : reftype, `ref*` : ref*}:
    `%|-%:%`(s, {TYPE rt, REFS ref*{ref <- `ref*`}}, rt)
    -- Reftype_ok: `%|-%:OK`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, rt)
    -- (Ref_ok: `%|-%:%`(s, ref, rt))*{ref <- `ref*`}

;; test.spectec:9154.1-9154.49
relation Exportinst_ok: `%|-%:OK`(store, exportinst)
  ;; test.spectec:9195.1-9197.33
  rule _{s : store, nm : name, xa : externaddr, xt : externtype}:
    `%|-%:OK`(s, {NAME nm, ADDR xa})
    -- Externaddr_ok: `%|-%:%`(s, xa, xt)

;; test.spectec:9219.1-9219.54
relation Moduleinst_ok: `%|-%:%`(store, moduleinst, context)
  ;; test.spectec:9221.1-9257.117
  rule _{s : store, `deftype*` : deftype*, `tagaddr*` : tagaddr*, `globaladdr*` : globaladdr*, `memaddr*` : memaddr*, `tableaddr*` : tableaddr*, `funcaddr*` : funcaddr*, `dataaddr*` : dataaddr*, `elemaddr*` : elemaddr*, `exportinst*` : exportinst*, `tagtype*` : tagtype*, `globaltype*` : globaltype*, `memtype*` : memtype*, `tabletype*` : tabletype*, `deftype_F*` : deftype*, `datatype*` : datatype*, `elemtype*` : elemtype*, `subtype*` : subtype*}:
    `%|-%:%`(s, {TYPES deftype*{deftype <- `deftype*`}, TAGS tagaddr*{tagaddr <- `tagaddr*`}, GLOBALS globaladdr*{globaladdr <- `globaladdr*`}, MEMS memaddr*{memaddr <- `memaddr*`}, TABLES tableaddr*{tableaddr <- `tableaddr*`}, FUNCS funcaddr*{funcaddr <- `funcaddr*`}, DATAS dataaddr*{dataaddr <- `dataaddr*`}, ELEMS elemaddr*{elemaddr <- `elemaddr*`}, EXPORTS exportinst*{exportinst <- `exportinst*`}}, {TYPES deftype*{deftype <- `deftype*`}, TAGS tagtype*{tagtype <- `tagtype*`}, GLOBALS globaltype*{globaltype <- `globaltype*`}, MEMS memtype*{memtype <- `memtype*`}, TABLES tabletype*{tabletype <- `tabletype*`}, FUNCS deftype_F*{deftype_F <- `deftype_F*`}, DATAS datatype*{datatype <- `datatype*`}, ELEMS elemtype*{elemtype <- `elemtype*`}, LOCALS [], LABELS [], RETURN ?(), REFS `%`_funcidx(i)^(i<|funcaddr*{funcaddr <- `funcaddr*`}|){}, RECS subtype*{subtype <- `subtype*`}})
    -- (Deftype_ok: `%|-%:OK`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, deftype))*{deftype <- `deftype*`}
    -- (Externaddr_ok: `%|-%:%`(s, TAG_externaddr(tagaddr), TAG_externtype(tagtype)))*{tagaddr <- `tagaddr*`, tagtype <- `tagtype*`}
    -- (Externaddr_ok: `%|-%:%`(s, GLOBAL_externaddr(globaladdr), GLOBAL_externtype(globaltype)))*{globaladdr <- `globaladdr*`, globaltype <- `globaltype*`}
    -- (Externaddr_ok: `%|-%:%`(s, FUNC_externaddr(funcaddr), FUNC_externtype((deftype_F : deftype <: typeuse))))*{deftype_F <- `deftype_F*`, funcaddr <- `funcaddr*`}
    -- (Externaddr_ok: `%|-%:%`(s, MEM_externaddr(memaddr), MEM_externtype(memtype)))*{memaddr <- `memaddr*`, memtype <- `memtype*`}
    -- (Externaddr_ok: `%|-%:%`(s, TABLE_externaddr(tableaddr), TABLE_externtype(tabletype)))*{tableaddr <- `tableaddr*`, tabletype <- `tabletype*`}
    -- (Datainst_ok: `%|-%:%`(s, s.DATAS_store[dataaddr], datatype))*{dataaddr <- `dataaddr*`, datatype <- `datatype*`}
    -- (Eleminst_ok: `%|-%:%`(s, s.ELEMS_store[elemaddr], elemtype))*{elemaddr <- `elemaddr*`, elemtype <- `elemtype*`}
    -- (Exportinst_ok: `%|-%:OK`(s, exportinst))*{exportinst <- `exportinst*`}
    -- if $disjoint_(syntax name, exportinst.NAME_exportinst*{exportinst <- `exportinst*`})
    -- (if (exportinst.ADDR_exportinst <- TAG_externaddr(tagaddr)*{tagaddr <- `tagaddr*`} ++ GLOBAL_externaddr(globaladdr)*{globaladdr <- `globaladdr*`} ++ MEM_externaddr(memaddr)*{memaddr <- `memaddr*`} ++ TABLE_externaddr(tableaddr)*{tableaddr <- `tableaddr*`} ++ FUNC_externaddr(funcaddr)*{funcaddr <- `funcaddr*`}))*{exportinst <- `exportinst*`}

;; test.spectec:9400.1-9400.44
relation Frame_ok: `%|-%:%`(store, frame, context)
  ;; test.spectec:9411.1-9414.37
  rule _{s : store, `val?*` : val?*, moduleinst : moduleinst, C : context, `lct*` : localtype*}:
    `%|-%:%`(s, {LOCALS val?{val <- `val?`}*{`val?` <- `val?*`}, MODULE moduleinst}, C +++ {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS lct*{lct <- `lct*`}, LABELS [], RETURN ?(), REFS [], RECS []})
    -- Moduleinst_ok: `%|-%:%`(s, moduleinst, C)
    -- (Localval_ok: `%|-%:%`(s, val?{val <- `val?`}, lct))*{lct <- `lct*`, `val?` <- `val?*`}

;; test.spectec:9079.1-9084.36
rec {

;; test.spectec:9079.1-9080.36
relation Instr_ok2: `%;%|-%:%`(store, context, instr, instrtype)
  ;; test.spectec:9086.1-9088.46
  rule plain{s : store, C : context, instr : instr, `t_1*` : valtype*, `x*` : idx*, `t_2*` : valtype*}:
    `%;%|-%:%`(s, C, instr, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instr_ok: `%|-%:%`(C, instr, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:9090.1-9092.27
  rule ref{s : store, C : context, ref : ref, rt : reftype}:
    `%;%|-%:%`(s, C, (ref : ref <: instr), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([(rt : reftype <: valtype)])))
    -- Ref_ok: `%|-%:%`(s, ref, rt)

  ;; test.spectec:9094.1-9097.68
  rule label{s : store, C : context, n : n, `instr'*` : instr*, `instr*` : instr*, `t*` : valtype*, `t'*` : valtype*, `x'*` : idx*, `x*` : idx*}:
    `%;%|-%:%`(s, C, `LABEL_%{%}%`_instr(n, instr'*{instr' <- `instr'*`}, instr*{instr <- `instr*`}), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype(t*{t <- `t*`})))
    -- Instrs_ok2: `%;%|-%:%`(s, C, instr'*{instr' <- `instr'*`}, `%->_%%`_instrtype(`%`_resulttype(t'^n{t' <- `t'*`}), x'*{x' <- `x'*`}, `%`_resulttype(t*{t <- `t*`})))
    -- Instrs_ok2: `%;%|-%:%`(s, {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t'^n{t' <- `t'*`})], RETURN ?(), REFS [], RECS []} +++ C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype([]), x*{x <- `x*`}, `%`_resulttype(t*{t <- `t*`})))

  ;; test.spectec:9099.1-9102.53
  rule frame{s : store, C : context, n : n, f : frame, `instr*` : instr*, `t*` : valtype*, C' : context}:
    `%;%|-%:%`(s, C, `FRAME_%{%}%`_instr(n, f, instr*{instr <- `instr*`}), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype(t^n{t <- `t*`})))
    -- Frame_ok: `%|-%:%`(s, f, C')
    -- Expr_ok2: `%;%|-%:%`(s, {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(`%`_resulttype(t^n{t <- `t*`})), REFS [], RECS []} +++ C', instr*{instr <- `instr*`}, `%`_resulttype(t^n{t <- `t*`}))

  ;; test.spectec:9104.1-9107.52
  rule handler{s : store, C : context, n : n, `catch*` : catch*, `instr*` : instr*, `t_1*` : valtype*, `t_2*` : valtype*, `x*` : idx*}:
    `%;%|-%:%`(s, C, `HANDLER_%{%}%`_instr(n, catch*{catch <- `catch*`}, instr*{instr <- `instr*`}), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (Catch_ok: `%|-%:OK`(C, catch))*{catch <- `catch*`}
    -- Instrs_ok2: `%;%|-%:%`(s, C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:9109.1-9111.42
  rule trap{s : store, C : context, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%;%|-%:%`(s, C, TRAP_instr, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

;; test.spectec:9081.1-9082.36
relation Instrs_ok2: `%;%|-%:%`(store, context, instr*, instrtype)
  ;; test.spectec:9114.1-9115.27
  rule empty{s : store, C : context}:
    `%;%|-%:%`(s, C, [], `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([])))

  ;; test.spectec:9117.1-9119.45
  rule instr{s : store, C : context, instr : instr, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%;%|-%:%`(s, C, [instr], `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instr_ok2: `%;%|-%:%`(s, C, instr, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:9121.1-9125.86
  rule seq{s : store, C : context, `instr_1*` : instr*, `instr_2*` : instr*, `t_1*` : valtype*, `x_1*` : idx*, `x_2*` : idx*, `t_3*` : valtype*, `t_2*` : valtype*, `init*` : init*, `t*` : valtype*}:
    `%;%|-%:%`(s, C, instr_1*{instr_1 <- `instr_1*`} ++ instr_2*{instr_2 <- `instr_2*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_1*{x_1 <- `x_1*`} ++ x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_3*{t_3 <- `t_3*`})))
    -- Instrs_ok2: `%;%|-%:%`(s, C, instr_1*{instr_1 <- `instr_1*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_1*{x_1 <- `x_1*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (if (C.LOCALS_context[x_1!`%`_idx.0] = `%%`_localtype(init, t)))*{init <- `init*`, t <- `t*`, x_1 <- `x_1*`}
    -- Instrs_ok2: `%;%|-%:%`(s, $with_locals(C, x_1*{x_1 <- `x_1*`}, `%%`_localtype(SET_init, t)*{t <- `t*`}), instr_2*{instr_2 <- `instr_2*`}, `%->_%%`_instrtype(`%`_resulttype(t_2*{t_2 <- `t_2*`}), x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_3*{t_3 <- `t_3*`})))

  ;; test.spectec:9127.1-9131.33
  rule sub{s : store, C : context, `instr*` : instr*, it' : instrtype, it : instrtype}:
    `%;%|-%:%`(s, C, instr*{instr <- `instr*`}, it')
    -- Instrs_ok2: `%;%|-%:%`(s, C, instr*{instr <- `instr*`}, it)
    -- Instrtype_sub: `%|-%<:%`(C, it, it')
    -- Instrtype_ok: `%|-%:OK`(C, it')

  ;; test.spectec:9134.1-9137.33
  rule frame{s : store, C : context, `instr*` : instr*, `t*` : valtype*, `t_1*` : valtype*, `x*` : idx*, `t_2*` : valtype*}:
    `%;%|-%:%`(s, C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t*{t <- `t*`} ++ t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok2: `%;%|-%:%`(s, C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Resulttype_ok: `%|-%:OK`(C, `%`_resulttype(t*{t <- `t*`}))

;; test.spectec:9083.1-9084.36
relation Expr_ok2: `%;%|-%:%`(store, context, expr, resulttype)
  ;; test.spectec:9140.1-9142.44
  rule _{s : store, C : context, `instr*` : instr*, `t*` : valtype*}:
    `%;%|-%:%`(s, C, instr*{instr <- `instr*`}, `%`_resulttype(t*{t <- `t*`}))
    -- Instrs_ok2: `%;%|-%:%`(s, C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype(t*{t <- `t*`})))
}

;; test.spectec:9147.1-9147.48
relation Taginst_ok: `%|-%:%`(store, taginst, tagtype)
  ;; test.spectec:9159.1-9161.31
  rule _{s : store, jt : tagtype}:
    `%|-%:%`(s, {TYPE jt}, jt)
    -- Tagtype_ok: `%|-%:OK`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, jt)

;; test.spectec:9148.1-9148.57
relation Globalinst_ok: `%|-%:%`(store, globalinst, globaltype)
  ;; test.spectec:9163.1-9166.26
  rule _{s : store, `mut?` : mut?, t : valtype, val : val}:
    `%|-%:%`(s, {TYPE `%%`_globaltype(mut?{mut <- `mut?`}, t), VALUE val}, `%%`_globaltype(mut?{mut <- `mut?`}, t))
    -- Globaltype_ok: `%|-%:OK`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, `%%`_globaltype(mut?{mut <- `mut?`}, t))
    -- Val_ok: `%|-%:%`(s, val, t)

;; test.spectec:9149.1-9149.48
relation Meminst_ok: `%|-%:%`(store, meminst, memtype)
  ;; test.spectec:9168.1-9171.37
  rule _{s : store, at : addrtype, n : n, `m?` : m?, `b*` : byte*}:
    `%|-%:%`(s, {TYPE `%%PAGE`_memtype(at, `[%..%]`_limits(`%`_u64(n), `%`_u64(m)?{m <- `m?`})), BYTES b*{b <- `b*`}}, `%%PAGE`_memtype(at, `[%..%]`_limits(`%`_u64(n), `%`_u64(m)?{m <- `m?`})))
    -- Memtype_ok: `%|-%:OK`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, `%%PAGE`_memtype(at, `[%..%]`_limits(`%`_u64(n), `%`_u64(m)?{m <- `m?`})))
    -- if (|b*{b <- `b*`}| = (n * (64 * $Ki)))

;; test.spectec:9150.1-9150.54
relation Tableinst_ok: `%|-%:%`(store, tableinst, tabletype)
  ;; test.spectec:9173.1-9177.30
  rule _{s : store, at : addrtype, n : n, `m?` : m?, rt : reftype, `ref*` : ref*}:
    `%|-%:%`(s, {TYPE `%%%`_tabletype(at, `[%..%]`_limits(`%`_u64(n), `%`_u64(m)?{m <- `m?`}), rt), REFS ref*{ref <- `ref*`}}, `%%%`_tabletype(at, `[%..%]`_limits(`%`_u64(n), `%`_u64(m)?{m <- `m?`}), rt))
    -- Tabletype_ok: `%|-%:OK`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, `%%%`_tabletype(at, `[%..%]`_limits(`%`_u64(n), `%`_u64(m)?{m <- `m?`}), rt))
    -- if (|ref*{ref <- `ref*`}| = n)
    -- (Ref_ok: `%|-%:%`(s, ref, rt))*{ref <- `ref*`}

;; test.spectec:9151.1-9151.50
relation Funcinst_ok: `%|-%:%`(store, funcinst, deftype)
  ;; test.spectec:9179.1-9185.33
  rule _{s : store, dt : deftype, moduleinst : moduleinst, func : func, C : context, dt' : deftype}:
    `%|-%:%`(s, {TYPE dt, MODULE moduleinst, CODE (func : func <: funccode)}, dt)
    -- Deftype_ok: `%|-%:OK`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, dt)
    -- Moduleinst_ok: `%|-%:%`(s, moduleinst, C)
    -- Func_ok: `%|-%:%`(C, func, dt')
    -- Deftype_sub: `%|-%<:%`(C, dt', dt)

;; test.spectec:9155.1-9155.49
relation Structinst_ok: `%|-%:OK`(store, structinst)
  ;; test.spectec:9200.1-9203.34
  rule _{s : store, dt : deftype, `fv*` : fieldval*, `mut?*` : mut?*, `zt*` : storagetype*}:
    `%|-%:OK`(s, {TYPE dt, FIELDS fv*{fv <- `fv*`}})
    -- Expand: `%~~%`(dt, STRUCT_comptype(`%`_list(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)*{`mut?` <- `mut?*`, zt <- `zt*`})))
    -- (Fieldval_ok: `%|-%:%`(s, fv, zt))*{fv <- `fv*`, zt <- `zt*`}

;; test.spectec:9156.1-9156.47
relation Arrayinst_ok: `%|-%:OK`(store, arrayinst)
  ;; test.spectec:9205.1-9208.34
  rule _{s : store, dt : deftype, `fv*` : fieldval*, `mut?` : mut?, zt : storagetype}:
    `%|-%:OK`(s, {TYPE dt, FIELDS fv*{fv <- `fv*`}})
    -- Expand: `%~~%`(dt, ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- (Fieldval_ok: `%|-%:%`(s, fv, zt))*{fv <- `fv*`}

;; test.spectec:9157.1-9157.43
relation Exninst_ok: `%|-%:OK`(store, exninst)
  ;; test.spectec:9210.1-9214.29
  rule _{s : store, ta : tagaddr, `val*` : val*, dt : deftype, `t*` : valtype*}:
    `%|-%:OK`(s, {TAG ta, FIELDS val*{val <- `val*`}})
    -- if ((dt : deftype <: typeuse) = s.TAGS_store[ta].TYPE_taginst)
    -- Expand: `%~~%`(dt, `FUNC%->%`_comptype(`%`_resulttype(t*{t <- `t*`}), `%`_resulttype([])))
    -- (Val_ok: `%|-%:%`(s, val, t))*{t <- `t*`, val <- `val*`}

;; test.spectec:9288.1-9289.50
rec {

;; test.spectec:9288.1-9289.50
relation ImmutReachable: `%>>_%%`(fieldval, store, fieldval)
  ;; test.spectec:9302.1-9305.35
  rule trans{fv_1 : fieldval, s : store, fv_2 : fieldval, fv' : fieldval}:
    `%>>_%%`(fv_1, s, fv_2)
    -- ImmutReachable: `%>>_%%`(fv_1, s, fv')
    -- ImmutReachable: `%>>_%%`(fv', s, fv_2)

  ;; test.spectec:9307.1-9310.20
  rule `ref.struct`{a : addr, s : store, i : nat, `ft*` : fieldtype*, zt : storagetype}:
    `%>>_%%`(`REF.STRUCT_ADDR`_fieldval(a), s, s.STRUCTS_store[a].FIELDS_structinst[i])
    -- Expand: `%~~%`(s.STRUCTS_store[a].TYPE_structinst, STRUCT_comptype(`%`_list(ft*{ft <- `ft*`})))
    -- if (ft*{ft <- `ft*`}[i] = `%%`_fieldtype(?(), zt))

  ;; test.spectec:9312.1-9314.42
  rule `ref.array`{a : addr, s : store, i : nat, zt : storagetype}:
    `%>>_%%`(`REF.ARRAY_ADDR`_fieldval(a), s, s.ARRAYS_store[a].FIELDS_arrayinst[i])
    -- Expand: `%~~%`(s.ARRAYS_store[a].TYPE_arrayinst, ARRAY_comptype(`%%`_fieldtype(?(), zt)))

  ;; test.spectec:9316.1-9317.44
  rule `ref.exn`{a : addr, s : store, i : nat}:
    `%>>_%%`(`REF.EXN_ADDR`_fieldval(a), s, (s.EXNS_store[a].FIELDS_exninst[i] : val <: fieldval))

  ;; test.spectec:9319.1-9320.28
  rule `ref.extern`{ref : ref, s : store}:
    `%>>_%%`(`REF.EXTERN`_fieldval(ref), s, (ref : ref <: fieldval))
}

;; test.spectec:9295.1-9295.57
def $NotImmutReachable(fieldval : fieldval, store : store, fieldval : fieldval) : bool
  ;; test.spectec:9296.1-9296.80
  def $NotImmutReachable{fv_1 : fieldval, s : store, fv_2 : fieldval}(fv_1, s, fv_2) = false
    -- ImmutReachable: `%>>_%%`(fv_1, s, fv_2)
  ;; test.spectec:9297.1-9297.59
  def $NotImmutReachable{fv_1 : fieldval, s : store, fv_2 : fieldval}(fv_1, s, fv_2) = true
    -- otherwise

;; test.spectec:9290.1-9291.54
relation NotImmutReachable: `~%>>_%%`(fieldval, store, fieldval)
  ;; test.spectec:9299.1-9299.82
  rule _{fv_1 : fieldval, s : store, fv_2 : fieldval}:
    `~%>>_%%`(fv_1, s, fv_2)
    -- if $NotImmutReachable(fv_1, s, fv_2)

;; test.spectec:9262.1-9262.33
relation Store_ok: `|-%:OK`(store)
  ;; test.spectec:9264.1-9285.102
  rule _{s : store, `taginst*` : taginst*, `tagtype*` : tagtype*, `globalinst*` : globalinst*, `globaltype*` : globaltype*, `meminst*` : meminst*, `memtype*` : memtype*, `tableinst*` : tableinst*, `tabletype*` : tabletype*, `deftype*` : deftype*, `funcinst*` : funcinst*, `datainst*` : datainst*, `datatype*` : datatype*, `eleminst*` : eleminst*, `elemtype*` : elemtype*, `structinst*` : structinst*, `arrayinst*` : arrayinst*, `exninst*` : exninst*}:
    `|-%:OK`(s)
    -- (Taginst_ok: `%|-%:%`(s, taginst, tagtype))*{taginst <- `taginst*`, tagtype <- `tagtype*`}
    -- (Globalinst_ok: `%|-%:%`(s, globalinst, globaltype))*{globalinst <- `globalinst*`, globaltype <- `globaltype*`}
    -- (Meminst_ok: `%|-%:%`(s, meminst, memtype))*{meminst <- `meminst*`, memtype <- `memtype*`}
    -- (Tableinst_ok: `%|-%:%`(s, tableinst, tabletype))*{tableinst <- `tableinst*`, tabletype <- `tabletype*`}
    -- (Funcinst_ok: `%|-%:%`(s, funcinst, deftype))*{deftype <- `deftype*`, funcinst <- `funcinst*`}
    -- (Datainst_ok: `%|-%:%`(s, datainst, datatype))*{datainst <- `datainst*`, datatype <- `datatype*`}
    -- (Eleminst_ok: `%|-%:%`(s, eleminst, elemtype))*{eleminst <- `eleminst*`, elemtype <- `elemtype*`}
    -- (Structinst_ok: `%|-%:OK`(s, structinst))*{structinst <- `structinst*`}
    -- (Arrayinst_ok: `%|-%:OK`(s, arrayinst))*{arrayinst <- `arrayinst*`}
    -- (Exninst_ok: `%|-%:OK`(s, exninst))*{exninst <- `exninst*`}
    -- (NotImmutReachable: `~%>>_%%`(`REF.STRUCT_ADDR`_fieldval(a), s, `REF.STRUCT_ADDR`_fieldval(a)))^(a<|structinst*{structinst <- `structinst*`}|){}
    -- (NotImmutReachable: `~%>>_%%`(`REF.ARRAY_ADDR`_fieldval(a), s, `REF.ARRAY_ADDR`_fieldval(a)))^(a<|arrayinst*{arrayinst <- `arrayinst*`}|){}
    -- (NotImmutReachable: `~%>>_%%`(`REF.EXN_ADDR`_fieldval(a), s, `REF.EXN_ADDR`_fieldval(a)))^(a<|exninst*{exninst <- `exninst*`}|){}
    -- if (s = {TAGS taginst*{taginst <- `taginst*`}, GLOBALS globalinst*{globalinst <- `globalinst*`}, MEMS meminst*{meminst <- `meminst*`}, TABLES tableinst*{tableinst <- `tableinst*`}, FUNCS funcinst*{funcinst <- `funcinst*`}, DATAS datainst*{datainst <- `datainst*`}, ELEMS eleminst*{eleminst <- `eleminst*`}, STRUCTS structinst*{structinst <- `structinst*`}, ARRAYS arrayinst*{arrayinst <- `arrayinst*`}, EXNS exninst*{exninst <- `exninst*`}})

;; test.spectec:9325.1-9325.45
relation Extend_taginst: `%<=%`(taginst, taginst)
  ;; test.spectec:9337.1-9338.26
  rule _{jt : tagtype}:
    `%<=%`({TYPE jt}, {TYPE jt})

;; test.spectec:9326.1-9326.54
relation Extend_globalinst: `%<=%`(globalinst, globalinst)
  ;; test.spectec:9340.1-9342.33
  rule _{`mut?` : mut?, t : valtype, val : val, val' : val}:
    `%<=%`({TYPE `%%`_globaltype(mut?{mut <- `mut?`}, t), VALUE val}, {TYPE `%%`_globaltype(mut?{mut <- `mut?`}, t), VALUE val'})
    -- if ((mut?{mut <- `mut?`} = ?(MUT_mut)) \/ (val = val'))

;; test.spectec:9327.1-9327.45
relation Extend_meminst: `%<=%`(meminst, meminst)
  ;; test.spectec:9344.1-9347.22
  rule _{at : addrtype, n : n, `m?` : m?, `b*` : byte*, n' : n, `b'*` : byte*}:
    `%<=%`({TYPE `%%PAGE`_memtype(at, `[%..%]`_limits(`%`_u64(n), `%`_u64(m)?{m <- `m?`})), BYTES b*{b <- `b*`}}, {TYPE `%%PAGE`_memtype(at, `[%..%]`_limits(`%`_u64(n'), `%`_u64(m)?{m <- `m?`})), BYTES b'*{b' <- `b'*`}})
    -- if (n <= n')
    -- if (|b*{b <- `b*`}| <= |b'*{b' <- `b'*`}|)

;; test.spectec:9328.1-9328.51
relation Extend_tableinst: `%<=%`(tableinst, tableinst)
  ;; test.spectec:9349.1-9352.26
  rule _{at : addrtype, n : n, `m?` : m?, rt : reftype, `ref*` : ref*, n' : n, `ref'*` : ref*}:
    `%<=%`({TYPE `%%%`_tabletype(at, `[%..%]`_limits(`%`_u64(n), `%`_u64(m)?{m <- `m?`}), rt), REFS ref*{ref <- `ref*`}}, {TYPE `%%%`_tabletype(at, `[%..%]`_limits(`%`_u64(n'), `%`_u64(m)?{m <- `m?`}), rt), REFS ref'*{ref' <- `ref'*`}})
    -- if (n <= n')
    -- if (|ref*{ref <- `ref*`}| <= |ref'*{ref' <- `ref'*`}|)

;; test.spectec:9329.1-9329.48
relation Extend_funcinst: `%<=%`(funcinst, funcinst)
  ;; test.spectec:9354.1-9355.66
  rule _{dt : deftype, mm : moduleinst, fc : funccode}:
    `%<=%`({TYPE dt, MODULE mm, CODE fc}, {TYPE dt, MODULE mm, CODE fc})

;; test.spectec:9330.1-9330.48
relation Extend_datainst: `%<=%`(datainst, datainst)
  ;; test.spectec:9357.1-9359.30
  rule _{`b*` : byte*, `b'*` : byte*}:
    `%<=%`({BYTES b*{b <- `b*`}}, {BYTES b'*{b' <- `b'*`}})
    -- if ((b*{b <- `b*`} = b'*{b' <- `b'*`}) \/ (b'*{b' <- `b'*`} = []))

;; test.spectec:9331.1-9331.48
relation Extend_eleminst: `%<=%`(eleminst, eleminst)
  ;; test.spectec:9361.1-9363.36
  rule _{rt : reftype, `ref*` : ref*, `ref'*` : ref*}:
    `%<=%`({TYPE rt, REFS ref*{ref <- `ref*`}}, {TYPE rt, REFS ref'*{ref' <- `ref'*`}})
    -- if ((ref*{ref <- `ref*`} = ref'*{ref' <- `ref'*`}) \/ (ref'*{ref' <- `ref'*`} = []))

;; test.spectec:9332.1-9332.54
relation Extend_structinst: `%<=%`(structinst, structinst)
  ;; test.spectec:9365.1-9368.34
  rule _{dt : deftype, `fv*` : fieldval*, `fv'*` : fieldval*, `mut?*` : mut?*, `zt*` : storagetype*}:
    `%<=%`({TYPE dt, FIELDS fv*{fv <- `fv*`}}, {TYPE dt, FIELDS fv'*{fv' <- `fv'*`}})
    -- Expand: `%~~%`(dt, STRUCT_comptype(`%`_list(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)*{`mut?` <- `mut?*`, zt <- `zt*`})))
    -- (if ((mut?{mut <- `mut?`} = ?(MUT_mut)) \/ (fv = fv')))*{fv <- `fv*`, fv' <- `fv'*`, `mut?` <- `mut?*`}

;; test.spectec:9333.1-9333.51
relation Extend_arrayinst: `%<=%`(arrayinst, arrayinst)
  ;; test.spectec:9370.1-9373.34
  rule _{dt : deftype, `fv*` : fieldval*, `fv'*` : fieldval*, `mut?` : mut?, zt : storagetype}:
    `%<=%`({TYPE dt, FIELDS fv*{fv <- `fv*`}}, {TYPE dt, FIELDS fv'*{fv' <- `fv'*`}})
    -- Expand: `%~~%`(dt, ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- (if ((mut?{mut <- `mut?`} = ?(MUT_mut)) \/ (fv = fv')))*{fv <- `fv*`, fv' <- `fv'*`}

;; test.spectec:9334.1-9334.45
relation Extend_exninst: `%<=%`(exninst, exninst)
  ;; test.spectec:9375.1-9376.50
  rule _{ta : tagaddr, `val*` : val*}:
    `%<=%`({TAG ta, FIELDS val*{val <- `val*`}}, {TAG ta, FIELDS val*{val <- `val*`}})

;; test.spectec:9335.1-9335.39
relation Extend_store: `%<=%`(store, store)
  ;; test.spectec:9379.1-9394.62
  rule _{s : store, s' : store}:
    `%<=%`(s, s')
    -- (Extend_taginst: `%<=%`(s.TAGS_store[a], s'.TAGS_store[a]))^(a<|s.TAGS_store|){}
    -- (Extend_globalinst: `%<=%`(s.GLOBALS_store[a], s'.GLOBALS_store[a]))^(a<|s.GLOBALS_store|){}
    -- (Extend_meminst: `%<=%`(s.MEMS_store[a], s'.MEMS_store[a]))^(a<|s.MEMS_store|){}
    -- (Extend_tableinst: `%<=%`(s.TABLES_store[a], s'.TABLES_store[a]))^(a<|s.TABLES_store|){}
    -- (Extend_funcinst: `%<=%`(s.FUNCS_store[a], s'.FUNCS_store[a]))^(a<|s.FUNCS_store|){}
    -- (Extend_datainst: `%<=%`(s.DATAS_store[a], s'.DATAS_store[a]))^(a<|s.DATAS_store|){}
    -- (Extend_eleminst: `%<=%`(s.ELEMS_store[a], s'.ELEMS_store[a]))^(a<|s.ELEMS_store|){}
    -- (Extend_structinst: `%<=%`(s.STRUCTS_store[a], s'.STRUCTS_store[a]))^(a<|s.STRUCTS_store|){}
    -- (Extend_arrayinst: `%<=%`(s.ARRAYS_store[a], s'.ARRAYS_store[a]))^(a<|s.ARRAYS_store|){}
    -- (Extend_exninst: `%<=%`(s.EXNS_store[a], s'.EXNS_store[a]))^(a<|s.EXNS_store|){}

;; test.spectec:9401.1-9401.38
relation State_ok: `|-%:%`(state, context)
  ;; test.spectec:9416.1-9419.26
  rule _{s : store, f : frame, C : context}:
    `|-%:%`(`%;%`_state(s, f), C)
    -- Store_ok: `|-%:OK`(s)
    -- Frame_ok: `%|-%:%`(s, f, C)

;; test.spectec:9402.1-9402.43
relation Config_ok: `|-%:%`(config, resulttype)
  ;; test.spectec:9421.1-9424.35
  rule _{s : store, f : frame, `instr*` : instr*, `t*` : valtype*, C : context}:
    `|-%:%`(`%;%`_config(`%;%`_state(s, f), instr*{instr <- `instr*`}), `%`_resulttype(t*{t <- `t*`}))
    -- State_ok: `|-%:%`(`%;%`_state(s, f), C)
    -- Expr_ok2: `%;%|-%:%`(s, C, instr*{instr <- `instr*`}, `%`_resulttype(t*{t <- `t*`}))

;; test.spectec:9439.1-9439.32
syntax A = nat

;; test.spectec:9440.1-9440.32
syntax B = nat

;; test.spectec:9442.1-9442.77
syntax sym = 
  | _FIRST(A_1 : A)
  | _DOTS
  | _LAST(A_n : A)

;; test.spectec:9444.1-9444.68
syntax symsplit = 
  | _FIRST(A_1 : A)
  | _LAST(A_2 : A)

;; test.spectec:9446.1-9446.37
syntax recorddots = ()

;; test.spectec:9447.1-9450.22
syntax record = 
{
  FIELD_1 A,
  FIELD_2 A,
  `...` recorddots
}

;; test.spectec:9452.1-9452.71
syntax pth = 
  | PTHSYNTAX

;; test.spectec:9467.1-9467.32
syntax T = nat

;; test.spectec:9469.1-9469.36
relation NotationTypingPremise: `%`(nat)

;; test.spectec:9470.1-9470.58
relation NotationTypingPremisedots: `...`

;; test.spectec:9471.1-9471.35
relation NotationTypingScheme: `%`(nat)
  ;; test.spectec:9473.1-9478.38
  rule _{conclusion : nat, premise_1 : nat, premise_2 : nat, premise_n : nat}:
    `%`(conclusion)
    -- NotationTypingPremise: `%`(premise_1)
    -- NotationTypingPremise: `%`(premise_2)
    -- NotationTypingPremisedots: `...`
    -- NotationTypingPremise: `%`(premise_n)

;; test.spectec:9480.1-9480.83
rec {

;; test.spectec:9480.1-9480.83
relation NotationTypingInstrScheme: `%|-%:%`(context, instr*, instrtype)
  ;; test.spectec:9482.1-9483.38
  rule `i32.add`{C : context}:
    `%|-%:%`(C, [BINOP_instr(I32_numtype, ADD_binop_)], `%->_%%`_instrtype(`%`_resulttype([I32_valtype I32_valtype]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:9485.1-9487.29
  rule `global.get`{C : context, x : idx, t : valtype, mut : mut}:
    `%|-%:%`(C, [`GLOBAL.GET`_instr(x)], `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([t])))
    -- if (C.GLOBALS_context[x!`%`_idx.0] = `%%`_globaltype(?(mut), t))

  ;; test.spectec:9489.1-9492.78
  rule block{C : context, blocktype : blocktype, `instr*` : instr*, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, [BLOCK_instr(blocktype, instr*{instr <- `instr*`})], `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Blocktype_ok: `%|-%:%`(C, blocktype, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- NotationTypingInstrScheme: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(), REFS [], RECS []} +++ C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
}

;; test.spectec:9507.1-9507.49
relation NotationReduct: `~>%`(instr*)
  ;; test.spectec:9509.1-9510.85
  rule 2{q_1 : num_(F64_numtype), q_4 : num_(F64_numtype), q_3 : num_(F64_numtype)}:
    `~>%`([CONST_instr(F64_numtype, q_1) CONST_instr(F64_numtype, q_4) CONST_instr(F64_numtype, q_3) BINOP_instr(F64_numtype, ADD_binop_) BINOP_instr(F64_numtype, MUL_binop_)])

  ;; test.spectec:9512.1-9513.53
  rule 3{q_1 : num_(F64_numtype), q_5 : num_(F64_numtype)}:
    `~>%`([CONST_instr(F64_numtype, q_1) CONST_instr(F64_numtype, q_5) BINOP_instr(F64_numtype, MUL_binop_)])

  ;; test.spectec:9515.1-9516.21
  rule 4{q_6 : num_(F64_numtype)}:
    `~>%`([CONST_instr(F64_numtype, q_6)])

;; test.spectec:9521.1-9521.40
def $instrdots : instr*

;; test.spectec:9523.1-9523.75
syntax label = 
  | `LABEL_%{%}`(n : n, `instr*` : instr*)

;; test.spectec:9524.1-9524.84
syntax callframe = 
  | `FRAME_%{%}`(n : n, frame : frame)

;; test.spectec:9531.1-9531.78
def $allocX(syntax X, syntax Y, store : store, X : X, Y : Y) : (store, addr)

;; test.spectec:9532.1-9532.117
rec {

;; test.spectec:9532.1-9532.117
def $allocXs(syntax X, syntax Y, store : store, X*, Y*) : (store, addr*)
  ;; test.spectec:9533.1-9533.57
  def $allocXs{syntax X, syntax Y, s : store}(syntax X, syntax Y, s, [], []) = (s, [])
  ;; test.spectec:9534.1-9536.65
  def $allocXs{syntax X, syntax Y, s : store, X : X, `X'*` : X*, Y : Y, `Y'*` : Y*, s_2 : store, a : addr, `a'*` : addr*, s_1 : store}(syntax X, syntax Y, s, [X] ++ X'*{X' <- `X'*`}, [Y] ++ Y'*{Y' <- `Y'*`}) = (s_2, [a] ++ a'*{a' <- `a'*`})
    -- if ((s_1, a) = $allocX(syntax X, syntax Y, s, X, Y))
    -- if ((s_2, a'*{a' <- `a'*`}) = $allocXs(syntax X, syntax Y, s_1, X'*{X' <- `X'*`}, Y'*{Y' <- `Y'*`}))
}

;; test.spectec:9551.1-9551.52
syntax symdots = 
  | `%`(i : nat)
    -- if (i = 0)

;; test.spectec:9553.1-9553.55
def $var(syntax X) : nat
  ;; test.spectec:9554.1-9554.26
  def $var{syntax X}(syntax X) = 0

;; test.spectec:9587.1-9587.41
syntax abbreviated = ()

;; test.spectec:9588.1-9588.38
syntax expanded = ()

;; test.spectec:9589.1-9589.37
syntax syntax = ()

;; test.spectec:5949.1-5949.41
grammar Bbyte : byte
  ;; test.spectec:5949.24-5949.41
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:(0x00 | ... | 0xFF) => `%`_byte(`<implicit-prod-result>`)

;; test.spectec:5951.1-5953.82
rec {

;; test.spectec:5951.1-5953.82
grammar BuN(N : N) : uN(N)
  ;; test.spectec:5952.5-5952.83
  prod{n : n} `%`_byte(n):Bbyte => `%`_uN(n)
    -- if ((n < (2 ^ 7)) /\ (n < (2 ^ N)))
  ;; test.spectec:5953.5-5953.82
  prod{m : m, n : n} {{`%`_byte(n):Bbyte} {`%`_uN(m):BuN((((N : nat <:> int) - (7 : nat <:> int)) : int <:> nat))}} => `%`_uN((((2 ^ 7) * m) + (((n : nat <:> int) - ((2 ^ 7) : nat <:> int)) : int <:> nat)))
    -- if ((n >= (2 ^ 7)) /\ (N > 7))
}

;; test.spectec:5955.1-5958.82
rec {

;; test.spectec:5955.1-5958.82
grammar BsN(N : N) : sN(N)
  ;; test.spectec:5956.5-5956.87
  prod{n : n} `%`_byte(n):Bbyte => `%`_sN((n : nat <:> int))
    -- if ((n < (2 ^ 6)) /\ (n < (2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat))))
  ;; test.spectec:5957.5-5957.101
  prod{n : n} `%`_byte(n):Bbyte => `%`_sN(((n : nat <:> int) - ((2 ^ 7) : nat <:> int)))
    -- if ((((2 ^ 6) <= n) /\ (n < (2 ^ 7))) /\ ((n : nat <:> int) >= (((2 ^ 7) : nat <:> int) - ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int))))
  ;; test.spectec:5958.5-5958.82
  prod{i : sN((((N : nat <:> int) - (7 : nat <:> int)) : int <:> nat)), n : n} {{`%`_byte(n):Bbyte} {i:BsN((((N : nat <:> int) - (7 : nat <:> int)) : int <:> nat))}} => `%`_sN(((((2 ^ 7) * (i!`%`_sN.0 : int <:> nat)) + (((n : nat <:> int) - ((2 ^ 7) : nat <:> int)) : int <:> nat)) : nat <:> int))
    -- if ((n >= (2 ^ 7)) /\ (N > 7))
}

;; test.spectec:5960.1-5961.50
grammar BiN(N : N) : iN(N)
  ;; test.spectec:5961.5-5961.50
  prod{i : sN(N)} i:BsN(N) => `%`_iN($inv_signed_(N, i!`%`_sN.0))

;; test.spectec:5964.1-5965.43
grammar BfN(N : N) : fN(N)
  ;; test.spectec:5965.5-5965.43
  prod{`b*` : byte*} b*{b <- `b*`}:Bbyte^(((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat){} => $inv_fbytes_(N, b*{b <- `b*`})

;; test.spectec:5968.1-5968.29
grammar Bu32 : u32
  ;; test.spectec:5968.22-5968.29
  prod{`<implicit-prod-result>` : uN(32)} `<implicit-prod-result>`:BuN(32) => `<implicit-prod-result>`

;; test.spectec:5969.1-5969.29
grammar Bu64 : u64
  ;; test.spectec:5969.22-5969.29
  prod{`<implicit-prod-result>` : uN(64)} `<implicit-prod-result>`:BuN(64) => `<implicit-prod-result>`

;; test.spectec:5971.1-5971.29
grammar Bs33 : s33
  ;; test.spectec:5971.22-5971.29
  prod{`<implicit-prod-result>` : sN(33)} `<implicit-prod-result>`:BsN(33) => `<implicit-prod-result>`

;; test.spectec:5973.1-5973.29
grammar Bi32 : i32
  ;; test.spectec:5973.22-5973.29
  prod{`<implicit-prod-result>` : uN(32)} `<implicit-prod-result>`:BuN(32) => `<implicit-prod-result>`

;; test.spectec:5974.1-5974.29
grammar Bi64 : i64
  ;; test.spectec:5974.22-5974.29
  prod{`<implicit-prod-result>` : uN(64)} `<implicit-prod-result>`:BuN(64) => `<implicit-prod-result>`

;; test.spectec:5976.1-5976.29
grammar Bf32 : f32
  ;; test.spectec:5976.22-5976.29
  prod{`<implicit-prod-result>` : fN(32)} `<implicit-prod-result>`:BfN(32) => `<implicit-prod-result>`

;; test.spectec:5977.1-5977.29
grammar Bf64 : f64
  ;; test.spectec:5977.22-5977.29
  prod{`<implicit-prod-result>` : fN(64)} `<implicit-prod-result>`:BfN(64) => `<implicit-prod-result>`

;; test.spectec:5982.1-5983.29
grammar Blist(syntax el, grammar BX : el) : el*
  ;; test.spectec:5983.5-5983.29
  prod{n : n, `el*` : el*} {{`%`_u32(n):Bu32} {el:BX^n{el <- `el*`}}} => el^n{el <- `el*`}

;; test.spectec:6008.1-6009.52
grammar Bname : name
  ;; test.spectec:6009.5-6009.52
  prod{name : name, `b*` : byte*} b*{b <- `b*`}:Blist(syntax byte, grammar Bbyte) => name
    -- if ($utf8(name!`%`_name.0) = b*{b <- `b*`})

;; test.spectec:6014.1-6014.41
grammar Btypeidx : typeidx
  ;; test.spectec:6014.30-6014.41
  prod{x : idx} x:Bu32 => x

;; test.spectec:6015.1-6015.39
grammar Btagidx : tagidx
  ;; test.spectec:6015.28-6015.39
  prod{x : idx} x:Bu32 => x

;; test.spectec:6016.1-6016.45
grammar Bglobalidx : globalidx
  ;; test.spectec:6016.34-6016.45
  prod{x : idx} x:Bu32 => x

;; test.spectec:6017.1-6017.39
grammar Bmemidx : memidx
  ;; test.spectec:6017.28-6017.39
  prod{x : idx} x:Bu32 => x

;; test.spectec:6018.1-6018.43
grammar Btableidx : tableidx
  ;; test.spectec:6018.32-6018.43
  prod{x : idx} x:Bu32 => x

;; test.spectec:6019.1-6019.41
grammar Bfuncidx : funcidx
  ;; test.spectec:6019.30-6019.41
  prod{x : idx} x:Bu32 => x

;; test.spectec:6020.1-6020.41
grammar Bdataidx : dataidx
  ;; test.spectec:6020.30-6020.41
  prod{x : idx} x:Bu32 => x

;; test.spectec:6021.1-6021.41
grammar Belemidx : elemidx
  ;; test.spectec:6021.30-6021.41
  prod{x : idx} x:Bu32 => x

;; test.spectec:6022.1-6022.43
grammar Blocalidx : localidx
  ;; test.spectec:6022.32-6022.43
  prod{x : idx} x:Bu32 => x

;; test.spectec:6023.1-6023.43
grammar Bfieldidx : fieldidx
  ;; test.spectec:6023.32-6023.43
  prod{x : idx} x:Bu32 => x

;; test.spectec:6024.1-6024.43
grammar Blabelidx : labelidx
  ;; test.spectec:6024.32-6024.43
  prod{l : labelidx} l:Bu32 => l

;; test.spectec:6026.1-6031.28
grammar Bexternidx : externidx
  ;; test.spectec:6027.5-6027.30
  prod{x : idx} {{0x00} {x:Bfuncidx}} => FUNC_externidx(x)
  ;; test.spectec:6028.5-6028.32
  prod{x : idx} {{0x01} {x:Btableidx}} => TABLE_externidx(x)
  ;; test.spectec:6029.5-6029.28
  prod{x : idx} {{0x02} {x:Bmemidx}} => MEM_externidx(x)
  ;; test.spectec:6030.5-6030.34
  prod{x : idx} {{0x03} {x:Bglobalidx}} => GLOBAL_externidx(x)
  ;; test.spectec:6031.5-6031.28
  prod{x : idx} {{0x04} {x:Btagidx}} => TAG_externidx(x)

;; test.spectec:6046.1-6050.16
grammar Bnumtype : numtype
  ;; test.spectec:6047.5-6047.16
  prod 0x7C => F64_numtype
  ;; test.spectec:6048.5-6048.16
  prod 0x7D => F32_numtype
  ;; test.spectec:6049.5-6049.16
  prod 0x7E => I64_numtype
  ;; test.spectec:6050.5-6050.16
  prod 0x7F => I32_numtype

;; test.spectec:6052.1-6053.17
grammar Bvectype : vectype
  ;; test.spectec:6053.5-6053.17
  prod 0x7B => V128_vectype

;; test.spectec:6055.1-6067.18
grammar Babsheaptype : heaptype
  ;; test.spectec:6056.5-6056.16
  prod 0x69 => EXN_heaptype
  ;; test.spectec:6057.5-6057.18
  prod 0x6A => ARRAY_heaptype
  ;; test.spectec:6058.5-6058.19
  prod 0x6B => STRUCT_heaptype
  ;; test.spectec:6059.5-6059.16
  prod 0x6C => I31_heaptype
  ;; test.spectec:6060.5-6060.15
  prod 0x6D => EQ_heaptype
  ;; test.spectec:6061.5-6061.16
  prod 0x6E => ANY_heaptype
  ;; test.spectec:6062.5-6062.19
  prod 0x6F => EXTERN_heaptype
  ;; test.spectec:6063.5-6063.17
  prod 0x70 => FUNC_heaptype
  ;; test.spectec:6064.5-6064.17
  prod 0x71 => NONE_heaptype
  ;; test.spectec:6065.5-6065.21
  prod 0x72 => NOEXTERN_heaptype
  ;; test.spectec:6066.5-6066.19
  prod 0x73 => NOFUNC_heaptype
  ;; test.spectec:6067.5-6067.18
  prod 0x74 => NOEXN_heaptype

;; test.spectec:6069.1-6071.54
grammar Bheaptype : heaptype
  ;; test.spectec:6070.5-6070.26
  prod{ht : heaptype} ht:Babsheaptype => ht
  ;; test.spectec:6071.5-6071.54
  prod{x33 : s33} x33:Bs33 => _IDX_heaptype($s33_to_u32(x33))
    -- if (x33!`%`_s33.0 >= (0 : nat <:> int))

;; test.spectec:6073.1-6076.35
grammar Breftype : reftype
  ;; test.spectec:6074.5-6074.37
  prod{ht : heaptype} {{0x63} {ht:Bheaptype}} => REF_reftype(?(NULL_null), ht)
  ;; test.spectec:6075.5-6075.32
  prod{ht : heaptype} {{0x64} {ht:Bheaptype}} => REF_reftype(?(), ht)
  ;; test.spectec:6076.5-6076.35
  prod{ht : heaptype} ht:Babsheaptype => REF_reftype(?(NULL_null), ht)

;; test.spectec:6078.1-6081.22
grammar Bvaltype : valtype
  ;; test.spectec:6079.5-6079.22
  prod{nt : numtype} nt:Bnumtype => (nt : numtype <: valtype)
  ;; test.spectec:6080.5-6080.22
  prod{vt : vectype} vt:Bvectype => (vt : vectype <: valtype)
  ;; test.spectec:6081.5-6081.22
  prod{rt : reftype} rt:Breftype => (rt : reftype <: valtype)

;; test.spectec:6084.1-6085.29
grammar Bresulttype : resulttype
  ;; test.spectec:6085.5-6085.29
  prod{`t*` : valtype*} t*{t <- `t*`}:Blist(syntax valtype, grammar Bvaltype) => `%`_resulttype(t*{t <- `t*`})

;; test.spectec:6090.1-6092.16
grammar Bmut : mut?
  ;; test.spectec:6091.5-6091.16
  prod 0x00 => ?()
  ;; test.spectec:6092.5-6092.16
  prod 0x01 => ?(MUT_mut)

;; test.spectec:6094.1-6096.15
grammar Bpacktype : packtype
  ;; test.spectec:6095.5-6095.16
  prod 0x77 => I16_packtype
  ;; test.spectec:6096.5-6096.15
  prod 0x78 => I8_packtype

;; test.spectec:6098.1-6100.23
grammar Bstoragetype : storagetype
  ;; test.spectec:6099.5-6099.20
  prod{t : valtype} t:Bvaltype => (t : valtype <: storagetype)
  ;; test.spectec:6100.5-6100.23
  prod{pt : packtype} pt:Bpacktype => (pt : packtype <: storagetype)

;; test.spectec:6102.1-6103.41
grammar Bfieldtype : fieldtype
  ;; test.spectec:6103.5-6103.41
  prod{`mut?` : mut?, zt : storagetype} {{zt:Bstoragetype} {mut?{mut <- `mut?`}:Bmut}} => `%%`_fieldtype(mut?{mut <- `mut?`}, zt)

;; test.spectec:6105.1-6108.64
grammar Bcomptype : comptype
  ;; test.spectec:6106.5-6106.35
  prod{ft : fieldtype} {{0x5E} {ft:Bfieldtype}} => ARRAY_comptype(ft)
  ;; test.spectec:6107.5-6107.45
  prod{`ft*` : fieldtype*} {{0x5F} {ft*{ft <- `ft*`}:Blist(syntax fieldtype, grammar Bfieldtype)}} => STRUCT_comptype(`%`_list(ft*{ft <- `ft*`}))
  ;; test.spectec:6108.5-6108.64
  prod{`t_1*` : valtype*, `t_2*` : valtype*} {{0x60} {`%`_resulttype(t_1*{t_1 <- `t_1*`}):Bresulttype} {`%`_resulttype(t_2*{t_2 <- `t_2*`}):Bresulttype}} => `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`}))

;; test.spectec:6110.1-6113.37
grammar Bsubtype : subtype
  ;; test.spectec:6111.5-6111.67
  prod{`x*` : idx*, ct : comptype} {{0x4F} {x*{x <- `x*`}:Blist(syntax typeidx, grammar Btypeidx)} {ct:Bcomptype}} => SUB_subtype(?(FINAL_final), _IDX_typeuse(x)*{x <- `x*`}, ct)
  ;; test.spectec:6112.5-6112.61
  prod{`x*` : idx*, ct : comptype} {{0x50} {x*{x <- `x*`}:Blist(syntax typeidx, grammar Btypeidx)} {ct:Bcomptype}} => SUB_subtype(?(), _IDX_typeuse(x)*{x <- `x*`}, ct)
  ;; test.spectec:6113.5-6113.37
  prod{ct : comptype} ct:Bcomptype => SUB_subtype(?(FINAL_final), [], ct)

;; test.spectec:6115.1-6117.26
grammar Brectype : rectype
  ;; test.spectec:6116.5-6116.40
  prod{`st*` : subtype*} {{0x4E} {st*{st <- `st*`}:Blist(syntax subtype, grammar Bsubtype)}} => REC_rectype(`%`_list(st*{st <- `st*`}))
  ;; test.spectec:6117.5-6117.26
  prod{st : subtype} st:Bsubtype => REC_rectype(`%`_list([st]))

;; test.spectec:6122.1-6126.43
grammar Blimits : (addrtype, limits)
  ;; test.spectec:6123.5-6123.38
  prod{n : n} {{0x00} {`%`_u64(n):Bu64}} => (I32_addrtype, `[%..%]`_limits(`%`_u64(n), ?()))
  ;; test.spectec:6124.5-6124.43
  prod{n : n, m : m} {{0x01} {`%`_u64(n):Bu64} {`%`_u64(m):Bu64}} => (I32_addrtype, `[%..%]`_limits(`%`_u64(n), ?(`%`_u64(m))))
  ;; test.spectec:6125.5-6125.38
  prod{n : n} {{0x04} {`%`_u64(n):Bu64}} => (I64_addrtype, `[%..%]`_limits(`%`_u64(n), ?()))
  ;; test.spectec:6126.5-6126.43
  prod{n : n, m : m} {{0x05} {`%`_u64(n):Bu64} {`%`_u64(m):Bu64}} => (I64_addrtype, `[%..%]`_limits(`%`_u64(n), ?(`%`_u64(m))))

;; test.spectec:6128.1-6129.30
grammar Btagtype : tagtype
  ;; test.spectec:6129.5-6129.30
  prod{x : idx} {{0x00} {x:Btypeidx}} => _IDX_tagtype(x)

;; test.spectec:6131.1-6132.35
grammar Bglobaltype : globaltype
  ;; test.spectec:6132.5-6132.35
  prod{`mut?` : mut?, t : valtype} {{t:Bvaltype} {mut?{mut <- `mut?`}:Bmut}} => `%%`_globaltype(mut?{mut <- `mut?`}, t)

;; test.spectec:6134.1-6135.36
grammar Bmemtype : memtype
  ;; test.spectec:6135.5-6135.36
  prod{at : addrtype, lim : limits} (at, lim):Blimits => `%%PAGE`_memtype(at, lim)

;; test.spectec:6137.1-6138.46
grammar Btabletype : tabletype
  ;; test.spectec:6138.5-6138.46
  prod{at : addrtype, lim : limits, rt : reftype} {{rt:Breftype} {(at, lim):Blimits}} => `%%%`_tabletype(at, lim, rt)

;; test.spectec:6141.1-6146.31
grammar Bexterntype : externtype
  ;; test.spectec:6142.5-6142.37
  prod{x : idx} {{0x00} {x:Btypeidx}} => FUNC_externtype(_IDX_typeuse(x))
  ;; test.spectec:6143.5-6143.35
  prod{tt : tabletype} {{0x01} {tt:Btabletype}} => TABLE_externtype(tt)
  ;; test.spectec:6144.5-6144.31
  prod{mt : memtype} {{0x02} {mt:Bmemtype}} => MEM_externtype(mt)
  ;; test.spectec:6145.5-6145.37
  prod{gt : globaltype} {{0x03} {gt:Bglobaltype}} => GLOBAL_externtype(gt)
  ;; test.spectec:6146.5-6146.31
  prod{jt : tagtype} {{0x04} {jt:Btagtype}} => TAG_externtype(jt)

;; test.spectec:6174.1-6178.25
grammar Bcastop : castop
  ;; test.spectec:6175.5-6175.23
  prod 0x00 => (?(), ?())
  ;; test.spectec:6176.5-6176.24
  prod 0x01 => (?(NULL_null), ?())
  ;; test.spectec:6177.5-6177.24
  prod 0x02 => (?(), ?(NULL_null))
  ;; test.spectec:6178.5-6178.25
  prod 0x03 => (?(NULL_null), ?(NULL_null))

;; test.spectec:6180.1-6183.35
grammar Bblocktype : blocktype
  ;; test.spectec:6181.5-6181.24
  prod 0x40 => _RESULT_blocktype(?())
  ;; test.spectec:6182.5-6182.28
  prod{t : valtype} t:Bvaltype => _RESULT_blocktype(?(t))
  ;; test.spectec:6183.5-6183.35
  prod{i : s33} i:Bs33 => _IDX_blocktype(`%`_typeidx((i!`%`_s33.0 : int <:> nat)))
    -- if (i!`%`_s33.0 >= (0 : nat <:> int))

;; test.spectec:6215.1-6219.40
grammar Bcatch : catch
  ;; test.spectec:6216.5-6216.44
  prod{x : idx, l : labelidx} {{0x00} {x:Btagidx} {l:Blabelidx}} => CATCH_catch(x, l)
  ;; test.spectec:6217.5-6217.48
  prod{x : idx, l : labelidx} {{0x01} {x:Btagidx} {l:Blabelidx}} => CATCH_REF_catch(x, l)
  ;; test.spectec:6218.5-6218.36
  prod{l : labelidx} {{0x02} {l:Blabelidx}} => CATCH_ALL_catch(l)
  ;; test.spectec:6219.5-6219.40
  prod{l : labelidx} {{0x03} {l:Blabelidx}} => CATCH_ALL_REF_catch(l)

;; test.spectec:6254.1-6256.92
grammar Bmemarg : memidxop
  ;; test.spectec:6255.5-6255.85
  prod{n : n, m : m} {{`%`_u32(n):Bu32} {`%`_u64(m):Bu64}} => (`%`_memidx(0), {ALIGN `%`_u32(n), OFFSET `%`_u64(m)})
    -- if (n < (2 ^ 6))
  ;; test.spectec:6256.5-6256.92
  prod{x : idx, n : n, m : m} {{`%`_u32(n):Bu32} {x:Bmemidx} {`%`_u64(m):Bu64}} => (x, {ALIGN `%`_u32((((n : nat <:> int) - ((2 ^ 6) : nat <:> int)) : int <:> nat)), OFFSET `%`_u64(m)})
    -- if (((2 ^ 6) <= n) /\ (n < (2 ^ 7)))

;; test.spectec:6546.1-6547.17
grammar Blaneidx : laneidx
  ;; test.spectec:6547.5-6547.17
  prod{l : labelidx} `%`_byte(l!`%`_labelidx.0):Bbyte => `%`_laneidx(l!`%`_labelidx.0)

;; test.spectec:6947.1-6961.71
rec {

;; test.spectec:6947.1-6961.71
grammar Binstr : instr
  ;; test.spectec:6162.5-6162.24
  prod 0x00 => UNREACHABLE_instr
  ;; test.spectec:6163.5-6163.16
  prod 0x01 => NOP_instr
  ;; test.spectec:6164.5-6164.17
  prod 0x1A => DROP_instr
  ;; test.spectec:6165.5-6165.19
  prod 0x1B => SELECT_instr(?())
  ;; test.spectec:6166.5-6166.41
  prod{`t*` : valtype*} {{0x1C} {t*{t <- `t*`}:Blist(syntax valtype, grammar Bvaltype)}} => SELECT_instr(?(t*{t <- `t*`}))
  ;; test.spectec:6186.5-6186.57
  prod{bt : blocktype, `in*` : instr*} {{0x02} {bt:Bblocktype} {in:Binstr*{in <- `in*`}} {0x0B}} => BLOCK_instr(bt, in*{in <- `in*`})
  ;; test.spectec:6187.5-6187.56
  prod{bt : blocktype, `in*` : instr*} {{0x03} {bt:Bblocktype} {in:Binstr*{in <- `in*`}} {0x0B}} => LOOP_instr(bt, in*{in <- `in*`})
  ;; test.spectec:6188.5-6188.63
  prod{bt : blocktype, `in*` : instr*} {{0x04} {bt:Bblocktype} {in:Binstr*{in <- `in*`}} {0x0B}} => `IF%%ELSE%`_instr(bt, in*{in <- `in*`}, [])
  ;; test.spectec:6189.5-6190.55
  prod{bt : blocktype, `in_1*` : instr*, `in_2*` : instr*} {{0x04} {bt:Bblocktype} {in_1:Binstr*{in_1 <- `in_1*`}} {0x05} {in_2:Binstr*{in_2 <- `in_2*`}} {0x0B}} => `IF%%ELSE%`_instr(bt, in_1*{in_1 <- `in_1*`}, in_2*{in_2 <- `in_2*`})
  ;; test.spectec:6194.5-6194.30
  prod{x : idx} {{0x08} {x:Btagidx}} => THROW_instr(x)
  ;; test.spectec:6195.5-6195.22
  prod 0x0A => THROW_REF_instr
  ;; test.spectec:6196.5-6196.29
  prod{l : labelidx} {{0x0C} {l:Blabelidx}} => BR_instr(l)
  ;; test.spectec:6197.5-6197.32
  prod{l : labelidx} {{0x0D} {l:Blabelidx}} => BR_IF_instr(l)
  ;; test.spectec:6198.5-6198.62
  prod{`l*` : labelidx*, l_n : labelidx} {{0x0E} {l*{l <- `l*`}:Blist(syntax labelidx, grammar Blabelidx)} {l_n:Blabelidx}} => BR_TABLE_instr(l*{l <- `l*`}, l_n)
  ;; test.spectec:6199.5-6199.19
  prod 0x0F => RETURN_instr
  ;; test.spectec:6200.5-6200.30
  prod{x : idx} {{0x10} {x:Bfuncidx}} => CALL_instr(x)
  ;; test.spectec:6201.5-6201.60
  prod{x : idx, y : idx} {{0x11} {y:Btypeidx} {x:Btableidx}} => CALL_INDIRECT_instr(x, _IDX_typeuse(y))
  ;; test.spectec:6202.5-6202.37
  prod{x : idx} {{0x12} {x:Bfuncidx}} => RETURN_CALL_instr(x)
  ;; test.spectec:6203.5-6203.67
  prod{x : idx, y : idx} {{0x13} {y:Btypeidx} {x:Btableidx}} => RETURN_CALL_INDIRECT_instr(x, _IDX_typeuse(y))
  ;; test.spectec:6204.5-6204.41
  prod{x : idx} {{0x14} {x:Btypeidx}} => CALL_REF_instr(_IDX_typeuse(x))
  ;; test.spectec:6205.5-6205.48
  prod{x : idx} {{0x15} {x:Btypeidx}} => RETURN_CALL_REF_instr(_IDX_typeuse(x))
  ;; test.spectec:6206.5-6206.81
  prod{bt : blocktype, `c*` : catch*, `in*` : instr*} {{0x1F} {bt:Bblocktype} {c*{c <- `c*`}:Blist(syntax catch, grammar Bcatch)} {in:Binstr*{in <- `in*`}} {0x0B}} => TRY_TABLE_instr(bt, `%`_list(c*{c <- `c*`}), in*{in <- `in*`})
  ;; test.spectec:6207.5-6207.37
  prod{l : labelidx} {{0xD5} {l:Blabelidx}} => BR_ON_NULL_instr(l)
  ;; test.spectec:6208.5-6208.41
  prod{l : labelidx} {{0xD6} {l:Blabelidx}} => BR_ON_NON_NULL_instr(l)
  ;; test.spectec:6209.5-6210.100
  prod{l : labelidx, `null_1?` : null?, ht_1 : heaptype, `null_2?` : null?, ht_2 : heaptype} {{0xFB} {`%`_u32(24):Bu32} {(null_1?{null_1 <- `null_1?`}, null_2?{null_2 <- `null_2?`}):Bcastop} {l:Blabelidx} {ht_1:Bheaptype} {ht_2:Bheaptype}} => BR_ON_CAST_instr(l, REF_reftype(null_1?{null_1 <- `null_1?`}, ht_1), REF_reftype(null_2?{null_2 <- `null_2?`}, ht_2))
  ;; test.spectec:6211.5-6212.105
  prod{l : labelidx, `null_1?` : null?, ht_1 : heaptype, `null_2?` : null?, ht_2 : heaptype} {{0xFB} {`%`_u32(25):Bu32} {(null_1?{null_1 <- `null_1?`}, null_2?{null_2 <- `null_2?`}):Bcastop} {l:Blabelidx} {ht_1:Bheaptype} {ht_2:Bheaptype}} => BR_ON_CAST_FAIL_instr(l, REF_reftype(null_1?{null_1 <- `null_1?`}, ht_1), REF_reftype(null_2?{null_2 <- `null_2?`}, ht_2))
  ;; test.spectec:6225.5-6225.36
  prod{x : idx} {{0x20} {x:Blocalidx}} => `LOCAL.GET`_instr(x)
  ;; test.spectec:6226.5-6226.36
  prod{x : idx} {{0x21} {x:Blocalidx}} => `LOCAL.SET`_instr(x)
  ;; test.spectec:6227.5-6227.36
  prod{x : idx} {{0x22} {x:Blocalidx}} => `LOCAL.TEE`_instr(x)
  ;; test.spectec:6231.5-6231.38
  prod{x : idx} {{0x23} {x:Bglobalidx}} => `GLOBAL.GET`_instr(x)
  ;; test.spectec:6232.5-6232.38
  prod{x : idx} {{0x24} {x:Bglobalidx}} => `GLOBAL.SET`_instr(x)
  ;; test.spectec:6239.5-6239.36
  prod{x : idx} {{0x25} {x:Btableidx}} => `TABLE.GET`_instr(x)
  ;; test.spectec:6240.5-6240.36
  prod{x : idx} {{0x26} {x:Btableidx}} => `TABLE.SET`_instr(x)
  ;; test.spectec:6241.5-6241.58
  prod{x : idx, y : idx} {{0xFC} {`%`_u32(12):Bu32} {y:Belemidx} {x:Btableidx}} => `TABLE.INIT`_instr(x, y)
  ;; test.spectec:6242.5-6242.43
  prod{x : idx} {{0xFC} {`%`_u32(13):Bu32} {x:Belemidx}} => `ELEM.DROP`_instr(x)
  ;; test.spectec:6243.5-6243.67
  prod{x_1 : idx, x_2 : idx} {{0xFC} {`%`_u32(14):Bu32} {x_1:Btableidx} {x_2:Btableidx}} => `TABLE.COPY`_instr(x_1, x_2)
  ;; test.spectec:6244.5-6244.45
  prod{x : idx} {{0xFC} {`%`_u32(15):Bu32} {x:Btableidx}} => `TABLE.GROW`_instr(x)
  ;; test.spectec:6245.5-6245.45
  prod{x : idx} {{0xFC} {`%`_u32(16):Bu32} {x:Btableidx}} => `TABLE.SIZE`_instr(x)
  ;; test.spectec:6246.5-6246.45
  prod{x : idx} {{0xFC} {`%`_u32(17):Bu32} {x:Btableidx}} => `TABLE.FILL`_instr(x)
  ;; test.spectec:6259.5-6259.41
  prod{x : idx, ao : memarg} {{0x28} {(x, ao):Bmemarg}} => LOAD_instr(I32_numtype, ?(), x, ao)
  ;; test.spectec:6260.5-6260.41
  prod{x : idx, ao : memarg} {{0x29} {(x, ao):Bmemarg}} => LOAD_instr(I64_numtype, ?(), x, ao)
  ;; test.spectec:6261.5-6261.41
  prod{x : idx, ao : memarg} {{0x2A} {(x, ao):Bmemarg}} => LOAD_instr(F32_numtype, ?(), x, ao)
  ;; test.spectec:6262.5-6262.41
  prod{x : idx, ao : memarg} {{0x2B} {(x, ao):Bmemarg}} => LOAD_instr(F64_numtype, ?(), x, ao)
  ;; test.spectec:6263.5-6263.50
  prod{x : idx, ao : memarg} {{0x2C} {(x, ao):Bmemarg}} => LOAD_instr(I32_numtype, ?(`%_%`_loadop_(`%`_sz(8), S_sx)), x, ao)
  ;; test.spectec:6264.5-6264.50
  prod{x : idx, ao : memarg} {{0x2D} {(x, ao):Bmemarg}} => LOAD_instr(I32_numtype, ?(`%_%`_loadop_(`%`_sz(8), U_sx)), x, ao)
  ;; test.spectec:6265.5-6265.51
  prod{x : idx, ao : memarg} {{0x2E} {(x, ao):Bmemarg}} => LOAD_instr(I32_numtype, ?(`%_%`_loadop_(`%`_sz(16), S_sx)), x, ao)
  ;; test.spectec:6266.5-6266.51
  prod{x : idx, ao : memarg} {{0x2F} {(x, ao):Bmemarg}} => LOAD_instr(I32_numtype, ?(`%_%`_loadop_(`%`_sz(16), U_sx)), x, ao)
  ;; test.spectec:6267.5-6267.50
  prod{x : idx, ao : memarg} {{0x30} {(x, ao):Bmemarg}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(8), S_sx)), x, ao)
  ;; test.spectec:6268.5-6268.50
  prod{x : idx, ao : memarg} {{0x31} {(x, ao):Bmemarg}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(8), U_sx)), x, ao)
  ;; test.spectec:6269.5-6269.51
  prod{x : idx, ao : memarg} {{0x32} {(x, ao):Bmemarg}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(16), S_sx)), x, ao)
  ;; test.spectec:6270.5-6270.51
  prod{x : idx, ao : memarg} {{0x33} {(x, ao):Bmemarg}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(16), U_sx)), x, ao)
  ;; test.spectec:6271.5-6271.51
  prod{x : idx, ao : memarg} {{0x34} {(x, ao):Bmemarg}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(32), S_sx)), x, ao)
  ;; test.spectec:6272.5-6272.51
  prod{x : idx, ao : memarg} {{0x35} {(x, ao):Bmemarg}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(32), U_sx)), x, ao)
  ;; test.spectec:6273.5-6273.42
  prod{x : idx, ao : memarg} {{0x36} {(x, ao):Bmemarg}} => STORE_instr(I32_numtype, ?(), x, ao)
  ;; test.spectec:6274.5-6274.42
  prod{x : idx, ao : memarg} {{0x37} {(x, ao):Bmemarg}} => STORE_instr(I64_numtype, ?(), x, ao)
  ;; test.spectec:6275.5-6275.42
  prod{x : idx, ao : memarg} {{0x38} {(x, ao):Bmemarg}} => STORE_instr(F32_numtype, ?(), x, ao)
  ;; test.spectec:6276.5-6276.42
  prod{x : idx, ao : memarg} {{0x39} {(x, ao):Bmemarg}} => STORE_instr(F64_numtype, ?(), x, ao)
  ;; test.spectec:6277.5-6277.45
  prod{x : idx, ao : memarg} {{0x3A} {(x, ao):Bmemarg}} => STORE_instr(I32_numtype, ?(`%`_storeop_(`%`_sz(8))), x, ao)
  ;; test.spectec:6278.5-6278.46
  prod{x : idx, ao : memarg} {{0x3B} {(x, ao):Bmemarg}} => STORE_instr(I32_numtype, ?(`%`_storeop_(`%`_sz(16))), x, ao)
  ;; test.spectec:6279.5-6279.45
  prod{x : idx, ao : memarg} {{0x3C} {(x, ao):Bmemarg}} => STORE_instr(I64_numtype, ?(`%`_storeop_(`%`_sz(8))), x, ao)
  ;; test.spectec:6280.5-6280.46
  prod{x : idx, ao : memarg} {{0x3D} {(x, ao):Bmemarg}} => STORE_instr(I64_numtype, ?(`%`_storeop_(`%`_sz(16))), x, ao)
  ;; test.spectec:6281.5-6281.46
  prod{x : idx, ao : memarg} {{0x3E} {(x, ao):Bmemarg}} => STORE_instr(I64_numtype, ?(`%`_storeop_(`%`_sz(32))), x, ao)
  ;; test.spectec:6282.5-6282.36
  prod{x : idx} {{0x3F} {x:Bmemidx}} => `MEMORY.SIZE`_instr(x)
  ;; test.spectec:6283.5-6283.36
  prod{x : idx} {{0x40} {x:Bmemidx}} => `MEMORY.GROW`_instr(x)
  ;; test.spectec:6284.5-6284.56
  prod{x : idx, y : idx} {{0xFC} {`%`_u32(8):Bu32} {y:Bdataidx} {x:Bmemidx}} => `MEMORY.INIT`_instr(x, y)
  ;; test.spectec:6285.5-6285.42
  prod{x : idx} {{0xFC} {`%`_u32(9):Bu32} {x:Bdataidx}} => `DATA.DROP`_instr(x)
  ;; test.spectec:6286.5-6286.64
  prod{x_1 : idx, x_2 : idx} {{0xFC} {`%`_u32(10):Bu32} {x_1:Bmemidx} {x_2:Bmemidx}} => `MEMORY.COPY`_instr(x_1, x_2)
  ;; test.spectec:6287.5-6287.44
  prod{x : idx} {{0xFC} {`%`_u32(11):Bu32} {x:Bmemidx}} => `MEMORY.FILL`_instr(x)
  ;; test.spectec:6294.5-6294.37
  prod{ht : heaptype} {{0xD0} {ht:Bheaptype}} => `REF.NULL`_instr(ht)
  ;; test.spectec:6295.5-6295.24
  prod 0xD1 => `REF.IS_NULL`_instr
  ;; test.spectec:6296.5-6296.34
  prod{x : idx} {{0xD2} {x:Bfuncidx}} => `REF.FUNC`_instr(x)
  ;; test.spectec:6297.5-6297.19
  prod 0xD3 => `REF.EQ`_instr
  ;; test.spectec:6298.5-6298.28
  prod 0xD4 => `REF.AS_NON_NULL`_instr
  ;; test.spectec:6299.5-6299.51
  prod{ht : heaptype} {{0xFB} {`%`_u32(20):Bu32} {ht:Bheaptype}} => `REF.TEST`_instr(REF_reftype(?(), ht))
  ;; test.spectec:6300.5-6300.56
  prod{ht : heaptype} {{0xFB} {`%`_u32(21):Bu32} {ht:Bheaptype}} => `REF.TEST`_instr(REF_reftype(?(NULL_null), ht))
  ;; test.spectec:6301.5-6301.51
  prod{ht : heaptype} {{0xFB} {`%`_u32(22):Bu32} {ht:Bheaptype}} => `REF.CAST`_instr(REF_reftype(?(), ht))
  ;; test.spectec:6302.5-6302.56
  prod{ht : heaptype} {{0xFB} {`%`_u32(23):Bu32} {ht:Bheaptype}} => `REF.CAST`_instr(REF_reftype(?(NULL_null), ht))
  ;; test.spectec:6306.5-6306.43
  prod{x : idx} {{0xFB} {`%`_u32(0):Bu32} {x:Btypeidx}} => `STRUCT.NEW`_instr(x)
  ;; test.spectec:6307.5-6307.51
  prod{x : idx} {{0xFB} {`%`_u32(1):Bu32} {x:Btypeidx}} => `STRUCT.NEW_DEFAULT`_instr(x)
  ;; test.spectec:6308.5-6308.57
  prod{x : idx, i : fieldidx} {{0xFB} {`%`_u32(2):Bu32} {x:Btypeidx} {i:Bfieldidx}} => `STRUCT.GET`_instr(?(), x, i)
  ;; test.spectec:6309.5-6309.59
  prod{x : idx, i : fieldidx} {{0xFB} {`%`_u32(3):Bu32} {x:Btypeidx} {i:Bfieldidx}} => `STRUCT.GET`_instr(?(S_sx), x, i)
  ;; test.spectec:6310.5-6310.59
  prod{x : idx, i : fieldidx} {{0xFB} {`%`_u32(4):Bu32} {x:Btypeidx} {i:Bfieldidx}} => `STRUCT.GET`_instr(?(U_sx), x, i)
  ;; test.spectec:6311.5-6311.57
  prod{x : idx, i : fieldidx} {{0xFB} {`%`_u32(5):Bu32} {x:Btypeidx} {i:Bfieldidx}} => `STRUCT.SET`_instr(x, i)
  ;; test.spectec:6315.5-6315.42
  prod{x : idx} {{0xFB} {`%`_u32(6):Bu32} {x:Btypeidx}} => `ARRAY.NEW`_instr(x)
  ;; test.spectec:6316.5-6316.50
  prod{x : idx} {{0xFB} {`%`_u32(7):Bu32} {x:Btypeidx}} => `ARRAY.NEW_DEFAULT`_instr(x)
  ;; test.spectec:6317.5-6317.57
  prod{x : idx, n : n} {{0xFB} {`%`_u32(8):Bu32} {x:Btypeidx} {`%`_u32(n):Bu32}} => `ARRAY.NEW_FIXED`_instr(x, `%`_u32(n))
  ;; test.spectec:6318.5-6318.60
  prod{x : idx, y : idx} {{0xFB} {`%`_u32(9):Bu32} {x:Btypeidx} {y:Bdataidx}} => `ARRAY.NEW_DATA`_instr(x, y)
  ;; test.spectec:6319.5-6319.61
  prod{x : idx, y : idx} {{0xFB} {`%`_u32(10):Bu32} {x:Btypeidx} {y:Belemidx}} => `ARRAY.NEW_ELEM`_instr(x, y)
  ;; test.spectec:6320.5-6320.43
  prod{x : idx} {{0xFB} {`%`_u32(11):Bu32} {x:Btypeidx}} => `ARRAY.GET`_instr(?(), x)
  ;; test.spectec:6321.5-6321.45
  prod{x : idx} {{0xFB} {`%`_u32(12):Bu32} {x:Btypeidx}} => `ARRAY.GET`_instr(?(S_sx), x)
  ;; test.spectec:6322.5-6322.45
  prod{x : idx} {{0xFB} {`%`_u32(13):Bu32} {x:Btypeidx}} => `ARRAY.GET`_instr(?(U_sx), x)
  ;; test.spectec:6323.5-6323.43
  prod{x : idx} {{0xFB} {`%`_u32(14):Bu32} {x:Btypeidx}} => `ARRAY.SET`_instr(x)
  ;; test.spectec:6324.5-6324.30
  prod {{0xFB} {`%`_u32(15):Bu32}} => `ARRAY.LEN`_instr
  ;; test.spectec:6325.5-6325.44
  prod{x : idx} {{0xFB} {`%`_u32(16):Bu32} {x:Btypeidx}} => `ARRAY.FILL`_instr(x)
  ;; test.spectec:6326.5-6326.65
  prod{x_1 : idx, x_2 : idx} {{0xFB} {`%`_u32(17):Bu32} {x_1:Btypeidx} {x_2:Btypeidx}} => `ARRAY.COPY`_instr(x_1, x_2)
  ;; test.spectec:6327.5-6327.62
  prod{x : idx, y : idx} {{0xFB} {`%`_u32(18):Bu32} {x:Btypeidx} {y:Bdataidx}} => `ARRAY.INIT_DATA`_instr(x, y)
  ;; test.spectec:6328.5-6328.62
  prod{x : idx, y : idx} {{0xFB} {`%`_u32(19):Bu32} {x:Btypeidx} {y:Belemidx}} => `ARRAY.INIT_ELEM`_instr(x, y)
  ;; test.spectec:6332.5-6332.39
  prod {{0xFB} {`%`_u32(26):Bu32}} => `ANY.CONVERT_EXTERN`_instr
  ;; test.spectec:6333.5-6333.39
  prod {{0xFB} {`%`_u32(27):Bu32}} => `EXTERN.CONVERT_ANY`_instr
  ;; test.spectec:6337.5-6337.28
  prod {{0xFB} {`%`_u32(28):Bu32}} => `REF.I31`_instr
  ;; test.spectec:6338.5-6338.30
  prod {{0xFB} {`%`_u32(29):Bu32}} => `I31.GET`_instr(S_sx)
  ;; test.spectec:6339.5-6339.30
  prod {{0xFB} {`%`_u32(30):Bu32}} => `I31.GET`_instr(U_sx)
  ;; test.spectec:6346.5-6346.31
  prod{i : i32} {{0x41} {i:Bi32}} => CONST_instr(I32_numtype, i)
  ;; test.spectec:6347.5-6347.31
  prod{i : i64} {{0x42} {i:Bi64}} => CONST_instr(I64_numtype, i)
  ;; test.spectec:6348.5-6348.31
  prod{p : f32} {{0x43} {p:Bf32}} => CONST_instr(F32_numtype, p)
  ;; test.spectec:6349.5-6349.31
  prod{p : f64} {{0x44} {p:Bf64}} => CONST_instr(F64_numtype, p)
  ;; test.spectec:6353.5-6353.27
  prod 0x45 => TESTOP_instr(I32_numtype, EQZ_testop_)
  ;; test.spectec:6357.5-6357.25
  prod 0x46 => RELOP_instr(I32_numtype, EQ_relop_)
  ;; test.spectec:6358.5-6358.25
  prod 0x47 => RELOP_instr(I32_numtype, NE_relop_)
  ;; test.spectec:6359.5-6359.27
  prod 0x48 => RELOP_instr(I32_numtype, LT_relop_(S_sx))
  ;; test.spectec:6360.5-6360.27
  prod 0x49 => RELOP_instr(I32_numtype, LT_relop_(U_sx))
  ;; test.spectec:6361.5-6361.27
  prod 0x4A => RELOP_instr(I32_numtype, GT_relop_(S_sx))
  ;; test.spectec:6362.5-6362.27
  prod 0x4B => RELOP_instr(I32_numtype, GT_relop_(U_sx))
  ;; test.spectec:6363.5-6363.27
  prod 0x4C => RELOP_instr(I32_numtype, LE_relop_(S_sx))
  ;; test.spectec:6364.5-6364.27
  prod 0x4D => RELOP_instr(I32_numtype, LE_relop_(U_sx))
  ;; test.spectec:6365.5-6365.27
  prod 0x4E => RELOP_instr(I32_numtype, GE_relop_(S_sx))
  ;; test.spectec:6366.5-6366.27
  prod 0x4F => RELOP_instr(I32_numtype, GE_relop_(U_sx))
  ;; test.spectec:6370.5-6370.27
  prod 0x50 => TESTOP_instr(I64_numtype, EQZ_testop_)
  ;; test.spectec:6374.5-6374.25
  prod 0x51 => RELOP_instr(I64_numtype, EQ_relop_)
  ;; test.spectec:6375.5-6375.25
  prod 0x52 => RELOP_instr(I64_numtype, NE_relop_)
  ;; test.spectec:6376.5-6376.27
  prod 0x53 => RELOP_instr(I64_numtype, LT_relop_(S_sx))
  ;; test.spectec:6377.5-6377.27
  prod 0x54 => RELOP_instr(I64_numtype, LT_relop_(U_sx))
  ;; test.spectec:6378.5-6378.27
  prod 0x55 => RELOP_instr(I64_numtype, GT_relop_(S_sx))
  ;; test.spectec:6379.5-6379.27
  prod 0x56 => RELOP_instr(I64_numtype, GT_relop_(U_sx))
  ;; test.spectec:6380.5-6380.27
  prod 0x57 => RELOP_instr(I64_numtype, LE_relop_(S_sx))
  ;; test.spectec:6381.5-6381.27
  prod 0x58 => RELOP_instr(I64_numtype, LE_relop_(U_sx))
  ;; test.spectec:6382.5-6382.27
  prod 0x59 => RELOP_instr(I64_numtype, GE_relop_(S_sx))
  ;; test.spectec:6383.5-6383.27
  prod 0x5A => RELOP_instr(I64_numtype, GE_relop_(U_sx))
  ;; test.spectec:6387.5-6387.25
  prod 0x5B => RELOP_instr(F32_numtype, EQ_relop_)
  ;; test.spectec:6388.5-6388.25
  prod 0x5C => RELOP_instr(F32_numtype, NE_relop_)
  ;; test.spectec:6389.5-6389.25
  prod 0x5D => RELOP_instr(F32_numtype, LT_relop_)
  ;; test.spectec:6390.5-6390.25
  prod 0x5E => RELOP_instr(F32_numtype, GT_relop_)
  ;; test.spectec:6391.5-6391.25
  prod 0x5F => RELOP_instr(F32_numtype, LE_relop_)
  ;; test.spectec:6392.5-6392.25
  prod 0x60 => RELOP_instr(F32_numtype, GE_relop_)
  ;; test.spectec:6396.5-6396.25
  prod 0x61 => RELOP_instr(F64_numtype, EQ_relop_)
  ;; test.spectec:6397.5-6397.25
  prod 0x62 => RELOP_instr(F64_numtype, NE_relop_)
  ;; test.spectec:6398.5-6398.25
  prod 0x63 => RELOP_instr(F64_numtype, LT_relop_)
  ;; test.spectec:6399.5-6399.25
  prod 0x64 => RELOP_instr(F64_numtype, GT_relop_)
  ;; test.spectec:6400.5-6400.25
  prod 0x65 => RELOP_instr(F64_numtype, LE_relop_)
  ;; test.spectec:6401.5-6401.25
  prod 0x66 => RELOP_instr(F64_numtype, GE_relop_)
  ;; test.spectec:6405.5-6405.25
  prod 0x67 => UNOP_instr(I32_numtype, CLZ_unop_)
  ;; test.spectec:6406.5-6406.25
  prod 0x68 => UNOP_instr(I32_numtype, CTZ_unop_)
  ;; test.spectec:6407.5-6407.28
  prod 0x69 => UNOP_instr(I32_numtype, POPCNT_unop_)
  ;; test.spectec:6411.5-6411.26
  prod 0x6A => BINOP_instr(I32_numtype, ADD_binop_)
  ;; test.spectec:6412.5-6412.26
  prod 0x6B => BINOP_instr(I32_numtype, SUB_binop_)
  ;; test.spectec:6413.5-6413.26
  prod 0x6C => BINOP_instr(I32_numtype, MUL_binop_)
  ;; test.spectec:6414.5-6414.28
  prod 0x6D => BINOP_instr(I32_numtype, DIV_binop_(S_sx))
  ;; test.spectec:6415.5-6415.28
  prod 0x6E => BINOP_instr(I32_numtype, DIV_binop_(U_sx))
  ;; test.spectec:6416.5-6416.28
  prod 0x6F => BINOP_instr(I32_numtype, REM_binop_(S_sx))
  ;; test.spectec:6417.5-6417.28
  prod 0x70 => BINOP_instr(I32_numtype, REM_binop_(U_sx))
  ;; test.spectec:6418.5-6418.26
  prod 0x71 => BINOP_instr(I32_numtype, AND_binop_)
  ;; test.spectec:6419.5-6419.25
  prod 0x72 => BINOP_instr(I32_numtype, OR_binop_)
  ;; test.spectec:6420.5-6420.26
  prod 0x73 => BINOP_instr(I32_numtype, XOR_binop_)
  ;; test.spectec:6421.5-6421.26
  prod 0x74 => BINOP_instr(I32_numtype, SHL_binop_)
  ;; test.spectec:6422.5-6422.28
  prod 0x75 => BINOP_instr(I32_numtype, SHR_binop_(S_sx))
  ;; test.spectec:6423.5-6423.28
  prod 0x76 => BINOP_instr(I32_numtype, SHR_binop_(U_sx))
  ;; test.spectec:6424.5-6424.27
  prod 0x77 => BINOP_instr(I32_numtype, ROTL_binop_)
  ;; test.spectec:6425.5-6425.27
  prod 0x78 => BINOP_instr(I32_numtype, ROTR_binop_)
  ;; test.spectec:6429.5-6429.25
  prod 0x79 => UNOP_instr(I64_numtype, CLZ_unop_)
  ;; test.spectec:6430.5-6430.25
  prod 0x7A => UNOP_instr(I64_numtype, CTZ_unop_)
  ;; test.spectec:6431.5-6431.28
  prod 0x7B => UNOP_instr(I64_numtype, POPCNT_unop_)
  ;; test.spectec:6435.5-6435.31
  prod 0xC0 => UNOP_instr(I32_numtype, EXTEND_unop_(`%`_sz(8)))
  ;; test.spectec:6436.5-6436.32
  prod 0xC1 => UNOP_instr(I32_numtype, EXTEND_unop_(`%`_sz(16)))
  ;; test.spectec:6440.5-6440.31
  prod 0xC2 => UNOP_instr(I64_numtype, EXTEND_unop_(`%`_sz(8)))
  ;; test.spectec:6441.5-6441.32
  prod 0xC3 => UNOP_instr(I64_numtype, EXTEND_unop_(`%`_sz(16)))
  ;; test.spectec:6442.5-6442.32
  prod 0xC4 => UNOP_instr(I64_numtype, EXTEND_unop_(`%`_sz(32)))
  ;; test.spectec:6446.5-6446.26
  prod 0x7C => BINOP_instr(I64_numtype, ADD_binop_)
  ;; test.spectec:6447.5-6447.26
  prod 0x7D => BINOP_instr(I64_numtype, SUB_binop_)
  ;; test.spectec:6448.5-6448.26
  prod 0x7E => BINOP_instr(I64_numtype, MUL_binop_)
  ;; test.spectec:6449.5-6449.28
  prod 0x7F => BINOP_instr(I64_numtype, DIV_binop_(S_sx))
  ;; test.spectec:6450.5-6450.28
  prod 0x80 => BINOP_instr(I64_numtype, DIV_binop_(U_sx))
  ;; test.spectec:6451.5-6451.28
  prod 0x81 => BINOP_instr(I64_numtype, REM_binop_(S_sx))
  ;; test.spectec:6452.5-6452.28
  prod 0x82 => BINOP_instr(I64_numtype, REM_binop_(U_sx))
  ;; test.spectec:6453.5-6453.26
  prod 0x83 => BINOP_instr(I64_numtype, AND_binop_)
  ;; test.spectec:6454.5-6454.25
  prod 0x84 => BINOP_instr(I64_numtype, OR_binop_)
  ;; test.spectec:6455.5-6455.26
  prod 0x85 => BINOP_instr(I64_numtype, XOR_binop_)
  ;; test.spectec:6456.5-6456.26
  prod 0x86 => BINOP_instr(I64_numtype, SHL_binop_)
  ;; test.spectec:6457.5-6457.28
  prod 0x87 => BINOP_instr(I64_numtype, SHR_binop_(S_sx))
  ;; test.spectec:6458.5-6458.28
  prod 0x88 => BINOP_instr(I64_numtype, SHR_binop_(U_sx))
  ;; test.spectec:6459.5-6459.27
  prod 0x89 => BINOP_instr(I64_numtype, ROTL_binop_)
  ;; test.spectec:6460.5-6460.27
  prod 0x8A => BINOP_instr(I64_numtype, ROTR_binop_)
  ;; test.spectec:6464.5-6464.25
  prod 0x8B => UNOP_instr(F32_numtype, ABS_unop_)
  ;; test.spectec:6465.5-6465.25
  prod 0x8C => UNOP_instr(F32_numtype, NEG_unop_)
  ;; test.spectec:6466.5-6466.26
  prod 0x8D => UNOP_instr(F32_numtype, CEIL_unop_)
  ;; test.spectec:6467.5-6467.27
  prod 0x8E => UNOP_instr(F32_numtype, FLOOR_unop_)
  ;; test.spectec:6468.5-6468.27
  prod 0x8F => UNOP_instr(F32_numtype, TRUNC_unop_)
  ;; test.spectec:6469.5-6469.29
  prod 0x90 => UNOP_instr(F32_numtype, NEAREST_unop_)
  ;; test.spectec:6470.5-6470.26
  prod 0x91 => UNOP_instr(F32_numtype, SQRT_unop_)
  ;; test.spectec:6474.5-6474.26
  prod 0x92 => BINOP_instr(F32_numtype, ADD_binop_)
  ;; test.spectec:6475.5-6475.26
  prod 0x93 => BINOP_instr(F32_numtype, SUB_binop_)
  ;; test.spectec:6476.5-6476.26
  prod 0x94 => BINOP_instr(F32_numtype, MUL_binop_)
  ;; test.spectec:6477.5-6477.26
  prod 0x95 => BINOP_instr(F32_numtype, DIV_binop_)
  ;; test.spectec:6478.5-6478.26
  prod 0x96 => BINOP_instr(F32_numtype, MIN_binop_)
  ;; test.spectec:6479.5-6479.26
  prod 0x97 => BINOP_instr(F32_numtype, MAX_binop_)
  ;; test.spectec:6480.5-6480.31
  prod 0x98 => BINOP_instr(F32_numtype, COPYSIGN_binop_)
  ;; test.spectec:6484.5-6484.25
  prod 0x99 => UNOP_instr(F64_numtype, ABS_unop_)
  ;; test.spectec:6485.5-6485.25
  prod 0x9A => UNOP_instr(F64_numtype, NEG_unop_)
  ;; test.spectec:6486.5-6486.26
  prod 0x9B => UNOP_instr(F64_numtype, CEIL_unop_)
  ;; test.spectec:6487.5-6487.27
  prod 0x9C => UNOP_instr(F64_numtype, FLOOR_unop_)
  ;; test.spectec:6488.5-6488.27
  prod 0x9D => UNOP_instr(F64_numtype, TRUNC_unop_)
  ;; test.spectec:6489.5-6489.29
  prod 0x9E => UNOP_instr(F64_numtype, NEAREST_unop_)
  ;; test.spectec:6490.5-6490.26
  prod 0x9F => UNOP_instr(F64_numtype, SQRT_unop_)
  ;; test.spectec:6494.5-6494.26
  prod 0xA0 => BINOP_instr(F64_numtype, ADD_binop_)
  ;; test.spectec:6495.5-6495.26
  prod 0xA1 => BINOP_instr(F64_numtype, SUB_binop_)
  ;; test.spectec:6496.5-6496.26
  prod 0xA2 => BINOP_instr(F64_numtype, MUL_binop_)
  ;; test.spectec:6497.5-6497.26
  prod 0xA3 => BINOP_instr(F64_numtype, DIV_binop_)
  ;; test.spectec:6498.5-6498.26
  prod 0xA4 => BINOP_instr(F64_numtype, MIN_binop_)
  ;; test.spectec:6499.5-6499.26
  prod 0xA5 => BINOP_instr(F64_numtype, MAX_binop_)
  ;; test.spectec:6500.5-6500.31
  prod 0xA6 => BINOP_instr(F64_numtype, COPYSIGN_binop_)
  ;; test.spectec:6505.5-6505.31
  prod 0xA7 => CVTOP_instr(I32_numtype, I64_numtype, WRAP_cvtop__)
  ;; test.spectec:6506.5-6506.34
  prod 0xA8 => CVTOP_instr(I32_numtype, F32_numtype, TRUNC_cvtop__(S_sx))
  ;; test.spectec:6507.5-6507.34
  prod 0xA9 => CVTOP_instr(I32_numtype, F32_numtype, TRUNC_cvtop__(U_sx))
  ;; test.spectec:6508.5-6508.34
  prod 0xAA => CVTOP_instr(I32_numtype, F64_numtype, TRUNC_cvtop__(S_sx))
  ;; test.spectec:6509.5-6509.34
  prod 0xAB => CVTOP_instr(I32_numtype, F64_numtype, TRUNC_cvtop__(U_sx))
  ;; test.spectec:6510.5-6510.35
  prod 0xAC => CVTOP_instr(I64_numtype, I32_numtype, EXTEND_cvtop__(S_sx))
  ;; test.spectec:6511.5-6511.35
  prod 0xAD => CVTOP_instr(I64_numtype, I32_numtype, EXTEND_cvtop__(U_sx))
  ;; test.spectec:6512.5-6512.34
  prod 0xAE => CVTOP_instr(I64_numtype, F32_numtype, TRUNC_cvtop__(S_sx))
  ;; test.spectec:6513.5-6513.34
  prod 0xAF => CVTOP_instr(I64_numtype, F32_numtype, TRUNC_cvtop__(U_sx))
  ;; test.spectec:6514.5-6514.34
  prod 0xB0 => CVTOP_instr(I64_numtype, F64_numtype, TRUNC_cvtop__(S_sx))
  ;; test.spectec:6515.5-6515.34
  prod 0xB1 => CVTOP_instr(I64_numtype, F64_numtype, TRUNC_cvtop__(U_sx))
  ;; test.spectec:6516.5-6516.36
  prod 0xB2 => CVTOP_instr(F32_numtype, I32_numtype, CONVERT_cvtop__(S_sx))
  ;; test.spectec:6517.5-6517.36
  prod 0xB3 => CVTOP_instr(F32_numtype, I32_numtype, CONVERT_cvtop__(U_sx))
  ;; test.spectec:6518.5-6518.36
  prod 0xB4 => CVTOP_instr(F32_numtype, I64_numtype, CONVERT_cvtop__(S_sx))
  ;; test.spectec:6519.5-6519.36
  prod 0xB5 => CVTOP_instr(F32_numtype, I64_numtype, CONVERT_cvtop__(U_sx))
  ;; test.spectec:6520.5-6520.33
  prod 0xB6 => CVTOP_instr(F32_numtype, F64_numtype, DEMOTE_cvtop__)
  ;; test.spectec:6521.5-6521.36
  prod 0xB7 => CVTOP_instr(F64_numtype, I32_numtype, CONVERT_cvtop__(S_sx))
  ;; test.spectec:6522.5-6522.36
  prod 0xB8 => CVTOP_instr(F64_numtype, I32_numtype, CONVERT_cvtop__(U_sx))
  ;; test.spectec:6523.5-6523.36
  prod 0xB9 => CVTOP_instr(F64_numtype, I64_numtype, CONVERT_cvtop__(S_sx))
  ;; test.spectec:6524.5-6524.36
  prod 0xBA => CVTOP_instr(F64_numtype, I64_numtype, CONVERT_cvtop__(U_sx))
  ;; test.spectec:6525.5-6525.34
  prod 0xBB => CVTOP_instr(F64_numtype, F32_numtype, PROMOTE_cvtop__)
  ;; test.spectec:6526.5-6526.38
  prod 0xBC => CVTOP_instr(I32_numtype, F32_numtype, REINTERPRET_cvtop__)
  ;; test.spectec:6527.5-6527.38
  prod 0xBD => CVTOP_instr(I64_numtype, F64_numtype, REINTERPRET_cvtop__)
  ;; test.spectec:6528.5-6528.38
  prod 0xBE => CVTOP_instr(F32_numtype, I32_numtype, REINTERPRET_cvtop__)
  ;; test.spectec:6529.5-6529.38
  prod 0xBF => CVTOP_instr(F64_numtype, I64_numtype, REINTERPRET_cvtop__)
  ;; test.spectec:6533.5-6533.45
  prod {{0xFC} {`%`_u32(0):Bu32}} => CVTOP_instr(I32_numtype, F32_numtype, TRUNC_SAT_cvtop__(S_sx))
  ;; test.spectec:6534.5-6534.45
  prod {{0xFC} {`%`_u32(1):Bu32}} => CVTOP_instr(I32_numtype, F32_numtype, TRUNC_SAT_cvtop__(U_sx))
  ;; test.spectec:6535.5-6535.45
  prod {{0xFC} {`%`_u32(2):Bu32}} => CVTOP_instr(I32_numtype, F64_numtype, TRUNC_SAT_cvtop__(S_sx))
  ;; test.spectec:6536.5-6536.45
  prod {{0xFC} {`%`_u32(3):Bu32}} => CVTOP_instr(I32_numtype, F64_numtype, TRUNC_SAT_cvtop__(U_sx))
  ;; test.spectec:6537.5-6537.45
  prod {{0xFC} {`%`_u32(4):Bu32}} => CVTOP_instr(I64_numtype, F32_numtype, TRUNC_SAT_cvtop__(S_sx))
  ;; test.spectec:6538.5-6538.45
  prod {{0xFC} {`%`_u32(5):Bu32}} => CVTOP_instr(I64_numtype, F32_numtype, TRUNC_SAT_cvtop__(U_sx))
  ;; test.spectec:6539.5-6539.45
  prod {{0xFC} {`%`_u32(6):Bu32}} => CVTOP_instr(I64_numtype, F64_numtype, TRUNC_SAT_cvtop__(S_sx))
  ;; test.spectec:6540.5-6540.45
  prod {{0xFC} {`%`_u32(7):Bu32}} => CVTOP_instr(I64_numtype, F64_numtype, TRUNC_SAT_cvtop__(U_sx))
  ;; test.spectec:6550.5-6550.50
  prod{x : idx, ao : memarg} {{0xFD} {`%`_u32(0):Bu32} {(x, ao):Bmemarg}} => VLOAD_instr(V128_vectype, ?(), x, ao)
  ;; test.spectec:6551.5-6551.70
  prod{x : idx, ao : memarg} {{0xFD} {`%`_u32(1):Bu32} {(x, ao):Bmemarg}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(8), 8, S_sx)), x, ao)
  ;; test.spectec:6552.5-6552.70
  prod{x : idx, ao : memarg} {{0xFD} {`%`_u32(2):Bu32} {(x, ao):Bmemarg}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(8), 8, U_sx)), x, ao)
  ;; test.spectec:6553.5-6553.71
  prod{x : idx, ao : memarg} {{0xFD} {`%`_u32(3):Bu32} {(x, ao):Bmemarg}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(16), 4, S_sx)), x, ao)
  ;; test.spectec:6554.5-6554.71
  prod{x : idx, ao : memarg} {{0xFD} {`%`_u32(4):Bu32} {(x, ao):Bmemarg}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(16), 4, U_sx)), x, ao)
  ;; test.spectec:6555.5-6555.71
  prod{x : idx, ao : memarg} {{0xFD} {`%`_u32(5):Bu32} {(x, ao):Bmemarg}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(32), 2, S_sx)), x, ao)
  ;; test.spectec:6556.5-6556.71
  prod{x : idx, ao : memarg} {{0xFD} {`%`_u32(6):Bu32} {(x, ao):Bmemarg}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(32), 2, U_sx)), x, ao)
  ;; test.spectec:6557.5-6557.61
  prod{x : idx, ao : memarg} {{0xFD} {`%`_u32(7):Bu32} {(x, ao):Bmemarg}} => VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(8))), x, ao)
  ;; test.spectec:6558.5-6558.62
  prod{x : idx, ao : memarg} {{0xFD} {`%`_u32(8):Bu32} {(x, ao):Bmemarg}} => VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(16))), x, ao)
  ;; test.spectec:6559.5-6559.62
  prod{x : idx, ao : memarg} {{0xFD} {`%`_u32(9):Bu32} {(x, ao):Bmemarg}} => VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(32))), x, ao)
  ;; test.spectec:6560.5-6560.63
  prod{x : idx, ao : memarg} {{0xFD} {`%`_u32(10):Bu32} {(x, ao):Bmemarg}} => VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(64))), x, ao)
  ;; test.spectec:6561.5-6561.52
  prod{x : idx, ao : memarg} {{0xFD} {`%`_u32(11):Bu32} {(x, ao):Bmemarg}} => VSTORE_instr(V128_vectype, x, ao)
  ;; test.spectec:6562.5-6562.72
  prod{x : idx, ao : memarg, i : laneidx} {{0xFD} {`%`_u32(84):Bu32} {(x, ao):Bmemarg} {i:Blaneidx}} => VLOAD_LANE_instr(V128_vectype, `%`_sz(8), x, ao, i)
  ;; test.spectec:6563.5-6563.73
  prod{x : idx, ao : memarg, i : laneidx} {{0xFD} {`%`_u32(85):Bu32} {(x, ao):Bmemarg} {i:Blaneidx}} => VLOAD_LANE_instr(V128_vectype, `%`_sz(16), x, ao, i)
  ;; test.spectec:6564.5-6564.73
  prod{x : idx, ao : memarg, i : laneidx} {{0xFD} {`%`_u32(86):Bu32} {(x, ao):Bmemarg} {i:Blaneidx}} => VLOAD_LANE_instr(V128_vectype, `%`_sz(32), x, ao, i)
  ;; test.spectec:6565.5-6565.73
  prod{x : idx, ao : memarg, i : laneidx} {{0xFD} {`%`_u32(87):Bu32} {(x, ao):Bmemarg} {i:Blaneidx}} => VLOAD_LANE_instr(V128_vectype, `%`_sz(64), x, ao, i)
  ;; test.spectec:6566.5-6566.73
  prod{x : idx, ao : memarg, i : laneidx} {{0xFD} {`%`_u32(88):Bu32} {(x, ao):Bmemarg} {i:Blaneidx}} => VSTORE_LANE_instr(V128_vectype, `%`_sz(8), x, ao, i)
  ;; test.spectec:6567.5-6567.74
  prod{x : idx, ao : memarg, i : laneidx} {{0xFD} {`%`_u32(89):Bu32} {(x, ao):Bmemarg} {i:Blaneidx}} => VSTORE_LANE_instr(V128_vectype, `%`_sz(16), x, ao, i)
  ;; test.spectec:6568.5-6568.74
  prod{x : idx, ao : memarg, i : laneidx} {{0xFD} {`%`_u32(90):Bu32} {(x, ao):Bmemarg} {i:Blaneidx}} => VSTORE_LANE_instr(V128_vectype, `%`_sz(32), x, ao, i)
  ;; test.spectec:6569.5-6569.74
  prod{x : idx, ao : memarg, i : laneidx} {{0xFD} {`%`_u32(91):Bu32} {(x, ao):Bmemarg} {i:Blaneidx}} => VSTORE_LANE_instr(V128_vectype, `%`_sz(64), x, ao, i)
  ;; test.spectec:6570.5-6570.62
  prod{x : idx, ao : memarg} {{0xFD} {`%`_u32(92):Bu32} {(x, ao):Bmemarg}} => VLOAD_instr(V128_vectype, ?(ZERO_vloadop_(`%`_sz(32))), x, ao)
  ;; test.spectec:6571.5-6571.62
  prod{x : idx, ao : memarg} {{0xFD} {`%`_u32(93):Bu32} {(x, ao):Bmemarg}} => VLOAD_instr(V128_vectype, ?(ZERO_vloadop_(`%`_sz(64))), x, ao)
  ;; test.spectec:6575.5-6575.72
  prod{`b*` : byte*} {{0xFD} {`%`_u32(12):Bu32} {b:Bbyte^16{b <- `b*`}}} => VCONST_instr(V128_vectype, $inv_ibytes_(128, b^16{b <- `b*`}))
  ;; test.spectec:6579.5-6579.61
  prod{`l*` : labelidx*} {{0xFD} {`%`_u32(13):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx^16{l <- `l*`}}} => VSHUFFLE_instr(`%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(16))), `%`_laneidx(l!`%`_labelidx.0)^16{l <- `l*`})
  ;; test.spectec:6580.5-6580.49
  prod {{0xFD} {`%`_u32(14):Bu32}} => VSWIZZLOP_instr(`%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(16))), SWIZZLE_vswizzlop_)
  ;; test.spectec:6581.5-6581.58
  prod {{0xFD} {`%`_u32(256):Bu32}} => VSWIZZLOP_instr(`%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(16))), RELAXED_SWIZZLE_vswizzlop_)
  ;; test.spectec:6585.5-6585.38
  prod {{0xFD} {`%`_u32(15):Bu32}} => VSPLAT_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)))
  ;; test.spectec:6586.5-6586.38
  prod {{0xFD} {`%`_u32(16):Bu32}} => VSPLAT_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)))
  ;; test.spectec:6587.5-6587.38
  prod {{0xFD} {`%`_u32(17):Bu32}} => VSPLAT_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)))
  ;; test.spectec:6588.5-6588.38
  prod {{0xFD} {`%`_u32(18):Bu32}} => VSPLAT_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)))
  ;; test.spectec:6589.5-6589.38
  prod {{0xFD} {`%`_u32(19):Bu32}} => VSPLAT_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)))
  ;; test.spectec:6590.5-6590.38
  prod {{0xFD} {`%`_u32(20):Bu32}} => VSPLAT_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)))
  ;; test.spectec:6594.5-6594.60
  prod{l : labelidx} {{0xFD} {`%`_u32(21):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ?(S_sx), `%`_laneidx(l!`%`_labelidx.0))
  ;; test.spectec:6595.5-6595.60
  prod{l : labelidx} {{0xFD} {`%`_u32(22):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ?(U_sx), `%`_laneidx(l!`%`_labelidx.0))
  ;; test.spectec:6596.5-6596.58
  prod{l : labelidx} {{0xFD} {`%`_u32(23):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), `%`_laneidx(l!`%`_labelidx.0))
  ;; test.spectec:6597.5-6597.60
  prod{l : labelidx} {{0xFD} {`%`_u32(24):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ?(S_sx), `%`_laneidx(l!`%`_labelidx.0))
  ;; test.spectec:6598.5-6598.60
  prod{l : labelidx} {{0xFD} {`%`_u32(25):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ?(U_sx), `%`_laneidx(l!`%`_labelidx.0))
  ;; test.spectec:6599.5-6599.58
  prod{l : labelidx} {{0xFD} {`%`_u32(26):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), `%`_laneidx(l!`%`_labelidx.0))
  ;; test.spectec:6600.5-6600.58
  prod{l : labelidx} {{0xFD} {`%`_u32(27):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), ?(), `%`_laneidx(l!`%`_labelidx.0))
  ;; test.spectec:6601.5-6601.58
  prod{l : labelidx} {{0xFD} {`%`_u32(28):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%`_laneidx(l!`%`_labelidx.0))
  ;; test.spectec:6602.5-6602.58
  prod{l : labelidx} {{0xFD} {`%`_u32(29):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), ?(), `%`_laneidx(l!`%`_labelidx.0))
  ;; test.spectec:6603.5-6603.58
  prod{l : labelidx} {{0xFD} {`%`_u32(30):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), `%`_laneidx(l!`%`_labelidx.0))
  ;; test.spectec:6604.5-6604.58
  prod{l : labelidx} {{0xFD} {`%`_u32(31):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), ?(), `%`_laneidx(l!`%`_labelidx.0))
  ;; test.spectec:6605.5-6605.58
  prod{l : labelidx} {{0xFD} {`%`_u32(32):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), `%`_laneidx(l!`%`_labelidx.0))
  ;; test.spectec:6606.5-6606.58
  prod{l : labelidx} {{0xFD} {`%`_u32(33):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), ?(), `%`_laneidx(l!`%`_labelidx.0))
  ;; test.spectec:6607.5-6607.58
  prod{l : labelidx} {{0xFD} {`%`_u32(34):Bu32} {`%`_laneidx(l!`%`_labelidx.0):Blaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), `%`_laneidx(l!`%`_labelidx.0))
  ;; test.spectec:6611.5-6611.41
  prod {{0xFD} {`%`_u32(35):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), EQ_vrelop_)
  ;; test.spectec:6612.5-6612.41
  prod {{0xFD} {`%`_u32(36):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), NE_vrelop_)
  ;; test.spectec:6613.5-6613.43
  prod {{0xFD} {`%`_u32(37):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), LT_vrelop_(S_sx))
  ;; test.spectec:6614.5-6614.43
  prod {{0xFD} {`%`_u32(38):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), LT_vrelop_(U_sx))
  ;; test.spectec:6615.5-6615.43
  prod {{0xFD} {`%`_u32(39):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), GT_vrelop_(S_sx))
  ;; test.spectec:6616.5-6616.43
  prod {{0xFD} {`%`_u32(40):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), GT_vrelop_(U_sx))
  ;; test.spectec:6617.5-6617.43
  prod {{0xFD} {`%`_u32(41):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), LE_vrelop_(S_sx))
  ;; test.spectec:6618.5-6618.43
  prod {{0xFD} {`%`_u32(42):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), LE_vrelop_(U_sx))
  ;; test.spectec:6619.5-6619.43
  prod {{0xFD} {`%`_u32(43):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), GE_vrelop_(S_sx))
  ;; test.spectec:6620.5-6620.43
  prod {{0xFD} {`%`_u32(44):Bu32}} => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), GE_vrelop_(U_sx))
  ;; test.spectec:6624.5-6624.41
  prod {{0xFD} {`%`_u32(45):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), EQ_vrelop_)
  ;; test.spectec:6625.5-6625.41
  prod {{0xFD} {`%`_u32(46):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), NE_vrelop_)
  ;; test.spectec:6626.5-6626.43
  prod {{0xFD} {`%`_u32(47):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), LT_vrelop_(S_sx))
  ;; test.spectec:6627.5-6627.43
  prod {{0xFD} {`%`_u32(48):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), LT_vrelop_(U_sx))
  ;; test.spectec:6628.5-6628.43
  prod {{0xFD} {`%`_u32(49):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), GT_vrelop_(S_sx))
  ;; test.spectec:6629.5-6629.43
  prod {{0xFD} {`%`_u32(50):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), GT_vrelop_(U_sx))
  ;; test.spectec:6630.5-6630.43
  prod {{0xFD} {`%`_u32(51):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), LE_vrelop_(S_sx))
  ;; test.spectec:6631.5-6631.43
  prod {{0xFD} {`%`_u32(52):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), LE_vrelop_(U_sx))
  ;; test.spectec:6632.5-6632.43
  prod {{0xFD} {`%`_u32(53):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), GE_vrelop_(S_sx))
  ;; test.spectec:6633.5-6633.43
  prod {{0xFD} {`%`_u32(54):Bu32}} => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), GE_vrelop_(U_sx))
  ;; test.spectec:6637.5-6637.41
  prod {{0xFD} {`%`_u32(55):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), EQ_vrelop_)
  ;; test.spectec:6638.5-6638.41
  prod {{0xFD} {`%`_u32(56):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), NE_vrelop_)
  ;; test.spectec:6639.5-6639.43
  prod {{0xFD} {`%`_u32(57):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), LT_vrelop_(S_sx))
  ;; test.spectec:6640.5-6640.43
  prod {{0xFD} {`%`_u32(58):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), LT_vrelop_(U_sx))
  ;; test.spectec:6641.5-6641.43
  prod {{0xFD} {`%`_u32(59):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), GT_vrelop_(S_sx))
  ;; test.spectec:6642.5-6642.43
  prod {{0xFD} {`%`_u32(60):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), GT_vrelop_(U_sx))
  ;; test.spectec:6643.5-6643.43
  prod {{0xFD} {`%`_u32(61):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), LE_vrelop_(S_sx))
  ;; test.spectec:6644.5-6644.43
  prod {{0xFD} {`%`_u32(62):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), LE_vrelop_(U_sx))
  ;; test.spectec:6645.5-6645.43
  prod {{0xFD} {`%`_u32(63):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), GE_vrelop_(S_sx))
  ;; test.spectec:6646.5-6646.43
  prod {{0xFD} {`%`_u32(64):Bu32}} => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), GE_vrelop_(U_sx))
  ;; test.spectec:6650.5-6650.41
  prod {{0xFD} {`%`_u32(65):Bu32}} => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), EQ_vrelop_)
  ;; test.spectec:6651.5-6651.41
  prod {{0xFD} {`%`_u32(66):Bu32}} => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), NE_vrelop_)
  ;; test.spectec:6652.5-6652.41
  prod {{0xFD} {`%`_u32(67):Bu32}} => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), LT_vrelop_)
  ;; test.spectec:6653.5-6653.41
  prod {{0xFD} {`%`_u32(68):Bu32}} => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), GT_vrelop_)
  ;; test.spectec:6654.5-6654.41
  prod {{0xFD} {`%`_u32(69):Bu32}} => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), LE_vrelop_)
  ;; test.spectec:6655.5-6655.41
  prod {{0xFD} {`%`_u32(70):Bu32}} => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), GE_vrelop_)
  ;; test.spectec:6659.5-6659.41
  prod {{0xFD} {`%`_u32(71):Bu32}} => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), EQ_vrelop_)
  ;; test.spectec:6660.5-6660.41
  prod {{0xFD} {`%`_u32(72):Bu32}} => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), NE_vrelop_)
  ;; test.spectec:6661.5-6661.41
  prod {{0xFD} {`%`_u32(73):Bu32}} => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), LT_vrelop_)
  ;; test.spectec:6662.5-6662.41
  prod {{0xFD} {`%`_u32(74):Bu32}} => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), GT_vrelop_)
  ;; test.spectec:6663.5-6663.41
  prod {{0xFD} {`%`_u32(75):Bu32}} => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), LE_vrelop_)
  ;; test.spectec:6664.5-6664.41
  prod {{0xFD} {`%`_u32(76):Bu32}} => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), GE_vrelop_)
  ;; test.spectec:6668.5-6668.36
  prod {{0xFD} {`%`_u32(77):Bu32}} => VVUNOP_instr(V128_vectype, NOT_vvunop)
  ;; test.spectec:6672.5-6672.37
  prod {{0xFD} {`%`_u32(78):Bu32}} => VVBINOP_instr(V128_vectype, AND_vvbinop)
  ;; test.spectec:6673.5-6673.40
  prod {{0xFD} {`%`_u32(79):Bu32}} => VVBINOP_instr(V128_vectype, ANDNOT_vvbinop)
  ;; test.spectec:6674.5-6674.36
  prod {{0xFD} {`%`_u32(80):Bu32}} => VVBINOP_instr(V128_vectype, OR_vvbinop)
  ;; test.spectec:6675.5-6675.37
  prod {{0xFD} {`%`_u32(81):Bu32}} => VVBINOP_instr(V128_vectype, XOR_vvbinop)
  ;; test.spectec:6679.5-6679.44
  prod {{0xFD} {`%`_u32(82):Bu32}} => VVTERNOP_instr(V128_vectype, BITSELECT_vvternop)
  ;; test.spectec:6683.5-6683.43
  prod {{0xFD} {`%`_u32(83):Bu32}} => VVTESTOP_instr(V128_vectype, ANY_TRUE_vvtestop)
  ;; test.spectec:6687.5-6687.41
  prod {{0xFD} {`%`_u32(96):Bu32}} => VUNOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ABS_vunop_)
  ;; test.spectec:6688.5-6688.41
  prod {{0xFD} {`%`_u32(97):Bu32}} => VUNOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), NEG_vunop_)
  ;; test.spectec:6689.5-6689.44
  prod {{0xFD} {`%`_u32(98):Bu32}} => VUNOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), POPCNT_vunop_)
  ;; test.spectec:6693.5-6693.48
  prod {{0xFD} {`%`_u32(99):Bu32}} => VTESTOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ALL_TRUE_vtestop_)
  ;; test.spectec:6697.5-6697.41
  prod {{0xFD} {`%`_u32(100):Bu32}} => VBITMASK_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))))
  ;; test.spectec:6701.5-6701.53
  prod {{0xFD} {`%`_u32(101):Bu32}} => VNARROW_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), S_sx)
  ;; test.spectec:6702.5-6702.53
  prod {{0xFD} {`%`_u32(102):Bu32}} => VNARROW_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), U_sx)
  ;; test.spectec:6706.5-6706.45
  prod {{0xFD} {`%`_u32(107):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), SHL_vshiftop_)
  ;; test.spectec:6707.5-6707.47
  prod {{0xFD} {`%`_u32(108):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), SHR_vshiftop_(S_sx))
  ;; test.spectec:6708.5-6708.47
  prod {{0xFD} {`%`_u32(109):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), SHR_vshiftop_(U_sx))
  ;; test.spectec:6712.5-6712.43
  prod {{0xFD} {`%`_u32(110):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ADD_vbinop_)
  ;; test.spectec:6713.5-6713.49
  prod {{0xFD} {`%`_u32(111):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ADD_SAT_vbinop_(S_sx))
  ;; test.spectec:6714.5-6714.49
  prod {{0xFD} {`%`_u32(112):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ADD_SAT_vbinop_(U_sx))
  ;; test.spectec:6715.5-6715.43
  prod {{0xFD} {`%`_u32(113):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), SUB_vbinop_)
  ;; test.spectec:6716.5-6716.49
  prod {{0xFD} {`%`_u32(114):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), SUB_SAT_vbinop_(S_sx))
  ;; test.spectec:6717.5-6717.49
  prod {{0xFD} {`%`_u32(115):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), SUB_SAT_vbinop_(U_sx))
  ;; test.spectec:6718.5-6718.45
  prod {{0xFD} {`%`_u32(118):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), MIN_vbinop_(S_sx))
  ;; test.spectec:6719.5-6719.45
  prod {{0xFD} {`%`_u32(119):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), MIN_vbinop_(U_sx))
  ;; test.spectec:6720.5-6720.45
  prod {{0xFD} {`%`_u32(120):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), MAX_vbinop_(S_sx))
  ;; test.spectec:6721.5-6721.45
  prod {{0xFD} {`%`_u32(121):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), MAX_vbinop_(U_sx))
  ;; test.spectec:6722.5-6722.46
  prod {{0xFD} {`%`_u32(123):Bu32}} => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), AVGRU_vbinop_)
  ;; test.spectec:6726.5-6726.70
  prod {{0xFD} {`%`_u32(124):Bu32}} => VEXTUNOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTADD_PAIRWISE_vextunop__(S_sx))
  ;; test.spectec:6727.5-6727.70
  prod {{0xFD} {`%`_u32(125):Bu32}} => VEXTUNOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTADD_PAIRWISE_vextunop__(U_sx))
  ;; test.spectec:6731.5-6731.42
  prod {{0xFD} {`%`_u32(128):Bu32}} => VUNOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ABS_vunop_)
  ;; test.spectec:6732.5-6732.42
  prod {{0xFD} {`%`_u32(129):Bu32}} => VUNOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), NEG_vunop_)
  ;; test.spectec:6736.5-6736.53
  prod {{0xFD} {`%`_u32(130):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), Q15MULR_SATS_vbinop_)
  ;; test.spectec:6737.5-6737.43
  prod {{0xFD} {`%`_u32(142):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ADD_vbinop_)
  ;; test.spectec:6738.5-6738.49
  prod {{0xFD} {`%`_u32(143):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ADD_SAT_vbinop_(S_sx))
  ;; test.spectec:6739.5-6739.49
  prod {{0xFD} {`%`_u32(144):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ADD_SAT_vbinop_(U_sx))
  ;; test.spectec:6740.5-6740.43
  prod {{0xFD} {`%`_u32(145):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), SUB_vbinop_)
  ;; test.spectec:6741.5-6741.49
  prod {{0xFD} {`%`_u32(146):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), SUB_SAT_vbinop_(S_sx))
  ;; test.spectec:6742.5-6742.49
  prod {{0xFD} {`%`_u32(147):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), SUB_SAT_vbinop_(U_sx))
  ;; test.spectec:6743.5-6743.43
  prod {{0xFD} {`%`_u32(149):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), MUL_vbinop_)
  ;; test.spectec:6744.5-6744.45
  prod {{0xFD} {`%`_u32(150):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), MIN_vbinop_(S_sx))
  ;; test.spectec:6745.5-6745.45
  prod {{0xFD} {`%`_u32(151):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), MIN_vbinop_(U_sx))
  ;; test.spectec:6746.5-6746.45
  prod {{0xFD} {`%`_u32(152):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), MAX_vbinop_(S_sx))
  ;; test.spectec:6747.5-6747.45
  prod {{0xFD} {`%`_u32(153):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), MAX_vbinop_(U_sx))
  ;; test.spectec:6748.5-6748.46
  prod {{0xFD} {`%`_u32(155):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), AVGRU_vbinop_)
  ;; test.spectec:6749.5-6749.57
  prod {{0xFD} {`%`_u32(273):Bu32}} => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), RELAXED_Q15MULRS_vbinop_)
  ;; test.spectec:6753.5-6753.49
  prod {{0xFD} {`%`_u32(131):Bu32}} => VTESTOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ALL_TRUE_vtestop_)
  ;; test.spectec:6757.5-6757.41
  prod {{0xFD} {`%`_u32(132):Bu32}} => VBITMASK_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))))
  ;; test.spectec:6761.5-6761.53
  prod {{0xFD} {`%`_u32(133):Bu32}} => VNARROW_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), S_sx)
  ;; test.spectec:6762.5-6762.53
  prod {{0xFD} {`%`_u32(134):Bu32}} => VNARROW_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), U_sx)
  ;; test.spectec:6766.5-6766.63
  prod {{0xFD} {`%`_u32(135):Bu32}} => VCVTOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), `%X%`_shape(I8_lanetype, `%`_dim(16)), EXTEND_vcvtop__(LOW_half, S_sx))
  ;; test.spectec:6767.5-6767.64
  prod {{0xFD} {`%`_u32(136):Bu32}} => VCVTOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), `%X%`_shape(I8_lanetype, `%`_dim(16)), EXTEND_vcvtop__(HIGH_half, S_sx))
  ;; test.spectec:6768.5-6768.63
  prod {{0xFD} {`%`_u32(137):Bu32}} => VCVTOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), `%X%`_shape(I8_lanetype, `%`_dim(16)), EXTEND_vcvtop__(LOW_half, U_sx))
  ;; test.spectec:6769.5-6769.64
  prod {{0xFD} {`%`_u32(138):Bu32}} => VCVTOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), `%X%`_shape(I8_lanetype, `%`_dim(16)), EXTEND_vcvtop__(HIGH_half, U_sx))
  ;; test.spectec:6773.5-6773.45
  prod {{0xFD} {`%`_u32(139):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), SHL_vshiftop_)
  ;; test.spectec:6774.5-6774.47
  prod {{0xFD} {`%`_u32(140):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), SHR_vshiftop_(S_sx))
  ;; test.spectec:6775.5-6775.47
  prod {{0xFD} {`%`_u32(141):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), SHR_vshiftop_(U_sx))
  ;; test.spectec:6779.5-6779.66
  prod {{0xFD} {`%`_u32(156):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTMUL_vextbinop__(LOW_half, S_sx))
  ;; test.spectec:6780.5-6780.67
  prod {{0xFD} {`%`_u32(157):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTMUL_vextbinop__(HIGH_half, S_sx))
  ;; test.spectec:6781.5-6781.66
  prod {{0xFD} {`%`_u32(158):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTMUL_vextbinop__(LOW_half, U_sx))
  ;; test.spectec:6782.5-6782.67
  prod {{0xFD} {`%`_u32(159):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTMUL_vextbinop__(HIGH_half, U_sx))
  ;; test.spectec:6783.5-6783.67
  prod {{0xFD} {`%`_u32(274):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), RELAXED_DOTS_vextbinop__)
  ;; test.spectec:6787.5-6787.70
  prod {{0xFD} {`%`_u32(126):Bu32}} => VEXTUNOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTADD_PAIRWISE_vextunop__(S_sx))
  ;; test.spectec:6788.5-6788.70
  prod {{0xFD} {`%`_u32(127):Bu32}} => VEXTUNOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTADD_PAIRWISE_vextunop__(U_sx))
  ;; test.spectec:6792.5-6792.42
  prod {{0xFD} {`%`_u32(160):Bu32}} => VUNOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), ABS_vunop_)
  ;; test.spectec:6793.5-6793.42
  prod {{0xFD} {`%`_u32(161):Bu32}} => VUNOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), NEG_vunop_)
  ;; test.spectec:6797.5-6797.49
  prod {{0xFD} {`%`_u32(163):Bu32}} => VTESTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), ALL_TRUE_vtestop_)
  ;; test.spectec:6801.5-6801.41
  prod {{0xFD} {`%`_u32(164):Bu32}} => VBITMASK_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))))
  ;; test.spectec:6805.5-6805.63
  prod {{0xFD} {`%`_u32(167):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(I16_lanetype, `%`_dim(8)), EXTEND_vcvtop__(LOW_half, S_sx))
  ;; test.spectec:6806.5-6806.64
  prod {{0xFD} {`%`_u32(168):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(I16_lanetype, `%`_dim(8)), EXTEND_vcvtop__(HIGH_half, S_sx))
  ;; test.spectec:6807.5-6807.63
  prod {{0xFD} {`%`_u32(169):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(I16_lanetype, `%`_dim(8)), EXTEND_vcvtop__(LOW_half, U_sx))
  ;; test.spectec:6808.5-6808.64
  prod {{0xFD} {`%`_u32(170):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(I16_lanetype, `%`_dim(8)), EXTEND_vcvtop__(HIGH_half, U_sx))
  ;; test.spectec:6812.5-6812.45
  prod {{0xFD} {`%`_u32(171):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), SHL_vshiftop_)
  ;; test.spectec:6813.5-6813.49
  prod {{0xFD} {`%`_u32(172):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), SHR_vshiftop_(S_sx))
  ;; test.spectec:6814.5-6814.49
  prod {{0xFD} {`%`_u32(173):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), SHR_vshiftop_(U_sx))
  ;; test.spectec:6818.5-6818.43
  prod {{0xFD} {`%`_u32(174):Bu32}} => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), ADD_vbinop_)
  ;; test.spectec:6819.5-6819.43
  prod {{0xFD} {`%`_u32(177):Bu32}} => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), SUB_vbinop_)
  ;; test.spectec:6820.5-6820.43
  prod {{0xFD} {`%`_u32(181):Bu32}} => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), MUL_vbinop_)
  ;; test.spectec:6821.5-6821.45
  prod {{0xFD} {`%`_u32(182):Bu32}} => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), MIN_vbinop_(S_sx))
  ;; test.spectec:6822.5-6822.45
  prod {{0xFD} {`%`_u32(183):Bu32}} => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), MIN_vbinop_(U_sx))
  ;; test.spectec:6823.5-6823.45
  prod {{0xFD} {`%`_u32(184):Bu32}} => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), MAX_vbinop_(S_sx))
  ;; test.spectec:6824.5-6824.45
  prod {{0xFD} {`%`_u32(185):Bu32}} => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), MAX_vbinop_(U_sx))
  ;; test.spectec:6828.5-6828.59
  prod {{0xFD} {`%`_u32(186):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), DOTS_vextbinop__)
  ;; test.spectec:6829.5-6829.66
  prod {{0xFD} {`%`_u32(188):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTMUL_vextbinop__(LOW_half, S_sx))
  ;; test.spectec:6830.5-6830.67
  prod {{0xFD} {`%`_u32(189):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTMUL_vextbinop__(HIGH_half, S_sx))
  ;; test.spectec:6831.5-6831.66
  prod {{0xFD} {`%`_u32(190):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTMUL_vextbinop__(LOW_half, U_sx))
  ;; test.spectec:6832.5-6832.67
  prod {{0xFD} {`%`_u32(191):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTMUL_vextbinop__(HIGH_half, U_sx))
  ;; test.spectec:6836.5-6836.72
  prod {{0xFD} {`%`_u32(275):Bu32}} => VEXTTERNOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), RELAXED_DOT_ADDS_vextternop__)
  ;; test.spectec:6840.5-6840.42
  prod {{0xFD} {`%`_u32(192):Bu32}} => VUNOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), ABS_vunop_)
  ;; test.spectec:6841.5-6841.42
  prod {{0xFD} {`%`_u32(193):Bu32}} => VUNOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), NEG_vunop_)
  ;; test.spectec:6845.5-6845.49
  prod {{0xFD} {`%`_u32(195):Bu32}} => VTESTOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), ALL_TRUE_vtestop_)
  ;; test.spectec:6849.5-6849.41
  prod {{0xFD} {`%`_u32(196):Bu32}} => VBITMASK_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))))
  ;; test.spectec:6853.5-6853.63
  prod {{0xFD} {`%`_u32(199):Bu32}} => VCVTOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), EXTEND_vcvtop__(LOW_half, S_sx))
  ;; test.spectec:6854.5-6854.64
  prod {{0xFD} {`%`_u32(200):Bu32}} => VCVTOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), EXTEND_vcvtop__(HIGH_half, S_sx))
  ;; test.spectec:6855.5-6855.63
  prod {{0xFD} {`%`_u32(201):Bu32}} => VCVTOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), EXTEND_vcvtop__(LOW_half, U_sx))
  ;; test.spectec:6856.5-6856.64
  prod {{0xFD} {`%`_u32(202):Bu32}} => VCVTOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), EXTEND_vcvtop__(HIGH_half, U_sx))
  ;; test.spectec:6860.5-6860.45
  prod {{0xFD} {`%`_u32(203):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), SHL_vshiftop_)
  ;; test.spectec:6861.5-6861.49
  prod {{0xFD} {`%`_u32(204):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), SHR_vshiftop_(S_sx))
  ;; test.spectec:6862.5-6862.49
  prod {{0xFD} {`%`_u32(205):Bu32}} => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), SHR_vshiftop_(U_sx))
  ;; test.spectec:6866.5-6866.43
  prod {{0xFD} {`%`_u32(206):Bu32}} => VBINOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), ADD_vbinop_)
  ;; test.spectec:6867.5-6867.43
  prod {{0xFD} {`%`_u32(209):Bu32}} => VBINOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), SUB_vbinop_)
  ;; test.spectec:6868.5-6868.43
  prod {{0xFD} {`%`_u32(213):Bu32}} => VBINOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), MUL_vbinop_)
  ;; test.spectec:6872.5-6872.42
  prod {{0xFD} {`%`_u32(214):Bu32}} => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), EQ_vrelop_)
  ;; test.spectec:6873.5-6873.42
  prod {{0xFD} {`%`_u32(215):Bu32}} => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), NE_vrelop_)
  ;; test.spectec:6874.5-6874.46
  prod {{0xFD} {`%`_u32(216):Bu32}} => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), LT_vrelop_(S_sx))
  ;; test.spectec:6875.5-6875.46
  prod {{0xFD} {`%`_u32(217):Bu32}} => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), GT_vrelop_(S_sx))
  ;; test.spectec:6876.5-6876.46
  prod {{0xFD} {`%`_u32(218):Bu32}} => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), LE_vrelop_(S_sx))
  ;; test.spectec:6877.5-6877.46
  prod {{0xFD} {`%`_u32(219):Bu32}} => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), GE_vrelop_(S_sx))
  ;; test.spectec:6881.5-6881.66
  prod {{0xFD} {`%`_u32(220):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), EXTMUL_vextbinop__(LOW_half, S_sx))
  ;; test.spectec:6882.5-6882.67
  prod {{0xFD} {`%`_u32(221):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), EXTMUL_vextbinop__(HIGH_half, S_sx))
  ;; test.spectec:6883.5-6883.66
  prod {{0xFD} {`%`_u32(222):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), EXTMUL_vextbinop__(LOW_half, U_sx))
  ;; test.spectec:6884.5-6884.67
  prod {{0xFD} {`%`_u32(223):Bu32}} => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), EXTMUL_vextbinop__(HIGH_half, U_sx))
  ;; test.spectec:6888.5-6888.43
  prod {{0xFD} {`%`_u32(103):Bu32}} => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), CEIL_vunop_)
  ;; test.spectec:6889.5-6889.44
  prod {{0xFD} {`%`_u32(104):Bu32}} => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), FLOOR_vunop_)
  ;; test.spectec:6890.5-6890.44
  prod {{0xFD} {`%`_u32(105):Bu32}} => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), TRUNC_vunop_)
  ;; test.spectec:6891.5-6891.46
  prod {{0xFD} {`%`_u32(106):Bu32}} => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), NEAREST_vunop_)
  ;; test.spectec:6892.5-6892.42
  prod {{0xFD} {`%`_u32(224):Bu32}} => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), ABS_vunop_)
  ;; test.spectec:6893.5-6893.42
  prod {{0xFD} {`%`_u32(225):Bu32}} => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), NEG_vunop_)
  ;; test.spectec:6894.5-6894.43
  prod {{0xFD} {`%`_u32(227):Bu32}} => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), SQRT_vunop_)
  ;; test.spectec:6898.5-6898.43
  prod {{0xFD} {`%`_u32(228):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), ADD_vbinop_)
  ;; test.spectec:6899.5-6899.43
  prod {{0xFD} {`%`_u32(229):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), SUB_vbinop_)
  ;; test.spectec:6900.5-6900.43
  prod {{0xFD} {`%`_u32(230):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), MUL_vbinop_)
  ;; test.spectec:6901.5-6901.43
  prod {{0xFD} {`%`_u32(231):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), DIV_vbinop_)
  ;; test.spectec:6902.5-6902.43
  prod {{0xFD} {`%`_u32(232):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), MIN_vbinop_)
  ;; test.spectec:6903.5-6903.43
  prod {{0xFD} {`%`_u32(233):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), MAX_vbinop_)
  ;; test.spectec:6904.5-6904.44
  prod {{0xFD} {`%`_u32(234):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), PMIN_vbinop_)
  ;; test.spectec:6905.5-6905.44
  prod {{0xFD} {`%`_u32(235):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), PMAX_vbinop_)
  ;; test.spectec:6906.5-6906.51
  prod {{0xFD} {`%`_u32(269):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), RELAXED_MIN_vbinop_)
  ;; test.spectec:6907.5-6907.51
  prod {{0xFD} {`%`_u32(270):Bu32}} => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), RELAXED_MAX_vbinop_)
  ;; test.spectec:6911.5-6911.53
  prod {{0xFD} {`%`_u32(261):Bu32}} => VTERNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), RELAXED_MADD_vternop_)
  ;; test.spectec:6912.5-6912.54
  prod {{0xFD} {`%`_u32(262):Bu32}} => VTERNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), RELAXED_NMADD_vternop_)
  ;; test.spectec:6916.5-6916.43
  prod {{0xFD} {`%`_u32(116):Bu32}} => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), CEIL_vunop_)
  ;; test.spectec:6917.5-6917.44
  prod {{0xFD} {`%`_u32(117):Bu32}} => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), FLOOR_vunop_)
  ;; test.spectec:6918.5-6918.44
  prod {{0xFD} {`%`_u32(122):Bu32}} => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), TRUNC_vunop_)
  ;; test.spectec:6919.5-6919.46
  prod {{0xFD} {`%`_u32(148):Bu32}} => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), NEAREST_vunop_)
  ;; test.spectec:6920.5-6920.42
  prod {{0xFD} {`%`_u32(236):Bu32}} => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), ABS_vunop_)
  ;; test.spectec:6921.5-6921.42
  prod {{0xFD} {`%`_u32(237):Bu32}} => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), NEG_vunop_)
  ;; test.spectec:6922.5-6922.43
  prod {{0xFD} {`%`_u32(239):Bu32}} => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), SQRT_vunop_)
  ;; test.spectec:6926.5-6926.43
  prod {{0xFD} {`%`_u32(240):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), ADD_vbinop_)
  ;; test.spectec:6927.5-6927.43
  prod {{0xFD} {`%`_u32(241):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), SUB_vbinop_)
  ;; test.spectec:6928.5-6928.43
  prod {{0xFD} {`%`_u32(242):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), MUL_vbinop_)
  ;; test.spectec:6929.5-6929.43
  prod {{0xFD} {`%`_u32(243):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), DIV_vbinop_)
  ;; test.spectec:6930.5-6930.43
  prod {{0xFD} {`%`_u32(244):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), MIN_vbinop_)
  ;; test.spectec:6931.5-6931.43
  prod {{0xFD} {`%`_u32(245):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), MAX_vbinop_)
  ;; test.spectec:6932.5-6932.44
  prod {{0xFD} {`%`_u32(246):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), PMIN_vbinop_)
  ;; test.spectec:6933.5-6933.44
  prod {{0xFD} {`%`_u32(247):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), PMAX_vbinop_)
  ;; test.spectec:6934.5-6934.51
  prod {{0xFD} {`%`_u32(271):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), RELAXED_MIN_vbinop_)
  ;; test.spectec:6935.5-6935.51
  prod {{0xFD} {`%`_u32(272):Bu32}} => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), RELAXED_MAX_vbinop_)
  ;; test.spectec:6939.5-6939.53
  prod {{0xFD} {`%`_u32(263):Bu32}} => VTERNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), RELAXED_MADD_vternop_)
  ;; test.spectec:6940.5-6940.54
  prod {{0xFD} {`%`_u32(264):Bu32}} => VTERNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), RELAXED_NMADD_vternop_)
  ;; test.spectec:6941.5-6941.59
  prod {{0xFD} {`%`_u32(265):Bu32}} => VTERNOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), RELAXED_LANESELECT_vternop_)
  ;; test.spectec:6942.5-6942.59
  prod {{0xFD} {`%`_u32(266):Bu32}} => VTERNOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), RELAXED_LANESELECT_vternop_)
  ;; test.spectec:6943.5-6943.59
  prod {{0xFD} {`%`_u32(267):Bu32}} => VTERNOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), RELAXED_LANESELECT_vternop_)
  ;; test.spectec:6944.5-6944.59
  prod {{0xFD} {`%`_u32(268):Bu32}} => VTERNOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), RELAXED_LANESELECT_vternop_)
  ;; test.spectec:6948.5-6948.61
  prod {{0xFD} {`%`_u32(94):Bu32}} => VCVTOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), `%X%`_shape(F64_lanetype, `%`_dim(2)), DEMOTE_vcvtop__(ZERO_zero))
  ;; test.spectec:6949.5-6949.61
  prod {{0xFD} {`%`_u32(95):Bu32}} => VCVTOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), `%X%`_shape(F32_lanetype, `%`_dim(4)), PROMOTELOW_vcvtop__)
  ;; test.spectec:6950.5-6950.62
  prod {{0xFD} {`%`_u32(248):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F32_lanetype, `%`_dim(4)), TRUNC_SAT_vcvtop__(S_sx, ?()))
  ;; test.spectec:6951.5-6951.62
  prod {{0xFD} {`%`_u32(249):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F32_lanetype, `%`_dim(4)), TRUNC_SAT_vcvtop__(U_sx, ?()))
  ;; test.spectec:6952.5-6952.60
  prod {{0xFD} {`%`_u32(250):Bu32}} => VCVTOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), `%X%`_shape(I32_lanetype, `%`_dim(4)), CONVERT_vcvtop__(?(), S_sx))
  ;; test.spectec:6953.5-6953.60
  prod {{0xFD} {`%`_u32(251):Bu32}} => VCVTOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), `%X%`_shape(I32_lanetype, `%`_dim(4)), CONVERT_vcvtop__(?(), U_sx))
  ;; test.spectec:6954.5-6954.67
  prod {{0xFD} {`%`_u32(252):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F64_lanetype, `%`_dim(2)), TRUNC_SAT_vcvtop__(S_sx, ?(ZERO_zero)))
  ;; test.spectec:6955.5-6955.67
  prod {{0xFD} {`%`_u32(253):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F64_lanetype, `%`_dim(2)), TRUNC_SAT_vcvtop__(U_sx, ?(ZERO_zero)))
  ;; test.spectec:6956.5-6956.64
  prod {{0xFD} {`%`_u32(254):Bu32}} => VCVTOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), CONVERT_vcvtop__(?(LOW_half), S_sx))
  ;; test.spectec:6957.5-6957.64
  prod {{0xFD} {`%`_u32(255):Bu32}} => VCVTOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), CONVERT_vcvtop__(?(LOW_half), U_sx))
  ;; test.spectec:6958.5-6958.66
  prod {{0xFD} {`%`_u32(257):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F32_lanetype, `%`_dim(4)), RELAXED_TRUNC_vcvtop__(S_sx, ?()))
  ;; test.spectec:6959.5-6959.66
  prod {{0xFD} {`%`_u32(258):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F32_lanetype, `%`_dim(4)), RELAXED_TRUNC_vcvtop__(U_sx, ?()))
  ;; test.spectec:6960.5-6960.71
  prod {{0xFD} {`%`_u32(259):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F64_lanetype, `%`_dim(2)), RELAXED_TRUNC_vcvtop__(S_sx, ?(ZERO_zero)))
  ;; test.spectec:6961.5-6961.71
  prod {{0xFD} {`%`_u32(260):Bu32}} => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F64_lanetype, `%`_dim(2)), RELAXED_TRUNC_vcvtop__(U_sx, ?(ZERO_zero)))
}

;; test.spectec:6966.1-6967.29
grammar Bexpr : expr
  ;; test.spectec:6967.5-6967.29
  prod{`in*` : instr*} {{in:Binstr*{in <- `in*`}} {0x0B}} => in*{in <- `in*`}

;; test.spectec:6984.1-6986.15
grammar Bsection_(N : N, syntax en, grammar BX : en*) : en*
  ;; test.spectec:6985.5-6985.55
  prod{`en*` : en*, len : nat} {{`%`_byte(N):Bbyte} {`%`_u32(len):Bu32} {en*{en <- `en*`}:BX}} => en*{en <- `en*`}
    -- if (len = 0)
  ;; test.spectec:6986.5-6986.15
  prod eps => []

;; test.spectec:6991.1-6992.23
grammar Bcustom : ()*
  ;; test.spectec:6992.5-6992.23
  prod {{Bname} {Bbyte*{}}} => []

;; test.spectec:6994.1-6995.32
grammar Bcustomsec : ()
  ;; test.spectec:6995.5-6995.32
  prod Bsection_(0, syntax (), grammar Bcustom) => ((), ()).1

;; test.spectec:7000.1-7001.27
grammar Btype : type
  ;; test.spectec:7001.5-7001.27
  prod{qt : rectype} qt:Brectype => TYPE_type(qt)

;; test.spectec:7003.1-7004.42
grammar Btypesec : type*
  ;; test.spectec:7004.5-7004.42
  prod{`ty*` : type*} ty*{ty <- `ty*`}:Bsection_(1, syntax type, grammar Blist(syntax type, grammar Btype)) => ty*{ty <- `ty*`}

;; test.spectec:7009.1-7010.64
grammar Bimport : import
  ;; test.spectec:7010.5-7010.64
  prod{nm_1 : name, nm_2 : name, xt : externtype} {{nm_1:Bname} {nm_2:Bname} {xt:Bexterntype}} => IMPORT_import(nm_1, nm_2, xt)

;; test.spectec:7012.1-7013.44
grammar Bimportsec : import*
  ;; test.spectec:7013.5-7013.44
  prod{`im*` : import*} im*{im <- `im*`}:Bsection_(2, syntax import, grammar Blist(syntax import, grammar Bimport)) => im*{im <- `im*`}

;; test.spectec:7018.1-7019.43
grammar Bfuncsec : typeidx*
  ;; test.spectec:7019.5-7019.43
  prod{`x*` : idx*} x*{x <- `x*`}:Bsection_(3, syntax typeidx, grammar Blist(syntax typeidx, grammar Btypeidx)) => x*{x <- `x*`}

;; test.spectec:7024.1-7026.50
grammar Btable : table
  ;; test.spectec:7025.5-7025.78
  prod{tt : tabletype, ht : heaptype, at : addrtype, lim : limits} tt:Btabletype => TABLE_table(tt, [`REF.NULL`_instr(ht)])
    -- if (tt = `%%%`_tabletype(at, lim, REF_reftype(NULL_null?{}, ht)))
  ;; test.spectec:7026.5-7026.50
  prod{tt : tabletype, e : expr} {{0x40} {0x00} {tt:Btabletype} {e:Bexpr}} => TABLE_table(tt, e)

;; test.spectec:7028.1-7029.45
grammar Btablesec : table*
  ;; test.spectec:7029.5-7029.45
  prod{`tab*` : table*} tab*{tab <- `tab*`}:Bsection_(4, syntax table, grammar Blist(syntax table, grammar Btable)) => tab*{tab <- `tab*`}

;; test.spectec:7034.1-7035.29
grammar Bmem : mem
  ;; test.spectec:7035.5-7035.29
  prod{mt : memtype} mt:Bmemtype => MEMORY_mem(mt)

;; test.spectec:7037.1-7038.43
grammar Bmemsec : mem*
  ;; test.spectec:7038.5-7038.43
  prod{`mem*` : mem*} mem*{mem <- `mem*`}:Bsection_(5, syntax mem, grammar Blist(syntax mem, grammar Bmem)) => mem*{mem <- `mem*`}

;; test.spectec:7043.1-7044.42
grammar Bglobal : global
  ;; test.spectec:7044.5-7044.42
  prod{gt : globaltype, e : expr} {{gt:Bglobaltype} {e:Bexpr}} => GLOBAL_global(gt, e)

;; test.spectec:7046.1-7047.48
grammar Bglobalsec : global*
  ;; test.spectec:7047.5-7047.48
  prod{`glob*` : global*} glob*{glob <- `glob*`}:Bsection_(6, syntax global, grammar Blist(syntax global, grammar Bglobal)) => glob*{glob <- `glob*`}

;; test.spectec:7052.1-7053.43
grammar Bexport : export
  ;; test.spectec:7053.5-7053.43
  prod{nm : name, xx : externidx} {{nm:Bname} {xx:Bexternidx}} => EXPORT_export(nm, xx)

;; test.spectec:7055.1-7056.44
grammar Bexportsec : export*
  ;; test.spectec:7056.5-7056.44
  prod{`ex*` : export*} ex*{ex <- `ex*`}:Bsection_(7, syntax export, grammar Blist(syntax export, grammar Bexport)) => ex*{ex <- `ex*`}

;; test.spectec:7061.1-7062.28
grammar Bstart : start*
  ;; test.spectec:7062.5-7062.28
  prod{x : idx} x:Bfuncidx => [START_start(x)]

;; test.spectec:7066.1-7067.60
grammar Bstartsec : start?
  ;; test.spectec:7067.5-7067.60
  prod{startopt : startopt} startopt:Bsection_(8, syntax start, grammar Bstart) => $opt_(syntax start, startopt)

;; test.spectec:7072.1-7073.21
grammar Belemkind : reftype
  ;; test.spectec:7073.5-7073.21
  prod 0x00 => REF_reftype(?(), FUNC_heaptype)

;; test.spectec:7075.1-7091.25
grammar Belem : elem
  ;; test.spectec:7076.5-7077.51
  prod{`y*` : idx*, e_o : expr} {{`%`_u32(0):Bu32} {e_o:Bexpr} {y*{y <- `y*`}:Blist(syntax funcidx, grammar Bfuncidx)}} => ELEM_elem(REF_reftype(?(), FUNC_heaptype), [`REF.FUNC`_instr(y)*{y <- `y*`}], ACTIVE_elemmode(`%`_tableidx(0), e_o))
  ;; test.spectec:7078.5-7079.36
  prod{rt : reftype, `y*` : idx*} {{`%`_u32(1):Bu32} {rt:Belemkind} {y*{y <- `y*`}:Blist(syntax funcidx, grammar Bfuncidx)}} => ELEM_elem(rt, [`REF.FUNC`_instr(y)*{y <- `y*`}], PASSIVE_elemmode)
  ;; test.spectec:7080.5-7081.41
  prod{rt : reftype, `y*` : idx*, x : idx, e : expr} {{`%`_u32(2):Bu32} {x:Btableidx} {e:Bexpr} {rt:Belemkind} {y*{y <- `y*`}:Blist(syntax funcidx, grammar Bfuncidx)}} => ELEM_elem(rt, [`REF.FUNC`_instr(y)*{y <- `y*`}], ACTIVE_elemmode(x, e))
  ;; test.spectec:7082.5-7083.36
  prod{rt : reftype, `y*` : idx*} {{`%`_u32(3):Bu32} {rt:Belemkind} {y*{y <- `y*`}:Blist(syntax funcidx, grammar Bfuncidx)}} => ELEM_elem(rt, [`REF.FUNC`_instr(y)*{y <- `y*`}], DECLARE_elemmode)
  ;; test.spectec:7084.5-7085.45
  prod{`e*` : expr*, e_O : expr} {{`%`_u32(4):Bu32} {e_O:Bexpr} {e*{e <- `e*`}:Blist(syntax expr, grammar Bexpr)}} => ELEM_elem(REF_reftype(?(NULL_null), FUNC_heaptype), e*{e <- `e*`}, ACTIVE_elemmode(`%`_tableidx(0), e_O))
  ;; test.spectec:7086.5-7087.25
  prod{rt : reftype, `e*` : expr*} {{`%`_u32(5):Bu32} {rt:Breftype} {e*{e <- `e*`}:Blist(syntax expr, grammar Bexpr)}} => ELEM_elem(rt, e*{e <- `e*`}, PASSIVE_elemmode)
  ;; test.spectec:7088.5-7089.32
  prod{rt : reftype, `e*` : expr*, x : idx, e_O : expr} {{`%`_u32(6):Bu32} {x:Btableidx} {e_O:Bexpr} {rt:Breftype} {e*{e <- `e*`}:Blist(syntax expr, grammar Bexpr)}} => ELEM_elem(rt, e*{e <- `e*`}, ACTIVE_elemmode(x, e_O))
  ;; test.spectec:7090.5-7091.25
  prod{rt : reftype, `e*` : expr*} {{`%`_u32(7):Bu32} {rt:Breftype} {e*{e <- `e*`}:Blist(syntax expr, grammar Bexpr)}} => ELEM_elem(rt, e*{e <- `e*`}, DECLARE_elemmode)

;; test.spectec:7093.1-7094.46
grammar Belemsec : elem*
  ;; test.spectec:7094.5-7094.46
  prod{`elem*` : elem*} elem*{elem <- `elem*`}:Bsection_(9, syntax elem, grammar Blist(syntax elem, grammar Belem)) => elem*{elem <- `elem*`}

;; test.spectec:7101.1-7102.37
grammar Blocals : local*
  ;; test.spectec:7102.5-7102.37
  prod{t : valtype, n : n} {{`%`_u32(n):Bu32} {t:Bvaltype}} => LOCAL_local(t)^n{}

;; test.spectec:7104.1-7106.45
grammar Bfunc : code
  ;; test.spectec:7105.5-7106.45
  prod{`loc**` : local**, e : expr} {{loc*{loc <- `loc*`}*{`loc*` <- `loc**`}:Blist(syntax local*, grammar Blocals)} {e:Bexpr}} => ($concat_(syntax local, loc*{loc <- `loc*`}*{`loc*` <- `loc**`}), e)
    -- if (|$concat_(syntax local, loc*{loc <- `loc*`}*{`loc*` <- `loc**`})| < (2 ^ 32))

;; test.spectec:7108.1-7109.55
grammar Bcode : code
  ;; test.spectec:7109.5-7109.55
  prod{code : code, len : nat} {{`%`_u32(len):Bu32} {code:Bfunc}} => code
    -- if (len = 0)

;; test.spectec:7111.1-7112.47
grammar Bcodesec : code*
  ;; test.spectec:7112.5-7112.47
  prod{`code*` : code*} code*{code <- `code*`}:Bsection_(10, syntax code, grammar Blist(syntax code, grammar Bcode)) => code*{code <- `code*`}

;; test.spectec:7117.1-7120.69
grammar Bdata : data
  ;; test.spectec:7118.5-7118.59
  prod{`b*` : byte*, e : expr} {{`%`_u32(0):Bu32} {e:Bexpr} {b*{b <- `b*`}:Blist(syntax byte, grammar Bbyte)}} => DATA_data(b*{b <- `b*`}, ACTIVE_datamode(`%`_memidx(0), e))
  ;; test.spectec:7119.5-7119.46
  prod{`b*` : byte*} {{`%`_u32(1):Bu32} {b*{b <- `b*`}:Blist(syntax byte, grammar Bbyte)}} => DATA_data(b*{b <- `b*`}, PASSIVE_datamode)
  ;; test.spectec:7120.5-7120.69
  prod{`b*` : byte*, x : idx, e : expr} {{`%`_u32(2):Bu32} {x:Bmemidx} {e:Bexpr} {b*{b <- `b*`}:Blist(syntax byte, grammar Bbyte)}} => DATA_data(b*{b <- `b*`}, ACTIVE_datamode(x, e))

;; test.spectec:7122.1-7123.47
grammar Bdatasec : data*
  ;; test.spectec:7123.5-7123.47
  prod{`data*` : data*} data*{data <- `data*`}:Bsection_(11, syntax data, grammar Blist(syntax data, grammar Bdata)) => data*{data <- `data*`}

;; test.spectec:7128.1-7129.16
grammar Bdatacnt : u32*
  ;; test.spectec:7129.5-7129.16
  prod{n : n} `%`_u32(n):Bu32 => [`%`_u32(n)]

;; test.spectec:7133.1-7134.53
grammar Bdatacntsec : u32?
  ;; test.spectec:7134.5-7134.53
  prod{nopt : nopt} nopt:Bsection_(12, syntax u32, grammar Bdatacnt) => $opt_(syntax u32, nopt)

;; test.spectec:7139.1-7140.26
grammar Btag : tag
  ;; test.spectec:7140.5-7140.26
  prod{jt : tagtype} jt:Btagtype => TAG_tag(jt)

;; test.spectec:7142.1-7143.44
grammar Btagsec : tag*
  ;; test.spectec:7143.5-7143.44
  prod{`tag*` : tag*} tag*{tag <- `tag*`}:Bsection_(13, syntax tag, grammar Blist(syntax tag, grammar Btag)) => tag*{tag <- `tag*`}

;; test.spectec:7148.1-7148.48
grammar Bmagic : ()
  ;; test.spectec:7148.23-7148.48
  prod {{0x00} {0x61} {0x73} {0x6D}} => ((), ()).1

;; test.spectec:7149.1-7149.50
grammar Bversion : ()
  ;; test.spectec:7149.25-7149.50
  prod {{0x01} {0x00} {0x00} {0x00}} => ((), ()).1

;; test.spectec:7150.1-7170.45
grammar Bmodule : module
  ;; test.spectec:7151.5-7170.45
  prod{`type*` : type*, `import*` : import*, `tag*` : tag*, `global*` : global*, `mem*` : mem*, `table*` : table*, `func*` : func*, `data*` : data*, `elem*` : elem*, `start?` : start?, `export*` : export*, `typeidx*` : typeidx*, `n?` : n?, `expr*` : expr*, `local**` : local**} {Bmagic Bversion {Bcustomsec*{}} {type*{type <- `type*`}:Btypesec} {Bcustomsec*{}} {import*{import <- `import*`}:Bimportsec} {Bcustomsec*{}} {typeidx*{typeidx <- `typeidx*`}:Bfuncsec} {Bcustomsec*{}} {table*{table <- `table*`}:Btablesec} {Bcustomsec*{}} {mem*{mem <- `mem*`}:Bmemsec} {Bcustomsec*{}} {tag*{tag <- `tag*`}:Btagsec} {Bcustomsec*{}} {global*{global <- `global*`}:Bglobalsec} {Bcustomsec*{}} {export*{export <- `export*`}:Bexportsec} {Bcustomsec*{}} {start?{start <- `start?`}:Bstartsec} {Bcustomsec*{}} {elem*{elem <- `elem*`}:Belemsec} {Bcustomsec*{}} {`%`_u32(n)?{n <- `n?`}:Bdatacntsec} {Bcustomsec*{}} {(local*{local <- `local*`}, expr)*{expr <- `expr*`, `local*` <- `local**`}:Bcodesec} {Bcustomsec*{}} {data*{data <- `data*`}:Bdatasec} {Bcustomsec*{}}} => MODULE_module(`%`_list(type*{type <- `type*`}), `%`_list(import*{import <- `import*`}), `%`_list(tag*{tag <- `tag*`}), `%`_list(global*{global <- `global*`}), `%`_list(mem*{mem <- `mem*`}), `%`_list(table*{table <- `table*`}), `%`_list(func*{func <- `func*`}), `%`_list(data*{data <- `data*`}), `%`_list(elem*{elem <- `elem*`}), start?{start <- `start?`}, `%`_list(export*{export <- `export*`}))
    -- (if (n = |data*{data <- `data*`}|))?{n <- `n?`}
    -- if ((n?{n <- `n?`} =/= ?()) \/ ($dataidx_funcs(func*{func <- `func*`}) = []))
    -- (if (func = FUNC_func(typeidx, local*{local <- `local*`}, expr)))*{expr <- `expr*`, func <- `func*`, `local*` <- `local**`, typeidx <- `typeidx*`}

;; test.spectec:7185.1-7186.52
grammar Tchar : char
  ;; test.spectec:7186.5-7186.26
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:(0x00 | ... | 0xD7FF) => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7186.29-7186.52
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:(0xE000 | ... | 0x10FFFF) => `%`_char(`<implicit-prod-result>`)

;; test.spectec:7188.1-7189.11
grammar Tsource : ()
  ;; test.spectec:7189.5-7189.11
  prod{`<implicit-prod-result>` : char} [`<implicit-prod-result>`]:Tchar*{} => (`<implicit-prod-result>`, ()).1

;; test.spectec:7194.1-7194.54
grammar TuNplain : ()
  ;; test.spectec:7194.51-7194.54
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:eps => (`<implicit-prod-result>`, ()).1

;; test.spectec:7195.1-7195.54
grammar TsNplain : ()
  ;; test.spectec:7195.51-7195.54
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:eps => (`<implicit-prod-result>`, ()).1

;; test.spectec:7196.1-7196.54
grammar TfNplain : ()
  ;; test.spectec:7196.51-7196.54
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:eps => (`<implicit-prod-result>`, ()).1

;; test.spectec:7382.1-7387.75
grammar Tidchar : char
  ;; test.spectec:7383.5-7383.20
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:(0x30 | ... | 0x39) => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7384.5-7384.20
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:(0x41 | ... | 0x5A) => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7385.5-7385.20
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:(0x61 | ... | 0x7A) => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7386.5-7386.8
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x21 => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7386.11-7386.14
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x23 => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7386.17-7386.20
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x24 => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7386.23-7386.26
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x25 => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7386.29-7386.32
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x26 => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7386.35-7386.38
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x27 => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7386.41-7386.44
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x2A => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7386.47-7386.50
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x2B => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7386.53-7386.56
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x2D => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7386.59-7386.62
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x2E => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7386.65-7386.68
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x2F => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7387.5-7387.8
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x3A => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7387.11-7387.14
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x3C => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7387.17-7387.20
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x3D => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7387.23-7387.26
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x3E => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7387.29-7387.32
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x3F => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7387.35-7387.38
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x40 => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7387.41-7387.45
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x5C => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7387.48-7387.51
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x5E => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7387.54-7387.57
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x5F => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7387.60-7387.63
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x60 => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7387.66-7387.69
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x7C => `%`_char(`<implicit-prod-result>`)
  ;; test.spectec:7387.72-7387.75
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x7E => `%`_char(`<implicit-prod-result>`)

;; test.spectec:7269.1-7270.30
grammar Tdigit : nat
  ;; test.spectec:7270.5-7270.30
  prod 0x30 => 0
  ;; test.spectec:7270.5-7270.30
  prod 0x31 => 1
  ;; test.spectec:7270.5-7270.30
  prod 0x32 => 2
  ;; test.spectec:7270.5-7270.30
  prod 0x33 => 3
  ;; test.spectec:7270.5-7270.30
  prod 0x34 => 4
  ;; test.spectec:7270.5-7270.30
  prod 0x35 => 5
  ;; test.spectec:7270.5-7270.30
  prod 0x36 => 6
  ;; test.spectec:7270.5-7270.30
  prod 0x37 => 7
  ;; test.spectec:7270.5-7270.30
  prod 0x38 => 8
  ;; test.spectec:7270.5-7270.30
  prod 0x39 => 9

;; test.spectec:7272.1-7275.32
grammar Thexdigit : nat
  ;; test.spectec:7273.5-7273.18
  prod{d : nat} d:Tdigit => d
  ;; test.spectec:7274.5-7274.32
  prod 0x41 => 10
  ;; test.spectec:7274.5-7274.32
  prod 0x42 => 11
  ;; test.spectec:7274.5-7274.32
  prod 0x43 => 12
  ;; test.spectec:7274.5-7274.32
  prod 0x44 => 13
  ;; test.spectec:7274.5-7274.32
  prod 0x45 => 14
  ;; test.spectec:7274.5-7274.32
  prod 0x46 => 15
  ;; test.spectec:7275.5-7275.32
  prod 0x61 => 10
  ;; test.spectec:7275.5-7275.32
  prod 0x62 => 11
  ;; test.spectec:7275.5-7275.32
  prod 0x63 => 12
  ;; test.spectec:7275.5-7275.32
  prod 0x64 => 13
  ;; test.spectec:7275.5-7275.32
  prod 0x65 => 14
  ;; test.spectec:7275.5-7275.32
  prod 0x66 => 15

;; test.spectec:7281.1-7283.46
rec {

;; test.spectec:7281.1-7283.46
grammar Thexnum : nat
  ;; test.spectec:7282.5-7282.21
  prod{h : nat} h:Thexdigit => h
  ;; test.spectec:7283.5-7283.46
  prod{n : n, h : nat} {{n:Thexnum} {"_"?{}} {h:Thexdigit}} => ((16 * n) + h)
}

;; test.spectec:7349.1-7357.74
grammar Tstringchar : char
  ;; test.spectec:7350.5-7350.76
  prod{c : char} c:Tchar => c
    -- if ((((c!`%`_char.0 >= 32) /\ (c!`%`_char.0 =/= 127)) /\ (c =/= `%`_char(34))) /\ (c =/= `%`_char(92)))
  ;; test.spectec:7351.5-7351.18
  prod "\\t" => `%`_char(9)
  ;; test.spectec:7352.5-7352.18
  prod "\\n" => `%`_char(10)
  ;; test.spectec:7353.5-7353.18
  prod "\\r" => `%`_char(13)
  ;; test.spectec:7354.5-7354.19
  prod "\\\"" => `%`_char(34)
  ;; test.spectec:7355.5-7355.18
  prod "\\'" => `%`_char(39)
  ;; test.spectec:7356.5-7356.19
  prod "\\\\" => `%`_char(92)
  ;; test.spectec:7357.5-7357.74
  prod{n : n} {{"\\u{"} {n:Thexnum} {"}"}} => `%`_char(n)
    -- if ((n < 55296) \/ ((59392 <= n) /\ (n < 1114112)))

;; test.spectec:7359.1-7361.58
grammar Tstringelem : byte*
  ;; test.spectec:7360.5-7360.30
  prod{c : char} c:Tstringchar => $utf8([c])
  ;; test.spectec:7361.5-7361.58
  prod{h_1 : nat, h_2 : nat} {{"\\"} {h_1:Thexdigit} {h_2:Thexdigit}} => [`%`_byte(((16 * h_1) + h_2))]

;; test.spectec:7363.1-7365.42
grammar Tstring : byte*
  ;; test.spectec:7364.5-7365.42
  prod{`b**` : byte**} {{"\""} {b*{b <- `b*`}:Tstringelem*{`b*` <- `b**`}} {"\""}} => $concat_(syntax byte, b*{b <- `b*`}*{`b*` <- `b**`})
    -- if (|$concat_(syntax byte, b*{b <- `b*`}*{`b*` <- `b**`})| < (2 ^ 32))

;; test.spectec:7376.1-7377.43
grammar Tname : name
  ;; test.spectec:7377.5-7377.43
  prod{`c*` : char*, `b*` : byte*} b*{b <- `b*`}:Tstring => `%`_name(c*{c <- `c*`})
    -- if (b*{b <- `b*`} = $utf8(c*{c <- `c*`}))

;; test.spectec:7389.1-7391.41
grammar Tid : name
  ;; test.spectec:7390.5-7390.26
  prod{`c*` : char*} {{"$"} {c*{c <- `c*`}:Tidchar+{}}} => `%`_name(c*{c <- `c*`})
  ;; test.spectec:7391.5-7391.41
  prod{`c*` : char*} {{"$"} {`%`_name(c*{c <- `c*`}):Tname}} => `%`_name(c*{c <- `c*`})
    -- if (|c*{c <- `c*`}| > 0)

;; test.spectec:7201.1-7202.31
grammar Tkeyword : ()
  ;; test.spectec:7202.5-7202.31
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{(0x61 | ... | 0x7A)} {Tidchar*{}}} => (`<implicit-prod-result>`, ()).1

;; test.spectec:7204.1-7205.61
grammar Treserved : ()
  ;; test.spectec:7205.5-7205.61
  prod{`<implicit-prod-result>` : ()} [`<implicit-prod-result>`]:({Tidchar} | {Tstring} | {","} | {";"} | {"["} | {"]"} | {"{"} | {"}"})+{} => (`<implicit-prod-result>`, ()).1

;; test.spectec:7198.1-7199.86
grammar Ttoken : ()
  ;; test.spectec:7199.5-7199.13
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:Tkeyword => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:7199.16-7199.24
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:TuNplain => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:7199.27-7199.35
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:TsNplain => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:7199.38-7199.46
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:TfNplain => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:7199.49-7199.56
  prod{`<implicit-prod-result>` : byte} [`<implicit-prod-result>`]:Tstring => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:7199.59-7199.62
  prod{`<implicit-prod-result>` : name} `<implicit-prod-result>`:Tid => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:7199.65-7199.68
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x28 => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:7199.71-7199.74
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x29 => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:7199.77-7199.86
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:Treserved => (`<implicit-prod-result>`, ()).1

;; test.spectec:7250.1-7251.21
grammar Tannotid : ()
  ;; test.spectec:7251.5-7251.13
  prod{`<implicit-prod-result>` : char} [`<implicit-prod-result>`]:Tidchar+{} => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:7251.16-7251.21
  prod{`<implicit-prod-result>` : name} `<implicit-prod-result>`:Tname => (`<implicit-prod-result>`, ()).1

;; test.spectec:7234.1-7242.18
rec {

;; test.spectec:7234.1-7235.26
grammar Tblockcomment : ()
  ;; test.spectec:7235.5-7235.26
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{"(;"} {Tblockchar*{}} {";)"}} => (`<implicit-prod-result>`, ()).1

;; test.spectec:7238.1-7242.18
grammar Tblockchar : ()
  ;; test.spectec:7239.5-7239.47
  prod{`<implicit-prod-result>` : char, c : char} `<implicit-prod-result>`:c:Tchar => (`<implicit-prod-result>`, ()).1
    -- if ((c =/= `%`_char(59)) /\ (c =/= `%`_char(40)))
  ;; test.spectec:7240.5-7240.47
  prod{`<implicit-prod-result>` : (), c : char} `<implicit-prod-result>`:{{";"+{}} {c:Tchar}} => (`<implicit-prod-result>`, ()).1
    -- if ((c =/= `%`_char(59)) /\ (c =/= `%`_char(41)))
  ;; test.spectec:7241.5-7241.47
  prod{`<implicit-prod-result>` : (), c : char} `<implicit-prod-result>`:{{"("+{}} {c:Tchar}} => (`<implicit-prod-result>`, ()).1
    -- if ((c =/= `%`_char(59)) /\ (c =/= `%`_char(40)))
  ;; test.spectec:7242.5-7242.18
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:Tblockcomment => (`<implicit-prod-result>`, ()).1
}

;; test.spectec:7229.1-7229.18
grammar Teof : ()
  ;; test.spectec:7229.16-7229.18
  prod{`<implicit-prod-result>` : text} `<implicit-prod-result>`:"" => (`<implicit-prod-result>`, ()).1

;; test.spectec:7231.1-7232.44
grammar Tlinechar : ()
  ;; test.spectec:7232.5-7232.44
  prod{`<implicit-prod-result>` : char, c : char} `<implicit-prod-result>`:c:Tchar => (`<implicit-prod-result>`, ()).1
    -- if ((c!`%`_char.0 =/= 10) /\ (c!`%`_char.0 =/= 13))

;; test.spectec:7216.1-7217.28
grammar Tnewline : ()
  ;; test.spectec:7217.5-7217.9
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x0A => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:7217.12-7217.16
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x0D => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:7217.19-7217.28
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{0x0D} {0x0A}} => (`<implicit-prod-result>`, ()).1

;; test.spectec:7226.1-7227.38
grammar Tlinecomment : ()
  ;; test.spectec:7227.5-7227.38
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{";;"} {Tlinechar*{}} (Tnewline | Teof)} => (`<implicit-prod-result>`, ()).1

;; test.spectec:7222.1-7223.33
grammar Tcomment : ()
  ;; test.spectec:7223.5-7223.17
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:Tlinecomment => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:7223.20-7223.33
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:Tblockcomment => (`<implicit-prod-result>`, ()).1

;; test.spectec:7213.1-7214.20
grammar Tformat : ()
  ;; test.spectec:7214.5-7214.13
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:Tnewline => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:7214.16-7214.20
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:0x09 => (`<implicit-prod-result>`, ()).1

;; test.spectec:7210.1-7248.41
rec {

;; test.spectec:7210.1-7211.41
grammar Tspace : ()
  ;; test.spectec:7211.5-7211.41
  prod{`<implicit-prod-result>` : ()} [`<implicit-prod-result>`]:({" "} | Tformat | Tcomment | Tannot)*{} => (`<implicit-prod-result>`, ()).1

;; test.spectec:7247.1-7248.41
grammar Tannot : ()
  ;; test.spectec:7248.5-7248.41
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{"(@"} Tannotid {(Tspace | Ttoken)*{}} {")"}} => (`<implicit-prod-result>`, ()).1
}

;; test.spectec:7266.1-7267.47
grammar Tsign : int
  ;; test.spectec:7267.5-7267.17
  prod eps => + (1 : nat <:> int)
  ;; test.spectec:7267.20-7267.32
  prod "+" => + (1 : nat <:> int)
  ;; test.spectec:7267.35-7267.47
  prod "-" => - (1 : nat <:> int)

;; test.spectec:7277.1-7279.40
rec {

;; test.spectec:7277.1-7279.40
grammar Tnum : nat
  ;; test.spectec:7278.5-7278.18
  prod{d : nat} d:Tdigit => d
  ;; test.spectec:7279.5-7279.40
  prod{n : n, d : nat} {{n:Tnum} {"_"?{}} {d:Tdigit}} => ((10 * n) + d)
}

;; test.spectec:7285.1-7287.42
grammar TuN(N : N) : uN(N)
  ;; test.spectec:7286.5-7286.42
  prod{n : n} n:Tnum => `%`_uN(n)
    -- if (n < (2 ^ N))
  ;; test.spectec:7287.5-7287.42
  prod{n : n} {{"0x"} {n:Thexnum}} => `%`_uN(n)
    -- if (n < (2 ^ N))

;; test.spectec:7289.1-7290.71
grammar TsN(N : N) : sN(N)
  ;; test.spectec:7290.5-7290.71
  prod{s : int, n : n} {{s:Tsign} {`%`_uN(n):TuN(N)}} => `%`_sN((s * (n : nat <:> int)))
    -- if ((- ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) <= (s * (n : nat <:> int))) /\ ((s * (n : nat <:> int)) < ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)))

;; test.spectec:7292.1-7294.35
grammar TiN(N : N) : iN(N)
  ;; test.spectec:7293.5-7293.18
  prod{n : n} `%`_uN(n):TuN(N) => `%`_iN(n)
  ;; test.spectec:7294.5-7294.35
  prod{i : sN(N)} i:TsN(N) => `%`_iN($inv_signed_(N, i!`%`_sN.0))

;; test.spectec:7297.1-7299.48
rec {

;; test.spectec:7297.1-7299.48
grammar Tfrac : rat
  ;; test.spectec:7298.5-7298.26
  prod{d : nat} d:Tdigit => ((d : nat <:> rat) / (10 : nat <:> rat))
  ;; test.spectec:7299.5-7299.48
  prod{d : nat, p : rat} {{d:Tdigit} {"_"?{}} {p:Tfrac}} => (((d + ((p / (10 : nat <:> rat)) : rat <:> nat)) : nat <:> rat) / (10 : nat <:> rat))
}

;; test.spectec:7301.1-7303.54
rec {

;; test.spectec:7301.1-7303.54
grammar Thexfrac : rat
  ;; test.spectec:7302.5-7302.29
  prod{h : nat} h:Thexdigit => ((h : nat <:> rat) / (16 : nat <:> rat))
  ;; test.spectec:7303.5-7303.54
  prod{h : nat, p : rat} {{h:Thexdigit} {"_"?{}} {p:Thexfrac}} => (((h + ((p / (16 : nat <:> rat)) : rat <:> nat)) : nat <:> rat) / (16 : nat <:> rat))
}

;; test.spectec:7305.1-7307.35
grammar Tmant : rat
  ;; test.spectec:7306.5-7306.21
  prod{p : nat} {{p:Tnum} {"."?{}}} => (p : nat <:> rat)
  ;; test.spectec:7307.5-7307.35
  prod{p : nat, q : rat} {{p:Tnum} {"."} {q:Tfrac}} => ((p + (q : rat <:> nat)) : nat <:> rat)

;; test.spectec:7309.1-7311.41
grammar Thexmant : rat
  ;; test.spectec:7310.5-7310.24
  prod{p : nat} {{p:Thexnum} {"."?{}}} => (p : nat <:> rat)
  ;; test.spectec:7311.5-7311.41
  prod{p : nat, q : rat} {{p:Thexnum} {"."} {q:Thexfrac}} => ((p + (q : rat <:> nat)) : nat <:> rat)

;; test.spectec:7318.1-7319.62
grammar Tfloat : rat
  ;; test.spectec:7319.5-7319.62
  prod{p : rat, s : int, ee : nat} {{p:Tmant} ({"E"} | {"e"}) {s:Tsign} {ee:Tnum}} => (p * ((10 ^ ((s * (ee : nat <:> int)) : int <:> nat)) : nat <:> rat))

;; test.spectec:7321.1-7322.69
grammar Thexfloat : rat
  ;; test.spectec:7322.5-7322.69
  prod{p : rat, s : int, ee : nat} {{"0x"} {p:Thexmant} ({"P"} | {"p"}) {s:Tsign} {ee:Tnum}} => (p * ((2 ^ ((s * (ee : nat <:> int)) : int <:> nat)) : nat <:> rat))

;; test.spectec:7324.1-7329.67
grammar TfNmag(N : N) : fNmag(N)
  ;; test.spectec:7325.5-7325.61
  prod{q : rat} q:Tfloat => $ieee_(N, q)
    -- if ($ieee_(N, q) =/= INF_fNmag)
  ;; test.spectec:7326.5-7326.61
  prod{q : rat} q:Thexfloat => $ieee_(N, q)
    -- if ($ieee_(N, q) =/= INF_fNmag)
  ;; test.spectec:7327.5-7327.17
  prod "inf" => INF_fNmag
  ;; test.spectec:7328.5-7328.29
  prod "nan" => NAN_fNmag($canon_(N))
  ;; test.spectec:7329.5-7329.67
  prod{n : n} {{"nan:0x"} {n:Thexnum}} => NAN_fNmag(n)
    -- if ((1 <= n) /\ (n < (2 ^ $signif(N))))

;; test.spectec:7331.1-7333.39
grammar TfN(N : N) : fN(N)
  ;; test.spectec:7332.5-7332.39
  prod{q : fNmag(N)} {{+ (1 : nat <:> int):Tsign} {q:TfNmag(N)}} => POS_fN(q)
  ;; test.spectec:7333.5-7333.39
  prod{q : fNmag(N)} {{- (1 : nat <:> int):Tsign} {q:TfNmag(N)}} => NEG_fN(q)

;; test.spectec:7336.1-7336.27
grammar Tu8 : u8
  ;; test.spectec:7336.20-7336.27
  prod{`<implicit-prod-result>` : uN(8)} `<implicit-prod-result>`:TuN(8) => `<implicit-prod-result>`

;; test.spectec:7337.1-7337.30
grammar Tu32 : u32
  ;; test.spectec:7337.22-7337.30
  prod{`<implicit-prod-result>` : uN(32)} `<implicit-prod-result>`:TuN(32) => `<implicit-prod-result>`

;; test.spectec:7338.1-7338.30
grammar Tu64 : u64
  ;; test.spectec:7338.22-7338.30
  prod{`<implicit-prod-result>` : uN(64)} `<implicit-prod-result>`:TuN(64) => `<implicit-prod-result>`

;; test.spectec:7339.1-7339.27
grammar Ti8 : u8
  ;; test.spectec:7339.20-7339.27
  prod{`<implicit-prod-result>` : iN(8)} `<implicit-prod-result>`:TiN(8) => `<implicit-prod-result>`

;; test.spectec:7340.1-7340.30
grammar Ti16 : u16
  ;; test.spectec:7340.22-7340.30
  prod{`<implicit-prod-result>` : iN(16)} `<implicit-prod-result>`:TiN(16) => `<implicit-prod-result>`

;; test.spectec:7341.1-7341.30
grammar Ti32 : u32
  ;; test.spectec:7341.22-7341.30
  prod{`<implicit-prod-result>` : iN(32)} `<implicit-prod-result>`:TiN(32) => `<implicit-prod-result>`

;; test.spectec:7342.1-7342.30
grammar Ti64 : u64
  ;; test.spectec:7342.22-7342.30
  prod{`<implicit-prod-result>` : iN(64)} `<implicit-prod-result>`:TiN(64) => `<implicit-prod-result>`

;; test.spectec:7343.1-7343.30
grammar Tf32 : f32
  ;; test.spectec:7343.22-7343.30
  prod{`<implicit-prod-result>` : fN(32)} `<implicit-prod-result>`:TfN(32) => `<implicit-prod-result>`

;; test.spectec:7344.1-7344.30
grammar Tf64 : f64
  ;; test.spectec:7344.22-7344.30
  prod{`<implicit-prod-result>` : fN(64)} `<implicit-prod-result>`:TfN(64) => `<implicit-prod-result>`

;; test.spectec:7370.1-7371.43
grammar Tlist(syntax el, grammar TX : el) : el*
  ;; test.spectec:7371.5-7371.43
  prod{`el*` : el*} el:TX*{el <- `el*`} => el*{el <- `el*`}
    -- if (|el*{el <- `el*`}| < (2 ^ 32))

;; test.spectec:7438.1-7440.35
grammar Tidx_(ids : name?*) : idx
  ;; test.spectec:7439.5-7439.16
  prod{x : idx} x:Tu32 => x
  ;; test.spectec:7440.5-7440.35
  prod{x : idx, id : name} id:Tid => x
    -- if (ids[x!`%`_idx.0] = ?(id))

;; test.spectec:7442.1-7442.48
grammar Ttypeidx_(I : I) : typeidx
  ;; test.spectec:7442.34-7442.48
  prod{`<implicit-prod-result>` : idx} `<implicit-prod-result>`:Tidx_(I.TYPES_I) => `<implicit-prod-result>`

;; test.spectec:7443.1-7443.45
grammar Ttagidx_(I : I) : tagidx
  ;; test.spectec:7443.32-7443.45
  prod{`<implicit-prod-result>` : idx} `<implicit-prod-result>`:Tidx_(I.TAGS_I) => `<implicit-prod-result>`

;; test.spectec:7444.1-7444.54
grammar Tglobalidx_(I : I) : globalidx
  ;; test.spectec:7444.38-7444.54
  prod{`<implicit-prod-result>` : idx} `<implicit-prod-result>`:Tidx_(I.GLOBALS_I) => `<implicit-prod-result>`

;; test.spectec:7445.1-7445.45
grammar Tmemidx_(I : I) : memidx
  ;; test.spectec:7445.32-7445.45
  prod{`<implicit-prod-result>` : idx} `<implicit-prod-result>`:Tidx_(I.MEMS_I) => `<implicit-prod-result>`

;; test.spectec:7446.1-7446.51
grammar Ttableidx_(I : I) : tableidx
  ;; test.spectec:7446.36-7446.51
  prod{`<implicit-prod-result>` : idx} `<implicit-prod-result>`:Tidx_(I.TABLES_I) => `<implicit-prod-result>`

;; test.spectec:7447.1-7447.48
grammar Tfuncidx_(I : I) : funcidx
  ;; test.spectec:7447.34-7447.48
  prod{`<implicit-prod-result>` : idx} `<implicit-prod-result>`:Tidx_(I.FUNCS_I) => `<implicit-prod-result>`

;; test.spectec:7448.1-7448.48
grammar Tdataidx_(I : I) : dataidx
  ;; test.spectec:7448.34-7448.48
  prod{`<implicit-prod-result>` : idx} `<implicit-prod-result>`:Tidx_(I.DATAS_I) => `<implicit-prod-result>`

;; test.spectec:7449.1-7449.48
grammar Telemidx_(I : I) : elemidx
  ;; test.spectec:7449.34-7449.48
  prod{`<implicit-prod-result>` : idx} `<implicit-prod-result>`:Tidx_(I.ELEMS_I) => `<implicit-prod-result>`

;; test.spectec:7450.1-7450.51
grammar Tlocalidx_(I : I) : localidx
  ;; test.spectec:7450.36-7450.51
  prod{`<implicit-prod-result>` : idx} `<implicit-prod-result>`:Tidx_(I.LOCALS_I) => `<implicit-prod-result>`

;; test.spectec:7451.1-7451.51
grammar Tlabelidx_(I : I) : labelidx
  ;; test.spectec:7451.36-7451.51
  prod{`<implicit-prod-result>` : idx} `<implicit-prod-result>`:Tidx_(I.LABELS_I) => `<implicit-prod-result>`

;; test.spectec:7452.1-7452.64
grammar Tfieldidx__(I : I, x : idx) : fieldidx
  ;; test.spectec:7452.46-7452.64
  prod{`<implicit-prod-result>` : idx} `<implicit-prod-result>`:Tidx_(I.FIELDS_I[x!`%`_idx.0]) => `<implicit-prod-result>`

;; test.spectec:7454.1-7459.44
grammar Texternidx_(I : I) : externidx
  ;; test.spectec:7455.5-7455.41
  prod{x : idx} {{"("} {"tag"} {x:Ttagidx_(I)} {")"}} => TAG_externidx(x)
  ;; test.spectec:7456.5-7456.50
  prod{x : idx} {{"("} {"global"} {x:Tglobalidx_(I)} {")"}} => GLOBAL_externidx(x)
  ;; test.spectec:7457.5-7457.44
  prod{x : idx} {{"("} {"memory"} {x:Tmemidx_(I)} {")"}} => MEM_externidx(x)
  ;; test.spectec:7458.5-7458.47
  prod{x : idx} {{"("} {"table"} {x:Ttableidx_(I)} {")"}} => TABLE_externidx(x)
  ;; test.spectec:7459.5-7459.44
  prod{x : idx} {{"("} {"func"} {x:Tfuncidx_(I)} {")"}} => FUNC_externidx(x)

;; test.spectec:7474.1-7478.17
grammar Tnumtype : numtype
  ;; test.spectec:7475.5-7475.17
  prod "i32" => I32_numtype
  ;; test.spectec:7476.5-7476.17
  prod "i64" => I64_numtype
  ;; test.spectec:7477.5-7477.17
  prod "f32" => F32_numtype
  ;; test.spectec:7478.5-7478.17
  prod "f64" => F64_numtype

;; test.spectec:7480.1-7481.19
grammar Tvectype : vectype
  ;; test.spectec:7481.5-7481.19
  prod "v128" => V128_vectype

;; test.spectec:7484.1-7496.27
grammar Tabsheaptype : heaptype
  ;; test.spectec:7485.5-7485.17
  prod "any" => ANY_heaptype
  ;; test.spectec:7486.5-7486.15
  prod "eq" => EQ_heaptype
  ;; test.spectec:7487.5-7487.17
  prod "i31" => I31_heaptype
  ;; test.spectec:7488.5-7488.23
  prod "struct" => STRUCT_heaptype
  ;; test.spectec:7489.5-7489.21
  prod "array" => ARRAY_heaptype
  ;; test.spectec:7490.5-7490.19
  prod "none" => NONE_heaptype
  ;; test.spectec:7491.5-7491.19
  prod "func" => FUNC_heaptype
  ;; test.spectec:7492.5-7492.23
  prod "nofunc" => NOFUNC_heaptype
  ;; test.spectec:7493.5-7493.17
  prod "exn" => EXN_heaptype
  ;; test.spectec:7494.5-7494.21
  prod "noexn" => NOEXN_heaptype
  ;; test.spectec:7495.5-7495.23
  prod "extern" => EXTERN_heaptype
  ;; test.spectec:7496.5-7496.27
  prod "noextern" => NOEXTERN_heaptype

;; test.spectec:7498.1-7500.29
grammar Theaptype_(I : I) : heaptype
  ;; test.spectec:7499.5-7499.26
  prod{ht : heaptype} ht:Tabsheaptype => ht
  ;; test.spectec:7500.5-7500.29
  prod{x : idx} x:Ttypeidx_(I) => _IDX_heaptype(x)

;; test.spectec:7502.1-7503.19
grammar Tnull : null
  ;; test.spectec:7503.5-7503.19
  prod "null" => NULL_null

;; test.spectec:7509.1-7521.55
grammar Treftype_(I : I) : reftype
  ;; test.spectec:7506.5-7506.64
  prod{`null?` : null?, ht : heaptype} {{"("} {"ref"} {null?{null <- `null?`}:Tnull?{}} {ht:Theaptype_(I)} {")"}} => REF_reftype(null?{null <- `null?`}, ht)

;; test.spectec:7523.1-7526.26
grammar Tvaltype_(I : I) : valtype
  ;; test.spectec:7524.5-7524.22
  prod{nt : numtype} nt:Tnumtype => (nt : numtype <: valtype)
  ;; test.spectec:7525.5-7525.22
  prod{vt : vectype} vt:Tvectype => (vt : vectype <: valtype)
  ;; test.spectec:7526.5-7526.26
  prod{rt : reftype} rt:Treftype_(I) => (rt : reftype <: valtype)

;; test.spectec:7531.1-7533.17
grammar Tpacktype : packtype
  ;; test.spectec:7532.5-7532.15
  prod "i8" => I8_packtype
  ;; test.spectec:7533.5-7533.17
  prod "i16" => I16_packtype

;; test.spectec:7535.1-7537.23
grammar Tstoragetype_(I : I) : storagetype
  ;; test.spectec:7536.5-7536.24
  prod{t : valtype} t:Tvaltype_(I) => (t : valtype <: storagetype)
  ;; test.spectec:7537.5-7537.23
  prod{pt : packtype} pt:Tpacktype => (pt : packtype <: storagetype)

;; test.spectec:7539.1-7541.48
grammar Tfieldtype_(I : I) : fieldtype
  ;; test.spectec:7540.5-7540.30
  prod{zt : storagetype} zt:Tstoragetype_(I) => `%%`_fieldtype(?(), zt)
  ;; test.spectec:7541.5-7541.48
  prod{zt : storagetype} {{"("} {"mut"} {zt:Tstoragetype_(I)} {")"}} => `%%`_fieldtype(?(MUT_mut), zt)

;; test.spectec:7549.1-7549.124
grammar Tfield_(I : I) : (fieldtype, name?)
  ;; test.spectec:7544.5-7544.60
  prod{ft : fieldtype, `id?` : char?} {{"("} {"field"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {ft:Tfieldtype_(I)} {")"}} => (ft, ?(`%`_name(lift(id?{id <- `id?`}))))

;; test.spectec:7555.1-7555.118
grammar Tparam_(I : I) : (valtype, name?)
  ;; test.spectec:7552.5-7552.56
  prod{t : valtype, `id?` : char?} {{"("} {"param"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {t:Tvaltype_(I)} {")"}} => (t, ?(`%`_name(lift(id?{id <- `id?`}))))

;; test.spectec:7561.1-7561.112
grammar Tresult_(I : I) : valtype
  ;; test.spectec:7558.5-7558.41
  prod{t : valtype} {{"("} {"result"} {t:Tvaltype_(I)} {")"}} => t

;; test.spectec:7563.1-7566.111
grammar Tcomptype_(I : I) : (comptype, idctxt)
  ;; test.spectec:7564.5-7564.84
  prod{`ft*` : fieldtype*, `id?*` : char?*} {{"("} {"struct"} {(ft, ?(`%`_name(lift(id?{id <- `id?`}))))*{ft <- `ft*`, `id?` <- `id?*`}:Tlist(syntax (fieldtype, name?), grammar Tfield_(I))} {")"}} => (STRUCT_comptype(`%`_list(ft*{ft <- `ft*`})), {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [?(`%`_name(lift(id?{id <- `id?`})))*{`id?` <- `id?*`}], TYPEDEFS []})
  ;; test.spectec:7565.5-7565.68
  prod{ft : fieldtype} {{"("} {"array"} {ft:Tfieldtype_(I)} {")"}} => (ARRAY_comptype(ft), {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [[?(`%`_name([]))]], TYPEDEFS []})
  ;; test.spectec:7566.5-7566.111
  prod{`t_1*` : valtype*, `t_2*` : valtype*, `id?*` : char?*} {{"("} {"func"} {(t_1, ?(`%`_name(lift(id?{id <- `id?`}))))*{`id?` <- `id?*`, t_1 <- `t_1*`}:Tlist(syntax (valtype, name?), grammar Tparam_(I))} {t_2*{t_2 <- `t_2*`}:Tlist(syntax valtype, grammar Tresult_(I))} {")"}} => (`FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})), {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [[?(`%`_name([]))]], TYPEDEFS []})

;; test.spectec:7569.1-7570.21
grammar Tfinal : final
  ;; test.spectec:7570.5-7570.21
  prod "final" => FINAL_final

;; test.spectec:7576.1-7576.109
grammar Tsubtype_(I : I) : (subtype, idctxt)
  ;; test.spectec:7573.5-7573.111
  prod{`fin?` : final?, `x*` : idx*, ct : comptype, I' : I} {{"("} {"sub"} {fin?{fin <- `fin?`}:Tfinal?{}} {x*{x <- `x*`}:Tlist(syntax typeidx, grammar Ttypeidx_(I))} {(ct, I'):Tcomptype_(I)} {")"}} => (SUB_subtype(fin?{fin <- `fin?`}, _IDX_typeuse(x)*{x <- `x*`}, ct), I')

;; test.spectec:7578.1-7579.78
grammar Ttypedef_(I : I) : (subtype, idctxt)
  ;; test.spectec:7579.5-7579.78
  prod{st : subtype, I' : I, `id?` : char?} {{"("} {"type"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {(st, I'):Tsubtype_(I)} {")"}} => (st, I' +++ {TYPES [?(`%`_name(lift(id?{id <- `id?`})))], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})

;; test.spectec:7585.1-7585.99
grammar Trectype_(I : I) : (rectype, idctxt)
  ;; test.spectec:7582.5-7582.81
  prod{`st*` : subtype*, `I'*` : I*} {{"("} {"rec"} {(st, I')*{I' <- `I'*`, st <- `st*`}:Tlist(syntax (subtype, idctxt), grammar Ttypedef_(I))} {")"}} => (REC_rectype(`%`_list(st*{st <- `st*`})), $concat_idctxt(I'*{I' <- `I'*`}))

;; test.spectec:7595.1-7595.57
grammar Taddrtype : addrtype
  ;; test.spectec:7591.5-7591.17
  prod "i32" => I32_addrtype
  ;; test.spectec:7592.5-7592.17
  prod "i64" => I64_addrtype

;; test.spectec:7598.1-7600.31
grammar Tlimits : limits
  ;; test.spectec:7599.5-7599.26
  prod{n : n} `%`_u64(n):Tu64 => `[%..%]`_limits(`%`_u64(n), ?())
  ;; test.spectec:7600.5-7600.31
  prod{n : n, m : m} {{`%`_u64(n):Tu64} {`%`_u64(m):Tu64}} => `[%..%]`_limits(`%`_u64(n), ?(`%`_u64(m)))

;; test.spectec:7641.1-7644.81
grammar Ttypeuse_(I : I) : (typeidx, idctxt)
  ;; test.spectec:7628.5-7632.39
  prod{x : idx, I' : I, `st*` : subtype*, i : n, `t_1*` : valtype*, `t_2*` : valtype*} {{"("} {"type"} {x:Ttypeidx_(I)} {")"}} => (x, I')
    -- if (I.TYPEDEFS_I[x!`%`_idx.0] = ?(_DEF_deftype(REC_rectype(`%`_list(st*{st <- `st*`})), i)))
    -- if (st*{st <- `st*`}[i] = SUB_subtype(?(FINAL_final), [], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`}))))
    -- if (I' = {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS ?(`%`_name([]))^|t_1*{t_1 <- `t_1*`}|{}, LABELS [], FIELDS [], TYPEDEFS []})
  ;; test.spectec:7633.5-7638.29
  prod{x : idx, I' : I, `id?*` : char?*, `t_1*` : valtype*, `t_2*` : valtype*, `st*` : subtype*, i : n} {{"("} {"type"} {x:Ttypeidx_(I)} {")"} {(t_1, ?(`%`_name(lift(id?{id <- `id?`}))))*{`id?` <- `id?*`, t_1 <- `t_1*`}:Tparam_(I)*{}} {t_2*{t_2 <- `t_2*`}:Tresult_(I)*{}}} => (x, I')
    -- if (I.TYPEDEFS_I[x!`%`_idx.0] = ?(_DEF_deftype(REC_rectype(`%`_list(st*{st <- `st*`})), i)))
    -- if (st*{st <- `st*`}[i] = SUB_subtype(?(FINAL_final), [], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`}))))
    -- if (I' = {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS ?(`%`_name(lift(id?{id <- `id?`})))*{`id?` <- `id?*`}, LABELS [], FIELDS [], TYPEDEFS []})
    -- Idctxt_ok: `|-%:OK`(I')

;; test.spectec:7603.1-7604.34
grammar Ttagtype_(I : I) : tagtype
  ;; test.spectec:7604.5-7604.34
  prod{x : idx, I' : I} (x, I'):Ttypeuse_(I) => _IDX_tagtype(x)

;; test.spectec:7606.1-7608.42
grammar Tglobaltype_(I : I) : globaltype
  ;; test.spectec:7607.5-7607.24
  prod{t : valtype} t:Tvaltype_(I) => `%%`_globaltype(?(), t)
  ;; test.spectec:7608.5-7608.42
  prod{t : valtype} {{"("} {"mut"} {t:Tvaltype_(I)} {")"}} => `%%`_globaltype(?(MUT_mut), t)

;; test.spectec:7610.1-7611.44
grammar Tmemtype_(I : I) : memtype
  ;; test.spectec:7611.5-7611.44
  prod{at : addrtype, lim : limits} {{at:Taddrtype} {lim:Tlimits}} => `%%PAGE`_memtype(at, lim)

;; test.spectec:7613.1-7614.58
grammar Ttabletype_(I : I) : tabletype
  ;; test.spectec:7614.5-7614.58
  prod{at : addrtype, lim : limits, rt : reftype} {{at:Taddrtype} {lim:Tlimits} {rt:Treftype_(I)}} => `%%%`_tabletype(at, lim, rt)

;; test.spectec:7617.1-7622.86
grammar Texterntype_(I : I) : (externtype, idctxt)
  ;; test.spectec:7618.5-7618.69
  prod{jt : tagtype, `id?` : char?} {{"("} {"tag"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {jt:Ttagtype_(I)} {")"}} => (TAG_externtype(jt), {TYPES [], TAGS [?(`%`_name(lift(id?{id <- `id?`})))], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})
  ;; test.spectec:7619.5-7619.81
  prod{gt : globaltype, `id?` : char?} {{"("} {"global"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {gt:Tglobaltype_(I)} {")"}} => (GLOBAL_externtype(gt), {TYPES [], TAGS [], GLOBALS [?(`%`_name(lift(id?{id <- `id?`})))], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})
  ;; test.spectec:7620.5-7620.72
  prod{mt : memtype, `id?` : char?} {{"("} {"memory"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {mt:Tmemtype_(I)} {")"}} => (MEM_externtype(mt), {TYPES [], TAGS [], GLOBALS [], MEMS [?(`%`_name(lift(id?{id <- `id?`})))], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})
  ;; test.spectec:7621.5-7621.77
  prod{tt : tabletype, `id?` : char?} {{"("} {"table"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {tt:Ttabletype_(I)} {")"}} => (TABLE_externtype(tt), {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [?(`%`_name(lift(id?{id <- `id?`})))], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})
  ;; test.spectec:7622.5-7622.86
  prod{x : idx, `id?` : char?, I' : I} {{"("} {"func"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {(x, I'):Ttypeuse_(I)} {")"}} => (FUNC_externtype(_IDX_typeuse(x)), {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [?(`%`_name(lift(id?{id <- `id?`})))], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})

;; test.spectec:7662.1-7665.79
grammar Tlabel_(I : I) : (name?, I)
  ;; test.spectec:7663.5-7663.36
  prod eps => (?(), {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []} +++ I)
  ;; test.spectec:7664.5-7664.78
  prod{id : name} id:Tid => (?(id), {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [?(id)], FIELDS [], TYPEDEFS []} +++ I)
    -- if ~ (?(id) <- I.LABELS_I)
  ;; test.spectec:7665.5-7665.79
  prod{id : name, x : idx} id:Tid => (?(id), {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [?(id)], FIELDS [], TYPEDEFS []} +++ I[LABELS_I[x!`%`_idx.0] = ?()])
    -- if (?(id) = I.LABELS_I[x!`%`_idx.0])

;; test.spectec:7711.1-7715.31
grammar Tblocktype_(I : I) : blocktype
  ;; test.spectec:7712.5-7712.34
  prod{`t?` : valtype?} t?{t <- `t?`}:Tresult_(I)?{} => _RESULT_blocktype(t?{t <- `t?`})
  ;; test.spectec:7713.5-7715.31
  prod{x : idx, I' : I} (x, I'):Ttypeuse_(I) => _IDX_blocktype(x)
    -- if (I' = {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS ?(`%`_name([]))*{}, LABELS [], FIELDS [], TYPEDEFS []})

;; test.spectec:7747.1-7751.63
grammar Tcatch_(I : I) : catch
  ;; test.spectec:7748.5-7748.63
  prod{x : idx, l : labelidx} {{"("} {"catch"} {x:Ttagidx_(I)} {l:Tlabelidx_(I)} {")"}} => CATCH_catch(x, l)
  ;; test.spectec:7749.5-7749.71
  prod{x : idx, l : labelidx} {{"("} {"catch_ref"} {x:Ttagidx_(I)} {l:Tlabelidx_(I)} {")"}} => CATCH_REF_catch(x, l)
  ;; test.spectec:7750.5-7750.55
  prod{l : labelidx} {{"("} {"catch_all"} {l:Tlabelidx_(I)} {")"}} => CATCH_ALL_catch(l)
  ;; test.spectec:7751.5-7751.63
  prod{l : labelidx} {{"("} {"catch_all_ref"} {l:Tlabelidx_(I)} {")"}} => CATCH_ALL_REF_catch(l)

;; test.spectec:7687.1-7696.73
grammar Tfoldedinstr_(I : I) : instr*

;; test.spectec:7843.1-7844.15
grammar Tlaneidx : laneidx
  ;; test.spectec:7844.5-7844.15
  prod{i : u8} i:Tu8 => i

;; test.spectec:7839.1-7841.13
grammar Talign_(N : N) : u32
  ;; test.spectec:7840.5-7840.43
  prod{n : n, m : m} {{"align="} {`%`_u64(m):Tu64}} => `%`_u32(n)
    -- if (m = (2 ^ n))
  ;; test.spectec:7841.5-7841.13
  prod eps => `%`_u32(N)

;; test.spectec:7835.1-7837.13
grammar Toffset : u64
  ;; test.spectec:7836.5-7836.26
  prod{m : m} {{"offset="} {`%`_u64(m):Tu64}} => `%`_u64(m)
  ;; test.spectec:7837.5-7837.13
  prod eps => `%`_u64(0)

;; test.spectec:7832.1-7833.50
grammar Tmemarg_(N : N) : memarg
  ;; test.spectec:7833.5-7833.50
  prod{n : n, m : m} {{`%`_u32(n):Talign_(N)} {`%`_u64(m):Toffset}} => {ALIGN `%`_u32(n), OFFSET `%`_u64(m)}

;; test.spectec:8660.1-8661.96
grammar Tplaininstr_(I : I) : instr
  ;; test.spectec:7702.5-7702.33
  prod "unreachable" => UNREACHABLE_instr
  ;; test.spectec:7703.5-7703.17
  prod "nop" => NOP_instr
  ;; test.spectec:7704.5-7704.19
  prod "drop" => DROP_instr
  ;; test.spectec:7705.5-7705.48
  prod{`t*?` : valtype*?} {{"select"} {t*{t <- `t*`}:Tresult_(I)*{}?{`t*` <- `t*?`}}} => SELECT_instr(t*{t <- `t*`}?{`t*` <- `t*?`})
  ;; test.spectec:7757.5-7757.33
  prod{l : labelidx} {{"br"} {l:Tlabelidx_(I)}} => BR_instr(l)
  ;; test.spectec:7758.5-7758.39
  prod{l : labelidx} {{"br_if"} {l:Tlabelidx_(I)}} => BR_IF_instr(l)
  ;; test.spectec:7759.5-7759.68
  prod{`l*` : labelidx*, l' : labelidx} {{"br_table"} {l*{l <- `l*`}:Tlabelidx_(I)*{}} {l':Tlabelidx_(I)}} => BR_TABLE_instr(l*{l <- `l*`}, l')
  ;; test.spectec:7760.5-7760.49
  prod{l : labelidx} {{"br_on_null"} {l:Tlabelidx_(I)}} => BR_ON_NULL_instr(l)
  ;; test.spectec:7761.5-7761.57
  prod{l : labelidx} {{"br_on_non_null"} {l:Tlabelidx_(I)}} => BR_ON_NON_NULL_instr(l)
  ;; test.spectec:7762.5-7762.95
  prod{l : labelidx, rt_1 : reftype, rt_2 : reftype} {{"br_on_cast"} {l:Tlabelidx_(I)} {rt_1:Treftype_(I)} {rt_2:Treftype_(I)}} => BR_ON_CAST_instr(l, rt_1, rt_2)
  ;; test.spectec:7763.5-7763.105
  prod{l : labelidx, rt_1 : reftype, rt_2 : reftype} {{"br_on_cast_fail"} {l:Tlabelidx_(I)} {rt_1:Treftype_(I)} {rt_2:Treftype_(I)}} => BR_ON_CAST_FAIL_instr(l, rt_1, rt_2)
  ;; test.spectec:7767.5-7767.36
  prod{x : idx} {{"call"} {x:Tfuncidx_(I)}} => CALL_instr(x)
  ;; test.spectec:7768.5-7768.55
  prod{x : idx} {{"call_ref"} {x:Ttypeidx_(I)}} => CALL_REF_instr(_IDX_typeuse(x))
  ;; test.spectec:7769.5-7770.31
  prod{x : idx, y : idx, I' : I} {{"call_indirect"} {x:Ttableidx_(I)} {(y, I'):Ttypeuse_(I)}} => CALL_INDIRECT_instr(x, _IDX_typeuse(y))
    -- if (I' = {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS ?(`%`_name([]))*{}, LABELS [], FIELDS [], TYPEDEFS []})
  ;; test.spectec:7771.5-7771.23
  prod "return" => RETURN_instr
  ;; test.spectec:7772.5-7772.50
  prod{x : idx} {{"return_call"} {x:Tfuncidx_(I)}} => RETURN_CALL_instr(x)
  ;; test.spectec:7773.5-7773.69
  prod{x : idx} {{"return_call_ref"} {x:Ttypeidx_(I)}} => RETURN_CALL_REF_instr(_IDX_typeuse(x))
  ;; test.spectec:7774.5-7775.31
  prod{x : idx, y : idx, I' : I} {{"return_call_indirect"} {x:Ttableidx_(I)} {(y, I'):Ttypeuse_(I)}} => RETURN_CALL_INDIRECT_instr(x, _IDX_typeuse(y))
    -- if (I' = {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS ?(`%`_name([]))*{}, LABELS [], FIELDS [], TYPEDEFS []})
  ;; test.spectec:7784.5-7784.37
  prod{x : idx} {{"throw"} {x:Ttagidx_(I)}} => THROW_instr(x)
  ;; test.spectec:7785.5-7785.29
  prod "throw_ref" => THROW_REF_instr
  ;; test.spectec:7792.5-7792.47
  prod{x : idx} {{"local.get"} {x:Tlocalidx_(I)}} => `LOCAL.GET`_instr(x)
  ;; test.spectec:7793.5-7793.47
  prod{x : idx} {{"local.set"} {x:Tlocalidx_(I)}} => `LOCAL.SET`_instr(x)
  ;; test.spectec:7794.5-7794.47
  prod{x : idx} {{"local.tee"} {x:Tlocalidx_(I)}} => `LOCAL.TEE`_instr(x)
  ;; test.spectec:7798.5-7798.50
  prod{x : idx} {{"global.get"} {x:Tglobalidx_(I)}} => `GLOBAL.GET`_instr(x)
  ;; test.spectec:7799.5-7799.50
  prod{x : idx} {{"global.set"} {x:Tglobalidx_(I)}} => `GLOBAL.SET`_instr(x)
  ;; test.spectec:7806.5-7806.47
  prod{x : idx} {{"table.get"} {x:Ttableidx_(I)}} => `TABLE.GET`_instr(x)
  ;; test.spectec:7807.5-7807.47
  prod{x : idx} {{"table.set"} {x:Ttableidx_(I)}} => `TABLE.SET`_instr(x)
  ;; test.spectec:7808.5-7808.49
  prod{x : idx} {{"table.size"} {x:Ttableidx_(I)}} => `TABLE.SIZE`_instr(x)
  ;; test.spectec:7809.5-7809.49
  prod{x : idx} {{"table.grow"} {x:Ttableidx_(I)}} => `TABLE.GROW`_instr(x)
  ;; test.spectec:7810.5-7810.49
  prod{x : idx} {{"table.fill"} {x:Ttableidx_(I)}} => `TABLE.FILL`_instr(x)
  ;; test.spectec:7811.5-7811.75
  prod{x_1 : idx, x_2 : idx} {{"table.copy"} {x_1:Ttableidx_(I)} {x_2:Ttableidx_(I)}} => `TABLE.COPY`_instr(x_1, x_2)
  ;; test.spectec:7812.5-7812.66
  prod{x : idx, y : idx} {{"table.init"} {x:Ttableidx_(I)} {y:Telemidx_(I)}} => `TABLE.INIT`_instr(x, y)
  ;; test.spectec:7826.5-7826.46
  prod{x : idx} {{"elem.drop"} {x:Telemidx_(I)}} => `ELEM.DROP`_instr(x)
  ;; test.spectec:7847.5-7847.61
  prod{x : idx, ao : memarg} {{"i32.load"} {x:Tmemidx_(I)} {ao:Tmemarg_(4)}} => LOAD_instr(I32_numtype, ?(), x, ao)
  ;; test.spectec:7848.5-7848.61
  prod{x : idx, ao : memarg} {{"i64.load"} {x:Tmemidx_(I)} {ao:Tmemarg_(8)}} => LOAD_instr(I64_numtype, ?(), x, ao)
  ;; test.spectec:7849.5-7849.61
  prod{x : idx, ao : memarg} {{"f32.load"} {x:Tmemidx_(I)} {ao:Tmemarg_(4)}} => LOAD_instr(F32_numtype, ?(), x, ao)
  ;; test.spectec:7850.5-7850.61
  prod{x : idx, ao : memarg} {{"f64.load"} {x:Tmemidx_(I)} {ao:Tmemarg_(8)}} => LOAD_instr(F64_numtype, ?(), x, ao)
  ;; test.spectec:7851.5-7851.73
  prod{x : idx, ao : memarg} {{"i32.load8_s"} {x:Tmemidx_(I)} {ao:Tmemarg_(1)}} => LOAD_instr(I32_numtype, ?(`%_%`_loadop_(`%`_sz(8), S_sx)), x, ao)
  ;; test.spectec:7852.5-7852.73
  prod{x : idx, ao : memarg} {{"i32.load8_u"} {x:Tmemidx_(I)} {ao:Tmemarg_(1)}} => LOAD_instr(I32_numtype, ?(`%_%`_loadop_(`%`_sz(8), U_sx)), x, ao)
  ;; test.spectec:7853.5-7853.75
  prod{x : idx, ao : memarg} {{"i32.load16_s"} {x:Tmemidx_(I)} {ao:Tmemarg_(2)}} => LOAD_instr(I32_numtype, ?(`%_%`_loadop_(`%`_sz(16), S_sx)), x, ao)
  ;; test.spectec:7854.5-7854.75
  prod{x : idx, ao : memarg} {{"i32.load16_u"} {x:Tmemidx_(I)} {ao:Tmemarg_(2)}} => LOAD_instr(I32_numtype, ?(`%_%`_loadop_(`%`_sz(16), U_sx)), x, ao)
  ;; test.spectec:7855.5-7855.73
  prod{x : idx, ao : memarg} {{"i64.load8_s"} {x:Tmemidx_(I)} {ao:Tmemarg_(1)}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(8), S_sx)), x, ao)
  ;; test.spectec:7856.5-7856.73
  prod{x : idx, ao : memarg} {{"i64.load8_u"} {x:Tmemidx_(I)} {ao:Tmemarg_(1)}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(8), U_sx)), x, ao)
  ;; test.spectec:7857.5-7857.75
  prod{x : idx, ao : memarg} {{"i64.load16_s"} {x:Tmemidx_(I)} {ao:Tmemarg_(2)}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(16), S_sx)), x, ao)
  ;; test.spectec:7858.5-7858.75
  prod{x : idx, ao : memarg} {{"i64.load16_u"} {x:Tmemidx_(I)} {ao:Tmemarg_(2)}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(16), U_sx)), x, ao)
  ;; test.spectec:7859.5-7859.75
  prod{x : idx, ao : memarg} {{"i64.load32_s"} {x:Tmemidx_(I)} {ao:Tmemarg_(4)}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(32), S_sx)), x, ao)
  ;; test.spectec:7860.5-7860.75
  prod{x : idx, ao : memarg} {{"i64.load32_u"} {x:Tmemidx_(I)} {ao:Tmemarg_(4)}} => LOAD_instr(I64_numtype, ?(`%_%`_loadop_(`%`_sz(32), U_sx)), x, ao)
  ;; test.spectec:7861.5-7861.65
  prod{x : idx, ao : memarg} {{"v128.load"} {x:Tmemidx_(I)} {ao:Tmemarg_(16)}} => VLOAD_instr(V128_vectype, ?(), x, ao)
  ;; test.spectec:7862.5-7862.89
  prod{x : idx, ao : memarg} {{"v128.load8x8_s"} {x:Tmemidx_(I)} {ao:Tmemarg_(8)}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(8), 8, S_sx)), x, ao)
  ;; test.spectec:7863.5-7863.89
  prod{x : idx, ao : memarg} {{"v128.load8x8_u"} {x:Tmemidx_(I)} {ao:Tmemarg_(8)}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(8), 8, U_sx)), x, ao)
  ;; test.spectec:7864.5-7864.91
  prod{x : idx, ao : memarg} {{"v128.load16x4_s"} {x:Tmemidx_(I)} {ao:Tmemarg_(8)}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(16), 4, S_sx)), x, ao)
  ;; test.spectec:7865.5-7865.91
  prod{x : idx, ao : memarg} {{"v128.load16x4_u"} {x:Tmemidx_(I)} {ao:Tmemarg_(8)}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(16), 4, U_sx)), x, ao)
  ;; test.spectec:7866.5-7866.91
  prod{x : idx, ao : memarg} {{"v128.load32x2_s"} {x:Tmemidx_(I)} {ao:Tmemarg_(8)}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(32), 2, S_sx)), x, ao)
  ;; test.spectec:7867.5-7867.91
  prod{x : idx, ao : memarg} {{"v128.load32x2_u"} {x:Tmemidx_(I)} {ao:Tmemarg_(8)}} => VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(32), 2, U_sx)), x, ao)
  ;; test.spectec:7868.5-7868.82
  prod{x : idx, ao : memarg} {{"v128.load8_splat"} {x:Tmemidx_(I)} {ao:Tmemarg_(1)}} => VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(8))), x, ao)
  ;; test.spectec:7869.5-7869.84
  prod{x : idx, ao : memarg} {{"v128.load16_splat"} {x:Tmemidx_(I)} {ao:Tmemarg_(2)}} => VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(16))), x, ao)
  ;; test.spectec:7870.5-7870.84
  prod{x : idx, ao : memarg} {{"v128.load32_splat"} {x:Tmemidx_(I)} {ao:Tmemarg_(4)}} => VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(32))), x, ao)
  ;; test.spectec:7871.5-7871.84
  prod{x : idx, ao : memarg} {{"v128.load64_splat"} {x:Tmemidx_(I)} {ao:Tmemarg_(8)}} => VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(64))), x, ao)
  ;; test.spectec:7872.5-7872.82
  prod{x : idx, ao : memarg} {{"v128.load32_zero"} {x:Tmemidx_(I)} {ao:Tmemarg_(4)}} => VLOAD_instr(V128_vectype, ?(ZERO_vloadop_(`%`_sz(32))), x, ao)
  ;; test.spectec:7873.5-7873.82
  prod{x : idx, ao : memarg} {{"v128.load64_zero"} {x:Tmemidx_(I)} {ao:Tmemarg_(8)}} => VLOAD_instr(V128_vectype, ?(ZERO_vloadop_(`%`_sz(64))), x, ao)
  ;; test.spectec:7874.5-7874.91
  prod{x : idx, ao : memarg, i : laneidx} {{"v128.load8_lane"} {x:Tmemidx_(I)} {ao:Tmemarg_(1)} {i:Tlaneidx}} => VLOAD_LANE_instr(V128_vectype, `%`_sz(8), x, ao, i)
  ;; test.spectec:7875.5-7875.93
  prod{x : idx, ao : memarg, i : laneidx} {{"v128.load16_lane"} {x:Tmemidx_(I)} {ao:Tmemarg_(2)} {i:Tlaneidx}} => VLOAD_LANE_instr(V128_vectype, `%`_sz(16), x, ao, i)
  ;; test.spectec:7876.5-7876.93
  prod{x : idx, ao : memarg, i : laneidx} {{"v128.load32_lane"} {x:Tmemidx_(I)} {ao:Tmemarg_(4)} {i:Tlaneidx}} => VLOAD_LANE_instr(V128_vectype, `%`_sz(32), x, ao, i)
  ;; test.spectec:7877.5-7877.93
  prod{x : idx, ao : memarg, i : laneidx} {{"v128.load64_lane"} {x:Tmemidx_(I)} {ao:Tmemarg_(8)} {i:Tlaneidx}} => VLOAD_LANE_instr(V128_vectype, `%`_sz(64), x, ao, i)
  ;; test.spectec:7878.5-7878.63
  prod{x : idx, ao : memarg} {{"i32.store"} {x:Tmemidx_(I)} {ao:Tmemarg_(4)}} => STORE_instr(I32_numtype, ?(), x, ao)
  ;; test.spectec:7879.5-7879.63
  prod{x : idx, ao : memarg} {{"i64.store"} {x:Tmemidx_(I)} {ao:Tmemarg_(8)}} => STORE_instr(I64_numtype, ?(), x, ao)
  ;; test.spectec:7880.5-7880.63
  prod{x : idx, ao : memarg} {{"f32.store"} {x:Tmemidx_(I)} {ao:Tmemarg_(4)}} => STORE_instr(F32_numtype, ?(), x, ao)
  ;; test.spectec:7881.5-7881.63
  prod{x : idx, ao : memarg} {{"f64.store"} {x:Tmemidx_(I)} {ao:Tmemarg_(8)}} => STORE_instr(F64_numtype, ?(), x, ao)
  ;; test.spectec:7882.5-7882.67
  prod{x : idx, ao : memarg} {{"i32.store8"} {x:Tmemidx_(I)} {ao:Tmemarg_(1)}} => STORE_instr(I32_numtype, ?(`%`_storeop_(`%`_sz(8))), x, ao)
  ;; test.spectec:7883.5-7883.69
  prod{x : idx, ao : memarg} {{"i32.store16"} {x:Tmemidx_(I)} {ao:Tmemarg_(2)}} => STORE_instr(I32_numtype, ?(`%`_storeop_(`%`_sz(16))), x, ao)
  ;; test.spectec:7884.5-7884.67
  prod{x : idx, ao : memarg} {{"i64.store8"} {x:Tmemidx_(I)} {ao:Tmemarg_(1)}} => STORE_instr(I64_numtype, ?(`%`_storeop_(`%`_sz(8))), x, ao)
  ;; test.spectec:7885.5-7885.69
  prod{x : idx, ao : memarg} {{"i64.store16"} {x:Tmemidx_(I)} {ao:Tmemarg_(2)}} => STORE_instr(I64_numtype, ?(`%`_storeop_(`%`_sz(16))), x, ao)
  ;; test.spectec:7886.5-7886.69
  prod{x : idx, ao : memarg} {{"i64.store32"} {x:Tmemidx_(I)} {ao:Tmemarg_(4)}} => STORE_instr(I64_numtype, ?(`%`_storeop_(`%`_sz(32))), x, ao)
  ;; test.spectec:7887.5-7887.67
  prod{x : idx, ao : memarg} {{"v128.store"} {x:Tmemidx_(I)} {ao:Tmemarg_(16)}} => VSTORE_instr(V128_vectype, x, ao)
  ;; test.spectec:7888.5-7888.93
  prod{x : idx, ao : memarg, i : laneidx} {{"v128.store8_lane"} {x:Tmemidx_(I)} {ao:Tmemarg_(1)} {i:Tlaneidx}} => VSTORE_LANE_instr(V128_vectype, `%`_sz(8), x, ao, i)
  ;; test.spectec:7889.5-7889.95
  prod{x : idx, ao : memarg, i : laneidx} {{"v128.store16_lane"} {x:Tmemidx_(I)} {ao:Tmemarg_(2)} {i:Tlaneidx}} => VSTORE_LANE_instr(V128_vectype, `%`_sz(16), x, ao, i)
  ;; test.spectec:7890.5-7890.95
  prod{x : idx, ao : memarg, i : laneidx} {{"v128.store32_lane"} {x:Tmemidx_(I)} {ao:Tmemarg_(4)} {i:Tlaneidx}} => VSTORE_LANE_instr(V128_vectype, `%`_sz(32), x, ao, i)
  ;; test.spectec:7891.5-7891.95
  prod{x : idx, ao : memarg, i : laneidx} {{"v128.store64_lane"} {x:Tmemidx_(I)} {ao:Tmemarg_(8)} {i:Tlaneidx}} => VSTORE_LANE_instr(V128_vectype, `%`_sz(64), x, ao, i)
  ;; test.spectec:7892.5-7892.49
  prod{x : idx} {{"memory.size"} {x:Tmemidx_(I)}} => `MEMORY.SIZE`_instr(x)
  ;; test.spectec:7893.5-7893.49
  prod{x : idx} {{"memory.grow"} {x:Tmemidx_(I)}} => `MEMORY.GROW`_instr(x)
  ;; test.spectec:7894.5-7894.49
  prod{x : idx} {{"memory.fill"} {x:Tmemidx_(I)}} => `MEMORY.FILL`_instr(x)
  ;; test.spectec:7895.5-7895.73
  prod{x_1 : idx, x_2 : idx} {{"memory.copy"} {x_1:Tmemidx_(I)} {x_2:Tmemidx_(I)}} => `MEMORY.COPY`_instr(x_1, x_2)
  ;; test.spectec:7896.5-7896.66
  prod{x : idx, y : idx} {{"memory.init"} {x:Tmemidx_(I)} {y:Tdataidx_(I)}} => `MEMORY.INIT`_instr(x, y)
  ;; test.spectec:7953.5-7953.46
  prod{x : idx} {{"data.drop"} {x:Tdataidx_(I)}} => `DATA.DROP`_instr(x)
  ;; test.spectec:7960.5-7960.47
  prod{ht : heaptype} {{"ref.null"} {ht:Theaptype_(I)}} => `REF.NULL`_instr(ht)
  ;; test.spectec:7961.5-7961.44
  prod{x : idx} {{"ref.func"} {x:Tfuncidx_(I)}} => `REF.FUNC`_instr(x)
  ;; test.spectec:7962.5-7962.33
  prod "ref.is_null" => `REF.IS_NULL`_instr
  ;; test.spectec:7963.5-7963.41
  prod "ref.as_non_null" => `REF.AS_NON_NULL`_instr
  ;; test.spectec:7964.5-7964.23
  prod "ref.eq" => `REF.EQ`_instr
  ;; test.spectec:7965.5-7965.46
  prod{rt : reftype} {{"ref.test"} {rt:Treftype_(I)}} => `REF.TEST`_instr(rt)
  ;; test.spectec:7966.5-7966.46
  prod{rt : reftype} {{"ref.cast"} {rt:Treftype_(I)}} => `REF.CAST`_instr(rt)
  ;; test.spectec:7970.5-7970.25
  prod "ref.i31" => `REF.I31`_instr
  ;; test.spectec:7971.5-7971.29
  prod "i31.get_s" => `I31.GET`_instr(S_sx)
  ;; test.spectec:7972.5-7972.29
  prod "i31.get_u" => `I31.GET`_instr(U_sx)
  ;; test.spectec:7976.5-7976.48
  prod{x : idx} {{"struct.new"} {x:Ttypeidx_(I)}} => `STRUCT.NEW`_instr(x)
  ;; test.spectec:7977.5-7977.64
  prod{x : idx} {{"struct.new_default"} {x:Ttypeidx_(I)}} => `STRUCT.NEW_DEFAULT`_instr(x)
  ;; test.spectec:7978.5-7978.69
  prod{x : idx, i : fieldidx} {{"struct.get"} {x:Ttypeidx_(I)} {i:Tfieldidx__(I, x)}} => `STRUCT.GET`_instr(?(), x, i)
  ;; test.spectec:7979.5-7979.73
  prod{x : idx, i : fieldidx} {{"struct.get_s"} {x:Ttypeidx_(I)} {i:Tfieldidx__(I, x)}} => `STRUCT.GET`_instr(?(S_sx), x, i)
  ;; test.spectec:7980.5-7980.73
  prod{x : idx, i : fieldidx} {{"struct.get_u"} {x:Ttypeidx_(I)} {i:Tfieldidx__(I, x)}} => `STRUCT.GET`_instr(?(U_sx), x, i)
  ;; test.spectec:7981.5-7981.69
  prod{x : idx, i : fieldidx} {{"struct.set"} {x:Ttypeidx_(I)} {i:Tfieldidx__(I, x)}} => `STRUCT.SET`_instr(x, i)
  ;; test.spectec:7985.5-7985.46
  prod{x : idx} {{"array.new"} {x:Ttypeidx_(I)}} => `ARRAY.NEW`_instr(x)
  ;; test.spectec:7986.5-7986.62
  prod{x : idx} {{"array.new_default"} {x:Ttypeidx_(I)}} => `ARRAY.NEW_DEFAULT`_instr(x)
  ;; test.spectec:7987.5-7987.67
  prod{x : idx, n : n} {{"array.new_fixed"} {x:Ttypeidx_(I)} {`%`_u32(n):Tu32}} => `ARRAY.NEW_FIXED`_instr(x, `%`_u32(n))
  ;; test.spectec:7988.5-7988.73
  prod{x : idx, y : idx} {{"array.new_data"} {x:Ttypeidx_(I)} {y:Tdataidx_(I)}} => `ARRAY.NEW_DATA`_instr(x, y)
  ;; test.spectec:7989.5-7989.73
  prod{x : idx, y : idx} {{"array.new_elem"} {x:Ttypeidx_(I)} {y:Telemidx_(I)}} => `ARRAY.NEW_ELEM`_instr(x, y)
  ;; test.spectec:7990.5-7990.46
  prod{x : idx} {{"array.get"} {x:Ttypeidx_(I)}} => `ARRAY.GET`_instr(?(), x)
  ;; test.spectec:7991.5-7991.50
  prod{x : idx} {{"array.get_s"} {x:Ttypeidx_(I)}} => `ARRAY.GET`_instr(?(S_sx), x)
  ;; test.spectec:7992.5-7992.50
  prod{x : idx} {{"array.get_u"} {x:Ttypeidx_(I)}} => `ARRAY.GET`_instr(?(U_sx), x)
  ;; test.spectec:7993.5-7993.46
  prod{x : idx} {{"array.set"} {x:Ttypeidx_(I)}} => `ARRAY.SET`_instr(x)
  ;; test.spectec:7994.5-7994.29
  prod "array.len" => `ARRAY.LEN`_instr
  ;; test.spectec:7995.5-7995.48
  prod{x : idx} {{"array.fill"} {x:Ttypeidx_(I)}} => `ARRAY.FILL`_instr(x)
  ;; test.spectec:7996.5-7996.73
  prod{x_1 : idx, x_2 : idx} {{"array.copy"} {x_1:Ttypeidx_(I)} {x_2:Ttypeidx_(I)}} => `ARRAY.COPY`_instr(x_1, x_2)
  ;; test.spectec:7997.5-7997.75
  prod{x : idx, y : idx} {{"array.init_data"} {x:Ttypeidx_(I)} {y:Tdataidx_(I)}} => `ARRAY.INIT_DATA`_instr(x, y)
  ;; test.spectec:7998.5-7998.75
  prod{x : idx, y : idx} {{"array.init_elem"} {x:Ttypeidx_(I)} {y:Telemidx_(I)}} => `ARRAY.INIT_ELEM`_instr(x, y)
  ;; test.spectec:8002.5-8002.47
  prod "any.convert_extern" => `ANY.CONVERT_EXTERN`_instr
  ;; test.spectec:8003.5-8003.47
  prod "extern.convert_any" => `EXTERN.CONVERT_ANY`_instr
  ;; test.spectec:8010.5-8010.38
  prod{c : u32} {{"i32.const"} {c:Ti32}} => CONST_instr(I32_numtype, c)
  ;; test.spectec:8011.5-8011.38
  prod{c : u64} {{"i64.const"} {c:Ti64}} => CONST_instr(I64_numtype, c)
  ;; test.spectec:8012.5-8012.38
  prod{c : f32} {{"f32.const"} {c:Tf32}} => CONST_instr(F32_numtype, c)
  ;; test.spectec:8013.5-8013.38
  prod{c : f64} {{"f64.const"} {c:Tf64}} => CONST_instr(F64_numtype, c)
  ;; test.spectec:8017.5-8017.32
  prod "i32.eqz" => TESTOP_instr(I32_numtype, EQZ_testop_)
  ;; test.spectec:8021.5-8021.32
  prod "i64.eqz" => TESTOP_instr(I64_numtype, EQZ_testop_)
  ;; test.spectec:8025.5-8025.29
  prod "i32.eq" => RELOP_instr(I32_numtype, EQ_relop_)
  ;; test.spectec:8026.5-8026.29
  prod "i32.ne" => RELOP_instr(I32_numtype, NE_relop_)
  ;; test.spectec:8027.5-8027.33
  prod "i32.lt_s" => RELOP_instr(I32_numtype, LT_relop_(S_sx))
  ;; test.spectec:8028.5-8028.33
  prod "i32.lt_u" => RELOP_instr(I32_numtype, LT_relop_(U_sx))
  ;; test.spectec:8029.5-8029.33
  prod "i32.gt_s" => RELOP_instr(I32_numtype, GT_relop_(S_sx))
  ;; test.spectec:8030.5-8030.33
  prod "i32.gt_u" => RELOP_instr(I32_numtype, GT_relop_(U_sx))
  ;; test.spectec:8031.5-8031.33
  prod "i32.le_s" => RELOP_instr(I32_numtype, LE_relop_(S_sx))
  ;; test.spectec:8032.5-8032.33
  prod "i32.le_u" => RELOP_instr(I32_numtype, LE_relop_(U_sx))
  ;; test.spectec:8033.5-8033.33
  prod "i32.ge_s" => RELOP_instr(I32_numtype, GE_relop_(S_sx))
  ;; test.spectec:8034.5-8034.33
  prod "i32.ge_u" => RELOP_instr(I32_numtype, GE_relop_(U_sx))
  ;; test.spectec:8038.5-8038.29
  prod "i64.eq" => RELOP_instr(I64_numtype, EQ_relop_)
  ;; test.spectec:8039.5-8039.29
  prod "i64.ne" => RELOP_instr(I64_numtype, NE_relop_)
  ;; test.spectec:8040.5-8040.33
  prod "i64.lt_s" => RELOP_instr(I64_numtype, LT_relop_(S_sx))
  ;; test.spectec:8041.5-8041.33
  prod "i64.lt_u" => RELOP_instr(I64_numtype, LT_relop_(U_sx))
  ;; test.spectec:8042.5-8042.33
  prod "i64.gt_s" => RELOP_instr(I64_numtype, GT_relop_(S_sx))
  ;; test.spectec:8043.5-8043.33
  prod "i64.gt_u" => RELOP_instr(I64_numtype, GT_relop_(U_sx))
  ;; test.spectec:8044.5-8044.33
  prod "i64.le_s" => RELOP_instr(I64_numtype, LE_relop_(S_sx))
  ;; test.spectec:8045.5-8045.33
  prod "i64.le_u" => RELOP_instr(I64_numtype, LE_relop_(U_sx))
  ;; test.spectec:8046.5-8046.33
  prod "i64.ge_s" => RELOP_instr(I64_numtype, GE_relop_(S_sx))
  ;; test.spectec:8047.5-8047.33
  prod "i64.ge_u" => RELOP_instr(I64_numtype, GE_relop_(U_sx))
  ;; test.spectec:8051.5-8051.29
  prod "f32.eq" => RELOP_instr(F32_numtype, EQ_relop_)
  ;; test.spectec:8052.5-8052.29
  prod "f32.ne" => RELOP_instr(F32_numtype, NE_relop_)
  ;; test.spectec:8053.5-8053.29
  prod "f32.lt" => RELOP_instr(F32_numtype, LT_relop_)
  ;; test.spectec:8054.5-8054.29
  prod "f32.gt" => RELOP_instr(F32_numtype, GT_relop_)
  ;; test.spectec:8055.5-8055.29
  prod "f32.le" => RELOP_instr(F32_numtype, LE_relop_)
  ;; test.spectec:8056.5-8056.29
  prod "f32.ge" => RELOP_instr(F32_numtype, GE_relop_)
  ;; test.spectec:8060.5-8060.29
  prod "f64.eq" => RELOP_instr(F64_numtype, EQ_relop_)
  ;; test.spectec:8061.5-8061.29
  prod "f64.ne" => RELOP_instr(F64_numtype, NE_relop_)
  ;; test.spectec:8062.5-8062.29
  prod "f64.lt" => RELOP_instr(F64_numtype, LT_relop_)
  ;; test.spectec:8063.5-8063.29
  prod "f64.gt" => RELOP_instr(F64_numtype, GT_relop_)
  ;; test.spectec:8064.5-8064.29
  prod "f64.le" => RELOP_instr(F64_numtype, LE_relop_)
  ;; test.spectec:8065.5-8065.29
  prod "f64.ge" => RELOP_instr(F64_numtype, GE_relop_)
  ;; test.spectec:8069.5-8069.30
  prod "i32.clz" => UNOP_instr(I32_numtype, CLZ_unop_)
  ;; test.spectec:8070.5-8070.30
  prod "i32.ctz" => UNOP_instr(I32_numtype, CTZ_unop_)
  ;; test.spectec:8071.5-8071.36
  prod "i32.popcnt" => UNOP_instr(I32_numtype, POPCNT_unop_)
  ;; test.spectec:8072.5-8072.42
  prod "i32.extend8_s" => UNOP_instr(I32_numtype, EXTEND_unop_(`%`_sz(8)))
  ;; test.spectec:8073.5-8073.44
  prod "i32.extend16_s" => UNOP_instr(I32_numtype, EXTEND_unop_(`%`_sz(16)))
  ;; test.spectec:8077.5-8077.30
  prod "i64.clz" => UNOP_instr(I64_numtype, CLZ_unop_)
  ;; test.spectec:8078.5-8078.30
  prod "i64.ctz" => UNOP_instr(I64_numtype, CTZ_unop_)
  ;; test.spectec:8079.5-8079.36
  prod "i64.popcnt" => UNOP_instr(I64_numtype, POPCNT_unop_)
  ;; test.spectec:8080.5-8080.42
  prod "i64.extend8_s" => UNOP_instr(I64_numtype, EXTEND_unop_(`%`_sz(8)))
  ;; test.spectec:8081.5-8081.44
  prod "i64.extend16_s" => UNOP_instr(I64_numtype, EXTEND_unop_(`%`_sz(16)))
  ;; test.spectec:8082.5-8082.44
  prod "i64.extend32_s" => UNOP_instr(I64_numtype, EXTEND_unop_(`%`_sz(32)))
  ;; test.spectec:8086.5-8086.30
  prod "f32.abs" => UNOP_instr(F32_numtype, ABS_unop_)
  ;; test.spectec:8087.5-8087.30
  prod "f32.neg" => UNOP_instr(F32_numtype, NEG_unop_)
  ;; test.spectec:8088.5-8088.32
  prod "f32.sqrt" => UNOP_instr(F32_numtype, SQRT_unop_)
  ;; test.spectec:8089.5-8089.32
  prod "f32.ceil" => UNOP_instr(F32_numtype, CEIL_unop_)
  ;; test.spectec:8090.5-8090.34
  prod "f32.floor" => UNOP_instr(F32_numtype, FLOOR_unop_)
  ;; test.spectec:8091.5-8091.34
  prod "f32.trunc" => UNOP_instr(F32_numtype, TRUNC_unop_)
  ;; test.spectec:8092.5-8092.38
  prod "f32.nearest" => UNOP_instr(F32_numtype, NEAREST_unop_)
  ;; test.spectec:8096.5-8096.30
  prod "f64.abs" => UNOP_instr(F64_numtype, ABS_unop_)
  ;; test.spectec:8097.5-8097.30
  prod "f64.neg" => UNOP_instr(F64_numtype, NEG_unop_)
  ;; test.spectec:8098.5-8098.32
  prod "f64.sqrt" => UNOP_instr(F64_numtype, SQRT_unop_)
  ;; test.spectec:8099.5-8099.32
  prod "f64.ceil" => UNOP_instr(F64_numtype, CEIL_unop_)
  ;; test.spectec:8100.5-8100.34
  prod "f64.floor" => UNOP_instr(F64_numtype, FLOOR_unop_)
  ;; test.spectec:8101.5-8101.34
  prod "f64.trunc" => UNOP_instr(F64_numtype, TRUNC_unop_)
  ;; test.spectec:8102.5-8102.38
  prod "f64.nearest" => UNOP_instr(F64_numtype, NEAREST_unop_)
  ;; test.spectec:8106.5-8106.31
  prod "i32.add" => BINOP_instr(I32_numtype, ADD_binop_)
  ;; test.spectec:8107.5-8107.31
  prod "i32.sub" => BINOP_instr(I32_numtype, SUB_binop_)
  ;; test.spectec:8108.5-8108.31
  prod "i32.mul" => BINOP_instr(I32_numtype, MUL_binop_)
  ;; test.spectec:8109.5-8109.35
  prod "i32.div_s" => BINOP_instr(I32_numtype, DIV_binop_(S_sx))
  ;; test.spectec:8110.5-8110.35
  prod "i32.div_u" => BINOP_instr(I32_numtype, DIV_binop_(U_sx))
  ;; test.spectec:8111.5-8111.35
  prod "i32.rem_s" => BINOP_instr(I32_numtype, REM_binop_(S_sx))
  ;; test.spectec:8112.5-8112.35
  prod "i32.rem_u" => BINOP_instr(I32_numtype, REM_binop_(U_sx))
  ;; test.spectec:8113.5-8113.31
  prod "i32.and" => BINOP_instr(I32_numtype, AND_binop_)
  ;; test.spectec:8114.5-8114.29
  prod "i32.or" => BINOP_instr(I32_numtype, OR_binop_)
  ;; test.spectec:8115.5-8115.31
  prod "i32.xor" => BINOP_instr(I32_numtype, XOR_binop_)
  ;; test.spectec:8116.5-8116.31
  prod "i32.shl" => BINOP_instr(I32_numtype, SHL_binop_)
  ;; test.spectec:8117.5-8117.35
  prod "i32.shr_s" => BINOP_instr(I32_numtype, SHR_binop_(S_sx))
  ;; test.spectec:8118.5-8118.35
  prod "i32.shr_u" => BINOP_instr(I32_numtype, SHR_binop_(U_sx))
  ;; test.spectec:8119.5-8119.33
  prod "i32.rotl" => BINOP_instr(I32_numtype, ROTL_binop_)
  ;; test.spectec:8120.5-8120.33
  prod "i32.rotr" => BINOP_instr(I32_numtype, ROTR_binop_)
  ;; test.spectec:8124.5-8124.31
  prod "i64.add" => BINOP_instr(I64_numtype, ADD_binop_)
  ;; test.spectec:8125.5-8125.31
  prod "i64.sub" => BINOP_instr(I64_numtype, SUB_binop_)
  ;; test.spectec:8126.5-8126.31
  prod "i64.mul" => BINOP_instr(I64_numtype, MUL_binop_)
  ;; test.spectec:8127.5-8127.35
  prod "i64.div_s" => BINOP_instr(I64_numtype, DIV_binop_(S_sx))
  ;; test.spectec:8128.5-8128.35
  prod "i64.div_u" => BINOP_instr(I64_numtype, DIV_binop_(U_sx))
  ;; test.spectec:8129.5-8129.35
  prod "i64.rem_s" => BINOP_instr(I64_numtype, REM_binop_(S_sx))
  ;; test.spectec:8130.5-8130.35
  prod "i64.rem_u" => BINOP_instr(I64_numtype, REM_binop_(U_sx))
  ;; test.spectec:8131.5-8131.31
  prod "i64.and" => BINOP_instr(I64_numtype, AND_binop_)
  ;; test.spectec:8132.5-8132.29
  prod "i64.or" => BINOP_instr(I64_numtype, OR_binop_)
  ;; test.spectec:8133.5-8133.31
  prod "i64.xor" => BINOP_instr(I64_numtype, XOR_binop_)
  ;; test.spectec:8134.5-8134.31
  prod "i64.shl" => BINOP_instr(I64_numtype, SHL_binop_)
  ;; test.spectec:8135.5-8135.35
  prod "i64.shr_s" => BINOP_instr(I64_numtype, SHR_binop_(S_sx))
  ;; test.spectec:8136.5-8136.35
  prod "i64.shr_u" => BINOP_instr(I64_numtype, SHR_binop_(U_sx))
  ;; test.spectec:8137.5-8137.33
  prod "i64.rotl" => BINOP_instr(I64_numtype, ROTL_binop_)
  ;; test.spectec:8138.5-8138.33
  prod "i64.rotr" => BINOP_instr(I64_numtype, ROTR_binop_)
  ;; test.spectec:8142.5-8142.31
  prod "f32.add" => BINOP_instr(F32_numtype, ADD_binop_)
  ;; test.spectec:8143.5-8143.31
  prod "f32.sub" => BINOP_instr(F32_numtype, SUB_binop_)
  ;; test.spectec:8144.5-8144.31
  prod "f32.mul" => BINOP_instr(F32_numtype, MUL_binop_)
  ;; test.spectec:8145.5-8145.31
  prod "f32.div" => BINOP_instr(F32_numtype, DIV_binop_)
  ;; test.spectec:8146.5-8146.31
  prod "f32.min" => BINOP_instr(F32_numtype, MIN_binop_)
  ;; test.spectec:8147.5-8147.31
  prod "f32.max" => BINOP_instr(F32_numtype, MAX_binop_)
  ;; test.spectec:8148.5-8148.41
  prod "f32.copysign" => BINOP_instr(F32_numtype, COPYSIGN_binop_)
  ;; test.spectec:8152.5-8152.31
  prod "f64.add" => BINOP_instr(F64_numtype, ADD_binop_)
  ;; test.spectec:8153.5-8153.31
  prod "f64.sub" => BINOP_instr(F64_numtype, SUB_binop_)
  ;; test.spectec:8154.5-8154.31
  prod "f64.mul" => BINOP_instr(F64_numtype, MUL_binop_)
  ;; test.spectec:8155.5-8155.31
  prod "f64.div" => BINOP_instr(F64_numtype, DIV_binop_)
  ;; test.spectec:8156.5-8156.31
  prod "f64.min" => BINOP_instr(F64_numtype, MIN_binop_)
  ;; test.spectec:8157.5-8157.31
  prod "f64.max" => BINOP_instr(F64_numtype, MAX_binop_)
  ;; test.spectec:8158.5-8158.41
  prod "f64.copysign" => BINOP_instr(F64_numtype, COPYSIGN_binop_)
  ;; test.spectec:8162.5-8162.41
  prod "i32.wrap_i64" => CVTOP_instr(I32_numtype, I64_numtype, WRAP_cvtop__)
  ;; test.spectec:8163.5-8163.47
  prod "i32.trunc_f32_s" => CVTOP_instr(I32_numtype, F32_numtype, TRUNC_cvtop__(S_sx))
  ;; test.spectec:8164.5-8164.47
  prod "i32.trunc_f32_u" => CVTOP_instr(I32_numtype, F32_numtype, TRUNC_cvtop__(U_sx))
  ;; test.spectec:8165.5-8165.47
  prod "i32.trunc_f64_s" => CVTOP_instr(I32_numtype, F64_numtype, TRUNC_cvtop__(S_sx))
  ;; test.spectec:8166.5-8166.47
  prod "i32.trunc_f64_u" => CVTOP_instr(I32_numtype, F64_numtype, TRUNC_cvtop__(U_sx))
  ;; test.spectec:8167.5-8167.55
  prod "i32.trunc_sat_f32_s" => CVTOP_instr(I32_numtype, F32_numtype, TRUNC_SAT_cvtop__(S_sx))
  ;; test.spectec:8168.5-8168.55
  prod "i32.trunc_sat_f32_u" => CVTOP_instr(I32_numtype, F32_numtype, TRUNC_SAT_cvtop__(U_sx))
  ;; test.spectec:8169.5-8169.55
  prod "i32.trunc_sat_f64_s" => CVTOP_instr(I32_numtype, F64_numtype, TRUNC_SAT_cvtop__(S_sx))
  ;; test.spectec:8170.5-8170.55
  prod "i32.trunc_sat_f64_u" => CVTOP_instr(I32_numtype, F64_numtype, TRUNC_SAT_cvtop__(U_sx))
  ;; test.spectec:8174.5-8174.49
  prod "i64.extend_i32_s" => CVTOP_instr(I64_numtype, I32_numtype, EXTEND_cvtop__(S_sx))
  ;; test.spectec:8175.5-8175.49
  prod "i64.extend_i32_u" => CVTOP_instr(I64_numtype, I32_numtype, EXTEND_cvtop__(U_sx))
  ;; test.spectec:8176.5-8176.47
  prod "i64.trunc_f32_s" => CVTOP_instr(I64_numtype, F32_numtype, TRUNC_cvtop__(S_sx))
  ;; test.spectec:8177.5-8177.47
  prod "i64.trunc_f32_u" => CVTOP_instr(I64_numtype, F32_numtype, TRUNC_cvtop__(U_sx))
  ;; test.spectec:8178.5-8178.47
  prod "i64.trunc_f64_s" => CVTOP_instr(I64_numtype, F64_numtype, TRUNC_cvtop__(S_sx))
  ;; test.spectec:8179.5-8179.47
  prod "i64.trunc_f64_u" => CVTOP_instr(I64_numtype, F64_numtype, TRUNC_cvtop__(U_sx))
  ;; test.spectec:8180.5-8180.55
  prod "i64.trunc_sat_f32_s" => CVTOP_instr(I64_numtype, F32_numtype, TRUNC_SAT_cvtop__(S_sx))
  ;; test.spectec:8181.5-8181.55
  prod "i64.trunc_sat_f32_u" => CVTOP_instr(I64_numtype, F32_numtype, TRUNC_SAT_cvtop__(U_sx))
  ;; test.spectec:8182.5-8182.55
  prod "i64.trunc_sat_f64_s" => CVTOP_instr(I64_numtype, F64_numtype, TRUNC_SAT_cvtop__(S_sx))
  ;; test.spectec:8183.5-8183.55
  prod "i64.trunc_sat_f64_u" => CVTOP_instr(I64_numtype, F64_numtype, TRUNC_SAT_cvtop__(U_sx))
  ;; test.spectec:8187.5-8187.45
  prod "f32.demote_f64" => CVTOP_instr(F32_numtype, F64_numtype, DEMOTE_cvtop__)
  ;; test.spectec:8188.5-8188.51
  prod "f32.convert_i32_s" => CVTOP_instr(F32_numtype, I32_numtype, CONVERT_cvtop__(S_sx))
  ;; test.spectec:8189.5-8189.51
  prod "f32.convert_i32_u" => CVTOP_instr(F32_numtype, I32_numtype, CONVERT_cvtop__(U_sx))
  ;; test.spectec:8190.5-8190.51
  prod "f32.convert_i64_s" => CVTOP_instr(F32_numtype, I64_numtype, CONVERT_cvtop__(S_sx))
  ;; test.spectec:8191.5-8191.51
  prod "f32.convert_i64_u" => CVTOP_instr(F32_numtype, I64_numtype, CONVERT_cvtop__(U_sx))
  ;; test.spectec:8195.5-8195.47
  prod "f64.promote_f32" => CVTOP_instr(F64_numtype, F32_numtype, PROMOTE_cvtop__)
  ;; test.spectec:8196.5-8196.51
  prod "f64.convert_i32_s" => CVTOP_instr(F64_numtype, I32_numtype, CONVERT_cvtop__(S_sx))
  ;; test.spectec:8197.5-8197.51
  prod "f64.convert_i32_u" => CVTOP_instr(F64_numtype, I32_numtype, CONVERT_cvtop__(U_sx))
  ;; test.spectec:8198.5-8198.51
  prod "f64.convert_i64_s" => CVTOP_instr(F64_numtype, I64_numtype, CONVERT_cvtop__(S_sx))
  ;; test.spectec:8199.5-8199.51
  prod "f64.convert_i64_u" => CVTOP_instr(F64_numtype, I64_numtype, CONVERT_cvtop__(U_sx))
  ;; test.spectec:8203.5-8203.55
  prod "i32.reinterpret_f32" => CVTOP_instr(I32_numtype, F32_numtype, REINTERPRET_cvtop__)
  ;; test.spectec:8204.5-8204.55
  prod "i64.reinterpret_f64" => CVTOP_instr(I64_numtype, F64_numtype, REINTERPRET_cvtop__)
  ;; test.spectec:8205.5-8205.55
  prod "f32.reinterpret_i32" => CVTOP_instr(F32_numtype, I32_numtype, REINTERPRET_cvtop__)
  ;; test.spectec:8206.5-8206.55
  prod "f64.reinterpret_i64" => CVTOP_instr(F64_numtype, I64_numtype, REINTERPRET_cvtop__)
  ;; test.spectec:8213.5-8213.101
  prod{`c*` : u8*} {{"v128.const"} {"i8x16"} {c*{c <- `c*`}:Ti8^16{}}} => VCONST_instr(V128_vectype, $inv_ibytes_(128, $concat_(syntax byte, $ibytes_(8, c)*{c <- `c*`})))
  ;; test.spectec:8214.5-8214.102
  prod{`c*` : u16*} {{"v128.const"} {"i16x8"} {c*{c <- `c*`}:Ti16^8{}}} => VCONST_instr(V128_vectype, $inv_ibytes_(128, $concat_(syntax byte, $ibytes_(16, c)*{c <- `c*`})))
  ;; test.spectec:8215.5-8215.102
  prod{`c*` : u32*} {{"v128.const"} {"i32x4"} {c*{c <- `c*`}:Ti32^4{}}} => VCONST_instr(V128_vectype, $inv_ibytes_(128, $concat_(syntax byte, $ibytes_(32, c)*{c <- `c*`})))
  ;; test.spectec:8216.5-8216.102
  prod{`c*` : u64*} {{"v128.const"} {"i64x2"} {c*{c <- `c*`}:Ti64^2{}}} => VCONST_instr(V128_vectype, $inv_ibytes_(128, $concat_(syntax byte, $ibytes_(64, c)*{c <- `c*`})))
  ;; test.spectec:8217.5-8217.102
  prod{`c*` : f32*} {{"v128.const"} {"f32x4"} {c*{c <- `c*`}:Tf32^4{}}} => VCONST_instr(V128_vectype, $inv_ibytes_(128, $concat_(syntax byte, $fbytes_(32, c)*{c <- `c*`})))
  ;; test.spectec:8218.5-8218.102
  prod{`c*` : f64*} {{"v128.const"} {"f64x2"} {c*{c <- `c*`}:Tf64^2{}}} => VCONST_instr(V128_vectype, $inv_ibytes_(128, $concat_(syntax byte, $fbytes_(64, c)*{c <- `c*`})))
  ;; test.spectec:8222.5-8222.61
  prod{`i*` : laneidx*} {{"i8x16.shuffle"} {i*{i <- `i*`}:Tlaneidx^16{}}} => VSHUFFLE_instr(`%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(16))), i*{i <- `i*`})
  ;; test.spectec:8223.5-8223.52
  prod "i8x16.swizzle" => VSWIZZLOP_instr(`%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(16))), SWIZZLE_vswizzlop_)
  ;; test.spectec:8224.5-8224.68
  prod "i8x16.relaxed_swizzle" => VSWIZZLOP_instr(`%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(16))), RELAXED_SWIZZLE_vswizzlop_)
  ;; test.spectec:8228.5-8228.39
  prod "i8x16.splat" => VSPLAT_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)))
  ;; test.spectec:8229.5-8229.39
  prod "i16x8.splat" => VSPLAT_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)))
  ;; test.spectec:8230.5-8230.39
  prod "i32x4.splat" => VSPLAT_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)))
  ;; test.spectec:8231.5-8231.39
  prod "i64x2.splat" => VSPLAT_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)))
  ;; test.spectec:8232.5-8232.39
  prod "f32x4.splat" => VSPLAT_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)))
  ;; test.spectec:8233.5-8233.39
  prod "f64x2.splat" => VSPLAT_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)))
  ;; test.spectec:8237.5-8237.70
  prod{i : laneidx} {{"i8x16.extract_lane_s"} {i:Tlaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ?(S_sx), i)
  ;; test.spectec:8238.5-8238.70
  prod{i : laneidx} {{"i8x16.extract_lane_u"} {i:Tlaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ?(U_sx), i)
  ;; test.spectec:8239.5-8239.70
  prod{i : laneidx} {{"i16x8.extract_lane_s"} {i:Tlaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ?(S_sx), i)
  ;; test.spectec:8240.5-8240.70
  prod{i : laneidx} {{"i16x8.extract_lane_u"} {i:Tlaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ?(U_sx), i)
  ;; test.spectec:8241.5-8241.66
  prod{i : laneidx} {{"i32x4.extract_lane"} {i:Tlaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), ?(), i)
  ;; test.spectec:8242.5-8242.66
  prod{i : laneidx} {{"i64x2.extract_lane"} {i:Tlaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), ?(), i)
  ;; test.spectec:8243.5-8243.66
  prod{i : laneidx} {{"f32x4.extract_lane"} {i:Tlaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), ?(), i)
  ;; test.spectec:8244.5-8244.66
  prod{i : laneidx} {{"f64x2.extract_lane"} {i:Tlaneidx}} => VEXTRACT_LANE_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), ?(), i)
  ;; test.spectec:8245.5-8245.66
  prod{i : laneidx} {{"i8x16.replace_lane"} {i:Tlaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), i)
  ;; test.spectec:8246.5-8246.66
  prod{i : laneidx} {{"i16x8.replace_lane"} {i:Tlaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), i)
  ;; test.spectec:8247.5-8247.66
  prod{i : laneidx} {{"i32x4.replace_lane"} {i:Tlaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), i)
  ;; test.spectec:8248.5-8248.66
  prod{i : laneidx} {{"i64x2.replace_lane"} {i:Tlaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), i)
  ;; test.spectec:8249.5-8249.66
  prod{i : laneidx} {{"f32x4.replace_lane"} {i:Tlaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), i)
  ;; test.spectec:8250.5-8250.66
  prod{i : laneidx} {{"f64x2.replace_lane"} {i:Tlaneidx}} => VREPLACE_LANE_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), i)
  ;; test.spectec:8254.5-8254.46
  prod "v128.any_true" => VVTESTOP_instr(V128_vectype, ANY_TRUE_vvtestop)
  ;; test.spectec:8258.5-8258.52
  prod "i8x16.all_true" => VTESTOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ALL_TRUE_vtestop_)
  ;; test.spectec:8262.5-8262.52
  prod "i16x8.all_true" => VTESTOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ALL_TRUE_vtestop_)
  ;; test.spectec:8266.5-8266.52
  prod "i32x4.all_true" => VTESTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), ALL_TRUE_vtestop_)
  ;; test.spectec:8270.5-8270.52
  prod "i64x2.all_true" => VTESTOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), ALL_TRUE_vtestop_)
  ;; test.spectec:8274.5-8274.39
  prod "i8x16.eq" => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), EQ_vrelop_)
  ;; test.spectec:8275.5-8275.39
  prod "i8x16.ne" => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), NE_vrelop_)
  ;; test.spectec:8276.5-8276.43
  prod "i8x16.lt_s" => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), LT_vrelop_(S_sx))
  ;; test.spectec:8277.5-8277.43
  prod "i8x16.lt_u" => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), LT_vrelop_(U_sx))
  ;; test.spectec:8278.5-8278.43
  prod "i8x16.gt_s" => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), GT_vrelop_(S_sx))
  ;; test.spectec:8279.5-8279.43
  prod "i8x16.gt_u" => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), GT_vrelop_(U_sx))
  ;; test.spectec:8280.5-8280.43
  prod "i8x16.le_s" => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), LE_vrelop_(S_sx))
  ;; test.spectec:8281.5-8281.43
  prod "i8x16.le_u" => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), LE_vrelop_(U_sx))
  ;; test.spectec:8282.5-8282.43
  prod "i8x16.ge_s" => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), GE_vrelop_(S_sx))
  ;; test.spectec:8283.5-8283.43
  prod "i8x16.ge_u" => VRELOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), GE_vrelop_(U_sx))
  ;; test.spectec:8287.5-8287.39
  prod "i16x8.eq" => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), EQ_vrelop_)
  ;; test.spectec:8288.5-8288.39
  prod "i16x8.ne" => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), NE_vrelop_)
  ;; test.spectec:8289.5-8289.43
  prod "i16x8.lt_s" => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), LT_vrelop_(S_sx))
  ;; test.spectec:8290.5-8290.43
  prod "i16x8.lt_u" => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), LT_vrelop_(U_sx))
  ;; test.spectec:8291.5-8291.43
  prod "i16x8.gt_s" => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), GT_vrelop_(S_sx))
  ;; test.spectec:8292.5-8292.43
  prod "i16x8.gt_u" => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), GT_vrelop_(U_sx))
  ;; test.spectec:8293.5-8293.43
  prod "i16x8.le_s" => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), LE_vrelop_(S_sx))
  ;; test.spectec:8294.5-8294.43
  prod "i16x8.le_u" => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), LE_vrelop_(U_sx))
  ;; test.spectec:8295.5-8295.43
  prod "i16x8.ge_s" => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), GE_vrelop_(S_sx))
  ;; test.spectec:8296.5-8296.43
  prod "i16x8.ge_u" => VRELOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), GE_vrelop_(U_sx))
  ;; test.spectec:8300.5-8300.39
  prod "i32x4.eq" => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), EQ_vrelop_)
  ;; test.spectec:8301.5-8301.39
  prod "i32x4.ne" => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), NE_vrelop_)
  ;; test.spectec:8302.5-8302.43
  prod "i32x4.lt_s" => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), LT_vrelop_(S_sx))
  ;; test.spectec:8303.5-8303.43
  prod "i32x4.lt_u" => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), LT_vrelop_(U_sx))
  ;; test.spectec:8304.5-8304.43
  prod "i32x4.gt_s" => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), GT_vrelop_(S_sx))
  ;; test.spectec:8305.5-8305.43
  prod "i32x4.gt_u" => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), GT_vrelop_(U_sx))
  ;; test.spectec:8306.5-8306.43
  prod "i32x4.le_s" => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), LE_vrelop_(S_sx))
  ;; test.spectec:8307.5-8307.43
  prod "i32x4.le_u" => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), LE_vrelop_(U_sx))
  ;; test.spectec:8308.5-8308.43
  prod "i32x4.ge_s" => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), GE_vrelop_(S_sx))
  ;; test.spectec:8309.5-8309.43
  prod "i32x4.ge_u" => VRELOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), GE_vrelop_(U_sx))
  ;; test.spectec:8313.5-8313.39
  prod "i64x2.eq" => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), EQ_vrelop_)
  ;; test.spectec:8314.5-8314.39
  prod "i64x2.ne" => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), NE_vrelop_)
  ;; test.spectec:8315.5-8315.43
  prod "i64x2.lt_s" => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), LT_vrelop_(S_sx))
  ;; test.spectec:8317.5-8317.43
  prod "i64x2.gt_s" => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), GT_vrelop_(S_sx))
  ;; test.spectec:8319.5-8319.43
  prod "i64x2.le_s" => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), LE_vrelop_(S_sx))
  ;; test.spectec:8321.5-8321.43
  prod "i64x2.ge_s" => VRELOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), GE_vrelop_(S_sx))
  ;; test.spectec:8326.5-8326.39
  prod "f32x4.eq" => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), EQ_vrelop_)
  ;; test.spectec:8327.5-8327.39
  prod "f32x4.ne" => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), NE_vrelop_)
  ;; test.spectec:8328.5-8328.39
  prod "f32x4.lt" => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), LT_vrelop_)
  ;; test.spectec:8329.5-8329.39
  prod "f32x4.gt" => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), GT_vrelop_)
  ;; test.spectec:8330.5-8330.39
  prod "f32x4.le" => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), LE_vrelop_)
  ;; test.spectec:8331.5-8331.39
  prod "f32x4.ge" => VRELOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), GE_vrelop_)
  ;; test.spectec:8335.5-8335.39
  prod "f64x2.eq" => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), EQ_vrelop_)
  ;; test.spectec:8336.5-8336.39
  prod "f64x2.ne" => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), NE_vrelop_)
  ;; test.spectec:8337.5-8337.39
  prod "f64x2.lt" => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), LT_vrelop_)
  ;; test.spectec:8338.5-8338.39
  prod "f64x2.gt" => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), GT_vrelop_)
  ;; test.spectec:8339.5-8339.39
  prod "f64x2.le" => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), LE_vrelop_)
  ;; test.spectec:8340.5-8340.39
  prod "f64x2.ge" => VRELOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), GE_vrelop_)
  ;; test.spectec:8344.5-8344.34
  prod "v128.not" => VVUNOP_instr(V128_vectype, NOT_vvunop)
  ;; test.spectec:8348.5-8348.40
  prod "i8x16.abs" => VUNOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ABS_vunop_)
  ;; test.spectec:8349.5-8349.40
  prod "i8x16.neg" => VUNOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), NEG_vunop_)
  ;; test.spectec:8350.5-8350.46
  prod "i8x16.popcnt" => VUNOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), POPCNT_vunop_)
  ;; test.spectec:8354.5-8354.40
  prod "i16x8.abs" => VUNOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ABS_vunop_)
  ;; test.spectec:8355.5-8355.40
  prod "i16x8.neg" => VUNOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), NEG_vunop_)
  ;; test.spectec:8360.5-8360.40
  prod "i32x4.abs" => VUNOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), ABS_vunop_)
  ;; test.spectec:8361.5-8361.40
  prod "i32x4.neg" => VUNOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), NEG_vunop_)
  ;; test.spectec:8366.5-8366.40
  prod "i64x2.abs" => VUNOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), ABS_vunop_)
  ;; test.spectec:8367.5-8367.40
  prod "i64x2.neg" => VUNOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), NEG_vunop_)
  ;; test.spectec:8372.5-8372.40
  prod "f32x4.abs" => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), ABS_vunop_)
  ;; test.spectec:8373.5-8373.40
  prod "f32x4.neg" => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), NEG_vunop_)
  ;; test.spectec:8374.5-8374.42
  prod "f32x4.sqrt" => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), SQRT_vunop_)
  ;; test.spectec:8375.5-8375.42
  prod "f32x4.ceil" => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), CEIL_vunop_)
  ;; test.spectec:8376.5-8376.44
  prod "f32x4.floor" => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), FLOOR_vunop_)
  ;; test.spectec:8377.5-8377.44
  prod "f32x4.trunc" => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), TRUNC_vunop_)
  ;; test.spectec:8378.5-8378.48
  prod "f32x4.nearest" => VUNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), NEAREST_vunop_)
  ;; test.spectec:8382.5-8382.40
  prod "f64x2.abs" => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), ABS_vunop_)
  ;; test.spectec:8383.5-8383.40
  prod "f64x2.neg" => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), NEG_vunop_)
  ;; test.spectec:8384.5-8384.42
  prod "f64x2.sqrt" => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), SQRT_vunop_)
  ;; test.spectec:8385.5-8385.42
  prod "f64x2.ceil" => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), CEIL_vunop_)
  ;; test.spectec:8386.5-8386.44
  prod "f64x2.floor" => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), FLOOR_vunop_)
  ;; test.spectec:8387.5-8387.44
  prod "f64x2.trunc" => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), TRUNC_vunop_)
  ;; test.spectec:8388.5-8388.48
  prod "f64x2.nearest" => VUNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), NEAREST_vunop_)
  ;; test.spectec:8392.5-8392.35
  prod "v128.and" => VVBINOP_instr(V128_vectype, AND_vvbinop)
  ;; test.spectec:8393.5-8393.41
  prod "v128.andnot" => VVBINOP_instr(V128_vectype, ANDNOT_vvbinop)
  ;; test.spectec:8394.5-8394.33
  prod "v128.or" => VVBINOP_instr(V128_vectype, OR_vvbinop)
  ;; test.spectec:8395.5-8395.35
  prod "v128.xor" => VVBINOP_instr(V128_vectype, XOR_vvbinop)
  ;; test.spectec:8399.5-8399.41
  prod "i8x16.add" => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ADD_vbinop_)
  ;; test.spectec:8400.5-8400.53
  prod "i8x16.add_sat_s" => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ADD_SAT_vbinop_(S_sx))
  ;; test.spectec:8401.5-8401.53
  prod "i8x16.add_sat_u" => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), ADD_SAT_vbinop_(U_sx))
  ;; test.spectec:8402.5-8402.41
  prod "i8x16.sub" => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), SUB_vbinop_)
  ;; test.spectec:8403.5-8403.53
  prod "i8x16.sub_sat_s" => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), SUB_SAT_vbinop_(S_sx))
  ;; test.spectec:8404.5-8404.53
  prod "i8x16.sub_sat_u" => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), SUB_SAT_vbinop_(U_sx))
  ;; test.spectec:8406.5-8406.45
  prod "i8x16.min_s" => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), MIN_vbinop_(S_sx))
  ;; test.spectec:8407.5-8407.45
  prod "i8x16.min_u" => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), MIN_vbinop_(U_sx))
  ;; test.spectec:8408.5-8408.45
  prod "i8x16.max_s" => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), MAX_vbinop_(S_sx))
  ;; test.spectec:8409.5-8409.45
  prod "i8x16.max_u" => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), MAX_vbinop_(U_sx))
  ;; test.spectec:8410.5-8410.47
  prod "i8x16.avgr_u" => VBINOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), AVGRU_vbinop_)
  ;; test.spectec:8414.5-8414.41
  prod "i16x8.add" => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ADD_vbinop_)
  ;; test.spectec:8415.5-8415.53
  prod "i16x8.add_sat_s" => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ADD_SAT_vbinop_(S_sx))
  ;; test.spectec:8416.5-8416.53
  prod "i16x8.add_sat_u" => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), ADD_SAT_vbinop_(U_sx))
  ;; test.spectec:8417.5-8417.41
  prod "i16x8.sub" => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), SUB_vbinop_)
  ;; test.spectec:8418.5-8418.53
  prod "i16x8.sub_sat_s" => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), SUB_SAT_vbinop_(S_sx))
  ;; test.spectec:8419.5-8419.53
  prod "i16x8.sub_sat_u" => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), SUB_SAT_vbinop_(U_sx))
  ;; test.spectec:8420.5-8420.41
  prod "i16x8.mul" => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), MUL_vbinop_)
  ;; test.spectec:8421.5-8421.45
  prod "i16x8.min_s" => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), MIN_vbinop_(S_sx))
  ;; test.spectec:8422.5-8422.45
  prod "i16x8.min_u" => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), MIN_vbinop_(U_sx))
  ;; test.spectec:8423.5-8423.45
  prod "i16x8.max_s" => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), MAX_vbinop_(S_sx))
  ;; test.spectec:8424.5-8424.45
  prod "i16x8.max_u" => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), MAX_vbinop_(U_sx))
  ;; test.spectec:8425.5-8425.47
  prod "i16x8.avgr_u" => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), AVGRU_vbinop_)
  ;; test.spectec:8426.5-8426.61
  prod "i16x8.q15mulr_sat_s" => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), Q15MULR_SATS_vbinop_)
  ;; test.spectec:8427.5-8427.69
  prod "i16x8.relaxed_q15mulr_s" => VBINOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), RELAXED_Q15MULRS_vbinop_)
  ;; test.spectec:8431.5-8431.41
  prod "i32x4.add" => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), ADD_vbinop_)
  ;; test.spectec:8434.5-8434.41
  prod "i32x4.sub" => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), SUB_vbinop_)
  ;; test.spectec:8437.5-8437.41
  prod "i32x4.mul" => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), MUL_vbinop_)
  ;; test.spectec:8438.5-8438.45
  prod "i32x4.min_s" => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), MIN_vbinop_(S_sx))
  ;; test.spectec:8439.5-8439.45
  prod "i32x4.min_u" => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), MIN_vbinop_(U_sx))
  ;; test.spectec:8440.5-8440.45
  prod "i32x4.max_s" => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), MAX_vbinop_(S_sx))
  ;; test.spectec:8441.5-8441.45
  prod "i32x4.max_u" => VBINOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), MAX_vbinop_(U_sx))
  ;; test.spectec:8446.5-8446.41
  prod "i64x2.add" => VBINOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), ADD_vbinop_)
  ;; test.spectec:8449.5-8449.41
  prod "i64x2.sub" => VBINOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), SUB_vbinop_)
  ;; test.spectec:8452.5-8452.41
  prod "i64x2.mul" => VBINOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), MUL_vbinop_)
  ;; test.spectec:8461.5-8461.41
  prod "f32x4.add" => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), ADD_vbinop_)
  ;; test.spectec:8462.5-8462.41
  prod "f32x4.sub" => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), SUB_vbinop_)
  ;; test.spectec:8463.5-8463.41
  prod "f32x4.mul" => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), MUL_vbinop_)
  ;; test.spectec:8464.5-8464.41
  prod "f32x4.div" => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), DIV_vbinop_)
  ;; test.spectec:8465.5-8465.41
  prod "f32x4.min" => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), MIN_vbinop_)
  ;; test.spectec:8466.5-8466.41
  prod "f32x4.max" => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), MAX_vbinop_)
  ;; test.spectec:8467.5-8467.43
  prod "f32x4.pmin" => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), PMIN_vbinop_)
  ;; test.spectec:8468.5-8468.43
  prod "f32x4.pmax" => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), PMAX_vbinop_)
  ;; test.spectec:8469.5-8469.57
  prod "f32x4.relaxed_min" => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), RELAXED_MIN_vbinop_)
  ;; test.spectec:8470.5-8470.57
  prod "f32x4.relaxed_max" => VBINOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), RELAXED_MAX_vbinop_)
  ;; test.spectec:8474.5-8474.41
  prod "f64x2.add" => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), ADD_vbinop_)
  ;; test.spectec:8475.5-8475.41
  prod "f64x2.sub" => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), SUB_vbinop_)
  ;; test.spectec:8476.5-8476.41
  prod "f64x2.mul" => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), MUL_vbinop_)
  ;; test.spectec:8477.5-8477.41
  prod "f64x2.div" => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), DIV_vbinop_)
  ;; test.spectec:8478.5-8478.41
  prod "f64x2.min" => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), MIN_vbinop_)
  ;; test.spectec:8479.5-8479.41
  prod "f64x2.max" => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), MAX_vbinop_)
  ;; test.spectec:8480.5-8480.43
  prod "f64x2.pmin" => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), PMIN_vbinop_)
  ;; test.spectec:8481.5-8481.43
  prod "f64x2.pmax" => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), PMAX_vbinop_)
  ;; test.spectec:8482.5-8482.57
  prod "f64x2.relaxed_min" => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), RELAXED_MIN_vbinop_)
  ;; test.spectec:8483.5-8483.57
  prod "f64x2.relaxed_max" => VBINOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), RELAXED_MAX_vbinop_)
  ;; test.spectec:8487.5-8487.48
  prod "v128.bitselect" => VVTERNOP_instr(V128_vectype, BITSELECT_vvternop)
  ;; test.spectec:8491.5-8491.72
  prod "i8x16.relaxed_laneselect" => VTERNOP_instr(`%X%`_shape(I8_lanetype, `%`_dim(16)), RELAXED_LANESELECT_vternop_)
  ;; test.spectec:8495.5-8495.72
  prod "i16x8.relaxed_laneselect" => VTERNOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), RELAXED_LANESELECT_vternop_)
  ;; test.spectec:8499.5-8499.72
  prod "i32x4.relaxed_laneselect" => VTERNOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), RELAXED_LANESELECT_vternop_)
  ;; test.spectec:8503.5-8503.72
  prod "i64x2.relaxed_laneselect" => VTERNOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), RELAXED_LANESELECT_vternop_)
  ;; test.spectec:8507.5-8507.60
  prod "f32x4.relaxed_madd" => VTERNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), RELAXED_MADD_vternop_)
  ;; test.spectec:8508.5-8508.62
  prod "f32x4.relaxed_nmadd" => VTERNOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), RELAXED_NMADD_vternop_)
  ;; test.spectec:8512.5-8512.60
  prod "f64x2.relaxed_madd" => VTERNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), RELAXED_MADD_vternop_)
  ;; test.spectec:8513.5-8513.62
  prod "f64x2.relaxed_nmadd" => VTERNOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), RELAXED_NMADD_vternop_)
  ;; test.spectec:8517.5-8517.43
  prod "i8x16.shl" => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), SHL_vshiftop_)
  ;; test.spectec:8518.5-8518.47
  prod "i8x16.shr_s" => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), SHR_vshiftop_(S_sx))
  ;; test.spectec:8519.5-8519.47
  prod "i8x16.shr_u" => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), SHR_vshiftop_(U_sx))
  ;; test.spectec:8523.5-8523.43
  prod "i16x8.shl" => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), SHL_vshiftop_)
  ;; test.spectec:8524.5-8524.47
  prod "i16x8.shr_s" => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), SHR_vshiftop_(S_sx))
  ;; test.spectec:8525.5-8525.47
  prod "i16x8.shr_u" => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), SHR_vshiftop_(U_sx))
  ;; test.spectec:8529.5-8529.43
  prod "i32x4.shl" => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), SHL_vshiftop_)
  ;; test.spectec:8530.5-8530.47
  prod "i32x4.shr_s" => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), SHR_vshiftop_(S_sx))
  ;; test.spectec:8531.5-8531.47
  prod "i32x4.shr_u" => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), SHR_vshiftop_(U_sx))
  ;; test.spectec:8535.5-8535.43
  prod "i64x2.shl" => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), SHL_vshiftop_)
  ;; test.spectec:8536.5-8536.47
  prod "i64x2.shr_s" => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), SHR_vshiftop_(S_sx))
  ;; test.spectec:8537.5-8537.47
  prod "i64x2.shr_u" => VSHIFTOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), SHR_vshiftop_(U_sx))
  ;; test.spectec:8541.5-8541.43
  prod "i8x16.bitmask" => VBITMASK_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))))
  ;; test.spectec:8545.5-8545.43
  prod "i16x8.bitmask" => VBITMASK_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))))
  ;; test.spectec:8549.5-8549.43
  prod "i32x4.bitmask" => VBITMASK_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))))
  ;; test.spectec:8553.5-8553.43
  prod "i64x2.bitmask" => VBITMASK_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))))
  ;; test.spectec:8557.5-8557.62
  prod "i8x16.narrow_i16x8_s" => VNARROW_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), S_sx)
  ;; test.spectec:8558.5-8558.62
  prod "i8x16.narrow_i16x8_u" => VNARROW_instr(`%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), U_sx)
  ;; test.spectec:8562.5-8562.62
  prod "i16x8.narrow_i32x4_s" => VNARROW_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), S_sx)
  ;; test.spectec:8563.5-8563.62
  prod "i16x8.narrow_i32x4_u" => VNARROW_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), U_sx)
  ;; test.spectec:8572.5-8572.76
  prod "i16x8.extend_low_i8x16_s" => VCVTOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), `%X%`_shape(I8_lanetype, `%`_dim(16)), EXTEND_vcvtop__(LOW_half, S_sx))
  ;; test.spectec:8573.5-8573.76
  prod "i16x8.extend_low_i8x16_u" => VCVTOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), `%X%`_shape(I8_lanetype, `%`_dim(16)), EXTEND_vcvtop__(LOW_half, U_sx))
  ;; test.spectec:8574.5-8574.78
  prod "i16x8.extend_high_i8x16_s" => VCVTOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), `%X%`_shape(I8_lanetype, `%`_dim(16)), EXTEND_vcvtop__(HIGH_half, S_sx))
  ;; test.spectec:8575.5-8575.78
  prod "i16x8.extend_high_i8x16_u" => VCVTOP_instr(`%X%`_shape(I16_lanetype, `%`_dim(8)), `%X%`_shape(I8_lanetype, `%`_dim(16)), EXTEND_vcvtop__(HIGH_half, U_sx))
  ;; test.spectec:8579.5-8579.76
  prod "i32x4.extend_low_i16x8_s" => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(I16_lanetype, `%`_dim(8)), EXTEND_vcvtop__(LOW_half, S_sx))
  ;; test.spectec:8580.5-8580.76
  prod "i32x4.extend_low_i16x8_u" => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(I16_lanetype, `%`_dim(8)), EXTEND_vcvtop__(LOW_half, U_sx))
  ;; test.spectec:8581.5-8581.78
  prod "i32x4.extend_high_i16x8_s" => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(I16_lanetype, `%`_dim(8)), EXTEND_vcvtop__(HIGH_half, S_sx))
  ;; test.spectec:8582.5-8582.78
  prod "i32x4.extend_high_i16x8_u" => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(I16_lanetype, `%`_dim(8)), EXTEND_vcvtop__(HIGH_half, U_sx))
  ;; test.spectec:8583.5-8583.74
  prod "i32x4.trunc_sat_f32x4_s" => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F32_lanetype, `%`_dim(4)), TRUNC_SAT_vcvtop__(S_sx, ?()))
  ;; test.spectec:8584.5-8584.74
  prod "i32x4.trunc_sat_f32x4_u" => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F32_lanetype, `%`_dim(4)), TRUNC_SAT_vcvtop__(U_sx, ?()))
  ;; test.spectec:8585.5-8585.84
  prod "i32x4.trunc_sat_f64x2_s_zero" => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F64_lanetype, `%`_dim(2)), TRUNC_SAT_vcvtop__(S_sx, ?(ZERO_zero)))
  ;; test.spectec:8586.5-8586.84
  prod "i32x4.trunc_sat_f64x2_u_zero" => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F64_lanetype, `%`_dim(2)), TRUNC_SAT_vcvtop__(U_sx, ?(ZERO_zero)))
  ;; test.spectec:8587.5-8587.82
  prod "i32x4.relaxed_trunc_f32x4_s" => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F32_lanetype, `%`_dim(4)), RELAXED_TRUNC_vcvtop__(S_sx, ?()))
  ;; test.spectec:8588.5-8588.82
  prod "i32x4.relaxed_trunc_f32x4_u" => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F32_lanetype, `%`_dim(4)), RELAXED_TRUNC_vcvtop__(U_sx, ?()))
  ;; test.spectec:8589.5-8589.92
  prod "i32x4.relaxed_trunc_f64x2_s_zero" => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F64_lanetype, `%`_dim(2)), RELAXED_TRUNC_vcvtop__(S_sx, ?(ZERO_zero)))
  ;; test.spectec:8590.5-8590.92
  prod "i32x4.relaxed_trunc_f64x2_u_zero" => VCVTOP_instr(`%X%`_shape(I32_lanetype, `%`_dim(4)), `%X%`_shape(F64_lanetype, `%`_dim(2)), RELAXED_TRUNC_vcvtop__(U_sx, ?(ZERO_zero)))
  ;; test.spectec:8594.5-8594.76
  prod "i64x2.extend_low_i32x4_s" => VCVTOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), EXTEND_vcvtop__(LOW_half, S_sx))
  ;; test.spectec:8595.5-8595.76
  prod "i64x2.extend_low_i32x4_u" => VCVTOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), EXTEND_vcvtop__(LOW_half, U_sx))
  ;; test.spectec:8596.5-8596.78
  prod "i64x2.extend_high_i32x4_s" => VCVTOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), EXTEND_vcvtop__(HIGH_half, S_sx))
  ;; test.spectec:8597.5-8597.78
  prod "i64x2.extend_high_i32x4_u" => VCVTOP_instr(`%X%`_shape(I64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), EXTEND_vcvtop__(HIGH_half, U_sx))
  ;; test.spectec:8607.5-8607.74
  prod "f32x4.demote_f64x2_zero" => VCVTOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), `%X%`_shape(F64_lanetype, `%`_dim(2)), DEMOTE_vcvtop__(ZERO_zero))
  ;; test.spectec:8608.5-8608.70
  prod "f32x4.convert_i32x4_s" => VCVTOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), `%X%`_shape(I32_lanetype, `%`_dim(4)), CONVERT_vcvtop__(?(), S_sx))
  ;; test.spectec:8609.5-8609.70
  prod "f32x4.convert_i32x4_u" => VCVTOP_instr(`%X%`_shape(F32_lanetype, `%`_dim(4)), `%X%`_shape(I32_lanetype, `%`_dim(4)), CONVERT_vcvtop__(?(), U_sx))
  ;; test.spectec:8615.5-8615.74
  prod "f64x2.promote_low_f32x4" => VCVTOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), `%X%`_shape(F32_lanetype, `%`_dim(4)), PROMOTELOW_vcvtop__)
  ;; test.spectec:8617.5-8617.78
  prod "f64x2.convert_low_i32x4_s" => VCVTOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), CONVERT_vcvtop__(?(LOW_half), S_sx))
  ;; test.spectec:8618.5-8618.78
  prod "f64x2.convert_low_i32x4_u" => VCVTOP_instr(`%X%`_shape(F64_lanetype, `%`_dim(2)), `%X%`_shape(I32_lanetype, `%`_dim(4)), CONVERT_vcvtop__(?(LOW_half), U_sx))
  ;; test.spectec:8626.5-8626.88
  prod "i16x8.extadd_pairwise_i8x16_s" => VEXTUNOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTADD_PAIRWISE_vextunop__(S_sx))
  ;; test.spectec:8627.5-8627.88
  prod "i16x8.extadd_pairwise_i8x16_u" => VEXTUNOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTADD_PAIRWISE_vextunop__(U_sx))
  ;; test.spectec:8631.5-8631.88
  prod "i32x4.extadd_pairwise_i16x8_s" => VEXTUNOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTADD_PAIRWISE_vextunop__(S_sx))
  ;; test.spectec:8632.5-8632.88
  prod "i32x4.extadd_pairwise_i16x8_u" => VEXTUNOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTADD_PAIRWISE_vextunop__(U_sx))
  ;; test.spectec:8636.5-8636.79
  prod "i16x8.extmul_low_i8x16_s" => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTMUL_vextbinop__(LOW_half, S_sx))
  ;; test.spectec:8637.5-8637.79
  prod "i16x8.extmul_low_i8x16_u" => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTMUL_vextbinop__(LOW_half, U_sx))
  ;; test.spectec:8638.5-8638.81
  prod "i16x8.extmul_high_i8x16_s" => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTMUL_vextbinop__(HIGH_half, S_sx))
  ;; test.spectec:8639.5-8639.81
  prod "i16x8.extmul_high_i8x16_u" => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), EXTMUL_vextbinop__(HIGH_half, U_sx))
  ;; test.spectec:8641.5-8641.87
  prod "i16x8.relaxed_dot_i8x16_i7x16_s" => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), `%`_ishape(`%X%`_shape(I8_lanetype, `%`_dim(16))), RELAXED_DOTS_vextbinop__)
  ;; test.spectec:8645.5-8645.79
  prod "i32x4.extmul_low_i16x8_s" => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTMUL_vextbinop__(LOW_half, S_sx))
  ;; test.spectec:8646.5-8646.79
  prod "i32x4.extmul_low_i16x8_u" => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTMUL_vextbinop__(LOW_half, U_sx))
  ;; test.spectec:8647.5-8647.81
  prod "i32x4.extmul_high_i16x8_s" => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTMUL_vextbinop__(HIGH_half, S_sx))
  ;; test.spectec:8648.5-8648.81
  prod "i32x4.extmul_high_i16x8_u" => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), EXTMUL_vextbinop__(HIGH_half, U_sx))
  ;; test.spectec:8649.5-8649.65
  prod "i32x4.dot_i16x8_s" => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), DOTS_vextbinop__)
  ;; test.spectec:8653.5-8653.79
  prod "i64x2.extmul_low_i32x4_s" => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), EXTMUL_vextbinop__(LOW_half, S_sx))
  ;; test.spectec:8654.5-8654.79
  prod "i64x2.extmul_low_i32x4_u" => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), EXTMUL_vextbinop__(LOW_half, U_sx))
  ;; test.spectec:8655.5-8655.81
  prod "i64x2.extmul_high_i32x4_s" => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), EXTMUL_vextbinop__(HIGH_half, S_sx))
  ;; test.spectec:8656.5-8656.81
  prod "i64x2.extmul_high_i32x4_u" => VEXTBINOP_instr(`%`_ishape(`%X%`_shape(I64_lanetype, `%`_dim(2))), `%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), EXTMUL_vextbinop__(HIGH_half, U_sx))
  ;; test.spectec:8661.5-8661.96
  prod "i32x4.relaxed_dot_i8x16_i7x16_add_s" => VEXTTERNOP_instr(`%`_ishape(`%X%`_shape(I32_lanetype, `%`_dim(4))), `%`_ishape(`%X%`_shape(I16_lanetype, `%`_dim(8))), RELAXED_DOT_ADDS_vextternop__)

;; test.spectec:7670.1-7745.65
rec {

;; test.spectec:7670.1-7672.29
grammar Tinstr_(I : I) : instr
  ;; test.spectec:7671.5-7671.29
  prod{in : instr} in:Tplaininstr_(I) => in
  ;; test.spectec:7672.5-7672.29
  prod{in : instr} in:Tblockinstr_(I) => in

;; test.spectec:7678.1-7679.52
grammar Tinstrs_(I : I) : instr*
  ;; test.spectec:7675.5-7675.27
  prod{`in*` : instr*} in*{in <- `in*`}:Tinstr_(I)*{} => in*{in <- `in*`}
  ;; test.spectec:7679.5-7679.52
  prod{`in**` : instr**} in*{in <- `in*`}*{`in*` <- `in**`}:Tfoldedinstr_(I)*{} => $concat_(syntax instr, in*{in <- `in*`}*{`in*` <- `in**`})

;; test.spectec:7743.1-7745.65
grammar Tblockinstr_(I : I) : instr
  ;; test.spectec:7718.5-7722.35
  prod{bt : blocktype, `in*` : instr*, `id?` : char?, I' : I, `id'?` : char?} {{"block"} {(?(`%`_name(lift(id?{id <- `id?`}))), I'):Tlabel_(I)} {bt:Tblocktype_(I)} {in*{in <- `in*`}:Tinstrs_(I')} {"end"} {?(`%`_name(lift(id'?{id' <- `id'?`}))):Tid?{}}} => BLOCK_instr(bt, in*{in <- `in*`})
    -- if ((id'?{id' <- `id'?`} = ?()) \/ (id'?{id' <- `id'?`} = id?{id <- `id?`}))
  ;; test.spectec:7723.5-7727.35
  prod{bt : blocktype, `in*` : instr*, `id?` : char?, I' : I, `id'?` : char?} {{"loop"} {(?(`%`_name(lift(id?{id <- `id?`}))), I'):Tlabel_(I)} {bt:Tblocktype_(I)} {in*{in <- `in*`}:Tinstrs_(I')} {"end"} {?(`%`_name(lift(id'?{id' <- `id'?`}))):Tid?{}}} => LOOP_instr(bt, in*{in <- `in*`})
    -- if ((id'?{id' <- `id'?`} = ?()) \/ (id'?{id' <- `id'?`} = id?{id <- `id?`}))
  ;; test.spectec:7728.5-7734.71
  prod{bt : blocktype, `in_1*` : instr*, `in_2*` : instr*, `id?` : char?, I' : I, `id_1?` : char?, `id_2?` : char?} {{"if"} {(?(`%`_name(lift(id?{id <- `id?`}))), I'):Tlabel_(I)} {bt:Tblocktype_(I)} {in_1*{in_1 <- `in_1*`}:Tinstrs_(I')} {"else"} {?(`%`_name(lift(id_1?{id_1 <- `id_1?`}))):Tid?{}} {in_2*{in_2 <- `in_2*`}:Tinstrs_(I')} {"end"} {?(`%`_name(lift(id_2?{id_2 <- `id_2?`}))):Tid?{}}} => `IF%%ELSE%`_instr(bt, in_1*{in_1 <- `in_1*`}, in_2*{in_2 <- `in_2*`})
    -- if (((id_1?{id_1 <- `id_1?`} = ?()) \/ (id_1?{id_1 <- `id_1?`} = id?{id <- `id?`})) /\ ((id_2?{id_2 <- `id_2?`} = ?()) \/ (id_2?{id_2 <- `id_2?`} = id?{id <- `id?`})))
  ;; test.spectec:7735.5-7740.35
  prod{bt : blocktype, `c*` : catch*, `in*` : instr*, `id?` : char?, I' : I, `id'?` : char?} {{"try_table"} {(?(`%`_name(lift(id?{id <- `id?`}))), I'):Tlabel_(I)} {bt:Tblocktype_(I)} {c*{c <- `c*`}:Tcatch_(I)*{}} {in*{in <- `in*`}:Tinstrs_(I')} {"end"} {?(`%`_name(lift(id'?{id' <- `id'?`}))):Tid?{}}} => TRY_TABLE_instr(bt, `%`_list(c*{c <- `c*`}), in*{in <- `in*`})
    -- if ((id'?{id' <- `id'?`} = ?()) \/ (id'?{id' <- `id'?`} = id?{id <- `id?`}))
}

;; test.spectec:8666.1-8667.27
grammar Texpr_(I : I) : expr
  ;; test.spectec:8667.5-8667.27
  prod{`in*` : instr*} in*{in <- `in*`}:Tinstrs_(I) => in*{in <- `in*`}

;; test.spectec:8682.1-8685.45
grammar Ttype_(I : I) : (type, idctxt)
  ;; test.spectec:8683.5-8685.45
  prod{qt : rectype, I' : I, I'' : I, n : n, `st*` : subtype*} (qt, I'):Trectype_(I) => (TYPE_type(qt), I' +++ I'')
    -- if (qt = REC_rectype(`%`_list(st^n{st <- `st*`})))
    -- if (I'' = {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS ?(_DEF_deftype(qt, i))^(i<n){}})

;; test.spectec:8690.1-8691.69
grammar Ttag_(I : I) : (tag, idctxt)
  ;; test.spectec:8691.5-8691.69
  prod{jt : tagtype, `id?` : char?} {{"("} {"tag"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {jt:Ttagtype_(I)} {")"}} => (TAG_tag(jt), {TYPES [], TAGS [?(`%`_name(lift(id?{id <- `id?`})))], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})

;; test.spectec:8696.1-8697.95
grammar Tglobal_(I : I) : (global, idctxt)
  ;; test.spectec:8697.5-8697.95
  prod{gt : globaltype, e : expr, `id?` : char?} {{"("} {"global"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {gt:Tglobaltype_(I)} {e:Texpr_(I)} {")"}} => (GLOBAL_global(gt, e), {TYPES [], TAGS [], GLOBALS [?(`%`_name(lift(id?{id <- `id?`})))], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})

;; test.spectec:8702.1-8703.75
grammar Tmem_(I : I) : (mem, idctxt)
  ;; test.spectec:8703.5-8703.75
  prod{mt : memtype, `id?` : char?} {{"("} {"memory"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {mt:Tmemtype_(I)} {")"}} => (MEMORY_mem(mt), {TYPES [], TAGS [], GLOBALS [], MEMS [?(`%`_name(lift(id?{id <- `id?`})))], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})

;; test.spectec:8712.1-8716.37
grammar Ttable_(I : I) : (table, idctxt)
  ;; test.spectec:8709.5-8709.91
  prod{tt : tabletype, e : expr, `id?` : char?} {{"("} {"table"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {tt:Ttabletype_(I)} {e:Texpr_(I)} {")"}} => (TABLE_table(tt, e), {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [?(`%`_name(lift(id?{id <- `id?`})))], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})

;; test.spectec:8733.1-8734.73
grammar Tlocal_(I : I) : (local*, idctxt)
  ;; test.spectec:8729.5-8730.30
  prod{t : valtype, `id?` : char?} {{"("} {"local"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {t:Tvaltype_(I)} {")"}} => ([LOCAL_local(t)], {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [?(`%`_name(lift(id?{id <- `id?`})))], LABELS [], FIELDS [], TYPEDEFS []})

;; test.spectec:8721.1-8726.29
grammar Tfunc_(I : I) : (func, idctxt)
  ;; test.spectec:8722.5-8726.29
  prod{x : idx, `loc**` : local**, e : expr, `id?` : char?, I_1 : I, `I_2*` : I*, I' : I} {{"("} {"func"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {(x, I_1):Ttypeuse_(I)} {(loc*{loc <- `loc*`}, I_2):Tlocal_(I)*{I_2 <- `I_2*`, `loc*` <- `loc**`}} {e:Texpr_(I')} {")"}} => (FUNC_func(x, $concat_(syntax local, loc*{loc <- `loc*`}*{`loc*` <- `loc**`}), e), {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [?(`%`_name(lift(id?{id <- `id?`})))], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})
    -- if (I' = I +++ I_1 +++ $concat_idctxt(I_2*{I_2 <- `I_2*`}))
    -- Idctxt_ok: `|-%:OK`(I')

;; test.spectec:8745.1-8746.40
grammar Tdatastring : byte*
  ;; test.spectec:8746.5-8746.40
  prod{`b**` : byte**} b*{b <- `b*`}*{`b*` <- `b**`}:Tstring*{} => $concat_(syntax byte, b*{b <- `b*`}*{`b*` <- `b**`})

;; test.spectec:8752.1-8753.36
grammar Tmemuse_(I : I) : memidx
  ;; test.spectec:8749.5-8749.40
  prod{x : idx} {{"("} {"memory"} {x:Tmemidx_(I)} {")"}} => x

;; test.spectec:8759.1-8760.62
grammar Toffset_(I : I) : expr
  ;; test.spectec:8756.5-8756.38
  prod{e : expr} {{"("} {"offset"} {e:Texpr_(I)} {")"}} => e

;; test.spectec:8739.1-8743.42
grammar Tdata_(I : I) : (data, idctxt)
  ;; test.spectec:8740.5-8741.37
  prod{`b*` : byte*, `id?` : char?} {{"("} {"data"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {b*{b <- `b*`}:Tdatastring} {")"}} => (DATA_data(b*{b <- `b*`}, PASSIVE_datamode), {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [?(`%`_name(lift(id?{id <- `id?`})))], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})
  ;; test.spectec:8742.5-8743.42
  prod{`b*` : byte*, x : idx, e : expr, `id?` : char?} {{"("} {"data"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {x:Tmemuse_(I)} {e:Toffset_(I)} {b*{b <- `b*`}:Tdatastring} {")"}} => (DATA_data(b*{b <- `b*`}, ACTIVE_datamode(x, e)), {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [?(`%`_name(lift(id?{id <- `id?`})))], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})

;; test.spectec:8789.1-8790.60
grammar Telemexpr_(I : I) : expr
  ;; test.spectec:8786.5-8786.36
  prod{e : expr} {{"("} {"item"} {e:Texpr_(I)} {")"}} => e

;; test.spectec:8782.1-8783.91
grammar Telemlist_(I : I) : (reftype, expr*)
  ;; test.spectec:8779.5-8779.56
  prod{rt : reftype, `e*` : expr*} {{rt:Treftype_(I)} {e*{e <- `e*`}:Tlist(syntax expr, grammar Telemexpr_(I))}} => (rt, e*{e <- `e*`})

;; test.spectec:8796.1-8797.35
grammar Ttableuse_(I : I) : tableidx
  ;; test.spectec:8793.5-8793.41
  prod{x : idx} {{"("} {"table"} {x:Ttableidx_(I)} {")"}} => x

;; test.spectec:8774.1-8776.58
grammar Telem_(I : I) : (elem, idctxt)
  ;; test.spectec:8766.5-8767.40
  prod{rt : reftype, `e*` : expr*, `id?` : char?} {{"("} {"elem"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {(rt, e*{e <- `e*`}):Telemlist_(I)} {")"}} => (ELEM_elem(rt, e*{e <- `e*`}, PASSIVE_elemmode), {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [?(`%`_name(lift(id?{id <- `id?`})))], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})
  ;; test.spectec:8768.5-8769.46
  prod{rt : reftype, `e*` : expr*, x : idx, e' : expr, `id?` : char?} {{"("} {"elem"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {x:Ttableuse_(I)} {e':Toffset_(I)} {(rt, e*{e <- `e*`}):Telemlist_(I)} {")"}} => (ELEM_elem(rt, e*{e <- `e*`}, ACTIVE_elemmode(x, e')), {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [?(`%`_name(lift(id?{id <- `id?`})))], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})
  ;; test.spectec:8770.5-8771.40
  prod{rt : reftype, `e*` : expr*, `id?` : char?} {{"("} {"elem"} {?(`%`_name(lift(id?{id <- `id?`}))):Tid?{}} {"declare"} {(rt, e*{e <- `e*`}):Telemlist_(I)} {")"}} => (ELEM_elem(rt, e*{e <- `e*`}, DECLARE_elemmode), {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [?(`%`_name(lift(id?{id <- `id?`})))], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})

;; test.spectec:8802.1-8803.52
grammar Tstart_(I : I) : (start, idctxt)
  ;; test.spectec:8803.5-8803.52
  prod{x : idx} {{"("} {"start"} {x:Tfuncidx_(I)} {")"}} => (START_start(x), {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})

;; test.spectec:8832.1-8834.62
grammar Timport_(I : I) : (import, idctxt)
  ;; test.spectec:8809.5-8809.96
  prod{nm_1 : name, nm_2 : name, xt : externtype, I' : I} {{"("} {"import"} {nm_1:Tname} {nm_2:Tname} {(xt, I'):Texterntype_(I)} {")"}} => (IMPORT_import(nm_1, nm_2, xt), I')

;; test.spectec:8839.1-8840.70
grammar Texport_(I : I) : (export, idctxt)
  ;; test.spectec:8840.5-8840.70
  prod{nm : name, xx : externidx} {{"("} {"export"} {nm:Tname} {xx:Texternidx_(I)} {")"}} => (EXPORT_export(nm, xx), {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], FIELDS [], TYPEDEFS []})

;; test.spectec:8842.1-8842.45
grammar Texportdots : ()
  ;; test.spectec:8842.23-8842.45
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{"("} {"export"} {Tname} {")"}} => (`<implicit-prod-result>`, ()).1

;; test.spectec:8843.1-8843.51
grammar Timportdots : ()
  ;; test.spectec:8843.23-8843.51
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{"("} {"import"} {Tname} {Tname} {")"}} => (`<implicit-prod-result>`, ()).1

;; test.spectec:8847.1-8849.42
grammar Texporttagdots_(I : I) : ()
  ;; test.spectec:8848.5-8848.30
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{Texportdots*{}} {Ttagtype_(I)}} => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:8849.5-8849.42
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{Texportdots*{}} Timportdots {Ttagtype_(I)}} => (`<implicit-prod-result>`, ()).1

;; test.spectec:8851.1-8853.45
grammar Texportglobaldots_(I : I) : ()
  ;; test.spectec:8852.5-8852.43
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{Texportdots*{}} {Tglobaltype_(I)} {Texpr_(I)}} => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:8853.5-8853.45
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{Texportdots*{}} Timportdots {Tglobaltype_(I)}} => (`<implicit-prod-result>`, ()).1

;; test.spectec:8855.1-8858.42
grammar Texportmemdots_(I : I) : ()
  ;; test.spectec:8856.5-8856.30
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{Texportdots*{}} {Tmemtype_(I)}} => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:8857.5-8857.55
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{Texportdots*{}} {Taddrtype?{}} {"("} {"data"} {Tdatastring} {")"}} => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:8858.5-8858.42
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{Texportdots*{}} Timportdots {Tmemtype_(I)}} => (`<implicit-prod-result>`, ()).1

;; test.spectec:8860.1-8863.44
grammar Texporttabledots_(I : I) : ()
  ;; test.spectec:8861.5-8861.43
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{Texportdots*{}} {Ttabletype_(I)} {Texpr_(I)?{}}} => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:8862.5-8862.70
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{Texportdots*{}} {Taddrtype?{}} {Treftype_(I)} {"("} {"elem"} {Telemlist_(I)} {")"}} => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:8863.5-8863.44
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{Texportdots*{}} Timportdots {Ttabletype_(I)}} => (`<implicit-prod-result>`, ()).1

;; test.spectec:8865.1-8867.42
grammar Texportfuncdots_(I : I) : ()
  ;; test.spectec:8866.5-8866.52
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{Texportdots*{}} {Ttypeuse_(I)} {Tlocal_(I)*{}} {Texpr_(I)}} => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:8867.5-8867.42
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:{{Texportdots*{}} Timportdots {Ttypeuse_(I)}} => (`<implicit-prod-result>`, ()).1

;; test.spectec:8873.1-8878.51
grammar Texporttag_(I : I) : ()

;; test.spectec:8880.1-8885.54
grammar Texportglobal_(I : I) : ()

;; test.spectec:8887.1-8892.51
grammar Texportmem_(I : I) : ()

;; test.spectec:8894.1-8899.53
grammar Texporttable_(I : I) : ()

;; test.spectec:8901.1-8906.52
grammar Texportfunc_(I : I) : ()

;; test.spectec:8909.1-8916.39
grammar Tdatamem_(I : I) : ()

;; test.spectec:8918.1-8925.19
grammar Telemtable_(I : I) : ()

;; test.spectec:8997.1-8999.65
grammar Tdecl_(I : I) : (decl, idctxt)
  ;; test.spectec:8998.5-8998.14
  prod{`<implicit-prod-result>` : (type, idctxt)} `<implicit-prod-result>`:Ttype_(I) => (`<implicit-prod-result>` : (type, idctxt) <: (decl, idctxt))
  ;; test.spectec:8998.17-8998.28
  prod{`<implicit-prod-result>` : (import, idctxt)} `<implicit-prod-result>`:Timport_(I) => (`<implicit-prod-result>` : (import, idctxt) <: (decl, idctxt))
  ;; test.spectec:8998.31-8998.39
  prod{`<implicit-prod-result>` : (tag, idctxt)} `<implicit-prod-result>`:Ttag_(I) => (`<implicit-prod-result>` : (tag, idctxt) <: (decl, idctxt))
  ;; test.spectec:8998.42-8998.53
  prod{`<implicit-prod-result>` : (global, idctxt)} `<implicit-prod-result>`:Tglobal_(I) => (`<implicit-prod-result>` : (global, idctxt) <: (decl, idctxt))
  ;; test.spectec:8998.56-8998.64
  prod{`<implicit-prod-result>` : (mem, idctxt)} `<implicit-prod-result>`:Tmem_(I) => (`<implicit-prod-result>` : (mem, idctxt) <: (decl, idctxt))
  ;; test.spectec:8998.67-8998.77
  prod{`<implicit-prod-result>` : (table, idctxt)} `<implicit-prod-result>`:Ttable_(I) => (`<implicit-prod-result>` : (table, idctxt) <: (decl, idctxt))
  ;; test.spectec:8999.5-8999.14
  prod{`<implicit-prod-result>` : (func, idctxt)} `<implicit-prod-result>`:Tfunc_(I) => (`<implicit-prod-result>` : (func, idctxt) <: (decl, idctxt))
  ;; test.spectec:8999.17-8999.26
  prod{`<implicit-prod-result>` : (data, idctxt)} `<implicit-prod-result>`:Tdata_(I) => (`<implicit-prod-result>` : (data, idctxt) <: (decl, idctxt))
  ;; test.spectec:8999.29-8999.38
  prod{`<implicit-prod-result>` : (elem, idctxt)} `<implicit-prod-result>`:Telem_(I) => (`<implicit-prod-result>` : (elem, idctxt) <: (decl, idctxt))
  ;; test.spectec:8999.41-8999.51
  prod{`<implicit-prod-result>` : (start, idctxt)} `<implicit-prod-result>`:Tstart_(I) => (`<implicit-prod-result>` : (start, idctxt) <: (decl, idctxt))
  ;; test.spectec:8999.54-8999.65
  prod{`<implicit-prod-result>` : (export, idctxt)} `<implicit-prod-result>`:Texport_(I) => (`<implicit-prod-result>` : (export, idctxt) <: (decl, idctxt))

;; test.spectec:9022.1-9023.50
grammar Tmodule : module
  ;; test.spectec:9003.5-9019.26
  prod{`type*` : type*, `import*` : import*, `tag*` : tag*, `global*` : global*, `mem*` : mem*, `table*` : table*, `func*` : func*, `data*` : data*, `elem*` : elem*, `start?` : start?, `export*` : export*, `I*` : I*, `decl*` : decl*, I' : I} {{"("} {"module"} {Tid?{}} {(decl, I)*{I <- `I*`, decl <- `decl*`}:Tdecl_(I')*{}} {")"}} => MODULE_module(`%`_list(type*{type <- `type*`}), `%`_list(import*{import <- `import*`}), `%`_list(tag*{tag <- `tag*`}), `%`_list(global*{global <- `global*`}), `%`_list(mem*{mem <- `mem*`}), `%`_list(table*{table <- `table*`}), `%`_list(func*{func <- `func*`}), `%`_list(data*{data <- `data*`}), `%`_list(elem*{elem <- `elem*`}), start?{start <- `start?`}, `%`_list(export*{export <- `export*`}))
    -- if (I' = $concat_idctxt(I*{I <- `I*`}))
    -- Idctxt_ok: `|-%:OK`(I')
    -- if (type*{type <- `type*`} = $typesd(decl*{decl <- `decl*`}))
    -- if (import*{import <- `import*`} = $importsd(decl*{decl <- `decl*`}))
    -- if (tag*{tag <- `tag*`} = $tagsd(decl*{decl <- `decl*`}))
    -- if (global*{global <- `global*`} = $globalsd(decl*{decl <- `decl*`}))
    -- if (mem*{mem <- `mem*`} = $memsd(decl*{decl <- `decl*`}))
    -- if (table*{table <- `table*`} = $tablesd(decl*{decl <- `decl*`}))
    -- if (func*{func <- `func*`} = $funcsd(decl*{decl <- `decl*`}))
    -- if (data*{data <- `data*`} = $datasd(decl*{decl <- `decl*`}))
    -- if (elem*{elem <- `elem*`} = $elemsd(decl*{decl <- `decl*`}))
    -- if (lift(start?{start <- `start?`}) = $startsd(decl*{decl <- `decl*`}))
    -- if (export*{export <- `export*`} = $exportsd(decl*{decl <- `decl*`}))
    -- if $ordered(decl*{decl <- `decl*`})

;; test.spectec:9025.1-9025.70
grammar Tdecldots_(I : I) : (decl, idctxt)*
  ;; test.spectec:9025.60-9025.70
  prod{`<implicit-prod-result>` : (decl, idctxt)} [`<implicit-prod-result>`]:Tdecl_(I)*{} => [`<implicit-prod-result>`]

;; test.spectec:9556.1-9556.71
grammar Bvar(syntax X) : ()
  ;; test.spectec:9556.61-9556.71
  prod 0x00 => ((), ()).1

;; test.spectec:9557.1-9557.100
grammar Bsym : A
  ;; test.spectec:9557.37-9557.59
  prod Bvar(syntax B) => $var(syntax A)
  ;; test.spectec:9557.62-9557.100
  prod (Bvar(syntax symdots) | Bvar(syntax B)) => $var(syntax A)

;; test.spectec:9560.1-9560.76
grammar Bsymsplit : ()
  ;; test.spectec:9559.61-9559.70
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:Bvar(syntax B) => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:9560.67-9560.76
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:Bvar(syntax B) => (`<implicit-prod-result>`, ()).1

;; test.spectec:9581.1-9581.71
grammar Tvar(syntax X) : ()
  ;; test.spectec:9581.61-9581.71
  prod 0x00 => ((), ()).1

;; test.spectec:9582.1-9582.100
grammar Tsym : A
  ;; test.spectec:9582.37-9582.59
  prod Tvar(syntax T) => $var(syntax A)
  ;; test.spectec:9582.62-9582.100
  prod (Tvar(syntax symdots) | Tvar(syntax T)) => $var(syntax A)

;; test.spectec:9585.1-9585.76
grammar Tsymsplit : ()
  ;; test.spectec:9584.61-9584.70
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:Tvar(syntax B) => (`<implicit-prod-result>`, ()).1
  ;; test.spectec:9585.67-9585.76
  prod{`<implicit-prod-result>` : ()} `<implicit-prod-result>`:Tvar(syntax B) => (`<implicit-prod-result>`, ()).1

;; test.spectec:9591.1-9592.80
grammar Tabbrev : ()


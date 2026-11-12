;; ============================================================================
;; Companion to specification/wasm-2.0/1-syntax.spectec
;; ============================================================================
;;
;; CATEGORIZATION RESULT: this is the one file in the directory whose
;; category-A content is substantial -- in fact it is essentially the
;; *entire* surface syntax of WebAssembly 2.0. Every other file in this
;; directory (0-aux, 2-syntax-aux, 3-numerics, 4-runtime, 5-runtime-aux,
;; 6-typing, 8-reduction, 9-module, A-binary, B-soundness) defines
;; semantics, algorithms, encoding or proofs *over* the syntax declared
;; here -- see their companion .wat files for why none of them needed one
;; of their own.
;;
;; Category A (exercised below) vs category B (spec-internal plumbing,
;; NOT exercised -- listed so the inventory is complete):
;;
;;   A: bit/byte's *use* as types.i32/i64/f32/f64 (numtype), V128
;;      (vectype), FUNCREF/EXTERNREF (reftype), valtype, resulttype,
;;      packtype (I8/I16, via SIMD shapes), shape/ishape/fshape/pshape,
;;      name, every index space (typeidx/funcidx/globalidx/tableidx/
;;      memidx/elemidx/dataidx/labelidx/localidx), mut, limits,
;;      globaltype, functype, tabletype, memtype, elemtype, externtype,
;;      sx, sz, memarg, blocktype, every unop_/binop_/testop_/relop_/
;;      cvtop__ operator name, every vvunop/vvbinop/vvternop/vvtestop/
;;      vunop_/vbinop_/vtestop_/vrelop_/vshiftop_/vextunop_/vextbinop_/
;;      vcvtop operator name, loadop_/vloadop, every instr/* alternative,
;;      expr, elemmode, datamode, type, local, func, global, table, mem,
;;      elem, data, start, externidx, export, import, module.
;;
;;   B: syntax list(X) (generic combinator); bit/byte/uN/sN/iN/fN/vN/char
;;      as *generic parametrized families* (the semantic domains -- "the
;;      set of N-bit unsigned integers" -- as opposed to one instantiation
;;      like i32 which IS category A); consttype/Inn/Fnn/Vnn/Pnn/Jnn/Lnn
;;      (internal grouping shorthands used to write other rules compactly
;;      -- you write "i32", never "Inn"); every `var` declaration (pure
;;      metavariable naming, e.g. "var t : valtype" just says "rules below
;;      may use the letter t to mean some valtype"); $lanetype/$size/
;;      $psize/$lsize/$isize/$jsize/$fsize/$sizenn*/$lsizenn*/$inv_*size
;;      and num_/pack_/lane_/vec_/$zero (auxiliary size/domain functions,
;;      not syntax); $dim/$shsize (auxiliary shape accessors); half/zero
;;      as used *inside* vcvtop's own definition (the grammar productions
;;      themselves, LOW/HIGH/ZERO, ARE category A -- they appear literally
;;      in mnemonics like i32x4.trunc_sat_f64x2_s_zero).
;;
;; Every demo function below is zero-argument and self-contained (constant
;; operands baked in) specifically so the whole file can be exercised in
;; one shot with:
;;     wasm-interp 1-syntax.wasm --run-all-exports --dummy-import-func
;; which is exactly how this file was verified (see the categorization
;; writeup / CATEGORIES.md in this directory for the expected-value cross
;; check). Every function name states the instruction(s) it demonstrates
;; and, in a trailing comment, the expected result -- open it in wasmdebug
;; and click through them.

(module
  ;; ============================================================
  ;; Types: `type` (explicit type-section entry) -- used below by
  ;; call_indirect and by the _IDX form of blocktype.
  ;; ============================================================
  (type $unary_i32 (func (param i32) (result i32)))

  ;; ============================================================
  ;; Import: `import`, and the FUNC case of `externidx`/`externtype`.
  ;; (Only function imports can be auto-stubbed by `wasm-interp
  ;; --dummy-import-func`, which is why this file imports only one
  ;; function; the GLOBAL/TABLE/MEM externtype cases are demonstrated
  ;; via `export` instead, further down, where no such restriction
  ;; applies.)
  ;; ============================================================
  (import "env" "log" (func $log (param i32) (result i32)))

  ;; ============================================================
  ;; Tables: `table` / `tabletype` (limits + reftype).
  ;; ============================================================
  (table $t0 (export "t0") 3 10 funcref)   ;; main funcref table, elem-initialized below
  (table $t1 (export "t1") 2 externref)    ;; reftype variety: externref table
  (table $t2 (export "t2") 3 funcref)      ;; empty funcref table: target for table.copy/table.init

  ;; ============================================================
  ;; Memory: `mem` / `memtype` (limits, in units of 64KiB pages).
  ;; ============================================================
  (memory $mem0 (export "mem0") 1 4)

  ;; ============================================================
  ;; Globals: `global` / `globaltype` (mut, every valtype).
  ;; ============================================================
  (global $g_count (export "g_count") (mut i32) (i32.const 0))  ;; bumped by $start_fn
  (global $g_i32 (export "g_i32") i32 (i32.const 7))
  (global $g_i64 (export "g_i64") i64 (i64.const 9))
  (global $g_f32 (export "g_f32") f32 (f32.const 1.5))
  (global $g_f64 (export "g_f64") f64 (f64.const 2.5))
  (global $g_v128 (export "g_v128") v128 (v128.const i32x4 1 2 3 4))
  (global $g_funcref (export "g_funcref") funcref (ref.null func))
  (global $g_externref (export "g_externref") externref (ref.null extern))
  ;; ref.func's precise inferred type in *code* can be a non-null typed
  ;; reference (under the later function-references proposal); as a global
  ;; initializer (a const-expr context) it stays plain funcref instead, so
  ;; these two act as portable "funcref-typed handles" for the table demos
  ;; below, whether or not that later proposal happens to be enabled too.
  (global $g_ref_mulby funcref (ref.func $mulby))
  (global $g_ref_sq funcref (ref.func $sq))

  ;; ============================================================
  ;; Elem segments: `elem` / `elemmode` (ACTIVE, PASSIVE, DECLARE).
  ;; ============================================================
  (elem $e_active (table $t0) (i32.const 0) funcref
    (ref.func $sq) (ref.func $addone))                          ;; ACTIVE: loads t0[0..2) at instantiation
  (elem $e_passive funcref (ref.func $sq))                       ;; PASSIVE: only used via table.init
  (elem $e_declare declare funcref (ref.func $mulby))            ;; DECLARE: makes $mulby a legal ref.func target

  ;; ============================================================
  ;; Data segments: `data` / `datamode` (ACTIVE, PASSIVE).
  ;; ============================================================
  (data $d_active (memory $mem0) (i32.const 0) "HELLO, WASM 2.0!")  ;; ACTIVE: loaded at instantiation
  (data $d_passive "PASSIVE-DATA-42")                                ;; PASSIVE: only used via memory.init

  ;; ============================================================
  ;; Start: `start`. Runs automatically once, right after allocation
  ;; and before you can call anything -- bumps $g_count so its value
  ;; observably differs from the literal 0 it was declared with.
  ;; ============================================================
  (start $start_fn)
  (func $start_fn
    (global.set $g_count (i32.add (global.get $g_count) (i32.const 1))))


  ;; ============================================================================
  ;; Helper functions referenced by the elem segments / call_indirect above.
  ;; ============================================================================
  (func $sq (param i32) (result i32) (i32.mul (local.get 0) (local.get 0)))
  (func $addone (param i32) (result i32) (i32.add (local.get 0) (i32.const 1)))
  (func $mulby (param i32) (result i32) (i32.mul (local.get 0) (i32.const 10)))


  ;; ============================================================================
  ;; NUMERIC INSTRUCTIONS -- instr/num: CONST, UNOP, BINOP, TESTOP, RELOP, CVTOP
  ;; One zero-arg exported function per operator; operands are fixed constants
  ;; chosen so the expected result is easy to hand-verify.
  ;; ============================================================================

  ;; -- i32 unop --
  (func (export "i32_clz") (result i32) (i32.clz (i32.const 1)))            ;; 31
  (func (export "i32_ctz") (result i32) (i32.ctz (i32.const 8)))            ;; 3
  (func (export "i32_popcnt") (result i32) (i32.popcnt (i32.const 7)))      ;; 3
  (func (export "i32_extend8_s") (result i32) (i32.extend8_s (i32.const 0xFF)))    ;; -1
  (func (export "i32_extend16_s") (result i32) (i32.extend16_s (i32.const 0xFFFF)));; -1

  ;; -- i32 binop --
  (func (export "i32_add") (result i32) (i32.add (i32.const 2) (i32.const 3)))   ;; 5
  (func (export "i32_sub") (result i32) (i32.sub (i32.const 5) (i32.const 3)))   ;; 2
  (func (export "i32_mul") (result i32) (i32.mul (i32.const 4) (i32.const 5)))   ;; 20
  (func (export "i32_div_s") (result i32) (i32.div_s (i32.const -7) (i32.const 2))) ;; -3
  (func (export "i32_div_u") (result i32) (i32.div_u (i32.const 7) (i32.const 2)))  ;; 3
  (func (export "i32_rem_s") (result i32) (i32.rem_s (i32.const -7) (i32.const 2))) ;; -1
  (func (export "i32_rem_u") (result i32) (i32.rem_u (i32.const 7) (i32.const 2)))  ;; 1
  (func (export "i32_and") (result i32) (i32.and (i32.const 12) (i32.const 10))) ;; 8
  (func (export "i32_or") (result i32) (i32.or (i32.const 12) (i32.const 10)))   ;; 14
  (func (export "i32_xor") (result i32) (i32.xor (i32.const 12) (i32.const 10))) ;; 6
  (func (export "i32_shl") (result i32) (i32.shl (i32.const 1) (i32.const 4)))   ;; 16
  (func (export "i32_shr_s") (result i32) (i32.shr_s (i32.const -16) (i32.const 2))) ;; -4
  (func (export "i32_shr_u") (result i32) (i32.shr_u (i32.const -16) (i32.const 2))) ;; 1073741820
  (func (export "i32_rotl") (result i32) (i32.rotl (i32.const 1) (i32.const 4)))     ;; 16
  (func (export "i32_rotr") (result i32) (i32.rotr (i32.const 16) (i32.const 4)))    ;; 1

  ;; -- i32 testop / relop --
  (func (export "i32_eqz") (result i32) (i32.eqz (i32.const 0)))                 ;; 1
  (func (export "i32_eq") (result i32) (i32.eq (i32.const 3) (i32.const 3)))     ;; 1
  (func (export "i32_ne") (result i32) (i32.ne (i32.const 3) (i32.const 4)))     ;; 1
  (func (export "i32_lt_s") (result i32) (i32.lt_s (i32.const -1) (i32.const 1))) ;; 1
  (func (export "i32_lt_u") (result i32) (i32.lt_u (i32.const -1) (i32.const 1))) ;; 0
  (func (export "i32_gt_s") (result i32) (i32.gt_s (i32.const 1) (i32.const -1))) ;; 1
  (func (export "i32_gt_u") (result i32) (i32.gt_u (i32.const 1) (i32.const -1))) ;; 0
  (func (export "i32_le_s") (result i32) (i32.le_s (i32.const -1) (i32.const -1))) ;; 1
  (func (export "i32_le_u") (result i32) (i32.le_u (i32.const 1) (i32.const 1)))   ;; 1
  (func (export "i32_ge_s") (result i32) (i32.ge_s (i32.const -1) (i32.const -1))) ;; 1
  (func (export "i32_ge_u") (result i32) (i32.ge_u (i32.const 2) (i32.const 1)))   ;; 1

  ;; -- i64 unop --
  (func (export "i64_clz") (result i64) (i64.clz (i64.const 1)))            ;; 63
  (func (export "i64_ctz") (result i64) (i64.ctz (i64.const 8)))            ;; 3
  (func (export "i64_popcnt") (result i64) (i64.popcnt (i64.const 7)))      ;; 3
  (func (export "i64_extend8_s") (result i64) (i64.extend8_s (i64.const 0xFF)))     ;; -1
  (func (export "i64_extend16_s") (result i64) (i64.extend16_s (i64.const 0xFFFF))) ;; -1
  (func (export "i64_extend32_s") (result i64) (i64.extend32_s (i64.const 0xFFFFFFFF))) ;; -1

  ;; -- i64 binop --
  (func (export "i64_add") (result i64) (i64.add (i64.const 2) (i64.const 3)))   ;; 5
  (func (export "i64_sub") (result i64) (i64.sub (i64.const 5) (i64.const 3)))   ;; 2
  (func (export "i64_mul") (result i64) (i64.mul (i64.const 4) (i64.const 5)))   ;; 20
  (func (export "i64_div_s") (result i64) (i64.div_s (i64.const -7) (i64.const 2))) ;; -3
  (func (export "i64_div_u") (result i64) (i64.div_u (i64.const 7) (i64.const 2)))  ;; 3
  (func (export "i64_rem_s") (result i64) (i64.rem_s (i64.const -7) (i64.const 2))) ;; -1
  (func (export "i64_rem_u") (result i64) (i64.rem_u (i64.const 7) (i64.const 2)))  ;; 1
  (func (export "i64_and") (result i64) (i64.and (i64.const 12) (i64.const 10))) ;; 8
  (func (export "i64_or") (result i64) (i64.or (i64.const 12) (i64.const 10)))   ;; 14
  (func (export "i64_xor") (result i64) (i64.xor (i64.const 12) (i64.const 10))) ;; 6
  (func (export "i64_shl") (result i64) (i64.shl (i64.const 1) (i64.const 4)))   ;; 16
  (func (export "i64_shr_s") (result i64) (i64.shr_s (i64.const -16) (i64.const 2))) ;; -4
  (func (export "i64_shr_u") (result i64) (i64.shr_u (i64.const -16) (i64.const 2))) ;; big positive
  (func (export "i64_rotl") (result i64) (i64.rotl (i64.const 1) (i64.const 4)))     ;; 16
  (func (export "i64_rotr") (result i64) (i64.rotr (i64.const 16) (i64.const 4)))    ;; 1

  ;; -- i64 testop / relop --
  (func (export "i64_eqz") (result i32) (i64.eqz (i64.const 0)))                 ;; 1
  (func (export "i64_eq") (result i32) (i64.eq (i64.const 3) (i64.const 3)))     ;; 1
  (func (export "i64_ne") (result i32) (i64.ne (i64.const 3) (i64.const 4)))     ;; 1
  (func (export "i64_lt_s") (result i32) (i64.lt_s (i64.const -1) (i64.const 1))) ;; 1
  (func (export "i64_lt_u") (result i32) (i64.lt_u (i64.const -1) (i64.const 1))) ;; 0
  (func (export "i64_gt_s") (result i32) (i64.gt_s (i64.const 1) (i64.const -1))) ;; 1
  (func (export "i64_gt_u") (result i32) (i64.gt_u (i64.const 1) (i64.const -1))) ;; 0
  (func (export "i64_le_s") (result i32) (i64.le_s (i64.const -1) (i64.const -1))) ;; 1
  (func (export "i64_le_u") (result i32) (i64.le_u (i64.const 1) (i64.const 1)))   ;; 1
  (func (export "i64_ge_s") (result i32) (i64.ge_s (i64.const -1) (i64.const -1))) ;; 1
  (func (export "i64_ge_u") (result i32) (i64.ge_u (i64.const 2) (i64.const 1)))   ;; 1

  ;; -- f32 unop --
  (func (export "f32_abs") (result f32) (f32.abs (f32.const -2.5)))       ;; 2.5
  (func (export "f32_neg") (result f32) (f32.neg (f32.const 2.5)))        ;; -2.5
  (func (export "f32_sqrt") (result f32) (f32.sqrt (f32.const 4.0)))      ;; 2.0
  (func (export "f32_ceil") (result f32) (f32.ceil (f32.const 3.2)))      ;; 4.0
  (func (export "f32_floor") (result f32) (f32.floor (f32.const 3.8)))    ;; 3.0
  (func (export "f32_trunc") (result f32) (f32.trunc (f32.const -3.7)))   ;; -3.0
  (func (export "f32_nearest") (result f32) (f32.nearest (f32.const 2.5))) ;; 2.0 (ties-to-even)

  ;; -- f32 binop --
  (func (export "f32_add") (result f32) (f32.add (f32.const 1.5) (f32.const 2.5)))   ;; 4.0
  (func (export "f32_sub") (result f32) (f32.sub (f32.const 5.5) (f32.const 2.5)))   ;; 3.0
  (func (export "f32_mul") (result f32) (f32.mul (f32.const 2.5) (f32.const 4.0)))   ;; 10.0
  (func (export "f32_div") (result f32) (f32.div (f32.const 10.0) (f32.const 4.0)))  ;; 2.5
  (func (export "f32_min") (result f32) (f32.min (f32.const 3.0) (f32.const 5.0)))   ;; 3.0
  (func (export "f32_max") (result f32) (f32.max (f32.const 3.0) (f32.const 5.0)))   ;; 5.0
  (func (export "f32_copysign") (result f32) (f32.copysign (f32.const 3.0) (f32.const -1.0))) ;; -3.0

  ;; -- f32 relop --
  (func (export "f32_eq") (result i32) (f32.eq (f32.const 2.0) (f32.const 2.0))) ;; 1
  (func (export "f32_ne") (result i32) (f32.ne (f32.const 2.0) (f32.const 3.0))) ;; 1
  (func (export "f32_lt") (result i32) (f32.lt (f32.const 1.0) (f32.const 2.0))) ;; 1
  (func (export "f32_gt") (result i32) (f32.gt (f32.const 2.0) (f32.const 1.0))) ;; 1
  (func (export "f32_le") (result i32) (f32.le (f32.const 2.0) (f32.const 2.0))) ;; 1
  (func (export "f32_ge") (result i32) (f32.ge (f32.const 2.0) (f32.const 2.0))) ;; 1

  ;; -- f64 unop --
  (func (export "f64_abs") (result f64) (f64.abs (f64.const -2.5)))       ;; 2.5
  (func (export "f64_neg") (result f64) (f64.neg (f64.const 2.5)))        ;; -2.5
  (func (export "f64_sqrt") (result f64) (f64.sqrt (f64.const 4.0)))      ;; 2.0
  (func (export "f64_ceil") (result f64) (f64.ceil (f64.const 3.2)))      ;; 4.0
  (func (export "f64_floor") (result f64) (f64.floor (f64.const 3.8)))    ;; 3.0
  (func (export "f64_trunc") (result f64) (f64.trunc (f64.const -3.7)))   ;; -3.0
  (func (export "f64_nearest") (result f64) (f64.nearest (f64.const 2.5))) ;; 2.0

  ;; -- f64 binop --
  (func (export "f64_add") (result f64) (f64.add (f64.const 1.5) (f64.const 2.5)))   ;; 4.0
  (func (export "f64_sub") (result f64) (f64.sub (f64.const 5.5) (f64.const 2.5)))   ;; 3.0
  (func (export "f64_mul") (result f64) (f64.mul (f64.const 2.5) (f64.const 4.0)))   ;; 10.0
  (func (export "f64_div") (result f64) (f64.div (f64.const 10.0) (f64.const 4.0)))  ;; 2.5
  (func (export "f64_min") (result f64) (f64.min (f64.const 3.0) (f64.const 5.0)))   ;; 3.0
  (func (export "f64_max") (result f64) (f64.max (f64.const 3.0) (f64.const 5.0)))   ;; 5.0
  (func (export "f64_copysign") (result f64) (f64.copysign (f64.const 3.0) (f64.const -1.0))) ;; -3.0

  ;; -- f64 relop --
  (func (export "f64_eq") (result i32) (f64.eq (f64.const 2.0) (f64.const 2.0))) ;; 1
  (func (export "f64_ne") (result i32) (f64.ne (f64.const 2.0) (f64.const 3.0))) ;; 1
  (func (export "f64_lt") (result i32) (f64.lt (f64.const 1.0) (f64.const 2.0))) ;; 1
  (func (export "f64_gt") (result i32) (f64.gt (f64.const 2.0) (f64.const 1.0))) ;; 1
  (func (export "f64_le") (result i32) (f64.le (f64.const 2.0) (f64.const 2.0))) ;; 1
  (func (export "f64_ge") (result i32) (f64.ge (f64.const 2.0) (f64.const 2.0))) ;; 1

  ;; -- cvtop: every numtype-to-numtype conversion --
  (func (export "cvt_i32_wrap_i64") (result i32) (i32.wrap_i64 (i64.const 0x100000005))) ;; 5
  (func (export "cvt_i64_extend_i32_s") (result i64) (i64.extend_i32_s (i32.const -1)))  ;; -1
  (func (export "cvt_i64_extend_i32_u") (result i64) (i64.extend_i32_u (i32.const -1)))  ;; 4294967295
  (func (export "cvt_i32_trunc_f32_s") (result i32) (i32.trunc_f32_s (f32.const 3.9)))   ;; 3
  (func (export "cvt_i32_trunc_f32_u") (result i32) (i32.trunc_f32_u (f32.const 3.9)))   ;; 3
  (func (export "cvt_i32_trunc_f64_s") (result i32) (i32.trunc_f64_s (f64.const -3.9)))  ;; -3
  (func (export "cvt_i32_trunc_f64_u") (result i32) (i32.trunc_f64_u (f64.const 3.9)))   ;; 3
  (func (export "cvt_i64_trunc_f32_s") (result i64) (i64.trunc_f32_s (f32.const 3.9)))   ;; 3
  (func (export "cvt_i64_trunc_f32_u") (result i64) (i64.trunc_f32_u (f32.const 3.9)))   ;; 3
  (func (export "cvt_i64_trunc_f64_s") (result i64) (i64.trunc_f64_s (f64.const -3.9)))  ;; -3
  (func (export "cvt_i64_trunc_f64_u") (result i64) (i64.trunc_f64_u (f64.const 3.9)))   ;; 3
  (func (export "cvt_i32_trunc_sat_f32_s") (result i32) (i32.trunc_sat_f32_s (f32.const 1e20)))  ;; 2147483647 (saturates)
  (func (export "cvt_i32_trunc_sat_f32_u") (result i32) (i32.trunc_sat_f32_u (f32.const -5.0)))  ;; 0 (saturates)
  (func (export "cvt_i32_trunc_sat_f64_s") (result i32) (i32.trunc_sat_f64_s (f64.const -1e20))) ;; -2147483648 (saturates)
  (func (export "cvt_i32_trunc_sat_f64_u") (result i32) (i32.trunc_sat_f64_u (f64.const 1e20)))  ;; -1 (u32 max, printed signed)
  (func (export "cvt_i64_trunc_sat_f32_s") (result i64) (i64.trunc_sat_f32_s (f32.const 1e20)))  ;; i64 max (saturates)
  (func (export "cvt_i64_trunc_sat_f32_u") (result i64) (i64.trunc_sat_f32_u (f32.const -5.0)))  ;; 0 (saturates)
  (func (export "cvt_i64_trunc_sat_f64_s") (result i64) (i64.trunc_sat_f64_s (f64.const -1e20))) ;; i64 min (saturates)
  (func (export "cvt_i64_trunc_sat_f64_u") (result i64) (i64.trunc_sat_f64_u (f64.const 1e20)))  ;; u64 max (saturates, printed -1)
  (func (export "cvt_f32_convert_i32_s") (result f32) (f32.convert_i32_s (i32.const -5)))    ;; -5.0
  (func (export "cvt_f32_convert_i32_u") (result f32) (f32.convert_i32_u (i32.const 1000)))  ;; 1000.0
  (func (export "cvt_f32_convert_i64_s") (result f32) (f32.convert_i64_s (i64.const -5)))    ;; -5.0
  (func (export "cvt_f32_convert_i64_u") (result f32) (f32.convert_i64_u (i64.const 1000)))  ;; 1000.0
  (func (export "cvt_f64_convert_i32_s") (result f64) (f64.convert_i32_s (i32.const -5)))    ;; -5.0
  (func (export "cvt_f64_convert_i32_u") (result f64) (f64.convert_i32_u (i32.const 1000)))  ;; 1000.0
  (func (export "cvt_f64_convert_i64_s") (result f64) (f64.convert_i64_s (i64.const -5)))    ;; -5.0
  (func (export "cvt_f64_convert_i64_u") (result f64) (f64.convert_i64_u (i64.const 1000)))  ;; 1000.0
  (func (export "cvt_f32_demote_f64") (result f32) (f32.demote_f64 (f64.const 2.5)))    ;; 2.5
  (func (export "cvt_f64_promote_f32") (result f64) (f64.promote_f32 (f32.const 2.5)))  ;; 2.5
  (func (export "cvt_i32_reinterpret_f32") (result i32) (i32.reinterpret_f32 (f32.const 1.0))) ;; 1065353216
  (func (export "cvt_i64_reinterpret_f64") (result i64) (i64.reinterpret_f64 (f64.const 1.0))) ;; 4607182418800017408
  (func (export "cvt_f32_reinterpret_i32") (result f32) (f32.reinterpret_i32 (i32.const 1065353216))) ;; 1.0
  (func (export "cvt_f64_reinterpret_i64") (result f64) (f64.reinterpret_i64 (i64.const 4607182418800017408))) ;; 1.0


  ;; ============================================================================
  ;; VECTOR (SIMD) INSTRUCTIONS -- instr/vec.
  ;; Every operator construct shown at least once, on a representative shape;
  ;; not every shape x operator combination (that's several hundred more and
  ;; wouldn't demonstrate any *new* construct -- see the categorization note).
  ;; v128 results are summarized as their i32x4 or f32x4 lanes in comments.
  ;; ============================================================================

  ;; -- VCONST, and one v128 constant per shape (exercises `shape` on all 6) --
  (func (export "v128_const_i8x16") (result v128) (v128.const i8x16 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16))
  (func (export "v128_const_i16x8") (result v128) (v128.const i16x8 1 2 3 4 5 6 7 8))
  (func (export "v128_const_i32x4") (result v128) (v128.const i32x4 1 2 3 4))
  (func (export "v128_const_i64x2") (result v128) (v128.const i64x2 1 2))
  (func (export "v128_const_f32x4") (result v128) (v128.const f32x4 1.0 2.0 3.0 4.0))
  (func (export "v128_const_f64x2") (result v128) (v128.const f64x2 1.0 2.0))

  ;; -- VVUNOP / VVBINOP / VVTERNOP / VVTESTOP (bitwise, shape-agnostic) --
  (func (export "v128_not") (result v128) (v128.not (v128.const i32x4 0 0 0 0)))               ;; all-1 lanes
  (func (export "v128_and") (result v128) (v128.and (v128.const i32x4 12 12 12 12) (v128.const i32x4 10 10 10 10))) ;; 8,8,8,8
  (func (export "v128_andnot") (result v128) (v128.andnot (v128.const i32x4 12 12 12 12) (v128.const i32x4 10 10 10 10))) ;; 4,4,4,4
  (func (export "v128_or") (result v128) (v128.or (v128.const i32x4 12 12 12 12) (v128.const i32x4 10 10 10 10)))   ;; 14,14,14,14
  (func (export "v128_xor") (result v128) (v128.xor (v128.const i32x4 12 12 12 12) (v128.const i32x4 10 10 10 10))) ;; 6,6,6,6
  (func (export "v128_bitselect") (result v128)
    (v128.bitselect (v128.const i32x4 -1 -1 -1 -1) (v128.const i32x4 0 0 0 0) (v128.const i32x4 -1 0 -1 0))) ;; -1,0,-1,0
  (func (export "v128_any_true") (result i32) (v128.any_true (v128.const i32x4 0 0 1 0)))      ;; 1

  ;; -- VUNOP (integer: ABS/NEG on i32x4, POPCNT is i8x16-only; float: full set on f32x4) --
  (func (export "i32x4_abs") (result v128) (i32x4.abs (v128.const i32x4 -1 2 -3 4)))     ;; 1,2,3,4
  (func (export "i32x4_neg") (result v128) (i32x4.neg (v128.const i32x4 1 -2 3 -4)))     ;; -1,2,-3,4
  (func (export "i8x16_popcnt") (result v128) (i8x16.popcnt (v128.const i8x16 7 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))) ;; 3,0,...
  (func (export "f32x4_abs") (result v128) (f32x4.abs (v128.const f32x4 -1.0 2.0 -3.0 4.0)))     ;; 1,2,3,4
  (func (export "f32x4_neg") (result v128) (f32x4.neg (v128.const f32x4 1.0 -2.0 3.0 -4.0)))     ;; -1,2,-3,4
  (func (export "f32x4_sqrt") (result v128) (f32x4.sqrt (v128.const f32x4 4.0 9.0 16.0 25.0)))   ;; 2,3,4,5
  (func (export "f32x4_ceil") (result v128) (f32x4.ceil (v128.const f32x4 1.1 2.1 3.1 4.1)))     ;; 2,3,4,5
  (func (export "f32x4_floor") (result v128) (f32x4.floor (v128.const f32x4 1.9 2.9 3.9 4.9)))   ;; 1,2,3,4
  (func (export "f32x4_trunc") (result v128) (f32x4.trunc (v128.const f32x4 -1.9 -2.9 -3.9 -4.9)));; -1,-2,-3,-4
  (func (export "f32x4_nearest") (result v128) (f32x4.nearest (v128.const f32x4 0.5 1.5 2.5 3.5))) ;; 0,2,2,4

  ;; -- VBINOP (integer, incl. saturating/averaging/widening-mul families; float full set) --
  (func (export "i32x4_add") (result v128) (i32x4.add (v128.const i32x4 1 2 3 4) (v128.const i32x4 10 10 10 10)))  ;; 11,12,13,14
  (func (export "i32x4_sub") (result v128) (i32x4.sub (v128.const i32x4 10 10 10 10) (v128.const i32x4 1 2 3 4)))  ;; 9,8,7,6
  (func (export "i32x4_mul") (result v128) (i32x4.mul (v128.const i32x4 1 2 3 4) (v128.const i32x4 5 5 5 5)))      ;; 5,10,15,20
  (func (export "i32x4_min_s") (result v128) (i32x4.min_s (v128.const i32x4 -1 2 -3 4) (v128.const i32x4 0 0 0 0))) ;; -1,0,-3,0
  (func (export "i32x4_min_u") (result v128) (i32x4.min_u (v128.const i32x4 1 2 3 4) (v128.const i32x4 2 2 2 2)))   ;; 1,2,2,2
  (func (export "i32x4_max_s") (result v128) (i32x4.max_s (v128.const i32x4 -1 2 -3 4) (v128.const i32x4 0 0 0 0))) ;; 0,2,0,4
  (func (export "i32x4_max_u") (result v128) (i32x4.max_u (v128.const i32x4 1 2 3 4) (v128.const i32x4 2 2 2 2)))   ;; 2,2,3,4
  (func (export "i8x16_add_sat_s") (result v128)
    (i8x16.add_sat_s (v128.const i8x16 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120)
                      (v128.const i8x16 100 100 100 100 100 100 100 100 100 100 100 100 100 100 100 100))) ;; saturates to 127
  (func (export "i8x16_sub_sat_u") (result v128)
    (i8x16.sub_sat_u (v128.const i8x16 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5)
                      (v128.const i8x16 10 10 10 10 10 10 10 10 10 10 10 10 10 10 10 10))) ;; saturates to 0
  (func (export "i8x16_avgr_u") (result v128)
    (i8x16.avgr_u (v128.const i8x16 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3 3)
                  (v128.const i8x16 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4))) ;; round((3+4)/2) = 4
  (func (export "i16x8_q15mulr_sat_s") (result v128)
    (i16x8.q15mulr_sat_s (v128.const i16x8 16384 0 0 0 0 0 0 0) (v128.const i16x8 16384 0 0 0 0 0 0 0)))
  (func (export "f32x4_add") (result v128) (f32x4.add (v128.const f32x4 1.5 1.5 1.5 1.5) (v128.const f32x4 2.5 2.5 2.5 2.5))) ;; 4.0 x4
  (func (export "f32x4_sub") (result v128) (f32x4.sub (v128.const f32x4 5.5 5.5 5.5 5.5) (v128.const f32x4 2.5 2.5 2.5 2.5))) ;; 3.0 x4
  (func (export "f32x4_mul") (result v128) (f32x4.mul (v128.const f32x4 2.5 2.5 2.5 2.5) (v128.const f32x4 4.0 4.0 4.0 4.0))) ;; 10.0 x4
  (func (export "f32x4_div") (result v128) (f32x4.div (v128.const f32x4 10.0 10.0 10.0 10.0) (v128.const f32x4 4.0 4.0 4.0 4.0))) ;; 2.5 x4
  (func (export "f32x4_min") (result v128) (f32x4.min (v128.const f32x4 3.0 3.0 3.0 3.0) (v128.const f32x4 5.0 5.0 5.0 5.0))) ;; 3.0 x4
  (func (export "f32x4_max") (result v128) (f32x4.max (v128.const f32x4 3.0 3.0 3.0 3.0) (v128.const f32x4 5.0 5.0 5.0 5.0))) ;; 5.0 x4
  (func (export "f32x4_pmin") (result v128) (f32x4.pmin (v128.const f32x4 3.0 3.0 3.0 3.0) (v128.const f32x4 5.0 5.0 5.0 5.0))) ;; 3.0 x4
  (func (export "f32x4_pmax") (result v128) (f32x4.pmax (v128.const f32x4 3.0 3.0 3.0 3.0) (v128.const f32x4 5.0 5.0 5.0 5.0))) ;; 5.0 x4

  ;; -- VTESTOP / VRELOP --
  (func (export "i32x4_all_true") (result i32) (i32x4.all_true (v128.const i32x4 1 2 3 4)))  ;; 1
  (func (export "i32x4_eq") (result v128) (i32x4.eq (v128.const i32x4 1 2 3 4) (v128.const i32x4 1 0 3 0)))  ;; -1,0,-1,0
  (func (export "i32x4_ne") (result v128) (i32x4.ne (v128.const i32x4 1 2 3 4) (v128.const i32x4 1 0 3 0)))  ;; 0,-1,0,-1
  (func (export "i32x4_lt_s") (result v128) (i32x4.lt_s (v128.const i32x4 -1 2 -3 4) (v128.const i32x4 0 0 0 0)))
  (func (export "i32x4_lt_u") (result v128) (i32x4.lt_u (v128.const i32x4 1 2 3 4) (v128.const i32x4 5 5 5 5)))
  (func (export "i32x4_gt_s") (result v128) (i32x4.gt_s (v128.const i32x4 -1 2 -3 4) (v128.const i32x4 0 0 0 0)))
  (func (export "i32x4_gt_u") (result v128) (i32x4.gt_u (v128.const i32x4 5 5 5 5) (v128.const i32x4 1 2 3 4)))
  (func (export "i32x4_le_s") (result v128) (i32x4.le_s (v128.const i32x4 -1 2 -3 4) (v128.const i32x4 0 0 0 0)))
  (func (export "i32x4_le_u") (result v128) (i32x4.le_u (v128.const i32x4 1 2 3 4) (v128.const i32x4 1 2 3 4)))
  (func (export "i32x4_ge_s") (result v128) (i32x4.ge_s (v128.const i32x4 -1 2 -3 4) (v128.const i32x4 0 0 0 0)))
  (func (export "i32x4_ge_u") (result v128) (i32x4.ge_u (v128.const i32x4 1 2 3 4) (v128.const i32x4 1 2 3 4)))
  (func (export "f32x4_eq") (result v128) (f32x4.eq (v128.const f32x4 1.0 2.0 3.0 4.0) (v128.const f32x4 1.0 0.0 3.0 0.0)))
  (func (export "f32x4_ne") (result v128) (f32x4.ne (v128.const f32x4 1.0 2.0 3.0 4.0) (v128.const f32x4 1.0 0.0 3.0 0.0)))
  (func (export "f32x4_lt") (result v128) (f32x4.lt (v128.const f32x4 1.0 2.0 3.0 4.0) (v128.const f32x4 5.0 5.0 5.0 5.0)))
  (func (export "f32x4_gt") (result v128) (f32x4.gt (v128.const f32x4 5.0 5.0 5.0 5.0) (v128.const f32x4 1.0 2.0 3.0 4.0)))
  (func (export "f32x4_le") (result v128) (f32x4.le (v128.const f32x4 1.0 2.0 3.0 4.0) (v128.const f32x4 1.0 2.0 3.0 4.0)))
  (func (export "f32x4_ge") (result v128) (f32x4.ge (v128.const f32x4 1.0 2.0 3.0 4.0) (v128.const f32x4 1.0 2.0 3.0 4.0)))

  ;; -- VSHIFTOP / VBITMASK / VSWIZZLE / VSHUFFLE / VSPLAT --
  (func (export "i32x4_shl") (result v128) (i32x4.shl (v128.const i32x4 1 1 1 1) (i32.const 4)))       ;; 16 x4
  (func (export "i32x4_shr_s") (result v128) (i32x4.shr_s (v128.const i32x4 -16 -16 -16 -16) (i32.const 2))) ;; -4 x4
  (func (export "i32x4_shr_u") (result v128) (i32x4.shr_u (v128.const i32x4 -16 -16 -16 -16) (i32.const 2))) ;; 1073741820 x4
  (func (export "i32x4_bitmask") (result i32) (i32x4.bitmask (v128.const i32x4 -1 0 -1 0)))  ;; 0b0101 = 5
  (func (export "i8x16_swizzle") (result v128)
    (i8x16.swizzle (v128.const i8x16 10 20 30 40 50 60 70 80 90 100 110 120 130 140 150 160)
                    (v128.const i8x16 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0)))  ;; picks lanes 1,0,1,0,...
  (func (export "i8x16_shuffle") (result v128)
    (i8x16.shuffle 0 1 2 3 16 17 18 19 4 5 6 7 20 21 22 23
      (v128.const i8x16 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16)
      (v128.const i8x16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32)))
  (func (export "i32x4_splat") (result v128) (i32x4.splat (i32.const 7)))    ;; 7,7,7,7
  (func (export "i8x16_splat") (result v128) (i8x16.splat (i32.const 7)))    ;; 7 x16 (packtype: unpacks to i32)
  (func (export "f32x4_splat") (result v128) (f32x4.splat (f32.const 7.0)))  ;; 7.0 x4

  ;; -- VEXTRACT_LANE / VREPLACE_LANE (numtype form, and packtype form with sx) --
  (func (export "i32x4_extract_lane") (result i32) (i32x4.extract_lane 2 (v128.const i32x4 10 20 30 40))) ;; 30
  (func (export "i8x16_extract_lane_s") (result i32)
    (i8x16.extract_lane_s 0 (v128.const i8x16 0xFF 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))) ;; -1
  (func (export "i8x16_extract_lane_u") (result i32)
    (i8x16.extract_lane_u 0 (v128.const i8x16 0xFF 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))) ;; 255
  (func (export "i32x4_replace_lane") (result v128)
    (i32x4.replace_lane 1 (v128.const i32x4 1 2 3 4) (i32.const 99)))  ;; 1,99,3,4
  (func (export "i8x16_replace_lane") (result v128)
    (i8x16.replace_lane 0 (v128.const i8x16 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16) (i32.const 99)))

  ;; -- VEXTUNOP / VEXTBINOP / VNARROW --
  (func (export "i16x8_extadd_pairwise_i8x16_s") (result v128)
    (i16x8.extadd_pairwise_i8x16_s (v128.const i8x16 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16))) ;; 3,7,11,15,19,23,27,31
  (func (export "i16x8_extadd_pairwise_i8x16_u") (result v128)
    (i16x8.extadd_pairwise_i8x16_u (v128.const i8x16 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16)))
  (func (export "i16x8_extmul_low_i8x16_s") (result v128)
    (i16x8.extmul_low_i8x16_s (v128.const i8x16 2 2 2 2 2 2 2 2 0 0 0 0 0 0 0 0)
                               (v128.const i8x16 3 3 3 3 3 3 3 3 0 0 0 0 0 0 0 0))) ;; 6 x8 (low half)
  (func (export "i16x8_extmul_high_i8x16_u") (result v128)
    (i16x8.extmul_high_i8x16_u (v128.const i8x16 0 0 0 0 0 0 0 0 2 2 2 2 2 2 2 2)
                                (v128.const i8x16 0 0 0 0 0 0 0 0 3 3 3 3 3 3 3 3))) ;; 6 x8 (high half)
  (func (export "i32x4_dot_i16x8_s") (result v128)
    (i32x4.dot_i16x8_s (v128.const i16x8 1 1 2 2 3 3 4 4) (v128.const i16x8 1 1 2 2 3 3 4 4))) ;; 2,8,18,32
  (func (export "i8x16_narrow_i16x8_s") (result v128)
    (i8x16.narrow_i16x8_s (v128.const i16x8 1 2 3 4 5 6 7 8) (v128.const i16x8 1 2 3 4 5 6 7 8)))
  (func (export "i8x16_narrow_i16x8_u") (result v128)
    (i8x16.narrow_i16x8_u (v128.const i16x8 1 2 3 4 5 6 7 8) (v128.const i16x8 1 2 3 4 5 6 7 8)))

  ;; -- VCVTOP: EXTEND half sx | TRUNC_SAT sx zero? | CONVERT half? sx | DEMOTE zero | PROMOTE LOW --
  (func (export "i16x8_extend_low_i8x16_s") (result v128)
    (i16x8.extend_low_i8x16_s (v128.const i8x16 -1 2 -3 4 5 6 7 8 9 10 11 12 13 14 15 16)))
  (func (export "i16x8_extend_high_i8x16_u") (result v128)
    (i16x8.extend_high_i8x16_u (v128.const i8x16 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16)))
  (func (export "i32x4_trunc_sat_f32x4_s") (result v128)
    (i32x4.trunc_sat_f32x4_s (v128.const f32x4 1.9 -1.9 1e20 -1e20)))
  (func (export "i32x4_trunc_sat_f32x4_u") (result v128)
    (i32x4.trunc_sat_f32x4_u (v128.const f32x4 1.9 0.0 1e20 -5.0)))
  (func (export "i32x4_trunc_sat_f64x2_s_zero") (result v128)
    (i32x4.trunc_sat_f64x2_s_zero (v128.const f64x2 1.9 -1.9)))
  (func (export "i32x4_trunc_sat_f64x2_u_zero") (result v128)
    (i32x4.trunc_sat_f64x2_u_zero (v128.const f64x2 1.9 0.0)))
  (func (export "f32x4_convert_i32x4_s") (result v128) (f32x4.convert_i32x4_s (v128.const i32x4 -1 2 -3 4)))
  (func (export "f32x4_convert_i32x4_u") (result v128) (f32x4.convert_i32x4_u (v128.const i32x4 1 2 3 4)))
  (func (export "f64x2_convert_low_i32x4_s") (result v128) (f64x2.convert_low_i32x4_s (v128.const i32x4 -1 2 0 0)))
  (func (export "f64x2_convert_low_i32x4_u") (result v128) (f64x2.convert_low_i32x4_u (v128.const i32x4 1 2 0 0)))
  (func (export "f32x4_demote_f64x2_zero") (result v128) (f32x4.demote_f64x2_zero (v128.const f64x2 1.5 2.5)))
  (func (export "f64x2_promote_low_f32x4") (result v128) (f64x2.promote_low_f32x4 (v128.const f32x4 1.5 2.5 0.0 0.0)))

  ;; -- a couple of i64x2 / f64x2 examples, to show every shape (not just i32x4/f32x4) --
  (func (export "i64x2_add") (result v128) (i64x2.add (v128.const i64x2 1 2) (v128.const i64x2 10 10)))
  (func (export "i64x2_eq") (result v128) (i64x2.eq (v128.const i64x2 1 2) (v128.const i64x2 1 0)))
  (func (export "i64x2_shl") (result v128) (i64x2.shl (v128.const i64x2 1 1) (i32.const 4)))
  (func (export "f64x2_add") (result v128) (f64x2.add (v128.const f64x2 1.5 1.5) (v128.const f64x2 2.5 2.5)))
  (func (export "f64x2_sqrt") (result v128) (f64x2.sqrt (v128.const f64x2 4.0 9.0)))


  ;; ============================================================================
  ;; REFERENCE INSTRUCTIONS -- instr/ref: REF.NULL, REF.FUNC, REF.IS_NULL
  ;; ============================================================================
  (func (export "ref_null_func_is_null") (result i32) (ref.is_null (ref.null func)))     ;; 1
  (func (export "ref_null_extern_is_null") (result i32) (ref.is_null (ref.null extern)))  ;; 1
  (func (export "ref_func_is_null") (result i32) (ref.is_null (ref.func $sq)))            ;; 0 (a real ref)


  ;; ============================================================================
  ;; PARAMETRIC INSTRUCTIONS -- instr/parametric: NOP, UNREACHABLE, DROP,
  ;; SELECT (implicit and explicit-typed forms)
  ;; ============================================================================
  (func (export "op_nop") (result i32) (nop) (i32.const 1))     ;; 1 (nop is a true no-op)
  (func (export "op_drop") (result i32) (i32.const 999) (drop) (i32.const 1)) ;; 1
  (func (export "op_select_implicit") (result i32)
    (select (i32.const 10) (i32.const 20) (i32.const 1)))       ;; 10 (condition nonzero -> first operand)
  (func (export "op_select_explicit") (result f32)
    (select (result f32) (f32.const 1.5) (f32.const 2.5) (i32.const 0))) ;; 2.5 (condition zero -> second operand)


  ;; ============================================================================
  ;; LOCAL / GLOBAL INSTRUCTIONS
  ;; ============================================================================
  (func (export "local_get_set_tee") (result i32)
    (local $x i32) (local $y i32)
    (local.set $x (i32.const 5))
    (local.tee $y (i32.add (local.get $x) (i32.const 1)))  ;; sets $y=6, leaves 6 on the stack
    (drop)
    (local.get $y))                                         ;; 6

  (func (export "global_get_set") (result i32)
    (global.set $g_count (i32.add (global.get $g_count) (i32.const 41)))
    (global.get $g_count))                                  ;; 1 (from $start_fn) + 41 = 42


  ;; ============================================================================
  ;; TABLE INSTRUCTIONS -- instr/table, instr/elem
  ;; ============================================================================
  (func (export "table_size") (result i32) (table.size $t0))      ;; 3 (declared min size)
  (func (export "table_get_is_null") (result i32) (ref.is_null (table.get $t0 (i32.const 2)))) ;; 1 (slot 2 unset)
  (func (export "table_set_then_get") (result i32)
    (table.set $t0 (i32.const 2) (global.get $g_ref_mulby))
    (call_indirect $t0 (type $unary_i32) (i32.const 6) (i32.const 2)))  ;; $mulby(6) = 60
  (func (export "table_grow") (result i32) (table.grow $t0 (ref.null func) (i32.const 2))) ;; 3 (old size)
  (func (export "table_fill") (result i32)
    (table.fill $t2 (i32.const 0) (global.get $g_ref_sq) (i32.const 3))
    (call_indirect $t2 (type $unary_i32) (i32.const 9) (i32.const 0))) ;; $sq(9) = 81
  (func (export "table_copy") (result i32)
    (table.copy $t2 $t0 (i32.const 0) (i32.const 0) (i32.const 1))    ;; t2[0] := t0[0] (=$sq)
    (call_indirect $t2 (type $unary_i32) (i32.const 5) (i32.const 0))) ;; $sq(5) = 25
  (func (export "table_init_then_elem_drop") (result i32)
    (table.init $t2 $e_passive (i32.const 2) (i32.const 0) (i32.const 1)) ;; t2[2] := elem($e_passive)[0] (=$sq)
    (elem.drop $e_passive)
    (call_indirect $t2 (type $unary_i32) (i32.const 4) (i32.const 2)))    ;; $sq(4) = 16

  ;; call_indirect on the actively-initialized $t0 (index 0 = $sq, index 1 = $addone)
  (func (export "call_indirect_sq") (result i32)
    (call_indirect $t0 (type $unary_i32) (i32.const 7) (i32.const 0)))    ;; $sq(7) = 49
  (func (export "call_indirect_addone") (result i32)
    (call_indirect $t0 (type $unary_i32) (i32.const 7) (i32.const 1)))    ;; $addone(7) = 8


  ;; ============================================================================
  ;; MEMORY INSTRUCTIONS -- instr/memory, instr/data
  ;; ============================================================================

  ;; plain + packed loads/stores (the "val" and "pack" forms of LOAD/STORE)
  (func (export "mem_load_active_data") (result i32) (i32.load8_u (i32.const 0)))  ;; 'H' = 72
  (func (export "mem_store_then_load") (result i32)
    (i32.store (i32.const 100) (i32.const 0x11223344))
    (i32.load (i32.const 100)))                                                    ;; 0x11223344
  (func (export "mem_store8_then_load8_s") (result i32)
    (i32.store8 (i32.const 104) (i32.const 0xFF))
    (i32.load8_s (i32.const 104)))                                                 ;; -1
  (func (export "mem_store16_then_load16_u") (result i32)
    (i32.store16 (i32.const 108) (i32.const 0xFFFF))
    (i32.load16_u (i32.const 108)))                                                ;; 65535
  (func (export "mem_i64_store32_then_load32_u") (result i64)
    (i64.store32 (i32.const 112) (i64.const 0xFFFFFFFF))
    (i64.load32_u (i32.const 112)))                                                ;; 4294967295

  ;; vector loads: plain, packed-with-sx, splat, zero; and vector store
  (func (export "mem_v128_store_then_load") (result v128)
    (v128.store (i32.const 128) (v128.const i32x4 1 2 3 4))
    (v128.load (i32.const 128)))
  (func (export "mem_v128_load8x8_s") (result v128)
    (i32.store8 (i32.const 144) (i32.const 0xFF))
    (v128.load8x8_s (i32.const 144)))
  (func (export "mem_v128_load32_splat") (result v128)
    (i32.store (i32.const 160) (i32.const 7))
    (v128.load32_splat (i32.const 160)))                                           ;; 7,7,7,7
  (func (export "mem_v128_load32_zero") (result v128)
    (i32.store (i32.const 164) (i32.const 9))
    (v128.load32_zero (i32.const 164)))                                            ;; 9,0,0,0
  (func (export "mem_v128_load_lane_store_lane") (result v128)
    (v128.store (i32.const 176) (v128.const i32x4 0 0 0 0))
    (v128.store32_lane 0 (i32.const 176) (v128.const i32x4 42 0 0 0))
    (v128.load32_lane 0 (i32.const 176) (v128.const i32x4 0 0 0 0)))               ;; 42,0,0,0

  ;; memory.size / memory.grow
  (func (export "mem_size") (result i32) (memory.size))          ;; 1 (declared min pages)
  (func (export "mem_grow") (result i32) (memory.grow (i32.const 1))) ;; 1 (old size, grows to 2)

  ;; memory.fill / memory.copy / memory.init / data.drop
  (func (export "mem_fill") (result i32)
    (memory.fill (i32.const 200) (i32.const 0x41) (i32.const 4))
    (i32.load (i32.const 200)))                                  ;; 0x41414141
  (func (export "mem_copy") (result i32)
    (memory.copy (i32.const 300) (i32.const 200) (i32.const 4))
    (i32.load (i32.const 300)))                                  ;; 0x41414141 (copied)
  (func (export "mem_init_passive_data") (result i32)
    (memory.init $d_passive (i32.const 400) (i32.const 0) (i32.const 13))
    (i32.load8_u (i32.const 400)))                                ;; 'P' = 80
  (func (export "mem_data_drop_ok") (result i32)
    (memory.init $d_passive (i32.const 420) (i32.const 0) (i32.const 4))
    (data.drop $d_passive)
    (i32.load8_u (i32.const 420)))                                ;; 'P' = 80 (drop doesn't undo prior init)


  ;; ============================================================================
  ;; CONTROL INSTRUCTIONS -- instr/block, instr/br, instr/call
  ;; ============================================================================

  ;; BLOCK (both blocktype forms: _RESULT and _IDX)
  (func (export "ctrl_block_result") (result i32)
    (block (result i32) (i32.const 42)))
  (func (export "ctrl_block_typeidx") (result i32)
    (i32.const 6)
    (block (type $unary_i32) (call $sq)))     ;; blocktype _IDX: block consumes the 6 as its param -- 36

  ;; LOOP (iterates via br to itself, exits via br_if)
  (func (export "ctrl_loop_sum_1_to_5") (result i32)
    (local $i i32) (local $acc i32)
    (local.set $i (i32.const 1))
    (block $exit
      (loop $continue
        (local.set $acc (i32.add (local.get $acc) (local.get $i)))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br_if $exit (i32.gt_s (local.get $i) (i32.const 5)))
        (br $continue)))
    (local.get $acc))                                        ;; 1+2+3+4+5 = 15

  ;; IF / ELSE
  (func (export "ctrl_if_else_true") (result i32)
    (if (result i32) (i32.const 1) (then (i32.const 111)) (else (i32.const 222)))) ;; 111
  (func (export "ctrl_if_else_false") (result i32)
    (if (result i32) (i32.const 0) (then (i32.const 111)) (else (i32.const 222)))) ;; 222

  ;; BR / BR_IF / BR_TABLE
  (func (export "ctrl_br") (result i32)
    (block $b (result i32) (br $b (i32.const 7)) (i32.const 0))) ;; 7 (unreachable const skipped)
  (func (export "ctrl_br_if") (result i32)
    (block $b (result i32)
      (i32.const 99)
      (br_if $b (i32.const 1))))                               ;; 99 (branch taken, carries 99 out)
  (func (export "ctrl_br_table") (result i32)
    (block $default (result i32)
      (block $two (result i32)
        (block $one (result i32)
          (block $zero (result i32)
            (br_table $zero $one $two $default (i32.const 555) (i32.const 1)))
          (return (i32.const 1000)))    ;; $zero target, not taken
        (return (i32.const 2000)))      ;; $one target -- taken (index 1); 555 is discarded by this `return`
      (return (i32.const 3000))))       ;; $two target, not taken -- overall result: 2000

  ;; CALL / CALL_INDIRECT (call_indirect already shown above, table section) / RETURN
  (func (export "ctrl_call") (result i32) (call $sq (i32.const 8)))   ;; 64
  (func (export "ctrl_return") (result i32)
    (return (i32.const 5)) (i32.const 999))                   ;; 5 (early return)

  ;; UNREACHABLE -- this is the one demo that's *expected* to trap; that IS
  ;; correct behavior for this instruction. wasm-interp will report a trap,
  ;; not a value, when this export runs.
  (func (export "ctrl_unreachable_traps") (result i32)
    (unreachable))


  ;; ============================================================================
  ;; A genuinely-parameterized, multi-local, multi-import-using function, to
  ;; show `local` (parameters) and the imported `$log` function actually
  ;; being called with a real argument. Not zero-arg, so it's not covered by
  ;; --run-all-exports -- verify with:
  ;;   wasm-interp 1-syntax.wasm --dummy-import-func -r add_and_log -a i32:7 -a i32:8
  ;; ============================================================================
  (func (export "add_and_log") (param $a i32) (param $b i32) (result i32)
    (local $sum i32)
    (local.set $sum (i32.add (local.get $a) (local.get $b)))
    (call $log (local.get $sum))
    (drop)                              ;; $log has a result too; discard it
    (local.get $sum))
)

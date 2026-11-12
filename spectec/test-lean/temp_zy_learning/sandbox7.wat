;; ============================================================================
;; sandbox7.wat -- one exported function per feature that's NEW in Wasm 2.0
;; relative to 1.0 (the MVP), each one commented with exactly where that
;; feature is defined in specification/wasm-2.0/*.spectec.
;; ============================================================================

(module
  ;; --- 1. SIGN EXTENSION ---
  ;; 1-syntax.spectec:283  unop_(Inn) = CLZ | CTZ | POPCNT | EXTEND n
  ;; 1-syntax.spectec:307  side condition: EXTEND sx -- if $sizenn1 < $sizenn2
  ;; 3-numerics.spectec:56 def $extend__(M, N, sx, iN(M)) : iN(N)  -- the actual semantics
  (func (export "sign_extend8") (param $x i32) (result i32)
    (i32.extend8_s (local.get $x)))

  ;; --- 2. NON-TRAPPING FLOAT-TO-INT (saturating truncation) ---
  ;; 1-syntax.spectec:314  cvtop = ... | TRUNC_SAT sx  (vs. plain TRUNC, which traps)
  ;; 3-numerics.spectec:58 def $trunc_sat__(M, N, sx, fN(M)) : iN(N)?
  (func (export "trunc_sat_demo") (param $f f32) (result i32)
    (i32.trunc_sat_f32_s (local.get $f)))

  ;; --- 3. MULTI-VALUE (function results AND block types) ---
  ;; 1-syntax.spectec:146      resulttype = list(valtype)  -- a LIST, not at-most-one
  ;; 1-syntax.spectec:169      functype = resulttype -> resulttype
  ;; 1-syntax.spectec:403-405  blocktype's `_IDX typeidx` case: a block can carry a
  ;;                           full functype (params AND multiple results), not just
  ;;                           the single optional result 1.0 allowed
  (func (export "multi_value_demo") (param $x i32) (result i32 i32)
    local.get $x
    (block (param i32) (result i32 i32)
      local.get $x
      i32.const 1
      i32.add))

  ;; --- 4. REFERENCE TYPES ---
  ;; 1-syntax.spectec:135-136  reftype = FUNCREF | EXTERNREF
  ;; 1-syntax.spectec:479-481  REF.NULL reftype | REF.FUNC funcidx | REF.IS_NULL
  (func $target (result i32) (i32.const 99))
  (func (export "ref_ops_demo") (result i32 i32)
    (ref.is_null (ref.null func))     ;; a null ref really is null
    (ref.is_null (ref.func $target))) ;; a real function ref is not

  ;; --- 5. MULTIPLE TABLES + TABLE INSTRUCTIONS ---
  ;; 9-module.spectec:571      module = ... table* ...  -- a LIST of tables
  ;; 1-syntax.spectec:496-502  TABLE.GET / TABLE.SET / TABLE.SIZE / TABLE.GROW /
  ;;                           TABLE.FILL / TABLE.COPY / TABLE.INIT
  ;; 1-syntax.spectec:506      ELEM.DROP
  (table $t0 2 funcref)
  (table $t1 1 externref)
  (func (export "tables_demo") (param $er externref) (result i32 i32 i32)
    (table.set $t0 (i32.const 0) (ref.func $target))
    (table.set $t1 (i32.const 0) (local.get $er))
    (table.grow $t0 (ref.null func) (i32.const 1))       ;; returns OLD size: 2
    (table.size $t0)                                      ;; size after growth: 3
    (ref.is_null (table.get $t0 (i32.const 0))))          ;; holds $target: not null

  ;; --- 6. BULK MEMORY OPERATIONS ---
  ;; 1-syntax.spectec:519-521  MEMORY.FILL | MEMORY.COPY | MEMORY.INIT dataidx
  ;; 1-syntax.spectec:525      DATA.DROP dataidx
  (memory 1)
  (data $d1 "hello")  ;; PASSIVE segment (no offset given) -- exists purely to be
                       ;; memory.init'd on demand, unlike an active segment which
                       ;; is auto-copied once at instantiation (see $instantiate,
                       ;; a few turns back)
  (func (export "bulk_memory_demo") (result i32 i32 i32)
    (memory.init $d1 (i32.const 0) (i32.const 0) (i32.const 5))  ;; mem[0..5) = "hello"
    (data.drop $d1)                                               ;; segment no longer needed
    (memory.fill (i32.const 10) (i32.const 65) (i32.const 3))    ;; mem[10..13) = 'A' 'A' 'A'
    (memory.copy (i32.const 20) (i32.const 0) (i32.const 5))     ;; mem[20..25) = mem[0..5)
    (i32.load8_u (i32.const 0))    ;; 'h' = 104
    (i32.load8_u (i32.const 10))   ;; 'A' = 65
    (i32.load8_u (i32.const 20)))  ;; 'h' = 104, copied

  ;; --- 6b. BULK TABLE OPERATIONS (table.init / elem.drop) ---
  (elem $e1 func $target)  ;; PASSIVE elem segment, same idea as $d1 above
  (func (export "bulk_table_demo") (result i32)
    (table.init $t0 $e1 (i32.const 1) (i32.const 0) (i32.const 1))  ;; t0[1] = elem[0] = $target
    (elem.drop $e1)
    (ref.is_null (table.get $t0 (i32.const 1))))  ;; not null

  ;; --- 7. VECTOR (SIMD) INSTRUCTIONS ---
  ;; 1-syntax.spectec:129-130  vectype = V128
  ;; 1-syntax.spectec:452      VBINOP shape vbinop_(shape)
  ;; 1-syntax.spectec:461-464  VSPLAT / VEXTRACT_LANE / VREPLACE_LANE
  (func (export "simd_demo") (result i32)
    (i32x4.extract_lane 0
      (i32x4.add
        (v128.const i32x4 1 2 3 4)
        (v128.const i32x4 10 20 30 40))))  ;; lane 0: 1+10 = 11
)

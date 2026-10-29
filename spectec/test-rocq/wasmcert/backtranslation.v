(* Translation from WasmCert-Coq (theory Wasm, v2.2.0) back to the
   SpecTec-generated Wasm 2.0 semantics (WasmSpectec.wasm): the inverse of
   [translation.v].

   The translation is partial ([option]-valued).  It fails on
   - WasmCert features that SpecTec's Wasm 2.0 does not have: tail calls
     ([BI_return_call], [BI_return_call_indirect], [AI_return_invoke]) and host
     functions ([FC_func_host]);
   - values that SpecTec's well-formedness rules out: indices and limits that do
     not fit in a u32, lane indices that do not fit in a u8, ill-typed operators
     (e.g. an integer operator at a float type), v128 values that are not 16
     bytes, names that are not valid UTF-8, memories whose fill byte is not 0.
   Whatever it produces is well-formed and is mapped back to its input by
   [translation.v] (see [backtranslation_props.v]).

   Its only hole is [vec_instr], the decoder of WasmCert's SIMD opcodes, the
   counterpart of [vec_code]: it is a parameter of this file, not an axiom. *)

From Stdlib Require Import NArith ZArith List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From compcert Require Integers Memdata.
From Wasm Require Import datatypes datatypes_properties operations.
From Wasm Require memory_list.
From WasmSpectec Require wasm.
From WasmCertBridge Require fN_flocq.
From WasmCertBridge Require Import translation.

Module S := WasmSpectec.wasm.
Module FL := WasmCertBridge.fN_flocq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope N_scope with num.

(** * Option helpers *)

Notation "'let?' x ':=' e1 'in' e2" :=
  (match e1 with Some x => e2 | None => None end)
  (at level 200, x ident, e1 at level 100, e2 at level 200).

Section OList.
Context {A B : Type} (f : A -> option B).

(* [f] on every element, failing if it fails anywhere. *)
Fixpoint olist (l : seq A) : option (seq B) :=
  match l with
  | [::] => Some [::]
  | x :: l' =>
      match f x with
      | Some y => match olist l' with Some ys => Some (y :: ys) | None => None end
      | None => None
      end
  end.

Definition oopt (o : option A) : option (option B) :=
  match o with
  | Some x => option_map Some (f x)
  | None => Some None
  end.

End OList.

Definition guard {A : Type} (b : bool) (x : option A) : option A := if b then x else None.

Section BackTranslation.

Context `{hfc : host_function_class}.

(* Decoder of WasmCert's SIMD opcodes, used on [BI_vunop], [BI_vbinop],
   [BI_vternop], [BI_vtestop] and [BI_vshiftop]; see [vec_code]. *)
Variable vec_instr : basic_instruction -> option S.instr.

(** * Types *)

Definition of_numtype (t : number_type) : S.numtype :=
  match t with
  | T_i32 => S.I32
  | T_i64 => S.I64
  | T_f32 => S.F32
  | T_f64 => S.F64
  end.

Definition of_Inn (t : number_type) : option S.Inn :=
  match t with
  | T_i32 => Some S.Inn_I32
  | T_i64 => Some S.Inn_I64
  | _ => None
  end.

Definition of_Fnn (t : number_type) : option S.Fnn :=
  match t with
  | T_f32 => Some S.Fnn_F32
  | T_f64 => Some S.Fnn_F64
  | _ => None
  end.

Definition of_reftype (t : reference_type) : S.reftype :=
  match t with
  | T_funcref => S.FUNCREF
  | T_externref => S.EXTERNREF
  end.

Definition of_valtype (t : value_type) : S.valtype :=
  match t with
  | T_num T_i32 => S.valtype_I32
  | T_num T_i64 => S.valtype_I64
  | T_num T_f32 => S.valtype_F32
  | T_num T_f64 => S.valtype_F64
  | T_vec T_v128 => S.valtype_V128
  | T_ref T_funcref => S.valtype_FUNCREF
  | T_ref T_externref => S.valtype_EXTERNREF
  | T_bot => S.BOT
  end.

Definition of_resulttype (ts : result_type) : S.resulttype := S.mk_list _ (map of_valtype ts).

Definition of_functype (ft : function_type) : S.functype :=
  match ft with
  | Tf t1 t2 => S.mk_functype (of_resulttype t1) (of_resulttype t2)
  end.

Definition u32_ok (n : N) : bool := (n <? 4294967296)%num.

Definition of_u32 (n : N) : option S.uN := guard (u32_ok n) (Some (S.mk_uN n)).

Definition of_u8 (n : N) : option S.uN := guard (n <? 256)%num (Some (S.mk_uN n)).

Definition of_limits (l : limits) : option S.limits :=
  let? mn := of_u32 (lim_min l) in
  let? mx := oopt of_u32 (lim_max l) in
  Some (S.mk_limits mn mx).

Definition of_mut (m : mutability) : option S.r_MUT :=
  match m with
  | MUT_var => Some S.MUT
  | MUT_const => None
  end.

Definition of_globaltype (g : global_type) : S.globaltype :=
  S.mk_globaltype (of_mut (tg_mut g)) (of_valtype (tg_t g)).

Definition of_tabletype (tab : table_type) : option S.tabletype :=
  let? l := of_limits (tt_limits tab) in
  Some (S.mk_tabletype l (of_reftype (tt_elem_type tab))).

Definition of_memtype (mt : memory_type) : option S.memtype :=
  option_map S.PAGE (of_limits mt).

Definition of_externtype (xt : extern_type) : option S.externtype :=
  match xt with
  | ET_func ft => Some (S.FUNC (of_functype ft))
  | ET_global gt => Some (S.GLOBAL (of_globaltype gt))
  | ET_table tab => option_map S.TABLE (of_tabletype tab)
  | ET_mem mt => option_map S.MEM (of_memtype mt)
  end.

(** * Values *)

Definition of_i32 (i : i32) : S.uN := S.mk_uN (Z.to_N (Wasm_int.Int32.unsigned i)).
Definition of_i64 (i : i64) : S.uN := S.mk_uN (Z.to_N (Wasm_int.Int64.unsigned i)).
Definition of_f32 (f : f32) : S.fN := FL.flocq_to_fN 32%num f.
Definition of_f64 (f : f64) : S.fN := FL.flocq_to_fN 64%num f.

Definition of_num (v : value_num) : S.num_ :=
  match v with
  | VAL_int32 i => S.mk_num__0 S.Inn_I32 (of_i32 i)
  | VAL_int64 i => S.mk_num__0 S.Inn_I64 (of_i64 i)
  | VAL_float32 f => S.mk_num__1 S.Fnn_F32 (of_f32 f)
  | VAL_float64 f => S.mk_num__1 S.Fnn_F64 (of_f64 f)
  end.

(* A v128 is read back from its 16 little-endian bytes. *)
Definition of_v128 (v : SIMD.v128) : option S.vec_ :=
  guard (Nat.eqb (size v) 16) (Some (S.mk_uN (Z.to_N (Memdata.decode_int v)))).

Definition of_vec (v : value_vec) : option S.vec_ :=
  match v with
  | VAL_vec128 v => of_v128 v
  end.

Definition of_ref (r : value_ref) : S.ref :=
  match r with
  | VAL_ref_null t => S.ref_REF_NULL (of_reftype t)
  | VAL_ref_func a => S.REF_FUNC_ADDR a
  | VAL_ref_extern a => S.REF_HOST_ADDR a
  end.

Definition of_val (v : value) : option S.val :=
  match v with
  | VAL_num c => Some (S.val_CONST (of_numtype (typeof_num c)) (of_num c))
  | VAL_vec c => option_map (S.val_VCONST S.V128) (of_vec c)
  | VAL_ref (VAL_ref_null t) => Some (S.val_REF_NULL (of_reftype t))
  | VAL_ref (VAL_ref_func a) => Some (S.val_REF_FUNC_ADDR a)
  | VAL_ref (VAL_ref_extern a) => Some (S.val_REF_HOST_ADDR a)
  end.

(** * Operators *)

Definition of_sx (s : sx) : S.sx :=
  match s with
  | SX_U => S.U
  | SX_S => S.res_S
  end.

Definition of_unop (t : number_type) (op : unop) : option S.unop_ :=
  match op with
  | Unop_i o =>
      let? inn := of_Inn t in
      Some (S.mk_unop__0 inn match o with
                             | UOI_clz => S.CLZ
                             | UOI_ctz => S.CTZ
                             | UOI_popcnt => S.POPCNT
                             end)
  | Unop_extend n =>
      let? inn := of_Inn t in
      Some (S.mk_unop__0 inn (S.EXTEND n))
  | Unop_f o =>
      let? fnn := of_Fnn t in
      Some (S.mk_unop__1 fnn match o with
                             | UOF_abs => S.ABS
                             | UOF_neg => S.unop_Fnn_NEG
                             | UOF_sqrt => S.SQRT
                             | UOF_ceil => S.CEIL
                             | UOF_floor => S.FLOOR
                             | UOF_trunc => S.TRUNC
                             | UOF_nearest => S.NEAREST
                             end)
  end.

Definition of_binop (t : number_type) (op : binop) : option S.binop_ :=
  match op with
  | Binop_i o =>
      let? inn := of_Inn t in
      Some (S.mk_binop__0 inn match o with
                              | BOI_add => S.ADD
                              | BOI_sub => S.SUB
                              | BOI_mul => S.MUL
                              | BOI_div s => S.DIV (of_sx s)
                              | BOI_rem s => S.REM (of_sx s)
                              | BOI_and => S.AND
                              | BOI_or => S.OR
                              | BOI_xor => S.XOR
                              | BOI_shl => S.SHL
                              | BOI_shr s => S.SHR (of_sx s)
                              | BOI_rotl => S.ROTL
                              | BOI_rotr => S.ROTR
                              end)
  | Binop_f o =>
      let? fnn := of_Fnn t in
      Some (S.mk_binop__1 fnn match o with
                              | BOF_add => S.binop_Fnn_ADD
                              | BOF_sub => S.binop_Fnn_SUB
                              | BOF_mul => S.binop_Fnn_MUL
                              | BOF_div => S.binop_Fnn_DIV
                              | BOF_min => S.MIN
                              | BOF_max => S.MAX
                              | BOF_copysign => S.COPYSIGN
                              end)
  end.

Definition of_testop (t : number_type) (op : testop) : option S.testop_ :=
  let? inn := of_Inn t in
  Some (S.mk_testop__0 inn S.EQZ).

Definition of_relop (t : number_type) (op : relop) : option S.relop_ :=
  match op with
  | Relop_i o =>
      let? inn := of_Inn t in
      Some (S.mk_relop__0 inn match o with
                              | ROI_eq => S.EQ
                              | ROI_ne => S.NE
                              | ROI_lt s => S.LT (of_sx s)
                              | ROI_gt s => S.GT (of_sx s)
                              | ROI_le s => S.LE (of_sx s)
                              | ROI_ge s => S.GE (of_sx s)
                              end)
  | Relop_f o =>
      let? fnn := of_Fnn t in
      Some (S.mk_relop__1 fnn match o with
                              | ROF_eq => S.relop_Fnn_EQ
                              | ROF_ne => S.relop_Fnn_NE
                              | ROF_lt => S.relop_Fnn_LT
                              | ROF_gt => S.relop_Fnn_GT
                              | ROF_le => S.relop_Fnn_LE
                              | ROF_ge => S.relop_Fnn_GE
                              end)
  end.

(* [BI_cvtop t2 op t1 sx] converts from [t1] to [t2]; only the conversions of
   Wasm 2.0 are accepted. *)
Definition of_cvtop (t2 : number_type) (op : cvtop) (t1 : number_type) (s : option sx)
    : option S.cvtop__ :=
  match op, t1, t2, s with
  | CVO_extend, T_i32, T_i64, Some s => Some (S.mk_cvtop___0 S.Inn_I32 S.Inn_I64 (S.cvtop__Inn_1_Inn_2_EXTEND (of_sx s)))
  | CVO_wrap, T_i64, T_i32, None => Some (S.mk_cvtop___0 S.Inn_I64 S.Inn_I32 S.WRAP)
  | CVO_convert, _, _, Some s =>
      let? inn := of_Inn t1 in let? fnn := of_Fnn t2 in
      Some (S.mk_cvtop___1 inn fnn (S.CONVERT (of_sx s)))
  | CVO_reinterpret, T_i32, T_f32, None => Some (S.mk_cvtop___1 S.Inn_I32 S.Fnn_F32 S.REINTERPRET)
  | CVO_reinterpret, T_i64, T_f64, None => Some (S.mk_cvtop___1 S.Inn_I64 S.Fnn_F64 S.REINTERPRET)
  | CVO_trunc, _, _, Some s =>
      let? fnn := of_Fnn t1 in let? inn := of_Inn t2 in
      Some (S.mk_cvtop___2 fnn inn (S.cvtop__Fnn_1_Inn_2_TRUNC (of_sx s)))
  | CVO_trunc_sat, _, _, Some s =>
      let? fnn := of_Fnn t1 in let? inn := of_Inn t2 in
      Some (S.mk_cvtop___2 fnn inn (S.TRUNC_SAT (of_sx s)))
  | CVO_reinterpret, T_f32, T_i32, None => Some (S.mk_cvtop___2 S.Fnn_F32 S.Inn_I32 S.cvtop__Fnn_1_Inn_2_REINTERPRET)
  | CVO_reinterpret, T_f64, T_i64, None => Some (S.mk_cvtop___2 S.Fnn_F64 S.Inn_I64 S.cvtop__Fnn_1_Inn_2_REINTERPRET)
  | CVO_promote, T_f32, T_f64, None => Some (S.mk_cvtop___3 S.Fnn_F32 S.Fnn_F64 S.PROMOTE)
  | CVO_demote, T_f64, T_f32, None => Some (S.mk_cvtop___3 S.Fnn_F64 S.Fnn_F32 S.DEMOTE)
  | _, _, _, _ => None
  end.

Definition of_memarg (m : memarg) : option S.memarg :=
  let? a := of_u32 (memarg_align m) in
  let? o := of_u32 (memarg_offset m) in
  Some {| S.ALIGN := a; S.OFFSET := o |}.

Definition sz_ok (n : N) : bool := (n =? 8)%num || (n =? 16)%num || (n =? 32)%num || (n =? 64)%num.

Definition of_packtype (tp : packed_type) : N :=
  match tp with
  | Tp_i8 => 8
  | Tp_i16 => 16
  | Tp_i32 => 32
  end.

(* A packed access must be narrower than its integer type. *)
Definition of_pack (t : number_type) (tp : packed_type) : option S.Inn :=
  let? inn := of_Inn t in
  guard (of_packtype tp <? S.sizenn (S.numtype_Inn inn))%num (Some inn).

Definition of_loadop (t : number_type) (lo : option (packed_type * sx)) : option (option S.loadop_) :=
  match lo with
  | None => Some None
  | Some (tp, s) =>
      let? inn := of_pack t tp in
      Some (Some (S.mk_loadop__0 inn (S.mk_loadop_Inn (S.mk_sz (of_packtype tp)) (of_sx s))))
  end.

Definition of_storeop (t : number_type) (so : option packed_type) : option (option S.sz) :=
  match so with
  | None => Some None
  | Some tp =>
      option_map (fun _ => Some (S.mk_sz (of_packtype tp))) (of_pack t tp)
  end.

Definition of_vloadop (lv : load_vec_arg) : option (option S.vloadop_) :=
  match lv with
  | LVA_none => Some None
  | LVA_extend (n, m) s =>
      guard (sz_ok n && (n * m =? 64)%num && (1 <? m)%num) (Some (Some (S.SHAPEX_ (S.mk_sz n) m (of_sx s))))
  | LVA_splat w => guard (sz_ok w) (Some (Some (S.SPLAT (S.mk_sz w))))
  | LVA_zero w => guard (sz_ok w && (32 <=? w)%num) (Some (Some (S.vloadop__ZERO (S.mk_sz w))))
  end.

Definition of_blocktype (bt : block_type) : option S.blocktype :=
  match bt with
  | BT_valtype t => Some (S._RESULT (option_map of_valtype t))
  | BT_id x => option_map S._IDX (of_u32 x)
  end.

Definition of_shape (sh : vshape) : S.shape :=
  match sh with
  | VS_i VSI_8_16 => S.X S.lanetype_I8 (S.mk_dim 16)
  | VS_i VSI_16_8 => S.X S.lanetype_I16 (S.mk_dim 8)
  | VS_i VSI_32_4 => S.X S.lanetype_I32 (S.mk_dim 4)
  | VS_i VSI_64_2 => S.X S.lanetype_I64 (S.mk_dim 2)
  | VS_f VSF_32_4 => S.X S.lanetype_F32 (S.mk_dim 4)
  | VS_f VSF_64_2 => S.X S.lanetype_F64 (S.mk_dim 2)
  end.

(* Lanes narrower than 32 bits are extracted with a signedness, the others
   without. *)
Definition packed_shape (sh : vshape) : bool :=
  match sh with
  | VS_i VSI_8_16 | VS_i VSI_16_8 => true
  | _ => false
  end.

(** * Instructions *)

Fixpoint of_instr (b : basic_instruction) : option S.instr :=
  match b with
  | BI_nop => Some S.NOP
  | BI_unreachable => Some S.UNREACHABLE
  | BI_drop => Some S.DROP
  | BI_select ts => Some (S.SELECT (option_map (map of_valtype) ts))
  | BI_block bt es =>
      let? bt' := of_blocktype bt in let? es' := olist of_instr es in
      Some (S.BLOCK bt' es')
  | BI_loop bt es =>
      let? bt' := of_blocktype bt in let? es' := olist of_instr es in
      Some (S.LOOP bt' es')
  | BI_if bt es1 es2 =>
      let? bt' := of_blocktype bt in
      let? es1' := olist of_instr es1 in let? es2' := olist of_instr es2 in
      Some (S.IFELSE bt' es1' es2')
  | BI_br l => option_map S.BR (of_u32 l)
  | BI_br_if l => option_map S.BR_IF (of_u32 l)
  | BI_br_table ls l =>
      let? ls' := olist of_u32 ls in let? l' := of_u32 l in Some (S.BR_TABLE ls' l')
  | BI_call x => option_map S.CALL (of_u32 x)
  | BI_call_indirect x y =>
      let? x' := of_u32 x in let? y' := of_u32 y in Some (S.CALL_INDIRECT x' y')
  | BI_return => Some S.RETURN
  | BI_return_call _ | BI_return_call_indirect _ _ => None
  | BI_const_num c => Some (S.CONST (of_numtype (typeof_num c)) (of_num c))
  | BI_unop t op => option_map (S.UNOP (of_numtype t)) (of_unop t op)
  | BI_binop t op => option_map (S.BINOP (of_numtype t)) (of_binop t op)
  | BI_testop t op => option_map (S.TESTOP (of_numtype t)) (of_testop t op)
  | BI_relop t op => option_map (S.RELOP (of_numtype t)) (of_relop t op)
  | BI_cvtop t2 op t1 s => option_map (S.CVTOP (of_numtype t2) (of_numtype t1)) (of_cvtop t2 op t1 s)
  | BI_const_vec c => option_map (S.VCONST S.V128) (of_vec c)
  | BI_vunop _ | BI_vbinop _ | BI_vternop _ | BI_vtestop _ | BI_vshiftop _ => vec_instr b
  | BI_splat_vec sh => Some (S.VSPLAT (of_shape sh))
  | BI_extract_vec sh s x =>
      guard (packed_shape sh == isSome s)
        (option_map (S.VEXTRACT_LANE (of_shape sh) (option_map of_sx s)) (of_u8 x))
  | BI_replace_vec sh x => option_map (S.VREPLACE_LANE (of_shape sh)) (of_u8 x)
  | BI_ref_null t => Some (S.REF_NULL (of_reftype t))
  | BI_ref_is_null => Some S.REF_IS_NULL
  | BI_ref_func x => option_map S.REF_FUNC (of_u32 x)
  | BI_local_get x => option_map S.LOCAL_GET (of_u32 x)
  | BI_local_set x => option_map S.LOCAL_SET (of_u32 x)
  | BI_local_tee x => option_map S.LOCAL_TEE (of_u32 x)
  | BI_global_get x => option_map S.GLOBAL_GET (of_u32 x)
  | BI_global_set x => option_map S.GLOBAL_SET (of_u32 x)
  | BI_table_get x => option_map S.TABLE_GET (of_u32 x)
  | BI_table_set x => option_map S.TABLE_SET (of_u32 x)
  | BI_table_size x => option_map S.TABLE_SIZE (of_u32 x)
  | BI_table_grow x => option_map S.TABLE_GROW (of_u32 x)
  | BI_table_fill x => option_map S.TABLE_FILL (of_u32 x)
  | BI_table_copy x y =>
      let? x' := of_u32 x in let? y' := of_u32 y in Some (S.TABLE_COPY x' y')
  | BI_table_init x y =>
      let? x' := of_u32 x in let? y' := of_u32 y in Some (S.TABLE_INIT x' y')
  | BI_elem_drop x => option_map S.ELEM_DROP (of_u32 x)
  | BI_load t lo m =>
      let? lo' := of_loadop t lo in let? m' := of_memarg m in
      Some (S.LOAD (of_numtype t) lo' m')
  | BI_store t so m =>
      let? so' := of_storeop t so in let? m' := of_memarg m in
      Some (S.STORE (of_numtype t) so' m')
  | BI_load_vec lv m =>
      let? lv' := of_vloadop lv in let? m' := of_memarg m in
      Some (S.VLOAD S.V128 lv' m')
  | BI_load_vec_lane w m x =>
      let? m' := of_memarg m in let? x' := of_u8 x in
      guard (sz_ok w) (Some (S.VLOAD_LANE S.V128 (S.mk_sz w) m' x'))
  | BI_store_vec m => option_map (S.VSTORE S.V128) (of_memarg m)
  | BI_store_vec_lane w m x =>
      let? m' := of_memarg m in let? x' := of_u8 x in
      guard (sz_ok w) (Some (S.VSTORE_LANE S.V128 (S.mk_sz w) m' x'))
  | BI_memory_size => Some S.MEMORY_SIZE
  | BI_memory_grow => Some S.MEMORY_GROW
  | BI_memory_fill => Some S.MEMORY_FILL
  | BI_memory_copy => Some S.MEMORY_COPY
  | BI_memory_init x => option_map S.MEMORY_INIT (of_u32 x)
  | BI_data_drop x => option_map S.DATA_DROP (of_u32 x)
  end.

Definition of_instrs (es : seq basic_instruction) : option (seq S.instr) := olist of_instr es.

(** * Runtime structures *)

Definition of_byte (b : byte) : S.byte := S.mk_byte (Z.to_N (Integers.Byte.unsigned b)).

Definition of_local (t : value_type) : S.local := S.LOCAL (of_valtype t).

Definition of_func (f : module_func) : option S.func :=
  let? x := of_u32 (modfunc_type f) in
  let? body := of_instrs (modfunc_body f) in
  Some (S.func_FUNC x (map of_local (modfunc_locals f)) body).

(* UTF-8 decoding, checked against the encoding [utf8_encode] of the forward
   translation.  SpecTec only encodes code points below 0x11000 in four bytes
   (see [S.fun_utf8]), so names with larger code points are rejected. *)
Fixpoint utf8_decode (bs : seq Byte.byte) : option (seq N) :=
  match bs with
  | [::] => Some [::]
  | b1 :: bs1 =>
      let n1 := Byte.to_N b1 in
      if (n1 <? 128)%num then option_map (cons n1) (utf8_decode bs1)
      else if (n1 <? 224)%num then
        match bs1 with
        | b2 :: bs2 =>
            option_map (cons ((n1 - 192) * 64 + (Byte.to_N b2 - 128))%num) (utf8_decode bs2)
        | _ => None
        end
      else if (n1 <? 240)%num then
        match bs1 with
        | b2 :: b3 :: bs3 =>
            option_map (cons ((n1 - 224) * 4096 + (Byte.to_N b2 - 128) * 64 + (Byte.to_N b3 - 128))%num)
              (utf8_decode bs3)
        | _ => None
        end
      else
        match bs1 with
        | b2 :: b3 :: b4 :: bs4 =>
            option_map (cons ((n1 - 240) * 262144 + (Byte.to_N b2 - 128) * 4096
                              + (Byte.to_N b3 - 128) * 64 + (Byte.to_N b4 - 128))%num)
              (utf8_decode bs4)
        | _ => None
        end
  end.

Definition char_ok (c : N) : bool :=
  (c <? 55296)%num || ((57344 <=? c)%num && (c <? 69632)%num).

Definition of_name (nm : name) : option S.name :=
  let? cs := utf8_decode nm in
  guard ((flatten (map utf8_encode cs) == nm) && all char_ok cs && (N.of_nat (size nm) <? 4294967296)%num)
    (Some (S.mk_name (map S.mk_char cs))).

Definition of_externaddr (v : extern_value) : S.externaddr :=
  match v with
  | EV_func a => S.externaddr_FUNC a
  | EV_global a => S.externaddr_GLOBAL a
  | EV_table a => S.externaddr_TABLE a
  | EV_mem a => S.externaddr_MEM a
  end.

Definition of_exportinst (e : exportinst) : option S.exportinst :=
  let? nm := of_name (exportinst_name e) in
  Some {| S.NAME := nm; S.ADDR := of_externaddr (exportinst_val e) |}.

Definition of_moduleinst (mi : moduleinst) : option S.moduleinst :=
  let? exps := olist of_exportinst (inst_exports mi) in
  Some {| S.TYPES := map of_functype (inst_types mi);
          S.FUNCS := inst_funcs mi;
          S.GLOBALS := inst_globals mi;
          S.TABLES := inst_tables mi;
          S.MEMS := inst_mems mi;
          S.ELEMS := inst_elems mi;
          S.DATAS := inst_datas mi;
          S.EXPORTS := exps |}.

Definition of_funcinst (fi : funcinst) : option S.funcinst :=
  match fi with
  | FC_func_native ft mi f =>
      let? mi' := of_moduleinst mi in let? f' := of_func f in
      Some {| S.funcinst_TYPE := of_functype ft; S.funcinst_MODULE := mi'; S.CODE := f' |}
  | FC_func_host _ _ => None
  end.

Definition of_globalinst (g : globalinst) : option S.globalinst :=
  let? v := of_val (g_val g) in
  Some {| S.globalinst_TYPE := of_globaltype (g_type g); S.VALUE := v |}.

Definition of_tableinst (ti : tableinst) : option S.tableinst :=
  let? tt := of_tabletype (tableinst_type ti) in
  Some {| S.tableinst_TYPE := tt; S.REFS := map of_ref (tableinst_elem ti) |}.

(* Memories are read back from their contents; the byte that fills them when
   they grow must be 0, as in the forward translation. *)
Definition of_meminst (m : meminst) : option S.meminst :=
  let? mt := of_memtype (meminst_type m) in
  let md : @mem_t memory_tr := meminst_data m in
  guard (Integers.Byte.eq (memory_list.ml_init md) Integers.Byte.zero)
    (Some {| S.meminst_TYPE := mt; S.BYTES := map of_byte (memory_list.ml_data md) |}).

Definition of_eleminst (ei : eleminst) : S.eleminst :=
  {| S.eleminst_TYPE := of_reftype (eleminst_type ei);
     S.eleminst_REFS := map of_ref (eleminst_elem ei) |}.

Definition of_datainst (di : datainst) : S.datainst :=
  {| S.datainst_BYTES := map of_byte (datainst_data di) |}.

Definition of_store (s : store_record) : option S.store :=
  let? fs := olist of_funcinst (s_funcs s) in
  let? gs := olist of_globalinst (s_globals s) in
  let? ts := olist of_tableinst (s_tables s) in
  let? ms := olist of_meminst (s_mems s) in
  Some {| S.store_FUNCS := fs; S.store_GLOBALS := gs; S.store_TABLES := ts;
          S.store_MEMS := ms; S.store_ELEMS := map of_eleminst (s_elems s);
          S.store_DATAS := map of_datainst (s_datas s) |}.

Definition of_frame (f : frame) : option S.frame :=
  let? vs := olist of_val (f_locs f) in
  let? mi := of_moduleinst (f_inst f) in
  Some {| S.LOCALS := vs; S.frame_MODULE := mi |}.

(** * Administrative instructions *)

Fixpoint of_admin (e : administrative_instruction) : option S.admininstr :=
  match e with
  | AI_basic b => option_map S.admininstr_instr (of_instr b)
  | AI_trap => Some S.admininstr_TRAP
  | AI_ref a => Some (S.admininstr_REF_FUNC_ADDR a)
  | AI_ref_extern a => Some (S.admininstr_REF_HOST_ADDR a)
  | AI_invoke a => Some (S.CALL_ADDR a)
  | AI_return_invoke _ => None
  | AI_label n cont es =>
      let? cont' := olist (fun e => match e with AI_basic b => of_instr b | _ => None end) cont in
      let? es' := olist of_admin es in
      Some (S.LABEL_ (N.of_nat n) cont' es')
  | AI_frame n f es =>
      let? f' := of_frame f in let? es' := olist of_admin es in
      Some (S.FRAME_ (N.of_nat n) f' es')
  end.

Definition of_admins (es : seq administrative_instruction) : option (seq S.admininstr) :=
  olist of_admin es.

Definition of_config (s : store_record) (f : frame) (es : seq administrative_instruction)
    : option S.config :=
  let? s' := of_store s in let? f' := of_frame f in let? es' := of_admins es in
  Some (S.mk_config (S.mk_state s' f') es').

(** * Typing contexts *)

(* [tc_refs] has no SpecTec counterpart and is dropped. *)
Definition of_context (C : t_context) : option S.context :=
  let? tabs := olist of_tabletype (tc_tables C) in
  let? mems := olist of_memtype (tc_mems C) in
  Some {| S.context_TYPES := map of_functype (tc_types C);
          S.context_FUNCS := map of_functype (tc_funcs C);
          S.context_GLOBALS := map of_globaltype (tc_globals C);
          S.context_TABLES := tabs;
          S.context_MEMS := mems;
          S.context_ELEMS := map of_reftype (tc_elems C);
          S.context_DATAS := map (fun _ => S.OK) (tc_datas C);
          S.context_LOCALS := map of_valtype (tc_locals C);
          S.LABELS := map of_resulttype (tc_labels C);
          S.context_RETURN := option_map of_resulttype (tc_return C) |}.

End BackTranslation.

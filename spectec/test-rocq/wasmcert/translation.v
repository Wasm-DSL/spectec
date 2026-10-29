(* Translation from the SpecTec-generated Wasm 2.0 semantics (WasmSpectec.wasm)
   to WasmCert-Coq (theory Wasm, v2.2.0).

   The translation is total.  Its holes are:
   - [vec_code]: the opcode WasmCert uses for a SpecTec vector instruction.
     WasmCert represents most SIMD instructions by their binary opcode and
     executes them through opaque parameters ([app_vunop_str], ...), so there
     is nothing to translate them against yet.
   Everything else (types, numbers, floats via Flocq, references, memories,
   stores, frames, instructions and administrative instructions) is concrete. *)

From Stdlib Require Import NArith ZArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From compcert Require Integers Memdata.
From Wasm Require Import datatypes operations opsem typing.
From Wasm Require memory_list.
From WasmSpectec Require wasm.
From WasmCertBridge Require fN_flocq.

Module S := WasmSpectec.wasm.
Module FL := WasmCertBridge.fN_flocq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* WasmCert's list-based memory instance ([memory_list.Memory_list]) is closed
   with Qed, so its [mem_t] does not compute.  This is the same instance, built
   transparently. *)
Definition memory_tr : Memory.
Proof.
  refine (@Build_Memory memory_list.memory_list memory_list.ml_make memory_list.ml_length
            memory_list.ml_lookup memory_list.ml_grow memory_list.ml_update
            _ _ _ _ _ _ _ _ _ _ _).
  - exact memory_list.ml_lookup_ib.
  - exact memory_list.ml_lookup_oob.
  - exact memory_list.ml_make_length.
  - exact memory_list.ml_make_lookup.
  - exact memory_list.ml_update_lookup.
  - exact memory_list.ml_update_lookup_ne.
  - by intros; eapply memory_list.ml_update_length; eauto.
  - exact memory_list.ml_update_ib.
  - exact memory_list.ml_update_oob.
  - exact memory_list.ml_grow_lookup.
  - exact memory_list.ml_grow_length.
Defined.

#[global] Existing Instance memory_tr.

(* mathcomp rebinds %N to nat; use %num for binary naturals. *)
Delimit Scope N_scope with num.

(** * Holes *)

(* Opcode of a SpecTec vector instruction in WasmCert's SIMD encoding.  Only
   used on vector instructions; see [tr_instr]. *)
Parameter vec_code : S.instr -> N.

Section Translation.

Context `{hfc : host_function_class}.

(** * Types *)

Definition tr_numtype (t : S.numtype) : number_type :=
  match t with
  | S.I32 => T_i32
  | S.I64 => T_i64
  | S.F32 => T_f32
  | S.F64 => T_f64
  end.

Definition tr_reftype (t : S.reftype) : reference_type :=
  match t with
  | S.FUNCREF => T_funcref
  | S.EXTERNREF => T_externref
  end.

Definition tr_valtype (t : S.valtype) : value_type :=
  match t with
  | S.valtype_I32 => T_num T_i32
  | S.valtype_I64 => T_num T_i64
  | S.valtype_F32 => T_num T_f32
  | S.valtype_F64 => T_num T_f64
  | S.valtype_V128 => T_vec T_v128
  | S.valtype_FUNCREF => T_ref T_funcref
  | S.valtype_EXTERNREF => T_ref T_externref
  | S.BOT => T_bot
  end.

Definition tr_resulttype (ts : S.resulttype) : result_type :=
  match ts with
  | S.mk_list l => map tr_valtype l
  end.

Definition tr_functype (ft : S.functype) : function_type :=
  match ft with
  | S.mk_functype t1 t2 => Tf (tr_resulttype t1) (tr_resulttype t2)
  end.

Definition tr_u32 (u : S.uN) : N := S.proj_uN_0 u.

Definition tr_limits (l : S.limits) : limits :=
  match l with
  | S.mk_limits mn mx => {| lim_min := tr_u32 mn; lim_max := option_map tr_u32 mx |}
  end.

Definition tr_mut (m : option S.r_MUT) : mutability :=
  match m with
  | Some _ => MUT_var
  | None => MUT_const
  end.

Definition tr_globaltype (g : S.globaltype) : global_type :=
  match g with
  | S.mk_globaltype m t => {| tg_mut := tr_mut m; tg_t := tr_valtype t |}
  end.

Definition tr_tabletype (tab : S.tabletype) : table_type :=
  match tab with
  | S.mk_tabletype l rt => {| tt_limits := tr_limits l; tt_elem_type := tr_reftype rt |}
  end.

Definition tr_memtype (mt : S.memtype) : memory_type :=
  match mt with
  | S.PAGE l => tr_limits l
  end.

Definition tr_externtype (xt : S.externtype) : extern_type :=
  match xt with
  | S.FUNC ft => ET_func (tr_functype ft)
  | S.GLOBAL gt => ET_global (tr_globaltype gt)
  | S.TABLE tab => ET_table (tr_tabletype tab)
  | S.MEM mt => ET_mem (tr_memtype mt)
  end.

(** * Values *)

Definition tr_i32 (u : S.uN) : i32 := Wasm_int.Int32.repr (Z.of_N (tr_u32 u)).
Definition tr_i64 (u : S.uN) : i64 := Wasm_int.Int64.repr (Z.of_N (tr_u32 u)).
Definition tr_f32 (f : S.fN) : f32 := FL.fN_to_flocq_total 32%num f.
Definition tr_f64 (f : S.fN) : f64 := FL.fN_to_flocq_total 64%num f.

Definition tr_num (c : S.num_) : value_num :=
  match c with
  | S.mk_num__0 S.Inn_I32 i => VAL_int32 (tr_i32 i)
  | S.mk_num__0 S.Inn_I64 i => VAL_int64 (tr_i64 i)
  | S.mk_num__1 S.Fnn_F32 f => VAL_float32 (tr_f32 f)
  | S.mk_num__1 S.Fnn_F64 f => VAL_float64 (tr_f64 f)
  end.

(* WasmCert stores a v128 as its 16 little-endian bytes. *)
Definition tr_v128 (c : S.vec_) : SIMD.v128 :=
  Memdata.encode_int 16%nat (Z.of_N (tr_u32 c)).

Definition tr_vec (c : S.vec_) : value_vec := VAL_vec128 (tr_v128 c).

Definition tr_ref (r : S.ref) : value_ref :=
  match r with
  | S.ref_REF_NULL rt => VAL_ref_null (tr_reftype rt)
  | S.REF_FUNC_ADDR a => VAL_ref_func a
  | S.REF_HOST_ADDR a => VAL_ref_extern a
  end.

Definition tr_val (v : S.val) : value :=
  match v with
  | S.val_CONST _ c => VAL_num (tr_num c)
  | S.val_VCONST _ c => VAL_vec (tr_vec c)
  | S.val_REF_NULL rt => VAL_ref (VAL_ref_null (tr_reftype rt))
  | S.val_REF_FUNC_ADDR a => VAL_ref (VAL_ref_func a)
  | S.val_REF_HOST_ADDR a => VAL_ref (VAL_ref_extern a)
  end.

(** * Operators *)

Definition tr_sx (s : S.sx) : sx :=
  match s with
  | S.U => SX_U
  | S.res_S => SX_S
  end.

Definition tr_unop (op : S.unop_) : unop :=
  match op with
  | S.mk_unop__0 _ S.CLZ => Unop_i UOI_clz
  | S.mk_unop__0 _ S.CTZ => Unop_i UOI_ctz
  | S.mk_unop__0 _ S.POPCNT => Unop_i UOI_popcnt
  | S.mk_unop__0 _ (S.EXTEND n) => Unop_extend n
  | S.mk_unop__1 _ S.ABS => Unop_f UOF_abs
  | S.mk_unop__1 _ S.unop_Fnn_NEG => Unop_f UOF_neg
  | S.mk_unop__1 _ S.SQRT => Unop_f UOF_sqrt
  | S.mk_unop__1 _ S.CEIL => Unop_f UOF_ceil
  | S.mk_unop__1 _ S.FLOOR => Unop_f UOF_floor
  | S.mk_unop__1 _ S.TRUNC => Unop_f UOF_trunc
  | S.mk_unop__1 _ S.NEAREST => Unop_f UOF_nearest
  end.

Definition tr_binop (op : S.binop_) : binop :=
  match op with
  | S.mk_binop__0 _ S.ADD => Binop_i BOI_add
  | S.mk_binop__0 _ S.SUB => Binop_i BOI_sub
  | S.mk_binop__0 _ S.MUL => Binop_i BOI_mul
  | S.mk_binop__0 _ (S.DIV s) => Binop_i (BOI_div (tr_sx s))
  | S.mk_binop__0 _ (S.REM s) => Binop_i (BOI_rem (tr_sx s))
  | S.mk_binop__0 _ S.AND => Binop_i BOI_and
  | S.mk_binop__0 _ S.OR => Binop_i BOI_or
  | S.mk_binop__0 _ S.XOR => Binop_i BOI_xor
  | S.mk_binop__0 _ S.SHL => Binop_i BOI_shl
  | S.mk_binop__0 _ (S.SHR s) => Binop_i (BOI_shr (tr_sx s))
  | S.mk_binop__0 _ S.ROTL => Binop_i BOI_rotl
  | S.mk_binop__0 _ S.ROTR => Binop_i BOI_rotr
  | S.mk_binop__1 _ S.binop_Fnn_ADD => Binop_f BOF_add
  | S.mk_binop__1 _ S.binop_Fnn_SUB => Binop_f BOF_sub
  | S.mk_binop__1 _ S.binop_Fnn_MUL => Binop_f BOF_mul
  | S.mk_binop__1 _ S.binop_Fnn_DIV => Binop_f BOF_div
  | S.mk_binop__1 _ S.MIN => Binop_f BOF_min
  | S.mk_binop__1 _ S.MAX => Binop_f BOF_max
  | S.mk_binop__1 _ S.COPYSIGN => Binop_f BOF_copysign
  end.

Definition tr_testop (op : S.testop_) : testop := TO_eqz.

Definition tr_relop (op : S.relop_) : relop :=
  match op with
  | S.mk_relop__0 _ S.EQ => Relop_i ROI_eq
  | S.mk_relop__0 _ S.NE => Relop_i ROI_ne
  | S.mk_relop__0 _ (S.LT s) => Relop_i (ROI_lt (tr_sx s))
  | S.mk_relop__0 _ (S.GT s) => Relop_i (ROI_gt (tr_sx s))
  | S.mk_relop__0 _ (S.LE s) => Relop_i (ROI_le (tr_sx s))
  | S.mk_relop__0 _ (S.GE s) => Relop_i (ROI_ge (tr_sx s))
  | S.mk_relop__1 _ S.relop_Fnn_EQ => Relop_f ROF_eq
  | S.mk_relop__1 _ S.relop_Fnn_NE => Relop_f ROF_ne
  | S.mk_relop__1 _ S.relop_Fnn_LT => Relop_f ROF_lt
  | S.mk_relop__1 _ S.relop_Fnn_GT => Relop_f ROF_gt
  | S.mk_relop__1 _ S.relop_Fnn_LE => Relop_f ROF_le
  | S.mk_relop__1 _ S.relop_Fnn_GE => Relop_f ROF_ge
  end.

(* WasmCert splits a conversion into the operator and its optional signedness. *)
Definition tr_cvtop (op : S.cvtop__) : cvtop * option sx :=
  match op with
  | S.mk_cvtop___0 _ _ (S.cvtop__Inn_1_Inn_2_EXTEND s) => (CVO_extend, Some (tr_sx s))
  | S.mk_cvtop___0 _ _ S.WRAP => (CVO_wrap, None)
  | S.mk_cvtop___1 _ _ (S.CONVERT s) => (CVO_convert, Some (tr_sx s))
  | S.mk_cvtop___1 _ _ S.REINTERPRET => (CVO_reinterpret, None)
  | S.mk_cvtop___2 _ _ (S.cvtop__Fnn_1_Inn_2_TRUNC s) => (CVO_trunc, Some (tr_sx s))
  | S.mk_cvtop___2 _ _ (S.TRUNC_SAT s) => (CVO_trunc_sat, Some (tr_sx s))
  | S.mk_cvtop___2 _ _ S.cvtop__Fnn_1_Inn_2_REINTERPRET => (CVO_reinterpret, None)
  | S.mk_cvtop___3 _ _ S.PROMOTE => (CVO_promote, None)
  | S.mk_cvtop___3 _ _ S.DEMOTE => (CVO_demote, None)
  end.

Definition tr_memarg (m : S.memarg) : memarg :=
  {| memarg_offset := tr_u32 (S.OFFSET m); memarg_align := tr_u32 (S.ALIGN m) |}.

Definition tr_sz (s : S.sz) : N :=
  match s with
  | S.mk_sz n => n
  end.

Definition tr_packtype (s : S.sz) : packed_type :=
  if N.eqb (tr_sz s) 8%num then Tp_i8
  else if N.eqb (tr_sz s) 16%num then Tp_i16
  else Tp_i32.

Definition tr_loadop (lo : option S.loadop_) : option (packed_type * sx) :=
  match lo with
  | Some (S.mk_loadop__0 _ (S.mk_loadop_Inn s x)) => Some (tr_packtype s, tr_sx x)
  | None => None
  end.

Definition tr_vloadop (lo : option S.vloadop_) : load_vec_arg :=
  match lo with
  | None => LVA_none
  | Some (S.SHAPEX_ s m x) => LVA_extend (tr_sz s, m) (tr_sx x)
  | Some (S.SPLAT s) => LVA_splat (tr_sz s)
  | Some (S.vloadop__ZERO s) => LVA_zero (tr_sz s)
  end.

Definition tr_blocktype (bt : S.blocktype) : block_type :=
  match bt with
  | S._RESULT t => BT_valtype (option_map tr_valtype t)
  | S._IDX x => BT_id (tr_u32 x)
  end.

Definition tr_shape (sh : S.shape) : vshape :=
  match sh with
  | S.X S.lanetype_I8 _ => VS_i VSI_8_16
  | S.X S.lanetype_I16 _ => VS_i VSI_16_8
  | S.X S.lanetype_I32 _ => VS_i VSI_32_4
  | S.X S.lanetype_I64 _ => VS_i VSI_64_2
  | S.X S.lanetype_F32 _ => VS_f VSF_32_4
  | S.X S.lanetype_F64 _ => VS_f VSF_64_2
  end.

Definition tr_ishape (sh : S.ishape) : vshape :=
  match sh with
  | S.mk_ishape sh => tr_shape sh
  end.

(** * Instructions *)

Fixpoint tr_instr (i : S.instr) : basic_instruction :=
  match i with
  | S.NOP => BI_nop
  | S.UNREACHABLE => BI_unreachable
  | S.DROP => BI_drop
  | S.SELECT ts => BI_select (option_map (map tr_valtype) ts)
  | S.BLOCK bt ins => BI_block (tr_blocktype bt) (map tr_instr ins)
  | S.LOOP bt ins => BI_loop (tr_blocktype bt) (map tr_instr ins)
  | S.IFELSE bt is1 is2 => BI_if (tr_blocktype bt) (map tr_instr is1) (map tr_instr is2)
  | S.BR l => BI_br (tr_u32 l)
  | S.BR_IF l => BI_br_if (tr_u32 l)
  | S.BR_TABLE ls l => BI_br_table (map tr_u32 ls) (tr_u32 l)
  | S.CALL x => BI_call (tr_u32 x)
  | S.CALL_INDIRECT x y => BI_call_indirect (tr_u32 x) (tr_u32 y)
  | S.RETURN => BI_return
  | S.CONST _ c => BI_const_num (tr_num c)
  | S.UNOP nt op => BI_unop (tr_numtype nt) (tr_unop op)
  | S.BINOP nt op => BI_binop (tr_numtype nt) (tr_binop op)
  | S.TESTOP nt op => BI_testop (tr_numtype nt) (tr_testop op)
  | S.RELOP nt op => BI_relop (tr_numtype nt) (tr_relop op)
  | S.CVTOP nt1 nt2 op => BI_cvtop (tr_numtype nt1) (tr_cvtop op).1 (tr_numtype nt2) (tr_cvtop op).2
  (* Vector instructions: the instruction class is fixed, the opcode is a hole. *)
  | S.VCONST _ c => BI_const_vec (tr_vec c)
  | S.VVUNOP _ _ => BI_vunop (vec_code i)
  | S.VVBINOP _ _ => BI_vbinop (vec_code i, [::])
  | S.VVTERNOP _ _ => BI_vternop (vec_code i)
  | S.VVTESTOP _ _ => BI_vtestop (vec_code i)
  | S.VUNOP _ _ => BI_vunop (vec_code i)
  | S.VBINOP _ _ => BI_vbinop (vec_code i, [::])
  | S.VTESTOP _ _ => BI_vtestop (vec_code i)
  | S.VRELOP _ _ => BI_vbinop (vec_code i, [::])
  | S.VSHIFTOP _ _ => BI_vshiftop (vec_code i)
  | S.VBITMASK _ => BI_vtestop (vec_code i)
  | S.VSWIZZLE _ => BI_vbinop (vec_code i, [::])
  | S.VSHUFFLE _ ls => BI_vbinop (vec_code i, map tr_u32 ls)
  | S.VSPLAT sh => BI_splat_vec (tr_shape sh)
  | S.VEXTRACT_LANE sh s j => BI_extract_vec (tr_shape sh) (option_map tr_sx s) (tr_u32 j)
  | S.VREPLACE_LANE sh j => BI_replace_vec (tr_shape sh) (tr_u32 j)
  | S.VEXTUNOP _ _ _ => BI_vunop (vec_code i)
  | S.VEXTBINOP _ _ _ => BI_vbinop (vec_code i, [::])
  | S.VNARROW _ _ _ => BI_vbinop (vec_code i, [::])
  | S.VCVTOP _ _ _ => BI_vunop (vec_code i)
  | S.REF_NULL rt => BI_ref_null (tr_reftype rt)
  | S.REF_FUNC x => BI_ref_func (tr_u32 x)
  | S.REF_IS_NULL => BI_ref_is_null
  | S.LOCAL_GET x => BI_local_get (tr_u32 x)
  | S.LOCAL_SET x => BI_local_set (tr_u32 x)
  | S.LOCAL_TEE x => BI_local_tee (tr_u32 x)
  | S.GLOBAL_GET x => BI_global_get (tr_u32 x)
  | S.GLOBAL_SET x => BI_global_set (tr_u32 x)
  | S.TABLE_GET x => BI_table_get (tr_u32 x)
  | S.TABLE_SET x => BI_table_set (tr_u32 x)
  | S.TABLE_SIZE x => BI_table_size (tr_u32 x)
  | S.TABLE_GROW x => BI_table_grow (tr_u32 x)
  | S.TABLE_FILL x => BI_table_fill (tr_u32 x)
  | S.TABLE_COPY x y => BI_table_copy (tr_u32 x) (tr_u32 y)
  | S.TABLE_INIT x y => BI_table_init (tr_u32 x) (tr_u32 y)
  | S.ELEM_DROP x => BI_elem_drop (tr_u32 x)
  | S.LOAD nt lo ao => BI_load (tr_numtype nt) (tr_loadop lo) (tr_memarg ao)
  | S.STORE nt so ao => BI_store (tr_numtype nt) (option_map tr_packtype so) (tr_memarg ao)
  | S.VLOAD _ lo ao => BI_load_vec (tr_vloadop lo) (tr_memarg ao)
  | S.VLOAD_LANE _ s ao j => BI_load_vec_lane (tr_sz s) (tr_memarg ao) (tr_u32 j)
  | S.VSTORE _ ao => BI_store_vec (tr_memarg ao)
  | S.VSTORE_LANE _ s ao j => BI_store_vec_lane (tr_sz s) (tr_memarg ao) (tr_u32 j)
  | S.MEMORY_SIZE => BI_memory_size
  | S.MEMORY_GROW => BI_memory_grow
  | S.MEMORY_FILL => BI_memory_fill
  | S.MEMORY_COPY => BI_memory_copy
  | S.MEMORY_INIT x => BI_memory_init (tr_u32 x)
  | S.DATA_DROP x => BI_data_drop (tr_u32 x)
  end.

Definition tr_instrs (ins : seq S.instr) : seq basic_instruction := map tr_instr ins.

(* Runtime structures *)

Definition tr_byte (b : S.byte) : byte :=
  match b with
  | S.mk_byte n => Integers.Byte.repr (Z.of_N n)
  end.

Definition tr_local (l : S.local) : value_type :=
  match l with
  | S.LOCAL t => tr_valtype t
  end.

Definition tr_func (f : S.func) : module_func :=
  match f with
  | S.func_FUNC x ls body =>
      {| modfunc_type := tr_u32 x;
         modfunc_locals := map tr_local ls;
         modfunc_body := tr_instrs body |}
  end.

(* UTF-8 encoding of a code point; names are only used by exports. *)
Definition byte_of_N (n : N) : Byte.byte :=
  match Byte.of_N n with
  | Some b => b
  | None => Byte.x00
  end.

Definition utf8_encode (c : N) : seq Byte.byte :=
  map byte_of_N
    (if N.ltb c 128 then [:: c]
     else if N.ltb c 2048 then [:: 192 + c / 64; 128 + c mod 64]
     else if N.ltb c 65536 then [:: 224 + c / 4096; 128 + (c / 64) mod 64; 128 + c mod 64]
     else [:: 240 + c / 262144; 128 + (c / 4096) mod 64; 128 + (c / 64) mod 64; 128 + c mod 64])%num.

Definition tr_name (nm : S.name) : name :=
  match nm with
  | S.mk_name cs => flatten (map (fun c => match c with S.mk_char n => utf8_encode n end) cs)
  end.

Definition tr_externaddr (a : S.externaddr) : extern_value :=
  match a with
  | S.externaddr_FUNC a => EV_func a
  | S.externaddr_GLOBAL a => EV_global a
  | S.externaddr_TABLE a => EV_table a
  | S.externaddr_MEM a => EV_mem a
  end.

Definition tr_exportinst (e : S.exportinst) : exportinst :=
  {| exportinst_name := tr_name (S.NAME e); exportinst_val := tr_externaddr (S.ADDR e) |}.

Definition tr_moduleinst (mi : S.moduleinst) : moduleinst :=
  {| inst_types := map tr_functype (S.TYPES mi);
     inst_funcs := S.FUNCS mi;
     inst_tables := S.TABLES mi;
     inst_mems := S.MEMS mi;
     inst_globals := S.GLOBALS mi;
     inst_elems := S.ELEMS mi;
     inst_datas := S.DATAS mi;
     inst_exports := map tr_exportinst (S.EXPORTS mi) |}.

Definition tr_funcinst (fi : S.funcinst) : funcinst :=
  FC_func_native (tr_functype (S.funcinst_TYPE fi)) (tr_moduleinst (S.funcinst_MODULE fi))
    (tr_func (S.CODE fi)).

Definition tr_globalinst (gi : S.globalinst) : globalinst :=
  {| g_type := tr_globaltype (S.globalinst_TYPE gi); g_val := tr_val (S.VALUE gi) |}.

Definition tr_tableinst (ti : S.tableinst) : tableinst :=
  {| tableinst_type := tr_tabletype (S.tableinst_TYPE ti);
     tableinst_elem := map tr_ref (S.REFS ti) |}.

Definition tr_mem_data (bs : seq S.byte) : @mem_t memory_tr :=
  {| memory_list.ml_init := Integers.Byte.zero; memory_list.ml_data := map tr_byte bs |}.

Definition tr_meminst (mi : S.meminst) : meminst :=
  {| meminst_type := tr_memtype (S.meminst_TYPE mi);
     meminst_data := tr_mem_data (S.BYTES mi) |}.

Definition tr_eleminst (ei : S.eleminst) : eleminst :=
  {| eleminst_type := tr_reftype (S.eleminst_TYPE ei);
     eleminst_elem := map tr_ref (S.eleminst_REFS ei) |}.

Definition tr_datainst (di : S.datainst) : datainst :=
  {| datainst_data := map tr_byte (S.datainst_BYTES di) |}.

Definition tr_store (s : S.store) : store_record :=
  {| s_funcs := map tr_funcinst (S.store_FUNCS s);
     s_tables := map tr_tableinst (S.store_TABLES s);
     s_mems := map tr_meminst (S.store_MEMS s);
     s_globals := map tr_globalinst (S.store_GLOBALS s);
     s_elems := map tr_eleminst (S.store_ELEMS s);
     s_datas := map tr_datainst (S.store_DATAS s) |}.

Definition tr_frame (f : S.frame) : frame :=
  {| f_locs := map tr_val (S.LOCALS f); f_inst := tr_moduleinst (S.frame_MODULE f) |}.

(* Administrative instructions *)

(* Every SpecTec administrative instruction that mirrors a plain instruction is
   translated through [tr_instr], so that [tr_admin_instr] holds by computation. *)
Fixpoint tr_admin (a : S.admininstr) : administrative_instruction :=
  match a with
  | S.admininstr_NOP => AI_basic (tr_instr S.NOP)
  | S.admininstr_UNREACHABLE => AI_basic (tr_instr S.UNREACHABLE)
  | S.admininstr_DROP => AI_basic (tr_instr S.DROP)
  | S.admininstr_SELECT x0 => AI_basic (tr_instr (S.SELECT x0))
  | S.admininstr_BLOCK x0 x1 => AI_basic (tr_instr (S.BLOCK x0 x1))
  | S.admininstr_LOOP x0 x1 => AI_basic (tr_instr (S.LOOP x0 x1))
  | S.admininstr_IFELSE x0 x1 x2 => AI_basic (tr_instr (S.IFELSE x0 x1 x2))
  | S.admininstr_BR x0 => AI_basic (tr_instr (S.BR x0))
  | S.admininstr_BR_IF x0 => AI_basic (tr_instr (S.BR_IF x0))
  | S.admininstr_BR_TABLE x0 x1 => AI_basic (tr_instr (S.BR_TABLE x0 x1))
  | S.admininstr_CALL x0 => AI_basic (tr_instr (S.CALL x0))
  | S.admininstr_CALL_INDIRECT x0 x1 => AI_basic (tr_instr (S.CALL_INDIRECT x0 x1))
  | S.admininstr_RETURN => AI_basic (tr_instr S.RETURN)
  | S.admininstr_CONST x0 x1 => AI_basic (tr_instr (S.CONST x0 x1))
  | S.admininstr_UNOP x0 x1 => AI_basic (tr_instr (S.UNOP x0 x1))
  | S.admininstr_BINOP x0 x1 => AI_basic (tr_instr (S.BINOP x0 x1))
  | S.admininstr_TESTOP x0 x1 => AI_basic (tr_instr (S.TESTOP x0 x1))
  | S.admininstr_RELOP x0 x1 => AI_basic (tr_instr (S.RELOP x0 x1))
  | S.admininstr_CVTOP x0 x1 x2 => AI_basic (tr_instr (S.CVTOP x0 x1 x2))
  | S.admininstr_VCONST x0 x1 => AI_basic (tr_instr (S.VCONST x0 x1))
  | S.admininstr_VVUNOP x0 x1 => AI_basic (tr_instr (S.VVUNOP x0 x1))
  | S.admininstr_VVBINOP x0 x1 => AI_basic (tr_instr (S.VVBINOP x0 x1))
  | S.admininstr_VVTERNOP x0 x1 => AI_basic (tr_instr (S.VVTERNOP x0 x1))
  | S.admininstr_VVTESTOP x0 x1 => AI_basic (tr_instr (S.VVTESTOP x0 x1))
  | S.admininstr_VUNOP x0 x1 => AI_basic (tr_instr (S.VUNOP x0 x1))
  | S.admininstr_VBINOP x0 x1 => AI_basic (tr_instr (S.VBINOP x0 x1))
  | S.admininstr_VTESTOP x0 x1 => AI_basic (tr_instr (S.VTESTOP x0 x1))
  | S.admininstr_VRELOP x0 x1 => AI_basic (tr_instr (S.VRELOP x0 x1))
  | S.admininstr_VSHIFTOP x0 x1 => AI_basic (tr_instr (S.VSHIFTOP x0 x1))
  | S.admininstr_VBITMASK x0 => AI_basic (tr_instr (S.VBITMASK x0))
  | S.admininstr_VSWIZZLE x0 => AI_basic (tr_instr (S.VSWIZZLE x0))
  | S.admininstr_VSHUFFLE x0 x1 => AI_basic (tr_instr (S.VSHUFFLE x0 x1))
  | S.admininstr_VSPLAT x0 => AI_basic (tr_instr (S.VSPLAT x0))
  | S.admininstr_VEXTRACT_LANE x0 x1 x2 => AI_basic (tr_instr (S.VEXTRACT_LANE x0 x1 x2))
  | S.admininstr_VREPLACE_LANE x0 x1 => AI_basic (tr_instr (S.VREPLACE_LANE x0 x1))
  | S.admininstr_VEXTUNOP x0 x1 x2 => AI_basic (tr_instr (S.VEXTUNOP x0 x1 x2))
  | S.admininstr_VEXTBINOP x0 x1 x2 => AI_basic (tr_instr (S.VEXTBINOP x0 x1 x2))
  | S.admininstr_VNARROW x0 x1 x2 => AI_basic (tr_instr (S.VNARROW x0 x1 x2))
  | S.admininstr_VCVTOP x0 x1 x2 => AI_basic (tr_instr (S.VCVTOP x0 x1 x2))
  | S.admininstr_REF_NULL x0 => AI_basic (tr_instr (S.REF_NULL x0))
  | S.admininstr_REF_FUNC x0 => AI_basic (tr_instr (S.REF_FUNC x0))
  | S.admininstr_REF_IS_NULL => AI_basic (tr_instr S.REF_IS_NULL)
  | S.admininstr_LOCAL_GET x0 => AI_basic (tr_instr (S.LOCAL_GET x0))
  | S.admininstr_LOCAL_SET x0 => AI_basic (tr_instr (S.LOCAL_SET x0))
  | S.admininstr_LOCAL_TEE x0 => AI_basic (tr_instr (S.LOCAL_TEE x0))
  | S.admininstr_GLOBAL_GET x0 => AI_basic (tr_instr (S.GLOBAL_GET x0))
  | S.admininstr_GLOBAL_SET x0 => AI_basic (tr_instr (S.GLOBAL_SET x0))
  | S.admininstr_TABLE_GET x0 => AI_basic (tr_instr (S.TABLE_GET x0))
  | S.admininstr_TABLE_SET x0 => AI_basic (tr_instr (S.TABLE_SET x0))
  | S.admininstr_TABLE_SIZE x0 => AI_basic (tr_instr (S.TABLE_SIZE x0))
  | S.admininstr_TABLE_GROW x0 => AI_basic (tr_instr (S.TABLE_GROW x0))
  | S.admininstr_TABLE_FILL x0 => AI_basic (tr_instr (S.TABLE_FILL x0))
  | S.admininstr_TABLE_COPY x0 x1 => AI_basic (tr_instr (S.TABLE_COPY x0 x1))
  | S.admininstr_TABLE_INIT x0 x1 => AI_basic (tr_instr (S.TABLE_INIT x0 x1))
  | S.admininstr_ELEM_DROP x0 => AI_basic (tr_instr (S.ELEM_DROP x0))
  | S.admininstr_LOAD x0 x1 x2 => AI_basic (tr_instr (S.LOAD x0 x1 x2))
  | S.admininstr_STORE x0 x1 x2 => AI_basic (tr_instr (S.STORE x0 x1 x2))
  | S.admininstr_VLOAD x0 x1 x2 => AI_basic (tr_instr (S.VLOAD x0 x1 x2))
  | S.admininstr_VLOAD_LANE x0 x1 x2 x3 => AI_basic (tr_instr (S.VLOAD_LANE x0 x1 x2 x3))
  | S.admininstr_VSTORE x0 x1 => AI_basic (tr_instr (S.VSTORE x0 x1))
  | S.admininstr_VSTORE_LANE x0 x1 x2 x3 => AI_basic (tr_instr (S.VSTORE_LANE x0 x1 x2 x3))
  | S.admininstr_MEMORY_SIZE => AI_basic (tr_instr S.MEMORY_SIZE)
  | S.admininstr_MEMORY_GROW => AI_basic (tr_instr S.MEMORY_GROW)
  | S.admininstr_MEMORY_FILL => AI_basic (tr_instr S.MEMORY_FILL)
  | S.admininstr_MEMORY_COPY => AI_basic (tr_instr S.MEMORY_COPY)
  | S.admininstr_MEMORY_INIT x0 => AI_basic (tr_instr (S.MEMORY_INIT x0))
  | S.admininstr_DATA_DROP x0 => AI_basic (tr_instr (S.DATA_DROP x0))
  | S.admininstr_REF_FUNC_ADDR a => AI_ref a
  | S.admininstr_REF_HOST_ADDR a => AI_ref_extern a
  | S.CALL_ADDR a => AI_invoke a
  | S.LABEL_ n ins es => AI_label (N.to_nat n) (to_e_list (tr_instrs ins)) (map tr_admin es)
  | S.FRAME_ n f es => AI_frame (N.to_nat n) (tr_frame f) (map tr_admin es)
  | S.admininstr_TRAP => AI_trap
  end.

Definition tr_admins (es : seq S.admininstr) : seq administrative_instruction := map tr_admin es.

(** * Typing contexts *)

(* SpecTec's Wasm 2.0 contexts have no [refs] component, so [ref.func x] is not
   restricted to declared references there.  We let WasmCert's [tc_refs] contain
   every function index, which makes the two checks coincide. *)
Definition tr_context (C : S.context) : t_context :=
  {| tc_types := map tr_functype (S.context_TYPES C);
     tc_funcs := map tr_functype (S.context_FUNCS C);
     tc_tables := map tr_tabletype (S.context_TABLES C);
     tc_mems := map tr_memtype (S.context_MEMS C);
     tc_globals := map tr_globaltype (S.context_GLOBALS C);
     tc_elems := map tr_reftype (S.context_ELEMS C);
     tc_datas := map (fun _ => tt) (S.context_DATAS C);
     tc_locals := map tr_valtype (S.context_LOCALS C);
     tc_labels := map tr_resulttype (S.LABELS C);
     tc_return := option_map tr_resulttype (S.context_RETURN C);
     tc_refs := iota_N 0 (size (S.context_FUNCS C)) |}.

End Translation.

(* Properties of the back-translation [backtranslation.v] (WasmCert -> SpecTec).

   - Soundness: whatever the back-translation produces is well-formed in SpecTec
     and is mapped back to its input by the forward translation [translation.v]
     ([of_instr_sound], [of_admin_sound], [of_config_sound], ...).
   - Completeness: on well-formed SpecTec inputs, back-translating the forward
     translation gives the input back ([of_instr_complete], ...).

   Together, the two translations are inverse bijections between well-formed
   SpecTec syntax and the domain of the back-translation.  For SIMD opcodes this
   holds relative to [vec_instr_sound] and [vec_instr_complete], which say that
   the opcode decoder [vec_instr] inverts [vec_code]. *)

From Stdlib Require Import NArith ZArith QArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From compcert Require Integers Memdata.
From Wasm Require Import datatypes datatypes_properties operations.
From Wasm Require memory_list.
From WasmSpectec Require wasm.
From WasmCertBridge Require fN_flocq.
From WasmCertBridge Require Import translation backtranslation.

Module S := WasmSpectec.wasm.
Module FL := WasmCertBridge.fN_flocq.

(* The eqType instances of SpecTec's types, without its names. *)
Import (canonicals) WasmSpectec.wasm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope N_scope with num.

(** * Option helpers *)

Section OListLemmas.
Context {A B : Type} (f : A -> option B).

Lemma olist_Forall2 l r : olist f l = Some r -> List.Forall2 (fun x y => f x = Some y) l r.
Proof.
  elim: l r => [|x l IH] r /=; first by case=> <-.
  case E: (f x) => [y|] //. case E': (olist f l) => [r'|] // [<-]. constructor => //. exact: IH.
Qed.

Lemma olist_cat l1 l2 r :
  olist f (l1 ++ l2) = Some r -> exists r1 r2, r = r1 ++ r2 /\ olist f l1 = Some r1 /\ olist f l2 = Some r2.
Proof.
  elim: l1 r => [|x l1 IH] r /=; first by move=> H; exists [::], r.
  case: (f x) => // y. case E: (olist f (l1 ++ l2)) => [r'|] // [<-].
  case: (IH _ E) => r1 [r2 [-> [-> ->]]]. by exists (y :: r1), r2.
Qed.

Lemma olist_inv (g : B -> A) l r :
  (forall x y, f x = Some y -> g y = x) -> olist f l = Some r -> map g r = l.
Proof. move=> H /olist_Forall2. by elim=> //= x y ? ? /H -> _ ->. Qed.

Lemma olist_Forall (P : B -> Prop) l r :
  (forall x y, f x = Some y -> P y) -> olist f l = Some r -> List.Forall P r.
Proof. move=> H /olist_Forall2. elim=> // x y ? ? /H Hy _ IH. by constructor. Qed.

Lemma olist_map (g : B -> A) r :
  List.Forall (fun y => f (g y) = Some y) r -> olist f (map g r) = Some r.
Proof. by elim=> //= y r' -> _ ->. Qed.

Lemma olist_lookup l r n x :
  olist f l = Some r -> lookup_N l n = Some x ->
  exists y, f x = Some y /\ lookup_N r n = Some y.
Proof.
  move=> /olist_Forall2 H. rewrite /lookup_N.
  elim: H (N.to_nat n) => [|a b l' r' Hab _ IH] [|k] //= Hx.
  - case: Hx => <-. by exists b.
  - exact: IH.
Qed.

Lemma oopt_Some o r : oopt f o = Some r ->
  match o, r with
  | Some x, Some y => f x = Some y
  | None, None => True
  | _, _ => False
  end.
Proof. case: o => [x|] /=; last by case=> <-. by case: (f x) => // y [<-]. Qed.

End OListLemmas.

(* Destructs the [let?], [option_map] and [guard] of a hypothesis
   [... = Some _]. *)
Ltac odestr H :=
  repeat (rewrite /option_map /guard in H;
    match type of H with
    | (match ?e with Some _ => _ | None => _ end) = Some _ =>
        let E := fresh "E" in destruct e eqn:E; [|discriminate H]
    | (if ?b then _ else _) = Some _ =>
        let E := fresh "E" in destruct b eqn:E; [|discriminate H]
    | Some _ = Some _ => injection H; clear H; intro H; subst
    end).

(** * Integers *)

Lemma wf_uN_iff k n : S.wf_uN k (S.mk_uN n) <-> (n < 2 ^ k)%num.
Proof.
  split.
  - move=> H; inversion H as [k' n' Hb]; subst.
    move: Hb => /andP [_ /N.leb_spec0]. rewrite /=. have := N.pow_nonzero 2 k. lia.
  - move=> Hn. constructor. apply/andP; split; apply/N.leb_spec0; first lia.
    rewrite /=. apply N2Z.inj_le; rewrite Z2N.id; lia.
Qed.

Lemma of_u32_Some n u : of_u32 n = Some u <-> u = S.mk_uN n /\ (n < 4294967296)%num.
Proof.
  rewrite /of_u32 /guard /u32_ok. case: N.ltb_spec0 => H; split.
  - by case=> <-.
  - by case=> ->.
  - by [].
  - by case=> _ /H.
Qed.

Lemma of_u32_sound n u : of_u32 n = Some u -> tr_u32 u = n /\ S.wf_uN 32%num u.
Proof. move=> /of_u32_Some [-> H]. split => //. exact/wf_uN_iff. Qed.

Lemma of_u32_complete u : S.wf_uN 32%num u -> of_u32 (tr_u32 u) = Some u.
Proof. case: u => n /wf_uN_iff H. by apply/of_u32_Some. Qed.

Lemma of_u8_Some n u : of_u8 n = Some u <-> u = S.mk_uN n /\ (n < 256)%num.
Proof.
  rewrite /of_u8 /guard. case: N.ltb_spec0 => H; split.
  - by case=> <-.
  - by case=> ->.
  - by [].
  - by case=> _ /H.
Qed.

Lemma of_u8_sound n u : of_u8 n = Some u -> tr_u32 u = n /\ S.wf_uN 8%num u.
Proof. move=> /of_u8_Some [-> H]. split => //. exact/wf_uN_iff. Qed.

Lemma of_u8_complete u : S.wf_uN 8%num u -> of_u8 (tr_u32 u) = Some u.
Proof. case: u => n /wf_uN_iff H. by apply/of_u8_Some. Qed.

Lemma olist_u32_sound ls ls' :
  olist of_u32 ls = Some ls' -> map tr_u32 ls' = ls /\ List.Forall (S.wf_uN 32%num) ls'.
Proof.
  move=> H. split; first by apply: olist_inv H => x y /of_u32_sound [].
  by apply: olist_Forall H => x y /of_u32_sound [].
Qed.

Lemma olist_u32_complete ls : List.Forall (S.wf_uN 32%num) ls -> olist of_u32 (map tr_u32 ls) = Some ls.
Proof. move=> H. apply: olist_map. apply: List.Forall_impl H. exact: of_u32_complete. Qed.

(** * Types *)

Lemma tr_of_numtype t : tr_numtype (of_numtype t) = t.
Proof. by case: t. Qed.

Lemma of_tr_numtype t : of_numtype (tr_numtype t) = t.
Proof. by case: t. Qed.

Lemma tr_of_reftype t : tr_reftype (of_reftype t) = t.
Proof. by case: t. Qed.

Lemma of_tr_reftype t : of_reftype (tr_reftype t) = t.
Proof. by case: t. Qed.

Lemma tr_of_valtype t : tr_valtype (of_valtype t) = t.
Proof. by case: t => [[]|[]|[]|]. Qed.

Lemma of_tr_valtype t : of_valtype (tr_valtype t) = t.
Proof. by case: t. Qed.

Lemma map_tr_of_valtype ts : map tr_valtype (map of_valtype ts) = ts.
Proof. by rewrite -map_comp (eq_map tr_of_valtype) map_id. Qed.

Lemma map_of_tr_valtype ts : map of_valtype (map tr_valtype ts) = ts.
Proof. by rewrite -map_comp (eq_map of_tr_valtype) map_id. Qed.

Lemma tr_of_resulttype ts : tr_resulttype (of_resulttype ts) = ts.
Proof. exact: map_tr_of_valtype. Qed.

Lemma of_tr_resulttype ts : of_resulttype (tr_resulttype ts) = ts.
Proof. case: ts => l. by rewrite /of_resulttype /= map_of_tr_valtype. Qed.

Lemma tr_of_functype ft : tr_functype (of_functype ft) = ft.
Proof. case: ft => t1 t2. by rewrite /of_functype /tr_functype !tr_of_resulttype. Qed.

Lemma of_tr_functype ft : of_functype (tr_functype ft) = ft.
Proof. case: ft => t1 t2. by rewrite /of_functype /tr_functype !of_tr_resulttype. Qed.

Lemma tr_of_globaltype g : tr_globaltype (of_globaltype g) = g.
Proof. by case: g => [[] t]; rewrite /= tr_of_valtype. Qed.

Lemma of_tr_globaltype g : of_globaltype (tr_globaltype g) = g.
Proof. by case: g => [[[]|] t]; rewrite /of_globaltype /= of_tr_valtype. Qed.

Lemma of_limits_sound l l' : of_limits l = Some l' -> tr_limits l' = l /\ S.wf_limits l'.
Proof.
  case: l => mn mx. rewrite /of_limits /=. move=> H. odestr H.
  case/of_u32_sound: E => <- Hmn.
  move/oopt_Some: E0. case: mx o => [m|] [m'|] //=.
  case/of_u32_sound => <- Hm. split => //. constructor => //. by repeat constructor.
Qed.

Lemma of_limits_complete l : S.wf_limits l -> of_limits (tr_limits l) = Some l.
Proof.
  case=> mn mx Hmn Hmx. rewrite /of_limits /= of_u32_complete //.
  case: mx Hmx => [m|] //= Hm. inversion Hm; subst. by rewrite of_u32_complete.
Qed.

Lemma of_tabletype_sound t t' : of_tabletype t = Some t' -> tr_tabletype t' = t /\ S.wf_tabletype t'.
Proof.
  case: t => l rt. rewrite /of_tabletype /= => H. odestr H.
  case/of_limits_sound: E => <- Hl. rewrite /= tr_of_reftype. by split => //; constructor.
Qed.

Lemma of_tabletype_complete t : S.wf_tabletype t -> of_tabletype (tr_tabletype t) = Some t.
Proof. case=> l rt Hl. by rewrite /of_tabletype /= of_limits_complete // of_tr_reftype. Qed.

Lemma of_memtype_sound t t' : of_memtype t = Some t' -> tr_memtype t' = t /\ S.wf_memtype t'.
Proof.
  rewrite /of_memtype => H. odestr H. case/of_limits_sound: E => <- Hl. by split => //; constructor.
Qed.

Lemma of_memtype_complete t : S.wf_memtype t -> of_memtype (tr_memtype t) = Some t.
Proof. case=> l Hl. by rewrite /of_memtype /= of_limits_complete. Qed.

Lemma of_externtype_sound t t' :
  of_externtype t = Some t' -> tr_externtype t' = t /\ S.wf_externtype t'.
Proof.
  case: t => [ft|tab|mt|gt] /= H; odestr H.
  - cbn [tr_externtype]; rewrite tr_of_functype. by split => //; constructor.
  - case/of_tabletype_sound: E => <- ?. by split => //; constructor.
  - case/of_memtype_sound: E => <- ?. by split => //; constructor.
  - cbn [tr_externtype]; rewrite tr_of_globaltype. by split => //; constructor.
Qed.

Lemma of_externtype_complete t : S.wf_externtype t -> of_externtype (tr_externtype t) = Some t.
Proof.
  case=> [ft|gt|tab Ht|mt Hm] /=.
  - by rewrite of_tr_functype.
  - by rewrite of_tr_globaltype.
  - by rewrite of_tabletype_complete.
  - by rewrite of_memtype_complete.
Qed.

(** * Values *)

Lemma max_unsigned32 : Wasm_int.Int32.max_unsigned = 4294967295%Z.
Proof. by vm_compute. Qed.

Lemma max_unsigned64 : Wasm_int.Int64.max_unsigned = 18446744073709551615%Z.
Proof. by vm_compute. Qed.

Lemma tr_of_i32 i : tr_i32 (of_i32 i) = i.
Proof.
  rewrite /tr_i32 /of_i32 /tr_u32 /= Z2N.id; first exact: Wasm_int.Int32.repr_unsigned.
  by case: (Wasm_int.Int32.unsigned_range i).
Qed.

Lemma tr_of_i64 i : tr_i64 (of_i64 i) = i.
Proof.
  rewrite /tr_i64 /of_i64 /tr_u32 /= Z2N.id; first exact: Wasm_int.Int64.repr_unsigned.
  by case: (Wasm_int.Int64.unsigned_range i).
Qed.

Lemma of_i32_wf i : S.wf_uN 32%num (of_i32 i).
Proof.
  apply/wf_uN_iff. have := Wasm_int.Int32.unsigned_range_2 i. rewrite max_unsigned32 /=. lia.
Qed.

Lemma of_i64_wf i : S.wf_uN 64%num (of_i64 i).
Proof.
  apply/wf_uN_iff. have := Wasm_int.Int64.unsigned_range_2 i. rewrite max_unsigned64 /=. lia.
Qed.

Lemma of_tr_i32 u : S.wf_uN 32%num u -> of_i32 (tr_i32 u) = u.
Proof.
  case: u => n /wf_uN_iff Hn.
  rewrite /of_i32 /tr_i32 /tr_u32 /S.proj_uN_0 Wasm_int.Int32.unsigned_repr ?N2Z.id //.
  rewrite max_unsigned32. simpl in Hn. lia.
Qed.

Lemma of_tr_i64 u : S.wf_uN 64%num u -> of_i64 (tr_i64 u) = u.
Proof.
  case: u => n /wf_uN_iff Hn.
  rewrite /of_i64 /tr_i64 /tr_u32 /S.proj_uN_0 Wasm_int.Int64.unsigned_repr ?N2Z.id //.
  rewrite max_unsigned64. simpl in Hn. lia.
Qed.

Lemma tr_of_f32 f : tr_f32 (of_f32 f) = f.
Proof.
  rewrite /tr_f32 /of_f32 /FL.fN_to_flocq_total. by rewrite FL.flocq_to_fN_inv.
Qed.

Lemma tr_of_f64 f : tr_f64 (of_f64 f) = f.
Proof.
  rewrite /tr_f64 /of_f64 /FL.fN_to_flocq_total. by rewrite FL.flocq_to_fN_inv.
Qed.

Lemma of_f32_wf f : S.wf_fN 32%num (of_f32 f).
Proof. apply: FL.flocq_to_fN_wf. by vm_compute. Qed.

Lemma of_f64_wf f : S.wf_fN 64%num (of_f64 f).
Proof. apply: FL.flocq_to_fN_wf. by vm_compute. Qed.

Lemma of_tr_f32 f : S.wf_fN 32%num f -> of_f32 (tr_f32 f) = f.
Proof. move=> H. by apply: FL.fN_to_flocq_total_inv; first vm_compute. Qed.

Lemma of_tr_f64 f : S.wf_fN 64%num f -> of_f64 (tr_f64 f) = f.
Proof. move=> H. by apply: FL.fN_to_flocq_total_inv; first vm_compute. Qed.

Lemma tr_of_num c : tr_num (of_num c) = c.
Proof.
  case: c => x /=; by rewrite ?tr_of_i32 ?tr_of_i64 ?tr_of_f32 ?tr_of_f64.
Qed.

Lemma of_num_wf c : S.wf_num_ (of_numtype (typeof_num c)) (of_num c).
Proof.
  case: c => x /=.
  - constructor => //. exact: of_i32_wf.
  - constructor => //. exact: of_i64_wf.
  - constructor => //. exact: of_f32_wf.
  - constructor => //. exact: of_f64_wf.
Qed.

Lemma of_tr_num nt c : S.wf_num_ nt c ->
  of_numtype (typeof_num (tr_num c)) = nt /\ of_num (tr_num c) = c.
Proof.
  case=> [nt' t x _ Hx /eqP -> | nt' t x Hx /eqP ->]; case: t Hx => /= Hx.
  - by rewrite of_tr_i32.
  - by rewrite of_tr_i64.
  - by rewrite of_tr_f32.
  - by rewrite of_tr_f64.
Qed.

(* v128 values as 16 little-endian bytes. *)
Lemma bytes_of_int_of_bytes l : Memdata.bytes_of_int (length l) (Memdata.int_of_bytes l) = l.
Proof.
  elim: l => //= b l IH. f_equal.
  - rewrite -[RHS]Integers.Byte.repr_unsigned. apply: Integers.Byte.eqm_samerepr.
    exists (Memdata.int_of_bytes l). change Integers.Byte.modulus with 256%Z. lia.
  - rewrite -[RHS]IH. f_equal.
    have := Integers.Byte.unsigned_range b. change Integers.Byte.modulus with 256%Z => Hb.
    by rewrite Z.div_add // Z.div_small.
Qed.

Lemma encode_decode_int l : Memdata.encode_int (length l) (Memdata.decode_int l) = l.
Proof.
  rewrite /Memdata.encode_int /Memdata.decode_int -(Memdata.rev_if_be_length l).
  by rewrite bytes_of_int_of_bytes Memdata.rev_if_be_involutive.
Qed.

Lemma length_size {A : Type} (l : seq A) : length l = size l.
Proof. by elim: l => //= ? ? ->. Qed.

Lemma of_v128_sound v c : of_v128 v = Some c -> tr_v128 c = v /\ S.wf_uN 128%num c.
Proof.
  rewrite /of_v128 => H. odestr H. move/Nat.eqb_spec: E => E.
  have Hr := Memdata.int_of_bytes_range (Memdata.rev_if_be v).
  rewrite Memdata.rev_if_be_length length_size E in Hr.
  change (two_p _) with (2 ^ 128)%Z in Hr.
  rewrite /tr_v128 /tr_u32 /= Z2N.id; last by rewrite /Memdata.decode_int; lia.
  split; first by rewrite -E -length_size encode_decode_int.
  apply/wf_uN_iff. rewrite /Memdata.decode_int. change (2 ^ 128)%num with (Z.to_N (2 ^ 128)). lia.
Qed.

Lemma of_tr_v128 c : S.wf_uN 128%num c -> of_v128 (tr_v128 c) = Some c.
Proof.
  case: c => n /wf_uN_iff Hn. rewrite /of_v128 /tr_v128 /tr_u32 /=.
  rewrite -length_size Memdata.encode_int_length /=.
  rewrite Memdata.decode_encode_int. change (two_p _) with (2 ^ 128)%Z.
  rewrite Z.mod_small ?N2Z.id //. change (2 ^ 128)%num with (Z.to_N (2 ^ 128)) in Hn. lia.
Qed.

Lemma tr_of_ref r : tr_ref (of_ref r) = r.
Proof. by case: r => //= t; rewrite tr_of_reftype. Qed.

Lemma of_tr_ref r : of_ref (tr_ref r) = r.
Proof. by case: r => //= t; rewrite of_tr_reftype. Qed.

Lemma of_val_sound v v' : of_val v = Some v' -> tr_val v' = v /\ S.wf_val v'.
Proof.
  case: v => [c|[c]|[t|a|a]] /= H; odestr H => /=.
  - rewrite tr_of_num. split => //. constructor. exact: of_num_wf.
  - case/of_v128_sound: E => <- Hc. by split => //; constructor.
  - rewrite tr_of_reftype. by split => //; constructor.
  - by split => //; constructor.
  - by split => //; constructor.
Qed.

Lemma of_val_complete v : S.wf_val v -> of_val (tr_val v) = Some v.
Proof.
  case=> [nt c Hc | vt c _ Hc | rt | a | a] /=.
  - by case: (of_tr_num Hc) => -> ->.
  - case: vt Hc => Hc. by rewrite /= of_tr_v128.
  - by case: rt.
  - by [].
  - by [].
Qed.

(** * Operators *)

Ltac closed := solve [ by [] | vm_compute; reflexivity | by repeat constructor ].

Lemma tr_of_sx s : tr_sx (of_sx s) = s.
Proof. by case: s. Qed.

Lemma of_tr_sx s : of_sx (tr_sx s) = s.
Proof. by case: s. Qed.

Lemma of_unop_sound t op op' :
  of_unop t op = Some op' -> tr_unop op' = op /\ S.wf_unop_ (of_numtype t) op'.
Proof.
  case: op => [o|o|n]; case: t => //=; try case: o; move=> [<-]; split => //; by constructor.
Qed.

Lemma of_unop_complete nt op : S.wf_unop_ nt op -> of_unop (tr_numtype nt) (tr_unop op) = Some op.
Proof. by case=> [nt' t x /eqP -> | nt' t x /eqP ->]; case: t; case: x. Qed.

Lemma of_binop_sound t op op' :
  of_binop t op = Some op' -> tr_binop op' = op /\ S.wf_binop_ (of_numtype t) op'.
Proof.
  case: op => o; case: t => //=; case: o => *;
  match goal with H : Some _ = Some _ |- _ => case: H => <- end;
  rewrite /= ?tr_of_sx; split => //; by constructor.
Qed.

Lemma of_binop_complete nt op : S.wf_binop_ nt op -> of_binop (tr_numtype nt) (tr_binop op) = Some op.
Proof. by case=> [nt' t x /eqP -> | nt' t x /eqP ->]; case: t; case: x => //= *; rewrite of_tr_sx. Qed.

Lemma of_testop_sound t op op' :
  of_testop t op = Some op' -> tr_testop op' = op /\ S.wf_testop_ (of_numtype t) op'.
Proof. case: op; case: t => //= [[<-]|[<-]]; split => //; by constructor. Qed.

Lemma of_testop_complete nt op : S.wf_testop_ nt op -> of_testop (tr_numtype nt) (tr_testop op) = Some op.
Proof. by case=> nt' t [] /eqP ->; case: t. Qed.

Lemma of_relop_sound t op op' :
  of_relop t op = Some op' -> tr_relop op' = op /\ S.wf_relop_ (of_numtype t) op'.
Proof.
  case: op => o; case: t => //=; case: o => *;
  match goal with H : Some _ = Some _ |- _ => case: H => <- end;
  rewrite /= ?tr_of_sx; split => //; by constructor.
Qed.

Lemma of_relop_complete nt op : S.wf_relop_ nt op -> of_relop (tr_numtype nt) (tr_relop op) = Some op.
Proof. by case=> [nt' t x /eqP -> | nt' t x /eqP ->]; case: t; case: x => //= *; rewrite of_tr_sx. Qed.

Lemma of_cvtop_sound t2 op t1 s c :
  of_cvtop t2 op t1 s = Some c ->
  tr_cvtop c = (op, s) /\ S.wf_cvtop__ (of_numtype t1) (of_numtype t2) c /\
  of_numtype t2 != of_numtype t1.
Proof.
  case: op; case: t1; case: t2; case: s => [s|] //= [<-]; rewrite /= ?tr_of_sx;
  (split; [done | split; [econstructor; try closed; econstructor; closed | closed]]).
Qed.

Lemma of_cvtop_complete nt1 nt2 c :
  S.wf_cvtop__ nt2 nt1 c ->
  of_cvtop (tr_numtype nt1) (tr_cvtop c).1 (tr_numtype nt2) (tr_cvtop c).2 = Some c.
Proof.
  move=> H; inversion H; subst;
  repeat match goal with Hb : is_true (_ == _) |- _ => move/eqP: Hb => Hb; subst end;
  match goal with Hx : _ |- _ => match type of Hx with
    | S.wf_cvtop__Inn_1_Inn_2 _ _ _ => inversion Hx
    | S.wf_cvtop__Inn_1_Fnn_2 _ _ _ => inversion Hx
    | S.wf_cvtop__Fnn_1_Inn_2 _ _ _ => inversion Hx
    | S.wf_cvtop__Fnn_1_Fnn_2 _ _ _ => inversion Hx end end; subst;
  repeat match goal with t : S.Inn |- _ => destruct t | t : S.Fnn |- _ => destruct t end;
  rewrite /= ?of_tr_sx //;
  match goal with Hb : is_true ?b |- _ => vm_compute in Hb; discriminate end.
Qed.

Lemma of_memarg_sound m m' : of_memarg m = Some m' -> tr_memarg m' = m /\ S.wf_memarg m'.
Proof.
  case: m => o a. rewrite /of_memarg /= => H. odestr H.
  case/of_u32_sound: E => <- Ha. case/of_u32_sound: E0 => <- Ho. by split => //; constructor.
Qed.

Lemma of_memarg_complete m : S.wf_memarg m -> of_memarg (tr_memarg m) = Some m.
Proof. case=> a o Ha Ho. by rewrite /of_memarg /= !of_u32_complete. Qed.

Lemma sz_okP n : sz_ok n <-> S.wf_sz (S.mk_sz n).
Proof.
  rewrite /sz_ok. split.
  - move=> H. constructor. move: H.
    by move=> /orP [/orP [/orP [/N.eqb_spec -> | /N.eqb_spec ->] | /N.eqb_spec ->] | /N.eqb_spec ->];
      rewrite eqxx ?orbT.
  - move=> H; inversion H; subst.
    by move: H1 => /orP [/orP [/orP [/eqP -> | /eqP ->] | /eqP ->] | /eqP ->].
Qed.

Lemma tr_of_packtype tp : tr_packtype (S.mk_sz (of_packtype tp)) = tp.
Proof. by case: tp. Qed.

Lemma of_pack_sound t tp inn :
  of_pack t tp = Some inn ->
  of_numtype t = S.numtype_Inn inn /\ (of_packtype tp < S.sizenn (S.numtype_Inn inn))%num /\
  S.wf_sz (S.mk_sz (of_packtype tp)).
Proof.
  rewrite /of_pack => H. odestr H. move/N.ltb_spec0: E0 => Hlt.
  have Hsz : S.wf_sz (S.mk_sz (of_packtype tp)) by apply/sz_okP; case: tp {Hlt}.
  case: t E => //= [[E]|[E]]; subst inn; by split.
Qed.

Lemma of_pack_complete inn n :
  S.wf_sz (S.mk_sz n) -> (n < S.sizenn (S.numtype_Inn inn))%num ->
  of_pack (tr_numtype (S.numtype_Inn inn)) (tr_packtype (S.mk_sz n)) = Some inn /\
  of_packtype (tr_packtype (S.mk_sz n)) = n.
Proof.
  move=> /sz_okP Hsz Hlt. rewrite /sz_ok in Hsz.
  have Hn : of_packtype (tr_packtype (S.mk_sz n)) = n.
  { case: inn Hlt => /= Hlt;
    move: Hsz => /orP [/orP [/orP [/N.eqb_spec -> | /N.eqb_spec ->] | /N.eqb_spec ->] | /N.eqb_spec Hn];
    try done; subst; vm_compute in Hlt; discriminate. }
  split => //. rewrite /of_pack Hn. case: inn Hlt => /= Hlt; by rewrite /guard (introT (N.ltb_spec0 _ _) Hlt).
Qed.

Lemma of_loadop_sound t lo lo' :
  of_loadop t lo = Some lo' ->
  tr_loadop lo' = lo /\ List.Forall (S.wf_loadop_ (of_numtype t)) (S.option_to_list lo').
Proof.
  case: lo => [[tp s]|] /= H; odestr H => //.
  case/of_pack_sound: E => Et [Hlt Hsz]. rewrite /= tr_of_packtype tr_of_sx.
  split => //. constructor => //. econstructor; last by rewrite Et.
  constructor => //. exact/N.ltb_spec0.
Qed.

Lemma of_loadop_complete nt lo :
  List.Forall (S.wf_loadop_ nt) (S.option_to_list lo) -> of_loadop (tr_numtype nt) (tr_loadop lo) = Some lo.
Proof.
  case: lo => [[inn [[n] s]]|] //= H. inversion H as [|? ? Hlo]; subst.
  inversion Hlo as [? ? ? Hin Heq]; subst. move/eqP: Heq => ->.
  inversion Hin as [? ? ? Hsz Hlt]; subst. move/N.ltb_spec0: Hlt => Hlt.
  case: (of_pack_complete Hsz Hlt) => -> ->. by rewrite of_tr_sx.
Qed.

Lemma of_vloadop_sound lv lv' :
  of_vloadop lv = Some lv' ->
  tr_vloadop lv' = lv /\ List.Forall (S.wf_vloadop_ S.V128) (S.option_to_list lv').
Proof.
  case: lv => [[n m] s|w|w|] /= H; odestr H => //=.
  - move: E => /andP [/andP [/sz_okP Hsz /N.eqb_spec Hnm] /N.ltb_spec0 Hm].
    rewrite tr_of_sx. split => //. constructor => //. constructor => //.
    apply/andP; split; last by apply/N.ltb_spec0.
    apply/Qeq_bool_iff. rewrite /Qeq /=. lia.
  - move: E => /andP [/sz_okP Hsz /N.leb_spec0 Hw].
    split => //. constructor => //. constructor => //. rewrite /S.N_geb /=. exact/N.leb_spec0.
  - move/sz_okP: E => Hsz. split => //. by constructor; [constructor | constructor].
Qed.

Lemma of_vloadop_complete lv :
  List.Forall (S.wf_vloadop_ S.V128) (S.option_to_list lv) -> of_vloadop (tr_vloadop lv) = Some lv.
Proof.
  case: lv => [lv|] //= H. inversion H as [|? ? Hlv]; subst. clear H.
  inversion Hlv as [? [n] m s Hsz Hb | ? [w] Hsz | ? [w] Hsz Hw]; subst; rewrite /= /guard.
  - move: Hb => /andP [/Qeq_bool_iff Hq /N.ltb_spec0 Hm]. rewrite /Qeq /= in Hq.
    have -> : sz_ok n by apply/sz_okP.
    have -> : (n * m =? 64)%num by apply/N.eqb_spec; lia.
    have -> : (1 <? m)%num by apply/N.ltb_spec0.
    by rewrite of_tr_sx.
  - by have -> : sz_ok w by apply/sz_okP.
  - have -> : sz_ok w by apply/sz_okP. by have -> : (32 <=? w)%num by exact: Hw.
Qed.

Lemma of_blocktype_sound bt bt' :
  of_blocktype bt = Some bt' -> tr_blocktype bt' = bt /\ S.wf_blocktype bt'.
Proof.
  case: bt => [x|t] /= H; odestr H.
  - case/of_u32_sound: E => <- ?. by split => //; constructor.
  - case: t => [t|] /=; rewrite ?tr_of_valtype; by split => //; constructor.
Qed.

Lemma of_blocktype_complete bt : S.wf_blocktype bt -> of_blocktype (tr_blocktype bt) = Some bt.
Proof.
  case=> [[t|]|x Hx] /=; rewrite ?of_tr_valtype //.
  by rewrite /of_blocktype /= of_u32_complete.
Qed.

Lemma tr_of_shape sh : tr_shape (of_shape sh) = sh.
Proof. by case: sh => [[]|[]]. Qed.

Lemma of_shape_wf sh : S.wf_shape (of_shape sh).
Proof. case: sh => [[]|[]]; constructor; closed. Qed.

Lemma of_tr_shape sh : S.wf_shape sh -> of_shape (tr_shape sh) = sh.
Proof.
  case=> lt [n] Hd /eqP Hsz. inversion Hd; subst.
  move: H0 => /orP [/orP [/orP [/orP [/eqP E | /eqP E] | /eqP E] | /eqP E] | /eqP E]; subst;
  by case: lt Hsz.
Qed.

Lemma packed_shape_tr sh :
  packed_shape (tr_shape sh) = ~~ (S.fun_lanetype sh \in [:: S.lanetype_I32; S.lanetype_I64; S.lanetype_F32; S.lanetype_F64]).
Proof. by case: sh => [[] [n]]. Qed.

Lemma of_storeop_sound t so so' :
  of_storeop t so = Some so' ->
  option_map tr_packtype so' = so /\
  forall m, S.wf_memarg m -> S.wf_instr (S.STORE (of_numtype t) so' m).
Proof.
  case: so => [tp|] /= H; odestr H => /=.
  - case/of_pack_sound: E => Et [Hlt Hsz]. rewrite tr_of_packtype. split => // m Hm.
    apply: (@S.instr_case_56 (Some i)) => //=.
    + by constructor.
    + constructor => //. rewrite Et eqxx /=. exact/N.ltb_spec0.
  - split => // m Hm. by apply: (@S.instr_case_56 None).
Qed.

(** * Instructions *)

Lemma olist_in_sound {A B : Type} (f : A -> option B) (g : B -> A) (P : B -> Prop) l r :
  (forall y, List.In y l -> forall x, f y = Some x -> g x = y /\ P x) ->
  olist f l = Some r -> map g r = l /\ List.Forall P r.
Proof.
  move=> H /olist_Forall2 H2. elim: H2 H => [|y x l' r' Hyx _ IH] H //=.
  case: (H y (or_introl erefl) x Hyx) => -> Hx.
  case: IH => [z Hz|-> Hr']; first by apply: H; right.
  by split => //; constructor.
Qed.

(* [IH] holds on every element of the list in the goal. *)
Ltac in_ih IH :=
  let y := fresh "y" in let l := fresh "l" in let IHl := fresh "IHl" in
  let z := fresh "z" in let Hz := fresh "Hz" in
  match goal with |- forall _, List.In _ ?es -> _ =>
    elim: es => [|y l IHl] z /=; [case | case=> [<-|Hz]; [exact: IH | exact: IHl Hz]]
  end.

Lemma option_map_tr_of_valtype ts :
  option_map (map tr_valtype) (option_map (map of_valtype) ts) = ts.
Proof. by case: ts => //= ts; rewrite map_tr_of_valtype. Qed.

Lemma option_map_of_tr_valtype ts :
  option_map (map of_valtype) (option_map (map tr_valtype) ts) = ts.
Proof. by case: ts => //= ts; rewrite map_of_tr_valtype. Qed.

Lemma tr_of_sx_opt s : option_map tr_sx (option_map of_sx s) = s.
Proof. by case: s => // s; rewrite /= tr_of_sx. Qed.

Lemma of_tr_sx_opt s : option_map of_sx (option_map tr_sx s) = s.
Proof. by case: s => // s; rewrite /= of_tr_sx. Qed.

(* Instructions that WasmCert represents by their SIMD opcode. *)
Definition is_vec_op (i : S.instr) : bool :=
  match i with
  | S.VVUNOP _ _ | S.VVBINOP _ _ | S.VVTERNOP _ _ | S.VVTESTOP _ _
  | S.VUNOP _ _ | S.VBINOP _ _ | S.VTESTOP _ _ | S.VRELOP _ _ | S.VSHIFTOP _ _
  | S.VBITMASK _ | S.VSWIZZLE _ | S.VSHUFFLE _ _
  | S.VEXTUNOP _ _ _ | S.VEXTBINOP _ _ _ | S.VNARROW _ _ _ | S.VCVTOP _ _ _ => true
  | _ => false
  end.

Section Instructions.

Context `{hfc : host_function_class}.
Variable vec_instr : basic_instruction -> option S.instr.

(* The SIMD decoder inverts [vec_code] on well-formed instructions. *)
Hypothesis vec_instr_sound :
  forall b i, vec_instr b = Some i -> tr_instr i = b /\ S.wf_instr i.
Hypothesis vec_instr_complete :
  forall i, is_vec_op i -> S.wf_instr i -> vec_instr (tr_instr i) = Some i.

Ltac snd_hyps :=
  repeat match goal with
  | E : of_u32 _ = Some _ |- _ => case/of_u32_sound: E => <- ?
  | E : of_u8 _ = Some _ |- _ => case/of_u8_sound: E => <- ?
  | E : olist of_u32 _ = Some _ |- _ => case/olist_u32_sound: E => <- ?
  | E : of_memarg _ = Some _ |- _ => case/of_memarg_sound: E => <- ?
  | E : of_blocktype _ = Some _ |- _ => case/of_blocktype_sound: E => <- ?
  | E : of_unop _ _ = Some _ |- _ => case/of_unop_sound: E => <- ?
  | E : of_binop _ _ = Some _ |- _ => case/of_binop_sound: E => <- ?
  | E : of_testop _ _ = Some _ |- _ => case/of_testop_sound: E => <- ?
  | E : of_relop _ _ = Some _ |- _ => case/of_relop_sound: E => <- ?
  | E : of_cvtop _ _ _ _ = Some _ |- _ =>
      let Ec := fresh "Ec" in case/of_cvtop_sound: E => Ec [? ?]; cbn [tr_instr]; rewrite Ec
  | E : of_storeop _ _ = Some _ |- _ => case/of_storeop_sound: E => <- ?
  | E : sz_ok _ = true |- _ => move/sz_okP: E => ?
  | E : None = Some _ |- _ => discriminate E
  | E : of_loadop _ _ = Some _ |- _ => case/of_loadop_sound: E => <- ?
  | E : of_vloadop _ = Some _ |- _ => case/of_vloadop_sound: E => <- ?
  | E : of_vec ?c = Some _ |- _ => case: c E => ? /of_v128_sound [<- ?]
  | E : vec_instr _ = Some _ |- _ => case/vec_instr_sound: E => <- ?
  end.

Definition instr_sound_at (b : basic_instruction) : Prop :=
  forall i, of_instr vec_instr b = Some i -> tr_instr i = b /\ S.wf_instr i.

Lemma instrs_sound_in es es' :
  (forall y, List.In y es -> instr_sound_at y) ->
  olist (of_instr vec_instr) es = Some es' -> map tr_instr es' = es /\ List.Forall S.wf_instr es'.
Proof. move=> H. apply: olist_in_sound => y Hy. exact: H. Qed.

Lemma block_sound bt es : (forall y, List.In y es -> instr_sound_at y) -> instr_sound_at (BI_block bt es).
Proof.
  move=> Hes i /= Hb. odestr Hb. case/of_blocktype_sound: E => <- ?.
  case/(instrs_sound_in Hes): E0 => <- ?. by split => //; constructor.
Qed.

Lemma loop_sound bt es : (forall y, List.In y es -> instr_sound_at y) -> instr_sound_at (BI_loop bt es).
Proof.
  move=> Hes i /= Hb. odestr Hb. case/of_blocktype_sound: E => <- ?.
  case/(instrs_sound_in Hes): E0 => <- ?. by split => //; constructor.
Qed.

Lemma if_sound bt es1 es2 :
  (forall y, List.In y es1 -> instr_sound_at y) -> (forall y, List.In y es2 -> instr_sound_at y) ->
  instr_sound_at (BI_if bt es1 es2).
Proof.
  move=> Hes1 Hes2 i /= Hb. odestr Hb. case/of_blocktype_sound: E => <- ?.
  case/(instrs_sound_in Hes1): E0 => <- ?. case/(instrs_sound_in Hes2): E1 => <- ?.
  by split => //; constructor.
Qed.

Lemma of_instr_sound : forall b, instr_sound_at b.
Proof.
  fix IH 1. case.
  all: try (by move=> bt es; apply: block_sound; in_ih IH).
  all: try (by move=> bt es; apply: loop_sound; in_ih IH).
  all: try (by move=> bt es1 es2; apply: if_sound; in_ih IH).
  all: clear IH; rewrite /instr_sound_at; intros;
       match goal with H : of_instr _ _ = Some _ |- _ => rename H into Hb end.
  all: rewrite /= in Hb; odestr Hb; snd_hyps.
  all: try (split; [cbn [tr_instr]; rewrite ?tr_of_numtype ?tr_of_reftype ?tr_of_num ?tr_of_shape
                    ?tr_of_packtype ?option_map_tr_of_valtype ?tr_of_sx_opt; done |]).
  all: try (by econstructor; eauto).
  all: try assumption.
  all: try (constructor; first [exact: of_num_wf | exact: of_shape_wf]).
  all: try (constructor; [exact: of_shape_wf | done]).
  - (* extract_lane: packed lanes and only them have a signedness *)
    apply: S.instr_case_33; [exact: of_shape_wf | done | closed | by case: v o E => [[]|[]] [s|]].
  - (* store *) by eauto.
Qed.

Definition instr_complete_at (i : S.instr) : Prop :=
  S.wf_instr i -> of_instr vec_instr (tr_instr i) = Some i.

Lemma instrs_complete_in ins :
  (forall y, List.In y ins -> instr_complete_at y) ->
  List.Forall S.wf_instr ins -> olist (of_instr vec_instr) (map tr_instr ins) = Some ins.
Proof.
  elim: ins => [|i ins IH] //= H /List.Forall_cons_iff [Hi Hins].
  rewrite (H i (or_introl erefl) Hi) IH //. by move=> y Hy; apply: H; right.
Qed.

Lemma block_complete bt ins :
  (forall y, List.In y ins -> instr_complete_at y) -> instr_complete_at (S.BLOCK bt ins).
Proof.
  move=> H Hwf /=. inversion Hwf; subst.
  by rewrite of_blocktype_complete // instrs_complete_in.
Qed.

Lemma loop_complete bt ins :
  (forall y, List.In y ins -> instr_complete_at y) -> instr_complete_at (S.LOOP bt ins).
Proof.
  move=> H Hwf /=. inversion Hwf; subst.
  by rewrite of_blocktype_complete // instrs_complete_in.
Qed.

Lemma if_complete bt ins1 ins2 :
  (forall y, List.In y ins1 -> instr_complete_at y) ->
  (forall y, List.In y ins2 -> instr_complete_at y) -> instr_complete_at (S.IFELSE bt ins1 ins2).
Proof.
  move=> H1 H2 Hwf /=. inversion Hwf; subst.
  by rewrite of_blocktype_complete // !instrs_complete_in.
Qed.

Lemma of_instr_complete : forall i, instr_complete_at i.
Proof.
  fix IH 1. case.
  all: try (by move=> bt ins; apply: block_complete; in_ih IH).
  all: try (by move=> bt ins; apply: loop_complete; in_ih IH).
  all: try (by move=> bt ins1 ins2; apply: if_complete; in_ih IH).
  all: clear IH; rewrite /instr_complete_at; intros until 1;
       match goal with H : S.wf_instr _ |- _ => rename H into Hwf end;
       inversion Hwf; subst.
  all: try (match goal with |- of_instr _ (tr_instr ?i) = _ => by apply: (vec_instr_complete (i := i)) end).
  all: repeat match goal with t : S.vectype |- _ => destruct t end.
  all: rewrite /= ?of_u32_complete ?of_u8_complete ?olist_u32_complete ?of_memarg_complete
          ?of_tr_numtype ?of_tr_reftype ?option_map_of_tr_valtype ?of_tr_shape //.
  all: repeat match goal with
       | H : S.wf_unop_ _ _ |- _ => rewrite (of_unop_complete H); clear H
       | H : S.wf_binop_ _ _ |- _ => rewrite (of_binop_complete H); clear H
       | H : S.wf_testop_ _ _ |- _ => rewrite (of_testop_complete H); clear H
       | H : S.wf_relop_ _ _ |- _ => rewrite (of_relop_complete H); clear H
       | H : S.wf_cvtop__ _ _ _ |- _ => rewrite (of_cvtop_complete H); clear H
       | H : S.wf_num_ _ _ |- _ => case: (of_tr_num H) => -> ->; clear H
       | H : List.Forall (S.wf_loadop_ _) _ |- _ => rewrite (of_loadop_complete H); clear H
       | H : List.Forall (S.wf_vloadop_ _) _ |- _ => rewrite (of_vloadop_complete H); clear H
       | H : S.wf_sz (S.mk_sz ?n) |- _ => have -> : sz_ok n by apply/sz_okP
       end.
  all: rewrite /= ?of_u32_complete ?of_u8_complete ?olist_u32_complete ?of_memarg_complete
          ?of_tr_numtype ?of_tr_reftype ?option_map_of_tr_valtype ?of_tr_shape ?of_tr_sx_opt //.
  all: clear Hwf.
  - (* vconst *) by rewrite of_tr_v128.
  - (* extract_lane *)
    rewrite /guard packed_shape_tr. case: sx_opt H5 => [s|] /= [H5a H5b].
    + have -> : (S.fun_lanetype v_shape \in [:: S.lanetype_I32; S.lanetype_I64; S.lanetype_F32;
                                               S.lanetype_F64]) = false by apply/negP => /H5a.
      by [].
    + by rewrite H5b.
  - (* load *) by rewrite (of_loadop_complete H1).
  - (* store *)
    case: sz_opt Inn_opt H2 H4 H5 => [[n]|] [inn|] //= H2 H4 H5; last by case: H4 => /(_ erefl).
    inversion H5 as [|? ? ? ? Hb]; subst. move: Hb => /andP [/eqP -> /N.ltb_spec0 Hlt].
    inversion H2 as [|? ? Hsz]; subst. case: (of_pack_complete Hsz Hlt) => Hp Hn.
    by rewrite /= Hp /= Hn.
  - (* vload *) by rewrite (of_vloadop_complete H1).
  - (* vload_lane *) case: v_sz H2 => n H2. by have -> : sz_ok n by apply/sz_okP.
  - (* vstore_lane *) case: v_sz H2 => n H2. by have -> : sz_ok n by apply/sz_okP.
Qed.

Lemma of_instrs_complete ins :
  List.Forall S.wf_instr ins -> of_instrs vec_instr (tr_instrs ins) = Some ins.
Proof. apply: instrs_complete_in => y _. exact: of_instr_complete. Qed.

Lemma of_instrs_sound es ins :
  of_instrs vec_instr es = Some ins -> tr_instrs ins = es /\ List.Forall S.wf_instr ins.
Proof. apply: instrs_sound_in => y _. exact: of_instr_sound. Qed.


(** * Names *)

Lemma byte_of_N_to n : (n < 256)%num -> Byte.to_N (byte_of_N n) = n.
Proof.
  move=> Hn. rewrite /byte_of_N. have := Byte.to_of_N_option_map n.
  case: (Byte.of_N n) => [b|] /=; case: N.leb_spec0 => H; try lia; first by case.
  discriminate.
Qed.

(* The UTF-8 encoding of a code point, as SpecTec bytes. *)
Definition enc_S (c : N) : seq S.byte := map (fun b => S.mk_byte (Byte.to_N b)) (utf8_encode c).

Lemma size_enc_S c : size (enc_S c) = size (utf8_encode c).
Proof. by rewrite size_map. Qed.

(* [lia] with [N.div] and [N.modulo] by constants. *)
Ltac nlia := zify; Z.to_euclidean_division_equations; lia.

Lemma char_ok_bound c : char_ok c -> (c < 69632)%num.
Proof. by rewrite /char_ok => /orP [/N.ltb_spec0 | /andP [_ /N.ltb_spec0]]; lia. Qed.

Lemma utf8_decode_char c rest :
  char_ok c -> utf8_decode (utf8_encode c ++ rest) = option_map (cons c) (utf8_decode rest).
Proof.
  move/char_ok_bound => Hc. rewrite /utf8_encode.
  case: (N.ltb_spec0 c 128) => H1.
  { cbn [map cat utf8_decode]. rewrite byte_of_N_to; last lia. by case: N.ltb_spec0. }
  case: (N.ltb_spec0 c 2048) => H2.
  { set x := (192 + c / 64)%num. set y := (128 + c mod 64)%num.
    have Hx : (192 <= x < 224)%num by subst x; nlia.
    have Hy : (128 <= y < 192)%num by subst y; nlia.
    have -> : c = ((x - 192) * 64 + (y - 128))%num by subst x y; nlia.
    clearbody x y. cbn [map cat utf8_decode]. rewrite !byte_of_N_to; try lia.
    by do 2 (case: N.ltb_spec0 => ?; try lia). }
  case: (N.ltb_spec0 c 65536) => H3.
  { set x := (224 + c / 4096)%num. set y := (128 + (c / 64) mod 64)%num. set z := (128 + c mod 64)%num.
    have Hx : (224 <= x < 240)%num by subst x; nlia.
    have Hy : (128 <= y < 192)%num by subst y; nlia.
    have Hz : (128 <= z < 192)%num by subst z; nlia.
    have -> : c = ((x - 224) * 4096 + (y - 128) * 64 + (z - 128))%num by subst x y z; nlia.
    clearbody x y z. cbn [map cat utf8_decode]. rewrite !byte_of_N_to; try lia.
    by do 3 (case: N.ltb_spec0 => ?; try lia). }
  set x := (240 + c / 262144)%num. set y := (128 + (c / 4096) mod 64)%num.
  set z := (128 + (c / 64) mod 64)%num. set w := (128 + c mod 64)%num.
  have Hx : x = 240%num by subst x; nlia.
  have Hy : (128 <= y < 192)%num by subst y; nlia.
  have Hz : (128 <= z < 192)%num by subst z; nlia.
  have Hw : (128 <= w < 192)%num by subst w; nlia.
  have -> : c = ((x - 240) * 262144 + (y - 128) * 4096 + (z - 128) * 64 + (w - 128))%num
    by subst x y z w; nlia.
  clearbody x y z w. subst x. cbn [map cat utf8_decode]. rewrite !byte_of_N_to; try lia.
  by do 3 (case: N.ltb_spec0 => ?; try lia).
Qed.

Lemma wf_byte_lt n : (n < 256)%num -> S.wf_byte (S.mk_byte n).
Proof. move=> Hn. constructor. apply/andP; split; apply/N.leb_spec0; cbn; lia. Qed.

(* The arithmetic side conditions of [S.fun_utf8]. *)
Ltac utf8_cond :=
  cbn [S.coerce S.proj_char_0_coercion S.proj_byte_0_coercion S.proj_char_0 S.proj_byte_0];
  repeat match goal with
  | |- is_true (_ && _) => apply/andP; split
  | |- is_true (N.leb _ _) => apply/N.leb_spec0
  | |- is_true (N.ltb _ _) => apply/N.ltb_spec0
  | |- is_true (_ == _) => apply/eqP
  end; nlia.

Lemma fun_utf8_char c : char_ok c -> S.fun_utf8 [:: S.mk_char c] (enc_S c).
Proof.
  move=> Hok. have Hc := char_ok_bound Hok. rewrite /enc_S /utf8_encode.
  case: (N.ltb_spec0 c 128) => H1.
  { cbn [map]. rewrite byte_of_N_to; last lia. apply: S.fun_utf8_case_0.
    - rewrite eqxx andbT. exact/N.ltb_spec0.
    - apply: wf_byte_lt; lia.
    - apply: wf_byte_lt; cbn; lia. }
  case: (N.ltb_spec0 c 2048) => H2.
  { cbn [map]. rewrite !byte_of_N_to; try nlia.
    apply: S.fun_utf8_case_1; try (apply: wf_byte_lt; nlia). utf8_cond. }
  case: (N.ltb_spec0 c 65536) => H3.
  { cbn [map]. rewrite !byte_of_N_to; try nlia.
    apply: S.fun_utf8_case_2; try (apply: wf_byte_lt; nlia).
    apply/andP; split; last by utf8_cond.
    move: Hok; rewrite /char_ok => /orP [/N.ltb_spec0 Hok | /andP [/N.leb_spec0 Hok _]];
      apply/orP; [left | right]; utf8_cond. }
  cbn [map]. rewrite !byte_of_N_to; try nlia.
  apply: S.fun_utf8_case_3; try (apply: wf_byte_lt; nlia). utf8_cond.
Qed.

Lemma concat_flatten (l : seq (seq S.byte)) : S.concat_ S.byte l = flatten l.
Proof. by elim: l => //= x l ->. Qed.

Lemma utf8_decode_chars cs rest :
  all char_ok cs -> utf8_decode (flatten (map utf8_encode cs) ++ rest) = option_map (cat cs) (utf8_decode rest).
Proof.
  elim: cs => [|c cs IH] /=; first by case: (utf8_decode rest).
  case/andP => Hc Hcs. rewrite -catA utf8_decode_char // IH //. by case: (utf8_decode rest).
Qed.

Lemma tr_name_chars cs : tr_name (S.mk_name (map S.mk_char cs)) = flatten (map utf8_encode cs).
Proof. by rewrite /tr_name -map_comp. Qed.

Lemma size_utf8_encode c :
  size (utf8_encode c) =
  if (c <? 128)%num then 1%nat else if (c <? 2048)%num then 2%nat else if (c <? 65536)%num then 3%nat else 4%nat.
Proof. rewrite /utf8_encode. by repeat case: ifP. Qed.

Lemma fun_utf8_chars cs :
  all char_ok cs -> S.fun_utf8 (map S.mk_char cs) (flatten (map enc_S cs)).
Proof.
  move=> Hcs.
  have H2 : List.Forall2 (fun v ch => S.fun_utf8 [:: ch] v) (map enc_S cs) (map S.mk_char cs).
  { elim: cs Hcs => [|c cs IH] //= /andP [Hc Hcs]. constructor; [exact: fun_utf8_char | exact: IH]. }
  have Hw : List.Forall (fun v => List.Forall S.wf_byte v) (map enc_S cs).
  { apply/List.Forall_forall => v /List.in_map_iff [c [<- _]].
    apply/List.Forall_forall => b /List.in_map_iff [b' [<- _]].
    apply: wf_byte_lt. have := Byte.to_N_bounded b'. lia. }
  have := @S.fun_utf8_case_4 (map S.mk_char cs) (map enc_S cs) (map enc_S cs) (map enc_S cs).
  rewrite concat_flatten !size_map eqxx. apply => //.
  elim: Hw => //= v l Hv _ IH. by apply/List.Forall_app; split.
Qed.

(* What [S.fun_utf8] says about the characters and the length of an encoding. *)
Lemma fun_utf8_props : forall chs v, S.fun_utf8 chs v ->
  all char_ok (map S.proj_char_0 chs) /\
  size v = size (flatten (map (fun c => utf8_encode (S.proj_char_0 c)) chs)).
Proof.
  fix IH 3. move=> chs v H. case: H.
  1-4: move=> [n]; cbn [S.coerce S.proj_char_0_coercion S.proj_char_0]; intros until 1;
    match goal with H : is_true _ |- _ => move: H end;
    rewrite /= ?cats0 size_utf8_encode /char_ok;
    move=> /andP [H _];
    repeat (case/orP: H => H || case/andP: H => [/N.leb_spec0 ? H] || move/N.ltb_spec0: H => ? );
    intros; repeat (case: N.ltb_spec0 => ? /=; try lia); repeat (case: N.leb_spec0 => ? /=; try lia);
    done.
  move=> chs' v2 v1 v0 _ _ _ _ _ H0 _ _. rewrite concat_flatten.
  elim: H0 => [|var ch vl chl Hvc _ IHl] //=.
  case: (IH _ _ Hvc) => /= /andP [Hc _] Hs. case: IHl => Hl Hsz.
  split; first by rewrite Hc. by rewrite !size_cat Hs cats0 Hsz.
Qed.

Lemma char_ok_wf c : char_ok c -> S.wf_char (S.mk_char c).
Proof.
  rewrite /char_ok => Hc. constructor.
  move: Hc => /orP [/N.ltb_spec0 H | /andP [/N.leb_spec0 H1 /N.ltb_spec0 H2]];
    apply/orP; [left | right]; apply/andP; split; apply/N.leb_spec0; lia.
Qed.

Lemma size_flatten_enc_S cs : size (flatten (map enc_S cs)) = size (flatten (map utf8_encode cs)).
Proof. by elim: cs => //= c cs IH; rewrite !size_cat size_enc_S IH. Qed.

Lemma of_name_sound nm n : of_name nm = Some n -> tr_name n = nm /\ S.wf_name n.
Proof.
  rewrite /of_name => H. odestr H.
  move: E0 => /andP [/andP [/eqP Henc Hok] /N.ltb_spec0 Hsz].
  rewrite tr_name_chars Henc. split => //.
  apply: (@S.name_case_0 _ (flatten (map enc_S l))).
  - exact: fun_utf8_chars.
  - elim: l {E Henc} Hok => //= c l IH /andP [Hc Hl]. constructor; [exact: char_ok_wf | exact: IH].
  - apply/N.ltb_spec0. by rewrite size_flatten_enc_S Henc.
Qed.

Lemma of_name_complete n : S.wf_name n -> of_name (tr_name n) = Some n.
Proof.
  case=> chars v Hu _ Hsz. case: (fun_utf8_props Hu) => Hok Hsize.
  have Hchars : chars = map S.mk_char (map S.proj_char_0 chars).
  { rewrite -map_comp. by elim: chars {Hu Hok Hsize} => //= [[c]] chars <-. }
  have Hsize' : size v = size (flatten (map utf8_encode (map S.proj_char_0 chars)))
    by rewrite -map_comp.
  clear Hsize Hu. move: (map S.proj_char_0 chars) Hok Hsize' Hchars => cs Hok Hsize ->.
  rewrite tr_name_chars /of_name.
  have := utf8_decode_chars [::] Hok. rewrite cats0 => -> /=.
  rewrite cats0 eqxx Hok /guard /=. move/N.ltb_spec0: Hsz. rewrite Hsize => Hsz.
  by have -> : (N.of_nat (size (flatten (map utf8_encode cs))) <? 4294967296)%num
    by apply/N.ltb_spec0.
Qed.

(* The instruction an administrative instruction embeds, if any. *)
Definition instr_of_admin (a : S.admininstr) : option S.instr :=
  match a with
  | S.admininstr_NOP => Some (S.NOP)
  | S.admininstr_UNREACHABLE => Some (S.UNREACHABLE)
  | S.admininstr_DROP => Some (S.DROP)
  | S.admininstr_SELECT x0 => Some (S.SELECT x0)
  | S.admininstr_BLOCK x0 x1 => Some (S.BLOCK x0 x1)
  | S.admininstr_LOOP x0 x1 => Some (S.LOOP x0 x1)
  | S.admininstr_IFELSE x0 x1 x2 => Some (S.IFELSE x0 x1 x2)
  | S.admininstr_BR x0 => Some (S.BR x0)
  | S.admininstr_BR_IF x0 => Some (S.BR_IF x0)
  | S.admininstr_BR_TABLE x0 x1 => Some (S.BR_TABLE x0 x1)
  | S.admininstr_CALL x0 => Some (S.CALL x0)
  | S.admininstr_CALL_INDIRECT x0 x1 => Some (S.CALL_INDIRECT x0 x1)
  | S.admininstr_RETURN => Some (S.RETURN)
  | S.admininstr_CONST x0 x1 => Some (S.CONST x0 x1)
  | S.admininstr_UNOP x0 x1 => Some (S.UNOP x0 x1)
  | S.admininstr_BINOP x0 x1 => Some (S.BINOP x0 x1)
  | S.admininstr_TESTOP x0 x1 => Some (S.TESTOP x0 x1)
  | S.admininstr_RELOP x0 x1 => Some (S.RELOP x0 x1)
  | S.admininstr_CVTOP x0 x1 x2 => Some (S.CVTOP x0 x1 x2)
  | S.admininstr_VCONST x0 x1 => Some (S.VCONST x0 x1)
  | S.admininstr_VVUNOP x0 x1 => Some (S.VVUNOP x0 x1)
  | S.admininstr_VVBINOP x0 x1 => Some (S.VVBINOP x0 x1)
  | S.admininstr_VVTERNOP x0 x1 => Some (S.VVTERNOP x0 x1)
  | S.admininstr_VVTESTOP x0 x1 => Some (S.VVTESTOP x0 x1)
  | S.admininstr_VUNOP x0 x1 => Some (S.VUNOP x0 x1)
  | S.admininstr_VBINOP x0 x1 => Some (S.VBINOP x0 x1)
  | S.admininstr_VTESTOP x0 x1 => Some (S.VTESTOP x0 x1)
  | S.admininstr_VRELOP x0 x1 => Some (S.VRELOP x0 x1)
  | S.admininstr_VSHIFTOP x0 x1 => Some (S.VSHIFTOP x0 x1)
  | S.admininstr_VBITMASK x0 => Some (S.VBITMASK x0)
  | S.admininstr_VSWIZZLE x0 => Some (S.VSWIZZLE x0)
  | S.admininstr_VSHUFFLE x0 x1 => Some (S.VSHUFFLE x0 x1)
  | S.admininstr_VSPLAT x0 => Some (S.VSPLAT x0)
  | S.admininstr_VEXTRACT_LANE x0 x1 x2 => Some (S.VEXTRACT_LANE x0 x1 x2)
  | S.admininstr_VREPLACE_LANE x0 x1 => Some (S.VREPLACE_LANE x0 x1)
  | S.admininstr_VEXTUNOP x0 x1 x2 => Some (S.VEXTUNOP x0 x1 x2)
  | S.admininstr_VEXTBINOP x0 x1 x2 => Some (S.VEXTBINOP x0 x1 x2)
  | S.admininstr_VNARROW x0 x1 x2 => Some (S.VNARROW x0 x1 x2)
  | S.admininstr_VCVTOP x0 x1 x2 => Some (S.VCVTOP x0 x1 x2)
  | S.admininstr_REF_NULL x0 => Some (S.REF_NULL x0)
  | S.admininstr_REF_FUNC x0 => Some (S.REF_FUNC x0)
  | S.admininstr_REF_IS_NULL => Some (S.REF_IS_NULL)
  | S.admininstr_LOCAL_GET x0 => Some (S.LOCAL_GET x0)
  | S.admininstr_LOCAL_SET x0 => Some (S.LOCAL_SET x0)
  | S.admininstr_LOCAL_TEE x0 => Some (S.LOCAL_TEE x0)
  | S.admininstr_GLOBAL_GET x0 => Some (S.GLOBAL_GET x0)
  | S.admininstr_GLOBAL_SET x0 => Some (S.GLOBAL_SET x0)
  | S.admininstr_TABLE_GET x0 => Some (S.TABLE_GET x0)
  | S.admininstr_TABLE_SET x0 => Some (S.TABLE_SET x0)
  | S.admininstr_TABLE_SIZE x0 => Some (S.TABLE_SIZE x0)
  | S.admininstr_TABLE_GROW x0 => Some (S.TABLE_GROW x0)
  | S.admininstr_TABLE_FILL x0 => Some (S.TABLE_FILL x0)
  | S.admininstr_TABLE_COPY x0 x1 => Some (S.TABLE_COPY x0 x1)
  | S.admininstr_TABLE_INIT x0 x1 => Some (S.TABLE_INIT x0 x1)
  | S.admininstr_ELEM_DROP x0 => Some (S.ELEM_DROP x0)
  | S.admininstr_LOAD x0 x1 x2 => Some (S.LOAD x0 x1 x2)
  | S.admininstr_STORE x0 x1 x2 => Some (S.STORE x0 x1 x2)
  | S.admininstr_VLOAD x0 x1 x2 => Some (S.VLOAD x0 x1 x2)
  | S.admininstr_VLOAD_LANE x0 x1 x2 x3 => Some (S.VLOAD_LANE x0 x1 x2 x3)
  | S.admininstr_VSTORE x0 x1 => Some (S.VSTORE x0 x1)
  | S.admininstr_VSTORE_LANE x0 x1 x2 x3 => Some (S.VSTORE_LANE x0 x1 x2 x3)
  | S.admininstr_MEMORY_SIZE => Some (S.MEMORY_SIZE)
  | S.admininstr_MEMORY_GROW => Some (S.MEMORY_GROW)
  | S.admininstr_MEMORY_FILL => Some (S.MEMORY_FILL)
  | S.admininstr_MEMORY_COPY => Some (S.MEMORY_COPY)
  | S.admininstr_MEMORY_INIT x0 => Some (S.MEMORY_INIT x0)
  | S.admininstr_DATA_DROP x0 => Some (S.DATA_DROP x0)
  | _ => None
  end.

Lemma instr_of_admin_inv a i : instr_of_admin a = Some i -> a = S.admininstr_instr i.
Proof. by case: a => //= *; match goal with H : Some _ = Some _ |- _ => case: H => <- end. Qed.

Lemma instr_of_admin_instr i : instr_of_admin (S.admininstr_instr i) = Some i.
Proof. by case: i. Qed.

Lemma tr_admin_instr i : tr_admin (S.admininstr_instr i) = AI_basic (tr_instr i).
Proof. by case: i. Qed.

Lemma wf_admin_of_instr i : S.wf_instr i -> S.wf_admininstr (S.admininstr_instr i).
Proof. case: i => /= *; match goal with H : S.wf_instr _ |- _ => inversion H; subst end; econstructor; eauto. Qed.

Lemma wf_instr_of_admin i : S.wf_admininstr (S.admininstr_instr i) -> S.wf_instr i.
Proof. case: i => /= *; match goal with H : S.wf_admininstr _ |- _ => inversion H; subst end; econstructor; eauto. Qed.

(** * Runtime structures *)

Lemma tr_of_externaddr v : tr_externaddr (of_externaddr v) = v.
Proof. by case: v. Qed.

Lemma of_tr_externaddr a : of_externaddr (tr_externaddr a) = a.
Proof. by case: a. Qed.

Lemma of_exportinst_sound e e' : of_exportinst e = Some e' -> tr_exportinst e' = e /\ S.wf_exportinst e'.
Proof.
  case: e => nm v. rewrite /of_exportinst /= => H. odestr H.
  case/of_name_sound: E => Hn Hw. rewrite /tr_exportinst /= Hn tr_of_externaddr.
  by split => //; constructor.
Qed.

Lemma of_exportinst_complete e : S.wf_exportinst e -> of_exportinst (tr_exportinst e) = Some e.
Proof. case=> nm a Hn. by rewrite /of_exportinst /= of_name_complete // of_tr_externaddr. Qed.

Lemma map_tr_of_functype fts : map tr_functype (map of_functype fts) = fts.
Proof. by rewrite -map_comp (eq_map tr_of_functype) map_id. Qed.

Lemma map_of_tr_functype fts : map of_functype (map tr_functype fts) = fts.
Proof. by rewrite -map_comp (eq_map of_tr_functype) map_id. Qed.

Lemma of_moduleinst_sound mi mi' :
  of_moduleinst mi = Some mi' -> tr_moduleinst mi' = mi /\ S.wf_moduleinst mi'.
Proof.
  case: mi => ty fu ta me gl el da ex. rewrite /of_moduleinst /= => H. odestr H.
  split; last first.
  - constructor. apply: olist_Forall E => x y /of_exportinst_sound []. done.
  - rewrite /tr_moduleinst /= map_tr_of_functype. f_equal.
    by apply: olist_inv E => x y /of_exportinst_sound [].
Qed.

Lemma of_moduleinst_complete mi : S.wf_moduleinst mi -> of_moduleinst (tr_moduleinst mi) = Some mi.
Proof.
  case=> ty fu gl ta me el da ex Hex. rewrite /of_moduleinst /= map_of_tr_functype.
  rewrite olist_map //. apply: List.Forall_impl Hex. exact: of_exportinst_complete.
Qed.

Lemma of_func_sound f f' : of_func vec_instr f = Some f' -> tr_func f' = f /\ S.wf_func f'.
Proof.
  case: f => x ls body. rewrite /of_func /= => H. odestr H.
  case/of_u32_sound: E => <- Hx. case/of_instrs_sound: E0 => <- Hb.
  rewrite /tr_func /= -map_comp. split; last by constructor.
  f_equal. by elim: ls => //= t ls ->; rewrite tr_of_valtype.
Qed.

Lemma of_func_complete f : S.wf_func f -> of_func vec_instr (tr_func f) = Some f.
Proof.
  case=> x ls body Hx Hb /=. rewrite /of_func /= of_u32_complete // of_instrs_complete //.
  f_equal. f_equal. rewrite -map_comp. by elim: ls => //= [[t]] ls ->; rewrite /of_local of_tr_valtype.
Qed.

Lemma of_funcinst_sound fi fi' :
  of_funcinst vec_instr fi = Some fi' -> tr_funcinst fi' = fi /\ S.wf_funcinst fi'.
Proof.
  case: fi => [ft mi f|ft hf] //= H. odestr H.
  case/of_moduleinst_sound: E => Emi Hmi. case/of_func_sound: E0 => Ef Hf.
  rewrite /tr_funcinst /= tr_of_functype Emi Ef. by split => //; constructor.
Qed.

Lemma of_funcinst_complete fi :
  S.wf_funcinst fi -> of_funcinst vec_instr (tr_funcinst fi) = Some fi.
Proof.
  case=> ft mi f Hmi Hf /=.
  by rewrite /tr_funcinst /= of_moduleinst_complete // of_func_complete // of_tr_functype.
Qed.

Lemma of_globalinst_sound g g' :
  of_globalinst g = Some g' -> tr_globalinst g' = g /\ S.wf_globalinst g'.
Proof.
  case: g => t v. rewrite /of_globalinst /= => H. odestr H.
  case/of_val_sound: E => Ev Hv. rewrite /tr_globalinst; cbn [S.globalinst_TYPE S.VALUE]; rewrite tr_of_globaltype Ev.
  by split => //; constructor.
Qed.

Lemma of_globalinst_complete g : S.wf_globalinst g -> of_globalinst (tr_globalinst g) = Some g.
Proof. case=> t v Hv. by rewrite /of_globalinst /= of_val_complete // of_tr_globaltype. Qed.

Lemma map_tr_of_ref rs : map tr_ref (map of_ref rs) = rs.
Proof. by rewrite -map_comp (eq_map tr_of_ref) map_id. Qed.

Lemma map_of_tr_ref rs : map of_ref (map tr_ref rs) = rs.
Proof. by rewrite -map_comp (eq_map of_tr_ref) map_id. Qed.

Lemma of_tableinst_sound t t' :
  of_tableinst t = Some t' -> tr_tableinst t' = t /\ S.wf_tableinst t'.
Proof.
  case: t => tt rs. rewrite /of_tableinst /= => H. odestr H.
  case/of_tabletype_sound: E => Et Ht. rewrite /tr_tableinst; cbn [S.tableinst_TYPE S.REFS]; rewrite Et map_tr_of_ref.
  by split => //; constructor.
Qed.

Lemma of_tableinst_complete t : S.wf_tableinst t -> of_tableinst (tr_tableinst t) = Some t.
Proof. case=> tt rs Ht. by rewrite /of_tableinst /= of_tabletype_complete // map_of_tr_ref. Qed.

Lemma tr_of_byte b : tr_byte (of_byte b) = b.
Proof.
  rewrite /tr_byte /of_byte Z2N.id; first exact: Integers.Byte.repr_unsigned.
  by case: (Integers.Byte.unsigned_range b).
Qed.

Lemma of_byte_wf b : S.wf_byte (of_byte b).
Proof.
  apply: wf_byte_lt. have := Integers.Byte.unsigned_range_2 b.
  change Integers.Byte.max_unsigned with 255%Z. lia.
Qed.

Lemma of_tr_byte b : S.wf_byte b -> of_byte (tr_byte b) = b.
Proof.
  case=> n /andP [_ /N.leb_spec0 Hn]. rewrite /of_byte /tr_byte Integers.Byte.unsigned_repr.
  - by rewrite N2Z.id.
  - change Integers.Byte.max_unsigned with 255%Z. lia.
Qed.

Lemma map_tr_of_byte bs : map tr_byte (map of_byte bs) = bs.
Proof. by rewrite -map_comp (eq_map tr_of_byte) map_id. Qed.

Lemma map_of_byte_wf bs : List.Forall S.wf_byte (map of_byte bs).
Proof. elim: bs => //= b l IH. constructor => //. exact: of_byte_wf. Qed.

Lemma map_of_tr_byte bs : List.Forall S.wf_byte bs -> map of_byte (map tr_byte bs) = bs.
Proof. elim=> // b l Hb _ IH. by rewrite map_cons map_cons of_tr_byte // IH. Qed.

Lemma of_meminst_sound m m' : of_meminst m = Some m' -> tr_meminst m' = m /\ S.wf_meminst m'.
Proof.
  case: m => mt [init bs]. rewrite /of_meminst /= => H. odestr H.
  case/of_memtype_sound: E => Et Ht. split; last by constructor => //; exact: map_of_byte_wf.
  rewrite /tr_meminst /tr_mem_data. cbn [S.meminst_TYPE S.BYTES]. rewrite Et map_tr_of_byte.
  have -> // : init = Integers.Byte.zero.
  have := Integers.Byte.eq_spec init Integers.Byte.zero. by rewrite E0.
Qed.

Lemma of_meminst_complete m : S.wf_meminst m -> of_meminst (tr_meminst m) = Some m.
Proof.
  case=> mt bs Ht Hbs. rewrite /of_meminst /tr_meminst /tr_mem_data /=.
  by rewrite of_memtype_complete // map_of_tr_byte.
Qed.

Lemma tr_of_eleminst e : tr_eleminst (of_eleminst e) = e.
Proof. case: e => t rs. by rewrite /tr_eleminst /of_eleminst /= tr_of_reftype map_tr_of_ref. Qed.

Lemma of_tr_eleminst e : of_eleminst (tr_eleminst e) = e.
Proof. case: e => t rs. by rewrite /tr_eleminst /of_eleminst /= of_tr_reftype map_of_tr_ref. Qed.

Lemma tr_of_datainst d : tr_datainst (of_datainst d) = d.
Proof. case: d => bs. by rewrite /tr_datainst /of_datainst /= map_tr_of_byte. Qed.

Lemma of_datainst_wf d : S.wf_datainst (of_datainst d).
Proof. constructor. exact: map_of_byte_wf. Qed.

Lemma of_tr_datainst d : S.wf_datainst d -> of_datainst (tr_datainst d) = d.
Proof. case=> bs Hbs. by rewrite /tr_datainst /of_datainst /= map_of_tr_byte. Qed.

Lemma of_store_sound s s' : of_store vec_instr s = Some s' -> tr_store s' = s /\ S.wf_store s'.
Proof.
  case: s => fs ts ms gs es ds. rewrite /of_store /= => H. odestr H.
  split.
  - rewrite /tr_store; cbn [S.store_FUNCS S.store_GLOBALS S.store_TABLES S.store_MEMS
                             S.store_ELEMS S.store_DATAS].
    rewrite (olist_inv _ E) ?(olist_inv _ E0) ?(olist_inv _ E1) ?(olist_inv _ E2);
      try (move=> x y; first [ case/of_funcinst_sound | case/of_globalinst_sound
                             | case/of_tableinst_sound | case/of_meminst_sound ]; done).
    by rewrite -!map_comp (eq_map tr_of_eleminst) (eq_map tr_of_datainst) !map_id.
  - constructor.
    + apply: olist_Forall E => x y /of_funcinst_sound []; done.
    + apply: olist_Forall E0 => x y /of_globalinst_sound []; done.
    + apply: olist_Forall E1 => x y /of_tableinst_sound []; done.
    + apply: olist_Forall E2 => x y /of_meminst_sound []; done.
    + apply/List.Forall_forall => d /List.in_map_iff [d' [<- _]]. exact: of_datainst_wf.
Qed.

Lemma of_store_complete s :
  S.wf_store s -> of_store vec_instr (tr_store s) = Some s.
Proof.
  case=> fs gs ts ms es ds Hfs Hgs Hts Hms Hds.
  rewrite /of_store /= !olist_map.
  - rewrite -map_comp (eq_map of_tr_eleminst) map_id. do 2 f_equal.
    elim: Hds => // d l Hd _ IH. by rewrite map_cons map_cons of_tr_datainst // IH.
  - apply: List.Forall_impl Hms. exact: of_meminst_complete.
  - apply: List.Forall_impl Hts. exact: of_tableinst_complete.
  - apply: List.Forall_impl Hgs. exact: of_globalinst_complete.
  - apply: List.Forall_impl Hfs. exact: of_funcinst_complete.
Qed.

Lemma of_frame_sound f f' : of_frame f = Some f' -> tr_frame f' = f /\ S.wf_frame f'.
Proof.
  case: f => vs mi. rewrite /of_frame /= => H. odestr H.
  case/of_moduleinst_sound: E0 => Emi Hmi. split.
  - rewrite /tr_frame; cbn [S.LOCALS S.frame_MODULE]. rewrite Emi.
    by rewrite (olist_inv _ E) // => x y /of_val_sound [].
  - constructor => //. apply: olist_Forall E => x y /of_val_sound []; done.
Qed.

Lemma of_frame_complete f : S.wf_frame f -> of_frame (tr_frame f) = Some f.
Proof.
  case=> vs mi Hvs Hmi. rewrite /of_frame /tr_frame /= of_moduleinst_complete //.
  rewrite olist_map //. apply: List.Forall_impl Hvs. exact: of_val_complete.
Qed.

(** * Administrative instructions *)

Definition admin_sound_at (e : administrative_instruction) : Prop :=
  forall a, of_admin vec_instr e = Some a -> tr_admin a = e /\ S.wf_admininstr a.

Lemma cont_sound cont ins :
  olist (fun e => match e with AI_basic b => of_instr vec_instr b | _ => None end) cont = Some ins ->
  to_e_list (tr_instrs ins) = cont /\ List.Forall S.wf_instr ins.
Proof.
  elim: cont ins => [|e cont IH] ins /=; first by case=> <-.
  case: e => // b. case E: (of_instr vec_instr b) => [i|] //.
  case E': (olist _ cont) => [l'|] // [<-].
  case/of_instr_sound: E => <- Hi. case: (IH _ E') => <- His. by split => //; constructor.
Qed.

Lemma label_sound n cont es :
  (forall y, List.In y es -> admin_sound_at y) -> admin_sound_at (AI_label n cont es).
Proof.
  move=> Hes a /= H. odestr H. case/cont_sound: E => Ec Hc.
  case/(olist_in_sound Hes): E0 => Ees Hw.
  rewrite /= Nat2N.id Ec /tr_admins Ees. by split => //; constructor.
Qed.

Lemma frame_sound n f es :
  (forall y, List.In y es -> admin_sound_at y) -> admin_sound_at (AI_frame n f es).
Proof.
  move=> Hes a /= H. odestr H. case/of_frame_sound: E => Ef Hf.
  case/(olist_in_sound Hes): E0 => Ees Hw.
  rewrite /= Nat2N.id Ef Ees. by split => //; constructor.
Qed.

Lemma of_admin_sound : forall e, admin_sound_at e.
Proof.
  fix IH 1. case.
  - move=> b a /= H. odestr H. case/of_instr_sound: E => <- Hw.
    rewrite tr_admin_instr. split => //. exact: wf_admin_of_instr.
  - by move=> a /= [<-]; split => //; constructor.
  - by move=> x a /= [<-]; split => //; constructor.
  - by move=> x a /= [<-]; split => //; constructor.
  - by move=> x a /= [<-]; split => //; constructor.
  - move=> x a H. discriminate H.
  - move=> n cont es. apply: label_sound. in_ih IH.
  - move=> n f es. apply: frame_sound. in_ih IH.
Qed.

Lemma of_admins_sound es as' :
  of_admins vec_instr es = Some as' -> tr_admins as' = es /\ List.Forall S.wf_admininstr as'.
Proof. apply: olist_in_sound => y _. exact: of_admin_sound. Qed.

Definition admin_complete_at (a : S.admininstr) : Prop :=
  S.wf_admininstr a -> of_admin vec_instr (tr_admin a) = Some a.

Lemma admin_instr_complete a i : instr_of_admin a = Some i -> admin_complete_at a.
Proof.
  move/instr_of_admin_inv => -> /wf_instr_of_admin Hw.
  by rewrite tr_admin_instr /= of_instr_complete.
Qed.

Lemma label_complete n ins es :
  (forall y, List.In y es -> admin_complete_at y) -> admin_complete_at (S.LABEL_ n ins es).
Proof.
  move=> Hes Hw /=. inversion Hw; subst.
  match goal with H : List.Forall _ ins |- _ => rename H into Hwi end.
  match goal with H : List.Forall _ es |- _ => rename H into Hwe end.
  rewrite N2Nat.id /to_e_list /tr_instrs -map_comp olist_map; last first.
  { apply: List.Forall_impl Hwi. exact: of_instr_complete. }
  rewrite olist_map //. elim: es Hes Hwe {Hw} => // e l IHl Hes /List.Forall_cons_iff [He Hl].
  constructor; first by apply: Hes => //; left.
  apply: IHl => // y Hy. apply: Hes. by right.
Qed.

Lemma frame_complete n f es :
  (forall y, List.In y es -> admin_complete_at y) -> admin_complete_at (S.FRAME_ n f es).
Proof.
  move=> Hes Hw /=. inversion Hw; subst.
  match goal with H : S.wf_frame _ |- _ => rename H into Hf end.
  match goal with H : List.Forall _ es |- _ => rename H into Hwe end.
  rewrite N2Nat.id of_frame_complete // olist_map //.
  elim: es Hes Hwe {Hw} => // e l IHl Hes /List.Forall_cons_iff [He Hl].
  constructor; first by apply: Hes => //; left.
  apply: IHl => // y Hy. apply: Hes. by right.
Qed.

Lemma of_admin_complete : forall a, admin_complete_at a.
Proof.
  fix IH 1. case.
  all: try (by move=> n ins es; apply: label_complete; in_ih IH).
  all: try (by move=> n f es; apply: frame_complete; in_ih IH).
  all: try (by intros; apply: admin_instr_complete; reflexivity).
  all: intros; rewrite /admin_complete_at => _; reflexivity.
Qed.

Lemma of_admins_complete as' :
  List.Forall S.wf_admininstr as' -> of_admins vec_instr (tr_admins as') = Some as'.
Proof.
  elim=> // a l Ha _ IH /=.
  by rewrite (of_admin_complete Ha) IH.
Qed.

(** * Configurations *)

Lemma of_config_sound s f es c :
  of_config vec_instr s f es = Some c ->
  exists s' f' es', c = S.mk_config (S.mk_state s' f') es' /\
    tr_store s' = s /\ tr_frame f' = f /\ tr_admins es' = es /\ S.wf_config c.
Proof.
  rewrite /of_config => H. odestr H.
  case/of_store_sound: E => Es Hs. case/of_frame_sound: E0 => Ef Hf.
  case/of_admins_sound: E1 => Ees Hes.
  exists s0, f0, l. by do 4 (split => //); repeat constructor.
Qed.

Lemma of_config_complete s f es :
  S.wf_config (S.mk_config (S.mk_state s f) es) ->
  of_config vec_instr (tr_store s) (tr_frame f) (tr_admins es) = Some (S.mk_config (S.mk_state s f) es).
Proof.
  move=> Hw. inversion Hw as [z es' Hz Hwes]; subst. inversion Hz; subst.
  by rewrite /of_config of_store_complete // of_frame_complete // of_admins_complete.
Qed.

End Instructions.

(** * Typing contexts *)

Lemma map_tr_of_globaltype gs : map tr_globaltype (map of_globaltype gs) = gs.
Proof. by rewrite -map_comp (eq_map tr_of_globaltype) map_id. Qed.

Lemma map_of_tr_globaltype gs : map of_globaltype (map tr_globaltype gs) = gs.
Proof. by rewrite -map_comp (eq_map of_tr_globaltype) map_id. Qed.

Lemma map_tr_of_reftype ts : map tr_reftype (map of_reftype ts) = ts.
Proof. by rewrite -map_comp (eq_map tr_of_reftype) map_id. Qed.

Lemma map_of_tr_reftype ts : map of_reftype (map tr_reftype ts) = ts.
Proof. by rewrite -map_comp (eq_map of_tr_reftype) map_id. Qed.

Lemma map_tr_of_resulttype ts : map tr_resulttype (map of_resulttype ts) = ts.
Proof. by rewrite -map_comp (eq_map tr_of_resulttype) map_id. Qed.

Lemma map_of_tr_resulttype ts : map of_resulttype (map tr_resulttype ts) = ts.
Proof. by rewrite -map_comp (eq_map of_tr_resulttype) map_id. Qed.

(* The back-translated context is well-formed, and translates back to the
   original one, except for [tc_refs], which SpecTec does not have. *)
Lemma of_context_sound C C' :
  of_context C = Some C' ->
  S.wf_context C' /\
  tr_context C' = Build_t_context (tc_types C) (tc_funcs C) (tc_tables C) (tc_mems C) (tc_globals C)
                    (tc_elems C) (tc_datas C) (tc_locals C) (tc_labels C) (tc_return C)
                    (iota_N 0 (size (tc_funcs C))).
Proof.
  case: C => ty fu ta me gl el da lo la re rf. rewrite /of_context /= => H. odestr H.
  split.
  - constructor.
    + apply: olist_Forall E => x y /of_tabletype_sound []; done.
    + apply: olist_Forall E0 => x y /of_memtype_sound []; done.
  - rewrite /tr_context.
    cbn [S.context_TYPES S.context_FUNCS S.context_GLOBALS S.context_TABLES S.context_MEMS
         S.context_ELEMS S.context_DATAS S.context_LOCALS S.LABELS S.context_RETURN].
    rewrite !map_tr_of_functype map_tr_of_globaltype map_tr_of_reftype map_tr_of_valtype
            map_tr_of_resulttype size_map.
    rewrite (olist_inv _ E); last by move=> x y /of_tabletype_sound [].
    rewrite (olist_inv _ E0); last by move=> x y /of_memtype_sound [].
    have -> : [seq tt | _ <- [seq S.OK | _ <- da]] = da by elim: da => //= [[]] da ->.
    case: re => [r|] //. cbn [option_map]. by rewrite tr_of_resulttype.
Qed.

Lemma of_context_complete C : S.wf_context C -> of_context (tr_context C) = Some C.
Proof.
  case=> ty fu gl ta me el da lo la re Hta Hme. rewrite /of_context /tr_context /=.
  rewrite !olist_map; last 2 first.
  - apply: List.Forall_impl Hme. exact: of_memtype_complete.
  - apply: List.Forall_impl Hta. exact: of_tabletype_complete.
  rewrite !map_of_tr_functype map_of_tr_globaltype map_of_tr_reftype map_of_tr_valtype
          map_of_tr_resulttype.
  have -> : [seq S.OK | _ <- [seq tt | _ <- da]] = da by elim: da => //= [[]] da ->.
  case: re => [r|] //. cbn [option_map]. by rewrite of_tr_resulttype.
Qed.

(** * Examples *)

(* A block, with the SIMD decoder left empty. *)
Example of_instr_block :
  of_instr (fun _ => None)
    (BI_block (BT_valtype None) [:: BI_const_num (VAL_int32 Wasm_int.Int32.one); BI_drop])
  = Some (S.BLOCK (S._RESULT None) [:: S.CONST S.I32 (S.mk_num__0 S.Inn_I32 (S.mk_uN 1%num)); S.DROP]).
Proof. by vm_compute. Qed.

(* Tail calls are not part of Wasm 2.0. *)
Example of_instr_return_call : of_instr (fun _ => None) (BI_return_call 0%num) = None.
Proof. by []. Qed.

(* Indices must fit in a u32. *)
Example of_instr_big_label : of_instr (fun _ => None) (BI_br 4294967296%num) = None.
Proof. by vm_compute. Qed.

(* "hé" in UTF-8. *)
Example of_name_utf8 :
  of_name [:: Byte.x68; Byte.xc3; Byte.xa9] = Some (S.mk_name [:: S.mk_char 104%num; S.mk_char 233%num]).
Proof. by vm_compute. Qed.

(* Truncated and overlong encodings are rejected. *)
Example of_name_truncated : of_name [:: Byte.xc3] = None.
Proof. by vm_compute. Qed.

Example of_name_overlong : of_name [:: Byte.xc1; Byte.xa9] = None.
Proof. by vm_compute. Qed.

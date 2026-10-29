(* Typing preservation for configurations: if SpecTec types a configuration
   ([Config_ok]), WasmCert types its translation ([config_typing]): the
   translated store is valid ([store_typing]) and the translated thread is
   typed at the translated result type ([thread_typing]).

   WasmCert computes the context of a module instance from the store
   ([inst_typing]), with the exact types of the tables and memories it
   refers to, whereas SpecTec's [Moduleinst_ok] may assign them supertypes
   (larger limits).  Instruction typing only depends on the element types of
   tables and on the number of memories, so the two contexts type the same
   code ([be_typing_equiv]). *)

From Stdlib Require Import NArith ZArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From Wasm Require Import datatypes datatypes_properties operations typing subtyping list_extra typing_inversion.
From Wasm Require memory_list.
From WasmSpectec Require wasm.
From WasmCertBridge Require Import translation.
From WasmCertBridge Require typing.

Module S := WasmSpectec.wasm.
Module T := WasmCertBridge.typing.

(* The eqType instances of SpecTec's types, without its names. *)
Import (canonicals) WasmSpectec.wasm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope N_scope with num.

(** * Contexts that differ only in table and memory limits *)

Record ctx_equiv (C1 C2 : t_context) : Prop := {
  ce_types : tc_types C1 = tc_types C2;
  ce_funcs : tc_funcs C1 = tc_funcs C2;
  ce_tables : map tt_elem_type (tc_tables C1) = map tt_elem_type (tc_tables C2);
  ce_mems : size (tc_mems C1) = size (tc_mems C2);
  ce_globals : tc_globals C1 = tc_globals C2;
  ce_elems : tc_elems C1 = tc_elems C2;
  ce_datas : tc_datas C1 = tc_datas C2;
  ce_locals : tc_locals C1 = tc_locals C2;
  ce_labels : tc_labels C1 = tc_labels C2;
  ce_return : tc_return C1 = tc_return C2;
  ce_refs : tc_refs C1 = tc_refs C2 }.

Lemma ctx_equiv_refl C : ctx_equiv C C.
Proof. by []. Qed.

Lemma ctx_equiv_sym C1 C2 : ctx_equiv C1 C2 -> ctx_equiv C2 C1.
Proof. by case=> *; constructor. Qed.

Lemma ctx_equiv_trans C1 C2 C3 : ctx_equiv C1 C2 -> ctx_equiv C2 C3 -> ctx_equiv C1 C3.
Proof. move=> [? ? ? ? ? ? ? ? ? ? ?] [? ? ? ? ? ? ? ? ? ? ?]; constructor; congruence. Qed.

Lemma ctx_equiv_label C1 C2 lab :
  ctx_equiv C1 C2 -> ctx_equiv (upd_label C1 (lab :: tc_labels C1)) (upd_label C2 (lab :: tc_labels C2)).
Proof. by case=> *; constructor => //=; congruence. Qed.

Lemma lookup_N_map_eq {A B : Type} (f : A -> B) l1 l2 n x :
  map f l1 = map f l2 -> lookup_N l1 n = Some x -> exists y, lookup_N l2 n = Some y /\ f y = f x.
Proof.
  rewrite /lookup_N. move: (N.to_nat n) => k.
  elim: l1 l2 k => [|a l1 IH] [|b l2] [|k] //= [Hab Hl] H.
  - case: H => <-. by exists b.
  - exact: IH.
Qed.

Lemma lookup_N_size {A B : Type} (l1 : seq A) (l2 : seq B) n x :
  size l1 = size l2 -> lookup_N l1 n = Some x -> exists y, lookup_N l2 n = Some y.
Proof.
  rewrite /lookup_N. move: (N.to_nat n) => k.
  elim: l1 l2 k => [|a l1 IH] [|b l2] [|k] //= [Hl] H.
  - by exists b.
  - exact: IH.
Qed.

Lemma expand_t_types C1 C2 tb : tc_types C1 = tc_types C2 -> expand_t C1 tb = expand_t C2 tb.
Proof. by case: tb => //= x ->. Qed.

Section BeTyping.

Context `{hfc : host_function_class}.

Lemma be_typing_equiv C1 es tf :
  be_typing C1 es tf -> forall C2, ctx_equiv C1 C2 -> be_typing C2 es tf.
Proof.
  elim=> {C1 es tf}.
  all: intros; match goal with H : ctx_equiv _ _ |- _ =>
         have HCE := H; destruct H as [HT HF HTa HM HG HE HD HL HLab HR HRf] end.
  all: repeat match goal with
       | H : lookup_N (tc_tables _) _ = Some _ |- _ =>
           let t := fresh "tab" in let Ht := fresh "Ht" in let Ht' := fresh "Hel" in
           case: (lookup_N_map_eq HTa H) => t [Ht Ht']; clear H
       | H : lookup_N (tc_mems _) _ = Some _ |- _ =>
           let m := fresh "mem" in let Hm := fresh "Hm" in
           case: (lookup_N_size HM H) => m Hm; clear H
       end.
  all: try (by econstructor; rewrite -?HT -?HF -?HG -?HE -?HD -?HL -?HLab -?HR -?HRf; eauto; congruence).
  all: try (by eapply bet_composition; eauto).
  all: try (by eapply bet_subtyping; eauto).
  all: have Hx := expand_t_types tb HT; rewrite Hx in H.
  - eapply bet_block; eauto. by apply: H1; apply: ctx_equiv_label.
  - eapply bet_loop; eauto. by apply: H1; apply: ctx_equiv_label.
  - eapply bet_if_wasm; eauto; [apply: H1 | apply: H3]; by apply: ctx_equiv_label.
Qed.

End BeTyping.

(** * Addresses, references and values *)

Section Store.

Context `{hfc : host_function_class}.

Lemma ext_func_inv s a ft :
  S.Externaddr_ok s (S.externaddr_FUNC a) (S.FUNC ft) ->
  (a < N.of_nat (size (S.store_FUNCS s)))%num /\ S.funcinst_TYPE (S.lookup_total (S.store_FUNCS s) a) = ft.
Proof.
  move Ex: (S.externaddr_FUNC a) => x. move Et: (S.FUNC ft) => xt H.
  elim: H a ft Ex Et => {s x xt} [s a' g Hlt Hg _ _ | s a' g Hlt Hg _ _ | s a' g Hlt Hg _ _ | s a' g Hlt Hg _ _ | s x xt xt' _ IH Hsub _ _ _] a0 t0 Ex Et; try discriminate.
  - case: Ex => ?; case: Et => ?; subst. move/N.ltb_spec0: Hlt => Hlt. split => //. by move/eqP: Hg => ->.
  - subst. inversion Hsub as [ft1 ft2 Hf _ _ | | |]; subst. inversion Hf; subst. exact: IH.
Qed.

Lemma ext_table_inv s a tt :
  S.Externaddr_ok s (S.externaddr_TABLE a) (S.TABLE tt) ->
  (a < N.of_nat (size (S.store_TABLES s)))%num /\
  tt_elem_type (tr_tabletype (S.tableinst_TYPE (S.lookup_total (S.store_TABLES s) a))) =
  tt_elem_type (tr_tabletype tt).
Proof.
  move Ex: (S.externaddr_TABLE a) => x. move Et: (S.TABLE tt) => xt H.
  elim: H a tt Ex Et => {s x xt} [s a' g Hlt Hg _ _ | s a' g Hlt Hg _ _ | s a' g Hlt Hg _ _ | s a' g Hlt Hg _ _ | s x xt xt' _ IH Hsub _ _ _] a0 t0 Ex Et; try discriminate.
  - case: Ex => ?; case: Et => ?; subst. move/N.ltb_spec0: Hlt => Hlt. split => //. by move/eqP: Hg => ->.
  - subst. inversion Hsub as [| | tt1 tt2 Ht _ _ |]; subst. inversion Ht; subst.
    by case: (IH _ _ erefl erefl) => Hlt' ->.
Qed.

Lemma ext_mem_inv s a mt :
  S.Externaddr_ok s (S.externaddr_MEM a) (S.MEM mt) -> (a < N.of_nat (size (S.store_MEMS s)))%num.
Proof.
  move Ex: (S.externaddr_MEM a) => x. move Et: (S.MEM mt) => xt H.
  elim: H a mt Ex Et => {s x xt} [s a' g Hlt Hg _ _ | s a' g Hlt Hg _ _ | s a' g Hlt Hg _ _ | s a' g Hlt Hg _ _ | s x xt xt' _ IH Hsub _ _ _] a0 t0 Ex Et; try discriminate.
  - case: Ex => ?; subst. exact/N.ltb_spec0.
  - subst. inversion Hsub as [| | | mt1 mt2 Hm _ _]; subst. exact: IH.
Qed.

Lemma ext_global_inv s a gt :
  S.Externaddr_ok s (S.externaddr_GLOBAL a) (S.GLOBAL gt) ->
  (a < N.of_nat (size (S.store_GLOBALS s)))%num /\
  S.globalinst_TYPE (S.lookup_total (S.store_GLOBALS s) a) = gt.
Proof.
  move Ex: (S.externaddr_GLOBAL a) => x. move Et: (S.GLOBAL gt) => xt H.
  elim: H a gt Ex Et => {s x xt} [s a' g Hlt Hg _ _ | s a' g Hlt Hg _ _ | s a' g Hlt Hg _ _ | s a' g Hlt Hg _ _ | s x xt xt' _ IH Hsub _ _ _] a0 t0 Ex Et; try discriminate.
  - case: Ex => ?; case: Et => ?; subst. move/N.ltb_spec0: Hlt => Hlt. split => //. by move/eqP: Hg => ->.
  - subst. inversion Hsub as [| gt1 gt2 Hg' _ _ | |]; subst. inversion Hg'; subst. exact: IH.
Qed.

Lemma lookup_N_tr {A B : Type} `{S.Inhabited A} (f : A -> B) (l : seq A) (n : N) :
  (n < N.of_nat (size l))%num -> lookup_N (map f l) n = Some (f (S.lookup_total l n)).
Proof. move=> /N.ltb_spec0 Hn. exact: T.lookup_N_map. Qed.

Lemma ext_func_typing_tr s a ft :
  S.Externaddr_ok s (S.externaddr_FUNC a) (S.FUNC ft) ->
  ext_func_typing (tr_store s) a = Some (tr_functype ft).
Proof.
  case/ext_func_inv => Hlt Hty. rewrite /ext_func_typing /= lookup_N_tr //.
  by rewrite /tr_funcinst /= Hty.
Qed.

Lemma ref_typing_tr s r rt :
  S.Ref_ok s r rt -> value_typing (tr_store s) (VAL_ref (tr_ref r)) (T_ref (tr_reftype rt)).
Proof.
  case=> {s r rt} [s rt _ | s a ext Ha _ _ | s a _];
    rewrite /value_typing /= ?(ext_func_typing_tr Ha) /value_subtyping /=; by rewrite ?eqxx.
Qed.

Lemma val_typing_tr s v t :
  S.Val_ok s v t -> value_typing (tr_store s) (tr_val v) (tr_valtype t).
Proof.
  case=> {s v t} [s nt c _ Hw | s vt c _ _ | s r rt Hr _].
  - inversion Hw as [? ? Hc| | | |]; subst. rewrite /value_typing /= (T.wf_num_typeof Hc) T.tr_valtype_num.
    by rewrite /value_subtyping eqxx.
  - case: vt. by rewrite /value_typing /= /value_subtyping eqxx.
  - have := ref_typing_tr Hr. rewrite T.tr_valtype_ref. by case: r {Hr}.
Qed.

(** * Module instances *)

Lemma those_Forall2 {A B : Type} (f : A -> option B) l l' :
  List.Forall2 (fun a b => f a = Some b) l l' -> those (map f l) = Some l'.
Proof. move=> H. rewrite -those_those0. by elim: H => //= a b l1 l2 -> _ ->. Qed.

Lemma Forall2_map_r {A B C : Type} (P : A -> C -> Prop) (g : B -> C) l l' :
  List.Forall2 (fun a b => P a (g b)) l l' -> List.Forall2 P l (map g l').
Proof. by elim=> //= *; constructor. Qed.

Lemma Forall2_impl2 {A B : Type} (P Q : A -> B -> Prop) l l' :
  (forall a b, P a b -> Q a b) -> List.Forall2 P l l' -> List.Forall2 Q l l'.
Proof. move=> H. by elim=> //= *; constructor; auto. Qed.

Lemma length_size {A : Type} (l : seq A) : length l = size l.
Proof. by elim: l => //= ? ? ->. Qed.

Lemma size_N_eq {A B : Type} (l : seq A) (l' : seq B) :
  N.of_nat (size l) == N.of_nat (size l') -> size l = size l'.
Proof. by move/eqP/Nat2N.inj. Qed.

Lemma eleminst_typing_tr s ei et :
  S.Eleminst_ok s ei et -> eleminst_typing (tr_store s) (tr_eleminst ei) = Some (tr_reftype et).
Proof.
  case=> {s ei et} s rt refs Hrefs _ _. rewrite /eleminst_typing /tr_eleminst /=.
  have -> : all (fun r => value_typing (tr_store s) (VAL_ref r) (T_ref (tr_reftype rt))) (map tr_ref refs).
  { elim: Hrefs => //= r l Hr _ ->. by rewrite (ref_typing_tr Hr). }
  by [].
Qed.

Lemma inst_typing_tr s mi C :
  S.Moduleinst_ok s mi C ->
  exists C0, inst_typing (tr_store s) (tr_moduleinst mi) = Some C0 /\ ctx_equiv C0 (tr_context C).
Proof.
  case=> {s mi C} s fts fas gas tas mas eas das exps ftFs gts tts mts ets dts
    _ Hgsz Hg Hfsz Hf Hmsz Hm Htsz Ht _ Hdsz Hdb Hd Hesz Heb He *.
  have Ef : those (map (ext_func_typing (tr_store s)) fas) = Some (map tr_functype ftFs).
  { apply: those_Forall2. apply: Forall2_map_r. apply: Forall2_impl2 Hf => a ft.
    exact: ext_func_typing_tr. }
  have Et : those (map (ext_table_typing (tr_store s)) tas) =
            Some (map (fun a => tr_tabletype (S.tableinst_TYPE (S.lookup_total (S.store_TABLES s) a))) tas).
  { apply: those_Forall2. elim: Ht {Htsz} => //= a tt l l' Ha _ IH. constructor => //.
    case/ext_table_inv: Ha => Hlt _. by rewrite /ext_table_typing /= lookup_N_tr. }
  have Em : those (map (ext_mem_typing (tr_store s)) mas) =
            Some (map (fun a => tr_memtype (S.meminst_TYPE (S.lookup_total (S.store_MEMS s) a))) mas).
  { apply: those_Forall2. elim: Hm {Hmsz} => //= a mt l l' Ha _ IH. constructor => //.
    have Hlt := ext_mem_inv Ha. by rewrite /ext_mem_typing /= lookup_N_tr. }
  have Eg : those (map (ext_global_typing (tr_store s)) gas) = Some (map tr_globaltype gts).
  { apply: those_Forall2. apply: Forall2_map_r. apply: Forall2_impl2 Hg => a gt.
    case/ext_global_inv => Hlt Hgt. by rewrite /ext_global_typing /= lookup_N_tr // /tr_globalinst /= Hgt. }
  have Ee : those (map (fun a => match lookup_N (s_elems (tr_store s)) a with
                                 | Some ei => eleminst_typing (tr_store s) ei
                                 | None => None end) eas) = Some (map tr_reftype ets).
  { apply: those_Forall2. apply: Forall2_map_r.
    elim: He Heb {Hesz} => //= a et l l' Ha _ IH /List.Forall_cons_iff [/N.ltb_spec0 Hlt Hl].
    constructor; last exact: IH.
    by rewrite lookup_N_tr // (eleminst_typing_tr Ha). }
  have Ed : those (map (fun a => match lookup_N (s_datas (tr_store s)) a with
                                 | Some di => datainst_typing (tr_store s) di
                                 | None => None end) das) = Some (map (fun _ => tt) dts).
  { apply: those_Forall2. apply: Forall2_map_r.
    elim: Hd Hdb {Hdsz} => //= a dt l l' Ha _ IH /List.Forall_cons_iff [/N.ltb_spec0 Hlt Hl].
    constructor; last exact: IH.
    by rewrite lookup_N_tr. }
  eexists. split.
  - rewrite /inst_typing /tr_moduleinst. cbn [inst_types inst_funcs inst_tables inst_mems inst_globals
      inst_elems inst_datas inst_exports].
    rewrite Ef Et Em Eg Ee Ed.
    have -> : forall l, all functype_valid l by elim.
    reflexivity.
  - constructor => //=.
    + rewrite -!map_comp. elim: Ht {Htsz} => //= a tt l l' Ha _ ->.
      by case/ext_table_inv: Ha => _ ->.
    + by rewrite !size_map (size_N_eq Hmsz).
    + by rewrite length_size (size_N_eq Hfsz).
Qed.

(** * Frames *)

Lemma moduleinst_ctx s mi C :
  S.Moduleinst_ok s mi C ->
  S.context_LOCALS C = [::] /\ S.LABELS C = [::] /\ S.context_RETURN C = None.
Proof. by case. Qed.

Lemma values_typing_tr s ts vs :
  List.Forall2 (fun t v => S.Val_ok s v t) ts vs ->
  values_typing (tr_store s) (map tr_val vs) (map tr_valtype ts).
Proof. by elim=> //= t v ts' vs' Hv _ IH; rewrite /values_typing /= (val_typing_tr Hv). Qed.

(* The context of a frame: the module's context with the frame's locals. *)
Lemma frame_typing_tr s f C' :
  S.Frame_ok s f C' ->
  exists CW, frame_typing (tr_store s) (tr_frame f) CW /\ ctx_equiv CW (tr_context C') /\
             S.LABELS C' = [::] /\ S.context_RETURN C' = None.
Proof.
  case=> {s f C'} s vs mi ts C Hmi _ Hvs _ _ _ _.
  case: (inst_typing_tr Hmi) => C0 [Hi He].
  case: (moduleinst_ctx Hmi) => HL [HLab HR].
  exists (upd_local C0 (map tr_valtype ts ++ tc_locals C0)). split; last split.
  - rewrite /frame_typing /tr_frame; cbn [f_inst f_locs]. rewrite Hi. exists (map tr_valtype ts). split => //.
    exact: values_typing_tr.
  - case: C Hmi He HL HLab HR => ty fu gl ta me el da lo la re /= Hmi
      [HT HF HTa HM HG HE HD HL' HLab' HR' HRf] HL HLab HR. subst.
    constructor => /=; try assumption.
    rewrite HL'. change (S._append ts [::]) with (ts ++ [::]). by rewrite !cats0.
  - case: C Hmi He HL HLab HR => ? ? ? ? ? ? ? ? ? ? /= _ _ _ -> ->. by [].
Qed.

(** * Administrative instructions *)

Scheme Instr_ok2_ind3 := Induction for S.Instr_ok2 Sort Prop
  with Instrs_ok2_ind3 := Induction for S.Instrs_ok2 Sort Prop
  with Expr_ok2_ind3 := Induction for S.Expr_ok2 Sort Prop.

Lemma ety_basic s C bes tf : be_typing C bes tf -> e_typing s C (to_e_list bes) tf.
Proof. exact: ety_a. Qed.

Lemma tr_admin_instr i : tr_admin (S.admininstr_instr i) = AI_basic (tr_instr i).
Proof. by case: i. Qed.

Lemma tr_admins_instrs ins : tr_admins (map S.admininstr_instr ins) = to_e_list (tr_instrs ins).
Proof. by elim: ins => //= i ins ->; rewrite tr_admin_instr. Qed.

Lemma ctx_equiv_label_tr CW C lab :
  ctx_equiv CW (tr_context C) ->
  ctx_equiv (upd_label CW ([:: tr_resulttype lab] ++ tc_labels CW))
    (tr_context (S._append
      {| S.context_TYPES := [::]; S.context_FUNCS := [::]; S.context_GLOBALS := [::];
         S.context_TABLES := [::]; S.context_MEMS := [::]; S.context_ELEMS := [::];
         S.context_DATAS := [::]; S.context_LOCALS := [::]; S.LABELS := [:: lab];
         S.context_RETURN := None |} C)).
Proof. rewrite T.tr_context_label. exact: ctx_equiv_label. Qed.

Lemma ctx_equiv_return_tr CW C rt :
  ctx_equiv CW (tr_context C) -> S.context_RETURN C = None ->
  ctx_equiv (upd_return CW (Some (tr_resulttype rt)))
    (tr_context (S._append
      {| S.context_TYPES := [::]; S.context_FUNCS := [::]; S.context_GLOBALS := [::];
         S.context_TABLES := [::]; S.context_MEMS := [::]; S.context_ELEMS := [::];
         S.context_DATAS := [::]; S.context_LOCALS := [::]; S.LABELS := [::];
         S.context_RETURN := Some rt |} C)).
Proof.
  case: C => ty fu gl ta me el da lo la re [HT HF HTa HM HG HE HD HL HLab HR HRf] /= Hre. subst re.
  by constructor => /=.
Qed.

Combined Scheme admin_ok_mut from Instr_ok2_ind3, Instrs_ok2_ind3, Expr_ok2_ind3.

Lemma admin_typing_tr :
  (forall s C a ft, S.Instr_ok2 s C a ft ->
     forall CW, ctx_equiv CW (tr_context C) -> e_typing (tr_store s) CW [:: tr_admin a] (tr_functype ft)) /\
  (forall s C es ft, S.Instrs_ok2 s C es ft ->
     forall CW, ctx_equiv CW (tr_context C) -> e_typing (tr_store s) CW (tr_admins es) (tr_functype ft)) /\
  (forall s C es rt, S.Expr_ok2 s C es rt ->
     forall CW, ctx_equiv CW (tr_context C) ->
     e_typing (tr_store s) CW (tr_admins es) (Tf [::] (tr_resulttype rt))).
Proof.
  apply: admin_ok_mut.
  - (* plain *)
    move=> s C i t1 t2 Hi _ _ _ CW HCW. rewrite tr_admin_instr.
    apply: (ety_basic (bes := [:: tr_instr i]) _). apply: be_typing_equiv (ctx_equiv_sym HCW).
    exact: T.Instr_ok_tr Hi.
  - (* label *)
    move=> s C n ins es t t' _ IH1 _ IH2 _ _ _ _ /eqP Hn CW HCW /=.
    apply: ety_label.
    + rewrite -tr_admins_instrs. exact: IH1.
    + apply: IH2. exact: ctx_equiv_label_tr HCW.
    + by rewrite Hn length_size size_map Nat2N.id.
  - (* frame *)
    move=> s C n f es t C' Hf _ IH _ _ _ _ _ /eqP Hn CW HCW /=.
    case: (frame_typing_tr Hf) => CWf [Hft [Hequiv [_ HR]]].
    apply: ety_frame; last by rewrite Hn length_size size_map Nat2N.id.
    apply: mk_thread_typing Hft erefl _. apply: IH. exact: (ctx_equiv_return_tr (S.mk_list _ t) Hequiv HR).
  - (* call_addr *)
    move=> s C a t1 t2 Ha _ _ _ _ CW HCW /=. apply: ety_invoke. exact: ext_func_typing_tr Ha.
  - (* ref *)
    move=> s C r rt Hr _ _ CW HCW. rewrite /= T.tr_valtype_ref.
    case: Hr => {r rt} [s1 rt _ | s1 a ext Ha _ _ | s1 a _] /=.
    + apply: (ety_basic (bes := [:: BI_ref_null (tr_reftype rt)]) _). exact: bet_ref_null.
    + apply: ety_ref. exact: ext_func_typing_tr Ha.
    + exact: ety_ref_extern.
  - (* trap *) move=> *. exact: ety_trap.
  - (* empty *) move=> s C _ _ CW HCW. apply: (ety_basic (bes := [::]) _). exact: bet_empty.
  - (* single *) move=> s C a t1 t2 _ IH _ _ _ CW HCW. exact: IH.
  - (* sequence *)
    move=> s C es1 es2 t1 t3 t2 _ IH1 _ IH2 _ _ _ _ CW HCW. rewrite /tr_admins map_cat.
    exact: et_composition' (IH1 _ HCW) (IH2 _ HCW).
  - (* subtyping *)
    move=> s C es t1' t2' t1 t2 _ IH Hs1 Hs2 _ _ _ CW HCW.
    apply: ety_subtyping (IH _ HCW) _.
    exists [::], [::], (map tr_valtype t1'), (map tr_valtype t2').
    do 3 (split => //). by split; apply: T.Resulttype_sub_tr.
  - (* framing *)
    move=> s C es t t1 t2 _ IH _ _ _ CW HCW. rewrite /= !map_cat.
    apply: ety_subtyping (IH _ HCW) _.
    exists (map tr_valtype t), (map tr_valtype t), (map tr_valtype t1), (map tr_valtype t2).
    do 2 (split => //). by split; [|split]; apply: T.values_subtyping_refl.
  - (* expression *) move=> s C es t _ IH _ _ _ CW HCW. exact: IH.
Qed.

(** * Stores *)

Lemma default_vals_tr ts :
  List.Forall (fun t => t != S.BOT) ts -> default_vals (map tr_valtype ts) <> None.
Proof.
  rewrite /default_vals -those_those0.
  elim=> // t ts' Ht _ IH /=.
  have [v ->] : exists v, default_val (tr_valtype t) = Some v by case: t Ht => //= _; eexists.
  by case: (those0 _) IH.
Qed.

Lemma func_typing_tr C C0 f ft :
  S.Func_ok C f ft -> ctx_equiv C0 (tr_context C) ->
  S.context_LOCALS C = [::] -> S.LABELS C = [::] -> S.context_RETURN C = None ->
  func_typing C0 (tr_func f) (tr_functype ft).
Proof.
  case=> {C f ft} C x ts body t1 t2 /N.ltb_spec0 Hx /eqP Ht Hbot Hexpr _ _ _ HC0 HL HLab HR.
  rewrite /func_typing /tr_func; cbn [modfunc_type modfunc_locals modfunc_body].
  rewrite (ce_types HC0) /tr_context; cbn [tc_types].
  rewrite lookup_N_tr // Ht. split => //. split.
  - inversion Hexpr as [? ? ? Hins _ _]; subst. rewrite /expr_typing.
    have := T.Instrs_ok_tr Hins. move/be_typing_equiv. apply.
    case: C HC0 HL HLab HR {Hins Hx Ht Hexpr} => ty fu gl ta me el da lo la re
      [HT HF HTa HM HG HE HD HL' HLab' HR' HRf] /= HL HLab HR. subst.
    constructor => //=. rewrite -map_comp. change (S._append (t1 ++ ts) [::]) with ((t1 ++ ts) ++ [::]).
    by rewrite cats0 map_cat.
  - rewrite -map_comp. exact: default_vals_tr.
Qed.

Lemma mem_length_tr mi : mem_length (tr_meminst mi) = N.of_nat (size (S.BYTES mi)).
Proof. by rewrite /mem_length /= /memory_list.ml_length /= size_map. Qed.

Lemma Forall2_exists {A B C : Type} (P : A -> B -> Prop) (Q : C -> Prop) (g : A -> C) l l' :
  (forall a b, P a b -> Q (g a)) -> List.Forall2 P l l' -> List.Forall Q (map g l).
Proof. move=> H. by elim=> //= a b ? ? Hab _ IH; constructor; [exact: H Hab | ]. Qed.

Lemma Limits_ok_valid l k : S.Limits_ok l k -> limit_valid_range (tr_limits l) k.
Proof.
  case=> n mo k' /N.leb_spec0 Hn Hmo _. rewrite /limit_valid_range /=.
  apply/andP; split; first exact/N.leb_spec0.
  case: mo Hmo => [m|] //= Hmo. by inversion Hmo.
Qed.

Lemma Tabletype_ok_valid tt : S.Tabletype_ok tt -> tabletype_valid (tr_tabletype tt).
Proof. case=> l rt Hl _. exact: Limits_ok_valid Hl. Qed.

Lemma Memtype_ok_valid mt : S.Memtype_ok mt -> memtype_valid (tr_memtype mt).
Proof. case=> l Hl _. exact: Limits_ok_valid Hl. Qed.

Lemma store_typing_tr s : S.Store_ok s -> store_typing (tr_store s).
Proof.
  case=> {}s gis gts mis mts tis tts fis fts dis dts eis ets
    _ Hg _ Hm _ Ht _ Hf _ Hd _ He /eqP Es _ _ _ _. subst s.
  set s := {| S.store_FUNCS := fis |}.
  rewrite /store_typing. case Es: (tr_store s) => [fs ts' ms gs es ds]. rewrite -Es.
  have [<- <- <- <- [<- <-]] : [/\ map tr_funcinst fis = fs, map tr_tableinst tis = ts',
    map tr_meminst mis = ms, map tr_globalinst gis = gs & map tr_eleminst eis = es /\ map tr_datainst dis = ds].
  { by move: Es; rewrite /tr_store /= => [[-> -> -> -> -> ->]]. }
  split; last split; last split; last split; last split.
  - apply: Forall2_exists Hf => fi ft.
    move=> Hfi. inversion Hfi as [s' ft' mi f C _ Hmi Hfok _ _ _]; subst. exists (tr_functype ft).
    rewrite /funcinst_typing /tr_funcinst. split => //. split => //.
    case: (inst_typing_tr Hmi) => C0 [-> HC0].
    case: (moduleinst_ctx Hmi) => HL [HLab HR].
    exact: func_typing_tr HC0 HL HLab HR.
  - apply: Forall2_exists Ht => ti tt Hti. inversion Hti; subst. eexists.
    rewrite /tableinst_typing /tr_tableinst. cbn [S.tableinst_TYPE S.REFS].
    match goal with H : S.Tabletype_ok _ |- _ => rewrite (Tabletype_ok_valid H) end.
    have -> : N.of_nat (length (map tr_ref ref_lst)) = v_n.
    { match goal with H : is_true (eq_op (N.of_nat (size ref_lst)) _) |- _ => move/eqP: H => <- end.
      by rewrite length_size size_map. }
    rewrite eqxx.
    have -> // : all (fun r => value_typing (tr_store s) (VAL_ref r) (T_ref (tr_reftype rt))) (map tr_ref ref_lst).
    match goal with H : List.Forall _ ref_lst |- _ => elim: H => //= r l Hr _ -> end.
    by rewrite (ref_typing_tr Hr).
  - apply: Forall2_exists Hm => mi mt Hmi. inversion Hmi; subst. eexists.
    rewrite /meminst_typing mem_length_tr /tr_meminst. cbn [S.meminst_TYPE S.BYTES].
    match goal with H : S.Memtype_ok _ |- _ => have Hv := Memtype_ok_valid H end.
    rewrite /tr_memtype in Hv. rewrite Hv.
    move/eqP: H0 => ->. change (64 * S.Ki)%num with page_size. by rewrite eqxx.
  - apply: Forall2_exists Hg => gi gt.
    move=> Hgi. inversion Hgi as [s' mu t v _ Hv _ _]; subst. eexists.
    by rewrite /globalinst_typing /tr_globalinst /= (val_typing_tr Hv).
  - apply: Forall2_exists He => ei et Hei. eexists. exact: eleminst_typing_tr Hei.
  - apply: Forall2_exists Hd => di dt _. by exists tt.
Qed.

End Store.

(** * Configurations *)

Section Config.

Context `{hfc : host_function_class}.

(* If SpecTec types a configuration, WasmCert types its translation at the
   translated result type. *)
Theorem Config_ok_tr s f es ts :
  S.Config_ok (S.mk_config (S.mk_state s f) es) ts ->
  config_typing (tr_store s) (tr_frame f, tr_admins es) (tr_resulttype ts).
Proof.
  move=> H. inversion H as [s' f' es' t C Hst Hexpr _ _ _]; subst.
  inversion Hst as [s1 f1 C1 Hs Hf _ _]; subst.
  split; first exact: store_typing_tr.
  case: (frame_typing_tr Hf) => CW [Hft [Hequiv [_ HR]]].
  apply: mk_thread_typing Hft erefl _.
  case: admin_typing_tr => _ [_ Hadm]. apply: (Hadm _ _ _ _ Hexpr).
  case: Hequiv => *. by constructor => //=; rewrite HR.
Qed.

End Config.

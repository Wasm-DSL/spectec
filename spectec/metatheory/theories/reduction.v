From Stdlib Require Import List String Reals.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat ssrint.
From MetaSpectec Require Import syntax subst env numerics.
Import ListNotations.

Definition option_forall {T : Type} (f : T -> Prop) (arg : option T) : Prop :=
	match arg with
		| None => True
		| Some a => f a
	end.

Definition list_zipWith {X Y Z : Type} (f : X -> Y -> Z) (xs : seq X) (ys : seq Y) : seq Z :=
	seq.map (fun '(x, y) => f x y) (seq.zip xs ys).

Definition slice {A : Type} (i j : nat) (l : list A) : list A :=
  firstn (j - i) (skipn i l).

(* PRE: i < size l *)
Definition update {A : Type} (l : list A) (i : nat) (x : A) : list A :=
  set_nth x l i x.

Definition update_slice {A : Type} (l : list A) (i : nat) (j : nat) (xs : list A) : list A :=
  let idx_lst := iota i (j - i) in
  foldl (fun acc '(idx, x) => update acc idx x) l (zip idx_lst xs)
.

Definition is_plaintyp (t : il_typ) : bool :=
  match t with
  | VarT _ _ => false
  | _ => true
  end
.

Inductive match_args : store -> list il_arg -> list il_quant -> list il_arg -> il_subst -> Prop :=
  | ma_rule : forall s ags qs ags' sbst,
    ok_subst (store_to_env s) (sbst) qs ->
    ags = List.map (subst_arg sbst) ags' ->
    match_args s ags qs ags' sbst
.

Inductive expand_typ : store -> il_typ -> il_deftyp -> Prop :=
  | et_plain : forall s t,
    is_plaintyp t ->
    expand_typ s t (AliasT t)
  | et_alias : forall s x ags t dt,
    expand_typ s (VarT x ags) (AliasT t) ->
    expand_typ s t dt ->
    expand_typ s (VarT x ags) dt
  | et_step : forall s e x ags ags' dt ps insts n qs sbst,
    store_to_env s = e ->
    StringMap.find x (TYPS e) = Some (ps, insts) ->
    List.nth_error insts n = Some (qs, ags', dt) ->
    match_args s ags qs ags' sbst ->
    expand_typ s (VarT x ags) (subst_deftyp sbst dt)
.

Inductive step_exp: store -> il_exp -> il_exp -> Prop :=
  (* UnE Rules *)
  | se_unop_ctx : forall s op e1 e2,
    step_exp s e1 e2 ->
    step_exp s (UnE op e1) (UnE op e2)
  | se_unop_bool : forall s boolop b,
    step_exp s (UnE (BoolUnop boolop) (BoolE b)) (BoolE (boolun boolop b))
  | se_unop_num : forall s numop n n',
    (numun numop n) = Some n' ->
    step_exp s (UnE (NumUnop numop) (NumE n)) (NumE n')
  (* BinE Rules *)
  | se_bin_ctxl : forall s op e1 e1' e2,
    step_exp s e1 e1' ->
    step_exp s (BinE op e1 e2) (BinE op e1' e2)
  | se_bin_ctxr : forall s op e1 e2 e2',
    step_exp s e2 e2' ->
    step_exp s (BinE op e1 e2) (BinE op e1 e2')
  | se_bin_bool : forall s boolop b1 b2,
    step_exp s (BinE (BoolBinop boolop) (BoolE b1) (BoolE b2)) (BoolE (boolbin boolop b1 b2))
  | se_bin_num : forall s numop n1 n2 n3,
    (numbin numop n1 n2) = Some n3 ->
    step_exp s (BinE (NumBinop numop) (NumE n1) (NumE n2)) (NumE n3)
  (* CmpE Rules *)
  | se_cmp_ctxl : forall s op e1 e1' e2,
    step_exp s e1 e1' ->
    step_exp s (CmpE op e1 e2) (CmpE op e1' e2)
  | se_cmp_ctxr : forall s op e1 e2 e2',
    step_exp s e2 e2' ->
    step_exp s (CmpE op e1 e2) (CmpE op e1 e2')
  | se_cmp_eq_true : forall s e1 e2,
    e1 = e2 ->
    step_exp s (CmpE (BoolCmpop EqOp) e1 e2) (BoolE true)
  | se_cmp_ne_false : forall s e1 e2,
    e1 = e2 ->
    step_exp s (CmpE (BoolCmpop NeqOp) e1 e2) (BoolE false)
  | se_cmp_num : forall s numcmpop n1 n2 b,
    (numcmp numcmpop n1 n2) = Some b ->
    step_exp s (CmpE (NumCmpop numcmpop) (NumE n1) (NumE n2)) (BoolE b)
  | se_cmp_opt_ctx : forall s opt_e e e',
    opt_e = Some e ->
    step_exp s e e' ->
    step_exp s (OptE opt_e) (OptE (Some e'))
  (* ListE rules *)
  | se_list_ctx : forall s es es',
    List.Forall2 (fun e e' => step_exp s e e') es es' ->
    step_exp s (ListE es) (ListE es')
  (* TupE rules *)
  | se_tup_ctx : forall s es es',
    List.Forall2 (fun e e' => step_exp s e e') es es' ->
    step_exp s (TupE es) (TupE es')
  (* StrE rules *)
  | se_str_ctx : forall s fields fields',
    List.Forall2 (fun f f' => step_exp s (snd f) (snd f')) fields fields' ->
    step_exp s (StrE fields) (StrE fields')
  (* CaseE rules *)
  | se_case_ctx : forall s m e e',
    step_exp s e e' ->
    step_exp s (CaseE m e) (CaseE m e')
  (* LiftE rules *)
  | se_lift_ctx : forall s e e',
    step_exp s e e' ->
    step_exp s (LiftE e) (LiftE e')
  | se_lift_none : forall s, step_exp s (LiftE (OptE None)) (ListE [])
  | se_list_some : forall s e , step_exp s (LiftE (OptE (Some e))) (ListE [e])
  (* ProjE rules *)
  | se_proj_ctx : forall s e e' n,
    step_exp s e e' ->
    step_exp s (ProjE e n) (ProjE e' n)
  | se_proj_tup : forall s es e_n n,
    List.nth_error es n = Some e_n ->
    step_exp s (ProjE (TupE es) n) e_n 
  (* LenE rules *)
  | se_len_ctx : forall s e e',
    step_exp s e e' ->
    step_exp s (LenE e) (LenE e')
  | se_len_list : forall s es,
    step_exp s (LenE (ListE es)) (NumE (NatE (List.length es)))
  (* MemE rules *)
  | se_mem_ctxl : forall s e1 e2 e1',
    step_exp s e1 e1' ->
    step_exp s (MemE e1 e2) (MemE e1' e2)
  | se_mem_ctxr : forall s e1 e2 e2',
    step_exp s e2 e2' ->
    step_exp s (MemE e1 e2) (MemE e1 e2')
  | se_mem_opt_true : forall s e1 e2,
    e1 = e2 ->
    step_exp s (MemE e1 (OptE (Some e2))) (BoolE true)
  | se_mem_opt_false : forall s e1 e2_opt,
    option_forall (fun e2 => e1 <> e2) e2_opt ->
    step_exp s (MemE e1 (OptE e2_opt)) (BoolE false)
  | se_mem_list_true : forall s e1 e2s,
    List.In e1 e2s ->
    step_exp s (MemE e1 (ListE e2s)) (BoolE true)
  | se_mem_list_false : forall s e1 e2s,
    List.Forall (fun e2 => e1 <> e2) e2s ->
    step_exp s (MemE e1 (ListE e2s)) (BoolE false)
  (* CatE rules *)
  | se_cat_ctxl : forall s e1 e1' e2,
    step_exp s e1 e1' ->
    step_exp s (CatE e1 e2) (CatE e1' e2)
  | se_cat_ctxr : forall s e1 e2 e2',
    step_exp s e2 e2' ->
    step_exp s (CatE e1 e2) (CatE e1 e2')
  | se_cat_opt1 : forall s e1,
    step_exp s (CatE (OptE (Some e1)) (OptE None)) (OptE (Some e1))
  | se_cat_opt2 : forall s e2,
    step_exp s (CatE (OptE None) (OptE (Some e2))) (OptE (Some e2))
  | se_cat_list : forall s es1 es2,
    step_exp s (CatE (ListE es1) (ListE es2)) (ListE (es1 ++ es2))
  | se_cat_str : forall s fields1 fields2,
    List.Forall2 (fun '(a, _) '(a', _) => a = a') fields1 fields2 ->
    step_exp s (CatE (StrE fields1) (StrE fields2)) (StrE (list_zipWith (fun x y => (fst x, CatE (snd x) (snd y))) fields1 fields2))
  (* AccE rules *)
  | se_acc_ctxexp : forall s e e' p,
    step_exp s e e' ->
    step_exp s (AccE e p) (AccE e' p)
  (* TODO: what does step path mean? *)
  | se_acc_root : forall s e,
    step_exp s (AccE e RootP) e
  | se_acc_the : forall s e e' p,
    step_exp s (AccE e p) (OptE (Some e')) ->
    step_exp s (AccE e (TheP p)) e'
  | se_acc_idx : forall s e e_lst' e_n' p n,
    step_exp s (AccE e p) (ListE e_lst') ->
    n < List.length e_lst' ->
    List.nth_error e_lst' n = Some e_n' ->
    step_exp s (AccE e (IdxP p (NumE (NatE n)))) e_n'
  | se_acc_slice : forall s e p n m e'_lst e''_lst,
    step_exp s (AccE e p) (ListE e'_lst) ->
    n <= m ->
    n < List.length e'_lst /\ (n + m) < List.length e'_lst ->
    e''_lst = slice n m e'_lst ->
    step_exp s (AccE e (SliceP p (NumE (NatE n)) (NumE (NatE n)))) (ListE e''_lst)
  | se_acc_dot : forall s e p a e_n' fields n,
    step_exp s (AccE e p) (StrE fields) ->
    List.nth_error fields n = Some (a, e_n') ->
    step_exp s (AccE e (DotP p a)) e_n'
  | se_acc_uncase : forall s e p m e',
    step_exp s (AccE e p) (CaseE m e') ->
    step_exp s (AccE e (UncaseP p m)) e'
  (* UpdE rules *)
  | se_upd_ctxl : forall s e1 e1' p e2,
    step_exp s e1 e1' ->
    step_exp s (UpdE e1 p e2) (UpdE e1' p e2)
  | se_upd_ctxr : forall s e1 p e2 e2',
    step_exp s e2 e2' ->
    step_exp s (UpdE e1 p e2) (UpdE e1 p e2')
  | se_upd_root : forall s e1 e2,
    step_exp s (UpdE e1 RootP e2) e2
  | se_upd_the : forall s e1 p e2 e',
    step_exp s (AccE e1 p) (OptE (Some e')) ->
    step_exp s (UpdE e1 (TheP p) e2) (UpdE e1 p (OptE (Some e2)))
  | se_upd_idx : forall s e1 p n e2 e_lst',
    step_exp s (AccE e1 p) (ListE e_lst') ->
    n < size e_lst' ->
    step_exp s (UpdE e1 (IdxP p (NumE (NatE n))) e2) (UpdE e1 p (ListE (update e_lst' n e2)))
  | se_upd_slice : forall s e1 p n m e2_lst e_lst',
    step_exp s (AccE e1 p) (ListE e_lst') ->
    n <= m ->
    n < size e_lst' ->
    (n + m) < size e_lst' ->
    step_exp s (UpdE e1 (SliceP p (NumE (NatE n)) (NumE (NatE m))) (ListE e2_lst)) (UpdE e1 p (ListE (update_slice e_lst' n m e2_lst)))
  | se_upd_dot : forall s e1 p e2 fields a e' n,
    step_exp s (AccE e1 p) (StrE fields) ->
    List.nth_error fields n = Some (a, e') ->
    step_exp s (UpdE e1 (DotP p a) e2) (UpdE e1 p (StrE (update fields n (a, e2))))
  | se_upd_uncase : forall s e1 p m e2 e', 
    step_exp s (AccE e1 p) (CaseE m e') ->
    step_exp s (UpdE e1 (UncaseP p m) e2) (UpdE e1 p (CaseE m e2))
  (* ExtE rule *)
  | se_ext : forall s e1 p e2,
    step_exp s (ExtE e1 p e2) (UpdE e1 p (CatE (AccE e1 p) e2))
  (* IterE rules *)
  | se_iter_ctx1 : forall s e it ep_lst e',
    step_exp s e e' ->
    step_exp s (IterE e it ep_lst) (IterE e' it ep_lst)
  (* TODO ctx on iter and exppull? *)
  (* | se_iter_quest : forall s e ep_lst, *)
  (* TODO other iter rules *)
    (* CallE rules *)
  | se_call_ctx : forall s x ags n a a',
    List.nth_error ags n = Some a ->
    step_arg s a a' ->
    step_exp s (CallE x ags) (CallE x (update ags n a'))
  | se_call_app : forall s x ags ags' ps qs t cs e prems sbst n,
    StringMap.find x (DEFS (store_to_env s)) = Some (ps, t, cs) ->
    List.nth_error cs n = Some (qs, ags', e, prems) ->
    match_args s ags qs ags' sbst ->
    reduce_prems s (List.map (subst_prem sbst) prems) [] ->
    step_exp s (CallE x ags) (subst_exp sbst e)
  (* CvtE rules *)
  | se_cvt_ctx : forall s e nt1 nt2 e',
    step_exp s e e' ->
    step_exp s (CvtE e nt1 nt2) (CvtE e' nt1 nt2)
  | se_cvt_num : forall s num nt1 nt2 e,
    numcvt nt2 num = Some e ->
    step_exp s (CvtE (NumE num) nt1 nt2) (NumE e)
  (* SubE rules *)
  | se_sub_ctx1 : forall s e t1 t2 e',
    step_exp s e e' ->
    step_exp s (SubE e t1 t2) (SubE e' t1 t2)
  | se_sub_ctx2 : forall s e t1 t1' t2,
    step_typ s t1 t1' ->
    step_exp s (SubE e t1 t2) (SubE e t1' t2)
  | se_sub_ctx3 : forall s e t1 t2 t2',
    step_typ s t2 t2' ->
    step_exp s (SubE e t1 t2) (SubE e t1 t2')
  | se_sub_sub : forall s e' t1' t2' t1 t2,
    step_exp s (SubE (SubE e' t1' t2') t1 t2) (SubE e' t1' t2)
  | se_sub_tup : forall s es tups tups',
    size es = size tups ->
    size tups = size tups' ->
    step_exp s (SubE (TupE es) (TupT tups) (TupT tups')) 
    (TupE (List.map (fun '(e, ((_, t1), (_, t2))) => SubE e t1 t2) (zip es (zip tups tups'))))
  (* TODO sub x's *)
with

step_arg : store -> il_arg -> il_arg -> Prop :=
  | sa_exp : forall s e e',
    step_exp s e e' ->
    step_arg s (ExpA e) (ExpA e')
  | sa_typ : forall s t t',
    step_typ s t t' ->
    step_arg s (TypA t) (TypA t')
with

step_typ : store -> il_typ -> il_typ -> Prop :=
  | st_var_ctx : forall s x ags n a a',
    List.nth_error ags n = Some a ->
    step_arg s a a' ->
    step_typ s (VarT x ags) (VarT x (update ags n a'))
  | st_var_app : forall s x ags t, 
    expand_typ s (VarT x ags) (AliasT t) ->
    step_typ s (VarT x ags) t
  | st_tup_ctx : forall s tups n x t,
    List.nth_error tups n = Some (x, t) ->
    step_typ s (TupT tups) (TupT (update tups n (x, t)))
  | st_iter_ctx : forall s t t' it,
    step_typ s t t' ->
    step_typ s (IterT t it) (IterT t' it)

with

step_prems : store -> list il_prem -> list il_prem -> Prop :=
  | sp_ctx : forall s p ps p' ps',
    step_prems s [p] p' ->
    step_prems s (p :: ps) (p' ++ ps')
  (* IfPr rules *)
  | sp_if_ctx : forall s e e',
    step_exp s e e' ->
    step_prems s [IfPr e] [IfPr e']
  | sp_if_true : forall s,
    step_prems s [IfPr (BoolE true)] []
  (* LetPr rules *)
  | sp_let_ctx : forall s e1 e2 e2',
    step_exp s e2 e2' ->
    step_prems s [LetPr e1 e2] [LetPr e1 e2']
  | sp_let : forall s e1 e2 e1' e2',
    reduce_exp s e1 e1' ->
    reduce_exp s e2 e2' ->
    e1' = e2' ->
    step_prems s [LetPr e1 e2] []
  (* IterPr rules *)
  | sp_iter_ctxl : forall s p it eps p',
    step_prems s [p] [p'] ->
    step_prems s [IterPr p it eps] [IterPr p' it eps]
  (* TODO ctx for iter and exppull? *)
  (* TODO other iter rules *)
with

reduce_exp : store -> il_exp -> il_exp -> Prop :=
  | re_refl : forall s e, reduce_exp s e e
  | re_step : forall s e1 e2 e3,
    step_exp s e1 e3 ->
    reduce_exp s e2 e3 ->
    reduce_exp s e1 e3

with

reduce_prems : store -> list il_prem -> list il_prem -> Prop :=
  | rp_refl : forall s p, reduce_prems s p p
  | rp_step : forall s p1 p2 p3,
    step_prems s p1 p2 ->
    reduce_prems s p2 p3 ->
    reduce_prems s p1 p3
.

Inductive reduce_arg : store -> il_arg -> il_arg -> Prop :=
  | ra_refl : forall s a, reduce_arg s a a
  | ra_step : forall s a1 a2 a3,
    step_arg s a1 a2 ->
    reduce_arg s a2 a3 ->
    reduce_arg s a1 a3
.

Inductive reduce_typ : store -> il_typ -> il_typ -> Prop :=
  | rt_refl : forall s t, reduce_typ s t t
  | rt_step : forall s t1 t2 t3,
    step_typ s t1 t2 ->
    reduce_typ s t2 t3 ->
    reduce_typ s t1 t3
.

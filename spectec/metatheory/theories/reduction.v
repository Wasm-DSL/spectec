From Stdlib Require Import List String Reals.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat ssrint.
From MetaSpectec Require Import syntax subst env numerics utils.
Import ListNotations.
Open Scope env_scope.

Inductive match_args : store -> list il_arg -> list il_quant -> list il_arg -> il_subst -> Prop :=
  | ma_rule : forall s ags qs ags' sbst,
    ags = List.map (subst_arg sbst) ags' ->
    match_args s ags qs ags' sbst
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
  | se_cmp_eq_true : forall s v1 v2,
    v1 = v2 ->
    step_exp s (CmpE (BoolCmpop EqOp) (val_to_exp v1) (val_to_exp v2)) (BoolE true)
  | se_cmp_eq_false : forall s v1 v2,
    v1 <> v2 ->
    step_exp s (CmpE (BoolCmpop EqOp) (val_to_exp v1) (val_to_exp v2)) (BoolE false)
  | se_cmp_ne_false : forall s v1 v2,
    v1 = v2 ->
    step_exp s (CmpE (BoolCmpop NeqOp) (val_to_exp v1) (val_to_exp v2)) (BoolE false)
  | se_cmp_ne_true : forall s v1 v2,
    v1 <> v2 ->
    step_exp s (CmpE (BoolCmpop NeqOp) (val_to_exp v1) (val_to_exp v2)) (BoolE true)
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
  | se_lift_some : forall s e , step_exp s (LiftE (OptE (Some e))) (ListE [e])

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
  | se_mem_true : forall s v1 v2s,
    List.In v1 v2s ->
    step_exp s (MemE (val_to_exp v1) (ListE (List.map val_to_exp v2s))) (BoolE true)
  | se_mem_false : forall s v1 v2s,
    List.Forall (fun v2 => v1 <> v2) v2s ->
    step_exp s (MemE (val_to_exp v1) (ListE (List.map val_to_exp v2s))) (BoolE false)

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
  | se_acc_ctxpath : forall s e p p',
    step_path s p p' ->
    step_exp s (AccE e p) (AccE e p')
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
  | se_upd_ctxm : forall s e1 p p' e2,
    step_path s p p' ->
    step_exp s (UpdE e1 p e2) (UpdE e1 p' e2)
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
  | se_iter_ctx1 : forall s e it eps e',
    step_exp s e e' ->
    step_exp s (IterE e it eps) (IterE e' it eps)
  | se_iter_ctx2 : forall s e it it' eps,
    step_iter s it it' ->
    step_exp s (IterE e it eps) (IterE e it' eps)
  | se_iter_ctx3 : forall s e it eps n ep ep',
    List.nth_error eps n = Some ep ->
    step_exppull s ep ep' ->
    step_exp s (IterE e it eps) (IterE e it (update eps n ep'))
  | se_iter_quest : forall s e xs es,
    let es' := List.map opt_to_lst es in
    let es'' := transpose es' in
    let es''' := lst_to_opt es'' in
    let ids := List.map fst xs in 
    same_size es' ->
    size xs = size es ->
    size es'' <= 1 ->
    step_exp s (IterE e I_OPT (list_zipWith (fun x e' => (x, OptE e')) xs es))
    (OptE (option_map (fun ess => subst_exp (many_svars (zip ids ess)) e) es'''))
  | se_iter_plus : forall s e xs ess,
    same_size ess ->
    seq.all (fun es => size es >= 1) ess ->
    let res_ess := (list_zipWith (fun x es => (x, ListE es)) xs ess) in
    step_exp s (IterE e I_PLUS res_ess) (IterE e I_STAR res_ess)
  | se_iter_star : forall s e xs ess n y,
    seq.all (fun es => size es == n) ess ->
    let res_ess := (list_zipWith (fun x es => (x, ListE es)) xs ess) in
    step_exp s (IterE e I_STAR res_ess) (IterE e (I_SUP y (NumE (NatE n))) res_ess)
  | se_iter_sup : forall s e x_i n xs ess,
    seq.all (fun es => size es == n) ess ->
    size xs = size ess -> 
    let ess' := transpose ess in
    let ids := List.map fst xs in
    let res_ess := (list_zipWith (fun x es => (x, ListE es)) xs ess) in
    let res_ess' := (list_mapi (fun i es => 
      let sbst := subst_svar x_i (NumE (NatE i)) in
      let sbst' := many_svars (zip ids es) in
      subst_exp (append_subst sbst sbst') e 
    ) ess') in
    step_exp s (IterE e (I_SUP x_i (NumE (NatE n))) res_ess) (ListE res_ess')

  (* CallE rules *)
  | se_call_ctx : forall s x ags n a a',
    List.nth_error ags n = Some a ->
    step_arg s a a' ->
    step_exp s (CallE x ags) (CallE x (update ags n a'))
  | se_call_app : forall s x ags cs ps t,
    StringMap.find x (DEFS (store_to_env s)) = Some (ps, t, cs) ->
    step_exp s (CallE x ags) (MatchE ags cs)

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
  | se_sub_refl : forall s e t,
    step_exp s (SubE e t t) e
  | se_sub_sub : forall s e' t1' t2' t1 t2,
    step_exp s (SubE (SubE e' t1' t2') t1 t2) (SubE e' t1' t2)
  | se_sub_tup : forall s es tups tups',
    size es = size tups ->
    size tups = size tups' ->
    let sbst1 := many_svars (list_zipWith (fun e '(x1, _) => (x1, e)) es tups) in
    let sbst2 := many_svars (list_zipWith (fun e '(x2, _) => (x2, e)) es tups') in
    step_exp s (SubE (TupE es) (TupT tups) (TupT tups')) 
    (TupE (List.map (fun '(e, ((_, t1), (_, t2))) => SubE e (subst_typ sbst1 t1) (subst_typ sbst2 t2)) (zip es (zip tups tups'))))
  | se_sub_opt : forall s e_opt t1 t2,
    step_exp s (SubE (OptE e_opt) (IterT t1 I_OPT) (IterT t2 I_OPT)) (OptE (option_map (fun e => SubE e t1 t2) e_opt))
  | se_sub_list : forall s es t1 t2,
    step_exp s (SubE (ListE es) (IterT t1 I_STAR) (IterT t2 I_STAR)) (ListE (List.map (fun e => SubE e t1 t2) es))
  | se_sub_case : forall s (e : il_exp) op e x1 x2 t1 t2 t1' t2' tcs1 tcs2 qs1 qs2 prs1 prs2,
    t1 = MatchT x1 [] [([], [], VariantT tcs1)] ->
    t2 = MatchT x2 [] [([], [], VariantT tcs2)] ->    
    List.In (op, qs1, t1', prs1) tcs1 ->
    List.In (op, qs2, t2', prs2) tcs2 ->
    step_exp s (SubE (CaseE op e) t1 t2) (CaseE op (SubE e t1' t2'))
  | se_sub_str : forall s efs x1 x2 t1 t2 t1s t2s tfs1 tfs2 ats es,
    t1 = MatchT x1 [] [([], [], StructT tfs1)] ->
    t2 = MatchT x2 [] [([], [], StructT tfs2)] -> 
    size efs = size tfs1 ->
    size efs = size tfs2 ->
    List_Forall3 (fun '(a, t) a' t' => a = a' /\ t = t') (atomtyps tfs2) ats t2s ->
    List.Forall2 (fun a t => List.In (a, t) (atomtyps tfs1)) ats t1s ->
    List.Forall2 (fun a e => List.In (a, e) efs) ats es ->
    step_exp s (SubE (StrE efs) t1 t2)
    (StrE (list_map3 (fun '(a, e) t1 t2 => (a, SubE e t1 t2)) (zip ats es) t1s t2s)) 

  (* IfE rules *)
  | se_ife_ctx1 : forall s e1 e2 e3 e1',
    step_exp s e1 e1' ->
    step_exp s (IfE e1 e2 e3) (IfE e1' e2 e3)
  | se_ife_true : forall s e2 e3,
    step_exp s (IfE (BoolE true) e2 e3) e2
  | se_ife_false : forall s e2 e3,
    step_exp s (IfE (BoolE false) e2 e3) e3

  (* MatchE rules *)
  | se_matche_ctx1 : forall s ags cs a a' n,
    List.nth_error ags n = Some a ->
    step_arg s a a' ->
    step_exp s (MatchE ags cs) (MatchE (update ags n a') cs)
  | se_matche_ctx2 : forall s ags cs c c' n,
    List.nth_error cs n = Some c -> 
    step_clause s c c' ->
    step_exp s (MatchE ags cs) (MatchE ags (update cs n c'))
  | se_matche_match : forall s ags qs ags' e prems cs ags'' ags''' qs' sbst,
    let ams := list_zipWith (fun a a' => MatchA a a') ags ags' in
    let ams' := list_zipWith (fun a a' => MatchA a a') ags'' ags''' in
    let new_c1 := (qs', ags''', subst_exp sbst e, List.map (subst_prem sbst) prems) in
    let new_c2 := ([], ags'', MatchE ags (cs), []) in
    step_argmatch s qs ams sbst qs' ams' ->
    step_exp s (MatchE ags ((qs, ags', e, prems) :: cs)) (MatchE ags'' [new_c1; new_c2])
  | se_matche_fail : forall s ags qs ags' e prems cs sbst,
    let ams := list_zipWith (fun a a' => MatchA a a') ags ags' in
    step_argmatch s qs ams sbst [] [FailA] ->
    step_exp s (MatchE ags ((qs, ags', e, prems) :: cs)) (MatchE ags cs)
  | se_matche_guess : forall s ags qs ags' e prems cs sbst,
    (* TODO ok subst *)
    (* NOTE: non-computational rule *)
    step_exp s (MatchE ags ((qs, ags', e, prems) :: cs)) (MatchE ags (([], List.map (subst_arg sbst) ags', e, prems) :: cs))
  | se_matche_matchtrue : forall s e cs,
    step_exp s (MatchE [] (([], [], e, []) :: cs)) e
  | se_matche_matchfalse : forall s e prems cs,
    step_exp s (MatchE [] (([], [], e, (IfPr (BoolE false)) :: prems) :: cs)) (MatchE [] cs)
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
  | st_var_app : forall s x ags ps insts,
    StringMap.find x (TYPS (store_to_env s)) = Some (ps, insts) ->
    step_typ s (VarT x ags) (MatchT x ags insts)
  | st_tup_ctx : forall s tups n x t t',
    List.nth_error tups n = Some (x, t) ->
    step_typ s t t' ->
    step_typ s (TupT tups) (TupT (update tups n (x, t')))
  | st_iter_ctx : forall s t t' it,
    step_typ s t t' ->
    step_typ s (IterT t it) (IterT t' it)
  | st_match_ctx1 : forall s x ags insts n a_n a_n',
    List.nth_error ags n = Some a_n ->
    step_arg s a_n a_n' ->
    step_typ s (MatchT x ags insts) (MatchT x (update ags n a_n') insts)
  | st_match_ctx2 : forall s x ags insts n inst_n inst_n',
    List.nth_error insts n = Some inst_n ->
    step_inst s inst_n inst_n' ->
    step_typ s (MatchT x ags insts) (MatchT x ags (update insts n inst_n'))
  | st_match_alias : forall s x t insts,
    step_typ s (MatchT x [] (([], [], AliasT t) :: insts)) t
  | st_match_match : forall s x ags ags' ags'' qs qs' ags''' insts dt sbst,
    let ams := list_zipWith (fun a a' => MatchA a a') ags ags' in
    let ams' := list_zipWith (fun a a' => MatchA a a') ags'' ags''' in
    let new_dt := AliasT (MatchT x ags insts) in
    step_argmatch s qs ams sbst qs' ams' ->
    step_typ s (MatchT x ags ((qs, ags', dt) :: insts)) (MatchT x ags'' [(qs', ags''', subst_deftyp sbst dt); ([], ags'', new_dt)])
  | st_match_fail : forall s x ags ags' qs insts dt sbst,
    let ams := list_zipWith (fun a a' => MatchA a a') ags ags' in
    step_argmatch s qs ams sbst [] [FailA] ->
    step_typ s (MatchT x ags ((qs, ags', dt) :: insts)) (MatchT x ags insts)


with

step_path : store -> il_path -> il_path -> Prop :=
  | sp_idx_ctxl : forall s p p' e,
    step_path s p p' ->
    step_path s (IdxP p e) (IdxP p' e)
  | sp_idx_ctxr : forall s p e e',
    step_exp s e e' ->
    step_path s (IdxP p e) (IdxP p e')
  | sp_the_ctx : forall s p p',
    step_path s p p' ->
    step_path s (TheP p) (TheP p')
  | sp_uncase_ctx : forall s m p p',
    step_path s p p' ->
    step_path s (UncaseP p m) (UncaseP p' m)
  | sp_slice_ctx1 : forall s p p' e1 e2,
    step_path s p p' ->
    step_path s (SliceP p e1 e2) (SliceP p' e1 e2)
  | sp_slice_ctx2 : forall s p e1 e1' e2,
    step_exp s e1 e1' ->
    step_path s (SliceP p e1 e2) (SliceP p e1' e2)
  | sp_slice_ctx3 : forall s p e1 e2 e2',
    step_exp s e2 e2' ->
    step_path s (SliceP p e1 e2) (SliceP p e1 e2')
  | sp_dot_ctx : forall s p p' a, 
    step_path s p p' ->
    step_path s (DotP p a) (DotP p' a) 

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
  | sp_iter_ctx1 : forall s p it eps p',
    step_prems s [p] [p'] ->
    step_prems s [IterPr p it eps] [IterPr p' it eps]
  | sp_iter_ctx2 : forall s p it it' eps p',
    step_iter s it it' ->
    step_prems s [IterPr p it eps] [IterPr p' it eps]
  | sp_iter_ctx3 : forall s pr it eps n ep ep',
    List.nth_error eps n = Some ep ->
    step_exppull s ep ep' ->
    step_prems s [IterPr pr it eps] [IterPr pr it (update eps n ep')]
  | sp_iter_quest : forall s pr xs es,
    let es' := List.map opt_to_lst es in
    let es'' := transpose es' in
    let es''' := lst_to_opt es'' in
    let ids := List.map fst xs in 
    same_size es' ->
    size xs = size es ->
    size es'' <= 1 ->
    step_prems s [IterPr pr I_OPT (list_zipWith (fun x e' => (x, OptE e')) xs es)]
    (opt_to_lst (option_map (fun ess => subst_prem (many_svars (zip ids ess)) pr) es'''))
  | sp_iter_plus : forall s pr xs ess,
    same_size ess ->
    seq.all (fun es => size es >= 1) ess ->
    let res_ess := (list_zipWith (fun x es => (x, ListE es)) xs ess) in
    step_prems s [IterPr pr I_PLUS res_ess] [IterPr pr I_STAR res_ess]
  | sp_iter_star : forall s pr xs ess n y,
    seq.all (fun es => size es == n) ess ->
    let res_ess := (list_zipWith (fun x es => (x, ListE es)) xs ess) in
    step_prems s [IterPr pr I_STAR res_ess] [IterPr pr (I_SUP y (NumE (NatE n))) res_ess]
  | sp_iter_sup : forall s pr x_i n xs ess,
    seq.all (fun es => size es == n) ess ->
    size xs = size ess -> 
    let ess' := transpose ess in
    let res_ess := (list_zipWith (fun x es => (x, ListE es)) xs ess) in
    let ids := List.map fst xs in 
    let res_ess' := (list_mapi (fun i es => 
      let sbst := subst_svar x_i (NumE (NatE i)) in
      let sbst' := many_svars (zip ids es) in
      subst_prem (append_subst sbst sbst') pr 
    ) ess') in
    step_prems s [IterPr pr (I_SUP x_i (NumE (NatE n))) res_ess] res_ess'

  (* ElsePr rule *)
  | sp_else : forall s,
    step_prems s [ElsePr] [IfPr (BoolE true)]

  (* NegPr rules *)
  | sp_neg_ctx : forall s p p',
    step_prems s [p] [p'] ->
    step_prems s [NegPr p] [NegPr p']
  | sp_neg_bool: forall s b,
    step_prems s [NegPr (IfPr (BoolE b))] [IfPr (BoolE (negb b))]
  
  (* RelPr rule (Non-computational) *)
  | sp_rel : forall s x ags e sbst prems e' ps t rules qs,
    StringMap.find x (RELS (store_to_env s)) = Some (ps, t, rules) ->
    let rules' := List.map (fun r => subst_rule (args_for_params ags ps) r) rules in
    List.In (qs, e', prems) rules' ->    
    (* TODO ok_subst *) 
    step_prems s [RulePr x ags e] (List.map (subst_prem sbst) prems ++ [IfPr (CmpE (BoolCmpop EqOp) (subst_exp sbst e') e)])

with

step_iter : store -> iter -> iter -> Prop :=
  | si_ctx : forall s x e e',
    step_exp s e e' ->
    step_iter s (I_SUP x e) (I_SUP x e')

with

step_exppull : store -> exppull -> exppull -> Prop :=
  | sep_ctx : forall s x e e',
    step_exp s e e' ->
    step_exppull s (x, e) (x, e')

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

with

step_inst : store -> il_inst -> il_inst -> Prop :=
  | sti_ctx : forall s qs ags t a a' n,
    List.nth_error ags n = Some a ->
    step_arg s a a' ->
    step_inst s (qs, ags, t) (qs, update ags n a', t)

with

step_clause : store -> il_clause -> il_clause -> Prop :=
  | stc_ctx1 : forall s qs ags e prems a a' n,
    List.nth_error ags n = Some a ->
    step_arg s a a' ->
    step_clause s (qs, ags, e, prems) (qs, update ags n a', e, prems)
  | stc_ctx2 : forall s qs ags e prems e',
    step_exp s e e' ->
    step_clause s (qs, ags, e, prems) (qs, ags, e', prems)
  | stc_ctx3 : forall s qs ags e prems prems',
    step_prems s prems prems' ->
    step_clause s (qs, ags, e, prems) (qs, ags, e, prems')

with

step_argmatch_plain : store -> list argmatch -> list argmatch -> Prop :=
  | sagp_ctx1 : forall s a a' a'',
    step_arg s a a'' ->
    step_argmatch_plain s [MatchA a a'] [MatchA a'' a']
  | sagp_ctx2 : forall s a a' a'',
    step_arg s a' a'' ->
    step_argmatch_plain s [MatchA a a'] [MatchA a a'']
  | sagp_eq : forall s a,
    step_argmatch_plain s [MatchA a a] []
    (* TODO disjointness *)

with

step_expmatch_plain : store -> list expmatch -> list expmatch -> Prop :=
  | semp_ctx1 : forall s e e' e'',
    step_exp s e e'' ->
    step_expmatch_plain s [MatchEM e e'] [MatchEM e'' e']
  | semp_ctx2 : forall s e e' e'',
    step_exp s e' e'' ->
    step_expmatch_plain s [MatchEM e e'] [MatchEM e e'']
  | semp_eq : forall s e,
    step_expmatch_plain s [MatchEM e e] []
  | semp_unplus : forall s num e,
    negb (isneg num) ->
    step_expmatch_plain s [MatchEM (NumE num) (UnE (NumUnop PlusOp) e)] [MatchEM (NumE num) e]
  | semp_unplus_false : forall s num e,
    isneg num ->
    step_expmatch_plain s [MatchEM (NumE num) (UnE (NumUnop PlusOp) e)] [FailEM]
  | semp_unminus : forall s num num' e,
    isneg num ->
    numun MinusOp num = Some num' ->
    step_expmatch_plain s [MatchEM (NumE num) (UnE (NumUnop MinusOp) e)] [MatchEM (NumE num') e] 
  | semp_unminus_false : forall s num e,
    negb (isneg num) ->
    step_expmatch_plain s [MatchEM (NumE num) (UnE (NumUnop MinusOp) e)] [FailEM]
  | semp_cvt : forall s num e nt1 nt2 num',
    numcvt nt1 num = Some num' ->
    step_expmatch_plain s [MatchEM (NumE num) (CvtE e nt1 nt2)] [MatchEM (NumE num') e]
  | semp_cvt_false : forall s num e nt1 nt2,
    numcvt nt1 num = None ->
    step_expmatch_plain s [MatchEM (NumE num) (CvtE e nt1 nt2)] [FailEM]
  | semp_tup : forall s tups tups',
    size tups = size tups' ->
    step_expmatch_plain s [MatchEM (TupE tups) (TupE tups')] (list_zipWith (fun e e' => MatchEM e e') tups tups')
  | semp_case : forall s e e' op,
    step_expmatch_plain s [MatchEM (CaseE op e) (CaseE op e')] [MatchEM e e']
  | semp_case_fail : forall s e e' op op',
    op <> op' ->
    step_expmatch_plain s [MatchEM (CaseE op e) (CaseE op' e')] [MatchEM e e']
  | semp_opt : forall s e e',
    same_opt e e' ->
    step_expmatch_plain s [MatchEM (OptE e) (OptE e')] (list_zipWith (fun e1 e2 => MatchEM e1 e2) (opt_to_lst e) (opt_to_lst e'))
  | semp_opt_fail : forall s e e',
    negb (same_opt e e') ->
    step_expmatch_plain s [MatchEM (OptE e) (OptE e')] [FailEM]
  | semp_list : forall s es es',
    size es = size es' ->
    step_expmatch_plain s [MatchEM (ListE es) (ListE es')] (list_zipWith (fun e1 e2 => MatchEM e1 e2) es es')
  | semp_list_fail : forall s es es',
    size es <> size es' ->
    step_expmatch_plain s [MatchEM (ListE es) (ListE es')] [FailEM]
  | semp_lift : forall s es e,
    size es <= 1 ->
    step_expmatch_plain s [MatchEM (ListE es) (LiftE e)] [MatchEM (OptE (lst_to_opt es)) e]
  | semp_lift_fail : forall s es e,
    size es > 1 ->
    step_expmatch_plain s [MatchEM (ListE es) (LiftE e)] [FailEM]
  | semp_cat_left : forall s e1s e2s e1s' e2',
    size e1s = size e1s' ->
    step_expmatch_plain s [MatchEM (ListE (e1s ++ e2s)) (CatE (ListE e1s') e2')] [MatchEM (ListE e1s) (ListE e1s'); MatchEM (ListE e2s) e2']
  | semp_cat_left_fail : forall s e1s e2s e1s' e2',
    size e1s <> size e1s' ->
    step_expmatch_plain s [MatchEM (ListE (e1s ++ e2s)) (CatE (ListE e1s') e2')] [FailEM]
  | semp_cat_right : forall s e1s e2s e1' e2s',
    size e2s = size e2s' ->
    step_expmatch_plain s [MatchEM (ListE (e1s ++ e2s)) (CatE e1' (ListE e2s'))] [MatchEM (ListE e1s) e1'; MatchEM (ListE e2s) (ListE e2s')]
  | semp_cat_right_fail : forall s e1s e2s e1' e2s',
    size e2s <> size e2s' ->
    step_expmatch_plain s [MatchEM (ListE (e1s ++ e2s)) (CatE e1' (ListE e2s'))] [FailEM] 
  | semp_str : forall s efs efs' es,
    List.Forall2 (fun '(l, e) '(l', e') => l = l' /\ List.In (l, e) efs) es efs' ->
    step_expmatch_plain s [MatchEM (StrE efs) (StrE efs')] (list_zipWith (fun ef ef' => MatchEM (exp_from_field ef) (exp_from_field ef')) es efs')
  | semp_iter_plus : forall s es e' eps,
    size es >= 1 ->
    step_expmatch_plain s [MatchEM (ListE es) (IterE e' I_PLUS eps)] [MatchEM (ListE es) (IterE e' I_STAR eps)]
  | semp_iter_plus_fail : forall s es e' eps,
    es = [] ->
    step_expmatch_plain s [MatchEM (ListE es) (IterE e' I_PLUS eps)] [FailEM]
  | semp_iter_star : forall s es e' eps y n,
    size es = n ->
    step_expmatch_plain s [MatchEM (ListE es) (IterE e' I_PLUS eps)] [MatchEM (ListE es) (IterE e' (I_SUP y (NumE (NatE n))) eps)]
    (* TODO y fresh *)
  | semp_sub_sub : forall s e t1 t2 e' t1' t2',
    sub_typ (store_to_env s) t1 t1' ->
    step_expmatch_plain s [MatchEM (SubE e t1 t2) (SubE e' t1' t2')] [MatchEM (SubE e t1 t1') e']
    (* TODO disjointness *)
  | semp_sub_tup : forall s es e' typs typs',
    size es = size typs ->
    size typs = size typs' ->
    let sbst1 := many_svars (list_mapi (fun i '(e, (x, _)) => (x, ProjE e i)) (zip es typs)) in
    let sbst2 := many_svars (list_mapi (fun i '(e, (x, _)) => (x, ProjE e i)) (zip es typs')) in
    let tups := List.map (fun '((_, t1), (_, t2)) => SubE e' (subst_typ sbst1 t1) (subst_typ sbst2 t2)) (zip typs typs') in
    step_expmatch_plain s [MatchEM (TupE es) (SubE e' (TupT typs) (TupT typs'))] 
    [MatchEM (TupE tups) e']

with

step_argmatch : store -> list il_quant -> list argmatch -> il_subst -> list il_quant -> list argmatch -> Prop :=
  | sam_plain : forall s qs ams ams',
    step_argmatch_plain s ams ams' ->
    step_argmatch s qs ams subst_empty qs ams'
  | sam_seq : forall s q1s qs qs' q2s am1s am am2s ams' sbst,
    step_argmatch s qs [am] sbst qs' ams' ->
    let new_q2s :=  List.map (subst_quant sbst) q2s in
    let new_am2s := List.map (subst_argmatch sbst) am2s in
    step_argmatch s (q1s ++ qs ++ q2s) (am1s ++ [am] ++ am2s) sbst (q1s ++ qs' ++ new_q2s) (am1s ++ ams' ++ new_am2s)
  | sam_seq_fail : forall s q1s qs q2s am1s am am2s sbst,
    step_argmatch s qs [am] sbst [] [FailA] ->
    step_argmatch s (q1s ++ qs ++ q2s) (am1s ++ [am] ++ am2s) sbst [] [FailA]
  | sam_typ : forall s x t,
    let sbst := subst_styp x t in
    step_argmatch s [TypP x] [MatchA (TypA t) (TypA (VarT x []))] sbst [] []
  | sam_exp : forall s x t e,
    let sbst := subst_svar x e in
    step_argmatch s [ExpP x t] [MatchA (ExpA e) (ExpA (VarE x))] sbst [] []
  | sam_fun : forall s x ps t y,
    let sbst := subst_sfun x y in
    step_argmatch s [DefP x ps t] [MatchA (DefA y) (DefA x)] sbst [] []
  | sam_exp_exp : forall s qs qs' em ems' sbst,
    step_expmatch s qs [em] sbst qs' ems' ->
    step_argmatch s qs [to_argmatch em] sbst qs' (List.map to_argmatch ems')
  | sam_exp_exp_fail : forall s qs em sbst,
    step_expmatch s qs [em] sbst [] [FailEM] ->
    step_argmatch s qs [to_argmatch em] sbst [] [FailA]

with

step_expmatch : store -> list il_quant -> list expmatch -> il_subst -> list il_quant -> list expmatch -> Prop :=
  | sem_plain : forall s qs ems ems',
    step_expmatch_plain s ems ems' ->
    step_expmatch s qs ems subst_empty qs ems'
  | sem_seq : forall s q1s qs qs' q2s em1s em em2s ems' sbst,
    step_expmatch s qs [em] sbst qs' ems' ->
    let new_q2s :=  List.map (subst_quant sbst) q2s in
    let new_em2s := List.map (subst_expmatch sbst) em2s in
    step_expmatch s (q1s ++ qs ++ q2s) (em1s ++ [em] ++ em2s) sbst (q1s ++ qs' ++ new_q2s) (em1s ++ ems' ++ new_em2s)
  | sem_seq_fail : forall s q1s qs q2s em1s em em2s sbst,
    step_expmatch s qs [em] sbst [] [FailEM] ->
    step_expmatch s (q1s ++ qs ++ q2s) (em1s ++ [em] ++ em2s) sbst [] [FailEM]
  | sem_iter_sup : forall s qs es e' y e_n eps n (xss : list (list il_id)),
    size es = n ->
    seq.all (fun xs => size xs == size es) xss ->
    let xss' := transpose xss in
    let qs' := List.concat (List.map (fun xs => list_zipWith (fun '(_, t, _) x => ExpP x t) eps xs) xss) in
    let ems := list_mapi (fun i '(xs, e) => 
      let sup_sbst := subst_svar y (NumE (NatE i)) in 
      let sbst := many_svars (List.map (fun '((x, _, _), x') => (x, VarE x')) (zip eps xs)) in
      MatchEM e (subst_exp (append_subst sup_sbst sbst) e') 
    ) (zip xss es) in
    let num_match := [MatchEM (NumE (NatE n)) e_n] in
    let list_match := list_zipWith (fun xs' '(_, _, ep) => MatchEM (ListE (List.map VarE xs')) ep) xss' eps in
    step_expmatch s qs [MatchEM (ListE es) (IterE e' (I_SUP y e_n) eps)] subst_empty (qs' ++ qs) (ems ++ num_match ++ list_match)
  | sem_iter_opt : forall s qs e e' eps (xss : option (list il_id)),
    let xss' := transpose_opt xss in
    let qs' := List.concat (List.map (fun xs => list_zipWith (fun '(_, t, _) x => ExpP x t) eps xs) (opt_to_lst xss)) in
    let ems := list_zipWith (fun xs e => 
      let sbst := many_svars (List.map (fun '((x, _, _), x') => (x, VarE x')) (zip eps xs)) in
      MatchEM e (subst_exp sbst e') 
    ) (opt_to_lst xss) (opt_to_lst e) in
    let opt_match := list_zipWith (fun xs' '(_, _, ep) => MatchEM (OptE (option_map VarE xs')) ep) xss' eps in
    step_expmatch s qs [MatchEM (OptE e) (IterE e' I_OPT eps)] subst_empty (qs' ++ qs) (ems ++ opt_match)

with

sub_typ : il_env -> il_typ -> il_typ -> Prop :=
  | st_tup : forall env x1 t1 x2 t2 tups tups',
    let env' := (single_var x1 t1) in
    let sbst := (subst_svar x2 (VarE x1)) in
    sub_typ env t1 t2 ->
    sub_typ (env @@ env') (TupT tups) (subst_typ sbst (TupT tups')) -> 
    sub_typ env (TupT ((x1, t1) :: tups)) (TupT ((x2, t2) :: tups'))
  | st_struct : forall env t1 t2 tfs1 tfs2,
    expand_typ (env_to_store env) t1 (StructT tfs1) ->
    expand_typ (env_to_store env) t2 (StructT tfs2) -> 
    sub_typ env t1 t2
  | st_iter : forall env t1 t2 it,
    sub_typ env t1 t2 ->
    sub_typ env (IterT t1 it) (IterT t2 it) 
  | st_refl : forall env t, sub_typ env t t
  | st_trans : forall env t1 t2 t',
    sub_typ env t1 t' ->
    sub_typ env t' t2 ->
    sub_typ env t1 t2

with

expand_typ : store -> il_typ -> il_deftyp -> Prop :=
  | et_plain : forall s t t',
    is_plaintyp t ->
    reduce_typ s t t' ->
    expand_typ s t (AliasT t)
  | et_def : forall s t dt x insts,
    reduce_typ s t (MatchT x [] (([], [], dt) :: insts)) -> 
    expand_typ s t dt

with

reduce_typ : store -> il_typ -> il_typ -> Prop :=
  | rt_refl : forall s t, reduce_typ s t t
  | rt_step : forall s t1 t2 t3,
    step_typ s t1 t2 ->
    reduce_typ s t2 t3 ->
    reduce_typ s t1 t3
.

Inductive reduce_arg : store -> il_arg -> il_arg -> Prop :=
  | ra_refl : forall s a, reduce_arg s a a
  | ra_step : forall s a1 a2 a3,
    step_arg s a1 a2 ->
    reduce_arg s a2 a3 ->
    reduce_arg s a1 a3
.

Inductive eq_typ : store -> il_typ -> il_typ -> Prop :=
  | eq_typ_rule : forall s t1 t2 t1' t2',
    reduce_typ s t1 t1' ->
    reduce_typ s t2 t2' ->
    t1' = t2' ->
    eq_typ s t1 t2
.
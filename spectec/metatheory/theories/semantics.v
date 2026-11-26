From Stdlib Require Import List String NArith.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.
From MetaSpectec Require Import syntax env subst numerics utils.
Import ListNotations.
Open Scope env_scope.

(* REDUCTION AND TYPING
   (doc/semantics/il/5-reduction.spectec and 6-typing.spectec)

   The two are mutually dependent in the DSL: reduction needs [Ok_subst]
   (MATCH-guess, REL, quantprems-guess) and typing needs [Expand_typ] and
   [Eq_typ].  Hence they form a single mutual inductive here.

   Partiality: a step  S |- X ~> X?  is  [step_X s x (Some x')]  for a step to
   x' and  [step_X s x None]  for failure (DSL: eps).  Context rules use
   [option_map] so that one rule covers both the step and its failure.

   Inductive premises use projections (tf_typ, ef_exp, ...) rather than
   destructuring patterns, which the positivity checker rejects.

   NAT numbers are Stdlib N, while list indices and lengths are nat; rules
   that index lists hence take n : nat and match on NatE (N.of_nat n). *)

(* Non-mutual parts *)

Inductive sub_numtyp : numtyp -> numtyp -> Prop :=
  | sn_nat : sub_numtyp NatT IntT
  | sn_int : sub_numtyp IntT RatT
  | sn_rat : sub_numtyp RatT RealT
  | sn_refl : forall nt, sub_numtyp nt nt
  | sn_trans : forall nt1 nt2 nt,
    sub_numtyp nt1 nt ->
    sub_numtyp nt nt2 ->
    sub_numtyp nt1 nt2
.

Inductive ok_numunop : numunop -> numtyp -> numtyp -> Prop :=
  | ok_unop_sign : forall numop nt,
    sub_numtyp IntT nt ->
    ok_numunop numop nt nt
.

Inductive ok_numbinop : numbinop -> numtyp -> numtyp -> numtyp -> Prop :=
  | ok_binop_add : forall nt, ok_numbinop AddOp nt nt nt
  | ok_binop_sub : forall nt nt',
    sub_numtyp IntT nt' ->
    ok_numbinop SubOp nt nt nt'
  | ok_binop_mul : forall nt, ok_numbinop MulOp nt nt nt
  | ok_binop_div : forall nt nt',
    sub_numtyp RatT nt' ->
    ok_numbinop DivOp nt nt nt'
  | ok_binop_mod : forall nt,
    sub_numtyp nt IntT ->
    ok_numbinop ModOp nt nt nt
  | ok_binop_pownat : forall nt, ok_numbinop PowOp nt NatT nt
  | ok_binop_powint : forall nt,
    sub_numtyp nt RatT ->
    ok_numbinop PowOp nt IntT nt
.

Definition iter_subst (eps : list exppull) (ess : list (list il_exp)) (y : il_id) (default : il_exp) (i : nat) : il_subst :=
  append_subst
    (many_svars (zip (List.map pull_id eps) (List.map (fun es => nth default es i) ess)))
    (subst_svar y (NumE (NatE (N.of_nat i)))).

Inductive

(* Types *)

step_typ : store -> il_typ -> option il_typ -> Prop :=
  | stt_var_apply : forall s x args ps insts,
    s_lookup_typ s x = Some (ps, insts) ->
    step_typ s (VarT x args) (Some (MatchT x args insts))
  | stt_match_alias : forall s x t insts,
    step_typ s (MatchT x [] (([], [], AliasT t) :: insts)) (Some t)
  | stt_match_match : forall s x args qs args' dt insts sbst qs' ams',
    size args = size args' ->
    step_argmatch s qs (zip args args') sbst (Some (qs', ams')) ->
    step_typ s (MatchT x args ((qs, args', dt) :: insts))
      (Some (MatchT x (List.map fst ams')
        [(qs', List.map snd ams', subst_deftyp sbst dt);
         ([], List.map fst ams', AliasT (MatchT x args insts))]))
  | stt_match_fail : forall s x args qs args' dt insts sbst,
    size args = size args' ->
    step_argmatch s qs (zip args args') sbst None ->
    step_typ s (MatchT x args ((qs, args', dt) :: insts)) (Some (MatchT x args insts))
  | stt_var_ctx : forall s x args n a oa,
    List.nth_error args n = Some a ->
    step_arg s a oa ->
    step_typ s (VarT x args) (option_map (fun a' => VarT x (update args n a')) oa)
  | stt_match_ctx1 : forall s x args insts n a oa,
    List.nth_error args n = Some a ->
    step_arg s a oa ->
    step_typ s (MatchT x args insts) (option_map (fun a' => MatchT x (update args n a') insts) oa)
  | stt_match_ctx2 : forall s x args insts n i oi,
    List.nth_error insts n = Some i ->
    step_inst s i oi ->
    step_typ s (MatchT x args insts) (option_map (fun i' => MatchT x args (update insts n i')) oi)
  | stt_tup_ctx : forall s xts n x t ot,
    List.nth_error xts n = Some (x, t) ->
    step_typ s t ot ->
    step_typ s (TupT xts) (option_map (fun t' => TupT (update xts n (x, t'))) ot)
  | stt_iter_ctx : forall s t it ot,
    step_typ s t ot ->
    step_typ s (IterT t it) (option_map (fun t' => IterT t' it) ot)

(* Iterators *)

with step_iter : store -> iter -> option iter -> Prop :=
  | si_sup_ctx : forall s x e oe,
    step_exp s e oe ->
    step_iter s (I_SUP x e) (option_map (I_SUP x) oe)

with step_exppull : store -> exppull -> option exppull -> Prop :=
  | sepl_ctx1 : forall s x t e ot,
    step_typ s t ot ->
    step_exppull s (x, t, e) (option_map (fun t' => (x, t', e)) ot)
  | sepl_ctx2 : forall s x t e oe,
    step_exp s e oe ->
    step_exppull s (x, t, e) (option_map (fun e' => (x, t, e')) oe)

with step_exppush : store -> exppush -> option exppush -> Prop :=
  | seps_ctx1 : forall s e x t oe,
    step_exp s e oe ->
    step_exppush s (e, x, t) (option_map (fun e' => (e', x, t)) oe)
  | seps_ctx2 : forall s e x t ot,
    step_typ s t ot ->
    step_exppush s (e, x, t) (option_map (fun t' => (e, x, t')) ot)

(* Expressions *)

with step_exp : store -> il_exp -> option il_exp -> Prop :=
  | se_un_bool : forall s op b,
    step_exp s (UnE (BoolUnop op) (BoolE b)) (Some (BoolE (boolun op b)))
  | se_un_num : forall s op n n',
    numun op n = Some n' ->
    step_exp s (UnE (NumUnop op) (NumE n)) (Some (NumE n'))
  | se_bin_bool : forall s op b1 b2,
    step_exp s (BinE (BoolBinop op) (BoolE b1) (BoolE b2)) (Some (BoolE (boolbin op b1 b2)))
  | se_bin_num : forall s op n1 n2 n3,
    numbin op n1 n2 = Some n3 ->
    step_exp s (BinE (NumBinop op) (NumE n1) (NumE n2)) (Some (NumE n3))
  | se_cmp_eq_true : forall s v1 v2,
    v1 = v2 ->
    step_exp s (CmpE (BoolCmpop EqOp) (val_to_exp v1) (val_to_exp v2)) (Some (BoolE true))
  | se_cmp_eq_false : forall s v1 v2,
    v1 <> v2 ->
    step_exp s (CmpE (BoolCmpop EqOp) (val_to_exp v1) (val_to_exp v2)) (Some (BoolE false))
  | se_cmp_ne_true : forall s v1 v2,
    v1 <> v2 ->
    step_exp s (CmpE (BoolCmpop NeqOp) (val_to_exp v1) (val_to_exp v2)) (Some (BoolE true))
  | se_cmp_ne_false : forall s v1 v2,
    v1 = v2 ->
    step_exp s (CmpE (BoolCmpop NeqOp) (val_to_exp v1) (val_to_exp v2)) (Some (BoolE false))
  | se_cmp_num : forall s op n1 n2 b,
    numcmp op n1 n2 = Some b ->
    step_exp s (CmpE (NumCmpop op) (NumE n1) (NumE n2)) (Some (BoolE b))

  | se_lift_none : forall s,
    step_exp s (LiftE (OptE None)) (Some (ListE []))
  | se_lift_some : forall s e,
    step_exp s (LiftE (OptE (Some e))) (Some (ListE [e]))
  | se_sel_tup : forall s vs n v,
    List.nth_error vs n = Some v ->
    step_exp s (ProjE (val_to_exp (TupV vs)) n) (Some (val_to_exp v))
  | se_len_list : forall s vs,
    step_exp s (LenE (val_to_exp (ListV vs))) (Some (NumE (NatE (N.of_nat (size vs)))))
  | se_mem_true : forall s v vs,
    List.In v vs ->
    step_exp s (MemE (val_to_exp v) (val_to_exp (ListV vs))) (Some (BoolE true))
  | se_mem_false : forall s v vs,
    List.Forall (fun v2 => v <> v2) vs ->
    step_exp s (MemE (val_to_exp v) (val_to_exp (ListV vs))) (Some (BoolE false))
  | se_cat_opt1 : forall s eo,
    step_exp s (CatE (OptE eo) (OptE None)) (Some (OptE eo))
  | se_cat_opt2 : forall s eo,
    step_exp s (CatE (OptE None) (OptE eo)) (Some (OptE eo))
  | se_cat_opt_bad : forall s e1 e2,
    step_exp s (CatE (OptE (Some e1)) (OptE (Some e2))) None
  | se_cat_list : forall s es1 es2,
    step_exp s (CatE (ListE es1) (ListE es2)) (Some (ListE (es1 ++ es2)))
  | se_cat_str : forall s t fs1 fs2,
    List.Forall2 (fun f1 f2 => ef_atom f1 = ef_atom f2) fs1 fs2 ->
    List.Forall (fun f => ef_qpr f = Some trueqpr) fs1 ->
    List.Forall (fun f => ef_qpr f = Some trueqpr) fs2 ->
    step_exp s (CatE (StrE t fs1) (StrE t fs2))
      (Some (StrE t (list_zipWith (fun f1 f2 => (ef_atom f1, CatE (ef_exp f1) (ef_exp f2), Some trueqpr)) fs1 fs2)))

  (* Inject the premises of a yet unchecked intro form *)
  | se_str : forall s t fs tfs,
    expand_typ s t (StructT tfs) ->
    List.Forall2 (fun f tf => ef_atom f = tf_atom tf) fs tfs ->
    List.Forall (fun f => ef_qpr f = None) fs ->
    step_exp s (StrE t fs)
      (Some (StrE t (list_zipWith (fun f tf =>
        (ef_atom f, ef_exp f, Some (subst_quantprems (tupsubst (ef_exp f) (tf_typ tf)) (tf_quantprems tf)))) fs tfs)))
  | se_inj : forall s t op e tcs qs t' prs,
    expand_typ s t (VariantT tcs) ->
    List.In (op, qs, t', prs) tcs ->
    step_exp s (CaseE t op e None) (Some (CaseE t op e (Some (subst_quantprems (tupsubst e t') (qs, prs)))))

  | se_acc_root : forall s e,
    step_exp s (AccE e RootP) (Some e)
  | se_acc_the_some : forall s e p e',
    step_exp s (AccE e p) (Some (OptE (Some e'))) ->
    step_exp s (AccE e (TheP p)) (Some e')
  | se_acc_the_none : forall s e p,
    step_exp s (AccE e p) (Some (OptE None)) ->
    step_exp s (AccE e (TheP p)) None
  | se_acc_idx_inb : forall s e p vs n v,
    step_exp s (AccE e p) (Some (val_to_exp (ListV vs))) ->
    List.nth_error vs n = Some v ->
    step_exp s (AccE e (IdxP p (NumE (NatE (N.of_nat n))))) (Some (val_to_exp v))
  | se_acc_idx_oob : forall s e p es n,
    step_exp s (AccE e p) (Some (ListE es)) ->
    size es <= n ->
    step_exp s (AccE e (IdxP p (NumE (NatE (N.of_nat n))))) None
  | se_acc_slice_inb : forall s e p vs n m,
    step_exp s (AccE e p) (Some (val_to_exp (ListV vs))) ->
    n + m <= size vs ->
    step_exp s (AccE e (SliceP p (NumE (NatE (N.of_nat n))) (NumE (NatE (N.of_nat m))))) (Some (ListE (slice n m (List.map val_to_exp vs))))
  | se_acc_slice_oob : forall s e p es n m,
    step_exp s (AccE e p) (Some (ListE es)) ->
    size es < n + m ->
    step_exp s (AccE e (SliceP p (NumE (NatE (N.of_nat n))) (NumE (NatE (N.of_nat m))))) None
  | se_acc_dot : forall s e p t vfs n a v,
    step_exp s (AccE e p) (Some (val_to_exp (StrV t vfs))) ->
    List.nth_error vfs n = Some (a, v) ->
    step_exp s (AccE e (DotP p a)) (Some (val_to_exp v))
  | se_acc_proj_good : forall s e p t m e',
    step_exp s (AccE e p) (Some (CaseE t m e' (Some trueqpr))) ->
    step_exp s (AccE e (UncaseP p m)) (Some e')
  | se_acc_proj_bad : forall s e p t m m' e',
    step_exp s (AccE e p) (Some (CaseE t m' e' (Some trueqpr))) ->
    m' <> m ->
    step_exp s (AccE e (UncaseP p m)) None

  | se_upd_root : forall s v1 e2,
    step_exp s (UpdE (val_to_exp v1) RootP e2) (Some e2)
  | se_upd_the_some : forall s e1 p e2 v',
    step_exp s (AccE e1 p) (Some (OptE (Some (val_to_exp v')))) ->
    step_exp s (UpdE e1 (TheP p) e2) (Some (UpdE e1 p (OptE (Some e2))))
  (* DSL premise reads  ACC e_1 p ~> eps ; OPT eps is meant *)
  | se_upd_the_none : forall s e1 p e2,
    step_exp s (AccE e1 p) (Some (OptE None)) ->
    step_exp s (UpdE e1 (TheP p) e2) None
  | se_upd_idx_inb : forall s e1 p n e2 vs,
    step_exp s (AccE e1 p) (Some (val_to_exp (ListV vs))) ->
    n < size vs ->
    step_exp s (UpdE e1 (IdxP p (NumE (NatE (N.of_nat n)))) e2) (Some (UpdE e1 p (ListE (update (List.map val_to_exp vs) n e2))))
  | se_upd_idx_oob : forall s e1 p n e2 es,
    step_exp s (AccE e1 p) (Some (ListE es)) ->
    size es <= n ->
    step_exp s (UpdE e1 (IdxP p (NumE (NatE (N.of_nat n)))) e2) None
  | se_upd_slice_inb : forall s e1 p n m e2s vs,
    step_exp s (AccE e1 p) (Some (val_to_exp (ListV vs))) ->
    n + m <= size vs ->
    step_exp s (UpdE e1 (SliceP p (NumE (NatE (N.of_nat n))) (NumE (NatE (N.of_nat m)))) (ListE e2s))
      (Some (UpdE e1 p (ListE (update_slice (List.map val_to_exp vs) n m e2s))))
  | se_upd_slice_oob : forall s e1 p n m e2s es,
    step_exp s (AccE e1 p) (Some (ListE es)) ->
    size es < n + m ->
    step_exp s (UpdE e1 (SliceP p (NumE (NatE (N.of_nat n))) (NumE (NatE (N.of_nat m)))) (ListE e2s)) None
  (* premises reset on the result, to trigger a recheck *)
  | se_upd_dot : forall s e1 p e2 t vfs n a v',
    step_exp s (AccE e1 p) (Some (val_to_exp (StrV t vfs))) ->
    List.nth_error vfs n = Some (a, v') ->
    step_exp s (UpdE e1 (DotP p a) e2)
      (Some (UpdE e1 p (StrE t (update (List.map (fun av => (av.1, val_to_exp av.2, Some trueqpr)) vfs) n (a, e2, None)))))
  | se_upd_proj_good : forall s e1 p m e2 t v',
    step_exp s (AccE e1 p) (Some (val_to_exp (CaseV t m v'))) ->
    step_exp s (UpdE e1 (UncaseP p m) e2) (Some (UpdE e1 p (CaseE t m e2 None)))
  | se_upd_proj_bad : forall s e1 p m m' e2 t e',
    step_exp s (AccE e1 p) (Some (CaseE t m' e' (Some trueqpr))) ->
    m' <> m ->
    step_exp s (UpdE e1 (UncaseP p m) e2) None
  | se_ext : forall s e1 p e2,
    step_exp s (ExtE e1 p e2) (Some (UpdE e1 p (CatE (AccE e1 p) e2)))

  | se_iter_quest_none : forall s e eps,
    List.Forall (fun ep => pull_exp ep = OptE None) eps ->
    step_exp s (IterE e I_OPT eps) (Some (OptE None))
  (* With no pulled variables the DSL yields OPT eps (se_iter_quest_none) *)
  | se_iter_quest_some : forall s e eps es,
    eps <> [] ->
    List.Forall2 (fun ep e' => pull_exp ep = OptE (Some e')) eps es ->
    step_exp s (IterE e I_OPT eps) (Some (OptE (Some (subst_exp (many_svars (zip (List.map pull_id eps) es)) e))))
  | se_iter_plus : forall s e eps ess es0 ess',
    List.Forall2 (fun ep es => pull_exp ep = ListE es) eps ess ->
    ess = es0 :: ess' ->
    1 <= size es0 ->
    step_exp s (IterE e I_PLUS eps) (Some (IterE e I_STAR eps))
  | se_iter_star : forall s e eps ess es0 ess' y,
    List.Forall2 (fun ep es => pull_exp ep = ListE es) eps ess ->
    ess = es0 :: ess' ->
    Fresh_id y ->
    step_exp s (IterE e I_STAR eps) (Some (IterE e (I_SUP y (NumE (NatE (N.of_nat (size es0))))) eps))
  | se_iter_sup_good : forall s e y n eps ess,
    List.Forall2 (fun ep es => pull_exp ep = ListE es) eps ess ->
    List.Forall (fun es => size es = n) ess ->
    step_exp s (IterE e (I_SUP y (NumE (NatE (N.of_nat n)))) eps)
      (Some (ListE (List.map (fun i => subst_exp (iter_subst eps ess y (VarE y) i) e) (iota 0 n))))
  | se_iter_sup_bad : forall s e y n eps ess,
    List.Forall2 (fun ep es => pull_exp ep = ListE es) eps ess ->
    List.Exists (fun es => size es <> n) ess ->
    step_exp s (IterE e (I_SUP y (NumE (NatE (N.of_nat n)))) eps) None

  | se_call_apply : forall s x args ps t cs,
    s_lookup_fun s x = Some (ps, t, cs) ->
    step_exp s (CallE x args) (Some (MatchE args cs))

  | se_cvt_good : forall s n nt1 nt2 n',
    num_cvt nt2 n (Some n') ->
    step_exp s (CvtE (NumE n) nt1 nt2) (Some (NumE n'))
  | se_cvt_bad : forall s n nt1 nt2,
    num_cvt nt2 n None ->
    step_exp s (CvtE (NumE n) nt1 nt2) None

  | se_sub_refl : forall s e t,
    step_exp s (SubE e t t) (Some e)
  | se_sub_sub : forall s e' t1' t2' t1 t2,
    step_exp s (SubE (SubE e' t1' t2') t1 t2) (Some (SubE e' t1' t2))
  | se_sub_tup : forall s es xts1 xts2,
    size es = size xts1 ->
    size xts1 = size xts2 ->
    let s1 := many_svars (zip (List.map fst xts1) es) in
    let s2 := many_svars (zip (List.map fst xts2) es) in
    step_exp s (SubE (TupE es) (TupT xts1) (TupT xts2))
      (Some (TupE (list_map3 (fun e xt1 xt2 => SubE e (subst_typ s1 xt1.2) (subst_typ s2 xt2.2)) es xts1 xts2)))
  | se_sub_opt : forall s eo t1 t2,
    step_exp s (SubE (OptE eo) (IterT t1 I_OPT) (IterT t2 I_OPT)) (Some (OptE (option_map (fun e => SubE e t1 t2) eo)))
  | se_sub_list : forall s es t1 t2,
    step_exp s (SubE (ListE es) (IterT t1 I_STAR) (IterT t2 I_STAR)) (Some (ListE (List.map (fun e => SubE e t1 t2) es)))
  (* premises reset on the result, to trigger a recheck *)
  | se_sub_str : forall s fs x1 x2 t1 t2 tfs1 tfs2 t1as es,
    t1 = MatchT x1 [] [([], [], StructT tfs1)] ->
    t2 = MatchT x2 [] [([], [], StructT tfs2)] ->
    List.Forall (fun f => ef_qpr f = Some trueqpr) fs ->
    List.Forall2 (fun tf2 t1a => exists qs prs, List.In (tf_atom tf2, qs, t1a, prs) tfs1) tfs2 t1as ->
    List.Forall2 (fun tf2 e => List.In (tf_atom tf2, e, Some trueqpr) fs) tfs2 es ->
    step_exp s (SubE (StrE t1 fs) t1 t2)
      (Some (StrE t2 (list_map3 (fun tf2 t1a e => (tf_atom tf2, SubE e t1a (tf_typ tf2), None)) tfs2 t1as es)))
  | se_sub_inj : forall s e op x1 x2 t1 t2 t1' t2' tcs1 tcs2 qs1 qs2 prs1 prs2,
    t1 = MatchT x1 [] [([], [], VariantT tcs1)] ->
    t2 = MatchT x2 [] [([], [], VariantT tcs2)] ->
    List.In (op, qs1, t1', prs1) tcs1 ->
    List.In (op, qs2, t2', prs2) tcs2 ->
    step_exp s (SubE (CaseE t1 op e (Some trueqpr)) t1 t2) (Some (CaseE t2 op (SubE e t1' t2') None))

  | se_match_match : forall s args qs args' e prs cs sbst qs' ams',
    size args = size args' ->
    step_argmatch s qs (zip args args') sbst (Some (qs', ams')) ->
    let ep := subst_expprems sbst e prs in
    step_exp s (MatchE args ((qs, args', e, prs) :: cs))
      (Some (MatchE (List.map fst ams')
        [(qs', List.map snd ams', ep.1, ep.2);
         ([], List.map fst ams', MatchE args cs, [])]))
  | se_match_fail : forall s args qs args' e prs cs sbst,
    size args = size args' ->
    step_argmatch s qs (zip args args') sbst None ->
    step_exp s (MatchE args ((qs, args', e, prs) :: cs)) (Some (MatchE args cs))
  (* Non-computational.  The DSL leaves e and pr* unsubstituted, which leaves
     the removed quantifiers free; we substitute them. *)
  | se_match_guess : forall s args qs args' e prs cs sbst,
    ok_subst (store_to_env s) sbst qs ->
    let ep := subst_expprems sbst e prs in
    step_exp s (MatchE args ((qs, args', e, prs) :: cs))
      (Some (MatchE args (([], List.map (subst_arg sbst) args', ep.1, ep.2) :: cs)))
  | se_match_true : forall s e cs,
    step_exp s (MatchE [] (([], [], e, []) :: cs)) (Some e)
  | se_match_false : forall s e prs cs,
    step_exp s (MatchE [] (([], [], e, IfPr (BoolE false) :: prs) :: cs)) (Some (MatchE [] cs))

  (* IfE (Rocq extension) *)
  | se_if_true : forall s e2 e3,
    step_exp s (IfE (BoolE true) e2 e3) (Some e2)
  | se_if_false : forall s e2 e3,
    step_exp s (IfE (BoolE false) e2 e3) (Some e3)

  (* Context rules (each covers the step and its failure) *)
  | se_un_ctx : forall s op e oe,
    step_exp s e oe ->
    step_exp s (UnE op e) (option_map (UnE op) oe)
  | se_bin_ctx1 : forall s op e1 e2 oe,
    step_exp s e1 oe ->
    step_exp s (BinE op e1 e2) (option_map (fun e1' => BinE op e1' e2) oe)
  | se_bin_ctx2 : forall s op e1 e2 oe,
    step_exp s e2 oe ->
    step_exp s (BinE op e1 e2) (option_map (fun e2' => BinE op e1 e2') oe)
  | se_cmp_ctx1 : forall s op e1 e2 oe,
    step_exp s e1 oe ->
    step_exp s (CmpE op e1 e2) (option_map (fun e1' => CmpE op e1' e2) oe)
  | se_cmp_ctx2 : forall s op e1 e2 oe,
    step_exp s e2 oe ->
    step_exp s (CmpE op e1 e2) (option_map (fun e2' => CmpE op e1 e2') oe)
  | se_opt_ctx : forall s e oe,
    step_exp s e oe ->
    step_exp s (OptE (Some e)) (option_map (fun e' => OptE (Some e')) oe)
  | se_list_ctx : forall s es n e oe,
    List.nth_error es n = Some e ->
    step_exp s e oe ->
    step_exp s (ListE es) (option_map (fun e' => ListE (update es n e')) oe)
  | se_tup_ctx : forall s es n e oe,
    List.nth_error es n = Some e ->
    step_exp s e oe ->
    step_exp s (TupE es) (option_map (fun e' => TupE (update es n e')) oe)
  | se_str_ctx1 : forall s t fs ot,
    step_typ s t ot ->
    step_exp s (StrE t fs) (option_map (fun t' => StrE t' fs) ot)
  | se_str_ctx2 : forall s t fs n f ofd,
    List.nth_error fs n = Some f ->
    step_expfield s f ofd ->
    step_exp s (StrE t fs) (option_map (fun f' => StrE t (update fs n f')) ofd)
  | se_inj_ctx1 : forall s t m e q ot,
    step_typ s t ot ->
    step_exp s (CaseE t m e q) (option_map (fun t' => CaseE t' m e q) ot)
  | se_inj_ctx2 : forall s t m e q oe,
    step_exp s e oe ->
    step_exp s (CaseE t m e q) (option_map (fun e' => CaseE t m e' q) oe)
  | se_inj_ctx3 : forall s t m e qp oqp,
    step_quantprems s qp oqp ->
    step_exp s (CaseE t m e (Some qp)) (option_map (fun qp' => CaseE t m e (Some qp')) oqp)
  | se_lift_ctx : forall s e oe,
    step_exp s e oe ->
    step_exp s (LiftE e) (option_map LiftE oe)
  | se_len_ctx : forall s e oe,
    step_exp s e oe ->
    step_exp s (LenE e) (option_map LenE oe)
  | se_mem_ctx1 : forall s e1 e2 oe,
    step_exp s e1 oe ->
    step_exp s (MemE e1 e2) (option_map (fun e1' => MemE e1' e2) oe)
  | se_mem_ctx2 : forall s e1 e2 oe,
    step_exp s e2 oe ->
    step_exp s (MemE e1 e2) (option_map (fun e2' => MemE e1 e2') oe)
  | se_cat_ctx1 : forall s e1 e2 oe,
    step_exp s e1 oe ->
    step_exp s (CatE e1 e2) (option_map (fun e1' => CatE e1' e2) oe)
  | se_cat_ctx2 : forall s e1 e2 oe,
    step_exp s e2 oe ->
    step_exp s (CatE e1 e2) (option_map (fun e2' => CatE e1 e2') oe)
  | se_sel_ctx : forall s e n oe,
    step_exp s e oe ->
    step_exp s (ProjE e n) (option_map (fun e' => ProjE e' n) oe)
  | se_acc_ctx1 : forall s e p oe,
    step_exp s e oe ->
    step_exp s (AccE e p) (option_map (fun e' => AccE e' p) oe)
  | se_acc_ctx2 : forall s e p op,
    step_path s p op ->
    step_exp s (AccE e p) (option_map (fun p' => AccE e p') op)
  | se_upd_ctx1 : forall s e1 p e2 oe,
    step_exp s e1 oe ->
    step_exp s (UpdE e1 p e2) (option_map (fun e1' => UpdE e1' p e2) oe)
  | se_upd_ctx2 : forall s e1 p e2 op,
    step_path s p op ->
    step_exp s (UpdE e1 p e2) (option_map (fun p' => UpdE e1 p' e2) op)
  | se_upd_ctx3 : forall s e1 p e2 oe,
    step_exp s e2 oe ->
    step_exp s (UpdE e1 p e2) (option_map (fun e2' => UpdE e1 p e2') oe)
  | se_iter_ctx1 : forall s e it eps oe,
    step_exp s e oe ->
    step_exp s (IterE e it eps) (option_map (fun e' => IterE e' it eps) oe)
  | se_iter_ctx2 : forall s e it eps oit,
    step_iter s it oit ->
    step_exp s (IterE e it eps) (option_map (fun it' => IterE e it' eps) oit)
  | se_iter_ctx3 : forall s e it eps n ep oep,
    List.nth_error eps n = Some ep ->
    step_exppull s ep oep ->
    step_exp s (IterE e it eps) (option_map (fun ep' => IterE e it (update eps n ep')) oep)
  | se_call_ctx : forall s x args n a oa,
    List.nth_error args n = Some a ->
    step_arg s a oa ->
    step_exp s (CallE x args) (option_map (fun a' => CallE x (update args n a')) oa)
  | se_cvt_ctx : forall s e nt1 nt2 oe,
    step_exp s e oe ->
    step_exp s (CvtE e nt1 nt2) (option_map (fun e' => CvtE e' nt1 nt2) oe)
  | se_sub_ctx1 : forall s e t1 t2 oe,
    step_exp s e oe ->
    step_exp s (SubE e t1 t2) (option_map (fun e' => SubE e' t1 t2) oe)
  | se_sub_ctx2 : forall s e t1 t2 ot,
    step_typ s t1 ot ->
    step_exp s (SubE e t1 t2) (option_map (fun t1' => SubE e t1' t2) ot)
  | se_sub_ctx3 : forall s e t1 t2 ot,
    step_typ s t2 ot ->
    step_exp s (SubE e t1 t2) (option_map (fun t2' => SubE e t1 t2') ot)
  | se_match_ctx1 : forall s args cs n a oa,
    List.nth_error args n = Some a ->
    step_arg s a oa ->
    step_exp s (MatchE args cs) (option_map (fun a' => MatchE (update args n a') cs) oa)
  | se_match_ctx2 : forall s args cs n c oc,
    List.nth_error cs n = Some c ->
    step_clause s c oc ->
    step_exp s (MatchE args cs) (option_map (fun c' => MatchE args (update cs n c')) oc)
  | se_if_ctx : forall s e1 e2 e3 oe,
    step_exp s e1 oe ->
    step_exp s (IfE e1 e2 e3) (option_map (fun e1' => IfE e1' e2 e3) oe)

with step_expfield : store -> expfield -> option expfield -> Prop :=
  | sef_ctx1 : forall s a e q oe,
    step_exp s e oe ->
    step_expfield s (a, e, q) (option_map (fun e' => (a, e', q)) oe)
  | sef_ctx2 : forall s a e qp oqp,
    step_quantprems s qp oqp ->
    step_expfield s (a, e, Some qp) (option_map (fun qp' => (a, e, Some qp')) oqp)

(* Paths *)

with step_path : store -> il_path -> option il_path -> Prop :=
  | spt_the_ctx : forall s p op,
    step_path s p op ->
    step_path s (TheP p) (option_map TheP op)
  | spt_idx_ctx1 : forall s p e op,
    step_path s p op ->
    step_path s (IdxP p e) (option_map (fun p' => IdxP p' e) op)
  | spt_idx_ctx2 : forall s p e oe,
    step_exp s e oe ->
    step_path s (IdxP p e) (option_map (IdxP p) oe)
  | spt_slice_ctx1 : forall s p e1 e2 op,
    step_path s p op ->
    step_path s (SliceP p e1 e2) (option_map (fun p' => SliceP p' e1 e2) op)
  | spt_slice_ctx2 : forall s p e1 e2 oe,
    step_exp s e1 oe ->
    step_path s (SliceP p e1 e2) (option_map (fun e1' => SliceP p e1' e2) oe)
  | spt_slice_ctx3 : forall s p e1 e2 oe,
    step_exp s e2 oe ->
    step_path s (SliceP p e1 e2) (option_map (fun e2' => SliceP p e1 e2') oe)
  | spt_dot_ctx : forall s p a op,
    step_path s p op ->
    step_path s (DotP p a) (option_map (fun p' => DotP p' a) op)
  | spt_proj_ctx : forall s p m op,
    step_path s p op ->
    step_path s (UncaseP p m) (option_map (fun p' => UncaseP p' m) op)

(* Matches:  S |- {q*} am* ~>_s {q'*} am'*   (None = failure) *)

with step_argmatch : store -> list il_quant -> list argmatch -> il_subst -> option (list il_quant * list argmatch) -> Prop :=
  | sam_plain : forall s qs ams oams,
    step_argmatch_plain s ams oams ->
    step_argmatch s qs ams subst_empty (option_map (fun ams' => (qs, ams')) oams)
  | sam_ctx : forall s q1s qs q2s am1s am am2s sbst qs' ams',
    step_argmatch s qs [am] sbst (Some (qs', ams')) ->
    step_argmatch s (q1s ++ qs ++ q2s) (am1s ++ am :: am2s) sbst
      (Some (q1s ++ qs' ++ List.map (subst_param sbst) q2s, am1s ++ ams' ++ List.map (subst_argmatch sbst) am2s))
  | sam_ctx_fail : forall s q1s qs q2s am1s am am2s sbst,
    step_argmatch s qs [am] sbst None ->
    step_argmatch s (q1s ++ qs ++ q2s) (am1s ++ am :: am2s) sbst None
  | sam_typ : forall s x t,
    step_argmatch s [TypP x] [(TypA t, TypA (VarT x []))] (subst_styp x t) (Some ([], []))
  | sam_exp : forall s x t e,
    step_argmatch s [ExpP x t] [(ExpA e, ExpA (VarE x))] (subst_svar x e) (Some ([], []))
  | sam_fun : forall s x ps t y,
    step_argmatch s [DefP x ps t] [(DefA y, DefA x)] (subst_sfun x y) (Some ([], []))
  | sam_gram : forall s x ps t g,
    step_argmatch s [GramP x ps t] [(GramA g, GramA (VarG x []))] (subst_sgram x g) (Some ([], []))
  | sam_exp_exp : forall s qs e e' sbst oems,
    step_expmatch s qs [(e, e')] sbst oems ->
    step_argmatch s qs [(ExpA e, ExpA e')] sbst
      (option_map (fun r => (r.1, List.map (fun em => (ExpA em.1, ExpA em.2)) r.2)) oems)

with step_argmatch_plain : store -> list argmatch -> option (list argmatch) -> Prop :=
  | samp_ctx1 : forall s a a' oa,
    step_arg s a oa ->
    step_argmatch_plain s [(a, a')] (option_map (fun a'' => [(a'', a')]) oa)
  | samp_ctx2 : forall s a a' oa,
    step_arg s a' oa ->
    step_argmatch_plain s [(a, a')] (option_map (fun a'' => [(a, a'')]) oa)

with step_expmatch : store -> list il_quant -> list expmatch -> il_subst -> option (list il_quant * list expmatch) -> Prop :=
  | sem_plain : forall s qs ems oems,
    step_expmatch_plain s ems oems ->
    step_expmatch s qs ems subst_empty (option_map (fun ems' => (qs, ems')) oems)
  | sem_ctx : forall s q1s qs q2s em1s em em2s sbst qs' ems',
    step_expmatch s qs [em] sbst (Some (qs', ems')) ->
    step_expmatch s (q1s ++ qs ++ q2s) (em1s ++ em :: em2s) sbst
      (Some (q1s ++ qs' ++ List.map (subst_param sbst) q2s, em1s ++ ems' ++ List.map (subst_expmatch sbst) em2s))
  | sem_ctx_fail : forall s q1s qs q2s em1s em em2s sbst,
    step_expmatch s qs [em] sbst None ->
    step_expmatch s (q1s ++ qs ++ q2s) (em1s ++ em :: em2s) sbst None
  (* inner match can only instantiate iteration variables *)
  | sem_iter_quest_none : forall s qs e' eps,
    step_expmatch s qs [(OptE None, IterE e' I_OPT eps)] subst_empty
      (Some (qs, List.map (fun ep => (OptE None, pull_exp ep)) eps))
  | sem_iter_quest_some : forall s qs e e' eps xs',
    size xs' = size eps ->
    List.Forall Fresh_id xs' ->
    List.NoDup xs' ->
    step_expmatch s qs [(OptE (Some e), IterE e' I_OPT eps)] subst_empty
      (Some (list_zipWith (fun x' ep => ExpP x' (pull_typ ep)) xs' eps ++ qs,
             (e, subst_exp (many_svars (list_zipWith (fun ep x' => (pull_id ep, VarE x')) eps xs')) e')
             :: list_zipWith (fun x' ep => (OptE (Some (VarE x')), pull_exp ep)) xs' eps))
  (* xss: one row of fresh names per iteration, one name per pulled variable *)
  | sem_iter_sup : forall s qs es e' y en eps xss,
    size xss = size es ->
    List.Forall (fun xs => size xs = size eps) xss ->
    List.Forall (List.Forall Fresh_id) xss ->
    List.NoDup (List.concat xss) ->
    step_expmatch s qs [(ListE es, IterE e' (I_SUP y en) eps)] subst_empty
      (Some (List.concat (List.map (fun xs => list_zipWith (fun x' ep => ExpP x' (pull_typ ep)) xs eps) xss) ++ qs,
             list_zipWith (fun i xe =>
               (xe.2, subst_exp (append_subst (many_svars (list_zipWith (fun ep x' => (pull_id ep, VarE x')) eps xe.1))
                                              (subst_svar y (NumE (NatE (N.of_nat i))))) e'))
               (iota 0 (size es)) (zip xss es)
             ++ [(NumE (NatE (N.of_nat (size es))), en)]
             ++ list_mapi (fun j ep => (ListE (List.map (fun xs => VarE (nth EmptyString xs j)) xss), pull_exp ep)) eps))

with step_expmatch_plain : store -> list expmatch -> option (list expmatch) -> Prop :=
  | semp_ctx1 : forall s e e' oe,
    step_exp s e oe ->
    step_expmatch_plain s [(e, e')] (option_map (fun e'' => [(e'', e')]) oe)
  | semp_ctx2 : forall s e e' oe,
    step_exp s e' oe ->
    step_expmatch_plain s [(e, e')] (option_map (fun e'' => [(e, e'')]) oe)
  | semp_eq : forall s v,
    step_expmatch_plain s [(val_to_exp v, val_to_exp v)] (Some [])
  | semp_unplus_good : forall s n e,
    ~~ isneg n ->
    step_expmatch_plain s [(NumE n, UnE (NumUnop PlusOp) e)] (Some [(NumE n, e)])
  | semp_unplus_bad : forall s n e,
    isneg n ->
    step_expmatch_plain s [(NumE n, UnE (NumUnop PlusOp) e)] None
  | semp_unminus_good : forall s n n' e,
    isneg n ->
    numun MinusOp n = Some n' ->
    step_expmatch_plain s [(NumE n, UnE (NumUnop MinusOp) e)] (Some [(NumE n', e)])
  | semp_unminus_bad : forall s n e,
    ~~ isneg n ->
    step_expmatch_plain s [(NumE n, UnE (NumUnop MinusOp) e)] None
  | semp_cvt_good : forall s n e nt1 nt2 n',
    num_cvt nt1 n (Some n') ->
    step_expmatch_plain s [(NumE n, CvtE e nt1 nt2)] (Some [(NumE n', e)])
  | semp_cvt_bad : forall s n e nt1 nt2,
    num_cvt nt1 n None ->
    step_expmatch_plain s [(NumE n, CvtE e nt1 nt2)] None
  | semp_tup : forall s es es',
    size es = size es' ->
    step_expmatch_plain s [(TupE es, TupE es')] (Some (zip es es'))
  (* premises on the pattern don't matter *)
  | semp_inj_good : forall s t t' op e e' q,
    step_expmatch_plain s [(CaseE t op e (Some trueqpr), CaseE t' op e' q)] (Some [(e, e')])
  | semp_inj_bad : forall s t t' op op' e e' q,
    op <> op' ->
    step_expmatch_plain s [(CaseE t op e (Some trueqpr), CaseE t' op' e' q)] None
  | semp_opt_good : forall s eo eo',
    same_opt eo eo' ->
    step_expmatch_plain s [(OptE eo, OptE eo')] (Some (zip (opt_to_lst eo) (opt_to_lst eo')))
  | semp_opt_bad : forall s eo eo',
    ~~ same_opt eo eo' ->
    step_expmatch_plain s [(OptE eo, OptE eo')] None
  | semp_list_good : forall s es es',
    size es = size es' ->
    step_expmatch_plain s [(ListE es, ListE es')] (Some (zip es es'))
  | semp_list_bad : forall s es es',
    size es <> size es' ->
    step_expmatch_plain s [(ListE es, ListE es')] None
  | semp_lift_good : forall s es e',
    size es <= 1 ->
    step_expmatch_plain s [(ListE es, LiftE e')] (Some [(OptE (lst_to_opt es), e')])
  | semp_lift_bad : forall s es e',
    1 < size es ->
    step_expmatch_plain s [(ListE es, LiftE e')] None
  | semp_cat_left_good : forall s e1s e2s e1s' e2',
    size e1s = size e1s' ->
    step_expmatch_plain s [(ListE (e1s ++ e2s), CatE (ListE e1s') e2')] (Some [(ListE e1s, ListE e1s'); (ListE e2s, e2')])
  | semp_cat_left_bad : forall s es e1s' e2',
    size es < size e1s' ->
    step_expmatch_plain s [(ListE es, CatE (ListE e1s') e2')] None
  | semp_cat_right_good : forall s e1s e2s e1' e2s',
    size e2s = size e2s' ->
    step_expmatch_plain s [(ListE (e1s ++ e2s), CatE e1' (ListE e2s'))] (Some [(ListE e1s, e1'); (ListE e2s, ListE e2s')])
  | semp_cat_right_bad : forall s es e1' e2s',
    size es < size e2s' ->
    step_expmatch_plain s [(ListE es, CatE e1' (ListE e2s'))] None
  | semp_str : forall s t t' efs efs' es,
    List.Forall2 (fun f' e => List.In (ef_atom f', e, Some trueqpr) efs) efs' es ->
    step_expmatch_plain s [(StrE t efs, StrE t' efs')] (Some (zip es (List.map ef_exp efs')))
  | semp_iter_plus_good : forall s es e' eps,
    1 <= size es ->
    step_expmatch_plain s [(ListE es, IterE e' I_PLUS eps)] (Some [(ListE es, IterE e' I_STAR eps)])
  | semp_iter_plus_bad : forall s e' eps,
    step_expmatch_plain s [(ListE [], IterE e' I_PLUS eps)] None
  | semp_iter_star : forall s es e' eps y,
    Fresh_id y ->
    step_expmatch_plain s [(ListE es, IterE e' I_STAR eps)] (Some [(ListE es, IterE e' (I_SUP y (NumE (NatE (N.of_nat (size es))))) eps)])
  | semp_sub_sub : forall s e t1 t2 e' t1' t2',
    sub_typ (store_to_env s) t1 t1' ->
    step_expmatch_plain s [(SubE e t1 t2, SubE e' t1' t2')] (Some [(SubE e t1 t1', e')])
  (* NOTE: transcribed as in the DSL; this rule looks suspicious there too *)
  | semp_sub_tup : forall s es e' xts1 xts2,
    size es = size xts1 ->
    size xts1 = size xts2 ->
    let s1 := many_svars (list_mapi (fun i ext => (ext.2.1, ProjE ext.1 i)) (zip es xts1)) in
    let s2 := many_svars (list_mapi (fun i ext => (ext.2.1, ProjE ext.1 i)) (zip es xts2)) in
    step_expmatch_plain s [(TupE es, SubE e' (TupT xts1) (TupT xts2))]
      (Some [(TupE (list_zipWith (fun xt1 xt2 => SubE e' (subst_typ s1 xt1.2) (subst_typ s2 xt2.2)) xts1 xts2), e')])

(* Arguments *)

with step_arg : store -> il_arg -> option il_arg -> Prop :=
  | sa_exp_ctx : forall s e oe,
    step_exp s e oe ->
    step_arg s (ExpA e) (option_map ExpA oe)
  | sa_typ_ctx : forall s t ot,
    step_typ s t ot ->
    step_arg s (TypA t) (option_map TypA ot)

(* Parameters *)

with step_param : store -> il_param -> option il_param -> Prop :=
  | spa_exp_ctx : forall s x t ot,
    step_typ s t ot ->
    step_param s (ExpP x t) (option_map (ExpP x) ot)
  | spa_fun_ctx1 : forall s x ps t n p op,
    List.nth_error ps n = Some p ->
    step_param s p op ->
    step_param s (DefP x ps t) (option_map (fun p' => DefP x (update ps n p') t) op)
  | spa_fun_ctx2 : forall s x ps t ot,
    step_typ s t ot ->
    step_param s (DefP x ps t) (option_map (DefP x ps) ot)
  | spa_gram_ctx1 : forall s x ps t n p op,
    List.nth_error ps n = Some p ->
    step_param s p op ->
    step_param s (GramP x ps t) (option_map (fun p' => GramP x (update ps n p') t) op)
  | spa_gram_ctx2 : forall s x ps t ot,
    step_typ s t ot ->
    step_param s (GramP x ps t) (option_map (GramP x ps) ot)

(* Premises:  S |- pr* ~>_s pr'*?  *)

with step_prems : store -> list il_prem -> il_subst -> option (list il_prem) -> Prop :=
  (* Refreshing: [av] is arbitrary, the new names must be fresh (Fresh_id) *)
  | sp_ctx : forall s ps1 p ps2 sbst ps' ps2' s' av,
    step_prems s [p] sbst (Some ps') ->
    refresh_prems av ps2 = (ps2', s') ->
    List.Forall Fresh_id (range_ids s') ->
    step_prems s (ps1 ++ p :: ps2) (append_subst sbst s') (Some (ps1 ++ ps' ++ List.map (subst_prem sbst) ps2'))
  | sp_ctx_fail : forall s ps1 p ps2 sbst,
    step_prems s [p] sbst None ->
    step_prems s (ps1 ++ p :: ps2) sbst None

  (* Non-computational.  The DSL leaves pr'* unsubstituted; we apply s. *)
  | sp_rel : forall s x args e ps t rules qs e' prs sbst prs' s' sa av,
    s_lookup_rel s x = Some (ps, t, rules) ->
    args_for_params args ps = Some sa ->
    List.In (qs, e', prs) (List.map (subst_rule sa) rules) ->
    ok_subst (store_to_env s) sbst qs ->
    refresh_prems av prs = (prs', s') ->
    List.Forall Fresh_id (range_ids s') ->
    step_prems s [RulePr x args e] subst_empty
      (Some (List.map (subst_prem sbst) prs' ++ [IfPr (CmpE (BoolCmpop EqOp) (subst_exp (append_subst sbst s') e') e)]))
  | sp_if_true : forall s,
    step_prems s [IfPr (BoolE true)] subst_empty (Some [])
  | sp_else : forall s,
    step_prems s [ElsePr] subst_empty (Some [IfPr (BoolE true)])
  (* LET-bad of the DSL is omitted: it applies unconditionally, so every LET
     could fail.  A failing pattern instead fails when the MATCH is evaluated. *)
  | sp_let : forall s xts e1 e2,
    let qs := List.map (fun xt => ExpP xt.1 xt.2) xts in
    step_prems s [LetPr qs e1 e2]
      (many_svars (List.map (fun xt => (xt.1, MatchE [ExpA e2] [(qs, [ExpA e1], VarE xt.1, [])])) xts))
      (Some [])
  | sp_not_true : forall s,
    step_prems s [NegPr (IfPr (BoolE true))] subst_empty (Some [IfPr (BoolE false)])
  | sp_not_false : forall s,
    step_prems s [NegPr (IfPr (BoolE false))] subst_empty (Some [IfPr (BoolE true)])

  | sp_iter_quest_none : forall s pr eps eqs,
    List.Forall (fun ep => pull_exp ep = OptE None) eps ->
    step_prems s [IterPr pr I_OPT eps eqs]
      (many_svars (List.map (fun eq => (push_id eq, OptE None)) eqs)) (Some [])
  | sp_iter_quest_some : forall s pr eps eqs es ys,
    eps <> [] ->
    List.Forall2 (fun ep e' => pull_exp ep = OptE (Some e')) eps es ->
    size ys = size (prem_binders pr) ->
    List.Forall Fresh_id ys ->
    List.NoDup ys ->
    let si := many_svars (zip (List.map pull_id eps) es) in
    let r := rename_prem pr ys in
    step_prems s [IterPr pr I_OPT eps eqs]
      (many_svars (List.map (fun eq => (push_id eq, OptE (Some (subst_exp (append_subst si r.2) (push_exp eq))))) eqs))
      (Some [subst_prem si r.1])
  (* All pulled expressions must be OPT literals, as in the DSL *)
  | sp_iter_quest_bad : forall s pr eps eqs oes,
    List.Forall2 (fun ep oe => pull_exp ep = OptE oe) eps oes ->
    List.In None oes ->
    List.Exists (fun oe => oe <> None) oes ->
    step_prems s [IterPr pr I_OPT eps eqs] subst_empty None
  | sp_iter_plus : forall s pr eps eqs ess es0 ess',
    List.Forall2 (fun ep es => pull_exp ep = ListE es) eps ess ->
    ess = es0 :: ess' ->
    1 <= size es0 ->
    step_prems s [IterPr pr I_PLUS eps eqs] subst_empty (Some [IterPr pr I_STAR eps eqs])
  | sp_iter_star : forall s pr eps eqs ess es0 ess' y,
    List.Forall2 (fun ep es => pull_exp ep = ListE es) eps ess ->
    ess = es0 :: ess' ->
    Fresh_id y ->
    step_prems s [IterPr pr I_STAR eps eqs] subst_empty
      (Some [IterPr pr (I_SUP y (NumE (NatE (N.of_nat (size es0))))) eps eqs])
  (* yss: distinct fresh names for the binders of each iteration's copy of pr *)
  | sp_iter_sup_good : forall s pr y n eps eqs ess yss,
    List.Forall2 (fun ep es => pull_exp ep = ListE es) eps ess ->
    List.Forall (fun es => size es = n) ess ->
    size yss = n ->
    List.Forall (fun ys => size ys = size (prem_binders pr)) yss ->
    List.Forall (List.Forall Fresh_id) yss ->
    List.NoDup (List.concat yss) ->
    let si := iter_subst eps ess y (VarE y) in
    let r := fun i => rename_prem pr (nth [] yss i) in
    step_prems s [IterPr pr (I_SUP y (NumE (NatE (N.of_nat n)))) eps eqs]
      (many_svars (List.map (fun eq =>
        (push_id eq, ListE (List.map (fun i => subst_exp (append_subst (si i) (r i).2) (push_exp eq)) (iota 0 n)))) eqs))
      (Some (List.map (fun i => subst_prem (si i) (r i).1) (iota 0 n)))
  | sp_iter_sup_bad : forall s pr y n eps eqs ess,
    List.Forall2 (fun ep es => pull_exp ep = ListE es) eps ess ->
    List.Exists (fun es => size es <> n) ess ->
    step_prems s [IterPr pr (I_SUP y (NumE (NatE (N.of_nat n)))) eps eqs] subst_empty None

  | sp_if_ctx : forall s e oe,
    step_exp s e oe ->
    step_prems s [IfPr e] subst_empty (option_map (fun e' => [IfPr e']) oe)
  | sp_let_ctx1 : forall s qs e1 e2 n q oq,
    List.nth_error qs n = Some q ->
    step_param s q oq ->
    step_prems s [LetPr qs e1 e2] subst_empty (option_map (fun q' => [LetPr (update qs n q') e1 e2]) oq)
  | sp_let_ctx2 : forall s qs e1 e2 oe,
    step_exp s e1 oe ->
    step_prems s [LetPr qs e1 e2] subst_empty (option_map (fun e1' => [LetPr qs e1' e2]) oe)
  | sp_let_ctx3 : forall s qs e1 e2 oe,
    step_exp s e2 oe ->
    step_prems s [LetPr qs e1 e2] subst_empty (option_map (fun e2' => [LetPr qs e1 e2']) oe)
  | sp_not_ctx : forall s p sbst p',
    step_prems s [p] sbst (Some [p']) ->
    step_prems s [NegPr p] subst_empty (Some [NegPr p'])
  | sp_not_ctx_fail : forall s p sbst,
    step_prems s [p] sbst None ->
    step_prems s [NegPr p] subst_empty None
  | sp_iter_ctx1 : forall s pr it eps eqs sbst pr',
    step_prems s [pr] sbst (Some [pr']) ->
    step_prems s [IterPr pr it eps eqs] subst_empty (Some [IterPr pr' it eps (List.map (subst_exppush sbst) eqs)])
  | sp_iter_ctx_fail1 : forall s pr it eps eqs sbst,
    step_prems s [pr] sbst None ->
    step_prems s [IterPr pr it eps eqs] subst_empty None
  | sp_iter_ctx2 : forall s pr it eps eqs oit,
    step_iter s it oit ->
    step_prems s [IterPr pr it eps eqs] subst_empty (option_map (fun it' => [IterPr pr it' eps eqs]) oit)
  | sp_iter_ctx3 : forall s pr it eps eqs n ep oep,
    List.nth_error eps n = Some ep ->
    step_exppull s ep oep ->
    step_prems s [IterPr pr it eps eqs] subst_empty (option_map (fun ep' => [IterPr pr it (update eps n ep') eqs]) oep)
  | sp_iter_ctx4 : forall s pr it eps eqs n eq oeq,
    List.nth_error eqs n = Some eq ->
    step_exppush s eq oeq ->
    step_prems s [IterPr pr it eps eqs] subst_empty (option_map (fun eq' => [IterPr pr it eps (update eqs n eq')]) oeq)

with step_quantprems : store -> quantprems -> option quantprems -> Prop :=
  (* Non-computational *)
  | sqp_guess : forall s qs prs sbst prs' s' av,
    ok_subst (store_to_env s) sbst qs ->
    refresh_prems av prs = (prs', s') ->
    List.Forall Fresh_id (range_ids s') ->
    step_quantprems s (qs, prs) (Some ([], List.map (subst_prem sbst) prs'))
  | sqp_ctx : forall s qs prs sbst ops,
    step_prems s prs sbst ops ->
    step_quantprems s (qs, prs) (option_map (fun prs' => (qs, prs')) ops)

(* Definitions *)

with step_inst : store -> il_inst -> option il_inst -> Prop :=
  | sti_ctx1 : forall s qs args dt n q oq,
    List.nth_error qs n = Some q ->
    step_param s q oq ->
    step_inst s (qs, args, dt) (option_map (fun q' => (update qs n q', args, dt)) oq)
  | sti_ctx2 : forall s qs args dt n a oa,
    List.nth_error args n = Some a ->
    step_arg s a oa ->
    step_inst s (qs, args, dt) (option_map (fun a' => (qs, update args n a', dt)) oa)

with step_clause : store -> il_clause -> option il_clause -> Prop :=
  | stc_ctx1 : forall s qs args e prs n q oq,
    List.nth_error qs n = Some q ->
    step_param s q oq ->
    step_clause s (qs, args, e, prs) (option_map (fun q' => (update qs n q', args, e, prs)) oq)
  | stc_ctx2 : forall s qs args e prs n a oa,
    List.nth_error args n = Some a ->
    step_arg s a oa ->
    step_clause s (qs, args, e, prs) (option_map (fun a' => (qs, update args n a', e, prs)) oa)
  | stc_ctx3 : forall s qs args e prs oe,
    step_exp s e oe ->
    step_clause s (qs, args, e, prs) (option_map (fun e' => (qs, args, e', prs)) oe)
  | stc_ctx4 : forall s qs args e prs sbst ops,
    step_prems s prs sbst ops ->
    step_clause s (qs, args, e, prs) (option_map (fun prs' => (qs, args, subst_exp sbst e, prs')) ops)

(* Type reduction, expansion and equivalence *)

with reduce_typ : store -> il_typ -> option il_typ -> Prop :=
  | rt_refl : forall s t,
    reduce_typ s t (Some t)
  | rt_step : forall s t t' ot,
    step_typ s t (Some t') ->
    reduce_typ s t' ot ->
    reduce_typ s t ot
  | rt_fail : forall s t,
    step_typ s t None ->
    reduce_typ s t None

with expand_typ : store -> il_typ -> il_deftyp -> Prop :=
  (* a nop when t is VAR *)
  | et_plain : forall s t t',
    reduce_typ s t (Some t') ->
    expand_typ s t (AliasT t')
  | et_def : forall s t x dt insts,
    reduce_typ s t (Some (MatchT x [] (([], [], dt) :: insts))) ->
    expand_typ s t dt

(* defined types are nominal *)
with eq_typ : store -> il_typ -> il_typ -> Prop :=
  | eqt_rule : forall s t1 t2 t',
    reduce_typ s t1 (Some t') ->
    reduce_typ s t2 (Some t') ->
    eq_typ s t1 t2

(* Type classification *)

with catable_typ : il_env -> il_typ -> Prop :=
  | ct_iter : forall env t t' it,
    expand_typ (env_to_store env) t (AliasT (IterT t' it)) ->
    catable_typ env t
  | ct_struct : forall env t tfs,
    expand_typ (env_to_store env) t (StructT tfs) ->
    List.Forall (fun tf => catable_typ env (tf_typ tf)) tfs ->
    catable_typ env t

(* Subtyping (TODO in the DSL: ought to be coinductive) *)

with sub_typ : il_env -> il_typ -> il_typ -> Prop :=
  | sbt_tup : forall env x1 t1 x2 t2 xts1 xts2,
    sub_typ env t1 t2 ->
    sub_typ (env @@ single_var x1 t1) (TupT xts1) (subst_typ (subst_svar x2 (VarE x1)) (TupT xts2)) ->
    sub_typ env (TupT ((x1, t1) :: xts1)) (TupT ((x2, t2) :: xts2))
  (* every field (a : t2a - qs prs) of t2 has a field (a : t1a - qs prs) in t1
     with t1a <: t2a; t1as lists those t1a, pointwise with tfs2 *)
  | sbt_struct : forall env t1 t2 tfs1 tfs2 t1as,
    expand_typ (env_to_store env) t1 (StructT tfs1) ->
    expand_typ (env_to_store env) t2 (StructT tfs2) ->
    List.Forall2 (fun tf2 t1a => List.In (tf_atom tf2, tf_quants tf2, t1a, tf_prems tf2) tfs1) tfs2 t1as ->
    List.Forall2 (fun tf2 t1a => sub_typ env t1a (tf_typ tf2)) tfs2 t1as ->
    sub_typ env t1 t2
  (* every case of t1 is a case of t2 (same quantifiers/premises), covariantly *)
  | sbt_variant : forall env t1 t2 tcs1 tcs2 t2as,
    expand_typ (env_to_store env) t1 (VariantT tcs1) ->
    expand_typ (env_to_store env) t2 (VariantT tcs2) ->
    List.Forall2 (fun tc1 t2a => List.In (tf_atom tc1, tf_quants tc1, t2a, tf_prems tc1) tcs2) tcs1 t2as ->
    List.Forall2 (fun tc1 t2a => sub_typ env (tf_typ tc1) t2a) tcs1 t2as ->
    sub_typ env t1 t2
  | sbt_iter : forall env t1 t2 it,
    sub_typ env t1 t2 ->
    sub_typ env (IterT t1 it) (IterT t2 it)
  | sbt_refl : forall env t,
    sub_typ env t t
  | sbt_trans : forall env t1 t2 t',
    sub_typ env t1 t' ->
    sub_typ env t' t2 ->
    sub_typ env t1 t2

with sub_param : il_env -> il_param -> il_param -> il_subst -> Prop :=
  | sbp_exp : forall env x1 t1 x2 t2,
    sub_typ env t1 t2 ->
    sub_param env (ExpP x1 t1) (ExpP x2 t2) (subst_svar x2 (VarE x1))
  | sbp_typ : forall env x1 x2,
    sub_param env (TypP x1) (TypP x2) (subst_styp x2 (VarT x1 []))
  | sbp_fun : forall env x1 ps1 t1 x2 ps2 t2 sbst,
    sub_params env ps2 ps1 sbst ->
    sub_typ (env @@ paramenv ps2) (subst_typ sbst t1) t2 ->
    sub_param env (DefP x1 ps1 t1) (DefP x2 ps2 t2) (subst_sfun x2 x1)
  | sbp_gram : forall env x1 ps1 t1 x2 ps2 t2 sbst,
    sub_params env ps2 ps1 sbst ->
    sub_typ (env @@ paramenv ps2) (subst_typ sbst t1) t2 ->
    sub_param env (GramP x1 ps1 t1) (GramP x2 ps2 t2) (subst_sgram x2 (VarG x1 []))

with sub_params : il_env -> list il_param -> list il_param -> il_subst -> Prop :=
  | sbps_nil : forall env,
    sub_params env [] [] subst_empty
  | sbps_cons : forall env p1 p1s p2 p2s sbst sbst',
    sub_param env p1 p2 sbst ->
    sub_params env p1s (List.map (subst_param sbst) p2s) sbst' ->
    sub_params env (p1 :: p1s) (p2 :: p2s) (append_subst sbst sbst')

(* Types *)

with ok_typ : il_env -> il_typ -> Prop :=
  | okt_bool : forall env, ok_typ env BoolT
  | okt_num : forall env nt, ok_typ env (NumT nt)
  | okt_text : forall env, ok_typ env TextT
  | okt_var : forall env x args ps insts sbst,
    lookup_typ env x = Some (ps, insts) ->
    ok_args env args ps sbst ->
    ok_typ env (VarT x args)
  | okt_tup_nil : forall env, ok_typ env (TupT [])
  | okt_tup_cons : forall env x1 t1 xts,
    ok_typ env t1 ->
    ok_typ (env @@ single_var x1 t1) (TupT xts) ->
    ok_typ env (TupT ((x1, t1) :: xts))
  | okt_iter : forall env t it,
    ok_typ env t ->
    (it = I_STAR) \/ (it = I_OPT) ->
    ok_typ env (IterT t it)
  | okt_match : forall env x args insts ps insts' sbst,
    lookup_typ env x = Some (ps, insts') ->
    ok_args env args ps sbst ->
    List.Forall (fun i => ok_inst env i ps) insts ->
    ok_typ env (MatchT x args insts)

with ok_deftyp : il_env -> il_deftyp -> Prop :=
  | okd_alias : forall env t,
    ok_typ env t ->
    ok_deftyp env (AliasT t)
  | okd_struct : forall env tfs,
    List.Forall (fun tf => ok_typfield env tf) tfs ->
    disjoint (List.map (fun tf => tf_atom tf) tfs) ->
    ok_deftyp env (StructT tfs)
  | okd_variant : forall env tcs,
    List.Forall (fun tc => ok_typcase env tc) tcs ->
    disjoint (List.map (fun tc => tf_atom tc) tcs) ->
    ok_deftyp env (VariantT tcs)

with ok_typfield : il_env -> typfield -> Prop :=
  | oktf_rule : forall env a qs t prs env',
    ok_typ env t ->
    ok_params (env @@ tupenv t) qs ->
    ok_prems (env @@ tupenv t @@ paramenv qs) prs env' ->
    ok_typfield env (a, qs, t, prs)

with ok_typcase : il_env -> typcase -> Prop :=
  | oktc_rule : forall env m qs t prs env',
    ok_typ env t ->
    ok_params (env @@ tupenv t) qs ->
    ok_prems (env @@ tupenv t @@ paramenv qs) prs env' ->
    ok_typcase env (m, qs, t, prs)

(* Iterators *)

with ok_iter : il_env -> iter -> iter -> il_env -> Prop :=
  | oki_quest : forall env, ok_iter env I_OPT I_OPT env_empty
  | oki_star : forall env, ok_iter env I_STAR I_STAR env_empty
  | oki_plus : forall env, ok_iter env I_PLUS I_STAR env_empty
  | oki_sup : forall env x e,
    ok_exp env e (NumT NatT) ->
    ok_iter env (I_SUP x e) I_STAR (single_var x (NumT NatT))

(* Expressions *)

with ok_exp : il_env -> il_exp -> il_typ -> Prop :=
  | oke_bool : forall env b, ok_exp env (BoolE b) BoolT
  | oke_nat : forall env n, ok_exp env (NumE (NatE n)) (NumT NatT)
  | oke_int : forall env i, ok_exp env (NumE (IntE i)) (NumT IntT)
  | oke_rat : forall env q, ok_exp env (NumE (RatE q)) (NumT RatT)
  | oke_real : forall env r, ok_exp env (NumE (RealE r)) (NumT RealT)
  | oke_text : forall env t, ok_exp env (TextE t) TextT
  | oke_var : forall env x t,
    lookup_exp env x = Some t ->
    ok_exp env (VarE x) t
  | oke_un_bool : forall env op e,
    ok_exp env e BoolT ->
    ok_exp env (UnE (BoolUnop op) e) BoolT
  | oke_un_num : forall env op e nt nt',
    ok_exp env e (NumT nt) ->
    ok_numunop op nt nt' ->
    ok_exp env (UnE (NumUnop op) e) (NumT nt')
  | oke_bin_bool : forall env op e1 e2,
    ok_exp env e1 BoolT ->
    ok_exp env e2 BoolT ->
    ok_exp env (BinE (BoolBinop op) e1 e2) BoolT
  | oke_bin_num : forall env op e1 e2 nt1 nt2 nt,
    ok_exp env e1 (NumT nt1) ->
    ok_exp env e2 (NumT nt2) ->
    ok_numbinop op nt1 nt2 nt ->
    ok_exp env (BinE (NumBinop op) e1 e2) (NumT nt)
  | oke_cmp_poly : forall env op e1 e2 t,
    ok_exp env e1 t ->
    ok_exp env e2 t ->
    ok_exp env (CmpE (BoolCmpop op) e1 e2) BoolT
  | oke_cmp_num : forall env op e1 e2 nt,
    ok_exp env e1 (NumT nt) ->
    ok_exp env e2 (NumT nt) ->
    ok_exp env (CmpE (NumCmpop op) e1 e2) BoolT
  | oke_tup_nil : forall env, ok_exp env (TupE []) (TupT [])
  | oke_tup_cons : forall env e1 es x1 t1 xts,
    ok_exp env e1 t1 ->
    ok_exp env (TupE es) (subst_typ (subst_svar x1 e1) (TupT xts)) ->
    ok_exp env (TupE (e1 :: es)) (TupT ((x1, t1) :: xts))
  | oke_opt : forall env eo t,
    option_forall (fun e => ok_exp env e t) eo ->
    ok_typ env t ->
    ok_exp env (OptE eo) (IterT t I_OPT)
  | oke_list : forall env es t,
    List.Forall (fun e => ok_exp env e t) es ->
    ok_typ env t ->
    ok_exp env (ListE es) (IterT t I_STAR)
  | oke_lift : forall env e t,
    ok_exp env e (IterT t I_OPT) ->
    ok_exp env (LiftE e) (IterT t I_STAR)
  (* premises need not hold *)
  | oke_inj : forall env t op e qpr tcs qs' t' prs',
    ok_typ env t ->
    expand_typ (env_to_store env) t (VariantT tcs) ->
    List.In (op, qs', t', prs') tcs ->
    ok_exp env e t' ->
    option_forall (fun qp => ok_quantprems env qp) qpr ->
    ok_exp env (CaseE t op e qpr) t
  (* premises need not hold *)
  | oke_str : forall env t fs tfs,
    ok_typ env t ->
    expand_typ (env_to_store env) t (StructT tfs) ->
    List.Forall2 (fun tf f => tf_atom tf = ef_atom f) tfs fs ->
    List.Forall2 (fun tf f => ok_exp env (ef_exp f) (tf_typ tf)) tfs fs ->
    List.Forall (fun f => option_forall (fun qp => ok_quantprems env qp) (ef_qpr f)) fs ->
    ok_exp env (StrE t fs) t
  | oke_sel : forall env e n xts xn tn,
    ok_exp env e (TupT xts) ->
    List.nth_error xts n = Some (xn, tn) ->
    ok_exp env (ProjE e n)
      (subst_typ (many_svars (List.map (fun i => ((nth (EmptyString, BoolT) xts i).1, ProjE e i)) (iota 0 n))) tn)
  | oke_len : forall env e t,
    ok_exp env e (IterT t I_STAR) ->
    ok_exp env (LenE e) (NumT NatT)
  | oke_mem : forall env e1 e2 t1,
    ok_exp env e1 t1 ->
    ok_exp env e2 (IterT t1 I_STAR) ->
    ok_exp env (MemE e1 e2) BoolT
  | oke_cat : forall env e1 e2 t,
    ok_exp env e1 t ->
    ok_exp env e2 t ->
    catable_typ env t ->
    ok_exp env (CatE e1 e2) t
  | oke_acc : forall env e p t t',
    ok_exp env e t ->
    ok_path env p t t' ->
    ok_exp env (AccE e p) t'
  | oke_upd : forall env e1 p e2 t1 t2,
    ok_exp env e1 t1 ->
    ok_exp env e2 t2 ->
    ok_path env p t1 t2 ->
    ok_exp env (UpdE e1 p e2) t1
  | oke_ext : forall env e1 p e2 t1 t2,
    ok_exp env e1 t1 ->
    ok_exp env e2 (IterT t2 I_STAR) ->
    ok_path env p t1 (IterT t2 I_STAR) ->
    ok_exp env (ExtE e1 p e2) t1
  | oke_call : forall env x args ps sbst t cs,
    lookup_fun env x = Some (ps, t, cs) ->
    ok_args env args ps sbst ->
    ok_exp env (CallE x args) (subst_typ sbst t)
  | oke_iter : forall env env' e it it' eps t,
    ok_iter env it it' env' ->
    List.Forall (fun ep => ok_typ env (pull_typ ep)) eps ->
    List.Forall (fun ep => ok_exp env (pull_exp ep) (IterT (pull_typ ep) it')) eps ->
    ok_exp (env @@ many_vars (List.map (fun ep => (pull_id ep, pull_typ ep)) eps) @@ env') e t ->
    ok_typ env t ->
    ok_exp env (IterE e it eps) (IterT t it')
  | oke_cvt : forall env e nt1 nt2,
    ok_exp env e (NumT nt1) ->
    ok_exp env (CvtE e nt1 nt2) (NumT nt2)
  | oke_sub : forall env e t1 t2,
    ok_exp env e t1 ->
    sub_typ env t1 t2 ->
    ok_exp env (SubE e t1 t2) t2
  | oke_match : forall env args ps cs t sbst,
    ok_args env args ps sbst ->
    ok_params env ps ->
    List.Forall (fun c => ok_clause (env @@ paramenv ps) c ps t) cs ->
    ok_exp env (MatchE args cs) t
  (* IfE (Rocq extension) *)
  | oke_if : forall env e1 e2 e3 t,
    ok_exp env e1 BoolT ->
    ok_exp env e2 t ->
    ok_exp env e3 t ->
    ok_exp env (IfE e1 e2 e3) t
  | oke_conv : forall env e t t',
    ok_exp env e t' ->
    eq_typ (env_to_store env) t t' ->
    ok_exp env e t

(* Paths *)

with ok_path : il_env -> il_path -> il_typ -> il_typ -> Prop :=
  | okpt_root : forall env t,
    ok_typ env t ->
    ok_path env RootP t t
  | okpt_the : forall env p t t',
    ok_path env p t (IterT t' I_OPT) ->
    ok_path env (TheP p) t t'
  | okpt_idx : forall env p e t t',
    ok_path env p t (IterT t' I_STAR) ->
    ok_exp env e (NumT NatT) ->
    ok_path env (IdxP p e) t t'
  | okpt_slice : forall env p e1 e2 t t',
    ok_path env p t (IterT t' I_STAR) ->
    ok_exp env e1 (NumT NatT) ->
    ok_exp env e2 (NumT NatT) ->
    ok_path env (SliceP p e1 e2) t t'
  (* premises cannot be used *)
  | okpt_dot : forall env p a x args t t' tfs qs prs,
    ok_path env p t (VarT x args) ->
    expand_typ (env_to_store env) (VarT x args) (StructT tfs) ->
    List.In (a, qs, t', prs) tfs ->
    ok_path env (DotP p a) t t'
  | okpt_proj : forall env p m t t' x args qs prs tcs,
    ok_path env p t (VarT x args) ->
    expand_typ (env_to_store env) (VarT x args) (VariantT tcs) ->
    List.In (m, qs, t', prs) tcs ->
    ok_path env (UncaseP p m) t t'
  | okpt_conv : forall env p t t' t'',
    ok_path env p t'' t' ->
    eq_typ (env_to_store env) t t'' ->
    ok_path env p t t'

(* Grammars *)

with ok_sym : il_env -> il_sym -> il_typ -> Prop :=
  | oks_var : forall env x args ps t prods sbst,
    lookup_gram env x = Some (ps, t, prods) ->
    ok_args env args ps sbst ->
    ok_sym env (VarG x args) (subst_typ sbst t)
  | oks_num : forall env n,
    ok_sym env (NumG n) (NumT NatT)
  | oks_text : forall env t,
    ok_sym env (TextG t) TextT
  | oks_seq : forall env gs ts,
    List.Forall2 (fun g t => ok_sym env g t) gs ts ->
    ok_sym env (SeqG gs) (TupT [])
  | oks_alt : forall env gs ts,
    List.Forall2 (fun g t => ok_sym env g t) gs ts ->
    ok_sym env (AltG gs) (TupT [])
  | oks_range : forall env g1 g2,
    ok_sym env g1 (NumT NatT) ->
    ok_sym env g2 (NumT NatT) ->
    ok_sym env (RangeG g1 g2) (NumT NatT)
  | oks_iter : forall env env' g it it' eps t,
    ok_iter env it it' env' ->
    List.Forall (fun ep => ok_typ env (pull_typ ep)) eps ->
    List.Forall (fun ep => ok_exp env (pull_exp ep) (IterT (pull_typ ep) it')) eps ->
    ok_sym (env @@ many_vars (List.map (fun ep => (pull_id ep, pull_typ ep)) eps) @@ env') g t ->
    ok_typ env t ->
    ok_sym env (IterG g it eps) (IterT t it')
  | oks_attr : forall env e g t,
    ok_sym env g t ->
    ok_exp env e t ->
    ok_sym env (AttrG e g) t
  | oks_conv : forall env g t t',
    ok_sym env g t' ->
    eq_typ (env_to_store env) t t' ->
    ok_sym env g t

(* Premises:  E |- pr : OK -| E'  (E' are the variables pr binds) *)

with ok_prem : il_env -> il_prem -> il_env -> Prop :=
  | okpr_rel : forall env x args e ps t rules sbst,
    lookup_rel env x = Some (ps, t, rules) ->
    ok_args env args ps sbst ->
    ok_exp env e (subst_typ sbst t) ->
    ok_prem env (RulePr x args e) env_empty
  | okpr_if : forall env e,
    ok_exp env e BoolT ->
    ok_prem env (IfPr e) env_empty
  | okpr_else : forall env,
    ok_prem env ElsePr env_empty
  | okpr_not : forall env p,
    ok_prem env p env_empty ->
    ok_prem env (NegPr p) env_empty
  | okpr_let : forall env qs e1 e2 t,
    ok_exp (env @@ paramenv qs) e1 t ->
    ok_exp env e2 t ->
    ok_prem env (LetPr qs e1 e2) (paramenv qs)
  (* the pushed expressions are typed in the body's scope: the iteration
     variables plus what pr binds (DSL reuses the name E' for both) *)
  | okpr_iter : forall env pr it it' env1 env2 eps eqs t2s,
    ok_iter env it it' env1 ->
    List.Forall (fun ep => ok_typ env (pull_typ ep)) eps ->
    List.Forall (fun ep => ok_exp env (pull_exp ep) (IterT (pull_typ ep) it')) eps ->
    ok_prem (env @@ many_vars (List.map (fun ep => (pull_id ep, pull_typ ep)) eps) @@ env1) pr env2 ->
    List.Forall (fun eq => ok_typ env (push_typ eq)) eqs ->
    List.Forall2 (fun eq t2 => eq_typ (env_to_store env) (push_typ eq) (IterT t2 it')) eqs t2s ->
    List.Forall2 (fun eq t2 =>
      ok_exp (env @@ many_vars (List.map (fun ep => (pull_id ep, pull_typ ep)) eps) @@ env1 @@ env2) (push_exp eq) t2) eqs t2s ->
    ok_prem env (IterPr pr it eps eqs) (many_vars (List.map (fun eq => (push_id eq, push_typ eq)) eqs))

with ok_prems : il_env -> list il_prem -> il_env -> Prop :=
  | okprs_nil : forall env,
    ok_prems env [] env_empty
  | okprs_cons : forall env p ps env1 env2,
    ok_prem env p env1 ->
    ok_prems (env @@ env1) ps env2 ->
    ok_prems env (p :: ps) (env1 @@ env2)

with ok_quantprems : il_env -> quantprems -> Prop :=
  | okqp_rule : forall env qs prs env',
    ok_params env qs ->
    ok_prems (env @@ paramenv qs) prs env' ->
    ok_quantprems env (qs, prs)

(* Parameters and arguments *)

with ok_param : il_env -> il_param -> Prop :=
  | okpa_typ : forall env x,
    ok_param env (TypP x)
  | okpa_exp : forall env x t,
    ok_typ env t ->
    ok_param env (ExpP x t)
  | okpa_fun : forall env x ps t,
    ok_params env ps ->
    ok_typ (env @@ paramenv ps) t ->
    ok_param env (DefP x ps t)
  | okpa_gram : forall env x ps t,
    ok_params env ps ->
    ok_typ (env @@ paramenv ps) t ->
    ok_param env (GramP x ps t)

with ok_params : il_env -> list il_param -> Prop :=
  | okpas_nil : forall env,
    ok_params env []
  | okpas_cons : forall env p1 ps,
    ok_param env p1 ->
    ok_params (env @@ paramenv [p1]) ps ->
    ok_params env (p1 :: ps)

with ok_arg : il_env -> il_arg -> il_param -> il_subst -> Prop :=
  | oka_typ : forall env t x,
    ok_typ env t ->
    ok_arg env (TypA t) (TypP x) (subst_styp x t)
  | oka_exp : forall env e x t,
    ok_exp env e t ->
    ok_arg env (ExpA e) (ExpP x t) (subst_svar x e)
  | oka_fun : forall env y x ps rt ps' rt' cs sbst,
    lookup_fun env y = Some (ps', rt', cs) ->
    sub_params env ps ps' sbst ->
    sub_typ env (subst_typ sbst rt') rt ->
    ok_arg env (DefA y) (DefP x ps rt) (subst_sfun x y)
  | oka_gram_ground : forall env g x t,
    ok_sym env g t ->
    ok_arg env (GramA g) (GramP x [] t) (subst_sgram x g)
  | oka_gram_higher : forall env y x ps t ps' t' prods sbst,
    lookup_gram env y = Some (ps', t', prods) ->
    sub_params env ps ps' sbst ->
    sub_typ env (subst_typ sbst t') t ->
    ok_arg env (GramA (VarG y [])) (GramP x ps t) (subst_sgram x (VarG y []))

with ok_args : il_env -> list il_arg -> list il_param -> il_subst -> Prop :=
  | okas_nil : forall env,
    ok_args env [] [] subst_empty
  (* the tail's parameters are instantiated with the head's substitution
     (the DSL uses the tail's own result, which is circular) *)
  | okas_cons : forall env a1 p1 sbst1 args ps sbst,
    ok_arg env a1 p1 sbst1 ->
    ok_args env args (List.map (subst_param sbst1) ps) sbst ->
    ok_args env (a1 :: args) (p1 :: ps) (append_subst sbst1 sbst)

with ok_subst : il_env -> il_subst -> list il_quant -> Prop :=
  | oksub_rule : forall env sbst qs sbsts,
    List.Forall2 (fun q sbst' => ok_arg env (subst_arg sbst (param_to_arg q)) (subst_param sbst q) sbst') qs sbsts ->
    ok_subst env sbst qs

(* Definitions used inside expressions and types *)

with ok_inst : il_env -> il_inst -> list il_param -> Prop :=
  | okin_rule : forall env qs args dt ps sbst,
    ok_params env qs ->
    ok_args (env @@ paramenv qs) args ps sbst ->
    ok_deftyp (env @@ paramenv qs) dt ->
    ok_inst env (qs, args, dt) ps

with ok_clause : il_env -> il_clause -> list il_param -> il_typ -> Prop :=
  | okc_rule : forall env qs args e prs ps t sbst env',
    ok_params env qs ->
    ok_args (env @@ paramenv qs) args ps sbst ->
    ok_prems (env @@ paramenv qs) prs env' ->
    ok_exp (env @@ paramenv qs @@ env') e t ->
    ok_clause env (qs, args, e, prs) ps t
.

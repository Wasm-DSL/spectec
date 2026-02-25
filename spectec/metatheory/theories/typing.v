From Stdlib Require Import List String Reals.
From mathcomp Require Import all_ssreflect all_algebra.
From MetaSpectec Require Import syntax env reduction subst utils.
Import ListNotations.
Open Scope env_scope.

Inductive composable_typ : il_env -> il_typ -> Prop :=
  | ct_iter : forall env t t' it,
    expand_typ (env_to_store env) t (AliasT (IterT t' it)) ->
    composable_typ env t
  | ct_struct : forall env t typfields,
    expand_typ (env_to_store env) t (StructT typfields) ->
    List.Forall (fun p => composable_typ env (snd (fst p))) typfields ->
    composable_typ env t
.

Inductive sub_numtyp : numtyp -> numtyp -> Prop :=
  | sn_nat : sub_numtyp NatT IntT
  | sn_int : sub_numtyp IntT RatT
  | sn_rat : sub_numtyp RatT RealT
  | sn_rfl : forall nt, sub_numtyp nt nt
  | sn_trans : forall nt1 nt2 nt,
    sub_numtyp nt1 nt ->
    sub_numtyp nt nt2 ->
    sub_numtyp nt1 nt2
.

Inductive sub_typ : il_env -> il_typ -> il_typ -> Prop :=
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
.

Inductive sub_param : il_env -> il_param -> il_param -> il_subst -> Prop :=
  | sp_exp : forall env x1 t1 x2 t2,
    sub_typ env t1 t2 ->
    sub_param env (ExpP x1 t1) (ExpP x2 t2) (subst_svar x2 (VarE x1))
  | sp_typ : forall env x1 x2,
    sub_param env (TypP x1) (TypP x2) (subst_styp x2 (VarT x1 []))
  | sp_fun : forall env x1 ps1 t1 x2 ps2 t2 sbst,
    let penv2 := paramenv ps2 in
    sub_params env ps2 ps1 sbst ->
    sub_typ (env @@ penv2) (subst_typ sbst t1) t2 ->
    sub_param env (DefP x1 ps1 t1) (DefP x2 ps2 t2) (subst_sfun x2 x1)

with

sub_params : il_env -> list il_param -> list il_param -> il_subst -> Prop :=
  | sps_emp : forall env, sub_params env [] [] subst_empty
  | sps_cons : forall env p1 p1s p2 p2s sbst sbst',
    sub_param env p1 p2 sbst ->
    sub_params env p1s (List.map (subst_param sbst) p2s) sbst' ->
    sub_params env (p1 :: p1s) (p2 :: p2s) (append_subst sbst sbst')
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

Inductive ok_exp: il_env -> il_exp -> il_typ -> Prop :=
  | oke_bool : forall env b, ok_exp env (BoolE b) BoolT
  | oke_nat : forall env n, ok_exp env (NumE (NatE n)) (NumT NatT)
  | oke_int : forall env i, ok_exp env (NumE (IntE i)) (NumT IntT)
  | oke_rat : forall env q, ok_exp env (NumE (RatE q)) (NumT RatT)
  | oke_real : forall env r, ok_exp env (NumE (RealE r)) (NumT RealT)
  | oke_text : forall env t, ok_exp env (TextE t) TextT
  | oke_unop_bool : forall env bop e,
    ok_exp env e BoolT ->
    ok_exp env (UnE (BoolUnop bop) e) BoolT
  | oke_unop_num : forall env numop e nt nt',
    ok_exp env e (NumT nt) ->
    ok_numunop numop nt nt' ->
    ok_exp env (UnE (NumUnop numop) e) (NumT nt')
  | oke_binop_bool : forall env bop e1 e2,
    ok_exp env e1 BoolT ->
    ok_exp env e2 BoolT ->
    ok_exp env (BinE (BoolBinop bop) e1 e2) BoolT
  | oke_binop_num : forall env numop e1 e2 nt1 nt2 nt,
    ok_exp env e1 (NumT nt1) ->
    ok_exp env e2 (NumT nt2) ->
    ok_numbinop numop nt1 nt2 nt ->
    ok_exp env (BinE (NumBinop numop) e1 e2) (NumT nt)
  | oke_cmp_bool : forall env bop e1 e2 t,
    ok_exp env e1 t ->
    ok_exp env e2 t ->
    ok_exp env (CmpE (BoolCmpop bop) e1 e2) BoolT
  | oke_cmp_num : forall env numop e1 e2 nt,
    ok_exp env e1 (NumT nt) ->
    ok_exp env e2 (NumT nt) ->
    ok_exp env (CmpE (NumCmpop numop) e1 e2) BoolT
  | oke_tup_eps : forall env, ok_exp env (TupE []) (TupT [])
  | oke_tup_cons : forall env e1 es x1 t1 tups,
    let sbst := (subst_svar x1 e1) in
    ok_exp env e1 t1 ->
    ok_exp env (TupE es) (subst_typ sbst (TupT tups)) ->
    ok_exp env (TupE (e1 :: es)) (TupT ((x1, t1) :: tups))
  | oke_opt : forall env e_opt t,
    option_forall (fun e => ok_exp env e t) e_opt ->
    ok_exp env (OptE e_opt) (IterT t I_OPT)
  | oke_list : forall env es t,
    List.Forall (fun e => ok_exp env e t) es ->
    ok_exp env (ListE es) (IterT t I_STAR)
  | oke_lift : forall env e t,
    ok_exp env e (IterT t I_OPT) ->
    ok_exp env (LiftE e) (IterT t I_STAR)
  | oke_case : forall env m e x ags tcs t qs ps,
    expand_typ (env_to_store env) (VarT x ags) (VariantT tcs) ->
    List.In (m, qs, t, ps) tcs ->
    ok_exp env e t ->
    ok_exp env (CaseE m e) (VarT x ags)
  | oke_str : forall env a e x ags tfs fs t qs ps,
    expand_typ (env_to_store env) (VarT x ags) (StructT tfs) ->
    size tfs = size fs ->
    List.In (a, qs, t, ps) tfs ->
    List.In (a, e) fs ->
    ok_exp env e t ->
    ok_exp env (StrE fs) (VarT x ags)
  (* TODO rule for ProjE *)
  | oke_len : forall env e t,
    ok_exp env e (IterT t I_STAR) ->
    ok_exp env (LenE e) (NumT NatT)
  | oke_mem : forall env e1 e2 t1,
    ok_exp env e1 t1 ->
    ok_exp env e2 (IterT t1 I_STAR) ->
    ok_exp env (MemE e1 e2) BoolT
  | oke_cat : forall env e1 e2 t,
    ok_exp env e1 (IterT t I_STAR) ->
    ok_exp env e2 (IterT t I_STAR) ->
    ok_exp env (CatE e1 e2) (IterT t I_STAR)
  | oke_comp : forall env e1 e2 t,
    ok_exp env e1 t ->
    ok_exp env e2 t ->
    composable_typ env t ->
    ok_exp env (CompE e1 e2) t
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
  | oke_call : forall env x ags ps sbst rt clauses,
    StringMap.find x (DEFS env) = Some (ps, rt, clauses) ->
    ok_args env ags ps sbst ->
    ok_exp env (CallE x ags) (subst_typ sbst rt)
  (* TODO iterE valid *)
  | oke_cvt : forall env e nt1 nt2,
    ok_exp env e (NumT nt1) ->
    ok_exp env (CvtE e nt1 nt2) (NumT nt2)
  | oke_sub : forall env e t1 t2, 
    ok_exp env e t1 ->
    sub_typ env t1 t2 ->
    ok_exp env (SubE e t1 t2) t2
  | ok_exp_conv : forall env e t t',
    ok_exp env e t' ->
    eq_typ (env_to_store env) t t' ->
    ok_exp env e t

with

ok_path : il_env -> il_path -> il_typ -> il_typ -> Prop :=
  | okp_root : forall env t,
    ok_typ env t ->
    ok_path env RootP t t
  | okp_the : forall env p t t',
    ok_path env p t (IterT t' I_OPT) ->
    ok_path env (TheP p) t t'
  | okp_idx : forall env p e t t',
    ok_path env p t (IterT t' I_STAR) ->
    ok_exp env e (NumT NatT) ->
    ok_path env (IdxP p e) t t'
  | okp_slice : forall env p e1 e2 t t',
    ok_path env p t (IterT t' I_STAR) ->
    ok_exp env e1 (NumT NatT) ->
    ok_exp env e2 (NumT NatT) ->
    ok_path env (SliceP p e1 e2) t t'
  | okp_dot : forall env p a x ags t t' tfs qs prems,
    ok_path env p t (VarT x ags) -> 
    expand_typ (env_to_store env) (VarT x ags) (StructT tfs) ->
    List.In (a, qs, t', prems) tfs ->
    ok_path env (DotP p a) t t'
  | okp_uncase : forall env p m t t' x ags qs prems tcs,
    ok_path env p t (VarT x ags) ->
    expand_typ (env_to_store env) (VarT x ags) (VariantT tcs) ->
    List.In (m, qs, t', prems) tcs ->
    ok_path env (UncaseP p m) t t'
  | okp_conv : forall env p t t' t'',
    ok_path env p t'' t' ->
    eq_typ (env_to_store env) t t'' ->
    ok_path env p t t'

with

ok_typ : il_env -> il_typ -> Prop :=
  | okt_bool : forall env, ok_typ env BoolT
  | okt_num : forall env nt, ok_typ env (NumT nt)
  | okt_text : forall env, ok_typ env TextT
  | okt_tupemp : forall env, ok_typ env (TupT [])
  | okt_tup : forall env x1 t1 tups,
    let env' := single_var x1 t1 in
    ok_typ env t1 ->
    ok_typ (env @@ env') (TupT tups) ->
    ok_typ env (TupT ((x1, t1) :: tups))
  | okt_iter : forall env t it,
    ok_typ env t ->
    (it = I_STAR) \/ (it = I_OPT) ->
    ok_typ env (IterT t it)
  | okt_var : forall env x ags ps insts sbst,
    (StringMap.find x (TYPS env) = Some (ps, insts)) -> 
    ok_args env ags ps sbst ->
    ok_typ env (VarT x ags)

with

ok_iter : il_env -> iter -> iter -> il_env -> Prop :=
  | oki_quest : forall env, ok_iter env I_OPT I_OPT env_empty 
  | oki_star : forall env, ok_iter env I_STAR I_STAR env_empty
  | oki_plus : forall env, ok_iter env I_PLUS I_STAR env_empty
  | oki_sup_none : forall env e,
    ok_exp env e (NumT NatT) ->
    ok_iter env (I_SUP None e) I_STAR env_empty
  | oki_sup_some : forall env e x,
    ok_exp env e (NumT NatT) ->
    ok_iter env (I_SUP (Some x) e) I_STAR (single_var x (NumT NatT))

with

ok_prem : il_env -> il_prem -> Prop :=
  | okp_rule : forall env x ags sbst e ps t rules,
    StringMap.find x (RELS env) = Some (ps, t, rules) ->
    ok_args env ags ps sbst ->
    ok_exp env e (subst_typ sbst t) ->
    ok_prem env (RulePr x ags e)
  | okp_if : forall env e,
    ok_exp env e BoolT ->
    ok_prem env (IfPr e)
  | okp_else : forall env, ok_prem env ElsePr
  (* TODO think about let semantics *)
  | okp_let : forall env e1 e2 t,
    ok_exp env e1 t ->
    ok_exp env e2 t ->
    ok_prem env (LetPr e1 e2)
  (* | okp_iter : forall env pr it it' env'' expps,
    let env' := single_var x  
    ok_iter env it it' env' -> *)
  | okp_neg : forall env p,
    ok_prem env p ->
    ok_prem env (NegPr p)

with

ok_arg : il_env -> il_arg -> il_param -> il_subst -> Prop :=
  | oka_exp : forall env e x t,
    ok_exp env e t ->
    ok_arg env (ExpA e) (ExpP x t) (subst_svar x e)
  | oka_typ : forall env t x,
    ok_typ env t ->
    ok_arg env (TypA t) (TypP x) (subst_styp x t)
  (* TODO fun arg *)
  | oka_fun : forall env y x ps rt ps' rt' clauses sbst,
    StringMap.find y (DEFS env) = Some (ps', rt', clauses) ->
    sub_params env ps ps' sbst ->
    sub_typ env (subst_typ sbst rt') rt ->
    ok_arg env (DefA y) (DefP x ps rt) (subst_sfun x y)

with

ok_args : il_env -> list il_arg -> list il_param -> il_subst -> Prop :=
  | okas_emp : forall env, ok_args env [] [] subst_empty
  | okas_cons : forall env a1 p1 sbst sbst1 ags ps,
    ok_arg env a1 p1 sbst1 ->
    ok_args env ags (List.map (subst_param sbst) ps) sbst ->
    ok_args env (a1 :: ags) (p1 :: ps) (append_subst sbst1 sbst)

with

ok_param : il_env -> il_param -> Prop :=
  | okpa_exp : forall env x t,
    ok_typ env t ->
    ok_param env (ExpP x t) 
  | okpa_typ : forall env x, ok_param env (TypP x)
  | okpa_fun : forall env x ps t, 
    let penv := paramenv ps in
    ok_params env ps ->
    ok_typ (env @@ penv) t ->
    ok_param env (DefP x ps t)

with

ok_params : il_env -> list il_param -> Prop :=
  | okpas_emp : forall env, ok_params env []
  | okpas_cons : forall env p1 ps,
    ok_param env p1 ->
    ok_params (env @@ (paramenv [p1])) ps
.

Inductive ok_typfield : il_env -> typfield -> Prop :=
  | oktypfield : forall env a t qs prems,
    let tenv := tupenv t in
    let qsenv := paramenv qs in
    ok_typ env t ->
    ok_params (env @@ tenv) qs ->
    List.Forall (fun p => ok_prem (env @@ tenv @@ qsenv) p) prems ->
    ok_typfield env (a, qs, t, prems)
.

Inductive ok_typcase : il_env -> typcase -> Prop :=
  | oktypcase : forall env m t qs prems,
    let tenv := tupenv t in
    let qsenv := paramenv qs in
    ok_typ env t ->
    ok_params (env @@ tenv) qs ->
    List.Forall (fun p => ok_prem (env @@ tenv @@ qsenv) p) prems ->
    ok_typcase env (m, qs, t, prems)
.

Inductive ok_deftyp : il_env -> il_deftyp -> Prop :=
  | okd_alias : forall env t,
    ok_typ env t ->
    ok_deftyp env (AliasT t)
  | okd_struct : forall env tfs,
    let atoms := List.map (fun '(a, qs, t, prems) => a) tfs in
    List.Forall (fun tf => ok_typfield env tf) tfs ->
    disjoint atoms ->
    ok_deftyp env (StructT tfs)
  | okd_variant : forall env tcs,
    let mixops := List.map (fun '(m, qs, t, prems) => m) tcs in
    List.Forall (fun tc => ok_typcase env tc) tcs ->
    disjoint mixops ->
    ok_deftyp env (VariantT tcs)
.
 

Inductive ok_inst : il_env -> il_inst -> list il_param -> Prop :=
  | oki_inst : forall env qs ags dt ps sbst,
    ok_params env qs ->
    ok_args (env @@ (paramenv qs)) ags ps sbst ->
    ok_deftyp (env @@ (paramenv qs)) dt ->
    ok_inst env (qs, ags, dt) ps
.

Inductive ok_rule : il_env -> il_rule -> il_typ -> Prop :=
  | okr_rule : forall env qs e prems t,
    ok_params env qs ->
    ok_exp (env @@ (paramenv qs)) e t ->
    List.Forall (fun p => ok_prem (env @@ (paramenv qs)) p) prems ->
    ok_rule env (qs, e, prems) t
.

Inductive ok_clause : il_env -> il_clause -> list il_param -> il_typ -> Prop :=
  | okc_clause : forall env qs ags e prems ps t sbst,
    let qsenv := paramenv qs in
    ok_params env qs ->
    ok_args (env @@ qsenv) ags ps sbst ->
    ok_exp (env @@ qsenv) e t ->
    List.Forall (fun p => ok_prem (env @@ qsenv) p) prems ->
    ok_clause env (qs, ags, e, prems) ps t
.

Inductive ok_def : il_env -> il_def -> il_env -> Prop :=
  | okd_typ : forall env x ps insts,
    let env' := single_envtyp x ps insts in
    ok_params env ps ->
    List.Forall (fun inst => ok_inst env inst ps) insts ->
    ok_def env (TypD x ps insts) (env @@ env')
  | okd_rel : forall env x ps t rules,
    let env' := single_rel x ps t rules in
    let penv := paramenv ps in
    ok_params env ps ->
    List.Forall (fun rule => ok_rule (env @@ penv) rule t) rules ->
    ok_def env (RelD x ps t rules) (env @@ env')
  | okd_fun : forall env x ps t clauses,
    let env' := single_def x ps t clauses in
    let penv := paramenv ps in
    ok_params env ps ->
    List.Forall (fun clause => ok_clause (env @@ penv) clause ps t) clauses ->
    ok_def env (DecD x ps t clauses) (env @@ env')
  (* TODO recs doesn't make much sense *)
  | okd_rec : forall env env' defs,
    ok_defs (env @@ env') defs env' ->
    ok_def env (RecD defs) env'
  
with

ok_defs : il_env -> list il_def -> il_env -> Prop :=
  | okdefs_emp : forall env, ok_defs env [] env_empty
  | okdefs_cons : forall env d1 defs env' env'', 
    ok_def env d1 env' ->
    ok_defs env' defs env'' ->
    ok_defs env (d1 :: defs) env''
.

Inductive ok_script : script -> Prop :=
  | okscript : forall defs env,
    ok_defs env_empty defs env ->
    ok_script defs
.

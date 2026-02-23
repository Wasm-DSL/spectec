From Stdlib Require Import List String Reals.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat ssrint.
From MetaSpectec Require Import syntax env reduction subst.
Import ListNotations.

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
    sub_typ (append_env env env') (TupT tups) (subst_typ sbst (TupT tups')) -> 
    sub_typ env (TupT ((x1, t1) :: tups)) (TupT ((x2, t2) :: tups'))
  | st_struct : forall env t1 t2 tfs1 tfs2,
    expand_typ (env_to_store env) t1 (StructT tfs1) ->
    expand_typ (env_to_store env) t2 (StructT tfs2) -> 
    sub_typ env t1 t2
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
    ok_exp env e (IterT t I_STAR)
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
    (* TODO - ok_args *)
    ok_exp env (CallE x ags) (subst_typ sbst rt)
  (* TODO iterE valid *)
  | oke_cvt : forall env e nt1 nt2,
    ok_exp env e (NumT nt1) ->
    ok_exp env (CvtE e nt1 nt2) (NumT nt2)
  (* TODO subE valid *)
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
    ok_typ (append_env env env') (TupT tups) ->
    ok_typ env (TupT ((x1, t1) :: tups))
  | okt_iter : forall env t it,
    ok_typ env t ->
    (it = I_STAR) \/ (it = I_OPT) ->
    ok_typ env (IterT t it)
  | okt_var : forall env x ags ps insts,
    (StringMap.find x (TYPS env) = Some (ps, insts)) -> 
    ok_typ env (VarT x ags)
.
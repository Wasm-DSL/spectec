From Stdlib Require Import List String Reals.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat ssrint.
From MetaSpectec Require Import syntax env.


 
(* Inductive valid_unop : unop -> optyp -> il_typ -> il_typ -> Prop :=
  | NotOp_ok : valid_unop NotOp BoolOp BoolT BoolT
  | Minus_ok : valid_unop MinusOp NumOp (NumT NatT) (NumT NatT)
  | Plus_ok : valid_unop PlusOp NumOp (NumT NatT) (NumT NatT)
. *)
(*
Inductive valid_binop : binop -> optyp -> il_typ -> il_typ -> il_typ -> Prop :=
  | AndOp_ok : valid_binop AndOp BoolOp BoolT BoolT BoolT
  | OrOp_ok : valid_binop OrOp BoolOp BoolT BoolT BoolT
  | ImplOp_ok : valid_binop ImplOp BoolOp BoolT BoolT BoolT
  | EquivOp_ok : valid_binop EquivOp BoolOp BoolT BoolT BoolT
  | AddOp_ok : valid_binop AddOp NumOp NatT NatT NatT
  | SubOp_ok : valid_binop AddOp NumOp NatT NatT NatT
  | MulOp_ok : valid_binop MulOp NumOp NatT NatT NatT
  | DivOp_ok : valid_binop DivOp NumOp NatT NatT NatT
  | ModOp_ok : valid_binop ModOp NumOp NatT NatT NatT
  | PowOp_ok : valid_binop PowOp NumOp NatT NatT NatT
.

Inductive valid_cmpop : cmpop -> optyp -> il_typ -> il_typ -> il_typ -> Prop :=
  | EqOp_ok : forall t, valid_cmpop EqOp BoolOp t t BoolT
  | NeqOp_ok : forall t, valid_cmpop NeqOp BoolOp t t BoolT
  | LtOp_ok : valid_cmpop LtOp NumOp NatT NatT BoolT
  | LeOp_ok : valid_cmpop LeOp NumOp NatT NatT BoolT
  | GtOp_ok : valid_cmpop GtOp NumOp NatT NatT BoolT
  | GeOp_ok : valid_cmpop GeOp NumOp NatT NatT BoolT
.

Inductive valid_typ : il_env -> il_typ -> Prop :=
  | VarT_ok : forall env il_id args params insts, 
    env[il_id]t = (params, insts) ->
    List.Forall2 (fun a p => valid_arg env a p) args params ->
    valid_typ env (VarT il_id args)
  | BoolT_ok : forall env, valid_typ env BoolT
  | NatT_ok : forall env, valid_typ env NatT
  | TextT_ok : forall env, valid_typ env TextT
  | IterT_ok : forall env iter t, 
    valid_typ env t -> valid_typ env (IterT iter t)
  | TupT_ok : forall env typbinds,
    List.Forall (fun p => valid_typ env (snd p)) typbinds ->
    valid_typ env (TupT typbinds)  

with

valid_exp : il_env -> side -> il_exp -> il_typ -> Prop :=
  | VarE_hole_ok : forall env t, valid_exp env LHS (VarE "_") t 
  | VarE_ok : forall env il_id s t,
    env[il_id]v = t ->
    valid_exp env s (VarE il_id) t
  | BoolE_ok : forall env s b, valid_exp env s (BoolE b) BoolT
  | NatE_ok : forall env s n, valid_exp env s (NatE n) NatT
  | TextE_ok : forall env s str, valid_exp env s (TextE str) TextT
  | UnE_ok : forall env s unop op e t,
    valid_unop unop op t t ->
    valid_exp env s e t ->
    valid_exp env s (UnE unop op e) t
  | BinE_ok : forall env s binop op e1 e2 t,
    valid_binop binop op t t t ->
    valid_exp env s e1 t ->
    valid_exp env s e2 t ->
    valid_exp env s (BinE binop op e1 e2) t
  | CmpE_ok : forall env s cmpop op e1 e2 t,
    valid_cmpop cmpop op t t BoolT ->
    valid_exp env s e1 t ->
    valid_exp env s e2 t ->
    valid_exp env s (CmpE cmpop op e1 e2) BoolT
  | IdxE_ok : forall env s e1 e2 t,
    valid_exp env s e1 (IterT I_STAR t) ->
    valid_exp env s e2 NatT ->
    valid_exp env s (IdxE e1 e2) t
    | I_SUP : option il_ild -> il_exp -> iter
  | SliceE_ok : forall env s e1 e2 e3 t,
    valid_exp env s e1 t ->
    valid_exp env s e2 NatT ->
    valid_exp env s e3 NatT ->
    valid_exp env s (SliceE e1 e2 e3) t

with

valid_arg : il_env -> il_arg -> il_param -> Prop :=
  | ExpA_ok : forall env e il_id t, 
    valid_exp env LHS e t ->
    valid_arg env (ExpA e) (ExpP il_id t)
  | TypA_ok : forall env t il_id,
    valid_typ env t ->
    valid_arg env (TypA t) (TypP il_id)
  | DefA_ok : forall env il_id ps t clauses, 
    env[il_id]d = (ps, t, clauses) ->
    valid_arg env (DefA il_id) (DefP il_id ps t)
. *)

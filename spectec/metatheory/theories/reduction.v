From Stdlib Require Import List String Reals.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat ssrint.
From MetaSpectec Require Import syntax subst env numerics.
Import ListNotations.

Definition option_to_list {T: Type} (arg : option T) : seq T :=
	match arg with
		| None => nil
		| Some a => a :: nil
	end.

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
  (* CasE rules *)
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
.

Inductive reduce_exp : store -> il_exp -> il_exp -> Prop :=
  | re_refl : forall s e, reduce_exp s e e
  | re_step : forall s e1 e2 e3, 
    reduce_exp s e2 e3 ->
    reduce_exp s e1 e3
.


From Stdlib Require Import List String.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat ssrint.
From MetaSpectec Require Import syntax env.
Require Import Stdlib.FSets.FMapAVL.
Require Import Stdlib.Structures.OrderedTypeEx.
Import ListNotations.

Module StringMap := FMapAVL.Make(String_as_OT).

Definition singleton {A} (k : string) (v : A) : StringMap.t A :=
  StringMap.add k v (StringMap.empty A).

Record il_subst : Type := 
  {
  S_EXP : StringMap.t il_exp;
  S_TYP : StringMap.t il_typ;
  S_FUN : StringMap.t il_id;
  }
.

Definition empty_exp : StringMap.t il_exp := StringMap.empty il_exp.
Definition empty_typ : StringMap.t il_typ := StringMap.empty il_typ.
Definition empty_id : StringMap.t il_id := StringMap.empty il_id.
Definition subst_empty : il_subst := {| S_EXP := empty_exp; S_TYP := empty_typ; S_FUN := empty_id |}.

Definition union {A}
  (m1 m2 : StringMap.t A) : StringMap.t A :=
  StringMap.fold (fun k v => StringMap.add k v) m1 m2.

Definition append_subst (s1 s2 : il_subst) : il_subst :=
  {|
  S_EXP := union s1.(S_EXP) s2.(S_EXP);
  S_TYP := union s1.(S_TYP) s2.(S_TYP);
  S_FUN := union s1.(S_FUN) s2.(S_FUN) 
  |}.

Record dom : Type :=
  {
  D_EXP : list il_id;
  D_TYP : list il_id;
  D_FUN : list il_id 
  }
.

Definition append_dom (d1 d2 : dom) : dom :=
  {|
  D_EXP := d1.(D_EXP) ++ d2.(D_EXP);
  D_TYP := d1.(D_TYP) ++ d2.(D_TYP);
  D_FUN := d1.(D_FUN) ++ d2.(D_FUN)
  |}
.

Definition get_keys {A : Type} (s : StringMap.t A) : list string :=
  List.map fst (StringMap.elements s).

Definition dom_subst (s : il_subst) : dom :=
  {| D_EXP := get_keys s.(S_EXP); D_TYP := get_keys s.(S_TYP); D_FUN := get_keys s.(S_FUN) |}.

Definition bound_param (p : il_param) : dom :=
  match p with
  | ExpP il_id _ => {| D_EXP := [il_id]; D_TYP := []; D_FUN := [] |}
  | TypP il_id => {| D_EXP := []; D_TYP := [il_id]; D_FUN := [] |}
  | DefP il_id _ _ => {| D_EXP := []; D_TYP := []; D_FUN := [il_id]|}
  end
.

Fixpoint bound_params (ps : list il_param) : dom :=
  match ps with
  | [] => {| D_EXP := []; D_TYP := []; D_FUN := [] |}
  | p :: ps => append_dom (bound_param p) (bound_params ps)
  end
.

(* TODO handle capture avoidance *)

Definition subst_fun (s : il_subst) (x : il_id) : il_id :=
  match StringMap.find x s.(S_FUN) with
  | Some y => y
  | None => x
  end
.

Definition subst_iter (s : il_subst) (i : iter) : iter :=
  match i with
  | I_SUP x e => I_SUP x e
  | _ => i
  end
.

Fixpoint subst_typ (s : il_subst) (t : il_typ) : il_typ :=
  match t with
  | VarT x args => 
    match StringMap.find x s.(S_TYP) with
    | Some t' => t'
    | None => VarT x (List.map (subst_arg s) args)
    end
  | TupT xts => TupT (List.map (fun '(x, t) => (x, subst_typ s t)) xts)
  | IterT t' it => IterT (subst_typ s t') (subst_iter s it)
  | _ => t
  end

with

subst_exp (s : il_subst) (e : il_exp) : il_exp :=
  match e with
  | VarE x => 
    match StringMap.find x s.(S_EXP) with
    | Some e' => e'
    | _ => e
    end
  | UnE unop e1 => UnE unop (subst_exp s e1)
  | BinE bop e1 e2 => BinE bop (subst_exp s e1) (subst_exp s e2)
  | CmpE cmop e1 e2 => CmpE cmop (subst_exp s e1) (subst_exp s e2)
  | TupE exps => TupE (List.map (subst_exp s) exps)
  | CaseE m e' => CaseE m (subst_exp s e')
  | OptE (Some e') => OptE (Some (subst_exp s e'))
  | ListE exps => ListE (List.map (subst_exp s) exps)
  | LiftE e' => LiftE (subst_exp s e')
  | StrE efields => StrE (List.map (fun '(a, e) => (a, subst_exp s e))efields)
  | ProjE e' n => ProjE (subst_exp s e') n
  | LenE e' => LenE (subst_exp s e')
  | MemE e1 e2 => MemE (subst_exp s e1) (subst_exp s e2)
  | CatE e1 e2 => CatE (subst_exp s e1) (subst_exp s e2)
  | CompE e1 e2 => CompE (subst_exp s e1) (subst_exp s e2)
  | IdxE e1 e2 => IdxE (subst_exp s e1) (subst_exp s e2)
  | SliceE e1 e2 e3 => SliceE (subst_exp s e1) (subst_exp s e2) (subst_exp s e3)
  | AccE e' p => AccE (subst_exp s e') (subst_path s p)
  | UpdE e1 p e2 => UpdE (subst_exp s e1) (subst_path s p) (subst_exp s e2)
  | ExtE e1 p e2 => ExtE (subst_exp s e1) (subst_path s p) (subst_exp s e2)
  | CallE x args => CallE x (List.map (subst_arg s) args)
  | IterE e' it xexps => IterE (subst_exp s e') (subst_iter s it) (List.map (fun '(x, e) => (x, subst_exp s e)) xexps)
  | CvtE e' nt1 nt2 => CvtE (subst_exp s e') nt1 nt2
  | SubE e' t1 t2 => SubE (subst_exp s e') (subst_typ s t1) (subst_typ s t2)
  | _ => e
  end

with

subst_path (s : il_subst) (p : il_path) : il_path :=
  match p with
  | RootP => RootP
  | IdxP p' e' => IdxP (subst_path s p') (subst_exp s e')
  | SliceP p' e1 e2 => SliceP (subst_path s p') (subst_exp s e1) (subst_exp s e2)
  | DotP p' a => DotP (subst_path s p') a
  | TheP p' => TheP (subst_path s p')
  | UncaseP p' m => UncaseP (subst_path s p') m 
  end

with 

subst_arg (s : il_subst) (a : il_arg) : il_arg :=
  match a with
  | ExpA e => ExpA (subst_exp s e)
  | TypA t => TypA (subst_typ s t)
  | DefA x => DefA (subst_fun s x)
  end
.

Fixpoint subst_param (s : il_subst) (p : il_param) : il_param :=
  match p with
  | ExpP x t => ExpP x (subst_typ s t)
  | TypP x => TypP x
  | DefP x ps t => DefP x (List.map (subst_param s) ps) (subst_typ s t)
  end
.

Definition subst_quant (s : il_subst) (p : il_quant) : il_quant := subst_param s p.

Fixpoint subst_prem (s : il_subst) (p : il_prem) : il_prem :=
  match p with
  | RulePr x args e => RulePr x (List.map (subst_arg s) args) (subst_exp s e)
  | IfPr e => IfPr (subst_exp s e)
  | ElsePr => ElsePr
  | LetPr e1 e2 => LetPr (subst_exp s e1) (subst_exp s e2)
  | IterPr p' it xexps => IterPr (subst_prem s p') (subst_iter s it) (List.map (fun '(x, e) => (x, subst_exp s e)) xexps)
  | NegPr p' => NegPr (subst_prem s p')
  end.

Definition arg_for_param (a : il_arg) (p : il_param) : il_subst :=
  match a, p with
  | ExpA e, ExpP x _ => {| S_EXP := singleton x e; S_TYP := empty_typ; S_FUN := empty_id |}
  | TypA t, TypP x => {| S_EXP := empty_exp; S_TYP := singleton x t; S_FUN := empty_id |}
  | DefA y, DefP x _ _ => {| S_EXP := empty_exp; S_TYP := empty_typ; S_FUN := singleton x y |} 
  | _, _ => subst_empty
  end
.

Fixpoint args_for_params (ags : list il_arg) (ps : list il_param) : il_subst :=
  match ags, ps with
  | [], [] => subst_empty
  | _, [] => subst_empty
  | [], _ => subst_empty
  | a :: ags', p :: ps' => append_subst (arg_for_param a p) (args_for_params ags' ps')
  end
.

Definition subst_deftyp (s : il_subst) (dt : il_deftyp) : il_deftyp :=
  match dt with
  | AliasT t => AliasT (subst_typ s t)
  | StructT typfields => StructT (List.map (fun '(a, qs, t, prems) =>
    (a, List.map (subst_quant s) qs, subst_typ s t, List.map (subst_prem s) prems) 
  ) typfields)
  | VariantT typcases => VariantT (List.map (fun '(m, qs, t, prems) =>
    (m, List.map (subst_quant s) qs, subst_typ s t, List.map (subst_prem s) prems) 
  ) typcases)
  end
.

Definition param_to_arg (p : il_param) : il_arg :=
  match p with
  | ExpP x _ => ExpA (VarE x)
  | TypP x => TypA (VarT x [])
  | DefP x _ _ => DefA x
  end
.

Inductive ok_subst : il_env -> il_subst -> list il_quant -> Prop := 
  | Subst_OK : forall E s q_lst,
    ok_subst E s q_lst.
     

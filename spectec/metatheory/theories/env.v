From Stdlib Require Import List String Reals.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat ssrint.
Require Import Stdlib.FSets.FMapAVL.
Require Import Stdlib.Structures.OrderedTypeEx.
From MetaSpectec Require Import syntax.
Import ListNotations.

Declare Scope env_scope.
Module StringMap := FMapAVL.Make(String_as_OT).

Definition union {A}
  (m1 m2 : StringMap.t A) : StringMap.t A :=
  StringMap.fold (fun k v => StringMap.add k v) m1 m2.

Definition singleton {A} (k : string) (v : A) : StringMap.t A :=
  StringMap.add k v (StringMap.empty A).

(* TYPING *)

Definition var_def : Type := il_typ.
Definition typ_def : Type := list il_param * list il_inst.
Definition rel_def : Type := list il_param * il_typ * list il_rule.
Definition definition_def : Type := list il_param * il_typ * list il_clause.

(* Typing context *)

Record il_env := {
  VARS : StringMap.t var_def;
  TYPS : StringMap.t typ_def;
  DEFS : StringMap.t definition_def;
  RELS : StringMap.t rel_def
}.

Definition empty_vars : StringMap.t var_def := StringMap.empty var_def.
Definition empty_typs : StringMap.t typ_def := StringMap.empty typ_def.
Definition empty_defs : StringMap.t definition_def := StringMap.empty definition_def.
Definition empty_rels : StringMap.t rel_def := StringMap.empty rel_def.

Definition env_empty : il_env := {| VARS := empty_vars; TYPS := empty_typs; DEFS := empty_defs; RELS := empty_rels |}.

Definition append_env (e1 e2 : il_env) : il_env :=
{|
  VARS := union e1.(VARS) e2.(VARS);
  TYPS := union e1.(TYPS) e2.(TYPS);
  DEFS := union e1.(DEFS) e2.(DEFS);
  RELS := union e1.(RELS) e2.(RELS) 
|}.

Definition single_var (x : il_id) (t : il_typ) : il_env :=
  {| VARS := singleton x t; TYPS := empty_typs; DEFS := empty_defs; RELS := empty_rels |}.

Definition single_envtyp (x : il_id) (ps : list il_param) (insts : list il_inst) : il_env :=
  {| VARS := empty_vars; TYPS := singleton x (ps, insts); DEFS := empty_defs; RELS := empty_rels |}.

Definition single_def (x : il_id) (ps : list il_param) (rt : il_typ) (clauses : list il_clause) : il_env :=
  {| VARS := empty_vars; TYPS := empty_typs; DEFS := singleton x (ps, rt, clauses); RELS := empty_rels |}.

Definition single_rel (x : il_id) (ps : list il_param) (t : il_typ) (rules : list il_rule) : il_env :=
  {| VARS := empty_vars; TYPS := empty_typs; DEFS := empty_defs; RELS := singleton x (ps, t, rules) |}.

Notation "x [ i ]v = t" := (StringMap.find i (VARS x) = Some t) (at level 20) : env_scope.
Notation "x [ i ]t = t" := (StringMap.find i (TYPS x) = Some t) (at level 20) : env_scope.
Notation "x [ i ]d = t" := (StringMap.find i (DEFS x) = Some t) (at level 20) : env_scope.
Notation "x [ i ]r = t" := (StringMap.find i (RELS x) = Some t) (at level 20) : env_scope.

Record store := {
  S_TYPS : StringMap.t typ_def;
  S_DEFS : StringMap.t definition_def;
  S_RELS : StringMap.t rel_def
}.

Definition store_to_env (s : store) : il_env :=
  {| VARS := empty_vars; TYPS := s.(S_TYPS); DEFS := s.(S_DEFS); RELS := s.(S_RELS) |}.

Definition env_to_store (e : il_env) : store :=
  {| S_TYPS := e.(TYPS); S_DEFS := e.(DEFS); S_RELS := e.(RELS) |}.

Fixpoint composeenvs (envs : list il_env) : il_env :=
  match envs with
  | [] => env_empty
  | e1 :: es => append_env e1 (composeenvs es)
  end
.

Definition tupenv (t : il_typ) : il_env :=
  match t with
  | TupT tups => composeenvs (List.map (fun '(x, t) => single_var x t) tups)
  | _ => env_empty
  end
.

Fixpoint paramenv (ps : list il_param) : il_env :=
  match ps with
  | [] => env_empty
  | ExpP x t :: ps' => append_env (single_var x t) (paramenv ps')
  | TypP x :: ps' => append_env (single_envtyp x [] []) (paramenv ps')
  | DefP x ps' rt :: ps'' => append_env (single_def x ps' rt []) (paramenv ps'')
  end
. 
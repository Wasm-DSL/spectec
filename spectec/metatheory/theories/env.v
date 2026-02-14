From Stdlib Require Import List String Reals.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat ssrint.
Require Import Stdlib.FSets.FMapAVL.
Require Import Stdlib.Structures.OrderedTypeEx.
From MetaSpectec Require Import syntax.

Module StringMap := FMapAVL.Make(String_as_OT).

(* TYPING *)

Definition var_def : Type := il_typ.
Definition typ_def : Type := list il_param * list il_inst.
Definition rel_def : Type := mixop * il_typ * list il_rule.
Definition definition_def : Type := list il_param * il_typ * list il_clause.

(* Typing context *)

Record il_env := {
  VARS : StringMap.t var_def;
  TYPS : StringMap.t typ_def;
  DEFS : StringMap.t definition_def;
  RELS : StringMap.t rel_def
}.

Notation "x [ i ]v = t" := (StringMap.find i (VARS x) = Some t) (at level 20).
Notation "x [ i ]t = t" := (StringMap.find i (TYPS x) = Some t) (at level 20).
Notation "x [ i ]d = t" := (StringMap.find i (DEFS x) = Some t) (at level 20).
Notation "x [ i ]r = t" := (StringMap.find i (RELS x) = Some t) (at level 20).

Record store := {
  S_TYPS : StringMap.t typ_def;
  S_DEFS : StringMap.t definition_def;
  S_RELS : StringMap.t rel_def
}.

Definition store_to_env (s : store) : il_env :=
  {| VARS := StringMap.empty var_def; TYPS := s.(S_TYPS); DEFS := s.(S_DEFS); RELS := s.(S_RELS) |}.
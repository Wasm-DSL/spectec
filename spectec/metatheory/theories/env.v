From Stdlib Require Import List String Reals.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat ssrint.
Require Import Stdlib.FSets.FMapAVL.
Require Import Stdlib.Structures.OrderedTypeEx.
From MetaSpectec Require Import syntax.
From RecordUpdate Require Import RecordUpdate.
Import ListNotations.

(* ENVIRONMENTS (doc/semantics/il/2-env.spectec) *)

Declare Scope env_scope.
Module StringMap := FMapAVL.Make(String_as_OT).

(* Right-biased: bindings in m2 shadow those in m1, matching the DSL's
   $lookup_ (last binding wins), so that [env @@ local] lets local shadow env. *)
Definition union {A}
  (m1 m2 : StringMap.t A) : StringMap.t A :=
  StringMap.fold (fun k v => StringMap.add k v) m2 m1.

Definition singleton {A} (k : string) (v : A) : StringMap.t A :=
  StringMap.add k v (StringMap.empty A).

(* Definitions stored in the environment *)

Definition var_def : Type := il_typ.
Definition typ_def : Type := list il_param * list il_inst.
Definition rel_def : Type := list il_param * il_typ * list il_rule.
Definition definition_def : Type := list il_param * il_typ * list il_clause.
Definition gram_def : Type := list il_param * il_typ * list il_prod.

(* Typing context  E = {S, EXP (id, typ)*} *)

Record il_env := {
  VARS : StringMap.t var_def;
  TYPS : StringMap.t typ_def;
  DEFS : StringMap.t definition_def;
  RELS : StringMap.t rel_def;
  GRAMS : StringMap.t gram_def
}.

#[export] Instance eta_il_env : Settable _ :=
  settable! Build_il_env <VARS; TYPS; DEFS; RELS; GRAMS>.

Definition env_empty : il_env :=
  {| VARS := StringMap.empty _; TYPS := StringMap.empty _; DEFS := StringMap.empty _;
     RELS := StringMap.empty _; GRAMS := StringMap.empty _ |}.

Definition append_env (e1 e2 : il_env) : il_env :=
{|
  VARS := union e1.(VARS) e2.(VARS);
  TYPS := union e1.(TYPS) e2.(TYPS);
  DEFS := union e1.(DEFS) e2.(DEFS);
  RELS := union e1.(RELS) e2.(RELS);
  GRAMS := union e1.(GRAMS) e2.(GRAMS)
|}.

Definition single_var (x : il_id) (t : il_typ) : il_env :=
  env_empty <| VARS := singleton x t |>.

Definition single_envtyp (x : il_id) (ps : list il_param) (insts : list il_inst) : il_env :=
  env_empty <| TYPS := singleton x (ps, insts) |>.

Definition single_def (x : il_id) (ps : list il_param) (rt : il_typ) (clauses : list il_clause) : il_env :=
  env_empty <| DEFS := singleton x (ps, rt, clauses) |>.

Definition single_rel (x : il_id) (ps : list il_param) (t : il_typ) (rules : list il_rule) : il_env :=
  env_empty <| RELS := singleton x (ps, t, rules) |>.

Definition single_gram (x : il_id) (ps : list il_param) (t : il_typ) (prods : list il_prod) : il_env :=
  env_empty <| GRAMS := singleton x (ps, t, prods) |>.

Fixpoint many_vars (xs : list (il_id * il_typ)) : il_env :=
  match xs with
  | [] => env_empty
  | (x, t) :: xs' => append_env (single_var x t) (many_vars xs')
  end
.

Notation "x @@ y" := (append_env x y) (at level 20) : env_scope.

(* Store  S = {TYP, FUN, REL, GRAM} *)

Record store := {
  S_TYPS : StringMap.t typ_def;
  S_DEFS : StringMap.t definition_def;
  S_RELS : StringMap.t rel_def;
  S_GRAMS : StringMap.t gram_def
}.

(* $storeenv *)
Definition store_to_env (s : store) : il_env :=
  {| VARS := StringMap.empty _; TYPS := s.(S_TYPS); DEFS := s.(S_DEFS);
     RELS := s.(S_RELS); GRAMS := s.(S_GRAMS) |}.

Definition env_to_store (e : il_env) : store :=
  {| S_TYPS := e.(TYPS); S_DEFS := e.(DEFS); S_RELS := e.(RELS); S_GRAMS := e.(GRAMS) |}.

(* Lookup: $lookup_typ etc. (last binding wins, via the right-biased union) *)

Definition lookup_exp (e : il_env) (x : il_id) : option il_typ := StringMap.find x e.(VARS).
Definition lookup_typ (e : il_env) (x : il_id) : option typ_def := StringMap.find x e.(TYPS).
Definition lookup_fun (e : il_env) (x : il_id) : option definition_def := StringMap.find x e.(DEFS).
Definition lookup_rel (e : il_env) (x : il_id) : option rel_def := StringMap.find x e.(RELS).
Definition lookup_gram (e : il_env) (x : il_id) : option gram_def := StringMap.find x e.(GRAMS).

Definition s_lookup_typ (s : store) (x : il_id) : option typ_def := StringMap.find x s.(S_TYPS).
Definition s_lookup_fun (s : store) (x : il_id) : option definition_def := StringMap.find x s.(S_DEFS).
Definition s_lookup_rel (s : store) (x : il_id) : option rel_def := StringMap.find x s.(S_RELS).
Definition s_lookup_gram (s : store) (x : il_id) : option gram_def := StringMap.find x s.(S_GRAMS).

Fixpoint composeenvs (envs : list il_env) : il_env :=
  match envs with
  | [] => env_empty
  | e1 :: es => append_env e1 (composeenvs es)
  end
.

Definition tupenv (t : il_typ) : il_env :=
  match t with
  | TupT tups => many_vars tups
  | _ => env_empty
  end
.

Definition paramenv1 (p : il_param) : il_env :=
  match p with
  | ExpP x t => single_var x t
  | TypP x => single_envtyp x [] []
  | DefP x ps rt => single_def x ps rt []
  | GramP x ps rt => single_gram x ps rt []
  end
.

Definition paramenv (ps : list il_param) : il_env :=
  composeenvs (List.map paramenv1 ps).

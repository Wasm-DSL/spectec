From Stdlib Require Import List String.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat ssrint.
From MetaSpectec Require Import syntax env.
From RecordUpdate Require Import RecordUpdate.
Require Import Stdlib.FSets.FMapAVL.
Require Import Stdlib.Structures.OrderedTypeEx.
Import ListNotations.

(* SUBSTITUTION (doc/semantics/il/4-subst.spectec) *)

Record il_subst : Type :=
  {
  S_EXP : StringMap.t il_exp;
  S_TYP : StringMap.t il_typ;
  S_FUN : StringMap.t il_id;
  S_GRAM : StringMap.t il_sym
  }
.

#[export] Instance eta_il_subst : Settable _ :=
  settable! Build_il_subst <S_EXP; S_TYP; S_FUN; S_GRAM>.

Definition subst_empty : il_subst :=
  {| S_EXP := StringMap.empty _; S_TYP := StringMap.empty _;
     S_FUN := StringMap.empty _; S_GRAM := StringMap.empty _ |}.

(* s1 ++ s2; right-biased like environments, so later (inner) bindings win *)
Definition append_subst (s1 s2 : il_subst) : il_subst :=
  {|
  S_EXP := union s1.(S_EXP) s2.(S_EXP);
  S_TYP := union s1.(S_TYP) s2.(S_TYP);
  S_FUN := union s1.(S_FUN) s2.(S_FUN);
  S_GRAM := union s1.(S_GRAM) s2.(S_GRAM)
  |}.

Definition subst_svar (x : il_id) (e : il_exp) : il_subst :=
  subst_empty <| S_EXP := singleton x e |>.

Definition subst_styp (x : il_id) (t : il_typ) : il_subst :=
  subst_empty <| S_TYP := singleton x t |>.

Definition subst_sfun (x : il_id) (y : il_id) : il_subst :=
  subst_empty <| S_FUN := singleton x y |>.

Definition subst_sgram (x : il_id) (g : il_sym) : il_subst :=
  subst_empty <| S_GRAM := singleton x g |>.

Fixpoint compose_substs (xs : list il_subst) : il_subst :=
  match xs with
  | [] => subst_empty
  | x :: xs' => append_subst x (compose_substs xs')
  end
.

Definition many_svars (xs : list (il_id * il_exp)) : il_subst :=
  compose_substs (List.map (fun '(x, e) => subst_svar x e) xs).

(* Domain *)

Record dom : Type :=
  {
  D_EXP : list il_id;
  D_TYP : list il_id;
  D_FUN : list il_id;
  D_GRAM : list il_id
  }
.

#[export] Instance eta_dom : Settable _ :=
  settable! Build_dom <D_EXP; D_TYP; D_FUN; D_GRAM>.

Definition dom_empty : dom := {| D_EXP := []; D_TYP := []; D_FUN := []; D_GRAM := [] |}.

Definition append_dom (d1 d2 : dom) : dom :=
  {|
  D_EXP := d1.(D_EXP) ++ d2.(D_EXP);
  D_TYP := d1.(D_TYP) ++ d2.(D_TYP);
  D_FUN := d1.(D_FUN) ++ d2.(D_FUN);
  D_GRAM := d1.(D_GRAM) ++ d2.(D_GRAM)
  |}
.

Definition get_keys {A : Type} (s : StringMap.t A) : list string :=
  List.map fst (StringMap.elements s).

Definition dom_subst (s : il_subst) : dom :=
  {| D_EXP := get_keys s.(S_EXP); D_TYP := get_keys s.(S_TYP);
     D_FUN := get_keys s.(S_FUN); D_GRAM := get_keys s.(S_GRAM) |}.

Definition bound_param (p : il_param) : dom :=
  match p with
  | ExpP x _ => dom_empty <| D_EXP := [x] |>
  | TypP x => dom_empty <| D_TYP := [x] |>
  | DefP x _ _ => dom_empty <| D_FUN := [x] |>
  | GramP x _ _ => dom_empty <| D_GRAM := [x] |>
  end
.

Fixpoint bound_params (ps : list il_param) : dom :=
  match ps with
  | [] => dom_empty
  | p :: ps => append_dom (bound_param p) (bound_params ps)
  end
.

(* Identifiers occurring in a phrase (free, bound, and of any sort).  This is
   an over-approximation of the free identifiers, used only to pick fresh
   names. *)

Fixpoint ids_typ (t : il_typ) : list il_id :=
  match t with
  | VarT x args => x :: List.concat (List.map ids_arg args)
  | BoolT | TextT | NumT _ => []
  | TupT xts => List.concat (List.map (fun '(x, t1) => x :: ids_typ t1) xts)
  | IterT t1 it => ids_typ t1 ++ ids_iter it
  | MatchT x args insts =>
    x :: List.concat (List.map ids_arg args) ++
    List.concat (List.map (fun '(qs, args', dt) =>
      List.concat (List.map ids_param qs) ++ List.concat (List.map ids_arg args') ++ ids_deftyp dt) insts)
  end

with ids_exp (e : il_exp) : list il_id :=
  match e with
  | VarE x => [x]
  | BoolE _ | NumE _ | TextE _ => []
  | UnE _ e1 | ProjE e1 _ | LiftE e1 | LenE e1 | CvtE e1 _ _ => ids_exp e1
  | BinE _ e1 e2 | CmpE _ e1 e2 | MemE e1 e2 | CatE e1 e2 => ids_exp e1 ++ ids_exp e2
  | TupE es | ListE es => List.concat (List.map ids_exp es)
  | CaseE t _ e1 qpr =>
    ids_typ t ++ ids_exp e1 ++
    match qpr with
    | Some (qs, prs) => List.concat (List.map ids_param qs) ++ List.concat (List.map ids_prem prs)
    | None => []
    end
  | OptE (Some e1) => ids_exp e1
  | OptE None => []
  | StrE t fs =>
    ids_typ t ++ List.concat (List.map (fun '(_, e1, qpr) =>
      ids_exp e1 ++
      match qpr with
      | Some (qs, prs) => List.concat (List.map ids_param qs) ++ List.concat (List.map ids_prem prs)
      | None => []
      end) fs)
  | AccE e1 p => ids_exp e1 ++ ids_path p
  | UpdE e1 p e2 | ExtE e1 p e2 => ids_exp e1 ++ ids_path p ++ ids_exp e2
  | CallE x args => x :: List.concat (List.map ids_arg args)
  | IterE e1 it eps =>
    ids_exp e1 ++ ids_iter it ++
    List.concat (List.map (fun '(x, t, ep) => x :: ids_typ t ++ ids_exp ep) eps)
  | SubE e1 t1 t2 => ids_exp e1 ++ ids_typ t1 ++ ids_typ t2
  | IfE e1 e2 e3 => ids_exp e1 ++ ids_exp e2 ++ ids_exp e3
  | MatchE args clauses =>
    List.concat (List.map ids_arg args) ++
    List.concat (List.map (fun '(qs, args', e1, prs) =>
      List.concat (List.map ids_param qs) ++ List.concat (List.map ids_arg args') ++
      ids_exp e1 ++ List.concat (List.map ids_prem prs)) clauses)
  end

with ids_path (p : il_path) : list il_id :=
  match p with
  | RootP => []
  | IdxP p1 e1 => ids_path p1 ++ ids_exp e1
  | SliceP p1 e1 e2 => ids_path p1 ++ ids_exp e1 ++ ids_exp e2
  | DotP p1 _ | TheP p1 | UncaseP p1 _ => ids_path p1
  end

with ids_sym (g : il_sym) : list il_id :=
  match g with
  | VarG x args => x :: List.concat (List.map ids_arg args)
  | NumG _ | TextG _ => []
  | SeqG gs | AltG gs => List.concat (List.map ids_sym gs)
  | RangeG g1 g2 => ids_sym g1 ++ ids_sym g2
  | AttrG e g1 => ids_exp e ++ ids_sym g1
  | IterG g1 it eps =>
    ids_sym g1 ++ ids_iter it ++
    List.concat (List.map (fun '(x, t, ep) => x :: ids_typ t ++ ids_exp ep) eps)
  end

with ids_arg (a : il_arg) : list il_id :=
  match a with
  | ExpA e => ids_exp e
  | TypA t => ids_typ t
  | DefA x => [x]
  | GramA g => ids_sym g
  end

with ids_iter (it : iter) : list il_id :=
  match it with
  | I_SUP x e => x :: ids_exp e
  | _ => []
  end

with ids_param (p : il_param) : list il_id :=
  match p with
  | ExpP x t => x :: ids_typ t
  | TypP x => [x]
  | DefP x ps t | GramP x ps t => x :: List.concat (List.map ids_param ps) ++ ids_typ t
  end

with ids_prem (p : il_prem) : list il_id :=
  match p with
  | RulePr x args e => x :: List.concat (List.map ids_arg args) ++ ids_exp e
  | IfPr e => ids_exp e
  | ElsePr => []
  | NegPr p1 => ids_prem p1
  | LetPr qs e1 e2 => List.concat (List.map ids_param qs) ++ ids_exp e1 ++ ids_exp e2
  | IterPr p1 it eps eqs =>
    ids_prem p1 ++ ids_iter it ++
    List.concat (List.map (fun '(x, t, ep) => x :: ids_typ t ++ ids_exp ep) eps) ++
    List.concat (List.map (fun '(e, x, t) => x :: ids_exp e ++ ids_typ t) eqs)
  end

with ids_deftyp (dt : il_deftyp) : list il_id :=
  match dt with
  | AliasT t => ids_typ t
  | StructT tfs =>
    List.concat (List.map (fun '(_, qs, t, prs) =>
      List.concat (List.map ids_param qs) ++ ids_typ t ++ List.concat (List.map ids_prem prs)) tfs)
  | VariantT tcs =>
    List.concat (List.map (fun '(_, qs, t, prs) =>
      List.concat (List.map ids_param qs) ++ ids_typ t ++ List.concat (List.map ids_prem prs)) tcs)
  end
.

Definition ids_params (ps : list il_param) : list il_id := List.concat (List.map ids_param ps).
Definition ids_prems (prs : list il_prem) : list il_id := List.concat (List.map ids_prem prs).
Definition ids_args (args : list il_arg) : list il_id := List.concat (List.map ids_arg args).

(* Identifiers in the range of a substitution *)
Definition range_ids (s : il_subst) : list il_id :=
  List.concat (List.map (fun xe => ids_exp xe.2) (StringMap.elements s.(S_EXP))) ++
  List.concat (List.map (fun xt => ids_typ xt.2) (StringMap.elements s.(S_TYP))) ++
  List.map snd (StringMap.elements s.(S_FUN)) ++
  List.concat (List.map (fun xg => ids_sym xg.2) (StringMap.elements s.(S_GRAM))).

(* Identifiers in the domain and range of a substitution *)
Definition ids_subst (s : il_subst) : list il_id :=
  get_keys s.(S_EXP) ++ get_keys s.(S_TYP) ++ get_keys s.(S_FUN) ++ get_keys s.(S_GRAM) ++
  range_ids s.

(* Freshness

   The DSL's [Fresh_id] is a builtin relation, and its [$refresh_*] functions
   are total.  We model it as follows:
   - [fresh_id av x], a concrete name supply used inside the substitution
     functions (capture avoidance under binders): a primed variant of [x] that
     does not occur in the avoid list [av] (see [fresh_id_fresh]).  Each
     binding site passes every identifier in scope (the substitution's domain
     and range, and the phrase the binder scopes over), so renaming never
     captures;
   - [Fresh_id], the freshness predicate used by the reduction rules that
     need fresh names relative to a context they cannot see (these premises
     also require the names to be pairwise distinct). *)

Parameter Fresh_id : il_id -> Prop.

Fixpoint primes (n : nat) : string :=
  match n with
  | O => EmptyString
  | S n' => ("'" ++ primes n')%string
  end.

(* First of x', x'', ... (from k primes on) not in av *)
Fixpoint fresh_search (av : list il_id) (x : il_id) (fuel k : nat) : il_id :=
  match fuel with
  (* Unreachable for fuel > |av| (pigeonhole); longer than every name in av *)
  | O => (x ++ "'" ++ String.concat EmptyString av)%string
  | S fuel' =>
    let c := (x ++ primes k)%string in
    if List.existsb (String.eqb c) av then fresh_search av x fuel' (S k) else c
  end.

Definition fresh_id (av : list il_id) (x : il_id) : il_id :=
  fresh_search av x (S (List.length av)) 1.

Lemma length_append_str : forall s1 s2 : string,
  String.length (s1 ++ s2) = String.length s1 + String.length s2.
Proof. by elim=> [//|c s1 IH] s2 /=; rewrite IH. Qed.

Lemma length_le_concat : forall (y : string) (av : list il_id),
  List.In y av -> String.length y <= String.length (String.concat EmptyString av).
Proof.
  move=> y; elim=> [//|a av IH] /=.
  case: av IH => [|b av] IH [Ha|Hin] //=; subst => //.
  - by rewrite length_append_str leq_addr.
  - rewrite length_append_str; apply: leq_trans (IH Hin) _; exact: leq_addl.
Qed.

Lemma fresh_search_fresh : forall av x fuel k, ~ List.In (fresh_search av x fuel k) av.
Proof.
  move=> av x; elim=> [|fuel IH] k /=.
  - move=> /length_le_concat; rewrite !length_append_str /=.
    by rewrite addnS ltnNge leq_addl.
  - case Hex: (List.existsb _ _); first exact: IH.
    move=> Hin; move: Hex; rewrite (proj2 (List.existsb_exists _ _)) //.
    by exists (x ++ primes k)%string; split; last exact: String.eqb_refl.
Qed.

Lemma fresh_id_fresh : forall av x, ~ List.In (fresh_id av x) av.
Proof. move=> av x; exact: fresh_search_fresh. Qed.

Definition refresh_expid (av : list il_id) (x : il_id) : il_id * il_subst :=
  let x' := fresh_id av x in (x', subst_svar x (VarE x')).
Definition refresh_typid (av : list il_id) (x : il_id) : il_id * il_subst :=
  let x' := fresh_id av x in (x', subst_styp x (VarT x' [])).
Definition refresh_funid (av : list il_id) (x : il_id) : il_id * il_subst :=
  let x' := fresh_id av x in (x', subst_sfun x x').
Definition refresh_gramid (av : list il_id) (x : il_id) : il_id * il_subst :=
  let x' := fresh_id av x in (x', subst_sgram x (VarG x' [])).

(* Rename the binder of a parameter to a given name *)
Definition rename_param_to (p : il_param) (y : il_id) : il_param * il_subst :=
  match p with
  | ExpP x t => (ExpP y t, subst_svar x (VarE y))
  | TypP x => (TypP y, subst_styp x (VarT y []))
  | DefP x ps t => (DefP y ps t, subst_sfun x y)
  | GramP x ps t => (GramP y ps t, subst_sgram x (VarG y []))
  end
.

Definition param_id (p : il_param) : il_id :=
  match p with
  | ExpP x _ | TypP x | DefP x _ _ | GramP x _ _ => x
  end
.

(* $refresh_param (binder only) *)
Definition refresh_param (av : list il_id) (p : il_param) : il_param * il_subst :=
  rename_param_to p (fresh_id av (param_id p)).

(* $refresh_list, fused with substitution: substitute [s] (plus the renamings
   of earlier binders) into each element, then rename that element's binders.
   Returns the new list and the renamings.  Fusing the two passes keeps every
   recursive call on a structural subterm. *)
Definition seq_refresh {X : Type} (f : il_subst -> X -> X * il_subst) (s : il_subst) :=
  fix go (acc : il_subst) (xs : list X) : list X * il_subst :=
  match xs with
  | [] => ([], acc)
  | x :: xs' =>
    let r1 := f (append_subst s acc) x in
    let r := go (append_subst acc (snd r1)) xs' in
    (fst r1 :: fst r, snd r)
  end.

(* [av]: identifiers to avoid, i.e. everything in the scope of the binders;
   the identifiers of the substitution are added here *)
Definition seq_refresh_params (sp : il_subst -> il_param -> il_param) (av : list il_id) (s : il_subst) (ps : list il_param) :=
  let av' := av ++ ids_subst s in
  seq_refresh (fun s' p => refresh_param av' (sp s' p)) s subst_empty ps.

Definition subst_fun (s : il_subst) (x : il_id) : il_id :=
  match StringMap.find x s.(S_FUN) with
  | Some y => y
  | None => x
  end
.

Fixpoint subst_typ (s : il_subst) (t : il_typ) {struct t} : il_typ :=
  match t with
  | VarT x [] =>
    match StringMap.find x s.(S_TYP) with
    | Some t' => t'
    | None => t
    end
  | VarT x args => VarT x (List.map (subst_arg s) args)
  | BoolT | TextT | NumT _ => t
  | TupT xts => TupT (List.map (fun '(x, t) => (x, subst_typ s t)) xts)
  | IterT t' it =>
    match it with
    | I_SUP x e =>
      let x' := fresh_id (ids_subst s ++ ids_typ t) x in
      IterT (subst_typ (append_subst s (subst_svar x (VarE x'))) t') (I_SUP x' (subst_exp s e))
    | _ => IterT (subst_typ s t') it
    end
  | MatchT x args insts =>
    MatchT x (List.map (subst_arg s) args) (List.map (fun '(qs, args', dt) =>
      let r := seq_refresh_params subst_param (ids_typ t) s qs in
      let s' := append_subst s (snd r) in
      (fst r, List.map (subst_arg s') args', subst_deftyp s' dt)
    ) insts)
  end

with

subst_exp (s : il_subst) (e : il_exp) {struct e} : il_exp :=
  match e with
  | VarE x =>
    match StringMap.find x s.(S_EXP) with
    | Some e' => e'
    | None => e
    end
  | BoolE _ | NumE _ | TextE _ => e
  | UnE op e1 => UnE op (subst_exp s e1)
  | BinE op e1 e2 => BinE op (subst_exp s e1) (subst_exp s e2)
  | CmpE op e1 e2 => CmpE op (subst_exp s e1) (subst_exp s e2)
  | TupE es => TupE (List.map (subst_exp s) es)
  | ProjE e1 n => ProjE (subst_exp s e1) n
  | CaseE t m e1 qpr =>
    CaseE (subst_typ s t) m (subst_exp s e1)
      (match qpr with
       | Some (qs, prs) =>
         let r := seq_refresh_params subst_param (ids_exp e) s qs in
         Some (fst r, List.map (subst_prem (append_subst s (snd r))) prs)
       | None => None
       end)
  | OptE (Some e1) => OptE (Some (subst_exp s e1))
  | OptE None => e
  | StrE t fs =>
    StrE (subst_typ s t) (List.map (fun '(a, e1, qpr) =>
      (a, subst_exp s e1,
       match qpr with
       | Some (qs, prs) =>
         let r := seq_refresh_params subst_param (ids_exp e) s qs in
         Some (fst r, List.map (subst_prem (append_subst s (snd r))) prs)
       | None => None
       end)) fs)
  | ListE es => ListE (List.map (subst_exp s) es)
  | LiftE e1 => LiftE (subst_exp s e1)
  | MemE e1 e2 => MemE (subst_exp s e1) (subst_exp s e2)
  | LenE e1 => LenE (subst_exp s e1)
  | CatE e1 e2 => CatE (subst_exp s e1) (subst_exp s e2)
  | AccE e1 p => AccE (subst_exp s e1) (subst_path s p)
  | UpdE e1 p e2 => UpdE (subst_exp s e1) (subst_path s p) (subst_exp s e2)
  | ExtE e1 p e2 => ExtE (subst_exp s e1) (subst_path s p) (subst_exp s e2)
  | CallE x args => CallE (subst_fun s x) (List.map (subst_arg s) args)
  | IterE e1 it eps =>
    (* $refresh_iter and $refresh_exppulls *)
    let av := ids_subst s ++ ids_exp e in
    let r_it := match it with
      | I_SUP x en => let x' := fresh_id av x in (I_SUP x' (subst_exp s en), subst_svar x (VarE x'))
      | _ => (it, subst_empty)
      end in
    let eps' := List.map (fun '(x, t, ep) => (fresh_id av x, subst_typ s t, subst_exp s ep)) eps in
    let s_eps := many_svars (List.map (fun '(x, _, _) => (x, VarE (fresh_id av x))) eps) in
    IterE (subst_exp (append_subst s (append_subst (snd r_it) s_eps)) e1) (fst r_it) eps'
  | CvtE e1 nt1 nt2 => CvtE (subst_exp s e1) nt1 nt2
  | SubE e1 t1 t2 => SubE (subst_exp s e1) (subst_typ s t1) (subst_typ s t2)
  | IfE e1 e2 e3 => IfE (subst_exp s e1) (subst_exp s e2) (subst_exp s e3)
  | MatchE args clauses =>
    MatchE (List.map (subst_arg s) args) (List.map (fun '(qs, args', e1, prs) =>
      let r := seq_refresh_params subst_param (ids_exp e) s qs in
      let s' := append_subst s (snd r) in
      (* $subst_expprems *)
      let rp := seq_refresh (subst_refresh_prem (ids_subst s' ++ ids_exp e)) s' subst_empty prs in
      (fst r, List.map (subst_arg s') args', subst_exp (append_subst s' (snd rp)) e1, fst rp)
    ) clauses)
  end

with

subst_path (s : il_subst) (p : il_path) {struct p} : il_path :=
  match p with
  | RootP => RootP
  | IdxP p' e' => IdxP (subst_path s p') (subst_exp s e')
  | SliceP p' e1 e2 => SliceP (subst_path s p') (subst_exp s e1) (subst_exp s e2)
  | DotP p' a => DotP (subst_path s p') a
  | TheP p' => TheP (subst_path s p')
  | UncaseP p' m => UncaseP (subst_path s p') m
  end

with

subst_sym (s : il_subst) (g : il_sym) {struct g} : il_sym :=
  match g with
  | VarG x [] =>
    match StringMap.find x s.(S_GRAM) with
    | Some g' => g'
    | None => g
    end
  | VarG x args =>
    match StringMap.find x s.(S_GRAM) with
    | Some (VarG y []) => VarG y (List.map (subst_arg s) args)
    | _ => VarG x (List.map (subst_arg s) args)
    end
  | NumG _ | TextG _ => g
  | SeqG gs => SeqG (List.map (subst_sym s) gs)
  | AltG gs => AltG (List.map (subst_sym s) gs)
  | RangeG g1 g2 => RangeG (subst_sym s g1) (subst_sym s g2)
  | AttrG e g1 => AttrG (subst_exp s e) (subst_sym s g1)
  | IterG g1 it eps =>
    let av := ids_subst s ++ ids_sym g in
    let r_it := match it with
      | I_SUP x en => let x' := fresh_id av x in (I_SUP x' (subst_exp s en), subst_svar x (VarE x'))
      | _ => (it, subst_empty)
      end in
    let eps' := List.map (fun '(x, t, ep) => (fresh_id av x, subst_typ s t, subst_exp s ep)) eps in
    let s_eps := many_svars (List.map (fun '(x, _, _) => (x, VarE (fresh_id av x))) eps) in
    IterG (subst_sym (append_subst s (append_subst (snd r_it) s_eps)) g1) (fst r_it) eps'
  end

with

subst_arg (s : il_subst) (a : il_arg) {struct a} : il_arg :=
  match a with
  | ExpA e => ExpA (subst_exp s e)
  | TypA t => TypA (subst_typ s t)
  | DefA x => DefA (subst_fun s x)
  | GramA g => GramA (subst_sym s g)
  end

with

subst_param (s : il_subst) (p : il_param) {struct p} : il_param :=
  match p with
  | ExpP x t => ExpP x (subst_typ s t)
  | TypP x => TypP x
  | DefP x ps t =>
    let r := seq_refresh_params subst_param (ids_param p) s ps in
    DefP x (fst r) (subst_typ (append_subst s (snd r)) t)
  | GramP x ps t =>
    let r := seq_refresh_params subst_param (ids_param p) s ps in
    GramP x (fst r) (subst_typ (append_subst s (snd r)) t)
  end

with

subst_prem (s : il_subst) (p : il_prem) {struct p} : il_prem :=
  match p with
  | RulePr x args e => RulePr x (List.map (subst_arg s) args) (subst_exp s e)
  | IfPr e => IfPr (subst_exp s e)
  | ElsePr => ElsePr
  | NegPr p' => NegPr (subst_prem s p')
  (* Assume: q* fresh (refreshed by the caller) *)
  | LetPr qs e1 e2 => LetPr (List.map (subst_param s) qs) (subst_exp s e1) (subst_exp s e2)
  (* Assume: the pushed variables are fresh (refreshed by the caller) *)
  | IterPr p' it eps eqs =>
    let av := ids_subst s ++ ids_prem p in
    let r_it := match it with
      | I_SUP x en => let x' := fresh_id av x in (I_SUP x' (subst_exp s en), subst_svar x (VarE x'))
      | _ => (it, subst_empty)
      end in
    let eps' := List.map (fun '(x, t, ep) => (fresh_id av x, subst_typ s t, subst_exp s ep)) eps in
    let s_eps := many_svars (List.map (fun '(x, _, _) => (x, VarE (fresh_id av x))) eps) in
    let s_in := append_subst s (append_subst (snd r_it) s_eps) in
    let rp := subst_refresh_prem av s_in p' in
    IterPr (fst rp) (fst r_it) eps'
      (List.map (fun '(e, x, t) => (subst_exp (append_subst s_in (snd rp)) e, x, subst_typ s t)) eqs)
  end

with

(* Substitute, then rename the binders the premise introduces ($refresh_prem);
   returns the renaming of those binders.  [av]: identifiers in the scope of
   those binders outside the premise itself (later premises, the body). *)
subst_refresh_prem (av : list il_id) (s : il_subst) (p : il_prem) {struct p} : il_prem * il_subst :=
  let av' := av ++ ids_subst s ++ ids_prem p in
  match p with
  | RulePr x args e => (RulePr x (List.map (subst_arg s) args) (subst_exp s e), subst_empty)
  | IfPr e => (IfPr (subst_exp s e), subst_empty)
  | ElsePr => (ElsePr, subst_empty)
  | NegPr p' => (NegPr (subst_prem s p'), subst_empty)
  | LetPr qs e1 e2 =>
    let r := seq_refresh_params subst_param av' s qs in
    (LetPr (fst r) (subst_exp (append_subst s (snd r)) e1) (subst_exp s e2), snd r)
  | IterPr p' it eps eqs =>
    let r_it := match it with
      | I_SUP x en => let x' := fresh_id av' x in (I_SUP x' (subst_exp s en), subst_svar x (VarE x'))
      | _ => (it, subst_empty)
      end in
    let eps' := List.map (fun '(x, t, ep) => (fresh_id av' x, subst_typ s t, subst_exp s ep)) eps in
    let s_eps := many_svars (List.map (fun '(x, _, _) => (x, VarE (fresh_id av' x))) eps) in
    let s_in := append_subst s (append_subst (snd r_it) s_eps) in
    let rp := subst_refresh_prem av' s_in p' in
    (IterPr (fst rp) (fst r_it) eps'
      (List.map (fun '(e, x, t) => (subst_exp (append_subst s_in (snd rp)) e, fresh_id av' x, subst_typ s t)) eqs),
     many_svars (List.map (fun '(_, x, _) => (x, VarE (fresh_id av' x))) eqs))
  end

with

subst_deftyp (s : il_subst) (dt : il_deftyp) {struct dt} : il_deftyp :=
  match dt with
  | AliasT t => AliasT (subst_typ s t)
  | StructT tfs => StructT (List.map (fun '(a, qs, t, prs) =>
    (* $subst_typprems *)
    let av := ids_subst s ++ ids_deftyp dt in
    let rt := match t with
      | TupT xts =>
        let r := seq_refresh (fun s0 '(x, tx) =>
          let x' := fresh_id av x in ((x', subst_typ s0 tx), subst_svar x (VarE x'))) s subst_empty xts in
        (TupT (fst r), snd r)
      | _ => (subst_typ s t, subst_empty)
      end in
    let s1 := append_subst s (snd rt) in
    let rq := seq_refresh_params subst_param av s1 qs in
    let s2 := append_subst s1 (snd rq) in
    let rp := seq_refresh (subst_refresh_prem (av ++ ids_subst s2)) s2 subst_empty prs in
    (a, fst rq, fst rt, fst rp)
  ) tfs)
  | VariantT tcs => VariantT (List.map (fun '(m, qs, t, prs) =>
    let av := ids_subst s ++ ids_deftyp dt in
    let rt := match t with
      | TupT xts =>
        let r := seq_refresh (fun s0 '(x, tx) =>
          let x' := fresh_id av x in ((x', subst_typ s0 tx), subst_svar x (VarE x'))) s subst_empty xts in
        (TupT (fst r), snd r)
      | _ => (subst_typ s t, subst_empty)
      end in
    let s1 := append_subst s (snd rt) in
    let rq := seq_refresh_params subst_param av s1 qs in
    let s2 := append_subst s1 (snd rq) in
    let rp := seq_refresh (subst_refresh_prem (av ++ ids_subst s2)) s2 subst_empty prs in
    (m, fst rq, fst rt, fst rp)
  ) tcs)
  end
.

Definition subst_iter (s : il_subst) (i : iter) : iter :=
  match i with
  | I_SUP x e => I_SUP x (subst_exp s e)
  | _ => i
  end
.

Definition subst_quant (s : il_subst) (p : il_quant) : il_quant := subst_param s p.

Definition refresh_params (av : list il_id) (ps : list il_param) : list il_param * il_subst :=
  seq_refresh_params subst_param (av ++ ids_params ps) subst_empty ps.

(* $refresh_prems.  [av]: identifiers in the scope of the premises' binders
   outside the premises themselves *)
Definition refresh_prems (av : list il_id) (prs : list il_prem) : list il_prem * il_subst :=
  seq_refresh (subst_refresh_prem (av ++ ids_prems prs)) subst_empty subst_empty prs.

Definition subst_quantprems (s : il_subst) (qpr : quantprems) : quantprems :=
  let r := seq_refresh_params subst_param (ids_params qpr.1 ++ ids_prems qpr.2) s qpr.1 in
  (fst r, List.map (subst_prem (append_subst s (snd r))) qpr.2).

(* $subst_expprems *)
Definition subst_expprems (s : il_subst) (e : il_exp) (prs : list il_prem) : il_exp * list il_prem :=
  let rp := seq_refresh (subst_refresh_prem (ids_subst s ++ ids_exp e ++ ids_prems prs)) s subst_empty prs in
  (subst_exp (append_subst s (snd rp)) e, fst rp).

Definition subst_inst (s : il_subst) (i : il_inst) : il_inst :=
  let '(qs, args, dt) := i in
  let r := seq_refresh_params subst_param (ids_params qs ++ ids_args args ++ ids_deftyp dt) s qs in
  let s' := append_subst s (snd r) in
  (fst r, List.map (subst_arg s') args, subst_deftyp s' dt).

Definition subst_rule (s : il_subst) (ru : il_rule) : il_rule :=
  let '(qs, e, prs) := ru in
  let r := seq_refresh_params subst_param (ids_params qs ++ ids_exp e ++ ids_prems prs) s qs in
  let ep := subst_expprems (append_subst s (snd r)) e prs in
  (fst r, ep.1, ep.2).

Definition subst_clause (s : il_subst) (c : il_clause) : il_clause :=
  let '(qs, args, e, prs) := c in
  let r := seq_refresh_params subst_param (ids_params qs ++ ids_args args ++ ids_exp e ++ ids_prems prs) s qs in
  let s' := append_subst s (snd r) in
  let ep := subst_expprems s' e prs in
  (fst r, List.map (subst_arg s') args, ep.1, ep.2).

Definition subst_prod (s : il_subst) (pd : il_prod) : il_prod :=
  let '(qs, g, e, prs) := pd in
  let r := seq_refresh_params subst_param (ids_params qs ++ ids_sym g ++ ids_exp e ++ ids_prems prs) s qs in
  let s' := append_subst s (snd r) in
  let ep := subst_expprems s' e prs in
  (fst r, subst_sym s' g, ep.1, ep.2).

Definition subst_argmatch (s : il_subst) (am : argmatch) : argmatch :=
  (subst_arg s am.1, subst_arg s am.2).

Definition subst_expmatch (s : il_subst) (em : expmatch) : expmatch :=
  (subst_exp s em.1, subst_exp s em.2).

Definition subst_exppush (s : il_subst) (eq : exppush) : exppush :=
  (subst_exp s (push_exp eq), push_id eq, subst_typ s (push_typ eq)).

(* Renaming the binders a premise introduces to given names (used by the
   reduction rules that need distinct fresh names per instance) *)

Definition prem_binders (p : il_prem) : list il_id :=
  match p with
  | LetPr qs _ _ => List.map param_id qs
  | IterPr _ _ _ eqs => List.map push_id eqs
  | _ => []
  end
.

Definition rename_prem (p : il_prem) (ys : list il_id) : il_prem * il_subst :=
  match p with
  | LetPr qs e1 e2 =>
    let fix go (acc : il_subst) (qs : list il_param) (ys : list il_id) : list il_param * il_subst :=
      match qs, ys with
      | q :: qs', y :: ys' =>
        let r1 := rename_param_to (subst_param acc q) y in
        let r := go (append_subst acc (snd r1)) qs' ys' in
        (fst r1 :: fst r, snd r)
      | _, _ => ([], acc)
      end in
    let r := go subst_empty qs ys in
    (LetPr (fst r) (subst_exp (snd r) e1) e2, snd r)
  | IterPr p' it eps eqs =>
    (IterPr p' it eps (List.map (fun '(eq, y) => (push_exp eq, y, push_typ eq)) (zip eqs ys)),
     many_svars (List.map (fun '(eq, y) => (push_id eq, VarE y)) (zip eqs ys)))
  | _ => (p, subst_empty)
  end
.

(* Constructing substitutions for parameters *)

(* Partial, as in the DSL: undefined on a kind mismatch or unequal lengths *)
Definition arg_for_param (a : il_arg) (p : il_param) : option il_subst :=
  match a, p with
  | ExpA e, ExpP x _ => Some (subst_svar x e)
  | TypA t, TypP x => Some (subst_styp x t)
  | DefA y, DefP x _ _ => Some (subst_sfun x y)
  | GramA g, GramP x _ _ => Some (subst_sgram x g)
  | _, _ => None
  end
.

Fixpoint args_for_params (ags : list il_arg) (ps : list il_param) : option il_subst :=
  match ags, ps with
  | [], [] => Some subst_empty
  | a :: ags', p :: ps' =>
    match arg_for_param a p with
    | Some s =>
      match args_for_params ags' (List.map (subst_param s) ps') with
      | Some s' => Some (append_subst s s')
      | None => None
      end
    | None => None
    end
  | _, _ => None
  end
.

(* $tupsubst *)
Definition tupsubst (e : il_exp) (t : il_typ) : il_subst :=
  match t with
  | TupT xts => many_svars (List.map (fun '(i, (x, _)) => (x, ProjE e i)) (zip (iota 0 (size xts)) xts))
  | _ => subst_empty
  end
.

(* $paramarg *)
Definition param_to_arg (p : il_param) : il_arg :=
  match p with
  | ExpP x _ => ExpA (VarE x)
  | TypP x => TypA (VarT x [])
  | DefP x _ _ => DefA x
  | GramP x _ _ => GramA (VarG x [])
  end
.

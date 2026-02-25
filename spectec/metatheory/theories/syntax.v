From Stdlib Require Import List String.
From mathcomp Require Import all_ssreflect all_algebra. 
Import GRing.Theory.

Parameter R : archiNumDomainType.

(* SYNTAX *)

Definition atom : Type := string.
Definition mixop : Type := list (list atom).
Definition il_id : Type := string.
Definition text : Type := string.

Inductive optyp : Type :=
  | BoolOp
  | NumOp
.

Inductive numunop : Type :=
  | PlusOp
  | MinusOp
.

Inductive boolunop : Type :=
  | NotOp
.

Inductive unop : Type :=
  | NumUnop : numunop -> unop
  | BoolUnop : boolunop -> unop
.

Inductive numbinop : Type :=
  | AddOp
  | SubOp
  | MulOp
  | DivOp
  | ModOp
  | PowOp
.

Inductive boolbinop : Type :=
  | AndOp
  | OrOp
  | ImplOp
  | EquivOp
.

Inductive binop : Type :=
  | NumBinop : numbinop -> binop
  | BoolBinop : boolbinop -> binop
.

Inductive numcmpop : Type :=
  | LtOp
  | LeOp
  | GtOp
  | GeOp
.

Inductive boolcmpop : Type :=
  | EqOp
  | NeqOp
.

Inductive cmpop : Type :=
  | NumCmpop : numcmpop -> cmpop
  | BoolCmpop : boolcmpop -> cmpop
.

Inductive numtyp : Type :=
  | NatT
  | IntT
  | RatT
  | RealT
.

Inductive il_num : Type :=
  | NatE : nat -> il_num
  | IntE : int -> il_num
  | RatE : rat -> il_num
  | RealE : R -> il_num
.

Inductive il_typ : Type :=
  | VarT : il_id -> list il_arg -> il_typ
  | BoolT
  | TextT
  | NumT : numtyp -> il_typ
  | TupT : list (il_id * il_typ) -> il_typ
  | IterT : il_typ -> iter -> il_typ

with

il_exp : Type :=
  | VarE : il_id -> il_exp
  | BoolE : bool -> il_exp
  | NumE : il_num -> il_exp
  | TextE : text -> il_exp
  | UnE : unop -> il_exp -> il_exp
  | BinE : binop -> il_exp -> il_exp -> il_exp
  | CmpE : cmpop -> il_exp -> il_exp -> il_exp
  | TupE : list il_exp -> il_exp
  | ProjE : il_exp -> nat -> il_exp
  | CaseE : mixop -> il_exp -> il_exp
  | OptE : option il_exp -> il_exp
  | StrE : list (atom * il_exp) -> il_exp
  | DotE : il_exp * atom -> il_exp
  | CompE : il_exp -> il_exp -> il_exp
  | ListE : list il_exp -> il_exp
  | LiftE : il_exp -> il_exp
  | MemE : il_exp -> il_exp -> il_exp
  | LenE : il_exp -> il_exp
  | CatE : il_exp -> il_exp -> il_exp
  | IdxE : il_exp -> il_exp -> il_exp
  | SliceE : il_exp -> il_exp -> il_exp -> il_exp
  | AccE : il_exp -> il_path -> il_exp
  | UpdE : il_exp -> il_path -> il_exp -> il_exp
  | ExtE : il_exp -> il_path -> il_exp -> il_exp
  | CallE : il_id -> list il_arg -> il_exp
  | IterE : il_exp -> iter -> list (il_id * il_exp) -> il_exp
  | CvtE : il_exp -> numtyp -> numtyp -> il_exp
  | SubE : il_exp -> il_typ -> il_typ -> il_exp
  | IfE : il_exp -> il_exp -> il_exp -> il_exp

with

il_path : Type :=
  | RootP
  | IdxP : il_path -> il_exp -> il_path
  | TheP : il_path -> il_path
  | UncaseP : il_path -> mixop -> il_path 
  | SliceP : il_path -> il_exp -> il_exp -> il_path
  | DotP : il_path -> atom -> il_path

with

il_arg : Type := 
  | ExpA : il_exp -> il_arg
  | TypA : il_typ -> il_arg
  | DefA : il_id -> il_arg

with

iter : Type :=
  | I_STAR
  | I_OPT
  | I_PLUS
  | I_SUP : option il_id -> il_exp -> iter
.

Definition exppull : Type := (il_id * il_exp).

Inductive il_param : Type :=
  | ExpP : il_id -> il_typ -> il_param
  | TypP : il_id -> il_param
  | DefP : il_id -> list il_param -> il_typ -> il_param
.

Definition il_quant : Type := il_param.

Inductive il_prem : Type :=
  | RulePr : il_id -> list il_arg -> il_exp -> il_prem
  | IfPr : il_exp -> il_prem
  | ElsePr
  | LetPr : il_exp -> il_exp -> il_prem
  | IterPr : il_prem -> iter -> list exppull -> il_prem
  | NegPr : il_prem -> il_prem
.

Definition typfield : Type := atom * list il_quant * il_typ * list il_prem.
Definition typcase : Type := mixop * list il_quant * il_typ * list il_prem.

Inductive il_deftyp : Type :=
  | AliasT : il_typ -> il_deftyp
  | StructT : list typfield -> il_deftyp
  | VariantT : list typcase -> il_deftyp
.

Definition il_inst : Type := list il_quant * list il_arg * il_deftyp.

Definition il_rule : Type := list il_quant * il_exp * list il_prem.

Definition il_clause : Type := list il_quant * list il_arg * il_exp * list il_prem.

Inductive il_def : Type :=
  | TypD : il_id -> list il_param -> list il_inst -> il_def
  | RelD : il_id -> list il_param -> il_typ -> list il_rule -> il_def
  | DecD : il_id -> list il_param -> il_typ -> list il_clause -> il_def
  | RecD : list il_def -> il_def
.

Definition script : Type := list il_def.

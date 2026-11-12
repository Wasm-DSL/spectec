open Util
open Sexpr
open Source
open Xl
open Il
open Ast


(* Literal *)

let bool b = Atom (Bool.to_string b)
let text t = Atom ("\"" ^ String.escaped t ^ "\"")
let id x = text x.it
let rec mixop = function
  | Mixop.Arg () -> Atom "Arg"
  | Mixop.Atom a -> Node ("Atom", [Atom (Atom.to_string a)])
  | Mixop.Brack (l, m, r) -> Node ("Brack", [Atom (Atom.to_string l); mixop m; Atom (Atom.to_string r)])
  | Mixop.Infix (m1, a, m2) -> Node ("Infix", [mixop m1; Atom (Atom.to_string a); mixop m2])
  | Mixop.Seq ms -> Node ("Seq", List.map mixop ms)

let num = function
  | `Nat n -> Node ("Nat", [Atom (Z.to_string n)])
  | `Int i -> Node ("Int", [Atom ((if i >= Z.zero then "+" else "-") ^ Z.to_string (Z.abs i))])
  | `Rat q -> Node ("Rat", [Atom (Z.to_string (Q.num q) ^ "/" ^ Z.to_string (Q.den q))])
  | `Real r -> Node ("Real", [Atom (Printf.sprintf "%.17g" r)])


(* Operators *)

let unop = function
  | `NotOp -> Atom "NotOp"
  | `PlusOp -> Atom "PlusOp"
  | `MinusOp -> Atom "MinusOp"
  | `PlusMinusOp -> Atom "PlusMinusOp"
  | `MinusPlusOp -> Atom "MinusPlusOp"

let binop = function
  | `AndOp -> Atom "AndOp"
  | `OrOp -> Atom "OrOp"
  | `ImplOp -> Atom "ImplOp"
  | `EquivOp -> Atom "EquivOp"
  | `AddOp -> Atom "AddOp"
  | `SubOp -> Atom "SubOp"
  | `MulOp -> Atom "MulOp"
  | `DivOp -> Atom "DivOp"
  | `ModOp -> Atom "ModOp"
  | `PowOp -> Atom "PowOp"

let cmpop = function
  | `EqOp -> Atom "EqOp"
  | `NeOp -> Atom "NeOp"
  | `LtOp -> Atom "LtOp"
  | `GtOp -> Atom "GtOp"
  | `LeOp -> Atom "LeOp"
  | `GeOp -> Atom "GeOp"


(* Iterations *)

let rec iter = function
  | Opt -> Atom "Opt"
  | List -> Atom "List"
  | List1 -> Atom "List1"
  | ListN (e, xo) -> Node ("ListN", [exp e] @ List.map id (Option.to_list xo))


(* Types *)

and booltyp t = Atom (Bool.string_of_typ t)
and numtyp t = Atom (Num.string_of_typ t)

and optyp = function
  | #Bool.typ as t -> booltyp t
  | #Num.typ as t -> numtyp t

and typ t =
  match t.it with
  | VarT (x, as1) -> Node ("VarT", [id x] @ List.map arg as1)
  | BoolT -> Atom "BoolT"
  | NumT t -> numtyp t
  | TextT -> Atom "TextT"
  | TupT ets -> Node ("TupT", List.map typbind ets)
  | IterT (t1, it) -> Node ("IterT", [typ t1; iter it])

and deftyp dt =
  match dt.it with
  | AliasT t -> Node ("AliasT", [typ t])
  | StructT tfs -> Node ("StructT", List.map typfield tfs)
  | VariantT tcs -> Node ("VariantT", List.map typcase tcs)

and typbind (x, t) =
  Node ("typbind", [id x; typ t])

and typfield (at, (t, qs, prs), _hints) =
  Node ("typfield", mixop (Mixop.Atom at) :: typ t :: List.map param qs @ List.map prem prs)

and typcase (op, (t, qs, prs), _hints) =
  Node ("typcase", mixop op :: typ t :: List.map param qs @ List.map prem prs)


(* Expressions *)

and exp e =
  match e.it with
  | VarE x -> Node ("VarE", [id x])
  | BoolE b -> Node ("BoolE", [bool b])
  | NumE n -> Node ("NumE", [num n])
  | TextE t -> Node ("TextE", [text t])
  | UnE (op, t, e2) -> Node ("UnE", [unop op; optyp t; exp e2])
  | BinE (op, t, e1, e2) -> Node ("BinE", [binop op; optyp t; exp e1; exp e2])
  | CmpE (op, t, e1, e2) -> Node ("CmpE", [cmpop op; optyp t; exp e1; exp e2])
  | IdxE (e1, e2) -> Node ("IdxE", [exp e1; exp e2])
  | SliceE (e1, e2, e3) -> Node ("SliceE", [exp e1; exp e2; exp e3])
  | UpdE (e1, p, e2) -> Node ("UpdE", [exp e1; path p; exp e2])
  | ExtE (e1, p, e2) -> Node ("ExtE", [exp e1; path p; exp e2])
  | StrE efs -> Node ("StrE", List.map expfield efs)
  | DotE (e1, at) -> Node ("DotE", [exp e1; mixop (Mixop.Atom at)])
  | CompE (e1, e2) -> Node ("CompE", [exp e1; exp e2])
  | MemE (e1, e2) -> Node ("MemE", [exp e1; exp e2])
  | LenE e1 -> Node ("LenE", [exp e1])
  | TupE es -> Node ("TupE", List.map exp es)
  | CallE (x, as1) -> Node ("CallE", id x :: List.map arg as1)
  | IterE (e1, it) -> Node ("IterE", [exp e1] @ iterexp it)
  | ProjE (e1, i) -> Node ("ProjE", [exp e1; Atom (string_of_int i)])
  | CaseE (op, e1) -> Node ("CaseE", [mixop op; exp e1])
  | UncaseE (e1, op) -> Node ("UncaseE", [exp e1; mixop op])
  | OptE eo -> Node ("OptE", List.map exp (Option.to_list eo))
  | TheE e1 -> Node ("TheE", [exp e1])
  | ListE es -> Node ("ListE", List.map exp es)
  | LiftE e1 -> Node ("LiftE", [exp e1])
  | CatE (e1, e2) -> Node ("CatE", [exp e1; exp e2])
  | CvtE (e1, nt1, nt2) -> Node ("CvtE", [numtyp nt1; numtyp nt2; exp e1])
  | SubE (e1, t1, t2) -> Node ("SubE", [typ t1; typ t2; exp e1])
  | IfE (e1, e2, e3) -> Node ("IfE", [exp e1; exp e2; exp e3])

and expfield (at, e) =
  Node ("expfield", [mixop (Mixop.Atom at); exp e])

and path p =
  match p.it with
  | RootP -> Atom "RootP"
  | IdxP (p1, e) -> Node ("IdxP", [path p1; exp e])
  | SliceP (p1, e1, e2) -> Node ("SliceP", [path p1; exp e1; exp e2])
  | DotP (p1, at) -> Node ("DotP", [path p1; mixop (Mixop.Atom at)])

and iterexp (it, xes) =
  iter it :: List.map (fun (x, e) -> Node ("iterexp", [id x; exp e])) xes


(* Grammars *)

and sym g =
  match g.it with
  | VarG (x, as1) -> Node ("VarG", id x :: List.map arg as1)
  | NumG n -> Node ("NumG", [Atom (Printf.sprintf "0x%02X" n)])
  | TextG t -> Node ("TextG", [text t])
  | EpsG -> Atom "EpsG"
  | SeqG gs -> Node ("SeqG", List.map sym gs)
  | AltG gs -> Node ("AltG", List.map sym gs)
  | RangeG (g1, g2) -> Node ("RangeG", [sym g1; sym g2])
  | IterG (g1, it) -> Node ("IterG", [sym g1] @ iterexp it)
  | AttrG (e, g1) -> Node ("AttrG", [exp e; sym g1])


(* Premises *)

and prem pr =
  match pr.it with
  | RulePr (x, as1, op, e) -> Node ("RulePr", id x :: List.map arg as1 @ [mixop op; exp e])
  | IfPr e -> Node ("IfPr", [exp e])
  | LetPr (_qs, e1, e2) -> Node ("LetPr", [exp e1; exp e2])
  | ElsePr -> Atom "ElsePr"
  | IterPr (pr1, it) -> Node ("IterPr", [prem pr1] @ iterexp it)
  | NegPr pr1 -> Node ("NegPr", [prem pr1])


(* Definitions *)

and arg a =
  match a.it with
  | ExpA e -> Node ("ExpA", [exp e])
  | TypA t -> Node ("TypA", [typ t])
  | DefA x -> Node ("DefA", [id x])
  | GramA g -> Node ("GramA", [sym g])

and param p =
  match p.it with
  | ExpP (x, t) -> Node ("ExpP", [id x; typ t])
  | TypP x -> Node ("TypP", [id x])
  | DefP (x, ps, t) -> Node ("DefP", [id x] @ List.map param ps @ [typ t])
  | GramP (x, ps, t) -> Node ("GramP", [id x] @ List.map param ps @ [typ t])

let inst inst =
  match inst.it with
  | InstD (ps, as_, dt) ->
    Node ("InstD", List.map param ps @ List.map arg as_ @ [deftyp dt])

let rule rule =
  match rule.it with
  | RuleD (x, ps, op, e, prs) ->
    Node ("RuleD", [id x] @ List.map param ps @ [mixop op; exp e] @ List.map prem prs)

let clause clause =
  match clause.it with
  | DefD (ps, as_, e, prs) ->
    Node ("DefD", List.map param ps @ List.map arg as_ @ [exp e] @ List.map prem prs)

let prod prod =
  match prod.it with
  | ProdD (ps, g, e, prs) ->
    Node ("ProdD", List.map param ps @ [sym g; exp e] @ List.map prem prs)

let hint h =
  Node ("hint", [id h.hintid; text (El.Print.string_of_exp h.hintexp)])

let hintdef h =
  match h.it with
  | TypH (x, hs) -> Node ("TypH", [id x] @ List.map hint hs)
  | RelH (x, hs) -> Node ("RelH", [id x] @ List.map hint hs)
  | DecH (x, hs) -> Node ("DecH", [id x] @ List.map hint hs)
  | GramH (x, hs) -> Node ("GramH", [id x] @ List.map hint hs)
  | RuleH (x, x2, hs) -> Node ("RuleH", [id x; id x2] @ List.map hint hs)

let rec def d =
  match d.it with
  | TypD (x, ps, insts) ->
    Node ("TypD", [id x] @ List.map param ps @ List.map inst insts)
  | RelD (x, ps, op, t, rules) ->
    Node ("RelD", [id x] @ List.map param ps @ [mixop op; typ t] @ List.map rule rules)
  | DecD (x, ps, t, clauses) ->
    Node ("DecD", [id x] @ List.map param ps @ [typ t] @ List.map clause clauses)
  | GramD (x, ps, t, prods) ->
    Node ("GramD", [id x] @ List.map param ps @ [typ t] @ List.map prod prods)
  | RecD ds ->
    Node ("RecD", List.map def ds)
  | HintD h ->
    Node ("HintD", [hintdef h])


(* Scripts *)

let script ds =
  List.filter ((<>) (Atom "script")) (List.map def ds)


(* Printing *)

open Config

let output_typ oc cfg t = Sexpr.output oc cfg.width (typ t)
let output_exp oc cfg e = Sexpr.output oc cfg.width (exp e)
let output_def oc cfg d = Sexpr.output oc cfg.width (def d)
let output_script oc cfg s = List.iter (Sexpr.output oc cfg.width) (script s)

let string_of_typ cfg t = Sexpr.to_string cfg.width (typ t)
let string_of_exp cfg e = Sexpr.to_string cfg.width (exp e)
let string_of_def cfg d = Sexpr.to_string cfg.width (def d)
let string_of_script cfg s =
  String.concat "\n" (List.map (Sexpr.to_string cfg.width) (script s))

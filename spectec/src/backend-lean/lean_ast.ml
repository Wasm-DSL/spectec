(* 

A tiny subset of the grammar of Lean4, mostly taken from https://lean-lang.org/doc/reference/latest

Just here to separate the logic for rendering Lean code into raw strings from building the Lean code.

snake_case names directly correspond to camelCase names in the Lean reference, whereas names starting with underscores (like _params) do not, and are my own refactorings for convenience.
*)

type doc_comment = string [@@deriving show]
type decl_id = string [@@deriving show]
type ident = string [@@deriving show]
type hole = Hole [@@deriving show]

type 'a non_empty_list = 'a Util.Lib.NonEmptyList.t 
let pp_non_empty_list pp_a fmt nel =
  Format.pp_print_list pp_a fmt (Util.Lib.NonEmptyList.to_list nel)


(* TODO: check again *)
type level =
  | LevelLit of int           (* 0, 1, 2, ... *)
  | LevelVar of ident         (* u, v *)
[@@deriving show]
  (*
    TODO: currently unused and thus not yet implemented, but there are some other productions from 
    
    https://lean-lang.org/doc/reference/latest/find/?domain=Verso.Genre.Manual.section&name=level-expressions
  *)
  (* | LevelAdd of level * int   (* Level + n *)
  | LevelMax of level * level
  | LevelIMax of level * level *)

type _index_type =
  | Plain
  | Option
  | Unsafe
[@@deriving show]

type term =
  | Hole of hole
  | FunType of term * term (* this is the X -> Y type, whereas Lambda is the concrete fun x => y *)
  | Ident of ident
  | Sort of level
  | Type of level option
  | Prop
  | ProdType of term * term (* According to https://lean-lang.org/doc/reference/latest/Basic-Types/Tuples/ this should technically be term * term, but I'm doing this for convenience *)
  
  | FunApp of term * argument non_empty_list

  (* what is this even for lol *)
  | FunAppEllipsis of term * argument list

  | Num of _numtype (* check if this makes sense *)
  | Text of string
  (*
    BinaryInfixFunApp does not exist in core Lean4 grammar;
    
    e.g. x + y desugars to HAdd.hAdd x y

    Nevertheless, this serves our conventional rendering
  *)
  | BinaryInfixFunApp of argument * term * argument
  | Tuple of term list (* unsure if this is officially in the Lean 4 grammar *)
  | DotProj of term * term (* unsure if this is officially in the Lean 4 grammar *)
  | LeadingDot of term (* unsure if this is officially in the Lean 4 grammar *)
  | Struct of {
    fields: struct_inst_field list;
    type_annotation: term option;
  }
  | List of term list
  | Index of {
    collection: term;
    index: term;
    index_type: _index_type;
  }
  | Slice of {
    collection: term;
    bounds: _slice_bounds;
  }
  | UpdateStruct of {
    struct_to_update: term;
    fields_to_update: struct_inst_field list;
  }

  | Lambda of {
    params: fun_binder non_empty_list;
    body: term;
  }

  | IfThenElse of {
    cond: term;
    then_branch: term;
    else_branch: term;
  }

  (*
    TODO: The actual Lean reference gives the fuller `match` grammar:

    term ::= ...
    | match
          ((generalizing := (trueVal | falseVal)))?
          ((motive := term))?
          matchDiscr,*
        with
      (| (term,* )|* => term)*

    at https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/
  
    but we'll use a simplified one for now.
  *)

  | Match of {
    match_terms: term list;
    cases: (term list * term) list;
  }

  | By of tactic_seq                     (* by tacticSeq *)

  | RightPipelineField of term * term (* term |> term *)
  
  | AnonymousApp            (* (· ·) — apply first arg to second *)

  (*
    ∀ x ∈ xs, P x

    This is Lean 4 macro notation (not a primitive term) that desugars to:

      ∀ x, x ∈ xs → P x

    It is the kernel-safe translation for IterPr: instead of defining
    Forall inductively (which breaks the kernel for mutual inductives),
    we emit this plain ∀ form which Lean accepts in all contexts.

    See: https://lean-lang.org/doc/reference/latest/Terms/Function-Types/
         for the underlying ∀ binder grammar this notation desugars to.
  *)
  | BoundedForall of {
      var        : ident;   (* x  — the bound element variable *)
      collection : term;    (* xs — the list being iterated over *)
      body       : term;    (* P x — the proposition applied to each element *)
    }

  | Not of term

  | Sorry

  (*
    Premises is NOT an official Lean 4 grammar production. It exists here purely
    for rendering convenience: it represents the premises-then-conclusion shape of
    an inductive constructor type (or a theorem statement -- see the Theorem
    signature construction in backend.ml, which builds one of these too), where
    each premise should appear on its own line:

      | case_name (params...) :
          premise_1 →
          premise_2 →
          conclusion

    The distinction from a chain of FunType nodes matters because FunType is also
    used for value-level function types (α → β) which should remain inline.
    Using a dedicated node lets the renderer apply the multi-line layout without
    any heuristics, and keeps backend.ml in control of which arrow chains are
    logical sequents vs. function types.

    Non-empty, by convention: the LAST element is the conclusion (the only one
    with no trailing/leading arrow), everything before it is a premise. Not
    modelled as a separate `conclusion` field -- both of backend.ml's builders
    either already have a flat list on hand (rule_prems for a theorem, where
    the last premise just *is* the conclusion) or would immediately glue
    premises and conclusion back into one list to render them (the old
    two-field version did exactly that, right after backend.ml's other
    builder had done the opposite split to construct it) -- so a plain list
    avoids that round trip on both ends. render_term uses
    Util.Lib.List.split_last to pull the conclusion off when it needs to
    render it without a trailing arrow.
  *)
  | Premises of term list

  (* | UpdateList of {
    name_of_list_to_update: term;
    index: term;
    new_value: term;
  } *)

  (*
    «let» ::= "let" letConfig letDecl (";")? term

    from https://lean-lang.org/doc/reference/latest/Terms/Local-Definitions/

    Examples:
      let x := 42
      x + 1

      let (a, b) := pair
      a + b

      let h : x = y := rfl
      h ▸ goal

      let +nondep (a, b) := pair
      a + b
  *)
  | Let of {
      let_config: let_config_item list;
      let_decl: let_decl;
      body: term;
    }
[@@deriving show]

(*
  letOpt ::= "nondep" | "postponeValue" | "usedOnly" | "zeta" | "generalize"

  Options that can be toggled on (+) or off (-) in a let configuration.

  Examples:
    let +nondep x := ...    -- enable nondep reduction
    let -zeta x := ...      -- disable zeta reduction
*)
and let_opt =
  | Nondep          (* nondep *)
  | PostponeValue   (* postponeValue *)
  | UsedOnly        (* usedOnly *)
  | Zeta            (* zeta *)
  | Generalize      (* generalize *)
[@@deriving show]

(*
  letConfigItem ::= "+" letOpt | "-" letOpt | "(" "eq" ":=" binderIdent ")"

  Each item either enables (+) or disables (-) a letOpt, or sets the equality
  hypothesis name used in dependent elimination.

  Examples:
    +nondep          → LetOptPos Nondep
    -zeta            → LetOptNeg Zeta
    (eq := h)        → LetOptEq "h"
*)
and let_config_item =
  | LetOptPos of let_opt      (* + letOpt *)
  | LetOptNeg of let_opt      (* - letOpt *)
  | LetOptEq of ident         (* (eq := binderIdent) *)
[@@deriving show]

(*
  letPatDecl ::= term (":" term)? ":=" term

  Both the pattern (LHS) and value (RHS) are full terms (termParser).
  The optional middle term is a type annotation.

  Examples:
    x := 42
      → { pat = Ident "x"; type_ = None; value = Num (LeanNat 42) }

    (a, b) := pair
      → { pat = Tuple [Ident "a"; Ident "b"]; type_ = None; value = Ident "pair" }

    h : x = y := rfl
      → { pat = Ident "h"; type_ = Some (BinaryInfixFunApp (Ident "x", Ident "=", Ident "y")); value = Ident "rfl" }

    ⟨tag, val⟩ := instr
      → { pat = <CaseE-derived term>; type_ = None; value = Ident "instr" }
*)
and let_pat_decl = {
  pat: term;
  type_: term option;
  value: term;
}
[@@deriving show]

(*
  letDecl ::= letPatDecl(true) | letIdDecl | letPatDecl(false) | letEqnsDecl

  We only need letPatDecl, since all LetPr cases (VarE, TupE, CaseE, StrE)
  are patterns expressible as terms. letIdDecl and letEqnsDecl cover named
  function definitions (with arguments), which the IL never generates.
*)
and let_decl =
  | LetPatDecl of let_pat_decl
[@@deriving show]



and fun_binder =
  | Ident_FB of ident
  | BracketedBinder_FB of bracketed_binder
  | Hole_FB
[@@deriving show]

and _slice_bounds =
  | SliceFrom of term
  | SliceTo of term
  | SliceBetween of term * term
[@@deriving show]

and struct_inst_field =
  | Ident_SIF of ident
  | AssignedField of {
    l_val: struct_inst_l_val;
    is_private: bool;
    term: term;
  }
[@@deriving show]



and struct_inst_l_val =
  | Ident_SILV of ident
  | Num_SILV of int
  (*
    TODO: currently unused and thus not yet implemented, but there is one more form described in:

    https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#Lean___Parser___Term___structInstLVal:~:text=a%20term%20in%20square%20brackets%2C%20followed%20by%20a%20sequence%20of%20zero%20or%20more%20subfields
  *)
[@@deriving show]

and argument =
  | Term of term
[@@deriving show]



and _numtype =
  | LeanNat of (Z.t [@printer fun fmt z -> Format.pp_print_string fmt (Z.to_string z)])
  | LeanInt of (Z.t [@printer fun fmt z -> Format.pp_print_string fmt (Z.to_string z)])
  | LeanRat of (Q.t [@printer fun fmt q -> Format.pp_print_string fmt (Q.to_string q)])
  | LeanReal of float
[@@deriving show]



and _ident_or_hole =
  | Ident_IOH of ident
  | Hole_IOH of hole
[@@deriving show]


and bracketed_binder =
  | ExplicitParam of _ident_or_hole non_empty_list * term
  | OptAutoParam of _ident_or_hole non_empty_list * term * term
  | ImplicitParam of _ident_or_hole non_empty_list * term
  | InstanceParam of term  (* [BEq X] — anonymous instance binder *)
[@@deriving show]

and _params =
  | Ident_P of ident
  | Hole_P of hole
  | BracketedBinder of bracketed_binder
[@@deriving show]

and decl_sig = _params list * term [@@deriving show]

and opt_decl_sig = _params list * term option [@@deriving show]


and tactic_seq = tactic list [@@deriving show]   (* separated by ; or newlines *)

and tactic =
  | TacticExact of term                  (* exact <term> *)
  | TacticIntros of ident list           (* intros [x y z ...] *)
  | TacticAssumption                     (* assumption *)
  | TacticFirst of tactic_seq list       (* first | seq | seq | ... *)
[@@deriving show]

type visibility =
  | Private
  | Protected
  | Public
[@@deriving show]

type recursion_modifer =
  | Partial
  | NonRec
[@@deriving show]

type decl_modifier = {
  comment: doc_comment option;
  (* TODO: attribute *)
  visibility: visibility option;
  noncomputable: bool;
  unsafe: bool;
  recursion_modifer: recursion_modifer option;
}
[@@deriving show]

type _deriving = {
  deriving: ident list;
  derive_deceq: bool;
}[@@deriving show]

(* Not part of Lean 4's own core grammar -- a custom command declared by
   test-lean/ExtendedDeriveDecEq.lean:
     syntax (name := deriveDecEqCmd) "derive_deceq " ident+ : command
   Modeled with the same `ident+` (non-empty list) shape as that rule, even
   though the elaborator only ever consults the first name and warns on the
   rest -- see [Backend.deceq_commands_for], which always emits exactly one. *)
type _derive_deceq = ident non_empty_list [@@deriving show]


type _def_case = term * term [@@deriving show]

type _def =
  | DefAsgn of {
      modifier: decl_modifier;
      id: decl_id;
      signature: opt_decl_sig;
      body: term;
    }
  | DefCases of {
      modifier: decl_modifier;
      id: decl_id;
      signature: opt_decl_sig;
      body: _def_case list;
    }
  | DefStruct of {
      modifier: decl_modifier;
      id: decl_id;
      signature: opt_decl_sig;
      body: struct_inst_field list;
    }
[@@deriving show]

type _inductive_case = {
  modifier: decl_modifier;
  id: ident;
  signature: opt_decl_sig;
}
[@@deriving show]

type _inductive = {
  modifier: decl_modifier;
  id: decl_id;
  signature: opt_decl_sig;
  cases: _inductive_case list;
  deriving: _deriving;
}
[@@deriving show]

type _abbrev = 
  | AbbrevAsgn of {
      modifier: decl_modifier;
      id: decl_id;
      signature: opt_decl_sig;
      body: term;
    }
  | AbbrevCases of {
      modifier: decl_modifier;
      id: decl_id;
      signature: opt_decl_sig;
      body: _def_case list;
    }
[@@deriving show]

type struct_field =
  | StructSimpleBinder of {
      modifier: decl_modifier;
      id: ident;
      signature: opt_decl_sig;
      (* TODO: := expr | by <tactic> *)
    }
  (* TODO: structExplicitBinder, structImplicitBinder, structInstBinder *)
[@@deriving show]

type _structure = {
  modifier: decl_modifier;
  id: decl_id;
  binders: bracketed_binder list;
  universe: term option;
  (* TODO: extends *)
  constructor: (decl_modifier * ident) option;
  fields: struct_field list;
  deriving: _deriving;
}
[@@deriving show]

type opaque = {
  modifier: decl_modifier;
  id: decl_id;
  signature: decl_sig;
  rhs: term option;
}
[@@deriving show]

(* TODO: technically, this is not just _def, but also theorems. *)
type mutual =
  (*
  I split this into two subtypes based on an error I've encountered:

  invalid mutual block: either all elements of the block must be
  inductive/structure declarations, or they must all be
  definitions/theorems/abbrevs
  *)
  | MutualInductiveStructure of _inductive list * _structure list
  | MutualDefAbbrev of _def list * _abbrev list
[@@deriving show]

type instance = {
  modifier: decl_modifier;
  priority: int option;           (* (priority := N) — optional *)
  id: decl_id option;             (* optional name; auto-generated if absent *)
  signature: decl_sig;            (* type is REQUIRED for instance (not opt_decl_sig) *)
  body: struct_inst_field list;   (* the `where` fields *)
}
[@@deriving show]

type _theorem = {
  modifier: decl_modifier;
  id: decl_id;
  signature: decl_sig;
  proof: term;
}
[@@deriving show]

type axiom = {
  id: decl_id;
  signature: decl_sig;
}[@@deriving show]

type command =
  | Def of _def
  | Inductive of _inductive
  | Abbrev of _abbrev
  | Structure of _structure
  | Opaque of opaque
  | Mutual of mutual
  | Instance of instance
  | Theorem of _theorem
  | DeriveDeceq of _derive_deceq
  | Axiom of axiom
[@@deriving show]

(* Not part of Lean 4's own command grammar: an import precedes every
   command in a file and isn't a command itself, so -- like every other
   _-prefixed type in this file -- it's modeled on its own rather than
   folded into [command]. *)
type _imports = ident list [@@deriving show]

(* Not a Lean AST construct either: the whole generated file, imports then
   commands. Was previously just `command list` with the intent noted in a
   comment (see render.ml's render__script); [_imports] is now a real
   field instead of an unmodeled side channel. *)
type _script = {
  imports: _imports;
  commands: command list;
}
[@@deriving show]

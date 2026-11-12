open Lean_ast
open Util.Lib

let empty_modifier : decl_modifier = {
  comment = None;
  visibility = None;
  noncomputable = false;
  unsafe = false;
  recursion_modifer = None;
}

let simple_lambda (param : ident) (body : term) : term =
  Lambda {
    params = NonEmptyList.from_list_unsafe [Ident_FB param];
    (* params = { head = Ident_FB param; tail = [] }; TODO: non empty list util *)
    body = body
  }

let opaque_def = By [
  TacticFirst [
    [TacticExact (DotProj (Ident "Inhabited", Ident "default"))];
    [TacticIntros []; TacticAssumption];
  ]
]

let rat_to_nat : command =
  (*
    def rat_to_nat (r : Rat) : Nat := (r.num.tdiv (Int.ofNat r.den)).toNat

    Not opaque: a real, computable definition, using only `Rat`'s own core
    fields (`num : Int`, `den : Nat` -- `Init.Data.Rat.Basic`, no import
    needed at all, it's part of the `prelude`) plus core `Int.tdiv`
    (explicitly T-rounding / truncate-toward-zero division -- NOT the
    default `/`, which is `Int.ediv` and floors for a positive divisor; the
    two diverge on negative non-integer input, e.g. `(-3).tdiv 2 = -1` vs
    `(-3) / 2 = -2`, confirmed by hand) and `Int.toNat`.

    `Int.tdiv` was chosen deliberately over the default `/`, and is total
    and correct for every `Rat` whatsoever, not just the ones this
    codebase happens to call it on: the original (now-removed) `opaque`
    stub's own doc comment specified this cast's semantics as "truncation
    toward zero (same semantics as SpecTec's $() cast)", and `Int.tdiv` is
    exactly that, by definition, for any input -- rather than a different
    convention (floor) that only happens to coincide with the documented
    one on today's call sites (which are all nonnegative) because every
    value they're ever fed also happens to already be an exact integer.
    Matching the documented cast semantics directly means correctness
    doesn't rest on that value-level coincidence continuing to hold for
    any future call site. `Int.toNat` clamps a negative result to `0`
    (unreachable today, since nothing here ever casts a negative `r`, but
    harmless either way: a `Nat` can't represent it regardless of
    convention). Confirmed computable and correct by hand, with zero
    imports: `#eval rat_to_nat (7/2 : Rat)` gives `3`.

    Earlier attempt used Mathlib's `Nat.floor` (`⌊·⌋₊`), simpler to state
    and gives `rat_to_nat_natCast` for free via `Nat.floor_natCast` -- but
    every generated file only `import ExtendedDeriveDecEq` (confirmed:
    that file itself only imports `Lean`/`Lean.Elab...`/`Lean.Meta...`,
    none of Mathlib), so `Nat.floor` doesn't actually resolve in the file
    it would need to. This core-only version avoids that: `rat_to_nat (n :
    Rat) = n` (`TypePreservation.lean`'s `rat_to_nat_natCast`, needed for
    `memory.grow`'s preservation case) still closes with plain `simp`
    after `unfold`, no Mathlib lemma needed, regardless of which of
    `tdiv`/`ediv` is used (both agree on every integer, so this proof
    doesn't distinguish them).

    Kept as a NAMED function rather than inlining this computation bare at
    each `$()`-cast call site, for the same reason as before: it pins the
    argument's type to `Rat` via a fixed, non-generic parameter, which is
    what keeps `TypePreservation.lean`'s existing 10 by-name references to
    `rat_to_nat`/`rat_to_nat_natCast` intact and keeps every future call
    site honest about what type it's casting from, regardless of whether
    its own subexpression happens to carry an explicit ascription.
  *)
  Def (DefAsgn {
    modifier = empty_modifier;
    id = "rat_to_nat";
    signature = (
      [ BracketedBinder (ExplicitParam (
          NonEmptyList.from_list_unsafe [Ident_IOH "r"],
          Ident "Rat"
        )) ],
      Some (Ident "Nat")
    );
    body = DotProj (
      FunApp (
        DotProj (DotProj (Ident "r", Ident "num"), Ident "tdiv"),
        NonEmptyList.from_list_unsafe [
          Term (FunApp (Ident "Int.ofNat", NonEmptyList.from_list_unsafe [Term (DotProj (Ident "r", Ident "den"))]))
        ]
      ),
      Ident "toNat"
    );
  })

let list_ap : command =
  (*
    def List.ap (fs : List (α → β)) (xs : List α) : List β :=
      List.zipWith (· ·) fs xs
  *)
  Def (DefAsgn {
    modifier = empty_modifier;
    id = "List.ap";
    signature = (
      [ BracketedBinder (ExplicitParam (NonEmptyList.from_list_unsafe [Ident_IOH "fs"],
          FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (FunType (Ident "α", Ident "β"))])));
        BracketedBinder (ExplicitParam (NonEmptyList.from_list_unsafe [Ident_IOH "xs"],
          FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (Ident "α")]))) ],
      Some (FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (Ident "β")]))
    );
    body = FunApp (
      FunApp (DotProj (Ident "List", Ident "zipWith"), NonEmptyList.from_list_unsafe [Term AnonymousApp]),
      NonEmptyList.from_list_unsafe [Term (Ident "fs"); Term (Ident "xs")]
    );
  })

let option_ap : command =
  (*
    def Option.ap (f : Option (α → β)) (x : Option α) : Option β :=
      f.bind (fun f => x.map f)
  *)
  Def (DefAsgn {
    modifier = empty_modifier;
    id = "Option.ap";
    signature = (
      [ BracketedBinder (ExplicitParam (NonEmptyList.from_list_unsafe [Ident_IOH "f"],
          FunApp (Ident "Option", NonEmptyList.from_list_unsafe [Term (FunType (Ident "α", Ident "β"))])));
        BracketedBinder (ExplicitParam (NonEmptyList.from_list_unsafe [Ident_IOH "x"],
          FunApp (Ident "Option", NonEmptyList.from_list_unsafe [Term (Ident "α")]))) ],
      Some (FunApp (Ident "Option", NonEmptyList.from_list_unsafe [Term (Ident "β")]))
    );
    body = FunApp (
      DotProj (Ident "f", Ident "bind"),
      NonEmptyList.from_list_unsafe [Term (Lambda {
        params = NonEmptyList.from_list_unsafe [Ident_FB "f"];
        body = FunApp (DotProj (Ident "x", Ident "map"), NonEmptyList.from_list_unsafe [Term (Ident "f")])
      })]
    );
  })

let splice : command =
  (*
    def splice (orig : List α) (payload : List α) (insertion_index : Nat) : List α :=
      let capped_insertion_index := Min.min insertion_index (orig.length)
      let capped_payload_length := Min.min payload.length (orig.length - capped_insertion_index)
      ((orig.take capped_insertion_index) ++ (payload.take capped_payload_length))
        ++ (orig.drop (capped_insertion_index + capped_payload_length))

    Not a port of any Rocq lemma -- new project-local infrastructure. Backs
    `SliceSeg` path-update translation (backend.ml's `create_upd_exp`): the
    naive `orig.take i ++ payload ++ orig.drop (i + j)` splice is only
    length-preserving when `payload`'s actual length equals the declared `j`
    exactly, which isn't guaranteed in general (e.g. an out-of-bounds memory
    store) and would otherwise let the result grow past `orig`'s real
    length. This clamps the insertion point and the effective payload length
    against `orig`'s real length first, so the result can never exceed
    `orig`'s length -- the Lean-combinator analogue of Rocq's
    `list_slice_update`, which gets the same property for free from its own
    structural recursion on the list. `α` is left to Lean's auto-bound
    implicit (same convention as `List.ap`/`Option.ap` above), and `Min.min`
    is used qualified rather than bare `min`, because some spec files (e.g.
    `0-aux.spectec`'s own `$min`) already compile to a top-level `def min`,
    which makes a bare `min` ambiguous against this clamp's intended generic
    `Min` typeclass method.
  *)
  Def (DefAsgn {
    modifier = empty_modifier;
    id = "splice";
    signature = (
      [ BracketedBinder (ExplicitParam (NonEmptyList.from_list_unsafe [Ident_IOH "orig"],
          FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (Ident "α")])));
        BracketedBinder (ExplicitParam (NonEmptyList.from_list_unsafe [Ident_IOH "payload"],
          FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (Ident "α")])));
        BracketedBinder (ExplicitParam (NonEmptyList.from_list_unsafe [Ident_IOH "insertion_index"],
          Ident "Nat")) ],
      Some (FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (Ident "α")]))
    );
    body =
      Let {
        let_config = [];
        let_decl = LetPatDecl {
          pat = Ident "capped_insertion_index";
          type_ = None;
          value = FunApp (DotProj (Ident "Min", Ident "min"), NonEmptyList.from_list_unsafe [
            Term (Ident "insertion_index");
            Term (DotProj (Ident "orig", Ident "length"))
          ]);
        };
        body = Let {
          let_config = [];
          let_decl = LetPatDecl {
            pat = Ident "capped_payload_length";
            type_ = None;
            value = FunApp (DotProj (Ident "Min", Ident "min"), NonEmptyList.from_list_unsafe [
              Term (DotProj (Ident "payload", Ident "length"));
              Term (BinaryInfixFunApp (
                Term (DotProj (Ident "orig", Ident "length")),
                Ident "-",
                Term (Ident "capped_insertion_index")
              ))
            ]);
          };
          body = BinaryInfixFunApp (
            Term (BinaryInfixFunApp (
              Term (FunApp (DotProj (Ident "orig", Ident "take"),
                NonEmptyList.from_list_unsafe [Term (Ident "capped_insertion_index")])),
              Ident "++",
              Term (FunApp (DotProj (Ident "payload", Ident "take"),
                NonEmptyList.from_list_unsafe [Term (Ident "capped_payload_length")]))
            )),
            Ident "++",
            Term (FunApp (DotProj (Ident "orig", Ident "drop"), NonEmptyList.from_list_unsafe [
              Term (BinaryInfixFunApp (
                Term (Ident "capped_insertion_index"), Ident "+", Term (Ident "capped_payload_length")
              ))
            ]))
          );
        };
      };
  })



(* let rec write__abbrev (dm : decl_modifier) (id : ) : _abbrev =
  AbbrevAsgn {
    modifier = dm;
    id = id;
    signature = opt_decl_sig;
    body = term;
  } *)
-- Illustrating: what would Sideconditions' premise-currying actually produce for
-- minus_recs's `_IDX` clause, versus what Totalize's expression-rewrite (the `.map`
-- fix) produces. Both built against the same minimal stand-in types used earlier.

abbrev n : Type := Nat
abbrev typeidx : Type := Nat
abbrev rectype : Type := Nat

inductive typeuse : Type where
  | _IDX (v_typeidx : typeidx) : typeuse
  | _DEF (v_rectype : rectype) (v_n : n) : typeuse
deriving Inhabited, BEq, DecidableEq

inductive typevar : Type where
  | _IDX (v_typeidx : typeidx) : typevar
  | REC (v_n : n) : typevar
deriving Inhabited, BEq, DecidableEq

section SideconditionsStyle
-- What `append_prems_to_term` would actually emit for the `_IDX` clause if
-- Sideconditions added its `≠ none` premise: the clause's declared return type
-- is `Option (...)`, but this ARM's body is `create_curried_func`'s output --
-- a FunType, i.e. the TYPE `(minus_recs ... ≠ none) → Option (...)` -- written
-- directly where a VALUE of type `Option (...)` belongs.
def minus_recs_sidecond (tv_lst : List typevar) (tu_lst : List typeuse) : Option (List typevar × List typeuse) :=
  match tv_lst, tu_lst with
  | [], [] => some ([], [])
  | (typevar.REC v_n) :: tv_lst, tu_1 :: tu_lst => minus_recs_sidecond tv_lst tu_lst
  | (typevar._IDX x) :: tv_lst, tu_1 :: tu_lst =>
      let (tv'_lst, tu'_lst) := Option.get! (minus_recs_sidecond tv_lst tu_lst)
      (minus_recs_sidecond tv_lst tu_lst ≠ none) → some ([typevar._IDX x] ++ tv'_lst, [tu_1] ++ tu'_lst)
  | _, _ => none
end SideconditionsStyle

section TotalizeStyle
-- What the `Totalize`-level fix (fold the LetPr into an IterE, rendered via
-- the existing `.map`/OMap path) produces: the return type is untouched, the
-- None case propagates for real, no premise, no currying.
def minus_recs_totalize (tv_lst : List typevar) (tu_lst : List typeuse) : Option (List typevar × List typeuse) :=
  match tv_lst, tu_lst with
  | [], [] => some ([], [])
  | (typevar.REC v_n) :: tv_lst, tu_1 :: tu_lst => minus_recs_totalize tv_lst tu_lst
  | (typevar._IDX x) :: tv_lst, tu_1 :: tu_lst =>
      (minus_recs_totalize tv_lst tu_lst).map (fun (tv', tu') => ([typevar._IDX x] ++ tv', [tu_1] ++ tu'))
  | _, _ => none

example : minus_recs_totalize [typevar._IDX 5] [] = none := by native_decide
end TotalizeStyle

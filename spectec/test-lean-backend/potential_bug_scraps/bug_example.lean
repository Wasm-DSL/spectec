def List.ap (fs : List (α → β)) (xs : List α) : List β :=
  List.zipWith ((· ·)) fs xs

def Option.ap (f : Option (α → β)) (x : Option α) : Option β :=
  f.bind (fun f => x.map f)

opaque rat_to_nat (r : Rat) : Nat := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Inductive Type Definition at: test-lean-backend/potential_bug_scraps/bug_example.spectec:10.1-10.21 -/
inductive marker : Type where
  | MARK : marker
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

/- Inductive Type Definition at: test-lean-backend/potential_bug_scraps/bug_example.spectec:12.1-13.20 -/
inductive thing : Type where
  | THING (marker_opt : Option marker) (_ : Nat) : thing
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

/- Inductive Relations Definition at: test-lean-backend/potential_bug_scraps/bug_example.spectec:17.1-17.30 -/
inductive Thing_ok : thing → Prop where
  | mk_Thing_ok (n : Nat) :
    n > 0 →
    Thing_ok (thing.THING (some marker.MARK) n)

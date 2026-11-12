def List.ap (fs : List (α → β)) (xs : List α) : List β :=
  List.zipWith ((· ·)) fs xs

def Option.ap (f : Option (α → β)) (x : Option α) : Option β :=
  f.bind (fun f => x.map f)

opaque rat_to_nat (r : Rat) : Nat := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Inductive Type Definition at: test-lean-backend/potential_bug_scraps/legitimate_example.spectec:7.1-7.25 -/
inductive tag : Type where
  | SMALL : tag
  | BIG : tag
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

/- Inductive Type Definition at: test-lean-backend/potential_bug_scraps/legitimate_example.spectec:9.1-9.18 -/
inductive marker : Type where
  | X : marker
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

/- Auxiliary Definition at: test-lean-backend/potential_bug_scraps/legitimate_example.spectec:11.1-11.26 -/
def extra (v_tag : tag) : Option marker :=
  match v_tag with
  | tag.SMALL => none
  | tag.BIG => some marker.X

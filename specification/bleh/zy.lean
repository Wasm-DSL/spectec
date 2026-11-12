abbrev n : Type := Nat

inductive vec (X : Type) : Type
  | mk_vec (X_lst : List X) (v_n : n) : X_lst.length < v_n -> vec X

-- structure Point where
--   x : Nat
--   y : Nat

-- def origin : Point := { x := 0, y := 0 }

-- -- Normal field update by name
-- def moved : Point := { origin with x := 5 }

-- -- Numeric index update (1-based): updates the first field (x)
-- def moved2 : Point := { origin with 1 := 5 }

-- -- Private modifier: places the value in current module's private scope
-- def moved3 : Point := { origin with x := private 42 }

-- #eval moved        -- { x := 5, y := 0 }
-- #eval moved2       -- { x := 5, y := 0 }
-- #eval moved3       -- { x := 42, y := 0 }


structure Y where
  a : Nat

structure C where
  a : Nat

structure B where
  c : C

structure Z where
  y: List Y
  b : B

structure X where
  y : Y
  z : List Z
  b : B

def x1 : X := {
  y := { a := 0 },
  z := [
    {
      y := [
        {a := 1},
        {a := 2},
        {a := 3}
      ],
      b := {
        c := {
          a := 0
        }
      }
    }
  ],
  b := {
    c := {
      a := 0
    }
  }
}
/-
(DotP (DotP (DotP RootP b) c) a)
-/
def x3 := {
  x1 with b := {
    x1.b with c := {
      x1.b.c with a := 10
    }
  }
}

def x4 := {
  x1 with b.c.a := 10
}

def x5 := {
  x1 with z := List.modify x1.z 0 (
    fun ze => {
      ze with y := List.modify ze.y 1 (
        fun ye => { ye with a := 20 }
      )
    }
  )
}

def y := [1,2,3]

/-
(UpdE
  (IdxP RootP 1)
999)

UpdateList {
  name_of_list_to_update = y
  idx = 1
  new_value = Num (LeanNat 999)
}
-/
def y2 := List.modify y 1 (fun ye => 999)

#eval y2 -- [1, 999, 3]


/-

x1.z[0].b.c.a := 20

UpdateStruct {
  struct_to_update = Ident x1
  fields_to_update = [
    AssignedField {
      l_val = Ident z
      is_private = false
      term = UpdateList {
        name_of_list_to_update = DotProj (Ident x1) (Ident z)       // x1.z
        idx = 1
        new_value = UpdateStruct {
          struct_to_update = Ident ze
          fields_to_update = [
            AssignedField {
              l_val = Ident b
              is_private = false
              term = UpdateStruct {
                struct_to_update = DotProj (Ident ze) (Ident b)
                fields_to_update = [
                  AssignedField {
                    l_val = Ident c
                    is_private = false
                    term = UpdateStruct {
                      struct_to_update = DotProj (DotProj (Ident ze) (Ident b)) (Ident c)
                      fields_to_update = [
                        AssignedField {
                          l_val = Ident a
                          is_private = false
                          term = Num (LeanNat 20)
                        }
                      ]
                    }
                  }
                ]
              }
            }
          ]
        }
      }
    }
  ]
}

x1.z[0].b.c.a := 20

(UpdE
  (DotP
    (DotP
      (DotP
        (IdxP
          (DotP RootP (Atom Z))
        0)
      (Atom B))
    (Atom C))
  (Atom A))
20)

RootP             x1

UpdateStruct      DotP (prev) (Atom Z)      | x1

UpdateList        IdxP (prev) 0             | x1.z

                                            | ze

UpdateStruct      DotP (prev) (Atom B)      | ze

UpdateStruct      DotP (prev) (Atom C)      | ze.b

                  DotP (prev) (Atom A)      | ze.b.c

                  20

-/

def x6 := {
  x1 with z := List.modify x1.z 0 (
    fun ze => {
      ze with b := {
        ze.b with c := {
          ze.b.c with a := 20
        }
      }
    }
  )
}

def x7 := {
  x1 with z := List.modify x1.z 0 (
    fun ze => {
      ze with b.c.a := 20
    }
  )
}



def x2 : X := {
  x1 with z := List.modify x1.z 0 (
    fun z => {
      z with y := List.modify z.y 1 (
        fun y => { y with a := 20 }
      )
    }
  )
}





#eval x2.z[0].y[1].a -- 20

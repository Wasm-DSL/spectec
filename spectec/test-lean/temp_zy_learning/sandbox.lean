inductive X : Type where
  | a

inductive Y : Type where
  | b
  | c

inductive Z : Type where
  | d

def f : X → Y
  | X.a => Y.b

def g : Y → Z
  | Y.b => Z.d
  | Y.c => Z.d

def gf : X → Z
  | x => g (f x)

example : Function.Injective gf := by
  unfold Function.Injective
  intro a1 a2 h
  cases a1
  cases a2
  rfl

example : ¬ Function.Injective g := by
  unfold Function.Injective
  intro n
  have h := n (a₁ := Y.b) (a₂ := Y.c)
  have h1 := h rfl
  contradiction


opaque weird_proof : True := trivial
#print weird_proof
-- opaque weird_proof : True          ← no body visible, confirmed sealed, exactly like `five_opaque` before

example : weird_proof = if 1 = 1 then True.intro else True.intro := rfl

def my_rfl {α : Sort u} (a : α) : a = a := Eq.refl a

theorem bleh : 5 = 10-5 := my_rfl 5

inductive MyNat : Type
| zero
| succ (n : MyNat)

def MyNat.sub : MyNat → MyNat → MyNat
| n, .zero => n
| .zero, .succ _ => .zero
| .succ n, .succ m => MyNat.sub n m

def five : MyNat := MyNat.succ (MyNat.succ (MyNat.succ (MyNat.succ (MyNat.succ MyNat.zero))))
def ten : MyNat := MyNat.succ (MyNat.succ (MyNat.succ (MyNat.succ (MyNat.succ (MyNat.succ (MyNat.succ (MyNat.succ (MyNat.succ (MyNat.succ MyNat.zero)))))))))

theorem myBleh : five = MyNat.sub ten five := my_rfl five
example : five = MyNat.sub ten five := rfl

(*
This transformation transforms type families into a single variant user-defined
type. 

This is achieved through the following steps:
  * Transform variant and struct instances of the type family into their own
    user-defined type, using the quantifiers as their respective dependent type arguments.
  * Transform the type family itself as a variant type with many as many cases as there
    were instances before, encoding the pattern matching as equality premises. 
  * Projection functions are made for each instance that go from type family to the
    sub type.
  * Implicit conversions going from type family to sub type and vice-versa are made
    explicit through the use of the constructor and projections made before. This is achieved
    by inspecting the expression and generating its "real type", and match that to the type
    given by elaboration.

As an example,
given the following type family:

syntax foo(p)
syntax foo{v : t}(a) = t_alias(a)
syntax foo{v : t}(b) = | case_1 | case_2 | ... | case_n
syntax foo{v : t}(c) = { field_1, field_2, ... , field_n }

where p is a parameter type, a, b and c are arguments that match their respective parameter type,
v is a quantifier that appears in a, b, and c with type t.

This is transformed into: 

syntax foo_case_2(v : t) = | case_1 | case_2 | ... | case_n
syntax foo_case_3(v : t) = { field_1, field_2, ... , field_n }

syntax foo(p) =
  | foo_make_case_1{v : t, x : t_alias(a)}(v : t, x : t_alias(a))
    -- if a == p
  | foo_make_case_2{v : t, x : foo_case_2(b)}(v : t, x : foo_case_2(b))
    -- if b == p
  | foo_make_case_3{v : t, x : foo_case_3(c)}(v : t, x : foo_case_2(c))
    -- if c == p

an example of the projection function is as follows:

def $proj_foo_case_1(v : t, x : foo(a)) : t_alias(a)?
def $proj_foo_case_1{v : t, x : t_alias(a)}(v, foo_make_case_1(v, x)) = ?(x)
def $proj_foo_case_1{v : t, x : foo(a)}(v, x) = ?()

Names were specifically chosen here for simplicity.
*)

val projection_hint_id : string
val transform : Il.Ast.script -> Il.Ast.script

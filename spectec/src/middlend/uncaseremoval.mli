(*
This transformation focuses on transforming uncase expressions into explicit projection functions.

This is achieved through the following steps:
  * The uncase expressions are collected and placed in a map (as a first pass). This is a map from id
  to a list of mixops.
  * When encountering a user defined type definition, we lookup in the map and generate
  the projection functions accordingly for each mixop in the list. If there is more than one case,
  the projection function returns the case tuple wrapped in an optional type.
  * When encountering an uncase expression, we just simply make the appropriate transformation
  to a function call.

This pass works with/without dependent types. It will simply add the dependent type parameters
to the projection function whenver necessary.

As an example,
given the following type:

syntax foo =
  | A v
  | B c v

where A and B are case constructors, and v c are types.

Assume we have uncase expressions somewhere in our script (with x being a variable of type foo):
(x!A).0 and (x!B).1

This is transformed into: 

syntax foo =
  | A v
  | B c v

def $proj_foo_0(x : foo) : (v)?
  def $proj_foo_0{var : v}(A(var)) = ?(var)
  def $proj_foo_0{var : foo}(var) = ?()

def $proj_foo_1(x : foo) : (c, v)?
  def $proj_foo_0{v_c : c, v_v : v}(B(v_c, v_v)) = ?((v_c, v_v))
  def $proj_foo_0{var : foo}(var) = ?()

with uncase expressions being transformed into:
(the($proj_foo_0(x))).0 and (the($proj_foo_1(x))).1

Names were specifically chosen here for simplicity.
*)

val transform : Il.Ast.script -> Il.Ast.script

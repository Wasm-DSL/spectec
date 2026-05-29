(* 
This pass expands the subtyping patterns that appear in the LHS of
function clauses and type family arguments. 

It achieves this through the following steps:
  * For each argument, we collect every unique sub expression.
  * Then, for each sub expression, we collect every case that is
  possible in the subtype. If the specific case additionally carries
  values, then we generate quants to add in the function scope. 
  * With all of these cases, for each unique sub expression, we compute
  the cartesian product in order to absolutely grab all the possible cases.
  See $cvtop to see how this might be done.
  * Once we have calculated the product, we generate a subst for each product
  and proceed to generate the clause/type instance.
  * Finally, we filter out quants that appear in the subst.

For example, take the following types and function:

syntax A = t1 nat | t2 nat nat
syntax B = t1 nat | t2 nat nat | t3 | t4 

def $foo(B) : nat
def $foo(x : A <: B) = 1
def $foo(t3) = 2
def $foo(t4) = 3

Would be transformed as such:

def $foo(B) : nat
def $foo{n : nat}(t1(n)) = 1
def $foo{n1 : nat, n2 : nat}(t2(n1, n2)) = 1
def $foo(t3) = 2
def $foo(t4) = 3
*)

val transform : Il.Ast.script -> Il.Ast.script

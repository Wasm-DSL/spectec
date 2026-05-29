(*
This transformation separates indexed types into simple types and their corresponding
wellformedness predicate. 

This is achieved through the following steps:
  * Create the wellformedness predicate as a relation that takes in the corresponding
  type, and its dependent type parameters. 
    * For variants, it creates a wellformedness case for each variant case. it supplies
    the premises that the indexed type used to have.
    * For structs/records, it creates a singular case where all premises of all fields
    are checked.
  * For definitions and relations, we collect terms that should have a wellformedness check 
  and add it to the current premise list. This results in wellformedness predicates being
  "bubbled up."
  * Then finally, we traverse through the IL, removing any notion of indexed types.

As an example,
given the following variant indexed type:

syntax foo(v : t) = 
  | CASE{v2 : t}(v2 : t)
  -- if v = v2

where t is an arbitrary type, and v and v2 are terms of type t.

Assume that type t needs a wellformedness check.

This is transformed into: 

syntax foo = 
  | CASE{v2 : t}(v2 : t)

relation wf_foo: `%%`(t, foo)
  rule foo_case_0{v : t, v2 : t}:
    `%%`(v, CASE_foo(v2))
    -- wf_t: `%`(v)
    -- if (v = v2)

This pass requires the typefamilyremoval pass to be ran first, as it ensures that type families are
transformed correctly.
*)

val wf_hint_id : string
val transform : Il.Ast.script -> Il.Ast.script
(*
This transformation replaces SubE expressions with explicit subtype injection
functions.

1. It traverses all expressions and finds out which type pairs
  occur in SubE expressions
  - all type pairs mentioned in SubE expressions
  - for all variant types: list of constructors
  - for all alias types: right hand side of the alias

2. It traverses all definitions to collect information about variant types and
  type aliases (assuming only such types occur in type aliases).

3. It generates explicit injection functions for pairs, and put them in the
right spot (after both types are defined, but outside `RecD` groups)

4. It replaces occurrences of SubE with a suitable CallE

Step 1 and 4 are done together, and step 2 and 3

This pass assumes that there is no name shadowing in the type definitions.
*)

val transform : Il.Ast.script -> Il.Ast.script

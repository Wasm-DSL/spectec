(*
This transformation totalizes partial functions.

Partial functions are recognized by the partial flag hint (for now, inference
would be possible).

The declarations are changed:

 * the return type is wrapped in the option type `?`
 * all clauses rhs' are wrapped in the option type injection `?(…)`
  unless rhs' contains a partial function call itself.
  * For this case, if it is only the partial function itself,
    it just leaves it untouched, as the function already returns
    the option type.
  * If its a more elaborate expression, it wraps the partial function
    in an option iteration.  
 * a catch-all clause is added returning `null` only when there is
    no catch-all clause present.

All calls to such functions are wrapped in option projection `THE e`.

*)

val transform : Il.Ast.script -> Il.Ast.script

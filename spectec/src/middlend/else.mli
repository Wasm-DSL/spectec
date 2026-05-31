(*
This transformation removes uses of the `otherwise` (`ElsePr`) premise from
inductive relations.

It only supports binary relations.

1. It figures out which rules are meant by “otherwise”:

  * All previous rules
  * Excluding those that definitely can’t apply when the present rule applies
    (decided by a simple and conservative comparision of the LHS).

2. It creates an auxillary inductive unary predicate with these rules (LHS only).
  * Note that these rules will be applied a simple naming scheme (just adding a number in front of it)
    For now to resolve naming 

3. It replaces the `ElsePr` with the negation of that rule.

*)

val else_relation_hint_id: string
val transform : Il.Ast.script -> Il.Ast.script

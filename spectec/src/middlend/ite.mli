(*
This pass recongizes when multiple subsequent clauses of a definition share the pattern and have
only boolean premises, and rewrites that to a single clause using if-then-else on the right-hand side.
*)

val transform : Il.Ast.script -> Il.Ast.script
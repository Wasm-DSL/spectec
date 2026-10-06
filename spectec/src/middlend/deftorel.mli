(* When true, only definitions carrying hint(partial) are converted to
   relations; all other functions are left unchanged. *)
val partial_only : bool ref

val transform : Il.Ast.script -> Il.Ast.script
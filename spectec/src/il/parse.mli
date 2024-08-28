val trace : bool ref
val check_ambiguity : bool ref

exception Grammar_unknown

val parse : Ast.script -> string -> string -> (Ast.exp, int * string) result
  (* raises Grammar_unknown *)

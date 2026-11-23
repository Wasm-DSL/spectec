(* 
  This pass simply ensures that there is no ambiguity between any names.

  It does this by creating a massive set of names, separated by the
  different main constructs (i.e. TypD, RelD, DecD, etc.).

  It makes sure that variables don't have the same name as anything else,
  as this could cause shadowing in some cases for ITPs. If it does have
  the same name, then it adds the prefix "v_" until the name is unique.

  For functions, we unsure that they don't have the same name as
  user-defined types and relations. If it does, then it adds the prefix
  "fun_" until the name is unique.
  
*)

val transform : Il.Ast.script -> Il.Ast.script

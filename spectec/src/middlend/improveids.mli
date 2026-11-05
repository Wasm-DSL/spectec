(* 
  This pass simply ensures that there is no ambiguity between any names.

  It does this by creating a massive set of names, separated by the
  different namespaces (i.e. TypD, RelD, DecD, etc.). This is done using
  the existing environment generator that the IL has.

  It makes sure that variables don't have the same name as any other
  namespace, as this could cause shadowing in some cases for ITPs. 
  If it does have the same name, then it adds the prefix 
  "v_".

  For functions, we ensure that they don't have the same name as
  user-defined types and relations. If it does, then it adds the prefix
  "fun_".

  For user-defined types and relations, we make sure that they don't have
  the same name as Atoms. If it does, then it adds the prefix "r_"

  Atoms are considered a namespace as well, and it is made sure that the
  other namespaces don't clash with this one. However, no disambiguation
  is made for Atoms of the same name. This is due to some ITPs having
  already builtin mechanisms to handle this.

  NOTE: This is not a guaranteed name clash avoidance pass, as it has a very
  naive renaming strategy. This will get revisited in the future 
  to ensure that this works for all cases
  but for now it is sufficient.
  
*)

val transform : Il.Ast.script -> Il.Ast.script

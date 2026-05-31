(*
This pass is towards a better representation of otherwise when the only concern are boolean premises. 
This simply takes the original premises of the generated relations and negates them.

The pass performs the following steps:
- It collects all of the generated relations from the otherwise removal pass (#187) 
  and makes a mapping (original relation -> generated relations).
- It then goes through each rule of the original relation and checks if there 
  is a negated relational premise.
- If there is, then we grab the boolean premises of the generated relation and negate them.

Some restrictions of this pass:
- If any premise contains a quantifier that was not present in the original rule's 
  conclusion (the one that had the otherwise), then we do not simplify it. 
  This is due to the quantification being flipped when negating the premise.
- Only works for boolean premises. (Iterated boolean premises would again flip quantification)

Example:

relation Step_pure: admininstr* ~> admininstr*
rule Step_pure/br_if-true:
  (CONST I32 c) (BR_IF l)  ~>  (BR l)
  -- if c =/= 0

rule Step_pure/br_if-false:
  (CONST I32 c) (BR_IF l)  ~>  eps
  -- otherwise

From else pass (omitting wf premises):

relation `Step_pure_before_br_if-false`: `%`(admininstr* )
  rule `br_if-true_0`{c : val_, l : labelidx}:
    `%`([CONST_admininstr(I32_valtype, c) BR_IF_admininstr(l)])
    -- if (!($proj_val__0(c))!`%`_uN.0 =/= 0)
    
relation Step_pure: `%~>%`(admininstr*, admininstr* )
  rule `br_if-true`{c : val_, l : labelidx}:
    `%~>%`([CONST_admininstr(I32_valtype, c) BR_IF_admininstr(l)], [BR_admininstr(l)])
    -- if (!($proj_val__0(c))!`%`_uN.0 =/= 0)

  rule `br_if-false`{c : val_, l : labelidx}:
    `%~>%`([CONST_admininstr(I32_valtype, c) BR_IF_admininstr(l)], [])
    -- ~ `Step_pure_before_br_if-false`: `%`([CONST_admininstr(I32_valtype, c) BR_IF_admininstr(l)])

From else simplification pass:

relation Step_pure: `%~>%`(admininstr*, admininstr* )
  rule `br_if-true`{c : val_, l : labelidx}:
    `%~>%`([CONST_admininstr(I32_valtype, c) BR_IF_admininstr(l)], [BR_admininstr(l)])
    -- if (!($proj_val__0(c))!`%`_uN.0 =/= 0)

  rule `br_if-false`{c : val_, l : labelidx}:
    `%~>%`([CONST_admininstr(I32_valtype, c) BR_IF_admininstr(l)], [])
    -- if (!($proj_val__0(c))!`%`_uN.0 = 0)
*)
    
val transform : Il.Ast.script -> Il.Ast.script

(TypD
  "tag"
  (InstD (VariantT (typcase (Atom SMALL) (TupT)) (typcase (Atom BIG) (TupT))))
)
(TypD "marker" (InstD (VariantT (typcase (Atom X) (TupT)))))
(DecD
  "extra"
  (ExpP "v_tag" (VarT "tag"))
  (IterT (VarT "marker") Opt)
  (DefD (ExpA (CaseE (Atom SMALL) (TupE))) (OptE))
  (DefD (ExpA (CaseE (Atom BIG) (TupE))) (OptE (CaseE (Atom X) (TupE))))
)


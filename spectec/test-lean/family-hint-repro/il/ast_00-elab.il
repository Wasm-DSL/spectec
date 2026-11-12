(TypD
  "numtype"
  (InstD
    (VariantT
      (typcase (Atom I32) (TupT))
      (typcase (Atom I64) (TupT))
      (typcase (Atom F32) (TupT))
      (typcase (Atom F64) (TupT))
    )
  )
)
(TypD "vectype" (InstD (VariantT (typcase (Atom V128) (TupT)))))
(TypD
  "Inn"
  (InstD (VariantT (typcase (Atom I32) (TupT)) (typcase (Atom I64) (TupT))))
)
(TypD
  "Fnn"
  (InstD (VariantT (typcase (Atom F32) (TupT)) (typcase (Atom F64) (TupT))))
)
(TypD "Vnn" (InstD (VariantT (typcase (Atom V128) (TupT)))))
(TypD
  "num_"
  (ExpP "numtype" (VarT "numtype"))
  (InstD
    (ExpP "Inn" (VarT "Inn"))
    (ExpA (SubE (VarT "Inn") (VarT "numtype") (VarE "Inn")))
    (AliasT nat)
  )
  (InstD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (AliasT nat)
  )
)
(TypD
  "vec_"
  (ExpP "vectype" (VarT "vectype"))
  (InstD (ExpP "vectype" (VarT "vectype")) (ExpA (VarE "vectype")) (AliasT nat))
)
(DecD
  "foo"
  (ExpP "numtype" (VarT "numtype"))
  (ExpP "num_" (VarT "num_" (ExpA (VarE "numtype"))))
  (IterT nat List)
)
(HintD (DecH "foo" (hint "builtin" "{}")))
(DecD
  "bar"
  (ExpP "vectype" (VarT "vectype"))
  (ExpP "vec_" (VarT "vec_" (ExpA (VarE "vectype"))))
  (IterT nat List)
)
(HintD (DecH "bar" (hint "builtin" "{}")))


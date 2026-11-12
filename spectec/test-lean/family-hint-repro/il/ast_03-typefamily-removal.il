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
    (ExpP "numtype" (VarT "numtype"))
    (ExpA (VarE "numtype"))
    (VariantT
      (typcase
        (Seq (Atom mk_num__0) Arg Arg)
        (TupT (typbind "Inn" (VarT "Inn")) (typbind "var_x" nat))
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype")
            (SubE (VarT "Inn") (VarT "numtype") (VarE "Inn"))
          )
        )
      )
      (typcase
        (Seq (Atom mk_num__1) Arg Arg)
        (TupT (typbind "Fnn" (VarT "Fnn")) (typbind "var_x" nat))
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype")
            (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))
          )
        )
      )
    )
  )
)
(DecD
  "proj_num__0"
  (ExpP "Inn" (VarT "Inn"))
  (ExpP
    "var_x"
    (VarT "num_" (ExpA (SubE (VarT "Inn") (VarT "numtype") (VarE "Inn"))))
  )
  (IterT nat Opt)
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" nat)
    (ExpA (VarE "Inn"))
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "var_x")))
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP
      "var_x"
      (VarT "num_" (ExpA (SubE (VarT "Inn") (VarT "numtype") (VarE "Inn"))))
    )
    (ExpA (VarE "Inn"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_num__1"
  (ExpP "Fnn" (VarT "Fnn"))
  (ExpP
    "var_x"
    (VarT "num_" (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))))
  )
  (IterT nat Opt)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" nat)
    (ExpA (VarE "Fnn"))
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "var_x")))
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "var_x"
      (VarT "num_" (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))))
    )
    (ExpA (VarE "Fnn"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(HintD (TypH "num_" (hint "type_family" "{}")))
(HintD (DecH "proj_num__0" (hint "tf_projection_func" "{}")))
(HintD (DecH "proj_num__1" (hint "tf_projection_func" "{}")))
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
(HintD (DecH "foo" (hint "partial" "{}")))
(HintD (DecH "foo" (hint "builtin" "{}")))
(DecD
  "bar"
  (ExpP "vectype" (VarT "vectype"))
  (ExpP "vec_" (VarT "vec_" (ExpA (VarE "vectype"))))
  (IterT nat List)
)
(HintD (DecH "bar" (hint "builtin" "{}")))


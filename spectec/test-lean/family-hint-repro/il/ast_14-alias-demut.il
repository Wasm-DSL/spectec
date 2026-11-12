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
(DecD
  "numtype_Inn"
  (ExpP "_" (VarT "Inn"))
  (VarT "numtype")
  (DefD (ExpA (CaseE (Atom I32) (TupE))) (CaseE (Atom I32) (TupE)))
  (DefD (ExpA (CaseE (Atom I64) (TupE))) (CaseE (Atom I64) (TupE)))
)
(TypD
  "Fnn"
  (InstD (VariantT (typcase (Atom F32) (TupT)) (typcase (Atom F64) (TupT))))
)
(DecD
  "numtype_Fnn"
  (ExpP "_" (VarT "Fnn"))
  (VarT "numtype")
  (DefD (ExpA (CaseE (Atom F32) (TupE))) (CaseE (Atom F32) (TupE)))
  (DefD (ExpA (CaseE (Atom F64) (TupE))) (CaseE (Atom F64) (TupE)))
)
(TypD "Vnn" (InstD (VariantT (typcase (Atom V128) (TupT)))))
(TypD
  "num_"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_num__0) Arg Arg)
        (TupT (typbind "Inn" (VarT "Inn")) (typbind "var_x" nat))
      )
      (typcase
        (Seq (Atom mk_num__1) Arg Arg)
        (TupT (typbind "Fnn" (VarT "Fnn")) (typbind "var_x" nat))
      )
    )
  )
)
(RelD
  "wf_num_"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "numtype")) (typbind "_" (VarT "num_")))
  (RuleD
    "num__case_0"
    (ExpP "numtype" (VarT "numtype"))
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" nat)
    (Seq Arg Arg)
    (TupE
      (VarE "numtype")
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "var_x")))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "numtype")
        (CallE "numtype_Inn" (ExpA (VarE "Inn")))
      )
    )
  )
  (RuleD
    "num__case_1"
    (ExpP "numtype" (VarT "numtype"))
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" nat)
    (Seq Arg Arg)
    (TupE
      (VarE "numtype")
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "var_x")))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "numtype")
        (CallE "numtype_Fnn" (ExpA (VarE "Fnn")))
      )
    )
  )
)
(HintD (RelH "wf_num_" (hint "wf-relation" "num_")))
(DecD
  "proj_num__0"
  (ExpP "var_x" (VarT "num_"))
  (IterT nat Opt)
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" nat)
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "var_x")))
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "num_")) (ExpA (VarE "var_x")) (OptE))
)
(DecD
  "proj_num__1"
  (ExpP "var_x" (VarT "num_"))
  (IterT nat Opt)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" nat)
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "var_x")))
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "num_")) (ExpA (VarE "var_x")) (OptE))
)
(HintD (TypH "num_" (hint "type_family" "{}")))
(HintD (DecH "proj_num__0" (hint "tf_projection_func" "{}")))
(HintD (DecH "proj_num__1" (hint "tf_projection_func" "{}")))
(TypD "vec_" (InstD (AliasT nat)))
(DecD
  "foo"
  (ExpP "numtype" (VarT "numtype"))
  (ExpP "num_" (VarT "num_"))
  (IterT (IterT nat List) Opt)
  (DefD
    (ExpP "x0" (VarT "numtype"))
    (ExpP "x1" (VarT "num_"))
    (ExpA (VarE "x0"))
    (ExpA (VarE "x1"))
    (OptE)
    ElsePr
  )
)
(HintD (DecH "foo" (hint "partial" "{}")))
(HintD (DecH "foo" (hint "builtin" "{}")))
(DecD
  "bar"
  (ExpP "vectype" (VarT "vectype"))
  (ExpP "vec_" (VarT "vec_"))
  (IterT nat List)
)
(HintD (DecH "bar" (hint "builtin" "{}")))


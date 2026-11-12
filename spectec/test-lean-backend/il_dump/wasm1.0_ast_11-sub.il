(TypD "MUT" (InstD (VariantT (typcase (Atom MUT) (TupT)))))
(HintD (TypH "MUT" (hint "show" "MUT")))
(TypD "N" (InstD (AliasT nat)))
(HintD (TypH "N" (hint "macro" "{}")))
(TypD "M" (InstD (AliasT nat)))
(HintD (TypH "M" (hint "macro" "{}")))
(TypD "n" (InstD (AliasT nat)))
(HintD (TypH "n" (hint "macro" "{}")))
(TypD "m" (InstD (AliasT nat)))
(HintD (TypH "m" (hint "macro" "{}")))
(DecD "Ki" nat (DefD (NumE (Nat 1024))))
(DecD
  "min"
  (ExpP "nat" nat)
  (ExpP "nat" nat)
  nat
  (DefD
    (ExpP "i" nat)
    (ExpP "j" nat)
    (ExpA (VarE "i"))
    (ExpA (VarE "j"))
    (IfE (CmpE LeOp nat (VarE "i") (VarE "j")) (VarE "i") (VarE "j"))
  )
)
(RecD
  (DecD
    "sum"
    (ExpP "_" (IterT nat List))
    nat
    (DefD (ExpA (ListE)) (NumE (Nat 0)))
    (DefD
      (ExpP "n" nat)
      (ExpP "n'*" (IterT (VarT "n") List))
      (ExpA
        (CatE
          (ListE (VarE "n"))
          (IterE (VarE "n'#1") List (iterexp "n'#1" (VarE "n'*")))
        )
      )
      (BinE
        AddOp
        nat
        (VarE "n")
        (CallE
          "sum"
          (ExpA (IterE (VarE "n'") List (iterexp "n'" (VarE "n'*"))))
        )
      )
    )
  )
)
(DecD
  "opt_"
  (TypP "X")
  (ExpP "_" (IterT (VarT "X") List))
  (IterT (IterT (VarT "X") Opt) Opt)
  (DefD (TypP "X") (TypA (VarT "X")) (ExpA (ListE)) (OptE (OptE)))
  (DefD
    (TypP "X")
    (ExpP "w" (VarT "X"))
    (TypA (VarT "X"))
    (ExpA (ListE (VarE "w")))
    (OptE (OptE (VarE "w")))
  )
  (DefD
    (TypP "X")
    (ExpP "x1" (IterT (VarT "X") List))
    (TypA (VarT "X"))
    (ExpA (VarE "x1"))
    (OptE)
    ElsePr
  )
)
(HintD (DecH "opt_" (hint "show" "%2") (hint "partial" "{}")))
(DecD
  "list_"
  (TypP "X")
  (ExpP "_" (IterT (VarT "X") Opt))
  (IterT (VarT "X") List)
  (DefD (TypP "X") (TypA (VarT "X")) (ExpA (OptE)) (ListE))
  (DefD
    (TypP "X")
    (ExpP "w" (VarT "X"))
    (TypA (VarT "X"))
    (ExpA (OptE (VarE "w")))
    (ListE (VarE "w"))
  )
)
(HintD (DecH "list_" (hint "show" "%2")))
(RecD
  (DecD
    "concat_"
    (TypP "X")
    (ExpP "_" (IterT (IterT (VarT "X") List) List))
    (IterT (VarT "X") List)
    (DefD (TypP "X") (TypA (VarT "X")) (ExpA (ListE)) (ListE))
    (DefD
      (TypP "X")
      (ExpP "w*" (IterT (VarT "X") List))
      (ExpP "w'**" (IterT (IterT (VarT "X") List) List))
      (TypA (VarT "X"))
      (ExpA
        (CatE
          (ListE (IterE (VarE "w#1") List (iterexp "w#1" (VarE "w*"))))
          (IterE
            (IterE (VarE "w'#1") List (iterexp "w'#1" (VarE "w'*#1")))
            List
            (iterexp "w'*#1" (VarE "w'**"))
          )
        )
      )
      (CatE
        (IterE (VarE "w") List (iterexp "w" (VarE "w*")))
        (CallE
          "concat_"
          (TypA (VarT "X"))
          (ExpA
            (IterE
              (IterE (VarE "w'") List (iterexp "w'" (VarE "w'*")))
              List
              (iterexp "w'*" (VarE "w'**"))
            )
          )
        )
      )
    )
  )
)
(HintD (DecH "concat_" (hint "show" "$concat(%2)")))
(RecD
  (DecD
    "disjoint_"
    (TypP "X")
    (ExpP "_" (IterT (VarT "X") List))
    BoolT
    (DefD (TypP "X") (TypA (VarT "X")) (ExpA (ListE)) (BoolE true))
    (DefD
      (TypP "X")
      (ExpP "w" (VarT "X"))
      (ExpP "w'*" (IterT (VarT "X") List))
      (TypA (VarT "X"))
      (ExpA
        (CatE
          (ListE (VarE "w"))
          (IterE (VarE "w'#2") List (iterexp "w'#2" (VarE "w'*")))
        )
      )
      (BinE
        AndOp
        bool
        (UnE
          NotOp
          bool
          (MemE (VarE "w") (IterE (VarE "w'") List (iterexp "w'" (VarE "w'*"))))
        )
        (CallE
          "disjoint_"
          (TypA (VarT "X"))
          (ExpA (IterE (VarE "w'") List (iterexp "w'" (VarE "w'*"))))
        )
      )
    )
  )
)
(HintD (DecH "disjoint_" (hint "show" "{%2 $disjoint}") (hint "macro" "none")))
(TypD
  "list"
  (TypP "X")
  (InstD
    (TypP "X")
    (TypA (VarT "X"))
    (VariantT
      (typcase
        Arg
        (TupT (typbind "X*" (IterT (VarT "X") List)))
        (IfPr
          (CmpE
            LtOp
            nat
            (LenE (IterE (VarE "X") List (iterexp "X" (VarE "X*"))))
            (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 32)))
          )
        )
      )
    )
  )
)
(TypD "byte" (InstD (VariantT (typcase Arg (TupT (typbind "i" nat))))))
(DecD
  "proj_byte_0"
  (ExpP "x" (VarT "byte"))
  (TupT (typbind "_" nat))
  (DefD
    (ExpP "v_num_0" nat)
    (ExpA (CaseE Arg (TupE (VarE "v_num_0"))))
    (TupE (VarE "v_num_0"))
  )
)
(HintD (DecH "proj_byte_0" (hint "uncase-proj-func" "{}")))
(RelD
  "wf_byte"
  (Seq Arg)
  (TupT (typbind "_" (VarT "byte")))
  (RuleD
    "byte_case_0"
    (ExpP "i" nat)
    (Seq Arg)
    (TupE (CaseE Arg (TupE (VarE "i"))))
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE GeOp nat (VarE "i") (NumE (Nat 0)))
        (CmpE LeOp nat (VarE "i") (NumE (Nat 255)))
      )
    )
  )
)
(HintD (RelH "wf_byte" (hint "wf-relation" "byte")))
(HintD (TypH "byte" (hint "desc" "\"byte\"")))
(TypD "uN" (InstD (VariantT (typcase Arg (TupT (typbind "i" nat))))))
(DecD
  "proj_uN_0"
  (ExpP "x" (VarT "uN"))
  (TupT (typbind "_" nat))
  (DefD
    (ExpP "v_num_0" nat)
    (ExpA (CaseE Arg (TupE (VarE "v_num_0"))))
    (TupE (VarE "v_num_0"))
  )
)
(HintD (DecH "proj_uN_0" (hint "uncase-proj-func" "{}")))
(RelD
  "wf_uN"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "N")) (typbind "_" (VarT "uN")))
  (RuleD
    "uN_case_0"
    (ExpP "N" (VarT "N"))
    (ExpP "i" nat)
    (Seq Arg Arg)
    (TupE (VarE "N") (CaseE Arg (TupE (VarE "i"))))
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE GeOp nat (VarE "i") (NumE (Nat 0)))
        (CmpE
          LeOp
          nat
          (VarE "i")
          (CvtE
            int
            nat
            (BinE
              SubOp
              int
              (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (VarE "N")))
              (CvtE nat int (NumE (Nat 1)))
            )
          )
        )
      )
    )
  )
)
(HintD (RelH "wf_uN" (hint "wf-relation" "uN")))
(HintD (TypH "uN" (hint "desc" "\"unsigned integer\"") (hint "show" "u#%")))
(TypD "sN" (InstD (VariantT (typcase Arg (TupT (typbind "i" int))))))
(DecD
  "proj_sN_0"
  (ExpP "x" (VarT "sN"))
  (TupT (typbind "_" int))
  (DefD
    (ExpP "v_num_0" int)
    (ExpA (CaseE Arg (TupE (VarE "v_num_0"))))
    (TupE (VarE "v_num_0"))
  )
)
(HintD (DecH "proj_sN_0" (hint "uncase-proj-func" "{}")))
(RelD
  "wf_sN"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "N")) (typbind "_" (VarT "sN")))
  (RuleD
    "sN_case_0"
    (ExpP "N" (VarT "N"))
    (ExpP "i" int)
    (Seq Arg Arg)
    (TupE (VarE "N") (CaseE Arg (TupE (VarE "i"))))
    (IfPr
      (BinE
        OrOp
        bool
        (BinE
          OrOp
          bool
          (BinE
            AndOp
            bool
            (CmpE
              GeOp
              int
              (VarE "i")
              (UnE
                MinusOp
                int
                (CvtE
                  nat
                  int
                  (BinE
                    PowOp
                    nat
                    (NumE (Nat 2))
                    (CvtE
                      int
                      nat
                      (BinE
                        SubOp
                        int
                        (CvtE nat int (VarE "N"))
                        (CvtE nat int (NumE (Nat 1)))
                      )
                    )
                  )
                )
              )
            )
            (CmpE
              LeOp
              int
              (VarE "i")
              (UnE MinusOp int (CvtE nat int (NumE (Nat 1))))
            )
          )
          (CmpE EqOp bool (VarE "i") (CvtE nat int (NumE (Nat 0))))
        )
        (BinE
          AndOp
          bool
          (CmpE
            GeOp
            int
            (VarE "i")
            (UnE PlusOp int (CvtE nat int (NumE (Nat 1))))
          )
          (CmpE
            LeOp
            int
            (VarE "i")
            (BinE
              SubOp
              int
              (CvtE
                nat
                int
                (BinE
                  PowOp
                  nat
                  (NumE (Nat 2))
                  (CvtE
                    int
                    nat
                    (BinE
                      SubOp
                      int
                      (CvtE nat int (VarE "N"))
                      (CvtE nat int (NumE (Nat 1)))
                    )
                  )
                )
              )
              (CvtE nat int (NumE (Nat 1)))
            )
          )
        )
      )
    )
  )
)
(HintD (RelH "wf_sN" (hint "wf-relation" "sN")))
(HintD (TypH "sN" (hint "desc" "\"signed integer\"") (hint "show" "s#%")))
(TypD "iN" (InstD (AliasT (VarT "uN"))))
(HintD (TypH "iN" (hint "desc" "\"integer\"") (hint "show" "i#%")))
(TypD "u31" (InstD (AliasT (VarT "uN"))))
(TypD "u32" (InstD (AliasT (VarT "uN"))))
(TypD "u64" (InstD (AliasT (VarT "uN"))))
(TypD "i32" (InstD (AliasT (VarT "iN"))))
(TypD "i64" (InstD (AliasT (VarT "iN"))))
(DecD
  "signif"
  (ExpP "N" (VarT "N"))
  (IterT nat Opt)
  (DefD (ExpA (NumE (Nat 32))) (OptE (NumE (Nat 23))))
  (DefD (ExpA (NumE (Nat 64))) (OptE (NumE (Nat 52))))
  (DefD (ExpP "x0" (VarT "N")) (ExpA (VarE "x0")) (OptE) ElsePr)
)
(HintD (DecH "signif" (hint "partial" "{}")))
(DecD
  "expon"
  (ExpP "N" (VarT "N"))
  (IterT nat Opt)
  (DefD (ExpA (NumE (Nat 32))) (OptE (NumE (Nat 8))))
  (DefD (ExpA (NumE (Nat 64))) (OptE (NumE (Nat 11))))
  (DefD (ExpP "x0" (VarT "N")) (ExpA (VarE "x0")) (OptE) ElsePr)
)
(HintD (DecH "expon" (hint "partial" "{}")))
(DecD
  "M"
  (ExpP "N" (VarT "N"))
  nat
  (DefD
    (ExpP "N" nat)
    (ExpA (VarE "N"))
    (TheE (CallE "signif" (ExpA (VarE "N"))))
  )
)
(HintD (DecH "M" (hint "show" "M")))
(DecD
  "E"
  (ExpP "N" (VarT "N"))
  nat
  (DefD
    (ExpP "N" nat)
    (ExpA (VarE "N"))
    (TheE (CallE "expon" (ExpA (VarE "N"))))
  )
)
(HintD (DecH "E" (hint "show" "E")))
(TypD "exp" (InstD (AliasT int)))
(TypD
  "fNmag"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom NORM) Arg Arg)
        (TupT (typbind "m" (VarT "m")) (typbind "exp" (VarT "exp")))
      )
      (typcase
        (Seq (Atom SUBNORM) Arg)
        (TupT (typbind "m" (VarT "m")))
        (ExpP "exp" (VarT "exp"))
      )
      (typcase (Atom INF) (TupT))
      (typcase (Seq (Atom NAN) Arg) (TupT (typbind "m" (VarT "m"))))
    )
  )
)
(RelD
  "wf_fNmag"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "N")) (typbind "_" (VarT "fNmag")))
  (RuleD
    "fNmag_case_0"
    (ExpP "N" (VarT "N"))
    (ExpP "m" (VarT "m"))
    (ExpP "exp" (VarT "exp"))
    (Seq Arg Arg)
    (TupE
      (VarE "N")
      (CaseE (Seq (Atom NORM) Arg Arg) (TupE (VarE "m") (VarE "exp")))
    )
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE
          LtOp
          nat
          (VarE "m")
          (BinE PowOp nat (NumE (Nat 2)) (CallE "M" (ExpA (VarE "N"))))
        )
        (BinE
          AndOp
          bool
          (CmpE
            LeOp
            int
            (BinE
              SubOp
              int
              (CvtE nat int (NumE (Nat 2)))
              (CvtE
                nat
                int
                (BinE
                  PowOp
                  nat
                  (NumE (Nat 2))
                  (CvtE
                    int
                    nat
                    (BinE
                      SubOp
                      int
                      (CvtE nat int (CallE "E" (ExpA (VarE "N"))))
                      (CvtE nat int (NumE (Nat 1)))
                    )
                  )
                )
              )
            )
            (VarE "exp")
          )
          (CmpE
            LeOp
            int
            (VarE "exp")
            (BinE
              SubOp
              int
              (CvtE
                nat
                int
                (BinE
                  PowOp
                  nat
                  (NumE (Nat 2))
                  (CvtE
                    int
                    nat
                    (BinE
                      SubOp
                      int
                      (CvtE nat int (CallE "E" (ExpA (VarE "N"))))
                      (CvtE nat int (NumE (Nat 1)))
                    )
                  )
                )
              )
              (CvtE nat int (NumE (Nat 1)))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fNmag_case_1"
    (ExpP "N" (VarT "N"))
    (ExpP "exp" (VarT "exp"))
    (ExpP "m" (VarT "m"))
    (Seq Arg Arg)
    (TupE (VarE "N") (CaseE (Seq (Atom SUBNORM) Arg) (TupE (VarE "m"))))
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE
          LtOp
          nat
          (VarE "m")
          (BinE PowOp nat (NumE (Nat 2)) (CallE "M" (ExpA (VarE "N"))))
        )
        (CmpE
          EqOp
          bool
          (BinE
            SubOp
            int
            (CvtE nat int (NumE (Nat 2)))
            (CvtE
              nat
              int
              (BinE
                PowOp
                nat
                (NumE (Nat 2))
                (CvtE
                  int
                  nat
                  (BinE
                    SubOp
                    int
                    (CvtE nat int (CallE "E" (ExpA (VarE "N"))))
                    (CvtE nat int (NumE (Nat 1)))
                  )
                )
              )
            )
          )
          (VarE "exp")
        )
      )
    )
  )
  (RuleD
    "fNmag_case_2"
    (ExpP "N" (VarT "N"))
    (Seq Arg Arg)
    (TupE (VarE "N") (CaseE (Atom INF) (TupE)))
  )
  (RuleD
    "fNmag_case_3"
    (ExpP "N" (VarT "N"))
    (ExpP "m" (VarT "m"))
    (Seq Arg Arg)
    (TupE (VarE "N") (CaseE (Seq (Atom NAN) Arg) (TupE (VarE "m"))))
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE LeOp nat (NumE (Nat 1)) (VarE "m"))
        (CmpE
          LtOp
          nat
          (VarE "m")
          (BinE PowOp nat (NumE (Nat 2)) (CallE "M" (ExpA (VarE "N"))))
        )
      )
    )
  )
)
(HintD (RelH "wf_fNmag" (hint "wf-relation" "fNmag")))
(TypD
  "fN"
  (InstD
    (VariantT
      (typcase (Seq (Atom POS) Arg) (TupT (typbind "_" (VarT "fNmag"))))
      (typcase (Seq (Atom NEG) Arg) (TupT (typbind "_" (VarT "fNmag"))))
    )
  )
)
(RelD
  "wf_fN"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "N")) (typbind "_" (VarT "fN")))
  (RuleD
    "fN_case_0"
    (ExpP "N" (VarT "N"))
    (ExpP "var_0" (VarT "fNmag"))
    (Seq Arg Arg)
    (TupE (VarE "N") (CaseE (Seq (Atom POS) Arg) (TupE (VarE "var_0"))))
    (RulePr "wf_fNmag" (Seq Arg Arg) (TupE (VarE "N") (VarE "var_0")))
  )
  (RuleD
    "fN_case_1"
    (ExpP "N" (VarT "N"))
    (ExpP "var_0" (VarT "fNmag"))
    (Seq Arg Arg)
    (TupE (VarE "N") (CaseE (Seq (Atom NEG) Arg) (TupE (VarE "var_0"))))
    (RulePr "wf_fNmag" (Seq Arg Arg) (TupE (VarE "N") (VarE "var_0")))
  )
)
(HintD (RelH "wf_fN" (hint "wf-relation" "fN")))
(HintD
  (TypH "fN" (hint "desc" "\"floating-point number\"") (hint "show" "f#%"))
)
(HintD (TypH "exp" (hint "show" "e")))
(HintD
  (TypH
    "fNmag"
    (hint "desc" "\"floating-point magnitude\"")
    (hint "show" "fNmag")
  )
)
(TypD "f32" (InstD (AliasT (VarT "fN"))))
(TypD "f64" (InstD (AliasT (VarT "fN"))))
(DecD
  "fzero"
  (ExpP "N" (VarT "N"))
  (VarT "fN")
  (DefD
    (ExpP "N" nat)
    (ExpA (VarE "N"))
    (CaseE
      (Seq (Atom POS) Arg)
      (TupE (CaseE (Seq (Atom SUBNORM) Arg) (TupE (NumE (Nat 0)))))
    )
    (RulePr
      "wf_fN"
      (Seq Arg Arg)
      (TupE
        (VarE "N")
        (CaseE
          (Seq (Atom POS) Arg)
          (TupE (CaseE (Seq (Atom SUBNORM) Arg) (TupE (NumE (Nat 0)))))
        )
      )
    )
  )
)
(HintD (DecH "fzero" (hint "show" "+ 0")))
(DecD
  "fone"
  (ExpP "N" (VarT "N"))
  (VarT "fN")
  (DefD
    (ExpP "N" nat)
    (ExpA (VarE "N"))
    (CaseE
      (Seq (Atom POS) Arg)
      (TupE
        (CaseE
          (Seq (Atom NORM) Arg Arg)
          (TupE (NumE (Nat 1)) (CvtE nat int (NumE (Nat 0))))
        )
      )
    )
    (RulePr
      "wf_fN"
      (Seq Arg Arg)
      (TupE
        (VarE "N")
        (CaseE
          (Seq (Atom POS) Arg)
          (TupE
            (CaseE
              (Seq (Atom NORM) Arg Arg)
              (TupE (NumE (Nat 1)) (CvtE nat int (NumE (Nat 0))))
            )
          )
        )
      )
    )
  )
)
(HintD (DecH "fone" (hint "show" "+ 1")))
(DecD
  "canon_"
  (ExpP "N" (VarT "N"))
  nat
  (DefD
    (ExpP "N" nat)
    (ExpA (VarE "N"))
    (BinE
      PowOp
      nat
      (NumE (Nat 2))
      (CvtE
        int
        nat
        (BinE
          SubOp
          int
          (CvtE nat int (TheE (CallE "signif" (ExpA (VarE "N")))))
          (CvtE nat int (NumE (Nat 1)))
        )
      )
    )
  )
)
(TypD "char" (InstD (VariantT (typcase Arg (TupT (typbind "i" nat))))))
(DecD
  "proj_char_0"
  (ExpP "x" (VarT "char"))
  (TupT (typbind "_" nat))
  (DefD
    (ExpP "v_num_0" nat)
    (ExpA (CaseE Arg (TupE (VarE "v_num_0"))))
    (TupE (VarE "v_num_0"))
  )
)
(HintD (DecH "proj_char_0" (hint "uncase-proj-func" "{}")))
(RelD
  "wf_char"
  (Seq Arg)
  (TupT (typbind "_" (VarT "char")))
  (RuleD
    "char_case_0"
    (ExpP "i" nat)
    (Seq Arg)
    (TupE (CaseE Arg (TupE (VarE "i"))))
    (IfPr
      (BinE
        OrOp
        bool
        (BinE
          AndOp
          bool
          (CmpE GeOp nat (VarE "i") (NumE (Nat 0)))
          (CmpE LeOp nat (VarE "i") (NumE (Nat 55295)))
        )
        (BinE
          AndOp
          bool
          (CmpE GeOp nat (VarE "i") (NumE (Nat 57344)))
          (CmpE LeOp nat (VarE "i") (NumE (Nat 1114111)))
        )
      )
    )
  )
)
(HintD (RelH "wf_char" (hint "wf-relation" "char")))
(HintD (TypH "char" (hint "desc" "\"character\"")))
(RecD
  (DecD
    "utf8"
    (ExpP "_" (IterT (VarT "char") List))
    (IterT (VarT "byte") List)
    (DefD
      (ExpP "ch" (VarT "char"))
      (ExpP "b" (VarT "byte"))
      (ExpA (ListE (VarE "ch")))
      (ListE (VarE "b"))
      (IfPr
        (BinE
          AndOp
          bool
          (CmpE
            LtOp
            nat
            (ProjE (CallE "proj_char_0" (ExpA (VarE "ch"))) 0)
            (NumE (Nat 128))
          )
          (CmpE
            EqOp
            bool
            (CaseE
              Arg
              (TupE (ProjE (CallE "proj_char_0" (ExpA (VarE "ch"))) 0))
            )
            (VarE "b")
          )
        )
      )
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "b")))
      (RulePr
        "wf_byte"
        (Seq Arg)
        (TupE
          (CaseE Arg (TupE (ProjE (CallE "proj_char_0" (ExpA (VarE "ch"))) 0)))
        )
      )
    )
    (DefD
      (ExpP "ch" (VarT "char"))
      (ExpP "b_1" (VarT "byte"))
      (ExpP "b_2" (VarT "byte"))
      (ExpA (ListE (VarE "ch")))
      (ListE (VarE "b_1") (VarE "b_2"))
      (IfPr
        (BinE
          AndOp
          bool
          (BinE
            AndOp
            bool
            (CmpE
              LeOp
              nat
              (NumE (Nat 128))
              (ProjE (CallE "proj_char_0" (ExpA (VarE "ch"))) 0)
            )
            (CmpE
              LtOp
              nat
              (ProjE (CallE "proj_char_0" (ExpA (VarE "ch"))) 0)
              (NumE (Nat 2048))
            )
          )
          (CmpE
            EqOp
            bool
            (ProjE (CallE "proj_char_0" (ExpA (VarE "ch"))) 0)
            (BinE
              AddOp
              nat
              (BinE
                MulOp
                nat
                (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 6)))
                (CvtE
                  int
                  nat
                  (BinE
                    SubOp
                    int
                    (CvtE
                      nat
                      int
                      (ProjE (CallE "proj_byte_0" (ExpA (VarE "b_1"))) 0)
                    )
                    (CvtE nat int (NumE (Nat 192)))
                  )
                )
              )
              (CvtE
                int
                nat
                (BinE
                  SubOp
                  int
                  (CvtE
                    nat
                    int
                    (ProjE (CallE "proj_byte_0" (ExpA (VarE "b_2"))) 0)
                  )
                  (CvtE nat int (NumE (Nat 128)))
                )
              )
            )
          )
        )
      )
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "b_1")))
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "b_2")))
    )
    (DefD
      (ExpP "ch" (VarT "char"))
      (ExpP "b_1" (VarT "byte"))
      (ExpP "b_2" (VarT "byte"))
      (ExpP "b_3" (VarT "byte"))
      (ExpA (ListE (VarE "ch")))
      (ListE (VarE "b_1") (VarE "b_2") (VarE "b_3"))
      (IfPr
        (BinE
          AndOp
          bool
          (BinE
            OrOp
            bool
            (BinE
              AndOp
              bool
              (CmpE
                LeOp
                nat
                (NumE (Nat 2048))
                (ProjE (CallE "proj_char_0" (ExpA (VarE "ch"))) 0)
              )
              (CmpE
                LtOp
                nat
                (ProjE (CallE "proj_char_0" (ExpA (VarE "ch"))) 0)
                (NumE (Nat 55296))
              )
            )
            (BinE
              AndOp
              bool
              (CmpE
                LeOp
                nat
                (NumE (Nat 57344))
                (ProjE (CallE "proj_char_0" (ExpA (VarE "ch"))) 0)
              )
              (CmpE
                LtOp
                nat
                (ProjE (CallE "proj_char_0" (ExpA (VarE "ch"))) 0)
                (NumE (Nat 65536))
              )
            )
          )
          (CmpE
            EqOp
            bool
            (ProjE (CallE "proj_char_0" (ExpA (VarE "ch"))) 0)
            (BinE
              AddOp
              nat
              (BinE
                AddOp
                nat
                (BinE
                  MulOp
                  nat
                  (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 12)))
                  (CvtE
                    int
                    nat
                    (BinE
                      SubOp
                      int
                      (CvtE
                        nat
                        int
                        (ProjE (CallE "proj_byte_0" (ExpA (VarE "b_1"))) 0)
                      )
                      (CvtE nat int (NumE (Nat 224)))
                    )
                  )
                )
                (BinE
                  MulOp
                  nat
                  (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 6)))
                  (CvtE
                    int
                    nat
                    (BinE
                      SubOp
                      int
                      (CvtE
                        nat
                        int
                        (ProjE (CallE "proj_byte_0" (ExpA (VarE "b_2"))) 0)
                      )
                      (CvtE nat int (NumE (Nat 128)))
                    )
                  )
                )
              )
              (CvtE
                int
                nat
                (BinE
                  SubOp
                  int
                  (CvtE
                    nat
                    int
                    (ProjE (CallE "proj_byte_0" (ExpA (VarE "b_3"))) 0)
                  )
                  (CvtE nat int (NumE (Nat 128)))
                )
              )
            )
          )
        )
      )
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "b_1")))
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "b_2")))
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "b_3")))
    )
    (DefD
      (ExpP "ch" (VarT "char"))
      (ExpP "b_1" (VarT "byte"))
      (ExpP "b_2" (VarT "byte"))
      (ExpP "b_3" (VarT "byte"))
      (ExpP "b_4" (VarT "byte"))
      (ExpA (ListE (VarE "ch")))
      (ListE (VarE "b_1") (VarE "b_2") (VarE "b_3") (VarE "b_4"))
      (IfPr
        (BinE
          AndOp
          bool
          (BinE
            AndOp
            bool
            (CmpE
              LeOp
              nat
              (NumE (Nat 65536))
              (ProjE (CallE "proj_char_0" (ExpA (VarE "ch"))) 0)
            )
            (CmpE
              LtOp
              nat
              (ProjE (CallE "proj_char_0" (ExpA (VarE "ch"))) 0)
              (NumE (Nat 69632))
            )
          )
          (CmpE
            EqOp
            bool
            (ProjE (CallE "proj_char_0" (ExpA (VarE "ch"))) 0)
            (BinE
              AddOp
              nat
              (BinE
                AddOp
                nat
                (BinE
                  AddOp
                  nat
                  (BinE
                    MulOp
                    nat
                    (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 18)))
                    (CvtE
                      int
                      nat
                      (BinE
                        SubOp
                        int
                        (CvtE
                          nat
                          int
                          (ProjE (CallE "proj_byte_0" (ExpA (VarE "b_1"))) 0)
                        )
                        (CvtE nat int (NumE (Nat 240)))
                      )
                    )
                  )
                  (BinE
                    MulOp
                    nat
                    (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 12)))
                    (CvtE
                      int
                      nat
                      (BinE
                        SubOp
                        int
                        (CvtE
                          nat
                          int
                          (ProjE (CallE "proj_byte_0" (ExpA (VarE "b_2"))) 0)
                        )
                        (CvtE nat int (NumE (Nat 128)))
                      )
                    )
                  )
                )
                (BinE
                  MulOp
                  nat
                  (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 6)))
                  (CvtE
                    int
                    nat
                    (BinE
                      SubOp
                      int
                      (CvtE
                        nat
                        int
                        (ProjE (CallE "proj_byte_0" (ExpA (VarE "b_3"))) 0)
                      )
                      (CvtE nat int (NumE (Nat 128)))
                    )
                  )
                )
              )
              (CvtE
                int
                nat
                (BinE
                  SubOp
                  int
                  (CvtE
                    nat
                    int
                    (ProjE (CallE "proj_byte_0" (ExpA (VarE "b_4"))) 0)
                  )
                  (CvtE nat int (NumE (Nat 128)))
                )
              )
            )
          )
        )
      )
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "b_1")))
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "b_2")))
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "b_3")))
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "b_4")))
    )
    (DefD
      (ExpP "ch*" (IterT (VarT "char") List))
      (ExpA (IterE (VarE "ch#1") List (iterexp "ch#1" (VarE "ch*"))))
      (CallE
        "concat_"
        (TypA (VarT "byte"))
        (ExpA
          (IterE
            (CallE "utf8" (ExpA (ListE (VarE "ch"))))
            List
            (iterexp "ch" (VarE "ch*"))
          )
        )
      )
      (IterPr
        (RulePr "wf_byte" (Seq Arg) (TupE (VarE "iter#1")))
        List
        (iterexp
          "iter#1"
          (CallE
            "concat_"
            (TypA (VarT "byte"))
            (ExpA
              (IterE
                (CallE "utf8" (ExpA (ListE (VarE "ch#2"))))
                List
                (iterexp "ch#2" (VarE "ch*"))
              )
            )
          )
        )
      )
      (IterPr
        (IterPr
          (RulePr "wf_byte" (Seq Arg) (TupE (VarE "iter#2")))
          List
          (iterexp "iter#2" (CallE "utf8" (ExpA (ListE (VarE "ch#3")))))
        )
        List
        (iterexp "ch#3" (VarE "ch*"))
      )
    )
  )
)
(TypD
  "name"
  (InstD
    (VariantT (typcase Arg (TupT (typbind "char*" (IterT (VarT "char") List)))))
  )
)
(DecD
  "proj_name_0"
  (ExpP "x" (VarT "name"))
  (TupT (typbind "_" (IterT (VarT "char") List)))
  (DefD
    (ExpP "v_char_list_0" (IterT (VarT "char") List))
    (ExpA (CaseE Arg (TupE (VarE "v_char_list_0"))))
    (TupE (VarE "v_char_list_0"))
  )
)
(HintD (DecH "proj_name_0" (hint "uncase-proj-func" "{}")))
(RelD
  "wf_name"
  (Seq Arg)
  (TupT (typbind "_" (VarT "name")))
  (RuleD
    "name_case_0"
    (ExpP "char*" (IterT (VarT "char") List))
    (Seq Arg)
    (TupE (CaseE Arg (TupE (VarE "char*"))))
    (IterPr
      (RulePr "wf_char" (Seq Arg) (TupE (VarE "char")))
      List
      (iterexp "char" (VarE "char*"))
    )
    (IfPr
      (CmpE
        LtOp
        nat
        (LenE
          (CallE
            "utf8"
            (ExpA (IterE (VarE "char") List (iterexp "char" (VarE "char*"))))
          )
        )
        (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 32)))
      )
    )
  )
)
(HintD (RelH "wf_name" (hint "wf-relation" "name")))
(HintD (TypH "name" (hint "desc" "\"name\"")))
(TypD "idx" (InstD (AliasT (VarT "u32"))))
(HintD (TypH "idx" (hint "desc" "\"index\"")))
(TypD "typeidx" (InstD (AliasT (VarT "idx"))))
(HintD (TypH "typeidx" (hint "desc" "\"type index\"")))
(TypD "funcidx" (InstD (AliasT (VarT "idx"))))
(HintD (TypH "funcidx" (hint "desc" "\"function index\"")))
(TypD "globalidx" (InstD (AliasT (VarT "idx"))))
(HintD (TypH "globalidx" (hint "desc" "\"global index\"")))
(TypD "tableidx" (InstD (AliasT (VarT "idx"))))
(HintD (TypH "tableidx" (hint "desc" "\"table index\"")))
(TypD "memidx" (InstD (AliasT (VarT "idx"))))
(HintD (TypH "memidx" (hint "desc" "\"memory index\"")))
(TypD "labelidx" (InstD (AliasT (VarT "idx"))))
(HintD (TypH "labelidx" (hint "desc" "\"label index\"")))
(TypD "localidx" (InstD (AliasT (VarT "idx"))))
(HintD (TypH "localidx" (hint "desc" "\"local index\"")))
(TypD
  "valtype"
  (InstD
    (VariantT
      (typcase (Atom I32) (TupT))
      (typcase (Atom I64) (TupT))
      (typcase (Atom F32) (TupT))
      (typcase (Atom F64) (TupT))
    )
  )
)
(HintD (TypH "valtype" (hint "desc" "\"number type\"")))
(TypD
  "Inn"
  (InstD (VariantT (typcase (Atom I32) (TupT)) (typcase (Atom I64) (TupT))))
)
(DecD
  "valtype_Inn"
  (ExpP "_" (VarT "Inn"))
  (VarT "valtype")
  (DefD (ExpA (CaseE (Atom I32) (TupE))) (CaseE (Atom I32) (TupE)))
  (DefD (ExpA (CaseE (Atom I64) (TupE))) (CaseE (Atom I64) (TupE)))
)
(HintD (TypH "Inn" (hint "show" "I#n")))
(TypD
  "Fnn"
  (InstD (VariantT (typcase (Atom F32) (TupT)) (typcase (Atom F64) (TupT))))
)
(DecD
  "valtype_Fnn"
  (ExpP "_" (VarT "Fnn"))
  (VarT "valtype")
  (DefD (ExpA (CaseE (Atom F32) (TupE))) (CaseE (Atom F32) (TupE)))
  (DefD (ExpA (CaseE (Atom F64) (TupE))) (CaseE (Atom F64) (TupE)))
)
(HintD (TypH "Fnn" (hint "show" "F#n")))
(TypD "resulttype" (InstD (AliasT (IterT (VarT "valtype") Opt))))
(HintD (TypH "resulttype" (hint "desc" "\"result type\"")))
(TypD "mut" (InstD (AliasT (IterT (VarT "MUT") Opt))))
(TypD
  "limits"
  (InstD
    (VariantT
      (typcase
        (Brack [ (Infix Arg .. Arg) ])
        (TupT
          (typbind "u32" (VarT "u32"))
          (typbind "u32?" (IterT (VarT "u32") Opt))
        )
      )
    )
  )
)
(RelD
  "wf_limits"
  (Seq Arg)
  (TupT (typbind "_" (VarT "limits")))
  (RuleD
    "limits_case_0"
    (ExpP "u32" (VarT "u32"))
    (ExpP "u32?" (IterT (VarT "u32") Opt))
    (Seq Arg)
    (TupE
      (CaseE (Brack [ (Infix Arg .. Arg) ]) (TupE (VarE "u32") (VarE "u32?")))
    )
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "u32")))
    (IterPr
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "u32")))
      Opt
      (iterexp "u32" (VarE "u32?"))
    )
  )
)
(HintD (RelH "wf_limits" (hint "wf-relation" "limits")))
(HintD (TypH "limits" (hint "desc" "\"limits\"")))
(TypD
  "globaltype"
  (InstD
    (VariantT
      (typcase
        (Seq Arg Arg)
        (TupT (typbind "mut" (VarT "mut")) (typbind "valtype" (VarT "valtype")))
      )
    )
  )
)
(HintD (TypH "globaltype" (hint "desc" "\"global type\"")))
(TypD
  "functype"
  (InstD
    (VariantT
      (typcase
        (Infix Arg -> Arg)
        (TupT
          (typbind "valtype*" (IterT (VarT "valtype") List))
          (typbind "valtype*" (IterT (VarT "valtype") List))
        )
      )
    )
  )
)
(HintD (TypH "functype" (hint "desc" "\"function type\"")))
(TypD "tabletype" (InstD (AliasT (VarT "limits"))))
(HintD (TypH "tabletype" (hint "desc" "\"table type\"")))
(TypD "memtype" (InstD (AliasT (VarT "limits"))))
(HintD (TypH "memtype" (hint "desc" "\"memory type\"")))
(TypD
  "externtype"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom FUNC) Arg)
        (TupT (typbind "functype" (VarT "functype")))
      )
      (typcase
        (Seq (Atom GLOBAL) Arg)
        (TupT (typbind "globaltype" (VarT "globaltype")))
      )
      (typcase
        (Seq (Atom TABLE) Arg)
        (TupT (typbind "tabletype" (VarT "tabletype")))
      )
      (typcase (Seq (Atom MEM) Arg) (TupT (typbind "memtype" (VarT "memtype"))))
    )
  )
)
(RelD
  "wf_externtype"
  (Seq Arg)
  (TupT (typbind "_" (VarT "externtype")))
  (RuleD
    "externtype_case_0"
    (ExpP "functype" (VarT "functype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "functype"))))
  )
  (RuleD
    "externtype_case_1"
    (ExpP "globaltype" (VarT "globaltype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "globaltype"))))
  )
  (RuleD
    "externtype_case_2"
    (ExpP "tabletype" (VarT "tabletype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tabletype"))))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "tabletype")))
  )
  (RuleD
    "externtype_case_3"
    (ExpP "memtype" (VarT "memtype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "memtype"))))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "memtype")))
  )
)
(HintD (RelH "wf_externtype" (hint "wf-relation" "externtype")))
(HintD (TypH "externtype" (hint "desc" "\"external type\"")))
(DecD
  "size"
  (ExpP "valtype" (VarT "valtype"))
  nat
  (DefD (ExpA (CaseE (Atom I32) (TupE))) (NumE (Nat 32)))
  (DefD (ExpA (CaseE (Atom I64) (TupE))) (NumE (Nat 64)))
  (DefD (ExpA (CaseE (Atom F32) (TupE))) (NumE (Nat 32)))
  (DefD (ExpA (CaseE (Atom F64) (TupE))) (NumE (Nat 64)))
)
(HintD (DecH "size" (hint "show" "|%|")))
(TypD
  "val_"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_val__0) Arg Arg)
        (TupT (typbind "Inn" (VarT "Inn")) (typbind "var_x" (VarT "iN")))
      )
      (typcase
        (Seq (Atom mk_val__1) Arg Arg)
        (TupT (typbind "Fnn" (VarT "Fnn")) (typbind "var_x" (VarT "fN")))
      )
    )
  )
)
(RelD
  "wf_val_"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "valtype")) (typbind "_" (VarT "val_")))
  (RuleD
    "val__case_0"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "iN"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE (Seq (Atom mk_val__0) Arg Arg) (TupE (VarE "Inn") (VarE "var_x")))
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (CallE "size" (ExpA (CallE "valtype_Inn" (ExpA (VarE "Inn")))))
        (VarE "var_x")
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Inn" (ExpA (VarE "Inn")))
      )
    )
  )
  (RuleD
    "val__case_1"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "fN"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE (Seq (Atom mk_val__1) Arg Arg) (TupE (VarE "Fnn") (VarE "var_x")))
    )
    (RulePr
      "wf_fN"
      (Seq Arg Arg)
      (TupE
        (CallE "size" (ExpA (CallE "valtype_Fnn" (ExpA (VarE "Fnn")))))
        (VarE "var_x")
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Fnn" (ExpA (VarE "Fnn")))
      )
    )
  )
)
(HintD (RelH "wf_val_" (hint "wf-relation" "val_")))
(DecD
  "proj_val__0"
  (ExpP "var_x" (VarT "val_"))
  (IterT (VarT "iN") Opt)
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "iN"))
    (ExpA
      (CaseE (Seq (Atom mk_val__0) Arg Arg) (TupE (VarE "Inn") (VarE "var_x")))
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "val_")) (ExpA (VarE "var_x")) (OptE))
)
(DecD
  "proj_val__1"
  (ExpP "var_x" (VarT "val_"))
  (IterT (VarT "fN") Opt)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "fN"))
    (ExpA
      (CaseE (Seq (Atom mk_val__1) Arg Arg) (TupE (VarE "Fnn") (VarE "var_x")))
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "val_")) (ExpA (VarE "var_x")) (OptE))
)
(HintD (TypH "val_" (hint "type_family" "{}")))
(HintD (DecH "proj_val__0" (hint "tf_projection_func" "{}")))
(HintD (DecH "proj_val__1" (hint "tf_projection_func" "{}")))
(TypD
  "sx"
  (InstD (VariantT (typcase (Atom U) (TupT)) (typcase (Atom S) (TupT))))
)
(HintD (TypH "sx" (hint "desc" "\"signedness\"")))
(TypD "sz" (InstD (VariantT (typcase Arg (TupT (typbind "i" nat))))))
(DecD
  "proj_sz_0"
  (ExpP "x" (VarT "sz"))
  (TupT (typbind "_" nat))
  (DefD
    (ExpP "v_num_0" nat)
    (ExpA (CaseE Arg (TupE (VarE "v_num_0"))))
    (TupE (VarE "v_num_0"))
  )
)
(HintD (DecH "proj_sz_0" (hint "uncase-proj-func" "{}")))
(RelD
  "wf_sz"
  (Seq Arg)
  (TupT (typbind "_" (VarT "sz")))
  (RuleD
    "sz_case_0"
    (ExpP "i" nat)
    (Seq Arg)
    (TupE (CaseE Arg (TupE (VarE "i"))))
    (IfPr
      (BinE
        OrOp
        bool
        (BinE
          OrOp
          bool
          (BinE
            OrOp
            bool
            (CmpE EqOp bool (VarE "i") (NumE (Nat 8)))
            (CmpE EqOp bool (VarE "i") (NumE (Nat 16)))
          )
          (CmpE EqOp bool (VarE "i") (NumE (Nat 32)))
        )
        (CmpE EqOp bool (VarE "i") (NumE (Nat 64)))
      )
    )
  )
)
(HintD (RelH "wf_sz" (hint "wf-relation" "sz")))
(HintD (TypH "sz" (hint "desc" "\"pack size\"")))
(TypD
  "unop_Inn"
  (InstD
    (VariantT
      (typcase (Atom CLZ) (TupT))
      (typcase (Atom CTZ) (TupT))
      (typcase (Atom POPCNT) (TupT))
    )
  )
)
(TypD
  "unop_Fnn"
  (InstD
    (VariantT
      (typcase (Atom ABS) (TupT))
      (typcase (Atom NEG) (TupT))
      (typcase (Atom SQRT) (TupT))
      (typcase (Atom CEIL) (TupT))
      (typcase (Atom FLOOR) (TupT))
      (typcase (Atom TRUNC) (TupT))
      (typcase (Atom NEAREST) (TupT))
    )
  )
)
(TypD
  "unop_"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupT (typbind "Inn" (VarT "Inn")) (typbind "var_x" (VarT "unop_Inn")))
      )
      (typcase
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupT (typbind "Fnn" (VarT "Fnn")) (typbind "var_x" (VarT "unop_Fnn")))
      )
    )
  )
)
(RelD
  "wf_unop_"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "valtype")) (typbind "_" (VarT "unop_")))
  (RuleD
    "unop__case_0"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "unop_Inn"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE (Seq (Atom mk_unop__0) Arg Arg) (TupE (VarE "Inn") (VarE "var_x")))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Inn" (ExpA (VarE "Inn")))
      )
    )
  )
  (RuleD
    "unop__case_1"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "unop_Fnn"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE (Seq (Atom mk_unop__1) Arg Arg) (TupE (VarE "Fnn") (VarE "var_x")))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Fnn" (ExpA (VarE "Fnn")))
      )
    )
  )
)
(HintD (RelH "wf_unop_" (hint "wf-relation" "unop_")))
(DecD
  "proj_unop__0"
  (ExpP "var_x" (VarT "unop_"))
  (IterT (VarT "unop_Inn") Opt)
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "unop_Inn"))
    (ExpA
      (CaseE (Seq (Atom mk_unop__0) Arg Arg) (TupE (VarE "Inn") (VarE "var_x")))
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "unop_")) (ExpA (VarE "var_x")) (OptE))
)
(DecD
  "proj_unop__1"
  (ExpP "var_x" (VarT "unop_"))
  (IterT (VarT "unop_Fnn") Opt)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "unop_Fnn"))
    (ExpA
      (CaseE (Seq (Atom mk_unop__1) Arg Arg) (TupE (VarE "Fnn") (VarE "var_x")))
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "unop_")) (ExpA (VarE "var_x")) (OptE))
)
(HintD (TypH "unop_" (hint "type_family" "{}")))
(HintD (DecH "proj_unop__0" (hint "tf_projection_func" "{}")))
(HintD (DecH "proj_unop__1" (hint "tf_projection_func" "{}")))
(TypD
  "binop_Inn"
  (InstD
    (VariantT
      (typcase (Atom ADD) (TupT))
      (typcase (Atom SUB) (TupT))
      (typcase (Atom MUL) (TupT))
      (typcase (Seq (Atom DIV) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Seq (Atom REM) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Atom AND) (TupT))
      (typcase (Atom OR) (TupT))
      (typcase (Atom XOR) (TupT))
      (typcase (Atom SHL) (TupT))
      (typcase (Seq (Atom SHR) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Atom ROTL) (TupT))
      (typcase (Atom ROTR) (TupT))
    )
  )
)
(TypD
  "binop_Fnn"
  (InstD
    (VariantT
      (typcase (Atom ADD) (TupT))
      (typcase (Atom SUB) (TupT))
      (typcase (Atom MUL) (TupT))
      (typcase (Atom DIV) (TupT))
      (typcase (Atom MIN) (TupT))
      (typcase (Atom MAX) (TupT))
      (typcase (Atom COPYSIGN) (TupT))
    )
  )
)
(TypD
  "binop_"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupT (typbind "Inn" (VarT "Inn")) (typbind "var_x" (VarT "binop_Inn")))
      )
      (typcase
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupT (typbind "Fnn" (VarT "Fnn")) (typbind "var_x" (VarT "binop_Fnn")))
      )
    )
  )
)
(RelD
  "wf_binop_"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "valtype")) (typbind "_" (VarT "binop_")))
  (RuleD
    "binop__case_0"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "binop_Inn"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Inn" (ExpA (VarE "Inn")))
      )
    )
  )
  (RuleD
    "binop__case_1"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "binop_Fnn"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (VarE "Fnn") (VarE "var_x"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Fnn" (ExpA (VarE "Fnn")))
      )
    )
  )
)
(HintD (RelH "wf_binop_" (hint "wf-relation" "binop_")))
(DecD
  "proj_binop__0"
  (ExpP "var_x" (VarT "binop_"))
  (IterT (VarT "binop_Inn") Opt)
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "binop_Inn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "binop_")) (ExpA (VarE "var_x")) (OptE))
)
(DecD
  "proj_binop__1"
  (ExpP "var_x" (VarT "binop_"))
  (IterT (VarT "binop_Fnn") Opt)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "binop_Fnn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (VarE "Fnn") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "binop_")) (ExpA (VarE "var_x")) (OptE))
)
(HintD (TypH "binop_" (hint "type_family" "{}")))
(HintD (DecH "proj_binop__0" (hint "tf_projection_func" "{}")))
(HintD (DecH "proj_binop__1" (hint "tf_projection_func" "{}")))
(TypD "testop_Inn" (InstD (VariantT (typcase (Atom EQZ) (TupT)))))
(TypD
  "testop_"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_testop__0) Arg Arg)
        (TupT
          (typbind "Inn" (VarT "Inn"))
          (typbind "var_x" (VarT "testop_Inn"))
        )
      )
    )
  )
)
(RelD
  "wf_testop_"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "valtype")) (typbind "_" (VarT "testop_")))
  (RuleD
    "testop__case_0"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "testop_Inn"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE
        (Seq (Atom mk_testop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Inn" (ExpA (VarE "Inn")))
      )
    )
  )
)
(HintD (RelH "wf_testop_" (hint "wf-relation" "testop_")))
(DecD
  "proj_testop__0"
  (ExpP "var_x" (VarT "testop_"))
  (VarT "testop_Inn")
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "testop_Inn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_testop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (VarE "var_x")
  )
)
(HintD (TypH "testop_" (hint "type_family" "{}")))
(HintD (DecH "proj_testop__0" (hint "tf_projection_func" "{}")))
(TypD
  "relop_Inn"
  (InstD
    (VariantT
      (typcase (Atom EQ) (TupT))
      (typcase (Atom NE) (TupT))
      (typcase (Seq (Atom LT) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Seq (Atom GT) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Seq (Atom LE) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Seq (Atom GE) Arg) (TupT (typbind "sx" (VarT "sx"))))
    )
  )
)
(TypD
  "relop_Fnn"
  (InstD
    (VariantT
      (typcase (Atom EQ) (TupT))
      (typcase (Atom NE) (TupT))
      (typcase (Atom LT) (TupT))
      (typcase (Atom GT) (TupT))
      (typcase (Atom LE) (TupT))
      (typcase (Atom GE) (TupT))
    )
  )
)
(TypD
  "relop_"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupT (typbind "Inn" (VarT "Inn")) (typbind "var_x" (VarT "relop_Inn")))
      )
      (typcase
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupT (typbind "Fnn" (VarT "Fnn")) (typbind "var_x" (VarT "relop_Fnn")))
      )
    )
  )
)
(RelD
  "wf_relop_"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "valtype")) (typbind "_" (VarT "relop_")))
  (RuleD
    "relop__case_0"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "relop_Inn"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Inn" (ExpA (VarE "Inn")))
      )
    )
  )
  (RuleD
    "relop__case_1"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "relop_Fnn"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (VarE "Fnn") (VarE "var_x"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Fnn" (ExpA (VarE "Fnn")))
      )
    )
  )
)
(HintD (RelH "wf_relop_" (hint "wf-relation" "relop_")))
(DecD
  "proj_relop__0"
  (ExpP "var_x" (VarT "relop_"))
  (IterT (VarT "relop_Inn") Opt)
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "relop_Inn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "relop_")) (ExpA (VarE "var_x")) (OptE))
)
(DecD
  "proj_relop__1"
  (ExpP "var_x" (VarT "relop_"))
  (IterT (VarT "relop_Fnn") Opt)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "relop_Fnn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (VarE "Fnn") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "relop_")) (ExpA (VarE "var_x")) (OptE))
)
(HintD (TypH "relop_" (hint "type_family" "{}")))
(HintD (DecH "proj_relop__0" (hint "tf_projection_func" "{}")))
(HintD (DecH "proj_relop__1" (hint "tf_projection_func" "{}")))
(TypD
  "cvtop"
  (InstD
    (VariantT
      (typcase (Seq (Atom EXTEND) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Atom WRAP) (TupT))
      (typcase (Seq (Atom CONVERT) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Seq (Atom TRUNC) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Atom PROMOTE) (TupT))
      (typcase (Atom DEMOTE) (TupT))
      (typcase (Atom REINTERPRET) (TupT))
    )
  )
)
(TypD
  "memarg"
  (InstD
    (StructT
      (typfield (Atom ALIGN) (VarT "u32"))
      (typfield (Atom OFFSET) (VarT "u32"))
    )
  )
)
(RelD
  "wf_memarg"
  (Seq Arg)
  (TupT (typbind "_" (VarT "memarg")))
  (RuleD
    "memarg_case_"
    (ExpP "var_0" (VarT "u32"))
    (ExpP "var_1" (VarT "u32"))
    (Seq Arg)
    (TupE
      (StrE
        (expfield (Atom ALIGN) (VarE "var_0"))
        (expfield (Atom OFFSET) (VarE "var_1"))
      )
    )
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "var_0")))
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "var_1")))
  )
)
(HintD (RelH "wf_memarg" (hint "wf-relation" "memarg")))
(HintD (TypH "memarg" (hint "desc" "\"memory argument\"")))
(TypD
  "loadop_Inn"
  (InstD
    (VariantT
      (typcase
        (Seq Arg (Atom _) Arg)
        (TupT (typbind "sz" (VarT "sz")) (typbind "sx" (VarT "sx")))
      )
    )
  )
)
(RelD
  "wf_loadop_Inn"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "Inn")) (typbind "_" (VarT "loadop_Inn")))
  (RuleD
    "loadop_Inn_case_0"
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "sz" (VarT "sz"))
    (ExpP "sx" (VarT "sx"))
    (Seq Arg Arg)
    (TupE
      (VarE "Inn")
      (CaseE (Seq Arg (Atom _) Arg) (TupE (VarE "sz") (VarE "sx")))
    )
    (RulePr "wf_sz" (Seq Arg) (TupE (VarE "sz")))
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (CallE "proj_sz_0" (ExpA (VarE "sz"))) 0)
        (CallE "size" (ExpA (CallE "valtype_Inn" (ExpA (VarE "Inn")))))
      )
    )
  )
)
(HintD (RelH "wf_loadop_Inn" (hint "wf-relation" "loadop_Inn")))
(TypD
  "loadop_"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_loadop__0) Arg Arg)
        (TupT
          (typbind "Inn" (VarT "Inn"))
          (typbind "var_x" (VarT "loadop_Inn"))
        )
      )
    )
  )
)
(RelD
  "wf_loadop_"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "valtype")) (typbind "_" (VarT "loadop_")))
  (RuleD
    "loadop__case_0"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "loadop_Inn"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE
        (Seq (Atom mk_loadop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (RulePr "wf_loadop_Inn" (Seq Arg Arg) (TupE (VarE "Inn") (VarE "var_x")))
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Inn" (ExpA (VarE "Inn")))
      )
    )
  )
)
(HintD (RelH "wf_loadop_" (hint "wf-relation" "loadop_")))
(DecD
  "proj_loadop__0"
  (ExpP "var_x" (VarT "loadop_"))
  (VarT "loadop_Inn")
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "loadop_Inn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_loadop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (VarE "var_x")
  )
)
(HintD (TypH "loadop_" (hint "type_family" "{}")))
(HintD (DecH "proj_loadop__0" (hint "tf_projection_func" "{}")))
(TypD "blocktype" (InstD (AliasT (IterT (VarT "valtype") Opt))))
(HintD (TypH "blocktype" (hint "desc" "\"block type\"")))
(RecD
  (TypD
    "instr"
    (InstD
      (VariantT
        (typcase (Atom NOP) (TupT))
        (typcase (Atom UNREACHABLE) (TupT))
        (typcase (Atom DROP) (TupT))
        (typcase (Atom SELECT) (TupT))
        (typcase
          (Seq (Atom BLOCK) Arg Arg)
          (TupT
            (typbind "blocktype" (VarT "blocktype"))
            (typbind "instr*" (IterT (VarT "instr") List))
          )
        )
        (typcase
          (Seq (Atom LOOP) Arg Arg)
          (TupT
            (typbind "blocktype" (VarT "blocktype"))
            (typbind "instr*" (IterT (VarT "instr") List))
          )
        )
        (typcase
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupT
            (typbind "blocktype" (VarT "blocktype"))
            (typbind "instr*" (IterT (VarT "instr") List))
            (typbind "instr*" (IterT (VarT "instr") List))
          )
        )
        (typcase
          (Seq (Atom BR) Arg)
          (TupT (typbind "labelidx" (VarT "labelidx")))
        )
        (typcase
          (Seq (Atom BR_IF) Arg)
          (TupT (typbind "labelidx" (VarT "labelidx")))
        )
        (typcase
          (Seq (Atom BR_TABLE) Arg Arg)
          (TupT
            (typbind "labelidx*" (IterT (VarT "labelidx") List))
            (typbind "labelidx" (VarT "labelidx"))
          )
        )
        (typcase
          (Seq (Atom CALL) Arg)
          (TupT (typbind "funcidx" (VarT "funcidx")))
        )
        (typcase
          (Seq (Atom CALL_INDIRECT) Arg)
          (TupT (typbind "typeidx" (VarT "typeidx")))
        )
        (typcase (Atom RETURN) (TupT))
        (typcase
          (Seq (Atom CONST) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "val_"))
          )
        )
        (typcase
          (Seq (Atom UNOP) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "unop_"))
          )
        )
        (typcase
          (Seq (Atom BINOP) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "binop_"))
          )
        )
        (typcase
          (Seq (Atom TESTOP) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "testop_"))
          )
        )
        (typcase
          (Seq (Atom RELOP) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "relop_"))
          )
        )
        (typcase
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupT
            (typbind "valtype_1" (VarT "valtype"))
            (typbind "valtype_2" (VarT "valtype"))
            (typbind "cvtop" (VarT "cvtop"))
          )
        )
        (typcase
          (Seq (Atom LOCAL.GET) Arg)
          (TupT (typbind "localidx" (VarT "localidx")))
        )
        (typcase
          (Seq (Atom LOCAL.SET) Arg)
          (TupT (typbind "localidx" (VarT "localidx")))
        )
        (typcase
          (Seq (Atom LOCAL.TEE) Arg)
          (TupT (typbind "localidx" (VarT "localidx")))
        )
        (typcase
          (Seq (Atom GLOBAL.GET) Arg)
          (TupT (typbind "globalidx" (VarT "globalidx")))
        )
        (typcase
          (Seq (Atom GLOBAL.SET) Arg)
          (TupT (typbind "globalidx" (VarT "globalidx")))
        )
        (typcase
          (Seq (Atom LOAD) Arg Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (IterT (VarT "loadop_") Opt))
            (typbind "memarg" (VarT "memarg"))
          )
        )
        (typcase
          (Seq (Atom STORE) Arg Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "sz?" (IterT (VarT "sz") Opt))
            (typbind "memarg" (VarT "memarg"))
          )
          (ExpP "Inn?" (IterT (VarT "Inn") Opt))
        )
        (typcase (Atom MEMORY.SIZE) (TupT))
        (typcase (Atom MEMORY.GROW) (TupT))
      )
    )
  )
)
(RecD
  (RelD
    "wf_instr"
    (Seq Arg)
    (TupT (typbind "_" (VarT "instr")))
    (RuleD "instr_case_0" (Seq Arg) (TupE (CaseE (Atom NOP) (TupE))))
    (RuleD "instr_case_1" (Seq Arg) (TupE (CaseE (Atom UNREACHABLE) (TupE))))
    (RuleD "instr_case_2" (Seq Arg) (TupE (CaseE (Atom DROP) (TupE))))
    (RuleD "instr_case_3" (Seq Arg) (TupE (CaseE (Atom SELECT) (TupE))))
    (RuleD
      "instr_case_4"
      (ExpP "blocktype" (VarT "blocktype"))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BLOCK) Arg Arg)
          (TupE (VarE "blocktype") (VarE "instr*"))
        )
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr")))
        List
        (iterexp "instr" (VarE "instr*"))
      )
    )
    (RuleD
      "instr_case_5"
      (ExpP "blocktype" (VarT "blocktype"))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LOOP) Arg Arg)
          (TupE (VarE "blocktype") (VarE "instr*"))
        )
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr")))
        List
        (iterexp "instr" (VarE "instr*"))
      )
    )
    (RuleD
      "instr_case_6"
      (ExpP "blocktype" (VarT "blocktype"))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (ExpP "instr*_0*" (IterT (VarT "instr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupE (VarE "blocktype") (VarE "instr*") (VarE "instr*_0*"))
        )
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr")))
        List
        (iterexp "instr" (VarE "instr*"))
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr*_0")))
        List
        (iterexp "instr*_0" (VarE "instr*_0*"))
      )
    )
    (RuleD
      "instr_case_7"
      (ExpP "labelidx" (VarT "labelidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BR) Arg) (TupE (VarE "labelidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "labelidx")))
    )
    (RuleD
      "instr_case_8"
      (ExpP "labelidx" (VarT "labelidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BR_IF) Arg) (TupE (VarE "labelidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "labelidx")))
    )
    (RuleD
      "instr_case_9"
      (ExpP "labelidx*" (IterT (VarT "labelidx") List))
      (ExpP "labelidx" (VarT "labelidx"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BR_TABLE) Arg Arg)
          (TupE (VarE "labelidx*") (VarE "labelidx"))
        )
      )
      (IterPr
        (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "labelidx")))
        List
        (iterexp "labelidx" (VarE "labelidx*"))
      )
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "labelidx")))
    )
    (RuleD
      "instr_case_10"
      (ExpP "funcidx" (VarT "funcidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "funcidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "funcidx")))
    )
    (RuleD
      "instr_case_11"
      (ExpP "typeidx" (VarT "typeidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "typeidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "typeidx")))
    )
    (RuleD "instr_case_12" (Seq Arg) (TupE (CaseE (Atom RETURN) (TupE))))
    (RuleD
      "instr_case_13"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "val_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0"))
        )
      )
      (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
    )
    (RuleD
      "instr_case_14"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "unop_"))
      (Seq Arg)
      (TupE
        (CaseE (Seq (Atom UNOP) Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
      )
      (RulePr "wf_unop_" (Seq Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
    )
    (RuleD
      "instr_case_15"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "binop_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BINOP) Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0"))
        )
      )
      (RulePr "wf_binop_" (Seq Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
    )
    (RuleD
      "instr_case_16"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "testop_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom TESTOP) Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0"))
        )
      )
      (RulePr "wf_testop_" (Seq Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
    )
    (RuleD
      "instr_case_17"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "relop_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom RELOP) Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0"))
        )
      )
      (RulePr "wf_relop_" (Seq Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
    )
    (RuleD
      "instr_case_18"
      (ExpP "valtype_1" (VarT "valtype"))
      (ExpP "valtype_2" (VarT "valtype"))
      (ExpP "cvtop" (VarT "cvtop"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupE (VarE "valtype_1") (VarE "valtype_2") (VarE "cvtop"))
        )
      )
      (IfPr (CmpE NeOp bool (VarE "valtype_1") (VarE "valtype_2")))
    )
    (RuleD
      "instr_case_19"
      (ExpP "localidx" (VarT "localidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL.GET) Arg) (TupE (VarE "localidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "localidx")))
    )
    (RuleD
      "instr_case_20"
      (ExpP "localidx" (VarT "localidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL.SET) Arg) (TupE (VarE "localidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "localidx")))
    )
    (RuleD
      "instr_case_21"
      (ExpP "localidx" (VarT "localidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL.TEE) Arg) (TupE (VarE "localidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "localidx")))
    )
    (RuleD
      "instr_case_22"
      (ExpP "globalidx" (VarT "globalidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "globalidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "globalidx")))
    )
    (RuleD
      "instr_case_23"
      (ExpP "globalidx" (VarT "globalidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL.SET) Arg) (TupE (VarE "globalidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "globalidx")))
    )
    (RuleD
      "instr_case_24"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0?" (IterT (VarT "loadop_") Opt))
      (ExpP "memarg" (VarT "memarg"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LOAD) Arg Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0?") (VarE "memarg"))
        )
      )
      (IterPr
        (RulePr
          "wf_loadop_"
          (Seq Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0"))
        )
        Opt
        (iterexp "var_0" (VarE "var_0?"))
      )
      (RulePr "wf_memarg" (Seq Arg) (TupE (VarE "memarg")))
    )
    (RuleD
      "instr_case_25"
      (ExpP "Inn?" (IterT (VarT "Inn") Opt))
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "sz?" (IterT (VarT "sz") Opt))
      (ExpP "memarg" (VarT "memarg"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom STORE) Arg Arg Arg)
          (TupE (VarE "valtype") (VarE "sz?") (VarE "memarg"))
        )
      )
      (IterPr
        (RulePr "wf_sz" (Seq Arg) (TupE (VarE "sz")))
        Opt
        (iterexp "sz" (VarE "sz?"))
      )
      (RulePr "wf_memarg" (Seq Arg) (TupE (VarE "memarg")))
      (IterPr
        (IfPr
          (BinE
            AndOp
            bool
            (CmpE
              EqOp
              bool
              (VarE "valtype")
              (CallE "valtype_Inn" (ExpA (VarE "Inn")))
            )
            (CmpE
              LtOp
              nat
              (ProjE (CallE "proj_sz_0" (ExpA (VarE "sz"))) 0)
              (CallE "size" (ExpA (CallE "valtype_Inn" (ExpA (VarE "Inn")))))
            )
          )
        )
        Opt
        (iterexp "Inn" (VarE "Inn?"))
        (iterexp "sz" (VarE "sz?"))
      )
    )
    (RuleD "instr_case_26" (Seq Arg) (TupE (CaseE (Atom MEMORY.SIZE) (TupE))))
    (RuleD "instr_case_27" (Seq Arg) (TupE (CaseE (Atom MEMORY.GROW) (TupE))))
  )
  (HintD (RelH "wf_instr" (hint "wf-relation" "instr")))
)
(HintD (TypH "instr" (hint "desc" "\"parametric instruction\"")))
(HintD (TypH "instr" (hint "desc" "\"block instruction\"")))
(HintD (TypH "instr" (hint "desc" "\"branch instruction\"")))
(HintD (TypH "instr" (hint "desc" "\"call instruction\"")))
(HintD (TypH "instr" (hint "desc" "\"numeric instruction\"")))
(HintD (TypH "instr" (hint "desc" "\"local instruction\"")))
(HintD (TypH "instr" (hint "desc" "\"global instruction\"")))
(HintD (TypH "instr" (hint "desc" "\"memory instruction\"")))
(TypD "expr" (InstD (AliasT (IterT (VarT "instr") List))))
(HintD (TypH "expr" (hint "desc" "\"expression\"")))
(HintD (TypH "instr" (hint "desc" "\"instruction\"")))
(TypD
  "type"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom TYPE) Arg)
        (TupT (typbind "functype" (VarT "functype")))
      )
    )
  )
)
(HintD (TypH "type" (hint "desc" "\"type\"")))
(TypD
  "local"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom LOCAL) Arg)
        (TupT (typbind "valtype" (VarT "valtype")))
      )
    )
  )
)
(HintD (TypH "local" (hint "desc" "\"local\"")))
(TypD
  "func"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom FUNC) Arg Arg Arg)
        (TupT
          (typbind "typeidx" (VarT "typeidx"))
          (typbind "local*" (IterT (VarT "local") List))
          (typbind "expr" (VarT "expr"))
        )
      )
    )
  )
)
(RelD
  "wf_func"
  (Seq Arg)
  (TupT (typbind "_" (VarT "func")))
  (RuleD
    "func_case_0"
    (ExpP "typeidx" (VarT "typeidx"))
    (ExpP "local*" (IterT (VarT "local") List))
    (ExpP "expr" (VarT "expr"))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom FUNC) Arg Arg Arg)
        (TupE (VarE "typeidx") (VarE "local*") (VarE "expr"))
      )
    )
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "typeidx")))
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "expr")))
      List
      (iterexp "expr" (VarE "expr"))
    )
  )
)
(HintD (RelH "wf_func" (hint "wf-relation" "func")))
(HintD (TypH "func" (hint "desc" "\"function\"")))
(TypD
  "global"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom GLOBAL) Arg Arg)
        (TupT
          (typbind "globaltype" (VarT "globaltype"))
          (typbind "expr" (VarT "expr"))
        )
      )
    )
  )
)
(RelD
  "wf_global"
  (Seq Arg)
  (TupT (typbind "_" (VarT "global")))
  (RuleD
    "global_case_0"
    (ExpP "globaltype" (VarT "globaltype"))
    (ExpP "expr" (VarT "expr"))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom GLOBAL) Arg Arg)
        (TupE (VarE "globaltype") (VarE "expr"))
      )
    )
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "expr")))
      List
      (iterexp "expr" (VarE "expr"))
    )
  )
)
(HintD (RelH "wf_global" (hint "wf-relation" "global")))
(HintD (TypH "global" (hint "desc" "\"global\"")))
(TypD
  "table"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom TABLE) Arg)
        (TupT (typbind "tabletype" (VarT "tabletype")))
      )
    )
  )
)
(RelD
  "wf_table"
  (Seq Arg)
  (TupT (typbind "_" (VarT "table")))
  (RuleD
    "table_case_0"
    (ExpP "tabletype" (VarT "tabletype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tabletype"))))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "tabletype")))
  )
)
(HintD (RelH "wf_table" (hint "wf-relation" "table")))
(HintD (TypH "table" (hint "desc" "\"table\"")))
(TypD
  "mem"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom MEMORY) Arg)
        (TupT (typbind "memtype" (VarT "memtype")))
      )
    )
  )
)
(RelD
  "wf_mem"
  (Seq Arg)
  (TupT (typbind "_" (VarT "mem")))
  (RuleD
    "mem_case_0"
    (ExpP "memtype" (VarT "memtype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom MEMORY) Arg) (TupE (VarE "memtype"))))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "memtype")))
  )
)
(HintD (RelH "wf_mem" (hint "wf-relation" "mem")))
(HintD (TypH "mem" (hint "desc" "\"memory\"")))
(TypD
  "elem"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom ELEM) Arg Arg)
        (TupT
          (typbind "expr" (VarT "expr"))
          (typbind "funcidx*" (IterT (VarT "funcidx") List))
        )
      )
    )
  )
)
(RelD
  "wf_elem"
  (Seq Arg)
  (TupT (typbind "_" (VarT "elem")))
  (RuleD
    "elem_case_0"
    (ExpP "expr" (VarT "expr"))
    (ExpP "funcidx*" (IterT (VarT "funcidx") List))
    (Seq Arg)
    (TupE
      (CaseE (Seq (Atom ELEM) Arg Arg) (TupE (VarE "expr") (VarE "funcidx*")))
    )
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "expr")))
      List
      (iterexp "expr" (VarE "expr"))
    )
    (IterPr
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "funcidx")))
      List
      (iterexp "funcidx" (VarE "funcidx*"))
    )
  )
)
(HintD (RelH "wf_elem" (hint "wf-relation" "elem")))
(HintD (TypH "elem" (hint "desc" "\"table segment\"")))
(TypD
  "data"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom DATA) Arg Arg)
        (TupT
          (typbind "expr" (VarT "expr"))
          (typbind "byte*" (IterT (VarT "byte") List))
        )
      )
    )
  )
)
(RelD
  "wf_data"
  (Seq Arg)
  (TupT (typbind "_" (VarT "data")))
  (RuleD
    "data_case_0"
    (ExpP "expr" (VarT "expr"))
    (ExpP "byte*" (IterT (VarT "byte") List))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom DATA) Arg Arg) (TupE (VarE "expr") (VarE "byte*"))))
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "expr")))
      List
      (iterexp "expr" (VarE "expr"))
    )
    (IterPr
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "byte")))
      List
      (iterexp "byte" (VarE "byte*"))
    )
  )
)
(HintD (RelH "wf_data" (hint "wf-relation" "data")))
(HintD (TypH "data" (hint "desc" "\"memory segment\"")))
(TypD
  "start"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom START) Arg)
        (TupT (typbind "funcidx" (VarT "funcidx")))
      )
    )
  )
)
(RelD
  "wf_start"
  (Seq Arg)
  (TupT (typbind "_" (VarT "start")))
  (RuleD
    "start_case_0"
    (ExpP "funcidx" (VarT "funcidx"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom START) Arg) (TupE (VarE "funcidx"))))
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "funcidx")))
  )
)
(HintD (RelH "wf_start" (hint "wf-relation" "start")))
(HintD (TypH "start" (hint "desc" "\"start function\"")))
(TypD
  "externidx"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom FUNC) Arg)
        (TupT (typbind "funcidx" (VarT "funcidx")))
      )
      (typcase
        (Seq (Atom GLOBAL) Arg)
        (TupT (typbind "globalidx" (VarT "globalidx")))
      )
      (typcase
        (Seq (Atom TABLE) Arg)
        (TupT (typbind "tableidx" (VarT "tableidx")))
      )
      (typcase (Seq (Atom MEM) Arg) (TupT (typbind "memidx" (VarT "memidx"))))
    )
  )
)
(RelD
  "wf_externidx"
  (Seq Arg)
  (TupT (typbind "_" (VarT "externidx")))
  (RuleD
    "externidx_case_0"
    (ExpP "funcidx" (VarT "funcidx"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "funcidx"))))
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "funcidx")))
  )
  (RuleD
    "externidx_case_1"
    (ExpP "globalidx" (VarT "globalidx"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "globalidx"))))
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "globalidx")))
  )
  (RuleD
    "externidx_case_2"
    (ExpP "tableidx" (VarT "tableidx"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tableidx"))))
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "tableidx")))
  )
  (RuleD
    "externidx_case_3"
    (ExpP "memidx" (VarT "memidx"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "memidx"))))
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "memidx")))
  )
)
(HintD (RelH "wf_externidx" (hint "wf-relation" "externidx")))
(HintD (TypH "externidx" (hint "desc" "\"external index\"")))
(TypD
  "export"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom EXPORT) Arg Arg)
        (TupT
          (typbind "name" (VarT "name"))
          (typbind "externidx" (VarT "externidx"))
        )
      )
    )
  )
)
(RelD
  "wf_export"
  (Seq Arg)
  (TupT (typbind "_" (VarT "export")))
  (RuleD
    "export_case_0"
    (ExpP "name" (VarT "name"))
    (ExpP "externidx" (VarT "externidx"))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom EXPORT) Arg Arg)
        (TupE (VarE "name") (VarE "externidx"))
      )
    )
    (RulePr "wf_name" (Seq Arg) (TupE (VarE "name")))
    (RulePr "wf_externidx" (Seq Arg) (TupE (VarE "externidx")))
  )
)
(HintD (RelH "wf_export" (hint "wf-relation" "export")))
(HintD (TypH "export" (hint "desc" "\"export\"")))
(TypD
  "import"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom IMPORT) Arg Arg Arg)
        (TupT
          (typbind "name" (VarT "name"))
          (typbind "name" (VarT "name"))
          (typbind "externtype" (VarT "externtype"))
        )
      )
    )
  )
)
(RelD
  "wf_import"
  (Seq Arg)
  (TupT (typbind "_" (VarT "import")))
  (RuleD
    "import_case_0"
    (ExpP "name" (VarT "name"))
    (ExpP "name_0" (VarT "name"))
    (ExpP "externtype" (VarT "externtype"))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom IMPORT) Arg Arg Arg)
        (TupE (VarE "name") (VarE "name_0") (VarE "externtype"))
      )
    )
    (RulePr "wf_name" (Seq Arg) (TupE (VarE "name")))
    (RulePr "wf_name" (Seq Arg) (TupE (VarE "name_0")))
    (RulePr "wf_externtype" (Seq Arg) (TupE (VarE "externtype")))
  )
)
(HintD (RelH "wf_import" (hint "wf-relation" "import")))
(HintD (TypH "import" (hint "desc" "\"import\"")))
(TypD
  "module"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
        (TupT
          (typbind "type*" (IterT (VarT "type") List))
          (typbind "import*" (IterT (VarT "import") List))
          (typbind "func*" (IterT (VarT "func") List))
          (typbind "global*" (IterT (VarT "global") List))
          (typbind "table*" (IterT (VarT "table") List))
          (typbind "mem*" (IterT (VarT "mem") List))
          (typbind "elem*" (IterT (VarT "elem") List))
          (typbind "data*" (IterT (VarT "data") List))
          (typbind "start?" (IterT (VarT "start") Opt))
          (typbind "export*" (IterT (VarT "export") List))
        )
      )
    )
  )
)
(RelD
  "wf_module"
  (Seq Arg)
  (TupT (typbind "_" (VarT "module")))
  (RuleD
    "module_case_0"
    (ExpP "type*" (IterT (VarT "type") List))
    (ExpP "import*" (IterT (VarT "import") List))
    (ExpP "func*" (IterT (VarT "func") List))
    (ExpP "global*" (IterT (VarT "global") List))
    (ExpP "table*" (IterT (VarT "table") List))
    (ExpP "mem*" (IterT (VarT "mem") List))
    (ExpP "elem*" (IterT (VarT "elem") List))
    (ExpP "data*" (IterT (VarT "data") List))
    (ExpP "start?" (IterT (VarT "start") Opt))
    (ExpP "export*" (IterT (VarT "export") List))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
        (TupE
          (VarE "type*")
          (VarE "import*")
          (VarE "func*")
          (VarE "global*")
          (VarE "table*")
          (VarE "mem*")
          (VarE "elem*")
          (VarE "data*")
          (VarE "start?")
          (VarE "export*")
        )
      )
    )
    (IterPr
      (RulePr "wf_import" (Seq Arg) (TupE (VarE "import")))
      List
      (iterexp "import" (VarE "import*"))
    )
    (IterPr
      (RulePr "wf_func" (Seq Arg) (TupE (VarE "func")))
      List
      (iterexp "func" (VarE "func*"))
    )
    (IterPr
      (RulePr "wf_global" (Seq Arg) (TupE (VarE "global")))
      List
      (iterexp "global" (VarE "global*"))
    )
    (IterPr
      (RulePr "wf_table" (Seq Arg) (TupE (VarE "table")))
      List
      (iterexp "table" (VarE "table*"))
    )
    (IterPr
      (RulePr "wf_mem" (Seq Arg) (TupE (VarE "mem")))
      List
      (iterexp "mem" (VarE "mem*"))
    )
    (IterPr
      (RulePr "wf_elem" (Seq Arg) (TupE (VarE "elem")))
      List
      (iterexp "elem" (VarE "elem*"))
    )
    (IterPr
      (RulePr "wf_data" (Seq Arg) (TupE (VarE "data")))
      List
      (iterexp "data" (VarE "data*"))
    )
    (IterPr
      (RulePr "wf_start" (Seq Arg) (TupE (VarE "start")))
      Opt
      (iterexp "start" (VarE "start?"))
    )
    (IterPr
      (RulePr "wf_export" (Seq Arg) (TupE (VarE "export")))
      List
      (iterexp "export" (VarE "export*"))
    )
  )
)
(HintD (RelH "wf_module" (hint "wf-relation" "module")))
(HintD (TypH "module" (hint "desc" "\"module\"")))
(RecD
  (DecD
    "funcsxt"
    (ExpP "_" (IterT (VarT "externtype") List))
    (IterT (VarT "functype") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "ft" (VarT "functype"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "ft"))))
          (IterE (VarE "xt#1") List (iterexp "xt#1" (VarE "xt*")))
        )
      )
      (CatE
        (ListE (VarE "ft"))
        (CallE
          "funcsxt"
          (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
        )
      )
    )
    (DefD
      (ExpP "externtype" (VarT "externtype"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE (VarE "externtype"))
          (IterE (VarE "xt#2") List (iterexp "xt#2" (VarE "xt*")))
        )
      )
      (CallE
        "funcsxt"
        (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
      )
    )
  )
)
(HintD (DecH "funcsxt" (hint "show" "$funcs(%)")))
(RecD
  (DecD
    "globalsxt"
    (ExpP "_" (IterT (VarT "externtype") List))
    (IterT (VarT "globaltype") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "gt" (VarT "globaltype"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "gt"))))
          (IterE (VarE "xt#3") List (iterexp "xt#3" (VarE "xt*")))
        )
      )
      (CatE
        (ListE (VarE "gt"))
        (CallE
          "globalsxt"
          (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
        )
      )
    )
    (DefD
      (ExpP "externtype" (VarT "externtype"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE (VarE "externtype"))
          (IterE (VarE "xt#4") List (iterexp "xt#4" (VarE "xt*")))
        )
      )
      (CallE
        "globalsxt"
        (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
      )
    )
  )
)
(HintD (DecH "globalsxt" (hint "show" "$globals(%)")))
(RecD
  (DecD
    "tablesxt"
    (ExpP "_" (IterT (VarT "externtype") List))
    (IterT (VarT "tabletype") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "tt" (VarT "limits"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tt"))))
          (IterE (VarE "xt#5") List (iterexp "xt#5" (VarE "xt*")))
        )
      )
      (CatE
        (ListE (VarE "tt"))
        (CallE
          "tablesxt"
          (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
        )
      )
      (IterPr
        (RulePr "wf_limits" (Seq Arg) (TupE (VarE "iter#3")))
        List
        (iterexp
          "iter#3"
          (CallE
            "tablesxt"
            (ExpA (IterE (VarE "xt#6") List (iterexp "xt#6" (VarE "xt*"))))
          )
        )
      )
    )
    (DefD
      (ExpP "externtype" (VarT "externtype"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE (VarE "externtype"))
          (IterE (VarE "xt#7") List (iterexp "xt#7" (VarE "xt*")))
        )
      )
      (CallE
        "tablesxt"
        (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
      )
      (IterPr
        (RulePr "wf_limits" (Seq Arg) (TupE (VarE "iter#4")))
        List
        (iterexp
          "iter#4"
          (CallE
            "tablesxt"
            (ExpA (IterE (VarE "xt#8") List (iterexp "xt#8" (VarE "xt*"))))
          )
        )
      )
    )
  )
)
(HintD (DecH "tablesxt" (hint "show" "$tables(%)")))
(RecD
  (DecD
    "memsxt"
    (ExpP "_" (IterT (VarT "externtype") List))
    (IterT (VarT "memtype") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "mt" (VarT "limits"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "mt"))))
          (IterE (VarE "xt#9") List (iterexp "xt#9" (VarE "xt*")))
        )
      )
      (CatE
        (ListE (VarE "mt"))
        (CallE
          "memsxt"
          (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
        )
      )
      (IterPr
        (RulePr "wf_limits" (Seq Arg) (TupE (VarE "iter#5")))
        List
        (iterexp
          "iter#5"
          (CallE
            "memsxt"
            (ExpA (IterE (VarE "xt#10") List (iterexp "xt#10" (VarE "xt*"))))
          )
        )
      )
    )
    (DefD
      (ExpP "externtype" (VarT "externtype"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE (VarE "externtype"))
          (IterE (VarE "xt#11") List (iterexp "xt#11" (VarE "xt*")))
        )
      )
      (CallE
        "memsxt"
        (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
      )
      (IterPr
        (RulePr "wf_limits" (Seq Arg) (TupE (VarE "iter#6")))
        List
        (iterexp
          "iter#6"
          (CallE
            "memsxt"
            (ExpA (IterE (VarE "xt#12") List (iterexp "xt#12" (VarE "xt*"))))
          )
        )
      )
    )
  )
)
(HintD (DecH "memsxt" (hint "show" "$mems(%)")))
(DecD
  "memarg0"
  (VarT "memarg")
  (DefD
    (StrE
      (expfield (Atom ALIGN) (CaseE Arg (TupE (NumE (Nat 0)))))
      (expfield (Atom OFFSET) (CaseE Arg (TupE (NumE (Nat 0)))))
    )
    (RulePr
      "wf_memarg"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom ALIGN) (CaseE Arg (TupE (NumE (Nat 0)))))
          (expfield (Atom OFFSET) (CaseE Arg (TupE (NumE (Nat 0)))))
        )
      )
    )
  )
)
(HintD (DecH "memarg0" (hint "show" "{}")))
(DecD
  "bool"
  (ExpP "bool" BoolT)
  nat
  (DefD (ExpA (BoolE false)) (NumE (Nat 0)))
  (DefD (ExpA (BoolE true)) (NumE (Nat 1)))
)
(DecD "truncz" (ExpP "rat" rat) int)
(HintD (DecH "truncz" (hint "builtin" "{}")))
(DecD
  "signed_"
  (ExpP "N" (VarT "N"))
  (ExpP "nat" nat)
  int
  (DefD
    (ExpP "N" nat)
    (ExpP "i" nat)
    (ExpA (VarE "N"))
    (ExpA (VarE "i"))
    (CvtE nat int (VarE "i"))
    (IfPr
      (CmpE
        LtOp
        nat
        (VarE "i")
        (BinE
          PowOp
          nat
          (NumE (Nat 2))
          (CvtE
            int
            nat
            (BinE
              SubOp
              int
              (CvtE nat int (VarE "N"))
              (CvtE nat int (NumE (Nat 1)))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i" nat)
    (ExpA (VarE "N"))
    (ExpA (VarE "i"))
    (BinE
      SubOp
      int
      (CvtE nat int (VarE "i"))
      (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (VarE "N")))
    )
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE
          LeOp
          nat
          (BinE
            PowOp
            nat
            (NumE (Nat 2))
            (CvtE
              int
              nat
              (BinE
                SubOp
                int
                (CvtE nat int (VarE "N"))
                (CvtE nat int (NumE (Nat 1)))
              )
            )
          )
          (VarE "i")
        )
        (CmpE LtOp nat (VarE "i") (BinE PowOp nat (NumE (Nat 2)) (VarE "N")))
      )
    )
  )
)
(HintD (DecH "signed_" (hint "inverse" "$inv_signed_")))
(DecD
  "inv_signed_"
  (ExpP "N" (VarT "N"))
  (ExpP "int" int)
  nat
  (DefD
    (ExpP "N" nat)
    (ExpP "i" int)
    (ExpA (VarE "N"))
    (ExpA (VarE "i"))
    (CvtE int nat (VarE "i"))
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE LeOp int (CvtE nat int (NumE (Nat 0))) (VarE "i"))
        (CmpE
          LtOp
          int
          (VarE "i")
          (CvtE
            nat
            int
            (BinE
              PowOp
              nat
              (NumE (Nat 2))
              (CvtE
                int
                nat
                (BinE
                  SubOp
                  int
                  (CvtE nat int (VarE "N"))
                  (CvtE nat int (NumE (Nat 1)))
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i" int)
    (ExpA (VarE "N"))
    (ExpA (VarE "i"))
    (CvtE
      int
      nat
      (BinE
        AddOp
        int
        (VarE "i")
        (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (VarE "N")))
      )
    )
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE
          LeOp
          int
          (UnE
            MinusOp
            int
            (CvtE
              nat
              int
              (BinE
                PowOp
                nat
                (NumE (Nat 2))
                (CvtE
                  int
                  nat
                  (BinE
                    SubOp
                    int
                    (CvtE nat int (VarE "N"))
                    (CvtE nat int (NumE (Nat 1)))
                  )
                )
              )
            )
          )
          (VarE "i")
        )
        (CmpE LtOp int (VarE "i") (CvtE nat int (NumE (Nat 0))))
      )
    )
  )
)
(HintD (DecH "inv_signed_" (hint "show" "$signed_(%)^(- 1)#((%))")))
(DecD
  "fabs_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fceil_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "ffloor_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fnearest_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fneg_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fsqrt_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "ftrunc_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD "iclz_" (ExpP "N" (VarT "N")) (ExpP "iN" (VarT "iN")) (VarT "iN"))
(DecD "ictz_" (ExpP "N" (VarT "N")) (ExpP "iN" (VarT "iN")) (VarT "iN"))
(DecD "ipopcnt_" (ExpP "N" (VarT "N")) (ExpP "iN" (VarT "iN")) (VarT "iN"))
(DecD
  "unop_"
  (ExpP "valtype" (VarT "valtype"))
  (ExpP "unop_" (VarT "unop_"))
  (ExpP "val_" (VarT "val_"))
  (IterT (IterT (VarT "val_") List) Opt)
  (DefD
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom CLZ) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "iclz_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "iclz_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom CLZ) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "iclz_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "iclz_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom CTZ) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ictz_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ictz_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom CTZ) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "ictz_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "ictz_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom POPCNT) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ipopcnt_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ipopcnt_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom POPCNT) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "ipopcnt_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "ipopcnt_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom ABS) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#2"))
        )
        List
        (iterexp
          "iter_0#2"
          (CallE
            "fabs_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          )
          (VarE "iter#7")
        )
      )
      List
      (iterexp
        "iter#7"
        (CallE
          "fabs_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#1"))
          )
        )
      )
      List
      (iterexp
        "iter_0#1"
        (CallE
          "fabs_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom ABS) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#4"))
        )
        List
        (iterexp
          "iter_0#4"
          (CallE
            "fabs_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          )
          (VarE "iter#8")
        )
      )
      List
      (iterexp
        "iter#8"
        (CallE
          "fabs_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#3"))
          )
        )
      )
      List
      (iterexp
        "iter_0#3"
        (CallE
          "fabs_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom NEG) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#6"))
        )
        List
        (iterexp
          "iter_0#6"
          (CallE
            "fneg_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          )
          (VarE "iter#9")
        )
      )
      List
      (iterexp
        "iter#9"
        (CallE
          "fneg_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#5"))
          )
        )
      )
      List
      (iterexp
        "iter_0#5"
        (CallE
          "fneg_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom NEG) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#8"))
        )
        List
        (iterexp
          "iter_0#8"
          (CallE
            "fneg_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          )
          (VarE "iter#10")
        )
      )
      List
      (iterexp
        "iter#10"
        (CallE
          "fneg_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#7"))
          )
        )
      )
      List
      (iterexp
        "iter_0#7"
        (CallE
          "fneg_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom SQRT) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#10"))
        )
        List
        (iterexp
          "iter_0#10"
          (CallE
            "fsqrt_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          )
          (VarE "iter#11")
        )
      )
      List
      (iterexp
        "iter#11"
        (CallE
          "fsqrt_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#9"))
          )
        )
      )
      List
      (iterexp
        "iter_0#9"
        (CallE
          "fsqrt_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom SQRT) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#12"))
        )
        List
        (iterexp
          "iter_0#12"
          (CallE
            "fsqrt_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          )
          (VarE "iter#12")
        )
      )
      List
      (iterexp
        "iter#12"
        (CallE
          "fsqrt_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#11"))
          )
        )
      )
      List
      (iterexp
        "iter_0#11"
        (CallE
          "fsqrt_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom CEIL) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#14"))
        )
        List
        (iterexp
          "iter_0#14"
          (CallE
            "fceil_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          )
          (VarE "iter#13")
        )
      )
      List
      (iterexp
        "iter#13"
        (CallE
          "fceil_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#13"))
          )
        )
      )
      List
      (iterexp
        "iter_0#13"
        (CallE
          "fceil_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom CEIL) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#16"))
        )
        List
        (iterexp
          "iter_0#16"
          (CallE
            "fceil_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          )
          (VarE "iter#14")
        )
      )
      List
      (iterexp
        "iter#14"
        (CallE
          "fceil_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#15"))
          )
        )
      )
      List
      (iterexp
        "iter_0#15"
        (CallE
          "fceil_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom FLOOR) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#18"))
        )
        List
        (iterexp
          "iter_0#18"
          (CallE
            "ffloor_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          )
          (VarE "iter#15")
        )
      )
      List
      (iterexp
        "iter#15"
        (CallE
          "ffloor_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#17"))
          )
        )
      )
      List
      (iterexp
        "iter_0#17"
        (CallE
          "ffloor_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom FLOOR) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#20"))
        )
        List
        (iterexp
          "iter_0#20"
          (CallE
            "ffloor_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          )
          (VarE "iter#16")
        )
      )
      List
      (iterexp
        "iter#16"
        (CallE
          "ffloor_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#19"))
          )
        )
      )
      List
      (iterexp
        "iter_0#19"
        (CallE
          "ffloor_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom TRUNC) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#22"))
        )
        List
        (iterexp
          "iter_0#22"
          (CallE
            "ftrunc_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          )
          (VarE "iter#17")
        )
      )
      List
      (iterexp
        "iter#17"
        (CallE
          "ftrunc_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#21"))
          )
        )
      )
      List
      (iterexp
        "iter_0#21"
        (CallE
          "ftrunc_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom TRUNC) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#24"))
        )
        List
        (iterexp
          "iter_0#24"
          (CallE
            "ftrunc_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          )
          (VarE "iter#18")
        )
      )
      List
      (iterexp
        "iter#18"
        (CallE
          "ftrunc_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#23"))
          )
        )
      )
      List
      (iterexp
        "iter_0#23"
        (CallE
          "ftrunc_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom NEAREST) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#26"))
        )
        List
        (iterexp
          "iter_0#26"
          (CallE
            "fnearest_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          )
          (VarE "iter#19")
        )
      )
      List
      (iterexp
        "iter#19"
        (CallE
          "fnearest_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#25"))
          )
        )
      )
      List
      (iterexp
        "iter_0#25"
        (CallE
          "fnearest_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom NEAREST) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#28"))
        )
        List
        (iterexp
          "iter_0#28"
          (CallE
            "fnearest_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          )
          (VarE "iter#20")
        )
      )
      List
      (iterexp
        "iter#20"
        (CallE
          "fnearest_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#27"))
          )
        )
      )
      List
      (iterexp
        "iter_0#27"
        (CallE
          "fnearest_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "unop_"))
    (ExpP "x2" (VarT "val_"))
    (ExpA (VarE "x0"))
    (ExpA (VarE "x1"))
    (ExpA (VarE "x2"))
    (OptE)
    ElsePr
  )
)
(HintD (DecH "unop_" (hint "partial" "{}")))
(HintD (DecH "unop_" (hint "show" "%2#$_(%1)#((%3))")))
(DecD
  "fadd_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fcopysign_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fdiv_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fmax_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fmin_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fmul_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fsub_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "iadd_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "iN" (VarT "iN"))
  (VarT "iN")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (BinE
          ModOp
          nat
          (BinE
            AddOp
            nat
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
          )
          (BinE PowOp nat (NumE (Nat 2)) (VarE "N"))
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (VarE "N")
        (CaseE
          Arg
          (TupE
            (BinE
              ModOp
              nat
              (BinE
                AddOp
                nat
                (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
                (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
              )
              (BinE PowOp nat (NumE (Nat 2)) (VarE "N"))
            )
          )
        )
      )
    )
  )
)
(DecD
  "iand_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "iN" (VarT "iN"))
  (VarT "iN")
)
(DecD
  "idiv_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "iN" (VarT "iN"))
  (IterT (VarT "iN") Opt)
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
    (OptE)
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (OptE
      (CaseE
        Arg
        (TupE
          (CvtE
            int
            nat
            (CallE
              "truncz"
              (ExpA
                (BinE
                  DivOp
                  rat
                  (CvtE
                    nat
                    rat
                    (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
                  )
                  (CvtE
                    nat
                    rat
                    (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
                  )
                )
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (VarE "N")
        (CaseE
          Arg
          (TupE
            (CvtE
              int
              nat
              (CallE
                "truncz"
                (ExpA
                  (BinE
                    DivOp
                    rat
                    (CvtE
                      nat
                      rat
                      (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
                    )
                    (CvtE
                      nat
                      rat
                      (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
    (OptE)
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (OptE)
    (IfPr
      (CmpE
        EqOp
        bool
        (BinE
          DivOp
          rat
          (CvtE
            int
            rat
            (CallE
              "signed_"
              (ExpA (VarE "N"))
              (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0))
            )
          )
          (CvtE
            int
            rat
            (CallE
              "signed_"
              (ExpA (VarE "N"))
              (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0))
            )
          )
        )
        (CvtE
          nat
          rat
          (BinE
            PowOp
            nat
            (NumE (Nat 2))
            (CvtE
              int
              nat
              (BinE
                SubOp
                int
                (CvtE nat int (VarE "N"))
                (CvtE nat int (NumE (Nat 1)))
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (OptE
      (CaseE
        Arg
        (TupE
          (CallE
            "inv_signed_"
            (ExpA (VarE "N"))
            (ExpA
              (CallE
                "truncz"
                (ExpA
                  (BinE
                    DivOp
                    rat
                    (CvtE
                      int
                      rat
                      (CallE
                        "signed_"
                        (ExpA (VarE "N"))
                        (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0))
                      )
                    )
                    (CvtE
                      int
                      rat
                      (CallE
                        "signed_"
                        (ExpA (VarE "N"))
                        (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0))
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (VarE "N")
        (CaseE
          Arg
          (TupE
            (CallE
              "inv_signed_"
              (ExpA (VarE "N"))
              (ExpA
                (CallE
                  "truncz"
                  (ExpA
                    (BinE
                      DivOp
                      rat
                      (CvtE
                        int
                        rat
                        (CallE
                          "signed_"
                          (ExpA (VarE "N"))
                          (ExpA
                            (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
                          )
                        )
                      )
                      (CvtE
                        int
                        rat
                        (CallE
                          "signed_"
                          (ExpA (VarE "N"))
                          (ExpA
                            (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "imul_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "iN" (VarT "iN"))
  (VarT "iN")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (BinE
          ModOp
          nat
          (BinE
            MulOp
            nat
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
          )
          (BinE PowOp nat (NumE (Nat 2)) (VarE "N"))
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (VarE "N")
        (CaseE
          Arg
          (TupE
            (BinE
              ModOp
              nat
              (BinE
                MulOp
                nat
                (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
                (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
              )
              (BinE PowOp nat (NumE (Nat 2)) (VarE "N"))
            )
          )
        )
      )
    )
  )
)
(DecD
  "ior_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "iN" (VarT "iN"))
  (VarT "iN")
)
(DecD
  "irem_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "iN" (VarT "iN"))
  (IterT (VarT "iN") Opt)
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
    (OptE)
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (OptE
      (CaseE
        Arg
        (TupE
          (CvtE
            int
            nat
            (BinE
              SubOp
              int
              (CvtE nat int (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0))
              (CvtE
                nat
                int
                (BinE
                  MulOp
                  nat
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
                  (CvtE
                    int
                    nat
                    (CallE
                      "truncz"
                      (ExpA
                        (BinE
                          DivOp
                          rat
                          (CvtE
                            nat
                            rat
                            (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
                          )
                          (CvtE
                            nat
                            rat
                            (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (VarE "N")
        (CaseE
          Arg
          (TupE
            (CvtE
              int
              nat
              (BinE
                SubOp
                int
                (CvtE nat int (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0))
                (CvtE
                  nat
                  int
                  (BinE
                    MulOp
                    nat
                    (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
                    (CvtE
                      int
                      nat
                      (CallE
                        "truncz"
                        (ExpA
                          (BinE
                            DivOp
                            rat
                            (CvtE
                              nat
                              rat
                              (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
                            )
                            (CvtE
                              nat
                              rat
                              (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
    (OptE)
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpP "j_1" int)
    (ExpP "j_2" int)
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (OptE
      (CaseE
        Arg
        (TupE
          (CallE
            "inv_signed_"
            (ExpA (VarE "N"))
            (ExpA
              (BinE
                SubOp
                int
                (VarE "j_1")
                (BinE
                  MulOp
                  int
                  (VarE "j_2")
                  (CallE
                    "truncz"
                    (ExpA
                      (BinE
                        DivOp
                        rat
                        (CvtE int rat (VarE "j_1"))
                        (CvtE int rat (VarE "j_2"))
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE
          EqOp
          bool
          (VarE "j_1")
          (CallE
            "signed_"
            (ExpA (VarE "N"))
            (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0))
          )
        )
        (CmpE
          EqOp
          bool
          (VarE "j_2")
          (CallE
            "signed_"
            (ExpA (VarE "N"))
            (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0))
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (VarE "N")
        (CaseE
          Arg
          (TupE
            (CallE
              "inv_signed_"
              (ExpA (VarE "N"))
              (ExpA
                (BinE
                  SubOp
                  int
                  (VarE "j_1")
                  (BinE
                    MulOp
                    int
                    (VarE "j_2")
                    (CallE
                      "truncz"
                      (ExpA
                        (BinE
                          DivOp
                          rat
                          (CvtE int rat (VarE "j_1"))
                          (CvtE int rat (VarE "j_2"))
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "irotl_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "iN" (VarT "iN"))
  (VarT "iN")
)
(DecD
  "irotr_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "iN" (VarT "iN"))
  (VarT "iN")
)
(DecD
  "ishl_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "u32" (VarT "u32"))
  (VarT "iN")
)
(DecD
  "ishr_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "u32" (VarT "u32"))
  (VarT "iN")
)
(DecD
  "isub_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "iN" (VarT "iN"))
  (VarT "iN")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CvtE
          int
          nat
          (BinE
            ModOp
            int
            (BinE
              SubOp
              int
              (CvtE
                nat
                int
                (BinE
                  AddOp
                  nat
                  (BinE PowOp nat (NumE (Nat 2)) (VarE "N"))
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
                )
              )
              (CvtE nat int (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0))
            )
            (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (VarE "N")))
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (VarE "N")
        (CaseE
          Arg
          (TupE
            (CvtE
              int
              nat
              (BinE
                ModOp
                int
                (BinE
                  SubOp
                  int
                  (CvtE
                    nat
                    int
                    (BinE
                      AddOp
                      nat
                      (BinE PowOp nat (NumE (Nat 2)) (VarE "N"))
                      (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
                    )
                  )
                  (CvtE
                    nat
                    int
                    (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
                  )
                )
                (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (VarE "N")))
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "ixor_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "iN" (VarT "iN"))
  (VarT "iN")
)
(DecD
  "binop_"
  (ExpP "valtype" (VarT "valtype"))
  (ExpP "binop_" (VarT "binop_"))
  (ExpP "val_" (VarT "val_"))
  (ExpP "val_" (VarT "val_"))
  (IterT (IterT (VarT "val_") List) Opt)
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom ADD) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "iadd_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "iadd_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom ADD) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "iadd_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "iadd_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom SUB) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "isub_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "isub_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom SUB) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "isub_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "isub_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom MUL) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "imul_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "imul_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom MUL) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "imul_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "imul_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom DIV) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (CallE
        "list_"
        (TypA (VarT "val_"))
        (ExpA
          (IterE
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0#31"))
            )
            Opt
            (iterexp
              "iter_0#31"
              (CallE
                "idiv_"
                (ExpA
                  (CallE
                    "size"
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "sx"))
                (ExpA (VarE "iN_1"))
                (ExpA (VarE "iN_2"))
              )
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (VarE "iter#21")
        )
      )
      List
      (iterexp
        "iter#21"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0#29"))
              )
              Opt
              (iterexp
                "iter_0#29"
                (CallE
                  "idiv_"
                  (ExpA
                    (CallE
                      "size"
                      (ExpA
                        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                      )
                    )
                  )
                  (ExpA (VarE "sx"))
                  (ExpA (VarE "iN_1"))
                  (ExpA (VarE "iN_2"))
                )
              )
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_uN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
          )
          (VarE "iter#22")
        )
      )
      Opt
      (iterexp
        "iter#22"
        (CallE
          "idiv_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA (VarE "iN_1"))
          (ExpA (VarE "iN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0#30"))
          )
        )
      )
      Opt
      (iterexp
        "iter_0#30"
        (CallE
          "idiv_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA (VarE "iN_1"))
          (ExpA (VarE "iN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom DIV) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (CallE
        "list_"
        (TypA (VarT "val_"))
        (ExpA
          (IterE
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0#34"))
            )
            Opt
            (iterexp
              "iter_0#34"
              (CallE
                "idiv_"
                (ExpA
                  (CallE
                    "size"
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "sx"))
                (ExpA (VarE "iN_1"))
                (ExpA (VarE "iN_2"))
              )
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (VarE "iter#23")
        )
      )
      List
      (iterexp
        "iter#23"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0#32"))
              )
              Opt
              (iterexp
                "iter_0#32"
                (CallE
                  "idiv_"
                  (ExpA
                    (CallE
                      "size"
                      (ExpA
                        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                      )
                    )
                  )
                  (ExpA (VarE "sx"))
                  (ExpA (VarE "iN_1"))
                  (ExpA (VarE "iN_2"))
                )
              )
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_uN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
          )
          (VarE "iter#24")
        )
      )
      Opt
      (iterexp
        "iter#24"
        (CallE
          "idiv_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA (VarE "iN_1"))
          (ExpA (VarE "iN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0#33"))
          )
        )
      )
      Opt
      (iterexp
        "iter_0#33"
        (CallE
          "idiv_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA (VarE "iN_1"))
          (ExpA (VarE "iN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom REM) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (CallE
        "list_"
        (TypA (VarT "val_"))
        (ExpA
          (IterE
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0#37"))
            )
            Opt
            (iterexp
              "iter_0#37"
              (CallE
                "irem_"
                (ExpA
                  (CallE
                    "size"
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "sx"))
                (ExpA (VarE "iN_1"))
                (ExpA (VarE "iN_2"))
              )
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (VarE "iter#25")
        )
      )
      List
      (iterexp
        "iter#25"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0#35"))
              )
              Opt
              (iterexp
                "iter_0#35"
                (CallE
                  "irem_"
                  (ExpA
                    (CallE
                      "size"
                      (ExpA
                        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                      )
                    )
                  )
                  (ExpA (VarE "sx"))
                  (ExpA (VarE "iN_1"))
                  (ExpA (VarE "iN_2"))
                )
              )
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_uN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
          )
          (VarE "iter#26")
        )
      )
      Opt
      (iterexp
        "iter#26"
        (CallE
          "irem_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA (VarE "iN_1"))
          (ExpA (VarE "iN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0#36"))
          )
        )
      )
      Opt
      (iterexp
        "iter_0#36"
        (CallE
          "irem_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA (VarE "iN_1"))
          (ExpA (VarE "iN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom REM) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (CallE
        "list_"
        (TypA (VarT "val_"))
        (ExpA
          (IterE
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0#40"))
            )
            Opt
            (iterexp
              "iter_0#40"
              (CallE
                "irem_"
                (ExpA
                  (CallE
                    "size"
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "sx"))
                (ExpA (VarE "iN_1"))
                (ExpA (VarE "iN_2"))
              )
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (VarE "iter#27")
        )
      )
      List
      (iterexp
        "iter#27"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0#38"))
              )
              Opt
              (iterexp
                "iter_0#38"
                (CallE
                  "irem_"
                  (ExpA
                    (CallE
                      "size"
                      (ExpA
                        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                      )
                    )
                  )
                  (ExpA (VarE "sx"))
                  (ExpA (VarE "iN_1"))
                  (ExpA (VarE "iN_2"))
                )
              )
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_uN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
          )
          (VarE "iter#28")
        )
      )
      Opt
      (iterexp
        "iter#28"
        (CallE
          "irem_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA (VarE "iN_1"))
          (ExpA (VarE "iN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0#39"))
          )
        )
      )
      Opt
      (iterexp
        "iter_0#39"
        (CallE
          "irem_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA (VarE "iN_1"))
          (ExpA (VarE "iN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom AND) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "iand_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "iand_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom AND) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "iand_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "iand_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom OR) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ior_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ior_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom OR) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "ior_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "ior_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom XOR) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ixor_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ixor_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom XOR) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "ixor_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "ixor_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom SHL) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ishl_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA
                (CaseE
                  Arg
                  (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                )
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ishl_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA
                (CaseE
                  Arg
                  (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom SHL) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "ishl_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA
                (CaseE
                  Arg
                  (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                )
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "ishl_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA
                (CaseE
                  Arg
                  (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom SHR) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ishr_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN_1"))
              (ExpA
                (CaseE
                  Arg
                  (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                )
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ishr_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN_1"))
              (ExpA
                (CaseE
                  Arg
                  (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom SHR) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "ishr_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN_1"))
              (ExpA
                (CaseE
                  Arg
                  (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                )
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "ishr_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN_1"))
              (ExpA
                (CaseE
                  Arg
                  (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom ROTL) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "irotl_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "irotl_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom ROTL) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "irotl_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "irotl_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom ROTR) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "irotr_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "irotr_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom ROTR) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "irotr_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "irotr_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom ADD) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#42"))
        )
        List
        (iterexp
          "iter_0#42"
          (CallE
            "fadd_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          )
          (VarE "iter#29")
        )
      )
      List
      (iterexp
        "iter#29"
        (CallE
          "fadd_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#41"))
          )
        )
      )
      List
      (iterexp
        "iter_0#41"
        (CallE
          "fadd_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom ADD) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#44"))
        )
        List
        (iterexp
          "iter_0#44"
          (CallE
            "fadd_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          )
          (VarE "iter#30")
        )
      )
      List
      (iterexp
        "iter#30"
        (CallE
          "fadd_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#43"))
          )
        )
      )
      List
      (iterexp
        "iter_0#43"
        (CallE
          "fadd_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom SUB) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#46"))
        )
        List
        (iterexp
          "iter_0#46"
          (CallE
            "fsub_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          )
          (VarE "iter#31")
        )
      )
      List
      (iterexp
        "iter#31"
        (CallE
          "fsub_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#45"))
          )
        )
      )
      List
      (iterexp
        "iter_0#45"
        (CallE
          "fsub_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom SUB) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#48"))
        )
        List
        (iterexp
          "iter_0#48"
          (CallE
            "fsub_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          )
          (VarE "iter#32")
        )
      )
      List
      (iterexp
        "iter#32"
        (CallE
          "fsub_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#47"))
          )
        )
      )
      List
      (iterexp
        "iter_0#47"
        (CallE
          "fsub_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom MUL) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#50"))
        )
        List
        (iterexp
          "iter_0#50"
          (CallE
            "fmul_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          )
          (VarE "iter#33")
        )
      )
      List
      (iterexp
        "iter#33"
        (CallE
          "fmul_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#49"))
          )
        )
      )
      List
      (iterexp
        "iter_0#49"
        (CallE
          "fmul_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom MUL) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#52"))
        )
        List
        (iterexp
          "iter_0#52"
          (CallE
            "fmul_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          )
          (VarE "iter#34")
        )
      )
      List
      (iterexp
        "iter#34"
        (CallE
          "fmul_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#51"))
          )
        )
      )
      List
      (iterexp
        "iter_0#51"
        (CallE
          "fmul_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom DIV) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#54"))
        )
        List
        (iterexp
          "iter_0#54"
          (CallE
            "fdiv_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          )
          (VarE "iter#35")
        )
      )
      List
      (iterexp
        "iter#35"
        (CallE
          "fdiv_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#53"))
          )
        )
      )
      List
      (iterexp
        "iter_0#53"
        (CallE
          "fdiv_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom DIV) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#56"))
        )
        List
        (iterexp
          "iter_0#56"
          (CallE
            "fdiv_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          )
          (VarE "iter#36")
        )
      )
      List
      (iterexp
        "iter#36"
        (CallE
          "fdiv_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#55"))
          )
        )
      )
      List
      (iterexp
        "iter_0#55"
        (CallE
          "fdiv_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom MIN) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#58"))
        )
        List
        (iterexp
          "iter_0#58"
          (CallE
            "fmin_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          )
          (VarE "iter#37")
        )
      )
      List
      (iterexp
        "iter#37"
        (CallE
          "fmin_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#57"))
          )
        )
      )
      List
      (iterexp
        "iter_0#57"
        (CallE
          "fmin_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom MIN) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#60"))
        )
        List
        (iterexp
          "iter_0#60"
          (CallE
            "fmin_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          )
          (VarE "iter#38")
        )
      )
      List
      (iterexp
        "iter#38"
        (CallE
          "fmin_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#59"))
          )
        )
      )
      List
      (iterexp
        "iter_0#59"
        (CallE
          "fmin_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom MAX) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#62"))
        )
        List
        (iterexp
          "iter_0#62"
          (CallE
            "fmax_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          )
          (VarE "iter#39")
        )
      )
      List
      (iterexp
        "iter#39"
        (CallE
          "fmax_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#61"))
          )
        )
      )
      List
      (iterexp
        "iter_0#61"
        (CallE
          "fmax_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom MAX) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#64"))
        )
        List
        (iterexp
          "iter_0#64"
          (CallE
            "fmax_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          )
          (VarE "iter#40")
        )
      )
      List
      (iterexp
        "iter#40"
        (CallE
          "fmax_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#63"))
          )
        )
      )
      List
      (iterexp
        "iter_0#63"
        (CallE
          "fmax_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom COPYSIGN) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#66"))
        )
        List
        (iterexp
          "iter_0#66"
          (CallE
            "fcopysign_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          )
          (VarE "iter#41")
        )
      )
      List
      (iterexp
        "iter#41"
        (CallE
          "fcopysign_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#65"))
          )
        )
      )
      List
      (iterexp
        "iter_0#65"
        (CallE
          "fcopysign_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom COPYSIGN) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#68"))
        )
        List
        (iterexp
          "iter_0#68"
          (CallE
            "fcopysign_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_fN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          )
          (VarE "iter#42")
        )
      )
      List
      (iterexp
        "iter#42"
        (CallE
          "fcopysign_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#67"))
          )
        )
      )
      List
      (iterexp
        "iter_0#67"
        (CallE
          "fcopysign_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "fN_1"))
          (ExpA (VarE "fN_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "binop_"))
    (ExpP "x2" (VarT "val_"))
    (ExpP "x3" (VarT "val_"))
    (ExpA (VarE "x0"))
    (ExpA (VarE "x1"))
    (ExpA (VarE "x2"))
    (ExpA (VarE "x3"))
    (OptE)
    ElsePr
  )
)
(HintD (DecH "binop_" (hint "partial" "{}")))
(HintD (DecH "binop_" (hint "show" "%2#$_(%1)#(%3, %4)")))
(DecD
  "ieqz_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN"))
  (VarT "u32")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (VarE "i_1"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              EqOp
              bool
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
              (NumE (Nat 0))
            )
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          Arg
          (TupE
            (CallE
              "bool"
              (ExpA
                (CmpE
                  EqOp
                  bool
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
                  (NumE (Nat 0))
                )
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "testop_"
  (ExpP "valtype" (VarT "valtype"))
  (ExpP "testop_" (VarT "testop_"))
  (ExpP "val_" (VarT "val_"))
  (IterT (VarT "val_") Opt)
  (DefD
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_testop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom EQZ) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "ieqz_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
              )
            )
            (ExpA (VarE "iN"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ieqz_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_testop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom EQZ) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "ieqz_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
              )
            )
            (ExpA (VarE "iN"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ieqz_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "testop_"))
    (ExpP "x2" (VarT "val_"))
    (ExpA (VarE "x0"))
    (ExpA (VarE "x1"))
    (ExpA (VarE "x2"))
    (OptE)
    ElsePr
  )
)
(HintD (DecH "testop_" (hint "partial" "{}")))
(HintD (DecH "testop_" (hint "show" "%2#$_(%1)#((%3))")))
(DecD
  "feq_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (ExpP "fN" (VarT "fN"))
  (VarT "u32")
)
(DecD
  "fge_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (ExpP "fN" (VarT "fN"))
  (VarT "u32")
)
(DecD
  "fgt_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (ExpP "fN" (VarT "fN"))
  (VarT "u32")
)
(DecD
  "fle_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (ExpP "fN" (VarT "fN"))
  (VarT "u32")
)
(DecD
  "flt_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (ExpP "fN" (VarT "fN"))
  (VarT "u32")
)
(DecD
  "fne_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (ExpP "fN" (VarT "fN"))
  (VarT "u32")
)
(DecD
  "ieq_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "iN" (VarT "iN"))
  (VarT "u32")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE (CallE "bool" (ExpA (CmpE EqOp bool (VarE "i_1") (VarE "i_2")))))
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          Arg
          (TupE
            (CallE "bool" (ExpA (CmpE EqOp bool (VarE "i_1") (VarE "i_2"))))
          )
        )
      )
    )
  )
)
(DecD
  "ige_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "iN" (VarT "iN"))
  (VarT "u32")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              GeOp
              nat
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
            )
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          Arg
          (TupE
            (CallE
              "bool"
              (ExpA
                (CmpE
                  GeOp
                  nat
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              GeOp
              int
              (CallE
                "signed_"
                (ExpA (VarE "N"))
                (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0))
              )
              (CallE
                "signed_"
                (ExpA (VarE "N"))
                (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0))
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          Arg
          (TupE
            (CallE
              "bool"
              (ExpA
                (CmpE
                  GeOp
                  int
                  (CallE
                    "signed_"
                    (ExpA (VarE "N"))
                    (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0))
                  )
                  (CallE
                    "signed_"
                    (ExpA (VarE "N"))
                    (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0))
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "igt_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "iN" (VarT "iN"))
  (VarT "u32")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              GtOp
              nat
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
            )
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          Arg
          (TupE
            (CallE
              "bool"
              (ExpA
                (CmpE
                  GtOp
                  nat
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              GtOp
              int
              (CallE
                "signed_"
                (ExpA (VarE "N"))
                (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0))
              )
              (CallE
                "signed_"
                (ExpA (VarE "N"))
                (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0))
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          Arg
          (TupE
            (CallE
              "bool"
              (ExpA
                (CmpE
                  GtOp
                  int
                  (CallE
                    "signed_"
                    (ExpA (VarE "N"))
                    (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0))
                  )
                  (CallE
                    "signed_"
                    (ExpA (VarE "N"))
                    (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0))
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "ile_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "iN" (VarT "iN"))
  (VarT "u32")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              LeOp
              nat
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
            )
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          Arg
          (TupE
            (CallE
              "bool"
              (ExpA
                (CmpE
                  LeOp
                  nat
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              LeOp
              int
              (CallE
                "signed_"
                (ExpA (VarE "N"))
                (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0))
              )
              (CallE
                "signed_"
                (ExpA (VarE "N"))
                (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0))
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          Arg
          (TupE
            (CallE
              "bool"
              (ExpA
                (CmpE
                  LeOp
                  int
                  (CallE
                    "signed_"
                    (ExpA (VarE "N"))
                    (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0))
                  )
                  (CallE
                    "signed_"
                    (ExpA (VarE "N"))
                    (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0))
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "ilt_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "iN" (VarT "iN"))
  (VarT "u32")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              LtOp
              nat
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
            )
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          Arg
          (TupE
            (CallE
              "bool"
              (ExpA
                (CmpE
                  LtOp
                  nat
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              LtOp
              int
              (CallE
                "signed_"
                (ExpA (VarE "N"))
                (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0))
              )
              (CallE
                "signed_"
                (ExpA (VarE "N"))
                (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0))
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          Arg
          (TupE
            (CallE
              "bool"
              (ExpA
                (CmpE
                  LtOp
                  int
                  (CallE
                    "signed_"
                    (ExpA (VarE "N"))
                    (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0))
                  )
                  (CallE
                    "signed_"
                    (ExpA (VarE "N"))
                    (ExpA (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0))
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "ine_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN"))
  (ExpP "iN" (VarT "iN"))
  (VarT "u32")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE (CallE "bool" (ExpA (CmpE NeOp bool (VarE "i_1") (VarE "i_2")))))
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          Arg
          (TupE
            (CallE "bool" (ExpA (CmpE NeOp bool (VarE "i_1") (VarE "i_2"))))
          )
        )
      )
    )
  )
)
(DecD
  "relop_"
  (ExpP "valtype" (VarT "valtype"))
  (ExpP "relop_" (VarT "relop_"))
  (ExpP "val_" (VarT "val_"))
  (ExpP "val_" (VarT "val_"))
  (IterT (VarT "val_") Opt)
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom EQ) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "ieq_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
              )
            )
            (ExpA (VarE "iN_1"))
            (ExpA (VarE "iN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ieq_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom EQ) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "ieq_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
              )
            )
            (ExpA (VarE "iN_1"))
            (ExpA (VarE "iN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ieq_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom NE) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "ine_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
              )
            )
            (ExpA (VarE "iN_1"))
            (ExpA (VarE "iN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ine_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom NE) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "ine_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
              )
            )
            (ExpA (VarE "iN_1"))
            (ExpA (VarE "iN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ine_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom LT) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "ilt_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
              )
            )
            (ExpA (VarE "sx"))
            (ExpA (VarE "iN_1"))
            (ExpA (VarE "iN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ilt_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom LT) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "ilt_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
              )
            )
            (ExpA (VarE "sx"))
            (ExpA (VarE "iN_1"))
            (ExpA (VarE "iN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ilt_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom GT) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "igt_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
              )
            )
            (ExpA (VarE "sx"))
            (ExpA (VarE "iN_1"))
            (ExpA (VarE "iN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "igt_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom GT) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "igt_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
              )
            )
            (ExpA (VarE "sx"))
            (ExpA (VarE "iN_1"))
            (ExpA (VarE "iN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "igt_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom LE) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "ile_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
              )
            )
            (ExpA (VarE "sx"))
            (ExpA (VarE "iN_1"))
            (ExpA (VarE "iN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ile_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom LE) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "ile_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
              )
            )
            (ExpA (VarE "sx"))
            (ExpA (VarE "iN_1"))
            (ExpA (VarE "iN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ile_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom GE) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "ige_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
              )
            )
            (ExpA (VarE "sx"))
            (ExpA (VarE "iN_1"))
            (ExpA (VarE "iN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ige_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom GE) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "ige_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
              )
            )
            (ExpA (VarE "sx"))
            (ExpA (VarE "iN_1"))
            (ExpA (VarE "iN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "ige_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN_1"))
              (ExpA (VarE "iN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom EQ) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "feq_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "feq_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
                )
              )
              (ExpA (VarE "fN_1"))
              (ExpA (VarE "fN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom EQ) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "feq_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "feq_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
                )
              )
              (ExpA (VarE "fN_1"))
              (ExpA (VarE "fN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom NE) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "fne_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "fne_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
                )
              )
              (ExpA (VarE "fN_1"))
              (ExpA (VarE "fN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom NE) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "fne_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "fne_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
                )
              )
              (ExpA (VarE "fN_1"))
              (ExpA (VarE "fN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom LT) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "flt_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "flt_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
                )
              )
              (ExpA (VarE "fN_1"))
              (ExpA (VarE "fN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom LT) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "flt_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "flt_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
                )
              )
              (ExpA (VarE "fN_1"))
              (ExpA (VarE "fN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom GT) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "fgt_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "fgt_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
                )
              )
              (ExpA (VarE "fN_1"))
              (ExpA (VarE "fN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom GT) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "fgt_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "fgt_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
                )
              )
              (ExpA (VarE "fN_1"))
              (ExpA (VarE "fN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom LE) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "fle_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "fle_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
                )
              )
              (ExpA (VarE "fN_1"))
              (ExpA (VarE "fN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom LE) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "fle_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "fle_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
                )
              )
              (ExpA (VarE "fN_1"))
              (ExpA (VarE "fN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom GE) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "fge_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "fge_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
                )
              )
              (ExpA (VarE "fN_1"))
              (ExpA (VarE "fN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom GE) (TupE)))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
    )
    (OptE
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CallE
            "fge_"
            (ExpA
              (CallE
                "size"
                (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
              )
            )
            (ExpA (VarE "fN_1"))
            (ExpA (VarE "fN_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "fge_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
                )
              )
              (ExpA (VarE "fN_1"))
              (ExpA (VarE "fN_2"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "relop_"))
    (ExpP "x2" (VarT "val_"))
    (ExpP "x3" (VarT "val_"))
    (ExpA (VarE "x0"))
    (ExpA (VarE "x1"))
    (ExpA (VarE "x2"))
    (ExpA (VarE "x3"))
    (OptE)
    ElsePr
  )
)
(HintD (DecH "relop_" (hint "partial" "{}")))
(HintD (DecH "relop_" (hint "show" "%2#$_(%1)#(%3, %4)")))
(DecD
  "convert__"
  (ExpP "M" (VarT "M"))
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN"))
  (VarT "fN")
)
(DecD
  "demote__"
  (ExpP "M" (VarT "M"))
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "extend__"
  (ExpP "M" (VarT "M"))
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN"))
  (VarT "iN")
)
(DecD
  "promote__"
  (ExpP "M" (VarT "M"))
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "reinterpret__"
  (ExpP "valtype_1" (VarT "valtype"))
  (ExpP "valtype_2" (VarT "valtype"))
  (ExpP "val_" (VarT "val_"))
  (VarT "val_")
)
(DecD
  "trunc__"
  (ExpP "M" (VarT "M"))
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "iN") Opt)
)
(DecD
  "wrap__"
  (ExpP "M" (VarT "M"))
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN"))
  (VarT "iN")
)
(DecD
  "cvtop__"
  (ExpP "valtype_1" (VarT "valtype"))
  (ExpP "valtype_2" (VarT "valtype"))
  (ExpP "cvtop" (VarT "cvtop"))
  (ExpP "val_" (VarT "val_"))
  (IterT (IterT (VarT "val_") List) Opt)
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA (CaseE (Seq (Atom EXTEND) Arg) (TupE (VarE "sx"))))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "extend__"
              (ExpA (NumE (Nat 32)))
              (ExpA (NumE (Nat 64)))
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I64) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "extend__"
              (ExpA (NumE (Nat 32)))
              (ExpA (NumE (Nat 64)))
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA (CaseE (Atom WRAP) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "wrap__"
              (ExpA (NumE (Nat 64)))
              (ExpA (NumE (Nat 32)))
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "wrap__"
              (ExpA (NumE (Nat 64)))
              (ExpA (NumE (Nat 32)))
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA (CaseE (Seq (Atom TRUNC) Arg) (TupE (VarE "sx"))))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (CallE
        "list_"
        (TypA (VarT "val_"))
        (ExpA
          (IterE
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0#71"))
            )
            Opt
            (iterexp
              "iter_0#71"
              (CallE
                "trunc__"
                (ExpA
                  (CallE
                    "size"
                    (ExpA
                      (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
                    )
                  )
                )
                (ExpA
                  (CallE
                    "size"
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "sx"))
                (ExpA (VarE "fN"))
              )
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (VarE "iter#43")
        )
      )
      List
      (iterexp
        "iter#43"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0#69"))
              )
              Opt
              (iterexp
                "iter_0#69"
                (CallE
                  "trunc__"
                  (ExpA
                    (CallE
                      "size"
                      (ExpA
                        (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
                      )
                    )
                  )
                  (ExpA
                    (CallE
                      "size"
                      (ExpA
                        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                      )
                    )
                  )
                  (ExpA (VarE "sx"))
                  (ExpA (VarE "fN"))
                )
              )
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_uN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
          )
          (VarE "iter#44")
        )
      )
      Opt
      (iterexp
        "iter#44"
        (CallE
          "trunc__"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0#70"))
          )
        )
      )
      Opt
      (iterexp
        "iter_0#70"
        (CallE
          "trunc__"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA (CaseE (Seq (Atom TRUNC) Arg) (TupE (VarE "sx"))))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (CallE
        "list_"
        (TypA (VarT "val_"))
        (ExpA
          (IterE
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0#74"))
            )
            Opt
            (iterexp
              "iter_0#74"
              (CallE
                "trunc__"
                (ExpA
                  (CallE
                    "size"
                    (ExpA
                      (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
                    )
                  )
                )
                (ExpA
                  (CallE
                    "size"
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "sx"))
                (ExpA (VarE "fN"))
              )
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (VarE "iter#45")
        )
      )
      List
      (iterexp
        "iter#45"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0#72"))
              )
              Opt
              (iterexp
                "iter_0#72"
                (CallE
                  "trunc__"
                  (ExpA
                    (CallE
                      "size"
                      (ExpA
                        (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
                      )
                    )
                  )
                  (ExpA
                    (CallE
                      "size"
                      (ExpA
                        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                      )
                    )
                  )
                  (ExpA (VarE "sx"))
                  (ExpA (VarE "fN"))
                )
              )
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_uN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
          )
          (VarE "iter#46")
        )
      )
      Opt
      (iterexp
        "iter#46"
        (CallE
          "trunc__"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0#73"))
          )
        )
      )
      Opt
      (iterexp
        "iter_0#73"
        (CallE
          "trunc__"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA (CaseE (Seq (Atom TRUNC) Arg) (TupE (VarE "sx"))))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (CallE
        "list_"
        (TypA (VarT "val_"))
        (ExpA
          (IterE
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0#77"))
            )
            Opt
            (iterexp
              "iter_0#77"
              (CallE
                "trunc__"
                (ExpA
                  (CallE
                    "size"
                    (ExpA
                      (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
                    )
                  )
                )
                (ExpA
                  (CallE
                    "size"
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "sx"))
                (ExpA (VarE "fN"))
              )
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (VarE "iter#47")
        )
      )
      List
      (iterexp
        "iter#47"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0#75"))
              )
              Opt
              (iterexp
                "iter_0#75"
                (CallE
                  "trunc__"
                  (ExpA
                    (CallE
                      "size"
                      (ExpA
                        (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
                      )
                    )
                  )
                  (ExpA
                    (CallE
                      "size"
                      (ExpA
                        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                      )
                    )
                  )
                  (ExpA (VarE "sx"))
                  (ExpA (VarE "fN"))
                )
              )
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_uN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
          )
          (VarE "iter#48")
        )
      )
      Opt
      (iterexp
        "iter#48"
        (CallE
          "trunc__"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0#76"))
          )
        )
      )
      Opt
      (iterexp
        "iter_0#76"
        (CallE
          "trunc__"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA (CaseE (Seq (Atom TRUNC) Arg) (TupE (VarE "sx"))))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (CallE
        "list_"
        (TypA (VarT "val_"))
        (ExpA
          (IterE
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0#80"))
            )
            Opt
            (iterexp
              "iter_0#80"
              (CallE
                "trunc__"
                (ExpA
                  (CallE
                    "size"
                    (ExpA
                      (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
                    )
                  )
                )
                (ExpA
                  (CallE
                    "size"
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "sx"))
                (ExpA (VarE "fN"))
              )
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (VarE "iter#49")
        )
      )
      List
      (iterexp
        "iter#49"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0#78"))
              )
              Opt
              (iterexp
                "iter_0#78"
                (CallE
                  "trunc__"
                  (ExpA
                    (CallE
                      "size"
                      (ExpA
                        (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
                      )
                    )
                  )
                  (ExpA
                    (CallE
                      "size"
                      (ExpA
                        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                      )
                    )
                  )
                  (ExpA (VarE "sx"))
                  (ExpA (VarE "fN"))
                )
              )
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_uN"
        (Seq Arg Arg)
        (TupE
          (CallE
            "size"
            (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
          )
          (VarE "iter#50")
        )
      )
      Opt
      (iterexp
        "iter#50"
        (CallE
          "trunc__"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0#79"))
          )
        )
      )
      Opt
      (iterexp
        "iter_0#79"
        (CallE
          "trunc__"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA (CaseE (Atom PROMOTE) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0"))
        )
        List
        (iterexp
          "iter_0"
          (CallE
            "promote__"
            (ExpA (NumE (Nat 32)))
            (ExpA (NumE (Nat 64)))
            (ExpA (VarE "fN"))
          )
        )
      )
    )
    (IterPr
      (RulePr "wf_fN" (Seq Arg Arg) (TupE (NumE (Nat 64)) (VarE "iter#51")))
      List
      (iterexp
        "iter#51"
        (CallE
          "promote__"
          (ExpA (NumE (Nat 32)))
          (ExpA (NumE (Nat 64)))
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0#81"))
          )
        )
      )
      List
      (iterexp
        "iter_0#81"
        (CallE
          "promote__"
          (ExpA (NumE (Nat 32)))
          (ExpA (NumE (Nat 64)))
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA (CaseE (Atom DEMOTE) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (IterE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0"))
        )
        List
        (iterexp
          "iter_0"
          (CallE
            "demote__"
            (ExpA (NumE (Nat 64)))
            (ExpA (NumE (Nat 32)))
            (ExpA (VarE "fN"))
          )
        )
      )
    )
    (IterPr
      (RulePr "wf_fN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "iter#52")))
      List
      (iterexp
        "iter#52"
        (CallE
          "demote__"
          (ExpA (NumE (Nat 64)))
          (ExpA (NumE (Nat 32)))
          (ExpA (VarE "fN"))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0#82"))
          )
        )
      )
      List
      (iterexp
        "iter_0#82"
        (CallE
          "demote__"
          (ExpA (NumE (Nat 64)))
          (ExpA (NumE (Nat 32)))
          (ExpA (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA (CaseE (Seq (Atom CONVERT) Arg) (TupE (VarE "sx"))))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE
            (CaseE (Atom F32) (TupE))
            (CallE
              "convert__"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE
            (CaseE (Atom F32) (TupE))
            (CallE
              "convert__"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA (CaseE (Seq (Atom CONVERT) Arg) (TupE (VarE "sx"))))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE
            (CaseE (Atom F32) (TupE))
            (CallE
              "convert__"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE
            (CaseE (Atom F32) (TupE))
            (CallE
              "convert__"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA (CaseE (Seq (Atom CONVERT) Arg) (TupE (VarE "sx"))))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE
            (CaseE (Atom F64) (TupE))
            (CallE
              "convert__"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE
            (CaseE (Atom F64) (TupE))
            (CallE
              "convert__"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA (CaseE (Seq (Atom CONVERT) Arg) (TupE (VarE "sx"))))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (ListE
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE
            (CaseE (Atom F64) (TupE))
            (CallE
              "convert__"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE
            (CaseE (Atom F64) (TupE))
            (CallE
              "convert__"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
                )
              )
              (ExpA (VarE "sx"))
              (ExpA (VarE "iN"))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA (CaseE (Atom REINTERPRET) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (ListE
        (CallE
          "reinterpret__"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          (ExpA
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "iN"))
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (CallE
          "size"
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
        (CallE
          "reinterpret__"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          (ExpA
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "iN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "iN"))
        )
      )
    )
  )
  (DefD
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA (CaseE (Atom REINTERPRET) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (ListE
        (CallE
          "reinterpret__"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          (ExpA
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I64) (TupE)) (VarE "iN"))
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (CallE
          "size"
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
        (CallE
          "reinterpret__"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          (ExpA
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I64) (TupE)) (VarE "iN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I64) (TupE)) (VarE "iN"))
        )
      )
    )
  )
  (DefD
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA (CaseE (Atom REINTERPRET) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (ListE
        (CallE
          "reinterpret__"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          (ExpA
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "iN"))
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (CallE
          "size"
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
        (CallE
          "reinterpret__"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          (ExpA
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "iN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "iN"))
        )
      )
    )
  )
  (DefD
    (ExpP "iN" (VarT "uN"))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA (CaseE (Atom REINTERPRET) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN"))
      )
    )
    (OptE
      (ListE
        (CallE
          "reinterpret__"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          (ExpA
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I64) (TupE)) (VarE "iN"))
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (CallE
          "size"
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
        (CallE
          "reinterpret__"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          (ExpA
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I64) (TupE)) (VarE "iN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I64) (TupE)) (VarE "iN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA (CaseE (Atom REINTERPRET) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (ListE
        (CallE
          "reinterpret__"
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
          (ExpA
            (CaseE
              (Seq (Atom mk_val__1) Arg Arg)
              (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (CallE
          "size"
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CallE
          "reinterpret__"
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
          (ExpA
            (CaseE
              (Seq (Atom mk_val__1) Arg Arg)
              (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA (CaseE (Atom I32) (TupE)))
    (ExpA (CaseE (Atom REINTERPRET) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (ListE
        (CallE
          "reinterpret__"
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
          (ExpA
            (CaseE
              (Seq (Atom mk_val__1) Arg Arg)
              (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (CallE
          "size"
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CallE
          "reinterpret__"
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
          (ExpA
            (CaseE
              (Seq (Atom mk_val__1) Arg Arg)
              (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F32) (TupE)))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA (CaseE (Atom REINTERPRET) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (ListE
        (CallE
          "reinterpret__"
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
          (ExpA
            (CaseE
              (Seq (Atom mk_val__1) Arg Arg)
              (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (CallE
          "size"
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CallE
          "reinterpret__"
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
          (ExpA
            (CaseE
              (Seq (Atom mk_val__1) Arg Arg)
              (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F32) (TupE)) (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "fN" (VarT "fN"))
    (ExpA (CaseE (Atom F64) (TupE)))
    (ExpA (CaseE (Atom I64) (TupE)))
    (ExpA (CaseE (Atom REINTERPRET) (TupE)))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
      )
    )
    (OptE
      (ListE
        (CallE
          "reinterpret__"
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
          (ExpA
            (CaseE
              (Seq (Atom mk_val__1) Arg Arg)
              (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (CallE
          "size"
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CallE
          "reinterpret__"
          (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
          (ExpA
            (CaseE
              (Seq (Atom mk_val__1) Arg Arg)
              (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE (CaseE (Atom F64) (TupE)) (VarE "fN"))
        )
      )
    )
  )
  (DefD
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "valtype"))
    (ExpP "x2" (VarT "cvtop"))
    (ExpP "x3" (VarT "val_"))
    (ExpA (VarE "x0"))
    (ExpA (VarE "x1"))
    (ExpA (VarE "x2"))
    (ExpA (VarE "x3"))
    (OptE)
    ElsePr
  )
)
(HintD (DecH "cvtop__" (hint "partial" "{}")))
(HintD (DecH "cvtop__" (hint "show" "%3#$__(%1, %2)#((%4))")))
(HintD (DecH "extend__" (hint "show" "$extend__(%, %)^(%)#((%))")))
(HintD (DecH "trunc__" (hint "show" "$trunc__(%, %)^(%)#((%))")))
(HintD (DecH "convert__" (hint "show" "$convert__(%, %)^(%)#((%))")))
(HintD (DecH "wrap__" (hint "builtin" "{}")))
(HintD (DecH "extend__" (hint "builtin" "{}")))
(HintD (DecH "trunc__" (hint "builtin" "{}")))
(HintD (DecH "demote__" (hint "builtin" "{}")))
(HintD (DecH "promote__" (hint "builtin" "{}")))
(HintD (DecH "convert__" (hint "builtin" "{}")))
(HintD (DecH "reinterpret__" (hint "builtin" "{}")))
(DecD
  "ibytes_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN"))
  (IterT (VarT "byte") List)
)
(HintD
  (DecH
    "ibytes_"
    (hint "show" "$bytes_(I#%, %)")
    (hint "inverse" "$inv_ibytes_")
  )
)
(DecD
  "fbytes_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN"))
  (IterT (VarT "byte") List)
)
(HintD
  (DecH
    "fbytes_"
    (hint "show" "$bytes_(F#%, %)")
    (hint "inverse" "$inv_fbytes_")
  )
)
(DecD
  "bytes_"
  (ExpP "valtype" (VarT "valtype"))
  (ExpP "val_" (VarT "val_"))
  (IterT (VarT "byte") List)
)
(HintD (DecH "bytes_" (hint "inverse" "$inv_bytes_")))
(DecD
  "inv_ibytes_"
  (ExpP "N" (VarT "N"))
  (ExpP "_" (IterT (VarT "byte") List))
  (VarT "iN")
)
(HintD (DecH "inv_ibytes_" (hint "show" "$bytes_(I#%, %)")))
(DecD
  "inv_fbytes_"
  (ExpP "N" (VarT "N"))
  (ExpP "_" (IterT (VarT "byte") List))
  (VarT "fN")
)
(HintD (DecH "inv_fbytes_" (hint "show" "$bytes_(F#%, %)")))
(DecD
  "inv_bytes_"
  (ExpP "valtype" (VarT "valtype"))
  (ExpP "_" (IterT (VarT "byte") List))
  (VarT "val_")
)
(HintD (DecH "inv_bytes_" (hint "show" "$bytes_(%, %)")))
(HintD (DecH "ibytes_" (hint "builtin" "{}")))
(HintD (DecH "fbytes_" (hint "builtin" "{}")))
(HintD (DecH "bytes_" (hint "builtin" "{}")))
(HintD (DecH "inv_ibytes_" (hint "builtin" "{}")))
(HintD (DecH "inv_fbytes_" (hint "builtin" "{}")))
(HintD (DecH "inv_bytes_" (hint "builtin" "{}")))
(HintD (DecH "idiv_" (hint "show" "$idiv_(%)^(%)#((%, %))")))
(HintD (DecH "irem_" (hint "show" "$irem_(%)^(%)#((%, %))")))
(DecD "inot_" (ExpP "N" (VarT "N")) (ExpP "iN" (VarT "iN")) (VarT "iN"))
(HintD (DecH "ishr_" (hint "show" "$ishr_(%)^(%)#((%, %))")))
(DecD
  "inez_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN"))
  (VarT "u32")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpA (VarE "N"))
    (ExpA (VarE "i_1"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              NeOp
              bool
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
              (NumE (Nat 0))
            )
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          Arg
          (TupE
            (CallE
              "bool"
              (ExpA
                (CmpE
                  NeOp
                  bool
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
                  (NumE (Nat 0))
                )
              )
            )
          )
        )
      )
    )
  )
)
(HintD (DecH "ilt_" (hint "show" "$ilt_(%)^(%)#((%, %))")))
(HintD (DecH "igt_" (hint "show" "$igt_(%)^(%)#((%, %))")))
(HintD (DecH "ile_" (hint "show" "$ile_(%)^(%)#((%, %))")))
(HintD (DecH "ige_" (hint "show" "$ige_(%)^(%)#((%, %))")))
(HintD (DecH "inot_" (hint "builtin" "{}")))
(HintD (DecH "iand_" (hint "builtin" "{}")))
(HintD (DecH "ior_" (hint "builtin" "{}")))
(HintD (DecH "ixor_" (hint "builtin" "{}")))
(HintD (DecH "ishl_" (hint "builtin" "{}")))
(HintD (DecH "ishr_" (hint "builtin" "{}")))
(HintD (DecH "irotl_" (hint "builtin" "{}")))
(HintD (DecH "irotr_" (hint "builtin" "{}")))
(HintD (DecH "iclz_" (hint "builtin" "{}")))
(HintD (DecH "ictz_" (hint "builtin" "{}")))
(HintD (DecH "ipopcnt_" (hint "builtin" "{}")))
(HintD (DecH "fadd_" (hint "builtin" "{}")))
(HintD (DecH "fsub_" (hint "builtin" "{}")))
(HintD (DecH "fmul_" (hint "builtin" "{}")))
(HintD (DecH "fdiv_" (hint "builtin" "{}")))
(HintD (DecH "fmin_" (hint "builtin" "{}")))
(HintD (DecH "fmax_" (hint "builtin" "{}")))
(HintD (DecH "fcopysign_" (hint "builtin" "{}")))
(HintD (DecH "fabs_" (hint "builtin" "{}")))
(HintD (DecH "fneg_" (hint "builtin" "{}")))
(HintD (DecH "fsqrt_" (hint "builtin" "{}")))
(HintD (DecH "fceil_" (hint "builtin" "{}")))
(HintD (DecH "ffloor_" (hint "builtin" "{}")))
(HintD (DecH "ftrunc_" (hint "builtin" "{}")))
(HintD (DecH "fnearest_" (hint "builtin" "{}")))
(HintD (DecH "feq_" (hint "builtin" "{}")))
(HintD (DecH "fne_" (hint "builtin" "{}")))
(HintD (DecH "flt_" (hint "builtin" "{}")))
(HintD (DecH "fgt_" (hint "builtin" "{}")))
(HintD (DecH "fle_" (hint "builtin" "{}")))
(HintD (DecH "fge_" (hint "builtin" "{}")))
(TypD "addr" (InstD (AliasT nat)))
(HintD (TypH "addr" (hint "desc" "\"address\"")))
(TypD "funcaddr" (InstD (AliasT (VarT "addr"))))
(HintD (TypH "funcaddr" (hint "desc" "\"function address\"")))
(TypD "globaladdr" (InstD (AliasT (VarT "addr"))))
(HintD (TypH "globaladdr" (hint "desc" "\"global address\"")))
(TypD "tableaddr" (InstD (AliasT (VarT "addr"))))
(HintD (TypH "tableaddr" (hint "desc" "\"table address\"")))
(TypD "memaddr" (InstD (AliasT (VarT "addr"))))
(HintD (TypH "memaddr" (hint "desc" "\"memory address\"")))
(TypD
  "externaddr"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom FUNC) Arg)
        (TupT (typbind "funcaddr" (VarT "funcaddr")))
      )
      (typcase
        (Seq (Atom GLOBAL) Arg)
        (TupT (typbind "globaladdr" (VarT "globaladdr")))
      )
      (typcase
        (Seq (Atom TABLE) Arg)
        (TupT (typbind "tableaddr" (VarT "tableaddr")))
      )
      (typcase (Seq (Atom MEM) Arg) (TupT (typbind "memaddr" (VarT "memaddr"))))
    )
  )
)
(HintD (TypH "externaddr" (hint "desc" "\"external value\"")))
(TypD
  "val"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom CONST) Arg Arg)
        (TupT (typbind "valtype" (VarT "valtype")) (typbind "_" (VarT "val_")))
      )
    )
  )
)
(RelD
  "wf_val"
  (Seq Arg)
  (TupT (typbind "_" (VarT "val")))
  (RuleD
    "val_case_0"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "var_0" (VarT "val_"))
    (Seq Arg)
    (TupE
      (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
    )
    (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
  )
)
(HintD (RelH "wf_val" (hint "wf-relation" "val")))
(HintD (TypH "val" (hint "desc" "\"value\"")))
(TypD
  "result"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom _VALS) Arg)
        (TupT (typbind "val*" (IterT (VarT "val") List)))
      )
      (typcase (Atom TRAP) (TupT))
    )
  )
)
(RelD
  "wf_result"
  (Seq Arg)
  (TupT (typbind "_" (VarT "result")))
  (RuleD
    "result_case_0"
    (ExpP "val*" (IterT (VarT "val") List))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom _VALS) Arg) (TupE (VarE "val*"))))
    (IterPr
      (RulePr "wf_val" (Seq Arg) (TupE (VarE "val")))
      List
      (iterexp "val" (VarE "val*"))
    )
  )
  (RuleD "result_case_1" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
)
(HintD (RelH "wf_result" (hint "wf-relation" "result")))
(HintD (TypH "result" (hint "desc" "\"result\"")))
(TypD
  "exportinst"
  (InstD
    (StructT
      (typfield (Atom NAME) (VarT "name"))
      (typfield (Atom ADDR) (VarT "externaddr"))
    )
  )
)
(RelD
  "wf_exportinst"
  (Seq Arg)
  (TupT (typbind "_" (VarT "exportinst")))
  (RuleD
    "exportinst_case_"
    (ExpP "var_0" (VarT "name"))
    (ExpP "var_1" (VarT "externaddr"))
    (Seq Arg)
    (TupE
      (StrE
        (expfield (Atom NAME) (VarE "var_0"))
        (expfield (Atom ADDR) (VarE "var_1"))
      )
    )
    (RulePr "wf_name" (Seq Arg) (TupE (VarE "var_0")))
  )
)
(HintD (RelH "wf_exportinst" (hint "wf-relation" "exportinst")))
(TypD
  "moduleinst"
  (InstD
    (StructT
      (typfield (Atom TYPES) (IterT (VarT "functype") List))
      (typfield (Atom FUNCS) (IterT (VarT "funcaddr") List))
      (typfield (Atom GLOBALS) (IterT (VarT "globaladdr") List))
      (typfield (Atom TABLES) (IterT (VarT "tableaddr") List))
      (typfield (Atom MEMS) (IterT (VarT "memaddr") List))
      (typfield (Atom EXPORTS) (IterT (VarT "exportinst") List))
    )
  )
)
(RelD
  "wf_moduleinst"
  (Seq Arg)
  (TupT (typbind "_" (VarT "moduleinst")))
  (RuleD
    "moduleinst_case_"
    (ExpP "var_0*" (IterT (VarT "functype") List))
    (ExpP "var_1*" (IterT (VarT "funcaddr") List))
    (ExpP "var_2*" (IterT (VarT "globaladdr") List))
    (ExpP "var_3*" (IterT (VarT "tableaddr") List))
    (ExpP "var_4*" (IterT (VarT "memaddr") List))
    (ExpP "var_5*" (IterT (VarT "exportinst") List))
    (Seq Arg)
    (TupE
      (StrE
        (expfield (Atom TYPES) (VarE "var_0*"))
        (expfield (Atom FUNCS) (VarE "var_1*"))
        (expfield (Atom GLOBALS) (VarE "var_2*"))
        (expfield (Atom TABLES) (VarE "var_3*"))
        (expfield (Atom MEMS) (VarE "var_4*"))
        (expfield (Atom EXPORTS) (VarE "var_5*"))
      )
    )
    (IterPr
      (RulePr "wf_exportinst" (Seq Arg) (TupE (VarE "var_5")))
      List
      (iterexp "var_5" (VarE "var_5*"))
    )
  )
)
(HintD (RelH "wf_moduleinst" (hint "wf-relation" "moduleinst")))
(TypD
  "funcinst"
  (InstD
    (StructT
      (typfield (Atom TYPE) (VarT "functype"))
      (typfield (Atom MODULE) (VarT "moduleinst"))
      (typfield (Atom CODE) (VarT "func"))
    )
  )
)
(RelD
  "wf_funcinst"
  (Seq Arg)
  (TupT (typbind "_" (VarT "funcinst")))
  (RuleD
    "funcinst_case_"
    (ExpP "var_0" (VarT "functype"))
    (ExpP "var_1" (VarT "moduleinst"))
    (ExpP "var_2" (VarT "func"))
    (Seq Arg)
    (TupE
      (StrE
        (expfield (Atom TYPE) (VarE "var_0"))
        (expfield (Atom MODULE) (VarE "var_1"))
        (expfield (Atom CODE) (VarE "var_2"))
      )
    )
    (RulePr "wf_moduleinst" (Seq Arg) (TupE (VarE "var_1")))
    (RulePr "wf_func" (Seq Arg) (TupE (VarE "var_2")))
  )
)
(HintD (RelH "wf_funcinst" (hint "wf-relation" "funcinst")))
(HintD (TypH "funcinst" (hint "desc" "\"function instance\"")))
(TypD
  "globalinst"
  (InstD
    (StructT
      (typfield (Atom TYPE) (VarT "globaltype"))
      (typfield (Atom VALUE) (VarT "val"))
    )
  )
)
(RelD
  "wf_globalinst"
  (Seq Arg)
  (TupT (typbind "_" (VarT "globalinst")))
  (RuleD
    "globalinst_case_"
    (ExpP "var_0" (VarT "globaltype"))
    (ExpP "var_1" (VarT "val"))
    (Seq Arg)
    (TupE
      (StrE
        (expfield (Atom TYPE) (VarE "var_0"))
        (expfield (Atom VALUE) (VarE "var_1"))
      )
    )
    (RulePr "wf_val" (Seq Arg) (TupE (VarE "var_1")))
  )
)
(HintD (RelH "wf_globalinst" (hint "wf-relation" "globalinst")))
(HintD (TypH "globalinst" (hint "desc" "\"global instance\"")))
(TypD
  "tableinst"
  (InstD
    (StructT
      (typfield (Atom TYPE) (VarT "tabletype"))
      (typfield (Atom REFS) (IterT (IterT (VarT "funcaddr") Opt) List))
    )
  )
)
(RelD
  "wf_tableinst"
  (Seq Arg)
  (TupT (typbind "_" (VarT "tableinst")))
  (RuleD
    "tableinst_case_"
    (ExpP "var_0" (VarT "tabletype"))
    (ExpP "var_1?*" (IterT (IterT (VarT "funcaddr") Opt) List))
    (Seq Arg)
    (TupE
      (StrE
        (expfield (Atom TYPE) (VarE "var_0"))
        (expfield (Atom REFS) (VarE "var_1?*"))
      )
    )
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "var_0")))
  )
)
(HintD (RelH "wf_tableinst" (hint "wf-relation" "tableinst")))
(HintD (TypH "tableinst" (hint "desc" "\"table instance\"")))
(TypD
  "meminst"
  (InstD
    (StructT
      (typfield (Atom TYPE) (VarT "memtype"))
      (typfield (Atom BYTES) (IterT (VarT "byte") List))
    )
  )
)
(RelD
  "wf_meminst"
  (Seq Arg)
  (TupT (typbind "_" (VarT "meminst")))
  (RuleD
    "meminst_case_"
    (ExpP "var_0" (VarT "memtype"))
    (ExpP "var_1*" (IterT (VarT "byte") List))
    (Seq Arg)
    (TupE
      (StrE
        (expfield (Atom TYPE) (VarE "var_0"))
        (expfield (Atom BYTES) (VarE "var_1*"))
      )
    )
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "var_0")))
    (IterPr
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "var_1")))
      List
      (iterexp "var_1" (VarE "var_1*"))
    )
  )
)
(HintD (RelH "wf_meminst" (hint "wf-relation" "meminst")))
(HintD (TypH "meminst" (hint "desc" "\"memory instance\"")))
(HintD (TypH "exportinst" (hint "desc" "\"export instance\"")))
(HintD (TypH "moduleinst" (hint "desc" "\"module instance\"")))
(TypD
  "store"
  (InstD
    (StructT
      (typfield (Atom FUNCS) (IterT (VarT "funcinst") List))
      (typfield (Atom GLOBALS) (IterT (VarT "globalinst") List))
      (typfield (Atom TABLES) (IterT (VarT "tableinst") List))
      (typfield (Atom MEMS) (IterT (VarT "meminst") List))
    )
  )
)
(RelD
  "wf_store"
  (Seq Arg)
  (TupT (typbind "_" (VarT "store")))
  (RuleD
    "store_case_"
    (ExpP "var_0*" (IterT (VarT "funcinst") List))
    (ExpP "var_1*" (IterT (VarT "globalinst") List))
    (ExpP "var_2*" (IterT (VarT "tableinst") List))
    (ExpP "var_3*" (IterT (VarT "meminst") List))
    (Seq Arg)
    (TupE
      (StrE
        (expfield (Atom FUNCS) (VarE "var_0*"))
        (expfield (Atom GLOBALS) (VarE "var_1*"))
        (expfield (Atom TABLES) (VarE "var_2*"))
        (expfield (Atom MEMS) (VarE "var_3*"))
      )
    )
    (IterPr
      (RulePr "wf_funcinst" (Seq Arg) (TupE (VarE "var_0")))
      List
      (iterexp "var_0" (VarE "var_0*"))
    )
    (IterPr
      (RulePr "wf_globalinst" (Seq Arg) (TupE (VarE "var_1")))
      List
      (iterexp "var_1" (VarE "var_1*"))
    )
    (IterPr
      (RulePr "wf_tableinst" (Seq Arg) (TupE (VarE "var_2")))
      List
      (iterexp "var_2" (VarE "var_2*"))
    )
    (IterPr
      (RulePr "wf_meminst" (Seq Arg) (TupE (VarE "var_3")))
      List
      (iterexp "var_3" (VarE "var_3*"))
    )
  )
)
(HintD (RelH "wf_store" (hint "wf-relation" "store")))
(HintD (TypH "store" (hint "desc" "\"store\"")))
(TypD
  "frame"
  (InstD
    (StructT
      (typfield (Atom LOCALS) (IterT (VarT "val") List))
      (typfield (Atom MODULE) (VarT "moduleinst"))
    )
  )
)
(RelD
  "wf_frame"
  (Seq Arg)
  (TupT (typbind "_" (VarT "frame")))
  (RuleD
    "frame_case_"
    (ExpP "var_0*" (IterT (VarT "val") List))
    (ExpP "var_1" (VarT "moduleinst"))
    (Seq Arg)
    (TupE
      (StrE
        (expfield (Atom LOCALS) (VarE "var_0*"))
        (expfield (Atom MODULE) (VarE "var_1"))
      )
    )
    (IterPr
      (RulePr "wf_val" (Seq Arg) (TupE (VarE "var_0")))
      List
      (iterexp "var_0" (VarE "var_0*"))
    )
    (RulePr "wf_moduleinst" (Seq Arg) (TupE (VarE "var_1")))
  )
)
(HintD (RelH "wf_frame" (hint "wf-relation" "frame")))
(HintD (TypH "frame" (hint "desc" "\"frame\"")))
(TypD
  "state"
  (InstD
    (VariantT
      (typcase
        (Infix Arg ; Arg)
        (TupT (typbind "store" (VarT "store")) (typbind "frame" (VarT "frame")))
      )
    )
  )
)
(RelD
  "wf_state"
  (Seq Arg)
  (TupT (typbind "_" (VarT "state")))
  (RuleD
    "state_case_0"
    (ExpP "store" (VarT "store"))
    (ExpP "frame" (VarT "frame"))
    (Seq Arg)
    (TupE (CaseE (Infix Arg ; Arg) (TupE (VarE "store") (VarE "frame"))))
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "store")))
    (RulePr "wf_frame" (Seq Arg) (TupE (VarE "frame")))
  )
)
(HintD (RelH "wf_state" (hint "wf-relation" "state")))
(HintD (TypH "state" (hint "desc" "\"state\"")))
(RecD
  (TypD
    "admininstr"
    (InstD
      (VariantT
        (typcase (Atom NOP) (TupT))
        (typcase (Atom UNREACHABLE) (TupT))
        (typcase (Atom DROP) (TupT))
        (typcase (Atom SELECT) (TupT))
        (typcase
          (Seq (Atom BLOCK) Arg Arg)
          (TupT
            (typbind "blocktype" (VarT "blocktype"))
            (typbind "instr*" (IterT (VarT "instr") List))
          )
        )
        (typcase
          (Seq (Atom LOOP) Arg Arg)
          (TupT
            (typbind "blocktype" (VarT "blocktype"))
            (typbind "instr*" (IterT (VarT "instr") List))
          )
        )
        (typcase
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupT
            (typbind "blocktype" (VarT "blocktype"))
            (typbind "instr*" (IterT (VarT "instr") List))
            (typbind "instr*" (IterT (VarT "instr") List))
          )
        )
        (typcase
          (Seq (Atom BR) Arg)
          (TupT (typbind "labelidx" (VarT "labelidx")))
        )
        (typcase
          (Seq (Atom BR_IF) Arg)
          (TupT (typbind "labelidx" (VarT "labelidx")))
        )
        (typcase
          (Seq (Atom BR_TABLE) Arg Arg)
          (TupT
            (typbind "labelidx*" (IterT (VarT "labelidx") List))
            (typbind "labelidx" (VarT "labelidx"))
          )
        )
        (typcase
          (Seq (Atom CALL) Arg)
          (TupT (typbind "funcidx" (VarT "funcidx")))
        )
        (typcase
          (Seq (Atom CALL_INDIRECT) Arg)
          (TupT (typbind "typeidx" (VarT "typeidx")))
        )
        (typcase (Atom RETURN) (TupT))
        (typcase
          (Seq (Atom CONST) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "val_"))
          )
        )
        (typcase
          (Seq (Atom UNOP) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "unop_"))
          )
        )
        (typcase
          (Seq (Atom BINOP) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "binop_"))
          )
        )
        (typcase
          (Seq (Atom TESTOP) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "testop_"))
          )
        )
        (typcase
          (Seq (Atom RELOP) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "relop_"))
          )
        )
        (typcase
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupT
            (typbind "valtype_1" (VarT "valtype"))
            (typbind "valtype_2" (VarT "valtype"))
            (typbind "cvtop" (VarT "cvtop"))
          )
        )
        (typcase
          (Seq (Atom LOCAL.GET) Arg)
          (TupT (typbind "localidx" (VarT "localidx")))
        )
        (typcase
          (Seq (Atom LOCAL.SET) Arg)
          (TupT (typbind "localidx" (VarT "localidx")))
        )
        (typcase
          (Seq (Atom LOCAL.TEE) Arg)
          (TupT (typbind "localidx" (VarT "localidx")))
        )
        (typcase
          (Seq (Atom GLOBAL.GET) Arg)
          (TupT (typbind "globalidx" (VarT "globalidx")))
        )
        (typcase
          (Seq (Atom GLOBAL.SET) Arg)
          (TupT (typbind "globalidx" (VarT "globalidx")))
        )
        (typcase
          (Seq (Atom LOAD) Arg Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (IterT (VarT "loadop_") Opt))
            (typbind "memarg" (VarT "memarg"))
          )
        )
        (typcase
          (Seq (Atom STORE) Arg Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "sz?" (IterT (VarT "sz") Opt))
            (typbind "memarg" (VarT "memarg"))
          )
          (ExpP "Inn?" (IterT (VarT "Inn") Opt))
        )
        (typcase (Atom MEMORY.SIZE) (TupT))
        (typcase (Atom MEMORY.GROW) (TupT))
        (typcase
          (Seq (Atom CALL_ADDR) Arg)
          (TupT (typbind "funcaddr" (VarT "funcaddr")))
        )
        (typcase
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupT
            (typbind "n" (VarT "n"))
            (typbind "instr*" (IterT (VarT "instr") List))
            (typbind "admininstr*" (IterT (VarT "admininstr") List))
          )
        )
        (typcase
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupT
            (typbind "n" (VarT "n"))
            (typbind "frame" (VarT "frame"))
            (typbind "admininstr*" (IterT (VarT "admininstr") List))
          )
        )
        (typcase (Atom TRAP) (TupT))
      )
    )
  )
)
(DecD
  "admininstr_instr"
  (ExpP "_" (VarT "instr"))
  (VarT "admininstr")
  (DefD (ExpA (CaseE (Atom NOP) (TupE))) (CaseE (Atom NOP) (TupE)))
  (DefD
    (ExpA (CaseE (Atom UNREACHABLE) (TupE)))
    (CaseE (Atom UNREACHABLE) (TupE))
  )
  (DefD (ExpA (CaseE (Atom DROP) (TupE))) (CaseE (Atom DROP) (TupE)))
  (DefD (ExpA (CaseE (Atom SELECT) (TupE))) (CaseE (Atom SELECT) (TupE)))
  (DefD
    (ExpP "x0" (VarT "blocktype"))
    (ExpP "x1" (IterT (VarT "instr") List))
    (ExpA (CaseE (Seq (Atom BLOCK) Arg Arg) (TupE (VarE "x0") (VarE "x1"))))
    (CaseE (Seq (Atom BLOCK) Arg Arg) (TupE (VarE "x0") (VarE "x1")))
  )
  (DefD
    (ExpP "x0" (VarT "blocktype"))
    (ExpP "x1" (IterT (VarT "instr") List))
    (ExpA (CaseE (Seq (Atom LOOP) Arg Arg) (TupE (VarE "x0") (VarE "x1"))))
    (CaseE (Seq (Atom LOOP) Arg Arg) (TupE (VarE "x0") (VarE "x1")))
  )
  (DefD
    (ExpP "x0" (VarT "blocktype"))
    (ExpP "x1" (IterT (VarT "instr") List))
    (ExpP "x2" (IterT (VarT "instr") List))
    (ExpA
      (CaseE
        (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
        (TupE (VarE "x0") (VarE "x1") (VarE "x2"))
      )
    )
    (CaseE
      (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
      (TupE (VarE "x0") (VarE "x1") (VarE "x2"))
    )
  )
  (DefD
    (ExpP "x0" (VarT "labelidx"))
    (ExpA (CaseE (Seq (Atom BR) Arg) (TupE (VarE "x0"))))
    (CaseE (Seq (Atom BR) Arg) (TupE (VarE "x0")))
  )
  (DefD
    (ExpP "x0" (VarT "labelidx"))
    (ExpA (CaseE (Seq (Atom BR_IF) Arg) (TupE (VarE "x0"))))
    (CaseE (Seq (Atom BR_IF) Arg) (TupE (VarE "x0")))
  )
  (DefD
    (ExpP "x0" (IterT (VarT "labelidx") List))
    (ExpP "x1" (VarT "labelidx"))
    (ExpA (CaseE (Seq (Atom BR_TABLE) Arg Arg) (TupE (VarE "x0") (VarE "x1"))))
    (CaseE (Seq (Atom BR_TABLE) Arg Arg) (TupE (VarE "x0") (VarE "x1")))
  )
  (DefD
    (ExpP "x0" (VarT "funcidx"))
    (ExpA (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "x0"))))
    (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "x0")))
  )
  (DefD
    (ExpP "x0" (VarT "typeidx"))
    (ExpA (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "x0"))))
    (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "x0")))
  )
  (DefD (ExpA (CaseE (Atom RETURN) (TupE))) (CaseE (Atom RETURN) (TupE)))
  (DefD
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "val_"))
    (ExpA (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "x0") (VarE "x1"))))
    (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "x0") (VarE "x1")))
  )
  (DefD
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "unop_"))
    (ExpA (CaseE (Seq (Atom UNOP) Arg Arg) (TupE (VarE "x0") (VarE "x1"))))
    (CaseE (Seq (Atom UNOP) Arg Arg) (TupE (VarE "x0") (VarE "x1")))
  )
  (DefD
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "binop_"))
    (ExpA (CaseE (Seq (Atom BINOP) Arg Arg) (TupE (VarE "x0") (VarE "x1"))))
    (CaseE (Seq (Atom BINOP) Arg Arg) (TupE (VarE "x0") (VarE "x1")))
  )
  (DefD
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "testop_"))
    (ExpA (CaseE (Seq (Atom TESTOP) Arg Arg) (TupE (VarE "x0") (VarE "x1"))))
    (CaseE (Seq (Atom TESTOP) Arg Arg) (TupE (VarE "x0") (VarE "x1")))
  )
  (DefD
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "relop_"))
    (ExpA (CaseE (Seq (Atom RELOP) Arg Arg) (TupE (VarE "x0") (VarE "x1"))))
    (CaseE (Seq (Atom RELOP) Arg Arg) (TupE (VarE "x0") (VarE "x1")))
  )
  (DefD
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "valtype"))
    (ExpP "x2" (VarT "cvtop"))
    (ExpA
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE (VarE "x0") (VarE "x1") (VarE "x2"))
      )
    )
    (CaseE
      (Seq (Atom CVTOP) Arg Arg Arg)
      (TupE (VarE "x0") (VarE "x1") (VarE "x2"))
    )
  )
  (DefD
    (ExpP "x0" (VarT "localidx"))
    (ExpA (CaseE (Seq (Atom LOCAL.GET) Arg) (TupE (VarE "x0"))))
    (CaseE (Seq (Atom LOCAL.GET) Arg) (TupE (VarE "x0")))
  )
  (DefD
    (ExpP "x0" (VarT "localidx"))
    (ExpA (CaseE (Seq (Atom LOCAL.SET) Arg) (TupE (VarE "x0"))))
    (CaseE (Seq (Atom LOCAL.SET) Arg) (TupE (VarE "x0")))
  )
  (DefD
    (ExpP "x0" (VarT "localidx"))
    (ExpA (CaseE (Seq (Atom LOCAL.TEE) Arg) (TupE (VarE "x0"))))
    (CaseE (Seq (Atom LOCAL.TEE) Arg) (TupE (VarE "x0")))
  )
  (DefD
    (ExpP "x0" (VarT "globalidx"))
    (ExpA (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "x0"))))
    (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "x0")))
  )
  (DefD
    (ExpP "x0" (VarT "globalidx"))
    (ExpA (CaseE (Seq (Atom GLOBAL.SET) Arg) (TupE (VarE "x0"))))
    (CaseE (Seq (Atom GLOBAL.SET) Arg) (TupE (VarE "x0")))
  )
  (DefD
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (IterT (VarT "loadop_") Opt))
    (ExpP "x2" (VarT "memarg"))
    (ExpA
      (CaseE
        (Seq (Atom LOAD) Arg Arg Arg)
        (TupE (VarE "x0") (VarE "x1") (VarE "x2"))
      )
    )
    (CaseE
      (Seq (Atom LOAD) Arg Arg Arg)
      (TupE (VarE "x0") (VarE "x1") (VarE "x2"))
    )
  )
  (DefD
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (IterT (VarT "sz") Opt))
    (ExpP "x2" (VarT "memarg"))
    (ExpA
      (CaseE
        (Seq (Atom STORE) Arg Arg Arg)
        (TupE (VarE "x0") (VarE "x1") (VarE "x2"))
      )
    )
    (CaseE
      (Seq (Atom STORE) Arg Arg Arg)
      (TupE (VarE "x0") (VarE "x1") (VarE "x2"))
    )
  )
  (DefD
    (ExpA (CaseE (Atom MEMORY.SIZE) (TupE)))
    (CaseE (Atom MEMORY.SIZE) (TupE))
  )
  (DefD
    (ExpA (CaseE (Atom MEMORY.GROW) (TupE)))
    (CaseE (Atom MEMORY.GROW) (TupE))
  )
)
(DecD
  "admininstr_val"
  (ExpP "_" (VarT "val"))
  (VarT "admininstr")
  (DefD
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "val_"))
    (ExpA (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "x0") (VarE "x1"))))
    (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "x0") (VarE "x1")))
  )
)
(RecD
  (RelD
    "wf_admininstr"
    (Seq Arg)
    (TupT (typbind "_" (VarT "admininstr")))
    (RuleD "admininstr_case_0" (Seq Arg) (TupE (CaseE (Atom NOP) (TupE))))
    (RuleD
      "admininstr_case_1"
      (Seq Arg)
      (TupE (CaseE (Atom UNREACHABLE) (TupE)))
    )
    (RuleD "admininstr_case_2" (Seq Arg) (TupE (CaseE (Atom DROP) (TupE))))
    (RuleD "admininstr_case_3" (Seq Arg) (TupE (CaseE (Atom SELECT) (TupE))))
    (RuleD
      "admininstr_case_4"
      (ExpP "blocktype" (VarT "blocktype"))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BLOCK) Arg Arg)
          (TupE (VarE "blocktype") (VarE "instr*"))
        )
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr")))
        List
        (iterexp "instr" (VarE "instr*"))
      )
    )
    (RuleD
      "admininstr_case_5"
      (ExpP "blocktype" (VarT "blocktype"))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LOOP) Arg Arg)
          (TupE (VarE "blocktype") (VarE "instr*"))
        )
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr")))
        List
        (iterexp "instr" (VarE "instr*"))
      )
    )
    (RuleD
      "admininstr_case_6"
      (ExpP "blocktype" (VarT "blocktype"))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (ExpP "instr*_0*" (IterT (VarT "instr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupE (VarE "blocktype") (VarE "instr*") (VarE "instr*_0*"))
        )
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr")))
        List
        (iterexp "instr" (VarE "instr*"))
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr*_0")))
        List
        (iterexp "instr*_0" (VarE "instr*_0*"))
      )
    )
    (RuleD
      "admininstr_case_7"
      (ExpP "labelidx" (VarT "labelidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BR) Arg) (TupE (VarE "labelidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "labelidx")))
    )
    (RuleD
      "admininstr_case_8"
      (ExpP "labelidx" (VarT "labelidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BR_IF) Arg) (TupE (VarE "labelidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "labelidx")))
    )
    (RuleD
      "admininstr_case_9"
      (ExpP "labelidx*" (IterT (VarT "labelidx") List))
      (ExpP "labelidx" (VarT "labelidx"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BR_TABLE) Arg Arg)
          (TupE (VarE "labelidx*") (VarE "labelidx"))
        )
      )
      (IterPr
        (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "labelidx")))
        List
        (iterexp "labelidx" (VarE "labelidx*"))
      )
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "labelidx")))
    )
    (RuleD
      "admininstr_case_10"
      (ExpP "funcidx" (VarT "funcidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "funcidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "funcidx")))
    )
    (RuleD
      "admininstr_case_11"
      (ExpP "typeidx" (VarT "typeidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "typeidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "typeidx")))
    )
    (RuleD "admininstr_case_12" (Seq Arg) (TupE (CaseE (Atom RETURN) (TupE))))
    (RuleD
      "admininstr_case_13"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "val_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0"))
        )
      )
      (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
    )
    (RuleD
      "admininstr_case_14"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "unop_"))
      (Seq Arg)
      (TupE
        (CaseE (Seq (Atom UNOP) Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
      )
      (RulePr "wf_unop_" (Seq Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
    )
    (RuleD
      "admininstr_case_15"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "binop_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BINOP) Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0"))
        )
      )
      (RulePr "wf_binop_" (Seq Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
    )
    (RuleD
      "admininstr_case_16"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "testop_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom TESTOP) Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0"))
        )
      )
      (RulePr "wf_testop_" (Seq Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
    )
    (RuleD
      "admininstr_case_17"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "relop_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom RELOP) Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0"))
        )
      )
      (RulePr "wf_relop_" (Seq Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
    )
    (RuleD
      "admininstr_case_18"
      (ExpP "valtype_1" (VarT "valtype"))
      (ExpP "valtype_2" (VarT "valtype"))
      (ExpP "cvtop" (VarT "cvtop"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupE (VarE "valtype_1") (VarE "valtype_2") (VarE "cvtop"))
        )
      )
      (IfPr (CmpE NeOp bool (VarE "valtype_1") (VarE "valtype_2")))
    )
    (RuleD
      "admininstr_case_19"
      (ExpP "localidx" (VarT "localidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL.GET) Arg) (TupE (VarE "localidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "localidx")))
    )
    (RuleD
      "admininstr_case_20"
      (ExpP "localidx" (VarT "localidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL.SET) Arg) (TupE (VarE "localidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "localidx")))
    )
    (RuleD
      "admininstr_case_21"
      (ExpP "localidx" (VarT "localidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL.TEE) Arg) (TupE (VarE "localidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "localidx")))
    )
    (RuleD
      "admininstr_case_22"
      (ExpP "globalidx" (VarT "globalidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "globalidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "globalidx")))
    )
    (RuleD
      "admininstr_case_23"
      (ExpP "globalidx" (VarT "globalidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL.SET) Arg) (TupE (VarE "globalidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "globalidx")))
    )
    (RuleD
      "admininstr_case_24"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0?" (IterT (VarT "loadop_") Opt))
      (ExpP "memarg" (VarT "memarg"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LOAD) Arg Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0?") (VarE "memarg"))
        )
      )
      (IterPr
        (RulePr
          "wf_loadop_"
          (Seq Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0"))
        )
        Opt
        (iterexp "var_0" (VarE "var_0?"))
      )
      (RulePr "wf_memarg" (Seq Arg) (TupE (VarE "memarg")))
    )
    (RuleD
      "admininstr_case_25"
      (ExpP "Inn?" (IterT (VarT "Inn") Opt))
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "sz?" (IterT (VarT "sz") Opt))
      (ExpP "memarg" (VarT "memarg"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom STORE) Arg Arg Arg)
          (TupE (VarE "valtype") (VarE "sz?") (VarE "memarg"))
        )
      )
      (IterPr
        (RulePr "wf_sz" (Seq Arg) (TupE (VarE "sz")))
        Opt
        (iterexp "sz" (VarE "sz?"))
      )
      (RulePr "wf_memarg" (Seq Arg) (TupE (VarE "memarg")))
      (IterPr
        (IfPr
          (BinE
            AndOp
            bool
            (CmpE
              EqOp
              bool
              (VarE "valtype")
              (CallE "valtype_Inn" (ExpA (VarE "Inn")))
            )
            (CmpE
              LtOp
              nat
              (ProjE (CallE "proj_sz_0" (ExpA (VarE "sz"))) 0)
              (CallE "size" (ExpA (CallE "valtype_Inn" (ExpA (VarE "Inn")))))
            )
          )
        )
        Opt
        (iterexp "Inn" (VarE "Inn?"))
        (iterexp "sz" (VarE "sz?"))
      )
    )
    (RuleD
      "admininstr_case_26"
      (Seq Arg)
      (TupE (CaseE (Atom MEMORY.SIZE) (TupE)))
    )
    (RuleD
      "admininstr_case_27"
      (Seq Arg)
      (TupE (CaseE (Atom MEMORY.GROW) (TupE)))
    )
    (RuleD
      "admininstr_case_28"
      (ExpP "funcaddr" (VarT "funcaddr"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CALL_ADDR) Arg) (TupE (VarE "funcaddr"))))
    )
    (RuleD
      "admininstr_case_29"
      (ExpP "n" (VarT "n"))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (ExpP "admininstr*" (IterT (VarT "admininstr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE (VarE "n") (VarE "instr*") (VarE "admininstr*"))
        )
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr")))
        List
        (iterexp "instr" (VarE "instr*"))
      )
      (IterPr
        (RulePr "wf_admininstr" (Seq Arg) (TupE (VarE "admininstr")))
        List
        (iterexp "admininstr" (VarE "admininstr*"))
      )
    )
    (RuleD
      "admininstr_case_30"
      (ExpP "n" (VarT "n"))
      (ExpP "frame" (VarT "frame"))
      (ExpP "admininstr*" (IterT (VarT "admininstr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE (VarE "n") (VarE "frame") (VarE "admininstr*"))
        )
      )
      (RulePr "wf_frame" (Seq Arg) (TupE (VarE "frame")))
      (IterPr
        (RulePr "wf_admininstr" (Seq Arg) (TupE (VarE "admininstr")))
        List
        (iterexp "admininstr" (VarE "admininstr*"))
      )
    )
    (RuleD "admininstr_case_31" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
  )
  (HintD (RelH "wf_admininstr" (hint "wf-relation" "admininstr")))
)
(TypD
  "config"
  (InstD
    (VariantT
      (typcase
        (Infix Arg ; Arg)
        (TupT
          (typbind "state" (VarT "state"))
          (typbind "admininstr*" (IterT (VarT "admininstr") List))
        )
      )
    )
  )
)
(RelD
  "wf_config"
  (Seq Arg)
  (TupT (typbind "_" (VarT "config")))
  (RuleD
    "config_case_0"
    (ExpP "state" (VarT "state"))
    (ExpP "admininstr*" (IterT (VarT "admininstr") List))
    (Seq Arg)
    (TupE (CaseE (Infix Arg ; Arg) (TupE (VarE "state") (VarE "admininstr*"))))
    (RulePr "wf_state" (Seq Arg) (TupE (VarE "state")))
    (IterPr
      (RulePr "wf_admininstr" (Seq Arg) (TupE (VarE "admininstr")))
      List
      (iterexp "admininstr" (VarE "admininstr*"))
    )
  )
)
(HintD (RelH "wf_config" (hint "wf-relation" "config")))
(HintD (TypH "config" (hint "desc" "\"configuration\"")))
(HintD
  (TypH
    "admininstr"
    (hint "show" "instr")
    (hint "desc" "\"administrative instruction\"")
  )
)
(DecD
  "default_"
  (ExpP "valtype" (VarT "valtype"))
  (VarT "val")
  (DefD
    (ExpA (CaseE (Atom I32) (TupE)))
    (CaseE
      (Seq (Atom CONST) Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (CaseE Arg (TupE (NumE (Nat 0)))))
        )
      )
    )
    (RulePr
      "wf_val"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (CaseE Arg (TupE (NumE (Nat 0)))))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpA (CaseE (Atom I64) (TupE)))
    (CaseE
      (Seq (Atom CONST) Arg Arg)
      (TupE
        (CaseE (Atom I64) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I64) (TupE)) (CaseE Arg (TupE (NumE (Nat 0)))))
        )
      )
    )
    (RulePr
      "wf_val"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I64) (TupE)) (CaseE Arg (TupE (NumE (Nat 0)))))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpA (CaseE (Atom F32) (TupE)))
    (CaseE
      (Seq (Atom CONST) Arg Arg)
      (TupE
        (CaseE (Atom F32) (TupE))
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE
            (CaseE (Atom F32) (TupE))
            (CallE "fzero" (ExpA (NumE (Nat 32))))
          )
        )
      )
    )
    (RulePr
      "wf_val"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE
            (CaseE (Atom F32) (TupE))
            (CaseE
              (Seq (Atom mk_val__1) Arg Arg)
              (TupE
                (CaseE (Atom F32) (TupE))
                (CallE "fzero" (ExpA (NumE (Nat 32))))
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpA (CaseE (Atom F64) (TupE)))
    (CaseE
      (Seq (Atom CONST) Arg Arg)
      (TupE
        (CaseE (Atom F64) (TupE))
        (CaseE
          (Seq (Atom mk_val__1) Arg Arg)
          (TupE
            (CaseE (Atom F64) (TupE))
            (CallE "fzero" (ExpA (NumE (Nat 64))))
          )
        )
      )
    )
    (RulePr
      "wf_val"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE
            (CaseE (Atom F64) (TupE))
            (CaseE
              (Seq (Atom mk_val__1) Arg Arg)
              (TupE
                (CaseE (Atom F64) (TupE))
                (CallE "fzero" (ExpA (NumE (Nat 64))))
              )
            )
          )
        )
      )
    )
  )
)
(RecD
  (DecD
    "funcsxa"
    (ExpP "_" (IterT (VarT "externaddr") List))
    (IterT (VarT "funcaddr") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "fa" nat)
      (ExpP "xv*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "fa"))))
          (IterE (VarE "xv#1") List (iterexp "xv#1" (VarE "xv*")))
        )
      )
      (CatE
        (ListE (VarE "fa"))
        (CallE
          "funcsxa"
          (ExpA (IterE (VarE "xv") List (iterexp "xv" (VarE "xv*"))))
        )
      )
    )
    (DefD
      (ExpP "externaddr" (VarT "externaddr"))
      (ExpP "xv*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (VarE "externaddr"))
          (IterE (VarE "xv#2") List (iterexp "xv#2" (VarE "xv*")))
        )
      )
      (CallE
        "funcsxa"
        (ExpA (IterE (VarE "xv") List (iterexp "xv" (VarE "xv*"))))
      )
    )
  )
)
(HintD (DecH "funcsxa" (hint "show" "$funcs(%)")))
(RecD
  (DecD
    "globalsxa"
    (ExpP "_" (IterT (VarT "externaddr") List))
    (IterT (VarT "globaladdr") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "ga" nat)
      (ExpP "xv*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "ga"))))
          (IterE (VarE "xv#3") List (iterexp "xv#3" (VarE "xv*")))
        )
      )
      (CatE
        (ListE (VarE "ga"))
        (CallE
          "globalsxa"
          (ExpA (IterE (VarE "xv") List (iterexp "xv" (VarE "xv*"))))
        )
      )
    )
    (DefD
      (ExpP "externaddr" (VarT "externaddr"))
      (ExpP "xv*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (VarE "externaddr"))
          (IterE (VarE "xv#4") List (iterexp "xv#4" (VarE "xv*")))
        )
      )
      (CallE
        "globalsxa"
        (ExpA (IterE (VarE "xv") List (iterexp "xv" (VarE "xv*"))))
      )
    )
  )
)
(HintD (DecH "globalsxa" (hint "show" "$globals(%)")))
(RecD
  (DecD
    "tablesxa"
    (ExpP "_" (IterT (VarT "externaddr") List))
    (IterT (VarT "tableaddr") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "ta" nat)
      (ExpP "xv*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "ta"))))
          (IterE (VarE "xv#5") List (iterexp "xv#5" (VarE "xv*")))
        )
      )
      (CatE
        (ListE (VarE "ta"))
        (CallE
          "tablesxa"
          (ExpA (IterE (VarE "xv") List (iterexp "xv" (VarE "xv*"))))
        )
      )
    )
    (DefD
      (ExpP "externaddr" (VarT "externaddr"))
      (ExpP "xv*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (VarE "externaddr"))
          (IterE (VarE "xv#6") List (iterexp "xv#6" (VarE "xv*")))
        )
      )
      (CallE
        "tablesxa"
        (ExpA (IterE (VarE "xv") List (iterexp "xv" (VarE "xv*"))))
      )
    )
  )
)
(HintD (DecH "tablesxa" (hint "show" "$tables(%)")))
(RecD
  (DecD
    "memsxa"
    (ExpP "_" (IterT (VarT "externaddr") List))
    (IterT (VarT "memaddr") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "ma" nat)
      (ExpP "xv*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "ma"))))
          (IterE (VarE "xv#7") List (iterexp "xv#7" (VarE "xv*")))
        )
      )
      (CatE
        (ListE (VarE "ma"))
        (CallE
          "memsxa"
          (ExpA (IterE (VarE "xv") List (iterexp "xv" (VarE "xv*"))))
        )
      )
    )
    (DefD
      (ExpP "externaddr" (VarT "externaddr"))
      (ExpP "xv*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (VarE "externaddr"))
          (IterE (VarE "xv#8") List (iterexp "xv#8" (VarE "xv*")))
        )
      )
      (CallE
        "memsxa"
        (ExpA (IterE (VarE "xv") List (iterexp "xv" (VarE "xv*"))))
      )
    )
  )
)
(HintD (DecH "memsxa" (hint "show" "$mems(%)")))
(DecD
  "store"
  (ExpP "state" (VarT "state"))
  (VarT "store")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (VarE "s")
  )
)
(HintD (DecH "store" (hint "show" "%.STORE")))
(DecD
  "frame"
  (ExpP "state" (VarT "state"))
  (VarT "frame")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (VarE "f")
  )
)
(HintD (DecH "frame" (hint "show" "%.FRAME")))
(DecD
  "funcaddr"
  (ExpP "state" (VarT "state"))
  (IterT (VarT "funcaddr") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (DotE (VarE "f") (Atom MODULE)) (Atom FUNCS))
  )
)
(HintD (DecH "funcaddr" (hint "show" "%.MODULE.FUNCS")))
(DecD
  "funcinst"
  (ExpP "state" (VarT "state"))
  (IterT (VarT "funcinst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom FUNCS))
  )
)
(HintD (DecH "funcinst" (hint "show" "%.FUNCS")))
(DecD
  "globalinst"
  (ExpP "state" (VarT "state"))
  (IterT (VarT "globalinst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom GLOBALS))
  )
)
(HintD (DecH "globalinst" (hint "show" "%.GLOBALS")))
(DecD
  "tableinst"
  (ExpP "state" (VarT "state"))
  (IterT (VarT "tableinst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom TABLES))
  )
)
(HintD (DecH "tableinst" (hint "show" "%.TABLES")))
(DecD
  "meminst"
  (ExpP "state" (VarT "state"))
  (IterT (VarT "meminst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom MEMS))
  )
)
(HintD (DecH "meminst" (hint "show" "%.MEMS")))
(DecD
  "moduleinst"
  (ExpP "state" (VarT "state"))
  (VarT "moduleinst")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "f") (Atom MODULE))
  )
)
(HintD (DecH "moduleinst" (hint "show" "%.MODULE")))
(DecD
  "type"
  (ExpP "state" (VarT "state"))
  (ExpP "typeidx" (VarT "typeidx"))
  (VarT "functype")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (DotE (VarE "f") (Atom MODULE)) (Atom TYPES))
      (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
    )
  )
)
(HintD (DecH "type" (hint "show" "%.TYPES[%]")))
(DecD
  "func"
  (ExpP "state" (VarT "state"))
  (ExpP "funcidx" (VarT "funcidx"))
  (VarT "funcinst")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (VarE "s") (Atom FUNCS))
      (IdxE
        (DotE (DotE (VarE "f") (Atom MODULE)) (Atom FUNCS))
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
      )
    )
  )
)
(HintD (DecH "func" (hint "show" "%.FUNCS[%]")))
(DecD
  "global"
  (ExpP "state" (VarT "state"))
  (ExpP "globalidx" (VarT "globalidx"))
  (VarT "globalinst")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (VarE "s") (Atom GLOBALS))
      (IdxE
        (DotE (DotE (VarE "f") (Atom MODULE)) (Atom GLOBALS))
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
      )
    )
  )
)
(HintD (DecH "global" (hint "show" "%.GLOBALS[%]")))
(DecD
  "table"
  (ExpP "state" (VarT "state"))
  (ExpP "tableidx" (VarT "tableidx"))
  (VarT "tableinst")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (VarE "s") (Atom TABLES))
      (IdxE
        (DotE (DotE (VarE "f") (Atom MODULE)) (Atom TABLES))
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
      )
    )
  )
)
(HintD (DecH "table" (hint "show" "%.TABLES[%]")))
(DecD
  "mem"
  (ExpP "state" (VarT "state"))
  (ExpP "memidx" (VarT "memidx"))
  (VarT "meminst")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (VarE "s") (Atom MEMS))
      (IdxE
        (DotE (DotE (VarE "f") (Atom MODULE)) (Atom MEMS))
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
      )
    )
  )
)
(HintD (DecH "mem" (hint "show" "%.MEMS[%]")))
(DecD
  "local"
  (ExpP "state" (VarT "state"))
  (ExpP "localidx" (VarT "localidx"))
  (VarT "val")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (VarE "f") (Atom LOCALS))
      (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
    )
  )
)
(HintD (DecH "local" (hint "show" "%.LOCALS[%]")))
(DecD
  "with_local"
  (ExpP "state" (VarT "state"))
  (ExpP "localidx" (VarT "localidx"))
  (ExpP "val" (VarT "val"))
  (VarT "state")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpP "v" (VarT "val"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (ExpA (VarE "v"))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (VarE "s")
        (UpdE
          (VarE "f")
          (IdxP
            (DotP RootP (Atom LOCALS))
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
          )
          (VarE "v")
        )
      )
    )
    (RulePr
      "wf_state"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "s")
            (UpdE
              (VarE "f")
              (IdxP
                (DotP RootP (Atom LOCALS))
                (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
              )
              (VarE "v")
            )
          )
        )
      )
    )
  )
)
(HintD (DecH "with_local" (hint "show" "%[LOCALS[%] = %]")))
(DecD
  "with_global"
  (ExpP "state" (VarT "state"))
  (ExpP "globalidx" (VarT "globalidx"))
  (ExpP "val" (VarT "val"))
  (VarT "state")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpP "v" (VarT "val"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (ExpA (VarE "v"))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (UpdE
          (VarE "s")
          (DotP
            (IdxP
              (DotP RootP (Atom GLOBALS))
              (IdxE
                (DotE (DotE (VarE "f") (Atom MODULE)) (Atom GLOBALS))
                (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
              )
            )
            (Atom VALUE)
          )
          (VarE "v")
        )
        (VarE "f")
      )
    )
    (RulePr
      "wf_state"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (UpdE
              (VarE "s")
              (DotP
                (IdxP
                  (DotP RootP (Atom GLOBALS))
                  (IdxE
                    (DotE (DotE (VarE "f") (Atom MODULE)) (Atom GLOBALS))
                    (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
                  )
                )
                (Atom VALUE)
              )
              (VarE "v")
            )
            (VarE "f")
          )
        )
      )
    )
  )
)
(HintD (DecH "with_global" (hint "show" "%[GLOBALS[%].VALUE = %]")))
(DecD
  "with_table"
  (ExpP "state" (VarT "state"))
  (ExpP "tableidx" (VarT "tableidx"))
  (ExpP "nat" nat)
  (ExpP "funcaddr" (VarT "funcaddr"))
  (VarT "state")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpP "i" nat)
    (ExpP "a" nat)
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (ExpA (VarE "i"))
    (ExpA (VarE "a"))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (UpdE
          (VarE "s")
          (IdxP
            (DotP
              (IdxP
                (DotP RootP (Atom TABLES))
                (IdxE
                  (DotE (DotE (VarE "f") (Atom MODULE)) (Atom TABLES))
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
                )
              )
              (Atom REFS)
            )
            (VarE "i")
          )
          (OptE (VarE "a"))
        )
        (VarE "f")
      )
    )
    (RulePr
      "wf_state"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (UpdE
              (VarE "s")
              (IdxP
                (DotP
                  (IdxP
                    (DotP RootP (Atom TABLES))
                    (IdxE
                      (DotE (DotE (VarE "f") (Atom MODULE)) (Atom TABLES))
                      (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
                    )
                  )
                  (Atom REFS)
                )
                (VarE "i")
              )
              (OptE (VarE "a"))
            )
            (VarE "f")
          )
        )
      )
    )
  )
)
(HintD (DecH "with_table" (hint "show" "%[TABLES[%].REFS[%] = %]")))
(DecD
  "with_tableinst"
  (ExpP "state" (VarT "state"))
  (ExpP "tableidx" (VarT "tableidx"))
  (ExpP "tableinst" (VarT "tableinst"))
  (VarT "state")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpP "ti" (VarT "tableinst"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (ExpA (VarE "ti"))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (UpdE
          (VarE "s")
          (IdxP
            (DotP RootP (Atom TABLES))
            (IdxE
              (DotE (DotE (VarE "f") (Atom MODULE)) (Atom TABLES))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
            )
          )
          (VarE "ti")
        )
        (VarE "f")
      )
    )
    (RulePr
      "wf_state"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (UpdE
              (VarE "s")
              (IdxP
                (DotP RootP (Atom TABLES))
                (IdxE
                  (DotE (DotE (VarE "f") (Atom MODULE)) (Atom TABLES))
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
                )
              )
              (VarE "ti")
            )
            (VarE "f")
          )
        )
      )
    )
  )
)
(HintD (DecH "with_tableinst" (hint "show" "%[TABLES[%] = %]")))
(DecD
  "with_mem"
  (ExpP "state" (VarT "state"))
  (ExpP "memidx" (VarT "memidx"))
  (ExpP "nat" nat)
  (ExpP "nat" nat)
  (ExpP "_" (IterT (VarT "byte") List))
  (VarT "state")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpP "i" nat)
    (ExpP "j" nat)
    (ExpP "b*" (IterT (VarT "byte") List))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (ExpA (VarE "i"))
    (ExpA (VarE "j"))
    (ExpA (IterE (VarE "b#1") List (iterexp "b#1" (VarE "b*"))))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (UpdE
          (VarE "s")
          (SliceP
            (DotP
              (IdxP
                (DotP RootP (Atom MEMS))
                (IdxE
                  (DotE (DotE (VarE "f") (Atom MODULE)) (Atom MEMS))
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
                )
              )
              (Atom BYTES)
            )
            (VarE "i")
            (VarE "j")
          )
          (IterE (VarE "b") List (iterexp "b" (VarE "b*")))
        )
        (VarE "f")
      )
    )
    (RulePr
      "wf_state"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (UpdE
              (VarE "s")
              (SliceP
                (DotP
                  (IdxP
                    (DotP RootP (Atom MEMS))
                    (IdxE
                      (DotE (DotE (VarE "f") (Atom MODULE)) (Atom MEMS))
                      (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
                    )
                  )
                  (Atom BYTES)
                )
                (VarE "i")
                (VarE "j")
              )
              (IterE (VarE "b#2") List (iterexp "b#2" (VarE "b*")))
            )
            (VarE "f")
          )
        )
      )
    )
  )
)
(HintD (DecH "with_mem" (hint "show" "%[MEMS[%].BYTES[% : %] = %]")))
(DecD
  "with_meminst"
  (ExpP "state" (VarT "state"))
  (ExpP "memidx" (VarT "memidx"))
  (ExpP "meminst" (VarT "meminst"))
  (VarT "state")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpP "mi" (VarT "meminst"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (ExpA (VarE "mi"))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (UpdE
          (VarE "s")
          (IdxP
            (DotP RootP (Atom MEMS))
            (IdxE
              (DotE (DotE (VarE "f") (Atom MODULE)) (Atom MEMS))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
            )
          )
          (VarE "mi")
        )
        (VarE "f")
      )
    )
    (RulePr
      "wf_state"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (UpdE
              (VarE "s")
              (IdxP
                (DotP RootP (Atom MEMS))
                (IdxE
                  (DotE (DotE (VarE "f") (Atom MODULE)) (Atom MEMS))
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
                )
              )
              (VarE "mi")
            )
            (VarE "f")
          )
        )
      )
    )
  )
)
(HintD (DecH "with_meminst" (hint "show" "%[MEMS[%] = %]")))
(DecD
  "growtable"
  (ExpP "tableinst" (VarT "tableinst"))
  (ExpP "nat" nat)
  (IterT (VarT "tableinst") Opt)
  (DefD
    (ExpP "ti" (VarT "tableinst"))
    (ExpP "n" nat)
    (ExpP "ti'" (VarT "tableinst"))
    (ExpP "i" (VarT "uN"))
    (ExpP "j?" (IterT (VarT "u32") Opt))
    (ExpP "a*" (IterT (VarT "addr") List))
    (ExpA (VarE "ti"))
    (ExpA (VarE "n"))
    (OptE (VarE "ti'"))
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "ti")
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Brack [ (Infix Arg .. Arg) ])
              (TupE
                (VarE "i")
                (IterE (VarE "j#1") Opt (iterexp "j#1" (VarE "j?")))
              )
            )
          )
          (expfield
            (Atom REFS)
            (IterE (OptE (VarE "a#1")) List (iterexp "a#1" (VarE "a*")))
          )
        )
      )
    )
    (LetPr
      (VarE "i'")
      (BinE
        AddOp
        nat
        (LenE (IterE (VarE "a#2") List (iterexp "a#2" (VarE "a*"))))
        (VarE "n")
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "ti'")
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Brack [ (Infix Arg .. Arg) ])
              (TupE
                (CaseE Arg (TupE (VarE "i'")))
                (IterE (VarE "j#2") Opt (iterexp "j#2" (VarE "j?")))
              )
            )
          )
          (expfield
            (Atom REFS)
            (CatE
              (IterE (OptE (VarE "a#3")) List (iterexp "a#3" (VarE "a*")))
              (IterE (OptE) (ListN (VarE "n")))
            )
          )
        )
      )
    )
    (IterPr
      (IfPr
        (CmpE
          LeOp
          nat
          (VarE "i'")
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "j#3"))) 0)
        )
      )
      Opt
      (iterexp "j#3" (VarE "j?"))
    )
    (RulePr "wf_tableinst" (Seq Arg) (TupE (VarE "ti'")))
    (RulePr
      "wf_tableinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Brack [ (Infix Arg .. Arg) ])
              (TupE
                (VarE "i")
                (IterE (VarE "j#4") Opt (iterexp "j#4" (VarE "j?")))
              )
            )
          )
          (expfield
            (Atom REFS)
            (IterE (OptE (VarE "a#4")) List (iterexp "a#4" (VarE "a*")))
          )
        )
      )
    )
    (RulePr
      "wf_tableinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Brack [ (Infix Arg .. Arg) ])
              (TupE
                (CaseE Arg (TupE (VarE "i'")))
                (IterE (VarE "j#5") Opt (iterexp "j#5" (VarE "j?")))
              )
            )
          )
          (expfield
            (Atom REFS)
            (CatE
              (IterE (OptE (VarE "a#5")) List (iterexp "a#5" (VarE "a*")))
              (IterE (OptE) (ListN (VarE "n")))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "x0" (VarT "tableinst"))
    (ExpP "x1" nat)
    (ExpA (VarE "x0"))
    (ExpA (VarE "x1"))
    (OptE)
    ElsePr
  )
)
(HintD (DecH "growtable" (hint "partial" "{}")))
(DecD
  "growmemory"
  (ExpP "meminst" (VarT "meminst"))
  (ExpP "nat" nat)
  (IterT (VarT "meminst") Opt)
  (DefD
    (ExpP "mi" (VarT "meminst"))
    (ExpP "n" nat)
    (ExpP "mi'" (VarT "meminst"))
    (ExpA (VarE "mi"))
    (ExpA (VarE "n"))
    (OptE (VarE "mi'"))
    (LetPr
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Brack [ (Infix Arg .. Arg) ])
            (TupE
              (VarE "i")
              (IterE (VarE "j#6") Opt (iterexp "j#6" (VarE "j?")))
            )
          )
        )
        (expfield
          (Atom BYTES)
          (IterE (VarE "b#3") List (iterexp "b#3" (VarE "b*")))
        )
      )
      (VarE "mi")
    )
    (LetPr
      (VarE "i'")
      (BinE
        AddOp
        rat
        (BinE
          DivOp
          rat
          (CvtE
            nat
            rat
            (LenE (IterE (VarE "b#4") List (iterexp "b#4" (VarE "b*"))))
          )
          (CvtE nat rat (BinE MulOp nat (NumE (Nat 64)) (CallE "Ki")))
        )
        (CvtE nat rat (VarE "n"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "mi'")
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Brack [ (Infix Arg .. Arg) ])
              (TupE
                (CaseE Arg (TupE (CvtE rat nat (VarE "i'"))))
                (IterE (VarE "j#7") Opt (iterexp "j#7" (VarE "j?")))
              )
            )
          )
          (expfield
            (Atom BYTES)
            (CatE
              (IterE (VarE "b#5") List (iterexp "b#5" (VarE "b*")))
              (IterE
                (CaseE Arg (TupE (NumE (Nat 0))))
                (ListN
                  (BinE
                    MulOp
                    nat
                    (VarE "n")
                    (BinE MulOp nat (NumE (Nat 64)) (CallE "Ki"))
                  )
                )
              )
            )
          )
        )
      )
    )
    (IterPr
      (IfPr
        (CmpE
          LeOp
          rat
          (VarE "i'")
          (CvtE nat rat (ProjE (CallE "proj_uN_0" (ExpA (VarE "j#8"))) 0))
        )
      )
      Opt
      (iterexp "j#8" (VarE "j?"))
    )
    (RulePr "wf_meminst" (Seq Arg) (TupE (VarE "mi'")))
    (RulePr
      "wf_meminst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Brack [ (Infix Arg .. Arg) ])
              (TupE
                (VarE "i")
                (IterE (VarE "j#9") Opt (iterexp "j#9" (VarE "j?")))
              )
            )
          )
          (expfield
            (Atom BYTES)
            (IterE (VarE "b#6") List (iterexp "b#6" (VarE "b*")))
          )
        )
      )
    )
    (RulePr
      "wf_meminst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Brack [ (Infix Arg .. Arg) ])
              (TupE
                (CaseE Arg (TupE (CvtE rat nat (VarE "i'"))))
                (IterE (VarE "j#10") Opt (iterexp "j#10" (VarE "j?")))
              )
            )
          )
          (expfield
            (Atom BYTES)
            (CatE
              (IterE (VarE "b#7") List (iterexp "b#7" (VarE "b*")))
              (IterE
                (CaseE Arg (TupE (NumE (Nat 0))))
                (ListN
                  (BinE
                    MulOp
                    nat
                    (VarE "n")
                    (BinE MulOp nat (NumE (Nat 64)) (CallE "Ki"))
                  )
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "x0" (VarT "meminst"))
    (ExpP "x1" nat)
    (ExpA (VarE "x0"))
    (ExpA (VarE "x1"))
    (OptE)
    ElsePr
  )
)
(HintD (DecH "growmemory" (hint "partial" "{}")))
(TypD
  "context"
  (InstD
    (StructT
      (typfield (Atom TYPES) (IterT (VarT "functype") List))
      (typfield (Atom FUNCS) (IterT (VarT "functype") List))
      (typfield (Atom GLOBALS) (IterT (VarT "globaltype") List))
      (typfield (Atom TABLES) (IterT (VarT "tabletype") List))
      (typfield (Atom MEMS) (IterT (VarT "memtype") List))
      (typfield (Atom LOCALS) (IterT (VarT "valtype") List))
      (typfield (Atom LABELS) (IterT (VarT "resulttype") List))
      (typfield (Atom RETURN) (IterT (VarT "resulttype") Opt))
    )
  )
)
(RelD
  "wf_context"
  (Seq Arg)
  (TupT (typbind "_" (VarT "context")))
  (RuleD
    "context_case_"
    (ExpP "var_0*" (IterT (VarT "functype") List))
    (ExpP "var_1*" (IterT (VarT "functype") List))
    (ExpP "var_2*" (IterT (VarT "globaltype") List))
    (ExpP "var_3*" (IterT (VarT "tabletype") List))
    (ExpP "var_4*" (IterT (VarT "memtype") List))
    (ExpP "var_5*" (IterT (VarT "valtype") List))
    (ExpP "var_6*" (IterT (VarT "resulttype") List))
    (ExpP "var_7?" (IterT (VarT "resulttype") Opt))
    (Seq Arg)
    (TupE
      (StrE
        (expfield (Atom TYPES) (VarE "var_0*"))
        (expfield (Atom FUNCS) (VarE "var_1*"))
        (expfield (Atom GLOBALS) (VarE "var_2*"))
        (expfield (Atom TABLES) (VarE "var_3*"))
        (expfield (Atom MEMS) (VarE "var_4*"))
        (expfield (Atom LOCALS) (VarE "var_5*"))
        (expfield (Atom LABELS) (VarE "var_6*"))
        (expfield (Atom RETURN) (VarE "var_7?"))
      )
    )
    (IterPr
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "var_3")))
      List
      (iterexp "var_3" (VarE "var_3*"))
    )
    (IterPr
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "var_4")))
      List
      (iterexp "var_4" (VarE "var_4*"))
    )
  )
)
(HintD (RelH "wf_context" (hint "wf-relation" "context")))
(HintD (TypH "context" (hint "desc" "\"context\"")))
(RelD
  "Limits_ok"
  (Infix (Seq) |- (Infix Arg : Arg))
  (TupT (typbind "_" (VarT "limits")) (typbind "_" nat))
  (RuleD
    ""
    (ExpP "n" (VarT "n"))
    (ExpP "m?" (IterT (VarT "m") Opt))
    (ExpP "k" nat)
    (Infix (Seq) |- (Infix Arg : Arg))
    (TupE
      (CaseE
        (Brack [ (Infix Arg .. Arg) ])
        (TupE
          (CaseE Arg (TupE (VarE "n")))
          (IterE (CaseE Arg (TupE (VarE "m"))) Opt (iterexp "m" (VarE "m?")))
        )
      )
      (VarE "k")
    )
    (IfPr (CmpE LeOp nat (VarE "n") (VarE "k")))
    (IterPr
      (IfPr
        (BinE
          AndOp
          bool
          (CmpE LeOp nat (VarE "n") (VarE "m"))
          (CmpE LeOp nat (VarE "m") (VarE "k"))
        )
      )
      Opt
      (iterexp "m" (VarE "m?"))
    )
    (RulePr
      "wf_limits"
      (Seq Arg)
      (TupE
        (CaseE
          (Brack [ (Infix Arg .. Arg) ])
          (TupE
            (CaseE Arg (TupE (VarE "n")))
            (IterE (CaseE Arg (TupE (VarE "m"))) Opt (iterexp "m" (VarE "m?")))
          )
        )
      )
    )
  )
)
(HintD (RelH "Limits_ok" (hint "show" "\"K-limits\"")))
(RelD
  "Functype_ok"
  (Infix (Seq) |- (Infix Arg : (Atom OK)))
  (VarT "functype")
  (RuleD
    ""
    (ExpP "t_1*" (IterT (VarT "valtype") List))
    (ExpP "t_2?" (IterT (VarT "valtype") Opt))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (CaseE
      (Infix Arg -> Arg)
      (TupE
        (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
        (LiftE (IterE (VarE "t_2") Opt (iterexp "t_2" (VarE "t_2?"))))
      )
    )
  )
)
(HintD (RelH "Functype_ok" (hint "show" "\"K-func\"")))
(RelD
  "Globaltype_ok"
  (Infix (Seq) |- (Infix Arg : (Atom OK)))
  (VarT "globaltype")
  (RuleD
    ""
    (ExpP "t" (VarT "valtype"))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (CaseE (Seq Arg Arg) (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "t")))
  )
)
(HintD (RelH "Globaltype_ok" (hint "show" "\"K-global\"")))
(RelD
  "Tabletype_ok"
  (Infix (Seq) |- (Infix Arg : (Atom OK)))
  (VarT "tabletype")
  (RuleD
    ""
    (ExpP "limits" (VarT "limits"))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (VarE "limits")
    (RulePr
      "Limits_ok"
      (Infix (Seq) |- (Infix Arg : Arg))
      (TupE
        (VarE "limits")
        (CvtE
          int
          nat
          (BinE
            SubOp
            int
            (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 32))))
            (CvtE nat int (NumE (Nat 1)))
          )
        )
      )
    )
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "limits")))
  )
)
(HintD (RelH "Tabletype_ok" (hint "show" "\"K-table\"")))
(RelD
  "Memtype_ok"
  (Infix (Seq) |- (Infix Arg : (Atom OK)))
  (VarT "memtype")
  (RuleD
    ""
    (ExpP "limits" (VarT "limits"))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (VarE "limits")
    (RulePr
      "Limits_ok"
      (Infix (Seq) |- (Infix Arg : Arg))
      (TupE (VarE "limits") (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 16))))
    )
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "limits")))
  )
)
(HintD (RelH "Memtype_ok" (hint "show" "\"K-mem\"")))
(RelD
  "Externtype_ok"
  (Infix (Seq) |- (Infix Arg : (Atom OK)))
  (VarT "externtype")
  (RuleD
    "func"
    (ExpP "functype" (VarT "functype"))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "functype")))
    (RulePr
      "Functype_ok"
      (Infix (Seq) |- (Infix Arg : (Atom OK)))
      (VarE "functype")
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "functype"))))
    )
  )
  (RuleD
    "global"
    (ExpP "globaltype" (VarT "globaltype"))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "globaltype")))
    (RulePr
      "Globaltype_ok"
      (Infix (Seq) |- (Infix Arg : (Atom OK)))
      (VarE "globaltype")
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "globaltype"))))
    )
  )
  (RuleD
    "table"
    (ExpP "tabletype" (VarT "tabletype"))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tabletype")))
    (RulePr
      "Tabletype_ok"
      (Infix (Seq) |- (Infix Arg : (Atom OK)))
      (VarE "tabletype")
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tabletype"))))
    )
  )
  (RuleD
    "mem"
    (ExpP "memtype" (VarT "memtype"))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "memtype")))
    (RulePr
      "Memtype_ok"
      (Infix (Seq) |- (Infix Arg : (Atom OK)))
      (VarE "memtype")
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "memtype"))))
    )
  )
)
(HintD (RelH "Externtype_ok" (hint "show" "\"K-extern\"")))
(RelD
  "Limits_sub"
  (Infix (Seq) |- (Infix Arg <: Arg))
  (TupT (typbind "_" (VarT "limits")) (typbind "_" (VarT "limits")))
  (RuleD
    "max"
    (ExpP "n_1" (VarT "n"))
    (ExpP "m_1" (VarT "m"))
    (ExpP "n_2" (VarT "n"))
    (ExpP "m_2?" (IterT (VarT "m") Opt))
    (Infix (Seq) |- (Infix Arg <: Arg))
    (TupE
      (CaseE
        (Brack [ (Infix Arg .. Arg) ])
        (TupE
          (CaseE Arg (TupE (VarE "n_1")))
          (OptE (CaseE Arg (TupE (VarE "m_1"))))
        )
      )
      (CaseE
        (Brack [ (Infix Arg .. Arg) ])
        (TupE
          (CaseE Arg (TupE (VarE "n_2")))
          (IterE
            (CaseE Arg (TupE (VarE "m_2")))
            Opt
            (iterexp "m_2" (VarE "m_2?"))
          )
        )
      )
    )
    (IfPr (CmpE GeOp nat (VarE "n_1") (VarE "n_2")))
    (IterPr
      (IfPr (CmpE LeOp nat (VarE "m_1") (VarE "m_2")))
      Opt
      (iterexp "m_2" (VarE "m_2?"))
    )
    (RulePr
      "wf_limits"
      (Seq Arg)
      (TupE
        (CaseE
          (Brack [ (Infix Arg .. Arg) ])
          (TupE
            (CaseE Arg (TupE (VarE "n_1")))
            (OptE (CaseE Arg (TupE (VarE "m_1"))))
          )
        )
      )
    )
    (RulePr
      "wf_limits"
      (Seq Arg)
      (TupE
        (CaseE
          (Brack [ (Infix Arg .. Arg) ])
          (TupE
            (CaseE Arg (TupE (VarE "n_2")))
            (IterE
              (CaseE Arg (TupE (VarE "m_2")))
              Opt
              (iterexp "m_2" (VarE "m_2?"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "eps"
    (ExpP "n_1" (VarT "n"))
    (ExpP "n_2" (VarT "n"))
    (Infix (Seq) |- (Infix Arg <: Arg))
    (TupE
      (CaseE
        (Brack [ (Infix Arg .. Arg) ])
        (TupE (CaseE Arg (TupE (VarE "n_1"))) (OptE))
      )
      (CaseE
        (Brack [ (Infix Arg .. Arg) ])
        (TupE (CaseE Arg (TupE (VarE "n_2"))) (OptE))
      )
    )
    (IfPr (CmpE GeOp nat (VarE "n_1") (VarE "n_2")))
    (RulePr
      "wf_limits"
      (Seq Arg)
      (TupE
        (CaseE
          (Brack [ (Infix Arg .. Arg) ])
          (TupE (CaseE Arg (TupE (VarE "n_1"))) (OptE))
        )
      )
    )
    (RulePr
      "wf_limits"
      (Seq Arg)
      (TupE
        (CaseE
          (Brack [ (Infix Arg .. Arg) ])
          (TupE (CaseE Arg (TupE (VarE "n_2"))) (OptE))
        )
      )
    )
  )
)
(HintD (RelH "Limits_sub" (hint "show" "\"S-limits\"")))
(RelD
  "Functype_sub"
  (Infix (Seq) |- (Infix Arg <: Arg))
  (TupT (typbind "_" (VarT "functype")) (typbind "_" (VarT "functype")))
  (RuleD
    ""
    (ExpP "ft" (VarT "functype"))
    (Infix (Seq) |- (Infix Arg <: Arg))
    (TupE (VarE "ft") (VarE "ft"))
  )
)
(HintD (RelH "Functype_sub" (hint "show" "\"S-func\"")))
(RelD
  "Globaltype_sub"
  (Infix (Seq) |- (Infix Arg <: Arg))
  (TupT (typbind "_" (VarT "globaltype")) (typbind "_" (VarT "globaltype")))
  (RuleD
    ""
    (ExpP "gt" (VarT "globaltype"))
    (Infix (Seq) |- (Infix Arg <: Arg))
    (TupE (VarE "gt") (VarE "gt"))
  )
)
(HintD (RelH "Globaltype_sub" (hint "show" "\"S-global\"")))
(RelD
  "Tabletype_sub"
  (Infix (Seq) |- (Infix Arg <: Arg))
  (TupT (typbind "_" (VarT "tabletype")) (typbind "_" (VarT "tabletype")))
  (RuleD
    ""
    (ExpP "lim_1" (VarT "limits"))
    (ExpP "lim_2" (VarT "limits"))
    (Infix (Seq) |- (Infix Arg <: Arg))
    (TupE (VarE "lim_1") (VarE "lim_2"))
    (RulePr
      "Limits_sub"
      (Infix (Seq) |- (Infix Arg <: Arg))
      (TupE (VarE "lim_1") (VarE "lim_2"))
    )
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "lim_1")))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "lim_2")))
  )
)
(HintD (RelH "Tabletype_sub" (hint "show" "\"S-table\"")))
(RelD
  "Memtype_sub"
  (Infix (Seq) |- (Infix Arg <: Arg))
  (TupT (typbind "_" (VarT "memtype")) (typbind "_" (VarT "memtype")))
  (RuleD
    ""
    (ExpP "lim_1" (VarT "limits"))
    (ExpP "lim_2" (VarT "limits"))
    (Infix (Seq) |- (Infix Arg <: Arg))
    (TupE (VarE "lim_1") (VarE "lim_2"))
    (RulePr
      "Limits_sub"
      (Infix (Seq) |- (Infix Arg <: Arg))
      (TupE (VarE "lim_1") (VarE "lim_2"))
    )
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "lim_1")))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "lim_2")))
  )
)
(HintD (RelH "Memtype_sub" (hint "show" "\"S-mem\"")))
(RelD
  "Externtype_sub"
  (Infix (Seq) |- (Infix Arg <: Arg))
  (TupT (typbind "_" (VarT "externtype")) (typbind "_" (VarT "externtype")))
  (RuleD
    "func"
    (ExpP "ft_1" (VarT "functype"))
    (ExpP "ft_2" (VarT "functype"))
    (Infix (Seq) |- (Infix Arg <: Arg))
    (TupE
      (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "ft_1")))
      (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "ft_2")))
    )
    (RulePr
      "Functype_sub"
      (Infix (Seq) |- (Infix Arg <: Arg))
      (TupE (VarE "ft_1") (VarE "ft_2"))
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "ft_1"))))
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "ft_2"))))
    )
  )
  (RuleD
    "global"
    (ExpP "gt_1" (VarT "globaltype"))
    (ExpP "gt_2" (VarT "globaltype"))
    (Infix (Seq) |- (Infix Arg <: Arg))
    (TupE
      (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "gt_1")))
      (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "gt_2")))
    )
    (RulePr
      "Globaltype_sub"
      (Infix (Seq) |- (Infix Arg <: Arg))
      (TupE (VarE "gt_1") (VarE "gt_2"))
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "gt_1"))))
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "gt_2"))))
    )
  )
  (RuleD
    "table"
    (ExpP "tt_1" (VarT "tabletype"))
    (ExpP "tt_2" (VarT "tabletype"))
    (Infix (Seq) |- (Infix Arg <: Arg))
    (TupE
      (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tt_1")))
      (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tt_2")))
    )
    (RulePr
      "Tabletype_sub"
      (Infix (Seq) |- (Infix Arg <: Arg))
      (TupE (VarE "tt_1") (VarE "tt_2"))
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tt_1"))))
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tt_2"))))
    )
  )
  (RuleD
    "mem"
    (ExpP "mt_1" (VarT "memtype"))
    (ExpP "mt_2" (VarT "memtype"))
    (Infix (Seq) |- (Infix Arg <: Arg))
    (TupE
      (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "mt_1")))
      (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "mt_2")))
    )
    (RulePr
      "Memtype_sub"
      (Infix (Seq) |- (Infix Arg <: Arg))
      (TupE (VarE "mt_1") (VarE "mt_2"))
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "mt_1"))))
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "mt_2"))))
    )
  )
)
(HintD (RelH "Externtype_sub" (hint "show" "\"S-extern\"")))
(RecD
  (RelD
    "Instr_ok"
    (Infix Arg |- (Infix Arg : Arg))
    (TupT
      (typbind "_" (VarT "context"))
      (typbind "_" (VarT "instr"))
      (typbind "_" (VarT "functype"))
    )
    (RuleD
      "nop"
      (ExpP "C" (VarT "context"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom NOP) (TupE))
        (CaseE (Infix Arg -> Arg) (TupE (ListE) (ListE)))
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_instr" (Seq Arg) (TupE (CaseE (Atom NOP) (TupE))))
    )
    (RuleD
      "unreachable"
      (ExpP "C" (VarT "context"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom UNREACHABLE) (TupE))
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
            (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_instr" (Seq Arg) (TupE (CaseE (Atom UNREACHABLE) (TupE))))
    )
    (RuleD
      "drop"
      (ExpP "C" (VarT "context"))
      (ExpP "t" (VarT "valtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom DROP) (TupE))
        (CaseE (Infix Arg -> Arg) (TupE (ListE (VarE "t")) (ListE)))
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_instr" (Seq Arg) (TupE (CaseE (Atom DROP) (TupE))))
    )
    (RuleD
      "select"
      (ExpP "C" (VarT "context"))
      (ExpP "t" (VarT "valtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom SELECT) (TupE))
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (ListE (VarE "t") (VarE "t") (CaseE (Atom I32) (TupE)))
            (ListE (VarE "t"))
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_instr" (Seq Arg) (TupE (CaseE (Atom SELECT) (TupE))))
    )
    (RuleD
      "block"
      (ExpP "C" (VarT "context"))
      (ExpP "t?" (IterT (VarT "valtype") Opt))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom BLOCK) Arg Arg)
          (TupE
            (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
            (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          )
        )
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (ListE)
            (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
          )
        )
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (CompE
            (StrE
              (expfield (Atom TYPES) (ListE))
              (expfield (Atom FUNCS) (ListE))
              (expfield (Atom GLOBALS) (ListE))
              (expfield (Atom TABLES) (ListE))
              (expfield (Atom MEMS) (ListE))
              (expfield (Atom LOCALS) (ListE))
              (expfield
                (Atom LABELS)
                (ListE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
              )
              (expfield (Atom RETURN) (OptE))
            )
            (VarE "C")
          )
          (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (ListE)
              (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
            )
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom BLOCK) Arg Arg)
            (TupE
              (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
              (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
            )
          )
        )
      )
      (RulePr
        "wf_context"
        (Seq Arg)
        (TupE
          (StrE
            (expfield (Atom TYPES) (ListE))
            (expfield (Atom FUNCS) (ListE))
            (expfield (Atom GLOBALS) (ListE))
            (expfield (Atom TABLES) (ListE))
            (expfield (Atom MEMS) (ListE))
            (expfield (Atom LOCALS) (ListE))
            (expfield
              (Atom LABELS)
              (ListE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
            )
            (expfield (Atom RETURN) (OptE))
          )
        )
      )
    )
    (RuleD
      "loop"
      (ExpP "C" (VarT "context"))
      (ExpP "t?" (IterT (VarT "valtype") Opt))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom LOOP) Arg Arg)
          (TupE
            (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
            (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          )
        )
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (ListE)
            (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
          )
        )
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (CompE
            (StrE
              (expfield (Atom TYPES) (ListE))
              (expfield (Atom FUNCS) (ListE))
              (expfield (Atom GLOBALS) (ListE))
              (expfield (Atom TABLES) (ListE))
              (expfield (Atom MEMS) (ListE))
              (expfield (Atom LOCALS) (ListE))
              (expfield (Atom LABELS) (ListE (OptE)))
              (expfield (Atom RETURN) (OptE))
            )
            (VarE "C")
          )
          (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          (CaseE (Infix Arg -> Arg) (TupE (ListE) (ListE)))
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom LOOP) Arg Arg)
            (TupE
              (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
              (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
            )
          )
        )
      )
      (RulePr
        "wf_context"
        (Seq Arg)
        (TupE
          (StrE
            (expfield (Atom TYPES) (ListE))
            (expfield (Atom FUNCS) (ListE))
            (expfield (Atom GLOBALS) (ListE))
            (expfield (Atom TABLES) (ListE))
            (expfield (Atom MEMS) (ListE))
            (expfield (Atom LOCALS) (ListE))
            (expfield (Atom LABELS) (ListE (OptE)))
            (expfield (Atom RETURN) (OptE))
          )
        )
      )
    )
    (RuleD
      "if"
      (ExpP "C" (VarT "context"))
      (ExpP "t?" (IterT (VarT "valtype") Opt))
      (ExpP "instr_1*" (IterT (VarT "instr") List))
      (ExpP "instr_2*" (IterT (VarT "instr") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupE
            (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
            (IterE (VarE "instr_1") List (iterexp "instr_1" (VarE "instr_1*")))
            (IterE (VarE "instr_2") List (iterexp "instr_2" (VarE "instr_2*")))
          )
        )
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (ListE (CaseE (Atom I32) (TupE)))
            (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
          )
        )
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (CompE
            (StrE
              (expfield (Atom TYPES) (ListE))
              (expfield (Atom FUNCS) (ListE))
              (expfield (Atom GLOBALS) (ListE))
              (expfield (Atom TABLES) (ListE))
              (expfield (Atom MEMS) (ListE))
              (expfield (Atom LOCALS) (ListE))
              (expfield
                (Atom LABELS)
                (ListE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
              )
              (expfield (Atom RETURN) (OptE))
            )
            (VarE "C")
          )
          (IterE (VarE "instr_1") List (iterexp "instr_1" (VarE "instr_1*")))
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (ListE)
              (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
            )
          )
        )
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (CompE
            (StrE
              (expfield (Atom TYPES) (ListE))
              (expfield (Atom FUNCS) (ListE))
              (expfield (Atom GLOBALS) (ListE))
              (expfield (Atom TABLES) (ListE))
              (expfield (Atom MEMS) (ListE))
              (expfield (Atom LOCALS) (ListE))
              (expfield
                (Atom LABELS)
                (ListE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
              )
              (expfield (Atom RETURN) (OptE))
            )
            (VarE "C")
          )
          (IterE (VarE "instr_2") List (iterexp "instr_2" (VarE "instr_2*")))
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (ListE)
              (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
            )
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
            (TupE
              (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
              (IterE
                (VarE "instr_1")
                List
                (iterexp "instr_1" (VarE "instr_1*"))
              )
              (IterE
                (VarE "instr_2")
                List
                (iterexp "instr_2" (VarE "instr_2*"))
              )
            )
          )
        )
      )
      (RulePr
        "wf_context"
        (Seq Arg)
        (TupE
          (StrE
            (expfield (Atom TYPES) (ListE))
            (expfield (Atom FUNCS) (ListE))
            (expfield (Atom GLOBALS) (ListE))
            (expfield (Atom TABLES) (ListE))
            (expfield (Atom MEMS) (ListE))
            (expfield (Atom LOCALS) (ListE))
            (expfield
              (Atom LABELS)
              (ListE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
            )
            (expfield (Atom RETURN) (OptE))
          )
        )
      )
    )
    (RuleD
      "br"
      (ExpP "C" (VarT "context"))
      (ExpP "l" (VarT "labelidx"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t?" (IterT (VarT "valtype") Opt))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom BR) Arg) (TupE (VarE "l")))
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (CatE
              (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
              (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
            )
            (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom LABELS))
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "l"))) 0)
          )
          (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom BR) Arg) (TupE (VarE "l"))))
      )
    )
    (RuleD
      "br_if"
      (ExpP "C" (VarT "context"))
      (ExpP "l" (VarT "labelidx"))
      (ExpP "t?" (IterT (VarT "valtype") Opt))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom BR_IF) Arg) (TupE (VarE "l")))
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (CatE
              (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
              (ListE (CaseE (Atom I32) (TupE)))
            )
            (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom LABELS))
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "l"))) 0)
          )
          (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom BR_IF) Arg) (TupE (VarE "l"))))
      )
    )
    (RuleD
      "br_table"
      (ExpP "C" (VarT "context"))
      (ExpP "l*" (IterT (VarT "labelidx") List))
      (ExpP "l'" (VarT "labelidx"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t?" (IterT (VarT "valtype") Opt))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom BR_TABLE) Arg Arg)
          (TupE (IterE (VarE "l") List (iterexp "l" (VarE "l*"))) (VarE "l'"))
        )
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (CatE
              (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
              (CatE
                (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
                (ListE (CaseE (Atom I32) (TupE)))
              )
            )
            (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
          (IdxE
            (DotE (VarE "C") (Atom LABELS))
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "l'"))) 0)
          )
        )
      )
      (IterPr
        (IfPr
          (CmpE
            EqOp
            bool
            (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
            (IdxE
              (DotE (VarE "C") (Atom LABELS))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "l"))) 0)
            )
          )
        )
        List
        (iterexp "l" (VarE "l*"))
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom BR_TABLE) Arg Arg)
            (TupE (IterE (VarE "l") List (iterexp "l" (VarE "l*"))) (VarE "l'"))
          )
        )
      )
    )
    (RuleD
      "call"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2?" (IterT (VarT "valtype") Opt))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
            (LiftE (IterE (VarE "t_2") Opt (iterexp "t_2" (VarE "t_2?"))))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom FUNCS))
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
          )
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
              (LiftE (IterE (VarE "t_2") Opt (iterexp "t_2" (VarE "t_2?"))))
            )
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "x"))))
      )
    )
    (RuleD
      "call_indirect"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2?" (IterT (VarT "valtype") Opt))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (CatE
              (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
              (ListE (CaseE (Atom I32) (TupE)))
            )
            (LiftE (IterE (VarE "t_2") Opt (iterexp "t_2" (VarE "t_2?"))))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
          )
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
              (LiftE (IterE (VarE "t_2") Opt (iterexp "t_2" (VarE "t_2?"))))
            )
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "x"))))
      )
    )
    (RuleD
      "return"
      (ExpP "C" (VarT "context"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t?" (IterT (VarT "valtype") Opt))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom RETURN) (TupE))
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (CatE
              (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
              (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
            )
            (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (DotE (VarE "C") (Atom RETURN))
          (OptE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_instr" (Seq Arg) (TupE (CaseE (Atom RETURN) (TupE))))
    )
    (RuleD
      "const"
      (ExpP "C" (VarT "context"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "c_t" (VarT "val_"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_t")))
        (CaseE (Infix Arg -> Arg) (TupE (ListE) (ListE (VarE "t"))))
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_t"))))
      )
    )
    (RuleD
      "unop"
      (ExpP "C" (VarT "context"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "unop_t" (VarT "unop_"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom UNOP) Arg Arg) (TupE (VarE "t") (VarE "unop_t")))
        (CaseE (Infix Arg -> Arg) (TupE (ListE (VarE "t")) (ListE (VarE "t"))))
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE
          (CaseE (Seq (Atom UNOP) Arg Arg) (TupE (VarE "t") (VarE "unop_t")))
        )
      )
    )
    (RuleD
      "binop"
      (ExpP "C" (VarT "context"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "binop_t" (VarT "binop_"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom BINOP) Arg Arg) (TupE (VarE "t") (VarE "binop_t")))
        (CaseE
          (Infix Arg -> Arg)
          (TupE (ListE (VarE "t") (VarE "t")) (ListE (VarE "t")))
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE
          (CaseE (Seq (Atom BINOP) Arg Arg) (TupE (VarE "t") (VarE "binop_t")))
        )
      )
    )
    (RuleD
      "testop"
      (ExpP "C" (VarT "context"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "testop_t" (VarT "testop_"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom TESTOP) Arg Arg) (TupE (VarE "t") (VarE "testop_t")))
        (CaseE
          (Infix Arg -> Arg)
          (TupE (ListE (VarE "t")) (ListE (CaseE (Atom I32) (TupE))))
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom TESTOP) Arg Arg)
            (TupE (VarE "t") (VarE "testop_t"))
          )
        )
      )
    )
    (RuleD
      "relop"
      (ExpP "C" (VarT "context"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "relop_t" (VarT "relop_"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom RELOP) Arg Arg) (TupE (VarE "t") (VarE "relop_t")))
        (CaseE
          (Infix Arg -> Arg)
          (TupE (ListE (VarE "t") (VarE "t")) (ListE (CaseE (Atom I32) (TupE))))
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE
          (CaseE (Seq (Atom RELOP) Arg Arg) (TupE (VarE "t") (VarE "relop_t")))
        )
      )
    )
    (RuleD
      "cvtop-reinterpret"
      (ExpP "C" (VarT "context"))
      (ExpP "nt_1" (VarT "valtype"))
      (ExpP "nt_2" (VarT "valtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupE (VarE "nt_1") (VarE "nt_2") (CaseE (Atom REINTERPRET) (TupE)))
        )
        (CaseE
          (Infix Arg -> Arg)
          (TupE (ListE (VarE "nt_2")) (ListE (VarE "nt_1")))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (CallE "size" (ExpA (VarE "nt_1")))
          (CallE "size" (ExpA (VarE "nt_2")))
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom CVTOP) Arg Arg Arg)
            (TupE (VarE "nt_1") (VarE "nt_2") (CaseE (Atom REINTERPRET) (TupE)))
          )
        )
      )
    )
    (RuleD
      "cvtop-convert"
      (ExpP "C" (VarT "context"))
      (ExpP "nt_1" (VarT "valtype"))
      (ExpP "nt_2" (VarT "valtype"))
      (ExpP "cvtop" (VarT "cvtop"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupE (VarE "nt_1") (VarE "nt_2") (VarE "cvtop"))
        )
        (CaseE
          (Infix Arg -> Arg)
          (TupE (ListE (VarE "nt_2")) (ListE (VarE "nt_1")))
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom CVTOP) Arg Arg Arg)
            (TupE (VarE "nt_1") (VarE "nt_2") (VarE "cvtop"))
          )
        )
      )
    )
    (RuleD
      "local.get"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t" (VarT "valtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom LOCAL.GET) Arg) (TupE (VarE "x")))
        (CaseE (Infix Arg -> Arg) (TupE (ListE) (ListE (VarE "t"))))
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom LOCALS))
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
          )
          (VarE "t")
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom LOCAL.GET) Arg) (TupE (VarE "x"))))
      )
    )
    (RuleD
      "local.set"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t" (VarT "valtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom LOCAL.SET) Arg) (TupE (VarE "x")))
        (CaseE (Infix Arg -> Arg) (TupE (ListE (VarE "t")) (ListE)))
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom LOCALS))
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
          )
          (VarE "t")
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom LOCAL.SET) Arg) (TupE (VarE "x"))))
      )
    )
    (RuleD
      "local.tee"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t" (VarT "valtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom LOCAL.TEE) Arg) (TupE (VarE "x")))
        (CaseE (Infix Arg -> Arg) (TupE (ListE (VarE "t")) (ListE (VarE "t"))))
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom LOCALS))
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
          )
          (VarE "t")
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom LOCAL.TEE) Arg) (TupE (VarE "x"))))
      )
    )
    (RuleD
      "global.get"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "mut" (VarT "mut"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "x")))
        (CaseE (Infix Arg -> Arg) (TupE (ListE) (ListE (VarE "t"))))
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom GLOBALS))
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
          )
          (CaseE (Seq Arg Arg) (TupE (VarE "mut") (VarE "t")))
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "x"))))
      )
    )
    (RuleD
      "global.set"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t" (VarT "valtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom GLOBAL.SET) Arg) (TupE (VarE "x")))
        (CaseE (Infix Arg -> Arg) (TupE (ListE (VarE "t")) (ListE)))
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom GLOBALS))
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
          )
          (CaseE
            (Seq Arg Arg)
            (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "t"))
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom GLOBAL.SET) Arg) (TupE (VarE "x"))))
      )
    )
    (RuleD
      "memory.size"
      (ExpP "C" (VarT "context"))
      (ExpP "mt" (VarT "memtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom MEMORY.SIZE) (TupE))
        (CaseE
          (Infix Arg -> Arg)
          (TupE (ListE) (ListE (CaseE (Atom I32) (TupE))))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "C") (Atom MEMS)) (NumE (Nat 0)))
          (VarE "mt")
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "mt")))
      (RulePr "wf_instr" (Seq Arg) (TupE (CaseE (Atom MEMORY.SIZE) (TupE))))
    )
    (RuleD
      "memory.grow"
      (ExpP "C" (VarT "context"))
      (ExpP "mt" (VarT "memtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom MEMORY.GROW) (TupE))
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (ListE (CaseE (Atom I32) (TupE)))
            (ListE (CaseE (Atom I32) (TupE)))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "C") (Atom MEMS)) (NumE (Nat 0)))
          (VarE "mt")
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "mt")))
      (RulePr "wf_instr" (Seq Arg) (TupE (CaseE (Atom MEMORY.GROW) (TupE))))
    )
    (RuleD
      "load-val"
      (ExpP "C" (VarT "context"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "memarg" (VarT "memarg"))
      (ExpP "mt" (VarT "memtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom LOAD) Arg Arg Arg)
          (TupE (VarE "t") (OptE) (VarE "memarg"))
        )
        (CaseE
          (Infix Arg -> Arg)
          (TupE (ListE (CaseE (Atom I32) (TupE))) (ListE (VarE "t")))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "C") (Atom MEMS)) (NumE (Nat 0)))
          (VarE "mt")
        )
      )
      (IfPr
        (CmpE
          LeOp
          rat
          (CvtE
            nat
            rat
            (BinE
              PowOp
              nat
              (NumE (Nat 2))
              (ProjE
                (CallE "proj_uN_0" (ExpA (DotE (VarE "memarg") (Atom ALIGN))))
                0
              )
            )
          )
          (BinE
            DivOp
            rat
            (CvtE nat rat (CallE "size" (ExpA (VarE "t"))))
            (CvtE nat rat (NumE (Nat 8)))
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "mt")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom LOAD) Arg Arg Arg)
            (TupE (VarE "t") (OptE) (VarE "memarg"))
          )
        )
      )
    )
    (RuleD
      "load-pack"
      (ExpP "C" (VarT "context"))
      (ExpP "Inn" (VarT "Inn"))
      (ExpP "M" (VarT "M"))
      (ExpP "sx" (VarT "sx"))
      (ExpP "memarg" (VarT "memarg"))
      (ExpP "mt" (VarT "memtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom LOAD) Arg Arg Arg)
          (TupE
            (CallE "valtype_Inn" (ExpA (VarE "Inn")))
            (OptE
              (CaseE
                (Seq (Atom mk_loadop__0) Arg Arg)
                (TupE
                  (VarE "Inn")
                  (CaseE
                    (Seq Arg (Atom _) Arg)
                    (TupE (CaseE Arg (TupE (VarE "M"))) (VarE "sx"))
                  )
                )
              )
            )
            (VarE "memarg")
          )
        )
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (ListE (CaseE (Atom I32) (TupE)))
            (ListE (CallE "valtype_Inn" (ExpA (VarE "Inn"))))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "C") (Atom MEMS)) (NumE (Nat 0)))
          (VarE "mt")
        )
      )
      (IfPr
        (CmpE
          LeOp
          rat
          (CvtE
            nat
            rat
            (BinE
              PowOp
              nat
              (NumE (Nat 2))
              (ProjE
                (CallE "proj_uN_0" (ExpA (DotE (VarE "memarg") (Atom ALIGN))))
                0
              )
            )
          )
          (BinE
            DivOp
            rat
            (CvtE nat rat (VarE "M"))
            (CvtE nat rat (NumE (Nat 8)))
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "mt")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom LOAD) Arg Arg Arg)
            (TupE
              (CallE "valtype_Inn" (ExpA (VarE "Inn")))
              (OptE
                (CaseE
                  (Seq (Atom mk_loadop__0) Arg Arg)
                  (TupE
                    (VarE "Inn")
                    (CaseE
                      (Seq Arg (Atom _) Arg)
                      (TupE (CaseE Arg (TupE (VarE "M"))) (VarE "sx"))
                    )
                  )
                )
              )
              (VarE "memarg")
            )
          )
        )
      )
    )
    (RuleD
      "store-val"
      (ExpP "C" (VarT "context"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "memarg" (VarT "memarg"))
      (ExpP "mt" (VarT "memtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom STORE) Arg Arg Arg)
          (TupE (VarE "t") (OptE) (VarE "memarg"))
        )
        (CaseE
          (Infix Arg -> Arg)
          (TupE (ListE (CaseE (Atom I32) (TupE)) (VarE "t")) (ListE))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "C") (Atom MEMS)) (NumE (Nat 0)))
          (VarE "mt")
        )
      )
      (IfPr
        (CmpE
          LeOp
          rat
          (CvtE
            nat
            rat
            (BinE
              PowOp
              nat
              (NumE (Nat 2))
              (ProjE
                (CallE "proj_uN_0" (ExpA (DotE (VarE "memarg") (Atom ALIGN))))
                0
              )
            )
          )
          (BinE
            DivOp
            rat
            (CvtE nat rat (CallE "size" (ExpA (VarE "t"))))
            (CvtE nat rat (NumE (Nat 8)))
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "mt")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom STORE) Arg Arg Arg)
            (TupE (VarE "t") (OptE) (VarE "memarg"))
          )
        )
      )
    )
    (RuleD
      "store-pack"
      (ExpP "C" (VarT "context"))
      (ExpP "Inn" (VarT "Inn"))
      (ExpP "M" (VarT "M"))
      (ExpP "memarg" (VarT "memarg"))
      (ExpP "mt" (VarT "memtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom STORE) Arg Arg Arg)
          (TupE
            (CallE "valtype_Inn" (ExpA (VarE "Inn")))
            (OptE (CaseE Arg (TupE (VarE "M"))))
            (VarE "memarg")
          )
        )
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (ListE
              (CaseE (Atom I32) (TupE))
              (CallE "valtype_Inn" (ExpA (VarE "Inn")))
            )
            (ListE)
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "C") (Atom MEMS)) (NumE (Nat 0)))
          (VarE "mt")
        )
      )
      (IfPr
        (CmpE
          LeOp
          rat
          (CvtE
            nat
            rat
            (BinE
              PowOp
              nat
              (NumE (Nat 2))
              (ProjE
                (CallE "proj_uN_0" (ExpA (DotE (VarE "memarg") (Atom ALIGN))))
                0
              )
            )
          )
          (BinE
            DivOp
            rat
            (CvtE nat rat (VarE "M"))
            (CvtE nat rat (NumE (Nat 8)))
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "mt")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom STORE) Arg Arg Arg)
            (TupE
              (CallE "valtype_Inn" (ExpA (VarE "Inn")))
              (OptE (CaseE Arg (TupE (VarE "M"))))
              (VarE "memarg")
            )
          )
        )
      )
    )
  )
  (RelD
    "Instrs_ok"
    (Infix Arg |- (Infix Arg : Arg))
    (TupT
      (typbind "_" (VarT "context"))
      (typbind "_" (IterT (VarT "instr") List))
      (typbind "_" (VarT "functype"))
    )
    (RuleD
      "empty"
      (ExpP "C" (VarT "context"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (ListE)
        (CaseE (Infix Arg -> Arg) (TupE (ListE) (ListE)))
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    )
    (RuleD
      "instr"
      (ExpP "C" (VarT "context"))
      (ExpP "instr" (VarT "instr"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (ListE (VarE "instr"))
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
            (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
          )
        )
      )
      (RulePr
        "Instr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (VarE "instr")
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
              (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
            )
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr")))
    )
    (RuleD
      "seq"
      (ExpP "C" (VarT "context"))
      (ExpP "instr_1*" (IterT (VarT "instr") List))
      (ExpP "instr_2*" (IterT (VarT "instr") List))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_3*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CatE
          (IterE (VarE "instr_1") List (iterexp "instr_1" (VarE "instr_1*")))
          (IterE (VarE "instr_2") List (iterexp "instr_2" (VarE "instr_2*")))
        )
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
            (IterE (VarE "t_3") List (iterexp "t_3" (VarE "t_3*")))
          )
        )
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (IterE (VarE "instr_1") List (iterexp "instr_1" (VarE "instr_1*")))
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
              (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
            )
          )
        )
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (IterE (VarE "instr_2") List (iterexp "instr_2" (VarE "instr_2*")))
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
              (IterE (VarE "t_3") List (iterexp "t_3" (VarE "t_3*")))
            )
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr_1")))
        List
        (iterexp "instr_1" (VarE "instr_1*"))
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr_2")))
        List
        (iterexp "instr_2" (VarE "instr_2*"))
      )
    )
    (RuleD
      "frame"
      (ExpP "C" (VarT "context"))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (ExpP "t*" (IterT (VarT "valtype") List))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (CatE
              (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
              (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
            )
            (CatE
              (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
              (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
            )
          )
        )
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
              (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
            )
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr")))
        List
        (iterexp "instr" (VarE "instr*"))
      )
    )
  )
)
(HintD (RelH "Instr_ok" (hint "show" "\"T\"")))
(HintD (RelH "Instrs_ok" (hint "show" "\"T*\"")))
(RelD
  "Expr_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "expr"))
    (typbind "_" (VarT "resulttype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "instr*" (IterT (VarT "instr") List))
    (ExpP "t?" (IterT (VarT "valtype") Opt))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
      (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
    )
    (RulePr
      "Instrs_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (ListE)
            (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
          )
        )
      )
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr")))
      List
      (iterexp "instr" (VarE "instr*"))
    )
  )
)
(HintD (RelH "Expr_ok" (hint "show" "\"T-expr\"")))
(RelD
  "Instr_const"
  (Infix Arg |- (Seq Arg (Atom CONST)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "instr")))
  (RuleD
    "const"
    (ExpP "C" (VarT "context"))
    (ExpP "t" (VarT "valtype"))
    (ExpP "c" (VarT "val_"))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c")))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_instr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c"))))
    )
  )
  (RuleD
    "global.get"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE (VarE "C") (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "x"))))
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE
          (DotE (VarE "C") (Atom GLOBALS))
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        )
        (CaseE (Seq Arg Arg) (TupE (OptE) (VarE "t")))
      )
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_instr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "x"))))
    )
  )
)
(HintD (RelH "Instr_const" (hint "show" "\"C-instr\"")))
(RelD
  "Expr_const"
  (Infix Arg |- (Seq Arg (Atom CONST)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "expr")))
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "instr*" (IterT (VarT "instr") List))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE
      (VarE "C")
      (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
    )
    (IterPr
      (RulePr
        "Instr_const"
        (Infix Arg |- (Seq Arg (Atom CONST)))
        (TupE (VarE "C") (VarE "instr"))
      )
      List
      (iterexp "instr" (VarE "instr*"))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr")))
      List
      (iterexp "instr" (VarE "instr*"))
    )
  )
)
(HintD (RelH "Expr_const" (hint "show" "\"C-expr\"")))
(RelD
  "Expr_ok_const"
  (Infix Arg |- (Infix Arg : (Seq Arg (Atom CONST))))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "expr"))
    (typbind "_" (IterT (VarT "valtype") Opt))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "expr" (VarT "expr"))
    (ExpP "t?" (IterT (VarT "valtype") Opt))
    (Infix Arg |- (Infix Arg : (Seq Arg (Atom CONST))))
    (TupE
      (VarE "C")
      (VarE "expr")
      (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
    )
    (RulePr
      "Expr_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (VarE "expr")
        (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
      )
    )
    (RulePr
      "Expr_const"
      (Infix Arg |- (Seq Arg (Atom CONST)))
      (TupE (VarE "C") (VarE "expr"))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "expr")))
      List
      (iterexp "expr" (VarE "expr"))
    )
  )
)
(HintD (RelH "Expr_ok_const" (hint "show" "\"TC-expr\"")))
(RelD
  "Type_ok"
  (Infix (Seq) |- (Infix Arg : Arg))
  (TupT (typbind "_" (VarT "type")) (typbind "_" (VarT "functype")))
  (RuleD
    ""
    (ExpP "ft" (VarT "functype"))
    (Infix (Seq) |- (Infix Arg : Arg))
    (TupE (CaseE (Seq (Atom TYPE) Arg) (TupE (VarE "ft"))) (VarE "ft"))
    (RulePr "Functype_ok" (Infix (Seq) |- (Infix Arg : (Atom OK))) (VarE "ft"))
  )
)
(HintD (RelH "Type_ok" (hint "show" "\"T-type\"")))
(RelD
  "Func_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "func"))
    (typbind "_" (VarT "functype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "t*" (IterT (VarT "valtype") List))
    (ExpP "expr" (VarT "expr"))
    (ExpP "t_1*" (IterT (VarT "valtype") List))
    (ExpP "t_2?" (IterT (VarT "valtype") Opt))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Seq (Atom FUNC) Arg Arg Arg)
        (TupE
          (VarE "x")
          (IterE
            (CaseE (Seq (Atom LOCAL) Arg) (TupE (VarE "t")))
            List
            (iterexp "t" (VarE "t*"))
          )
          (VarE "expr")
        )
      )
      (CaseE
        (Infix Arg -> Arg)
        (TupE
          (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
          (LiftE (IterE (VarE "t_2") Opt (iterexp "t_2" (VarE "t_2?"))))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE
          (DotE (VarE "C") (Atom TYPES))
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        )
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
            (LiftE (IterE (VarE "t_2") Opt (iterexp "t_2" (VarE "t_2?"))))
          )
        )
      )
    )
    (RulePr
      "Expr_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (CompE
          (VarE "C")
          (StrE
            (expfield (Atom TYPES) (ListE))
            (expfield (Atom FUNCS) (ListE))
            (expfield (Atom GLOBALS) (ListE))
            (expfield (Atom TABLES) (ListE))
            (expfield (Atom MEMS) (ListE))
            (expfield
              (Atom LOCALS)
              (CatE
                (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
              )
            )
            (expfield
              (Atom LABELS)
              (ListE (IterE (VarE "t_2") Opt (iterexp "t_2" (VarE "t_2?"))))
            )
            (expfield
              (Atom RETURN)
              (OptE (IterE (VarE "t_2") Opt (iterexp "t_2" (VarE "t_2?"))))
            )
          )
        )
        (VarE "expr")
        (IterE (VarE "t_2") Opt (iterexp "t_2" (VarE "t_2?")))
      )
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_func"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom FUNC) Arg Arg Arg)
          (TupE
            (VarE "x")
            (IterE
              (CaseE (Seq (Atom LOCAL) Arg) (TupE (VarE "t")))
              List
              (iterexp "t" (VarE "t*"))
            )
            (VarE "expr")
          )
        )
      )
    )
    (RulePr
      "wf_context"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom TYPES) (ListE))
          (expfield (Atom FUNCS) (ListE))
          (expfield (Atom GLOBALS) (ListE))
          (expfield (Atom TABLES) (ListE))
          (expfield (Atom MEMS) (ListE))
          (expfield
            (Atom LOCALS)
            (CatE
              (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
              (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
            )
          )
          (expfield
            (Atom LABELS)
            (ListE (IterE (VarE "t_2") Opt (iterexp "t_2" (VarE "t_2?"))))
          )
          (expfield
            (Atom RETURN)
            (OptE (IterE (VarE "t_2") Opt (iterexp "t_2" (VarE "t_2?"))))
          )
        )
      )
    )
  )
)
(HintD (RelH "Func_ok" (hint "show" "\"T-func\"")))
(RelD
  "Global_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "global"))
    (typbind "_" (VarT "globaltype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "gt" (VarT "globaltype"))
    (ExpP "expr" (VarT "expr"))
    (ExpP "mut" (VarT "mut"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom GLOBAL) Arg Arg) (TupE (VarE "gt") (VarE "expr")))
      (VarE "gt")
    )
    (RulePr
      "Globaltype_ok"
      (Infix (Seq) |- (Infix Arg : (Atom OK)))
      (VarE "gt")
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "gt")
        (CaseE (Seq Arg Arg) (TupE (VarE "mut") (VarE "t")))
      )
    )
    (RulePr
      "Expr_ok_const"
      (Infix Arg |- (Infix Arg : (Seq Arg (Atom CONST))))
      (TupE (VarE "C") (VarE "expr") (OptE (VarE "t")))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_global"
      (Seq Arg)
      (TupE
        (CaseE (Seq (Atom GLOBAL) Arg Arg) (TupE (VarE "gt") (VarE "expr")))
      )
    )
  )
)
(HintD (RelH "Global_ok" (hint "show" "\"T-global\"")))
(RelD
  "Table_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "table"))
    (typbind "_" (VarT "tabletype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "tt" (VarT "tabletype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tt")))
      (VarE "tt")
    )
    (RulePr "Tabletype_ok" (Infix (Seq) |- (Infix Arg : (Atom OK))) (VarE "tt"))
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_table"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tt"))))
    )
  )
)
(HintD (RelH "Table_ok" (hint "show" "\"T-table\"")))
(RelD
  "Mem_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "mem"))
    (typbind "_" (VarT "memtype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "mt" (VarT "memtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom MEMORY) Arg) (TupE (VarE "mt")))
      (VarE "mt")
    )
    (RulePr "Memtype_ok" (Infix (Seq) |- (Infix Arg : (Atom OK))) (VarE "mt"))
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_mem"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom MEMORY) Arg) (TupE (VarE "mt"))))
    )
  )
)
(HintD (RelH "Mem_ok" (hint "show" "\"T-mem\"")))
(RelD
  "Elem_ok"
  (Infix Arg |- (Infix Arg : (Atom OK)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "elem")))
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "expr" (VarT "expr"))
    (ExpP "x*" (IterT (VarT "idx") List))
    (ExpP "lim" (VarT "limits"))
    (ExpP "ft*" (IterT (VarT "functype") List))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE
      (VarE "C")
      (CaseE
        (Seq (Atom ELEM) Arg Arg)
        (TupE (VarE "expr") (IterE (VarE "x") List (iterexp "x" (VarE "x*"))))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE (DotE (VarE "C") (Atom TABLES)) (NumE (Nat 0)))
        (VarE "lim")
      )
    )
    (RulePr
      "Expr_ok_const"
      (Infix Arg |- (Infix Arg : (Seq Arg (Atom CONST))))
      (TupE (VarE "C") (VarE "expr") (OptE (CaseE (Atom I32) (TupE))))
    )
    (IterPr
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom FUNCS))
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
          )
          (VarE "ft")
        )
      )
      List
      (iterexp "ft" (VarE "ft*"))
      (iterexp "x" (VarE "x*"))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "lim")))
    (RulePr
      "wf_elem"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom ELEM) Arg Arg)
          (TupE (VarE "expr") (IterE (VarE "x") List (iterexp "x" (VarE "x*"))))
        )
      )
    )
  )
)
(HintD (RelH "Elem_ok" (hint "show" "\"T-elem\"")))
(RelD
  "Data_ok"
  (Infix Arg |- (Infix Arg : (Atom OK)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "data")))
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "expr" (VarT "expr"))
    (ExpP "b*" (IterT (VarT "byte") List))
    (ExpP "lim" (VarT "limits"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE
      (VarE "C")
      (CaseE
        (Seq (Atom DATA) Arg Arg)
        (TupE (VarE "expr") (IterE (VarE "b") List (iterexp "b" (VarE "b*"))))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE (DotE (VarE "C") (Atom MEMS)) (NumE (Nat 0)))
        (VarE "lim")
      )
    )
    (RulePr
      "Expr_ok_const"
      (Infix Arg |- (Infix Arg : (Seq Arg (Atom CONST))))
      (TupE (VarE "C") (VarE "expr") (OptE (CaseE (Atom I32) (TupE))))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "lim")))
    (RulePr
      "wf_data"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom DATA) Arg Arg)
          (TupE (VarE "expr") (IterE (VarE "b") List (iterexp "b" (VarE "b*"))))
        )
      )
    )
  )
)
(HintD (RelH "Data_ok" (hint "show" "\"T-data\"")))
(RelD
  "Start_ok"
  (Infix Arg |- (Infix Arg : (Atom OK)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "start")))
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE (VarE "C") (CaseE (Seq (Atom START) Arg) (TupE (VarE "x"))))
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE
          (DotE (VarE "C") (Atom FUNCS))
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        )
        (CaseE (Infix Arg -> Arg) (TupE (ListE) (ListE)))
      )
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_start"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom START) Arg) (TupE (VarE "x"))))
    )
  )
)
(HintD (RelH "Start_ok" (hint "show" "\"T-start\"")))
(RelD
  "Import_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "import"))
    (typbind "_" (VarT "externtype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "name_1" (VarT "name"))
    (ExpP "name_2" (VarT "name"))
    (ExpP "xt" (VarT "externtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Seq (Atom IMPORT) Arg Arg Arg)
        (TupE (VarE "name_1") (VarE "name_2") (VarE "xt"))
      )
      (VarE "xt")
    )
    (RulePr
      "Externtype_ok"
      (Infix (Seq) |- (Infix Arg : (Atom OK)))
      (VarE "xt")
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_import"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom IMPORT) Arg Arg Arg)
          (TupE (VarE "name_1") (VarE "name_2") (VarE "xt"))
        )
      )
    )
  )
)
(HintD (RelH "Import_ok" (hint "show" "\"T-import\"")))
(RelD
  "Externidx_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "externidx"))
    (typbind "_" (VarT "externtype"))
  )
  (RuleD
    "func"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "ft" (VarT "functype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "x")))
      (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "ft")))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE
          (DotE (VarE "C") (Atom FUNCS))
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        )
        (VarE "ft")
      )
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_externidx"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "x"))))
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "ft"))))
    )
  )
  (RuleD
    "global"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "gt" (VarT "globaltype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "x")))
      (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "gt")))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE
          (DotE (VarE "C") (Atom GLOBALS))
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        )
        (VarE "gt")
      )
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_externidx"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "x"))))
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "gt"))))
    )
  )
  (RuleD
    "table"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "tt" (VarT "tabletype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "x")))
      (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tt")))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE
          (DotE (VarE "C") (Atom TABLES))
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        )
        (VarE "tt")
      )
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_externidx"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "x"))))
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tt"))))
    )
  )
  (RuleD
    "mem"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "mt" (VarT "memtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "x")))
      (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "mt")))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE
          (DotE (VarE "C") (Atom MEMS))
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        )
        (VarE "mt")
      )
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_externidx"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "x"))))
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "mt"))))
    )
  )
)
(RelD
  "Export_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "export"))
    (typbind "_" (VarT "externtype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "name" (VarT "name"))
    (ExpP "externidx" (VarT "externidx"))
    (ExpP "xt" (VarT "externtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Seq (Atom EXPORT) Arg Arg)
        (TupE (VarE "name") (VarE "externidx"))
      )
      (VarE "xt")
    )
    (RulePr
      "Externidx_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "C") (VarE "externidx") (VarE "xt"))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr "wf_externtype" (Seq Arg) (TupE (VarE "xt")))
    (RulePr
      "wf_export"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom EXPORT) Arg Arg)
          (TupE (VarE "name") (VarE "externidx"))
        )
      )
    )
  )
)
(HintD (RelH "Export_ok" (hint "show" "\"T-export\"")))
(HintD (RelH "Externidx_ok" (hint "show" "\"T-externidx\"")))
(RelD
  "Module_ok"
  (Infix (Seq) |- (Infix Arg : (Atom OK)))
  (VarT "module")
  (RuleD
    ""
    (ExpP "type*" (IterT (VarT "type") List))
    (ExpP "import*" (IterT (VarT "import") List))
    (ExpP "func*" (IterT (VarT "func") List))
    (ExpP "global*" (IterT (VarT "global") List))
    (ExpP "table*" (IterT (VarT "table") List))
    (ExpP "mem*" (IterT (VarT "mem") List))
    (ExpP "elem*" (IterT (VarT "elem") List))
    (ExpP "data*" (IterT (VarT "data") List))
    (ExpP "start?" (IterT (VarT "start") Opt))
    (ExpP "export*" (IterT (VarT "export") List))
    (ExpP "ft'*" (IterT (VarT "functype") List))
    (ExpP "ixt*" (IterT (VarT "externtype") List))
    (ExpP "C'" (VarT "context"))
    (ExpP "gt*" (IterT (VarT "globaltype") List))
    (ExpP "C" (VarT "context"))
    (ExpP "ft*" (IterT (VarT "functype") List))
    (ExpP "tt*" (IterT (VarT "tabletype") List))
    (ExpP "mt*" (IterT (VarT "memtype") List))
    (ExpP "xt*" (IterT (VarT "externtype") List))
    (ExpP "ift*" (IterT (VarT "functype") List))
    (ExpP "igt*" (IterT (VarT "globaltype") List))
    (ExpP "itt*" (IterT (VarT "tabletype") List))
    (ExpP "imt*" (IterT (VarT "memtype") List))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (CaseE
      (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
      (TupE
        (IterE (VarE "type") List (iterexp "type" (VarE "type*")))
        (IterE (VarE "import") List (iterexp "import" (VarE "import*")))
        (IterE (VarE "func") List (iterexp "func" (VarE "func*")))
        (IterE (VarE "global") List (iterexp "global" (VarE "global*")))
        (IterE (VarE "table") List (iterexp "table" (VarE "table*")))
        (IterE (VarE "mem") List (iterexp "mem" (VarE "mem*")))
        (IterE (VarE "elem") List (iterexp "elem" (VarE "elem*")))
        (IterE (VarE "data") List (iterexp "data" (VarE "data*")))
        (IterE (VarE "start") Opt (iterexp "start" (VarE "start?")))
        (IterE (VarE "export") List (iterexp "export" (VarE "export*")))
      )
    )
    (IterPr
      (RulePr
        "Type_ok"
        (Infix (Seq) |- (Infix Arg : Arg))
        (TupE (VarE "type") (VarE "ft'"))
      )
      List
      (iterexp "ft'" (VarE "ft'*"))
      (iterexp "type" (VarE "type*"))
    )
    (IterPr
      (RulePr
        "Import_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (StrE
            (expfield
              (Atom TYPES)
              (IterE (VarE "ft'") List (iterexp "ft'" (VarE "ft'*")))
            )
            (expfield (Atom FUNCS) (ListE))
            (expfield (Atom GLOBALS) (ListE))
            (expfield (Atom TABLES) (ListE))
            (expfield (Atom MEMS) (ListE))
            (expfield (Atom LOCALS) (ListE))
            (expfield (Atom LABELS) (ListE))
            (expfield (Atom RETURN) (OptE))
          )
          (VarE "import")
          (VarE "ixt")
        )
      )
      List
      (iterexp "import" (VarE "import*"))
      (iterexp "ixt" (VarE "ixt*"))
    )
    (IterPr
      (RulePr
        "Global_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C'") (VarE "global") (VarE "gt"))
      )
      List
      (iterexp "global" (VarE "global*"))
      (iterexp "gt" (VarE "gt*"))
    )
    (IterPr
      (RulePr
        "Func_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C") (VarE "func") (VarE "ft"))
      )
      List
      (iterexp "ft" (VarE "ft*"))
      (iterexp "func" (VarE "func*"))
    )
    (IterPr
      (RulePr
        "Table_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C") (VarE "table") (VarE "tt"))
      )
      List
      (iterexp "table" (VarE "table*"))
      (iterexp "tt" (VarE "tt*"))
    )
    (IterPr
      (RulePr
        "Mem_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C") (VarE "mem") (VarE "mt"))
      )
      List
      (iterexp "mem" (VarE "mem*"))
      (iterexp "mt" (VarE "mt*"))
    )
    (IterPr
      (RulePr
        "Elem_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "elem"))
      )
      List
      (iterexp "elem" (VarE "elem*"))
    )
    (IterPr
      (RulePr
        "Data_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "data"))
      )
      List
      (iterexp "data" (VarE "data*"))
    )
    (IterPr
      (RulePr
        "Start_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "start"))
      )
      Opt
      (iterexp "start" (VarE "start?"))
    )
    (IterPr
      (RulePr
        "Export_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C") (VarE "export") (VarE "xt"))
      )
      List
      (iterexp "export" (VarE "export*"))
      (iterexp "xt" (VarE "xt*"))
    )
    (IfPr
      (CmpE
        LeOp
        nat
        (LenE (IterE (VarE "tt") List (iterexp "tt" (VarE "tt*"))))
        (NumE (Nat 1))
      )
    )
    (IfPr
      (CmpE
        LeOp
        nat
        (LenE (IterE (VarE "mt") List (iterexp "mt" (VarE "mt*"))))
        (NumE (Nat 1))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "C")
        (StrE
          (expfield
            (Atom TYPES)
            (IterE (VarE "ft'") List (iterexp "ft'" (VarE "ft'*")))
          )
          (expfield
            (Atom FUNCS)
            (CatE
              (IterE (VarE "ift") List (iterexp "ift" (VarE "ift*")))
              (IterE (VarE "ft") List (iterexp "ft" (VarE "ft*")))
            )
          )
          (expfield
            (Atom GLOBALS)
            (CatE
              (IterE (VarE "igt") List (iterexp "igt" (VarE "igt*")))
              (IterE (VarE "gt") List (iterexp "gt" (VarE "gt*")))
            )
          )
          (expfield
            (Atom TABLES)
            (CatE
              (IterE (VarE "itt") List (iterexp "itt" (VarE "itt*")))
              (IterE (VarE "tt") List (iterexp "tt" (VarE "tt*")))
            )
          )
          (expfield
            (Atom MEMS)
            (CatE
              (IterE (VarE "imt") List (iterexp "imt" (VarE "imt*")))
              (IterE (VarE "mt") List (iterexp "mt" (VarE "mt*")))
            )
          )
          (expfield (Atom LOCALS) (ListE))
          (expfield (Atom LABELS) (ListE))
          (expfield (Atom RETURN) (OptE))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "C'")
        (StrE
          (expfield
            (Atom TYPES)
            (IterE (VarE "ft'") List (iterexp "ft'" (VarE "ft'*")))
          )
          (expfield
            (Atom FUNCS)
            (CatE
              (IterE (VarE "ift") List (iterexp "ift" (VarE "ift*")))
              (IterE (VarE "ft") List (iterexp "ft" (VarE "ft*")))
            )
          )
          (expfield
            (Atom GLOBALS)
            (IterE (VarE "igt") List (iterexp "igt" (VarE "igt*")))
          )
          (expfield (Atom TABLES) (ListE))
          (expfield (Atom MEMS) (ListE))
          (expfield (Atom LOCALS) (ListE))
          (expfield (Atom LABELS) (ListE))
          (expfield (Atom RETURN) (OptE))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IterE (VarE "ift") List (iterexp "ift" (VarE "ift*")))
        (CallE
          "funcsxt"
          (ExpA (IterE (VarE "ixt") List (iterexp "ixt" (VarE "ixt*"))))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IterE (VarE "igt") List (iterexp "igt" (VarE "igt*")))
        (CallE
          "globalsxt"
          (ExpA (IterE (VarE "ixt") List (iterexp "ixt" (VarE "ixt*"))))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IterE (VarE "itt") List (iterexp "itt" (VarE "itt*")))
        (CallE
          "tablesxt"
          (ExpA (IterE (VarE "ixt") List (iterexp "ixt" (VarE "ixt*"))))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IterE (VarE "imt") List (iterexp "imt" (VarE "imt*")))
        (CallE
          "memsxt"
          (ExpA (IterE (VarE "ixt") List (iterexp "ixt" (VarE "ixt*"))))
        )
      )
    )
    (IterPr
      (RulePr "wf_externtype" (Seq Arg) (TupE (VarE "ixt")))
      List
      (iterexp "ixt" (VarE "ixt*"))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C'")))
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (IterPr
      (RulePr "wf_externtype" (Seq Arg) (TupE (VarE "xt")))
      List
      (iterexp "xt" (VarE "xt*"))
    )
    (IterPr
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "iter")))
      List
      (iterexp
        "iter"
        (CallE
          "tablesxt"
          (ExpA (IterE (VarE "ixt") List (iterexp "ixt" (VarE "ixt*"))))
        )
      )
    )
    (IterPr
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "iter")))
      List
      (iterexp
        "iter"
        (CallE
          "memsxt"
          (ExpA (IterE (VarE "ixt") List (iterexp "ixt" (VarE "ixt*"))))
        )
      )
    )
    (RulePr
      "wf_module"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
          (TupE
            (IterE (VarE "type") List (iterexp "type" (VarE "type*")))
            (IterE (VarE "import") List (iterexp "import" (VarE "import*")))
            (IterE (VarE "func") List (iterexp "func" (VarE "func*")))
            (IterE (VarE "global") List (iterexp "global" (VarE "global*")))
            (IterE (VarE "table") List (iterexp "table" (VarE "table*")))
            (IterE (VarE "mem") List (iterexp "mem" (VarE "mem*")))
            (IterE (VarE "elem") List (iterexp "elem" (VarE "elem*")))
            (IterE (VarE "data") List (iterexp "data" (VarE "data*")))
            (IterE (VarE "start") Opt (iterexp "start" (VarE "start?")))
            (IterE (VarE "export") List (iterexp "export" (VarE "export*")))
          )
        )
      )
    )
    (RulePr
      "wf_context"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPES)
            (IterE (VarE "ft'") List (iterexp "ft'" (VarE "ft'*")))
          )
          (expfield (Atom FUNCS) (ListE))
          (expfield (Atom GLOBALS) (ListE))
          (expfield (Atom TABLES) (ListE))
          (expfield (Atom MEMS) (ListE))
          (expfield (Atom LOCALS) (ListE))
          (expfield (Atom LABELS) (ListE))
          (expfield (Atom RETURN) (OptE))
        )
      )
    )
    (RulePr
      "wf_context"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPES)
            (IterE (VarE "ft'") List (iterexp "ft'" (VarE "ft'*")))
          )
          (expfield
            (Atom FUNCS)
            (CatE
              (IterE (VarE "ift") List (iterexp "ift" (VarE "ift*")))
              (IterE (VarE "ft") List (iterexp "ft" (VarE "ft*")))
            )
          )
          (expfield
            (Atom GLOBALS)
            (CatE
              (IterE (VarE "igt") List (iterexp "igt" (VarE "igt*")))
              (IterE (VarE "gt") List (iterexp "gt" (VarE "gt*")))
            )
          )
          (expfield
            (Atom TABLES)
            (CatE
              (IterE (VarE "itt") List (iterexp "itt" (VarE "itt*")))
              (IterE (VarE "tt") List (iterexp "tt" (VarE "tt*")))
            )
          )
          (expfield
            (Atom MEMS)
            (CatE
              (IterE (VarE "imt") List (iterexp "imt" (VarE "imt*")))
              (IterE (VarE "mt") List (iterexp "mt" (VarE "mt*")))
            )
          )
          (expfield (Atom LOCALS) (ListE))
          (expfield (Atom LABELS) (ListE))
          (expfield (Atom RETURN) (OptE))
        )
      )
    )
    (RulePr
      "wf_context"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPES)
            (IterE (VarE "ft'") List (iterexp "ft'" (VarE "ft'*")))
          )
          (expfield
            (Atom FUNCS)
            (CatE
              (IterE (VarE "ift") List (iterexp "ift" (VarE "ift*")))
              (IterE (VarE "ft") List (iterexp "ft" (VarE "ft*")))
            )
          )
          (expfield
            (Atom GLOBALS)
            (IterE (VarE "igt") List (iterexp "igt" (VarE "igt*")))
          )
          (expfield (Atom TABLES) (ListE))
          (expfield (Atom MEMS) (ListE))
          (expfield (Atom LOCALS) (ListE))
          (expfield (Atom LABELS) (ListE))
          (expfield (Atom RETURN) (OptE))
        )
      )
    )
  )
)
(HintD (RelH "Module_ok" (hint "show" "\"T-module\"")))
(RelD
  "Step_pure"
  (Infix Arg ~> Arg)
  (TupT
    (typbind "_" (IterT (VarT "admininstr") List))
    (typbind "_" (IterT (VarT "admininstr") List))
  )
  (RuleD
    "unreachable"
    (Infix Arg ~> Arg)
    (TupE
      (ListE (CaseE (Atom UNREACHABLE) (TupE)))
      (ListE (CaseE (Atom TRAP) (TupE)))
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom UNREACHABLE) (TupE))))
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
  )
  (RuleD
    "nop"
    (Infix Arg ~> Arg)
    (TupE (ListE (CaseE (Atom NOP) (TupE))) (ListE))
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom NOP) (TupE))))
  )
  (RuleD
    "drop"
    (ExpP "val" (VarT "val"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CallE "admininstr_val" (ExpA (VarE "val")))
        (CaseE (Atom DROP) (TupE))
      )
      (ListE)
    )
    (RulePr "wf_val" (Seq Arg) (TupE (VarE "val")))
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom DROP) (TupE))))
  )
  (RuleD
    "select-true"
    (ExpP "val_1" (VarT "val"))
    (ExpP "val_2" (VarT "val"))
    (ExpP "c" (VarT "val_"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CallE "admininstr_val" (ExpA (VarE "val_1")))
        (CallE "admininstr_val" (ExpA (VarE "val_2")))
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
        (CaseE (Atom SELECT) (TupE))
      )
      (ListE (CallE "admininstr_val" (ExpA (VarE "val_1"))))
    )
    (IfPr
      (CmpE
        NeOp
        bool
        (ProjE
          (CallE
            "proj_uN_0"
            (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "c")))))
          )
          0
        )
        (NumE (Nat 0))
      )
    )
    (RulePr "wf_val" (Seq Arg) (TupE (VarE "val_1")))
    (RulePr "wf_val" (Seq Arg) (TupE (VarE "val_2")))
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
      )
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom SELECT) (TupE))))
  )
  (RuleD
    "select-false"
    (ExpP "val_1" (VarT "val"))
    (ExpP "val_2" (VarT "val"))
    (ExpP "c" (VarT "val_"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CallE "admininstr_val" (ExpA (VarE "val_1")))
        (CallE "admininstr_val" (ExpA (VarE "val_2")))
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
        (CaseE (Atom SELECT) (TupE))
      )
      (ListE (CallE "admininstr_val" (ExpA (VarE "val_2"))))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (ProjE
          (CallE
            "proj_uN_0"
            (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "c")))))
          )
          0
        )
        (NumE (Nat 0))
      )
    )
    (RulePr "wf_val" (Seq Arg) (TupE (VarE "val_1")))
    (RulePr "wf_val" (Seq Arg) (TupE (VarE "val_2")))
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
      )
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom SELECT) (TupE))))
  )
  (RuleD
    "if-true"
    (ExpP "c" (VarT "val_"))
    (ExpP "t?" (IterT (VarT "valtype") Opt))
    (ExpP "instr_1*" (IterT (VarT "instr") List))
    (ExpP "instr_2*" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
        (CaseE
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupE
            (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
            (IterE (VarE "instr_1") List (iterexp "instr_1" (VarE "instr_1*")))
            (IterE (VarE "instr_2") List (iterexp "instr_2" (VarE "instr_2*")))
          )
        )
      )
      (ListE
        (CaseE
          (Seq (Atom BLOCK) Arg Arg)
          (TupE
            (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
            (IterE (VarE "instr_1") List (iterexp "instr_1" (VarE "instr_1*")))
          )
        )
      )
    )
    (IfPr
      (CmpE
        NeOp
        bool
        (ProjE
          (CallE
            "proj_uN_0"
            (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "c")))))
          )
          0
        )
        (NumE (Nat 0))
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupE
            (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
            (IterE (VarE "instr_1") List (iterexp "instr_1" (VarE "instr_1*")))
            (IterE (VarE "instr_2") List (iterexp "instr_2" (VarE "instr_2*")))
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BLOCK) Arg Arg)
          (TupE
            (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
            (IterE (VarE "instr_1") List (iterexp "instr_1" (VarE "instr_1*")))
          )
        )
      )
    )
  )
  (RuleD
    "if-false"
    (ExpP "c" (VarT "val_"))
    (ExpP "t?" (IterT (VarT "valtype") Opt))
    (ExpP "instr_1*" (IterT (VarT "instr") List))
    (ExpP "instr_2*" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
        (CaseE
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupE
            (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
            (IterE (VarE "instr_1") List (iterexp "instr_1" (VarE "instr_1*")))
            (IterE (VarE "instr_2") List (iterexp "instr_2" (VarE "instr_2*")))
          )
        )
      )
      (ListE
        (CaseE
          (Seq (Atom BLOCK) Arg Arg)
          (TupE
            (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
            (IterE (VarE "instr_2") List (iterexp "instr_2" (VarE "instr_2*")))
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (ProjE
          (CallE
            "proj_uN_0"
            (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "c")))))
          )
          0
        )
        (NumE (Nat 0))
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupE
            (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
            (IterE (VarE "instr_1") List (iterexp "instr_1" (VarE "instr_1*")))
            (IterE (VarE "instr_2") List (iterexp "instr_2" (VarE "instr_2*")))
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BLOCK) Arg Arg)
          (TupE
            (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
            (IterE (VarE "instr_2") List (iterexp "instr_2" (VarE "instr_2*")))
          )
        )
      )
    )
  )
  (RuleD
    "label-vals"
    (ExpP "n" (VarT "n"))
    (ExpP "instr*" (IterT (VarT "instr") List))
    (ExpP "val*" (IterT (VarT "val") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
            (IterE
              (CallE "admininstr_val" (ExpA (VarE "val")))
              List
              (iterexp "val" (VarE "val*"))
            )
          )
        )
      )
      (IterE
        (CallE "admininstr_val" (ExpA (VarE "val")))
        List
        (iterexp "val" (VarE "val*"))
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
            (IterE
              (CallE "admininstr_val" (ExpA (VarE "val")))
              List
              (iterexp "val" (VarE "val*"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "br-zero"
    (ExpP "n" (VarT "n"))
    (ExpP "instr'*" (IterT (VarT "instr") List))
    (ExpP "val'*" (IterT (VarT "val") List))
    (ExpP "val*" (IterT (VarT "val") List))
    (ExpP "instr*" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (IterE (VarE "instr'") List (iterexp "instr'" (VarE "instr'*")))
            (CatE
              (CatE
                (CatE
                  (IterE
                    (CallE "admininstr_val" (ExpA (VarE "val'")))
                    List
                    (iterexp "val'" (VarE "val'*"))
                  )
                  (IterE
                    (CallE "admininstr_val" (ExpA (VarE "val")))
                    (ListN (VarE "n"))
                    (iterexp "val" (VarE "val*"))
                  )
                )
                (ListE
                  (CaseE
                    (Seq (Atom BR) Arg)
                    (TupE (CaseE Arg (TupE (NumE (Nat 0)))))
                  )
                )
              )
              (IterE
                (CallE "admininstr_instr" (ExpA (VarE "instr")))
                List
                (iterexp "instr" (VarE "instr*"))
              )
            )
          )
        )
      )
      (CatE
        (IterE
          (CallE "admininstr_val" (ExpA (VarE "val")))
          (ListN (VarE "n"))
          (iterexp "val" (VarE "val*"))
        )
        (IterE
          (CallE "admininstr_instr" (ExpA (VarE "instr'")))
          List
          (iterexp "instr'" (VarE "instr'*"))
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (IterE (VarE "instr'") List (iterexp "instr'" (VarE "instr'*")))
            (CatE
              (CatE
                (CatE
                  (IterE
                    (CallE "admininstr_val" (ExpA (VarE "val'")))
                    List
                    (iterexp "val'" (VarE "val'*"))
                  )
                  (IterE
                    (CallE "admininstr_val" (ExpA (VarE "val")))
                    (ListN (VarE "n"))
                    (iterexp "val" (VarE "val*"))
                  )
                )
                (ListE
                  (CaseE
                    (Seq (Atom BR) Arg)
                    (TupE (CaseE Arg (TupE (NumE (Nat 0)))))
                  )
                )
              )
              (IterE
                (CallE "admininstr_instr" (ExpA (VarE "instr")))
                List
                (iterexp "instr" (VarE "instr*"))
              )
            )
          )
        )
      )
    )
    (IfPr (CmpE EqOp bool (VarE "n") (LenE (VarE "val*"))))
  )
  (RuleD
    "br-succ"
    (ExpP "n" (VarT "n"))
    (ExpP "instr'*" (IterT (VarT "instr") List))
    (ExpP "val*" (IterT (VarT "val") List))
    (ExpP "l" (VarT "labelidx"))
    (ExpP "instr*" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (IterE (VarE "instr'") List (iterexp "instr'" (VarE "instr'*")))
            (CatE
              (CatE
                (IterE
                  (CallE "admininstr_val" (ExpA (VarE "val")))
                  List
                  (iterexp "val" (VarE "val*"))
                )
                (ListE
                  (CaseE
                    (Seq (Atom BR) Arg)
                    (TupE
                      (CaseE
                        Arg
                        (TupE
                          (BinE
                            AddOp
                            nat
                            (ProjE (CallE "proj_uN_0" (ExpA (VarE "l"))) 0)
                            (NumE (Nat 1))
                          )
                        )
                      )
                    )
                  )
                )
              )
              (IterE
                (CallE "admininstr_instr" (ExpA (VarE "instr")))
                List
                (iterexp "instr" (VarE "instr*"))
              )
            )
          )
        )
      )
      (CatE
        (IterE
          (CallE "admininstr_val" (ExpA (VarE "val")))
          List
          (iterexp "val" (VarE "val*"))
        )
        (ListE (CaseE (Seq (Atom BR) Arg) (TupE (VarE "l"))))
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (IterE (VarE "instr'") List (iterexp "instr'" (VarE "instr'*")))
            (CatE
              (CatE
                (IterE
                  (CallE "admininstr_val" (ExpA (VarE "val")))
                  List
                  (iterexp "val" (VarE "val*"))
                )
                (ListE
                  (CaseE
                    (Seq (Atom BR) Arg)
                    (TupE
                      (CaseE
                        Arg
                        (TupE
                          (BinE
                            AddOp
                            nat
                            (ProjE (CallE "proj_uN_0" (ExpA (VarE "l"))) 0)
                            (NumE (Nat 1))
                          )
                        )
                      )
                    )
                  )
                )
              )
              (IterE
                (CallE "admininstr_instr" (ExpA (VarE "instr")))
                List
                (iterexp "instr" (VarE "instr*"))
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BR) Arg) (TupE (VarE "l"))))
    )
  )
  (RuleD
    "br_if-true"
    (ExpP "c" (VarT "val_"))
    (ExpP "l" (VarT "labelidx"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
        (CaseE (Seq (Atom BR_IF) Arg) (TupE (VarE "l")))
      )
      (ListE (CaseE (Seq (Atom BR) Arg) (TupE (VarE "l"))))
    )
    (IfPr
      (CmpE
        NeOp
        bool
        (ProjE
          (CallE
            "proj_uN_0"
            (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "c")))))
          )
          0
        )
        (NumE (Nat 0))
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BR_IF) Arg) (TupE (VarE "l"))))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BR) Arg) (TupE (VarE "l"))))
    )
  )
  (RuleD
    "br_if-false"
    (ExpP "c" (VarT "val_"))
    (ExpP "l" (VarT "labelidx"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
        (CaseE (Seq (Atom BR_IF) Arg) (TupE (VarE "l")))
      )
      (ListE)
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (ProjE
          (CallE
            "proj_uN_0"
            (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "c")))))
          )
          0
        )
        (NumE (Nat 0))
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BR_IF) Arg) (TupE (VarE "l"))))
    )
  )
  (RuleD
    "br_table-lt"
    (ExpP "i" (VarT "val_"))
    (ExpP "l*" (IterT (VarT "labelidx") List))
    (ExpP "l'" (VarT "labelidx"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
        )
        (CaseE
          (Seq (Atom BR_TABLE) Arg Arg)
          (TupE (IterE (VarE "l") List (iterexp "l" (VarE "l*"))) (VarE "l'"))
        )
      )
      (ListE
        (CaseE
          (Seq (Atom BR) Arg)
          (TupE
            (IdxE
              (IterE (VarE "l") List (iterexp "l" (VarE "l*")))
              (ProjE
                (CallE
                  "proj_uN_0"
                  (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
                )
                0
              )
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE
          (CallE
            "proj_uN_0"
            (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
          )
          0
        )
        (LenE (IterE (VarE "l") List (iterexp "l" (VarE "l*"))))
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BR_TABLE) Arg Arg)
          (TupE (IterE (VarE "l") List (iterexp "l" (VarE "l*"))) (VarE "l'"))
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BR) Arg)
          (TupE
            (IdxE
              (IterE (VarE "l") List (iterexp "l" (VarE "l*")))
              (ProjE
                (CallE
                  "proj_uN_0"
                  (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
                )
                0
              )
            )
          )
        )
      )
    )
  )
  (RuleD
    "br_table-ge"
    (ExpP "i" (VarT "val_"))
    (ExpP "l*" (IterT (VarT "labelidx") List))
    (ExpP "l'" (VarT "labelidx"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
        )
        (CaseE
          (Seq (Atom BR_TABLE) Arg Arg)
          (TupE (IterE (VarE "l") List (iterexp "l" (VarE "l*"))) (VarE "l'"))
        )
      )
      (ListE (CaseE (Seq (Atom BR) Arg) (TupE (VarE "l'"))))
    )
    (IfPr
      (CmpE
        GeOp
        nat
        (ProjE
          (CallE
            "proj_uN_0"
            (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
          )
          0
        )
        (LenE (IterE (VarE "l") List (iterexp "l" (VarE "l*"))))
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BR_TABLE) Arg Arg)
          (TupE (IterE (VarE "l") List (iterexp "l" (VarE "l*"))) (VarE "l'"))
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BR) Arg) (TupE (VarE "l'"))))
    )
  )
  (RuleD
    "frame-vals"
    (ExpP "n" (VarT "n"))
    (ExpP "f" (VarT "frame"))
    (ExpP "val*" (IterT (VarT "val") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (VarE "f")
            (IterE
              (CallE "admininstr_val" (ExpA (VarE "val")))
              (ListN (VarE "n"))
              (iterexp "val" (VarE "val*"))
            )
          )
        )
      )
      (IterE
        (CallE "admininstr_val" (ExpA (VarE "val")))
        (ListN (VarE "n"))
        (iterexp "val" (VarE "val*"))
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (VarE "f")
            (IterE
              (CallE "admininstr_val" (ExpA (VarE "val")))
              (ListN (VarE "n"))
              (iterexp "val" (VarE "val*"))
            )
          )
        )
      )
    )
    (IfPr (CmpE EqOp bool (VarE "n") (LenE (VarE "val*"))))
  )
  (RuleD
    "return-frame"
    (ExpP "n" (VarT "n"))
    (ExpP "f" (VarT "frame"))
    (ExpP "val'*" (IterT (VarT "val") List))
    (ExpP "val*" (IterT (VarT "val") List))
    (ExpP "instr*" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (VarE "f")
            (CatE
              (CatE
                (CatE
                  (IterE
                    (CallE "admininstr_val" (ExpA (VarE "val'")))
                    List
                    (iterexp "val'" (VarE "val'*"))
                  )
                  (IterE
                    (CallE "admininstr_val" (ExpA (VarE "val")))
                    (ListN (VarE "n"))
                    (iterexp "val" (VarE "val*"))
                  )
                )
                (ListE (CaseE (Atom RETURN) (TupE)))
              )
              (IterE
                (CallE "admininstr_instr" (ExpA (VarE "instr")))
                List
                (iterexp "instr" (VarE "instr*"))
              )
            )
          )
        )
      )
      (IterE
        (CallE "admininstr_val" (ExpA (VarE "val")))
        (ListN (VarE "n"))
        (iterexp "val" (VarE "val*"))
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (VarE "f")
            (CatE
              (CatE
                (CatE
                  (IterE
                    (CallE "admininstr_val" (ExpA (VarE "val'")))
                    List
                    (iterexp "val'" (VarE "val'*"))
                  )
                  (IterE
                    (CallE "admininstr_val" (ExpA (VarE "val")))
                    (ListN (VarE "n"))
                    (iterexp "val" (VarE "val*"))
                  )
                )
                (ListE (CaseE (Atom RETURN) (TupE)))
              )
              (IterE
                (CallE "admininstr_instr" (ExpA (VarE "instr")))
                List
                (iterexp "instr" (VarE "instr*"))
              )
            )
          )
        )
      )
    )
    (IfPr (CmpE EqOp bool (VarE "n") (LenE (VarE "val*"))))
  )
  (RuleD
    "return-label"
    (ExpP "n" (VarT "n"))
    (ExpP "instr'*" (IterT (VarT "instr") List))
    (ExpP "val*" (IterT (VarT "val") List))
    (ExpP "instr*" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (IterE (VarE "instr'") List (iterexp "instr'" (VarE "instr'*")))
            (CatE
              (CatE
                (IterE
                  (CallE "admininstr_val" (ExpA (VarE "val")))
                  List
                  (iterexp "val" (VarE "val*"))
                )
                (ListE (CaseE (Atom RETURN) (TupE)))
              )
              (IterE
                (CallE "admininstr_instr" (ExpA (VarE "instr")))
                List
                (iterexp "instr" (VarE "instr*"))
              )
            )
          )
        )
      )
      (CatE
        (IterE
          (CallE "admininstr_val" (ExpA (VarE "val")))
          List
          (iterexp "val" (VarE "val*"))
        )
        (ListE (CaseE (Atom RETURN) (TupE)))
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (IterE (VarE "instr'") List (iterexp "instr'" (VarE "instr'*")))
            (CatE
              (CatE
                (IterE
                  (CallE "admininstr_val" (ExpA (VarE "val")))
                  List
                  (iterexp "val" (VarE "val*"))
                )
                (ListE (CaseE (Atom RETURN) (TupE)))
              )
              (IterE
                (CallE "admininstr_instr" (ExpA (VarE "instr")))
                List
                (iterexp "instr" (VarE "instr*"))
              )
            )
          )
        )
      )
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom RETURN) (TupE))))
  )
  (RuleD
    "trap-vals"
    (ExpP "val*" (IterT (VarT "val") List))
    (ExpP "instr*" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (CatE
        (IterE
          (CallE "admininstr_val" (ExpA (VarE "val")))
          List
          (iterexp "val" (VarE "val*"))
        )
        (CatE
          (ListE (CaseE (Atom TRAP) (TupE)))
          (IterE
            (CallE "admininstr_instr" (ExpA (VarE "instr")))
            List
            (iterexp "instr" (VarE "instr*"))
          )
        )
      )
      (ListE (CaseE (Atom TRAP) (TupE)))
    )
    (IfPr
      (BinE
        OrOp
        bool
        (CmpE
          NeOp
          bool
          (IterE (VarE "val") List (iterexp "val" (VarE "val*")))
          (ListE)
        )
        (CmpE
          NeOp
          bool
          (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          (ListE)
        )
      )
    )
    (IterPr
      (RulePr "wf_val" (Seq Arg) (TupE (VarE "val")))
      List
      (iterexp "val" (VarE "val*"))
    )
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr")))
      List
      (iterexp "instr" (VarE "instr*"))
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
  )
  (RuleD
    "trap-label"
    (ExpP "n" (VarT "n"))
    (ExpP "instr'*" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (IterE (VarE "instr'") List (iterexp "instr'" (VarE "instr'*")))
            (ListE (CaseE (Atom TRAP) (TupE)))
          )
        )
      )
      (ListE (CaseE (Atom TRAP) (TupE)))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (IterE (VarE "instr'") List (iterexp "instr'" (VarE "instr'*")))
            (ListE (CaseE (Atom TRAP) (TupE)))
          )
        )
      )
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
  )
  (RuleD
    "trap-frame"
    (ExpP "n" (VarT "n"))
    (ExpP "f" (VarT "frame"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE (VarE "n") (VarE "f") (ListE (CaseE (Atom TRAP) (TupE))))
        )
      )
      (ListE (CaseE (Atom TRAP) (TupE)))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE (VarE "n") (VarE "f") (ListE (CaseE (Atom TRAP) (TupE))))
        )
      )
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
  )
  (RuleD
    "unop-val"
    (ExpP "t" (VarT "valtype"))
    (ExpP "c_1" (VarT "val_"))
    (ExpP "unop" (VarT "unop_"))
    (ExpP "c" (VarT "val_"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_1")))
        (CaseE (Seq (Atom UNOP) Arg Arg) (TupE (VarE "t") (VarE "unop")))
      )
      (ListE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c"))))
    )
    (IfPr
      (MemE
        (VarE "c")
        (TheE
          (CallE
            "unop_"
            (ExpA (VarE "t"))
            (ExpA (VarE "unop"))
            (ExpA (VarE "c_1"))
          )
        )
      )
    )
    (IterPr
      (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "t") (VarE "iter")))
      List
      (iterexp
        "iter"
        (TheE
          (CallE
            "unop_"
            (ExpA (VarE "t"))
            (ExpA (VarE "unop"))
            (ExpA (VarE "c_1"))
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_1"))))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom UNOP) Arg Arg) (TupE (VarE "t") (VarE "unop"))))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c"))))
    )
  )
  (RuleD
    "unop-trap"
    (ExpP "t" (VarT "valtype"))
    (ExpP "c_1" (VarT "val_"))
    (ExpP "unop" (VarT "unop_"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_1")))
        (CaseE (Seq (Atom UNOP) Arg Arg) (TupE (VarE "t") (VarE "unop")))
      )
      (ListE (CaseE (Atom TRAP) (TupE)))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (TheE
          (CallE
            "unop_"
            (ExpA (VarE "t"))
            (ExpA (VarE "unop"))
            (ExpA (VarE "c_1"))
          )
        )
        (ListE)
      )
    )
    (IterPr
      (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "t") (VarE "iter")))
      List
      (iterexp
        "iter"
        (TheE
          (CallE
            "unop_"
            (ExpA (VarE "t"))
            (ExpA (VarE "unop"))
            (ExpA (VarE "c_1"))
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_1"))))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom UNOP) Arg Arg) (TupE (VarE "t") (VarE "unop"))))
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
  )
  (RuleD
    "binop-val"
    (ExpP "t" (VarT "valtype"))
    (ExpP "c_1" (VarT "val_"))
    (ExpP "c_2" (VarT "val_"))
    (ExpP "binop" (VarT "binop_"))
    (ExpP "c" (VarT "val_"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_1")))
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_2")))
        (CaseE (Seq (Atom BINOP) Arg Arg) (TupE (VarE "t") (VarE "binop")))
      )
      (ListE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c"))))
    )
    (IfPr
      (MemE
        (VarE "c")
        (TheE
          (CallE
            "binop_"
            (ExpA (VarE "t"))
            (ExpA (VarE "binop"))
            (ExpA (VarE "c_1"))
            (ExpA (VarE "c_2"))
          )
        )
      )
    )
    (IterPr
      (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "t") (VarE "iter")))
      List
      (iterexp
        "iter"
        (TheE
          (CallE
            "binop_"
            (ExpA (VarE "t"))
            (ExpA (VarE "binop"))
            (ExpA (VarE "c_1"))
            (ExpA (VarE "c_2"))
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_1"))))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_2"))))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BINOP) Arg Arg) (TupE (VarE "t") (VarE "binop"))))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c"))))
    )
  )
  (RuleD
    "binop-trap"
    (ExpP "t" (VarT "valtype"))
    (ExpP "c_1" (VarT "val_"))
    (ExpP "c_2" (VarT "val_"))
    (ExpP "binop" (VarT "binop_"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_1")))
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_2")))
        (CaseE (Seq (Atom BINOP) Arg Arg) (TupE (VarE "t") (VarE "binop")))
      )
      (ListE (CaseE (Atom TRAP) (TupE)))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (TheE
          (CallE
            "binop_"
            (ExpA (VarE "t"))
            (ExpA (VarE "binop"))
            (ExpA (VarE "c_1"))
            (ExpA (VarE "c_2"))
          )
        )
        (ListE)
      )
    )
    (IterPr
      (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "t") (VarE "iter")))
      List
      (iterexp
        "iter"
        (TheE
          (CallE
            "binop_"
            (ExpA (VarE "t"))
            (ExpA (VarE "binop"))
            (ExpA (VarE "c_1"))
            (ExpA (VarE "c_2"))
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_1"))))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_2"))))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BINOP) Arg Arg) (TupE (VarE "t") (VarE "binop"))))
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
  )
  (RuleD
    "testop"
    (ExpP "t" (VarT "valtype"))
    (ExpP "c_1" (VarT "val_"))
    (ExpP "testop" (VarT "testop_"))
    (ExpP "c" (VarT "val_"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_1")))
        (CaseE (Seq (Atom TESTOP) Arg Arg) (TupE (VarE "t") (VarE "testop")))
      )
      (ListE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "c")
        (TheE
          (CallE
            "testop_"
            (ExpA (VarE "t"))
            (ExpA (VarE "testop"))
            (ExpA (VarE "c_1"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (TheE
          (CallE
            "testop_"
            (ExpA (VarE "t"))
            (ExpA (VarE "testop"))
            (ExpA (VarE "c_1"))
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_1"))))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE (Seq (Atom TESTOP) Arg Arg) (TupE (VarE "t") (VarE "testop")))
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
      )
    )
  )
  (RuleD
    "relop"
    (ExpP "t" (VarT "valtype"))
    (ExpP "c_1" (VarT "val_"))
    (ExpP "c_2" (VarT "val_"))
    (ExpP "relop" (VarT "relop_"))
    (ExpP "c" (VarT "val_"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_1")))
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_2")))
        (CaseE (Seq (Atom RELOP) Arg Arg) (TupE (VarE "t") (VarE "relop")))
      )
      (ListE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "c")
        (TheE
          (CallE
            "relop_"
            (ExpA (VarE "t"))
            (ExpA (VarE "relop"))
            (ExpA (VarE "c_1"))
            (ExpA (VarE "c_2"))
          )
        )
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (TheE
          (CallE
            "relop_"
            (ExpA (VarE "t"))
            (ExpA (VarE "relop"))
            (ExpA (VarE "c_1"))
            (ExpA (VarE "c_2"))
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_1"))))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_2"))))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom RELOP) Arg Arg) (TupE (VarE "t") (VarE "relop"))))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
      )
    )
  )
  (RuleD
    "cvtop-val"
    (ExpP "t_1" (VarT "valtype"))
    (ExpP "c_1" (VarT "val_"))
    (ExpP "t_2" (VarT "valtype"))
    (ExpP "cvtop" (VarT "cvtop"))
    (ExpP "c" (VarT "val_"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t_1") (VarE "c_1")))
        (CaseE
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupE (VarE "t_2") (VarE "t_1") (VarE "cvtop"))
        )
      )
      (ListE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t_2") (VarE "c"))))
    )
    (IfPr
      (MemE
        (VarE "c")
        (TheE
          (CallE
            "cvtop__"
            (ExpA (VarE "t_1"))
            (ExpA (VarE "t_2"))
            (ExpA (VarE "cvtop"))
            (ExpA (VarE "c_1"))
          )
        )
      )
    )
    (IterPr
      (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "t_2") (VarE "iter")))
      List
      (iterexp
        "iter"
        (TheE
          (CallE
            "cvtop__"
            (ExpA (VarE "t_1"))
            (ExpA (VarE "t_2"))
            (ExpA (VarE "cvtop"))
            (ExpA (VarE "c_1"))
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t_1") (VarE "c_1"))))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupE (VarE "t_2") (VarE "t_1") (VarE "cvtop"))
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t_2") (VarE "c"))))
    )
  )
  (RuleD
    "cvtop-trap"
    (ExpP "t_1" (VarT "valtype"))
    (ExpP "c_1" (VarT "val_"))
    (ExpP "t_2" (VarT "valtype"))
    (ExpP "cvtop" (VarT "cvtop"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t_1") (VarE "c_1")))
        (CaseE
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupE (VarE "t_2") (VarE "t_1") (VarE "cvtop"))
        )
      )
      (ListE (CaseE (Atom TRAP) (TupE)))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (TheE
          (CallE
            "cvtop__"
            (ExpA (VarE "t_1"))
            (ExpA (VarE "t_2"))
            (ExpA (VarE "cvtop"))
            (ExpA (VarE "c_1"))
          )
        )
        (ListE)
      )
    )
    (IterPr
      (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "t_2") (VarE "iter")))
      List
      (iterexp
        "iter"
        (TheE
          (CallE
            "cvtop__"
            (ExpA (VarE "t_1"))
            (ExpA (VarE "t_2"))
            (ExpA (VarE "cvtop"))
            (ExpA (VarE "c_1"))
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t_1") (VarE "c_1"))))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupE (VarE "t_2") (VarE "t_1") (VarE "cvtop"))
        )
      )
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
  )
  (RuleD
    "local.tee"
    (ExpP "val" (VarT "val"))
    (ExpP "x" (VarT "idx"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CallE "admininstr_val" (ExpA (VarE "val")))
        (CaseE (Seq (Atom LOCAL.TEE) Arg) (TupE (VarE "x")))
      )
      (ListE
        (CallE "admininstr_val" (ExpA (VarE "val")))
        (CallE "admininstr_val" (ExpA (VarE "val")))
        (CaseE (Seq (Atom LOCAL.SET) Arg) (TupE (VarE "x")))
      )
    )
    (RulePr "wf_val" (Seq Arg) (TupE (VarE "val")))
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL.TEE) Arg) (TupE (VarE "x"))))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL.SET) Arg) (TupE (VarE "x"))))
    )
  )
)
(RelD
  "Step_read_before_call_indirect-trap"
  Arg
  (VarT "config")
  (RuleD
    "call_indirect-call_0"
    (ExpP "z" (VarT "state"))
    (ExpP "i" (VarT "val_"))
    (ExpP "x" (VarT "idx"))
    (ExpP "a" (VarT "addr"))
    Arg
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (VarE "z")
        (ListE
          (CaseE
            (Seq (Atom CONST) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
          )
          (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "x")))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE
          (DotE
            (CallE
              "table"
              (ExpA (VarE "z"))
              (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
            )
            (Atom REFS)
          )
          (ProjE
            (CallE
              "proj_uN_0"
              (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
            )
            0
          )
        )
        (OptE (VarE "a"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE "type" (ExpA (VarE "z")) (ExpA (VarE "x")))
        (DotE
          (IdxE (CallE "funcinst" (ExpA (VarE "z"))) (VarE "a"))
          (Atom TYPE)
        )
      )
    )
    (RulePr
      "wf_tableinst"
      (Seq Arg)
      (TupE
        (CallE
          "table"
          (ExpA (VarE "z"))
          (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
        )
      )
    )
    (IterPr
      (RulePr "wf_funcinst" (Seq Arg) (TupE (VarE "iter")))
      List
      (iterexp "iter" (CallE "funcinst" (ExpA (VarE "z"))))
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
              )
              (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "x")))
            )
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CALL_ADDR) Arg) (TupE (VarE "a"))))
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE (NumE (Nat 32)) (CaseE Arg (TupE (NumE (Nat 0)))))
    )
  )
)
(HintD
  (RelH
    "Step_read_before_call_indirect-trap"
    (hint "else-relation" "\"Step_read\"")
  )
)
(RelD
  "Step_read"
  (Infix Arg ~> Arg)
  (TupT
    (typbind "_" (VarT "config"))
    (typbind "_" (IterT (VarT "admininstr") List))
  )
  (RuleD
    "block"
    (ExpP "z" (VarT "state"))
    (ExpP "t?" (IterT (VarT "valtype") Opt))
    (ExpP "instr*" (IterT (VarT "instr") List))
    (ExpP "n" (VarT "n"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (ListE
            (CaseE
              (Seq (Atom BLOCK) Arg Arg)
              (TupE
                (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
                (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
              )
            )
          )
        )
      )
      (ListE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (ListE)
            (IterE
              (CallE "admininstr_instr" (ExpA (VarE "instr")))
              List
              (iterexp "instr" (VarE "instr*"))
            )
          )
        )
      )
    )
    (IfPr
      (BinE
        OrOp
        bool
        (BinE
          AndOp
          bool
          (CmpE
            EqOp
            bool
            (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
            (OptE)
          )
          (CmpE EqOp bool (VarE "n") (NumE (Nat 0)))
        )
        (BinE
          AndOp
          bool
          (CmpE
            NeOp
            bool
            (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
            (OptE)
          )
          (CmpE EqOp bool (VarE "n") (NumE (Nat 1)))
        )
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom BLOCK) Arg Arg)
                (TupE
                  (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
                  (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
                )
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (ListE)
            (IterE
              (CallE "admininstr_instr" (ExpA (VarE "instr")))
              List
              (iterexp "instr" (VarE "instr*"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "loop"
    (ExpP "z" (VarT "state"))
    (ExpP "t?" (IterT (VarT "valtype") Opt))
    (ExpP "instr*" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (ListE
            (CaseE
              (Seq (Atom LOOP) Arg Arg)
              (TupE
                (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
                (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
              )
            )
          )
        )
      )
      (ListE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (NumE (Nat 0))
            (ListE
              (CaseE
                (Seq (Atom LOOP) Arg Arg)
                (TupE
                  (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
                  (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
                )
              )
            )
            (IterE
              (CallE "admininstr_instr" (ExpA (VarE "instr")))
              List
              (iterexp "instr" (VarE "instr*"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom LOOP) Arg Arg)
                (TupE
                  (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
                  (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
                )
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (NumE (Nat 0))
            (ListE
              (CaseE
                (Seq (Atom LOOP) Arg Arg)
                (TupE
                  (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
                  (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
                )
              )
            )
            (IterE
              (CallE "admininstr_instr" (ExpA (VarE "instr")))
              List
              (iterexp "instr" (VarE "instr*"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "call"
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "idx"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (ListE (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "x"))))
        )
      )
      (ListE
        (CaseE
          (Seq (Atom CALL_ADDR) Arg)
          (TupE
            (IdxE
              (CallE "funcaddr" (ExpA (VarE "z")))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
            )
          )
        )
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "x"))))
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CALL_ADDR) Arg)
          (TupE
            (IdxE
              (CallE "funcaddr" (ExpA (VarE "z")))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
            )
          )
        )
      )
    )
  )
  (RuleD
    "call_indirect-call"
    (ExpP "z" (VarT "state"))
    (ExpP "i" (VarT "val_"))
    (ExpP "x" (VarT "idx"))
    (ExpP "a" (VarT "addr"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (ListE
            (CaseE
              (Seq (Atom CONST) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
            )
            (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "x")))
          )
        )
      )
      (ListE (CaseE (Seq (Atom CALL_ADDR) Arg) (TupE (VarE "a"))))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE
          (DotE
            (CallE
              "table"
              (ExpA (VarE "z"))
              (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
            )
            (Atom REFS)
          )
          (ProjE
            (CallE
              "proj_uN_0"
              (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
            )
            0
          )
        )
        (OptE (VarE "a"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE "type" (ExpA (VarE "z")) (ExpA (VarE "x")))
        (DotE
          (IdxE (CallE "funcinst" (ExpA (VarE "z"))) (VarE "a"))
          (Atom TYPE)
        )
      )
    )
    (RulePr
      "wf_tableinst"
      (Seq Arg)
      (TupE
        (CallE
          "table"
          (ExpA (VarE "z"))
          (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
        )
      )
    )
    (IterPr
      (RulePr "wf_funcinst" (Seq Arg) (TupE (VarE "iter")))
      List
      (iterexp "iter" (CallE "funcinst" (ExpA (VarE "z"))))
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
              )
              (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "x")))
            )
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CALL_ADDR) Arg) (TupE (VarE "a"))))
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE (NumE (Nat 32)) (CaseE Arg (TupE (NumE (Nat 0)))))
    )
  )
  (RuleD
    "call_indirect-trap"
    (ExpP "z" (VarT "state"))
    (ExpP "i" (VarT "val_"))
    (ExpP "x" (VarT "idx"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (ListE
            (CaseE
              (Seq (Atom CONST) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
            )
            (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "x")))
          )
        )
      )
      (ListE (CaseE (Atom TRAP) (TupE)))
    )
    (NegPr
      (RulePr
        "Step_read_before_call_indirect-trap"
        Arg
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
              )
              (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "x")))
            )
          )
        )
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
              )
              (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "x")))
            )
          )
        )
      )
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
  )
  (RuleD
    "call_addr"
    (ExpP "z" (VarT "state"))
    (ExpP "k" nat)
    (ExpP "val*" (IterT (VarT "val") List))
    (ExpP "a" (VarT "addr"))
    (ExpP "n" (VarT "n"))
    (ExpP "f" (VarT "frame"))
    (ExpP "instr*" (IterT (VarT "instr") List))
    (ExpP "t_1*" (IterT (VarT "valtype") List))
    (ExpP "t_2*" (IterT (VarT "valtype") List))
    (ExpP "mm" (VarT "moduleinst"))
    (ExpP "func" (VarT "func"))
    (ExpP "x" (VarT "idx"))
    (ExpP "t*" (IterT (VarT "valtype") List))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (CatE
            (IterE
              (CallE "admininstr_val" (ExpA (VarE "val")))
              (ListN (VarE "k"))
              (iterexp "val" (VarE "val*"))
            )
            (ListE (CaseE (Seq (Atom CALL_ADDR) Arg) (TupE (VarE "a"))))
          )
        )
      )
      (ListE
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (VarE "f")
            (ListE
              (CaseE
                (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
                (TupE
                  (VarE "n")
                  (ListE)
                  (IterE
                    (CallE "admininstr_instr" (ExpA (VarE "instr")))
                    List
                    (iterexp "instr" (VarE "instr*"))
                  )
                )
              )
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE (CallE "funcinst" (ExpA (VarE "z"))) (VarE "a"))
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Infix Arg -> Arg)
              (TupE
                (IterE
                  (VarE "t_1")
                  (ListN (VarE "k"))
                  (iterexp "t_1" (VarE "t_1*"))
                )
                (IterE
                  (VarE "t_2")
                  (ListN (VarE "n"))
                  (iterexp "t_2" (VarE "t_2*"))
                )
              )
            )
          )
          (expfield (Atom MODULE) (VarE "mm"))
          (expfield (Atom CODE) (VarE "func"))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "func")
        (CaseE
          (Seq (Atom FUNC) Arg Arg Arg)
          (TupE
            (VarE "x")
            (IterE
              (CaseE (Seq (Atom LOCAL) Arg) (TupE (VarE "t")))
              List
              (iterexp "t" (VarE "t*"))
            )
            (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "f")
        (StrE
          (expfield
            (Atom LOCALS)
            (CatE
              (IterE
                (VarE "val")
                (ListN (VarE "k"))
                (iterexp "val" (VarE "val*"))
              )
              (IterE
                (CallE "default_" (ExpA (VarE "t")))
                List
                (iterexp "t" (VarE "t*"))
              )
            )
          )
          (expfield (Atom MODULE) (VarE "mm"))
        )
      )
    )
    (IterPr
      (RulePr "wf_funcinst" (Seq Arg) (TupE (VarE "iter")))
      List
      (iterexp "iter" (CallE "funcinst" (ExpA (VarE "z"))))
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (CatE
              (IterE
                (CallE "admininstr_val" (ExpA (VarE "val")))
                (ListN (VarE "k"))
                (iterexp "val" (VarE "val*"))
              )
              (ListE (CaseE (Seq (Atom CALL_ADDR) Arg) (TupE (VarE "a"))))
            )
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (VarE "f")
            (ListE
              (CaseE
                (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
                (TupE
                  (VarE "n")
                  (ListE)
                  (IterE
                    (CallE "admininstr_instr" (ExpA (VarE "instr")))
                    List
                    (iterexp "instr" (VarE "instr*"))
                  )
                )
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_funcinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Infix Arg -> Arg)
              (TupE
                (IterE
                  (VarE "t_1")
                  (ListN (VarE "k"))
                  (iterexp "t_1" (VarE "t_1*"))
                )
                (IterE
                  (VarE "t_2")
                  (ListN (VarE "n"))
                  (iterexp "t_2" (VarE "t_2*"))
                )
              )
            )
          )
          (expfield (Atom MODULE) (VarE "mm"))
          (expfield (Atom CODE) (VarE "func"))
        )
      )
    )
    (RulePr
      "wf_func"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom FUNC) Arg Arg Arg)
          (TupE
            (VarE "x")
            (IterE
              (CaseE (Seq (Atom LOCAL) Arg) (TupE (VarE "t")))
              List
              (iterexp "t" (VarE "t*"))
            )
            (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          )
        )
      )
    )
    (RulePr
      "wf_frame"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom LOCALS)
            (CatE
              (IterE
                (VarE "val")
                (ListN (VarE "k"))
                (iterexp "val" (VarE "val*"))
              )
              (IterE
                (CallE "default_" (ExpA (VarE "t")))
                List
                (iterexp "t" (VarE "t*"))
              )
            )
          )
          (expfield (Atom MODULE) (VarE "mm"))
        )
      )
    )
    (IfPr (CmpE EqOp bool (VarE "k") (LenE (VarE "val*"))))
    (IfPr (CmpE EqOp bool (VarE "k") (LenE (VarE "t_1*"))))
    (IfPr (CmpE EqOp bool (VarE "n") (LenE (VarE "t_2*"))))
  )
  (RuleD
    "local.get"
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "idx"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (ListE (CaseE (Seq (Atom LOCAL.GET) Arg) (TupE (VarE "x"))))
        )
      )
      (ListE
        (CallE
          "admininstr_val"
          (ExpA (CallE "local" (ExpA (VarE "z")) (ExpA (VarE "x"))))
        )
      )
    )
    (RulePr
      "wf_val"
      (Seq Arg)
      (TupE (CallE "local" (ExpA (VarE "z")) (ExpA (VarE "x"))))
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE (CaseE (Seq (Atom LOCAL.GET) Arg) (TupE (VarE "x"))))
          )
        )
      )
    )
  )
  (RuleD
    "global.get"
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "idx"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (ListE (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "x"))))
        )
      )
      (ListE
        (CallE
          "admininstr_val"
          (ExpA
            (DotE
              (CallE "global" (ExpA (VarE "z")) (ExpA (VarE "x")))
              (Atom VALUE)
            )
          )
        )
      )
    )
    (RulePr
      "wf_globalinst"
      (Seq Arg)
      (TupE (CallE "global" (ExpA (VarE "z")) (ExpA (VarE "x"))))
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "x"))))
          )
        )
      )
    )
  )
  (RuleD
    "load-num-trap"
    (ExpP "z" (VarT "state"))
    (ExpP "i" (VarT "val_"))
    (ExpP "t" (VarT "valtype"))
    (ExpP "ao" (VarT "memarg"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (ListE
            (CaseE
              (Seq (Atom CONST) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
            )
            (CaseE
              (Seq (Atom LOAD) Arg Arg Arg)
              (TupE (VarE "t") (OptE) (VarE "ao"))
            )
          )
        )
      )
      (ListE (CaseE (Atom TRAP) (TupE)))
    )
    (IfPr
      (CmpE
        GtOp
        nat
        (BinE
          AddOp
          nat
          (BinE
            AddOp
            nat
            (ProjE
              (CallE
                "proj_uN_0"
                (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
              )
              0
            )
            (ProjE
              (CallE "proj_uN_0" (ExpA (DotE (VarE "ao") (Atom OFFSET))))
              0
            )
          )
          (CvtE
            rat
            nat
            (BinE
              DivOp
              rat
              (CvtE nat rat (CallE "size" (ExpA (VarE "t"))))
              (CvtE nat rat (NumE (Nat 8)))
            )
          )
        )
        (LenE
          (DotE
            (CallE
              "mem"
              (ExpA (VarE "z"))
              (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
            )
            (Atom BYTES)
          )
        )
      )
    )
    (RulePr
      "wf_meminst"
      (Seq Arg)
      (TupE
        (CallE "mem" (ExpA (VarE "z")) (ExpA (CaseE Arg (TupE (NumE (Nat 0))))))
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
              )
              (CaseE
                (Seq (Atom LOAD) Arg Arg Arg)
                (TupE (VarE "t") (OptE) (VarE "ao"))
              )
            )
          )
        )
      )
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE (NumE (Nat 32)) (CaseE Arg (TupE (NumE (Nat 0)))))
    )
  )
  (RuleD
    "load-num-val"
    (ExpP "z" (VarT "state"))
    (ExpP "i" (VarT "val_"))
    (ExpP "t" (VarT "valtype"))
    (ExpP "ao" (VarT "memarg"))
    (ExpP "c" (VarT "val_"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (ListE
            (CaseE
              (Seq (Atom CONST) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
            )
            (CaseE
              (Seq (Atom LOAD) Arg Arg Arg)
              (TupE (VarE "t") (OptE) (VarE "ao"))
            )
          )
        )
      )
      (ListE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c"))))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE "bytes_" (ExpA (VarE "t")) (ExpA (VarE "c")))
        (SliceE
          (DotE
            (CallE
              "mem"
              (ExpA (VarE "z"))
              (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
            )
            (Atom BYTES)
          )
          (BinE
            AddOp
            nat
            (ProjE
              (CallE
                "proj_uN_0"
                (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
              )
              0
            )
            (ProjE
              (CallE "proj_uN_0" (ExpA (DotE (VarE "ao") (Atom OFFSET))))
              0
            )
          )
          (CvtE
            rat
            nat
            (BinE
              DivOp
              rat
              (CvtE nat rat (CallE "size" (ExpA (VarE "t"))))
              (CvtE nat rat (NumE (Nat 8)))
            )
          )
        )
      )
    )
    (IterPr
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "iter")))
      List
      (iterexp "iter" (CallE "bytes_" (ExpA (VarE "t")) (ExpA (VarE "c"))))
    )
    (RulePr
      "wf_meminst"
      (Seq Arg)
      (TupE
        (CallE "mem" (ExpA (VarE "z")) (ExpA (CaseE Arg (TupE (NumE (Nat 0))))))
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
              )
              (CaseE
                (Seq (Atom LOAD) Arg Arg Arg)
                (TupE (VarE "t") (OptE) (VarE "ao"))
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c"))))
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE (NumE (Nat 32)) (CaseE Arg (TupE (NumE (Nat 0)))))
    )
  )
  (RuleD
    "load-pack-trap"
    (ExpP "z" (VarT "state"))
    (ExpP "i" (VarT "val_"))
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "n" (VarT "n"))
    (ExpP "sx" (VarT "sx"))
    (ExpP "ao" (VarT "memarg"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (ListE
            (CaseE
              (Seq (Atom CONST) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
            )
            (CaseE
              (Seq (Atom LOAD) Arg Arg Arg)
              (TupE
                (CallE "valtype_Inn" (ExpA (VarE "Inn")))
                (OptE
                  (CaseE
                    (Seq (Atom mk_loadop__0) Arg Arg)
                    (TupE
                      (VarE "Inn")
                      (CaseE
                        (Seq Arg (Atom _) Arg)
                        (TupE (CaseE Arg (TupE (VarE "n"))) (VarE "sx"))
                      )
                    )
                  )
                )
                (VarE "ao")
              )
            )
          )
        )
      )
      (ListE (CaseE (Atom TRAP) (TupE)))
    )
    (IfPr
      (CmpE
        GtOp
        nat
        (BinE
          AddOp
          nat
          (BinE
            AddOp
            nat
            (ProjE
              (CallE
                "proj_uN_0"
                (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
              )
              0
            )
            (ProjE
              (CallE "proj_uN_0" (ExpA (DotE (VarE "ao") (Atom OFFSET))))
              0
            )
          )
          (CvtE
            rat
            nat
            (BinE
              DivOp
              rat
              (CvtE nat rat (VarE "n"))
              (CvtE nat rat (NumE (Nat 8)))
            )
          )
        )
        (LenE
          (DotE
            (CallE
              "mem"
              (ExpA (VarE "z"))
              (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
            )
            (Atom BYTES)
          )
        )
      )
    )
    (RulePr
      "wf_meminst"
      (Seq Arg)
      (TupE
        (CallE "mem" (ExpA (VarE "z")) (ExpA (CaseE Arg (TupE (NumE (Nat 0))))))
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
              )
              (CaseE
                (Seq (Atom LOAD) Arg Arg Arg)
                (TupE
                  (CallE "valtype_Inn" (ExpA (VarE "Inn")))
                  (OptE
                    (CaseE
                      (Seq (Atom mk_loadop__0) Arg Arg)
                      (TupE
                        (VarE "Inn")
                        (CaseE
                          (Seq Arg (Atom _) Arg)
                          (TupE (CaseE Arg (TupE (VarE "n"))) (VarE "sx"))
                        )
                      )
                    )
                  )
                  (VarE "ao")
                )
              )
            )
          )
        )
      )
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE (NumE (Nat 32)) (CaseE Arg (TupE (NumE (Nat 0)))))
    )
  )
  (RuleD
    "load-pack-val"
    (ExpP "z" (VarT "state"))
    (ExpP "i" (VarT "val_"))
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "n" (VarT "n"))
    (ExpP "sx" (VarT "sx"))
    (ExpP "ao" (VarT "memarg"))
    (ExpP "c" (VarT "iN"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (ListE
            (CaseE
              (Seq (Atom CONST) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
            )
            (CaseE
              (Seq (Atom LOAD) Arg Arg Arg)
              (TupE
                (CallE "valtype_Inn" (ExpA (VarE "Inn")))
                (OptE
                  (CaseE
                    (Seq (Atom mk_loadop__0) Arg Arg)
                    (TupE
                      (VarE "Inn")
                      (CaseE
                        (Seq Arg (Atom _) Arg)
                        (TupE (CaseE Arg (TupE (VarE "n"))) (VarE "sx"))
                      )
                    )
                  )
                )
                (VarE "ao")
              )
            )
          )
        )
      )
      (ListE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE
            (CallE "valtype_Inn" (ExpA (VarE "Inn")))
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE
                (VarE "Inn")
                (CallE
                  "extend__"
                  (ExpA (VarE "n"))
                  (ExpA
                    (CallE
                      "size"
                      (ExpA (CallE "valtype_Inn" (ExpA (VarE "Inn"))))
                    )
                  )
                  (ExpA (VarE "sx"))
                  (ExpA (VarE "c"))
                )
              )
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE "ibytes_" (ExpA (VarE "n")) (ExpA (VarE "c")))
        (SliceE
          (DotE
            (CallE
              "mem"
              (ExpA (VarE "z"))
              (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
            )
            (Atom BYTES)
          )
          (BinE
            AddOp
            nat
            (ProjE
              (CallE
                "proj_uN_0"
                (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
              )
              0
            )
            (ProjE
              (CallE "proj_uN_0" (ExpA (DotE (VarE "ao") (Atom OFFSET))))
              0
            )
          )
          (CvtE
            rat
            nat
            (BinE
              DivOp
              rat
              (CvtE nat rat (VarE "n"))
              (CvtE nat rat (NumE (Nat 8)))
            )
          )
        )
      )
    )
    (IterPr
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "iter")))
      List
      (iterexp "iter" (CallE "ibytes_" (ExpA (VarE "n")) (ExpA (VarE "c"))))
    )
    (RulePr
      "wf_meminst"
      (Seq Arg)
      (TupE
        (CallE "mem" (ExpA (VarE "z")) (ExpA (CaseE Arg (TupE (NumE (Nat 0))))))
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
              )
              (CaseE
                (Seq (Atom LOAD) Arg Arg Arg)
                (TupE
                  (CallE "valtype_Inn" (ExpA (VarE "Inn")))
                  (OptE
                    (CaseE
                      (Seq (Atom mk_loadop__0) Arg Arg)
                      (TupE
                        (VarE "Inn")
                        (CaseE
                          (Seq Arg (Atom _) Arg)
                          (TupE (CaseE Arg (TupE (VarE "n"))) (VarE "sx"))
                        )
                      )
                    )
                  )
                  (VarE "ao")
                )
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE
            (CallE "valtype_Inn" (ExpA (VarE "Inn")))
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE
                (VarE "Inn")
                (CallE
                  "extend__"
                  (ExpA (VarE "n"))
                  (ExpA
                    (CallE
                      "size"
                      (ExpA (CallE "valtype_Inn" (ExpA (VarE "Inn"))))
                    )
                  )
                  (ExpA (VarE "sx"))
                  (ExpA (VarE "c"))
                )
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE (NumE (Nat 32)) (CaseE Arg (TupE (NumE (Nat 0)))))
    )
  )
  (RuleD
    "memory.size"
    (ExpP "z" (VarT "state"))
    (ExpP "n" (VarT "n"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE (VarE "z") (ListE (CaseE (Atom MEMORY.SIZE) (TupE))))
      )
      (ListE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (CaseE Arg (TupE (VarE "n"))))
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (BinE
          MulOp
          nat
          (BinE MulOp nat (VarE "n") (NumE (Nat 64)))
          (CallE "Ki")
        )
        (LenE
          (DotE
            (CallE
              "mem"
              (ExpA (VarE "z"))
              (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
            )
            (Atom BYTES)
          )
        )
      )
    )
    (RulePr
      "wf_meminst"
      (Seq Arg)
      (TupE
        (CallE "mem" (ExpA (VarE "z")) (ExpA (CaseE Arg (TupE (NumE (Nat 0))))))
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE (VarE "z") (ListE (CaseE (Atom MEMORY.SIZE) (TupE))))
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (CaseE Arg (TupE (VarE "n"))))
            )
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE (NumE (Nat 32)) (CaseE Arg (TupE (NumE (Nat 0)))))
    )
  )
)
(RecD
  (RelD
    "Step"
    (Infix Arg ~> Arg)
    (TupT (typbind "_" (VarT "config")) (typbind "_" (VarT "config")))
    (RuleD
      "pure"
      (ExpP "z" (VarT "state"))
      (ExpP "admininstr*" (IterT (VarT "admininstr") List))
      (ExpP "admininstr'*" (IterT (VarT "admininstr") List))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (IterE
              (VarE "admininstr")
              List
              (iterexp "admininstr" (VarE "admininstr*"))
            )
          )
        )
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (IterE
              (VarE "admininstr'")
              List
              (iterexp "admininstr'" (VarE "admininstr'*"))
            )
          )
        )
      )
      (RulePr
        "Step_pure"
        (Infix Arg ~> Arg)
        (TupE
          (IterE
            (VarE "admininstr")
            List
            (iterexp "admininstr" (VarE "admininstr*"))
          )
          (IterE
            (VarE "admininstr'")
            List
            (iterexp "admininstr'" (VarE "admininstr'*"))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (IterE
                (VarE "admininstr")
                List
                (iterexp "admininstr" (VarE "admininstr*"))
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (IterE
                (VarE "admininstr'")
                List
                (iterexp "admininstr'" (VarE "admininstr'*"))
              )
            )
          )
        )
      )
    )
    (RuleD
      "read"
      (ExpP "z" (VarT "state"))
      (ExpP "admininstr*" (IterT (VarT "admininstr") List))
      (ExpP "admininstr'*" (IterT (VarT "admininstr") List))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (IterE
              (VarE "admininstr")
              List
              (iterexp "admininstr" (VarE "admininstr*"))
            )
          )
        )
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (IterE
              (VarE "admininstr'")
              List
              (iterexp "admininstr'" (VarE "admininstr'*"))
            )
          )
        )
      )
      (RulePr
        "Step_read"
        (Infix Arg ~> Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (IterE
                (VarE "admininstr")
                List
                (iterexp "admininstr" (VarE "admininstr*"))
              )
            )
          )
          (IterE
            (VarE "admininstr'")
            List
            (iterexp "admininstr'" (VarE "admininstr'*"))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (IterE
                (VarE "admininstr")
                List
                (iterexp "admininstr" (VarE "admininstr*"))
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (IterE
                (VarE "admininstr'")
                List
                (iterexp "admininstr'" (VarE "admininstr'*"))
              )
            )
          )
        )
      )
    )
    (RuleD
      "ctxt-label"
      (ExpP "z" (VarT "state"))
      (ExpP "n" (VarT "n"))
      (ExpP "instr_0*" (IterT (VarT "instr") List))
      (ExpP "admininstr*" (IterT (VarT "admininstr") List))
      (ExpP "z'" (VarT "state"))
      (ExpP "admininstr'*" (IterT (VarT "admininstr") List))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
                (TupE
                  (VarE "n")
                  (IterE
                    (VarE "instr_0")
                    List
                    (iterexp "instr_0" (VarE "instr_0*"))
                  )
                  (IterE
                    (VarE "admininstr")
                    List
                    (iterexp "admininstr" (VarE "admininstr*"))
                  )
                )
              )
            )
          )
        )
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z'")
            (ListE
              (CaseE
                (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
                (TupE
                  (VarE "n")
                  (IterE
                    (VarE "instr_0")
                    List
                    (iterexp "instr_0" (VarE "instr_0*"))
                  )
                  (IterE
                    (VarE "admininstr'")
                    List
                    (iterexp "admininstr'" (VarE "admininstr'*"))
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "Step"
        (Infix Arg ~> Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (IterE
                (VarE "admininstr")
                List
                (iterexp "admininstr" (VarE "admininstr*"))
              )
            )
          )
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z'")
              (IterE
                (VarE "admininstr'")
                List
                (iterexp "admininstr'" (VarE "admininstr'*"))
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (ListE
                (CaseE
                  (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
                  (TupE
                    (VarE "n")
                    (IterE
                      (VarE "instr_0")
                      List
                      (iterexp "instr_0" (VarE "instr_0*"))
                    )
                    (IterE
                      (VarE "admininstr")
                      List
                      (iterexp "admininstr" (VarE "admininstr*"))
                    )
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z'")
              (ListE
                (CaseE
                  (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
                  (TupE
                    (VarE "n")
                    (IterE
                      (VarE "instr_0")
                      List
                      (iterexp "instr_0" (VarE "instr_0*"))
                    )
                    (IterE
                      (VarE "admininstr'")
                      List
                      (iterexp "admininstr'" (VarE "admininstr'*"))
                    )
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (IterE
                (VarE "admininstr")
                List
                (iterexp "admininstr" (VarE "admininstr*"))
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z'")
              (IterE
                (VarE "admininstr'")
                List
                (iterexp "admininstr'" (VarE "admininstr'*"))
              )
            )
          )
        )
      )
    )
    (RuleD
      "ctxt-frame"
      (ExpP "s" (VarT "store"))
      (ExpP "f" (VarT "frame"))
      (ExpP "n" (VarT "n"))
      (ExpP "f'" (VarT "frame"))
      (ExpP "admininstr*" (IterT (VarT "admininstr") List))
      (ExpP "s'" (VarT "store"))
      (ExpP "f''" (VarT "frame"))
      (ExpP "admininstr'*" (IterT (VarT "admininstr") List))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f")))
            (ListE
              (CaseE
                (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
                (TupE
                  (VarE "n")
                  (VarE "f'")
                  (IterE
                    (VarE "admininstr")
                    List
                    (iterexp "admininstr" (VarE "admininstr*"))
                  )
                )
              )
            )
          )
        )
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (CaseE (Infix Arg ; Arg) (TupE (VarE "s'") (VarE "f")))
            (ListE
              (CaseE
                (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
                (TupE
                  (VarE "n")
                  (VarE "f''")
                  (IterE
                    (VarE "admininstr'")
                    List
                    (iterexp "admininstr'" (VarE "admininstr'*"))
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "Step"
        (Infix Arg ~> Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f'")))
              (IterE
                (VarE "admininstr")
                List
                (iterexp "admininstr" (VarE "admininstr*"))
              )
            )
          )
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (CaseE (Infix Arg ; Arg) (TupE (VarE "s'") (VarE "f''")))
              (IterE
                (VarE "admininstr'")
                List
                (iterexp "admininstr'" (VarE "admininstr'*"))
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f")))
              (ListE
                (CaseE
                  (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
                  (TupE
                    (VarE "n")
                    (VarE "f'")
                    (IterE
                      (VarE "admininstr")
                      List
                      (iterexp "admininstr" (VarE "admininstr*"))
                    )
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (CaseE (Infix Arg ; Arg) (TupE (VarE "s'") (VarE "f")))
              (ListE
                (CaseE
                  (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
                  (TupE
                    (VarE "n")
                    (VarE "f''")
                    (IterE
                      (VarE "admininstr'")
                      List
                      (iterexp "admininstr'" (VarE "admininstr'*"))
                    )
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f'")))
              (IterE
                (VarE "admininstr")
                List
                (iterexp "admininstr" (VarE "admininstr*"))
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (CaseE (Infix Arg ; Arg) (TupE (VarE "s'") (VarE "f''")))
              (IterE
                (VarE "admininstr'")
                List
                (iterexp "admininstr'" (VarE "admininstr'*"))
              )
            )
          )
        )
      )
    )
    (RuleD
      "ctxt-instrs"
      (ExpP "z" (VarT "state"))
      (ExpP "val*" (IterT (VarT "val") List))
      (ExpP "admininstr*" (IterT (VarT "admininstr") List))
      (ExpP "admininstr_1*" (IterT (VarT "admininstr") List))
      (ExpP "z'" (VarT "state"))
      (ExpP "admininstr'*" (IterT (VarT "admininstr") List))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (CatE
              (IterE
                (CallE "admininstr_val" (ExpA (VarE "val")))
                List
                (iterexp "val" (VarE "val*"))
              )
              (CatE
                (IterE
                  (VarE "admininstr")
                  List
                  (iterexp "admininstr" (VarE "admininstr*"))
                )
                (IterE
                  (VarE "admininstr_1")
                  List
                  (iterexp "admininstr_1" (VarE "admininstr_1*"))
                )
              )
            )
          )
        )
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z'")
            (CatE
              (IterE
                (CallE "admininstr_val" (ExpA (VarE "val")))
                List
                (iterexp "val" (VarE "val*"))
              )
              (CatE
                (IterE
                  (VarE "admininstr'")
                  List
                  (iterexp "admininstr'" (VarE "admininstr'*"))
                )
                (IterE
                  (VarE "admininstr_1")
                  List
                  (iterexp "admininstr_1" (VarE "admininstr_1*"))
                )
              )
            )
          )
        )
      )
      (RulePr
        "Step"
        (Infix Arg ~> Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (IterE
                (VarE "admininstr")
                List
                (iterexp "admininstr" (VarE "admininstr*"))
              )
            )
          )
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z'")
              (IterE
                (VarE "admininstr'")
                List
                (iterexp "admininstr'" (VarE "admininstr'*"))
              )
            )
          )
        )
      )
      (IfPr
        (BinE
          OrOp
          bool
          (CmpE
            NeOp
            bool
            (IterE (VarE "val") List (iterexp "val" (VarE "val*")))
            (ListE)
          )
          (CmpE
            NeOp
            bool
            (IterE
              (VarE "admininstr_1")
              List
              (iterexp "admininstr_1" (VarE "admininstr_1*"))
            )
            (ListE)
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (CatE
                (IterE
                  (CallE "admininstr_val" (ExpA (VarE "val")))
                  List
                  (iterexp "val" (VarE "val*"))
                )
                (CatE
                  (IterE
                    (VarE "admininstr")
                    List
                    (iterexp "admininstr" (VarE "admininstr*"))
                  )
                  (IterE
                    (VarE "admininstr_1")
                    List
                    (iterexp "admininstr_1" (VarE "admininstr_1*"))
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z'")
              (CatE
                (IterE
                  (CallE "admininstr_val" (ExpA (VarE "val")))
                  List
                  (iterexp "val" (VarE "val*"))
                )
                (CatE
                  (IterE
                    (VarE "admininstr'")
                    List
                    (iterexp "admininstr'" (VarE "admininstr'*"))
                  )
                  (IterE
                    (VarE "admininstr_1")
                    List
                    (iterexp "admininstr_1" (VarE "admininstr_1*"))
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (IterE
                (VarE "admininstr")
                List
                (iterexp "admininstr" (VarE "admininstr*"))
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z'")
              (IterE
                (VarE "admininstr'")
                List
                (iterexp "admininstr'" (VarE "admininstr'*"))
              )
            )
          )
        )
      )
    )
    (RuleD
      "local.set"
      (ExpP "z" (VarT "state"))
      (ExpP "val" (VarT "val"))
      (ExpP "x" (VarT "idx"))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CallE "admininstr_val" (ExpA (VarE "val")))
              (CaseE (Seq (Atom LOCAL.SET) Arg) (TupE (VarE "x")))
            )
          )
        )
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (CallE
              "with_local"
              (ExpA (VarE "z"))
              (ExpA (VarE "x"))
              (ExpA (VarE "val"))
            )
            (ListE)
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (ListE
                (CallE "admininstr_val" (ExpA (VarE "val")))
                (CaseE (Seq (Atom LOCAL.SET) Arg) (TupE (VarE "x")))
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (CallE
                "with_local"
                (ExpA (VarE "z"))
                (ExpA (VarE "x"))
                (ExpA (VarE "val"))
              )
              (ListE)
            )
          )
        )
      )
    )
    (RuleD
      "global.set"
      (ExpP "z" (VarT "state"))
      (ExpP "val" (VarT "val"))
      (ExpP "x" (VarT "idx"))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CallE "admininstr_val" (ExpA (VarE "val")))
              (CaseE (Seq (Atom GLOBAL.SET) Arg) (TupE (VarE "x")))
            )
          )
        )
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (CallE
              "with_global"
              (ExpA (VarE "z"))
              (ExpA (VarE "x"))
              (ExpA (VarE "val"))
            )
            (ListE)
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (ListE
                (CallE "admininstr_val" (ExpA (VarE "val")))
                (CaseE (Seq (Atom GLOBAL.SET) Arg) (TupE (VarE "x")))
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (CallE
                "with_global"
                (ExpA (VarE "z"))
                (ExpA (VarE "x"))
                (ExpA (VarE "val"))
              )
              (ListE)
            )
          )
        )
      )
    )
    (RuleD
      "store-num-trap"
      (ExpP "z" (VarT "state"))
      (ExpP "i" (VarT "val_"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "c" (VarT "val_"))
      (ExpP "ao" (VarT "memarg"))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
              )
              (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c")))
              (CaseE
                (Seq (Atom STORE) Arg Arg Arg)
                (TupE (VarE "t") (OptE) (VarE "ao"))
              )
            )
          )
        )
        (CaseE
          (Infix Arg ; Arg)
          (TupE (VarE "z") (ListE (CaseE (Atom TRAP) (TupE))))
        )
      )
      (IfPr
        (CmpE
          GtOp
          nat
          (BinE
            AddOp
            nat
            (BinE
              AddOp
              nat
              (ProjE
                (CallE
                  "proj_uN_0"
                  (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
                )
                0
              )
              (ProjE
                (CallE "proj_uN_0" (ExpA (DotE (VarE "ao") (Atom OFFSET))))
                0
              )
            )
            (CvtE
              rat
              nat
              (BinE
                DivOp
                rat
                (CvtE nat rat (CallE "size" (ExpA (VarE "t"))))
                (CvtE nat rat (NumE (Nat 8)))
              )
            )
          )
          (LenE
            (DotE
              (CallE
                "mem"
                (ExpA (VarE "z"))
                (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
              )
              (Atom BYTES)
            )
          )
        )
      )
      (RulePr
        "wf_meminst"
        (Seq Arg)
        (TupE
          (CallE
            "mem"
            (ExpA (VarE "z"))
            (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (ListE
                (CaseE
                  (Seq (Atom CONST) Arg Arg)
                  (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
                )
                (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c")))
                (CaseE
                  (Seq (Atom STORE) Arg Arg Arg)
                  (TupE (VarE "t") (OptE) (VarE "ao"))
                )
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE (VarE "z") (ListE (CaseE (Atom TRAP) (TupE))))
          )
        )
      )
      (RulePr
        "wf_uN"
        (Seq Arg Arg)
        (TupE (NumE (Nat 32)) (CaseE Arg (TupE (NumE (Nat 0)))))
      )
    )
    (RuleD
      "store-num-val"
      (ExpP "z" (VarT "state"))
      (ExpP "i" (VarT "val_"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "c" (VarT "val_"))
      (ExpP "ao" (VarT "memarg"))
      (ExpP "b*" (IterT (VarT "byte") List))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
              )
              (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c")))
              (CaseE
                (Seq (Atom STORE) Arg Arg Arg)
                (TupE (VarE "t") (OptE) (VarE "ao"))
              )
            )
          )
        )
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (CallE
              "with_mem"
              (ExpA (VarE "z"))
              (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
              (ExpA
                (BinE
                  AddOp
                  nat
                  (ProjE
                    (CallE
                      "proj_uN_0"
                      (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
                    )
                    0
                  )
                  (ProjE
                    (CallE "proj_uN_0" (ExpA (DotE (VarE "ao") (Atom OFFSET))))
                    0
                  )
                )
              )
              (ExpA
                (CvtE
                  rat
                  nat
                  (BinE
                    DivOp
                    rat
                    (CvtE nat rat (CallE "size" (ExpA (VarE "t"))))
                    (CvtE nat rat (NumE (Nat 8)))
                  )
                )
              )
              (ExpA (IterE (VarE "b") List (iterexp "b" (VarE "b*"))))
            )
            (ListE)
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IterE (VarE "b") List (iterexp "b" (VarE "b*")))
          (CallE "bytes_" (ExpA (VarE "t")) (ExpA (VarE "c")))
        )
      )
      (IterPr
        (RulePr "wf_byte" (Seq Arg) (TupE (VarE "iter")))
        List
        (iterexp "iter" (CallE "bytes_" (ExpA (VarE "t")) (ExpA (VarE "c"))))
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (ListE
                (CaseE
                  (Seq (Atom CONST) Arg Arg)
                  (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
                )
                (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c")))
                (CaseE
                  (Seq (Atom STORE) Arg Arg Arg)
                  (TupE (VarE "t") (OptE) (VarE "ao"))
                )
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (CallE
                "with_mem"
                (ExpA (VarE "z"))
                (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
                (ExpA
                  (BinE
                    AddOp
                    nat
                    (ProjE
                      (CallE
                        "proj_uN_0"
                        (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
                      )
                      0
                    )
                    (ProjE
                      (CallE
                        "proj_uN_0"
                        (ExpA (DotE (VarE "ao") (Atom OFFSET)))
                      )
                      0
                    )
                  )
                )
                (ExpA
                  (CvtE
                    rat
                    nat
                    (BinE
                      DivOp
                      rat
                      (CvtE nat rat (CallE "size" (ExpA (VarE "t"))))
                      (CvtE nat rat (NumE (Nat 8)))
                    )
                  )
                )
                (ExpA (IterE (VarE "b") List (iterexp "b" (VarE "b*"))))
              )
              (ListE)
            )
          )
        )
      )
    )
    (RuleD
      "store-pack-trap"
      (ExpP "z" (VarT "state"))
      (ExpP "i" (VarT "val_"))
      (ExpP "Inn" (VarT "Inn"))
      (ExpP "c" (VarT "val_"))
      (ExpP "n" (VarT "n"))
      (ExpP "ao" (VarT "memarg"))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
              )
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CallE "valtype_Inn" (ExpA (VarE "Inn"))) (VarE "c"))
              )
              (CaseE
                (Seq (Atom STORE) Arg Arg Arg)
                (TupE
                  (CallE "valtype_Inn" (ExpA (VarE "Inn")))
                  (OptE (CaseE Arg (TupE (VarE "n"))))
                  (VarE "ao")
                )
              )
            )
          )
        )
        (CaseE
          (Infix Arg ; Arg)
          (TupE (VarE "z") (ListE (CaseE (Atom TRAP) (TupE))))
        )
      )
      (IfPr
        (CmpE
          GtOp
          nat
          (BinE
            AddOp
            nat
            (BinE
              AddOp
              nat
              (ProjE
                (CallE
                  "proj_uN_0"
                  (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
                )
                0
              )
              (ProjE
                (CallE "proj_uN_0" (ExpA (DotE (VarE "ao") (Atom OFFSET))))
                0
              )
            )
            (CvtE
              rat
              nat
              (BinE
                DivOp
                rat
                (CvtE nat rat (VarE "n"))
                (CvtE nat rat (NumE (Nat 8)))
              )
            )
          )
          (LenE
            (DotE
              (CallE
                "mem"
                (ExpA (VarE "z"))
                (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
              )
              (Atom BYTES)
            )
          )
        )
      )
      (RulePr
        "wf_meminst"
        (Seq Arg)
        (TupE
          (CallE
            "mem"
            (ExpA (VarE "z"))
            (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (ListE
                (CaseE
                  (Seq (Atom CONST) Arg Arg)
                  (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
                )
                (CaseE
                  (Seq (Atom CONST) Arg Arg)
                  (TupE (CallE "valtype_Inn" (ExpA (VarE "Inn"))) (VarE "c"))
                )
                (CaseE
                  (Seq (Atom STORE) Arg Arg Arg)
                  (TupE
                    (CallE "valtype_Inn" (ExpA (VarE "Inn")))
                    (OptE (CaseE Arg (TupE (VarE "n"))))
                    (VarE "ao")
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE (VarE "z") (ListE (CaseE (Atom TRAP) (TupE))))
          )
        )
      )
      (RulePr
        "wf_uN"
        (Seq Arg Arg)
        (TupE (NumE (Nat 32)) (CaseE Arg (TupE (NumE (Nat 0)))))
      )
    )
    (RuleD
      "store-pack-val"
      (ExpP "z" (VarT "state"))
      (ExpP "i" (VarT "val_"))
      (ExpP "Inn" (VarT "Inn"))
      (ExpP "c" (VarT "val_"))
      (ExpP "n" (VarT "n"))
      (ExpP "ao" (VarT "memarg"))
      (ExpP "b*" (IterT (VarT "byte") List))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
              )
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CallE "valtype_Inn" (ExpA (VarE "Inn"))) (VarE "c"))
              )
              (CaseE
                (Seq (Atom STORE) Arg Arg Arg)
                (TupE
                  (CallE "valtype_Inn" (ExpA (VarE "Inn")))
                  (OptE (CaseE Arg (TupE (VarE "n"))))
                  (VarE "ao")
                )
              )
            )
          )
        )
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (CallE
              "with_mem"
              (ExpA (VarE "z"))
              (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
              (ExpA
                (BinE
                  AddOp
                  nat
                  (ProjE
                    (CallE
                      "proj_uN_0"
                      (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
                    )
                    0
                  )
                  (ProjE
                    (CallE "proj_uN_0" (ExpA (DotE (VarE "ao") (Atom OFFSET))))
                    0
                  )
                )
              )
              (ExpA
                (CvtE
                  rat
                  nat
                  (BinE
                    DivOp
                    rat
                    (CvtE nat rat (VarE "n"))
                    (CvtE nat rat (NumE (Nat 8)))
                  )
                )
              )
              (ExpA (IterE (VarE "b") List (iterexp "b" (VarE "b*"))))
            )
            (ListE)
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IterE (VarE "b") List (iterexp "b" (VarE "b*")))
          (CallE
            "ibytes_"
            (ExpA (VarE "n"))
            (ExpA
              (CallE
                "wrap__"
                (ExpA
                  (CallE
                    "size"
                    (ExpA (CallE "valtype_Inn" (ExpA (VarE "Inn"))))
                  )
                )
                (ExpA (VarE "n"))
                (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "c")))))
              )
            )
          )
        )
      )
      (IterPr
        (RulePr "wf_byte" (Seq Arg) (TupE (VarE "iter")))
        List
        (iterexp
          "iter"
          (CallE
            "ibytes_"
            (ExpA (VarE "n"))
            (ExpA
              (CallE
                "wrap__"
                (ExpA
                  (CallE
                    "size"
                    (ExpA (CallE "valtype_Inn" (ExpA (VarE "Inn"))))
                  )
                )
                (ExpA (VarE "n"))
                (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "c")))))
              )
            )
          )
        )
      )
      (RulePr
        "wf_uN"
        (Seq Arg Arg)
        (TupE
          (VarE "n")
          (CallE
            "wrap__"
            (ExpA
              (CallE "size" (ExpA (CallE "valtype_Inn" (ExpA (VarE "Inn")))))
            )
            (ExpA (VarE "n"))
            (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "c")))))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (ListE
                (CaseE
                  (Seq (Atom CONST) Arg Arg)
                  (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
                )
                (CaseE
                  (Seq (Atom CONST) Arg Arg)
                  (TupE (CallE "valtype_Inn" (ExpA (VarE "Inn"))) (VarE "c"))
                )
                (CaseE
                  (Seq (Atom STORE) Arg Arg Arg)
                  (TupE
                    (CallE "valtype_Inn" (ExpA (VarE "Inn")))
                    (OptE (CaseE Arg (TupE (VarE "n"))))
                    (VarE "ao")
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (CallE
                "with_mem"
                (ExpA (VarE "z"))
                (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
                (ExpA
                  (BinE
                    AddOp
                    nat
                    (ProjE
                      (CallE
                        "proj_uN_0"
                        (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
                      )
                      0
                    )
                    (ProjE
                      (CallE
                        "proj_uN_0"
                        (ExpA (DotE (VarE "ao") (Atom OFFSET)))
                      )
                      0
                    )
                  )
                )
                (ExpA
                  (CvtE
                    rat
                    nat
                    (BinE
                      DivOp
                      rat
                      (CvtE nat rat (VarE "n"))
                      (CvtE nat rat (NumE (Nat 8)))
                    )
                  )
                )
                (ExpA (IterE (VarE "b") List (iterexp "b" (VarE "b*"))))
              )
              (ListE)
            )
          )
        )
      )
    )
    (RuleD
      "memory.grow-succeed"
      (ExpP "z" (VarT "state"))
      (ExpP "n" (VarT "n"))
      (ExpP "mi" (VarT "meminst"))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE
                  (CaseE (Atom I32) (TupE))
                  (CaseE
                    (Seq (Atom mk_val__0) Arg Arg)
                    (TupE
                      (CaseE (Atom I32) (TupE))
                      (CaseE Arg (TupE (VarE "n")))
                    )
                  )
                )
              )
              (CaseE (Atom MEMORY.GROW) (TupE))
            )
          )
        )
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (CallE
              "with_meminst"
              (ExpA (VarE "z"))
              (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
              (ExpA (VarE "mi"))
            )
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE
                  (CaseE (Atom I32) (TupE))
                  (CaseE
                    (Seq (Atom mk_val__0) Arg Arg)
                    (TupE
                      (CaseE (Atom I32) (TupE))
                      (CaseE
                        Arg
                        (TupE
                          (CvtE
                            rat
                            nat
                            (BinE
                              DivOp
                              rat
                              (CvtE
                                nat
                                rat
                                (LenE
                                  (DotE
                                    (CallE
                                      "mem"
                                      (ExpA (VarE "z"))
                                      (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
                                    )
                                    (Atom BYTES)
                                  )
                                )
                              )
                              (CvtE
                                nat
                                rat
                                (BinE MulOp nat (NumE (Nat 64)) (CallE "Ki"))
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (TheE
            (CallE
              "growmemory"
              (ExpA
                (CallE
                  "mem"
                  (ExpA (VarE "z"))
                  (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
                )
              )
              (ExpA (VarE "n"))
            )
          )
          (VarE "mi")
        )
      )
      (RulePr
        "wf_meminst"
        (Seq Arg)
        (TupE
          (TheE
            (CallE
              "growmemory"
              (ExpA
                (CallE
                  "mem"
                  (ExpA (VarE "z"))
                  (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
                )
              )
              (ExpA (VarE "n"))
            )
          )
        )
      )
      (RulePr
        "wf_meminst"
        (Seq Arg)
        (TupE
          (CallE
            "mem"
            (ExpA (VarE "z"))
            (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (ListE
                (CaseE
                  (Seq (Atom CONST) Arg Arg)
                  (TupE
                    (CaseE (Atom I32) (TupE))
                    (CaseE
                      (Seq (Atom mk_val__0) Arg Arg)
                      (TupE
                        (CaseE (Atom I32) (TupE))
                        (CaseE Arg (TupE (VarE "n")))
                      )
                    )
                  )
                )
                (CaseE (Atom MEMORY.GROW) (TupE))
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (CallE
                "with_meminst"
                (ExpA (VarE "z"))
                (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
                (ExpA (VarE "mi"))
              )
              (ListE
                (CaseE
                  (Seq (Atom CONST) Arg Arg)
                  (TupE
                    (CaseE (Atom I32) (TupE))
                    (CaseE
                      (Seq (Atom mk_val__0) Arg Arg)
                      (TupE
                        (CaseE (Atom I32) (TupE))
                        (CaseE
                          Arg
                          (TupE
                            (CvtE
                              rat
                              nat
                              (BinE
                                DivOp
                                rat
                                (CvtE
                                  nat
                                  rat
                                  (LenE
                                    (DotE
                                      (CallE
                                        "mem"
                                        (ExpA (VarE "z"))
                                        (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
                                      )
                                      (Atom BYTES)
                                    )
                                  )
                                )
                                (CvtE
                                  nat
                                  rat
                                  (BinE MulOp nat (NumE (Nat 64)) (CallE "Ki"))
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "wf_uN"
        (Seq Arg Arg)
        (TupE (NumE (Nat 32)) (CaseE Arg (TupE (NumE (Nat 0)))))
      )
    )
    (RuleD
      "memory.grow-fail"
      (ExpP "z" (VarT "state"))
      (ExpP "n" (VarT "n"))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE
                  (CaseE (Atom I32) (TupE))
                  (CaseE
                    (Seq (Atom mk_val__0) Arg Arg)
                    (TupE
                      (CaseE (Atom I32) (TupE))
                      (CaseE Arg (TupE (VarE "n")))
                    )
                  )
                )
              )
              (CaseE (Atom MEMORY.GROW) (TupE))
            )
          )
        )
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE
                  (CaseE (Atom I32) (TupE))
                  (CaseE
                    (Seq (Atom mk_val__0) Arg Arg)
                    (TupE
                      (CaseE (Atom I32) (TupE))
                      (CaseE
                        Arg
                        (TupE
                          (CallE
                            "inv_signed_"
                            (ExpA (NumE (Nat 32)))
                            (ExpA
                              (UnE MinusOp int (CvtE nat int (NumE (Nat 1))))
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (ListE
                (CaseE
                  (Seq (Atom CONST) Arg Arg)
                  (TupE
                    (CaseE (Atom I32) (TupE))
                    (CaseE
                      (Seq (Atom mk_val__0) Arg Arg)
                      (TupE
                        (CaseE (Atom I32) (TupE))
                        (CaseE Arg (TupE (VarE "n")))
                      )
                    )
                  )
                )
                (CaseE (Atom MEMORY.GROW) (TupE))
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (ListE
                (CaseE
                  (Seq (Atom CONST) Arg Arg)
                  (TupE
                    (CaseE (Atom I32) (TupE))
                    (CaseE
                      (Seq (Atom mk_val__0) Arg Arg)
                      (TupE
                        (CaseE (Atom I32) (TupE))
                        (CaseE
                          Arg
                          (TupE
                            (CallE
                              "inv_signed_"
                              (ExpA (NumE (Nat 32)))
                              (ExpA
                                (UnE MinusOp int (CvtE nat int (NumE (Nat 1))))
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)
(HintD (RelH "Step" (hint "show" "\"E\"") (hint "tabular" "{}")))
(HintD (RelH "Step_pure" (hint "show" "\"E\"") (hint "tabular" "{}")))
(HintD (RelH "Step_read" (hint "show" "\"E\"") (hint "tabular" "{}")))
(RecD
  (RelD
    "Steps"
    (Infix Arg ~>* Arg)
    (TupT (typbind "_" (VarT "config")) (typbind "_" (VarT "config")))
    (RuleD
      "refl"
      (ExpP "z" (VarT "state"))
      (ExpP "admininstr*" (IterT (VarT "admininstr") List))
      (Infix Arg ~>* Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (IterE
              (VarE "admininstr")
              List
              (iterexp "admininstr" (VarE "admininstr*"))
            )
          )
        )
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (IterE
              (VarE "admininstr")
              List
              (iterexp "admininstr" (VarE "admininstr*"))
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (IterE
                (VarE "admininstr")
                List
                (iterexp "admininstr" (VarE "admininstr*"))
              )
            )
          )
        )
      )
    )
    (RuleD
      "trans"
      (ExpP "z" (VarT "state"))
      (ExpP "admininstr*" (IterT (VarT "admininstr") List))
      (ExpP "z''" (VarT "state"))
      (ExpP "admininstr''*" (IterT (VarT "admininstr") List))
      (ExpP "z'" (VarT "state"))
      (ExpP "admininstr'*" (IterT (VarT "admininstr") List))
      (Infix Arg ~>* Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (IterE
              (VarE "admininstr")
              List
              (iterexp "admininstr" (VarE "admininstr*"))
            )
          )
        )
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z''")
            (IterE
              (VarE "admininstr''")
              List
              (iterexp "admininstr''" (VarE "admininstr''*"))
            )
          )
        )
      )
      (RulePr
        "Step"
        (Infix Arg ~> Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (IterE
                (VarE "admininstr")
                List
                (iterexp "admininstr" (VarE "admininstr*"))
              )
            )
          )
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z'")
              (IterE
                (VarE "admininstr'")
                List
                (iterexp "admininstr'" (VarE "admininstr'*"))
              )
            )
          )
        )
      )
      (RulePr
        "Steps"
        (Infix Arg ~>* Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z'")
              (IterE
                (VarE "admininstr'")
                List
                (iterexp "admininstr'" (VarE "admininstr'*"))
              )
            )
          )
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z''")
              (IterE
                (VarE "admininstr''")
                List
                (iterexp "admininstr''" (VarE "admininstr''*"))
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z")
              (IterE
                (VarE "admininstr")
                List
                (iterexp "admininstr" (VarE "admininstr*"))
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z''")
              (IterE
                (VarE "admininstr''")
                List
                (iterexp "admininstr''" (VarE "admininstr''*"))
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Infix Arg ; Arg)
            (TupE
              (VarE "z'")
              (IterE
                (VarE "admininstr'")
                List
                (iterexp "admininstr'" (VarE "admininstr'*"))
              )
            )
          )
        )
      )
    )
  )
)
(HintD (RelH "Steps" (hint "show" "\"E\"") (hint "tabular" "{}")))
(RelD
  "Eval_expr"
  (Infix (Infix Arg ; Arg) ~>* (Infix Arg ; Arg))
  (TupT
    (typbind "_" (VarT "state"))
    (typbind "_" (VarT "expr"))
    (typbind "_" (VarT "state"))
    (typbind "_" (IterT (VarT "val") List))
  )
  (RuleD
    ""
    (ExpP "z" (VarT "state"))
    (ExpP "instr*" (IterT (VarT "instr") List))
    (ExpP "z'" (VarT "state"))
    (ExpP "val*" (IterT (VarT "val") List))
    (Infix (Infix Arg ; Arg) ~>* (Infix Arg ; Arg))
    (TupE
      (VarE "z")
      (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
      (VarE "z'")
      (IterE (VarE "val") List (iterexp "val" (VarE "val*")))
    )
    (RulePr
      "Steps"
      (Infix Arg ~>* Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (IterE
              (CallE "admininstr_instr" (ExpA (VarE "instr")))
              List
              (iterexp "instr" (VarE "instr*"))
            )
          )
        )
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z'")
            (IterE
              (CallE "admininstr_val" (ExpA (VarE "val")))
              List
              (iterexp "val" (VarE "val*"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z")
            (IterE
              (CallE "admininstr_instr" (ExpA (VarE "instr")))
              List
              (iterexp "instr" (VarE "instr*"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (VarE "z'")
            (IterE
              (CallE "admininstr_val" (ExpA (VarE "val")))
              List
              (iterexp "val" (VarE "val*"))
            )
          )
        )
      )
    )
  )
)
(HintD (RelH "Eval_expr" (hint "show" "\"E-expr\"") (hint "tabular" "{}")))
(RecD
  (DecD
    "funcs"
    (ExpP "_" (IterT (VarT "externaddr") List))
    (IterT (VarT "funcaddr") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "fa" nat)
      (ExpP "externaddr'*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "fa"))))
          (IterE
            (VarE "externaddr'#1")
            List
            (iterexp "externaddr'#1" (VarE "externaddr'*"))
          )
        )
      )
      (CatE
        (ListE (VarE "fa"))
        (CallE
          "funcs"
          (ExpA
            (IterE
              (VarE "externaddr'")
              List
              (iterexp "externaddr'" (VarE "externaddr'*"))
            )
          )
        )
      )
    )
    (DefD
      (ExpP "externaddr" (VarT "externaddr"))
      (ExpP "externaddr'*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (VarE "externaddr"))
          (IterE
            (VarE "externaddr'#2")
            List
            (iterexp "externaddr'#2" (VarE "externaddr'*"))
          )
        )
      )
      (CallE
        "funcs"
        (ExpA
          (IterE
            (VarE "externaddr'")
            List
            (iterexp "externaddr'" (VarE "externaddr'*"))
          )
        )
      )
    )
  )
)
(RecD
  (DecD
    "globals"
    (ExpP "_" (IterT (VarT "externaddr") List))
    (IterT (VarT "globaladdr") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "ga" nat)
      (ExpP "externaddr'*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "ga"))))
          (IterE
            (VarE "externaddr'#3")
            List
            (iterexp "externaddr'#3" (VarE "externaddr'*"))
          )
        )
      )
      (CatE
        (ListE (VarE "ga"))
        (CallE
          "globals"
          (ExpA
            (IterE
              (VarE "externaddr'")
              List
              (iterexp "externaddr'" (VarE "externaddr'*"))
            )
          )
        )
      )
    )
    (DefD
      (ExpP "externaddr" (VarT "externaddr"))
      (ExpP "externaddr'*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (VarE "externaddr"))
          (IterE
            (VarE "externaddr'#4")
            List
            (iterexp "externaddr'#4" (VarE "externaddr'*"))
          )
        )
      )
      (CallE
        "globals"
        (ExpA
          (IterE
            (VarE "externaddr'")
            List
            (iterexp "externaddr'" (VarE "externaddr'*"))
          )
        )
      )
    )
  )
)
(RecD
  (DecD
    "tables"
    (ExpP "_" (IterT (VarT "externaddr") List))
    (IterT (VarT "tableaddr") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "ta" nat)
      (ExpP "externaddr'*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "ta"))))
          (IterE
            (VarE "externaddr'#5")
            List
            (iterexp "externaddr'#5" (VarE "externaddr'*"))
          )
        )
      )
      (CatE
        (ListE (VarE "ta"))
        (CallE
          "tables"
          (ExpA
            (IterE
              (VarE "externaddr'")
              List
              (iterexp "externaddr'" (VarE "externaddr'*"))
            )
          )
        )
      )
    )
    (DefD
      (ExpP "externaddr" (VarT "externaddr"))
      (ExpP "externaddr'*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (VarE "externaddr"))
          (IterE
            (VarE "externaddr'#6")
            List
            (iterexp "externaddr'#6" (VarE "externaddr'*"))
          )
        )
      )
      (CallE
        "tables"
        (ExpA
          (IterE
            (VarE "externaddr'")
            List
            (iterexp "externaddr'" (VarE "externaddr'*"))
          )
        )
      )
    )
  )
)
(RecD
  (DecD
    "mems"
    (ExpP "_" (IterT (VarT "externaddr") List))
    (IterT (VarT "memaddr") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "ma" nat)
      (ExpP "externaddr'*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "ma"))))
          (IterE
            (VarE "externaddr'#7")
            List
            (iterexp "externaddr'#7" (VarE "externaddr'*"))
          )
        )
      )
      (CatE
        (ListE (VarE "ma"))
        (CallE
          "mems"
          (ExpA
            (IterE
              (VarE "externaddr'")
              List
              (iterexp "externaddr'" (VarE "externaddr'*"))
            )
          )
        )
      )
    )
    (DefD
      (ExpP "externaddr" (VarT "externaddr"))
      (ExpP "externaddr'*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (VarE "externaddr"))
          (IterE
            (VarE "externaddr'#8")
            List
            (iterexp "externaddr'#8" (VarE "externaddr'*"))
          )
        )
      )
      (CallE
        "mems"
        (ExpA
          (IterE
            (VarE "externaddr'")
            List
            (iterexp "externaddr'" (VarE "externaddr'*"))
          )
        )
      )
    )
  )
)
(DecD
  "allocfunc"
  (ExpP "store" (VarT "store"))
  (ExpP "moduleinst" (VarT "moduleinst"))
  (ExpP "func" (VarT "func"))
  (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "funcaddr")))
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "moduleinst" (VarT "moduleinst"))
    (ExpP "func" (VarT "func"))
    (ExpP "fi" (VarT "funcinst"))
    (ExpP "x" (VarT "uN"))
    (ExpP "local*" (IterT (VarT "local") List))
    (ExpP "expr" (IterT (VarT "instr") List))
    (ExpA (VarE "s"))
    (ExpA (VarE "moduleinst"))
    (ExpA (VarE "func"))
    (TupE
      (ExtE (VarE "s") (DotP RootP (Atom FUNCS)) (ListE (VarE "fi")))
      (LenE (DotE (VarE "s") (Atom FUNCS)))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "fi")
        (StrE
          (expfield
            (Atom TYPE)
            (IdxE
              (DotE (VarE "moduleinst") (Atom TYPES))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
            )
          )
          (expfield (Atom MODULE) (VarE "moduleinst"))
          (expfield (Atom CODE) (VarE "func"))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "func")
        (CaseE
          (Seq (Atom FUNC) Arg Arg Arg)
          (TupE
            (VarE "x")
            (IterE (VarE "local#1") List (iterexp "local#1" (VarE "local*")))
            (VarE "expr")
          )
        )
      )
    )
    (RulePr "wf_funcinst" (Seq Arg) (TupE (VarE "fi")))
    (RulePr
      "wf_funcinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (IdxE
              (DotE (VarE "moduleinst") (Atom TYPES))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
            )
          )
          (expfield (Atom MODULE) (VarE "moduleinst"))
          (expfield (Atom CODE) (VarE "func"))
        )
      )
    )
    (RulePr
      "wf_func"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom FUNC) Arg Arg Arg)
          (TupE
            (VarE "x")
            (IterE (VarE "local#2") List (iterexp "local#2" (VarE "local*")))
            (VarE "expr")
          )
        )
      )
    )
  )
)
(RecD
  (DecD
    "allocfuncs"
    (ExpP "store" (VarT "store"))
    (ExpP "moduleinst" (VarT "moduleinst"))
    (ExpP "_" (IterT (VarT "func") List))
    (TupT
      (typbind "_" (VarT "store"))
      (typbind "_" (IterT (VarT "funcaddr") List))
    )
    (DefD
      (ExpP "s" (VarT "store"))
      (ExpP "moduleinst" (VarT "moduleinst"))
      (ExpA (VarE "s"))
      (ExpA (VarE "moduleinst"))
      (ExpA (ListE))
      (TupE (VarE "s") (ListE))
    )
    (DefD
      (ExpP "s" (VarT "store"))
      (ExpP "moduleinst" (VarT "moduleinst"))
      (ExpP "func" (VarT "func"))
      (ExpP "func'*" (IterT (VarT "func") List))
      (ExpA (VarE "s"))
      (ExpA (VarE "moduleinst"))
      (ExpA
        (CatE
          (ListE (VarE "func"))
          (IterE (VarE "func'#1") List (iterexp "func'#1" (VarE "func'*")))
        )
      )
      (TupE
        (VarE "s_2")
        (CatE
          (ListE (VarE "fa"))
          (IterE (VarE "fa'") List (iterexp "fa'" (VarE "fa'*")))
        )
      )
      (LetPr
        (TupE (VarE "s_1") (VarE "fa"))
        (CallE
          "allocfunc"
          (ExpA (VarE "s"))
          (ExpA (VarE "moduleinst"))
          (ExpA (VarE "func"))
        )
      )
      (LetPr
        (TupE
          (VarE "s_2")
          (IterE (VarE "fa'#1") List (iterexp "fa'#1" (VarE "fa'*")))
        )
        (CallE
          "allocfuncs"
          (ExpA (VarE "s_1"))
          (ExpA (VarE "moduleinst"))
          (ExpA
            (IterE (VarE "func'#2") List (iterexp "func'#2" (VarE "func'*")))
          )
        )
      )
      (RulePr
        "wf_store"
        (Seq Arg)
        (TupE
          (ProjE
            (CallE
              "allocfunc"
              (ExpA (VarE "s"))
              (ExpA (VarE "moduleinst"))
              (ExpA (VarE "func"))
            )
            0
          )
        )
      )
      (RulePr
        "wf_store"
        (Seq Arg)
        (TupE
          (ProjE
            (CallE
              "allocfuncs"
              (ExpA (VarE "s_1"))
              (ExpA (VarE "moduleinst"))
              (ExpA
                (IterE
                  (VarE "func'#3")
                  List
                  (iterexp "func'#3" (VarE "func'*"))
                )
              )
            )
            0
          )
        )
      )
    )
  )
)
(DecD
  "allocglobal"
  (ExpP "store" (VarT "store"))
  (ExpP "globaltype" (VarT "globaltype"))
  (ExpP "val" (VarT "val"))
  (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "globaladdr")))
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "globaltype" (VarT "globaltype"))
    (ExpP "val" (VarT "val"))
    (ExpP "gi" (VarT "globalinst"))
    (ExpA (VarE "s"))
    (ExpA (VarE "globaltype"))
    (ExpA (VarE "val"))
    (TupE
      (ExtE (VarE "s") (DotP RootP (Atom GLOBALS)) (ListE (VarE "gi")))
      (LenE (DotE (VarE "s") (Atom GLOBALS)))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "gi")
        (StrE
          (expfield (Atom TYPE) (VarE "globaltype"))
          (expfield (Atom VALUE) (VarE "val"))
        )
      )
    )
    (RulePr "wf_globalinst" (Seq Arg) (TupE (VarE "gi")))
    (RulePr
      "wf_globalinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom TYPE) (VarE "globaltype"))
          (expfield (Atom VALUE) (VarE "val"))
        )
      )
    )
  )
)
(RecD
  (DecD
    "allocglobals"
    (ExpP "store" (VarT "store"))
    (ExpP "_" (IterT (VarT "globaltype") List))
    (ExpP "_" (IterT (VarT "val") List))
    (TupT
      (typbind "_" (VarT "store"))
      (typbind "_" (IterT (VarT "globaladdr") List))
    )
    (DefD
      (ExpP "s" (VarT "store"))
      (ExpA (VarE "s"))
      (ExpA (ListE))
      (ExpA (ListE))
      (TupE (VarE "s") (ListE))
    )
    (DefD
      (ExpP "s" (VarT "store"))
      (ExpP "globaltype" (VarT "globaltype"))
      (ExpP "globaltype'*" (IterT (VarT "globaltype") List))
      (ExpP "val" (VarT "val"))
      (ExpP "val'*" (IterT (VarT "val") List))
      (ExpA (VarE "s"))
      (ExpA
        (CatE
          (ListE (VarE "globaltype"))
          (IterE
            (VarE "globaltype'#1")
            List
            (iterexp "globaltype'#1" (VarE "globaltype'*"))
          )
        )
      )
      (ExpA
        (CatE
          (ListE (VarE "val"))
          (IterE (VarE "val'#1") List (iterexp "val'#1" (VarE "val'*")))
        )
      )
      (TupE
        (VarE "s_2")
        (CatE
          (ListE (VarE "ga"))
          (IterE (VarE "ga'") List (iterexp "ga'" (VarE "ga'*")))
        )
      )
      (LetPr
        (TupE (VarE "s_1") (VarE "ga"))
        (CallE
          "allocglobal"
          (ExpA (VarE "s"))
          (ExpA (VarE "globaltype"))
          (ExpA (VarE "val"))
        )
      )
      (LetPr
        (TupE
          (VarE "s_2")
          (IterE (VarE "ga'#1") List (iterexp "ga'#1" (VarE "ga'*")))
        )
        (CallE
          "allocglobals"
          (ExpA (VarE "s_1"))
          (ExpA
            (IterE
              (VarE "globaltype'#2")
              List
              (iterexp "globaltype'#2" (VarE "globaltype'*"))
            )
          )
          (ExpA (IterE (VarE "val'#2") List (iterexp "val'#2" (VarE "val'*"))))
        )
      )
      (RulePr
        "wf_store"
        (Seq Arg)
        (TupE
          (ProjE
            (CallE
              "allocglobal"
              (ExpA (VarE "s"))
              (ExpA (VarE "globaltype"))
              (ExpA (VarE "val"))
            )
            0
          )
        )
      )
      (RulePr
        "wf_store"
        (Seq Arg)
        (TupE
          (ProjE
            (CallE
              "allocglobals"
              (ExpA (VarE "s_1"))
              (ExpA
                (IterE
                  (VarE "globaltype'#3")
                  List
                  (iterexp "globaltype'#3" (VarE "globaltype'*"))
                )
              )
              (ExpA
                (IterE (VarE "val'#3") List (iterexp "val'#3" (VarE "val'*")))
              )
            )
            0
          )
        )
      )
    )
  )
)
(DecD
  "alloctable"
  (ExpP "store" (VarT "store"))
  (ExpP "tabletype" (VarT "tabletype"))
  (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "tableaddr")))
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "i" (VarT "uN"))
    (ExpP "j?" (IterT (VarT "u32") Opt))
    (ExpP "ti" (VarT "tableinst"))
    (ExpA (VarE "s"))
    (ExpA
      (CaseE
        (Brack [ (Infix Arg .. Arg) ])
        (TupE (VarE "i") (IterE (VarE "j#11") Opt (iterexp "j#11" (VarE "j?"))))
      )
    )
    (TupE
      (ExtE (VarE "s") (DotP RootP (Atom TABLES)) (ListE (VarE "ti")))
      (LenE (DotE (VarE "s") (Atom TABLES)))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "ti")
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Brack [ (Infix Arg .. Arg) ])
              (TupE
                (VarE "i")
                (IterE (VarE "j#12") Opt (iterexp "j#12" (VarE "j?")))
              )
            )
          )
          (expfield
            (Atom REFS)
            (IterE
              (OptE)
              (ListN (ProjE (CallE "proj_uN_0" (ExpA (VarE "i"))) 0))
            )
          )
        )
      )
    )
    (RulePr "wf_tableinst" (Seq Arg) (TupE (VarE "ti")))
    (RulePr
      "wf_tableinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Brack [ (Infix Arg .. Arg) ])
              (TupE
                (VarE "i")
                (IterE (VarE "j#13") Opt (iterexp "j#13" (VarE "j?")))
              )
            )
          )
          (expfield
            (Atom REFS)
            (IterE
              (OptE)
              (ListN (ProjE (CallE "proj_uN_0" (ExpA (VarE "i"))) 0))
            )
          )
        )
      )
    )
  )
)
(RecD
  (DecD
    "alloctables"
    (ExpP "store" (VarT "store"))
    (ExpP "_" (IterT (VarT "tabletype") List))
    (TupT
      (typbind "_" (VarT "store"))
      (typbind "_" (IterT (VarT "tableaddr") List))
    )
    (DefD
      (ExpP "s" (VarT "store"))
      (ExpA (VarE "s"))
      (ExpA (ListE))
      (TupE (VarE "s") (ListE))
    )
    (DefD
      (ExpP "s" (VarT "store"))
      (ExpP "tabletype" (VarT "limits"))
      (ExpP "tabletype'*" (IterT (VarT "tabletype") List))
      (ExpA (VarE "s"))
      (ExpA
        (CatE
          (ListE (VarE "tabletype"))
          (IterE
            (VarE "tabletype'#1")
            List
            (iterexp "tabletype'#1" (VarE "tabletype'*"))
          )
        )
      )
      (TupE
        (VarE "s_2")
        (CatE
          (ListE (VarE "ta"))
          (IterE (VarE "ta'") List (iterexp "ta'" (VarE "ta'*")))
        )
      )
      (LetPr
        (TupE (VarE "s_1") (VarE "ta"))
        (CallE "alloctable" (ExpA (VarE "s")) (ExpA (VarE "tabletype")))
      )
      (LetPr
        (TupE
          (VarE "s_2")
          (IterE (VarE "ta'#1") List (iterexp "ta'#1" (VarE "ta'*")))
        )
        (CallE
          "alloctables"
          (ExpA (VarE "s_1"))
          (ExpA
            (IterE
              (VarE "tabletype'#2")
              List
              (iterexp "tabletype'#2" (VarE "tabletype'*"))
            )
          )
        )
      )
      (RulePr
        "wf_store"
        (Seq Arg)
        (TupE
          (ProjE
            (CallE "alloctable" (ExpA (VarE "s")) (ExpA (VarE "tabletype")))
            0
          )
        )
      )
      (RulePr
        "wf_store"
        (Seq Arg)
        (TupE
          (ProjE
            (CallE
              "alloctables"
              (ExpA (VarE "s_1"))
              (ExpA
                (IterE
                  (VarE "tabletype'#3")
                  List
                  (iterexp "tabletype'#3" (VarE "tabletype'*"))
                )
              )
            )
            0
          )
        )
      )
    )
  )
)
(DecD
  "allocmem"
  (ExpP "store" (VarT "store"))
  (ExpP "memtype" (VarT "memtype"))
  (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "memaddr")))
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "i" (VarT "uN"))
    (ExpP "j?" (IterT (VarT "u32") Opt))
    (ExpP "mi" (VarT "meminst"))
    (ExpA (VarE "s"))
    (ExpA
      (CaseE
        (Brack [ (Infix Arg .. Arg) ])
        (TupE (VarE "i") (IterE (VarE "j#14") Opt (iterexp "j#14" (VarE "j?"))))
      )
    )
    (TupE
      (ExtE (VarE "s") (DotP RootP (Atom MEMS)) (ListE (VarE "mi")))
      (LenE (DotE (VarE "s") (Atom MEMS)))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "mi")
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Brack [ (Infix Arg .. Arg) ])
              (TupE
                (VarE "i")
                (IterE (VarE "j#15") Opt (iterexp "j#15" (VarE "j?")))
              )
            )
          )
          (expfield
            (Atom BYTES)
            (IterE
              (CaseE Arg (TupE (NumE (Nat 0))))
              (ListN
                (BinE
                  MulOp
                  nat
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "i"))) 0)
                  (BinE MulOp nat (NumE (Nat 64)) (CallE "Ki"))
                )
              )
            )
          )
        )
      )
    )
    (RulePr "wf_meminst" (Seq Arg) (TupE (VarE "mi")))
    (RulePr
      "wf_meminst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Brack [ (Infix Arg .. Arg) ])
              (TupE
                (VarE "i")
                (IterE (VarE "j#16") Opt (iterexp "j#16" (VarE "j?")))
              )
            )
          )
          (expfield
            (Atom BYTES)
            (IterE
              (CaseE Arg (TupE (NumE (Nat 0))))
              (ListN
                (BinE
                  MulOp
                  nat
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "i"))) 0)
                  (BinE MulOp nat (NumE (Nat 64)) (CallE "Ki"))
                )
              )
            )
          )
        )
      )
    )
  )
)
(RecD
  (DecD
    "allocmems"
    (ExpP "store" (VarT "store"))
    (ExpP "_" (IterT (VarT "memtype") List))
    (TupT
      (typbind "_" (VarT "store"))
      (typbind "_" (IterT (VarT "memaddr") List))
    )
    (DefD
      (ExpP "s" (VarT "store"))
      (ExpA (VarE "s"))
      (ExpA (ListE))
      (TupE (VarE "s") (ListE))
    )
    (DefD
      (ExpP "s" (VarT "store"))
      (ExpP "memtype" (VarT "limits"))
      (ExpP "memtype'*" (IterT (VarT "memtype") List))
      (ExpA (VarE "s"))
      (ExpA
        (CatE
          (ListE (VarE "memtype"))
          (IterE
            (VarE "memtype'#1")
            List
            (iterexp "memtype'#1" (VarE "memtype'*"))
          )
        )
      )
      (TupE
        (VarE "s_2")
        (CatE
          (ListE (VarE "ma"))
          (IterE (VarE "ma'") List (iterexp "ma'" (VarE "ma'*")))
        )
      )
      (LetPr
        (TupE (VarE "s_1") (VarE "ma"))
        (CallE "allocmem" (ExpA (VarE "s")) (ExpA (VarE "memtype")))
      )
      (LetPr
        (TupE
          (VarE "s_2")
          (IterE (VarE "ma'#1") List (iterexp "ma'#1" (VarE "ma'*")))
        )
        (CallE
          "allocmems"
          (ExpA (VarE "s_1"))
          (ExpA
            (IterE
              (VarE "memtype'#2")
              List
              (iterexp "memtype'#2" (VarE "memtype'*"))
            )
          )
        )
      )
      (RulePr
        "wf_store"
        (Seq Arg)
        (TupE
          (ProjE (CallE "allocmem" (ExpA (VarE "s")) (ExpA (VarE "memtype"))) 0)
        )
      )
      (RulePr
        "wf_store"
        (Seq Arg)
        (TupE
          (ProjE
            (CallE
              "allocmems"
              (ExpA (VarE "s_1"))
              (ExpA
                (IterE
                  (VarE "memtype'#3")
                  List
                  (iterexp "memtype'#3" (VarE "memtype'*"))
                )
              )
            )
            0
          )
        )
      )
    )
  )
)
(DecD
  "instexport"
  (ExpP "_" (IterT (VarT "funcaddr") List))
  (ExpP "_" (IterT (VarT "globaladdr") List))
  (ExpP "_" (IterT (VarT "tableaddr") List))
  (ExpP "_" (IterT (VarT "memaddr") List))
  (ExpP "export" (VarT "export"))
  (VarT "exportinst")
  (DefD
    (ExpP "fa*" (IterT (VarT "funcaddr") List))
    (ExpP "ga*" (IterT (VarT "globaladdr") List))
    (ExpP "ta*" (IterT (VarT "tableaddr") List))
    (ExpP "ma*" (IterT (VarT "memaddr") List))
    (ExpP "name" (VarT "name"))
    (ExpP "x" (VarT "uN"))
    (ExpA (IterE (VarE "fa#1") List (iterexp "fa#1" (VarE "fa*"))))
    (ExpA (IterE (VarE "ga#1") List (iterexp "ga#1" (VarE "ga*"))))
    (ExpA (IterE (VarE "ta#1") List (iterexp "ta#1" (VarE "ta*"))))
    (ExpA (IterE (VarE "ma#1") List (iterexp "ma#1" (VarE "ma*"))))
    (ExpA
      (CaseE
        (Seq (Atom EXPORT) Arg Arg)
        (TupE (VarE "name") (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "x"))))
      )
    )
    (StrE
      (expfield (Atom NAME) (VarE "name"))
      (expfield
        (Atom ADDR)
        (CaseE
          (Seq (Atom FUNC) Arg)
          (TupE
            (IdxE
              (IterE (VarE "fa") List (iterexp "fa" (VarE "fa*")))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
            )
          )
        )
      )
    )
    (RulePr
      "wf_exportinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom NAME) (VarE "name"))
          (expfield
            (Atom ADDR)
            (CaseE
              (Seq (Atom FUNC) Arg)
              (TupE
                (IdxE
                  (IterE (VarE "fa#2") List (iterexp "fa#2" (VarE "fa*")))
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "fa*" (IterT (VarT "funcaddr") List))
    (ExpP "ga*" (IterT (VarT "globaladdr") List))
    (ExpP "ta*" (IterT (VarT "tableaddr") List))
    (ExpP "ma*" (IterT (VarT "memaddr") List))
    (ExpP "name" (VarT "name"))
    (ExpP "x" (VarT "uN"))
    (ExpA (IterE (VarE "fa#3") List (iterexp "fa#3" (VarE "fa*"))))
    (ExpA (IterE (VarE "ga#2") List (iterexp "ga#2" (VarE "ga*"))))
    (ExpA (IterE (VarE "ta#2") List (iterexp "ta#2" (VarE "ta*"))))
    (ExpA (IterE (VarE "ma#2") List (iterexp "ma#2" (VarE "ma*"))))
    (ExpA
      (CaseE
        (Seq (Atom EXPORT) Arg Arg)
        (TupE (VarE "name") (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "x"))))
      )
    )
    (StrE
      (expfield (Atom NAME) (VarE "name"))
      (expfield
        (Atom ADDR)
        (CaseE
          (Seq (Atom GLOBAL) Arg)
          (TupE
            (IdxE
              (IterE (VarE "ga") List (iterexp "ga" (VarE "ga*")))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
            )
          )
        )
      )
    )
    (RulePr
      "wf_exportinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom NAME) (VarE "name"))
          (expfield
            (Atom ADDR)
            (CaseE
              (Seq (Atom GLOBAL) Arg)
              (TupE
                (IdxE
                  (IterE (VarE "ga#3") List (iterexp "ga#3" (VarE "ga*")))
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "fa*" (IterT (VarT "funcaddr") List))
    (ExpP "ga*" (IterT (VarT "globaladdr") List))
    (ExpP "ta*" (IterT (VarT "tableaddr") List))
    (ExpP "ma*" (IterT (VarT "memaddr") List))
    (ExpP "name" (VarT "name"))
    (ExpP "x" (VarT "uN"))
    (ExpA (IterE (VarE "fa#4") List (iterexp "fa#4" (VarE "fa*"))))
    (ExpA (IterE (VarE "ga#4") List (iterexp "ga#4" (VarE "ga*"))))
    (ExpA (IterE (VarE "ta#3") List (iterexp "ta#3" (VarE "ta*"))))
    (ExpA (IterE (VarE "ma#3") List (iterexp "ma#3" (VarE "ma*"))))
    (ExpA
      (CaseE
        (Seq (Atom EXPORT) Arg Arg)
        (TupE (VarE "name") (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "x"))))
      )
    )
    (StrE
      (expfield (Atom NAME) (VarE "name"))
      (expfield
        (Atom ADDR)
        (CaseE
          (Seq (Atom TABLE) Arg)
          (TupE
            (IdxE
              (IterE (VarE "ta") List (iterexp "ta" (VarE "ta*")))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
            )
          )
        )
      )
    )
    (RulePr
      "wf_exportinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom NAME) (VarE "name"))
          (expfield
            (Atom ADDR)
            (CaseE
              (Seq (Atom TABLE) Arg)
              (TupE
                (IdxE
                  (IterE (VarE "ta#4") List (iterexp "ta#4" (VarE "ta*")))
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "fa*" (IterT (VarT "funcaddr") List))
    (ExpP "ga*" (IterT (VarT "globaladdr") List))
    (ExpP "ta*" (IterT (VarT "tableaddr") List))
    (ExpP "ma*" (IterT (VarT "memaddr") List))
    (ExpP "name" (VarT "name"))
    (ExpP "x" (VarT "uN"))
    (ExpA (IterE (VarE "fa#5") List (iterexp "fa#5" (VarE "fa*"))))
    (ExpA (IterE (VarE "ga#5") List (iterexp "ga#5" (VarE "ga*"))))
    (ExpA (IterE (VarE "ta#5") List (iterexp "ta#5" (VarE "ta*"))))
    (ExpA (IterE (VarE "ma#4") List (iterexp "ma#4" (VarE "ma*"))))
    (ExpA
      (CaseE
        (Seq (Atom EXPORT) Arg Arg)
        (TupE (VarE "name") (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "x"))))
      )
    )
    (StrE
      (expfield (Atom NAME) (VarE "name"))
      (expfield
        (Atom ADDR)
        (CaseE
          (Seq (Atom MEM) Arg)
          (TupE
            (IdxE
              (IterE (VarE "ma") List (iterexp "ma" (VarE "ma*")))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
            )
          )
        )
      )
    )
    (RulePr
      "wf_exportinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom NAME) (VarE "name"))
          (expfield
            (Atom ADDR)
            (CaseE
              (Seq (Atom MEM) Arg)
              (TupE
                (IdxE
                  (IterE (VarE "ma#5") List (iterexp "ma#5" (VarE "ma*")))
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
                )
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "allocmodule"
  (ExpP "store" (VarT "store"))
  (ExpP "module" (VarT "module"))
  (ExpP "_" (IterT (VarT "externaddr") List))
  (ExpP "_" (IterT (VarT "val") List))
  (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "moduleinst")))
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "module" (VarT "module"))
    (ExpP "externaddr*" (IterT (VarT "externaddr") List))
    (ExpP "val*" (IterT (VarT "val") List))
    (ExpP "s_4" (VarT "store"))
    (ExpP "moduleinst" (VarT "moduleinst"))
    (ExpP "ft*" (IterT (VarT "functype") List))
    (ExpP "import*" (IterT (VarT "import") List))
    (ExpP "n_func" nat)
    (ExpP "func*" (IterT (VarT "func") List))
    (ExpP "n_global" nat)
    (ExpP "expr_1*" (IterT (VarT "expr") List))
    (ExpP "globaltype*" (IterT (VarT "globaltype") List))
    (ExpP "n_table" nat)
    (ExpP "tabletype*" (IterT (VarT "tabletype") List))
    (ExpP "n_mem" nat)
    (ExpP "memtype*" (IterT (VarT "memtype") List))
    (ExpP "elem*" (IterT (VarT "elem") List))
    (ExpP "data*" (IterT (VarT "data") List))
    (ExpP "start?" (IterT (VarT "start") Opt))
    (ExpP "export*" (IterT (VarT "export") List))
    (ExpP "s_1" (VarT "store"))
    (ExpP "s_2" (VarT "store"))
    (ExpP "s_3" (VarT "store"))
    (ExpA (VarE "s"))
    (ExpA (VarE "module"))
    (ExpA
      (IterE
        (VarE "externaddr#1")
        List
        (iterexp "externaddr#1" (VarE "externaddr*"))
      )
    )
    (ExpA (IterE (VarE "val#1") List (iterexp "val#1" (VarE "val*"))))
    (TupE (VarE "s_4") (VarE "moduleinst"))
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "module")
        (CaseE
          (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
          (TupE
            (IterE
              (CaseE (Seq (Atom TYPE) Arg) (TupE (VarE "ft#1")))
              List
              (iterexp "ft#1" (VarE "ft*"))
            )
            (IterE (VarE "import#1") List (iterexp "import#1" (VarE "import*")))
            (IterE
              (VarE "func#1")
              (ListN (VarE "n_func"))
              (iterexp "func#1" (VarE "func*"))
            )
            (IterE
              (CaseE
                (Seq (Atom GLOBAL) Arg Arg)
                (TupE (VarE "globaltype#195") (VarE "expr_1#1"))
              )
              (ListN (VarE "n_global"))
              (iterexp "expr_1#1" (VarE "expr_1*"))
              (iterexp "globaltype#195" (VarE "globaltype*"))
            )
            (IterE
              (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tabletype#241")))
              (ListN (VarE "n_table"))
              (iterexp "tabletype#241" (VarE "tabletype*"))
            )
            (IterE
              (CaseE (Seq (Atom MEMORY) Arg) (TupE (VarE "memtype#293")))
              (ListN (VarE "n_mem"))
              (iterexp "memtype#293" (VarE "memtype*"))
            )
            (IterE (VarE "elem#1") List (iterexp "elem#1" (VarE "elem*")))
            (IterE (VarE "data#1") List (iterexp "data#1" (VarE "data*")))
            (IterE (VarE "start#1") Opt (iterexp "start#1" (VarE "start?")))
            (IterE (VarE "export#1") List (iterexp "export#1" (VarE "export*")))
          )
        )
      )
    )
    (LetPr
      (IterE (VarE "fa_ex#1") List (iterexp "fa_ex#1" (VarE "fa_ex*")))
      (CallE
        "funcs"
        (ExpA
          (IterE
            (VarE "externaddr#2")
            List
            (iterexp "externaddr#2" (VarE "externaddr*"))
          )
        )
      )
    )
    (LetPr
      (IterE (VarE "ga_ex#1") List (iterexp "ga_ex#1" (VarE "ga_ex*")))
      (CallE
        "globals"
        (ExpA
          (IterE
            (VarE "externaddr#3")
            List
            (iterexp "externaddr#3" (VarE "externaddr*"))
          )
        )
      )
    )
    (LetPr
      (IterE (VarE "ta_ex#1") List (iterexp "ta_ex#1" (VarE "ta_ex*")))
      (CallE
        "tables"
        (ExpA
          (IterE
            (VarE "externaddr#4")
            List
            (iterexp "externaddr#4" (VarE "externaddr*"))
          )
        )
      )
    )
    (LetPr
      (IterE (VarE "ma_ex#1") List (iterexp "ma_ex#1" (VarE "ma_ex*")))
      (CallE
        "mems"
        (ExpA
          (IterE
            (VarE "externaddr#5")
            List
            (iterexp "externaddr#5" (VarE "externaddr*"))
          )
        )
      )
    )
    (LetPr
      (IterE (VarE "fa#6") List (iterexp "fa#6" (VarE "fa*")))
      (IterE
        (BinE AddOp nat (LenE (DotE (VarE "s") (Atom FUNCS))) (VarE "i_func#1"))
        (ListN (VarE "n_func") "i_func#1")
      )
    )
    (LetPr
      (IterE (VarE "ga#6") List (iterexp "ga#6" (VarE "ga*")))
      (IterE
        (BinE
          AddOp
          nat
          (LenE (DotE (VarE "s") (Atom GLOBALS)))
          (VarE "i_global#1")
        )
        (ListN (VarE "n_global") "i_global#1")
      )
    )
    (LetPr
      (IterE (VarE "ta#6") List (iterexp "ta#6" (VarE "ta*")))
      (IterE
        (BinE
          AddOp
          nat
          (LenE (DotE (VarE "s") (Atom TABLES)))
          (VarE "i_table#1")
        )
        (ListN (VarE "n_table") "i_table#1")
      )
    )
    (LetPr
      (IterE (VarE "ma#6") List (iterexp "ma#6" (VarE "ma*")))
      (IterE
        (BinE AddOp nat (LenE (DotE (VarE "s") (Atom MEMS))) (VarE "i_mem#1"))
        (ListN (VarE "n_mem") "i_mem#1")
      )
    )
    (LetPr
      (IterE (VarE "xi#1") List (iterexp "xi#1" (VarE "xi*")))
      (IterE
        (CallE
          "instexport"
          (ExpA
            (CatE
              (IterE (VarE "fa_ex#2") List (iterexp "fa_ex#2" (VarE "fa_ex*")))
              (IterE (VarE "fa#7") List (iterexp "fa#7" (VarE "fa*")))
            )
          )
          (ExpA
            (CatE
              (IterE (VarE "ga_ex#2") List (iterexp "ga_ex#2" (VarE "ga_ex*")))
              (IterE (VarE "ga#7") List (iterexp "ga#7" (VarE "ga*")))
            )
          )
          (ExpA
            (CatE
              (IterE (VarE "ta_ex#2") List (iterexp "ta_ex#2" (VarE "ta_ex*")))
              (IterE (VarE "ta#7") List (iterexp "ta#7" (VarE "ta*")))
            )
          )
          (ExpA
            (CatE
              (IterE (VarE "ma_ex#2") List (iterexp "ma_ex#2" (VarE "ma_ex*")))
              (IterE (VarE "ma#7") List (iterexp "ma#7" (VarE "ma*")))
            )
          )
          (ExpA (VarE "export#2"))
        )
        List
        (iterexp "export#2" (VarE "export*"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "moduleinst")
        (StrE
          (expfield
            (Atom TYPES)
            (IterE (VarE "ft#2") List (iterexp "ft#2" (VarE "ft*")))
          )
          (expfield
            (Atom FUNCS)
            (CatE
              (IterE (VarE "fa_ex#3") List (iterexp "fa_ex#3" (VarE "fa_ex*")))
              (IterE (VarE "fa#8") List (iterexp "fa#8" (VarE "fa*")))
            )
          )
          (expfield
            (Atom GLOBALS)
            (CatE
              (IterE (VarE "ga_ex#3") List (iterexp "ga_ex#3" (VarE "ga_ex*")))
              (IterE (VarE "ga#8") List (iterexp "ga#8" (VarE "ga*")))
            )
          )
          (expfield
            (Atom TABLES)
            (CatE
              (IterE (VarE "ta_ex#3") List (iterexp "ta_ex#3" (VarE "ta_ex*")))
              (IterE (VarE "ta#8") List (iterexp "ta#8" (VarE "ta*")))
            )
          )
          (expfield
            (Atom MEMS)
            (CatE
              (IterE (VarE "ma_ex#3") List (iterexp "ma_ex#3" (VarE "ma_ex*")))
              (IterE (VarE "ma#8") List (iterexp "ma#8" (VarE "ma*")))
            )
          )
          (expfield
            (Atom EXPORTS)
            (IterE (VarE "xi#2") List (iterexp "xi#2" (VarE "xi*")))
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (TupE
          (VarE "s_1")
          (IterE (VarE "fa#9") List (iterexp "fa#9" (VarE "fa*")))
        )
        (CallE
          "allocfuncs"
          (ExpA (VarE "s"))
          (ExpA (VarE "moduleinst"))
          (ExpA
            (IterE
              (VarE "func#2")
              (ListN (VarE "n_func"))
              (iterexp "func#2" (VarE "func*"))
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (TupE
          (VarE "s_2")
          (IterE (VarE "ga#9") List (iterexp "ga#9" (VarE "ga*")))
        )
        (CallE
          "allocglobals"
          (ExpA (VarE "s_1"))
          (ExpA
            (IterE
              (VarE "globaltype#197")
              (ListN (VarE "n_global"))
              (iterexp "globaltype#197" (VarE "globaltype*"))
            )
          )
          (ExpA (IterE (VarE "val#2") List (iterexp "val#2" (VarE "val*"))))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (TupE
          (VarE "s_3")
          (IterE (VarE "ta#9") List (iterexp "ta#9" (VarE "ta*")))
        )
        (CallE
          "alloctables"
          (ExpA (VarE "s_2"))
          (ExpA
            (IterE
              (VarE "tabletype#243")
              (ListN (VarE "n_table"))
              (iterexp "tabletype#243" (VarE "tabletype*"))
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (TupE
          (VarE "s_4")
          (IterE (VarE "ma#9") List (iterexp "ma#9" (VarE "ma*")))
        )
        (CallE
          "allocmems"
          (ExpA (VarE "s_3"))
          (ExpA
            (IterE
              (VarE "memtype#295")
              (ListN (VarE "n_mem"))
              (iterexp "memtype#295" (VarE "memtype*"))
            )
          )
        )
      )
    )
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s_4")))
    (RulePr "wf_moduleinst" (Seq Arg) (TupE (VarE "moduleinst")))
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s_1")))
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s_2")))
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s_3")))
    (IterPr
      (RulePr
        "wf_exportinst"
        (Seq Arg)
        (TupE
          (CallE
            "instexport"
            (ExpA
              (CatE
                (IterE
                  (VarE "fa_ex#4")
                  List
                  (iterexp "fa_ex#4" (VarE "fa_ex*"))
                )
                (IterE (VarE "fa#10") List (iterexp "fa#10" (VarE "fa*")))
              )
            )
            (ExpA
              (CatE
                (IterE
                  (VarE "ga_ex#4")
                  List
                  (iterexp "ga_ex#4" (VarE "ga_ex*"))
                )
                (IterE (VarE "ga#10") List (iterexp "ga#10" (VarE "ga*")))
              )
            )
            (ExpA
              (CatE
                (IterE
                  (VarE "ta_ex#4")
                  List
                  (iterexp "ta_ex#4" (VarE "ta_ex*"))
                )
                (IterE (VarE "ta#10") List (iterexp "ta#10" (VarE "ta*")))
              )
            )
            (ExpA
              (CatE
                (IterE
                  (VarE "ma_ex#4")
                  List
                  (iterexp "ma_ex#4" (VarE "ma_ex*"))
                )
                (IterE (VarE "ma#10") List (iterexp "ma#10" (VarE "ma*")))
              )
            )
            (ExpA (VarE "export#3"))
          )
        )
      )
      List
      (iterexp "export#3" (VarE "export*"))
    )
    (RulePr
      "wf_store"
      (Seq Arg)
      (TupE
        (ProjE
          (CallE
            "allocfuncs"
            (ExpA (VarE "s"))
            (ExpA (VarE "moduleinst"))
            (ExpA
              (IterE
                (VarE "func#3")
                (ListN (VarE "n_func"))
                (iterexp "func#3" (VarE "func*"))
              )
            )
          )
          0
        )
      )
    )
    (RulePr
      "wf_store"
      (Seq Arg)
      (TupE
        (ProjE
          (CallE
            "allocglobals"
            (ExpA (VarE "s_1"))
            (ExpA
              (IterE
                (VarE "globaltype#198")
                (ListN (VarE "n_global"))
                (iterexp "globaltype#198" (VarE "globaltype*"))
              )
            )
            (ExpA (IterE (VarE "val#3") List (iterexp "val#3" (VarE "val*"))))
          )
          0
        )
      )
    )
    (RulePr
      "wf_store"
      (Seq Arg)
      (TupE
        (ProjE
          (CallE
            "alloctables"
            (ExpA (VarE "s_2"))
            (ExpA
              (IterE
                (VarE "tabletype#244")
                (ListN (VarE "n_table"))
                (iterexp "tabletype#244" (VarE "tabletype*"))
              )
            )
          )
          0
        )
      )
    )
    (RulePr
      "wf_store"
      (Seq Arg)
      (TupE
        (ProjE
          (CallE
            "allocmems"
            (ExpA (VarE "s_3"))
            (ExpA
              (IterE
                (VarE "memtype#296")
                (ListN (VarE "n_mem"))
                (iterexp "memtype#296" (VarE "memtype*"))
              )
            )
          )
          0
        )
      )
    )
    (RulePr
      "wf_module"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
          (TupE
            (IterE
              (CaseE (Seq (Atom TYPE) Arg) (TupE (VarE "ft#3")))
              List
              (iterexp "ft#3" (VarE "ft*"))
            )
            (IterE (VarE "import#2") List (iterexp "import#2" (VarE "import*")))
            (IterE
              (VarE "func#4")
              (ListN (VarE "n_func"))
              (iterexp "func#4" (VarE "func*"))
            )
            (IterE
              (CaseE
                (Seq (Atom GLOBAL) Arg Arg)
                (TupE (VarE "globaltype#199") (VarE "expr_1#2"))
              )
              (ListN (VarE "n_global"))
              (iterexp "expr_1#2" (VarE "expr_1*"))
              (iterexp "globaltype#199" (VarE "globaltype*"))
            )
            (IterE
              (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tabletype#245")))
              (ListN (VarE "n_table"))
              (iterexp "tabletype#245" (VarE "tabletype*"))
            )
            (IterE
              (CaseE (Seq (Atom MEMORY) Arg) (TupE (VarE "memtype#297")))
              (ListN (VarE "n_mem"))
              (iterexp "memtype#297" (VarE "memtype*"))
            )
            (IterE (VarE "elem#2") List (iterexp "elem#2" (VarE "elem*")))
            (IterE (VarE "data#2") List (iterexp "data#2" (VarE "data*")))
            (IterE (VarE "start#2") Opt (iterexp "start#2" (VarE "start?")))
            (IterE (VarE "export#4") List (iterexp "export#4" (VarE "export*")))
          )
        )
      )
    )
    (RulePr
      "wf_moduleinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPES)
            (IterE (VarE "ft#4") List (iterexp "ft#4" (VarE "ft*")))
          )
          (expfield
            (Atom FUNCS)
            (CatE
              (IterE (VarE "fa_ex#5") List (iterexp "fa_ex#5" (VarE "fa_ex*")))
              (IterE (VarE "fa#11") List (iterexp "fa#11" (VarE "fa*")))
            )
          )
          (expfield
            (Atom GLOBALS)
            (CatE
              (IterE (VarE "ga_ex#5") List (iterexp "ga_ex#5" (VarE "ga_ex*")))
              (IterE (VarE "ga#11") List (iterexp "ga#11" (VarE "ga*")))
            )
          )
          (expfield
            (Atom TABLES)
            (CatE
              (IterE (VarE "ta_ex#5") List (iterexp "ta_ex#5" (VarE "ta_ex*")))
              (IterE (VarE "ta#11") List (iterexp "ta#11" (VarE "ta*")))
            )
          )
          (expfield
            (Atom MEMS)
            (CatE
              (IterE (VarE "ma_ex#5") List (iterexp "ma_ex#5" (VarE "ma_ex*")))
              (IterE (VarE "ma#11") List (iterexp "ma#11" (VarE "ma*")))
            )
          )
          (expfield
            (Atom EXPORTS)
            (IterE (VarE "xi#3") List (iterexp "xi#3" (VarE "xi*")))
          )
        )
      )
    )
  )
)
(RecD
  (DecD
    "initelem"
    (ExpP "store" (VarT "store"))
    (ExpP "moduleinst" (VarT "moduleinst"))
    (ExpP "_" (IterT (VarT "u32") List))
    (ExpP "_" (IterT (IterT (VarT "funcaddr") List) List))
    (VarT "store")
    (DefD
      (ExpP "s" (VarT "store"))
      (ExpP "moduleinst" (VarT "moduleinst"))
      (ExpA (VarE "s"))
      (ExpA (VarE "moduleinst"))
      (ExpA (ListE))
      (ExpA (ListE))
      (VarE "s")
    )
    (DefD
      (ExpP "s" (VarT "store"))
      (ExpP "moduleinst" (VarT "moduleinst"))
      (ExpP "i" (VarT "uN"))
      (ExpP "i'*" (IterT (VarT "u32") List))
      (ExpP "a*" (IterT (VarT "addr") List))
      (ExpP "a'**" (IterT (IterT (VarT "addr") List) List))
      (ExpP "s_1" (VarT "store"))
      (ExpA (VarE "s"))
      (ExpA (VarE "moduleinst"))
      (ExpA
        (CatE
          (ListE (VarE "i"))
          (IterE (VarE "i'#1") List (iterexp "i'#1" (VarE "i'*")))
        )
      )
      (ExpA
        (CatE
          (ListE (IterE (VarE "a#6") List (iterexp "a#6" (VarE "a*"))))
          (IterE
            (IterE (VarE "a'#1") List (iterexp "a'#1" (VarE "a'*#1")))
            List
            (iterexp "a'*#1" (VarE "a'**"))
          )
        )
      )
      (VarE "s_2")
      (IfPr
        (CmpE
          EqOp
          bool
          (VarE "s_1")
          (UpdE
            (VarE "s")
            (SliceP
              (DotP
                (IdxP
                  (DotP RootP (Atom TABLES))
                  (IdxE (DotE (VarE "moduleinst") (Atom TABLES)) (NumE (Nat 0)))
                )
                (Atom REFS)
              )
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "i"))) 0)
              (LenE (IterE (VarE "a#8") List (iterexp "a#8" (VarE "a*"))))
            )
            (IterE (OptE (VarE "a#7")) List (iterexp "a#7" (VarE "a*")))
          )
        )
      )
      (LetPr
        (VarE "s_2")
        (CallE
          "initelem"
          (ExpA (VarE "s_1"))
          (ExpA (VarE "moduleinst"))
          (ExpA (IterE (VarE "i'#2") List (iterexp "i'#2" (VarE "i'*"))))
          (ExpA
            (IterE
              (IterE (VarE "a'#2") List (iterexp "a'#2" (VarE "a'*#2")))
              List
              (iterexp "a'*#2" (VarE "a'**"))
            )
          )
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s_1")))
      (RulePr
        "wf_store"
        (Seq Arg)
        (TupE
          (CallE
            "initelem"
            (ExpA (VarE "s_1"))
            (ExpA (VarE "moduleinst"))
            (ExpA (IterE (VarE "i'#3") List (iterexp "i'#3" (VarE "i'*"))))
            (ExpA
              (IterE
                (IterE (VarE "a'#3") List (iterexp "a'#3" (VarE "a'*#3")))
                List
                (iterexp "a'*#3" (VarE "a'**"))
              )
            )
          )
        )
      )
    )
  )
)
(RecD
  (DecD
    "initdata"
    (ExpP "store" (VarT "store"))
    (ExpP "moduleinst" (VarT "moduleinst"))
    (ExpP "_" (IterT (VarT "u32") List))
    (ExpP "_" (IterT (IterT (VarT "byte") List) List))
    (VarT "store")
    (DefD
      (ExpP "s" (VarT "store"))
      (ExpP "moduleinst" (VarT "moduleinst"))
      (ExpA (VarE "s"))
      (ExpA (VarE "moduleinst"))
      (ExpA (ListE))
      (ExpA (ListE))
      (VarE "s")
    )
    (DefD
      (ExpP "s" (VarT "store"))
      (ExpP "moduleinst" (VarT "moduleinst"))
      (ExpP "i" (VarT "uN"))
      (ExpP "i'*" (IterT (VarT "u32") List))
      (ExpP "b*" (IterT (VarT "byte") List))
      (ExpP "b'**" (IterT (IterT (VarT "byte") List) List))
      (ExpA (VarE "s"))
      (ExpA (VarE "moduleinst"))
      (ExpA
        (CatE
          (ListE (VarE "i"))
          (IterE (VarE "i'#4") List (iterexp "i'#4" (VarE "i'*")))
        )
      )
      (ExpA
        (CatE
          (ListE (IterE (VarE "b#8") List (iterexp "b#8" (VarE "b*"))))
          (IterE
            (IterE (VarE "b'#1") List (iterexp "b'#1" (VarE "b'*#1")))
            List
            (iterexp "b'*#1" (VarE "b'**"))
          )
        )
      )
      (VarE "s_2")
      (LetPr
        (VarE "s_1")
        (UpdE
          (VarE "s")
          (SliceP
            (DotP
              (IdxP
                (DotP RootP (Atom MEMS))
                (IdxE (DotE (VarE "moduleinst") (Atom MEMS)) (NumE (Nat 0)))
              )
              (Atom BYTES)
            )
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "i"))) 0)
            (LenE (IterE (VarE "b#10") List (iterexp "b#10" (VarE "b*"))))
          )
          (IterE (VarE "b#9") List (iterexp "b#9" (VarE "b*")))
        )
      )
      (LetPr
        (VarE "s_2")
        (CallE
          "initdata"
          (ExpA (VarE "s_1"))
          (ExpA (VarE "moduleinst"))
          (ExpA (IterE (VarE "i'#5") List (iterexp "i'#5" (VarE "i'*"))))
          (ExpA
            (IterE
              (IterE (VarE "b'#2") List (iterexp "b'#2" (VarE "b'*#2")))
              List
              (iterexp "b'*#2" (VarE "b'**"))
            )
          )
        )
      )
      (RulePr
        "wf_store"
        (Seq Arg)
        (TupE
          (CallE
            "initdata"
            (ExpA (VarE "s_1"))
            (ExpA (VarE "moduleinst"))
            (ExpA (IterE (VarE "i'#6") List (iterexp "i'#6" (VarE "i'*"))))
            (ExpA
              (IterE
                (IterE (VarE "b'#3") List (iterexp "b'#3" (VarE "b'*#3")))
                List
                (iterexp "b'*#3" (VarE "b'**"))
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "instantiate"
  (ExpP "store" (VarT "store"))
  (ExpP "module" (VarT "module"))
  (ExpP "_" (IterT (VarT "externaddr") List))
  (VarT "config")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "module" (VarT "module"))
    (ExpP "externaddr*" (IterT (VarT "externaddr") List))
    (ExpP "f" (VarT "frame"))
    (ExpP "x'?" (IterT (VarT "idx") Opt))
    (ExpP "functype*" (IterT (VarT "functype") List))
    (ExpP "expr_G*" (IterT (VarT "expr") List))
    (ExpP "globaltype*" (IterT (VarT "globaltype") List))
    (ExpP "expr_E*" (IterT (VarT "expr") List))
    (ExpP "x**" (IterT (IterT (VarT "idx") List) List))
    (ExpP "b**" (IterT (IterT (VarT "byte") List) List))
    (ExpP "expr_D*" (IterT (VarT "expr") List))
    (ExpP "moduleinst_init" (VarT "moduleinst"))
    (ExpP "f_init" (VarT "frame"))
    (ExpP "val*" (IterT (VarT "val") List))
    (ExpP "i_E*" (IterT (VarT "val_") List))
    (ExpP "i_D*" (IterT (VarT "val_") List))
    (ExpA (VarE "s"))
    (ExpA (VarE "module"))
    (ExpA
      (IterE
        (VarE "externaddr#6")
        List
        (iterexp "externaddr#6" (VarE "externaddr*"))
      )
    )
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (CaseE (Infix Arg ; Arg) (TupE (VarE "s_3") (VarE "f")))
        (LiftE
          (IterE
            (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "x'")))
            Opt
            (iterexp "x'" (VarE "x'?"))
          )
        )
      )
    )
    (LetPr
      (CaseE
        (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
        (TupE
          (IterE (VarE "type#1") List (iterexp "type#1" (VarE "type*")))
          (IterE (VarE "import#3") List (iterexp "import#3" (VarE "import*")))
          (IterE (VarE "func#5") List (iterexp "func#5" (VarE "func*")))
          (IterE (VarE "global#1") List (iterexp "global#1" (VarE "global*")))
          (IterE (VarE "table#1") List (iterexp "table#1" (VarE "table*")))
          (IterE (VarE "mem#1") List (iterexp "mem#1" (VarE "mem*")))
          (IterE (VarE "elem#3") List (iterexp "elem#3" (VarE "elem*")))
          (IterE (VarE "data#3") List (iterexp "data#3" (VarE "data*")))
          (IterE (VarE "start#3") Opt (iterexp "start#3" (VarE "start?")))
          (IterE (VarE "export#5") List (iterexp "export#5" (VarE "export*")))
        )
      )
      (VarE "module")
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IterE (VarE "type#2") List (iterexp "type#2" (VarE "type*")))
        (IterE
          (CaseE (Seq (Atom TYPE) Arg) (TupE (VarE "functype#49")))
          List
          (iterexp "functype#49" (VarE "functype*"))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IterE (VarE "global#2") List (iterexp "global#2" (VarE "global*")))
        (IterE
          (CaseE
            (Seq (Atom GLOBAL) Arg Arg)
            (TupE (VarE "globaltype#201") (VarE "expr_G#1"))
          )
          List
          (iterexp "expr_G#1" (VarE "expr_G*"))
          (iterexp "globaltype#201" (VarE "globaltype*"))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IterE (VarE "elem#4") List (iterexp "elem#4" (VarE "elem*")))
        (IterE
          (CaseE
            (Seq (Atom ELEM) Arg Arg)
            (TupE
              (VarE "expr_E#1")
              (IterE (VarE "x#1") List (iterexp "x#1" (VarE "x*#1")))
            )
          )
          List
          (iterexp "expr_E#1" (VarE "expr_E*"))
          (iterexp "x*#1" (VarE "x**"))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IterE (VarE "data#4") List (iterexp "data#4" (VarE "data*")))
        (IterE
          (CaseE
            (Seq (Atom DATA) Arg Arg)
            (TupE
              (VarE "expr_D#1")
              (IterE (VarE "b#11") List (iterexp "b#11" (VarE "b*#1")))
            )
          )
          List
          (iterexp "b*#1" (VarE "b**"))
          (iterexp "expr_D#1" (VarE "expr_D*"))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IterE (VarE "start#4") Opt (iterexp "start#4" (VarE "start?")))
        (IterE
          (CaseE (Seq (Atom START) Arg) (TupE (VarE "x'#1")))
          Opt
          (iterexp "x'#1" (VarE "x'?"))
        )
      )
    )
    (LetPr
      (VarE "n_F")
      (LenE (IterE (VarE "func#6") List (iterexp "func#6" (VarE "func*"))))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "moduleinst_init")
        (StrE
          (expfield
            (Atom TYPES)
            (IterE
              (VarE "functype#51")
              List
              (iterexp "functype#51" (VarE "functype*"))
            )
          )
          (expfield
            (Atom FUNCS)
            (CatE
              (CallE
                "funcs"
                (ExpA
                  (IterE
                    (VarE "externaddr#7")
                    List
                    (iterexp "externaddr#7" (VarE "externaddr*"))
                  )
                )
              )
              (IterE
                (BinE
                  AddOp
                  nat
                  (LenE (DotE (VarE "s") (Atom FUNCS)))
                  (VarE "i_F#1")
                )
                (ListN (VarE "n_F") "i_F#1")
              )
            )
          )
          (expfield
            (Atom GLOBALS)
            (CallE
              "globals"
              (ExpA
                (IterE
                  (VarE "externaddr#8")
                  List
                  (iterexp "externaddr#8" (VarE "externaddr*"))
                )
              )
            )
          )
          (expfield (Atom TABLES) (ListE))
          (expfield (Atom MEMS) (ListE))
          (expfield (Atom EXPORTS) (ListE))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "f_init")
        (StrE
          (expfield (Atom LOCALS) (ListE))
          (expfield (Atom MODULE) (VarE "moduleinst_init"))
        )
      )
    )
    (LetPr
      (VarE "z")
      (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f_init")))
    )
    (IterPr
      (RulePr
        "Eval_expr"
        (Infix (Infix Arg ; Arg) ~>* (Infix Arg ; Arg))
        (TupE (VarE "z") (VarE "expr_G#2") (VarE "z") (ListE (VarE "val#4")))
      )
      List
      (iterexp "expr_G#2" (VarE "expr_G*"))
      (iterexp "val#4" (VarE "val*"))
    )
    (IterPr
      (RulePr
        "Eval_expr"
        (Infix (Infix Arg ; Arg) ~>* (Infix Arg ; Arg))
        (TupE
          (VarE "z")
          (VarE "expr_E#2")
          (VarE "z")
          (ListE
            (CaseE
              (Seq (Atom CONST) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "i_E#1"))
            )
          )
        )
      )
      List
      (iterexp "expr_E#2" (VarE "expr_E*"))
      (iterexp "i_E#1" (VarE "i_E*"))
    )
    (IterPr
      (RulePr
        "Eval_expr"
        (Infix (Infix Arg ; Arg) ~>* (Infix Arg ; Arg))
        (TupE
          (VarE "z")
          (VarE "expr_D#2")
          (VarE "z")
          (ListE
            (CaseE
              (Seq (Atom CONST) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "i_D#1"))
            )
          )
        )
      )
      List
      (iterexp "expr_D#2" (VarE "expr_D*"))
      (iterexp "i_D#1" (VarE "i_D*"))
    )
    (LetPr
      (TupE (VarE "s_1") (VarE "moduleinst"))
      (CallE
        "allocmodule"
        (ExpA (VarE "s"))
        (ExpA (VarE "module"))
        (ExpA
          (IterE
            (VarE "externaddr#9")
            List
            (iterexp "externaddr#9" (VarE "externaddr*"))
          )
        )
        (ExpA (IterE (VarE "val#5") List (iterexp "val#5" (VarE "val*"))))
      )
    )
    (LetPr
      (VarE "s_2")
      (CallE
        "initelem"
        (ExpA (VarE "s_1"))
        (ExpA (VarE "moduleinst"))
        (ExpA
          (IterE
            (TheE (CallE "proj_val__0" (ExpA (VarE "i_E#2"))))
            List
            (iterexp "i_E#2" (VarE "i_E*"))
          )
        )
        (ExpA
          (IterE
            (IterE
              (IdxE
                (DotE (VarE "moduleinst") (Atom FUNCS))
                (ProjE (CallE "proj_uN_0" (ExpA (VarE "x#2"))) 0)
              )
              List
              (iterexp "x#2" (VarE "x*#2"))
            )
            List
            (iterexp "x*#2" (VarE "x**"))
          )
        )
      )
    )
    (LetPr
      (VarE "s_3")
      (CallE
        "initdata"
        (ExpA (VarE "s_2"))
        (ExpA (VarE "moduleinst"))
        (ExpA
          (IterE
            (TheE (CallE "proj_val__0" (ExpA (VarE "i_D#2"))))
            List
            (iterexp "i_D#2" (VarE "i_D*"))
          )
        )
        (ExpA
          (IterE
            (IterE (VarE "b#12") List (iterexp "b#12" (VarE "b*#2")))
            List
            (iterexp "b*#2" (VarE "b**"))
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "f")
        (StrE
          (expfield (Atom LOCALS) (ListE))
          (expfield (Atom MODULE) (VarE "moduleinst"))
        )
      )
    )
    (IterPr
      (RulePr "wf_val" (Seq Arg) (TupE (VarE "val#6")))
      List
      (iterexp "val#6" (VarE "val*"))
    )
    (RulePr
      "wf_store"
      (Seq Arg)
      (TupE
        (ProjE
          (CallE
            "allocmodule"
            (ExpA (VarE "s"))
            (ExpA (VarE "module"))
            (ExpA
              (IterE
                (VarE "externaddr#10")
                List
                (iterexp "externaddr#10" (VarE "externaddr*"))
              )
            )
            (ExpA (IterE (VarE "val#7") List (iterexp "val#7" (VarE "val*"))))
          )
          0
        )
      )
    )
    (RulePr
      "wf_moduleinst"
      (Seq Arg)
      (TupE
        (ProjE
          (CallE
            "allocmodule"
            (ExpA (VarE "s"))
            (ExpA (VarE "module"))
            (ExpA
              (IterE
                (VarE "externaddr#11")
                List
                (iterexp "externaddr#11" (VarE "externaddr*"))
              )
            )
            (ExpA (IterE (VarE "val#8") List (iterexp "val#8" (VarE "val*"))))
          )
          1
        )
      )
    )
    (RulePr
      "wf_store"
      (Seq Arg)
      (TupE
        (CallE
          "initelem"
          (ExpA (VarE "s_1"))
          (ExpA (VarE "moduleinst"))
          (ExpA
            (IterE
              (TheE (CallE "proj_val__0" (ExpA (VarE "i_E#3"))))
              List
              (iterexp "i_E#3" (VarE "i_E*"))
            )
          )
          (ExpA
            (IterE
              (IterE
                (IdxE
                  (DotE (VarE "moduleinst") (Atom FUNCS))
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "x#3"))) 0)
                )
                List
                (iterexp "x#3" (VarE "x*#3"))
              )
              List
              (iterexp "x*#3" (VarE "x**"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_store"
      (Seq Arg)
      (TupE
        (CallE
          "initdata"
          (ExpA (VarE "s_2"))
          (ExpA (VarE "moduleinst"))
          (ExpA
            (IterE
              (TheE (CallE "proj_val__0" (ExpA (VarE "i_D#3"))))
              List
              (iterexp "i_D#3" (VarE "i_D*"))
            )
          )
          (ExpA
            (IterE
              (IterE (VarE "b#13") List (iterexp "b#13" (VarE "b*#3")))
              List
              (iterexp "b*#3" (VarE "b**"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (CaseE (Infix Arg ; Arg) (TupE (VarE "s_3") (VarE "f")))
            (LiftE
              (IterE
                (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "x'#2")))
                Opt
                (iterexp "x'#2" (VarE "x'?"))
              )
            )
          )
        )
      )
    )
    (RulePr
      "wf_module"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
          (TupE
            (IterE (VarE "type#3") List (iterexp "type#3" (VarE "type*")))
            (IterE (VarE "import#4") List (iterexp "import#4" (VarE "import*")))
            (IterE (VarE "func#7") List (iterexp "func#7" (VarE "func*")))
            (IterE (VarE "global#3") List (iterexp "global#3" (VarE "global*")))
            (IterE (VarE "table#2") List (iterexp "table#2" (VarE "table*")))
            (IterE (VarE "mem#2") List (iterexp "mem#2" (VarE "mem*")))
            (IterE (VarE "elem#5") List (iterexp "elem#5" (VarE "elem*")))
            (IterE (VarE "data#5") List (iterexp "data#5" (VarE "data*")))
            (IterE (VarE "start#5") Opt (iterexp "start#5" (VarE "start?")))
            (IterE (VarE "export#6") List (iterexp "export#6" (VarE "export*")))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "wf_global"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom GLOBAL) Arg Arg)
            (TupE (VarE "globaltype#203") (VarE "expr_G#3"))
          )
        )
      )
      List
      (iterexp "expr_G#3" (VarE "expr_G*"))
      (iterexp "globaltype#203" (VarE "globaltype*"))
    )
    (IterPr
      (RulePr
        "wf_elem"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom ELEM) Arg Arg)
            (TupE
              (VarE "expr_E#3")
              (IterE (VarE "x#4") List (iterexp "x#4" (VarE "x*#4")))
            )
          )
        )
      )
      List
      (iterexp "expr_E#3" (VarE "expr_E*"))
      (iterexp "x*#4" (VarE "x**"))
    )
    (IterPr
      (RulePr
        "wf_data"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom DATA) Arg Arg)
            (TupE
              (VarE "expr_D#3")
              (IterE (VarE "b#14") List (iterexp "b#14" (VarE "b*#4")))
            )
          )
        )
      )
      List
      (iterexp "b*#4" (VarE "b**"))
      (iterexp "expr_D#3" (VarE "expr_D*"))
    )
    (IterPr
      (RulePr
        "wf_start"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom START) Arg) (TupE (VarE "x'#3"))))
      )
      Opt
      (iterexp "x'#3" (VarE "x'?"))
    )
    (RulePr
      "wf_moduleinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPES)
            (IterE
              (VarE "functype#52")
              List
              (iterexp "functype#52" (VarE "functype*"))
            )
          )
          (expfield
            (Atom FUNCS)
            (CatE
              (CallE
                "funcs"
                (ExpA
                  (IterE
                    (VarE "externaddr#12")
                    List
                    (iterexp "externaddr#12" (VarE "externaddr*"))
                  )
                )
              )
              (IterE
                (BinE
                  AddOp
                  nat
                  (LenE (DotE (VarE "s") (Atom FUNCS)))
                  (VarE "i_F#2")
                )
                (ListN (VarE "n_F") "i_F#2")
              )
            )
          )
          (expfield
            (Atom GLOBALS)
            (CallE
              "globals"
              (ExpA
                (IterE
                  (VarE "externaddr#13")
                  List
                  (iterexp "externaddr#13" (VarE "externaddr*"))
                )
              )
            )
          )
          (expfield (Atom TABLES) (ListE))
          (expfield (Atom MEMS) (ListE))
          (expfield (Atom EXPORTS) (ListE))
        )
      )
    )
    (RulePr
      "wf_frame"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom LOCALS) (ListE))
          (expfield (Atom MODULE) (VarE "moduleinst_init"))
        )
      )
    )
    (RulePr
      "wf_state"
      (Seq Arg)
      (TupE (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f_init"))))
    )
    (IterPr
      (RulePr
        "wf_val"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom CONST) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "i_E#4"))
          )
        )
      )
      List
      (iterexp "i_E#4" (VarE "i_E*"))
    )
    (IterPr
      (RulePr
        "wf_val"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom CONST) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "i_D#4"))
          )
        )
      )
      List
      (iterexp "i_D#4" (VarE "i_D*"))
    )
    (RulePr
      "wf_frame"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom LOCALS) (ListE))
          (expfield (Atom MODULE) (VarE "moduleinst"))
        )
      )
    )
  )
)
(DecD
  "invoke"
  (ExpP "store" (VarT "store"))
  (ExpP "funcaddr" (VarT "funcaddr"))
  (ExpP "_" (IterT (VarT "val") List))
  (VarT "config")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "fa" nat)
    (ExpP "n" nat)
    (ExpP "val*" (IterT (VarT "val") List))
    (ExpP "f" (VarT "frame"))
    (ExpP "t_1*" (IterT (VarT "valtype") List))
    (ExpP "t_2*" (IterT (VarT "valtype") List))
    (ExpA (VarE "s"))
    (ExpA (VarE "fa"))
    (ExpA (IterE (VarE "val#9") List (iterexp "val#9" (VarE "val*"))))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f")))
        (CatE
          (IterE
            (CallE "admininstr_val" (ExpA (VarE "val")))
            (ListN (VarE "n"))
            (iterexp "val" (VarE "val*"))
          )
          (ListE (CaseE (Seq (Atom CALL_ADDR) Arg) (TupE (VarE "fa"))))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "f")
        (StrE
          (expfield (Atom LOCALS) (ListE))
          (expfield
            (Atom MODULE)
            (StrE
              (expfield (Atom TYPES) (ListE))
              (expfield (Atom FUNCS) (ListE))
              (expfield (Atom GLOBALS) (ListE))
              (expfield (Atom TABLES) (ListE))
              (expfield (Atom MEMS) (ListE))
              (expfield (Atom EXPORTS) (ListE))
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (DotE
          (IdxE
            (CallE
              "funcinst"
              (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
            )
            (VarE "fa")
          )
          (Atom TYPE)
        )
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (IterE
              (VarE "t_1#1")
              (ListN (VarE "n"))
              (iterexp "t_1#1" (VarE "t_1*"))
            )
            (IterE (VarE "t_2#1") List (iterexp "t_2#1" (VarE "t_2*")))
          )
        )
      )
    )
    (IterPr
      (RulePr "wf_funcinst" (Seq Arg) (TupE (VarE "iter#53")))
      List
      (iterexp
        "iter#53"
        (CallE
          "funcinst"
          (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
        )
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f")))
            (CatE
              (IterE
                (CallE "admininstr_val" (ExpA (VarE "val#10")))
                (ListN (VarE "n"))
                (iterexp "val#10" (VarE "val*"))
              )
              (ListE (CaseE (Seq (Atom CALL_ADDR) Arg) (TupE (VarE "fa"))))
            )
          )
        )
      )
    )
    (RulePr
      "wf_frame"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom LOCALS) (ListE))
          (expfield
            (Atom MODULE)
            (StrE
              (expfield (Atom TYPES) (ListE))
              (expfield (Atom FUNCS) (ListE))
              (expfield (Atom GLOBALS) (ListE))
              (expfield (Atom TABLES) (ListE))
              (expfield (Atom MEMS) (ListE))
              (expfield (Atom EXPORTS) (ListE))
            )
          )
        )
      )
    )
    (RulePr
      "wf_state"
      (Seq Arg)
      (TupE (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    )
    (IfPr (CmpE EqOp bool (VarE "n") (LenE (VarE "val*"))))
  )
)
(TypD "startopt" (InstD (AliasT (IterT (VarT "start") List))))
(HintD (TypH "startopt" (hint "show" "start?")))
(TypD
  "code"
  (InstD
    (AliasT
      (TupT
        (typbind "_" (IterT (VarT "local") List))
        (typbind "_" (VarT "expr"))
      )
    )
  )
)
(RelD
  "Context_ok"
  (Infix (Seq) |- (Infix Arg : (Atom OK)))
  (VarT "context")
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "ft*" (IterT (VarT "functype") List))
    (ExpP "ft_2*" (IterT (VarT "functype") List))
    (ExpP "gt*" (IterT (VarT "globaltype") List))
    (ExpP "tt*" (IterT (VarT "tabletype") List))
    (ExpP "mt*" (IterT (VarT "memtype") List))
    (ExpP "lct*" (IterT (VarT "valtype") List))
    (ExpP "rt*" (IterT (VarT "valtype") List))
    (ExpP "rt'?" (IterT (VarT "valtype") Opt))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (VarE "C")
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "C")
        (StrE
          (expfield
            (Atom TYPES)
            (IterE (VarE "ft") List (iterexp "ft" (VarE "ft*")))
          )
          (expfield
            (Atom FUNCS)
            (IterE (VarE "ft_2") List (iterexp "ft_2" (VarE "ft_2*")))
          )
          (expfield
            (Atom GLOBALS)
            (IterE (VarE "gt") List (iterexp "gt" (VarE "gt*")))
          )
          (expfield
            (Atom TABLES)
            (IterE (VarE "tt") List (iterexp "tt" (VarE "tt*")))
          )
          (expfield
            (Atom MEMS)
            (IterE (VarE "mt") List (iterexp "mt" (VarE "mt*")))
          )
          (expfield
            (Atom LOCALS)
            (IterE (VarE "lct") List (iterexp "lct" (VarE "lct*")))
          )
          (expfield
            (Atom LABELS)
            (IterE (OptE (VarE "rt")) List (iterexp "rt" (VarE "rt*")))
          )
          (expfield
            (Atom RETURN)
            (OptE (IterE (VarE "rt'") Opt (iterexp "rt'" (VarE "rt'?"))))
          )
        )
      )
    )
    (IterPr
      (RulePr
        "Functype_ok"
        (Infix (Seq) |- (Infix Arg : (Atom OK)))
        (VarE "ft")
      )
      List
      (iterexp "ft" (VarE "ft*"))
    )
    (IterPr
      (RulePr
        "Globaltype_ok"
        (Infix (Seq) |- (Infix Arg : (Atom OK)))
        (VarE "gt")
      )
      List
      (iterexp "gt" (VarE "gt*"))
    )
    (IterPr
      (RulePr "Memtype_ok" (Infix (Seq) |- (Infix Arg : (Atom OK))) (VarE "mt"))
      List
      (iterexp "mt" (VarE "mt*"))
    )
    (IterPr
      (RulePr
        "Tabletype_ok"
        (Infix (Seq) |- (Infix Arg : (Atom OK)))
        (VarE "tt")
      )
      List
      (iterexp "tt" (VarE "tt*"))
    )
    (IterPr
      (RulePr
        "Functype_ok"
        (Infix (Seq) |- (Infix Arg : (Atom OK)))
        (VarE "ft_2")
      )
      List
      (iterexp "ft_2" (VarE "ft_2*"))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_context"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPES)
            (IterE (VarE "ft") List (iterexp "ft" (VarE "ft*")))
          )
          (expfield
            (Atom FUNCS)
            (IterE (VarE "ft_2") List (iterexp "ft_2" (VarE "ft_2*")))
          )
          (expfield
            (Atom GLOBALS)
            (IterE (VarE "gt") List (iterexp "gt" (VarE "gt*")))
          )
          (expfield
            (Atom TABLES)
            (IterE (VarE "tt") List (iterexp "tt" (VarE "tt*")))
          )
          (expfield
            (Atom MEMS)
            (IterE (VarE "mt") List (iterexp "mt" (VarE "mt*")))
          )
          (expfield
            (Atom LOCALS)
            (IterE (VarE "lct") List (iterexp "lct" (VarE "lct*")))
          )
          (expfield
            (Atom LABELS)
            (IterE (OptE (VarE "rt")) List (iterexp "rt" (VarE "rt*")))
          )
          (expfield
            (Atom RETURN)
            (OptE (IterE (VarE "rt'") Opt (iterexp "rt'" (VarE "rt'?"))))
          )
        )
      )
    )
  )
)
(HintD (RelH "Context_ok" (hint "macro" "\"%context\"")))
(RelD
  "Val_ok"
  (Infix (Seq) |- (Infix Arg : Arg))
  (TupT (typbind "_" (VarT "val")) (typbind "_" (VarT "valtype")))
  (RuleD
    ""
    (ExpP "t" (VarT "valtype"))
    (ExpP "c_t" (VarT "val_"))
    (Infix (Seq) |- (Infix Arg : Arg))
    (TupE
      (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_t")))
      (VarE "t")
    )
    (RulePr
      "wf_val"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_t"))))
    )
  )
)
(RelD
  "Result_ok"
  (Infix (Seq) |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "result"))
    (typbind "_" (IterT (VarT "valtype") List))
  )
  (RuleD
    "result"
    (ExpP "v*" (IterT (VarT "val") List))
    (ExpP "t*" (IterT (VarT "valtype") List))
    (Infix (Seq) |- (Infix Arg : Arg))
    (TupE
      (CaseE
        (Seq (Atom _VALS) Arg)
        (TupE (IterE (VarE "v") List (iterexp "v" (VarE "v*"))))
      )
      (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
    )
    (IterPr
      (RulePr
        "Val_ok"
        (Infix (Seq) |- (Infix Arg : Arg))
        (TupE (VarE "v") (VarE "t"))
      )
      List
      (iterexp "t" (VarE "t*"))
      (iterexp "v" (VarE "v*"))
    )
    (RulePr
      "wf_result"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom _VALS) Arg)
          (TupE (IterE (VarE "v") List (iterexp "v" (VarE "v*"))))
        )
      )
    )
  )
  (RuleD
    "trap"
    (ExpP "t*" (IterT (VarT "valtype") List))
    (Infix (Seq) |- (Infix Arg : Arg))
    (TupE
      (CaseE (Atom TRAP) (TupE))
      (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
    )
    (RulePr "wf_result" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
  )
)
(TypD "adminexpr" (InstD (AliasT (IterT (VarT "admininstr") List))))
(RecD
  (RelD
    "Externaddr_ok"
    (Infix Arg |- (Infix Arg : Arg))
    (TupT
      (typbind "_" (VarT "store"))
      (typbind "_" (VarT "externaddr"))
      (typbind "_" (VarT "externtype"))
    )
    (RuleD
      "global"
      (ExpP "s" (VarT "store"))
      (ExpP "a" (VarT "addr"))
      (ExpP "globalinst" (VarT "globalinst"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "a")))
        (CaseE
          (Seq (Atom GLOBAL) Arg)
          (TupE (DotE (VarE "globalinst") (Atom TYPE)))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "s") (Atom GLOBALS)) (VarE "a"))
          (VarE "globalinst")
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr
        "wf_externtype"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom GLOBAL) Arg)
            (TupE (DotE (VarE "globalinst") (Atom TYPE)))
          )
        )
      )
    )
    (RuleD
      "mem"
      (ExpP "s" (VarT "store"))
      (ExpP "a" (VarT "addr"))
      (ExpP "meminst" (VarT "meminst"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "a")))
        (CaseE (Seq (Atom MEM) Arg) (TupE (DotE (VarE "meminst") (Atom TYPE))))
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "s") (Atom MEMS)) (VarE "a"))
          (VarE "meminst")
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr
        "wf_externtype"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom MEM) Arg)
            (TupE (DotE (VarE "meminst") (Atom TYPE)))
          )
        )
      )
    )
    (RuleD
      "table"
      (ExpP "s" (VarT "store"))
      (ExpP "a" (VarT "addr"))
      (ExpP "tableinst" (VarT "tableinst"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "a")))
        (CaseE
          (Seq (Atom TABLE) Arg)
          (TupE (DotE (VarE "tableinst") (Atom TYPE)))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "s") (Atom TABLES)) (VarE "a"))
          (VarE "tableinst")
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr
        "wf_externtype"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom TABLE) Arg)
            (TupE (DotE (VarE "tableinst") (Atom TYPE)))
          )
        )
      )
    )
    (RuleD
      "func"
      (ExpP "s" (VarT "store"))
      (ExpP "a" (VarT "addr"))
      (ExpP "funcinst" (VarT "funcinst"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "a")))
        (CaseE
          (Seq (Atom FUNC) Arg)
          (TupE (DotE (VarE "funcinst") (Atom TYPE)))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "s") (Atom FUNCS)) (VarE "a"))
          (VarE "funcinst")
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr
        "wf_externtype"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom FUNC) Arg)
            (TupE (DotE (VarE "funcinst") (Atom TYPE)))
          )
        )
      )
    )
    (RuleD
      "sub"
      (ExpP "s" (VarT "store"))
      (ExpP "externaddr" (VarT "externaddr"))
      (ExpP "xt" (VarT "externtype"))
      (ExpP "xt'" (VarT "externtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "s") (VarE "externaddr") (VarE "xt"))
      (RulePr
        "Externaddr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "s") (VarE "externaddr") (VarE "xt'"))
      )
      (RulePr
        "Externtype_sub"
        (Infix (Seq) |- (Infix Arg <: Arg))
        (TupE (VarE "xt'") (VarE "xt"))
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr "wf_externtype" (Seq Arg) (TupE (VarE "xt")))
      (RulePr "wf_externtype" (Seq Arg) (TupE (VarE "xt'")))
    )
  )
)
(RelD
  "Exportinst_ok"
  (Infix Arg |- (Infix Arg : (Atom OK)))
  (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "exportinst")))
  (RuleD
    ""
    (ExpP "s" (VarT "store"))
    (ExpP "nm" (VarT "name"))
    (ExpP "xa" (VarT "externaddr"))
    (ExpP "xt" (VarT "externtype"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE
      (VarE "s")
      (StrE
        (expfield (Atom NAME) (VarE "nm"))
        (expfield (Atom ADDR) (VarE "xa"))
      )
    )
    (RulePr
      "Externaddr_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "s") (VarE "xa") (VarE "xt"))
    )
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
    (RulePr "wf_externtype" (Seq Arg) (TupE (VarE "xt")))
    (RulePr
      "wf_exportinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom NAME) (VarE "nm"))
          (expfield (Atom ADDR) (VarE "xa"))
        )
      )
    )
  )
)
(RelD
  "Moduleinst_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "moduleinst"))
    (typbind "_" (VarT "context"))
  )
  (RuleD
    ""
    (ExpP "s" (VarT "store"))
    (ExpP "functype*" (IterT (VarT "functype") List))
    (ExpP "funcaddr*" (IterT (VarT "funcaddr") List))
    (ExpP "globaladdr*" (IterT (VarT "globaladdr") List))
    (ExpP "tableaddr*" (IterT (VarT "tableaddr") List))
    (ExpP "memaddr*" (IterT (VarT "memaddr") List))
    (ExpP "exportinst*" (IterT (VarT "exportinst") List))
    (ExpP "functype_F*" (IterT (VarT "functype") List))
    (ExpP "globaltype*" (IterT (VarT "globaltype") List))
    (ExpP "tabletype*" (IterT (VarT "tabletype") List))
    (ExpP "memtype*" (IterT (VarT "memtype") List))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (StrE
        (expfield
          (Atom TYPES)
          (IterE (VarE "functype") List (iterexp "functype" (VarE "functype*")))
        )
        (expfield
          (Atom FUNCS)
          (IterE (VarE "funcaddr") List (iterexp "funcaddr" (VarE "funcaddr*")))
        )
        (expfield
          (Atom GLOBALS)
          (IterE
            (VarE "globaladdr")
            List
            (iterexp "globaladdr" (VarE "globaladdr*"))
          )
        )
        (expfield
          (Atom TABLES)
          (IterE
            (VarE "tableaddr")
            List
            (iterexp "tableaddr" (VarE "tableaddr*"))
          )
        )
        (expfield
          (Atom MEMS)
          (IterE (VarE "memaddr") List (iterexp "memaddr" (VarE "memaddr*")))
        )
        (expfield
          (Atom EXPORTS)
          (IterE
            (VarE "exportinst")
            List
            (iterexp "exportinst" (VarE "exportinst*"))
          )
        )
      )
      (StrE
        (expfield
          (Atom TYPES)
          (IterE (VarE "functype") List (iterexp "functype" (VarE "functype*")))
        )
        (expfield
          (Atom FUNCS)
          (IterE
            (VarE "functype_F")
            List
            (iterexp "functype_F" (VarE "functype_F*"))
          )
        )
        (expfield
          (Atom GLOBALS)
          (IterE
            (VarE "globaltype")
            List
            (iterexp "globaltype" (VarE "globaltype*"))
          )
        )
        (expfield
          (Atom TABLES)
          (IterE
            (VarE "tabletype")
            List
            (iterexp "tabletype" (VarE "tabletype*"))
          )
        )
        (expfield
          (Atom MEMS)
          (IterE (VarE "memtype") List (iterexp "memtype" (VarE "memtype*")))
        )
        (expfield (Atom LOCALS) (ListE))
        (expfield (Atom LABELS) (ListE))
        (expfield (Atom RETURN) (OptE))
      )
    )
    (IterPr
      (RulePr
        "Functype_ok"
        (Infix (Seq) |- (Infix Arg : (Atom OK)))
        (VarE "functype")
      )
      List
      (iterexp "functype" (VarE "functype*"))
    )
    (IterPr
      (RulePr
        "Externaddr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "globaladdr")))
          (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "globaltype")))
        )
      )
      List
      (iterexp "globaladdr" (VarE "globaladdr*"))
      (iterexp "globaltype" (VarE "globaltype*"))
    )
    (IterPr
      (RulePr
        "Externaddr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "funcaddr")))
          (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "functype_F")))
        )
      )
      List
      (iterexp "funcaddr" (VarE "funcaddr*"))
      (iterexp "functype_F" (VarE "functype_F*"))
    )
    (IterPr
      (RulePr
        "Externaddr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "memaddr")))
          (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "memtype")))
        )
      )
      List
      (iterexp "memaddr" (VarE "memaddr*"))
      (iterexp "memtype" (VarE "memtype*"))
    )
    (IterPr
      (RulePr
        "Externaddr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tableaddr")))
          (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tabletype")))
        )
      )
      List
      (iterexp "tableaddr" (VarE "tableaddr*"))
      (iterexp "tabletype" (VarE "tabletype*"))
    )
    (IterPr
      (RulePr
        "Exportinst_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "s") (VarE "exportinst"))
      )
      List
      (iterexp "exportinst" (VarE "exportinst*"))
    )
    (IfPr
      (CallE
        "disjoint_"
        (TypA (VarT "name"))
        (ExpA
          (IterE
            (DotE (VarE "exportinst") (Atom NAME))
            List
            (iterexp "exportinst" (VarE "exportinst*"))
          )
        )
      )
    )
    (IterPr
      (IfPr
        (MemE
          (DotE (VarE "exportinst") (Atom ADDR))
          (CatE
            (IterE
              (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "globaladdr")))
              List
              (iterexp "globaladdr" (VarE "globaladdr*"))
            )
            (CatE
              (IterE
                (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "memaddr")))
                List
                (iterexp "memaddr" (VarE "memaddr*"))
              )
              (CatE
                (IterE
                  (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tableaddr")))
                  List
                  (iterexp "tableaddr" (VarE "tableaddr*"))
                )
                (IterE
                  (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "funcaddr")))
                  List
                  (iterexp "funcaddr" (VarE "funcaddr*"))
                )
              )
            )
          )
        )
      )
      List
      (iterexp "exportinst" (VarE "exportinst*"))
    )
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
    (RulePr
      "wf_moduleinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPES)
            (IterE
              (VarE "functype")
              List
              (iterexp "functype" (VarE "functype*"))
            )
          )
          (expfield
            (Atom FUNCS)
            (IterE
              (VarE "funcaddr")
              List
              (iterexp "funcaddr" (VarE "funcaddr*"))
            )
          )
          (expfield
            (Atom GLOBALS)
            (IterE
              (VarE "globaladdr")
              List
              (iterexp "globaladdr" (VarE "globaladdr*"))
            )
          )
          (expfield
            (Atom TABLES)
            (IterE
              (VarE "tableaddr")
              List
              (iterexp "tableaddr" (VarE "tableaddr*"))
            )
          )
          (expfield
            (Atom MEMS)
            (IterE (VarE "memaddr") List (iterexp "memaddr" (VarE "memaddr*")))
          )
          (expfield
            (Atom EXPORTS)
            (IterE
              (VarE "exportinst")
              List
              (iterexp "exportinst" (VarE "exportinst*"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_context"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPES)
            (IterE
              (VarE "functype")
              List
              (iterexp "functype" (VarE "functype*"))
            )
          )
          (expfield
            (Atom FUNCS)
            (IterE
              (VarE "functype_F")
              List
              (iterexp "functype_F" (VarE "functype_F*"))
            )
          )
          (expfield
            (Atom GLOBALS)
            (IterE
              (VarE "globaltype")
              List
              (iterexp "globaltype" (VarE "globaltype*"))
            )
          )
          (expfield
            (Atom TABLES)
            (IterE
              (VarE "tabletype")
              List
              (iterexp "tabletype" (VarE "tabletype*"))
            )
          )
          (expfield
            (Atom MEMS)
            (IterE (VarE "memtype") List (iterexp "memtype" (VarE "memtype*")))
          )
          (expfield (Atom LOCALS) (ListE))
          (expfield (Atom LABELS) (ListE))
          (expfield (Atom RETURN) (OptE))
        )
      )
    )
    (IterPr
      (RulePr
        "wf_externtype"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "globaltype"))))
      )
      List
      (iterexp "globaltype" (VarE "globaltype*"))
    )
    (IterPr
      (RulePr
        "wf_externtype"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "functype_F"))))
      )
      List
      (iterexp "functype_F" (VarE "functype_F*"))
    )
    (IterPr
      (RulePr
        "wf_externtype"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "memtype"))))
      )
      List
      (iterexp "memtype" (VarE "memtype*"))
    )
    (IterPr
      (RulePr
        "wf_externtype"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tabletype"))))
      )
      List
      (iterexp "tabletype" (VarE "tabletype*"))
    )
  )
)
(RelD
  "Frame_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "frame"))
    (typbind "_" (VarT "context"))
  )
  (RuleD
    ""
    (ExpP "s" (VarT "store"))
    (ExpP "val*" (IterT (VarT "val") List))
    (ExpP "moduleinst" (VarT "moduleinst"))
    (ExpP "C" (VarT "context"))
    (ExpP "t*" (IterT (VarT "valtype") List))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (StrE
        (expfield
          (Atom LOCALS)
          (IterE (VarE "val") List (iterexp "val" (VarE "val*")))
        )
        (expfield (Atom MODULE) (VarE "moduleinst"))
      )
      (CompE
        (VarE "C")
        (StrE
          (expfield (Atom TYPES) (ListE))
          (expfield (Atom FUNCS) (ListE))
          (expfield (Atom GLOBALS) (ListE))
          (expfield (Atom TABLES) (ListE))
          (expfield (Atom MEMS) (ListE))
          (expfield
            (Atom LOCALS)
            (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
          )
          (expfield (Atom LABELS) (ListE))
          (expfield (Atom RETURN) (OptE))
        )
      )
    )
    (RulePr
      "Moduleinst_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "s") (VarE "moduleinst") (VarE "C"))
    )
    (IterPr
      (RulePr
        "Val_ok"
        (Infix (Seq) |- (Infix Arg : Arg))
        (TupE (VarE "val") (VarE "t"))
      )
      List
      (iterexp "t" (VarE "t*"))
      (iterexp "val" (VarE "val*"))
    )
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_frame"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom LOCALS)
            (IterE (VarE "val") List (iterexp "val" (VarE "val*")))
          )
          (expfield (Atom MODULE) (VarE "moduleinst"))
        )
      )
    )
    (RulePr
      "wf_context"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom TYPES) (ListE))
          (expfield (Atom FUNCS) (ListE))
          (expfield (Atom GLOBALS) (ListE))
          (expfield (Atom TABLES) (ListE))
          (expfield (Atom MEMS) (ListE))
          (expfield
            (Atom LOCALS)
            (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
          )
          (expfield (Atom LABELS) (ListE))
          (expfield (Atom RETURN) (OptE))
        )
      )
    )
  )
)
(RecD
  (RelD
    "Instr_ok2"
    (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
    (TupT
      (typbind "_" (VarT "store"))
      (typbind "_" (VarT "context"))
      (typbind "_" (VarT "admininstr"))
      (typbind "_" (VarT "functype"))
    )
    (RuleD
      "plain"
      (ExpP "s" (VarT "store"))
      (ExpP "C" (VarT "context"))
      (ExpP "instr" (VarT "instr"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (CallE "admininstr_instr" (ExpA (VarE "instr")))
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
            (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
          )
        )
      )
      (RulePr
        "Instr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (VarE "instr")
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
              (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
            )
          )
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr")))
    )
    (RuleD
      "label"
      (ExpP "s" (VarT "store"))
      (ExpP "C" (VarT "context"))
      (ExpP "n" (VarT "n"))
      (ExpP "instr'*" (IterT (VarT "instr") List))
      (ExpP "admininstr*" (IterT (VarT "admininstr") List))
      (ExpP "t?" (IterT (VarT "valtype") Opt))
      (ExpP "t'?" (IterT (VarT "valtype") Opt))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (IterE (VarE "instr'") List (iterexp "instr'" (VarE "instr'*")))
            (IterE
              (VarE "admininstr")
              List
              (iterexp "admininstr" (VarE "admininstr*"))
            )
          )
        )
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (ListE)
            (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (LenE (LiftE (IterE (VarE "t'") Opt (iterexp "t'" (VarE "t'?")))))
          (VarE "n")
        )
      )
      (RulePr
        "Instrs_ok2"
        (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (VarE "C")
          (IterE
            (CallE "admininstr_instr" (ExpA (VarE "instr'")))
            List
            (iterexp "instr'" (VarE "instr'*"))
          )
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (LiftE (IterE (VarE "t'") Opt (iterexp "t'" (VarE "t'?"))))
              (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
            )
          )
        )
      )
      (RulePr
        "Instrs_ok2"
        (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (CompE
            (StrE
              (expfield (Atom TYPES) (ListE))
              (expfield (Atom FUNCS) (ListE))
              (expfield (Atom GLOBALS) (ListE))
              (expfield (Atom TABLES) (ListE))
              (expfield (Atom MEMS) (ListE))
              (expfield (Atom LOCALS) (ListE))
              (expfield
                (Atom LABELS)
                (ListE (IterE (VarE "t'") Opt (iterexp "t'" (VarE "t'?"))))
              )
              (expfield (Atom RETURN) (OptE))
            )
            (VarE "C")
          )
          (IterE
            (VarE "admininstr")
            List
            (iterexp "admininstr" (VarE "admininstr*"))
          )
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (ListE)
              (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
            )
          )
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_admininstr"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
            (TupE
              (VarE "n")
              (IterE (VarE "instr'") List (iterexp "instr'" (VarE "instr'*")))
              (IterE
                (VarE "admininstr")
                List
                (iterexp "admininstr" (VarE "admininstr*"))
              )
            )
          )
        )
      )
      (RulePr
        "wf_context"
        (Seq Arg)
        (TupE
          (StrE
            (expfield (Atom TYPES) (ListE))
            (expfield (Atom FUNCS) (ListE))
            (expfield (Atom GLOBALS) (ListE))
            (expfield (Atom TABLES) (ListE))
            (expfield (Atom MEMS) (ListE))
            (expfield (Atom LOCALS) (ListE))
            (expfield
              (Atom LABELS)
              (ListE (IterE (VarE "t'") Opt (iterexp "t'" (VarE "t'?"))))
            )
            (expfield (Atom RETURN) (OptE))
          )
        )
      )
    )
    (RuleD
      "frame"
      (ExpP "s" (VarT "store"))
      (ExpP "C" (VarT "context"))
      (ExpP "n" (VarT "n"))
      (ExpP "f" (VarT "frame"))
      (ExpP "admininstr*" (IterT (VarT "admininstr") List))
      (ExpP "t?" (IterT (VarT "valtype") Opt))
      (ExpP "C'" (VarT "context"))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "n")
            (VarE "f")
            (IterE
              (VarE "admininstr")
              List
              (iterexp "admininstr" (VarE "admininstr*"))
            )
          )
        )
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (ListE)
            (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (LenE (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))))
          (VarE "n")
        )
      )
      (RulePr
        "Frame_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "s") (VarE "f") (VarE "C'"))
      )
      (RulePr
        "Expr_ok2"
        (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (CompE
            (StrE
              (expfield (Atom TYPES) (ListE))
              (expfield (Atom FUNCS) (ListE))
              (expfield (Atom GLOBALS) (ListE))
              (expfield (Atom TABLES) (ListE))
              (expfield (Atom MEMS) (ListE))
              (expfield (Atom LOCALS) (ListE))
              (expfield (Atom LABELS) (ListE))
              (expfield
                (Atom RETURN)
                (OptE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
              )
            )
            (VarE "C'")
          )
          (IterE
            (VarE "admininstr")
            List
            (iterexp "admininstr" (VarE "admininstr*"))
          )
          (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C'")))
      (RulePr
        "wf_admininstr"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
            (TupE
              (VarE "n")
              (VarE "f")
              (IterE
                (VarE "admininstr")
                List
                (iterexp "admininstr" (VarE "admininstr*"))
              )
            )
          )
        )
      )
      (RulePr
        "wf_context"
        (Seq Arg)
        (TupE
          (StrE
            (expfield (Atom TYPES) (ListE))
            (expfield (Atom FUNCS) (ListE))
            (expfield (Atom GLOBALS) (ListE))
            (expfield (Atom TABLES) (ListE))
            (expfield (Atom MEMS) (ListE))
            (expfield (Atom LOCALS) (ListE))
            (expfield (Atom LABELS) (ListE))
            (expfield
              (Atom RETURN)
              (OptE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
            )
          )
        )
      )
    )
    (RuleD
      "call_addr"
      (ExpP "s" (VarT "store"))
      (ExpP "C" (VarT "context"))
      (ExpP "funcaddr" (VarT "funcaddr"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (CaseE (Seq (Atom CALL_ADDR) Arg) (TupE (VarE "funcaddr")))
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
            (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
          )
        )
      )
      (RulePr
        "Externaddr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "funcaddr")))
          (CaseE
            (Seq (Atom FUNC) Arg)
            (TupE
              (CaseE
                (Infix Arg -> Arg)
                (TupE
                  (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                  (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
                )
              )
            )
          )
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_admininstr"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom CALL_ADDR) Arg) (TupE (VarE "funcaddr"))))
      )
      (RulePr
        "wf_externtype"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom FUNC) Arg)
            (TupE
              (CaseE
                (Infix Arg -> Arg)
                (TupE
                  (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                  (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
                )
              )
            )
          )
        )
      )
    )
    (RuleD
      "trap"
      (ExpP "s" (VarT "store"))
      (ExpP "C" (VarT "context"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (CaseE (Atom TRAP) (TupE))
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
            (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
          )
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
    )
  )
  (RelD
    "Instrs_ok2"
    (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
    (TupT
      (typbind "_" (VarT "store"))
      (typbind "_" (VarT "context"))
      (typbind "_" (IterT (VarT "admininstr") List))
      (typbind "_" (VarT "functype"))
    )
    (RuleD
      "empty"
      (ExpP "s" (VarT "store"))
      (ExpP "C" (VarT "context"))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (ListE)
        (CaseE (Infix Arg -> Arg) (TupE (ListE) (ListE)))
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    )
    (RuleD
      "instr"
      (ExpP "s" (VarT "store"))
      (ExpP "C" (VarT "context"))
      (ExpP "admininstr" (VarT "admininstr"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (ListE (VarE "admininstr"))
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
            (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
          )
        )
      )
      (RulePr
        "Instr_ok2"
        (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (VarE "C")
          (VarE "admininstr")
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
              (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
            )
          )
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_admininstr" (Seq Arg) (TupE (VarE "admininstr")))
    )
    (RuleD
      "seq"
      (ExpP "s" (VarT "store"))
      (ExpP "C" (VarT "context"))
      (ExpP "admininstr_1*" (IterT (VarT "admininstr") List))
      (ExpP "admininstr_2*" (IterT (VarT "admininstr") List))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_3*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (CatE
          (IterE
            (VarE "admininstr_1")
            List
            (iterexp "admininstr_1" (VarE "admininstr_1*"))
          )
          (IterE
            (VarE "admininstr_2")
            List
            (iterexp "admininstr_2" (VarE "admininstr_2*"))
          )
        )
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
            (IterE (VarE "t_3") List (iterexp "t_3" (VarE "t_3*")))
          )
        )
      )
      (RulePr
        "Instrs_ok2"
        (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (VarE "C")
          (IterE
            (VarE "admininstr_1")
            List
            (iterexp "admininstr_1" (VarE "admininstr_1*"))
          )
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
              (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
            )
          )
        )
      )
      (RulePr
        "Instrs_ok2"
        (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (VarE "C")
          (IterE
            (VarE "admininstr_2")
            List
            (iterexp "admininstr_2" (VarE "admininstr_2*"))
          )
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
              (IterE (VarE "t_3") List (iterexp "t_3" (VarE "t_3*")))
            )
          )
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (IterPr
        (RulePr "wf_admininstr" (Seq Arg) (TupE (VarE "admininstr_1")))
        List
        (iterexp "admininstr_1" (VarE "admininstr_1*"))
      )
      (IterPr
        (RulePr "wf_admininstr" (Seq Arg) (TupE (VarE "admininstr_2")))
        List
        (iterexp "admininstr_2" (VarE "admininstr_2*"))
      )
    )
    (RuleD
      "frame"
      (ExpP "s" (VarT "store"))
      (ExpP "C" (VarT "context"))
      (ExpP "admininstr*" (IterT (VarT "admininstr") List))
      (ExpP "t*" (IterT (VarT "valtype") List))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (IterE
          (VarE "admininstr")
          List
          (iterexp "admininstr" (VarE "admininstr*"))
        )
        (CaseE
          (Infix Arg -> Arg)
          (TupE
            (CatE
              (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
              (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
            )
            (CatE
              (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
              (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
            )
          )
        )
      )
      (RulePr
        "Instrs_ok2"
        (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (VarE "C")
          (IterE
            (VarE "admininstr")
            List
            (iterexp "admininstr" (VarE "admininstr*"))
          )
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
              (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
            )
          )
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (IterPr
        (RulePr "wf_admininstr" (Seq Arg) (TupE (VarE "admininstr")))
        List
        (iterexp "admininstr" (VarE "admininstr*"))
      )
    )
  )
  (RelD
    "Expr_ok2"
    (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
    (TupT
      (typbind "_" (VarT "store"))
      (typbind "_" (VarT "context"))
      (typbind "_" (VarT "adminexpr"))
      (typbind "_" (VarT "resulttype"))
    )
    (RuleD
      ""
      (ExpP "s" (VarT "store"))
      (ExpP "C" (VarT "context"))
      (ExpP "admininstr*" (IterT (VarT "admininstr") List))
      (ExpP "t?" (IterT (VarT "valtype") Opt))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (IterE
          (VarE "admininstr")
          List
          (iterexp "admininstr" (VarE "admininstr*"))
        )
        (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
      )
      (RulePr
        "Instrs_ok2"
        (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (VarE "C")
          (IterE
            (VarE "admininstr")
            List
            (iterexp "admininstr" (VarE "admininstr*"))
          )
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (ListE)
              (LiftE (IterE (VarE "t") Opt (iterexp "t" (VarE "t?"))))
            )
          )
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (IterPr
        (RulePr "wf_admininstr" (Seq Arg) (TupE (VarE "admininstr")))
        List
        (iterexp "admininstr" (VarE "admininstr*"))
      )
    )
  )
)
(HintD (RelH "Instr_ok2" (hint "prose" "\"%3 is valid with %4\"")))
(HintD (RelH "Instrs_ok2" (hint "prose" "\"%3 is valid with %4\"")))
(HintD (RelH "Expr_ok2" (hint "prose" "\"%3 is valid with %4\"")))
(HintD (RelH "Externaddr_ok" (hint "macro" "\"%externaddr\"")))
(RelD
  "Globalinst_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "globalinst"))
    (typbind "_" (VarT "globaltype"))
  )
  (RuleD
    ""
    (ExpP "s" (VarT "store"))
    (ExpP "mut" (VarT "mut"))
    (ExpP "t" (VarT "valtype"))
    (ExpP "val" (VarT "val"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE (Seq Arg Arg) (TupE (VarE "mut") (VarE "t")))
        )
        (expfield (Atom VALUE) (VarE "val"))
      )
      (CaseE (Seq Arg Arg) (TupE (VarE "mut") (VarE "t")))
    )
    (RulePr
      "Globaltype_ok"
      (Infix (Seq) |- (Infix Arg : (Atom OK)))
      (CaseE (Seq Arg Arg) (TupE (VarE "mut") (VarE "t")))
    )
    (RulePr
      "Val_ok"
      (Infix (Seq) |- (Infix Arg : Arg))
      (TupE (VarE "val") (VarE "t"))
    )
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
    (RulePr
      "wf_globalinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE (Seq Arg Arg) (TupE (VarE "mut") (VarE "t")))
          )
          (expfield (Atom VALUE) (VarE "val"))
        )
      )
    )
  )
)
(RelD
  "Meminst_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "meminst"))
    (typbind "_" (VarT "memtype"))
  )
  (RuleD
    ""
    (ExpP "s" (VarT "store"))
    (ExpP "n" (VarT "n"))
    (ExpP "m?" (IterT (VarT "m") Opt))
    (ExpP "b*" (IterT (VarT "byte") List))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Brack [ (Infix Arg .. Arg) ])
            (TupE
              (CaseE Arg (TupE (VarE "n")))
              (IterE
                (CaseE Arg (TupE (VarE "m")))
                Opt
                (iterexp "m" (VarE "m?"))
              )
            )
          )
        )
        (expfield
          (Atom BYTES)
          (IterE (VarE "b") List (iterexp "b" (VarE "b*")))
        )
      )
      (CaseE
        (Brack [ (Infix Arg .. Arg) ])
        (TupE
          (CaseE Arg (TupE (VarE "n")))
          (IterE (CaseE Arg (TupE (VarE "m"))) Opt (iterexp "m" (VarE "m?")))
        )
      )
    )
    (RulePr
      "Memtype_ok"
      (Infix (Seq) |- (Infix Arg : (Atom OK)))
      (CaseE
        (Brack [ (Infix Arg .. Arg) ])
        (TupE
          (CaseE Arg (TupE (VarE "n")))
          (IterE (CaseE Arg (TupE (VarE "m"))) Opt (iterexp "m" (VarE "m?")))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (LenE (IterE (VarE "b") List (iterexp "b" (VarE "b*"))))
        (BinE
          MulOp
          nat
          (VarE "n")
          (BinE MulOp nat (NumE (Nat 64)) (CallE "Ki"))
        )
      )
    )
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
    (RulePr
      "wf_meminst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Brack [ (Infix Arg .. Arg) ])
              (TupE
                (CaseE Arg (TupE (VarE "n")))
                (IterE
                  (CaseE Arg (TupE (VarE "m")))
                  Opt
                  (iterexp "m" (VarE "m?"))
                )
              )
            )
          )
          (expfield
            (Atom BYTES)
            (IterE (VarE "b") List (iterexp "b" (VarE "b*")))
          )
        )
      )
    )
    (RulePr
      "wf_limits"
      (Seq Arg)
      (TupE
        (CaseE
          (Brack [ (Infix Arg .. Arg) ])
          (TupE
            (CaseE Arg (TupE (VarE "n")))
            (IterE (CaseE Arg (TupE (VarE "m"))) Opt (iterexp "m" (VarE "m?")))
          )
        )
      )
    )
  )
)
(RelD
  "Tableinst_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "tableinst"))
    (typbind "_" (VarT "tabletype"))
  )
  (RuleD
    ""
    (ExpP "s" (VarT "store"))
    (ExpP "n" (VarT "n"))
    (ExpP "m?" (IterT (VarT "m") Opt))
    (ExpP "fa?*" (IterT (IterT (VarT "funcaddr") Opt) List))
    (ExpP "ft?*" (IterT (IterT (VarT "functype") Opt) List))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Brack [ (Infix Arg .. Arg) ])
            (TupE
              (CaseE Arg (TupE (VarE "n")))
              (IterE
                (CaseE Arg (TupE (VarE "m")))
                Opt
                (iterexp "m" (VarE "m?"))
              )
            )
          )
        )
        (expfield
          (Atom REFS)
          (IterE
            (IterE (VarE "fa") Opt (iterexp "fa" (VarE "fa?")))
            List
            (iterexp "fa?" (VarE "fa?*"))
          )
        )
      )
      (CaseE
        (Brack [ (Infix Arg .. Arg) ])
        (TupE
          (CaseE Arg (TupE (VarE "n")))
          (IterE (CaseE Arg (TupE (VarE "m"))) Opt (iterexp "m" (VarE "m?")))
        )
      )
    )
    (RulePr
      "Tabletype_ok"
      (Infix (Seq) |- (Infix Arg : (Atom OK)))
      (CaseE
        (Brack [ (Infix Arg .. Arg) ])
        (TupE
          (CaseE Arg (TupE (VarE "n")))
          (IterE (CaseE Arg (TupE (VarE "m"))) Opt (iterexp "m" (VarE "m?")))
        )
      )
    )
    (IterPr
      (IterPr
        (RulePr
          "Externaddr_ok"
          (Infix Arg |- (Infix Arg : Arg))
          (TupE
            (VarE "s")
            (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "fa")))
            (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "ft")))
          )
        )
        Opt
        (iterexp "fa" (VarE "fa?"))
        (iterexp "ft" (VarE "ft?"))
      )
      List
      (iterexp "fa?" (VarE "fa?*"))
      (iterexp "ft?" (VarE "ft?*"))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (LenE
          (IterE
            (IterE (VarE "fa") Opt (iterexp "fa" (VarE "fa?")))
            List
            (iterexp "fa?" (VarE "fa?*"))
          )
        )
        (VarE "n")
      )
    )
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
    (RulePr
      "wf_tableinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Brack [ (Infix Arg .. Arg) ])
              (TupE
                (CaseE Arg (TupE (VarE "n")))
                (IterE
                  (CaseE Arg (TupE (VarE "m")))
                  Opt
                  (iterexp "m" (VarE "m?"))
                )
              )
            )
          )
          (expfield
            (Atom REFS)
            (IterE
              (IterE (VarE "fa") Opt (iterexp "fa" (VarE "fa?")))
              List
              (iterexp "fa?" (VarE "fa?*"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_limits"
      (Seq Arg)
      (TupE
        (CaseE
          (Brack [ (Infix Arg .. Arg) ])
          (TupE
            (CaseE Arg (TupE (VarE "n")))
            (IterE (CaseE Arg (TupE (VarE "m"))) Opt (iterexp "m" (VarE "m?")))
          )
        )
      )
    )
    (IterPr
      (IterPr
        (RulePr
          "wf_externtype"
          (Seq Arg)
          (TupE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "ft"))))
        )
        Opt
        (iterexp "ft" (VarE "ft?"))
      )
      List
      (iterexp "ft?" (VarE "ft?*"))
    )
  )
)
(RelD
  "Funcinst_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "funcinst"))
    (typbind "_" (VarT "functype"))
  )
  (RuleD
    ""
    (ExpP "s" (VarT "store"))
    (ExpP "ft" (VarT "functype"))
    (ExpP "moduleinst" (VarT "moduleinst"))
    (ExpP "func" (VarT "func"))
    (ExpP "C" (VarT "context"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (StrE
        (expfield (Atom TYPE) (VarE "ft"))
        (expfield (Atom MODULE) (VarE "moduleinst"))
        (expfield (Atom CODE) (VarE "func"))
      )
      (VarE "ft")
    )
    (RulePr "Functype_ok" (Infix (Seq) |- (Infix Arg : (Atom OK))) (VarE "ft"))
    (RulePr
      "Moduleinst_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "s") (VarE "moduleinst") (VarE "C"))
    )
    (RulePr
      "Func_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "C") (VarE "func") (VarE "ft"))
    )
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_funcinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom TYPE) (VarE "ft"))
          (expfield (Atom MODULE) (VarE "moduleinst"))
          (expfield (Atom CODE) (VarE "func"))
        )
      )
    )
  )
)
(RelD
  "Store_ok"
  (Infix (Seq) |- (Infix Arg : (Atom OK)))
  (VarT "store")
  (RuleD
    ""
    (ExpP "s" (VarT "store"))
    (ExpP "globalinst*" (IterT (VarT "globalinst") List))
    (ExpP "globaltype*" (IterT (VarT "globaltype") List))
    (ExpP "meminst*" (IterT (VarT "meminst") List))
    (ExpP "memtype*" (IterT (VarT "memtype") List))
    (ExpP "tableinst*" (IterT (VarT "tableinst") List))
    (ExpP "tabletype*" (IterT (VarT "tabletype") List))
    (ExpP "funcinst*" (IterT (VarT "funcinst") List))
    (ExpP "functype*" (IterT (VarT "functype") List))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (VarE "s")
    (IterPr
      (RulePr
        "Globalinst_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "s") (VarE "globalinst") (VarE "globaltype"))
      )
      List
      (iterexp "globalinst" (VarE "globalinst*"))
      (iterexp "globaltype" (VarE "globaltype*"))
    )
    (IterPr
      (RulePr
        "Meminst_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "s") (VarE "meminst") (VarE "memtype"))
      )
      List
      (iterexp "meminst" (VarE "meminst*"))
      (iterexp "memtype" (VarE "memtype*"))
    )
    (IterPr
      (RulePr
        "Tableinst_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "s") (VarE "tableinst") (VarE "tabletype"))
      )
      List
      (iterexp "tableinst" (VarE "tableinst*"))
      (iterexp "tabletype" (VarE "tabletype*"))
    )
    (IterPr
      (RulePr
        "Funcinst_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "s") (VarE "funcinst") (VarE "functype"))
      )
      List
      (iterexp "funcinst" (VarE "funcinst*"))
      (iterexp "functype" (VarE "functype*"))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "s")
        (StrE
          (expfield
            (Atom FUNCS)
            (IterE
              (VarE "funcinst")
              List
              (iterexp "funcinst" (VarE "funcinst*"))
            )
          )
          (expfield
            (Atom GLOBALS)
            (IterE
              (VarE "globalinst")
              List
              (iterexp "globalinst" (VarE "globalinst*"))
            )
          )
          (expfield
            (Atom TABLES)
            (IterE
              (VarE "tableinst")
              List
              (iterexp "tableinst" (VarE "tableinst*"))
            )
          )
          (expfield
            (Atom MEMS)
            (IterE (VarE "meminst") List (iterexp "meminst" (VarE "meminst*")))
          )
        )
      )
    )
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
    (IterPr
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "memtype")))
      List
      (iterexp "memtype" (VarE "memtype*"))
    )
    (IterPr
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "tabletype")))
      List
      (iterexp "tabletype" (VarE "tabletype*"))
    )
    (RulePr
      "wf_store"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom FUNCS)
            (IterE
              (VarE "funcinst")
              List
              (iterexp "funcinst" (VarE "funcinst*"))
            )
          )
          (expfield
            (Atom GLOBALS)
            (IterE
              (VarE "globalinst")
              List
              (iterexp "globalinst" (VarE "globalinst*"))
            )
          )
          (expfield
            (Atom TABLES)
            (IterE
              (VarE "tableinst")
              List
              (iterexp "tableinst" (VarE "tableinst*"))
            )
          )
          (expfield
            (Atom MEMS)
            (IterE (VarE "meminst") List (iterexp "meminst" (VarE "meminst*")))
          )
        )
      )
    )
  )
)
(RelD
  "Extend_globalinst"
  (Seq Arg (Atom <=) Arg)
  (TupT (typbind "_" (VarT "globalinst")) (typbind "_" (VarT "globalinst")))
  (RuleD
    ""
    (ExpP "mut" (VarT "mut"))
    (ExpP "t" (VarT "valtype"))
    (ExpP "val" (VarT "val"))
    (ExpP "val'" (VarT "val"))
    (Seq Arg (Atom <=) Arg)
    (TupE
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE (Seq Arg Arg) (TupE (VarE "mut") (VarE "t")))
        )
        (expfield (Atom VALUE) (VarE "val"))
      )
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE (Seq Arg Arg) (TupE (VarE "mut") (VarE "t")))
        )
        (expfield (Atom VALUE) (VarE "val'"))
      )
    )
    (IfPr
      (BinE
        OrOp
        bool
        (CmpE EqOp bool (VarE "mut") (OptE (CaseE (Atom MUT) (TupE))))
        (CmpE EqOp bool (VarE "val") (VarE "val'"))
      )
    )
    (RulePr
      "wf_globalinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE (Seq Arg Arg) (TupE (VarE "mut") (VarE "t")))
          )
          (expfield (Atom VALUE) (VarE "val"))
        )
      )
    )
    (RulePr
      "wf_globalinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE (Seq Arg Arg) (TupE (VarE "mut") (VarE "t")))
          )
          (expfield (Atom VALUE) (VarE "val'"))
        )
      )
    )
  )
)
(RelD
  "Extend_meminst"
  (Seq Arg (Atom <=) Arg)
  (TupT (typbind "_" (VarT "meminst")) (typbind "_" (VarT "meminst")))
  (RuleD
    ""
    (ExpP "n" (VarT "n"))
    (ExpP "m?" (IterT (VarT "m") Opt))
    (ExpP "b*" (IterT (VarT "byte") List))
    (ExpP "n'" (VarT "n"))
    (ExpP "b'*" (IterT (VarT "byte") List))
    (Seq Arg (Atom <=) Arg)
    (TupE
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Brack [ (Infix Arg .. Arg) ])
            (TupE
              (CaseE Arg (TupE (VarE "n")))
              (IterE
                (CaseE Arg (TupE (VarE "m")))
                Opt
                (iterexp "m" (VarE "m?"))
              )
            )
          )
        )
        (expfield
          (Atom BYTES)
          (IterE (VarE "b") List (iterexp "b" (VarE "b*")))
        )
      )
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Brack [ (Infix Arg .. Arg) ])
            (TupE
              (CaseE Arg (TupE (VarE "n'")))
              (IterE
                (CaseE Arg (TupE (VarE "m")))
                Opt
                (iterexp "m" (VarE "m?"))
              )
            )
          )
        )
        (expfield
          (Atom BYTES)
          (IterE (VarE "b'") List (iterexp "b'" (VarE "b'*")))
        )
      )
    )
    (IfPr (CmpE LeOp nat (VarE "n") (VarE "n'")))
    (IfPr
      (CmpE
        LeOp
        nat
        (LenE (IterE (VarE "b") List (iterexp "b" (VarE "b*"))))
        (LenE (IterE (VarE "b'") List (iterexp "b'" (VarE "b'*"))))
      )
    )
    (RulePr
      "wf_meminst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Brack [ (Infix Arg .. Arg) ])
              (TupE
                (CaseE Arg (TupE (VarE "n")))
                (IterE
                  (CaseE Arg (TupE (VarE "m")))
                  Opt
                  (iterexp "m" (VarE "m?"))
                )
              )
            )
          )
          (expfield
            (Atom BYTES)
            (IterE (VarE "b") List (iterexp "b" (VarE "b*")))
          )
        )
      )
    )
    (RulePr
      "wf_meminst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Brack [ (Infix Arg .. Arg) ])
              (TupE
                (CaseE Arg (TupE (VarE "n'")))
                (IterE
                  (CaseE Arg (TupE (VarE "m")))
                  Opt
                  (iterexp "m" (VarE "m?"))
                )
              )
            )
          )
          (expfield
            (Atom BYTES)
            (IterE (VarE "b'") List (iterexp "b'" (VarE "b'*")))
          )
        )
      )
    )
  )
)
(RelD
  "Extend_tableinst"
  (Seq Arg (Atom <=) Arg)
  (TupT (typbind "_" (VarT "tableinst")) (typbind "_" (VarT "tableinst")))
  (RuleD
    ""
    (ExpP "n" (VarT "n"))
    (ExpP "m?" (IterT (VarT "m") Opt))
    (ExpP "ref*" (IterT (VarT "funcaddr") List))
    (ExpP "n'" (VarT "n"))
    (ExpP "ref'*" (IterT (VarT "funcaddr") List))
    (Seq Arg (Atom <=) Arg)
    (TupE
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Brack [ (Infix Arg .. Arg) ])
            (TupE
              (CaseE Arg (TupE (VarE "n")))
              (IterE
                (CaseE Arg (TupE (VarE "m")))
                Opt
                (iterexp "m" (VarE "m?"))
              )
            )
          )
        )
        (expfield
          (Atom REFS)
          (IterE (OptE (VarE "ref")) List (iterexp "ref" (VarE "ref*")))
        )
      )
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Brack [ (Infix Arg .. Arg) ])
            (TupE
              (CaseE Arg (TupE (VarE "n'")))
              (IterE
                (CaseE Arg (TupE (VarE "m")))
                Opt
                (iterexp "m" (VarE "m?"))
              )
            )
          )
        )
        (expfield
          (Atom REFS)
          (IterE (OptE (VarE "ref'")) List (iterexp "ref'" (VarE "ref'*")))
        )
      )
    )
    (IfPr (CmpE LeOp nat (VarE "n") (VarE "n'")))
    (IfPr
      (CmpE
        LeOp
        nat
        (LenE (IterE (VarE "ref") List (iterexp "ref" (VarE "ref*"))))
        (LenE (IterE (VarE "ref'") List (iterexp "ref'" (VarE "ref'*"))))
      )
    )
    (RulePr
      "wf_tableinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Brack [ (Infix Arg .. Arg) ])
              (TupE
                (CaseE Arg (TupE (VarE "n")))
                (IterE
                  (CaseE Arg (TupE (VarE "m")))
                  Opt
                  (iterexp "m" (VarE "m?"))
                )
              )
            )
          )
          (expfield
            (Atom REFS)
            (IterE (OptE (VarE "ref")) List (iterexp "ref" (VarE "ref*")))
          )
        )
      )
    )
    (RulePr
      "wf_tableinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Brack [ (Infix Arg .. Arg) ])
              (TupE
                (CaseE Arg (TupE (VarE "n'")))
                (IterE
                  (CaseE Arg (TupE (VarE "m")))
                  Opt
                  (iterexp "m" (VarE "m?"))
                )
              )
            )
          )
          (expfield
            (Atom REFS)
            (IterE (OptE (VarE "ref'")) List (iterexp "ref'" (VarE "ref'*")))
          )
        )
      )
    )
  )
)
(RelD
  "Extend_funcinst"
  (Seq Arg (Atom <=) Arg)
  (TupT (typbind "_" (VarT "funcinst")) (typbind "_" (VarT "funcinst")))
  (RuleD
    ""
    (ExpP "ft" (VarT "functype"))
    (ExpP "mm" (VarT "moduleinst"))
    (ExpP "fc" (VarT "func"))
    (Seq Arg (Atom <=) Arg)
    (TupE
      (StrE
        (expfield (Atom TYPE) (VarE "ft"))
        (expfield (Atom MODULE) (VarE "mm"))
        (expfield (Atom CODE) (VarE "fc"))
      )
      (StrE
        (expfield (Atom TYPE) (VarE "ft"))
        (expfield (Atom MODULE) (VarE "mm"))
        (expfield (Atom CODE) (VarE "fc"))
      )
    )
    (RulePr
      "wf_funcinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom TYPE) (VarE "ft"))
          (expfield (Atom MODULE) (VarE "mm"))
          (expfield (Atom CODE) (VarE "fc"))
        )
      )
    )
  )
)
(RelD
  "Extend_store"
  (Seq Arg (Atom <=) Arg)
  (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "store")))
  (RuleD
    ""
    (ExpP "s" (VarT "store"))
    (ExpP "s'" (VarT "store"))
    (Seq Arg (Atom <=) Arg)
    (TupE (VarE "s") (VarE "s'"))
    (IterPr
      (RulePr
        "Extend_globalinst"
        (Seq Arg (Atom <=) Arg)
        (TupE
          (IdxE (DotE (VarE "s") (Atom GLOBALS)) (VarE "a"))
          (IdxE (DotE (VarE "s'") (Atom GLOBALS)) (VarE "a"))
        )
      )
      (ListN (LenE (DotE (VarE "s") (Atom GLOBALS))) "a")
    )
    (IterPr
      (RulePr
        "Extend_meminst"
        (Seq Arg (Atom <=) Arg)
        (TupE
          (IdxE (DotE (VarE "s") (Atom MEMS)) (VarE "a"))
          (IdxE (DotE (VarE "s'") (Atom MEMS)) (VarE "a"))
        )
      )
      (ListN (LenE (DotE (VarE "s") (Atom MEMS))) "a")
    )
    (IterPr
      (RulePr
        "Extend_tableinst"
        (Seq Arg (Atom <=) Arg)
        (TupE
          (IdxE (DotE (VarE "s") (Atom TABLES)) (VarE "a"))
          (IdxE (DotE (VarE "s'") (Atom TABLES)) (VarE "a"))
        )
      )
      (ListN (LenE (DotE (VarE "s") (Atom TABLES))) "a")
    )
    (IterPr
      (RulePr
        "Extend_funcinst"
        (Seq Arg (Atom <=) Arg)
        (TupE
          (IdxE (DotE (VarE "s") (Atom FUNCS)) (VarE "a"))
          (IdxE (DotE (VarE "s'") (Atom FUNCS)) (VarE "a"))
        )
      )
      (ListN (LenE (DotE (VarE "s") (Atom FUNCS))) "a")
    )
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s'")))
  )
)
(RelD
  "State_ok"
  (Infix (Seq) |- (Infix Arg : Arg))
  (TupT (typbind "_" (VarT "state")) (typbind "_" (VarT "context")))
  (RuleD
    ""
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "C" (VarT "context"))
    (Infix (Seq) |- (Infix Arg : Arg))
    (TupE (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))) (VarE "C"))
    (RulePr "Store_ok" (Infix (Seq) |- (Infix Arg : (Atom OK))) (VarE "s"))
    (RulePr
      "Frame_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "s") (VarE "f") (VarE "C"))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_state"
      (Seq Arg)
      (TupE (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    )
  )
)
(RelD
  "Config_ok"
  (Infix (Seq) |- (Infix Arg : Arg))
  (TupT (typbind "_" (VarT "config")) (typbind "_" (VarT "resulttype")))
  (RuleD
    ""
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "admininstr*" (IterT (VarT "admininstr") List))
    (ExpP "t?" (IterT (VarT "valtype") Opt))
    (ExpP "C" (VarT "context"))
    (Infix (Seq) |- (Infix Arg : Arg))
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f")))
          (IterE
            (VarE "admininstr")
            List
            (iterexp "admininstr" (VarE "admininstr*"))
          )
        )
      )
      (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
    )
    (RulePr
      "State_ok"
      (Infix (Seq) |- (Infix Arg : Arg))
      (TupE (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))) (VarE "C"))
    )
    (RulePr
      "Expr_ok2"
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (IterE
          (VarE "admininstr")
          List
          (iterexp "admininstr" (VarE "admininstr*"))
        )
        (IterE (VarE "t") Opt (iterexp "t" (VarE "t?")))
      )
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Infix Arg ; Arg)
          (TupE
            (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f")))
            (IterE
              (VarE "admininstr")
              List
              (iterexp "admininstr" (VarE "admininstr*"))
            )
          )
        )
      )
    )
    (RulePr
      "wf_state"
      (Seq Arg)
      (TupE (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    )
  )
)
(GramD
  "Bbyte"
  (VarT "byte")
  (ProdD
    (ExpP "<implicit-prod-result>" nat)
    (AttrG (VarE "<implicit-prod-result>") (RangeG (NumG 0x00) (NumG 0xFF)))
    (CaseE Arg (TupE (VarE "<implicit-prod-result>")))
  )
)
(RecD
  (GramD
    "BuN"
    (ExpP "N" (VarT "N"))
    (VarT "uN")
    (ProdD
      (ExpP "n" (VarT "n"))
      (AttrG (CaseE Arg (TupE (VarE "n"))) (VarG "Bbyte"))
      (CaseE Arg (TupE (VarE "n")))
      (IfPr
        (BinE
          AndOp
          bool
          (CmpE
            LtOp
            nat
            (VarE "n")
            (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7)))
          )
          (CmpE LtOp nat (VarE "n") (BinE PowOp nat (NumE (Nat 2)) (VarE "N")))
        )
      )
    )
    (ProdD
      (ExpP "m" (VarT "m"))
      (ExpP "n" (VarT "n"))
      (SeqG
        (SeqG (AttrG (CaseE Arg (TupE (VarE "n"))) (VarG "Bbyte")))
        (SeqG
          (AttrG
            (CaseE Arg (TupE (VarE "m")))
            (VarG
              "BuN"
              (ExpA
                (CvtE
                  int
                  nat
                  (BinE
                    SubOp
                    int
                    (CvtE nat int (VarE "N"))
                    (CvtE nat int (NumE (Nat 7)))
                  )
                )
              )
            )
          )
        )
      )
      (CaseE
        Arg
        (TupE
          (BinE
            AddOp
            nat
            (BinE
              MulOp
              nat
              (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7)))
              (VarE "m")
            )
            (CvtE
              int
              nat
              (BinE
                SubOp
                int
                (CvtE nat int (VarE "n"))
                (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7))))
              )
            )
          )
        )
      )
      (IfPr
        (BinE
          AndOp
          bool
          (CmpE
            GeOp
            nat
            (VarE "n")
            (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7)))
          )
          (CmpE GtOp nat (VarE "N") (NumE (Nat 7)))
        )
      )
    )
  )
)
(GramD
  "Bu32"
  (VarT "u32")
  (ProdD
    (ExpP "<implicit-prod-result>" (VarT "uN"))
    (AttrG (VarE "<implicit-prod-result>") (VarG "BuN" (ExpA (NumE (Nat 32)))))
    (VarE "<implicit-prod-result>")
  )
)
(GramD
  "Blist"
  (TypP "el")
  (GramP "BX" (VarT "el"))
  (IterT (VarT "el") List)
  (ProdD
    (ExpP "n" (VarT "n"))
    (ExpP "el*" (IterT (VarT "el") List))
    (SeqG
      (SeqG (AttrG (CaseE Arg (TupE (VarE "n"))) (VarG "Bu32")))
      (SeqG
        (IterG
          (AttrG (VarE "el") (VarG "BX"))
          (ListN (VarE "n"))
          (iterexp "el" (VarE "el*"))
        )
      )
    )
    (IterE (VarE "el") (ListN (VarE "n")) (iterexp "el" (VarE "el*")))
  )
)
(HintD (GramH "BuN" (hint "show" "Bu#%")))
(RecD
  (GramD
    "BsN"
    (ExpP "N" (VarT "N"))
    (VarT "sN")
    (ProdD
      (ExpP "n" (VarT "n"))
      (AttrG (CaseE Arg (TupE (VarE "n"))) (VarG "Bbyte"))
      (CaseE Arg (TupE (CvtE nat int (VarE "n"))))
      (IfPr
        (BinE
          AndOp
          bool
          (CmpE
            LtOp
            nat
            (VarE "n")
            (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 6)))
          )
          (CmpE
            LtOp
            nat
            (VarE "n")
            (BinE
              PowOp
              nat
              (NumE (Nat 2))
              (CvtE
                int
                nat
                (BinE
                  SubOp
                  int
                  (CvtE nat int (VarE "N"))
                  (CvtE nat int (NumE (Nat 1)))
                )
              )
            )
          )
        )
      )
    )
    (ProdD
      (ExpP "n" (VarT "n"))
      (AttrG (CaseE Arg (TupE (VarE "n"))) (VarG "Bbyte"))
      (CaseE
        Arg
        (TupE
          (BinE
            SubOp
            int
            (CvtE nat int (VarE "n"))
            (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7))))
          )
        )
      )
      (IfPr
        (BinE
          AndOp
          bool
          (BinE
            AndOp
            bool
            (CmpE
              LeOp
              nat
              (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 6)))
              (VarE "n")
            )
            (CmpE
              LtOp
              nat
              (VarE "n")
              (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7)))
            )
          )
          (CmpE
            GeOp
            int
            (CvtE nat int (VarE "n"))
            (BinE
              SubOp
              int
              (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7))))
              (CvtE
                nat
                int
                (BinE
                  PowOp
                  nat
                  (NumE (Nat 2))
                  (CvtE
                    int
                    nat
                    (BinE
                      SubOp
                      int
                      (CvtE nat int (VarE "N"))
                      (CvtE nat int (NumE (Nat 1)))
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    (ProdD
      (ExpP "i" (VarT "sN"))
      (ExpP "n" (VarT "n"))
      (SeqG
        (SeqG (AttrG (CaseE Arg (TupE (VarE "n"))) (VarG "Bbyte")))
        (SeqG
          (AttrG
            (VarE "i")
            (VarG
              "BsN"
              (ExpA
                (CvtE
                  int
                  nat
                  (BinE
                    SubOp
                    int
                    (CvtE nat int (VarE "N"))
                    (CvtE nat int (NumE (Nat 7)))
                  )
                )
              )
            )
          )
        )
      )
      (CaseE
        Arg
        (TupE
          (CvtE
            nat
            int
            (BinE
              AddOp
              nat
              (BinE
                MulOp
                nat
                (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7)))
                (CvtE int nat (ProjE (CallE "proj_sN_0" (ExpA (VarE "i"))) 0))
              )
              (CvtE
                int
                nat
                (BinE
                  SubOp
                  int
                  (CvtE nat int (VarE "n"))
                  (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7))))
                )
              )
            )
          )
        )
      )
      (IfPr
        (BinE
          AndOp
          bool
          (CmpE
            GeOp
            nat
            (VarE "n")
            (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7)))
          )
          (CmpE GtOp nat (VarE "N") (NumE (Nat 7)))
        )
      )
    )
  )
)
(HintD (GramH "BsN" (hint "show" "Bs#%")))
(GramD
  "BiN"
  (ExpP "N" (VarT "N"))
  (VarT "iN")
  (ProdD
    (ExpP "i" (VarT "sN"))
    (AttrG (VarE "i") (VarG "BsN" (ExpA (VarE "N"))))
    (CaseE
      Arg
      (TupE
        (CallE
          "inv_signed_"
          (ExpA (VarE "N"))
          (ExpA (ProjE (CallE "proj_sN_0" (ExpA (VarE "i"))) 0))
        )
      )
    )
  )
)
(HintD (GramH "BiN" (hint "show" "Bi#%")))
(GramD
  "BfN"
  (ExpP "N" (VarT "N"))
  (VarT "fN")
  (ProdD
    (ExpP "b*" (IterT (VarT "byte") List))
    (AttrG
      (IterE (VarE "b") List (iterexp "b" (VarE "b*")))
      (IterG
        (VarG "Bbyte")
        (ListN
          (CvtE
            rat
            nat
            (BinE
              DivOp
              rat
              (CvtE nat rat (VarE "N"))
              (CvtE nat rat (NumE (Nat 8)))
            )
          )
        )
      )
    )
    (CallE
      "inv_fbytes_"
      (ExpA (VarE "N"))
      (ExpA (IterE (VarE "b") List (iterexp "b" (VarE "b*"))))
    )
  )
)
(HintD (GramH "BfN" (hint "show" "Bf#%")))
(GramD
  "Bu64"
  (VarT "u64")
  (ProdD
    (ExpP "<implicit-prod-result>" (VarT "uN"))
    (AttrG (VarE "<implicit-prod-result>") (VarG "BuN" (ExpA (NumE (Nat 64)))))
    (VarE "<implicit-prod-result>")
  )
)
(GramD
  "Bi32"
  (VarT "i32")
  (ProdD
    (ExpP "<implicit-prod-result>" (VarT "iN"))
    (AttrG (VarE "<implicit-prod-result>") (VarG "BiN" (ExpA (NumE (Nat 32)))))
    (VarE "<implicit-prod-result>")
  )
)
(GramD
  "Bi64"
  (VarT "i64")
  (ProdD
    (ExpP "<implicit-prod-result>" (VarT "iN"))
    (AttrG (VarE "<implicit-prod-result>") (VarG "BiN" (ExpA (NumE (Nat 64)))))
    (VarE "<implicit-prod-result>")
  )
)
(GramD
  "Bf32"
  (VarT "f32")
  (ProdD
    (ExpP "<implicit-prod-result>" (VarT "fN"))
    (AttrG (VarE "<implicit-prod-result>") (VarG "BfN" (ExpA (NumE (Nat 32)))))
    (VarE "<implicit-prod-result>")
  )
)
(GramD
  "Bf64"
  (VarT "f64")
  (ProdD
    (ExpP "<implicit-prod-result>" (VarT "fN"))
    (AttrG (VarE "<implicit-prod-result>") (VarG "BfN" (ExpA (NumE (Nat 64)))))
    (VarE "<implicit-prod-result>")
  )
)
(GramD
  "Bname"
  (VarT "name")
  (ProdD
    (ExpP "name" (VarT "name"))
    (ExpP "b*" (IterT (VarT "byte") List))
    (AttrG
      (IterE (VarE "b") List (iterexp "b" (VarE "b*")))
      (VarG "Blist" (TypA (VarT "byte")) (GramA (VarG "Bbyte")))
    )
    (VarE "name")
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE
          "utf8"
          (ExpA (ProjE (CallE "proj_name_0" (ExpA (VarE "name"))) 0))
        )
        (IterE (VarE "b") List (iterexp "b" (VarE "b*")))
      )
    )
  )
)
(GramD
  "Btypeidx"
  (VarT "typeidx")
  (ProdD (ExpP "x" (VarT "idx")) (AttrG (VarE "x") (VarG "Bu32")) (VarE "x"))
)
(GramD
  "Bfuncidx"
  (VarT "funcidx")
  (ProdD (ExpP "x" (VarT "idx")) (AttrG (VarE "x") (VarG "Bu32")) (VarE "x"))
)
(GramD
  "Bglobalidx"
  (VarT "globalidx")
  (ProdD (ExpP "x" (VarT "idx")) (AttrG (VarE "x") (VarG "Bu32")) (VarE "x"))
)
(GramD
  "Btableidx"
  (VarT "tableidx")
  (ProdD (ExpP "x" (VarT "idx")) (AttrG (VarE "x") (VarG "Bu32")) (VarE "x"))
)
(GramD
  "Bmemidx"
  (VarT "memidx")
  (ProdD (ExpP "x" (VarT "idx")) (AttrG (VarE "x") (VarG "Bu32")) (VarE "x"))
)
(GramD
  "Blocalidx"
  (VarT "localidx")
  (ProdD (ExpP "x" (VarT "idx")) (AttrG (VarE "x") (VarG "Bu32")) (VarE "x"))
)
(GramD
  "Blabelidx"
  (VarT "labelidx")
  (ProdD (ExpP "x" (VarT "idx")) (AttrG (VarE "x") (VarG "Bu32")) (VarE "x"))
)
(GramD
  "Bexternidx"
  (VarT "externidx")
  (ProdD
    (ExpP "x" (VarT "idx"))
    (SeqG (SeqG (NumG 0x00)) (SeqG (AttrG (VarE "x") (VarG "Bfuncidx"))))
    (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "x")))
  )
  (ProdD
    (ExpP "x" (VarT "idx"))
    (SeqG (SeqG (NumG 0x01)) (SeqG (AttrG (VarE "x") (VarG "Btableidx"))))
    (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "x")))
  )
  (ProdD
    (ExpP "x" (VarT "idx"))
    (SeqG (SeqG (NumG 0x02)) (SeqG (AttrG (VarE "x") (VarG "Bmemidx"))))
    (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "x")))
  )
  (ProdD
    (ExpP "x" (VarT "idx"))
    (SeqG (SeqG (NumG 0x03)) (SeqG (AttrG (VarE "x") (VarG "Bglobalidx"))))
    (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "x")))
  )
)
(GramD
  "Bvaltype"
  (VarT "valtype")
  (ProdD (NumG 0x7F) (CaseE (Atom I32) (TupE)))
  (ProdD (NumG 0x7E) (CaseE (Atom I64) (TupE)))
  (ProdD (NumG 0x7D) (CaseE (Atom F32) (TupE)))
  (ProdD (NumG 0x7C) (CaseE (Atom F64) (TupE)))
)
(GramD
  "Bresulttype"
  (IterT (VarT "valtype") List)
  (ProdD
    (ExpP "t*" (IterT (VarT "valtype") List))
    (AttrG
      (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
      (VarG "Blist" (TypA (VarT "valtype")) (GramA (VarG "Bvaltype")))
    )
    (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
  )
)
(GramD
  "Bfunctype"
  (VarT "functype")
  (ProdD
    (ExpP "t_1*" (IterT (VarT "valtype") List))
    (ExpP "t_2*" (IterT (VarT "valtype") List))
    (SeqG
      (SeqG (NumG 0x60))
      (SeqG
        (AttrG
          (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
          (VarG "Bresulttype")
        )
      )
      (SeqG
        (AttrG
          (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
          (VarG "Bresulttype")
        )
      )
    )
    (CaseE
      (Infix Arg -> Arg)
      (TupE
        (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
        (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
      )
    )
  )
)
(GramD
  "Bmut"
  (VarT "mut")
  (ProdD (NumG 0x00) (OptE))
  (ProdD (NumG 0x01) (OptE (CaseE (Atom MUT) (TupE))))
)
(GramD
  "Blimits"
  (VarT "limits")
  (ProdD
    (ExpP "n" (VarT "n"))
    (SeqG
      (SeqG (NumG 0x00))
      (SeqG (AttrG (CaseE Arg (TupE (VarE "n"))) (VarG "Bu32")))
    )
    (CaseE
      (Brack [ (Infix Arg .. Arg) ])
      (TupE (CaseE Arg (TupE (VarE "n"))) (OptE))
    )
  )
  (ProdD
    (ExpP "n" (VarT "n"))
    (ExpP "m" (VarT "m"))
    (SeqG
      (SeqG (NumG 0x01))
      (SeqG (AttrG (CaseE Arg (TupE (VarE "n"))) (VarG "Bu32")))
      (SeqG (AttrG (CaseE Arg (TupE (VarE "m"))) (VarG "Bu32")))
    )
    (CaseE
      (Brack [ (Infix Arg .. Arg) ])
      (TupE (CaseE Arg (TupE (VarE "n"))) (OptE (CaseE Arg (TupE (VarE "m")))))
    )
  )
)
(GramD
  "Bglobaltype"
  (VarT "globaltype")
  (ProdD
    (ExpP "mut" (VarT "mut"))
    (ExpP "t" (VarT "valtype"))
    (SeqG
      (SeqG (AttrG (VarE "t") (VarG "Bvaltype")))
      (SeqG (AttrG (VarE "mut") (VarG "Bmut")))
    )
    (CaseE (Seq Arg Arg) (TupE (VarE "mut") (VarE "t")))
  )
)
(GramD
  "Btabletype"
  (VarT "tabletype")
  (ProdD
    (ExpP "lim" (VarT "limits"))
    (SeqG (SeqG (NumG 0x70)) (SeqG (AttrG (VarE "lim") (VarG "Blimits"))))
    (VarE "lim")
  )
)
(GramD
  "Bmemtype"
  (VarT "memtype")
  (ProdD
    (ExpP "lim" (VarT "limits"))
    (AttrG (VarE "lim") (VarG "Blimits"))
    (VarE "lim")
  )
)
(GramD
  "Bexterntype"
  (VarT "externtype")
  (ProdD
    (ExpP "ft" (VarT "functype"))
    (SeqG (SeqG (NumG 0x00)) (SeqG (AttrG (VarE "ft") (VarG "Bfunctype"))))
    (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "ft")))
  )
  (ProdD
    (ExpP "tt" (VarT "tabletype"))
    (SeqG (SeqG (NumG 0x01)) (SeqG (AttrG (VarE "tt") (VarG "Btabletype"))))
    (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tt")))
  )
  (ProdD
    (ExpP "mt" (VarT "memtype"))
    (SeqG (SeqG (NumG 0x02)) (SeqG (AttrG (VarE "mt") (VarG "Bmemtype"))))
    (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "mt")))
  )
  (ProdD
    (ExpP "gt" (VarT "globaltype"))
    (SeqG (SeqG (NumG 0x03)) (SeqG (AttrG (VarE "gt") (VarG "Bglobaltype"))))
    (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "gt")))
  )
)
(GramD
  "Bblocktype"
  (VarT "blocktype")
  (ProdD (NumG 0x40) (OptE))
  (ProdD
    (ExpP "t" (VarT "valtype"))
    (AttrG (VarE "t") (VarG "Bvaltype"))
    (OptE (VarE "t"))
  )
)
(GramD
  "Bmemarg"
  (VarT "memarg")
  (ProdD
    (ExpP "n" (VarT "n"))
    (ExpP "m" (VarT "m"))
    (SeqG
      (SeqG (AttrG (CaseE Arg (TupE (VarE "n"))) (VarG "Bu32")))
      (SeqG (AttrG (CaseE Arg (TupE (VarE "m"))) (VarG "Bu32")))
    )
    (StrE
      (expfield (Atom ALIGN) (CaseE Arg (TupE (VarE "n"))))
      (expfield (Atom OFFSET) (CaseE Arg (TupE (VarE "m"))))
    )
  )
)
(RecD
  (GramD
    "Binstr"
    (VarT "instr")
    (ProdD (NumG 0x00) (CaseE (Atom UNREACHABLE) (TupE)))
    (ProdD (NumG 0x01) (CaseE (Atom NOP) (TupE)))
    (ProdD
      (ExpP "bt" (VarT "blocktype"))
      (ExpP "in*" (IterT (VarT "instr") List))
      (SeqG
        (SeqG (NumG 0x02))
        (SeqG (AttrG (VarE "bt") (VarG "Bblocktype")))
        (SeqG
          (IterG
            (AttrG (VarE "in") (VarG "Binstr"))
            List
            (iterexp "in" (VarE "in*"))
          )
        )
        (SeqG (NumG 0x0B))
      )
      (CaseE
        (Seq (Atom BLOCK) Arg Arg)
        (TupE (VarE "bt") (IterE (VarE "in") List (iterexp "in" (VarE "in*"))))
      )
    )
    (ProdD
      (ExpP "bt" (VarT "blocktype"))
      (ExpP "in*" (IterT (VarT "instr") List))
      (SeqG
        (SeqG (NumG 0x03))
        (SeqG (AttrG (VarE "bt") (VarG "Bblocktype")))
        (SeqG
          (IterG
            (AttrG (VarE "in") (VarG "Binstr"))
            List
            (iterexp "in" (VarE "in*"))
          )
        )
        (SeqG (NumG 0x0B))
      )
      (CaseE
        (Seq (Atom LOOP) Arg Arg)
        (TupE (VarE "bt") (IterE (VarE "in") List (iterexp "in" (VarE "in*"))))
      )
    )
    (ProdD
      (ExpP "bt" (VarT "blocktype"))
      (ExpP "in*" (IterT (VarT "instr") List))
      (SeqG
        (SeqG (NumG 0x04))
        (SeqG (AttrG (VarE "bt") (VarG "Bblocktype")))
        (SeqG
          (IterG
            (AttrG (VarE "in") (VarG "Binstr"))
            List
            (iterexp "in" (VarE "in*"))
          )
        )
        (SeqG (NumG 0x0B))
      )
      (CaseE
        (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
        (TupE
          (VarE "bt")
          (IterE (VarE "in") List (iterexp "in" (VarE "in*")))
          (ListE)
        )
      )
    )
    (ProdD
      (ExpP "bt" (VarT "blocktype"))
      (ExpP "in_1*" (IterT (VarT "instr") List))
      (ExpP "in_2*" (IterT (VarT "instr") List))
      (SeqG
        (SeqG (NumG 0x04))
        (SeqG (AttrG (VarE "bt") (VarG "Bblocktype")))
        (SeqG
          (IterG
            (AttrG (VarE "in_1") (VarG "Binstr"))
            List
            (iterexp "in_1" (VarE "in_1*"))
          )
        )
        (SeqG (NumG 0x05))
        (SeqG
          (IterG
            (AttrG (VarE "in_2") (VarG "Binstr"))
            List
            (iterexp "in_2" (VarE "in_2*"))
          )
        )
        (SeqG (NumG 0x0B))
      )
      (CaseE
        (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
        (TupE
          (VarE "bt")
          (IterE (VarE "in_1") List (iterexp "in_1" (VarE "in_1*")))
          (IterE (VarE "in_2") List (iterexp "in_2" (VarE "in_2*")))
        )
      )
    )
    (ProdD
      (ExpP "l" (VarT "labelidx"))
      (SeqG (SeqG (NumG 0x0C)) (SeqG (AttrG (VarE "l") (VarG "Blabelidx"))))
      (CaseE (Seq (Atom BR) Arg) (TupE (VarE "l")))
    )
    (ProdD
      (ExpP "l" (VarT "labelidx"))
      (SeqG (SeqG (NumG 0x0D)) (SeqG (AttrG (VarE "l") (VarG "Blabelidx"))))
      (CaseE (Seq (Atom BR_IF) Arg) (TupE (VarE "l")))
    )
    (ProdD
      (ExpP "l*" (IterT (VarT "labelidx") List))
      (ExpP "l_N" (VarT "labelidx"))
      (SeqG
        (SeqG (NumG 0x0E))
        (SeqG
          (AttrG
            (IterE (VarE "l") List (iterexp "l" (VarE "l*")))
            (VarG "Blist" (TypA (VarT "labelidx")) (GramA (VarG "Blabelidx")))
          )
        )
        (SeqG (AttrG (VarE "l_N") (VarG "Blabelidx")))
      )
      (CaseE
        (Seq (Atom BR_TABLE) Arg Arg)
        (TupE (IterE (VarE "l") List (iterexp "l" (VarE "l*"))) (VarE "l_N"))
      )
    )
    (ProdD (NumG 0x0F) (CaseE (Atom RETURN) (TupE)))
    (ProdD
      (ExpP "x" (VarT "idx"))
      (SeqG (SeqG (NumG 0x10)) (SeqG (AttrG (VarE "x") (VarG "Bfuncidx"))))
      (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "x")))
    )
    (ProdD
      (ExpP "x" (VarT "idx"))
      (SeqG
        (SeqG (NumG 0x11))
        (SeqG (AttrG (VarE "x") (VarG "Btypeidx")))
        (SeqG (NumG 0x00))
      )
      (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "x")))
    )
    (ProdD (NumG 0x1A) (CaseE (Atom DROP) (TupE)))
    (ProdD (NumG 0x1B) (CaseE (Atom SELECT) (TupE)))
    (ProdD
      (ExpP "x" (VarT "idx"))
      (SeqG (SeqG (NumG 0x20)) (SeqG (AttrG (VarE "x") (VarG "Blocalidx"))))
      (CaseE (Seq (Atom LOCAL.GET) Arg) (TupE (VarE "x")))
    )
    (ProdD
      (ExpP "x" (VarT "idx"))
      (SeqG (SeqG (NumG 0x21)) (SeqG (AttrG (VarE "x") (VarG "Blocalidx"))))
      (CaseE (Seq (Atom LOCAL.SET) Arg) (TupE (VarE "x")))
    )
    (ProdD
      (ExpP "x" (VarT "idx"))
      (SeqG (SeqG (NumG 0x22)) (SeqG (AttrG (VarE "x") (VarG "Blocalidx"))))
      (CaseE (Seq (Atom LOCAL.TEE) Arg) (TupE (VarE "x")))
    )
    (ProdD
      (ExpP "x" (VarT "idx"))
      (SeqG (SeqG (NumG 0x23)) (SeqG (AttrG (VarE "x") (VarG "Bglobalidx"))))
      (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "x")))
    )
    (ProdD
      (ExpP "x" (VarT "idx"))
      (SeqG (SeqG (NumG 0x24)) (SeqG (AttrG (VarE "x") (VarG "Bglobalidx"))))
      (CaseE (Seq (Atom GLOBAL.SET) Arg) (TupE (VarE "x")))
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x28)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom LOAD) Arg Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (OptE) (VarE "ao"))
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x29)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom LOAD) Arg Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (OptE) (VarE "ao"))
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x2A)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom LOAD) Arg Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (OptE) (VarE "ao"))
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x2B)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom LOAD) Arg Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (OptE) (VarE "ao"))
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x2C)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom LOAD) Arg Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (OptE
            (CaseE
              (Seq (Atom mk_loadop__0) Arg Arg)
              (TupE
                (CaseE (Atom I32) (TupE))
                (CaseE
                  (Seq Arg (Atom _) Arg)
                  (TupE
                    (CaseE Arg (TupE (NumE (Nat 8))))
                    (CaseE (Atom S) (TupE))
                  )
                )
              )
            )
          )
          (VarE "ao")
        )
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x2D)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom LOAD) Arg Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (OptE
            (CaseE
              (Seq (Atom mk_loadop__0) Arg Arg)
              (TupE
                (CaseE (Atom I32) (TupE))
                (CaseE
                  (Seq Arg (Atom _) Arg)
                  (TupE
                    (CaseE Arg (TupE (NumE (Nat 8))))
                    (CaseE (Atom U) (TupE))
                  )
                )
              )
            )
          )
          (VarE "ao")
        )
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x2E)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom LOAD) Arg Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (OptE
            (CaseE
              (Seq (Atom mk_loadop__0) Arg Arg)
              (TupE
                (CaseE (Atom I32) (TupE))
                (CaseE
                  (Seq Arg (Atom _) Arg)
                  (TupE
                    (CaseE Arg (TupE (NumE (Nat 16))))
                    (CaseE (Atom S) (TupE))
                  )
                )
              )
            )
          )
          (VarE "ao")
        )
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x2F)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom LOAD) Arg Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (OptE
            (CaseE
              (Seq (Atom mk_loadop__0) Arg Arg)
              (TupE
                (CaseE (Atom I32) (TupE))
                (CaseE
                  (Seq Arg (Atom _) Arg)
                  (TupE
                    (CaseE Arg (TupE (NumE (Nat 16))))
                    (CaseE (Atom U) (TupE))
                  )
                )
              )
            )
          )
          (VarE "ao")
        )
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x30)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom LOAD) Arg Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (OptE
            (CaseE
              (Seq (Atom mk_loadop__0) Arg Arg)
              (TupE
                (CaseE (Atom I64) (TupE))
                (CaseE
                  (Seq Arg (Atom _) Arg)
                  (TupE
                    (CaseE Arg (TupE (NumE (Nat 8))))
                    (CaseE (Atom S) (TupE))
                  )
                )
              )
            )
          )
          (VarE "ao")
        )
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x31)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom LOAD) Arg Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (OptE
            (CaseE
              (Seq (Atom mk_loadop__0) Arg Arg)
              (TupE
                (CaseE (Atom I64) (TupE))
                (CaseE
                  (Seq Arg (Atom _) Arg)
                  (TupE
                    (CaseE Arg (TupE (NumE (Nat 8))))
                    (CaseE (Atom U) (TupE))
                  )
                )
              )
            )
          )
          (VarE "ao")
        )
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x32)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom LOAD) Arg Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (OptE
            (CaseE
              (Seq (Atom mk_loadop__0) Arg Arg)
              (TupE
                (CaseE (Atom I64) (TupE))
                (CaseE
                  (Seq Arg (Atom _) Arg)
                  (TupE
                    (CaseE Arg (TupE (NumE (Nat 16))))
                    (CaseE (Atom S) (TupE))
                  )
                )
              )
            )
          )
          (VarE "ao")
        )
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x33)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom LOAD) Arg Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (OptE
            (CaseE
              (Seq (Atom mk_loadop__0) Arg Arg)
              (TupE
                (CaseE (Atom I64) (TupE))
                (CaseE
                  (Seq Arg (Atom _) Arg)
                  (TupE
                    (CaseE Arg (TupE (NumE (Nat 16))))
                    (CaseE (Atom U) (TupE))
                  )
                )
              )
            )
          )
          (VarE "ao")
        )
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x34)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom LOAD) Arg Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (OptE
            (CaseE
              (Seq (Atom mk_loadop__0) Arg Arg)
              (TupE
                (CaseE (Atom I64) (TupE))
                (CaseE
                  (Seq Arg (Atom _) Arg)
                  (TupE
                    (CaseE Arg (TupE (NumE (Nat 32))))
                    (CaseE (Atom S) (TupE))
                  )
                )
              )
            )
          )
          (VarE "ao")
        )
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x35)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom LOAD) Arg Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (OptE
            (CaseE
              (Seq (Atom mk_loadop__0) Arg Arg)
              (TupE
                (CaseE (Atom I64) (TupE))
                (CaseE
                  (Seq Arg (Atom _) Arg)
                  (TupE
                    (CaseE Arg (TupE (NumE (Nat 32))))
                    (CaseE (Atom U) (TupE))
                  )
                )
              )
            )
          )
          (VarE "ao")
        )
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x36)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom STORE) Arg Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (OptE) (VarE "ao"))
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x37)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom STORE) Arg Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (OptE) (VarE "ao"))
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x38)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom STORE) Arg Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (OptE) (VarE "ao"))
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x39)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom STORE) Arg Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (OptE) (VarE "ao"))
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x3A)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom STORE) Arg Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (OptE (CaseE Arg (TupE (NumE (Nat 8)))))
          (VarE "ao")
        )
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x3B)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom STORE) Arg Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (OptE (CaseE Arg (TupE (NumE (Nat 16)))))
          (VarE "ao")
        )
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x3C)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom STORE) Arg Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (OptE (CaseE Arg (TupE (NumE (Nat 8)))))
          (VarE "ao")
        )
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x3D)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom STORE) Arg Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (OptE (CaseE Arg (TupE (NumE (Nat 16)))))
          (VarE "ao")
        )
      )
    )
    (ProdD
      (ExpP "ao" (VarT "memarg"))
      (SeqG (SeqG (NumG 0x3E)) (SeqG (AttrG (VarE "ao") (VarG "Bmemarg"))))
      (CaseE
        (Seq (Atom STORE) Arg Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (OptE (CaseE Arg (TupE (NumE (Nat 32)))))
          (VarE "ao")
        )
      )
    )
    (ProdD
      (SeqG (SeqG (NumG 0x3F)) (SeqG (NumG 0x00)))
      (CaseE (Atom MEMORY.SIZE) (TupE))
    )
    (ProdD
      (SeqG (SeqG (NumG 0x40)) (SeqG (NumG 0x00)))
      (CaseE (Atom MEMORY.GROW) (TupE))
    )
    (ProdD
      (ExpP "i" (VarT "i32"))
      (SeqG (SeqG (NumG 0x41)) (SeqG (AttrG (VarE "i") (VarG "Bi32"))))
      (CaseE
        (Seq (Atom CONST) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
          )
        )
      )
    )
    (ProdD
      (ExpP "i" (VarT "i64"))
      (SeqG (SeqG (NumG 0x42)) (SeqG (AttrG (VarE "i") (VarG "Bi64"))))
      (CaseE
        (Seq (Atom CONST) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (VarE "i"))
          )
        )
      )
    )
    (ProdD
      (ExpP "p" (VarT "f32"))
      (SeqG (SeqG (NumG 0x43)) (SeqG (AttrG (VarE "p") (VarG "Bf32"))))
      (CaseE
        (Seq (Atom CONST) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "p"))
          )
        )
      )
    )
    (ProdD
      (ExpP "p" (VarT "f64"))
      (SeqG (SeqG (NumG 0x44)) (SeqG (AttrG (VarE "p") (VarG "Bf64"))))
      (CaseE
        (Seq (Atom CONST) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "p"))
          )
        )
      )
    )
    (ProdD
      (NumG 0x45)
      (CaseE
        (Seq (Atom TESTOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_testop__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom EQZ) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x46)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom EQ) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x47)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom NE) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x48)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE
              (CaseE (Atom I32) (TupE))
              (CaseE (Seq (Atom LT) Arg) (TupE (CaseE (Atom S) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x49)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE
              (CaseE (Atom I32) (TupE))
              (CaseE (Seq (Atom LT) Arg) (TupE (CaseE (Atom U) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x4A)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE
              (CaseE (Atom I32) (TupE))
              (CaseE (Seq (Atom GT) Arg) (TupE (CaseE (Atom S) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x4B)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE
              (CaseE (Atom I32) (TupE))
              (CaseE (Seq (Atom GT) Arg) (TupE (CaseE (Atom U) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x4C)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE
              (CaseE (Atom I32) (TupE))
              (CaseE (Seq (Atom LE) Arg) (TupE (CaseE (Atom S) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x4D)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE
              (CaseE (Atom I32) (TupE))
              (CaseE (Seq (Atom LE) Arg) (TupE (CaseE (Atom U) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x4E)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE
              (CaseE (Atom I32) (TupE))
              (CaseE (Seq (Atom GE) Arg) (TupE (CaseE (Atom S) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x4F)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE
              (CaseE (Atom I32) (TupE))
              (CaseE (Seq (Atom GE) Arg) (TupE (CaseE (Atom U) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x50)
      (CaseE
        (Seq (Atom TESTOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_testop__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom EQZ) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x51)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom EQ) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x52)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom NE) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x53)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE
              (CaseE (Atom I64) (TupE))
              (CaseE (Seq (Atom LT) Arg) (TupE (CaseE (Atom S) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x54)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE
              (CaseE (Atom I64) (TupE))
              (CaseE (Seq (Atom LT) Arg) (TupE (CaseE (Atom U) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x55)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE
              (CaseE (Atom I64) (TupE))
              (CaseE (Seq (Atom GT) Arg) (TupE (CaseE (Atom S) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x56)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE
              (CaseE (Atom I64) (TupE))
              (CaseE (Seq (Atom GT) Arg) (TupE (CaseE (Atom U) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x57)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE
              (CaseE (Atom I64) (TupE))
              (CaseE (Seq (Atom LE) Arg) (TupE (CaseE (Atom S) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x58)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE
              (CaseE (Atom I64) (TupE))
              (CaseE (Seq (Atom LE) Arg) (TupE (CaseE (Atom U) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x59)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE
              (CaseE (Atom I64) (TupE))
              (CaseE (Seq (Atom GE) Arg) (TupE (CaseE (Atom S) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x5A)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_relop__0) Arg Arg)
            (TupE
              (CaseE (Atom I64) (TupE))
              (CaseE (Seq (Atom GE) Arg) (TupE (CaseE (Atom U) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x5B)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_relop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom EQ) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x5C)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_relop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom NE) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x5D)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_relop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom LT) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x5E)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_relop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom GT) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x5F)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_relop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom LE) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x60)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_relop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom GE) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x61)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_relop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom EQ) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x62)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_relop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom NE) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x63)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_relop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom LT) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x64)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_relop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom GT) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x65)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_relop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom LE) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x66)
      (CaseE
        (Seq (Atom RELOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_relop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom GE) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x67)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_unop__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom CLZ) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x68)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_unop__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom CTZ) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x69)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_unop__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom POPCNT) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x6A)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom ADD) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x6B)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom SUB) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x6C)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom MUL) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x6D)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE
              (CaseE (Atom I32) (TupE))
              (CaseE (Seq (Atom DIV) Arg) (TupE (CaseE (Atom S) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x6E)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE
              (CaseE (Atom I32) (TupE))
              (CaseE (Seq (Atom DIV) Arg) (TupE (CaseE (Atom U) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x6F)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE
              (CaseE (Atom I32) (TupE))
              (CaseE (Seq (Atom REM) Arg) (TupE (CaseE (Atom S) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x70)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE
              (CaseE (Atom I32) (TupE))
              (CaseE (Seq (Atom REM) Arg) (TupE (CaseE (Atom U) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x71)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom AND) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x72)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom OR) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x73)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom XOR) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x74)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom SHL) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x75)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE
              (CaseE (Atom I32) (TupE))
              (CaseE (Seq (Atom SHR) Arg) (TupE (CaseE (Atom S) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x76)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE
              (CaseE (Atom I32) (TupE))
              (CaseE (Seq (Atom SHR) Arg) (TupE (CaseE (Atom U) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x77)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom ROTL) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x78)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom ROTR) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x79)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_unop__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom CLZ) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x7A)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_unop__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom CTZ) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x7B)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_unop__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom POPCNT) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x7C)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom ADD) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x7D)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom SUB) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x7E)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom MUL) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x7F)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE
              (CaseE (Atom I64) (TupE))
              (CaseE (Seq (Atom DIV) Arg) (TupE (CaseE (Atom S) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x80)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE
              (CaseE (Atom I64) (TupE))
              (CaseE (Seq (Atom DIV) Arg) (TupE (CaseE (Atom U) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x81)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE
              (CaseE (Atom I64) (TupE))
              (CaseE (Seq (Atom REM) Arg) (TupE (CaseE (Atom S) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x82)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE
              (CaseE (Atom I64) (TupE))
              (CaseE (Seq (Atom REM) Arg) (TupE (CaseE (Atom U) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x83)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom AND) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x84)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom OR) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x85)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom XOR) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x86)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom SHL) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x87)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE
              (CaseE (Atom I64) (TupE))
              (CaseE (Seq (Atom SHR) Arg) (TupE (CaseE (Atom S) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x88)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE
              (CaseE (Atom I64) (TupE))
              (CaseE (Seq (Atom SHR) Arg) (TupE (CaseE (Atom U) (TupE))))
            )
          )
        )
      )
    )
    (ProdD
      (NumG 0x89)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom ROTL) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x8A)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom ROTR) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x8B)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_unop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom ABS) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x8C)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_unop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom NEG) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x8D)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_unop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom CEIL) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x8E)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_unop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom FLOOR) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x8F)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_unop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom TRUNC) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x90)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_unop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom NEAREST) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x91)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_unop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom SQRT) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x92)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom ADD) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x93)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom SUB) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x94)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom MUL) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x95)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom DIV) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x96)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom MIN) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x97)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom MAX) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x98)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_binop__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom COPYSIGN) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x99)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_unop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom ABS) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x9A)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_unop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom NEG) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x9B)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_unop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom CEIL) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x9C)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_unop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom FLOOR) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x9D)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_unop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom TRUNC) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x9E)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_unop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom NEAREST) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0x9F)
      (CaseE
        (Seq (Atom UNOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_unop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom SQRT) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0xA0)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom ADD) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0xA1)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom SUB) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0xA2)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom MUL) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0xA3)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom DIV) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0xA4)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom MIN) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0xA5)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom MAX) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0xA6)
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_binop__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom COPYSIGN) (TupE)))
          )
        )
      )
    )
    (ProdD
      (NumG 0xA7)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Atom I64) (TupE))
          (CaseE (Atom WRAP) (TupE))
        )
      )
    )
    (ProdD
      (NumG 0xA8)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Atom F32) (TupE))
          (CaseE (Seq (Atom TRUNC) Arg) (TupE (CaseE (Atom S) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xA9)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Atom F32) (TupE))
          (CaseE (Seq (Atom TRUNC) Arg) (TupE (CaseE (Atom U) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xAA)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Atom F64) (TupE))
          (CaseE (Seq (Atom TRUNC) Arg) (TupE (CaseE (Atom S) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xAB)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Atom F64) (TupE))
          (CaseE (Seq (Atom TRUNC) Arg) (TupE (CaseE (Atom U) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xAC)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom EXTEND) Arg) (TupE (CaseE (Atom S) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xAD)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom EXTEND) Arg) (TupE (CaseE (Atom U) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xAE)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Atom F32) (TupE))
          (CaseE (Seq (Atom TRUNC) Arg) (TupE (CaseE (Atom S) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xAF)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Atom F32) (TupE))
          (CaseE (Seq (Atom TRUNC) Arg) (TupE (CaseE (Atom U) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xB0)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Atom F64) (TupE))
          (CaseE (Seq (Atom TRUNC) Arg) (TupE (CaseE (Atom S) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xB1)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Atom F64) (TupE))
          (CaseE (Seq (Atom TRUNC) Arg) (TupE (CaseE (Atom U) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xB2)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom CONVERT) Arg) (TupE (CaseE (Atom S) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xB3)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom CONVERT) Arg) (TupE (CaseE (Atom U) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xB4)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom CONVERT) Arg) (TupE (CaseE (Atom S) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xB5)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom CONVERT) Arg) (TupE (CaseE (Atom U) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xB6)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE (Atom F64) (TupE))
          (CaseE (Atom DEMOTE) (TupE))
        )
      )
    )
    (ProdD
      (NumG 0xB7)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom CONVERT) Arg) (TupE (CaseE (Atom S) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xB8)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom CONVERT) Arg) (TupE (CaseE (Atom U) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xB9)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom CONVERT) Arg) (TupE (CaseE (Atom S) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xBA)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom CONVERT) Arg) (TupE (CaseE (Atom U) (TupE))))
        )
      )
    )
    (ProdD
      (NumG 0xBB)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE (Atom F64) (TupE))
          (CaseE (Atom PROMOTE) (TupE))
        )
      )
    )
    (ProdD
      (NumG 0xBC)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Atom F32) (TupE))
          (CaseE (Atom REINTERPRET) (TupE))
        )
      )
    )
    (ProdD
      (NumG 0xBD)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Atom F64) (TupE))
          (CaseE (Atom REINTERPRET) (TupE))
        )
      )
    )
    (ProdD
      (NumG 0xBE)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE (Atom I32) (TupE))
          (CaseE (Atom REINTERPRET) (TupE))
        )
      )
    )
    (ProdD
      (NumG 0xBF)
      (CaseE
        (Seq (Atom CVTOP) Arg Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE (Atom I64) (TupE))
          (CaseE (Atom REINTERPRET) (TupE))
        )
      )
    )
  )
)
(GramD
  "Bexpr"
  (VarT "expr")
  (ProdD
    (ExpP "in*" (IterT (VarT "instr") List))
    (SeqG
      (SeqG
        (IterG
          (AttrG (VarE "in") (VarG "Binstr"))
          List
          (iterexp "in" (VarE "in*"))
        )
      )
      (SeqG (NumG 0x0B))
    )
    (IterE (VarE "in") List (iterexp "in" (VarE "in*")))
  )
)
(GramD
  "Bsection_"
  (ExpP "N" (VarT "N"))
  (TypP "en")
  (GramP "BX" (IterT (VarT "en") List))
  (IterT (VarT "en") List)
  (ProdD
    (ExpP "en*" (IterT (VarT "en") List))
    (ExpP "len" nat)
    (SeqG
      (SeqG (AttrG (CaseE Arg (TupE (VarE "N"))) (VarG "Bbyte")))
      (SeqG (AttrG (CaseE Arg (TupE (VarE "len"))) (VarG "Bu32")))
      (SeqG
        (AttrG (IterE (VarE "en") List (iterexp "en" (VarE "en*"))) (VarG "BX"))
      )
    )
    (IterE (VarE "en") List (iterexp "en" (VarE "en*")))
    (IfPr (CmpE EqOp bool (VarE "len") (NumE (Nat 0))))
  )
  (ProdD EpsG (ListE))
)
(HintD (GramH "Bsection_" (hint "desc" "\"section\"")))
(GramD
  "Bcustom"
  (IterT (TupT) List)
  (ProdD
    (SeqG (SeqG (VarG "Bname")) (SeqG (IterG (VarG "Bbyte") List)))
    (ListE)
  )
)
(HintD (GramH "Bcustom" (hint "desc" "\"custom data\"")))
(GramD
  "Bcustomsec"
  (TupT)
  (ProdD
    (VarG
      "Bsection_"
      (ExpA (NumE (Nat 0)))
      (TypA (TupT))
      (GramA (VarG "Bcustom"))
    )
    (ProjE (TupE (TupE) (TupE)) 1)
  )
)
(HintD (GramH "Bcustomsec" (hint "desc" "\"custom section\"")))
(GramD
  "Btype"
  (VarT "type")
  (ProdD
    (ExpP "ft" (VarT "functype"))
    (AttrG (VarE "ft") (VarG "Bfunctype"))
    (CaseE (Seq (Atom TYPE) Arg) (TupE (VarE "ft")))
  )
)
(GramD
  "Btypesec"
  (IterT (VarT "type") List)
  (ProdD
    (ExpP "ty*" (IterT (VarT "type") List))
    (AttrG
      (IterE (VarE "ty") List (iterexp "ty" (VarE "ty*")))
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 1)))
        (TypA (VarT "type"))
        (GramA (VarG "Blist" (TypA (VarT "type")) (GramA (VarG "Btype"))))
      )
    )
    (IterE (VarE "ty") List (iterexp "ty" (VarE "ty*")))
  )
)
(HintD (GramH "Btypesec" (hint "desc" "\"type section\"")))
(GramD
  "Bimport"
  (VarT "import")
  (ProdD
    (ExpP "nm_1" (VarT "name"))
    (ExpP "nm_2" (VarT "name"))
    (ExpP "xt" (VarT "externtype"))
    (SeqG
      (SeqG (AttrG (VarE "nm_1") (VarG "Bname")))
      (SeqG (AttrG (VarE "nm_2") (VarG "Bname")))
      (SeqG (AttrG (VarE "xt") (VarG "Bexterntype")))
    )
    (CaseE
      (Seq (Atom IMPORT) Arg Arg Arg)
      (TupE (VarE "nm_1") (VarE "nm_2") (VarE "xt"))
    )
  )
)
(GramD
  "Bimportsec"
  (IterT (VarT "import") List)
  (ProdD
    (ExpP "im*" (IterT (VarT "import") List))
    (AttrG
      (IterE (VarE "im") List (iterexp "im" (VarE "im*")))
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 2)))
        (TypA (VarT "import"))
        (GramA (VarG "Blist" (TypA (VarT "import")) (GramA (VarG "Bimport"))))
      )
    )
    (IterE (VarE "im") List (iterexp "im" (VarE "im*")))
  )
)
(HintD (GramH "Bimportsec" (hint "desc" "\"import section\"")))
(GramD
  "Bfuncsec"
  (IterT (VarT "typeidx") List)
  (ProdD
    (ExpP "x*" (IterT (VarT "idx") List))
    (AttrG
      (IterE (VarE "x") List (iterexp "x" (VarE "x*")))
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 3)))
        (TypA (VarT "typeidx"))
        (GramA (VarG "Blist" (TypA (VarT "typeidx")) (GramA (VarG "Btypeidx"))))
      )
    )
    (IterE (VarE "x") List (iterexp "x" (VarE "x*")))
  )
)
(HintD (GramH "Bfuncsec" (hint "desc" "\"function section\"")))
(GramD
  "Btable"
  (VarT "table")
  (ProdD
    (ExpP "tt" (VarT "tabletype"))
    (AttrG (VarE "tt") (VarG "Btabletype"))
    (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tt")))
  )
)
(GramD
  "Btablesec"
  (IterT (VarT "table") List)
  (ProdD
    (ExpP "tab*" (IterT (VarT "table") List))
    (AttrG
      (IterE (VarE "tab") List (iterexp "tab" (VarE "tab*")))
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 4)))
        (TypA (VarT "table"))
        (GramA (VarG "Blist" (TypA (VarT "table")) (GramA (VarG "Btable"))))
      )
    )
    (IterE (VarE "tab") List (iterexp "tab" (VarE "tab*")))
  )
)
(HintD (GramH "Btablesec" (hint "desc" "\"table section\"")))
(GramD
  "Bmem"
  (VarT "mem")
  (ProdD
    (ExpP "mt" (VarT "memtype"))
    (AttrG (VarE "mt") (VarG "Bmemtype"))
    (CaseE (Seq (Atom MEMORY) Arg) (TupE (VarE "mt")))
  )
)
(GramD
  "Bmemsec"
  (IterT (VarT "mem") List)
  (ProdD
    (ExpP "mem*" (IterT (VarT "mem") List))
    (AttrG
      (IterE (VarE "mem") List (iterexp "mem" (VarE "mem*")))
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 5)))
        (TypA (VarT "mem"))
        (GramA (VarG "Blist" (TypA (VarT "mem")) (GramA (VarG "Bmem"))))
      )
    )
    (IterE (VarE "mem") List (iterexp "mem" (VarE "mem*")))
  )
)
(HintD (GramH "Bmemsec" (hint "desc" "\"memory section\"")))
(GramD
  "Bglobal"
  (VarT "global")
  (ProdD
    (ExpP "gt" (VarT "globaltype"))
    (ExpP "e" (VarT "expr"))
    (SeqG
      (SeqG (AttrG (VarE "gt") (VarG "Bglobaltype")))
      (SeqG (AttrG (VarE "e") (VarG "Bexpr")))
    )
    (CaseE (Seq (Atom GLOBAL) Arg Arg) (TupE (VarE "gt") (VarE "e")))
  )
)
(GramD
  "Bglobalsec"
  (IterT (VarT "global") List)
  (ProdD
    (ExpP "glob*" (IterT (VarT "global") List))
    (AttrG
      (IterE (VarE "glob") List (iterexp "glob" (VarE "glob*")))
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 6)))
        (TypA (VarT "global"))
        (GramA (VarG "Blist" (TypA (VarT "global")) (GramA (VarG "Bglobal"))))
      )
    )
    (IterE (VarE "glob") List (iterexp "glob" (VarE "glob*")))
  )
)
(HintD (GramH "Bglobalsec" (hint "desc" "\"global section\"")))
(GramD
  "Bexport"
  (VarT "export")
  (ProdD
    (ExpP "nm" (VarT "name"))
    (ExpP "xx" (VarT "externidx"))
    (SeqG
      (SeqG (AttrG (VarE "nm") (VarG "Bname")))
      (SeqG (AttrG (VarE "xx") (VarG "Bexternidx")))
    )
    (CaseE (Seq (Atom EXPORT) Arg Arg) (TupE (VarE "nm") (VarE "xx")))
  )
)
(GramD
  "Bexportsec"
  (IterT (VarT "export") List)
  (ProdD
    (ExpP "ex*" (IterT (VarT "export") List))
    (AttrG
      (IterE (VarE "ex") List (iterexp "ex" (VarE "ex*")))
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 7)))
        (TypA (VarT "export"))
        (GramA (VarG "Blist" (TypA (VarT "export")) (GramA (VarG "Bexport"))))
      )
    )
    (IterE (VarE "ex") List (iterexp "ex" (VarE "ex*")))
  )
)
(HintD (GramH "Bexportsec" (hint "desc" "\"export section\"")))
(GramD
  "Bstart"
  (IterT (VarT "start") List)
  (ProdD
    (ExpP "x" (VarT "idx"))
    (AttrG (VarE "x") (VarG "Bfuncidx"))
    (ListE (CaseE (Seq (Atom START) Arg) (TupE (VarE "x"))))
  )
)
(GramD
  "Bstartsec"
  (IterT (VarT "start") Opt)
  (ProdD
    (ExpP "startopt" (VarT "startopt"))
    (AttrG
      (VarE "startopt")
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 8)))
        (TypA (VarT "start"))
        (GramA (VarG "Bstart"))
      )
    )
    (TheE (CallE "opt_" (TypA (VarT "start")) (ExpA (VarE "startopt"))))
  )
)
(HintD (GramH "Bstartsec" (hint "desc" "\"start section\"")))
(GramD
  "Belem"
  (VarT "elem")
  (ProdD
    (ExpP "e" (VarT "expr"))
    (ExpP "x*" (IterT (VarT "idx") List))
    (SeqG
      (SeqG (NumG 0x00))
      (SeqG (AttrG (VarE "e") (VarG "Bexpr")))
      (SeqG
        (AttrG
          (IterE (VarE "x") List (iterexp "x" (VarE "x*")))
          (VarG "Blist" (TypA (VarT "funcidx")) (GramA (VarG "Bfuncidx")))
        )
      )
    )
    (CaseE
      (Seq (Atom ELEM) Arg Arg)
      (TupE (VarE "e") (IterE (VarE "x") List (iterexp "x" (VarE "x*"))))
    )
  )
)
(GramD
  "Belemsec"
  (IterT (VarT "elem") List)
  (ProdD
    (ExpP "elem*" (IterT (VarT "elem") List))
    (AttrG
      (IterE (VarE "elem") List (iterexp "elem" (VarE "elem*")))
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 9)))
        (TypA (VarT "elem"))
        (GramA (VarG "Blist" (TypA (VarT "elem")) (GramA (VarG "Belem"))))
      )
    )
    (IterE (VarE "elem") List (iterexp "elem" (VarE "elem*")))
  )
)
(HintD (GramH "Belemsec" (hint "desc" "\"element section\"")))
(GramD
  "Blocals"
  (IterT (VarT "local") List)
  (ProdD
    (ExpP "t" (VarT "valtype"))
    (ExpP "n" (VarT "n"))
    (SeqG
      (SeqG (AttrG (CaseE Arg (TupE (VarE "n"))) (VarG "Bu32")))
      (SeqG (AttrG (VarE "t") (VarG "Bvaltype")))
    )
    (IterE (CaseE (Seq (Atom LOCAL) Arg) (TupE (VarE "t"))) (ListN (VarE "n")))
  )
)
(HintD (GramH "Blocals" (hint "desc" "\"local\"")))
(GramD
  "Bfunc"
  (VarT "code")
  (ProdD
    (ExpP "local**" (IterT (IterT (VarT "local") List) List))
    (ExpP "expr" (VarT "expr"))
    (SeqG
      (SeqG
        (AttrG
          (IterE
            (IterE (VarE "local") List (iterexp "local" (VarE "local*")))
            List
            (iterexp "local*" (VarE "local**"))
          )
          (VarG
            "Blist"
            (TypA (IterT (VarT "local") List))
            (GramA (VarG "Blocals"))
          )
        )
      )
      (SeqG (AttrG (VarE "expr") (VarG "Bexpr")))
    )
    (TupE
      (CallE
        "concat_"
        (TypA (VarT "local"))
        (ExpA
          (IterE
            (IterE (VarE "local") List (iterexp "local" (VarE "local*")))
            List
            (iterexp "local*" (VarE "local**"))
          )
        )
      )
      (VarE "expr")
    )
  )
)
(GramD
  "Bcode"
  (VarT "code")
  (ProdD
    (ExpP "code" (VarT "code"))
    (ExpP "len" nat)
    (SeqG
      (SeqG (AttrG (CaseE Arg (TupE (VarE "len"))) (VarG "Bu32")))
      (SeqG (AttrG (VarE "code") (VarG "Bfunc")))
    )
    (VarE "code")
    (IfPr (CmpE EqOp bool (VarE "len") (NumE (Nat 0))))
  )
)
(GramD
  "Bcodesec"
  (IterT (VarT "code") List)
  (ProdD
    (ExpP "code*" (IterT (VarT "code") List))
    (AttrG
      (IterE (VarE "code") List (iterexp "code" (VarE "code*")))
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 10)))
        (TypA (VarT "code"))
        (GramA (VarG "Blist" (TypA (VarT "code")) (GramA (VarG "Bcode"))))
      )
    )
    (IterE (VarE "code") List (iterexp "code" (VarE "code*")))
  )
)
(HintD (GramH "Bcodesec" (hint "desc" "\"code section\"")))
(GramD
  "Bdata"
  (VarT "data")
  (ProdD
    (ExpP "e" (VarT "expr"))
    (ExpP "b*" (IterT (VarT "byte") List))
    (SeqG
      (SeqG (NumG 0x00))
      (SeqG (AttrG (VarE "e") (VarG "Bexpr")))
      (SeqG
        (AttrG
          (IterE (VarE "b") List (iterexp "b" (VarE "b*")))
          (VarG "Blist" (TypA (VarT "byte")) (GramA (VarG "Bbyte")))
        )
      )
    )
    (CaseE
      (Seq (Atom DATA) Arg Arg)
      (TupE (VarE "e") (IterE (VarE "b") List (iterexp "b" (VarE "b*"))))
    )
  )
)
(GramD
  "Bdatasec"
  (IterT (VarT "data") List)
  (ProdD
    (ExpP "data*" (IterT (VarT "data") List))
    (AttrG
      (IterE (VarE "data") List (iterexp "data" (VarE "data*")))
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 11)))
        (TypA (VarT "data"))
        (GramA (VarG "Blist" (TypA (VarT "data")) (GramA (VarG "Bdata"))))
      )
    )
    (IterE (VarE "data") List (iterexp "data" (VarE "data*")))
  )
)
(HintD (GramH "Bdatasec" (hint "desc" "\"data section\"")))
(GramD
  "Bmodule"
  (VarT "module")
  (ProdD
    (ExpP "type*" (IterT (VarT "type") List))
    (ExpP "import*" (IterT (VarT "import") List))
    (ExpP "func*" (IterT (VarT "func") List))
    (ExpP "global*" (IterT (VarT "global") List))
    (ExpP "table*" (IterT (VarT "table") List))
    (ExpP "mem*" (IterT (VarT "mem") List))
    (ExpP "elem*" (IterT (VarT "elem") List))
    (ExpP "data*" (IterT (VarT "data") List))
    (ExpP "start?" (IterT (VarT "start") Opt))
    (ExpP "export*" (IterT (VarT "export") List))
    (ExpP "typeidx*" (IterT (VarT "typeidx") List))
    (ExpP "expr*" (IterT (VarT "expr") List))
    (ExpP "local**" (IterT (IterT (VarT "local") List) List))
    (SeqG
      (SeqG (NumG 0x00))
      (SeqG (NumG 0x61))
      (SeqG (NumG 0x73))
      (SeqG (NumG 0x6D))
      (SeqG (AttrG (CaseE Arg (TupE (NumE (Nat 1)))) (VarG "Bu32")))
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG
        (AttrG
          (IterE (VarE "type") List (iterexp "type" (VarE "type*")))
          (VarG "Btypesec")
        )
      )
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG
        (AttrG
          (IterE (VarE "import") List (iterexp "import" (VarE "import*")))
          (VarG "Bimportsec")
        )
      )
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG
        (AttrG
          (IterE (VarE "typeidx") List (iterexp "typeidx" (VarE "typeidx*")))
          (VarG "Bfuncsec")
        )
      )
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG
        (AttrG
          (IterE (VarE "table") List (iterexp "table" (VarE "table*")))
          (VarG "Btablesec")
        )
      )
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG
        (AttrG
          (IterE (VarE "mem") List (iterexp "mem" (VarE "mem*")))
          (VarG "Bmemsec")
        )
      )
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG
        (AttrG
          (IterE (VarE "global") List (iterexp "global" (VarE "global*")))
          (VarG "Bglobalsec")
        )
      )
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG
        (AttrG
          (IterE (VarE "export") List (iterexp "export" (VarE "export*")))
          (VarG "Bexportsec")
        )
      )
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG
        (AttrG
          (IterE (VarE "start") Opt (iterexp "start" (VarE "start?")))
          (VarG "Bstartsec")
        )
      )
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG
        (AttrG
          (IterE (VarE "elem") List (iterexp "elem" (VarE "elem*")))
          (VarG "Belemsec")
        )
      )
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG
        (AttrG
          (IterE
            (TupE
              (IterE (VarE "local") List (iterexp "local" (VarE "local*")))
              (VarE "expr")
            )
            List
            (iterexp "expr" (VarE "expr*"))
            (iterexp "local*" (VarE "local**"))
          )
          (VarG "Bcodesec")
        )
      )
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG
        (AttrG
          (IterE (VarE "data") List (iterexp "data" (VarE "data*")))
          (VarG "Bdatasec")
        )
      )
      (SeqG (IterG (VarG "Bcustomsec") List))
    )
    (CaseE
      (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
      (TupE
        (IterE (VarE "type") List (iterexp "type" (VarE "type*")))
        (IterE (VarE "import") List (iterexp "import" (VarE "import*")))
        (IterE (VarE "func") List (iterexp "func" (VarE "func*")))
        (IterE (VarE "global") List (iterexp "global" (VarE "global*")))
        (IterE (VarE "table") List (iterexp "table" (VarE "table*")))
        (IterE (VarE "mem") List (iterexp "mem" (VarE "mem*")))
        (IterE (VarE "elem") List (iterexp "elem" (VarE "elem*")))
        (IterE (VarE "data") List (iterexp "data" (VarE "data*")))
        (IterE (VarE "start") Opt (iterexp "start" (VarE "start?")))
        (IterE (VarE "export") List (iterexp "export" (VarE "export*")))
      )
    )
    (IterPr
      (IfPr
        (CmpE
          EqOp
          bool
          (VarE "func")
          (CaseE
            (Seq (Atom FUNC) Arg Arg Arg)
            (TupE
              (VarE "typeidx")
              (IterE (VarE "local") List (iterexp "local" (VarE "local*")))
              (VarE "expr")
            )
          )
        )
      )
      List
      (iterexp "expr" (VarE "expr*"))
      (iterexp "func" (VarE "func*"))
      (iterexp "local*" (VarE "local**"))
      (iterexp "typeidx" (VarE "typeidx*"))
    )
  )
)


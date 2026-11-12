(TypD "r_MUT" (InstD (VariantT (typcase (Atom MUT) (TupT)))))
(HintD (TypH "r_MUT" (hint "show" "MUT")))
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
  (ExpP "nat_0" nat)
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
  (RelD
    "fun_sum"
    (Seq Arg Arg)
    (TupT (typbind "_" (IterT nat List)) (typbind "_" nat))
    (RuleD "fun_sum_case_0" (Seq Arg Arg) (TupE (ListE) (NumE (Nat 0))))
    (RuleD
      "fun_sum_case_1"
      (ExpP "v_n" nat)
      (ExpP "n'_lst" (IterT (VarT "n") List))
      (ExpP "var_0" nat)
      (Seq Arg Arg)
      (TupE
        (CatE (ListE (VarE "v_n")) (VarE "n'_lst"))
        (BinE AddOp nat (VarE "v_n") (VarE "var_0"))
      )
      (RulePr "fun_sum" (Seq Arg Arg) (TupE (VarE "n'_lst") (VarE "var_0")))
    )
  )
)
(DecD
  "opt_"
  (TypP "X")
  (ExpP "var_0_lst" (IterT (VarT "X") List))
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
  (ExpP "var_0_opt" (IterT (VarT "X") Opt))
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
    (ExpP "var_0_lst_lst" (IterT (IterT (VarT "X") List) List))
    (IterT (VarT "X") List)
    (DefD (TypP "X") (TypA (VarT "X")) (ExpA (ListE)) (ListE))
    (DefD
      (TypP "X")
      (ExpP "w_lst" (IterT (VarT "X") List))
      (ExpP "w'_lst_lst" (IterT (IterT (VarT "X") List) List))
      (TypA (VarT "X"))
      (ExpA (CatE (ListE (VarE "w_lst")) (VarE "w'_lst_lst")))
      (CatE
        (VarE "w_lst")
        (CallE "concat_" (TypA (VarT "X")) (ExpA (VarE "w'_lst_lst")))
      )
    )
  )
)
(HintD (DecH "concat_" (hint "show" "$concat(%2)")))
(RecD
  (DecD
    "disjoint_"
    (TypP "X")
    (ExpP "var_0_lst" (IterT (VarT "X") List))
    BoolT
    (DefD (TypP "X") (TypA (VarT "X")) (ExpA (ListE)) (BoolE true))
    (DefD
      (TypP "X")
      (ExpP "w" (VarT "X"))
      (ExpP "w'_lst" (IterT (VarT "X") List))
      (TypA (VarT "X"))
      (ExpA (CatE (ListE (VarE "w")) (VarE "w'_lst")))
      (BinE
        AndOp
        bool
        (UnE NotOp bool (MemE (VarE "w") (VarE "w'_lst")))
        (CallE "disjoint_" (TypA (VarT "X")) (ExpA (VarE "w'_lst")))
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
        (Seq (Atom mk_list) Arg)
        (TupT (typbind "X_lst" (IterT (VarT "X") List)))
        (IfPr
          (CmpE
            LtOp
            nat
            (LenE (VarE "X_lst"))
            (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 32)))
          )
        )
      )
    )
  )
)
(TypD
  "byte"
  (InstD (VariantT (typcase (Seq (Atom mk_byte) Arg) (TupT (typbind "i" nat)))))
)
(DecD
  "proj_byte_0"
  (ExpP "x" (VarT "byte"))
  (TupT (typbind "_" nat))
  (DefD
    (ExpP "v_num_0" nat)
    (ExpA (CaseE (Seq (Atom mk_byte) Arg) (TupE (VarE "v_num_0"))))
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
    (TupE (CaseE (Seq (Atom mk_byte) Arg) (TupE (VarE "i"))))
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
(TypD
  "uN"
  (InstD (VariantT (typcase (Seq (Atom mk_uN) Arg) (TupT (typbind "i" nat)))))
)
(DecD
  "proj_uN_0"
  (ExpP "x" (VarT "uN"))
  (TupT (typbind "_" nat))
  (DefD
    (ExpP "v_num_0" nat)
    (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_num_0"))))
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
    (ExpP "v_N" (VarT "N"))
    (ExpP "i" nat)
    (Seq Arg Arg)
    (TupE (VarE "v_N") (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "i"))))
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
              (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (VarE "v_N")))
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
(TypD
  "sN"
  (InstD (VariantT (typcase (Seq (Atom mk_sN) Arg) (TupT (typbind "i" int)))))
)
(DecD
  "proj_sN_0"
  (ExpP "x" (VarT "sN"))
  (TupT (typbind "_" int))
  (DefD
    (ExpP "v_num_0" int)
    (ExpA (CaseE (Seq (Atom mk_sN) Arg) (TupE (VarE "v_num_0"))))
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
    (ExpP "v_N" (VarT "N"))
    (ExpP "i" int)
    (Seq Arg Arg)
    (TupE (VarE "v_N") (CaseE (Seq (Atom mk_sN) Arg) (TupE (VarE "i"))))
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
                        (CvtE nat int (VarE "v_N"))
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
                      (CvtE nat int (VarE "v_N"))
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
  (ExpP "v_N" (VarT "N"))
  (IterT nat Opt)
  (DefD (ExpA (NumE (Nat 32))) (OptE (NumE (Nat 23))))
  (DefD (ExpA (NumE (Nat 64))) (OptE (NumE (Nat 52))))
  (DefD (ExpP "x0" (VarT "N")) (ExpA (VarE "x0")) (OptE) ElsePr)
)
(HintD (DecH "signif" (hint "partial" "{}")))
(DecD
  "expon"
  (ExpP "v_N" (VarT "N"))
  (IterT nat Opt)
  (DefD (ExpA (NumE (Nat 32))) (OptE (NumE (Nat 8))))
  (DefD (ExpA (NumE (Nat 64))) (OptE (NumE (Nat 11))))
  (DefD (ExpP "x0" (VarT "N")) (ExpA (VarE "x0")) (OptE) ElsePr)
)
(HintD (DecH "expon" (hint "partial" "{}")))
(DecD
  "fun_M"
  (ExpP "v_N" (VarT "N"))
  nat
  (DefD
    (ExpP "v_N" nat)
    (ExpA (VarE "v_N"))
    (TheE (CallE "signif" (ExpA (VarE "v_N"))))
  )
)
(HintD (DecH "M" (hint "show" "M")))
(DecD
  "E"
  (ExpP "v_N" (VarT "N"))
  nat
  (DefD
    (ExpP "v_N" nat)
    (ExpA (VarE "v_N"))
    (TheE (CallE "expon" (ExpA (VarE "v_N"))))
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
        (TupT (typbind "v_m" (VarT "m")) (typbind "v_exp" (VarT "exp")))
      )
      (typcase
        (Seq (Atom SUBNORM) Arg)
        (TupT (typbind "v_m" (VarT "m")))
        (ExpP "v_exp" (VarT "exp"))
      )
      (typcase (Atom INF) (TupT))
      (typcase (Seq (Atom NAN) Arg) (TupT (typbind "v_m" (VarT "m"))))
    )
  )
)
(RelD
  "wf_fNmag"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "N")) (typbind "_" (VarT "fNmag")))
  (RuleD
    "fNmag_case_0"
    (ExpP "v_N" (VarT "N"))
    (ExpP "v_m" (VarT "m"))
    (ExpP "v_exp" (VarT "exp"))
    (Seq Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE (Seq (Atom NORM) Arg Arg) (TupE (VarE "v_m") (VarE "v_exp")))
    )
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE
          LtOp
          nat
          (VarE "v_m")
          (BinE PowOp nat (NumE (Nat 2)) (CallE "fun_M" (ExpA (VarE "v_N"))))
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
                      (CvtE nat int (CallE "E" (ExpA (VarE "v_N"))))
                      (CvtE nat int (NumE (Nat 1)))
                    )
                  )
                )
              )
            )
            (VarE "v_exp")
          )
          (CmpE
            LeOp
            int
            (VarE "v_exp")
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
                      (CvtE nat int (CallE "E" (ExpA (VarE "v_N"))))
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
    (ExpP "v_N" (VarT "N"))
    (ExpP "v_exp" (VarT "exp"))
    (ExpP "v_m" (VarT "m"))
    (Seq Arg Arg)
    (TupE (VarE "v_N") (CaseE (Seq (Atom SUBNORM) Arg) (TupE (VarE "v_m"))))
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE
          LtOp
          nat
          (VarE "v_m")
          (BinE PowOp nat (NumE (Nat 2)) (CallE "fun_M" (ExpA (VarE "v_N"))))
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
                    (CvtE nat int (CallE "E" (ExpA (VarE "v_N"))))
                    (CvtE nat int (NumE (Nat 1)))
                  )
                )
              )
            )
          )
          (VarE "v_exp")
        )
      )
    )
  )
  (RuleD
    "fNmag_case_2"
    (ExpP "v_N" (VarT "N"))
    (Seq Arg Arg)
    (TupE (VarE "v_N") (CaseE (Atom INF) (TupE)))
  )
  (RuleD
    "fNmag_case_3"
    (ExpP "v_N" (VarT "N"))
    (ExpP "v_m" (VarT "m"))
    (Seq Arg Arg)
    (TupE (VarE "v_N") (CaseE (Seq (Atom NAN) Arg) (TupE (VarE "v_m"))))
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE LeOp nat (NumE (Nat 1)) (VarE "v_m"))
        (CmpE
          LtOp
          nat
          (VarE "v_m")
          (BinE PowOp nat (NumE (Nat 2)) (CallE "fun_M" (ExpA (VarE "v_N"))))
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
    (ExpP "v_N" (VarT "N"))
    (ExpP "var_0" (VarT "fNmag"))
    (Seq Arg Arg)
    (TupE (VarE "v_N") (CaseE (Seq (Atom POS) Arg) (TupE (VarE "var_0"))))
    (RulePr "wf_fNmag" (Seq Arg Arg) (TupE (VarE "v_N") (VarE "var_0")))
  )
  (RuleD
    "fN_case_1"
    (ExpP "v_N" (VarT "N"))
    (ExpP "var_0" (VarT "fNmag"))
    (Seq Arg Arg)
    (TupE (VarE "v_N") (CaseE (Seq (Atom NEG) Arg) (TupE (VarE "var_0"))))
    (RulePr "wf_fNmag" (Seq Arg Arg) (TupE (VarE "v_N") (VarE "var_0")))
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
(RelD
  "fun_fzero"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "N")) (typbind "_" (VarT "fN")))
  (RuleD
    "fun_fzero_case_0"
    (ExpP "v_N" nat)
    (Seq Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE
        (Seq (Atom POS) Arg)
        (TupE (CaseE (Seq (Atom SUBNORM) Arg) (TupE (NumE (Nat 0)))))
      )
    )
    (RulePr
      "wf_fN"
      (Seq Arg Arg)
      (TupE
        (VarE "v_N")
        (CaseE
          (Seq (Atom POS) Arg)
          (TupE (CaseE (Seq (Atom SUBNORM) Arg) (TupE (NumE (Nat 0)))))
        )
      )
    )
  )
)
(HintD (DecH "fzero" (hint "show" "+ 0")))
(RelD
  "fun_fone"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "N")) (typbind "_" (VarT "fN")))
  (RuleD
    "fun_fone_case_0"
    (ExpP "v_N" nat)
    (Seq Arg Arg)
    (TupE
      (VarE "v_N")
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
    (RulePr
      "wf_fN"
      (Seq Arg Arg)
      (TupE
        (VarE "v_N")
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
  (ExpP "v_N" (VarT "N"))
  nat
  (DefD
    (ExpP "v_N" nat)
    (ExpA (VarE "v_N"))
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
          (CvtE nat int (TheE (CallE "signif" (ExpA (VarE "v_N")))))
          (CvtE nat int (NumE (Nat 1)))
        )
      )
    )
  )
)
(TypD
  "char"
  (InstD (VariantT (typcase (Seq (Atom mk_char) Arg) (TupT (typbind "i" nat)))))
)
(DecD
  "proj_char_0"
  (ExpP "x" (VarT "char"))
  (TupT (typbind "_" nat))
  (DefD
    (ExpP "v_num_0" nat)
    (ExpA (CaseE (Seq (Atom mk_char) Arg) (TupE (VarE "v_num_0"))))
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
    (TupE (CaseE (Seq (Atom mk_char) Arg) (TupE (VarE "i"))))
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
  (RelD
    "fun_utf8"
    (Seq Arg Arg)
    (TupT
      (typbind "_" (IterT (VarT "char") List))
      (typbind "_" (IterT (VarT "byte") List))
    )
    (RuleD
      "fun_utf8_case_0"
      (ExpP "ch" (VarT "char"))
      (ExpP "b" (VarT "byte"))
      (Seq Arg Arg)
      (TupE (ListE (VarE "ch")) (ListE (VarE "b")))
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
              (Seq (Atom mk_byte) Arg)
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
          (CaseE
            (Seq (Atom mk_byte) Arg)
            (TupE (ProjE (CallE "proj_char_0" (ExpA (VarE "ch"))) 0))
          )
        )
      )
    )
    (RuleD
      "fun_utf8_case_1"
      (ExpP "ch" (VarT "char"))
      (ExpP "b_1" (VarT "byte"))
      (ExpP "b_2" (VarT "byte"))
      (Seq Arg Arg)
      (TupE (ListE (VarE "ch")) (ListE (VarE "b_1") (VarE "b_2")))
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
    (RuleD
      "fun_utf8_case_2"
      (ExpP "ch" (VarT "char"))
      (ExpP "b_1" (VarT "byte"))
      (ExpP "b_2" (VarT "byte"))
      (ExpP "b_3" (VarT "byte"))
      (Seq Arg Arg)
      (TupE (ListE (VarE "ch")) (ListE (VarE "b_1") (VarE "b_2") (VarE "b_3")))
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
    (RuleD
      "fun_utf8_case_3"
      (ExpP "ch" (VarT "char"))
      (ExpP "b_1" (VarT "byte"))
      (ExpP "b_2" (VarT "byte"))
      (ExpP "b_3" (VarT "byte"))
      (ExpP "b_4" (VarT "byte"))
      (Seq Arg Arg)
      (TupE
        (ListE (VarE "ch"))
        (ListE (VarE "b_1") (VarE "b_2") (VarE "b_3") (VarE "b_4"))
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
    (RuleD
      "fun_utf8_case_4"
      (ExpP "ch_lst" (IterT (VarT "char") List))
      (ExpP "var_2_lst" (IterT (IterT (VarT "byte") List) List))
      (ExpP "var_1_lst" (IterT (IterT (VarT "byte") List) List))
      (ExpP "var_0_lst" (IterT (IterT (VarT "byte") List) List))
      (Seq Arg Arg)
      (TupE
        (VarE "ch_lst")
        (CallE "concat_" (TypA (VarT "byte")) (ExpA (VarE "var_0_lst")))
      )
      (IfPr (CmpE EqOp bool (LenE (VarE "var_2_lst")) (LenE (VarE "ch_lst"))))
      (IterPr
        (RulePr
          "fun_utf8"
          (Seq Arg Arg)
          (TupE (ListE (VarE "ch_3")) (VarE "var_2"))
        )
        List
        (iterexp "var_2" (VarE "var_2_lst"))
        (iterexp "ch_3" (VarE "ch_lst"))
      )
      (IfPr (CmpE EqOp bool (LenE (VarE "var_1_lst")) (LenE (VarE "ch_lst"))))
      (IterPr
        (RulePr
          "fun_utf8"
          (Seq Arg Arg)
          (TupE (ListE (VarE "ch_2")) (VarE "var_1"))
        )
        List
        (iterexp "var_1" (VarE "var_1_lst"))
        (iterexp "ch_2" (VarE "ch_lst"))
      )
      (IfPr (CmpE EqOp bool (LenE (VarE "var_0_lst")) (LenE (VarE "ch_lst"))))
      (IterPr
        (RulePr
          "fun_utf8"
          (Seq Arg Arg)
          (TupE (ListE (VarE "ch")) (VarE "var_0"))
        )
        List
        (iterexp "var_0" (VarE "var_0_lst"))
        (iterexp "ch" (VarE "ch_lst"))
      )
      (IterPr
        (RulePr "wf_byte" (Seq Arg) (TupE (VarE "iter_1")))
        List
        (iterexp
          "iter_1"
          (CallE "concat_" (TypA (VarT "byte")) (ExpA (VarE "var_1_lst")))
        )
      )
      (IterPr
        (IterPr
          (RulePr "wf_byte" (Seq Arg) (TupE (VarE "iter_2")))
          List
          (iterexp "iter_2" (VarE "var_2"))
        )
        List
        (iterexp "var_2" (VarE "var_2_lst"))
      )
    )
  )
)
(TypD
  "name"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_name) Arg)
        (TupT (typbind "char_lst" (IterT (VarT "char") List)))
      )
    )
  )
)
(DecD
  "proj_name_0"
  (ExpP "x" (VarT "name"))
  (TupT (typbind "_" (IterT (VarT "char") List)))
  (DefD
    (ExpP "v_char_list_0" (IterT (VarT "char") List))
    (ExpA (CaseE (Seq (Atom mk_name) Arg) (TupE (VarE "v_char_list_0"))))
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
    (ExpP "char_lst" (IterT (VarT "char") List))
    (ExpP "var_0" (IterT (VarT "byte") List))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom mk_name) Arg) (TupE (VarE "char_lst"))))
    (RulePr "fun_utf8" (Seq Arg Arg) (TupE (VarE "char_lst") (VarE "var_0")))
    (IterPr
      (RulePr "wf_char" (Seq Arg) (TupE (VarE "v_char")))
      List
      (iterexp "v_char" (VarE "char_lst"))
    )
    (IfPr
      (CmpE
        LtOp
        nat
        (LenE (VarE "var_0"))
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
  (ExpP "var_0" (VarT "Inn"))
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
  (ExpP "var_0" (VarT "Fnn"))
  (VarT "valtype")
  (DefD (ExpA (CaseE (Atom F32) (TupE))) (CaseE (Atom F32) (TupE)))
  (DefD (ExpA (CaseE (Atom F64) (TupE))) (CaseE (Atom F64) (TupE)))
)
(HintD (TypH "Fnn" (hint "show" "F#n")))
(TypD "resulttype" (InstD (AliasT (IterT (VarT "valtype") Opt))))
(HintD (TypH "resulttype" (hint "desc" "\"result type\"")))
(TypD "mut" (InstD (AliasT (IterT (VarT "r_MUT") Opt))))
(TypD
  "limits"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_limits) Arg Arg)
        (TupT
          (typbind "v_u32" (VarT "u32"))
          (typbind "u32_opt" (IterT (VarT "u32") Opt))
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
    (ExpP "v_u32" (VarT "u32"))
    (ExpP "u32_opt" (IterT (VarT "u32") Opt))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_limits) Arg Arg)
        (TupE (VarE "v_u32") (VarE "u32_opt"))
      )
    )
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_u32")))
    (IterPr
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_u32")))
      Opt
      (iterexp "v_u32" (VarE "u32_opt"))
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
        (Seq (Atom mk_globaltype) Arg Arg)
        (TupT
          (typbind "v_mut" (VarT "mut"))
          (typbind "v_valtype" (VarT "valtype"))
        )
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
        (Seq (Atom mk_functype) Arg Arg)
        (TupT
          (typbind "valtype_lst" (IterT (VarT "valtype") List))
          (typbind "valtype_lst" (IterT (VarT "valtype") List))
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
        (TupT (typbind "v_functype" (VarT "functype")))
      )
      (typcase
        (Seq (Atom GLOBAL) Arg)
        (TupT (typbind "v_globaltype" (VarT "globaltype")))
      )
      (typcase
        (Seq (Atom TABLE) Arg)
        (TupT (typbind "v_tabletype" (VarT "tabletype")))
      )
      (typcase
        (Seq (Atom MEM) Arg)
        (TupT (typbind "v_memtype" (VarT "memtype")))
      )
    )
  )
)
(RelD
  "wf_externtype"
  (Seq Arg)
  (TupT (typbind "_" (VarT "externtype")))
  (RuleD
    "externtype_case_0"
    (ExpP "v_functype" (VarT "functype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "v_functype"))))
  )
  (RuleD
    "externtype_case_1"
    (ExpP "v_globaltype" (VarT "globaltype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "v_globaltype"))))
  )
  (RuleD
    "externtype_case_2"
    (ExpP "v_tabletype" (VarT "tabletype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "v_tabletype"))))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "v_tabletype")))
  )
  (RuleD
    "externtype_case_3"
    (ExpP "v_memtype" (VarT "memtype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "v_memtype"))))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "v_memtype")))
  )
)
(HintD (RelH "wf_externtype" (hint "wf-relation" "externtype")))
(HintD (TypH "externtype" (hint "desc" "\"external type\"")))
(DecD
  "size"
  (ExpP "v_valtype" (VarT "valtype"))
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
        (TupT (typbind "v_Inn" (VarT "Inn")) (typbind "var_x" (VarT "iN")))
      )
      (typcase
        (Seq (Atom mk_val__1) Arg Arg)
        (TupT (typbind "v_Fnn" (VarT "Fnn")) (typbind "var_x" (VarT "fN")))
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
    (ExpP "v_valtype" (VarT "valtype"))
    (ExpP "v_Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "iN"))
    (Seq Arg Arg)
    (TupE
      (VarE "v_valtype")
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (VarE "v_Inn") (VarE "var_x"))
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (CallE "size" (ExpA (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))))
        (VarE "var_x")
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "v_valtype")
        (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
      )
    )
  )
  (RuleD
    "val__case_1"
    (ExpP "v_valtype" (VarT "valtype"))
    (ExpP "v_Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "fN"))
    (Seq Arg Arg)
    (TupE
      (VarE "v_valtype")
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (VarE "v_Fnn") (VarE "var_x"))
      )
    )
    (RulePr
      "wf_fN"
      (Seq Arg Arg)
      (TupE
        (CallE "size" (ExpA (CallE "valtype_Fnn" (ExpA (VarE "v_Fnn")))))
        (VarE "var_x")
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "v_valtype")
        (CallE "valtype_Fnn" (ExpA (VarE "v_Fnn")))
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
    (ExpP "v_Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "iN"))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (VarE "v_Inn") (VarE "var_x"))
      )
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
    (ExpP "v_Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "fN"))
    (ExpA
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (VarE "v_Fnn") (VarE "var_x"))
      )
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
(TypD
  "sz"
  (InstD (VariantT (typcase (Seq (Atom mk_sz) Arg) (TupT (typbind "i" nat)))))
)
(DecD
  "proj_sz_0"
  (ExpP "x" (VarT "sz"))
  (TupT (typbind "_" nat))
  (DefD
    (ExpP "v_num_0" nat)
    (ExpA (CaseE (Seq (Atom mk_sz) Arg) (TupE (VarE "v_num_0"))))
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
    (TupE (CaseE (Seq (Atom mk_sz) Arg) (TupE (VarE "i"))))
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
        (TupT
          (typbind "v_Inn" (VarT "Inn"))
          (typbind "var_x" (VarT "unop_Inn"))
        )
      )
      (typcase
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupT
          (typbind "v_Fnn" (VarT "Fnn"))
          (typbind "var_x" (VarT "unop_Fnn"))
        )
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
    (ExpP "v_valtype" (VarT "valtype"))
    (ExpP "v_Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "unop_Inn"))
    (Seq Arg Arg)
    (TupE
      (VarE "v_valtype")
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (VarE "v_Inn") (VarE "var_x"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "v_valtype")
        (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
      )
    )
  )
  (RuleD
    "unop__case_1"
    (ExpP "v_valtype" (VarT "valtype"))
    (ExpP "v_Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "unop_Fnn"))
    (Seq Arg Arg)
    (TupE
      (VarE "v_valtype")
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (VarE "v_Fnn") (VarE "var_x"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "v_valtype")
        (CallE "valtype_Fnn" (ExpA (VarE "v_Fnn")))
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
    (ExpP "v_Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "unop_Inn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (VarE "v_Inn") (VarE "var_x"))
      )
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
    (ExpP "v_Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "unop_Fnn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (VarE "v_Fnn") (VarE "var_x"))
      )
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
      (typcase (Seq (Atom DIV) Arg) (TupT (typbind "v_sx" (VarT "sx"))))
      (typcase (Seq (Atom REM) Arg) (TupT (typbind "v_sx" (VarT "sx"))))
      (typcase (Atom AND) (TupT))
      (typcase (Atom OR) (TupT))
      (typcase (Atom XOR) (TupT))
      (typcase (Atom SHL) (TupT))
      (typcase (Seq (Atom SHR) Arg) (TupT (typbind "v_sx" (VarT "sx"))))
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
        (TupT
          (typbind "v_Inn" (VarT "Inn"))
          (typbind "var_x" (VarT "binop_Inn"))
        )
      )
      (typcase
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupT
          (typbind "v_Fnn" (VarT "Fnn"))
          (typbind "var_x" (VarT "binop_Fnn"))
        )
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
    (ExpP "v_valtype" (VarT "valtype"))
    (ExpP "v_Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "binop_Inn"))
    (Seq Arg Arg)
    (TupE
      (VarE "v_valtype")
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "v_Inn") (VarE "var_x"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "v_valtype")
        (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
      )
    )
  )
  (RuleD
    "binop__case_1"
    (ExpP "v_valtype" (VarT "valtype"))
    (ExpP "v_Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "binop_Fnn"))
    (Seq Arg Arg)
    (TupE
      (VarE "v_valtype")
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (VarE "v_Fnn") (VarE "var_x"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "v_valtype")
        (CallE "valtype_Fnn" (ExpA (VarE "v_Fnn")))
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
    (ExpP "v_Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "binop_Inn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "v_Inn") (VarE "var_x"))
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
    (ExpP "v_Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "binop_Fnn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (VarE "v_Fnn") (VarE "var_x"))
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
          (typbind "v_Inn" (VarT "Inn"))
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
    (ExpP "v_valtype" (VarT "valtype"))
    (ExpP "v_Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "testop_Inn"))
    (Seq Arg Arg)
    (TupE
      (VarE "v_valtype")
      (CaseE
        (Seq (Atom mk_testop__0) Arg Arg)
        (TupE (VarE "v_Inn") (VarE "var_x"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "v_valtype")
        (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
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
    (ExpP "v_Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "testop_Inn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_testop__0) Arg Arg)
        (TupE (VarE "v_Inn") (VarE "var_x"))
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
      (typcase (Seq (Atom LT) Arg) (TupT (typbind "v_sx" (VarT "sx"))))
      (typcase (Seq (Atom GT) Arg) (TupT (typbind "v_sx" (VarT "sx"))))
      (typcase (Seq (Atom LE) Arg) (TupT (typbind "v_sx" (VarT "sx"))))
      (typcase (Seq (Atom GE) Arg) (TupT (typbind "v_sx" (VarT "sx"))))
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
        (TupT
          (typbind "v_Inn" (VarT "Inn"))
          (typbind "var_x" (VarT "relop_Inn"))
        )
      )
      (typcase
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupT
          (typbind "v_Fnn" (VarT "Fnn"))
          (typbind "var_x" (VarT "relop_Fnn"))
        )
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
    (ExpP "v_valtype" (VarT "valtype"))
    (ExpP "v_Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "relop_Inn"))
    (Seq Arg Arg)
    (TupE
      (VarE "v_valtype")
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (VarE "v_Inn") (VarE "var_x"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "v_valtype")
        (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
      )
    )
  )
  (RuleD
    "relop__case_1"
    (ExpP "v_valtype" (VarT "valtype"))
    (ExpP "v_Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "relop_Fnn"))
    (Seq Arg Arg)
    (TupE
      (VarE "v_valtype")
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (VarE "v_Fnn") (VarE "var_x"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "v_valtype")
        (CallE "valtype_Fnn" (ExpA (VarE "v_Fnn")))
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
    (ExpP "v_Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "relop_Inn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (VarE "v_Inn") (VarE "var_x"))
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
    (ExpP "v_Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "relop_Fnn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (VarE "v_Fnn") (VarE "var_x"))
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
      (typcase (Seq (Atom EXTEND) Arg) (TupT (typbind "v_sx" (VarT "sx"))))
      (typcase (Atom WRAP) (TupT))
      (typcase (Seq (Atom CONVERT) Arg) (TupT (typbind "v_sx" (VarT "sx"))))
      (typcase (Seq (Atom TRUNC) Arg) (TupT (typbind "v_sx" (VarT "sx"))))
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
        (Seq (Atom mk_loadop_Inn) Arg Arg)
        (TupT (typbind "v_sz" (VarT "sz")) (typbind "v_sx" (VarT "sx")))
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
    (ExpP "v_Inn" (VarT "Inn"))
    (ExpP "v_sz" (VarT "sz"))
    (ExpP "v_sx" (VarT "sx"))
    (Seq Arg Arg)
    (TupE
      (VarE "v_Inn")
      (CaseE
        (Seq (Atom mk_loadop_Inn) Arg Arg)
        (TupE (VarE "v_sz") (VarE "v_sx"))
      )
    )
    (RulePr "wf_sz" (Seq Arg) (TupE (VarE "v_sz")))
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (CallE "proj_sz_0" (ExpA (VarE "v_sz"))) 0)
        (CallE "size" (ExpA (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))))
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
          (typbind "v_Inn" (VarT "Inn"))
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
    (ExpP "v_valtype" (VarT "valtype"))
    (ExpP "v_Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "loadop_Inn"))
    (Seq Arg Arg)
    (TupE
      (VarE "v_valtype")
      (CaseE
        (Seq (Atom mk_loadop__0) Arg Arg)
        (TupE (VarE "v_Inn") (VarE "var_x"))
      )
    )
    (RulePr "wf_loadop_Inn" (Seq Arg Arg) (TupE (VarE "v_Inn") (VarE "var_x")))
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "v_valtype")
        (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
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
    (ExpP "v_Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "loadop_Inn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_loadop__0) Arg Arg)
        (TupE (VarE "v_Inn") (VarE "var_x"))
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
            (typbind "v_blocktype" (VarT "blocktype"))
            (typbind "instr_lst" (IterT (VarT "instr") List))
          )
        )
        (typcase
          (Seq (Atom LOOP) Arg Arg)
          (TupT
            (typbind "v_blocktype" (VarT "blocktype"))
            (typbind "instr_lst" (IterT (VarT "instr") List))
          )
        )
        (typcase
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupT
            (typbind "v_blocktype" (VarT "blocktype"))
            (typbind "instr_lst" (IterT (VarT "instr") List))
            (typbind "instr_lst" (IterT (VarT "instr") List))
          )
        )
        (typcase
          (Seq (Atom BR) Arg)
          (TupT (typbind "v_labelidx" (VarT "labelidx")))
        )
        (typcase
          (Seq (Atom BR_IF) Arg)
          (TupT (typbind "v_labelidx" (VarT "labelidx")))
        )
        (typcase
          (Seq (Atom BR_TABLE) Arg Arg)
          (TupT
            (typbind "labelidx_lst" (IterT (VarT "labelidx") List))
            (typbind "v_labelidx" (VarT "labelidx"))
          )
        )
        (typcase
          (Seq (Atom CALL) Arg)
          (TupT (typbind "v_funcidx" (VarT "funcidx")))
        )
        (typcase
          (Seq (Atom CALL_INDIRECT) Arg)
          (TupT (typbind "v_typeidx" (VarT "typeidx")))
        )
        (typcase (Atom RETURN) (TupT))
        (typcase
          (Seq (Atom CONST) Arg Arg)
          (TupT
            (typbind "v_valtype" (VarT "valtype"))
            (typbind "_" (VarT "val_"))
          )
        )
        (typcase
          (Seq (Atom UNOP) Arg Arg)
          (TupT
            (typbind "v_valtype" (VarT "valtype"))
            (typbind "_" (VarT "unop_"))
          )
        )
        (typcase
          (Seq (Atom BINOP) Arg Arg)
          (TupT
            (typbind "v_valtype" (VarT "valtype"))
            (typbind "_" (VarT "binop_"))
          )
        )
        (typcase
          (Seq (Atom TESTOP) Arg Arg)
          (TupT
            (typbind "v_valtype" (VarT "valtype"))
            (typbind "_" (VarT "testop_"))
          )
        )
        (typcase
          (Seq (Atom RELOP) Arg Arg)
          (TupT
            (typbind "v_valtype" (VarT "valtype"))
            (typbind "_" (VarT "relop_"))
          )
        )
        (typcase
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupT
            (typbind "valtype_1" (VarT "valtype"))
            (typbind "valtype_2" (VarT "valtype"))
            (typbind "v_cvtop" (VarT "cvtop"))
          )
        )
        (typcase
          (Seq (Atom LOCAL_GET) Arg)
          (TupT (typbind "v_localidx" (VarT "localidx")))
        )
        (typcase
          (Seq (Atom LOCAL_SET) Arg)
          (TupT (typbind "v_localidx" (VarT "localidx")))
        )
        (typcase
          (Seq (Atom LOCAL_TEE) Arg)
          (TupT (typbind "v_localidx" (VarT "localidx")))
        )
        (typcase
          (Seq (Atom GLOBAL_GET) Arg)
          (TupT (typbind "v_globalidx" (VarT "globalidx")))
        )
        (typcase
          (Seq (Atom GLOBAL_SET) Arg)
          (TupT (typbind "v_globalidx" (VarT "globalidx")))
        )
        (typcase
          (Seq (Atom LOAD) Arg Arg Arg)
          (TupT
            (typbind "v_valtype" (VarT "valtype"))
            (typbind "_" (IterT (VarT "loadop_") Opt))
            (typbind "v_memarg" (VarT "memarg"))
          )
        )
        (typcase
          (Seq (Atom STORE) Arg Arg Arg)
          (TupT
            (typbind "v_valtype" (VarT "valtype"))
            (typbind "sz_opt" (IterT (VarT "sz") Opt))
            (typbind "v_memarg" (VarT "memarg"))
          )
          (ExpP "Inn_opt" (IterT (VarT "Inn") Opt))
        )
        (typcase (Atom MEMORY_SIZE) (TupT))
        (typcase (Atom MEMORY_GROW) (TupT))
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
      (ExpP "v_blocktype" (VarT "blocktype"))
      (ExpP "instr_lst" (IterT (VarT "instr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BLOCK) Arg Arg)
          (TupE (VarE "v_blocktype") (VarE "instr_lst"))
        )
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_instr")))
        List
        (iterexp "v_instr" (VarE "instr_lst"))
      )
    )
    (RuleD
      "instr_case_5"
      (ExpP "v_blocktype" (VarT "blocktype"))
      (ExpP "instr_lst" (IterT (VarT "instr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LOOP) Arg Arg)
          (TupE (VarE "v_blocktype") (VarE "instr_lst"))
        )
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_instr")))
        List
        (iterexp "v_instr" (VarE "instr_lst"))
      )
    )
    (RuleD
      "instr_case_6"
      (ExpP "v_blocktype" (VarT "blocktype"))
      (ExpP "instr_lst" (IterT (VarT "instr") List))
      (ExpP "instr_lst_0_lst" (IterT (VarT "instr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupE
            (VarE "v_blocktype")
            (VarE "instr_lst")
            (VarE "instr_lst_0_lst")
          )
        )
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_instr")))
        List
        (iterexp "v_instr" (VarE "instr_lst"))
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr_lst_0")))
        List
        (iterexp "instr_lst_0" (VarE "instr_lst_0_lst"))
      )
    )
    (RuleD
      "instr_case_7"
      (ExpP "v_labelidx" (VarT "labelidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BR) Arg) (TupE (VarE "v_labelidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_labelidx")))
    )
    (RuleD
      "instr_case_8"
      (ExpP "v_labelidx" (VarT "labelidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BR_IF) Arg) (TupE (VarE "v_labelidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_labelidx")))
    )
    (RuleD
      "instr_case_9"
      (ExpP "labelidx_lst" (IterT (VarT "labelidx") List))
      (ExpP "v_labelidx" (VarT "labelidx"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BR_TABLE) Arg Arg)
          (TupE (VarE "labelidx_lst") (VarE "v_labelidx"))
        )
      )
      (IterPr
        (RulePr
          "wf_uN"
          (Seq Arg Arg)
          (TupE (NumE (Nat 32)) (VarE "v_labelidx"))
        )
        List
        (iterexp "v_labelidx" (VarE "labelidx_lst"))
      )
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_labelidx")))
    )
    (RuleD
      "instr_case_10"
      (ExpP "v_funcidx" (VarT "funcidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "v_funcidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_funcidx")))
    )
    (RuleD
      "instr_case_11"
      (ExpP "v_typeidx" (VarT "typeidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "v_typeidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_typeidx")))
    )
    (RuleD "instr_case_12" (Seq Arg) (TupE (CaseE (Atom RETURN) (TupE))))
    (RuleD
      "instr_case_13"
      (ExpP "v_valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "val_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (VarE "v_valtype") (VarE "var_0"))
        )
      )
      (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "v_valtype") (VarE "var_0")))
    )
    (RuleD
      "instr_case_14"
      (ExpP "v_valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "unop_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom UNOP) Arg Arg)
          (TupE (VarE "v_valtype") (VarE "var_0"))
        )
      )
      (RulePr "wf_unop_" (Seq Arg Arg) (TupE (VarE "v_valtype") (VarE "var_0")))
    )
    (RuleD
      "instr_case_15"
      (ExpP "v_valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "binop_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BINOP) Arg Arg)
          (TupE (VarE "v_valtype") (VarE "var_0"))
        )
      )
      (RulePr
        "wf_binop_"
        (Seq Arg Arg)
        (TupE (VarE "v_valtype") (VarE "var_0"))
      )
    )
    (RuleD
      "instr_case_16"
      (ExpP "v_valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "testop_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom TESTOP) Arg Arg)
          (TupE (VarE "v_valtype") (VarE "var_0"))
        )
      )
      (RulePr
        "wf_testop_"
        (Seq Arg Arg)
        (TupE (VarE "v_valtype") (VarE "var_0"))
      )
    )
    (RuleD
      "instr_case_17"
      (ExpP "v_valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "relop_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom RELOP) Arg Arg)
          (TupE (VarE "v_valtype") (VarE "var_0"))
        )
      )
      (RulePr
        "wf_relop_"
        (Seq Arg Arg)
        (TupE (VarE "v_valtype") (VarE "var_0"))
      )
    )
    (RuleD
      "instr_case_18"
      (ExpP "valtype_1" (VarT "valtype"))
      (ExpP "valtype_2" (VarT "valtype"))
      (ExpP "v_cvtop" (VarT "cvtop"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupE (VarE "valtype_1") (VarE "valtype_2") (VarE "v_cvtop"))
        )
      )
      (IfPr (CmpE NeOp bool (VarE "valtype_1") (VarE "valtype_2")))
    )
    (RuleD
      "instr_case_19"
      (ExpP "v_localidx" (VarT "localidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL_GET) Arg) (TupE (VarE "v_localidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_localidx")))
    )
    (RuleD
      "instr_case_20"
      (ExpP "v_localidx" (VarT "localidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL_SET) Arg) (TupE (VarE "v_localidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_localidx")))
    )
    (RuleD
      "instr_case_21"
      (ExpP "v_localidx" (VarT "localidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL_TEE) Arg) (TupE (VarE "v_localidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_localidx")))
    )
    (RuleD
      "instr_case_22"
      (ExpP "v_globalidx" (VarT "globalidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL_GET) Arg) (TupE (VarE "v_globalidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_globalidx")))
    )
    (RuleD
      "instr_case_23"
      (ExpP "v_globalidx" (VarT "globalidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL_SET) Arg) (TupE (VarE "v_globalidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_globalidx")))
    )
    (RuleD
      "instr_case_24"
      (ExpP "v_valtype" (VarT "valtype"))
      (ExpP "var_0_opt" (IterT (VarT "loadop_") Opt))
      (ExpP "v_memarg" (VarT "memarg"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LOAD) Arg Arg Arg)
          (TupE (VarE "v_valtype") (VarE "var_0_opt") (VarE "v_memarg"))
        )
      )
      (IterPr
        (RulePr
          "wf_loadop_"
          (Seq Arg Arg)
          (TupE (VarE "v_valtype") (VarE "var_0"))
        )
        Opt
        (iterexp "var_0" (VarE "var_0_opt"))
      )
      (RulePr "wf_memarg" (Seq Arg) (TupE (VarE "v_memarg")))
    )
    (RuleD
      "instr_case_25"
      (ExpP "Inn_opt" (IterT (VarT "Inn") Opt))
      (ExpP "v_valtype" (VarT "valtype"))
      (ExpP "sz_opt" (IterT (VarT "sz") Opt))
      (ExpP "v_memarg" (VarT "memarg"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom STORE) Arg Arg Arg)
          (TupE (VarE "v_valtype") (VarE "sz_opt") (VarE "v_memarg"))
        )
      )
      (IterPr
        (RulePr "wf_sz" (Seq Arg) (TupE (VarE "v_sz")))
        Opt
        (iterexp "v_sz" (VarE "sz_opt"))
      )
      (RulePr "wf_memarg" (Seq Arg) (TupE (VarE "v_memarg")))
      (IfPr
        (BinE
          EquivOp
          bool
          (CmpE EqOp bool (VarE "Inn_opt") (OptE))
          (CmpE EqOp bool (VarE "sz_opt") (OptE))
        )
      )
      (IterPr
        (IfPr
          (BinE
            AndOp
            bool
            (CmpE
              EqOp
              bool
              (VarE "v_valtype")
              (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
            )
            (CmpE
              LtOp
              nat
              (ProjE (CallE "proj_sz_0" (ExpA (VarE "v_sz"))) 0)
              (CallE "size" (ExpA (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))))
            )
          )
        )
        Opt
        (iterexp "v_Inn" (VarE "Inn_opt"))
        (iterexp "v_sz" (VarE "sz_opt"))
      )
    )
    (RuleD "instr_case_26" (Seq Arg) (TupE (CaseE (Atom MEMORY_SIZE) (TupE))))
    (RuleD "instr_case_27" (Seq Arg) (TupE (CaseE (Atom MEMORY_GROW) (TupE))))
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
        (TupT (typbind "v_functype" (VarT "functype")))
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
        (TupT (typbind "v_valtype" (VarT "valtype")))
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
          (typbind "v_typeidx" (VarT "typeidx"))
          (typbind "local_lst" (IterT (VarT "local") List))
          (typbind "v_expr" (VarT "expr"))
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
    (ExpP "v_typeidx" (VarT "typeidx"))
    (ExpP "local_lst" (IterT (VarT "local") List))
    (ExpP "v_expr" (VarT "expr"))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom FUNC) Arg Arg Arg)
        (TupE (VarE "v_typeidx") (VarE "local_lst") (VarE "v_expr"))
      )
    )
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_typeidx")))
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_expr")))
      List
      (iterexp "v_expr" (VarE "v_expr"))
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
          (typbind "v_globaltype" (VarT "globaltype"))
          (typbind "v_expr" (VarT "expr"))
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
    (ExpP "v_globaltype" (VarT "globaltype"))
    (ExpP "v_expr" (VarT "expr"))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom GLOBAL) Arg Arg)
        (TupE (VarE "v_globaltype") (VarE "v_expr"))
      )
    )
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_expr")))
      List
      (iterexp "v_expr" (VarE "v_expr"))
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
        (TupT (typbind "v_tabletype" (VarT "tabletype")))
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
    (ExpP "v_tabletype" (VarT "tabletype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "v_tabletype"))))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "v_tabletype")))
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
        (TupT (typbind "v_memtype" (VarT "memtype")))
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
    (ExpP "v_memtype" (VarT "memtype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom MEMORY) Arg) (TupE (VarE "v_memtype"))))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "v_memtype")))
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
          (typbind "v_expr" (VarT "expr"))
          (typbind "funcidx_lst" (IterT (VarT "funcidx") List))
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
    (ExpP "v_expr" (VarT "expr"))
    (ExpP "funcidx_lst" (IterT (VarT "funcidx") List))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom ELEM) Arg Arg)
        (TupE (VarE "v_expr") (VarE "funcidx_lst"))
      )
    )
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_expr")))
      List
      (iterexp "v_expr" (VarE "v_expr"))
    )
    (IterPr
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_funcidx")))
      List
      (iterexp "v_funcidx" (VarE "funcidx_lst"))
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
          (typbind "v_expr" (VarT "expr"))
          (typbind "byte_lst" (IterT (VarT "byte") List))
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
    (ExpP "v_expr" (VarT "expr"))
    (ExpP "byte_lst" (IterT (VarT "byte") List))
    (Seq Arg)
    (TupE
      (CaseE (Seq (Atom DATA) Arg Arg) (TupE (VarE "v_expr") (VarE "byte_lst")))
    )
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_expr")))
      List
      (iterexp "v_expr" (VarE "v_expr"))
    )
    (IterPr
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "v_byte")))
      List
      (iterexp "v_byte" (VarE "byte_lst"))
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
        (TupT (typbind "v_funcidx" (VarT "funcidx")))
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
    (ExpP "v_funcidx" (VarT "funcidx"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom START) Arg) (TupE (VarE "v_funcidx"))))
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_funcidx")))
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
        (TupT (typbind "v_funcidx" (VarT "funcidx")))
      )
      (typcase
        (Seq (Atom GLOBAL) Arg)
        (TupT (typbind "v_globalidx" (VarT "globalidx")))
      )
      (typcase
        (Seq (Atom TABLE) Arg)
        (TupT (typbind "v_tableidx" (VarT "tableidx")))
      )
      (typcase (Seq (Atom MEM) Arg) (TupT (typbind "v_memidx" (VarT "memidx"))))
    )
  )
)
(RelD
  "wf_externidx"
  (Seq Arg)
  (TupT (typbind "_" (VarT "externidx")))
  (RuleD
    "externidx_case_0"
    (ExpP "v_funcidx" (VarT "funcidx"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "v_funcidx"))))
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_funcidx")))
  )
  (RuleD
    "externidx_case_1"
    (ExpP "v_globalidx" (VarT "globalidx"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "v_globalidx"))))
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_globalidx")))
  )
  (RuleD
    "externidx_case_2"
    (ExpP "v_tableidx" (VarT "tableidx"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "v_tableidx"))))
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_tableidx")))
  )
  (RuleD
    "externidx_case_3"
    (ExpP "v_memidx" (VarT "memidx"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "v_memidx"))))
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_memidx")))
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
          (typbind "v_name" (VarT "name"))
          (typbind "v_externidx" (VarT "externidx"))
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
    (ExpP "v_name" (VarT "name"))
    (ExpP "v_externidx" (VarT "externidx"))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom EXPORT) Arg Arg)
        (TupE (VarE "v_name") (VarE "v_externidx"))
      )
    )
    (RulePr "wf_name" (Seq Arg) (TupE (VarE "v_name")))
    (RulePr "wf_externidx" (Seq Arg) (TupE (VarE "v_externidx")))
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
          (typbind "v_name" (VarT "name"))
          (typbind "v_name" (VarT "name"))
          (typbind "v_externtype" (VarT "externtype"))
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
    (ExpP "v_name" (VarT "name"))
    (ExpP "name_0" (VarT "name"))
    (ExpP "v_externtype" (VarT "externtype"))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom IMPORT) Arg Arg Arg)
        (TupE (VarE "v_name") (VarE "name_0") (VarE "v_externtype"))
      )
    )
    (RulePr "wf_name" (Seq Arg) (TupE (VarE "v_name")))
    (RulePr "wf_name" (Seq Arg) (TupE (VarE "name_0")))
    (RulePr "wf_externtype" (Seq Arg) (TupE (VarE "v_externtype")))
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
          (typbind "type_lst" (IterT (VarT "type") List))
          (typbind "import_lst" (IterT (VarT "import") List))
          (typbind "func_lst" (IterT (VarT "func") List))
          (typbind "global_lst" (IterT (VarT "global") List))
          (typbind "table_lst" (IterT (VarT "table") List))
          (typbind "mem_lst" (IterT (VarT "mem") List))
          (typbind "elem_lst" (IterT (VarT "elem") List))
          (typbind "data_lst" (IterT (VarT "data") List))
          (typbind "start_opt" (IterT (VarT "start") Opt))
          (typbind "export_lst" (IterT (VarT "export") List))
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
    (ExpP "type_lst" (IterT (VarT "type") List))
    (ExpP "import_lst" (IterT (VarT "import") List))
    (ExpP "func_lst" (IterT (VarT "func") List))
    (ExpP "global_lst" (IterT (VarT "global") List))
    (ExpP "table_lst" (IterT (VarT "table") List))
    (ExpP "mem_lst" (IterT (VarT "mem") List))
    (ExpP "elem_lst" (IterT (VarT "elem") List))
    (ExpP "data_lst" (IterT (VarT "data") List))
    (ExpP "start_opt" (IterT (VarT "start") Opt))
    (ExpP "export_lst" (IterT (VarT "export") List))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
        (TupE
          (VarE "type_lst")
          (VarE "import_lst")
          (VarE "func_lst")
          (VarE "global_lst")
          (VarE "table_lst")
          (VarE "mem_lst")
          (VarE "elem_lst")
          (VarE "data_lst")
          (VarE "start_opt")
          (VarE "export_lst")
        )
      )
    )
    (IterPr
      (RulePr "wf_import" (Seq Arg) (TupE (VarE "v_import")))
      List
      (iterexp "v_import" (VarE "import_lst"))
    )
    (IterPr
      (RulePr "wf_func" (Seq Arg) (TupE (VarE "v_func")))
      List
      (iterexp "v_func" (VarE "func_lst"))
    )
    (IterPr
      (RulePr "wf_global" (Seq Arg) (TupE (VarE "v_global")))
      List
      (iterexp "v_global" (VarE "global_lst"))
    )
    (IterPr
      (RulePr "wf_table" (Seq Arg) (TupE (VarE "v_table")))
      List
      (iterexp "v_table" (VarE "table_lst"))
    )
    (IterPr
      (RulePr "wf_mem" (Seq Arg) (TupE (VarE "v_mem")))
      List
      (iterexp "v_mem" (VarE "mem_lst"))
    )
    (IterPr
      (RulePr "wf_elem" (Seq Arg) (TupE (VarE "v_elem")))
      List
      (iterexp "v_elem" (VarE "elem_lst"))
    )
    (IterPr
      (RulePr "wf_data" (Seq Arg) (TupE (VarE "v_data")))
      List
      (iterexp "v_data" (VarE "data_lst"))
    )
    (IterPr
      (RulePr "wf_start" (Seq Arg) (TupE (VarE "v_start")))
      Opt
      (iterexp "v_start" (VarE "start_opt"))
    )
    (IterPr
      (RulePr "wf_export" (Seq Arg) (TupE (VarE "v_export")))
      List
      (iterexp "v_export" (VarE "export_lst"))
    )
  )
)
(HintD (RelH "wf_module" (hint "wf-relation" "module")))
(HintD (TypH "module" (hint "desc" "\"module\"")))
(RecD
  (RelD
    "fun_funcsxt"
    (Seq Arg Arg)
    (TupT
      (typbind "_" (IterT (VarT "externtype") List))
      (typbind "_" (IterT (VarT "functype") List))
    )
    (RuleD "fun_funcsxt_case_0" (Seq Arg Arg) (TupE (ListE) (ListE)))
    (RuleD
      "fun_funcsxt_case_1"
      (ExpP "ft" (VarT "functype"))
      (ExpP "xt_lst" (IterT (VarT "externtype") List))
      (ExpP "var_0" (IterT (VarT "functype") List))
      (Seq Arg Arg)
      (TupE
        (CatE
          (ListE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "ft"))))
          (VarE "xt_lst")
        )
        (CatE (ListE (VarE "ft")) (VarE "var_0"))
      )
      (RulePr "fun_funcsxt" (Seq Arg Arg) (TupE (VarE "xt_lst") (VarE "var_0")))
    )
    (RuleD
      "fun_funcsxt_case_2"
      (ExpP "v_externtype" (VarT "externtype"))
      (ExpP "xt_lst" (IterT (VarT "externtype") List))
      (ExpP "var_0" (IterT (VarT "functype") List))
      (Seq Arg Arg)
      (TupE (CatE (ListE (VarE "v_externtype")) (VarE "xt_lst")) (VarE "var_0"))
      (RulePr "fun_funcsxt" (Seq Arg Arg) (TupE (VarE "xt_lst") (VarE "var_0")))
    )
  )
)
(HintD (DecH "funcsxt" (hint "show" "$funcs(%)")))
(RecD
  (RelD
    "fun_globalsxt"
    (Seq Arg Arg)
    (TupT
      (typbind "_" (IterT (VarT "externtype") List))
      (typbind "_" (IterT (VarT "globaltype") List))
    )
    (RuleD "fun_globalsxt_case_0" (Seq Arg Arg) (TupE (ListE) (ListE)))
    (RuleD
      "fun_globalsxt_case_1"
      (ExpP "gt" (VarT "globaltype"))
      (ExpP "xt_lst" (IterT (VarT "externtype") List))
      (ExpP "var_0" (IterT (VarT "globaltype") List))
      (Seq Arg Arg)
      (TupE
        (CatE
          (ListE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "gt"))))
          (VarE "xt_lst")
        )
        (CatE (ListE (VarE "gt")) (VarE "var_0"))
      )
      (RulePr
        "fun_globalsxt"
        (Seq Arg Arg)
        (TupE (VarE "xt_lst") (VarE "var_0"))
      )
    )
    (RuleD
      "fun_globalsxt_case_2"
      (ExpP "v_externtype" (VarT "externtype"))
      (ExpP "xt_lst" (IterT (VarT "externtype") List))
      (ExpP "var_0" (IterT (VarT "globaltype") List))
      (Seq Arg Arg)
      (TupE (CatE (ListE (VarE "v_externtype")) (VarE "xt_lst")) (VarE "var_0"))
      (RulePr
        "fun_globalsxt"
        (Seq Arg Arg)
        (TupE (VarE "xt_lst") (VarE "var_0"))
      )
    )
  )
)
(HintD (DecH "globalsxt" (hint "show" "$globals(%)")))
(RecD
  (RelD
    "fun_tablesxt"
    (Seq Arg Arg)
    (TupT
      (typbind "_" (IterT (VarT "externtype") List))
      (typbind "_" (IterT (VarT "tabletype") List))
    )
    (RuleD "fun_tablesxt_case_0" (Seq Arg Arg) (TupE (ListE) (ListE)))
    (RuleD
      "fun_tablesxt_case_1"
      (ExpP "tt" (VarT "limits"))
      (ExpP "xt_lst" (IterT (VarT "externtype") List))
      (ExpP "var_1" (IterT (VarT "tabletype") List))
      (ExpP "var_0" (IterT (VarT "tabletype") List))
      (Seq Arg Arg)
      (TupE
        (CatE
          (ListE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tt"))))
          (VarE "xt_lst")
        )
        (CatE (ListE (VarE "tt")) (VarE "var_0"))
      )
      (RulePr
        "fun_tablesxt"
        (Seq Arg Arg)
        (TupE (VarE "xt_lst") (VarE "var_1"))
      )
      (RulePr
        "fun_tablesxt"
        (Seq Arg Arg)
        (TupE (VarE "xt_lst") (VarE "var_0"))
      )
      (IterPr
        (RulePr "wf_limits" (Seq Arg) (TupE (VarE "iter_3")))
        List
        (iterexp "iter_3" (VarE "var_1"))
      )
    )
    (RuleD
      "fun_tablesxt_case_2"
      (ExpP "v_externtype" (VarT "externtype"))
      (ExpP "xt_lst" (IterT (VarT "externtype") List))
      (ExpP "var_1" (IterT (VarT "tabletype") List))
      (ExpP "var_0" (IterT (VarT "tabletype") List))
      (Seq Arg Arg)
      (TupE (CatE (ListE (VarE "v_externtype")) (VarE "xt_lst")) (VarE "var_0"))
      (RulePr
        "fun_tablesxt"
        (Seq Arg Arg)
        (TupE (VarE "xt_lst") (VarE "var_1"))
      )
      (RulePr
        "fun_tablesxt"
        (Seq Arg Arg)
        (TupE (VarE "xt_lst") (VarE "var_0"))
      )
      (IterPr
        (RulePr "wf_limits" (Seq Arg) (TupE (VarE "iter_4")))
        List
        (iterexp "iter_4" (VarE "var_1"))
      )
    )
  )
)
(HintD (DecH "tablesxt" (hint "show" "$tables(%)")))
(RecD
  (RelD
    "fun_memsxt"
    (Seq Arg Arg)
    (TupT
      (typbind "_" (IterT (VarT "externtype") List))
      (typbind "_" (IterT (VarT "memtype") List))
    )
    (RuleD "fun_memsxt_case_0" (Seq Arg Arg) (TupE (ListE) (ListE)))
    (RuleD
      "fun_memsxt_case_1"
      (ExpP "mt" (VarT "limits"))
      (ExpP "xt_lst" (IterT (VarT "externtype") List))
      (ExpP "var_1" (IterT (VarT "memtype") List))
      (ExpP "var_0" (IterT (VarT "memtype") List))
      (Seq Arg Arg)
      (TupE
        (CatE
          (ListE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "mt"))))
          (VarE "xt_lst")
        )
        (CatE (ListE (VarE "mt")) (VarE "var_0"))
      )
      (RulePr "fun_memsxt" (Seq Arg Arg) (TupE (VarE "xt_lst") (VarE "var_1")))
      (RulePr "fun_memsxt" (Seq Arg Arg) (TupE (VarE "xt_lst") (VarE "var_0")))
      (IterPr
        (RulePr "wf_limits" (Seq Arg) (TupE (VarE "iter_5")))
        List
        (iterexp "iter_5" (VarE "var_1"))
      )
    )
    (RuleD
      "fun_memsxt_case_2"
      (ExpP "v_externtype" (VarT "externtype"))
      (ExpP "xt_lst" (IterT (VarT "externtype") List))
      (ExpP "var_1" (IterT (VarT "memtype") List))
      (ExpP "var_0" (IterT (VarT "memtype") List))
      (Seq Arg Arg)
      (TupE (CatE (ListE (VarE "v_externtype")) (VarE "xt_lst")) (VarE "var_0"))
      (RulePr "fun_memsxt" (Seq Arg Arg) (TupE (VarE "xt_lst") (VarE "var_1")))
      (RulePr "fun_memsxt" (Seq Arg Arg) (TupE (VarE "xt_lst") (VarE "var_0")))
      (IterPr
        (RulePr "wf_limits" (Seq Arg) (TupE (VarE "iter_6")))
        List
        (iterexp "iter_6" (VarE "var_1"))
      )
    )
  )
)
(HintD (DecH "memsxt" (hint "show" "$mems(%)")))
(RelD
  "fun_memarg0"
  (Seq Arg)
  (TupT (typbind "_" (VarT "memarg")))
  (RuleD
    "fun_memarg0_case_0"
    (Seq Arg)
    (TupE
      (StrE
        (expfield
          (Atom ALIGN)
          (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
        )
        (expfield
          (Atom OFFSET)
          (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
        )
      )
    )
    (RulePr
      "wf_memarg"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom ALIGN)
            (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
          )
          (expfield
            (Atom OFFSET)
            (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
          )
        )
      )
    )
  )
)
(HintD (DecH "memarg0" (hint "show" "{}")))
(DecD
  "bool"
  (ExpP "v_bool" BoolT)
  nat
  (DefD (ExpA (BoolE false)) (NumE (Nat 0)))
  (DefD (ExpA (BoolE true)) (NumE (Nat 1)))
)
(DecD "truncz" (ExpP "rat" rat) int)
(HintD (DecH "truncz" (hint "builtin" "{}")))
(RelD
  "fun_signed_"
  (Seq Arg Arg Arg)
  (TupT (typbind "_" (VarT "N")) (typbind "_" nat) (typbind "_" int))
  (RuleD
    "fun_signed__case_0"
    (ExpP "v_N" nat)
    (ExpP "i" nat)
    (Seq Arg Arg Arg)
    (TupE (VarE "v_N") (VarE "i") (CvtE nat int (VarE "i")))
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
              (CvtE nat int (VarE "v_N"))
              (CvtE nat int (NumE (Nat 1)))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_signed__case_1"
    (ExpP "v_N" nat)
    (ExpP "i" nat)
    (Seq Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (VarE "i")
      (BinE
        SubOp
        int
        (CvtE nat int (VarE "i"))
        (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (VarE "v_N")))
      )
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
                (CvtE nat int (VarE "v_N"))
                (CvtE nat int (NumE (Nat 1)))
              )
            )
          )
          (VarE "i")
        )
        (CmpE LtOp nat (VarE "i") (BinE PowOp nat (NumE (Nat 2)) (VarE "v_N")))
      )
    )
  )
)
(HintD (DecH "signed_" (hint "inverse" "$inv_signed_")))
(RelD
  "fun_inv_signed_"
  (Seq Arg Arg Arg)
  (TupT (typbind "_" (VarT "N")) (typbind "_" int) (typbind "_" nat))
  (RuleD
    "fun_inv_signed__case_0"
    (ExpP "v_N" nat)
    (ExpP "i" int)
    (Seq Arg Arg Arg)
    (TupE (VarE "v_N") (VarE "i") (CvtE int nat (VarE "i")))
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
                  (CvtE nat int (VarE "v_N"))
                  (CvtE nat int (NumE (Nat 1)))
                )
              )
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_inv_signed__case_1"
    (ExpP "v_N" nat)
    (ExpP "i" int)
    (Seq Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (VarE "i")
      (CvtE
        int
        nat
        (BinE
          AddOp
          int
          (VarE "i")
          (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (VarE "v_N")))
        )
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
                    (CvtE nat int (VarE "v_N"))
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
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fceil_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "ffloor_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fnearest_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fneg_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fsqrt_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "ftrunc_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD "iclz_" (ExpP "v_N" (VarT "N")) (ExpP "v_iN" (VarT "iN")) (VarT "iN"))
(DecD "ictz_" (ExpP "v_N" (VarT "N")) (ExpP "v_iN" (VarT "iN")) (VarT "iN"))
(DecD "ipopcnt_" (ExpP "v_N" (VarT "N")) (ExpP "v_iN" (VarT "iN")) (VarT "iN"))
(RelD
  "fun_unop__before_fun_unop__case_20"
  (Seq Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "valtype"))
    (typbind "_" (VarT "unop_"))
    (typbind "_" (VarT "val_"))
  )
  (RuleD
    "fun_unop__case_19"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom NEAREST) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
          (VarE "iter_20")
        )
      )
      List
      (iterexp
        "iter_20"
        (CallE
          "fnearest_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_27"))
          )
        )
      )
      List
      (iterexp
        "iter_0_27"
        (CallE
          "fnearest_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_18"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom NEAREST) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
          (VarE "iter_19")
        )
      )
      List
      (iterexp
        "iter_19"
        (CallE
          "fnearest_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_25"))
          )
        )
      )
      List
      (iterexp
        "iter_0_25"
        (CallE
          "fnearest_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_17"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom TRUNC) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
          (VarE "iter_18")
        )
      )
      List
      (iterexp
        "iter_18"
        (CallE
          "ftrunc_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_23"))
          )
        )
      )
      List
      (iterexp
        "iter_0_23"
        (CallE
          "ftrunc_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_16"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom TRUNC) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
          (VarE "iter_17")
        )
      )
      List
      (iterexp
        "iter_17"
        (CallE
          "ftrunc_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_21"))
          )
        )
      )
      List
      (iterexp
        "iter_0_21"
        (CallE
          "ftrunc_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_15"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom FLOOR) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
          (VarE "iter_16")
        )
      )
      List
      (iterexp
        "iter_16"
        (CallE
          "ffloor_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_19"))
          )
        )
      )
      List
      (iterexp
        "iter_0_19"
        (CallE
          "ffloor_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_14"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom FLOOR) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
          (VarE "iter_15")
        )
      )
      List
      (iterexp
        "iter_15"
        (CallE
          "ffloor_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_17"))
          )
        )
      )
      List
      (iterexp
        "iter_0_17"
        (CallE
          "ffloor_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_13"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom CEIL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
          (VarE "iter_14")
        )
      )
      List
      (iterexp
        "iter_14"
        (CallE
          "fceil_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_15"))
          )
        )
      )
      List
      (iterexp
        "iter_0_15"
        (CallE
          "fceil_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_12"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom CEIL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
          (VarE "iter_13")
        )
      )
      List
      (iterexp
        "iter_13"
        (CallE
          "fceil_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_13"))
          )
        )
      )
      List
      (iterexp
        "iter_0_13"
        (CallE
          "fceil_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_11"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom SQRT) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
          (VarE "iter_12")
        )
      )
      List
      (iterexp
        "iter_12"
        (CallE
          "fsqrt_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_11"))
          )
        )
      )
      List
      (iterexp
        "iter_0_11"
        (CallE
          "fsqrt_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_10"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom SQRT) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
          (VarE "iter_11")
        )
      )
      List
      (iterexp
        "iter_11"
        (CallE
          "fsqrt_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_9"))
          )
        )
      )
      List
      (iterexp
        "iter_0_9"
        (CallE
          "fsqrt_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_9"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom NEG) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
          (VarE "iter_10")
        )
      )
      List
      (iterexp
        "iter_10"
        (CallE
          "fneg_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_7"))
          )
        )
      )
      List
      (iterexp
        "iter_0_7"
        (CallE
          "fneg_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_8"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom NEG) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
          (VarE "iter_9")
        )
      )
      List
      (iterexp
        "iter_9"
        (CallE
          "fneg_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_5"))
          )
        )
      )
      List
      (iterexp
        "iter_0_5"
        (CallE
          "fneg_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_7"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom ABS) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
          (VarE "iter_8")
        )
      )
      List
      (iterexp
        "iter_8"
        (CallE
          "fabs_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_3"))
          )
        )
      )
      List
      (iterexp
        "iter_0_3"
        (CallE
          "fabs_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_6"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom ABS) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
          (VarE "iter_7")
        )
      )
      List
      (iterexp
        "iter_7"
        (CallE
          "fabs_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_1"))
          )
        )
      )
      List
      (iterexp
        "iter_0_1"
        (CallE
          "fabs_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_5"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom POPCNT) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_4"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom POPCNT) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_3"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom CTZ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_2"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom CTZ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_1"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom CLZ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_0"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom CLZ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
)
(RelD
  "fun_unop_"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "valtype"))
    (typbind "_" (VarT "unop_"))
    (typbind "_" (VarT "val_"))
    (typbind "_" (IterT (IterT (VarT "val_") List) Opt))
  )
  (RuleD
    "fun_unop__case_0"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom CLZ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "v_iN"))
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
              "iclz_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_1"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom CLZ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "v_iN"))
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
              "iclz_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_2"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom CTZ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "v_iN"))
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
              "ictz_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_3"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom CTZ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "v_iN"))
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
              "ictz_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_4"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom POPCNT) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "v_iN"))
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
              "ipopcnt_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
                )
              )
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_5"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom POPCNT) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "v_iN"))
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
              "ipopcnt_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
                )
              )
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_6"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom ABS) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_2"))
          )
          List
          (iterexp
            "iter_0_2"
            (CallE
              "fabs_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
                )
              )
              (ExpA (VarE "v_fN"))
            )
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
          (VarE "iter_7")
        )
      )
      List
      (iterexp
        "iter_7"
        (CallE
          "fabs_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_1"))
          )
        )
      )
      List
      (iterexp
        "iter_0_1"
        (CallE
          "fabs_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_7"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom ABS) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_4"))
          )
          List
          (iterexp
            "iter_0_4"
            (CallE
              "fabs_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
                )
              )
              (ExpA (VarE "v_fN"))
            )
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
          (VarE "iter_8")
        )
      )
      List
      (iterexp
        "iter_8"
        (CallE
          "fabs_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_3"))
          )
        )
      )
      List
      (iterexp
        "iter_0_3"
        (CallE
          "fabs_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_8"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom NEG) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_6"))
          )
          List
          (iterexp
            "iter_0_6"
            (CallE
              "fneg_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
                )
              )
              (ExpA (VarE "v_fN"))
            )
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
          (VarE "iter_9")
        )
      )
      List
      (iterexp
        "iter_9"
        (CallE
          "fneg_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_5"))
          )
        )
      )
      List
      (iterexp
        "iter_0_5"
        (CallE
          "fneg_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_9"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom NEG) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_8"))
          )
          List
          (iterexp
            "iter_0_8"
            (CallE
              "fneg_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
                )
              )
              (ExpA (VarE "v_fN"))
            )
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
          (VarE "iter_10")
        )
      )
      List
      (iterexp
        "iter_10"
        (CallE
          "fneg_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_7"))
          )
        )
      )
      List
      (iterexp
        "iter_0_7"
        (CallE
          "fneg_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_10"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom SQRT) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_10"))
          )
          List
          (iterexp
            "iter_0_10"
            (CallE
              "fsqrt_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
                )
              )
              (ExpA (VarE "v_fN"))
            )
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
          (VarE "iter_11")
        )
      )
      List
      (iterexp
        "iter_11"
        (CallE
          "fsqrt_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_9"))
          )
        )
      )
      List
      (iterexp
        "iter_0_9"
        (CallE
          "fsqrt_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_11"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom SQRT) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_12"))
          )
          List
          (iterexp
            "iter_0_12"
            (CallE
              "fsqrt_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
                )
              )
              (ExpA (VarE "v_fN"))
            )
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
          (VarE "iter_12")
        )
      )
      List
      (iterexp
        "iter_12"
        (CallE
          "fsqrt_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_11"))
          )
        )
      )
      List
      (iterexp
        "iter_0_11"
        (CallE
          "fsqrt_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_12"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom CEIL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_14"))
          )
          List
          (iterexp
            "iter_0_14"
            (CallE
              "fceil_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
                )
              )
              (ExpA (VarE "v_fN"))
            )
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
          (VarE "iter_13")
        )
      )
      List
      (iterexp
        "iter_13"
        (CallE
          "fceil_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_13"))
          )
        )
      )
      List
      (iterexp
        "iter_0_13"
        (CallE
          "fceil_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_13"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom CEIL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_16"))
          )
          List
          (iterexp
            "iter_0_16"
            (CallE
              "fceil_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
                )
              )
              (ExpA (VarE "v_fN"))
            )
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
          (VarE "iter_14")
        )
      )
      List
      (iterexp
        "iter_14"
        (CallE
          "fceil_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_15"))
          )
        )
      )
      List
      (iterexp
        "iter_0_15"
        (CallE
          "fceil_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_14"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom FLOOR) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_18"))
          )
          List
          (iterexp
            "iter_0_18"
            (CallE
              "ffloor_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
                )
              )
              (ExpA (VarE "v_fN"))
            )
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
          (VarE "iter_15")
        )
      )
      List
      (iterexp
        "iter_15"
        (CallE
          "ffloor_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_17"))
          )
        )
      )
      List
      (iterexp
        "iter_0_17"
        (CallE
          "ffloor_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_15"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom FLOOR) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_20"))
          )
          List
          (iterexp
            "iter_0_20"
            (CallE
              "ffloor_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
                )
              )
              (ExpA (VarE "v_fN"))
            )
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
          (VarE "iter_16")
        )
      )
      List
      (iterexp
        "iter_16"
        (CallE
          "ffloor_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_19"))
          )
        )
      )
      List
      (iterexp
        "iter_0_19"
        (CallE
          "ffloor_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_16"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom TRUNC) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_22"))
          )
          List
          (iterexp
            "iter_0_22"
            (CallE
              "ftrunc_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
                )
              )
              (ExpA (VarE "v_fN"))
            )
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
          (VarE "iter_17")
        )
      )
      List
      (iterexp
        "iter_17"
        (CallE
          "ftrunc_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_21"))
          )
        )
      )
      List
      (iterexp
        "iter_0_21"
        (CallE
          "ftrunc_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_17"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom TRUNC) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_24"))
          )
          List
          (iterexp
            "iter_0_24"
            (CallE
              "ftrunc_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
                )
              )
              (ExpA (VarE "v_fN"))
            )
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
          (VarE "iter_18")
        )
      )
      List
      (iterexp
        "iter_18"
        (CallE
          "ftrunc_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_23"))
          )
        )
      )
      List
      (iterexp
        "iter_0_23"
        (CallE
          "ftrunc_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_18"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom NEAREST) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_26"))
          )
          List
          (iterexp
            "iter_0_26"
            (CallE
              "fnearest_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
                )
              )
              (ExpA (VarE "v_fN"))
            )
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
          (VarE "iter_19")
        )
      )
      List
      (iterexp
        "iter_19"
        (CallE
          "fnearest_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_25"))
          )
        )
      )
      List
      (iterexp
        "iter_0_25"
        (CallE
          "fnearest_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_19"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom NEAREST) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_28"))
          )
          List
          (iterexp
            "iter_0_28"
            (CallE
              "fnearest_"
              (ExpA
                (CallE
                  "size"
                  (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
                )
              )
              (ExpA (VarE "v_fN"))
            )
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
          (VarE "iter_20")
        )
      )
      List
      (iterexp
        "iter_20"
        (CallE
          "fnearest_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_27"))
          )
        )
      )
      List
      (iterexp
        "iter_0_27"
        (CallE
          "fnearest_"
          (ExpA
            (CallE
              "size"
              (ExpA (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE)))))
            )
          )
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_unop__case_20"
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "unop_"))
    (ExpP "x2" (VarT "val_"))
    (Seq Arg Arg Arg Arg)
    (TupE (VarE "x0") (VarE "x1") (VarE "x2") (OptE))
    (NegPr
      (RulePr
        "fun_unop__before_fun_unop__case_20"
        (Seq Arg Arg Arg)
        (TupE (VarE "x0") (VarE "x1") (VarE "x2"))
      )
    )
  )
)
(HintD (DecH "unop_" (hint "partial" "{}")))
(HintD (DecH "unop_" (hint "show" "%2#$_(%1)#((%3))")))
(DecD
  "fadd_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (ExpP "fN_0" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fcopysign_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (ExpP "fN_0" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fdiv_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (ExpP "fN_0" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fmax_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (ExpP "fN_0" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fmin_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (ExpP "fN_0" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fmul_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (ExpP "fN_0" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "fsub_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (ExpP "fN_0" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(RelD
  "fun_iadd_"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "N"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "iN"))
  )
  (RuleD
    "fun_iadd__case_0"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (VarE "i_1")
      (VarE "i_2")
      (CaseE
        (Seq (Atom mk_uN) Arg)
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
            (BinE PowOp nat (NumE (Nat 2)) (VarE "v_N"))
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (VarE "v_N")
        (CaseE
          (Seq (Atom mk_uN) Arg)
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
              (BinE PowOp nat (NumE (Nat 2)) (VarE "v_N"))
            )
          )
        )
      )
    )
  )
)
(DecD
  "iand_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_iN" (VarT "iN"))
  (ExpP "iN_0" (VarT "iN"))
  (VarT "iN")
)
(RelD
  "fun_idiv_"
  (Seq Arg Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "N"))
    (typbind "_" (VarT "sx"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (IterT (VarT "iN") Opt))
  )
  (RuleD
    "fun_idiv__case_0"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE (Atom U) (TupE))
      (VarE "i_1")
      (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
      (OptE)
    )
  )
  (RuleD
    "fun_idiv__case_1"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE (Atom U) (TupE))
      (VarE "i_1")
      (VarE "i_2")
      (OptE
        (CaseE
          (Seq (Atom mk_uN) Arg)
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
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (VarE "v_N")
        (CaseE
          (Seq (Atom mk_uN) Arg)
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
  (RuleD
    "fun_idiv__case_2"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE (Atom S) (TupE))
      (VarE "i_1")
      (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
      (OptE)
    )
  )
  (RuleD
    "fun_idiv__case_3"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpP "var_1" int)
    (ExpP "var_0" int)
    (Seq Arg Arg Arg Arg Arg)
    (TupE (VarE "v_N") (CaseE (Atom S) (TupE)) (VarE "i_1") (VarE "i_2") (OptE))
    (RulePr
      "fun_signed_"
      (Seq Arg Arg Arg)
      (TupE
        (VarE "v_N")
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
        (VarE "var_1")
      )
    )
    (RulePr
      "fun_signed_"
      (Seq Arg Arg Arg)
      (TupE
        (VarE "v_N")
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
        (VarE "var_0")
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (BinE
          DivOp
          rat
          (CvtE int rat (VarE "var_0"))
          (CvtE int rat (VarE "var_1"))
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
                (CvtE nat int (VarE "v_N"))
                (CvtE nat int (NumE (Nat 1)))
              )
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_idiv__case_4"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpP "var_2" int)
    (ExpP "var_1" int)
    (ExpP "var_0" nat)
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE (Atom S) (TupE))
      (VarE "i_1")
      (VarE "i_2")
      (OptE (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "var_0"))))
    )
    (RulePr
      "fun_signed_"
      (Seq Arg Arg Arg)
      (TupE
        (VarE "v_N")
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
        (VarE "var_2")
      )
    )
    (RulePr
      "fun_signed_"
      (Seq Arg Arg Arg)
      (TupE
        (VarE "v_N")
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
        (VarE "var_1")
      )
    )
    (RulePr
      "fun_inv_signed_"
      (Seq Arg Arg Arg)
      (TupE
        (VarE "v_N")
        (CallE
          "truncz"
          (ExpA
            (BinE
              DivOp
              rat
              (CvtE int rat (VarE "var_1"))
              (CvtE int rat (VarE "var_2"))
            )
          )
        )
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE (VarE "v_N") (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "var_0"))))
    )
  )
)
(RelD
  "fun_imul_"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "N"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "iN"))
  )
  (RuleD
    "fun_imul__case_0"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (VarE "i_1")
      (VarE "i_2")
      (CaseE
        (Seq (Atom mk_uN) Arg)
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
            (BinE PowOp nat (NumE (Nat 2)) (VarE "v_N"))
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (VarE "v_N")
        (CaseE
          (Seq (Atom mk_uN) Arg)
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
              (BinE PowOp nat (NumE (Nat 2)) (VarE "v_N"))
            )
          )
        )
      )
    )
  )
)
(DecD
  "ior_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_iN" (VarT "iN"))
  (ExpP "iN_0" (VarT "iN"))
  (VarT "iN")
)
(RelD
  "fun_irem_"
  (Seq Arg Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "N"))
    (typbind "_" (VarT "sx"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (IterT (VarT "iN") Opt))
  )
  (RuleD
    "fun_irem__case_0"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE (Atom U) (TupE))
      (VarE "i_1")
      (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
      (OptE)
    )
  )
  (RuleD
    "fun_irem__case_1"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE (Atom U) (TupE))
      (VarE "i_1")
      (VarE "i_2")
      (OptE
        (CaseE
          (Seq (Atom mk_uN) Arg)
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
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (VarE "v_N")
        (CaseE
          (Seq (Atom mk_uN) Arg)
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
  (RuleD
    "fun_irem__case_2"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE (Atom S) (TupE))
      (VarE "i_1")
      (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
      (OptE)
    )
  )
  (RuleD
    "fun_irem__case_3"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpP "j_1" int)
    (ExpP "j_2" int)
    (ExpP "var_2" int)
    (ExpP "var_1" int)
    (ExpP "var_0" nat)
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE (Atom S) (TupE))
      (VarE "i_1")
      (VarE "i_2")
      (OptE (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "var_0"))))
    )
    (RulePr
      "fun_signed_"
      (Seq Arg Arg Arg)
      (TupE
        (VarE "v_N")
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
        (VarE "var_2")
      )
    )
    (RulePr
      "fun_signed_"
      (Seq Arg Arg Arg)
      (TupE
        (VarE "v_N")
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
        (VarE "var_1")
      )
    )
    (RulePr
      "fun_inv_signed_"
      (Seq Arg Arg Arg)
      (TupE
        (VarE "v_N")
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
        (VarE "var_0")
      )
    )
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE EqOp bool (VarE "j_1") (VarE "var_1"))
        (CmpE EqOp bool (VarE "j_2") (VarE "var_2"))
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE (VarE "v_N") (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "var_0"))))
    )
  )
)
(DecD
  "irotl_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_iN" (VarT "iN"))
  (ExpP "iN_0" (VarT "iN"))
  (VarT "iN")
)
(DecD
  "irotr_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_iN" (VarT "iN"))
  (ExpP "iN_0" (VarT "iN"))
  (VarT "iN")
)
(DecD
  "ishl_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_iN" (VarT "iN"))
  (ExpP "v_u32" (VarT "u32"))
  (VarT "iN")
)
(DecD
  "ishr_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_sx" (VarT "sx"))
  (ExpP "v_iN" (VarT "iN"))
  (ExpP "v_u32" (VarT "u32"))
  (VarT "iN")
)
(RelD
  "fun_isub_"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "N"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "iN"))
  )
  (RuleD
    "fun_isub__case_0"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (VarE "i_1")
      (VarE "i_2")
      (CaseE
        (Seq (Atom mk_uN) Arg)
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
                    (BinE PowOp nat (NumE (Nat 2)) (VarE "v_N"))
                    (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
                  )
                )
                (CvtE nat int (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0))
              )
              (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (VarE "v_N")))
            )
          )
        )
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (VarE "v_N")
        (CaseE
          (Seq (Atom mk_uN) Arg)
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
                      (BinE PowOp nat (NumE (Nat 2)) (VarE "v_N"))
                      (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
                    )
                  )
                  (CvtE
                    nat
                    int
                    (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
                  )
                )
                (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (VarE "v_N")))
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
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_iN" (VarT "iN"))
  (ExpP "iN_0" (VarT "iN"))
  (VarT "iN")
)
(RelD
  "fun_binop__before_fun_binop__case_38"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "valtype"))
    (typbind "_" (VarT "binop_"))
    (typbind "_" (VarT "val_"))
    (typbind "_" (VarT "val_"))
  )
  (RuleD
    "fun_binop__case_37"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom COPYSIGN) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
          (VarE "iter_42")
        )
      )
      List
      (iterexp
        "iter_42"
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_67"))
          )
        )
      )
      List
      (iterexp
        "iter_0_67"
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
  (RuleD
    "fun_binop__case_36"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom COPYSIGN) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
          (VarE "iter_41")
        )
      )
      List
      (iterexp
        "iter_41"
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_65"))
          )
        )
      )
      List
      (iterexp
        "iter_0_65"
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
  (RuleD
    "fun_binop__case_35"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom MAX) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
          (VarE "iter_40")
        )
      )
      List
      (iterexp
        "iter_40"
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_63"))
          )
        )
      )
      List
      (iterexp
        "iter_0_63"
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
  (RuleD
    "fun_binop__case_34"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom MAX) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
          (VarE "iter_39")
        )
      )
      List
      (iterexp
        "iter_39"
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_61"))
          )
        )
      )
      List
      (iterexp
        "iter_0_61"
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
  (RuleD
    "fun_binop__case_33"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom MIN) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
          (VarE "iter_38")
        )
      )
      List
      (iterexp
        "iter_38"
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_59"))
          )
        )
      )
      List
      (iterexp
        "iter_0_59"
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
  (RuleD
    "fun_binop__case_32"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom MIN) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
          (VarE "iter_37")
        )
      )
      List
      (iterexp
        "iter_37"
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_57"))
          )
        )
      )
      List
      (iterexp
        "iter_0_57"
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
  (RuleD
    "fun_binop__case_31"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom DIV) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
          (VarE "iter_36")
        )
      )
      List
      (iterexp
        "iter_36"
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_55"))
          )
        )
      )
      List
      (iterexp
        "iter_0_55"
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
  (RuleD
    "fun_binop__case_30"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom DIV) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
          (VarE "iter_35")
        )
      )
      List
      (iterexp
        "iter_35"
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_53"))
          )
        )
      )
      List
      (iterexp
        "iter_0_53"
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
  (RuleD
    "fun_binop__case_29"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom MUL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
          (VarE "iter_34")
        )
      )
      List
      (iterexp
        "iter_34"
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_51"))
          )
        )
      )
      List
      (iterexp
        "iter_0_51"
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
  (RuleD
    "fun_binop__case_28"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom MUL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
          (VarE "iter_33")
        )
      )
      List
      (iterexp
        "iter_33"
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_49"))
          )
        )
      )
      List
      (iterexp
        "iter_0_49"
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
  (RuleD
    "fun_binop__case_27"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom SUB) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
          (VarE "iter_32")
        )
      )
      List
      (iterexp
        "iter_32"
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_47"))
          )
        )
      )
      List
      (iterexp
        "iter_0_47"
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
  (RuleD
    "fun_binop__case_26"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom SUB) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
          (VarE "iter_31")
        )
      )
      List
      (iterexp
        "iter_31"
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_45"))
          )
        )
      )
      List
      (iterexp
        "iter_0_45"
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
  (RuleD
    "fun_binop__case_25"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom ADD) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
          (VarE "iter_30")
        )
      )
      List
      (iterexp
        "iter_30"
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_43"))
          )
        )
      )
      List
      (iterexp
        "iter_0_43"
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
  (RuleD
    "fun_binop__case_24"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom ADD) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
          (VarE "iter_29")
        )
      )
      List
      (iterexp
        "iter_29"
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_41"))
          )
        )
      )
      List
      (iterexp
        "iter_0_41"
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
  (RuleD
    "fun_binop__case_23"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom ROTR) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
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
  (RuleD
    "fun_binop__case_22"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom ROTR) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
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
  (RuleD
    "fun_binop__case_21"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom ROTL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
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
  (RuleD
    "fun_binop__case_20"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom ROTL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
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
  (RuleD
    "fun_binop__case_19"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom SHR) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
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
              (ExpA (VarE "v_sx"))
              (ExpA (VarE "iN_1"))
              (ExpA
                (CaseE
                  (Seq (Atom mk_uN) Arg)
                  (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                )
              )
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_18"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom SHR) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
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
              (ExpA (VarE "v_sx"))
              (ExpA (VarE "iN_1"))
              (ExpA
                (CaseE
                  (Seq (Atom mk_uN) Arg)
                  (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                )
              )
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_17"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom SHL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
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
                  (Seq (Atom mk_uN) Arg)
                  (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                )
              )
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_16"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom SHL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
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
                  (Seq (Atom mk_uN) Arg)
                  (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                )
              )
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_15"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom XOR) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
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
  (RuleD
    "fun_binop__case_14"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom XOR) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
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
  (RuleD
    "fun_binop__case_13"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom OR) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
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
  (RuleD
    "fun_binop__case_12"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom OR) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
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
  (RuleD
    "fun_binop__case_11"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom AND) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
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
  (RuleD
    "fun_binop__case_10"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom AND) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
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
  (RuleD
    "fun_binop__case_9"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (IterT (VarT "iN") Opt))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom REM) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_irem_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (VarE "iter_27")
        )
      )
      List
      (iterexp
        "iter_27"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_38"))
              )
              Opt
              (iterexp "iter_0_38" (VarE "var_0"))
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
          (VarE "iter_28")
        )
      )
      Opt
      (iterexp "iter_28" (VarE "var_0"))
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_39"))
          )
        )
      )
      Opt
      (iterexp "iter_0_39" (VarE "var_0"))
    )
  )
  (RuleD
    "fun_binop__case_8"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (IterT (VarT "iN") Opt))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom REM) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_irem_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (VarE "iter_25")
        )
      )
      List
      (iterexp
        "iter_25"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_35"))
              )
              Opt
              (iterexp "iter_0_35" (VarE "var_0"))
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
          (VarE "iter_26")
        )
      )
      Opt
      (iterexp "iter_26" (VarE "var_0"))
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_36"))
          )
        )
      )
      Opt
      (iterexp "iter_0_36" (VarE "var_0"))
    )
  )
  (RuleD
    "fun_binop__case_7"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (IterT (VarT "iN") Opt))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom DIV) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_idiv_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (VarE "iter_23")
        )
      )
      List
      (iterexp
        "iter_23"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_32"))
              )
              Opt
              (iterexp "iter_0_32" (VarE "var_0"))
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
          (VarE "iter_24")
        )
      )
      Opt
      (iterexp "iter_24" (VarE "var_0"))
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_33"))
          )
        )
      )
      Opt
      (iterexp "iter_0_33" (VarE "var_0"))
    )
  )
  (RuleD
    "fun_binop__case_6"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (IterT (VarT "iN") Opt))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom DIV) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_idiv_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (VarE "iter_21")
        )
      )
      List
      (iterexp
        "iter_21"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_29"))
              )
              Opt
              (iterexp "iter_0_29" (VarE "var_0"))
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
          (VarE "iter_22")
        )
      )
      Opt
      (iterexp "iter_22" (VarE "var_0"))
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_30"))
          )
        )
      )
      Opt
      (iterexp "iter_0_30" (VarE "var_0"))
    )
  )
  (RuleD
    "fun_binop__case_5"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom MUL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_imul_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I64) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_4"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom MUL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_imul_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_3"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom SUB) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_isub_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I64) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_2"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom SUB) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_isub_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_1"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom ADD) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_iadd_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I64) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_0"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom ADD) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_iadd_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
)
(RelD
  "fun_binop_"
  (Seq Arg Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "valtype"))
    (typbind "_" (VarT "binop_"))
    (typbind "_" (VarT "val_"))
    (typbind "_" (VarT "val_"))
    (typbind "_" (IterT (IterT (VarT "val_") List) Opt))
  )
  (RuleD
    "fun_binop__case_0"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom ADD) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (ListE
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
          )
        )
      )
    )
    (RulePr
      "fun_iadd_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_1"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom ADD) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (ListE
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (VarE "var_0"))
          )
        )
      )
    )
    (RulePr
      "fun_iadd_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I64) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_2"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom SUB) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (ListE
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
          )
        )
      )
    )
    (RulePr
      "fun_isub_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_3"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom SUB) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (ListE
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (VarE "var_0"))
          )
        )
      )
    )
    (RulePr
      "fun_isub_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I64) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_4"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom MUL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (ListE
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
          )
        )
      )
    )
    (RulePr
      "fun_imul_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_5"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom MUL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (ListE
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (VarE "var_0"))
          )
        )
      )
    )
    (RulePr
      "fun_imul_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I64) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_6"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (IterT (VarT "iN") Opt))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom DIV) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_31"))
              )
              Opt
              (iterexp "iter_0_31" (VarE "var_0"))
            )
          )
        )
      )
    )
    (RulePr
      "fun_idiv_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (VarE "iter_21")
        )
      )
      List
      (iterexp
        "iter_21"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_29"))
              )
              Opt
              (iterexp "iter_0_29" (VarE "var_0"))
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
          (VarE "iter_22")
        )
      )
      Opt
      (iterexp "iter_22" (VarE "var_0"))
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_30"))
          )
        )
      )
      Opt
      (iterexp "iter_0_30" (VarE "var_0"))
    )
  )
  (RuleD
    "fun_binop__case_7"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (IterT (VarT "iN") Opt))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom DIV) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_34"))
              )
              Opt
              (iterexp "iter_0_34" (VarE "var_0"))
            )
          )
        )
      )
    )
    (RulePr
      "fun_idiv_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (VarE "iter_23")
        )
      )
      List
      (iterexp
        "iter_23"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_32"))
              )
              Opt
              (iterexp "iter_0_32" (VarE "var_0"))
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
          (VarE "iter_24")
        )
      )
      Opt
      (iterexp "iter_24" (VarE "var_0"))
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_33"))
          )
        )
      )
      Opt
      (iterexp "iter_0_33" (VarE "var_0"))
    )
  )
  (RuleD
    "fun_binop__case_8"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (IterT (VarT "iN") Opt))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom REM) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_37"))
              )
              Opt
              (iterexp "iter_0_37" (VarE "var_0"))
            )
          )
        )
      )
    )
    (RulePr
      "fun_irem_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (VarE "iter_25")
        )
      )
      List
      (iterexp
        "iter_25"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_35"))
              )
              Opt
              (iterexp "iter_0_35" (VarE "var_0"))
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
          (VarE "iter_26")
        )
      )
      Opt
      (iterexp "iter_26" (VarE "var_0"))
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_36"))
          )
        )
      )
      Opt
      (iterexp "iter_0_36" (VarE "var_0"))
    )
  )
  (RuleD
    "fun_binop__case_9"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (IterT (VarT "iN") Opt))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom REM) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_40"))
              )
              Opt
              (iterexp "iter_0_40" (VarE "var_0"))
            )
          )
        )
      )
    )
    (RulePr
      "fun_irem_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (VarE "iter_27")
        )
      )
      List
      (iterexp
        "iter_27"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_38"))
              )
              Opt
              (iterexp "iter_0_38" (VarE "var_0"))
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
          (VarE "iter_28")
        )
      )
      Opt
      (iterexp "iter_28" (VarE "var_0"))
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_39"))
          )
        )
      )
      Opt
      (iterexp "iter_0_39" (VarE "var_0"))
    )
  )
  (RuleD
    "fun_binop__case_10"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom AND) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                    )
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
  (RuleD
    "fun_binop__case_11"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom AND) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                    )
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
  (RuleD
    "fun_binop__case_12"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom OR) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                    )
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
  (RuleD
    "fun_binop__case_13"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom OR) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                    )
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
  (RuleD
    "fun_binop__case_14"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom XOR) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                    )
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
  (RuleD
    "fun_binop__case_15"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom XOR) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                    )
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
  (RuleD
    "fun_binop__case_16"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom SHL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "iN_1"))
                (ExpA
                  (CaseE
                    (Seq (Atom mk_uN) Arg)
                    (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                  )
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
                  (Seq (Atom mk_uN) Arg)
                  (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                )
              )
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_17"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom SHL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "iN_1"))
                (ExpA
                  (CaseE
                    (Seq (Atom mk_uN) Arg)
                    (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                  )
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
                  (Seq (Atom mk_uN) Arg)
                  (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                )
              )
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_18"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom SHR) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "v_sx"))
                (ExpA (VarE "iN_1"))
                (ExpA
                  (CaseE
                    (Seq (Atom mk_uN) Arg)
                    (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                  )
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
              (ExpA (VarE "v_sx"))
              (ExpA (VarE "iN_1"))
              (ExpA
                (CaseE
                  (Seq (Atom mk_uN) Arg)
                  (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                )
              )
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_19"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom SHR) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "v_sx"))
                (ExpA (VarE "iN_1"))
                (ExpA
                  (CaseE
                    (Seq (Atom mk_uN) Arg)
                    (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                  )
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
              (ExpA (VarE "v_sx"))
              (ExpA (VarE "iN_1"))
              (ExpA
                (CaseE
                  (Seq (Atom mk_uN) Arg)
                  (TupE (ProjE (CallE "proj_uN_0" (ExpA (VarE "iN_2"))) 0))
                )
              )
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_binop__case_20"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom ROTL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                    )
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
  (RuleD
    "fun_binop__case_21"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom ROTL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                    )
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
  (RuleD
    "fun_binop__case_22"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom ROTR) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                    )
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
  (RuleD
    "fun_binop__case_23"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom ROTR) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                    )
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
  (RuleD
    "fun_binop__case_24"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom ADD) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_42"))
          )
          List
          (iterexp
            "iter_0_42"
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
          (VarE "iter_29")
        )
      )
      List
      (iterexp
        "iter_29"
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_41"))
          )
        )
      )
      List
      (iterexp
        "iter_0_41"
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
  (RuleD
    "fun_binop__case_25"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom ADD) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_44"))
          )
          List
          (iterexp
            "iter_0_44"
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
          (VarE "iter_30")
        )
      )
      List
      (iterexp
        "iter_30"
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_43"))
          )
        )
      )
      List
      (iterexp
        "iter_0_43"
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
  (RuleD
    "fun_binop__case_26"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom SUB) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_46"))
          )
          List
          (iterexp
            "iter_0_46"
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
          (VarE "iter_31")
        )
      )
      List
      (iterexp
        "iter_31"
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_45"))
          )
        )
      )
      List
      (iterexp
        "iter_0_45"
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
  (RuleD
    "fun_binop__case_27"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom SUB) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_48"))
          )
          List
          (iterexp
            "iter_0_48"
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
          (VarE "iter_32")
        )
      )
      List
      (iterexp
        "iter_32"
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_47"))
          )
        )
      )
      List
      (iterexp
        "iter_0_47"
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
  (RuleD
    "fun_binop__case_28"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom MUL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_50"))
          )
          List
          (iterexp
            "iter_0_50"
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
          (VarE "iter_33")
        )
      )
      List
      (iterexp
        "iter_33"
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_49"))
          )
        )
      )
      List
      (iterexp
        "iter_0_49"
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
  (RuleD
    "fun_binop__case_29"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom MUL) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_52"))
          )
          List
          (iterexp
            "iter_0_52"
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
          (VarE "iter_34")
        )
      )
      List
      (iterexp
        "iter_34"
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_51"))
          )
        )
      )
      List
      (iterexp
        "iter_0_51"
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
  (RuleD
    "fun_binop__case_30"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom DIV) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_54"))
          )
          List
          (iterexp
            "iter_0_54"
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
          (VarE "iter_35")
        )
      )
      List
      (iterexp
        "iter_35"
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_53"))
          )
        )
      )
      List
      (iterexp
        "iter_0_53"
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
  (RuleD
    "fun_binop__case_31"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom DIV) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_56"))
          )
          List
          (iterexp
            "iter_0_56"
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
          (VarE "iter_36")
        )
      )
      List
      (iterexp
        "iter_36"
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_55"))
          )
        )
      )
      List
      (iterexp
        "iter_0_55"
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
  (RuleD
    "fun_binop__case_32"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom MIN) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_58"))
          )
          List
          (iterexp
            "iter_0_58"
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
          (VarE "iter_37")
        )
      )
      List
      (iterexp
        "iter_37"
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_57"))
          )
        )
      )
      List
      (iterexp
        "iter_0_57"
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
  (RuleD
    "fun_binop__case_33"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom MIN) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_60"))
          )
          List
          (iterexp
            "iter_0_60"
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
          (VarE "iter_38")
        )
      )
      List
      (iterexp
        "iter_38"
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_59"))
          )
        )
      )
      List
      (iterexp
        "iter_0_59"
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
  (RuleD
    "fun_binop__case_34"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom MAX) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_62"))
          )
          List
          (iterexp
            "iter_0_62"
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
          (VarE "iter_39")
        )
      )
      List
      (iterexp
        "iter_39"
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_61"))
          )
        )
      )
      List
      (iterexp
        "iter_0_61"
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
  (RuleD
    "fun_binop__case_35"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom MAX) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_64"))
          )
          List
          (iterexp
            "iter_0_64"
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
          (VarE "iter_40")
        )
      )
      List
      (iterexp
        "iter_40"
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_63"))
          )
        )
      )
      List
      (iterexp
        "iter_0_63"
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
  (RuleD
    "fun_binop__case_36"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom COPYSIGN) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_66"))
          )
          List
          (iterexp
            "iter_0_66"
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
          (VarE "iter_41")
        )
      )
      List
      (iterexp
        "iter_41"
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_65"))
          )
        )
      )
      List
      (iterexp
        "iter_0_65"
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
  (RuleD
    "fun_binop__case_37"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom COPYSIGN) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
      )
      (OptE
        (IterE
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_68"))
          )
          List
          (iterexp
            "iter_0_68"
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
          (VarE "iter_42")
        )
      )
      List
      (iterexp
        "iter_42"
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_67"))
          )
        )
      )
      List
      (iterexp
        "iter_0_67"
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
  (RuleD
    "fun_binop__case_38"
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "binop_"))
    (ExpP "x2" (VarT "val_"))
    (ExpP "x3" (VarT "val_"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE (VarE "x0") (VarE "x1") (VarE "x2") (VarE "x3") (OptE))
    (NegPr
      (RulePr
        "fun_binop__before_fun_binop__case_38"
        (Seq Arg Arg Arg Arg)
        (TupE (VarE "x0") (VarE "x1") (VarE "x2") (VarE "x3"))
      )
    )
  )
)
(HintD (DecH "binop_" (hint "partial" "{}")))
(HintD (DecH "binop_" (hint "show" "%2#$_(%1)#(%3, %4)")))
(RelD
  "fun_ieqz_"
  (Seq Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "N"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "u32"))
  )
  (RuleD
    "fun_ieqz__case_0"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (Seq Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (VarE "i_1")
      (CaseE
        (Seq (Atom mk_uN) Arg)
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
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          (Seq (Atom mk_uN) Arg)
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
(RelD
  "fun_testop__before_fun_testop__case_2"
  (Seq Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "valtype"))
    (typbind "_" (VarT "testop_"))
    (typbind "_" (VarT "val_"))
  )
  (RuleD
    "fun_testop__case_1"
    (ExpP "v_iN" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_testop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom EQZ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
      )
    )
    (RulePr
      "fun_ieqz_"
      (Seq Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "v_iN")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_testop__case_0"
    (ExpP "v_iN" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_testop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom EQZ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
      )
    )
    (RulePr
      "fun_ieqz_"
      (Seq Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "v_iN")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
)
(RelD
  "fun_testop_"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "valtype"))
    (typbind "_" (VarT "testop_"))
    (typbind "_" (VarT "val_"))
    (typbind "_" (IterT (VarT "val_") Opt))
  )
  (RuleD
    "fun_testop__case_0"
    (ExpP "v_iN" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_testop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom EQZ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
      )
      (OptE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
    (RulePr
      "fun_ieqz_"
      (Seq Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "v_iN")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_testop__case_1"
    (ExpP "v_iN" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_testop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom EQZ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
      )
      (OptE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
    (RulePr
      "fun_ieqz_"
      (Seq Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "v_iN")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_testop__case_2"
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "testop_"))
    (ExpP "x2" (VarT "val_"))
    (Seq Arg Arg Arg Arg)
    (TupE (VarE "x0") (VarE "x1") (VarE "x2") (OptE))
    (NegPr
      (RulePr
        "fun_testop__before_fun_testop__case_2"
        (Seq Arg Arg Arg)
        (TupE (VarE "x0") (VarE "x1") (VarE "x2"))
      )
    )
  )
)
(HintD (DecH "testop_" (hint "partial" "{}")))
(HintD (DecH "testop_" (hint "show" "%2#$_(%1)#((%3))")))
(DecD
  "feq_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (ExpP "fN_0" (VarT "fN"))
  (VarT "u32")
)
(DecD
  "fge_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (ExpP "fN_0" (VarT "fN"))
  (VarT "u32")
)
(DecD
  "fgt_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (ExpP "fN_0" (VarT "fN"))
  (VarT "u32")
)
(DecD
  "fle_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (ExpP "fN_0" (VarT "fN"))
  (VarT "u32")
)
(DecD
  "flt_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (ExpP "fN_0" (VarT "fN"))
  (VarT "u32")
)
(DecD
  "fne_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (ExpP "fN_0" (VarT "fN"))
  (VarT "u32")
)
(RelD
  "fun_ieq_"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "N"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "u32"))
  )
  (RuleD
    "fun_ieq__case_0"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (VarE "i_1")
      (VarE "i_2")
      (CaseE
        (Seq (Atom mk_uN) Arg)
        (TupE (CallE "bool" (ExpA (CmpE EqOp bool (VarE "i_1") (VarE "i_2")))))
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          (Seq (Atom mk_uN) Arg)
          (TupE
            (CallE "bool" (ExpA (CmpE EqOp bool (VarE "i_1") (VarE "i_2"))))
          )
        )
      )
    )
  )
)
(RelD
  "fun_ige_"
  (Seq Arg Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "N"))
    (typbind "_" (VarT "sx"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "u32"))
  )
  (RuleD
    "fun_ige__case_0"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE (Atom U) (TupE))
      (VarE "i_1")
      (VarE "i_2")
      (CaseE
        (Seq (Atom mk_uN) Arg)
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
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          (Seq (Atom mk_uN) Arg)
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
  (RuleD
    "fun_ige__case_1"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpP "var_1" int)
    (ExpP "var_0" int)
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE (Atom S) (TupE))
      (VarE "i_1")
      (VarE "i_2")
      (CaseE
        (Seq (Atom mk_uN) Arg)
        (TupE
          (CallE "bool" (ExpA (CmpE GeOp int (VarE "var_0") (VarE "var_1"))))
        )
      )
    )
    (RulePr
      "fun_signed_"
      (Seq Arg Arg Arg)
      (TupE
        (VarE "v_N")
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
        (VarE "var_1")
      )
    )
    (RulePr
      "fun_signed_"
      (Seq Arg Arg Arg)
      (TupE
        (VarE "v_N")
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          (Seq (Atom mk_uN) Arg)
          (TupE
            (CallE "bool" (ExpA (CmpE GeOp int (VarE "var_0") (VarE "var_1"))))
          )
        )
      )
    )
  )
)
(RelD
  "fun_igt_"
  (Seq Arg Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "N"))
    (typbind "_" (VarT "sx"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "u32"))
  )
  (RuleD
    "fun_igt__case_0"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE (Atom U) (TupE))
      (VarE "i_1")
      (VarE "i_2")
      (CaseE
        (Seq (Atom mk_uN) Arg)
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
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          (Seq (Atom mk_uN) Arg)
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
  (RuleD
    "fun_igt__case_1"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpP "var_1" int)
    (ExpP "var_0" int)
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE (Atom S) (TupE))
      (VarE "i_1")
      (VarE "i_2")
      (CaseE
        (Seq (Atom mk_uN) Arg)
        (TupE
          (CallE "bool" (ExpA (CmpE GtOp int (VarE "var_0") (VarE "var_1"))))
        )
      )
    )
    (RulePr
      "fun_signed_"
      (Seq Arg Arg Arg)
      (TupE
        (VarE "v_N")
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
        (VarE "var_1")
      )
    )
    (RulePr
      "fun_signed_"
      (Seq Arg Arg Arg)
      (TupE
        (VarE "v_N")
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          (Seq (Atom mk_uN) Arg)
          (TupE
            (CallE "bool" (ExpA (CmpE GtOp int (VarE "var_0") (VarE "var_1"))))
          )
        )
      )
    )
  )
)
(RelD
  "fun_ile_"
  (Seq Arg Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "N"))
    (typbind "_" (VarT "sx"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "u32"))
  )
  (RuleD
    "fun_ile__case_0"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE (Atom U) (TupE))
      (VarE "i_1")
      (VarE "i_2")
      (CaseE
        (Seq (Atom mk_uN) Arg)
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
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          (Seq (Atom mk_uN) Arg)
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
  (RuleD
    "fun_ile__case_1"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpP "var_1" int)
    (ExpP "var_0" int)
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE (Atom S) (TupE))
      (VarE "i_1")
      (VarE "i_2")
      (CaseE
        (Seq (Atom mk_uN) Arg)
        (TupE
          (CallE "bool" (ExpA (CmpE LeOp int (VarE "var_0") (VarE "var_1"))))
        )
      )
    )
    (RulePr
      "fun_signed_"
      (Seq Arg Arg Arg)
      (TupE
        (VarE "v_N")
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
        (VarE "var_1")
      )
    )
    (RulePr
      "fun_signed_"
      (Seq Arg Arg Arg)
      (TupE
        (VarE "v_N")
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          (Seq (Atom mk_uN) Arg)
          (TupE
            (CallE "bool" (ExpA (CmpE LeOp int (VarE "var_0") (VarE "var_1"))))
          )
        )
      )
    )
  )
)
(RelD
  "fun_ilt_"
  (Seq Arg Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "N"))
    (typbind "_" (VarT "sx"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "u32"))
  )
  (RuleD
    "fun_ilt__case_0"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE (Atom U) (TupE))
      (VarE "i_1")
      (VarE "i_2")
      (CaseE
        (Seq (Atom mk_uN) Arg)
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
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          (Seq (Atom mk_uN) Arg)
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
  (RuleD
    "fun_ilt__case_1"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (ExpP "var_1" int)
    (ExpP "var_0" int)
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (CaseE (Atom S) (TupE))
      (VarE "i_1")
      (VarE "i_2")
      (CaseE
        (Seq (Atom mk_uN) Arg)
        (TupE
          (CallE "bool" (ExpA (CmpE LtOp int (VarE "var_0") (VarE "var_1"))))
        )
      )
    )
    (RulePr
      "fun_signed_"
      (Seq Arg Arg Arg)
      (TupE
        (VarE "v_N")
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_2"))) 0)
        (VarE "var_1")
      )
    )
    (RulePr
      "fun_signed_"
      (Seq Arg Arg Arg)
      (TupE
        (VarE "v_N")
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "i_1"))) 0)
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          (Seq (Atom mk_uN) Arg)
          (TupE
            (CallE "bool" (ExpA (CmpE LtOp int (VarE "var_0") (VarE "var_1"))))
          )
        )
      )
    )
  )
)
(RelD
  "fun_ine_"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "N"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "u32"))
  )
  (RuleD
    "fun_ine__case_0"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (ExpP "i_2" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (VarE "i_1")
      (VarE "i_2")
      (CaseE
        (Seq (Atom mk_uN) Arg)
        (TupE (CallE "bool" (ExpA (CmpE NeOp bool (VarE "i_1") (VarE "i_2")))))
      )
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          (Seq (Atom mk_uN) Arg)
          (TupE
            (CallE "bool" (ExpA (CmpE NeOp bool (VarE "i_1") (VarE "i_2"))))
          )
        )
      )
    )
  )
)
(RelD
  "fun_relop__before_fun_relop__case_24"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "valtype"))
    (typbind "_" (VarT "relop_"))
    (typbind "_" (VarT "val_"))
    (typbind "_" (VarT "val_"))
  )
  (RuleD
    "fun_relop__case_23"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom GE) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_22"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom GE) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_21"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom LE) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_20"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom LE) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_19"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom GT) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_18"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom GT) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_17"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom LT) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_16"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom LT) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_15"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom NE) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_14"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom NE) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_13"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom EQ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_12"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom EQ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_11"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom GE) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_ige_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_10"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom GE) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_ige_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_9"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom LE) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_ile_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_8"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom LE) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_ile_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_7"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom GT) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_igt_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_6"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom GT) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_igt_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_5"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom LT) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_ilt_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_4"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom LT) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_ilt_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_3"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom NE) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_ine_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_2"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom NE) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_ine_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_1"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom EQ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_ieq_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_0"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom EQ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
    )
    (RulePr
      "fun_ieq_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
)
(RelD
  "fun_relop_"
  (Seq Arg Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "valtype"))
    (typbind "_" (VarT "relop_"))
    (typbind "_" (VarT "val_"))
    (typbind "_" (VarT "val_"))
    (typbind "_" (IterT (VarT "val_") Opt))
  )
  (RuleD
    "fun_relop__case_0"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom EQ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
    (RulePr
      "fun_ieq_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_1"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom EQ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
    (RulePr
      "fun_ieq_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_2"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (CaseE (Atom NE) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
    (RulePr
      "fun_ine_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_3"
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (CaseE (Atom NE) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
    (RulePr
      "fun_ine_"
      (Seq Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_4"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom LT) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
    (RulePr
      "fun_ilt_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_5"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom LT) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
    (RulePr
      "fun_ilt_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_6"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom GT) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
    (RulePr
      "fun_igt_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_7"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom GT) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
    (RulePr
      "fun_igt_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_8"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom LE) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
    (RulePr
      "fun_ile_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_9"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom LE) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
    (RulePr
      "fun_ile_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_10"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE (Seq (Atom GE) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
    (RulePr
      "fun_ige_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_11"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "iN_1" (VarT "uN"))
    (ExpP "iN_2" (VarT "uN"))
    (ExpP "var_0" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE (Seq (Atom GE) Arg) (TupE (VarE "v_sx")))
        )
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "iN_2"))
      )
      (OptE
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
    (RulePr
      "fun_ige_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (CallE
          "size"
          (ExpA (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE)))))
        )
        (VarE "v_sx")
        (VarE "iN_1")
        (VarE "iN_2")
        (VarE "var_0")
      )
    )
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "var_0"))
        )
      )
    )
  )
  (RuleD
    "fun_relop__case_12"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom EQ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_13"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom EQ) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_14"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom NE) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_15"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom NE) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_16"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom LT) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_17"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom LT) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_18"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom GT) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_19"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom GT) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_20"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom LE) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_21"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom LE) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_22"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (CaseE (Atom GE) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_23"
    (ExpP "fN_1" (VarT "fN"))
    (ExpP "fN_2" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (CaseE (Atom GE) (TupE)))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_1"))
      )
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "fN_2"))
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
  (RuleD
    "fun_relop__case_24"
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "relop_"))
    (ExpP "x2" (VarT "val_"))
    (ExpP "x3" (VarT "val_"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE (VarE "x0") (VarE "x1") (VarE "x2") (VarE "x3") (OptE))
    (NegPr
      (RulePr
        "fun_relop__before_fun_relop__case_24"
        (Seq Arg Arg Arg Arg)
        (TupE (VarE "x0") (VarE "x1") (VarE "x2") (VarE "x3"))
      )
    )
  )
)
(HintD (DecH "relop_" (hint "partial" "{}")))
(HintD (DecH "relop_" (hint "show" "%2#$_(%1)#(%3, %4)")))
(DecD
  "convert__"
  (ExpP "v_M" (VarT "M"))
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_sx" (VarT "sx"))
  (ExpP "v_iN" (VarT "iN"))
  (VarT "fN")
)
(DecD
  "demote__"
  (ExpP "v_M" (VarT "M"))
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "extend__"
  (ExpP "v_M" (VarT "M"))
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_sx" (VarT "sx"))
  (ExpP "v_iN" (VarT "iN"))
  (VarT "iN")
)
(DecD
  "promote__"
  (ExpP "v_M" (VarT "M"))
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
  (IterT (VarT "fN") List)
)
(DecD
  "reinterpret__"
  (ExpP "valtype_1" (VarT "valtype"))
  (ExpP "valtype_2" (VarT "valtype"))
  (ExpP "v_val_" (VarT "val_"))
  (VarT "val_")
)
(DecD
  "trunc__"
  (ExpP "v_M" (VarT "M"))
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_sx" (VarT "sx"))
  (ExpP "v_fN" (VarT "fN"))
  (IterT (VarT "iN") Opt)
)
(DecD
  "wrap__"
  (ExpP "v_M" (VarT "M"))
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_iN" (VarT "iN"))
  (VarT "iN")
)
(RelD
  "fun_cvtop___before_fun_cvtop___case_20"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "valtype"))
    (typbind "_" (VarT "valtype"))
    (typbind "_" (VarT "cvtop"))
    (typbind "_" (VarT "val_"))
  )
  (RuleD
    "fun_cvtop___case_19"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE (Atom I64) (TupE))
      (CaseE (Atom REINTERPRET) (TupE))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
              (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
          (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_18"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE (Atom I64) (TupE))
      (CaseE (Atom REINTERPRET) (TupE))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
              (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
          (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_17"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE (Atom I32) (TupE))
      (CaseE (Atom REINTERPRET) (TupE))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
              (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
          (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_16"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE (Atom I32) (TupE))
      (CaseE (Atom REINTERPRET) (TupE))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
              (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
          (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_15"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE (Atom F64) (TupE))
      (CaseE (Atom REINTERPRET) (TupE))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
              (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
          (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_14"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE (Atom F64) (TupE))
      (CaseE (Atom REINTERPRET) (TupE))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
              (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
          (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_13"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE (Atom F32) (TupE))
      (CaseE (Atom REINTERPRET) (TupE))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
              (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
          (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_12"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE (Atom F32) (TupE))
      (CaseE (Atom REINTERPRET) (TupE))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
              (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
          (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_11"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE (Atom F64) (TupE))
      (CaseE (Seq (Atom CONVERT) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
              (ExpA (VarE "v_sx"))
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_10"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE (Atom F64) (TupE))
      (CaseE (Seq (Atom CONVERT) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
              (ExpA (VarE "v_sx"))
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_9"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE (Atom F32) (TupE))
      (CaseE (Seq (Atom CONVERT) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
              (ExpA (VarE "v_sx"))
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_8"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE (Atom F32) (TupE))
      (CaseE (Seq (Atom CONVERT) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
              (ExpA (VarE "v_sx"))
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_7"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE (Atom F32) (TupE))
      (CaseE (Atom DEMOTE) (TupE))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
      )
    )
    (IterPr
      (RulePr "wf_fN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "iter_52")))
      List
      (iterexp
        "iter_52"
        (CallE
          "demote__"
          (ExpA (NumE (Nat 64)))
          (ExpA (NumE (Nat 32)))
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_82"))
          )
        )
      )
      List
      (iterexp
        "iter_0_82"
        (CallE
          "demote__"
          (ExpA (NumE (Nat 64)))
          (ExpA (NumE (Nat 32)))
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_6"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE (Atom F64) (TupE))
      (CaseE (Atom PROMOTE) (TupE))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
      )
    )
    (IterPr
      (RulePr "wf_fN" (Seq Arg Arg) (TupE (NumE (Nat 64)) (VarE "iter_51")))
      List
      (iterexp
        "iter_51"
        (CallE
          "promote__"
          (ExpA (NumE (Nat 32)))
          (ExpA (NumE (Nat 64)))
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_81"))
          )
        )
      )
      List
      (iterexp
        "iter_0_81"
        (CallE
          "promote__"
          (ExpA (NumE (Nat 32)))
          (ExpA (NumE (Nat 64)))
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_5"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE (Atom I64) (TupE))
      (CaseE (Seq (Atom TRUNC) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (VarE "iter_49")
        )
      )
      List
      (iterexp
        "iter_49"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_78"))
              )
              Opt
              (iterexp
                "iter_0_78"
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
                  (ExpA (VarE "v_sx"))
                  (ExpA (VarE "v_fN"))
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
          (VarE "iter_50")
        )
      )
      Opt
      (iterexp
        "iter_50"
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
          (ExpA (VarE "v_sx"))
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_79"))
          )
        )
      )
      Opt
      (iterexp
        "iter_0_79"
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
          (ExpA (VarE "v_sx"))
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_4"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE (Atom I64) (TupE))
      (CaseE (Seq (Atom TRUNC) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
          (VarE "iter_47")
        )
      )
      List
      (iterexp
        "iter_47"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_75"))
              )
              Opt
              (iterexp
                "iter_0_75"
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
                  (ExpA (VarE "v_sx"))
                  (ExpA (VarE "v_fN"))
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
          (VarE "iter_48")
        )
      )
      Opt
      (iterexp
        "iter_48"
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
          (ExpA (VarE "v_sx"))
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_76"))
          )
        )
      )
      Opt
      (iterexp
        "iter_0_76"
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
          (ExpA (VarE "v_sx"))
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_3"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE (Atom I32) (TupE))
      (CaseE (Seq (Atom TRUNC) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (VarE "iter_45")
        )
      )
      List
      (iterexp
        "iter_45"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_72"))
              )
              Opt
              (iterexp
                "iter_0_72"
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
                  (ExpA (VarE "v_sx"))
                  (ExpA (VarE "v_fN"))
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
          (VarE "iter_46")
        )
      )
      Opt
      (iterexp
        "iter_46"
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
          (ExpA (VarE "v_sx"))
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_73"))
          )
        )
      )
      Opt
      (iterexp
        "iter_0_73"
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
          (ExpA (VarE "v_sx"))
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_2"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE (Atom I32) (TupE))
      (CaseE (Seq (Atom TRUNC) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
      )
    )
    (IterPr
      (RulePr
        "wf_val_"
        (Seq Arg Arg)
        (TupE
          (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
          (VarE "iter_43")
        )
      )
      List
      (iterexp
        "iter_43"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_69"))
              )
              Opt
              (iterexp
                "iter_0_69"
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
                  (ExpA (VarE "v_sx"))
                  (ExpA (VarE "v_fN"))
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
          (VarE "iter_44")
        )
      )
      Opt
      (iterexp
        "iter_44"
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
          (ExpA (VarE "v_sx"))
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_70"))
          )
        )
      )
      Opt
      (iterexp
        "iter_0_70"
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
          (ExpA (VarE "v_sx"))
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_1"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE (Atom I32) (TupE))
      (CaseE (Atom WRAP) (TupE))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_0"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE (Atom I64) (TupE))
      (CaseE (Seq (Atom EXTEND) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
              (ExpA (VarE "v_sx"))
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
)
(RelD
  "fun_cvtop__"
  (Seq Arg Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "valtype"))
    (typbind "_" (VarT "valtype"))
    (typbind "_" (VarT "cvtop"))
    (typbind "_" (VarT "val_"))
    (typbind "_" (IterT (IterT (VarT "val_") List) Opt))
  )
  (RuleD
    "fun_cvtop___case_0"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE (Atom I64) (TupE))
      (CaseE (Seq (Atom EXTEND) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
                (ExpA (VarE "v_sx"))
                (ExpA (VarE "v_iN"))
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
        (CaseE (Atom I64) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I64) (TupE))
            (CallE
              "extend__"
              (ExpA (NumE (Nat 32)))
              (ExpA (NumE (Nat 64)))
              (ExpA (VarE "v_sx"))
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_1"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE (Atom I32) (TupE))
      (CaseE (Atom WRAP) (TupE))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
                (ExpA (VarE "v_iN"))
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
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_val__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "wrap__"
              (ExpA (NumE (Nat 64)))
              (ExpA (NumE (Nat 32)))
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_2"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE (Atom I32) (TupE))
      (CaseE (Seq (Atom TRUNC) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_71"))
              )
              Opt
              (iterexp
                "iter_0_71"
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
                  (ExpA (VarE "v_sx"))
                  (ExpA (VarE "v_fN"))
                )
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
          (VarE "iter_43")
        )
      )
      List
      (iterexp
        "iter_43"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_69"))
              )
              Opt
              (iterexp
                "iter_0_69"
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
                  (ExpA (VarE "v_sx"))
                  (ExpA (VarE "v_fN"))
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
          (VarE "iter_44")
        )
      )
      Opt
      (iterexp
        "iter_44"
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
          (ExpA (VarE "v_sx"))
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_70"))
          )
        )
      )
      Opt
      (iterexp
        "iter_0_70"
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
          (ExpA (VarE "v_sx"))
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_3"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE (Atom I32) (TupE))
      (CaseE (Seq (Atom TRUNC) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_74"))
              )
              Opt
              (iterexp
                "iter_0_74"
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
                  (ExpA (VarE "v_sx"))
                  (ExpA (VarE "v_fN"))
                )
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
          (VarE "iter_45")
        )
      )
      List
      (iterexp
        "iter_45"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_72"))
              )
              Opt
              (iterexp
                "iter_0_72"
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
                  (ExpA (VarE "v_sx"))
                  (ExpA (VarE "v_fN"))
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
          (VarE "iter_46")
        )
      )
      Opt
      (iterexp
        "iter_46"
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
          (ExpA (VarE "v_sx"))
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom I32) (TupE)) (VarE "iter_0_73"))
          )
        )
      )
      Opt
      (iterexp
        "iter_0_73"
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
          (ExpA (VarE "v_sx"))
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_4"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE (Atom I64) (TupE))
      (CaseE (Seq (Atom TRUNC) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_77"))
              )
              Opt
              (iterexp
                "iter_0_77"
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
                  (ExpA (VarE "v_sx"))
                  (ExpA (VarE "v_fN"))
                )
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
          (VarE "iter_47")
        )
      )
      List
      (iterexp
        "iter_47"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_75"))
              )
              Opt
              (iterexp
                "iter_0_75"
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
                  (ExpA (VarE "v_sx"))
                  (ExpA (VarE "v_fN"))
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
          (VarE "iter_48")
        )
      )
      Opt
      (iterexp
        "iter_48"
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
          (ExpA (VarE "v_sx"))
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_76"))
          )
        )
      )
      Opt
      (iterexp
        "iter_0_76"
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
          (ExpA (VarE "v_sx"))
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_5"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE (Atom I64) (TupE))
      (CaseE (Seq (Atom TRUNC) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
      )
      (OptE
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_80"))
              )
              Opt
              (iterexp
                "iter_0_80"
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
                  (ExpA (VarE "v_sx"))
                  (ExpA (VarE "v_fN"))
                )
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
          (VarE "iter_49")
        )
      )
      List
      (iterexp
        "iter_49"
        (CallE
          "list_"
          (TypA (VarT "val_"))
          (ExpA
            (IterE
              (CaseE
                (Seq (Atom mk_val__0) Arg Arg)
                (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_78"))
              )
              Opt
              (iterexp
                "iter_0_78"
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
                  (ExpA (VarE "v_sx"))
                  (ExpA (VarE "v_fN"))
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
          (VarE "iter_50")
        )
      )
      Opt
      (iterexp
        "iter_50"
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
          (ExpA (VarE "v_sx"))
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom I64) (TupE)) (VarE "iter_0_79"))
          )
        )
      )
      Opt
      (iterexp
        "iter_0_79"
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
          (ExpA (VarE "v_sx"))
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_6"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE (Atom F64) (TupE))
      (CaseE (Atom PROMOTE) (TupE))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
              (ExpA (VarE "v_fN"))
            )
          )
        )
      )
    )
    (IterPr
      (RulePr "wf_fN" (Seq Arg Arg) (TupE (NumE (Nat 64)) (VarE "iter_51")))
      List
      (iterexp
        "iter_51"
        (CallE
          "promote__"
          (ExpA (NumE (Nat 32)))
          (ExpA (NumE (Nat 64)))
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F64) (TupE)) (VarE "iter_0_81"))
          )
        )
      )
      List
      (iterexp
        "iter_0_81"
        (CallE
          "promote__"
          (ExpA (NumE (Nat 32)))
          (ExpA (NumE (Nat 64)))
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_7"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE (Atom F32) (TupE))
      (CaseE (Atom DEMOTE) (TupE))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
              (ExpA (VarE "v_fN"))
            )
          )
        )
      )
    )
    (IterPr
      (RulePr "wf_fN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "iter_52")))
      List
      (iterexp
        "iter_52"
        (CallE
          "demote__"
          (ExpA (NumE (Nat 64)))
          (ExpA (NumE (Nat 32)))
          (ExpA (VarE "v_fN"))
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
            (TupE (CaseE (Atom F32) (TupE)) (VarE "iter_0_82"))
          )
        )
      )
      List
      (iterexp
        "iter_0_82"
        (CallE
          "demote__"
          (ExpA (NumE (Nat 64)))
          (ExpA (NumE (Nat 32)))
          (ExpA (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_8"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE (Atom F32) (TupE))
      (CaseE (Seq (Atom CONVERT) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                    )
                  )
                )
                (ExpA
                  (CallE
                    "size"
                    (ExpA
                      (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "v_sx"))
                (ExpA (VarE "v_iN"))
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
              (ExpA (VarE "v_sx"))
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_9"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE (Atom F32) (TupE))
      (CaseE (Seq (Atom CONVERT) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                    )
                  )
                )
                (ExpA
                  (CallE
                    "size"
                    (ExpA
                      (CallE "valtype_Fnn" (ExpA (CaseE (Atom F32) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "v_sx"))
                (ExpA (VarE "v_iN"))
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
              (ExpA (VarE "v_sx"))
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_10"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE (Atom F64) (TupE))
      (CaseE (Seq (Atom CONVERT) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I32) (TupE))))
                    )
                  )
                )
                (ExpA
                  (CallE
                    "size"
                    (ExpA
                      (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "v_sx"))
                (ExpA (VarE "v_iN"))
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
              (ExpA (VarE "v_sx"))
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_11"
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE (Atom F64) (TupE))
      (CaseE (Seq (Atom CONVERT) Arg) (TupE (VarE "v_sx")))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
                    (ExpA
                      (CallE "valtype_Inn" (ExpA (CaseE (Atom I64) (TupE))))
                    )
                  )
                )
                (ExpA
                  (CallE
                    "size"
                    (ExpA
                      (CallE "valtype_Fnn" (ExpA (CaseE (Atom F64) (TupE))))
                    )
                  )
                )
                (ExpA (VarE "v_sx"))
                (ExpA (VarE "v_iN"))
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
              (ExpA (VarE "v_sx"))
              (ExpA (VarE "v_iN"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_12"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE (Atom F32) (TupE))
      (CaseE (Atom REINTERPRET) (TupE))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
                (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
              (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
          (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_13"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE (Atom F32) (TupE))
      (CaseE (Atom REINTERPRET) (TupE))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
                (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
              (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
          (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_14"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE (Atom F64) (TupE))
      (CaseE (Atom REINTERPRET) (TupE))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
                (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
              (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
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
          (TupE (CaseE (Atom I32) (TupE)) (VarE "v_iN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_15"
    (ExpP "v_iN" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE (Atom F64) (TupE))
      (CaseE (Atom REINTERPRET) (TupE))
      (CaseE
        (Seq (Atom mk_val__0) Arg Arg)
        (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
                (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
              (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
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
          (TupE (CaseE (Atom I64) (TupE)) (VarE "v_iN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_16"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE (Atom I32) (TupE))
      (CaseE (Atom REINTERPRET) (TupE))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
                (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
              (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
          (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_17"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE (Atom I32) (TupE))
      (CaseE (Atom REINTERPRET) (TupE))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
                (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
              (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
          (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_18"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE (Atom I64) (TupE))
      (CaseE (Atom REINTERPRET) (TupE))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
                (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
              (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
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
          (TupE (CaseE (Atom F32) (TupE)) (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_19"
    (ExpP "v_fN" (VarT "fN"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE (Atom I64) (TupE))
      (CaseE (Atom REINTERPRET) (TupE))
      (CaseE
        (Seq (Atom mk_val__1) Arg Arg)
        (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
                (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
              (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
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
          (TupE (CaseE (Atom F64) (TupE)) (VarE "v_fN"))
        )
      )
    )
  )
  (RuleD
    "fun_cvtop___case_20"
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "valtype"))
    (ExpP "x2" (VarT "cvtop"))
    (ExpP "x3" (VarT "val_"))
    (Seq Arg Arg Arg Arg Arg)
    (TupE (VarE "x0") (VarE "x1") (VarE "x2") (VarE "x3") (OptE))
    (NegPr
      (RulePr
        "fun_cvtop___before_fun_cvtop___case_20"
        (Seq Arg Arg Arg Arg)
        (TupE (VarE "x0") (VarE "x1") (VarE "x2") (VarE "x3"))
      )
    )
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
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_iN" (VarT "iN"))
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
  (ExpP "v_N" (VarT "N"))
  (ExpP "v_fN" (VarT "fN"))
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
  (ExpP "v_valtype" (VarT "valtype"))
  (ExpP "v_val_" (VarT "val_"))
  (IterT (VarT "byte") List)
)
(HintD (DecH "bytes_" (hint "inverse" "$inv_bytes_")))
(DecD
  "inv_ibytes_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "var_0_lst" (IterT (VarT "byte") List))
  (VarT "iN")
)
(HintD (DecH "inv_ibytes_" (hint "show" "$bytes_(I#%, %)")))
(DecD
  "inv_fbytes_"
  (ExpP "v_N" (VarT "N"))
  (ExpP "var_0_lst" (IterT (VarT "byte") List))
  (VarT "fN")
)
(HintD (DecH "inv_fbytes_" (hint "show" "$bytes_(F#%, %)")))
(DecD
  "inv_bytes_"
  (ExpP "v_valtype" (VarT "valtype"))
  (ExpP "var_0_lst" (IterT (VarT "byte") List))
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
(DecD "inot_" (ExpP "v_N" (VarT "N")) (ExpP "v_iN" (VarT "iN")) (VarT "iN"))
(HintD (DecH "ishr_" (hint "show" "$ishr_(%)^(%)#((%, %))")))
(RelD
  "fun_inez_"
  (Seq Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "N"))
    (typbind "_" (VarT "iN"))
    (typbind "_" (VarT "u32"))
  )
  (RuleD
    "fun_inez__case_0"
    (ExpP "v_N" nat)
    (ExpP "i_1" (VarT "uN"))
    (Seq Arg Arg Arg)
    (TupE
      (VarE "v_N")
      (VarE "i_1")
      (CaseE
        (Seq (Atom mk_uN) Arg)
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
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (NumE (Nat 32))
        (CaseE
          (Seq (Atom mk_uN) Arg)
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
        (TupT (typbind "v_funcaddr" (VarT "funcaddr")))
      )
      (typcase
        (Seq (Atom GLOBAL) Arg)
        (TupT (typbind "v_globaladdr" (VarT "globaladdr")))
      )
      (typcase
        (Seq (Atom TABLE) Arg)
        (TupT (typbind "v_tableaddr" (VarT "tableaddr")))
      )
      (typcase
        (Seq (Atom MEM) Arg)
        (TupT (typbind "v_memaddr" (VarT "memaddr")))
      )
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
        (TupT
          (typbind "v_valtype" (VarT "valtype"))
          (typbind "_" (VarT "val_"))
        )
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
    (ExpP "v_valtype" (VarT "valtype"))
    (ExpP "var_0" (VarT "val_"))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom CONST) Arg Arg)
        (TupE (VarE "v_valtype") (VarE "var_0"))
      )
    )
    (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "v_valtype") (VarE "var_0")))
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
        (TupT (typbind "val_lst" (IterT (VarT "val") List)))
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
    (ExpP "val_lst" (IterT (VarT "val") List))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom _VALS) Arg) (TupE (VarE "val_lst"))))
    (IterPr
      (RulePr "wf_val" (Seq Arg) (TupE (VarE "v_val")))
      List
      (iterexp "v_val" (VarE "val_lst"))
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
    (ExpP "var_0_lst" (IterT (VarT "functype") List))
    (ExpP "var_1_lst" (IterT (VarT "funcaddr") List))
    (ExpP "var_2_lst" (IterT (VarT "globaladdr") List))
    (ExpP "var_3_lst" (IterT (VarT "tableaddr") List))
    (ExpP "var_4_lst" (IterT (VarT "memaddr") List))
    (ExpP "var_5_lst" (IterT (VarT "exportinst") List))
    (Seq Arg)
    (TupE
      (StrE
        (expfield (Atom TYPES) (VarE "var_0_lst"))
        (expfield (Atom FUNCS) (VarE "var_1_lst"))
        (expfield (Atom GLOBALS) (VarE "var_2_lst"))
        (expfield (Atom TABLES) (VarE "var_3_lst"))
        (expfield (Atom MEMS) (VarE "var_4_lst"))
        (expfield (Atom EXPORTS) (VarE "var_5_lst"))
      )
    )
    (IterPr
      (RulePr "wf_exportinst" (Seq Arg) (TupE (VarE "var_5")))
      List
      (iterexp "var_5" (VarE "var_5_lst"))
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
    (ExpP "var_1_opt_lst" (IterT (IterT (VarT "funcaddr") Opt) List))
    (Seq Arg)
    (TupE
      (StrE
        (expfield (Atom TYPE) (VarE "var_0"))
        (expfield (Atom REFS) (VarE "var_1_opt_lst"))
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
    (ExpP "var_1_lst" (IterT (VarT "byte") List))
    (Seq Arg)
    (TupE
      (StrE
        (expfield (Atom TYPE) (VarE "var_0"))
        (expfield (Atom BYTES) (VarE "var_1_lst"))
      )
    )
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "var_0")))
    (IterPr
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "var_1")))
      List
      (iterexp "var_1" (VarE "var_1_lst"))
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
    (ExpP "var_0_lst" (IterT (VarT "funcinst") List))
    (ExpP "var_1_lst" (IterT (VarT "globalinst") List))
    (ExpP "var_2_lst" (IterT (VarT "tableinst") List))
    (ExpP "var_3_lst" (IterT (VarT "meminst") List))
    (Seq Arg)
    (TupE
      (StrE
        (expfield (Atom FUNCS) (VarE "var_0_lst"))
        (expfield (Atom GLOBALS) (VarE "var_1_lst"))
        (expfield (Atom TABLES) (VarE "var_2_lst"))
        (expfield (Atom MEMS) (VarE "var_3_lst"))
      )
    )
    (IterPr
      (RulePr "wf_funcinst" (Seq Arg) (TupE (VarE "var_0")))
      List
      (iterexp "var_0" (VarE "var_0_lst"))
    )
    (IterPr
      (RulePr "wf_globalinst" (Seq Arg) (TupE (VarE "var_1")))
      List
      (iterexp "var_1" (VarE "var_1_lst"))
    )
    (IterPr
      (RulePr "wf_tableinst" (Seq Arg) (TupE (VarE "var_2")))
      List
      (iterexp "var_2" (VarE "var_2_lst"))
    )
    (IterPr
      (RulePr "wf_meminst" (Seq Arg) (TupE (VarE "var_3")))
      List
      (iterexp "var_3" (VarE "var_3_lst"))
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
    (ExpP "var_0_lst" (IterT (VarT "val") List))
    (ExpP "var_1" (VarT "moduleinst"))
    (Seq Arg)
    (TupE
      (StrE
        (expfield (Atom LOCALS) (VarE "var_0_lst"))
        (expfield (Atom MODULE) (VarE "var_1"))
      )
    )
    (IterPr
      (RulePr "wf_val" (Seq Arg) (TupE (VarE "var_0")))
      List
      (iterexp "var_0" (VarE "var_0_lst"))
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
        (Seq (Atom mk_state) Arg Arg)
        (TupT
          (typbind "v_store" (VarT "store"))
          (typbind "v_frame" (VarT "frame"))
        )
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
    (ExpP "v_store" (VarT "store"))
    (ExpP "v_frame" (VarT "frame"))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_state) Arg Arg)
        (TupE (VarE "v_store") (VarE "v_frame"))
      )
    )
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "v_store")))
    (RulePr "wf_frame" (Seq Arg) (TupE (VarE "v_frame")))
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
            (typbind "v_blocktype" (VarT "blocktype"))
            (typbind "instr_lst" (IterT (VarT "instr") List))
          )
        )
        (typcase
          (Seq (Atom LOOP) Arg Arg)
          (TupT
            (typbind "v_blocktype" (VarT "blocktype"))
            (typbind "instr_lst" (IterT (VarT "instr") List))
          )
        )
        (typcase
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupT
            (typbind "v_blocktype" (VarT "blocktype"))
            (typbind "instr_lst" (IterT (VarT "instr") List))
            (typbind "instr_lst" (IterT (VarT "instr") List))
          )
        )
        (typcase
          (Seq (Atom BR) Arg)
          (TupT (typbind "v_labelidx" (VarT "labelidx")))
        )
        (typcase
          (Seq (Atom BR_IF) Arg)
          (TupT (typbind "v_labelidx" (VarT "labelidx")))
        )
        (typcase
          (Seq (Atom BR_TABLE) Arg Arg)
          (TupT
            (typbind "labelidx_lst" (IterT (VarT "labelidx") List))
            (typbind "v_labelidx" (VarT "labelidx"))
          )
        )
        (typcase
          (Seq (Atom CALL) Arg)
          (TupT (typbind "v_funcidx" (VarT "funcidx")))
        )
        (typcase
          (Seq (Atom CALL_INDIRECT) Arg)
          (TupT (typbind "v_typeidx" (VarT "typeidx")))
        )
        (typcase (Atom RETURN) (TupT))
        (typcase
          (Seq (Atom CONST) Arg Arg)
          (TupT
            (typbind "v_valtype" (VarT "valtype"))
            (typbind "_" (VarT "val_"))
          )
        )
        (typcase
          (Seq (Atom UNOP) Arg Arg)
          (TupT
            (typbind "v_valtype" (VarT "valtype"))
            (typbind "_" (VarT "unop_"))
          )
        )
        (typcase
          (Seq (Atom BINOP) Arg Arg)
          (TupT
            (typbind "v_valtype" (VarT "valtype"))
            (typbind "_" (VarT "binop_"))
          )
        )
        (typcase
          (Seq (Atom TESTOP) Arg Arg)
          (TupT
            (typbind "v_valtype" (VarT "valtype"))
            (typbind "_" (VarT "testop_"))
          )
        )
        (typcase
          (Seq (Atom RELOP) Arg Arg)
          (TupT
            (typbind "v_valtype" (VarT "valtype"))
            (typbind "_" (VarT "relop_"))
          )
        )
        (typcase
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupT
            (typbind "valtype_1" (VarT "valtype"))
            (typbind "valtype_2" (VarT "valtype"))
            (typbind "v_cvtop" (VarT "cvtop"))
          )
        )
        (typcase
          (Seq (Atom LOCAL_GET) Arg)
          (TupT (typbind "v_localidx" (VarT "localidx")))
        )
        (typcase
          (Seq (Atom LOCAL_SET) Arg)
          (TupT (typbind "v_localidx" (VarT "localidx")))
        )
        (typcase
          (Seq (Atom LOCAL_TEE) Arg)
          (TupT (typbind "v_localidx" (VarT "localidx")))
        )
        (typcase
          (Seq (Atom GLOBAL_GET) Arg)
          (TupT (typbind "v_globalidx" (VarT "globalidx")))
        )
        (typcase
          (Seq (Atom GLOBAL_SET) Arg)
          (TupT (typbind "v_globalidx" (VarT "globalidx")))
        )
        (typcase
          (Seq (Atom LOAD) Arg Arg Arg)
          (TupT
            (typbind "v_valtype" (VarT "valtype"))
            (typbind "_" (IterT (VarT "loadop_") Opt))
            (typbind "v_memarg" (VarT "memarg"))
          )
        )
        (typcase
          (Seq (Atom STORE) Arg Arg Arg)
          (TupT
            (typbind "v_valtype" (VarT "valtype"))
            (typbind "sz_opt" (IterT (VarT "sz") Opt))
            (typbind "v_memarg" (VarT "memarg"))
          )
          (ExpP "Inn_opt" (IterT (VarT "Inn") Opt))
        )
        (typcase (Atom MEMORY_SIZE) (TupT))
        (typcase (Atom MEMORY_GROW) (TupT))
        (typcase
          (Seq (Atom CALL_ADDR) Arg)
          (TupT (typbind "v_funcaddr" (VarT "funcaddr")))
        )
        (typcase
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupT
            (typbind "v_n" (VarT "n"))
            (typbind "instr_lst" (IterT (VarT "instr") List))
            (typbind "admininstr_lst" (IterT (VarT "admininstr") List))
          )
        )
        (typcase
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupT
            (typbind "v_n" (VarT "n"))
            (typbind "v_frame" (VarT "frame"))
            (typbind "admininstr_lst" (IterT (VarT "admininstr") List))
          )
        )
        (typcase (Atom TRAP) (TupT))
      )
    )
  )
)
(DecD
  "admininstr_instr"
  (ExpP "var_0" (VarT "instr"))
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
    (ExpA (CaseE (Seq (Atom LOCAL_GET) Arg) (TupE (VarE "x0"))))
    (CaseE (Seq (Atom LOCAL_GET) Arg) (TupE (VarE "x0")))
  )
  (DefD
    (ExpP "x0" (VarT "localidx"))
    (ExpA (CaseE (Seq (Atom LOCAL_SET) Arg) (TupE (VarE "x0"))))
    (CaseE (Seq (Atom LOCAL_SET) Arg) (TupE (VarE "x0")))
  )
  (DefD
    (ExpP "x0" (VarT "localidx"))
    (ExpA (CaseE (Seq (Atom LOCAL_TEE) Arg) (TupE (VarE "x0"))))
    (CaseE (Seq (Atom LOCAL_TEE) Arg) (TupE (VarE "x0")))
  )
  (DefD
    (ExpP "x0" (VarT "globalidx"))
    (ExpA (CaseE (Seq (Atom GLOBAL_GET) Arg) (TupE (VarE "x0"))))
    (CaseE (Seq (Atom GLOBAL_GET) Arg) (TupE (VarE "x0")))
  )
  (DefD
    (ExpP "x0" (VarT "globalidx"))
    (ExpA (CaseE (Seq (Atom GLOBAL_SET) Arg) (TupE (VarE "x0"))))
    (CaseE (Seq (Atom GLOBAL_SET) Arg) (TupE (VarE "x0")))
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
    (ExpA (CaseE (Atom MEMORY_SIZE) (TupE)))
    (CaseE (Atom MEMORY_SIZE) (TupE))
  )
  (DefD
    (ExpA (CaseE (Atom MEMORY_GROW) (TupE)))
    (CaseE (Atom MEMORY_GROW) (TupE))
  )
)
(DecD
  "admininstr_val"
  (ExpP "var_0" (VarT "val"))
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
      (ExpP "v_blocktype" (VarT "blocktype"))
      (ExpP "instr_lst" (IterT (VarT "instr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BLOCK) Arg Arg)
          (TupE (VarE "v_blocktype") (VarE "instr_lst"))
        )
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_instr")))
        List
        (iterexp "v_instr" (VarE "instr_lst"))
      )
    )
    (RuleD
      "admininstr_case_5"
      (ExpP "v_blocktype" (VarT "blocktype"))
      (ExpP "instr_lst" (IterT (VarT "instr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LOOP) Arg Arg)
          (TupE (VarE "v_blocktype") (VarE "instr_lst"))
        )
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_instr")))
        List
        (iterexp "v_instr" (VarE "instr_lst"))
      )
    )
    (RuleD
      "admininstr_case_6"
      (ExpP "v_blocktype" (VarT "blocktype"))
      (ExpP "instr_lst" (IterT (VarT "instr") List))
      (ExpP "instr_lst_0_lst" (IterT (VarT "instr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupE
            (VarE "v_blocktype")
            (VarE "instr_lst")
            (VarE "instr_lst_0_lst")
          )
        )
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_instr")))
        List
        (iterexp "v_instr" (VarE "instr_lst"))
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr_lst_0")))
        List
        (iterexp "instr_lst_0" (VarE "instr_lst_0_lst"))
      )
    )
    (RuleD
      "admininstr_case_7"
      (ExpP "v_labelidx" (VarT "labelidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BR) Arg) (TupE (VarE "v_labelidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_labelidx")))
    )
    (RuleD
      "admininstr_case_8"
      (ExpP "v_labelidx" (VarT "labelidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BR_IF) Arg) (TupE (VarE "v_labelidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_labelidx")))
    )
    (RuleD
      "admininstr_case_9"
      (ExpP "labelidx_lst" (IterT (VarT "labelidx") List))
      (ExpP "v_labelidx" (VarT "labelidx"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BR_TABLE) Arg Arg)
          (TupE (VarE "labelidx_lst") (VarE "v_labelidx"))
        )
      )
      (IterPr
        (RulePr
          "wf_uN"
          (Seq Arg Arg)
          (TupE (NumE (Nat 32)) (VarE "v_labelidx"))
        )
        List
        (iterexp "v_labelidx" (VarE "labelidx_lst"))
      )
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_labelidx")))
    )
    (RuleD
      "admininstr_case_10"
      (ExpP "v_funcidx" (VarT "funcidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "v_funcidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_funcidx")))
    )
    (RuleD
      "admininstr_case_11"
      (ExpP "v_typeidx" (VarT "typeidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "v_typeidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_typeidx")))
    )
    (RuleD "admininstr_case_12" (Seq Arg) (TupE (CaseE (Atom RETURN) (TupE))))
    (RuleD
      "admininstr_case_13"
      (ExpP "v_valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "val_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (VarE "v_valtype") (VarE "var_0"))
        )
      )
      (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "v_valtype") (VarE "var_0")))
    )
    (RuleD
      "admininstr_case_14"
      (ExpP "v_valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "unop_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom UNOP) Arg Arg)
          (TupE (VarE "v_valtype") (VarE "var_0"))
        )
      )
      (RulePr "wf_unop_" (Seq Arg Arg) (TupE (VarE "v_valtype") (VarE "var_0")))
    )
    (RuleD
      "admininstr_case_15"
      (ExpP "v_valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "binop_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BINOP) Arg Arg)
          (TupE (VarE "v_valtype") (VarE "var_0"))
        )
      )
      (RulePr
        "wf_binop_"
        (Seq Arg Arg)
        (TupE (VarE "v_valtype") (VarE "var_0"))
      )
    )
    (RuleD
      "admininstr_case_16"
      (ExpP "v_valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "testop_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom TESTOP) Arg Arg)
          (TupE (VarE "v_valtype") (VarE "var_0"))
        )
      )
      (RulePr
        "wf_testop_"
        (Seq Arg Arg)
        (TupE (VarE "v_valtype") (VarE "var_0"))
      )
    )
    (RuleD
      "admininstr_case_17"
      (ExpP "v_valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "relop_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom RELOP) Arg Arg)
          (TupE (VarE "v_valtype") (VarE "var_0"))
        )
      )
      (RulePr
        "wf_relop_"
        (Seq Arg Arg)
        (TupE (VarE "v_valtype") (VarE "var_0"))
      )
    )
    (RuleD
      "admininstr_case_18"
      (ExpP "valtype_1" (VarT "valtype"))
      (ExpP "valtype_2" (VarT "valtype"))
      (ExpP "v_cvtop" (VarT "cvtop"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupE (VarE "valtype_1") (VarE "valtype_2") (VarE "v_cvtop"))
        )
      )
      (IfPr (CmpE NeOp bool (VarE "valtype_1") (VarE "valtype_2")))
    )
    (RuleD
      "admininstr_case_19"
      (ExpP "v_localidx" (VarT "localidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL_GET) Arg) (TupE (VarE "v_localidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_localidx")))
    )
    (RuleD
      "admininstr_case_20"
      (ExpP "v_localidx" (VarT "localidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL_SET) Arg) (TupE (VarE "v_localidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_localidx")))
    )
    (RuleD
      "admininstr_case_21"
      (ExpP "v_localidx" (VarT "localidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL_TEE) Arg) (TupE (VarE "v_localidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_localidx")))
    )
    (RuleD
      "admininstr_case_22"
      (ExpP "v_globalidx" (VarT "globalidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL_GET) Arg) (TupE (VarE "v_globalidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_globalidx")))
    )
    (RuleD
      "admininstr_case_23"
      (ExpP "v_globalidx" (VarT "globalidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL_SET) Arg) (TupE (VarE "v_globalidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "v_globalidx")))
    )
    (RuleD
      "admininstr_case_24"
      (ExpP "v_valtype" (VarT "valtype"))
      (ExpP "var_0_opt" (IterT (VarT "loadop_") Opt))
      (ExpP "v_memarg" (VarT "memarg"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LOAD) Arg Arg Arg)
          (TupE (VarE "v_valtype") (VarE "var_0_opt") (VarE "v_memarg"))
        )
      )
      (IterPr
        (RulePr
          "wf_loadop_"
          (Seq Arg Arg)
          (TupE (VarE "v_valtype") (VarE "var_0"))
        )
        Opt
        (iterexp "var_0" (VarE "var_0_opt"))
      )
      (RulePr "wf_memarg" (Seq Arg) (TupE (VarE "v_memarg")))
    )
    (RuleD
      "admininstr_case_25"
      (ExpP "Inn_opt" (IterT (VarT "Inn") Opt))
      (ExpP "v_valtype" (VarT "valtype"))
      (ExpP "sz_opt" (IterT (VarT "sz") Opt))
      (ExpP "v_memarg" (VarT "memarg"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom STORE) Arg Arg Arg)
          (TupE (VarE "v_valtype") (VarE "sz_opt") (VarE "v_memarg"))
        )
      )
      (IterPr
        (RulePr "wf_sz" (Seq Arg) (TupE (VarE "v_sz")))
        Opt
        (iterexp "v_sz" (VarE "sz_opt"))
      )
      (RulePr "wf_memarg" (Seq Arg) (TupE (VarE "v_memarg")))
      (IfPr
        (BinE
          EquivOp
          bool
          (CmpE EqOp bool (VarE "Inn_opt") (OptE))
          (CmpE EqOp bool (VarE "sz_opt") (OptE))
        )
      )
      (IterPr
        (IfPr
          (BinE
            AndOp
            bool
            (CmpE
              EqOp
              bool
              (VarE "v_valtype")
              (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
            )
            (CmpE
              LtOp
              nat
              (ProjE (CallE "proj_sz_0" (ExpA (VarE "v_sz"))) 0)
              (CallE "size" (ExpA (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))))
            )
          )
        )
        Opt
        (iterexp "v_Inn" (VarE "Inn_opt"))
        (iterexp "v_sz" (VarE "sz_opt"))
      )
    )
    (RuleD
      "admininstr_case_26"
      (Seq Arg)
      (TupE (CaseE (Atom MEMORY_SIZE) (TupE)))
    )
    (RuleD
      "admininstr_case_27"
      (Seq Arg)
      (TupE (CaseE (Atom MEMORY_GROW) (TupE)))
    )
    (RuleD
      "admininstr_case_28"
      (ExpP "v_funcaddr" (VarT "funcaddr"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CALL_ADDR) Arg) (TupE (VarE "v_funcaddr"))))
    )
    (RuleD
      "admininstr_case_29"
      (ExpP "v_n" (VarT "n"))
      (ExpP "instr_lst" (IterT (VarT "instr") List))
      (ExpP "admininstr_lst" (IterT (VarT "admininstr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE (VarE "v_n") (VarE "instr_lst") (VarE "admininstr_lst"))
        )
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_instr")))
        List
        (iterexp "v_instr" (VarE "instr_lst"))
      )
      (IterPr
        (RulePr "wf_admininstr" (Seq Arg) (TupE (VarE "v_admininstr")))
        List
        (iterexp "v_admininstr" (VarE "admininstr_lst"))
      )
    )
    (RuleD
      "admininstr_case_30"
      (ExpP "v_n" (VarT "n"))
      (ExpP "v_frame" (VarT "frame"))
      (ExpP "admininstr_lst" (IterT (VarT "admininstr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE (VarE "v_n") (VarE "v_frame") (VarE "admininstr_lst"))
        )
      )
      (RulePr "wf_frame" (Seq Arg) (TupE (VarE "v_frame")))
      (IterPr
        (RulePr "wf_admininstr" (Seq Arg) (TupE (VarE "v_admininstr")))
        List
        (iterexp "v_admininstr" (VarE "admininstr_lst"))
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
        (Seq (Atom mk_config) Arg Arg)
        (TupT
          (typbind "v_state" (VarT "state"))
          (typbind "admininstr_lst" (IterT (VarT "admininstr") List))
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
    (ExpP "v_state" (VarT "state"))
    (ExpP "admininstr_lst" (IterT (VarT "admininstr") List))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE (VarE "v_state") (VarE "admininstr_lst"))
      )
    )
    (RulePr "wf_state" (Seq Arg) (TupE (VarE "v_state")))
    (IterPr
      (RulePr "wf_admininstr" (Seq Arg) (TupE (VarE "v_admininstr")))
      List
      (iterexp "v_admininstr" (VarE "admininstr_lst"))
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
(RelD
  "fun_default_"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "valtype")) (typbind "_" (VarT "val")))
  (RuleD
    "fun_default__case_0"
    (Seq Arg Arg)
    (TupE
      (CaseE (Atom I32) (TupE))
      (CaseE
        (Seq (Atom CONST) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE
              (CaseE (Atom I32) (TupE))
              (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
            )
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
            (CaseE (Atom I32) (TupE))
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE
                (CaseE (Atom I32) (TupE))
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
              )
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_default__case_1"
    (Seq Arg Arg)
    (TupE
      (CaseE (Atom I64) (TupE))
      (CaseE
        (Seq (Atom CONST) Arg Arg)
        (TupE
          (CaseE (Atom I64) (TupE))
          (CaseE
            (Seq (Atom mk_val__0) Arg Arg)
            (TupE
              (CaseE (Atom I64) (TupE))
              (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
            )
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
            (CaseE (Atom I64) (TupE))
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE
                (CaseE (Atom I64) (TupE))
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
              )
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_default__case_2"
    (ExpP "var_0" (VarT "fN"))
    (Seq Arg Arg)
    (TupE
      (CaseE (Atom F32) (TupE))
      (CaseE
        (Seq (Atom CONST) Arg Arg)
        (TupE
          (CaseE (Atom F32) (TupE))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F32) (TupE)) (VarE "var_0"))
          )
        )
      )
    )
    (RulePr "fun_fzero" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "var_0")))
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
              (TupE (CaseE (Atom F32) (TupE)) (VarE "var_0"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_default__case_3"
    (ExpP "var_0" (VarT "fN"))
    (Seq Arg Arg)
    (TupE
      (CaseE (Atom F64) (TupE))
      (CaseE
        (Seq (Atom CONST) Arg Arg)
        (TupE
          (CaseE (Atom F64) (TupE))
          (CaseE
            (Seq (Atom mk_val__1) Arg Arg)
            (TupE (CaseE (Atom F64) (TupE)) (VarE "var_0"))
          )
        )
      )
    )
    (RulePr "fun_fzero" (Seq Arg Arg) (TupE (NumE (Nat 64)) (VarE "var_0")))
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
              (TupE (CaseE (Atom F64) (TupE)) (VarE "var_0"))
            )
          )
        )
      )
    )
  )
)
(RecD
  (RelD
    "fun_funcsxa"
    (Seq Arg Arg)
    (TupT
      (typbind "_" (IterT (VarT "externaddr") List))
      (typbind "_" (IterT (VarT "funcaddr") List))
    )
    (RuleD "fun_funcsxa_case_0" (Seq Arg Arg) (TupE (ListE) (ListE)))
    (RuleD
      "fun_funcsxa_case_1"
      (ExpP "fa" nat)
      (ExpP "xv_lst" (IterT (VarT "externaddr") List))
      (ExpP "var_0" (IterT (VarT "funcaddr") List))
      (Seq Arg Arg)
      (TupE
        (CatE
          (ListE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "fa"))))
          (VarE "xv_lst")
        )
        (CatE (ListE (VarE "fa")) (VarE "var_0"))
      )
      (RulePr "fun_funcsxa" (Seq Arg Arg) (TupE (VarE "xv_lst") (VarE "var_0")))
    )
    (RuleD
      "fun_funcsxa_case_2"
      (ExpP "v_externaddr" (VarT "externaddr"))
      (ExpP "xv_lst" (IterT (VarT "externaddr") List))
      (ExpP "var_0" (IterT (VarT "funcaddr") List))
      (Seq Arg Arg)
      (TupE (CatE (ListE (VarE "v_externaddr")) (VarE "xv_lst")) (VarE "var_0"))
      (RulePr "fun_funcsxa" (Seq Arg Arg) (TupE (VarE "xv_lst") (VarE "var_0")))
    )
  )
)
(HintD (DecH "funcsxa" (hint "show" "$funcs(%)")))
(RecD
  (RelD
    "fun_globalsxa"
    (Seq Arg Arg)
    (TupT
      (typbind "_" (IterT (VarT "externaddr") List))
      (typbind "_" (IterT (VarT "globaladdr") List))
    )
    (RuleD "fun_globalsxa_case_0" (Seq Arg Arg) (TupE (ListE) (ListE)))
    (RuleD
      "fun_globalsxa_case_1"
      (ExpP "ga" nat)
      (ExpP "xv_lst" (IterT (VarT "externaddr") List))
      (ExpP "var_0" (IterT (VarT "globaladdr") List))
      (Seq Arg Arg)
      (TupE
        (CatE
          (ListE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "ga"))))
          (VarE "xv_lst")
        )
        (CatE (ListE (VarE "ga")) (VarE "var_0"))
      )
      (RulePr
        "fun_globalsxa"
        (Seq Arg Arg)
        (TupE (VarE "xv_lst") (VarE "var_0"))
      )
    )
    (RuleD
      "fun_globalsxa_case_2"
      (ExpP "v_externaddr" (VarT "externaddr"))
      (ExpP "xv_lst" (IterT (VarT "externaddr") List))
      (ExpP "var_0" (IterT (VarT "globaladdr") List))
      (Seq Arg Arg)
      (TupE (CatE (ListE (VarE "v_externaddr")) (VarE "xv_lst")) (VarE "var_0"))
      (RulePr
        "fun_globalsxa"
        (Seq Arg Arg)
        (TupE (VarE "xv_lst") (VarE "var_0"))
      )
    )
  )
)
(HintD (DecH "globalsxa" (hint "show" "$globals(%)")))
(RecD
  (RelD
    "fun_tablesxa"
    (Seq Arg Arg)
    (TupT
      (typbind "_" (IterT (VarT "externaddr") List))
      (typbind "_" (IterT (VarT "tableaddr") List))
    )
    (RuleD "fun_tablesxa_case_0" (Seq Arg Arg) (TupE (ListE) (ListE)))
    (RuleD
      "fun_tablesxa_case_1"
      (ExpP "ta" nat)
      (ExpP "xv_lst" (IterT (VarT "externaddr") List))
      (ExpP "var_0" (IterT (VarT "tableaddr") List))
      (Seq Arg Arg)
      (TupE
        (CatE
          (ListE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "ta"))))
          (VarE "xv_lst")
        )
        (CatE (ListE (VarE "ta")) (VarE "var_0"))
      )
      (RulePr
        "fun_tablesxa"
        (Seq Arg Arg)
        (TupE (VarE "xv_lst") (VarE "var_0"))
      )
    )
    (RuleD
      "fun_tablesxa_case_2"
      (ExpP "v_externaddr" (VarT "externaddr"))
      (ExpP "xv_lst" (IterT (VarT "externaddr") List))
      (ExpP "var_0" (IterT (VarT "tableaddr") List))
      (Seq Arg Arg)
      (TupE (CatE (ListE (VarE "v_externaddr")) (VarE "xv_lst")) (VarE "var_0"))
      (RulePr
        "fun_tablesxa"
        (Seq Arg Arg)
        (TupE (VarE "xv_lst") (VarE "var_0"))
      )
    )
  )
)
(HintD (DecH "tablesxa" (hint "show" "$tables(%)")))
(RecD
  (RelD
    "fun_memsxa"
    (Seq Arg Arg)
    (TupT
      (typbind "_" (IterT (VarT "externaddr") List))
      (typbind "_" (IterT (VarT "memaddr") List))
    )
    (RuleD "fun_memsxa_case_0" (Seq Arg Arg) (TupE (ListE) (ListE)))
    (RuleD
      "fun_memsxa_case_1"
      (ExpP "ma" nat)
      (ExpP "xv_lst" (IterT (VarT "externaddr") List))
      (ExpP "var_0" (IterT (VarT "memaddr") List))
      (Seq Arg Arg)
      (TupE
        (CatE
          (ListE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "ma"))))
          (VarE "xv_lst")
        )
        (CatE (ListE (VarE "ma")) (VarE "var_0"))
      )
      (RulePr "fun_memsxa" (Seq Arg Arg) (TupE (VarE "xv_lst") (VarE "var_0")))
    )
    (RuleD
      "fun_memsxa_case_2"
      (ExpP "v_externaddr" (VarT "externaddr"))
      (ExpP "xv_lst" (IterT (VarT "externaddr") List))
      (ExpP "var_0" (IterT (VarT "memaddr") List))
      (Seq Arg Arg)
      (TupE (CatE (ListE (VarE "v_externaddr")) (VarE "xv_lst")) (VarE "var_0"))
      (RulePr "fun_memsxa" (Seq Arg Arg) (TupE (VarE "xv_lst") (VarE "var_0")))
    )
  )
)
(HintD (DecH "memsxa" (hint "show" "$mems(%)")))
(DecD
  "fun_store"
  (ExpP "v_state" (VarT "state"))
  (VarT "store")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
    (VarE "s")
  )
)
(HintD (DecH "store" (hint "show" "%.STORE")))
(DecD
  "fun_frame"
  (ExpP "v_state" (VarT "state"))
  (VarT "frame")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
    (VarE "f")
  )
)
(HintD (DecH "frame" (hint "show" "%.FRAME")))
(DecD
  "fun_funcaddr"
  (ExpP "v_state" (VarT "state"))
  (IterT (VarT "funcaddr") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (DotE (VarE "f") (Atom MODULE)) (Atom FUNCS))
  )
)
(HintD (DecH "funcaddr" (hint "show" "%.MODULE.FUNCS")))
(DecD
  "fun_funcinst"
  (ExpP "v_state" (VarT "state"))
  (IterT (VarT "funcinst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom FUNCS))
  )
)
(HintD (DecH "funcinst" (hint "show" "%.FUNCS")))
(DecD
  "fun_globalinst"
  (ExpP "v_state" (VarT "state"))
  (IterT (VarT "globalinst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom GLOBALS))
  )
)
(HintD (DecH "globalinst" (hint "show" "%.GLOBALS")))
(DecD
  "fun_tableinst"
  (ExpP "v_state" (VarT "state"))
  (IterT (VarT "tableinst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom TABLES))
  )
)
(HintD (DecH "tableinst" (hint "show" "%.TABLES")))
(DecD
  "fun_meminst"
  (ExpP "v_state" (VarT "state"))
  (IterT (VarT "meminst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom MEMS))
  )
)
(HintD (DecH "meminst" (hint "show" "%.MEMS")))
(DecD
  "fun_moduleinst"
  (ExpP "v_state" (VarT "state"))
  (VarT "moduleinst")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "f") (Atom MODULE))
  )
)
(HintD (DecH "moduleinst" (hint "show" "%.MODULE")))
(DecD
  "fun_type"
  (ExpP "v_state" (VarT "state"))
  (ExpP "v_typeidx" (VarT "typeidx"))
  (VarT "functype")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (DotE (VarE "f") (Atom MODULE)) (Atom TYPES))
      (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
    )
  )
)
(HintD (DecH "type" (hint "show" "%.TYPES[%]")))
(DecD
  "fun_func"
  (ExpP "v_state" (VarT "state"))
  (ExpP "v_funcidx" (VarT "funcidx"))
  (VarT "funcinst")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
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
  "fun_global"
  (ExpP "v_state" (VarT "state"))
  (ExpP "v_globalidx" (VarT "globalidx"))
  (VarT "globalinst")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
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
  "fun_table"
  (ExpP "v_state" (VarT "state"))
  (ExpP "v_tableidx" (VarT "tableidx"))
  (VarT "tableinst")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
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
  "fun_mem"
  (ExpP "v_state" (VarT "state"))
  (ExpP "v_memidx" (VarT "memidx"))
  (VarT "meminst")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
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
  "fun_local"
  (ExpP "v_state" (VarT "state"))
  (ExpP "v_localidx" (VarT "localidx"))
  (VarT "val")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (VarE "f") (Atom LOCALS))
      (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
    )
  )
)
(HintD (DecH "local" (hint "show" "%.LOCALS[%]")))
(RelD
  "fun_with_local"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "state"))
    (typbind "_" (VarT "localidx"))
    (typbind "_" (VarT "val"))
    (typbind "_" (VarT "state"))
  )
  (RuleD
    "fun_with_local_case_0"
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpP "v" (VarT "val"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f")))
      (VarE "x")
      (VarE "v")
      (CaseE
        (Seq (Atom mk_state) Arg Arg)
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
    (RulePr
      "wf_state"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_state) Arg Arg)
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
(RelD
  "fun_with_global"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "state"))
    (typbind "_" (VarT "globalidx"))
    (typbind "_" (VarT "val"))
    (typbind "_" (VarT "state"))
  )
  (RuleD
    "fun_with_global_case_0"
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpP "v" (VarT "val"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f")))
      (VarE "x")
      (VarE "v")
      (CaseE
        (Seq (Atom mk_state) Arg Arg)
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
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (DotE (DotE (VarE "f") (Atom MODULE)) (Atom GLOBALS)))
      )
    )
    (RulePr
      "wf_state"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_state) Arg Arg)
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
(RelD
  "fun_with_table"
  (Seq Arg Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "state"))
    (typbind "_" (VarT "tableidx"))
    (typbind "_" nat)
    (typbind "_" (VarT "funcaddr"))
    (typbind "_" (VarT "state"))
  )
  (RuleD
    "fun_with_table_case_0"
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpP "i" nat)
    (ExpP "a" nat)
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f")))
      (VarE "x")
      (VarE "i")
      (VarE "a")
      (CaseE
        (Seq (Atom mk_state) Arg Arg)
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
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (DotE (DotE (VarE "f") (Atom MODULE)) (Atom TABLES)))
      )
    )
    (RulePr
      "wf_state"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_state) Arg Arg)
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
(RelD
  "fun_with_tableinst"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "state"))
    (typbind "_" (VarT "tableidx"))
    (typbind "_" (VarT "tableinst"))
    (typbind "_" (VarT "state"))
  )
  (RuleD
    "fun_with_tableinst_case_0"
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpP "ti" (VarT "tableinst"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f")))
      (VarE "x")
      (VarE "ti")
      (CaseE
        (Seq (Atom mk_state) Arg Arg)
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
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (DotE (DotE (VarE "f") (Atom MODULE)) (Atom TABLES)))
      )
    )
    (RulePr
      "wf_state"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_state) Arg Arg)
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
(RelD
  "fun_with_mem"
  (Seq Arg Arg Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "state"))
    (typbind "_" (VarT "memidx"))
    (typbind "_" nat)
    (typbind "_" nat)
    (typbind "_" (IterT (VarT "byte") List))
    (typbind "_" (VarT "state"))
  )
  (RuleD
    "fun_with_mem_case_0"
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpP "i" nat)
    (ExpP "j" nat)
    (ExpP "b_lst" (IterT (VarT "byte") List))
    (Seq Arg Arg Arg Arg Arg Arg)
    (TupE
      (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f")))
      (VarE "x")
      (VarE "i")
      (VarE "j")
      (VarE "b_lst")
      (CaseE
        (Seq (Atom mk_state) Arg Arg)
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
            (VarE "b_lst")
          )
          (VarE "f")
        )
      )
    )
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (DotE (DotE (VarE "f") (Atom MODULE)) (Atom MEMS)))
      )
    )
    (RulePr
      "wf_state"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_state) Arg Arg)
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
              (VarE "b_lst")
            )
            (VarE "f")
          )
        )
      )
    )
  )
)
(HintD (DecH "with_mem" (hint "show" "%[MEMS[%].BYTES[% : %] = %]")))
(RelD
  "fun_with_meminst"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "state"))
    (typbind "_" (VarT "memidx"))
    (typbind "_" (VarT "meminst"))
    (typbind "_" (VarT "state"))
  )
  (RuleD
    "fun_with_meminst_case_0"
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" (VarT "uN"))
    (ExpP "mi" (VarT "meminst"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f")))
      (VarE "x")
      (VarE "mi")
      (CaseE
        (Seq (Atom mk_state) Arg Arg)
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
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (DotE (DotE (VarE "f") (Atom MODULE)) (Atom MEMS)))
      )
    )
    (RulePr
      "wf_state"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_state) Arg Arg)
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
(RelD
  "fun_growtable_before_fun_growtable_case_1"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "tableinst")) (typbind "_" nat))
  (RuleD
    "fun_growtable_case_0"
    (ExpP "ti" (VarT "tableinst"))
    (ExpP "v_n" nat)
    (ExpP "ti'" (VarT "tableinst"))
    (ExpP "i" (VarT "uN"))
    (ExpP "j_opt" (IterT (VarT "u32") Opt))
    (ExpP "a_lst" (IterT (VarT "addr") List))
    (ExpP "i'" nat)
    (Seq Arg Arg)
    (TupE (VarE "ti") (VarE "v_n"))
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "ti")
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Seq (Atom mk_limits) Arg Arg)
              (TupE (VarE "i") (VarE "j_opt"))
            )
          )
          (expfield
            (Atom REFS)
            (IterE (OptE (VarE "a_1")) List (iterexp "a_1" (VarE "a_lst")))
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "i'")
        (BinE AddOp nat (LenE (VarE "a_lst")) (VarE "v_n"))
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "i'")))
                (VarE "j_opt")
              )
            )
          )
          (expfield
            (Atom REFS)
            (CatE
              (IterE (OptE (VarE "a_3")) List (iterexp "a_3" (VarE "a_lst")))
              (IterE (OptE) (ListN (VarE "v_n")))
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
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "j_3"))) 0)
        )
      )
      Opt
      (iterexp "j_3" (VarE "j_opt"))
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE (VarE "i") (VarE "j_opt"))
            )
          )
          (expfield
            (Atom REFS)
            (IterE (OptE (VarE "a_4")) List (iterexp "a_4" (VarE "a_lst")))
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "i'")))
                (VarE "j_opt")
              )
            )
          )
          (expfield
            (Atom REFS)
            (CatE
              (IterE (OptE (VarE "a_5")) List (iterexp "a_5" (VarE "a_lst")))
              (IterE (OptE) (ListN (VarE "v_n")))
            )
          )
        )
      )
    )
  )
)
(RelD
  "fun_growtable"
  (Seq Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "tableinst"))
    (typbind "_" nat)
    (typbind "_" (IterT (VarT "tableinst") Opt))
  )
  (RuleD
    "fun_growtable_case_0"
    (ExpP "ti" (VarT "tableinst"))
    (ExpP "v_n" nat)
    (ExpP "ti'" (VarT "tableinst"))
    (ExpP "i" (VarT "uN"))
    (ExpP "j_opt" (IterT (VarT "u32") Opt))
    (ExpP "a_lst" (IterT (VarT "addr") List))
    (ExpP "i'" nat)
    (Seq Arg Arg Arg)
    (TupE (VarE "ti") (VarE "v_n") (OptE (VarE "ti'")))
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "ti")
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Seq (Atom mk_limits) Arg Arg)
              (TupE (VarE "i") (VarE "j_opt"))
            )
          )
          (expfield
            (Atom REFS)
            (IterE (OptE (VarE "a_1")) List (iterexp "a_1" (VarE "a_lst")))
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "i'")
        (BinE AddOp nat (LenE (VarE "a_lst")) (VarE "v_n"))
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "i'")))
                (VarE "j_opt")
              )
            )
          )
          (expfield
            (Atom REFS)
            (CatE
              (IterE (OptE (VarE "a_3")) List (iterexp "a_3" (VarE "a_lst")))
              (IterE (OptE) (ListN (VarE "v_n")))
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
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "j_3"))) 0)
        )
      )
      Opt
      (iterexp "j_3" (VarE "j_opt"))
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE (VarE "i") (VarE "j_opt"))
            )
          )
          (expfield
            (Atom REFS)
            (IterE (OptE (VarE "a_4")) List (iterexp "a_4" (VarE "a_lst")))
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "i'")))
                (VarE "j_opt")
              )
            )
          )
          (expfield
            (Atom REFS)
            (CatE
              (IterE (OptE (VarE "a_5")) List (iterexp "a_5" (VarE "a_lst")))
              (IterE (OptE) (ListN (VarE "v_n")))
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_growtable_case_1"
    (ExpP "x0" (VarT "tableinst"))
    (ExpP "x1" nat)
    (Seq Arg Arg Arg)
    (TupE (VarE "x0") (VarE "x1") (OptE))
    (NegPr
      (RulePr
        "fun_growtable_before_fun_growtable_case_1"
        (Seq Arg Arg)
        (TupE (VarE "x0") (VarE "x1"))
      )
    )
  )
)
(HintD (DecH "growtable" (hint "partial" "{}")))
(RelD
  "fun_growmemory_before_fun_growmemory_case_1"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "meminst")) (typbind "_" nat))
  (RuleD
    "fun_growmemory_case_0"
    (ExpP "mi" (VarT "meminst"))
    (ExpP "v_n" nat)
    (ExpP "mi'" (VarT "meminst"))
    (ExpP "i" (VarT "u32"))
    (ExpP "j_opt" (IterT (VarT "u32") Opt))
    (ExpP "b_lst" (IterT (VarT "byte") List))
    (ExpP "i'" rat)
    (Seq Arg Arg)
    (TupE (VarE "mi") (VarE "v_n"))
    (IfPr
      (CmpE
        EqOp
        bool
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Seq (Atom mk_limits) Arg Arg)
              (TupE (VarE "i") (VarE "j_opt"))
            )
          )
          (expfield (Atom BYTES) (VarE "b_lst"))
        )
        (VarE "mi")
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "i'")
        (BinE
          AddOp
          rat
          (BinE
            DivOp
            rat
            (CvtE nat rat (LenE (VarE "b_lst")))
            (CvtE nat rat (BinE MulOp nat (NumE (Nat 64)) (CallE "Ki")))
          )
          (CvtE nat rat (VarE "v_n"))
        )
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (CvtE rat nat (VarE "i'"))))
                (VarE "j_opt")
              )
            )
          )
          (expfield
            (Atom BYTES)
            (CatE
              (VarE "b_lst")
              (IterE
                (CaseE (Seq (Atom mk_byte) Arg) (TupE (NumE (Nat 0))))
                (ListN
                  (BinE
                    MulOp
                    nat
                    (VarE "v_n")
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
          (CvtE nat rat (ProjE (CallE "proj_uN_0" (ExpA (VarE "j_8"))) 0))
        )
      )
      Opt
      (iterexp "j_8" (VarE "j_opt"))
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE (VarE "i") (VarE "j_opt"))
            )
          )
          (expfield (Atom BYTES) (VarE "b_lst"))
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (CvtE rat nat (VarE "i'"))))
                (VarE "j_opt")
              )
            )
          )
          (expfield
            (Atom BYTES)
            (CatE
              (VarE "b_lst")
              (IterE
                (CaseE (Seq (Atom mk_byte) Arg) (TupE (NumE (Nat 0))))
                (ListN
                  (BinE
                    MulOp
                    nat
                    (VarE "v_n")
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
(RelD
  "fun_growmemory"
  (Seq Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "meminst"))
    (typbind "_" nat)
    (typbind "_" (IterT (VarT "meminst") Opt))
  )
  (RuleD
    "fun_growmemory_case_0"
    (ExpP "mi" (VarT "meminst"))
    (ExpP "v_n" nat)
    (ExpP "mi'" (VarT "meminst"))
    (ExpP "i" (VarT "u32"))
    (ExpP "j_opt" (IterT (VarT "u32") Opt))
    (ExpP "b_lst" (IterT (VarT "byte") List))
    (ExpP "i'" rat)
    (Seq Arg Arg Arg)
    (TupE (VarE "mi") (VarE "v_n") (OptE (VarE "mi'")))
    (IfPr
      (CmpE
        EqOp
        bool
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Seq (Atom mk_limits) Arg Arg)
              (TupE (VarE "i") (VarE "j_opt"))
            )
          )
          (expfield (Atom BYTES) (VarE "b_lst"))
        )
        (VarE "mi")
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "i'")
        (BinE
          AddOp
          rat
          (BinE
            DivOp
            rat
            (CvtE nat rat (LenE (VarE "b_lst")))
            (CvtE nat rat (BinE MulOp nat (NumE (Nat 64)) (CallE "Ki")))
          )
          (CvtE nat rat (VarE "v_n"))
        )
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (CvtE rat nat (VarE "i'"))))
                (VarE "j_opt")
              )
            )
          )
          (expfield
            (Atom BYTES)
            (CatE
              (VarE "b_lst")
              (IterE
                (CaseE (Seq (Atom mk_byte) Arg) (TupE (NumE (Nat 0))))
                (ListN
                  (BinE
                    MulOp
                    nat
                    (VarE "v_n")
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
          (CvtE nat rat (ProjE (CallE "proj_uN_0" (ExpA (VarE "j_8"))) 0))
        )
      )
      Opt
      (iterexp "j_8" (VarE "j_opt"))
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE (VarE "i") (VarE "j_opt"))
            )
          )
          (expfield (Atom BYTES) (VarE "b_lst"))
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (CvtE rat nat (VarE "i'"))))
                (VarE "j_opt")
              )
            )
          )
          (expfield
            (Atom BYTES)
            (CatE
              (VarE "b_lst")
              (IterE
                (CaseE (Seq (Atom mk_byte) Arg) (TupE (NumE (Nat 0))))
                (ListN
                  (BinE
                    MulOp
                    nat
                    (VarE "v_n")
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
  (RuleD
    "fun_growmemory_case_1"
    (ExpP "x0" (VarT "meminst"))
    (ExpP "x1" nat)
    (Seq Arg Arg Arg)
    (TupE (VarE "x0") (VarE "x1") (OptE))
    (NegPr
      (RulePr
        "fun_growmemory_before_fun_growmemory_case_1"
        (Seq Arg Arg)
        (TupE (VarE "x0") (VarE "x1"))
      )
    )
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
    (ExpP "var_0_lst" (IterT (VarT "functype") List))
    (ExpP "var_1_lst" (IterT (VarT "functype") List))
    (ExpP "var_2_lst" (IterT (VarT "globaltype") List))
    (ExpP "var_3_lst" (IterT (VarT "tabletype") List))
    (ExpP "var_4_lst" (IterT (VarT "memtype") List))
    (ExpP "var_5_lst" (IterT (VarT "valtype") List))
    (ExpP "var_6_lst" (IterT (VarT "resulttype") List))
    (ExpP "var_7_opt" (IterT (VarT "resulttype") Opt))
    (Seq Arg)
    (TupE
      (StrE
        (expfield (Atom TYPES) (VarE "var_0_lst"))
        (expfield (Atom FUNCS) (VarE "var_1_lst"))
        (expfield (Atom GLOBALS) (VarE "var_2_lst"))
        (expfield (Atom TABLES) (VarE "var_3_lst"))
        (expfield (Atom MEMS) (VarE "var_4_lst"))
        (expfield (Atom LOCALS) (VarE "var_5_lst"))
        (expfield (Atom LABELS) (VarE "var_6_lst"))
        (expfield (Atom RETURN) (VarE "var_7_opt"))
      )
    )
    (IterPr
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "var_3")))
      List
      (iterexp "var_3" (VarE "var_3_lst"))
    )
    (IterPr
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "var_4")))
      List
      (iterexp "var_4" (VarE "var_4_lst"))
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
    "mk_Limits_ok"
    (ExpP "v_n" (VarT "n"))
    (ExpP "m_opt" (IterT (VarT "m") Opt))
    (ExpP "k" nat)
    (Infix (Seq) |- (Infix Arg : Arg))
    (TupE
      (CaseE
        (Seq (Atom mk_limits) Arg Arg)
        (TupE
          (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
          (IterE
            (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
            Opt
            (iterexp "v_m" (VarE "m_opt"))
          )
        )
      )
      (VarE "k")
    )
    (IfPr (CmpE LeOp nat (VarE "v_n") (VarE "k")))
    (IterPr
      (IfPr
        (BinE
          AndOp
          bool
          (CmpE LeOp nat (VarE "v_n") (VarE "v_m"))
          (CmpE LeOp nat (VarE "v_m") (VarE "k"))
        )
      )
      Opt
      (iterexp "v_m" (VarE "m_opt"))
    )
    (RulePr
      "wf_limits"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_limits) Arg Arg)
          (TupE
            (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
            (IterE
              (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
              Opt
              (iterexp "v_m" (VarE "m_opt"))
            )
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
    "mk_Functype_ok"
    (ExpP "t_1_lst" (IterT (VarT "valtype") List))
    (ExpP "t_2_opt" (IterT (VarT "valtype") Opt))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (CaseE
      (Seq (Atom mk_functype) Arg Arg)
      (TupE (VarE "t_1_lst") (LiftE (VarE "t_2_opt")))
    )
  )
)
(HintD (RelH "Functype_ok" (hint "show" "\"K-func\"")))
(RelD
  "Globaltype_ok"
  (Infix (Seq) |- (Infix Arg : (Atom OK)))
  (VarT "globaltype")
  (RuleD
    "mk_Globaltype_ok"
    (ExpP "t" (VarT "valtype"))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (CaseE
      (Seq (Atom mk_globaltype) Arg Arg)
      (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "t"))
    )
  )
)
(HintD (RelH "Globaltype_ok" (hint "show" "\"K-global\"")))
(RelD
  "Tabletype_ok"
  (Infix (Seq) |- (Infix Arg : (Atom OK)))
  (VarT "tabletype")
  (RuleD
    "mk_Tabletype_ok"
    (ExpP "v_limits" (VarT "limits"))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (VarE "v_limits")
    (RulePr
      "Limits_ok"
      (Infix (Seq) |- (Infix Arg : Arg))
      (TupE
        (VarE "v_limits")
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
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "v_limits")))
  )
)
(HintD (RelH "Tabletype_ok" (hint "show" "\"K-table\"")))
(RelD
  "Memtype_ok"
  (Infix (Seq) |- (Infix Arg : (Atom OK)))
  (VarT "memtype")
  (RuleD
    "mk_Memtype_ok"
    (ExpP "v_limits" (VarT "limits"))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (VarE "v_limits")
    (RulePr
      "Limits_ok"
      (Infix (Seq) |- (Infix Arg : Arg))
      (TupE (VarE "v_limits") (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 16))))
    )
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "v_limits")))
  )
)
(HintD (RelH "Memtype_ok" (hint "show" "\"K-mem\"")))
(RelD
  "Externtype_ok"
  (Infix (Seq) |- (Infix Arg : (Atom OK)))
  (VarT "externtype")
  (RuleD
    "func"
    (ExpP "v_functype" (VarT "functype"))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "v_functype")))
    (RulePr
      "Functype_ok"
      (Infix (Seq) |- (Infix Arg : (Atom OK)))
      (VarE "v_functype")
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "v_functype"))))
    )
  )
  (RuleD
    "global"
    (ExpP "v_globaltype" (VarT "globaltype"))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "v_globaltype")))
    (RulePr
      "Globaltype_ok"
      (Infix (Seq) |- (Infix Arg : (Atom OK)))
      (VarE "v_globaltype")
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "v_globaltype"))))
    )
  )
  (RuleD
    "table"
    (ExpP "v_tabletype" (VarT "tabletype"))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "v_tabletype")))
    (RulePr
      "Tabletype_ok"
      (Infix (Seq) |- (Infix Arg : (Atom OK)))
      (VarE "v_tabletype")
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "v_tabletype"))))
    )
  )
  (RuleD
    "mem"
    (ExpP "v_memtype" (VarT "memtype"))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "v_memtype")))
    (RulePr
      "Memtype_ok"
      (Infix (Seq) |- (Infix Arg : (Atom OK)))
      (VarE "v_memtype")
    )
    (RulePr
      "wf_externtype"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "v_memtype"))))
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
    (ExpP "m_2_opt" (IterT (VarT "m") Opt))
    (Infix (Seq) |- (Infix Arg <: Arg))
    (TupE
      (CaseE
        (Seq (Atom mk_limits) Arg Arg)
        (TupE
          (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "n_1")))
          (OptE (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "m_1"))))
        )
      )
      (CaseE
        (Seq (Atom mk_limits) Arg Arg)
        (TupE
          (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "n_2")))
          (IterE
            (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "m_2")))
            Opt
            (iterexp "m_2" (VarE "m_2_opt"))
          )
        )
      )
    )
    (IfPr (CmpE GeOp nat (VarE "n_1") (VarE "n_2")))
    (IterPr
      (IfPr (CmpE LeOp nat (VarE "m_1") (VarE "m_2")))
      Opt
      (iterexp "m_2" (VarE "m_2_opt"))
    )
    (RulePr
      "wf_limits"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_limits) Arg Arg)
          (TupE
            (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "n_1")))
            (OptE (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "m_1"))))
          )
        )
      )
    )
    (RulePr
      "wf_limits"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_limits) Arg Arg)
          (TupE
            (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "n_2")))
            (IterE
              (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "m_2")))
              Opt
              (iterexp "m_2" (VarE "m_2_opt"))
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
        (Seq (Atom mk_limits) Arg Arg)
        (TupE (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "n_1"))) (OptE))
      )
      (CaseE
        (Seq (Atom mk_limits) Arg Arg)
        (TupE (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "n_2"))) (OptE))
      )
    )
    (IfPr (CmpE GeOp nat (VarE "n_1") (VarE "n_2")))
    (RulePr
      "wf_limits"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_limits) Arg Arg)
          (TupE (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "n_1"))) (OptE))
        )
      )
    )
    (RulePr
      "wf_limits"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_limits) Arg Arg)
          (TupE (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "n_2"))) (OptE))
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
    "mk_Functype_sub"
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
    "mk_Globaltype_sub"
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
    "mk_Tabletype_sub"
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
    "mk_Memtype_sub"
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
        (CaseE (Seq (Atom mk_functype) Arg Arg) (TupE (ListE) (ListE)))
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_instr" (Seq Arg) (TupE (CaseE (Atom NOP) (TupE))))
    )
    (RuleD
      "unreachable"
      (ExpP "C" (VarT "context"))
      (ExpP "t_1_lst" (IterT (VarT "valtype") List))
      (ExpP "t_2_lst" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom UNREACHABLE) (TupE))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
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
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (ListE (VarE "t")) (ListE))
        )
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
          (Seq (Atom mk_functype) Arg Arg)
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
      (ExpP "t_opt" (IterT (VarT "valtype") Opt))
      (ExpP "instr_lst" (IterT (VarT "instr") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom BLOCK) Arg Arg)
          (TupE (VarE "t_opt") (VarE "instr_lst"))
        )
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (ListE) (LiftE (VarE "t_opt")))
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
              (expfield (Atom LABELS) (ListE (VarE "t_opt")))
              (expfield (Atom RETURN) (OptE))
            )
            (VarE "C")
          )
          (VarE "instr_lst")
          (CaseE
            (Seq (Atom mk_functype) Arg Arg)
            (TupE (ListE) (LiftE (VarE "t_opt")))
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
            (TupE (VarE "t_opt") (VarE "instr_lst"))
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
            (expfield (Atom LABELS) (ListE (VarE "t_opt")))
            (expfield (Atom RETURN) (OptE))
          )
        )
      )
    )
    (RuleD
      "loop"
      (ExpP "C" (VarT "context"))
      (ExpP "t_opt" (IterT (VarT "valtype") Opt))
      (ExpP "instr_lst" (IterT (VarT "instr") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom LOOP) Arg Arg)
          (TupE (VarE "t_opt") (VarE "instr_lst"))
        )
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (ListE) (LiftE (VarE "t_opt")))
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
          (VarE "instr_lst")
          (CaseE (Seq (Atom mk_functype) Arg Arg) (TupE (ListE) (ListE)))
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom LOOP) Arg Arg)
            (TupE (VarE "t_opt") (VarE "instr_lst"))
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
      (ExpP "t_opt" (IterT (VarT "valtype") Opt))
      (ExpP "instr_1_lst" (IterT (VarT "instr") List))
      (ExpP "instr_2_lst" (IterT (VarT "instr") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupE (VarE "t_opt") (VarE "instr_1_lst") (VarE "instr_2_lst"))
        )
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (ListE (CaseE (Atom I32) (TupE))) (LiftE (VarE "t_opt")))
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
              (expfield (Atom LABELS) (ListE (VarE "t_opt")))
              (expfield (Atom RETURN) (OptE))
            )
            (VarE "C")
          )
          (VarE "instr_1_lst")
          (CaseE
            (Seq (Atom mk_functype) Arg Arg)
            (TupE (ListE) (LiftE (VarE "t_opt")))
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
              (expfield (Atom LABELS) (ListE (VarE "t_opt")))
              (expfield (Atom RETURN) (OptE))
            )
            (VarE "C")
          )
          (VarE "instr_2_lst")
          (CaseE
            (Seq (Atom mk_functype) Arg Arg)
            (TupE (ListE) (LiftE (VarE "t_opt")))
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
            (TupE (VarE "t_opt") (VarE "instr_1_lst") (VarE "instr_2_lst"))
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
            (expfield (Atom LABELS) (ListE (VarE "t_opt")))
            (expfield (Atom RETURN) (OptE))
          )
        )
      )
    )
    (RuleD
      "br"
      (ExpP "C" (VarT "context"))
      (ExpP "l" (VarT "labelidx"))
      (ExpP "t_1_lst" (IterT (VarT "valtype") List))
      (ExpP "t_opt" (IterT (VarT "valtype") Opt))
      (ExpP "t_2_lst" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom BR) Arg) (TupE (VarE "l")))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (CatE (VarE "t_1_lst") (LiftE (VarE "t_opt"))) (VarE "t_2_lst"))
        )
      )
      (IfPr
        (CmpE
          LtOp
          nat
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "l"))) 0)
          (LenE (DotE (VarE "C") (Atom LABELS)))
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
          (VarE "t_opt")
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
      (ExpP "t_opt" (IterT (VarT "valtype") Opt))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom BR_IF) Arg) (TupE (VarE "l")))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE
            (CatE (LiftE (VarE "t_opt")) (ListE (CaseE (Atom I32) (TupE))))
            (LiftE (VarE "t_opt"))
          )
        )
      )
      (IfPr
        (CmpE
          LtOp
          nat
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "l"))) 0)
          (LenE (DotE (VarE "C") (Atom LABELS)))
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
          (VarE "t_opt")
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
      (ExpP "l_lst" (IterT (VarT "labelidx") List))
      (ExpP "l'" (VarT "labelidx"))
      (ExpP "t_1_lst" (IterT (VarT "valtype") List))
      (ExpP "t_opt" (IterT (VarT "valtype") Opt))
      (ExpP "t_2_lst" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom BR_TABLE) Arg Arg) (TupE (VarE "l_lst") (VarE "l'")))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE
            (CatE
              (VarE "t_1_lst")
              (CatE (LiftE (VarE "t_opt")) (ListE (CaseE (Atom I32) (TupE))))
            )
            (VarE "t_2_lst")
          )
        )
      )
      (IfPr
        (CmpE
          LtOp
          nat
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "l'"))) 0)
          (LenE (DotE (VarE "C") (Atom LABELS)))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (VarE "t_opt")
          (IdxE
            (DotE (VarE "C") (Atom LABELS))
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "l'"))) 0)
          )
        )
      )
      (IterPr
        (IfPr
          (CmpE
            LtOp
            nat
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "l"))) 0)
            (LenE (DotE (VarE "C") (Atom LABELS)))
          )
        )
        List
        (iterexp "l" (VarE "l_lst"))
      )
      (IterPr
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "t_opt")
            (IdxE
              (DotE (VarE "C") (Atom LABELS))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "l"))) 0)
            )
          )
        )
        List
        (iterexp "l" (VarE "l_lst"))
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom BR_TABLE) Arg Arg)
            (TupE (VarE "l_lst") (VarE "l'"))
          )
        )
      )
    )
    (RuleD
      "call"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t_1_lst" (IterT (VarT "valtype") List))
      (ExpP "t_2_opt" (IterT (VarT "valtype") Opt))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "x")))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (VarE "t_1_lst") (LiftE (VarE "t_2_opt")))
        )
      )
      (IfPr
        (CmpE
          LtOp
          nat
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
          (LenE (DotE (VarE "C") (Atom FUNCS)))
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
            (Seq (Atom mk_functype) Arg Arg)
            (TupE (VarE "t_1_lst") (LiftE (VarE "t_2_opt")))
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
      (ExpP "t_1_lst" (IterT (VarT "valtype") List))
      (ExpP "t_2_opt" (IterT (VarT "valtype") Opt))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "x")))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE
            (CatE (VarE "t_1_lst") (ListE (CaseE (Atom I32) (TupE))))
            (LiftE (VarE "t_2_opt"))
          )
        )
      )
      (IfPr
        (CmpE
          LtOp
          nat
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
          (LenE (DotE (VarE "C") (Atom TYPES)))
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
            (Seq (Atom mk_functype) Arg Arg)
            (TupE (VarE "t_1_lst") (LiftE (VarE "t_2_opt")))
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
      (ExpP "t_1_lst" (IterT (VarT "valtype") List))
      (ExpP "t_opt" (IterT (VarT "valtype") Opt))
      (ExpP "t_2_lst" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom RETURN) (TupE))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (CatE (VarE "t_1_lst") (LiftE (VarE "t_opt"))) (VarE "t_2_lst"))
        )
      )
      (IfPr
        (CmpE EqOp bool (DotE (VarE "C") (Atom RETURN)) (OptE (VarE "t_opt")))
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
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (ListE) (ListE (VarE "t")))
        )
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
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (ListE (VarE "t")) (ListE (VarE "t")))
        )
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
          (Seq (Atom mk_functype) Arg Arg)
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
          (Seq (Atom mk_functype) Arg Arg)
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
          (Seq (Atom mk_functype) Arg Arg)
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
      "cvtop_reinterpret"
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
          (Seq (Atom mk_functype) Arg Arg)
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
      "cvtop_convert"
      (ExpP "C" (VarT "context"))
      (ExpP "nt_1" (VarT "valtype"))
      (ExpP "nt_2" (VarT "valtype"))
      (ExpP "v_cvtop" (VarT "cvtop"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupE (VarE "nt_1") (VarE "nt_2") (VarE "v_cvtop"))
        )
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
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
            (TupE (VarE "nt_1") (VarE "nt_2") (VarE "v_cvtop"))
          )
        )
      )
    )
    (RuleD
      "local_get"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t" (VarT "valtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom LOCAL_GET) Arg) (TupE (VarE "x")))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (ListE) (ListE (VarE "t")))
        )
      )
      (IfPr
        (CmpE
          LtOp
          nat
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
          (LenE (DotE (VarE "C") (Atom LOCALS)))
        )
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
        (TupE (CaseE (Seq (Atom LOCAL_GET) Arg) (TupE (VarE "x"))))
      )
    )
    (RuleD
      "local_set"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t" (VarT "valtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom LOCAL_SET) Arg) (TupE (VarE "x")))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (ListE (VarE "t")) (ListE))
        )
      )
      (IfPr
        (CmpE
          LtOp
          nat
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
          (LenE (DotE (VarE "C") (Atom LOCALS)))
        )
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
        (TupE (CaseE (Seq (Atom LOCAL_SET) Arg) (TupE (VarE "x"))))
      )
    )
    (RuleD
      "local_tee"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t" (VarT "valtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom LOCAL_TEE) Arg) (TupE (VarE "x")))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (ListE (VarE "t")) (ListE (VarE "t")))
        )
      )
      (IfPr
        (CmpE
          LtOp
          nat
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
          (LenE (DotE (VarE "C") (Atom LOCALS)))
        )
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
        (TupE (CaseE (Seq (Atom LOCAL_TEE) Arg) (TupE (VarE "x"))))
      )
    )
    (RuleD
      "global_get"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "v_mut" (VarT "mut"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom GLOBAL_GET) Arg) (TupE (VarE "x")))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (ListE) (ListE (VarE "t")))
        )
      )
      (IfPr
        (CmpE
          LtOp
          nat
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
          (LenE (DotE (VarE "C") (Atom GLOBALS)))
        )
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
            (Seq (Atom mk_globaltype) Arg Arg)
            (TupE (VarE "v_mut") (VarE "t"))
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom GLOBAL_GET) Arg) (TupE (VarE "x"))))
      )
    )
    (RuleD
      "global_set"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t" (VarT "valtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom GLOBAL_SET) Arg) (TupE (VarE "x")))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (ListE (VarE "t")) (ListE))
        )
      )
      (IfPr
        (CmpE
          LtOp
          nat
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
          (LenE (DotE (VarE "C") (Atom GLOBALS)))
        )
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
            (Seq (Atom mk_globaltype) Arg Arg)
            (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "t"))
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr
        "wf_instr"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom GLOBAL_SET) Arg) (TupE (VarE "x"))))
      )
    )
    (RuleD
      "memory_size"
      (ExpP "C" (VarT "context"))
      (ExpP "mt" (VarT "memtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom MEMORY_SIZE) (TupE))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (ListE) (ListE (CaseE (Atom I32) (TupE))))
        )
      )
      (IfPr (CmpE LtOp nat (NumE (Nat 0)) (LenE (DotE (VarE "C") (Atom MEMS)))))
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
      (RulePr "wf_instr" (Seq Arg) (TupE (CaseE (Atom MEMORY_SIZE) (TupE))))
    )
    (RuleD
      "memory_grow"
      (ExpP "C" (VarT "context"))
      (ExpP "mt" (VarT "memtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom MEMORY_GROW) (TupE))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE
            (ListE (CaseE (Atom I32) (TupE)))
            (ListE (CaseE (Atom I32) (TupE)))
          )
        )
      )
      (IfPr (CmpE LtOp nat (NumE (Nat 0)) (LenE (DotE (VarE "C") (Atom MEMS)))))
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
      (RulePr "wf_instr" (Seq Arg) (TupE (CaseE (Atom MEMORY_GROW) (TupE))))
    )
    (RuleD
      "load_val"
      (ExpP "C" (VarT "context"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "v_memarg" (VarT "memarg"))
      (ExpP "mt" (VarT "memtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom LOAD) Arg Arg Arg)
          (TupE (VarE "t") (OptE) (VarE "v_memarg"))
        )
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (ListE (CaseE (Atom I32) (TupE))) (ListE (VarE "t")))
        )
      )
      (IfPr (CmpE LtOp nat (NumE (Nat 0)) (LenE (DotE (VarE "C") (Atom MEMS)))))
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
                (CallE "proj_uN_0" (ExpA (DotE (VarE "v_memarg") (Atom ALIGN))))
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
            (TupE (VarE "t") (OptE) (VarE "v_memarg"))
          )
        )
      )
    )
    (RuleD
      "load_pack"
      (ExpP "C" (VarT "context"))
      (ExpP "v_Inn" (VarT "Inn"))
      (ExpP "v_M" (VarT "M"))
      (ExpP "v_sx" (VarT "sx"))
      (ExpP "v_memarg" (VarT "memarg"))
      (ExpP "mt" (VarT "memtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom LOAD) Arg Arg Arg)
          (TupE
            (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
            (OptE
              (CaseE
                (Seq (Atom mk_loadop__0) Arg Arg)
                (TupE
                  (VarE "v_Inn")
                  (CaseE
                    (Seq (Atom mk_loadop_Inn) Arg Arg)
                    (TupE
                      (CaseE (Seq (Atom mk_sz) Arg) (TupE (VarE "v_M")))
                      (VarE "v_sx")
                    )
                  )
                )
              )
            )
            (VarE "v_memarg")
          )
        )
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE
            (ListE (CaseE (Atom I32) (TupE)))
            (ListE (CallE "valtype_Inn" (ExpA (VarE "v_Inn"))))
          )
        )
      )
      (IfPr (CmpE LtOp nat (NumE (Nat 0)) (LenE (DotE (VarE "C") (Atom MEMS)))))
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
                (CallE "proj_uN_0" (ExpA (DotE (VarE "v_memarg") (Atom ALIGN))))
                0
              )
            )
          )
          (BinE
            DivOp
            rat
            (CvtE nat rat (VarE "v_M"))
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
              (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
              (OptE
                (CaseE
                  (Seq (Atom mk_loadop__0) Arg Arg)
                  (TupE
                    (VarE "v_Inn")
                    (CaseE
                      (Seq (Atom mk_loadop_Inn) Arg Arg)
                      (TupE
                        (CaseE (Seq (Atom mk_sz) Arg) (TupE (VarE "v_M")))
                        (VarE "v_sx")
                      )
                    )
                  )
                )
              )
              (VarE "v_memarg")
            )
          )
        )
      )
    )
    (RuleD
      "store_val"
      (ExpP "C" (VarT "context"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "v_memarg" (VarT "memarg"))
      (ExpP "mt" (VarT "memtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom STORE) Arg Arg Arg)
          (TupE (VarE "t") (OptE) (VarE "v_memarg"))
        )
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (ListE (CaseE (Atom I32) (TupE)) (VarE "t")) (ListE))
        )
      )
      (IfPr (CmpE LtOp nat (NumE (Nat 0)) (LenE (DotE (VarE "C") (Atom MEMS)))))
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
                (CallE "proj_uN_0" (ExpA (DotE (VarE "v_memarg") (Atom ALIGN))))
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
            (TupE (VarE "t") (OptE) (VarE "v_memarg"))
          )
        )
      )
    )
    (RuleD
      "store_pack"
      (ExpP "C" (VarT "context"))
      (ExpP "v_Inn" (VarT "Inn"))
      (ExpP "v_M" (VarT "M"))
      (ExpP "v_memarg" (VarT "memarg"))
      (ExpP "mt" (VarT "memtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom STORE) Arg Arg Arg)
          (TupE
            (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
            (OptE (CaseE (Seq (Atom mk_sz) Arg) (TupE (VarE "v_M"))))
            (VarE "v_memarg")
          )
        )
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE
            (ListE
              (CaseE (Atom I32) (TupE))
              (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
            )
            (ListE)
          )
        )
      )
      (IfPr (CmpE LtOp nat (NumE (Nat 0)) (LenE (DotE (VarE "C") (Atom MEMS)))))
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
                (CallE "proj_uN_0" (ExpA (DotE (VarE "v_memarg") (Atom ALIGN))))
                0
              )
            )
          )
          (BinE
            DivOp
            rat
            (CvtE nat rat (VarE "v_M"))
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
              (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
              (OptE (CaseE (Seq (Atom mk_sz) Arg) (TupE (VarE "v_M"))))
              (VarE "v_memarg")
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
        (CaseE (Seq (Atom mk_functype) Arg Arg) (TupE (ListE) (ListE)))
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    )
    (RuleD
      "instr"
      (ExpP "C" (VarT "context"))
      (ExpP "v_instr" (VarT "instr"))
      (ExpP "t_1_lst" (IterT (VarT "valtype") List))
      (ExpP "t_2_lst" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (ListE (VarE "v_instr"))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
        )
      )
      (RulePr
        "Instr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (VarE "v_instr")
          (CaseE
            (Seq (Atom mk_functype) Arg Arg)
            (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_instr")))
    )
    (RuleD
      "seq"
      (ExpP "C" (VarT "context"))
      (ExpP "instr_1_lst" (IterT (VarT "instr") List))
      (ExpP "instr_2_lst" (IterT (VarT "instr") List))
      (ExpP "t_1_lst" (IterT (VarT "valtype") List))
      (ExpP "t_3_lst" (IterT (VarT "valtype") List))
      (ExpP "t_2_lst" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CatE (VarE "instr_1_lst") (VarE "instr_2_lst"))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (VarE "t_1_lst") (VarE "t_3_lst"))
        )
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (VarE "instr_1_lst")
          (CaseE
            (Seq (Atom mk_functype) Arg Arg)
            (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
          )
        )
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (VarE "instr_2_lst")
          (CaseE
            (Seq (Atom mk_functype) Arg Arg)
            (TupE (VarE "t_2_lst") (VarE "t_3_lst"))
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr_1")))
        List
        (iterexp "instr_1" (VarE "instr_1_lst"))
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr_2")))
        List
        (iterexp "instr_2" (VarE "instr_2_lst"))
      )
    )
    (RuleD
      "frame"
      (ExpP "C" (VarT "context"))
      (ExpP "instr_lst" (IterT (VarT "instr") List))
      (ExpP "t_lst" (IterT (VarT "valtype") List))
      (ExpP "t_1_lst" (IterT (VarT "valtype") List))
      (ExpP "t_2_lst" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (VarE "instr_lst")
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE
            (CatE (VarE "t_lst") (VarE "t_1_lst"))
            (CatE (VarE "t_lst") (VarE "t_2_lst"))
          )
        )
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (VarE "instr_lst")
          (CaseE
            (Seq (Atom mk_functype) Arg Arg)
            (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
          )
        )
      )
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_instr")))
        List
        (iterexp "v_instr" (VarE "instr_lst"))
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
    "mk_Expr_ok"
    (ExpP "C" (VarT "context"))
    (ExpP "instr_lst" (IterT (VarT "instr") List))
    (ExpP "t_opt" (IterT (VarT "valtype") Opt))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE (VarE "C") (VarE "instr_lst") (VarE "t_opt"))
    (RulePr
      "Instrs_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (VarE "instr_lst")
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (ListE) (LiftE (VarE "t_opt")))
        )
      )
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_instr")))
      List
      (iterexp "v_instr" (VarE "instr_lst"))
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
    "global_get"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE (VarE "C") (CaseE (Seq (Atom GLOBAL_GET) Arg) (TupE (VarE "x"))))
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (DotE (VarE "C") (Atom GLOBALS)))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE
          (DotE (VarE "C") (Atom GLOBALS))
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        )
        (CaseE (Seq (Atom mk_globaltype) Arg Arg) (TupE (OptE) (VarE "t")))
      )
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_instr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL_GET) Arg) (TupE (VarE "x"))))
    )
  )
)
(HintD (RelH "Instr_const" (hint "show" "\"C-instr\"")))
(RelD
  "Expr_const"
  (Infix Arg |- (Seq Arg (Atom CONST)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "expr")))
  (RuleD
    "mk_Expr_const"
    (ExpP "C" (VarT "context"))
    (ExpP "instr_lst" (IterT (VarT "instr") List))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE (VarE "C") (VarE "instr_lst"))
    (IterPr
      (RulePr
        "Instr_const"
        (Infix Arg |- (Seq Arg (Atom CONST)))
        (TupE (VarE "C") (VarE "v_instr"))
      )
      List
      (iterexp "v_instr" (VarE "instr_lst"))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_instr")))
      List
      (iterexp "v_instr" (VarE "instr_lst"))
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
    "mk_Expr_ok_const"
    (ExpP "C" (VarT "context"))
    (ExpP "v_expr" (VarT "expr"))
    (ExpP "t_opt" (IterT (VarT "valtype") Opt))
    (Infix Arg |- (Infix Arg : (Seq Arg (Atom CONST))))
    (TupE (VarE "C") (VarE "v_expr") (VarE "t_opt"))
    (RulePr
      "Expr_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "C") (VarE "v_expr") (VarE "t_opt"))
    )
    (RulePr
      "Expr_const"
      (Infix Arg |- (Seq Arg (Atom CONST)))
      (TupE (VarE "C") (VarE "v_expr"))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_expr")))
      List
      (iterexp "v_expr" (VarE "v_expr"))
    )
  )
)
(HintD (RelH "Expr_ok_const" (hint "show" "\"TC-expr\"")))
(RelD
  "Type_ok"
  (Infix (Seq) |- (Infix Arg : Arg))
  (TupT (typbind "_" (VarT "type")) (typbind "_" (VarT "functype")))
  (RuleD
    "mk_Type_ok"
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
    "mk_Func_ok"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "t_lst" (IterT (VarT "valtype") List))
    (ExpP "v_expr" (VarT "expr"))
    (ExpP "t_1_lst" (IterT (VarT "valtype") List))
    (ExpP "t_2_opt" (IterT (VarT "valtype") Opt))
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
            (iterexp "t" (VarE "t_lst"))
          )
          (VarE "v_expr")
        )
      )
      (CaseE
        (Seq (Atom mk_functype) Arg Arg)
        (TupE (VarE "t_1_lst") (LiftE (VarE "t_2_opt")))
      )
    )
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (DotE (VarE "C") (Atom TYPES)))
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
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (VarE "t_1_lst") (LiftE (VarE "t_2_opt")))
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
            (expfield (Atom LOCALS) (CatE (VarE "t_1_lst") (VarE "t_lst")))
            (expfield (Atom LABELS) (ListE (VarE "t_2_opt")))
            (expfield (Atom RETURN) (OptE (VarE "t_2_opt")))
          )
        )
        (VarE "v_expr")
        (VarE "t_2_opt")
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
              (iterexp "t" (VarE "t_lst"))
            )
            (VarE "v_expr")
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
          (expfield (Atom LOCALS) (CatE (VarE "t_1_lst") (VarE "t_lst")))
          (expfield (Atom LABELS) (ListE (VarE "t_2_opt")))
          (expfield (Atom RETURN) (OptE (VarE "t_2_opt")))
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
    "mk_Global_ok"
    (ExpP "C" (VarT "context"))
    (ExpP "gt" (VarT "globaltype"))
    (ExpP "v_expr" (VarT "expr"))
    (ExpP "v_mut" (VarT "mut"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom GLOBAL) Arg Arg) (TupE (VarE "gt") (VarE "v_expr")))
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
        (CaseE
          (Seq (Atom mk_globaltype) Arg Arg)
          (TupE (VarE "v_mut") (VarE "t"))
        )
      )
    )
    (RulePr
      "Expr_ok_const"
      (Infix Arg |- (Infix Arg : (Seq Arg (Atom CONST))))
      (TupE (VarE "C") (VarE "v_expr") (OptE (VarE "t")))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_global"
      (Seq Arg)
      (TupE
        (CaseE (Seq (Atom GLOBAL) Arg Arg) (TupE (VarE "gt") (VarE "v_expr")))
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
    "mk_Table_ok"
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
    "mk_Mem_ok"
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
    "mk_Elem_ok"
    (ExpP "C" (VarT "context"))
    (ExpP "v_expr" (VarT "expr"))
    (ExpP "x_lst" (IterT (VarT "idx") List))
    (ExpP "lim" (VarT "limits"))
    (ExpP "ft_lst" (IterT (VarT "functype") List))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom ELEM) Arg Arg) (TupE (VarE "v_expr") (VarE "x_lst")))
    )
    (IfPr (CmpE LtOp nat (NumE (Nat 0)) (LenE (DotE (VarE "C") (Atom TABLES)))))
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
      (TupE (VarE "C") (VarE "v_expr") (OptE (CaseE (Atom I32) (TupE))))
    )
    (IfPr (CmpE EqOp bool (LenE (VarE "ft_lst")) (LenE (VarE "x_lst"))))
    (IterPr
      (IfPr
        (CmpE
          LtOp
          nat
          (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
          (LenE (DotE (VarE "C") (Atom FUNCS)))
        )
      )
      List
      (iterexp "x" (VarE "x_lst"))
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
      (iterexp "ft" (VarE "ft_lst"))
      (iterexp "x" (VarE "x_lst"))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "lim")))
    (RulePr
      "wf_elem"
      (Seq Arg)
      (TupE
        (CaseE (Seq (Atom ELEM) Arg Arg) (TupE (VarE "v_expr") (VarE "x_lst")))
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
    "mk_Data_ok"
    (ExpP "C" (VarT "context"))
    (ExpP "v_expr" (VarT "expr"))
    (ExpP "b_lst" (IterT (VarT "byte") List))
    (ExpP "lim" (VarT "limits"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom DATA) Arg Arg) (TupE (VarE "v_expr") (VarE "b_lst")))
    )
    (IfPr (CmpE LtOp nat (NumE (Nat 0)) (LenE (DotE (VarE "C") (Atom MEMS)))))
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
      (TupE (VarE "C") (VarE "v_expr") (OptE (CaseE (Atom I32) (TupE))))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "lim")))
    (RulePr
      "wf_data"
      (Seq Arg)
      (TupE
        (CaseE (Seq (Atom DATA) Arg Arg) (TupE (VarE "v_expr") (VarE "b_lst")))
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
    "mk_Start_ok"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE (VarE "C") (CaseE (Seq (Atom START) Arg) (TupE (VarE "x"))))
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (DotE (VarE "C") (Atom FUNCS)))
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
        (CaseE (Seq (Atom mk_functype) Arg Arg) (TupE (ListE) (ListE)))
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
    "mk_Import_ok"
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
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (DotE (VarE "C") (Atom FUNCS)))
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
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (DotE (VarE "C") (Atom GLOBALS)))
      )
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
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (DotE (VarE "C") (Atom TABLES)))
      )
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
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (DotE (VarE "C") (Atom MEMS)))
      )
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
    "mk_Export_ok"
    (ExpP "C" (VarT "context"))
    (ExpP "v_name" (VarT "name"))
    (ExpP "v_externidx" (VarT "externidx"))
    (ExpP "xt" (VarT "externtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Seq (Atom EXPORT) Arg Arg)
        (TupE (VarE "v_name") (VarE "v_externidx"))
      )
      (VarE "xt")
    )
    (RulePr
      "Externidx_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "C") (VarE "v_externidx") (VarE "xt"))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr "wf_externtype" (Seq Arg) (TupE (VarE "xt")))
    (RulePr
      "wf_export"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom EXPORT) Arg Arg)
          (TupE (VarE "v_name") (VarE "v_externidx"))
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
    "mk_Module_ok"
    (ExpP "type_lst" (IterT (VarT "type") List))
    (ExpP "import_lst" (IterT (VarT "import") List))
    (ExpP "func_lst" (IterT (VarT "func") List))
    (ExpP "global_lst" (IterT (VarT "global") List))
    (ExpP "table_lst" (IterT (VarT "table") List))
    (ExpP "mem_lst" (IterT (VarT "mem") List))
    (ExpP "elem_lst" (IterT (VarT "elem") List))
    (ExpP "data_lst" (IterT (VarT "data") List))
    (ExpP "start_opt" (IterT (VarT "start") Opt))
    (ExpP "export_lst" (IterT (VarT "export") List))
    (ExpP "ft'_lst" (IterT (VarT "functype") List))
    (ExpP "ixt_lst" (IterT (VarT "externtype") List))
    (ExpP "C'" (VarT "context"))
    (ExpP "gt_lst" (IterT (VarT "globaltype") List))
    (ExpP "C" (VarT "context"))
    (ExpP "ft_lst" (IterT (VarT "functype") List))
    (ExpP "tt_lst" (IterT (VarT "tabletype") List))
    (ExpP "mt_lst" (IterT (VarT "memtype") List))
    (ExpP "xt_lst" (IterT (VarT "externtype") List))
    (ExpP "ift_lst" (IterT (VarT "functype") List))
    (ExpP "igt_lst" (IterT (VarT "globaltype") List))
    (ExpP "itt_lst" (IterT (VarT "tabletype") List))
    (ExpP "imt_lst" (IterT (VarT "memtype") List))
    (ExpP "var_3" (IterT (VarT "memtype") List))
    (ExpP "var_2" (IterT (VarT "tabletype") List))
    (ExpP "var_1" (IterT (VarT "globaltype") List))
    (ExpP "var_0" (IterT (VarT "functype") List))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (CaseE
      (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
      (TupE
        (VarE "type_lst")
        (VarE "import_lst")
        (VarE "func_lst")
        (VarE "global_lst")
        (VarE "table_lst")
        (VarE "mem_lst")
        (VarE "elem_lst")
        (VarE "data_lst")
        (VarE "start_opt")
        (VarE "export_lst")
      )
    )
    (RulePr "fun_memsxt" (Seq Arg Arg) (TupE (VarE "ixt_lst") (VarE "var_3")))
    (RulePr "fun_tablesxt" (Seq Arg Arg) (TupE (VarE "ixt_lst") (VarE "var_2")))
    (RulePr
      "fun_globalsxt"
      (Seq Arg Arg)
      (TupE (VarE "ixt_lst") (VarE "var_1"))
    )
    (RulePr "fun_funcsxt" (Seq Arg Arg) (TupE (VarE "ixt_lst") (VarE "var_0")))
    (IfPr (CmpE EqOp bool (LenE (VarE "ft'_lst")) (LenE (VarE "type_lst"))))
    (IterPr
      (RulePr
        "Type_ok"
        (Infix (Seq) |- (Infix Arg : Arg))
        (TupE (VarE "v_type") (VarE "ft'"))
      )
      List
      (iterexp "ft'" (VarE "ft'_lst"))
      (iterexp "v_type" (VarE "type_lst"))
    )
    (IfPr (CmpE EqOp bool (LenE (VarE "import_lst")) (LenE (VarE "ixt_lst"))))
    (IterPr
      (RulePr
        "Import_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (StrE
            (expfield (Atom TYPES) (VarE "ft'_lst"))
            (expfield (Atom FUNCS) (ListE))
            (expfield (Atom GLOBALS) (ListE))
            (expfield (Atom TABLES) (ListE))
            (expfield (Atom MEMS) (ListE))
            (expfield (Atom LOCALS) (ListE))
            (expfield (Atom LABELS) (ListE))
            (expfield (Atom RETURN) (OptE))
          )
          (VarE "v_import")
          (VarE "ixt")
        )
      )
      List
      (iterexp "v_import" (VarE "import_lst"))
      (iterexp "ixt" (VarE "ixt_lst"))
    )
    (IfPr (CmpE EqOp bool (LenE (VarE "global_lst")) (LenE (VarE "gt_lst"))))
    (IterPr
      (RulePr
        "Global_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C'") (VarE "v_global") (VarE "gt"))
      )
      List
      (iterexp "v_global" (VarE "global_lst"))
      (iterexp "gt" (VarE "gt_lst"))
    )
    (IfPr (CmpE EqOp bool (LenE (VarE "ft_lst")) (LenE (VarE "func_lst"))))
    (IterPr
      (RulePr
        "Func_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C") (VarE "v_func") (VarE "ft"))
      )
      List
      (iterexp "ft" (VarE "ft_lst"))
      (iterexp "v_func" (VarE "func_lst"))
    )
    (IfPr (CmpE EqOp bool (LenE (VarE "table_lst")) (LenE (VarE "tt_lst"))))
    (IterPr
      (RulePr
        "Table_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C") (VarE "v_table") (VarE "tt"))
      )
      List
      (iterexp "v_table" (VarE "table_lst"))
      (iterexp "tt" (VarE "tt_lst"))
    )
    (IfPr (CmpE EqOp bool (LenE (VarE "mem_lst")) (LenE (VarE "mt_lst"))))
    (IterPr
      (RulePr
        "Mem_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C") (VarE "v_mem") (VarE "mt"))
      )
      List
      (iterexp "v_mem" (VarE "mem_lst"))
      (iterexp "mt" (VarE "mt_lst"))
    )
    (IterPr
      (RulePr
        "Elem_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "v_elem"))
      )
      List
      (iterexp "v_elem" (VarE "elem_lst"))
    )
    (IterPr
      (RulePr
        "Data_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "v_data"))
      )
      List
      (iterexp "v_data" (VarE "data_lst"))
    )
    (IterPr
      (RulePr
        "Start_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "v_start"))
      )
      Opt
      (iterexp "v_start" (VarE "start_opt"))
    )
    (IfPr (CmpE EqOp bool (LenE (VarE "export_lst")) (LenE (VarE "xt_lst"))))
    (IterPr
      (RulePr
        "Export_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C") (VarE "v_export") (VarE "xt"))
      )
      List
      (iterexp "v_export" (VarE "export_lst"))
      (iterexp "xt" (VarE "xt_lst"))
    )
    (IfPr (CmpE LeOp nat (LenE (VarE "tt_lst")) (NumE (Nat 1))))
    (IfPr (CmpE LeOp nat (LenE (VarE "mt_lst")) (NumE (Nat 1))))
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "C")
        (StrE
          (expfield (Atom TYPES) (VarE "ft'_lst"))
          (expfield (Atom FUNCS) (CatE (VarE "ift_lst") (VarE "ft_lst")))
          (expfield (Atom GLOBALS) (CatE (VarE "igt_lst") (VarE "gt_lst")))
          (expfield (Atom TABLES) (CatE (VarE "itt_lst") (VarE "tt_lst")))
          (expfield (Atom MEMS) (CatE (VarE "imt_lst") (VarE "mt_lst")))
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
          (expfield (Atom TYPES) (VarE "ft'_lst"))
          (expfield (Atom FUNCS) (CatE (VarE "ift_lst") (VarE "ft_lst")))
          (expfield (Atom GLOBALS) (VarE "igt_lst"))
          (expfield (Atom TABLES) (ListE))
          (expfield (Atom MEMS) (ListE))
          (expfield (Atom LOCALS) (ListE))
          (expfield (Atom LABELS) (ListE))
          (expfield (Atom RETURN) (OptE))
        )
      )
    )
    (IfPr (CmpE EqOp bool (VarE "ift_lst") (VarE "var_0")))
    (IfPr (CmpE EqOp bool (VarE "igt_lst") (VarE "var_1")))
    (IfPr (CmpE EqOp bool (VarE "itt_lst") (VarE "var_2")))
    (IfPr (CmpE EqOp bool (VarE "imt_lst") (VarE "var_3")))
    (IterPr
      (RulePr "wf_externtype" (Seq Arg) (TupE (VarE "ixt")))
      List
      (iterexp "ixt" (VarE "ixt_lst"))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C'")))
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (IterPr
      (RulePr "wf_externtype" (Seq Arg) (TupE (VarE "xt")))
      List
      (iterexp "xt" (VarE "xt_lst"))
    )
    (IterPr
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "iter")))
      List
      (iterexp "iter" (VarE "var_2"))
    )
    (IterPr
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "iter")))
      List
      (iterexp "iter" (VarE "var_3"))
    )
    (RulePr
      "wf_module"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
          (TupE
            (VarE "type_lst")
            (VarE "import_lst")
            (VarE "func_lst")
            (VarE "global_lst")
            (VarE "table_lst")
            (VarE "mem_lst")
            (VarE "elem_lst")
            (VarE "data_lst")
            (VarE "start_opt")
            (VarE "export_lst")
          )
        )
      )
    )
    (RulePr
      "wf_context"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom TYPES) (VarE "ft'_lst"))
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
          (expfield (Atom TYPES) (VarE "ft'_lst"))
          (expfield (Atom FUNCS) (CatE (VarE "ift_lst") (VarE "ft_lst")))
          (expfield (Atom GLOBALS) (CatE (VarE "igt_lst") (VarE "gt_lst")))
          (expfield (Atom TABLES) (CatE (VarE "itt_lst") (VarE "tt_lst")))
          (expfield (Atom MEMS) (CatE (VarE "imt_lst") (VarE "mt_lst")))
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
          (expfield (Atom TYPES) (VarE "ft'_lst"))
          (expfield (Atom FUNCS) (CatE (VarE "ift_lst") (VarE "ft_lst")))
          (expfield (Atom GLOBALS) (VarE "igt_lst"))
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
    (ExpP "v_val" (VarT "val"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CallE "admininstr_val" (ExpA (VarE "v_val")))
        (CaseE (Atom DROP) (TupE))
      )
      (ListE)
    )
    (RulePr "wf_val" (Seq Arg) (TupE (VarE "v_val")))
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom DROP) (TupE))))
  )
  (RuleD
    "select_true"
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
    (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "c"))) (OptE)))
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
    "select_false"
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
    (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "c"))) (OptE)))
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
    "if_true"
    (ExpP "c" (VarT "val_"))
    (ExpP "t_opt" (IterT (VarT "valtype") Opt))
    (ExpP "instr_1_lst" (IterT (VarT "instr") List))
    (ExpP "instr_2_lst" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
        (CaseE
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupE (VarE "t_opt") (VarE "instr_1_lst") (VarE "instr_2_lst"))
        )
      )
      (ListE
        (CaseE
          (Seq (Atom BLOCK) Arg Arg)
          (TupE (VarE "t_opt") (VarE "instr_1_lst"))
        )
      )
    )
    (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "c"))) (OptE)))
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
          (TupE (VarE "t_opt") (VarE "instr_1_lst") (VarE "instr_2_lst"))
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BLOCK) Arg Arg)
          (TupE (VarE "t_opt") (VarE "instr_1_lst"))
        )
      )
    )
  )
  (RuleD
    "if_false"
    (ExpP "c" (VarT "val_"))
    (ExpP "t_opt" (IterT (VarT "valtype") Opt))
    (ExpP "instr_1_lst" (IterT (VarT "instr") List))
    (ExpP "instr_2_lst" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
        (CaseE
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupE (VarE "t_opt") (VarE "instr_1_lst") (VarE "instr_2_lst"))
        )
      )
      (ListE
        (CaseE
          (Seq (Atom BLOCK) Arg Arg)
          (TupE (VarE "t_opt") (VarE "instr_2_lst"))
        )
      )
    )
    (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "c"))) (OptE)))
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
          (TupE (VarE "t_opt") (VarE "instr_1_lst") (VarE "instr_2_lst"))
        )
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BLOCK) Arg Arg)
          (TupE (VarE "t_opt") (VarE "instr_2_lst"))
        )
      )
    )
  )
  (RuleD
    "label_vals"
    (ExpP "v_n" (VarT "n"))
    (ExpP "instr_lst" (IterT (VarT "instr") List))
    (ExpP "val_lst" (IterT (VarT "val") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "v_n")
            (VarE "instr_lst")
            (IterE
              (CallE "admininstr_val" (ExpA (VarE "v_val")))
              List
              (iterexp "v_val" (VarE "val_lst"))
            )
          )
        )
      )
      (IterE
        (CallE "admininstr_val" (ExpA (VarE "v_val")))
        List
        (iterexp "v_val" (VarE "val_lst"))
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "v_n")
            (VarE "instr_lst")
            (IterE
              (CallE "admininstr_val" (ExpA (VarE "v_val")))
              List
              (iterexp "v_val" (VarE "val_lst"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "br_zero"
    (ExpP "v_n" (VarT "n"))
    (ExpP "instr'_lst" (IterT (VarT "instr") List))
    (ExpP "val'_lst" (IterT (VarT "val") List))
    (ExpP "val_lst" (IterT (VarT "val") List))
    (ExpP "instr_lst" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "v_n")
            (VarE "instr'_lst")
            (CatE
              (CatE
                (CatE
                  (IterE
                    (CallE "admininstr_val" (ExpA (VarE "val'")))
                    List
                    (iterexp "val'" (VarE "val'_lst"))
                  )
                  (IterE
                    (CallE "admininstr_val" (ExpA (VarE "v_val")))
                    (ListN (VarE "v_n"))
                    (iterexp "v_val" (VarE "val_lst"))
                  )
                )
                (ListE
                  (CaseE
                    (Seq (Atom BR) Arg)
                    (TupE (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
                  )
                )
              )
              (IterE
                (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
                List
                (iterexp "v_instr" (VarE "instr_lst"))
              )
            )
          )
        )
      )
      (CatE
        (IterE
          (CallE "admininstr_val" (ExpA (VarE "v_val")))
          (ListN (VarE "v_n"))
          (iterexp "v_val" (VarE "val_lst"))
        )
        (IterE
          (CallE "admininstr_instr" (ExpA (VarE "instr'")))
          List
          (iterexp "instr'" (VarE "instr'_lst"))
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
            (VarE "v_n")
            (VarE "instr'_lst")
            (CatE
              (CatE
                (CatE
                  (IterE
                    (CallE "admininstr_val" (ExpA (VarE "val'")))
                    List
                    (iterexp "val'" (VarE "val'_lst"))
                  )
                  (IterE
                    (CallE "admininstr_val" (ExpA (VarE "v_val")))
                    (ListN (VarE "v_n"))
                    (iterexp "v_val" (VarE "val_lst"))
                  )
                )
                (ListE
                  (CaseE
                    (Seq (Atom BR) Arg)
                    (TupE (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
                  )
                )
              )
              (IterE
                (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
                List
                (iterexp "v_instr" (VarE "instr_lst"))
              )
            )
          )
        )
      )
    )
    (IfPr (CmpE EqOp bool (VarE "v_n") (LenE (VarE "val_lst"))))
  )
  (RuleD
    "br_succ"
    (ExpP "v_n" (VarT "n"))
    (ExpP "instr'_lst" (IterT (VarT "instr") List))
    (ExpP "val_lst" (IterT (VarT "val") List))
    (ExpP "l" (VarT "labelidx"))
    (ExpP "instr_lst" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "v_n")
            (VarE "instr'_lst")
            (CatE
              (CatE
                (IterE
                  (CallE "admininstr_val" (ExpA (VarE "v_val")))
                  List
                  (iterexp "v_val" (VarE "val_lst"))
                )
                (ListE
                  (CaseE
                    (Seq (Atom BR) Arg)
                    (TupE
                      (CaseE
                        (Seq (Atom mk_uN) Arg)
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
                (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
                List
                (iterexp "v_instr" (VarE "instr_lst"))
              )
            )
          )
        )
      )
      (CatE
        (IterE
          (CallE "admininstr_val" (ExpA (VarE "v_val")))
          List
          (iterexp "v_val" (VarE "val_lst"))
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
            (VarE "v_n")
            (VarE "instr'_lst")
            (CatE
              (CatE
                (IterE
                  (CallE "admininstr_val" (ExpA (VarE "v_val")))
                  List
                  (iterexp "v_val" (VarE "val_lst"))
                )
                (ListE
                  (CaseE
                    (Seq (Atom BR) Arg)
                    (TupE
                      (CaseE
                        (Seq (Atom mk_uN) Arg)
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
                (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
                List
                (iterexp "v_instr" (VarE "instr_lst"))
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
    "br_if_true"
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
    (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "c"))) (OptE)))
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
    "br_if_false"
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
    (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "c"))) (OptE)))
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
    "br_table_lt"
    (ExpP "i" (VarT "val_"))
    (ExpP "l_lst" (IterT (VarT "labelidx") List))
    (ExpP "l'" (VarT "labelidx"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
        )
        (CaseE (Seq (Atom BR_TABLE) Arg Arg) (TupE (VarE "l_lst") (VarE "l'")))
      )
      (ListE
        (CaseE
          (Seq (Atom BR) Arg)
          (TupE
            (IdxE
              (VarE "l_lst")
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
        (LenE (VarE "l_lst"))
      )
    )
    (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "i"))) (OptE)))
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
        (CaseE (Seq (Atom BR_TABLE) Arg Arg) (TupE (VarE "l_lst") (VarE "l'")))
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
              (VarE "l_lst")
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
    "br_table_ge"
    (ExpP "i" (VarT "val_"))
    (ExpP "l_lst" (IterT (VarT "labelidx") List))
    (ExpP "l'" (VarT "labelidx"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
        )
        (CaseE (Seq (Atom BR_TABLE) Arg Arg) (TupE (VarE "l_lst") (VarE "l'")))
      )
      (ListE (CaseE (Seq (Atom BR) Arg) (TupE (VarE "l'"))))
    )
    (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "i"))) (OptE)))
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
        (LenE (VarE "l_lst"))
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
        (CaseE (Seq (Atom BR_TABLE) Arg Arg) (TupE (VarE "l_lst") (VarE "l'")))
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BR) Arg) (TupE (VarE "l'"))))
    )
  )
  (RuleD
    "frame_vals"
    (ExpP "v_n" (VarT "n"))
    (ExpP "f" (VarT "frame"))
    (ExpP "val_lst" (IterT (VarT "val") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "v_n")
            (VarE "f")
            (IterE
              (CallE "admininstr_val" (ExpA (VarE "v_val")))
              (ListN (VarE "v_n"))
              (iterexp "v_val" (VarE "val_lst"))
            )
          )
        )
      )
      (IterE
        (CallE "admininstr_val" (ExpA (VarE "v_val")))
        (ListN (VarE "v_n"))
        (iterexp "v_val" (VarE "val_lst"))
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "v_n")
            (VarE "f")
            (IterE
              (CallE "admininstr_val" (ExpA (VarE "v_val")))
              (ListN (VarE "v_n"))
              (iterexp "v_val" (VarE "val_lst"))
            )
          )
        )
      )
    )
    (IfPr (CmpE EqOp bool (VarE "v_n") (LenE (VarE "val_lst"))))
  )
  (RuleD
    "return_frame"
    (ExpP "v_n" (VarT "n"))
    (ExpP "f" (VarT "frame"))
    (ExpP "val'_lst" (IterT (VarT "val") List))
    (ExpP "val_lst" (IterT (VarT "val") List))
    (ExpP "instr_lst" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "v_n")
            (VarE "f")
            (CatE
              (CatE
                (CatE
                  (IterE
                    (CallE "admininstr_val" (ExpA (VarE "val'")))
                    List
                    (iterexp "val'" (VarE "val'_lst"))
                  )
                  (IterE
                    (CallE "admininstr_val" (ExpA (VarE "v_val")))
                    (ListN (VarE "v_n"))
                    (iterexp "v_val" (VarE "val_lst"))
                  )
                )
                (ListE (CaseE (Atom RETURN) (TupE)))
              )
              (IterE
                (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
                List
                (iterexp "v_instr" (VarE "instr_lst"))
              )
            )
          )
        )
      )
      (IterE
        (CallE "admininstr_val" (ExpA (VarE "v_val")))
        (ListN (VarE "v_n"))
        (iterexp "v_val" (VarE "val_lst"))
      )
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "v_n")
            (VarE "f")
            (CatE
              (CatE
                (CatE
                  (IterE
                    (CallE "admininstr_val" (ExpA (VarE "val'")))
                    List
                    (iterexp "val'" (VarE "val'_lst"))
                  )
                  (IterE
                    (CallE "admininstr_val" (ExpA (VarE "v_val")))
                    (ListN (VarE "v_n"))
                    (iterexp "v_val" (VarE "val_lst"))
                  )
                )
                (ListE (CaseE (Atom RETURN) (TupE)))
              )
              (IterE
                (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
                List
                (iterexp "v_instr" (VarE "instr_lst"))
              )
            )
          )
        )
      )
    )
    (IfPr (CmpE EqOp bool (VarE "v_n") (LenE (VarE "val_lst"))))
  )
  (RuleD
    "return_label"
    (ExpP "v_n" (VarT "n"))
    (ExpP "instr'_lst" (IterT (VarT "instr") List))
    (ExpP "val_lst" (IterT (VarT "val") List))
    (ExpP "instr_lst" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "v_n")
            (VarE "instr'_lst")
            (CatE
              (CatE
                (IterE
                  (CallE "admininstr_val" (ExpA (VarE "v_val")))
                  List
                  (iterexp "v_val" (VarE "val_lst"))
                )
                (ListE (CaseE (Atom RETURN) (TupE)))
              )
              (IterE
                (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
                List
                (iterexp "v_instr" (VarE "instr_lst"))
              )
            )
          )
        )
      )
      (CatE
        (IterE
          (CallE "admininstr_val" (ExpA (VarE "v_val")))
          List
          (iterexp "v_val" (VarE "val_lst"))
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
            (VarE "v_n")
            (VarE "instr'_lst")
            (CatE
              (CatE
                (IterE
                  (CallE "admininstr_val" (ExpA (VarE "v_val")))
                  List
                  (iterexp "v_val" (VarE "val_lst"))
                )
                (ListE (CaseE (Atom RETURN) (TupE)))
              )
              (IterE
                (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
                List
                (iterexp "v_instr" (VarE "instr_lst"))
              )
            )
          )
        )
      )
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom RETURN) (TupE))))
  )
  (RuleD
    "trap_vals"
    (ExpP "val_lst" (IterT (VarT "val") List))
    (ExpP "instr_lst" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (CatE
        (IterE
          (CallE "admininstr_val" (ExpA (VarE "v_val")))
          List
          (iterexp "v_val" (VarE "val_lst"))
        )
        (CatE
          (ListE (CaseE (Atom TRAP) (TupE)))
          (IterE
            (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
            List
            (iterexp "v_instr" (VarE "instr_lst"))
          )
        )
      )
      (ListE (CaseE (Atom TRAP) (TupE)))
    )
    (IfPr
      (BinE
        OrOp
        bool
        (CmpE NeOp bool (VarE "val_lst") (ListE))
        (CmpE NeOp bool (VarE "instr_lst") (ListE))
      )
    )
    (IterPr
      (RulePr "wf_val" (Seq Arg) (TupE (VarE "v_val")))
      List
      (iterexp "v_val" (VarE "val_lst"))
    )
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_instr")))
      List
      (iterexp "v_instr" (VarE "instr_lst"))
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
  )
  (RuleD
    "trap_label"
    (ExpP "v_n" (VarT "n"))
    (ExpP "instr'_lst" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "v_n")
            (VarE "instr'_lst")
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
            (VarE "v_n")
            (VarE "instr'_lst")
            (ListE (CaseE (Atom TRAP) (TupE)))
          )
        )
      )
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
  )
  (RuleD
    "trap_frame"
    (ExpP "v_n" (VarT "n"))
    (ExpP "f" (VarT "frame"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE (VarE "v_n") (VarE "f") (ListE (CaseE (Atom TRAP) (TupE))))
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
          (TupE (VarE "v_n") (VarE "f") (ListE (CaseE (Atom TRAP) (TupE))))
        )
      )
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
  )
  (RuleD
    "unop_val"
    (ExpP "t" (VarT "valtype"))
    (ExpP "c_1" (VarT "val_"))
    (ExpP "unop" (VarT "unop_"))
    (ExpP "c" (VarT "val_"))
    (ExpP "var_0" (IterT (IterT (VarT "val_") List) Opt))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_1")))
        (CaseE (Seq (Atom UNOP) Arg Arg) (TupE (VarE "t") (VarE "unop")))
      )
      (ListE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c"))))
    )
    (RulePr
      "fun_unop_"
      (Seq Arg Arg Arg Arg)
      (TupE (VarE "t") (VarE "unop") (VarE "c_1") (VarE "var_0"))
    )
    (IfPr (CmpE GtOp nat (LenE (TheE (VarE "var_0"))) (NumE (Nat 0))))
    (IfPr (CmpE NeOp bool (VarE "var_0") (OptE)))
    (IfPr (MemE (VarE "c") (TheE (VarE "var_0"))))
    (IterPr
      (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "t") (VarE "iter")))
      List
      (iterexp "iter" (TheE (VarE "var_0")))
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
    "unop_trap"
    (ExpP "t" (VarT "valtype"))
    (ExpP "c_1" (VarT "val_"))
    (ExpP "unop" (VarT "unop_"))
    (ExpP "var_0" (IterT (IterT (VarT "val_") List) Opt))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_1")))
        (CaseE (Seq (Atom UNOP) Arg Arg) (TupE (VarE "t") (VarE "unop")))
      )
      (ListE (CaseE (Atom TRAP) (TupE)))
    )
    (RulePr
      "fun_unop_"
      (Seq Arg Arg Arg Arg)
      (TupE (VarE "t") (VarE "unop") (VarE "c_1") (VarE "var_0"))
    )
    (IfPr (CmpE NeOp bool (VarE "var_0") (OptE)))
    (IfPr (CmpE EqOp bool (TheE (VarE "var_0")) (ListE)))
    (IterPr
      (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "t") (VarE "iter")))
      List
      (iterexp "iter" (TheE (VarE "var_0")))
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
    "binop_val"
    (ExpP "t" (VarT "valtype"))
    (ExpP "c_1" (VarT "val_"))
    (ExpP "c_2" (VarT "val_"))
    (ExpP "binop" (VarT "binop_"))
    (ExpP "c" (VarT "val_"))
    (ExpP "var_0" (IterT (IterT (VarT "val_") List) Opt))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_1")))
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_2")))
        (CaseE (Seq (Atom BINOP) Arg Arg) (TupE (VarE "t") (VarE "binop")))
      )
      (ListE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c"))))
    )
    (RulePr
      "fun_binop_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE (VarE "t") (VarE "binop") (VarE "c_1") (VarE "c_2") (VarE "var_0"))
    )
    (IfPr (CmpE GtOp nat (LenE (TheE (VarE "var_0"))) (NumE (Nat 0))))
    (IfPr (CmpE NeOp bool (VarE "var_0") (OptE)))
    (IfPr (MemE (VarE "c") (TheE (VarE "var_0"))))
    (IterPr
      (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "t") (VarE "iter")))
      List
      (iterexp "iter" (TheE (VarE "var_0")))
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
    "binop_trap"
    (ExpP "t" (VarT "valtype"))
    (ExpP "c_1" (VarT "val_"))
    (ExpP "c_2" (VarT "val_"))
    (ExpP "binop" (VarT "binop_"))
    (ExpP "var_0" (IterT (IterT (VarT "val_") List) Opt))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_1")))
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c_2")))
        (CaseE (Seq (Atom BINOP) Arg Arg) (TupE (VarE "t") (VarE "binop")))
      )
      (ListE (CaseE (Atom TRAP) (TupE)))
    )
    (RulePr
      "fun_binop_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE (VarE "t") (VarE "binop") (VarE "c_1") (VarE "c_2") (VarE "var_0"))
    )
    (IfPr (CmpE NeOp bool (VarE "var_0") (OptE)))
    (IfPr (CmpE EqOp bool (TheE (VarE "var_0")) (ListE)))
    (IterPr
      (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "t") (VarE "iter")))
      List
      (iterexp "iter" (TheE (VarE "var_0")))
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
    (ExpP "var_0" (IterT (VarT "val_") Opt))
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
    (RulePr
      "fun_testop_"
      (Seq Arg Arg Arg Arg)
      (TupE (VarE "t") (VarE "testop") (VarE "c_1") (VarE "var_0"))
    )
    (IfPr (CmpE NeOp bool (VarE "var_0") (OptE)))
    (IfPr (CmpE EqOp bool (VarE "c") (TheE (VarE "var_0"))))
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE (CaseE (Atom I32) (TupE)) (TheE (VarE "var_0")))
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
    (ExpP "var_0" (IterT (VarT "val_") Opt))
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
    (RulePr
      "fun_relop_"
      (Seq Arg Arg Arg Arg Arg)
      (TupE (VarE "t") (VarE "relop") (VarE "c_1") (VarE "c_2") (VarE "var_0"))
    )
    (IfPr (CmpE NeOp bool (VarE "var_0") (OptE)))
    (IfPr (CmpE EqOp bool (VarE "c") (TheE (VarE "var_0"))))
    (RulePr
      "wf_val_"
      (Seq Arg Arg)
      (TupE (CaseE (Atom I32) (TupE)) (TheE (VarE "var_0")))
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
    "cvtop_val"
    (ExpP "t_1" (VarT "valtype"))
    (ExpP "c_1" (VarT "val_"))
    (ExpP "t_2" (VarT "valtype"))
    (ExpP "v_cvtop" (VarT "cvtop"))
    (ExpP "c" (VarT "val_"))
    (ExpP "var_0" (IterT (IterT (VarT "val_") List) Opt))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t_1") (VarE "c_1")))
        (CaseE
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupE (VarE "t_2") (VarE "t_1") (VarE "v_cvtop"))
        )
      )
      (ListE (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t_2") (VarE "c"))))
    )
    (RulePr
      "fun_cvtop__"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (VarE "t_1")
        (VarE "t_2")
        (VarE "v_cvtop")
        (VarE "c_1")
        (VarE "var_0")
      )
    )
    (IfPr (CmpE GtOp nat (LenE (TheE (VarE "var_0"))) (NumE (Nat 0))))
    (IfPr (CmpE NeOp bool (VarE "var_0") (OptE)))
    (IfPr (MemE (VarE "c") (TheE (VarE "var_0"))))
    (IterPr
      (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "t_2") (VarE "iter")))
      List
      (iterexp "iter" (TheE (VarE "var_0")))
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
          (TupE (VarE "t_2") (VarE "t_1") (VarE "v_cvtop"))
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
    "cvtop_trap"
    (ExpP "t_1" (VarT "valtype"))
    (ExpP "c_1" (VarT "val_"))
    (ExpP "t_2" (VarT "valtype"))
    (ExpP "v_cvtop" (VarT "cvtop"))
    (ExpP "var_0" (IterT (IterT (VarT "val_") List) Opt))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t_1") (VarE "c_1")))
        (CaseE
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupE (VarE "t_2") (VarE "t_1") (VarE "v_cvtop"))
        )
      )
      (ListE (CaseE (Atom TRAP) (TupE)))
    )
    (RulePr
      "fun_cvtop__"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (VarE "t_1")
        (VarE "t_2")
        (VarE "v_cvtop")
        (VarE "c_1")
        (VarE "var_0")
      )
    )
    (IfPr (CmpE NeOp bool (VarE "var_0") (OptE)))
    (IfPr (CmpE EqOp bool (TheE (VarE "var_0")) (ListE)))
    (IterPr
      (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "t_2") (VarE "iter")))
      List
      (iterexp "iter" (TheE (VarE "var_0")))
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
          (TupE (VarE "t_2") (VarE "t_1") (VarE "v_cvtop"))
        )
      )
    )
    (RulePr "wf_admininstr" (Seq Arg) (TupE (CaseE (Atom TRAP) (TupE))))
  )
  (RuleD
    "local_tee"
    (ExpP "v_val" (VarT "val"))
    (ExpP "x" (VarT "idx"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CallE "admininstr_val" (ExpA (VarE "v_val")))
        (CaseE (Seq (Atom LOCAL_TEE) Arg) (TupE (VarE "x")))
      )
      (ListE
        (CallE "admininstr_val" (ExpA (VarE "v_val")))
        (CallE "admininstr_val" (ExpA (VarE "v_val")))
        (CaseE (Seq (Atom LOCAL_SET) Arg) (TupE (VarE "x")))
      )
    )
    (RulePr "wf_val" (Seq Arg) (TupE (VarE "v_val")))
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL_TEE) Arg) (TupE (VarE "x"))))
    )
    (RulePr
      "wf_admininstr"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL_SET) Arg) (TupE (VarE "x"))))
    )
  )
)
(RelD
  "Step_read_before_call_indirect_trap"
  Arg
  (VarT "config")
  (RuleD
    "call_indirect_call_0"
    (ExpP "z" (VarT "state"))
    (ExpP "i" (VarT "val_"))
    (ExpP "x" (VarT "idx"))
    (ExpP "a" (VarT "addr"))
    Arg
    (CaseE
      (Seq (Atom mk_config) Arg Arg)
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
        LtOp
        nat
        (ProjE
          (CallE
            "proj_uN_0"
            (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
          )
          0
        )
        (LenE
          (DotE
            (CallE
              "fun_table"
              (ExpA (VarE "z"))
              (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
            )
            (Atom REFS)
          )
        )
      )
    )
    (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "i"))) (OptE)))
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE
          (DotE
            (CallE
              "fun_table"
              (ExpA (VarE "z"))
              (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
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
      (CmpE LtOp nat (VarE "a") (LenE (CallE "fun_funcinst" (ExpA (VarE "z")))))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE "fun_type" (ExpA (VarE "z")) (ExpA (VarE "x")))
        (DotE
          (IdxE (CallE "fun_funcinst" (ExpA (VarE "z"))) (VarE "a"))
          (Atom TYPE)
        )
      )
    )
    (RulePr
      "wf_tableinst"
      (Seq Arg)
      (TupE
        (CallE
          "fun_table"
          (ExpA (VarE "z"))
          (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
        )
      )
    )
    (IterPr
      (RulePr "wf_funcinst" (Seq Arg) (TupE (VarE "iter")))
      List
      (iterexp "iter" (CallE "fun_funcinst" (ExpA (VarE "z"))))
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
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
      (TupE
        (NumE (Nat 32))
        (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
      )
    )
  )
)
(HintD
  (RelH
    "Step_read_before_call_indirect_trap"
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
    (ExpP "t_opt" (IterT (VarT "valtype") Opt))
    (ExpP "instr_lst" (IterT (VarT "instr") List))
    (ExpP "v_n" (VarT "n"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE
          (VarE "z")
          (ListE
            (CaseE
              (Seq (Atom BLOCK) Arg Arg)
              (TupE (VarE "t_opt") (VarE "instr_lst"))
            )
          )
        )
      )
      (ListE
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "v_n")
            (ListE)
            (IterE
              (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
              List
              (iterexp "v_instr" (VarE "instr_lst"))
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
          (CmpE EqOp bool (VarE "t_opt") (OptE))
          (CmpE EqOp bool (VarE "v_n") (NumE (Nat 0)))
        )
        (BinE
          AndOp
          bool
          (CmpE NeOp bool (VarE "t_opt") (OptE))
          (CmpE EqOp bool (VarE "v_n") (NumE (Nat 1)))
        )
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom BLOCK) Arg Arg)
                (TupE (VarE "t_opt") (VarE "instr_lst"))
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
            (VarE "v_n")
            (ListE)
            (IterE
              (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
              List
              (iterexp "v_instr" (VarE "instr_lst"))
            )
          )
        )
      )
    )
  )
  (RuleD
    "loop"
    (ExpP "z" (VarT "state"))
    (ExpP "t_opt" (IterT (VarT "valtype") Opt))
    (ExpP "instr_lst" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE
          (VarE "z")
          (ListE
            (CaseE
              (Seq (Atom LOOP) Arg Arg)
              (TupE (VarE "t_opt") (VarE "instr_lst"))
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
                (TupE (VarE "t_opt") (VarE "instr_lst"))
              )
            )
            (IterE
              (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
              List
              (iterexp "v_instr" (VarE "instr_lst"))
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
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom LOOP) Arg Arg)
                (TupE (VarE "t_opt") (VarE "instr_lst"))
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
                (TupE (VarE "t_opt") (VarE "instr_lst"))
              )
            )
            (IterE
              (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
              List
              (iterexp "v_instr" (VarE "instr_lst"))
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
        (Seq (Atom mk_config) Arg Arg)
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
              (CallE "fun_funcaddr" (ExpA (VarE "z")))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (CallE "fun_funcaddr" (ExpA (VarE "z"))))
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
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
              (CallE "fun_funcaddr" (ExpA (VarE "z")))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
            )
          )
        )
      )
    )
  )
  (RuleD
    "call_indirect_call"
    (ExpP "z" (VarT "state"))
    (ExpP "i" (VarT "val_"))
    (ExpP "x" (VarT "idx"))
    (ExpP "a" (VarT "addr"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
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
        LtOp
        nat
        (ProjE
          (CallE
            "proj_uN_0"
            (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "i")))))
          )
          0
        )
        (LenE
          (DotE
            (CallE
              "fun_table"
              (ExpA (VarE "z"))
              (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
            )
            (Atom REFS)
          )
        )
      )
    )
    (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "i"))) (OptE)))
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE
          (DotE
            (CallE
              "fun_table"
              (ExpA (VarE "z"))
              (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
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
      (CmpE LtOp nat (VarE "a") (LenE (CallE "fun_funcinst" (ExpA (VarE "z")))))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE "fun_type" (ExpA (VarE "z")) (ExpA (VarE "x")))
        (DotE
          (IdxE (CallE "fun_funcinst" (ExpA (VarE "z"))) (VarE "a"))
          (Atom TYPE)
        )
      )
    )
    (RulePr
      "wf_tableinst"
      (Seq Arg)
      (TupE
        (CallE
          "fun_table"
          (ExpA (VarE "z"))
          (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
        )
      )
    )
    (IterPr
      (RulePr "wf_funcinst" (Seq Arg) (TupE (VarE "iter")))
      List
      (iterexp "iter" (CallE "fun_funcinst" (ExpA (VarE "z"))))
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
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
      (TupE
        (NumE (Nat 32))
        (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
      )
    )
  )
  (RuleD
    "call_indirect_trap"
    (ExpP "z" (VarT "state"))
    (ExpP "i" (VarT "val_"))
    (ExpP "x" (VarT "idx"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
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
        "Step_read_before_call_indirect_trap"
        Arg
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
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
          (Seq (Atom mk_config) Arg Arg)
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
    (ExpP "val_lst" (IterT (VarT "val") List))
    (ExpP "a" (VarT "addr"))
    (ExpP "v_n" (VarT "n"))
    (ExpP "f" (VarT "frame"))
    (ExpP "instr_lst" (IterT (VarT "instr") List))
    (ExpP "t_1_lst" (IterT (VarT "valtype") List))
    (ExpP "t_2_lst" (IterT (VarT "valtype") List))
    (ExpP "mm" (VarT "moduleinst"))
    (ExpP "v_func" (VarT "func"))
    (ExpP "x" (VarT "idx"))
    (ExpP "t_lst" (IterT (VarT "valtype") List))
    (ExpP "var_0_lst" (IterT (VarT "val") List))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE
          (VarE "z")
          (CatE
            (IterE
              (CallE "admininstr_val" (ExpA (VarE "v_val")))
              (ListN (VarE "k"))
              (iterexp "v_val" (VarE "val_lst"))
            )
            (ListE (CaseE (Seq (Atom CALL_ADDR) Arg) (TupE (VarE "a"))))
          )
        )
      )
      (ListE
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE
            (VarE "v_n")
            (VarE "f")
            (ListE
              (CaseE
                (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
                (TupE
                  (VarE "v_n")
                  (ListE)
                  (IterE
                    (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
                    List
                    (iterexp "v_instr" (VarE "instr_lst"))
                  )
                )
              )
            )
          )
        )
      )
    )
    (IfPr (CmpE EqOp bool (LenE (VarE "var_0_lst")) (LenE (VarE "t_lst"))))
    (IterPr
      (RulePr "fun_default_" (Seq Arg Arg) (TupE (VarE "t") (VarE "var_0")))
      List
      (iterexp "var_0" (VarE "var_0_lst"))
      (iterexp "t" (VarE "t_lst"))
    )
    (IfPr
      (CmpE LtOp nat (VarE "a") (LenE (CallE "fun_funcinst" (ExpA (VarE "z")))))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE (CallE "fun_funcinst" (ExpA (VarE "z"))) (VarE "a"))
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Seq (Atom mk_functype) Arg Arg)
              (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
            )
          )
          (expfield (Atom MODULE) (VarE "mm"))
          (expfield (Atom CODE) (VarE "v_func"))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "v_func")
        (CaseE
          (Seq (Atom FUNC) Arg Arg Arg)
          (TupE
            (VarE "x")
            (IterE
              (CaseE (Seq (Atom LOCAL) Arg) (TupE (VarE "t")))
              List
              (iterexp "t" (VarE "t_lst"))
            )
            (VarE "instr_lst")
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
          (expfield (Atom LOCALS) (CatE (VarE "val_lst") (VarE "var_0_lst")))
          (expfield (Atom MODULE) (VarE "mm"))
        )
      )
    )
    (IterPr
      (RulePr "wf_funcinst" (Seq Arg) (TupE (VarE "iter")))
      List
      (iterexp "iter" (CallE "fun_funcinst" (ExpA (VarE "z"))))
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "z")
            (CatE
              (IterE
                (CallE "admininstr_val" (ExpA (VarE "v_val")))
                (ListN (VarE "k"))
                (iterexp "v_val" (VarE "val_lst"))
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
            (VarE "v_n")
            (VarE "f")
            (ListE
              (CaseE
                (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
                (TupE
                  (VarE "v_n")
                  (ListE)
                  (IterE
                    (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
                    List
                    (iterexp "v_instr" (VarE "instr_lst"))
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
              (Seq (Atom mk_functype) Arg Arg)
              (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
            )
          )
          (expfield (Atom MODULE) (VarE "mm"))
          (expfield (Atom CODE) (VarE "v_func"))
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
              (iterexp "t" (VarE "t_lst"))
            )
            (VarE "instr_lst")
          )
        )
      )
    )
    (RulePr
      "wf_frame"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom LOCALS) (CatE (VarE "val_lst") (VarE "var_0_lst")))
          (expfield (Atom MODULE) (VarE "mm"))
        )
      )
    )
    (IfPr (CmpE EqOp bool (VarE "k") (LenE (VarE "val_lst"))))
    (IfPr (CmpE EqOp bool (VarE "k") (LenE (VarE "t_1_lst"))))
    (IfPr (CmpE EqOp bool (VarE "v_n") (LenE (VarE "t_2_lst"))))
  )
  (RuleD
    "local_get"
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "idx"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE
          (VarE "z")
          (ListE (CaseE (Seq (Atom LOCAL_GET) Arg) (TupE (VarE "x"))))
        )
      )
      (ListE
        (CallE
          "admininstr_val"
          (ExpA (CallE "fun_local" (ExpA (VarE "z")) (ExpA (VarE "x"))))
        )
      )
    )
    (RulePr
      "wf_val"
      (Seq Arg)
      (TupE (CallE "fun_local" (ExpA (VarE "z")) (ExpA (VarE "x"))))
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "z")
            (ListE (CaseE (Seq (Atom LOCAL_GET) Arg) (TupE (VarE "x"))))
          )
        )
      )
    )
  )
  (RuleD
    "global_get"
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "idx"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE
          (VarE "z")
          (ListE (CaseE (Seq (Atom GLOBAL_GET) Arg) (TupE (VarE "x"))))
        )
      )
      (ListE
        (CallE
          "admininstr_val"
          (ExpA
            (DotE
              (CallE "fun_global" (ExpA (VarE "z")) (ExpA (VarE "x")))
              (Atom VALUE)
            )
          )
        )
      )
    )
    (RulePr
      "wf_globalinst"
      (Seq Arg)
      (TupE (CallE "fun_global" (ExpA (VarE "z")) (ExpA (VarE "x"))))
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "z")
            (ListE (CaseE (Seq (Atom GLOBAL_GET) Arg) (TupE (VarE "x"))))
          )
        )
      )
    )
  )
  (RuleD
    "load_num_trap"
    (ExpP "z" (VarT "state"))
    (ExpP "i" (VarT "val_"))
    (ExpP "t" (VarT "valtype"))
    (ExpP "ao" (VarT "memarg"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
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
    (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "i"))) (OptE)))
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
              "fun_mem"
              (ExpA (VarE "z"))
              (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
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
          "fun_mem"
          (ExpA (VarE "z"))
          (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
        )
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
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
      (TupE
        (NumE (Nat 32))
        (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
      )
    )
  )
  (RuleD
    "load_num_val"
    (ExpP "z" (VarT "state"))
    (ExpP "i" (VarT "val_"))
    (ExpP "t" (VarT "valtype"))
    (ExpP "ao" (VarT "memarg"))
    (ExpP "c" (VarT "val_"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
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
    (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "i"))) (OptE)))
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE "bytes_" (ExpA (VarE "t")) (ExpA (VarE "c")))
        (SliceE
          (DotE
            (CallE
              "fun_mem"
              (ExpA (VarE "z"))
              (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
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
        (CallE
          "fun_mem"
          (ExpA (VarE "z"))
          (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
        )
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
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
      (TupE
        (NumE (Nat 32))
        (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
      )
    )
  )
  (RuleD
    "load_pack_trap"
    (ExpP "z" (VarT "state"))
    (ExpP "i" (VarT "val_"))
    (ExpP "v_Inn" (VarT "Inn"))
    (ExpP "v_n" (VarT "n"))
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "ao" (VarT "memarg"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
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
                (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
                (OptE
                  (CaseE
                    (Seq (Atom mk_loadop__0) Arg Arg)
                    (TupE
                      (VarE "v_Inn")
                      (CaseE
                        (Seq (Atom mk_loadop_Inn) Arg Arg)
                        (TupE
                          (CaseE (Seq (Atom mk_sz) Arg) (TupE (VarE "v_n")))
                          (VarE "v_sx")
                        )
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
    (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "i"))) (OptE)))
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
              (CvtE nat rat (VarE "v_n"))
              (CvtE nat rat (NumE (Nat 8)))
            )
          )
        )
        (LenE
          (DotE
            (CallE
              "fun_mem"
              (ExpA (VarE "z"))
              (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
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
          "fun_mem"
          (ExpA (VarE "z"))
          (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
        )
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
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
                  (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
                  (OptE
                    (CaseE
                      (Seq (Atom mk_loadop__0) Arg Arg)
                      (TupE
                        (VarE "v_Inn")
                        (CaseE
                          (Seq (Atom mk_loadop_Inn) Arg Arg)
                          (TupE
                            (CaseE (Seq (Atom mk_sz) Arg) (TupE (VarE "v_n")))
                            (VarE "v_sx")
                          )
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
      (TupE
        (NumE (Nat 32))
        (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
      )
    )
  )
  (RuleD
    "load_pack_val"
    (ExpP "z" (VarT "state"))
    (ExpP "i" (VarT "val_"))
    (ExpP "v_Inn" (VarT "Inn"))
    (ExpP "v_n" (VarT "n"))
    (ExpP "v_sx" (VarT "sx"))
    (ExpP "ao" (VarT "memarg"))
    (ExpP "c" (VarT "iN"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
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
                (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
                (OptE
                  (CaseE
                    (Seq (Atom mk_loadop__0) Arg Arg)
                    (TupE
                      (VarE "v_Inn")
                      (CaseE
                        (Seq (Atom mk_loadop_Inn) Arg Arg)
                        (TupE
                          (CaseE (Seq (Atom mk_sz) Arg) (TupE (VarE "v_n")))
                          (VarE "v_sx")
                        )
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
            (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE
                (VarE "v_Inn")
                (CallE
                  "extend__"
                  (ExpA (VarE "v_n"))
                  (ExpA
                    (CallE
                      "size"
                      (ExpA (CallE "valtype_Inn" (ExpA (VarE "v_Inn"))))
                    )
                  )
                  (ExpA (VarE "v_sx"))
                  (ExpA (VarE "c"))
                )
              )
            )
          )
        )
      )
    )
    (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "i"))) (OptE)))
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE "ibytes_" (ExpA (VarE "v_n")) (ExpA (VarE "c")))
        (SliceE
          (DotE
            (CallE
              "fun_mem"
              (ExpA (VarE "z"))
              (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
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
              (CvtE nat rat (VarE "v_n"))
              (CvtE nat rat (NumE (Nat 8)))
            )
          )
        )
      )
    )
    (IterPr
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "iter")))
      List
      (iterexp "iter" (CallE "ibytes_" (ExpA (VarE "v_n")) (ExpA (VarE "c"))))
    )
    (RulePr
      "wf_meminst"
      (Seq Arg)
      (TupE
        (CallE
          "fun_mem"
          (ExpA (VarE "z"))
          (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
        )
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
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
                  (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
                  (OptE
                    (CaseE
                      (Seq (Atom mk_loadop__0) Arg Arg)
                      (TupE
                        (VarE "v_Inn")
                        (CaseE
                          (Seq (Atom mk_loadop_Inn) Arg Arg)
                          (TupE
                            (CaseE (Seq (Atom mk_sz) Arg) (TupE (VarE "v_n")))
                            (VarE "v_sx")
                          )
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
            (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
            (CaseE
              (Seq (Atom mk_val__0) Arg Arg)
              (TupE
                (VarE "v_Inn")
                (CallE
                  "extend__"
                  (ExpA (VarE "v_n"))
                  (ExpA
                    (CallE
                      "size"
                      (ExpA (CallE "valtype_Inn" (ExpA (VarE "v_Inn"))))
                    )
                  )
                  (ExpA (VarE "v_sx"))
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
      (TupE
        (NumE (Nat 32))
        (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
      )
    )
  )
  (RuleD
    "memory_size"
    (ExpP "z" (VarT "state"))
    (ExpP "v_n" (VarT "n"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE (VarE "z") (ListE (CaseE (Atom MEMORY_SIZE) (TupE))))
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
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
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
        (BinE
          MulOp
          nat
          (BinE MulOp nat (VarE "v_n") (NumE (Nat 64)))
          (CallE "Ki")
        )
        (LenE
          (DotE
            (CallE
              "fun_mem"
              (ExpA (VarE "z"))
              (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
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
          "fun_mem"
          (ExpA (VarE "z"))
          (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
        )
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE (VarE "z") (ListE (CaseE (Atom MEMORY_SIZE) (TupE))))
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
              (TupE
                (CaseE (Atom I32) (TupE))
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
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
        (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
      )
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
      (ExpP "admininstr_lst" (IterT (VarT "admininstr") List))
      (ExpP "admininstr'_lst" (IterT (VarT "admininstr") List))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE (VarE "z") (VarE "admininstr_lst"))
        )
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE (VarE "z") (VarE "admininstr'_lst"))
        )
      )
      (RulePr
        "Step_pure"
        (Infix Arg ~> Arg)
        (TupE (VarE "admininstr_lst") (VarE "admininstr'_lst"))
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z") (VarE "admininstr_lst"))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z") (VarE "admininstr'_lst"))
          )
        )
      )
    )
    (RuleD
      "read"
      (ExpP "z" (VarT "state"))
      (ExpP "admininstr_lst" (IterT (VarT "admininstr") List))
      (ExpP "admininstr'_lst" (IterT (VarT "admininstr") List))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE (VarE "z") (VarE "admininstr_lst"))
        )
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE (VarE "z") (VarE "admininstr'_lst"))
        )
      )
      (RulePr
        "Step_read"
        (Infix Arg ~> Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z") (VarE "admininstr_lst"))
          )
          (VarE "admininstr'_lst")
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z") (VarE "admininstr_lst"))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z") (VarE "admininstr'_lst"))
          )
        )
      )
    )
    (RuleD
      "ctxt_label"
      (ExpP "z" (VarT "state"))
      (ExpP "v_n" (VarT "n"))
      (ExpP "instr_0_lst" (IterT (VarT "instr") List))
      (ExpP "admininstr_lst" (IterT (VarT "admininstr") List))
      (ExpP "z'" (VarT "state"))
      (ExpP "admininstr'_lst" (IterT (VarT "admininstr") List))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
                (TupE (VarE "v_n") (VarE "instr_0_lst") (VarE "admininstr_lst"))
              )
            )
          )
        )
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "z'")
            (ListE
              (CaseE
                (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
                (TupE
                  (VarE "v_n")
                  (VarE "instr_0_lst")
                  (VarE "admininstr'_lst")
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
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z") (VarE "admininstr_lst"))
          )
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z'") (VarE "admininstr'_lst"))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE
              (VarE "z")
              (ListE
                (CaseE
                  (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
                  (TupE
                    (VarE "v_n")
                    (VarE "instr_0_lst")
                    (VarE "admininstr_lst")
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
            (Seq (Atom mk_config) Arg Arg)
            (TupE
              (VarE "z'")
              (ListE
                (CaseE
                  (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
                  (TupE
                    (VarE "v_n")
                    (VarE "instr_0_lst")
                    (VarE "admininstr'_lst")
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
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z") (VarE "admininstr_lst"))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z'") (VarE "admininstr'_lst"))
          )
        )
      )
    )
    (RuleD
      "ctxt_frame"
      (ExpP "s" (VarT "store"))
      (ExpP "f" (VarT "frame"))
      (ExpP "v_n" (VarT "n"))
      (ExpP "f'" (VarT "frame"))
      (ExpP "admininstr_lst" (IterT (VarT "admininstr") List))
      (ExpP "s'" (VarT "store"))
      (ExpP "f''" (VarT "frame"))
      (ExpP "admininstr'_lst" (IterT (VarT "admininstr") List))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f")))
            (ListE
              (CaseE
                (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
                (TupE (VarE "v_n") (VarE "f'") (VarE "admininstr_lst"))
              )
            )
          )
        )
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s'") (VarE "f")))
            (ListE
              (CaseE
                (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
                (TupE (VarE "v_n") (VarE "f''") (VarE "admininstr'_lst"))
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
            (Seq (Atom mk_config) Arg Arg)
            (TupE
              (CaseE
                (Seq (Atom mk_state) Arg Arg)
                (TupE (VarE "s") (VarE "f'"))
              )
              (VarE "admininstr_lst")
            )
          )
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE
              (CaseE
                (Seq (Atom mk_state) Arg Arg)
                (TupE (VarE "s'") (VarE "f''"))
              )
              (VarE "admininstr'_lst")
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE
              (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f")))
              (ListE
                (CaseE
                  (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
                  (TupE (VarE "v_n") (VarE "f'") (VarE "admininstr_lst"))
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
            (Seq (Atom mk_config) Arg Arg)
            (TupE
              (CaseE
                (Seq (Atom mk_state) Arg Arg)
                (TupE (VarE "s'") (VarE "f"))
              )
              (ListE
                (CaseE
                  (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
                  (TupE (VarE "v_n") (VarE "f''") (VarE "admininstr'_lst"))
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
            (Seq (Atom mk_config) Arg Arg)
            (TupE
              (CaseE
                (Seq (Atom mk_state) Arg Arg)
                (TupE (VarE "s") (VarE "f'"))
              )
              (VarE "admininstr_lst")
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE
              (CaseE
                (Seq (Atom mk_state) Arg Arg)
                (TupE (VarE "s'") (VarE "f''"))
              )
              (VarE "admininstr'_lst")
            )
          )
        )
      )
    )
    (RuleD
      "ctxt_instrs"
      (ExpP "z" (VarT "state"))
      (ExpP "val_lst" (IterT (VarT "val") List))
      (ExpP "admininstr_lst" (IterT (VarT "admininstr") List))
      (ExpP "admininstr_1_lst" (IterT (VarT "admininstr") List))
      (ExpP "z'" (VarT "state"))
      (ExpP "admininstr'_lst" (IterT (VarT "admininstr") List))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "z")
            (CatE
              (IterE
                (CallE "admininstr_val" (ExpA (VarE "v_val")))
                List
                (iterexp "v_val" (VarE "val_lst"))
              )
              (CatE (VarE "admininstr_lst") (VarE "admininstr_1_lst"))
            )
          )
        )
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "z'")
            (CatE
              (IterE
                (CallE "admininstr_val" (ExpA (VarE "v_val")))
                List
                (iterexp "v_val" (VarE "val_lst"))
              )
              (CatE (VarE "admininstr'_lst") (VarE "admininstr_1_lst"))
            )
          )
        )
      )
      (RulePr
        "Step"
        (Infix Arg ~> Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z") (VarE "admininstr_lst"))
          )
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z'") (VarE "admininstr'_lst"))
          )
        )
      )
      (IfPr
        (BinE
          OrOp
          bool
          (CmpE NeOp bool (VarE "val_lst") (ListE))
          (CmpE NeOp bool (VarE "admininstr_1_lst") (ListE))
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE
              (VarE "z")
              (CatE
                (IterE
                  (CallE "admininstr_val" (ExpA (VarE "v_val")))
                  List
                  (iterexp "v_val" (VarE "val_lst"))
                )
                (CatE (VarE "admininstr_lst") (VarE "admininstr_1_lst"))
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
            (Seq (Atom mk_config) Arg Arg)
            (TupE
              (VarE "z'")
              (CatE
                (IterE
                  (CallE "admininstr_val" (ExpA (VarE "v_val")))
                  List
                  (iterexp "v_val" (VarE "val_lst"))
                )
                (CatE (VarE "admininstr'_lst") (VarE "admininstr_1_lst"))
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
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z") (VarE "admininstr_lst"))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z'") (VarE "admininstr'_lst"))
          )
        )
      )
    )
    (RuleD
      "local_set"
      (ExpP "z" (VarT "state"))
      (ExpP "v_val" (VarT "val"))
      (ExpP "x" (VarT "idx"))
      (ExpP "var_0" (VarT "state"))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "z")
            (ListE
              (CallE "admininstr_val" (ExpA (VarE "v_val")))
              (CaseE (Seq (Atom LOCAL_SET) Arg) (TupE (VarE "x")))
            )
          )
        )
        (CaseE (Seq (Atom mk_config) Arg Arg) (TupE (VarE "var_0") (ListE)))
      )
      (RulePr
        "fun_with_local"
        (Seq Arg Arg Arg Arg)
        (TupE (VarE "z") (VarE "x") (VarE "v_val") (VarE "var_0"))
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE
              (VarE "z")
              (ListE
                (CallE "admininstr_val" (ExpA (VarE "v_val")))
                (CaseE (Seq (Atom LOCAL_SET) Arg) (TupE (VarE "x")))
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE (Seq (Atom mk_config) Arg Arg) (TupE (VarE "var_0") (ListE)))
        )
      )
    )
    (RuleD
      "global_set"
      (ExpP "z" (VarT "state"))
      (ExpP "v_val" (VarT "val"))
      (ExpP "x" (VarT "idx"))
      (ExpP "var_0" (VarT "state"))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "z")
            (ListE
              (CallE "admininstr_val" (ExpA (VarE "v_val")))
              (CaseE (Seq (Atom GLOBAL_SET) Arg) (TupE (VarE "x")))
            )
          )
        )
        (CaseE (Seq (Atom mk_config) Arg Arg) (TupE (VarE "var_0") (ListE)))
      )
      (RulePr
        "fun_with_global"
        (Seq Arg Arg Arg Arg)
        (TupE (VarE "z") (VarE "x") (VarE "v_val") (VarE "var_0"))
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE
              (VarE "z")
              (ListE
                (CallE "admininstr_val" (ExpA (VarE "v_val")))
                (CaseE (Seq (Atom GLOBAL_SET) Arg) (TupE (VarE "x")))
              )
            )
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE (Seq (Atom mk_config) Arg Arg) (TupE (VarE "var_0") (ListE)))
        )
      )
    )
    (RuleD
      "store_num_trap"
      (ExpP "z" (VarT "state"))
      (ExpP "i" (VarT "val_"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "c" (VarT "val_"))
      (ExpP "ao" (VarT "memarg"))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
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
          (Seq (Atom mk_config) Arg Arg)
          (TupE (VarE "z") (ListE (CaseE (Atom TRAP) (TupE))))
        )
      )
      (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "i"))) (OptE)))
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
                "fun_mem"
                (ExpA (VarE "z"))
                (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
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
            "fun_mem"
            (ExpA (VarE "z"))
            (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
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
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z") (ListE (CaseE (Atom TRAP) (TupE))))
          )
        )
      )
      (RulePr
        "wf_uN"
        (Seq Arg Arg)
        (TupE
          (NumE (Nat 32))
          (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
        )
      )
    )
    (RuleD
      "store_num_val"
      (ExpP "z" (VarT "state"))
      (ExpP "i" (VarT "val_"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "c" (VarT "val_"))
      (ExpP "ao" (VarT "memarg"))
      (ExpP "b_lst" (IterT (VarT "byte") List))
      (ExpP "var_0" (VarT "state"))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
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
        (CaseE (Seq (Atom mk_config) Arg Arg) (TupE (VarE "var_0") (ListE)))
      )
      (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "i"))) (OptE)))
      (RulePr
        "fun_with_mem"
        (Seq Arg Arg Arg Arg Arg Arg)
        (TupE
          (VarE "z")
          (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
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
          (VarE "b_lst")
          (VarE "var_0")
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (VarE "b_lst")
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
            (Seq (Atom mk_config) Arg Arg)
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
          (CaseE (Seq (Atom mk_config) Arg Arg) (TupE (VarE "var_0") (ListE)))
        )
      )
    )
    (RuleD
      "store_pack_trap"
      (ExpP "z" (VarT "state"))
      (ExpP "i" (VarT "val_"))
      (ExpP "v_Inn" (VarT "Inn"))
      (ExpP "c" (VarT "val_"))
      (ExpP "v_n" (VarT "n"))
      (ExpP "ao" (VarT "memarg"))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
              )
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CallE "valtype_Inn" (ExpA (VarE "v_Inn"))) (VarE "c"))
              )
              (CaseE
                (Seq (Atom STORE) Arg Arg Arg)
                (TupE
                  (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
                  (OptE (CaseE (Seq (Atom mk_sz) Arg) (TupE (VarE "v_n"))))
                  (VarE "ao")
                )
              )
            )
          )
        )
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE (VarE "z") (ListE (CaseE (Atom TRAP) (TupE))))
        )
      )
      (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "i"))) (OptE)))
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
                (CvtE nat rat (VarE "v_n"))
                (CvtE nat rat (NumE (Nat 8)))
              )
            )
          )
          (LenE
            (DotE
              (CallE
                "fun_mem"
                (ExpA (VarE "z"))
                (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
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
            "fun_mem"
            (ExpA (VarE "z"))
            (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE
              (VarE "z")
              (ListE
                (CaseE
                  (Seq (Atom CONST) Arg Arg)
                  (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
                )
                (CaseE
                  (Seq (Atom CONST) Arg Arg)
                  (TupE (CallE "valtype_Inn" (ExpA (VarE "v_Inn"))) (VarE "c"))
                )
                (CaseE
                  (Seq (Atom STORE) Arg Arg Arg)
                  (TupE
                    (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
                    (OptE (CaseE (Seq (Atom mk_sz) Arg) (TupE (VarE "v_n"))))
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
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z") (ListE (CaseE (Atom TRAP) (TupE))))
          )
        )
      )
      (RulePr
        "wf_uN"
        (Seq Arg Arg)
        (TupE
          (NumE (Nat 32))
          (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
        )
      )
    )
    (RuleD
      "store_pack_val"
      (ExpP "z" (VarT "state"))
      (ExpP "i" (VarT "val_"))
      (ExpP "v_Inn" (VarT "Inn"))
      (ExpP "c" (VarT "val_"))
      (ExpP "v_n" (VarT "n"))
      (ExpP "ao" (VarT "memarg"))
      (ExpP "b_lst" (IterT (VarT "byte") List))
      (ExpP "var_0" (VarT "state"))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "z")
            (ListE
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
              )
              (CaseE
                (Seq (Atom CONST) Arg Arg)
                (TupE (CallE "valtype_Inn" (ExpA (VarE "v_Inn"))) (VarE "c"))
              )
              (CaseE
                (Seq (Atom STORE) Arg Arg Arg)
                (TupE
                  (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
                  (OptE (CaseE (Seq (Atom mk_sz) Arg) (TupE (VarE "v_n"))))
                  (VarE "ao")
                )
              )
            )
          )
        )
        (CaseE (Seq (Atom mk_config) Arg Arg) (TupE (VarE "var_0") (ListE)))
      )
      (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "i"))) (OptE)))
      (RulePr
        "fun_with_mem"
        (Seq Arg Arg Arg Arg Arg Arg)
        (TupE
          (VarE "z")
          (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
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
              (CvtE nat rat (VarE "v_n"))
              (CvtE nat rat (NumE (Nat 8)))
            )
          )
          (VarE "b_lst")
          (VarE "var_0")
        )
      )
      (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "c"))) (OptE)))
      (IfPr
        (CmpE
          EqOp
          bool
          (VarE "b_lst")
          (CallE
            "ibytes_"
            (ExpA (VarE "v_n"))
            (ExpA
              (CallE
                "wrap__"
                (ExpA
                  (CallE
                    "size"
                    (ExpA (CallE "valtype_Inn" (ExpA (VarE "v_Inn"))))
                  )
                )
                (ExpA (VarE "v_n"))
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
            (ExpA (VarE "v_n"))
            (ExpA
              (CallE
                "wrap__"
                (ExpA
                  (CallE
                    "size"
                    (ExpA (CallE "valtype_Inn" (ExpA (VarE "v_Inn"))))
                  )
                )
                (ExpA (VarE "v_n"))
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
          (VarE "v_n")
          (CallE
            "wrap__"
            (ExpA
              (CallE "size" (ExpA (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))))
            )
            (ExpA (VarE "v_n"))
            (ExpA (TheE (CallE "proj_val__0" (ExpA (VarE "c")))))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE
              (VarE "z")
              (ListE
                (CaseE
                  (Seq (Atom CONST) Arg Arg)
                  (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
                )
                (CaseE
                  (Seq (Atom CONST) Arg Arg)
                  (TupE (CallE "valtype_Inn" (ExpA (VarE "v_Inn"))) (VarE "c"))
                )
                (CaseE
                  (Seq (Atom STORE) Arg Arg Arg)
                  (TupE
                    (CallE "valtype_Inn" (ExpA (VarE "v_Inn")))
                    (OptE (CaseE (Seq (Atom mk_sz) Arg) (TupE (VarE "v_n"))))
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
          (CaseE (Seq (Atom mk_config) Arg Arg) (TupE (VarE "var_0") (ListE)))
        )
      )
    )
    (RuleD
      "memory_grow_succeed"
      (ExpP "z" (VarT "state"))
      (ExpP "v_n" (VarT "n"))
      (ExpP "mi" (VarT "meminst"))
      (ExpP "var_1" (IterT (VarT "meminst") Opt))
      (ExpP "var_0" (VarT "state"))
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
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
                      (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
                    )
                  )
                )
              )
              (CaseE (Atom MEMORY_GROW) (TupE))
            )
          )
        )
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "var_0")
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
                        (Seq (Atom mk_uN) Arg)
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
                                      "fun_mem"
                                      (ExpA (VarE "z"))
                                      (ExpA
                                        (CaseE
                                          (Seq (Atom mk_uN) Arg)
                                          (TupE (NumE (Nat 0)))
                                        )
                                      )
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
      (RulePr
        "fun_growmemory"
        (Seq Arg Arg Arg)
        (TupE
          (CallE
            "fun_mem"
            (ExpA (VarE "z"))
            (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
          )
          (VarE "v_n")
          (VarE "var_1")
        )
      )
      (RulePr
        "fun_with_meminst"
        (Seq Arg Arg Arg Arg)
        (TupE
          (VarE "z")
          (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
          (VarE "mi")
          (VarE "var_0")
        )
      )
      (IfPr (CmpE NeOp bool (VarE "var_1") (OptE)))
      (IfPr (CmpE EqOp bool (TheE (VarE "var_1")) (VarE "mi")))
      (RulePr "wf_meminst" (Seq Arg) (TupE (TheE (VarE "var_1"))))
      (RulePr
        "wf_meminst"
        (Seq Arg)
        (TupE
          (CallE
            "fun_mem"
            (ExpA (VarE "z"))
            (ExpA (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0)))))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
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
                        (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
                      )
                    )
                  )
                )
                (CaseE (Atom MEMORY_GROW) (TupE))
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
            (Seq (Atom mk_config) Arg Arg)
            (TupE
              (VarE "var_0")
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
                          (Seq (Atom mk_uN) Arg)
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
                                        "fun_mem"
                                        (ExpA (VarE "z"))
                                        (ExpA
                                          (CaseE
                                            (Seq (Atom mk_uN) Arg)
                                            (TupE (NumE (Nat 0)))
                                          )
                                        )
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
        (TupE
          (NumE (Nat 32))
          (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 0))))
        )
      )
    )
    (RuleD
      "memory_grow_fail"
      (ExpP "z" (VarT "state"))
      (ExpP "v_n" (VarT "n"))
      (ExpP "var_0" nat)
      (Infix Arg ~> Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
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
                      (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
                    )
                  )
                )
              )
              (CaseE (Atom MEMORY_GROW) (TupE))
            )
          )
        )
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
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
                      (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "var_0")))
                    )
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "fun_inv_signed_"
        (Seq Arg Arg Arg)
        (TupE
          (NumE (Nat 32))
          (UnE MinusOp int (CvtE nat int (NumE (Nat 1))))
          (VarE "var_0")
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
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
                        (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
                      )
                    )
                  )
                )
                (CaseE (Atom MEMORY_GROW) (TupE))
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
            (Seq (Atom mk_config) Arg Arg)
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
                        (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "var_0")))
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
      (ExpP "admininstr_lst" (IterT (VarT "admininstr") List))
      (Infix Arg ~>* Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE (VarE "z") (VarE "admininstr_lst"))
        )
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE (VarE "z") (VarE "admininstr_lst"))
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z") (VarE "admininstr_lst"))
          )
        )
      )
    )
    (RuleD
      "trans"
      (ExpP "z" (VarT "state"))
      (ExpP "admininstr_lst" (IterT (VarT "admininstr") List))
      (ExpP "z''" (VarT "state"))
      (ExpP "admininstr''_lst" (IterT (VarT "admininstr") List))
      (ExpP "z'" (VarT "state"))
      (ExpP "admininstr'_lst" (IterT (VarT "admininstr") List))
      (Infix Arg ~>* Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE (VarE "z") (VarE "admininstr_lst"))
        )
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE (VarE "z''") (VarE "admininstr''_lst"))
        )
      )
      (RulePr
        "Step"
        (Infix Arg ~> Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z") (VarE "admininstr_lst"))
          )
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z'") (VarE "admininstr'_lst"))
          )
        )
      )
      (RulePr
        "Steps"
        (Infix Arg ~>* Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z'") (VarE "admininstr'_lst"))
          )
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z''") (VarE "admininstr''_lst"))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z") (VarE "admininstr_lst"))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z''") (VarE "admininstr''_lst"))
          )
        )
      )
      (RulePr
        "wf_config"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom mk_config) Arg Arg)
            (TupE (VarE "z'") (VarE "admininstr'_lst"))
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
    "mk_Eval_expr"
    (ExpP "z" (VarT "state"))
    (ExpP "instr_lst" (IterT (VarT "instr") List))
    (ExpP "z'" (VarT "state"))
    (ExpP "val_lst" (IterT (VarT "val") List))
    (Infix (Infix Arg ; Arg) ~>* (Infix Arg ; Arg))
    (TupE (VarE "z") (VarE "instr_lst") (VarE "z'") (VarE "val_lst"))
    (RulePr
      "Steps"
      (Infix Arg ~>* Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "z")
            (IterE
              (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
              List
              (iterexp "v_instr" (VarE "instr_lst"))
            )
          )
        )
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "z'")
            (IterE
              (CallE "admininstr_val" (ExpA (VarE "v_val")))
              List
              (iterexp "v_val" (VarE "val_lst"))
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
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "z")
            (IterE
              (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
              List
              (iterexp "v_instr" (VarE "instr_lst"))
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
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (VarE "z'")
            (IterE
              (CallE "admininstr_val" (ExpA (VarE "v_val")))
              List
              (iterexp "v_val" (VarE "val_lst"))
            )
          )
        )
      )
    )
  )
)
(HintD (RelH "Eval_expr" (hint "show" "\"E-expr\"") (hint "tabular" "{}")))
(RecD
  (RelD
    "fun_funcs"
    (Seq Arg Arg)
    (TupT
      (typbind "_" (IterT (VarT "externaddr") List))
      (typbind "_" (IterT (VarT "funcaddr") List))
    )
    (RuleD "fun_funcs_case_0" (Seq Arg Arg) (TupE (ListE) (ListE)))
    (RuleD
      "fun_funcs_case_1"
      (ExpP "fa" nat)
      (ExpP "externaddr'_lst" (IterT (VarT "externaddr") List))
      (ExpP "var_0" (IterT (VarT "funcaddr") List))
      (Seq Arg Arg)
      (TupE
        (CatE
          (ListE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "fa"))))
          (VarE "externaddr'_lst")
        )
        (CatE (ListE (VarE "fa")) (VarE "var_0"))
      )
      (RulePr
        "fun_funcs"
        (Seq Arg Arg)
        (TupE (VarE "externaddr'_lst") (VarE "var_0"))
      )
    )
    (RuleD
      "fun_funcs_case_2"
      (ExpP "v_externaddr" (VarT "externaddr"))
      (ExpP "externaddr'_lst" (IterT (VarT "externaddr") List))
      (ExpP "var_0" (IterT (VarT "funcaddr") List))
      (Seq Arg Arg)
      (TupE
        (CatE (ListE (VarE "v_externaddr")) (VarE "externaddr'_lst"))
        (VarE "var_0")
      )
      (RulePr
        "fun_funcs"
        (Seq Arg Arg)
        (TupE (VarE "externaddr'_lst") (VarE "var_0"))
      )
    )
  )
)
(RecD
  (RelD
    "fun_globals"
    (Seq Arg Arg)
    (TupT
      (typbind "_" (IterT (VarT "externaddr") List))
      (typbind "_" (IterT (VarT "globaladdr") List))
    )
    (RuleD "fun_globals_case_0" (Seq Arg Arg) (TupE (ListE) (ListE)))
    (RuleD
      "fun_globals_case_1"
      (ExpP "ga" nat)
      (ExpP "externaddr'_lst" (IterT (VarT "externaddr") List))
      (ExpP "var_0" (IterT (VarT "globaladdr") List))
      (Seq Arg Arg)
      (TupE
        (CatE
          (ListE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "ga"))))
          (VarE "externaddr'_lst")
        )
        (CatE (ListE (VarE "ga")) (VarE "var_0"))
      )
      (RulePr
        "fun_globals"
        (Seq Arg Arg)
        (TupE (VarE "externaddr'_lst") (VarE "var_0"))
      )
    )
    (RuleD
      "fun_globals_case_2"
      (ExpP "v_externaddr" (VarT "externaddr"))
      (ExpP "externaddr'_lst" (IterT (VarT "externaddr") List))
      (ExpP "var_0" (IterT (VarT "globaladdr") List))
      (Seq Arg Arg)
      (TupE
        (CatE (ListE (VarE "v_externaddr")) (VarE "externaddr'_lst"))
        (VarE "var_0")
      )
      (RulePr
        "fun_globals"
        (Seq Arg Arg)
        (TupE (VarE "externaddr'_lst") (VarE "var_0"))
      )
    )
  )
)
(RecD
  (RelD
    "fun_tables"
    (Seq Arg Arg)
    (TupT
      (typbind "_" (IterT (VarT "externaddr") List))
      (typbind "_" (IterT (VarT "tableaddr") List))
    )
    (RuleD "fun_tables_case_0" (Seq Arg Arg) (TupE (ListE) (ListE)))
    (RuleD
      "fun_tables_case_1"
      (ExpP "ta" nat)
      (ExpP "externaddr'_lst" (IterT (VarT "externaddr") List))
      (ExpP "var_0" (IterT (VarT "tableaddr") List))
      (Seq Arg Arg)
      (TupE
        (CatE
          (ListE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "ta"))))
          (VarE "externaddr'_lst")
        )
        (CatE (ListE (VarE "ta")) (VarE "var_0"))
      )
      (RulePr
        "fun_tables"
        (Seq Arg Arg)
        (TupE (VarE "externaddr'_lst") (VarE "var_0"))
      )
    )
    (RuleD
      "fun_tables_case_2"
      (ExpP "v_externaddr" (VarT "externaddr"))
      (ExpP "externaddr'_lst" (IterT (VarT "externaddr") List))
      (ExpP "var_0" (IterT (VarT "tableaddr") List))
      (Seq Arg Arg)
      (TupE
        (CatE (ListE (VarE "v_externaddr")) (VarE "externaddr'_lst"))
        (VarE "var_0")
      )
      (RulePr
        "fun_tables"
        (Seq Arg Arg)
        (TupE (VarE "externaddr'_lst") (VarE "var_0"))
      )
    )
  )
)
(RecD
  (RelD
    "fun_mems"
    (Seq Arg Arg)
    (TupT
      (typbind "_" (IterT (VarT "externaddr") List))
      (typbind "_" (IterT (VarT "memaddr") List))
    )
    (RuleD "fun_mems_case_0" (Seq Arg Arg) (TupE (ListE) (ListE)))
    (RuleD
      "fun_mems_case_1"
      (ExpP "ma" nat)
      (ExpP "externaddr'_lst" (IterT (VarT "externaddr") List))
      (ExpP "var_0" (IterT (VarT "memaddr") List))
      (Seq Arg Arg)
      (TupE
        (CatE
          (ListE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "ma"))))
          (VarE "externaddr'_lst")
        )
        (CatE (ListE (VarE "ma")) (VarE "var_0"))
      )
      (RulePr
        "fun_mems"
        (Seq Arg Arg)
        (TupE (VarE "externaddr'_lst") (VarE "var_0"))
      )
    )
    (RuleD
      "fun_mems_case_2"
      (ExpP "v_externaddr" (VarT "externaddr"))
      (ExpP "externaddr'_lst" (IterT (VarT "externaddr") List))
      (ExpP "var_0" (IterT (VarT "memaddr") List))
      (Seq Arg Arg)
      (TupE
        (CatE (ListE (VarE "v_externaddr")) (VarE "externaddr'_lst"))
        (VarE "var_0")
      )
      (RulePr
        "fun_mems"
        (Seq Arg Arg)
        (TupE (VarE "externaddr'_lst") (VarE "var_0"))
      )
    )
  )
)
(RelD
  "fun_allocfunc"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "moduleinst"))
    (typbind "_" (VarT "func"))
    (typbind
      "_"
      (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "funcaddr")))
    )
  )
  (RuleD
    "fun_allocfunc_case_0"
    (ExpP "s" (VarT "store"))
    (ExpP "v_moduleinst" (VarT "moduleinst"))
    (ExpP "v_func" (VarT "func"))
    (ExpP "fi" (VarT "funcinst"))
    (ExpP "x" (VarT "uN"))
    (ExpP "local_lst" (IterT (VarT "local") List))
    (ExpP "v_expr" (IterT (VarT "instr") List))
    (Seq Arg Arg Arg Arg)
    (TupE
      (VarE "s")
      (VarE "v_moduleinst")
      (VarE "v_func")
      (TupE
        (ExtE (VarE "s") (DotP RootP (Atom FUNCS)) (ListE (VarE "fi")))
        (LenE (DotE (VarE "s") (Atom FUNCS)))
      )
    )
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (DotE (VarE "v_moduleinst") (Atom TYPES)))
      )
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
              (DotE (VarE "v_moduleinst") (Atom TYPES))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
            )
          )
          (expfield (Atom MODULE) (VarE "v_moduleinst"))
          (expfield (Atom CODE) (VarE "v_func"))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "v_func")
        (CaseE
          (Seq (Atom FUNC) Arg Arg Arg)
          (TupE (VarE "x") (VarE "local_lst") (VarE "v_expr"))
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
              (DotE (VarE "v_moduleinst") (Atom TYPES))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
            )
          )
          (expfield (Atom MODULE) (VarE "v_moduleinst"))
          (expfield (Atom CODE) (VarE "v_func"))
        )
      )
    )
    (RulePr
      "wf_func"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom FUNC) Arg Arg Arg)
          (TupE (VarE "x") (VarE "local_lst") (VarE "v_expr"))
        )
      )
    )
  )
)
(RecD
  (RelD
    "fun_allocfuncs"
    (Seq Arg Arg Arg Arg)
    (TupT
      (typbind "_" (VarT "store"))
      (typbind "_" (VarT "moduleinst"))
      (typbind "_" (IterT (VarT "func") List))
      (typbind
        "_"
        (TupT
          (typbind "_" (VarT "store"))
          (typbind "_" (IterT (VarT "funcaddr") List))
        )
      )
    )
    (RuleD
      "fun_allocfuncs_case_0"
      (ExpP "s" (VarT "store"))
      (ExpP "v_moduleinst" (VarT "moduleinst"))
      (Seq Arg Arg Arg Arg)
      (TupE (VarE "s") (VarE "v_moduleinst") (ListE) (TupE (VarE "s") (ListE)))
    )
    (RuleD
      "fun_allocfuncs_case_1"
      (ExpP "s" (VarT "store"))
      (ExpP "v_moduleinst" (VarT "moduleinst"))
      (ExpP "v_func" (VarT "func"))
      (ExpP "func'_lst" (IterT (VarT "func") List))
      (ExpP "fa" (VarT "funcaddr"))
      (ExpP "s_1" (VarT "store"))
      (ExpP "s_2" (VarT "store"))
      (ExpP "fa'_lst" (IterT (VarT "funcaddr") List))
      (ExpP
        "var_2"
        (TupT
          (typbind "_" (VarT "store"))
          (typbind "_" (IterT (VarT "funcaddr") List))
        )
      )
      (ExpP
        "var_1"
        (TupT
          (typbind "_" (VarT "store"))
          (typbind "_" (IterT (VarT "funcaddr") List))
        )
      )
      (ExpP
        "var_0"
        (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "funcaddr")))
      )
      (Seq Arg Arg Arg Arg)
      (TupE
        (VarE "s")
        (VarE "v_moduleinst")
        (CatE (ListE (VarE "v_func")) (VarE "func'_lst"))
        (TupE (VarE "s_2") (CatE (ListE (VarE "fa")) (VarE "fa'_lst")))
      )
      (RulePr
        "fun_allocfuncs"
        (Seq Arg Arg Arg Arg)
        (TupE
          (VarE "s_1")
          (VarE "v_moduleinst")
          (VarE "func'_lst")
          (VarE "var_2")
        )
      )
      (RulePr
        "fun_allocfuncs"
        (Seq Arg Arg Arg Arg)
        (TupE
          (VarE "s_1")
          (VarE "v_moduleinst")
          (VarE "func'_lst")
          (VarE "var_1")
        )
      )
      (RulePr
        "fun_allocfunc"
        (Seq Arg Arg Arg Arg)
        (TupE (VarE "s") (VarE "v_moduleinst") (VarE "v_func") (VarE "var_0"))
      )
      (IfPr (CmpE EqOp bool (TupE (VarE "s_1") (VarE "fa")) (VarE "var_0")))
      (IfPr
        (CmpE EqOp bool (TupE (VarE "s_2") (VarE "fa'_lst")) (VarE "var_1"))
      )
      (RulePr "wf_store" (Seq Arg) (TupE (ProjE (VarE "var_0") 0)))
      (RulePr "wf_store" (Seq Arg) (TupE (ProjE (VarE "var_2") 0)))
    )
  )
)
(RelD
  "fun_allocglobal"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "globaltype"))
    (typbind "_" (VarT "val"))
    (typbind
      "_"
      (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "globaladdr")))
    )
  )
  (RuleD
    "fun_allocglobal_case_0"
    (ExpP "s" (VarT "store"))
    (ExpP "v_globaltype" (VarT "globaltype"))
    (ExpP "v_val" (VarT "val"))
    (ExpP "gi" (VarT "globalinst"))
    (Seq Arg Arg Arg Arg)
    (TupE
      (VarE "s")
      (VarE "v_globaltype")
      (VarE "v_val")
      (TupE
        (ExtE (VarE "s") (DotP RootP (Atom GLOBALS)) (ListE (VarE "gi")))
        (LenE (DotE (VarE "s") (Atom GLOBALS)))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "gi")
        (StrE
          (expfield (Atom TYPE) (VarE "v_globaltype"))
          (expfield (Atom VALUE) (VarE "v_val"))
        )
      )
    )
    (RulePr "wf_globalinst" (Seq Arg) (TupE (VarE "gi")))
    (RulePr
      "wf_globalinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom TYPE) (VarE "v_globaltype"))
          (expfield (Atom VALUE) (VarE "v_val"))
        )
      )
    )
  )
)
(RecD
  (RelD
    "fun_allocglobals"
    (Seq Arg Arg Arg Arg)
    (TupT
      (typbind "_" (VarT "store"))
      (typbind "_" (IterT (VarT "globaltype") List))
      (typbind "_" (IterT (VarT "val") List))
      (typbind
        "_"
        (TupT
          (typbind "_" (VarT "store"))
          (typbind "_" (IterT (VarT "globaladdr") List))
        )
      )
    )
    (RuleD
      "fun_allocglobals_case_0"
      (ExpP "s" (VarT "store"))
      (Seq Arg Arg Arg Arg)
      (TupE (VarE "s") (ListE) (ListE) (TupE (VarE "s") (ListE)))
    )
    (RuleD
      "fun_allocglobals_case_1"
      (ExpP "s" (VarT "store"))
      (ExpP "v_globaltype" (VarT "globaltype"))
      (ExpP "globaltype'_lst" (IterT (VarT "globaltype") List))
      (ExpP "v_val" (VarT "val"))
      (ExpP "val'_lst" (IterT (VarT "val") List))
      (ExpP "ga" (VarT "globaladdr"))
      (ExpP "s_1" (VarT "store"))
      (ExpP "s_2" (VarT "store"))
      (ExpP "ga'_lst" (IterT (VarT "globaladdr") List))
      (ExpP
        "var_2"
        (TupT
          (typbind "_" (VarT "store"))
          (typbind "_" (IterT (VarT "globaladdr") List))
        )
      )
      (ExpP
        "var_1"
        (TupT
          (typbind "_" (VarT "store"))
          (typbind "_" (IterT (VarT "globaladdr") List))
        )
      )
      (ExpP
        "var_0"
        (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "globaladdr")))
      )
      (Seq Arg Arg Arg Arg)
      (TupE
        (VarE "s")
        (CatE (ListE (VarE "v_globaltype")) (VarE "globaltype'_lst"))
        (CatE (ListE (VarE "v_val")) (VarE "val'_lst"))
        (TupE (VarE "s_2") (CatE (ListE (VarE "ga")) (VarE "ga'_lst")))
      )
      (RulePr
        "fun_allocglobals"
        (Seq Arg Arg Arg Arg)
        (TupE
          (VarE "s_1")
          (VarE "globaltype'_lst")
          (VarE "val'_lst")
          (VarE "var_2")
        )
      )
      (RulePr
        "fun_allocglobals"
        (Seq Arg Arg Arg Arg)
        (TupE
          (VarE "s_1")
          (VarE "globaltype'_lst")
          (VarE "val'_lst")
          (VarE "var_1")
        )
      )
      (RulePr
        "fun_allocglobal"
        (Seq Arg Arg Arg Arg)
        (TupE (VarE "s") (VarE "v_globaltype") (VarE "v_val") (VarE "var_0"))
      )
      (IfPr (CmpE EqOp bool (TupE (VarE "s_1") (VarE "ga")) (VarE "var_0")))
      (IfPr
        (CmpE EqOp bool (TupE (VarE "s_2") (VarE "ga'_lst")) (VarE "var_1"))
      )
      (RulePr "wf_store" (Seq Arg) (TupE (ProjE (VarE "var_0") 0)))
      (RulePr "wf_store" (Seq Arg) (TupE (ProjE (VarE "var_2") 0)))
    )
  )
)
(RelD
  "fun_alloctable"
  (Seq Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "tabletype"))
    (typbind
      "_"
      (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "tableaddr")))
    )
  )
  (RuleD
    "fun_alloctable_case_0"
    (ExpP "s" (VarT "store"))
    (ExpP "i" (VarT "uN"))
    (ExpP "j_opt" (IterT (VarT "u32") Opt))
    (ExpP "ti" (VarT "tableinst"))
    (Seq Arg Arg Arg)
    (TupE
      (VarE "s")
      (CaseE (Seq (Atom mk_limits) Arg Arg) (TupE (VarE "i") (VarE "j_opt")))
      (TupE
        (ExtE (VarE "s") (DotP RootP (Atom TABLES)) (ListE (VarE "ti")))
        (LenE (DotE (VarE "s") (Atom TABLES)))
      )
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE (VarE "i") (VarE "j_opt"))
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE (VarE "i") (VarE "j_opt"))
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
  (RelD
    "fun_alloctables"
    (Seq Arg Arg Arg)
    (TupT
      (typbind "_" (VarT "store"))
      (typbind "_" (IterT (VarT "tabletype") List))
      (typbind
        "_"
        (TupT
          (typbind "_" (VarT "store"))
          (typbind "_" (IterT (VarT "tableaddr") List))
        )
      )
    )
    (RuleD
      "fun_alloctables_case_0"
      (ExpP "s" (VarT "store"))
      (Seq Arg Arg Arg)
      (TupE (VarE "s") (ListE) (TupE (VarE "s") (ListE)))
    )
    (RuleD
      "fun_alloctables_case_1"
      (ExpP "s" (VarT "store"))
      (ExpP "v_tabletype" (VarT "limits"))
      (ExpP "tabletype'_lst" (IterT (VarT "tabletype") List))
      (ExpP "ta" (VarT "tableaddr"))
      (ExpP "s_1" (VarT "store"))
      (ExpP "s_2" (VarT "store"))
      (ExpP "ta'_lst" (IterT (VarT "tableaddr") List))
      (ExpP
        "var_2"
        (TupT
          (typbind "_" (VarT "store"))
          (typbind "_" (IterT (VarT "tableaddr") List))
        )
      )
      (ExpP
        "var_1"
        (TupT
          (typbind "_" (VarT "store"))
          (typbind "_" (IterT (VarT "tableaddr") List))
        )
      )
      (ExpP
        "var_0"
        (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "tableaddr")))
      )
      (Seq Arg Arg Arg)
      (TupE
        (VarE "s")
        (CatE (ListE (VarE "v_tabletype")) (VarE "tabletype'_lst"))
        (TupE (VarE "s_2") (CatE (ListE (VarE "ta")) (VarE "ta'_lst")))
      )
      (RulePr
        "fun_alloctables"
        (Seq Arg Arg Arg)
        (TupE (VarE "s_1") (VarE "tabletype'_lst") (VarE "var_2"))
      )
      (RulePr
        "fun_alloctables"
        (Seq Arg Arg Arg)
        (TupE (VarE "s_1") (VarE "tabletype'_lst") (VarE "var_1"))
      )
      (RulePr
        "fun_alloctable"
        (Seq Arg Arg Arg)
        (TupE (VarE "s") (VarE "v_tabletype") (VarE "var_0"))
      )
      (IfPr (CmpE EqOp bool (TupE (VarE "s_1") (VarE "ta")) (VarE "var_0")))
      (IfPr
        (CmpE EqOp bool (TupE (VarE "s_2") (VarE "ta'_lst")) (VarE "var_1"))
      )
      (RulePr "wf_store" (Seq Arg) (TupE (ProjE (VarE "var_0") 0)))
      (RulePr "wf_store" (Seq Arg) (TupE (ProjE (VarE "var_2") 0)))
    )
  )
)
(RelD
  "fun_allocmem"
  (Seq Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "memtype"))
    (typbind
      "_"
      (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "memaddr")))
    )
  )
  (RuleD
    "fun_allocmem_case_0"
    (ExpP "s" (VarT "store"))
    (ExpP "i" (VarT "uN"))
    (ExpP "j_opt" (IterT (VarT "u32") Opt))
    (ExpP "mi" (VarT "meminst"))
    (Seq Arg Arg Arg)
    (TupE
      (VarE "s")
      (CaseE (Seq (Atom mk_limits) Arg Arg) (TupE (VarE "i") (VarE "j_opt")))
      (TupE
        (ExtE (VarE "s") (DotP RootP (Atom MEMS)) (ListE (VarE "mi")))
        (LenE (DotE (VarE "s") (Atom MEMS)))
      )
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE (VarE "i") (VarE "j_opt"))
            )
          )
          (expfield
            (Atom BYTES)
            (IterE
              (CaseE (Seq (Atom mk_byte) Arg) (TupE (NumE (Nat 0))))
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE (VarE "i") (VarE "j_opt"))
            )
          )
          (expfield
            (Atom BYTES)
            (IterE
              (CaseE (Seq (Atom mk_byte) Arg) (TupE (NumE (Nat 0))))
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
  (RelD
    "fun_allocmems"
    (Seq Arg Arg Arg)
    (TupT
      (typbind "_" (VarT "store"))
      (typbind "_" (IterT (VarT "memtype") List))
      (typbind
        "_"
        (TupT
          (typbind "_" (VarT "store"))
          (typbind "_" (IterT (VarT "memaddr") List))
        )
      )
    )
    (RuleD
      "fun_allocmems_case_0"
      (ExpP "s" (VarT "store"))
      (Seq Arg Arg Arg)
      (TupE (VarE "s") (ListE) (TupE (VarE "s") (ListE)))
    )
    (RuleD
      "fun_allocmems_case_1"
      (ExpP "s" (VarT "store"))
      (ExpP "v_memtype" (VarT "limits"))
      (ExpP "memtype'_lst" (IterT (VarT "memtype") List))
      (ExpP "ma" (VarT "memaddr"))
      (ExpP "s_1" (VarT "store"))
      (ExpP "s_2" (VarT "store"))
      (ExpP "ma'_lst" (IterT (VarT "memaddr") List))
      (ExpP
        "var_2"
        (TupT
          (typbind "_" (VarT "store"))
          (typbind "_" (IterT (VarT "memaddr") List))
        )
      )
      (ExpP
        "var_1"
        (TupT
          (typbind "_" (VarT "store"))
          (typbind "_" (IterT (VarT "memaddr") List))
        )
      )
      (ExpP
        "var_0"
        (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "memaddr")))
      )
      (Seq Arg Arg Arg)
      (TupE
        (VarE "s")
        (CatE (ListE (VarE "v_memtype")) (VarE "memtype'_lst"))
        (TupE (VarE "s_2") (CatE (ListE (VarE "ma")) (VarE "ma'_lst")))
      )
      (RulePr
        "fun_allocmems"
        (Seq Arg Arg Arg)
        (TupE (VarE "s_1") (VarE "memtype'_lst") (VarE "var_2"))
      )
      (RulePr
        "fun_allocmems"
        (Seq Arg Arg Arg)
        (TupE (VarE "s_1") (VarE "memtype'_lst") (VarE "var_1"))
      )
      (RulePr
        "fun_allocmem"
        (Seq Arg Arg Arg)
        (TupE (VarE "s") (VarE "v_memtype") (VarE "var_0"))
      )
      (IfPr (CmpE EqOp bool (TupE (VarE "s_1") (VarE "ma")) (VarE "var_0")))
      (IfPr
        (CmpE EqOp bool (TupE (VarE "s_2") (VarE "ma'_lst")) (VarE "var_1"))
      )
      (RulePr "wf_store" (Seq Arg) (TupE (ProjE (VarE "var_0") 0)))
      (RulePr "wf_store" (Seq Arg) (TupE (ProjE (VarE "var_2") 0)))
    )
  )
)
(RelD
  "fun_instexport"
  (Seq Arg Arg Arg Arg Arg Arg)
  (TupT
    (typbind "_" (IterT (VarT "funcaddr") List))
    (typbind "_" (IterT (VarT "globaladdr") List))
    (typbind "_" (IterT (VarT "tableaddr") List))
    (typbind "_" (IterT (VarT "memaddr") List))
    (typbind "_" (VarT "export"))
    (typbind "_" (VarT "exportinst"))
  )
  (RuleD
    "fun_instexport_case_0"
    (ExpP "fa_lst" (IterT (VarT "funcaddr") List))
    (ExpP "ga_lst" (IterT (VarT "globaladdr") List))
    (ExpP "ta_lst" (IterT (VarT "tableaddr") List))
    (ExpP "ma_lst" (IterT (VarT "memaddr") List))
    (ExpP "v_name" (VarT "name"))
    (ExpP "x" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg Arg)
    (TupE
      (VarE "fa_lst")
      (VarE "ga_lst")
      (VarE "ta_lst")
      (VarE "ma_lst")
      (CaseE
        (Seq (Atom EXPORT) Arg Arg)
        (TupE (VarE "v_name") (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "x"))))
      )
      (StrE
        (expfield (Atom NAME) (VarE "v_name"))
        (expfield
          (Atom ADDR)
          (CaseE
            (Seq (Atom FUNC) Arg)
            (TupE
              (IdxE
                (VarE "fa_lst")
                (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
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
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (VarE "fa_lst"))
      )
    )
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (VarE "fa_lst"))
      )
    )
    (RulePr
      "wf_exportinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom NAME) (VarE "v_name"))
          (expfield
            (Atom ADDR)
            (CaseE
              (Seq (Atom FUNC) Arg)
              (TupE
                (IdxE
                  (VarE "fa_lst")
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
                )
              )
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_instexport_case_1"
    (ExpP "fa_lst" (IterT (VarT "funcaddr") List))
    (ExpP "ga_lst" (IterT (VarT "globaladdr") List))
    (ExpP "ta_lst" (IterT (VarT "tableaddr") List))
    (ExpP "ma_lst" (IterT (VarT "memaddr") List))
    (ExpP "v_name" (VarT "name"))
    (ExpP "x" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg Arg)
    (TupE
      (VarE "fa_lst")
      (VarE "ga_lst")
      (VarE "ta_lst")
      (VarE "ma_lst")
      (CaseE
        (Seq (Atom EXPORT) Arg Arg)
        (TupE (VarE "v_name") (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "x"))))
      )
      (StrE
        (expfield (Atom NAME) (VarE "v_name"))
        (expfield
          (Atom ADDR)
          (CaseE
            (Seq (Atom GLOBAL) Arg)
            (TupE
              (IdxE
                (VarE "ga_lst")
                (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
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
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (VarE "ga_lst"))
      )
    )
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (VarE "ga_lst"))
      )
    )
    (RulePr
      "wf_exportinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom NAME) (VarE "v_name"))
          (expfield
            (Atom ADDR)
            (CaseE
              (Seq (Atom GLOBAL) Arg)
              (TupE
                (IdxE
                  (VarE "ga_lst")
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
                )
              )
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_instexport_case_2"
    (ExpP "fa_lst" (IterT (VarT "funcaddr") List))
    (ExpP "ga_lst" (IterT (VarT "globaladdr") List))
    (ExpP "ta_lst" (IterT (VarT "tableaddr") List))
    (ExpP "ma_lst" (IterT (VarT "memaddr") List))
    (ExpP "v_name" (VarT "name"))
    (ExpP "x" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg Arg)
    (TupE
      (VarE "fa_lst")
      (VarE "ga_lst")
      (VarE "ta_lst")
      (VarE "ma_lst")
      (CaseE
        (Seq (Atom EXPORT) Arg Arg)
        (TupE (VarE "v_name") (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "x"))))
      )
      (StrE
        (expfield (Atom NAME) (VarE "v_name"))
        (expfield
          (Atom ADDR)
          (CaseE
            (Seq (Atom TABLE) Arg)
            (TupE
              (IdxE
                (VarE "ta_lst")
                (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
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
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (VarE "ta_lst"))
      )
    )
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (VarE "ta_lst"))
      )
    )
    (RulePr
      "wf_exportinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom NAME) (VarE "v_name"))
          (expfield
            (Atom ADDR)
            (CaseE
              (Seq (Atom TABLE) Arg)
              (TupE
                (IdxE
                  (VarE "ta_lst")
                  (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
                )
              )
            )
          )
        )
      )
    )
  )
  (RuleD
    "fun_instexport_case_3"
    (ExpP "fa_lst" (IterT (VarT "funcaddr") List))
    (ExpP "ga_lst" (IterT (VarT "globaladdr") List))
    (ExpP "ta_lst" (IterT (VarT "tableaddr") List))
    (ExpP "ma_lst" (IterT (VarT "memaddr") List))
    (ExpP "v_name" (VarT "name"))
    (ExpP "x" (VarT "uN"))
    (Seq Arg Arg Arg Arg Arg Arg)
    (TupE
      (VarE "fa_lst")
      (VarE "ga_lst")
      (VarE "ta_lst")
      (VarE "ma_lst")
      (CaseE
        (Seq (Atom EXPORT) Arg Arg)
        (TupE (VarE "v_name") (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "x"))))
      )
      (StrE
        (expfield (Atom NAME) (VarE "v_name"))
        (expfield
          (Atom ADDR)
          (CaseE
            (Seq (Atom MEM) Arg)
            (TupE
              (IdxE
                (VarE "ma_lst")
                (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
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
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (VarE "ma_lst"))
      )
    )
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (CallE "proj_uN_0" (ExpA (VarE "x"))) 0)
        (LenE (VarE "ma_lst"))
      )
    )
    (RulePr
      "wf_exportinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom NAME) (VarE "v_name"))
          (expfield
            (Atom ADDR)
            (CaseE
              (Seq (Atom MEM) Arg)
              (TupE
                (IdxE
                  (VarE "ma_lst")
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
(RelD
  "fun_allocmodule"
  (Seq Arg Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "module"))
    (typbind "_" (IterT (VarT "externaddr") List))
    (typbind "_" (IterT (VarT "val") List))
    (typbind
      "_"
      (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "moduleinst")))
    )
  )
  (RuleD
    "fun_allocmodule_case_0"
    (ExpP "s" (VarT "store"))
    (ExpP "v_module" (VarT "module"))
    (ExpP "externaddr_lst" (IterT (VarT "externaddr") List))
    (ExpP "val_lst" (IterT (VarT "val") List))
    (ExpP "s_4" (VarT "store"))
    (ExpP "v_moduleinst" (VarT "moduleinst"))
    (ExpP "ft_lst" (IterT (VarT "functype") List))
    (ExpP "import_lst" (IterT (VarT "import") List))
    (ExpP "n_func" nat)
    (ExpP "func_lst" (IterT (VarT "func") List))
    (ExpP "n_global" nat)
    (ExpP "expr_1_lst" (IterT (VarT "expr") List))
    (ExpP "globaltype_lst" (IterT (VarT "globaltype") List))
    (ExpP "n_table" nat)
    (ExpP "tabletype_lst" (IterT (VarT "tabletype") List))
    (ExpP "n_mem" nat)
    (ExpP "memtype_lst" (IterT (VarT "memtype") List))
    (ExpP "elem_lst" (IterT (VarT "elem") List))
    (ExpP "data_lst" (IterT (VarT "data") List))
    (ExpP "start_opt" (IterT (VarT "start") Opt))
    (ExpP "export_lst" (IterT (VarT "export") List))
    (ExpP "s_1" (VarT "store"))
    (ExpP "s_2" (VarT "store"))
    (ExpP "s_3" (VarT "store"))
    (ExpP "fa_ex_lst" (IterT (VarT "funcaddr") List))
    (ExpP "ga_ex_lst" (IterT (VarT "globaladdr") List))
    (ExpP "ta_ex_lst" (IterT (VarT "tableaddr") List))
    (ExpP "ma_ex_lst" (IterT (VarT "memaddr") List))
    (ExpP "fa_lst" (IterT (VarT "funcaddr") List))
    (ExpP "ga_lst" (IterT (VarT "globaladdr") List))
    (ExpP "ta_lst" (IterT (VarT "tableaddr") List))
    (ExpP "ma_lst" (IterT (VarT "memaddr") List))
    (ExpP "xi_lst" (IterT (VarT "exportinst") List))
    (ExpP
      "var_13"
      (TupT
        (typbind "_" (VarT "store"))
        (typbind "_" (IterT (VarT "memaddr") List))
      )
    )
    (ExpP
      "var_12"
      (TupT
        (typbind "_" (VarT "store"))
        (typbind "_" (IterT (VarT "tableaddr") List))
      )
    )
    (ExpP
      "var_11"
      (TupT
        (typbind "_" (VarT "store"))
        (typbind "_" (IterT (VarT "globaladdr") List))
      )
    )
    (ExpP
      "var_10"
      (TupT
        (typbind "_" (VarT "store"))
        (typbind "_" (IterT (VarT "funcaddr") List))
      )
    )
    (ExpP "var_9_lst" (IterT (VarT "exportinst") List))
    (ExpP
      "var_8"
      (TupT
        (typbind "_" (VarT "store"))
        (typbind "_" (IterT (VarT "memaddr") List))
      )
    )
    (ExpP
      "var_7"
      (TupT
        (typbind "_" (VarT "store"))
        (typbind "_" (IterT (VarT "tableaddr") List))
      )
    )
    (ExpP
      "var_6"
      (TupT
        (typbind "_" (VarT "store"))
        (typbind "_" (IterT (VarT "globaladdr") List))
      )
    )
    (ExpP
      "var_5"
      (TupT
        (typbind "_" (VarT "store"))
        (typbind "_" (IterT (VarT "funcaddr") List))
      )
    )
    (ExpP "var_4_lst" (IterT (VarT "exportinst") List))
    (ExpP "var_3" (IterT (VarT "memaddr") List))
    (ExpP "var_2" (IterT (VarT "tableaddr") List))
    (ExpP "var_1" (IterT (VarT "globaladdr") List))
    (ExpP "var_0" (IterT (VarT "funcaddr") List))
    (Seq Arg Arg Arg Arg Arg)
    (TupE
      (VarE "s")
      (VarE "v_module")
      (VarE "externaddr_lst")
      (VarE "val_lst")
      (TupE (VarE "s_4") (VarE "v_moduleinst"))
    )
    (RulePr
      "fun_allocmems"
      (Seq Arg Arg Arg)
      (TupE (VarE "s_3") (VarE "memtype_lst") (VarE "var_13"))
    )
    (RulePr
      "fun_alloctables"
      (Seq Arg Arg Arg)
      (TupE (VarE "s_2") (VarE "tabletype_lst") (VarE "var_12"))
    )
    (RulePr
      "fun_allocglobals"
      (Seq Arg Arg Arg Arg)
      (TupE
        (VarE "s_1")
        (VarE "globaltype_lst")
        (VarE "val_lst")
        (VarE "var_11")
      )
    )
    (RulePr
      "fun_allocfuncs"
      (Seq Arg Arg Arg Arg)
      (TupE (VarE "s") (VarE "v_moduleinst") (VarE "func_lst") (VarE "var_10"))
    )
    (IfPr (CmpE EqOp bool (LenE (VarE "var_9_lst")) (LenE (VarE "export_lst"))))
    (IterPr
      (RulePr
        "fun_instexport"
        (Seq Arg Arg Arg Arg Arg Arg)
        (TupE
          (CatE (VarE "fa_ex_lst") (VarE "fa_lst"))
          (CatE (VarE "ga_ex_lst") (VarE "ga_lst"))
          (CatE (VarE "ta_ex_lst") (VarE "ta_lst"))
          (CatE (VarE "ma_ex_lst") (VarE "ma_lst"))
          (VarE "export_3")
          (VarE "var_9")
        )
      )
      List
      (iterexp "var_9" (VarE "var_9_lst"))
      (iterexp "export_3" (VarE "export_lst"))
    )
    (RulePr
      "fun_allocmems"
      (Seq Arg Arg Arg)
      (TupE (VarE "s_3") (VarE "memtype_lst") (VarE "var_8"))
    )
    (RulePr
      "fun_alloctables"
      (Seq Arg Arg Arg)
      (TupE (VarE "s_2") (VarE "tabletype_lst") (VarE "var_7"))
    )
    (RulePr
      "fun_allocglobals"
      (Seq Arg Arg Arg Arg)
      (TupE
        (VarE "s_1")
        (VarE "globaltype_lst")
        (VarE "val_lst")
        (VarE "var_6")
      )
    )
    (RulePr
      "fun_allocfuncs"
      (Seq Arg Arg Arg Arg)
      (TupE (VarE "s") (VarE "v_moduleinst") (VarE "func_lst") (VarE "var_5"))
    )
    (IfPr (CmpE EqOp bool (LenE (VarE "var_4_lst")) (LenE (VarE "export_lst"))))
    (IterPr
      (RulePr
        "fun_instexport"
        (Seq Arg Arg Arg Arg Arg Arg)
        (TupE
          (CatE (VarE "fa_ex_lst") (VarE "fa_lst"))
          (CatE (VarE "ga_ex_lst") (VarE "ga_lst"))
          (CatE (VarE "ta_ex_lst") (VarE "ta_lst"))
          (CatE (VarE "ma_ex_lst") (VarE "ma_lst"))
          (VarE "export_2")
          (VarE "var_4")
        )
      )
      List
      (iterexp "var_4" (VarE "var_4_lst"))
      (iterexp "export_2" (VarE "export_lst"))
    )
    (RulePr
      "fun_mems"
      (Seq Arg Arg)
      (TupE (VarE "externaddr_lst") (VarE "var_3"))
    )
    (RulePr
      "fun_tables"
      (Seq Arg Arg)
      (TupE (VarE "externaddr_lst") (VarE "var_2"))
    )
    (RulePr
      "fun_globals"
      (Seq Arg Arg)
      (TupE (VarE "externaddr_lst") (VarE "var_1"))
    )
    (RulePr
      "fun_funcs"
      (Seq Arg Arg)
      (TupE (VarE "externaddr_lst") (VarE "var_0"))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "v_module")
        (CaseE
          (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
          (TupE
            (IterE
              (CaseE (Seq (Atom TYPE) Arg) (TupE (VarE "ft_1")))
              List
              (iterexp "ft_1" (VarE "ft_lst"))
            )
            (VarE "import_lst")
            (VarE "func_lst")
            (IterE
              (CaseE
                (Seq (Atom GLOBAL) Arg Arg)
                (TupE (VarE "globaltype_195") (VarE "expr_1_1"))
              )
              (ListN (VarE "n_global"))
              (iterexp "expr_1_1" (VarE "expr_1_lst"))
              (iterexp "globaltype_195" (VarE "globaltype_lst"))
            )
            (IterE
              (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tabletype_241")))
              (ListN (VarE "n_table"))
              (iterexp "tabletype_241" (VarE "tabletype_lst"))
            )
            (IterE
              (CaseE (Seq (Atom MEMORY) Arg) (TupE (VarE "memtype_293")))
              (ListN (VarE "n_mem"))
              (iterexp "memtype_293" (VarE "memtype_lst"))
            )
            (VarE "elem_lst")
            (VarE "data_lst")
            (VarE "start_opt")
            (VarE "export_lst")
          )
        )
      )
    )
    (IfPr (CmpE EqOp bool (VarE "fa_ex_lst") (VarE "var_0")))
    (IfPr (CmpE EqOp bool (VarE "ga_ex_lst") (VarE "var_1")))
    (IfPr (CmpE EqOp bool (VarE "ta_ex_lst") (VarE "var_2")))
    (IfPr (CmpE EqOp bool (VarE "ma_ex_lst") (VarE "var_3")))
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "fa_lst")
        (IterE
          (BinE
            AddOp
            nat
            (LenE (DotE (VarE "s") (Atom FUNCS)))
            (VarE "i_func_1")
          )
          (ListN (VarE "n_func") "i_func_1")
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "ga_lst")
        (IterE
          (BinE
            AddOp
            nat
            (LenE (DotE (VarE "s") (Atom GLOBALS)))
            (VarE "i_global_1")
          )
          (ListN (VarE "n_global") "i_global_1")
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "ta_lst")
        (IterE
          (BinE
            AddOp
            nat
            (LenE (DotE (VarE "s") (Atom TABLES)))
            (VarE "i_table_1")
          )
          (ListN (VarE "n_table") "i_table_1")
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "ma_lst")
        (IterE
          (BinE AddOp nat (LenE (DotE (VarE "s") (Atom MEMS))) (VarE "i_mem_1"))
          (ListN (VarE "n_mem") "i_mem_1")
        )
      )
    )
    (IfPr (CmpE EqOp bool (VarE "xi_lst") (VarE "var_4_lst")))
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "v_moduleinst")
        (StrE
          (expfield (Atom TYPES) (VarE "ft_lst"))
          (expfield (Atom FUNCS) (CatE (VarE "fa_ex_lst") (VarE "fa_lst")))
          (expfield (Atom GLOBALS) (CatE (VarE "ga_ex_lst") (VarE "ga_lst")))
          (expfield (Atom TABLES) (CatE (VarE "ta_ex_lst") (VarE "ta_lst")))
          (expfield (Atom MEMS) (CatE (VarE "ma_ex_lst") (VarE "ma_lst")))
          (expfield (Atom EXPORTS) (VarE "xi_lst"))
        )
      )
    )
    (IfPr (CmpE EqOp bool (TupE (VarE "s_1") (VarE "fa_lst")) (VarE "var_5")))
    (IfPr (CmpE EqOp bool (TupE (VarE "s_2") (VarE "ga_lst")) (VarE "var_6")))
    (IfPr (CmpE EqOp bool (TupE (VarE "s_3") (VarE "ta_lst")) (VarE "var_7")))
    (IfPr (CmpE EqOp bool (TupE (VarE "s_4") (VarE "ma_lst")) (VarE "var_8")))
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s_4")))
    (RulePr "wf_moduleinst" (Seq Arg) (TupE (VarE "v_moduleinst")))
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s_1")))
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s_2")))
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s_3")))
    (IterPr
      (RulePr "wf_exportinst" (Seq Arg) (TupE (VarE "var_9")))
      List
      (iterexp "var_9" (VarE "var_9_lst"))
    )
    (RulePr "wf_store" (Seq Arg) (TupE (ProjE (VarE "var_10") 0)))
    (RulePr "wf_store" (Seq Arg) (TupE (ProjE (VarE "var_11") 0)))
    (RulePr "wf_store" (Seq Arg) (TupE (ProjE (VarE "var_12") 0)))
    (RulePr "wf_store" (Seq Arg) (TupE (ProjE (VarE "var_13") 0)))
    (RulePr
      "wf_module"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
          (TupE
            (IterE
              (CaseE (Seq (Atom TYPE) Arg) (TupE (VarE "ft_3")))
              List
              (iterexp "ft_3" (VarE "ft_lst"))
            )
            (VarE "import_lst")
            (VarE "func_lst")
            (IterE
              (CaseE
                (Seq (Atom GLOBAL) Arg Arg)
                (TupE (VarE "globaltype_199") (VarE "expr_1_2"))
              )
              (ListN (VarE "n_global"))
              (iterexp "expr_1_2" (VarE "expr_1_lst"))
              (iterexp "globaltype_199" (VarE "globaltype_lst"))
            )
            (IterE
              (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tabletype_245")))
              (ListN (VarE "n_table"))
              (iterexp "tabletype_245" (VarE "tabletype_lst"))
            )
            (IterE
              (CaseE (Seq (Atom MEMORY) Arg) (TupE (VarE "memtype_297")))
              (ListN (VarE "n_mem"))
              (iterexp "memtype_297" (VarE "memtype_lst"))
            )
            (VarE "elem_lst")
            (VarE "data_lst")
            (VarE "start_opt")
            (VarE "export_lst")
          )
        )
      )
    )
    (RulePr
      "wf_moduleinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom TYPES) (VarE "ft_lst"))
          (expfield (Atom FUNCS) (CatE (VarE "fa_ex_lst") (VarE "fa_lst")))
          (expfield (Atom GLOBALS) (CatE (VarE "ga_ex_lst") (VarE "ga_lst")))
          (expfield (Atom TABLES) (CatE (VarE "ta_ex_lst") (VarE "ta_lst")))
          (expfield (Atom MEMS) (CatE (VarE "ma_ex_lst") (VarE "ma_lst")))
          (expfield (Atom EXPORTS) (VarE "xi_lst"))
        )
      )
    )
  )
)
(RecD
  (RelD
    "fun_initelem"
    (Seq Arg Arg Arg Arg Arg)
    (TupT
      (typbind "_" (VarT "store"))
      (typbind "_" (VarT "moduleinst"))
      (typbind "_" (IterT (VarT "u32") List))
      (typbind "_" (IterT (IterT (VarT "funcaddr") List) List))
      (typbind "_" (VarT "store"))
    )
    (RuleD
      "fun_initelem_case_0"
      (ExpP "s" (VarT "store"))
      (ExpP "v_moduleinst" (VarT "moduleinst"))
      (Seq Arg Arg Arg Arg Arg)
      (TupE (VarE "s") (VarE "v_moduleinst") (ListE) (ListE) (VarE "s"))
    )
    (RuleD
      "fun_initelem_case_1"
      (ExpP "s" (VarT "store"))
      (ExpP "v_moduleinst" (VarT "moduleinst"))
      (ExpP "i" (VarT "uN"))
      (ExpP "i'_lst" (IterT (VarT "u32") List))
      (ExpP "a_lst" (IterT (VarT "addr") List))
      (ExpP "a'_lst_lst" (IterT (IterT (VarT "addr") List) List))
      (ExpP "s_1" (VarT "store"))
      (ExpP "s_2" (VarT "store"))
      (ExpP "var_1" (VarT "store"))
      (ExpP "var_0" (VarT "store"))
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (VarE "s")
        (VarE "v_moduleinst")
        (CatE (ListE (VarE "i")) (VarE "i'_lst"))
        (CatE (ListE (VarE "a_lst")) (VarE "a'_lst_lst"))
        (VarE "s_2")
      )
      (RulePr
        "fun_initelem"
        (Seq Arg Arg Arg Arg Arg)
        (TupE
          (VarE "s_1")
          (VarE "v_moduleinst")
          (VarE "i'_lst")
          (VarE "a'_lst_lst")
          (VarE "var_1")
        )
      )
      (RulePr
        "fun_initelem"
        (Seq Arg Arg Arg Arg Arg)
        (TupE
          (VarE "s_1")
          (VarE "v_moduleinst")
          (VarE "i'_lst")
          (VarE "a'_lst_lst")
          (VarE "var_0")
        )
      )
      (IfPr
        (CmpE
          LtOp
          nat
          (NumE (Nat 0))
          (LenE (DotE (VarE "v_moduleinst") (Atom TABLES)))
        )
      )
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
                  (IdxE
                    (DotE (VarE "v_moduleinst") (Atom TABLES))
                    (NumE (Nat 0))
                  )
                )
                (Atom REFS)
              )
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "i"))) 0)
              (LenE (VarE "a_lst"))
            )
            (IterE (OptE (VarE "a_7")) List (iterexp "a_7" (VarE "a_lst")))
          )
        )
      )
      (IfPr (CmpE EqOp bool (VarE "s_2") (VarE "var_0")))
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s_1")))
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "var_1")))
    )
  )
)
(RecD
  (RelD
    "fun_initdata"
    (Seq Arg Arg Arg Arg Arg)
    (TupT
      (typbind "_" (VarT "store"))
      (typbind "_" (VarT "moduleinst"))
      (typbind "_" (IterT (VarT "u32") List))
      (typbind "_" (IterT (IterT (VarT "byte") List) List))
      (typbind "_" (VarT "store"))
    )
    (RuleD
      "fun_initdata_case_0"
      (ExpP "s" (VarT "store"))
      (ExpP "v_moduleinst" (VarT "moduleinst"))
      (Seq Arg Arg Arg Arg Arg)
      (TupE (VarE "s") (VarE "v_moduleinst") (ListE) (ListE) (VarE "s"))
    )
    (RuleD
      "fun_initdata_case_1"
      (ExpP "s" (VarT "store"))
      (ExpP "v_moduleinst" (VarT "moduleinst"))
      (ExpP "i" (VarT "uN"))
      (ExpP "i'_lst" (IterT (VarT "u32") List))
      (ExpP "b_lst" (IterT (VarT "byte") List))
      (ExpP "b'_lst_lst" (IterT (IterT (VarT "byte") List) List))
      (ExpP "s_1" (VarT "store"))
      (ExpP "s_2" (VarT "store"))
      (ExpP "var_1" (VarT "store"))
      (ExpP "var_0" (VarT "store"))
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (VarE "s")
        (VarE "v_moduleinst")
        (CatE (ListE (VarE "i")) (VarE "i'_lst"))
        (CatE (ListE (VarE "b_lst")) (VarE "b'_lst_lst"))
        (VarE "s_2")
      )
      (RulePr
        "fun_initdata"
        (Seq Arg Arg Arg Arg Arg)
        (TupE
          (VarE "s_1")
          (VarE "v_moduleinst")
          (VarE "i'_lst")
          (VarE "b'_lst_lst")
          (VarE "var_1")
        )
      )
      (RulePr
        "fun_initdata"
        (Seq Arg Arg Arg Arg Arg)
        (TupE
          (VarE "s_1")
          (VarE "v_moduleinst")
          (VarE "i'_lst")
          (VarE "b'_lst_lst")
          (VarE "var_0")
        )
      )
      (IfPr
        (CmpE
          LtOp
          nat
          (NumE (Nat 0))
          (LenE (DotE (VarE "v_moduleinst") (Atom MEMS)))
        )
      )
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
                  (DotP RootP (Atom MEMS))
                  (IdxE (DotE (VarE "v_moduleinst") (Atom MEMS)) (NumE (Nat 0)))
                )
                (Atom BYTES)
              )
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "i"))) 0)
              (LenE (VarE "b_lst"))
            )
            (VarE "b_lst")
          )
        )
      )
      (IfPr (CmpE EqOp bool (VarE "s_2") (VarE "var_0")))
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "var_1")))
    )
  )
)
(RelD
  "fun_instantiate"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "module"))
    (typbind "_" (IterT (VarT "externaddr") List))
    (typbind "_" (VarT "config"))
  )
  (RuleD
    "fun_instantiate_case_0"
    (ExpP "s" (VarT "store"))
    (ExpP "v_module" (VarT "module"))
    (ExpP "externaddr_lst" (IterT (VarT "externaddr") List))
    (ExpP "f" (VarT "frame"))
    (ExpP "x'_opt" (IterT (VarT "idx") Opt))
    (ExpP "functype_lst" (IterT (VarT "functype") List))
    (ExpP "expr_G_lst" (IterT (VarT "expr") List))
    (ExpP "globaltype_lst" (IterT (VarT "globaltype") List))
    (ExpP "expr_E_lst" (IterT (VarT "expr") List))
    (ExpP "x_lst_lst" (IterT (IterT (VarT "idx") List) List))
    (ExpP "b_lst_lst" (IterT (IterT (VarT "byte") List) List))
    (ExpP "expr_D_lst" (IterT (VarT "expr") List))
    (ExpP "moduleinst_init" (VarT "moduleinst"))
    (ExpP "f_init" (VarT "frame"))
    (ExpP "val_lst" (IterT (VarT "val") List))
    (ExpP "i_E_lst" (IterT (VarT "val_") List))
    (ExpP "i_D_lst" (IterT (VarT "val_") List))
    (ExpP "type_lst" (IterT (VarT "type") List))
    (ExpP "import_lst" (IterT (VarT "import") List))
    (ExpP "func_lst" (IterT (VarT "func") List))
    (ExpP "global_lst" (IterT (VarT "global") List))
    (ExpP "table_lst" (IterT (VarT "table") List))
    (ExpP "mem_lst" (IterT (VarT "mem") List))
    (ExpP "elem_lst" (IterT (VarT "elem") List))
    (ExpP "data_lst" (IterT (VarT "data") List))
    (ExpP "start_opt" (IterT (VarT "start") Opt))
    (ExpP "export_lst" (IterT (VarT "export") List))
    (ExpP "n_F" (VarT "n"))
    (ExpP "z" (VarT "state"))
    (ExpP "s_1" (VarT "store"))
    (ExpP "v_moduleinst" (VarT "moduleinst"))
    (ExpP "s_2" (VarT "store"))
    (ExpP "s_3" (VarT "store"))
    (ExpP "var_10" (IterT (VarT "globaladdr") List))
    (ExpP "var_9" (IterT (VarT "funcaddr") List))
    (ExpP "var_8" (VarT "store"))
    (ExpP "var_7" (VarT "store"))
    (ExpP
      "var_6"
      (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "moduleinst")))
    )
    (ExpP
      "var_5"
      (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "moduleinst")))
    )
    (ExpP "var_4" (VarT "store"))
    (ExpP "var_3" (VarT "store"))
    (ExpP
      "var_2"
      (TupT (typbind "_" (VarT "store")) (typbind "_" (VarT "moduleinst")))
    )
    (ExpP "var_1" (IterT (VarT "globaladdr") List))
    (ExpP "var_0" (IterT (VarT "funcaddr") List))
    (Seq Arg Arg Arg Arg)
    (TupE
      (VarE "s")
      (VarE "v_module")
      (VarE "externaddr_lst")
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE
          (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s_3") (VarE "f")))
          (LiftE
            (IterE
              (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "x'")))
              Opt
              (iterexp "x'" (VarE "x'_opt"))
            )
          )
        )
      )
    )
    (RulePr
      "fun_globals"
      (Seq Arg Arg)
      (TupE (VarE "externaddr_lst") (VarE "var_10"))
    )
    (RulePr
      "fun_funcs"
      (Seq Arg Arg)
      (TupE (VarE "externaddr_lst") (VarE "var_9"))
    )
    (IterPr
      (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "i_D_3"))) (OptE)))
      List
      (iterexp "i_D_3" (VarE "i_D_lst"))
    )
    (RulePr
      "fun_initdata"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (VarE "s_2")
        (VarE "v_moduleinst")
        (IterE
          (TheE (CallE "proj_val__0" (ExpA (VarE "i_D_3"))))
          List
          (iterexp "i_D_3" (VarE "i_D_lst"))
        )
        (VarE "b_lst_lst")
        (VarE "var_8")
      )
    )
    (IterPr
      (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "i_E_3"))) (OptE)))
      List
      (iterexp "i_E_3" (VarE "i_E_lst"))
    )
    (IterPr
      (IterPr
        (IfPr
          (CmpE
            LtOp
            nat
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "x_3"))) 0)
            (LenE (DotE (VarE "v_moduleinst") (Atom FUNCS)))
          )
        )
        List
        (iterexp "x_3" (VarE "x_lst_3"))
      )
      List
      (iterexp "x_lst_3" (VarE "x_lst_lst"))
    )
    (RulePr
      "fun_initelem"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (VarE "s_1")
        (VarE "v_moduleinst")
        (IterE
          (TheE (CallE "proj_val__0" (ExpA (VarE "i_E_3"))))
          List
          (iterexp "i_E_3" (VarE "i_E_lst"))
        )
        (IterE
          (IterE
            (IdxE
              (DotE (VarE "v_moduleinst") (Atom FUNCS))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "x_3"))) 0)
            )
            List
            (iterexp "x_3" (VarE "x_lst_3"))
          )
          List
          (iterexp "x_lst_3" (VarE "x_lst_lst"))
        )
        (VarE "var_7")
      )
    )
    (RulePr
      "fun_allocmodule"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (VarE "s")
        (VarE "v_module")
        (VarE "externaddr_lst")
        (VarE "val_lst")
        (VarE "var_6")
      )
    )
    (RulePr
      "fun_allocmodule"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (VarE "s")
        (VarE "v_module")
        (VarE "externaddr_lst")
        (VarE "val_lst")
        (VarE "var_5")
      )
    )
    (IterPr
      (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "i_D_2"))) (OptE)))
      List
      (iterexp "i_D_2" (VarE "i_D_lst"))
    )
    (RulePr
      "fun_initdata"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (VarE "s_2")
        (VarE "v_moduleinst")
        (IterE
          (TheE (CallE "proj_val__0" (ExpA (VarE "i_D_2"))))
          List
          (iterexp "i_D_2" (VarE "i_D_lst"))
        )
        (VarE "b_lst_lst")
        (VarE "var_4")
      )
    )
    (IterPr
      (IfPr (CmpE NeOp bool (CallE "proj_val__0" (ExpA (VarE "i_E_2"))) (OptE)))
      List
      (iterexp "i_E_2" (VarE "i_E_lst"))
    )
    (IterPr
      (IterPr
        (IfPr
          (CmpE
            LtOp
            nat
            (ProjE (CallE "proj_uN_0" (ExpA (VarE "x_2"))) 0)
            (LenE (DotE (VarE "v_moduleinst") (Atom FUNCS)))
          )
        )
        List
        (iterexp "x_2" (VarE "x_lst_2"))
      )
      List
      (iterexp "x_lst_2" (VarE "x_lst_lst"))
    )
    (RulePr
      "fun_initelem"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (VarE "s_1")
        (VarE "v_moduleinst")
        (IterE
          (TheE (CallE "proj_val__0" (ExpA (VarE "i_E_2"))))
          List
          (iterexp "i_E_2" (VarE "i_E_lst"))
        )
        (IterE
          (IterE
            (IdxE
              (DotE (VarE "v_moduleinst") (Atom FUNCS))
              (ProjE (CallE "proj_uN_0" (ExpA (VarE "x_2"))) 0)
            )
            List
            (iterexp "x_2" (VarE "x_lst_2"))
          )
          List
          (iterexp "x_lst_2" (VarE "x_lst_lst"))
        )
        (VarE "var_3")
      )
    )
    (RulePr
      "fun_allocmodule"
      (Seq Arg Arg Arg Arg Arg)
      (TupE
        (VarE "s")
        (VarE "v_module")
        (VarE "externaddr_lst")
        (VarE "val_lst")
        (VarE "var_2")
      )
    )
    (RulePr
      "fun_globals"
      (Seq Arg Arg)
      (TupE (VarE "externaddr_lst") (VarE "var_1"))
    )
    (RulePr
      "fun_funcs"
      (Seq Arg Arg)
      (TupE (VarE "externaddr_lst") (VarE "var_0"))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CaseE
          (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
          (TupE
            (VarE "type_lst")
            (VarE "import_lst")
            (VarE "func_lst")
            (VarE "global_lst")
            (VarE "table_lst")
            (VarE "mem_lst")
            (VarE "elem_lst")
            (VarE "data_lst")
            (VarE "start_opt")
            (VarE "export_lst")
          )
        )
        (VarE "v_module")
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "type_lst")
        (IterE
          (CaseE (Seq (Atom TYPE) Arg) (TupE (VarE "functype_49")))
          List
          (iterexp "functype_49" (VarE "functype_lst"))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "global_lst")
        (IterE
          (CaseE
            (Seq (Atom GLOBAL) Arg Arg)
            (TupE (VarE "globaltype_201") (VarE "expr_G_1"))
          )
          List
          (iterexp "expr_G_1" (VarE "expr_G_lst"))
          (iterexp "globaltype_201" (VarE "globaltype_lst"))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "elem_lst")
        (IterE
          (CaseE
            (Seq (Atom ELEM) Arg Arg)
            (TupE (VarE "expr_E_1") (VarE "x_lst_1"))
          )
          List
          (iterexp "expr_E_1" (VarE "expr_E_lst"))
          (iterexp "x_lst_1" (VarE "x_lst_lst"))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "data_lst")
        (IterE
          (CaseE
            (Seq (Atom DATA) Arg Arg)
            (TupE (VarE "expr_D_1") (VarE "b_lst_1"))
          )
          List
          (iterexp "b_lst_1" (VarE "b_lst_lst"))
          (iterexp "expr_D_1" (VarE "expr_D_lst"))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "start_opt")
        (IterE
          (CaseE (Seq (Atom START) Arg) (TupE (VarE "x'_1")))
          Opt
          (iterexp "x'_1" (VarE "x'_opt"))
        )
      )
    )
    (IfPr (CmpE EqOp bool (VarE "n_F") (LenE (VarE "func_lst"))))
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "moduleinst_init")
        (StrE
          (expfield (Atom TYPES) (VarE "functype_lst"))
          (expfield
            (Atom FUNCS)
            (CatE
              (VarE "var_0")
              (IterE
                (BinE
                  AddOp
                  nat
                  (LenE (DotE (VarE "s") (Atom FUNCS)))
                  (VarE "i_F_1")
                )
                (ListN (VarE "n_F") "i_F_1")
              )
            )
          )
          (expfield (Atom GLOBALS) (VarE "var_1"))
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
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "z")
        (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f_init")))
      )
    )
    (IfPr (CmpE EqOp bool (LenE (VarE "expr_G_lst")) (LenE (VarE "val_lst"))))
    (IterPr
      (RulePr
        "Eval_expr"
        (Infix (Infix Arg ; Arg) ~>* (Infix Arg ; Arg))
        (TupE (VarE "z") (VarE "expr_G_2") (VarE "z") (ListE (VarE "val_4")))
      )
      List
      (iterexp "expr_G_2" (VarE "expr_G_lst"))
      (iterexp "val_4" (VarE "val_lst"))
    )
    (IfPr (CmpE EqOp bool (LenE (VarE "expr_E_lst")) (LenE (VarE "i_E_lst"))))
    (IterPr
      (RulePr
        "Eval_expr"
        (Infix (Infix Arg ; Arg) ~>* (Infix Arg ; Arg))
        (TupE
          (VarE "z")
          (VarE "expr_E_2")
          (VarE "z")
          (ListE
            (CaseE
              (Seq (Atom CONST) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "i_E_1"))
            )
          )
        )
      )
      List
      (iterexp "expr_E_2" (VarE "expr_E_lst"))
      (iterexp "i_E_1" (VarE "i_E_lst"))
    )
    (IfPr (CmpE EqOp bool (LenE (VarE "expr_D_lst")) (LenE (VarE "i_D_lst"))))
    (IterPr
      (RulePr
        "Eval_expr"
        (Infix (Infix Arg ; Arg) ~>* (Infix Arg ; Arg))
        (TupE
          (VarE "z")
          (VarE "expr_D_2")
          (VarE "z")
          (ListE
            (CaseE
              (Seq (Atom CONST) Arg Arg)
              (TupE (CaseE (Atom I32) (TupE)) (VarE "i_D_1"))
            )
          )
        )
      )
      List
      (iterexp "expr_D_2" (VarE "expr_D_lst"))
      (iterexp "i_D_1" (VarE "i_D_lst"))
    )
    (IfPr
      (CmpE EqOp bool (TupE (VarE "s_1") (VarE "v_moduleinst")) (VarE "var_2"))
    )
    (IfPr (CmpE EqOp bool (VarE "s_2") (VarE "var_3")))
    (IfPr (CmpE EqOp bool (VarE "s_3") (VarE "var_4")))
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "f")
        (StrE
          (expfield (Atom LOCALS) (ListE))
          (expfield (Atom MODULE) (VarE "v_moduleinst"))
        )
      )
    )
    (IterPr
      (RulePr "wf_val" (Seq Arg) (TupE (VarE "val_6")))
      List
      (iterexp "val_6" (VarE "val_lst"))
    )
    (RulePr "wf_store" (Seq Arg) (TupE (ProjE (VarE "var_5") 0)))
    (RulePr "wf_moduleinst" (Seq Arg) (TupE (ProjE (VarE "var_6") 1)))
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "var_7")))
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "var_8")))
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s_3") (VarE "f")))
            (LiftE
              (IterE
                (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "x'_2")))
                Opt
                (iterexp "x'_2" (VarE "x'_opt"))
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
            (VarE "type_lst")
            (VarE "import_lst")
            (VarE "func_lst")
            (VarE "global_lst")
            (VarE "table_lst")
            (VarE "mem_lst")
            (VarE "elem_lst")
            (VarE "data_lst")
            (VarE "start_opt")
            (VarE "export_lst")
          )
        )
      )
    )
    (IfPr
      (CmpE EqOp bool (LenE (VarE "expr_G_lst")) (LenE (VarE "globaltype_lst")))
    )
    (IterPr
      (RulePr
        "wf_global"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom GLOBAL) Arg Arg)
            (TupE (VarE "globaltype_203") (VarE "expr_G_3"))
          )
        )
      )
      List
      (iterexp "expr_G_3" (VarE "expr_G_lst"))
      (iterexp "globaltype_203" (VarE "globaltype_lst"))
    )
    (IfPr (CmpE EqOp bool (LenE (VarE "expr_E_lst")) (LenE (VarE "x_lst_lst"))))
    (IterPr
      (RulePr
        "wf_elem"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom ELEM) Arg Arg)
            (TupE (VarE "expr_E_3") (VarE "x_lst_4"))
          )
        )
      )
      List
      (iterexp "expr_E_3" (VarE "expr_E_lst"))
      (iterexp "x_lst_4" (VarE "x_lst_lst"))
    )
    (IfPr (CmpE EqOp bool (LenE (VarE "b_lst_lst")) (LenE (VarE "expr_D_lst"))))
    (IterPr
      (RulePr
        "wf_data"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom DATA) Arg Arg)
            (TupE (VarE "expr_D_3") (VarE "b_lst_4"))
          )
        )
      )
      List
      (iterexp "b_lst_4" (VarE "b_lst_lst"))
      (iterexp "expr_D_3" (VarE "expr_D_lst"))
    )
    (IterPr
      (RulePr
        "wf_start"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom START) Arg) (TupE (VarE "x'_3"))))
      )
      Opt
      (iterexp "x'_3" (VarE "x'_opt"))
    )
    (RulePr
      "wf_moduleinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom TYPES) (VarE "functype_lst"))
          (expfield
            (Atom FUNCS)
            (CatE
              (VarE "var_9")
              (IterE
                (BinE
                  AddOp
                  nat
                  (LenE (DotE (VarE "s") (Atom FUNCS)))
                  (VarE "i_F_2")
                )
                (ListN (VarE "n_F") "i_F_2")
              )
            )
          )
          (expfield (Atom GLOBALS) (VarE "var_10"))
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
      (TupE
        (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f_init")))
      )
    )
    (IterPr
      (RulePr
        "wf_val"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom CONST) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "i_E_4"))
          )
        )
      )
      List
      (iterexp "i_E_4" (VarE "i_E_lst"))
    )
    (IterPr
      (RulePr
        "wf_val"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom CONST) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "i_D_4"))
          )
        )
      )
      List
      (iterexp "i_D_4" (VarE "i_D_lst"))
    )
    (RulePr
      "wf_frame"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom LOCALS) (ListE))
          (expfield (Atom MODULE) (VarE "v_moduleinst"))
        )
      )
    )
  )
)
(RelD
  "fun_invoke"
  (Seq Arg Arg Arg Arg)
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "funcaddr"))
    (typbind "_" (IterT (VarT "val") List))
    (typbind "_" (VarT "config"))
  )
  (RuleD
    "fun_invoke_case_0"
    (ExpP "s" (VarT "store"))
    (ExpP "fa" nat)
    (ExpP "v_n" nat)
    (ExpP "val_lst" (IterT (VarT "val") List))
    (ExpP "f" (VarT "frame"))
    (ExpP "t_1_lst" (IterT (VarT "valtype") List))
    (ExpP "t_2_lst" (IterT (VarT "valtype") List))
    (Seq Arg Arg Arg Arg)
    (TupE
      (VarE "s")
      (VarE "fa")
      (VarE "val_lst")
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE
          (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f")))
          (CatE
            (IterE
              (CallE "admininstr_val" (ExpA (VarE "v_val")))
              (ListN (VarE "v_n"))
              (iterexp "v_val" (VarE "val_lst"))
            )
            (ListE (CaseE (Seq (Atom CALL_ADDR) Arg) (TupE (VarE "fa"))))
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
        LtOp
        nat
        (VarE "fa")
        (LenE
          (CallE
            "fun_funcinst"
            (ExpA
              (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f")))
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
              "fun_funcinst"
              (ExpA
                (CaseE
                  (Seq (Atom mk_state) Arg Arg)
                  (TupE (VarE "s") (VarE "f"))
                )
              )
            )
            (VarE "fa")
          )
          (Atom TYPE)
        )
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
        )
      )
    )
    (IterPr
      (RulePr "wf_funcinst" (Seq Arg) (TupE (VarE "iter_53")))
      List
      (iterexp
        "iter_53"
        (CallE
          "fun_funcinst"
          (ExpA
            (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f")))
          )
        )
      )
    )
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f")))
            (CatE
              (IterE
                (CallE "admininstr_val" (ExpA (VarE "val_10")))
                (ListN (VarE "v_n"))
                (iterexp "val_10" (VarE "val_lst"))
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
      (TupE (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
    )
    (IfPr (CmpE EqOp bool (VarE "v_n") (LenE (VarE "val_lst"))))
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
    "mk_Context_ok"
    (ExpP "C" (VarT "context"))
    (ExpP "ft_lst" (IterT (VarT "functype") List))
    (ExpP "ft_2_lst" (IterT (VarT "functype") List))
    (ExpP "gt_lst" (IterT (VarT "globaltype") List))
    (ExpP "tt_lst" (IterT (VarT "tabletype") List))
    (ExpP "mt_lst" (IterT (VarT "memtype") List))
    (ExpP "lct_lst" (IterT (VarT "valtype") List))
    (ExpP "rt_lst" (IterT (VarT "valtype") List))
    (ExpP "rt'_opt" (IterT (VarT "valtype") Opt))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (VarE "C")
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "C")
        (StrE
          (expfield (Atom TYPES) (VarE "ft_lst"))
          (expfield (Atom FUNCS) (VarE "ft_2_lst"))
          (expfield (Atom GLOBALS) (VarE "gt_lst"))
          (expfield (Atom TABLES) (VarE "tt_lst"))
          (expfield (Atom MEMS) (VarE "mt_lst"))
          (expfield (Atom LOCALS) (VarE "lct_lst"))
          (expfield
            (Atom LABELS)
            (IterE (OptE (VarE "rt")) List (iterexp "rt" (VarE "rt_lst")))
          )
          (expfield (Atom RETURN) (OptE (VarE "rt'_opt")))
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
      (iterexp "ft" (VarE "ft_lst"))
    )
    (IterPr
      (RulePr
        "Globaltype_ok"
        (Infix (Seq) |- (Infix Arg : (Atom OK)))
        (VarE "gt")
      )
      List
      (iterexp "gt" (VarE "gt_lst"))
    )
    (IterPr
      (RulePr "Memtype_ok" (Infix (Seq) |- (Infix Arg : (Atom OK))) (VarE "mt"))
      List
      (iterexp "mt" (VarE "mt_lst"))
    )
    (IterPr
      (RulePr
        "Tabletype_ok"
        (Infix (Seq) |- (Infix Arg : (Atom OK)))
        (VarE "tt")
      )
      List
      (iterexp "tt" (VarE "tt_lst"))
    )
    (IterPr
      (RulePr
        "Functype_ok"
        (Infix (Seq) |- (Infix Arg : (Atom OK)))
        (VarE "ft_2")
      )
      List
      (iterexp "ft_2" (VarE "ft_2_lst"))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_context"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom TYPES) (VarE "ft_lst"))
          (expfield (Atom FUNCS) (VarE "ft_2_lst"))
          (expfield (Atom GLOBALS) (VarE "gt_lst"))
          (expfield (Atom TABLES) (VarE "tt_lst"))
          (expfield (Atom MEMS) (VarE "mt_lst"))
          (expfield (Atom LOCALS) (VarE "lct_lst"))
          (expfield
            (Atom LABELS)
            (IterE (OptE (VarE "rt")) List (iterexp "rt" (VarE "rt_lst")))
          )
          (expfield (Atom RETURN) (OptE (VarE "rt'_opt")))
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
    "mk_Val_ok"
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
    (ExpP "v_lst" (IterT (VarT "val") List))
    (ExpP "t_lst" (IterT (VarT "valtype") List))
    (Infix (Seq) |- (Infix Arg : Arg))
    (TupE (CaseE (Seq (Atom _VALS) Arg) (TupE (VarE "v_lst"))) (VarE "t_lst"))
    (IfPr (CmpE EqOp bool (LenE (VarE "t_lst")) (LenE (VarE "v_lst"))))
    (IterPr
      (RulePr
        "Val_ok"
        (Infix (Seq) |- (Infix Arg : Arg))
        (TupE (VarE "v") (VarE "t"))
      )
      List
      (iterexp "t" (VarE "t_lst"))
      (iterexp "v" (VarE "v_lst"))
    )
    (RulePr
      "wf_result"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom _VALS) Arg) (TupE (VarE "v_lst"))))
    )
  )
  (RuleD
    "trap"
    (ExpP "t_lst" (IterT (VarT "valtype") List))
    (Infix (Seq) |- (Infix Arg : Arg))
    (TupE (CaseE (Atom TRAP) (TupE)) (VarE "t_lst"))
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
      (ExpP "v_globalinst" (VarT "globalinst"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "a")))
        (CaseE
          (Seq (Atom GLOBAL) Arg)
          (TupE (DotE (VarE "v_globalinst") (Atom TYPE)))
        )
      )
      (IfPr (CmpE LtOp nat (VarE "a") (LenE (DotE (VarE "s") (Atom GLOBALS)))))
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "s") (Atom GLOBALS)) (VarE "a"))
          (VarE "v_globalinst")
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr
        "wf_externtype"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom GLOBAL) Arg)
            (TupE (DotE (VarE "v_globalinst") (Atom TYPE)))
          )
        )
      )
    )
    (RuleD
      "mem"
      (ExpP "s" (VarT "store"))
      (ExpP "a" (VarT "addr"))
      (ExpP "v_meminst" (VarT "meminst"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "a")))
        (CaseE
          (Seq (Atom MEM) Arg)
          (TupE (DotE (VarE "v_meminst") (Atom TYPE)))
        )
      )
      (IfPr (CmpE LtOp nat (VarE "a") (LenE (DotE (VarE "s") (Atom MEMS)))))
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "s") (Atom MEMS)) (VarE "a"))
          (VarE "v_meminst")
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr
        "wf_externtype"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom MEM) Arg)
            (TupE (DotE (VarE "v_meminst") (Atom TYPE)))
          )
        )
      )
    )
    (RuleD
      "table"
      (ExpP "s" (VarT "store"))
      (ExpP "a" (VarT "addr"))
      (ExpP "v_tableinst" (VarT "tableinst"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "a")))
        (CaseE
          (Seq (Atom TABLE) Arg)
          (TupE (DotE (VarE "v_tableinst") (Atom TYPE)))
        )
      )
      (IfPr (CmpE LtOp nat (VarE "a") (LenE (DotE (VarE "s") (Atom TABLES)))))
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "s") (Atom TABLES)) (VarE "a"))
          (VarE "v_tableinst")
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr
        "wf_externtype"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom TABLE) Arg)
            (TupE (DotE (VarE "v_tableinst") (Atom TYPE)))
          )
        )
      )
    )
    (RuleD
      "func"
      (ExpP "s" (VarT "store"))
      (ExpP "a" (VarT "addr"))
      (ExpP "v_funcinst" (VarT "funcinst"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "a")))
        (CaseE
          (Seq (Atom FUNC) Arg)
          (TupE (DotE (VarE "v_funcinst") (Atom TYPE)))
        )
      )
      (IfPr (CmpE LtOp nat (VarE "a") (LenE (DotE (VarE "s") (Atom FUNCS)))))
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "s") (Atom FUNCS)) (VarE "a"))
          (VarE "v_funcinst")
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr
        "wf_externtype"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom FUNC) Arg)
            (TupE (DotE (VarE "v_funcinst") (Atom TYPE)))
          )
        )
      )
    )
    (RuleD
      "sub"
      (ExpP "s" (VarT "store"))
      (ExpP "v_externaddr" (VarT "externaddr"))
      (ExpP "xt" (VarT "externtype"))
      (ExpP "xt'" (VarT "externtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "s") (VarE "v_externaddr") (VarE "xt"))
      (RulePr
        "Externaddr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "s") (VarE "v_externaddr") (VarE "xt'"))
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
    "mk_Exportinst_ok"
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
    "mk_Moduleinst_ok"
    (ExpP "s" (VarT "store"))
    (ExpP "functype_lst" (IterT (VarT "functype") List))
    (ExpP "funcaddr_lst" (IterT (VarT "funcaddr") List))
    (ExpP "globaladdr_lst" (IterT (VarT "globaladdr") List))
    (ExpP "tableaddr_lst" (IterT (VarT "tableaddr") List))
    (ExpP "memaddr_lst" (IterT (VarT "memaddr") List))
    (ExpP "exportinst_lst" (IterT (VarT "exportinst") List))
    (ExpP "functype_F_lst" (IterT (VarT "functype") List))
    (ExpP "globaltype_lst" (IterT (VarT "globaltype") List))
    (ExpP "tabletype_lst" (IterT (VarT "tabletype") List))
    (ExpP "memtype_lst" (IterT (VarT "memtype") List))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (StrE
        (expfield (Atom TYPES) (VarE "functype_lst"))
        (expfield (Atom FUNCS) (VarE "funcaddr_lst"))
        (expfield (Atom GLOBALS) (VarE "globaladdr_lst"))
        (expfield (Atom TABLES) (VarE "tableaddr_lst"))
        (expfield (Atom MEMS) (VarE "memaddr_lst"))
        (expfield (Atom EXPORTS) (VarE "exportinst_lst"))
      )
      (StrE
        (expfield (Atom TYPES) (VarE "functype_lst"))
        (expfield (Atom FUNCS) (VarE "functype_F_lst"))
        (expfield (Atom GLOBALS) (VarE "globaltype_lst"))
        (expfield (Atom TABLES) (VarE "tabletype_lst"))
        (expfield (Atom MEMS) (VarE "memtype_lst"))
        (expfield (Atom LOCALS) (ListE))
        (expfield (Atom LABELS) (ListE))
        (expfield (Atom RETURN) (OptE))
      )
    )
    (IterPr
      (RulePr
        "Functype_ok"
        (Infix (Seq) |- (Infix Arg : (Atom OK)))
        (VarE "v_functype")
      )
      List
      (iterexp "v_functype" (VarE "functype_lst"))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (LenE (VarE "globaladdr_lst"))
        (LenE (VarE "globaltype_lst"))
      )
    )
    (IterPr
      (RulePr
        "Externaddr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "v_globaladdr")))
          (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "v_globaltype")))
        )
      )
      List
      (iterexp "v_globaladdr" (VarE "globaladdr_lst"))
      (iterexp "v_globaltype" (VarE "globaltype_lst"))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (LenE (VarE "funcaddr_lst"))
        (LenE (VarE "functype_F_lst"))
      )
    )
    (IterPr
      (RulePr
        "Externaddr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "v_funcaddr")))
          (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "functype_F")))
        )
      )
      List
      (iterexp "v_funcaddr" (VarE "funcaddr_lst"))
      (iterexp "functype_F" (VarE "functype_F_lst"))
    )
    (IfPr
      (CmpE EqOp bool (LenE (VarE "memaddr_lst")) (LenE (VarE "memtype_lst")))
    )
    (IterPr
      (RulePr
        "Externaddr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "v_memaddr")))
          (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "v_memtype")))
        )
      )
      List
      (iterexp "v_memaddr" (VarE "memaddr_lst"))
      (iterexp "v_memtype" (VarE "memtype_lst"))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (LenE (VarE "tableaddr_lst"))
        (LenE (VarE "tabletype_lst"))
      )
    )
    (IterPr
      (RulePr
        "Externaddr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "v_tableaddr")))
          (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "v_tabletype")))
        )
      )
      List
      (iterexp "v_tableaddr" (VarE "tableaddr_lst"))
      (iterexp "v_tabletype" (VarE "tabletype_lst"))
    )
    (IterPr
      (RulePr
        "Exportinst_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "s") (VarE "v_exportinst"))
      )
      List
      (iterexp "v_exportinst" (VarE "exportinst_lst"))
    )
    (IfPr
      (CallE
        "disjoint_"
        (TypA (VarT "name"))
        (ExpA
          (IterE
            (DotE (VarE "v_exportinst") (Atom NAME))
            List
            (iterexp "v_exportinst" (VarE "exportinst_lst"))
          )
        )
      )
    )
    (IfPr
      (CmpE
        GtOp
        nat
        (LenE
          (CatE
            (IterE
              (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "v_globaladdr")))
              List
              (iterexp "v_globaladdr" (VarE "globaladdr_lst"))
            )
            (CatE
              (IterE
                (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "v_memaddr")))
                List
                (iterexp "v_memaddr" (VarE "memaddr_lst"))
              )
              (CatE
                (IterE
                  (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "v_tableaddr")))
                  List
                  (iterexp "v_tableaddr" (VarE "tableaddr_lst"))
                )
                (IterE
                  (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "v_funcaddr")))
                  List
                  (iterexp "v_funcaddr" (VarE "funcaddr_lst"))
                )
              )
            )
          )
        )
        (NumE (Nat 0))
      )
    )
    (IterPr
      (IfPr
        (MemE
          (DotE (VarE "v_exportinst") (Atom ADDR))
          (CatE
            (IterE
              (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "v_globaladdr")))
              List
              (iterexp "v_globaladdr" (VarE "globaladdr_lst"))
            )
            (CatE
              (IterE
                (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "v_memaddr")))
                List
                (iterexp "v_memaddr" (VarE "memaddr_lst"))
              )
              (CatE
                (IterE
                  (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "v_tableaddr")))
                  List
                  (iterexp "v_tableaddr" (VarE "tableaddr_lst"))
                )
                (IterE
                  (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "v_funcaddr")))
                  List
                  (iterexp "v_funcaddr" (VarE "funcaddr_lst"))
                )
              )
            )
          )
        )
      )
      List
      (iterexp "v_exportinst" (VarE "exportinst_lst"))
    )
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
    (RulePr
      "wf_moduleinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom TYPES) (VarE "functype_lst"))
          (expfield (Atom FUNCS) (VarE "funcaddr_lst"))
          (expfield (Atom GLOBALS) (VarE "globaladdr_lst"))
          (expfield (Atom TABLES) (VarE "tableaddr_lst"))
          (expfield (Atom MEMS) (VarE "memaddr_lst"))
          (expfield (Atom EXPORTS) (VarE "exportinst_lst"))
        )
      )
    )
    (RulePr
      "wf_context"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom TYPES) (VarE "functype_lst"))
          (expfield (Atom FUNCS) (VarE "functype_F_lst"))
          (expfield (Atom GLOBALS) (VarE "globaltype_lst"))
          (expfield (Atom TABLES) (VarE "tabletype_lst"))
          (expfield (Atom MEMS) (VarE "memtype_lst"))
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
        (TupE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "v_globaltype"))))
      )
      List
      (iterexp "v_globaltype" (VarE "globaltype_lst"))
    )
    (IterPr
      (RulePr
        "wf_externtype"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "functype_F"))))
      )
      List
      (iterexp "functype_F" (VarE "functype_F_lst"))
    )
    (IterPr
      (RulePr
        "wf_externtype"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "v_memtype"))))
      )
      List
      (iterexp "v_memtype" (VarE "memtype_lst"))
    )
    (IterPr
      (RulePr
        "wf_externtype"
        (Seq Arg)
        (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "v_tabletype"))))
      )
      List
      (iterexp "v_tabletype" (VarE "tabletype_lst"))
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
    "mk_Frame_ok"
    (ExpP "s" (VarT "store"))
    (ExpP "val_lst" (IterT (VarT "val") List))
    (ExpP "v_moduleinst" (VarT "moduleinst"))
    (ExpP "C" (VarT "context"))
    (ExpP "t_lst" (IterT (VarT "valtype") List))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (StrE
        (expfield (Atom LOCALS) (VarE "val_lst"))
        (expfield (Atom MODULE) (VarE "v_moduleinst"))
      )
      (CompE
        (VarE "C")
        (StrE
          (expfield (Atom TYPES) (ListE))
          (expfield (Atom FUNCS) (ListE))
          (expfield (Atom GLOBALS) (ListE))
          (expfield (Atom TABLES) (ListE))
          (expfield (Atom MEMS) (ListE))
          (expfield (Atom LOCALS) (VarE "t_lst"))
          (expfield (Atom LABELS) (ListE))
          (expfield (Atom RETURN) (OptE))
        )
      )
    )
    (RulePr
      "Moduleinst_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "s") (VarE "v_moduleinst") (VarE "C"))
    )
    (IfPr (CmpE EqOp bool (LenE (VarE "t_lst")) (LenE (VarE "val_lst"))))
    (IterPr
      (RulePr
        "Val_ok"
        (Infix (Seq) |- (Infix Arg : Arg))
        (TupE (VarE "v_val") (VarE "t"))
      )
      List
      (iterexp "t" (VarE "t_lst"))
      (iterexp "v_val" (VarE "val_lst"))
    )
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_frame"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom LOCALS) (VarE "val_lst"))
          (expfield (Atom MODULE) (VarE "v_moduleinst"))
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
          (expfield (Atom LOCALS) (VarE "t_lst"))
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
      (ExpP "v_instr" (VarT "instr"))
      (ExpP "t_1_lst" (IterT (VarT "valtype") List))
      (ExpP "t_2_lst" (IterT (VarT "valtype") List))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (CallE "admininstr_instr" (ExpA (VarE "v_instr")))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
        )
      )
      (RulePr
        "Instr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (VarE "v_instr")
          (CaseE
            (Seq (Atom mk_functype) Arg Arg)
            (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
          )
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "v_instr")))
    )
    (RuleD
      "label"
      (ExpP "s" (VarT "store"))
      (ExpP "C" (VarT "context"))
      (ExpP "v_n" (VarT "n"))
      (ExpP "instr'_lst" (IterT (VarT "instr") List))
      (ExpP "admininstr_lst" (IterT (VarT "admininstr") List))
      (ExpP "t_opt" (IterT (VarT "valtype") Opt))
      (ExpP "t'_opt" (IterT (VarT "valtype") Opt))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (CaseE
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupE (VarE "v_n") (VarE "instr'_lst") (VarE "admininstr_lst"))
        )
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (ListE) (LiftE (VarE "t_opt")))
        )
      )
      (IfPr (CmpE EqOp bool (LenE (LiftE (VarE "t'_opt"))) (VarE "v_n")))
      (RulePr
        "Instrs_ok2"
        (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (VarE "C")
          (IterE
            (CallE "admininstr_instr" (ExpA (VarE "instr'")))
            List
            (iterexp "instr'" (VarE "instr'_lst"))
          )
          (CaseE
            (Seq (Atom mk_functype) Arg Arg)
            (TupE (LiftE (VarE "t'_opt")) (LiftE (VarE "t_opt")))
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
              (expfield (Atom LABELS) (ListE (VarE "t'_opt")))
              (expfield (Atom RETURN) (OptE))
            )
            (VarE "C")
          )
          (VarE "admininstr_lst")
          (CaseE
            (Seq (Atom mk_functype) Arg Arg)
            (TupE (ListE) (LiftE (VarE "t_opt")))
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
            (TupE (VarE "v_n") (VarE "instr'_lst") (VarE "admininstr_lst"))
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
            (expfield (Atom LABELS) (ListE (VarE "t'_opt")))
            (expfield (Atom RETURN) (OptE))
          )
        )
      )
    )
    (RuleD
      "frame"
      (ExpP "s" (VarT "store"))
      (ExpP "C" (VarT "context"))
      (ExpP "v_n" (VarT "n"))
      (ExpP "f" (VarT "frame"))
      (ExpP "admininstr_lst" (IterT (VarT "admininstr") List))
      (ExpP "t_opt" (IterT (VarT "valtype") Opt))
      (ExpP "C'" (VarT "context"))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (CaseE
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupE (VarE "v_n") (VarE "f") (VarE "admininstr_lst"))
        )
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (ListE) (LiftE (VarE "t_opt")))
        )
      )
      (IfPr (CmpE EqOp bool (LenE (LiftE (VarE "t_opt"))) (VarE "v_n")))
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
              (expfield (Atom RETURN) (OptE (VarE "t_opt")))
            )
            (VarE "C'")
          )
          (VarE "admininstr_lst")
          (VarE "t_opt")
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
            (TupE (VarE "v_n") (VarE "f") (VarE "admininstr_lst"))
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
            (expfield (Atom RETURN) (OptE (VarE "t_opt")))
          )
        )
      )
    )
    (RuleD
      "call_addr"
      (ExpP "s" (VarT "store"))
      (ExpP "C" (VarT "context"))
      (ExpP "v_funcaddr" (VarT "funcaddr"))
      (ExpP "t_1_lst" (IterT (VarT "valtype") List))
      (ExpP "t_2_lst" (IterT (VarT "valtype") List))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (CaseE (Seq (Atom CALL_ADDR) Arg) (TupE (VarE "v_funcaddr")))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
        )
      )
      (RulePr
        "Externaddr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "v_funcaddr")))
          (CaseE
            (Seq (Atom FUNC) Arg)
            (TupE
              (CaseE
                (Seq (Atom mk_functype) Arg Arg)
                (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
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
        (TupE (CaseE (Seq (Atom CALL_ADDR) Arg) (TupE (VarE "v_funcaddr"))))
      )
      (RulePr
        "wf_externtype"
        (Seq Arg)
        (TupE
          (CaseE
            (Seq (Atom FUNC) Arg)
            (TupE
              (CaseE
                (Seq (Atom mk_functype) Arg Arg)
                (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
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
      (ExpP "t_1_lst" (IterT (VarT "valtype") List))
      (ExpP "t_2_lst" (IterT (VarT "valtype") List))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (CaseE (Atom TRAP) (TupE))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
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
        (CaseE (Seq (Atom mk_functype) Arg Arg) (TupE (ListE) (ListE)))
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    )
    (RuleD
      "instr"
      (ExpP "s" (VarT "store"))
      (ExpP "C" (VarT "context"))
      (ExpP "v_admininstr" (VarT "admininstr"))
      (ExpP "t_1_lst" (IterT (VarT "valtype") List))
      (ExpP "t_2_lst" (IterT (VarT "valtype") List))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (ListE (VarE "v_admininstr"))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
        )
      )
      (RulePr
        "Instr_ok2"
        (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (VarE "C")
          (VarE "v_admininstr")
          (CaseE
            (Seq (Atom mk_functype) Arg Arg)
            (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
          )
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (RulePr "wf_admininstr" (Seq Arg) (TupE (VarE "v_admininstr")))
    )
    (RuleD
      "seq"
      (ExpP "s" (VarT "store"))
      (ExpP "C" (VarT "context"))
      (ExpP "admininstr_1_lst" (IterT (VarT "admininstr") List))
      (ExpP "admininstr_2_lst" (IterT (VarT "admininstr") List))
      (ExpP "t_1_lst" (IterT (VarT "valtype") List))
      (ExpP "t_3_lst" (IterT (VarT "valtype") List))
      (ExpP "t_2_lst" (IterT (VarT "valtype") List))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (CatE (VarE "admininstr_1_lst") (VarE "admininstr_2_lst"))
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE (VarE "t_1_lst") (VarE "t_3_lst"))
        )
      )
      (RulePr
        "Instrs_ok2"
        (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (VarE "C")
          (VarE "admininstr_1_lst")
          (CaseE
            (Seq (Atom mk_functype) Arg Arg)
            (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
          )
        )
      )
      (RulePr
        "Instrs_ok2"
        (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (VarE "C")
          (VarE "admininstr_2_lst")
          (CaseE
            (Seq (Atom mk_functype) Arg Arg)
            (TupE (VarE "t_2_lst") (VarE "t_3_lst"))
          )
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (IterPr
        (RulePr "wf_admininstr" (Seq Arg) (TupE (VarE "admininstr_1")))
        List
        (iterexp "admininstr_1" (VarE "admininstr_1_lst"))
      )
      (IterPr
        (RulePr "wf_admininstr" (Seq Arg) (TupE (VarE "admininstr_2")))
        List
        (iterexp "admininstr_2" (VarE "admininstr_2_lst"))
      )
    )
    (RuleD
      "frame"
      (ExpP "s" (VarT "store"))
      (ExpP "C" (VarT "context"))
      (ExpP "admininstr_lst" (IterT (VarT "admininstr") List))
      (ExpP "t_lst" (IterT (VarT "valtype") List))
      (ExpP "t_1_lst" (IterT (VarT "valtype") List))
      (ExpP "t_2_lst" (IterT (VarT "valtype") List))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (VarE "C")
        (VarE "admininstr_lst")
        (CaseE
          (Seq (Atom mk_functype) Arg Arg)
          (TupE
            (CatE (VarE "t_lst") (VarE "t_1_lst"))
            (CatE (VarE "t_lst") (VarE "t_2_lst"))
          )
        )
      )
      (RulePr
        "Instrs_ok2"
        (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (VarE "C")
          (VarE "admininstr_lst")
          (CaseE
            (Seq (Atom mk_functype) Arg Arg)
            (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
          )
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (IterPr
        (RulePr "wf_admininstr" (Seq Arg) (TupE (VarE "v_admininstr")))
        List
        (iterexp "v_admininstr" (VarE "admininstr_lst"))
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
      "mk_Expr_ok2"
      (ExpP "s" (VarT "store"))
      (ExpP "C" (VarT "context"))
      (ExpP "admininstr_lst" (IterT (VarT "admininstr") List))
      (ExpP "t_opt" (IterT (VarT "valtype") Opt))
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE (VarE "s") (VarE "C") (VarE "admininstr_lst") (VarE "t_opt"))
      (RulePr
        "Instrs_ok2"
        (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (VarE "C")
          (VarE "admininstr_lst")
          (CaseE
            (Seq (Atom mk_functype) Arg Arg)
            (TupE (ListE) (LiftE (VarE "t_opt")))
          )
        )
      )
      (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
      (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
      (IterPr
        (RulePr "wf_admininstr" (Seq Arg) (TupE (VarE "v_admininstr")))
        List
        (iterexp "v_admininstr" (VarE "admininstr_lst"))
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
    "mk_Globalinst_ok"
    (ExpP "s" (VarT "store"))
    (ExpP "v_mut" (VarT "mut"))
    (ExpP "t" (VarT "valtype"))
    (ExpP "v_val" (VarT "val"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Seq (Atom mk_globaltype) Arg Arg)
            (TupE (VarE "v_mut") (VarE "t"))
          )
        )
        (expfield (Atom VALUE) (VarE "v_val"))
      )
      (CaseE
        (Seq (Atom mk_globaltype) Arg Arg)
        (TupE (VarE "v_mut") (VarE "t"))
      )
    )
    (RulePr
      "Globaltype_ok"
      (Infix (Seq) |- (Infix Arg : (Atom OK)))
      (CaseE
        (Seq (Atom mk_globaltype) Arg Arg)
        (TupE (VarE "v_mut") (VarE "t"))
      )
    )
    (RulePr
      "Val_ok"
      (Infix (Seq) |- (Infix Arg : Arg))
      (TupE (VarE "v_val") (VarE "t"))
    )
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
    (RulePr
      "wf_globalinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Seq (Atom mk_globaltype) Arg Arg)
              (TupE (VarE "v_mut") (VarE "t"))
            )
          )
          (expfield (Atom VALUE) (VarE "v_val"))
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
    "mk_Meminst_ok"
    (ExpP "s" (VarT "store"))
    (ExpP "v_n" (VarT "n"))
    (ExpP "m_opt" (IterT (VarT "m") Opt))
    (ExpP "b_lst" (IterT (VarT "byte") List))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Seq (Atom mk_limits) Arg Arg)
            (TupE
              (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
              (IterE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
                Opt
                (iterexp "v_m" (VarE "m_opt"))
              )
            )
          )
        )
        (expfield (Atom BYTES) (VarE "b_lst"))
      )
      (CaseE
        (Seq (Atom mk_limits) Arg Arg)
        (TupE
          (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
          (IterE
            (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
            Opt
            (iterexp "v_m" (VarE "m_opt"))
          )
        )
      )
    )
    (RulePr
      "Memtype_ok"
      (Infix (Seq) |- (Infix Arg : (Atom OK)))
      (CaseE
        (Seq (Atom mk_limits) Arg Arg)
        (TupE
          (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
          (IterE
            (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
            Opt
            (iterexp "v_m" (VarE "m_opt"))
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (LenE (VarE "b_lst"))
        (BinE
          MulOp
          nat
          (VarE "v_n")
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
                (IterE
                  (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
                  Opt
                  (iterexp "v_m" (VarE "m_opt"))
                )
              )
            )
          )
          (expfield (Atom BYTES) (VarE "b_lst"))
        )
      )
    )
    (RulePr
      "wf_limits"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_limits) Arg Arg)
          (TupE
            (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
            (IterE
              (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
              Opt
              (iterexp "v_m" (VarE "m_opt"))
            )
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
    "mk_Tableinst_ok"
    (ExpP "s" (VarT "store"))
    (ExpP "v_n" (VarT "n"))
    (ExpP "m_opt" (IterT (VarT "m") Opt))
    (ExpP "fa_opt_lst" (IterT (IterT (VarT "funcaddr") Opt) List))
    (ExpP "ft_opt_lst" (IterT (IterT (VarT "functype") Opt) List))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Seq (Atom mk_limits) Arg Arg)
            (TupE
              (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
              (IterE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
                Opt
                (iterexp "v_m" (VarE "m_opt"))
              )
            )
          )
        )
        (expfield (Atom REFS) (VarE "fa_opt_lst"))
      )
      (CaseE
        (Seq (Atom mk_limits) Arg Arg)
        (TupE
          (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
          (IterE
            (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
            Opt
            (iterexp "v_m" (VarE "m_opt"))
          )
        )
      )
    )
    (RulePr
      "Tabletype_ok"
      (Infix (Seq) |- (Infix Arg : (Atom OK)))
      (CaseE
        (Seq (Atom mk_limits) Arg Arg)
        (TupE
          (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
          (IterE
            (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
            Opt
            (iterexp "v_m" (VarE "m_opt"))
          )
        )
      )
    )
    (IfPr
      (CmpE EqOp bool (LenE (VarE "fa_opt_lst")) (LenE (VarE "ft_opt_lst")))
    )
    (IterPr
      (IfPr
        (BinE
          EquivOp
          bool
          (CmpE EqOp bool (VarE "fa_opt") (OptE))
          (CmpE EqOp bool (VarE "ft_opt") (OptE))
        )
      )
      List
      (iterexp "fa_opt" (VarE "fa_opt_lst"))
      (iterexp "ft_opt" (VarE "ft_opt_lst"))
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
        (iterexp "fa" (VarE "fa_opt"))
        (iterexp "ft" (VarE "ft_opt"))
      )
      List
      (iterexp "fa_opt" (VarE "fa_opt_lst"))
      (iterexp "ft_opt" (VarE "ft_opt_lst"))
    )
    (IfPr (CmpE EqOp bool (LenE (VarE "fa_opt_lst")) (VarE "v_n")))
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
    (RulePr
      "wf_tableinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Seq (Atom mk_limits) Arg Arg)
              (TupE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
                (IterE
                  (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
                  Opt
                  (iterexp "v_m" (VarE "m_opt"))
                )
              )
            )
          )
          (expfield (Atom REFS) (VarE "fa_opt_lst"))
        )
      )
    )
    (RulePr
      "wf_limits"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_limits) Arg Arg)
          (TupE
            (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
            (IterE
              (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
              Opt
              (iterexp "v_m" (VarE "m_opt"))
            )
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
        (iterexp "ft" (VarE "ft_opt"))
      )
      List
      (iterexp "ft_opt" (VarE "ft_opt_lst"))
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
    "mk_Funcinst_ok"
    (ExpP "s" (VarT "store"))
    (ExpP "ft" (VarT "functype"))
    (ExpP "v_moduleinst" (VarT "moduleinst"))
    (ExpP "v_func" (VarT "func"))
    (ExpP "C" (VarT "context"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (StrE
        (expfield (Atom TYPE) (VarE "ft"))
        (expfield (Atom MODULE) (VarE "v_moduleinst"))
        (expfield (Atom CODE) (VarE "v_func"))
      )
      (VarE "ft")
    )
    (RulePr "Functype_ok" (Infix (Seq) |- (Infix Arg : (Atom OK))) (VarE "ft"))
    (RulePr
      "Moduleinst_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "s") (VarE "v_moduleinst") (VarE "C"))
    )
    (RulePr
      "Func_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "C") (VarE "v_func") (VarE "ft"))
    )
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_funcinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom TYPE) (VarE "ft"))
          (expfield (Atom MODULE) (VarE "v_moduleinst"))
          (expfield (Atom CODE) (VarE "v_func"))
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
    "mk_Store_ok"
    (ExpP "s" (VarT "store"))
    (ExpP "globalinst_lst" (IterT (VarT "globalinst") List))
    (ExpP "globaltype_lst" (IterT (VarT "globaltype") List))
    (ExpP "meminst_lst" (IterT (VarT "meminst") List))
    (ExpP "memtype_lst" (IterT (VarT "memtype") List))
    (ExpP "tableinst_lst" (IterT (VarT "tableinst") List))
    (ExpP "tabletype_lst" (IterT (VarT "tabletype") List))
    (ExpP "funcinst_lst" (IterT (VarT "funcinst") List))
    (ExpP "functype_lst" (IterT (VarT "functype") List))
    (Infix (Seq) |- (Infix Arg : (Atom OK)))
    (VarE "s")
    (IfPr
      (CmpE
        EqOp
        bool
        (LenE (VarE "globalinst_lst"))
        (LenE (VarE "globaltype_lst"))
      )
    )
    (IterPr
      (RulePr
        "Globalinst_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "s") (VarE "v_globalinst") (VarE "v_globaltype"))
      )
      List
      (iterexp "v_globalinst" (VarE "globalinst_lst"))
      (iterexp "v_globaltype" (VarE "globaltype_lst"))
    )
    (IfPr
      (CmpE EqOp bool (LenE (VarE "meminst_lst")) (LenE (VarE "memtype_lst")))
    )
    (IterPr
      (RulePr
        "Meminst_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "s") (VarE "v_meminst") (VarE "v_memtype"))
      )
      List
      (iterexp "v_meminst" (VarE "meminst_lst"))
      (iterexp "v_memtype" (VarE "memtype_lst"))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (LenE (VarE "tableinst_lst"))
        (LenE (VarE "tabletype_lst"))
      )
    )
    (IterPr
      (RulePr
        "Tableinst_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "s") (VarE "v_tableinst") (VarE "v_tabletype"))
      )
      List
      (iterexp "v_tableinst" (VarE "tableinst_lst"))
      (iterexp "v_tabletype" (VarE "tabletype_lst"))
    )
    (IfPr
      (CmpE EqOp bool (LenE (VarE "funcinst_lst")) (LenE (VarE "functype_lst")))
    )
    (IterPr
      (RulePr
        "Funcinst_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "s") (VarE "v_funcinst") (VarE "v_functype"))
      )
      List
      (iterexp "v_funcinst" (VarE "funcinst_lst"))
      (iterexp "v_functype" (VarE "functype_lst"))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "s")
        (StrE
          (expfield (Atom FUNCS) (VarE "funcinst_lst"))
          (expfield (Atom GLOBALS) (VarE "globalinst_lst"))
          (expfield (Atom TABLES) (VarE "tableinst_lst"))
          (expfield (Atom MEMS) (VarE "meminst_lst"))
        )
      )
    )
    (RulePr "wf_store" (Seq Arg) (TupE (VarE "s")))
    (IterPr
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "v_memtype")))
      List
      (iterexp "v_memtype" (VarE "memtype_lst"))
    )
    (IterPr
      (RulePr "wf_limits" (Seq Arg) (TupE (VarE "v_tabletype")))
      List
      (iterexp "v_tabletype" (VarE "tabletype_lst"))
    )
    (RulePr
      "wf_store"
      (Seq Arg)
      (TupE
        (StrE
          (expfield (Atom FUNCS) (VarE "funcinst_lst"))
          (expfield (Atom GLOBALS) (VarE "globalinst_lst"))
          (expfield (Atom TABLES) (VarE "tableinst_lst"))
          (expfield (Atom MEMS) (VarE "meminst_lst"))
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
    "mk_Extend_globalinst"
    (ExpP "v_mut" (VarT "mut"))
    (ExpP "t" (VarT "valtype"))
    (ExpP "v_val" (VarT "val"))
    (ExpP "val'" (VarT "val"))
    (Seq Arg (Atom <=) Arg)
    (TupE
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Seq (Atom mk_globaltype) Arg Arg)
            (TupE (VarE "v_mut") (VarE "t"))
          )
        )
        (expfield (Atom VALUE) (VarE "v_val"))
      )
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Seq (Atom mk_globaltype) Arg Arg)
            (TupE (VarE "v_mut") (VarE "t"))
          )
        )
        (expfield (Atom VALUE) (VarE "val'"))
      )
    )
    (IfPr
      (BinE
        OrOp
        bool
        (CmpE EqOp bool (VarE "v_mut") (OptE (CaseE (Atom MUT) (TupE))))
        (CmpE EqOp bool (VarE "v_val") (VarE "val'"))
      )
    )
    (RulePr
      "wf_globalinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Seq (Atom mk_globaltype) Arg Arg)
              (TupE (VarE "v_mut") (VarE "t"))
            )
          )
          (expfield (Atom VALUE) (VarE "v_val"))
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
            (CaseE
              (Seq (Atom mk_globaltype) Arg Arg)
              (TupE (VarE "v_mut") (VarE "t"))
            )
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
    "mk_Extend_meminst"
    (ExpP "v_n" (VarT "n"))
    (ExpP "m_opt" (IterT (VarT "m") Opt))
    (ExpP "b_lst" (IterT (VarT "byte") List))
    (ExpP "n'" (VarT "n"))
    (ExpP "b'_lst" (IterT (VarT "byte") List))
    (Seq Arg (Atom <=) Arg)
    (TupE
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Seq (Atom mk_limits) Arg Arg)
            (TupE
              (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
              (IterE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
                Opt
                (iterexp "v_m" (VarE "m_opt"))
              )
            )
          )
        )
        (expfield (Atom BYTES) (VarE "b_lst"))
      )
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Seq (Atom mk_limits) Arg Arg)
            (TupE
              (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "n'")))
              (IterE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
                Opt
                (iterexp "v_m" (VarE "m_opt"))
              )
            )
          )
        )
        (expfield (Atom BYTES) (VarE "b'_lst"))
      )
    )
    (IfPr (CmpE LeOp nat (VarE "v_n") (VarE "n'")))
    (IfPr (CmpE LeOp nat (LenE (VarE "b_lst")) (LenE (VarE "b'_lst"))))
    (RulePr
      "wf_meminst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Seq (Atom mk_limits) Arg Arg)
              (TupE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
                (IterE
                  (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
                  Opt
                  (iterexp "v_m" (VarE "m_opt"))
                )
              )
            )
          )
          (expfield (Atom BYTES) (VarE "b_lst"))
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "n'")))
                (IterE
                  (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
                  Opt
                  (iterexp "v_m" (VarE "m_opt"))
                )
              )
            )
          )
          (expfield (Atom BYTES) (VarE "b'_lst"))
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
    "mk_Extend_tableinst"
    (ExpP "v_n" (VarT "n"))
    (ExpP "m_opt" (IterT (VarT "m") Opt))
    (ExpP "ref_lst" (IterT (VarT "funcaddr") List))
    (ExpP "n'" (VarT "n"))
    (ExpP "ref'_lst" (IterT (VarT "funcaddr") List))
    (Seq Arg (Atom <=) Arg)
    (TupE
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Seq (Atom mk_limits) Arg Arg)
            (TupE
              (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
              (IterE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
                Opt
                (iterexp "v_m" (VarE "m_opt"))
              )
            )
          )
        )
        (expfield
          (Atom REFS)
          (IterE (OptE (VarE "ref")) List (iterexp "ref" (VarE "ref_lst")))
        )
      )
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Seq (Atom mk_limits) Arg Arg)
            (TupE
              (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "n'")))
              (IterE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
                Opt
                (iterexp "v_m" (VarE "m_opt"))
              )
            )
          )
        )
        (expfield
          (Atom REFS)
          (IterE (OptE (VarE "ref'")) List (iterexp "ref'" (VarE "ref'_lst")))
        )
      )
    )
    (IfPr (CmpE LeOp nat (VarE "v_n") (VarE "n'")))
    (IfPr (CmpE LeOp nat (LenE (VarE "ref_lst")) (LenE (VarE "ref'_lst"))))
    (RulePr
      "wf_tableinst"
      (Seq Arg)
      (TupE
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Seq (Atom mk_limits) Arg Arg)
              (TupE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
                (IterE
                  (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
                  Opt
                  (iterexp "v_m" (VarE "m_opt"))
                )
              )
            )
          )
          (expfield
            (Atom REFS)
            (IterE (OptE (VarE "ref")) List (iterexp "ref" (VarE "ref_lst")))
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
              (Seq (Atom mk_limits) Arg Arg)
              (TupE
                (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "n'")))
                (IterE
                  (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
                  Opt
                  (iterexp "v_m" (VarE "m_opt"))
                )
              )
            )
          )
          (expfield
            (Atom REFS)
            (IterE (OptE (VarE "ref'")) List (iterexp "ref'" (VarE "ref'_lst")))
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
    "mk_Extend_funcinst"
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
    "mk_Extend_store"
    (ExpP "s" (VarT "store"))
    (ExpP "s'" (VarT "store"))
    (Seq Arg (Atom <=) Arg)
    (TupE (VarE "s") (VarE "s'"))
    (IterPr
      (IfPr (CmpE LtOp nat (VarE "a") (LenE (DotE (VarE "s") (Atom GLOBALS)))))
      (ListN (LenE (DotE (VarE "s") (Atom GLOBALS))) "a")
    )
    (IterPr
      (IfPr (CmpE LtOp nat (VarE "a") (LenE (DotE (VarE "s'") (Atom GLOBALS)))))
      (ListN (LenE (DotE (VarE "s") (Atom GLOBALS))) "a")
    )
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
      (IfPr (CmpE LtOp nat (VarE "a") (LenE (DotE (VarE "s") (Atom MEMS)))))
      (ListN (LenE (DotE (VarE "s") (Atom MEMS))) "a")
    )
    (IterPr
      (IfPr (CmpE LtOp nat (VarE "a") (LenE (DotE (VarE "s'") (Atom MEMS)))))
      (ListN (LenE (DotE (VarE "s") (Atom MEMS))) "a")
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
      (IfPr (CmpE LtOp nat (VarE "a") (LenE (DotE (VarE "s") (Atom TABLES)))))
      (ListN (LenE (DotE (VarE "s") (Atom TABLES))) "a")
    )
    (IterPr
      (IfPr (CmpE LtOp nat (VarE "a") (LenE (DotE (VarE "s'") (Atom TABLES)))))
      (ListN (LenE (DotE (VarE "s") (Atom TABLES))) "a")
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
      (IfPr (CmpE LtOp nat (VarE "a") (LenE (DotE (VarE "s") (Atom FUNCS)))))
      (ListN (LenE (DotE (VarE "s") (Atom FUNCS))) "a")
    )
    (IterPr
      (IfPr (CmpE LtOp nat (VarE "a") (LenE (DotE (VarE "s'") (Atom FUNCS)))))
      (ListN (LenE (DotE (VarE "s") (Atom FUNCS))) "a")
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
    "mk_State_ok"
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "C" (VarT "context"))
    (Infix (Seq) |- (Infix Arg : Arg))
    (TupE
      (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f")))
      (VarE "C")
    )
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
      (TupE (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
    )
  )
)
(RelD
  "Config_ok"
  (Infix (Seq) |- (Infix Arg : Arg))
  (TupT (typbind "_" (VarT "config")) (typbind "_" (VarT "resulttype")))
  (RuleD
    "mk_Config_ok"
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "admininstr_lst" (IterT (VarT "admininstr") List))
    (ExpP "t_opt" (IterT (VarT "valtype") Opt))
    (ExpP "C" (VarT "context"))
    (Infix (Seq) |- (Infix Arg : Arg))
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE
          (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f")))
          (VarE "admininstr_lst")
        )
      )
      (VarE "t_opt")
    )
    (RulePr
      "State_ok"
      (Infix (Seq) |- (Infix Arg : Arg))
      (TupE
        (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f")))
        (VarE "C")
      )
    )
    (RulePr
      "Expr_ok2"
      (Infix (Infix Arg ; Arg) |- (Infix Arg : Arg))
      (TupE (VarE "s") (VarE "C") (VarE "admininstr_lst") (VarE "t_opt"))
    )
    (RulePr "wf_context" (Seq Arg) (TupE (VarE "C")))
    (RulePr
      "wf_config"
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom mk_config) Arg Arg)
          (TupE
            (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f")))
            (VarE "admininstr_lst")
          )
        )
      )
    )
    (RulePr
      "wf_state"
      (Seq Arg)
      (TupE (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
    )
  )
)
(GramD
  "Bbyte"
  (VarT "byte")
  (ProdD
    (ExpP "<implicit_prod_result>" nat)
    (AttrG (VarE "<implicit_prod_result>") (RangeG (NumG 0x00) (NumG 0xFF)))
    (CaseE (Seq (Atom mk_byte) Arg) (TupE (VarE "<implicit_prod_result>")))
  )
)
(RecD
  (GramD
    "BuN"
    (ExpP "v_N" (VarT "N"))
    (VarT "uN")
    (ProdD
      (ExpP "v_n" (VarT "n"))
      (AttrG
        (CaseE (Seq (Atom mk_byte) Arg) (TupE (VarE "v_n")))
        (VarG "Bbyte")
      )
      (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
      (IfPr
        (BinE
          AndOp
          bool
          (CmpE
            LtOp
            nat
            (VarE "v_n")
            (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7)))
          )
          (CmpE
            LtOp
            nat
            (VarE "v_n")
            (BinE PowOp nat (NumE (Nat 2)) (VarE "v_N"))
          )
        )
      )
    )
    (ProdD
      (ExpP "v_m" (VarT "m"))
      (ExpP "v_n" (VarT "n"))
      (SeqG
        (SeqG
          (AttrG
            (CaseE (Seq (Atom mk_byte) Arg) (TupE (VarE "v_n")))
            (VarG "Bbyte")
          )
        )
        (SeqG
          (AttrG
            (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
            (VarG
              "BuN"
              (ExpA
                (CvtE
                  int
                  nat
                  (BinE
                    SubOp
                    int
                    (CvtE nat int (VarE "v_N"))
                    (CvtE nat int (NumE (Nat 7)))
                  )
                )
              )
            )
          )
        )
      )
      (CaseE
        (Seq (Atom mk_uN) Arg)
        (TupE
          (BinE
            AddOp
            nat
            (BinE
              MulOp
              nat
              (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7)))
              (VarE "v_m")
            )
            (CvtE
              int
              nat
              (BinE
                SubOp
                int
                (CvtE nat int (VarE "v_n"))
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
            (VarE "v_n")
            (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7)))
          )
          (CmpE GtOp nat (VarE "v_N") (NumE (Nat 7)))
        )
      )
    )
  )
)
(GramD
  "Bu32"
  (VarT "u32")
  (ProdD
    (ExpP "<implicit_prod_result>" (VarT "uN"))
    (AttrG (VarE "<implicit_prod_result>") (VarG "BuN" (ExpA (NumE (Nat 32)))))
    (VarE "<implicit_prod_result>")
  )
)
(GramD
  "Blist"
  (TypP "el")
  (GramP "BX" (VarT "el"))
  (IterT (VarT "el") List)
  (ProdD
    (ExpP "v_n" (VarT "n"))
    (ExpP "el_lst" (IterT (VarT "el") List))
    (SeqG
      (SeqG
        (AttrG (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n"))) (VarG "Bu32"))
      )
      (SeqG
        (IterG
          (AttrG (VarE "el") (VarG "BX"))
          (ListN (VarE "v_n"))
          (iterexp "el" (VarE "el_lst"))
        )
      )
    )
    (VarE "el_lst")
  )
)
(HintD (GramH "BuN" (hint "show" "Bu#%")))
(RecD
  (GramD
    "BsN"
    (ExpP "v_N" (VarT "N"))
    (VarT "sN")
    (ProdD
      (ExpP "v_n" (VarT "n"))
      (AttrG
        (CaseE (Seq (Atom mk_byte) Arg) (TupE (VarE "v_n")))
        (VarG "Bbyte")
      )
      (CaseE (Seq (Atom mk_sN) Arg) (TupE (CvtE nat int (VarE "v_n"))))
      (IfPr
        (BinE
          AndOp
          bool
          (CmpE
            LtOp
            nat
            (VarE "v_n")
            (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 6)))
          )
          (CmpE
            LtOp
            nat
            (VarE "v_n")
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
                  (CvtE nat int (VarE "v_N"))
                  (CvtE nat int (NumE (Nat 1)))
                )
              )
            )
          )
        )
      )
    )
    (ProdD
      (ExpP "v_n" (VarT "n"))
      (AttrG
        (CaseE (Seq (Atom mk_byte) Arg) (TupE (VarE "v_n")))
        (VarG "Bbyte")
      )
      (CaseE
        (Seq (Atom mk_sN) Arg)
        (TupE
          (BinE
            SubOp
            int
            (CvtE nat int (VarE "v_n"))
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
              (VarE "v_n")
            )
            (CmpE
              LtOp
              nat
              (VarE "v_n")
              (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7)))
            )
          )
          (CmpE
            GeOp
            int
            (CvtE nat int (VarE "v_n"))
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
                      (CvtE nat int (VarE "v_N"))
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
      (ExpP "v_n" (VarT "n"))
      (SeqG
        (SeqG
          (AttrG
            (CaseE (Seq (Atom mk_byte) Arg) (TupE (VarE "v_n")))
            (VarG "Bbyte")
          )
        )
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
                    (CvtE nat int (VarE "v_N"))
                    (CvtE nat int (NumE (Nat 7)))
                  )
                )
              )
            )
          )
        )
      )
      (CaseE
        (Seq (Atom mk_sN) Arg)
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
                  (CvtE nat int (VarE "v_n"))
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
            (VarE "v_n")
            (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7)))
          )
          (CmpE GtOp nat (VarE "v_N") (NumE (Nat 7)))
        )
      )
    )
  )
)
(HintD (GramH "BsN" (hint "show" "Bs#%")))
(GramD
  "BiN"
  (ExpP "v_N" (VarT "N"))
  (VarT "iN")
  (ProdD
    (ExpP "i" (VarT "sN"))
    (ExpP "var_0" nat)
    (AttrG (VarE "i") (VarG "BsN" (ExpA (VarE "v_N"))))
    (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "var_0")))
    (RulePr
      "fun_inv_signed_"
      (Seq Arg Arg Arg)
      (TupE
        (VarE "v_N")
        (ProjE (CallE "proj_sN_0" (ExpA (VarE "i"))) 0)
        (VarE "var_0")
      )
    )
  )
)
(HintD (GramH "BiN" (hint "show" "Bi#%")))
(GramD
  "BfN"
  (ExpP "v_N" (VarT "N"))
  (VarT "fN")
  (ProdD
    (ExpP "b_lst" (IterT (VarT "byte") List))
    (AttrG
      (VarE "b_lst")
      (IterG
        (VarG "Bbyte")
        (ListN
          (CvtE
            rat
            nat
            (BinE
              DivOp
              rat
              (CvtE nat rat (VarE "v_N"))
              (CvtE nat rat (NumE (Nat 8)))
            )
          )
        )
      )
    )
    (CallE "inv_fbytes_" (ExpA (VarE "v_N")) (ExpA (VarE "b_lst")))
  )
)
(HintD (GramH "BfN" (hint "show" "Bf#%")))
(GramD
  "Bu64"
  (VarT "u64")
  (ProdD
    (ExpP "<implicit_prod_result>" (VarT "uN"))
    (AttrG (VarE "<implicit_prod_result>") (VarG "BuN" (ExpA (NumE (Nat 64)))))
    (VarE "<implicit_prod_result>")
  )
)
(GramD
  "Bi32"
  (VarT "i32")
  (ProdD
    (ExpP "<implicit_prod_result>" (VarT "iN"))
    (AttrG (VarE "<implicit_prod_result>") (VarG "BiN" (ExpA (NumE (Nat 32)))))
    (VarE "<implicit_prod_result>")
  )
)
(GramD
  "Bi64"
  (VarT "i64")
  (ProdD
    (ExpP "<implicit_prod_result>" (VarT "iN"))
    (AttrG (VarE "<implicit_prod_result>") (VarG "BiN" (ExpA (NumE (Nat 64)))))
    (VarE "<implicit_prod_result>")
  )
)
(GramD
  "Bf32"
  (VarT "f32")
  (ProdD
    (ExpP "<implicit_prod_result>" (VarT "fN"))
    (AttrG (VarE "<implicit_prod_result>") (VarG "BfN" (ExpA (NumE (Nat 32)))))
    (VarE "<implicit_prod_result>")
  )
)
(GramD
  "Bf64"
  (VarT "f64")
  (ProdD
    (ExpP "<implicit_prod_result>" (VarT "fN"))
    (AttrG (VarE "<implicit_prod_result>") (VarG "BfN" (ExpA (NumE (Nat 64)))))
    (VarE "<implicit_prod_result>")
  )
)
(GramD
  "Bname"
  (VarT "name")
  (ProdD
    (ExpP "v_name" (VarT "name"))
    (ExpP "b_lst" (IterT (VarT "byte") List))
    (ExpP "var_0" (IterT (VarT "byte") List))
    (AttrG
      (VarE "b_lst")
      (VarG "Blist" (TypA (VarT "byte")) (GramA (VarG "Bbyte")))
    )
    (VarE "v_name")
    (RulePr
      "fun_utf8"
      (Seq Arg Arg)
      (TupE
        (ProjE (CallE "proj_name_0" (ExpA (VarE "v_name"))) 0)
        (VarE "var_0")
      )
    )
    (IfPr (CmpE EqOp bool (VarE "var_0") (VarE "b_lst")))
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
    (ExpP "t_lst" (IterT (VarT "valtype") List))
    (AttrG
      (VarE "t_lst")
      (VarG "Blist" (TypA (VarT "valtype")) (GramA (VarG "Bvaltype")))
    )
    (VarE "t_lst")
  )
)
(GramD
  "Bfunctype"
  (VarT "functype")
  (ProdD
    (ExpP "t_1_lst" (IterT (VarT "valtype") List))
    (ExpP "t_2_lst" (IterT (VarT "valtype") List))
    (SeqG
      (SeqG (NumG 0x60))
      (SeqG (AttrG (VarE "t_1_lst") (VarG "Bresulttype")))
      (SeqG (AttrG (VarE "t_2_lst") (VarG "Bresulttype")))
    )
    (CaseE
      (Seq (Atom mk_functype) Arg Arg)
      (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
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
    (ExpP "v_n" (VarT "n"))
    (SeqG
      (SeqG (NumG 0x00))
      (SeqG
        (AttrG (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n"))) (VarG "Bu32"))
      )
    )
    (CaseE
      (Seq (Atom mk_limits) Arg Arg)
      (TupE (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n"))) (OptE))
    )
  )
  (ProdD
    (ExpP "v_n" (VarT "n"))
    (ExpP "v_m" (VarT "m"))
    (SeqG
      (SeqG (NumG 0x01))
      (SeqG
        (AttrG (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n"))) (VarG "Bu32"))
      )
      (SeqG
        (AttrG (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m"))) (VarG "Bu32"))
      )
    )
    (CaseE
      (Seq (Atom mk_limits) Arg Arg)
      (TupE
        (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n")))
        (OptE (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m"))))
      )
    )
  )
)
(GramD
  "Bglobaltype"
  (VarT "globaltype")
  (ProdD
    (ExpP "v_mut" (VarT "mut"))
    (ExpP "t" (VarT "valtype"))
    (SeqG
      (SeqG (AttrG (VarE "t") (VarG "Bvaltype")))
      (SeqG (AttrG (VarE "v_mut") (VarG "Bmut")))
    )
    (CaseE (Seq (Atom mk_globaltype) Arg Arg) (TupE (VarE "v_mut") (VarE "t")))
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
    (ExpP "v_n" (VarT "n"))
    (ExpP "v_m" (VarT "m"))
    (SeqG
      (SeqG
        (AttrG (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n"))) (VarG "Bu32"))
      )
      (SeqG
        (AttrG (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m"))) (VarG "Bu32"))
      )
    )
    (StrE
      (expfield (Atom ALIGN) (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n"))))
      (expfield
        (Atom OFFSET)
        (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_m")))
      )
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
      (ExpP "in_lst" (IterT (VarT "instr") List))
      (SeqG
        (SeqG (NumG 0x02))
        (SeqG (AttrG (VarE "bt") (VarG "Bblocktype")))
        (SeqG
          (IterG
            (AttrG (VarE "in") (VarG "Binstr"))
            List
            (iterexp "in" (VarE "in_lst"))
          )
        )
        (SeqG (NumG 0x0B))
      )
      (CaseE (Seq (Atom BLOCK) Arg Arg) (TupE (VarE "bt") (VarE "in_lst")))
    )
    (ProdD
      (ExpP "bt" (VarT "blocktype"))
      (ExpP "in_lst" (IterT (VarT "instr") List))
      (SeqG
        (SeqG (NumG 0x03))
        (SeqG (AttrG (VarE "bt") (VarG "Bblocktype")))
        (SeqG
          (IterG
            (AttrG (VarE "in") (VarG "Binstr"))
            List
            (iterexp "in" (VarE "in_lst"))
          )
        )
        (SeqG (NumG 0x0B))
      )
      (CaseE (Seq (Atom LOOP) Arg Arg) (TupE (VarE "bt") (VarE "in_lst")))
    )
    (ProdD
      (ExpP "bt" (VarT "blocktype"))
      (ExpP "in_lst" (IterT (VarT "instr") List))
      (SeqG
        (SeqG (NumG 0x04))
        (SeqG (AttrG (VarE "bt") (VarG "Bblocktype")))
        (SeqG
          (IterG
            (AttrG (VarE "in") (VarG "Binstr"))
            List
            (iterexp "in" (VarE "in_lst"))
          )
        )
        (SeqG (NumG 0x0B))
      )
      (CaseE
        (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
        (TupE (VarE "bt") (VarE "in_lst") (ListE))
      )
    )
    (ProdD
      (ExpP "bt" (VarT "blocktype"))
      (ExpP "in_1_lst" (IterT (VarT "instr") List))
      (ExpP "in_2_lst" (IterT (VarT "instr") List))
      (SeqG
        (SeqG (NumG 0x04))
        (SeqG (AttrG (VarE "bt") (VarG "Bblocktype")))
        (SeqG
          (IterG
            (AttrG (VarE "in_1") (VarG "Binstr"))
            List
            (iterexp "in_1" (VarE "in_1_lst"))
          )
        )
        (SeqG (NumG 0x05))
        (SeqG
          (IterG
            (AttrG (VarE "in_2") (VarG "Binstr"))
            List
            (iterexp "in_2" (VarE "in_2_lst"))
          )
        )
        (SeqG (NumG 0x0B))
      )
      (CaseE
        (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
        (TupE (VarE "bt") (VarE "in_1_lst") (VarE "in_2_lst"))
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
      (ExpP "l_lst" (IterT (VarT "labelidx") List))
      (ExpP "l_N" (VarT "labelidx"))
      (SeqG
        (SeqG (NumG 0x0E))
        (SeqG
          (AttrG
            (VarE "l_lst")
            (VarG "Blist" (TypA (VarT "labelidx")) (GramA (VarG "Blabelidx")))
          )
        )
        (SeqG (AttrG (VarE "l_N") (VarG "Blabelidx")))
      )
      (CaseE (Seq (Atom BR_TABLE) Arg Arg) (TupE (VarE "l_lst") (VarE "l_N")))
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
      (CaseE (Seq (Atom LOCAL_GET) Arg) (TupE (VarE "x")))
    )
    (ProdD
      (ExpP "x" (VarT "idx"))
      (SeqG (SeqG (NumG 0x21)) (SeqG (AttrG (VarE "x") (VarG "Blocalidx"))))
      (CaseE (Seq (Atom LOCAL_SET) Arg) (TupE (VarE "x")))
    )
    (ProdD
      (ExpP "x" (VarT "idx"))
      (SeqG (SeqG (NumG 0x22)) (SeqG (AttrG (VarE "x") (VarG "Blocalidx"))))
      (CaseE (Seq (Atom LOCAL_TEE) Arg) (TupE (VarE "x")))
    )
    (ProdD
      (ExpP "x" (VarT "idx"))
      (SeqG (SeqG (NumG 0x23)) (SeqG (AttrG (VarE "x") (VarG "Bglobalidx"))))
      (CaseE (Seq (Atom GLOBAL_GET) Arg) (TupE (VarE "x")))
    )
    (ProdD
      (ExpP "x" (VarT "idx"))
      (SeqG (SeqG (NumG 0x24)) (SeqG (AttrG (VarE "x") (VarG "Bglobalidx"))))
      (CaseE (Seq (Atom GLOBAL_SET) Arg) (TupE (VarE "x")))
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
                  (Seq (Atom mk_loadop_Inn) Arg Arg)
                  (TupE
                    (CaseE (Seq (Atom mk_sz) Arg) (TupE (NumE (Nat 8))))
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
                  (Seq (Atom mk_loadop_Inn) Arg Arg)
                  (TupE
                    (CaseE (Seq (Atom mk_sz) Arg) (TupE (NumE (Nat 8))))
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
                  (Seq (Atom mk_loadop_Inn) Arg Arg)
                  (TupE
                    (CaseE (Seq (Atom mk_sz) Arg) (TupE (NumE (Nat 16))))
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
                  (Seq (Atom mk_loadop_Inn) Arg Arg)
                  (TupE
                    (CaseE (Seq (Atom mk_sz) Arg) (TupE (NumE (Nat 16))))
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
                  (Seq (Atom mk_loadop_Inn) Arg Arg)
                  (TupE
                    (CaseE (Seq (Atom mk_sz) Arg) (TupE (NumE (Nat 8))))
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
                  (Seq (Atom mk_loadop_Inn) Arg Arg)
                  (TupE
                    (CaseE (Seq (Atom mk_sz) Arg) (TupE (NumE (Nat 8))))
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
                  (Seq (Atom mk_loadop_Inn) Arg Arg)
                  (TupE
                    (CaseE (Seq (Atom mk_sz) Arg) (TupE (NumE (Nat 16))))
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
                  (Seq (Atom mk_loadop_Inn) Arg Arg)
                  (TupE
                    (CaseE (Seq (Atom mk_sz) Arg) (TupE (NumE (Nat 16))))
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
                  (Seq (Atom mk_loadop_Inn) Arg Arg)
                  (TupE
                    (CaseE (Seq (Atom mk_sz) Arg) (TupE (NumE (Nat 32))))
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
                  (Seq (Atom mk_loadop_Inn) Arg Arg)
                  (TupE
                    (CaseE (Seq (Atom mk_sz) Arg) (TupE (NumE (Nat 32))))
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
          (OptE (CaseE (Seq (Atom mk_sz) Arg) (TupE (NumE (Nat 8)))))
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
          (OptE (CaseE (Seq (Atom mk_sz) Arg) (TupE (NumE (Nat 16)))))
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
          (OptE (CaseE (Seq (Atom mk_sz) Arg) (TupE (NumE (Nat 8)))))
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
          (OptE (CaseE (Seq (Atom mk_sz) Arg) (TupE (NumE (Nat 16)))))
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
          (OptE (CaseE (Seq (Atom mk_sz) Arg) (TupE (NumE (Nat 32)))))
          (VarE "ao")
        )
      )
    )
    (ProdD
      (SeqG (SeqG (NumG 0x3F)) (SeqG (NumG 0x00)))
      (CaseE (Atom MEMORY_SIZE) (TupE))
    )
    (ProdD
      (SeqG (SeqG (NumG 0x40)) (SeqG (NumG 0x00)))
      (CaseE (Atom MEMORY_GROW) (TupE))
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
    (ExpP "in_lst" (IterT (VarT "instr") List))
    (SeqG
      (SeqG
        (IterG
          (AttrG (VarE "in") (VarG "Binstr"))
          List
          (iterexp "in" (VarE "in_lst"))
        )
      )
      (SeqG (NumG 0x0B))
    )
    (VarE "in_lst")
  )
)
(GramD
  "Bsection_"
  (ExpP "v_N" (VarT "N"))
  (TypP "en")
  (GramP "BX" (IterT (VarT "en") List))
  (IterT (VarT "en") List)
  (ProdD
    (ExpP "en_lst" (IterT (VarT "en") List))
    (ExpP "len" nat)
    (SeqG
      (SeqG
        (AttrG
          (CaseE (Seq (Atom mk_byte) Arg) (TupE (VarE "v_N")))
          (VarG "Bbyte")
        )
      )
      (SeqG
        (AttrG (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "len"))) (VarG "Bu32"))
      )
      (SeqG (AttrG (VarE "en_lst") (VarG "BX")))
    )
    (VarE "en_lst")
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
    (ExpP "ty_lst" (IterT (VarT "type") List))
    (AttrG
      (VarE "ty_lst")
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 1)))
        (TypA (VarT "type"))
        (GramA (VarG "Blist" (TypA (VarT "type")) (GramA (VarG "Btype"))))
      )
    )
    (VarE "ty_lst")
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
    (ExpP "im_lst" (IterT (VarT "import") List))
    (AttrG
      (VarE "im_lst")
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 2)))
        (TypA (VarT "import"))
        (GramA (VarG "Blist" (TypA (VarT "import")) (GramA (VarG "Bimport"))))
      )
    )
    (VarE "im_lst")
  )
)
(HintD (GramH "Bimportsec" (hint "desc" "\"import section\"")))
(GramD
  "Bfuncsec"
  (IterT (VarT "typeidx") List)
  (ProdD
    (ExpP "x_lst" (IterT (VarT "idx") List))
    (AttrG
      (VarE "x_lst")
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 3)))
        (TypA (VarT "typeidx"))
        (GramA (VarG "Blist" (TypA (VarT "typeidx")) (GramA (VarG "Btypeidx"))))
      )
    )
    (VarE "x_lst")
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
    (ExpP "tab_lst" (IterT (VarT "table") List))
    (AttrG
      (VarE "tab_lst")
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 4)))
        (TypA (VarT "table"))
        (GramA (VarG "Blist" (TypA (VarT "table")) (GramA (VarG "Btable"))))
      )
    )
    (VarE "tab_lst")
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
    (ExpP "mem_lst" (IterT (VarT "mem") List))
    (AttrG
      (VarE "mem_lst")
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 5)))
        (TypA (VarT "mem"))
        (GramA (VarG "Blist" (TypA (VarT "mem")) (GramA (VarG "Bmem"))))
      )
    )
    (VarE "mem_lst")
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
    (ExpP "glob_lst" (IterT (VarT "global") List))
    (AttrG
      (VarE "glob_lst")
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 6)))
        (TypA (VarT "global"))
        (GramA (VarG "Blist" (TypA (VarT "global")) (GramA (VarG "Bglobal"))))
      )
    )
    (VarE "glob_lst")
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
    (ExpP "ex_lst" (IterT (VarT "export") List))
    (AttrG
      (VarE "ex_lst")
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 7)))
        (TypA (VarT "export"))
        (GramA (VarG "Blist" (TypA (VarT "export")) (GramA (VarG "Bexport"))))
      )
    )
    (VarE "ex_lst")
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
    (ExpP "v_startopt" (VarT "startopt"))
    (AttrG
      (VarE "v_startopt")
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 8)))
        (TypA (VarT "start"))
        (GramA (VarG "Bstart"))
      )
    )
    (TheE (CallE "opt_" (TypA (VarT "start")) (ExpA (VarE "v_startopt"))))
  )
)
(HintD (GramH "Bstartsec" (hint "desc" "\"start section\"")))
(GramD
  "Belem"
  (VarT "elem")
  (ProdD
    (ExpP "e" (VarT "expr"))
    (ExpP "x_lst" (IterT (VarT "idx") List))
    (SeqG
      (SeqG (NumG 0x00))
      (SeqG (AttrG (VarE "e") (VarG "Bexpr")))
      (SeqG
        (AttrG
          (VarE "x_lst")
          (VarG "Blist" (TypA (VarT "funcidx")) (GramA (VarG "Bfuncidx")))
        )
      )
    )
    (CaseE (Seq (Atom ELEM) Arg Arg) (TupE (VarE "e") (VarE "x_lst")))
  )
)
(GramD
  "Belemsec"
  (IterT (VarT "elem") List)
  (ProdD
    (ExpP "elem_lst" (IterT (VarT "elem") List))
    (AttrG
      (VarE "elem_lst")
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 9)))
        (TypA (VarT "elem"))
        (GramA (VarG "Blist" (TypA (VarT "elem")) (GramA (VarG "Belem"))))
      )
    )
    (VarE "elem_lst")
  )
)
(HintD (GramH "Belemsec" (hint "desc" "\"element section\"")))
(GramD
  "Blocals"
  (IterT (VarT "local") List)
  (ProdD
    (ExpP "t" (VarT "valtype"))
    (ExpP "v_n" (VarT "n"))
    (SeqG
      (SeqG
        (AttrG (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "v_n"))) (VarG "Bu32"))
      )
      (SeqG (AttrG (VarE "t") (VarG "Bvaltype")))
    )
    (IterE
      (CaseE (Seq (Atom LOCAL) Arg) (TupE (VarE "t")))
      (ListN (VarE "v_n"))
    )
  )
)
(HintD (GramH "Blocals" (hint "desc" "\"local\"")))
(GramD
  "Bfunc"
  (VarT "code")
  (ProdD
    (ExpP "local_lst_lst" (IterT (IterT (VarT "local") List) List))
    (ExpP "v_expr" (VarT "expr"))
    (SeqG
      (SeqG
        (AttrG
          (VarE "local_lst_lst")
          (VarG
            "Blist"
            (TypA (IterT (VarT "local") List))
            (GramA (VarG "Blocals"))
          )
        )
      )
      (SeqG (AttrG (VarE "v_expr") (VarG "Bexpr")))
    )
    (TupE
      (CallE "concat_" (TypA (VarT "local")) (ExpA (VarE "local_lst_lst")))
      (VarE "v_expr")
    )
  )
)
(GramD
  "Bcode"
  (VarT "code")
  (ProdD
    (ExpP "v_code" (VarT "code"))
    (ExpP "len" nat)
    (SeqG
      (SeqG
        (AttrG (CaseE (Seq (Atom mk_uN) Arg) (TupE (VarE "len"))) (VarG "Bu32"))
      )
      (SeqG (AttrG (VarE "v_code") (VarG "Bfunc")))
    )
    (VarE "v_code")
    (IfPr (CmpE EqOp bool (VarE "len") (NumE (Nat 0))))
  )
)
(GramD
  "Bcodesec"
  (IterT (VarT "code") List)
  (ProdD
    (ExpP "code_lst" (IterT (VarT "code") List))
    (AttrG
      (VarE "code_lst")
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 10)))
        (TypA (VarT "code"))
        (GramA (VarG "Blist" (TypA (VarT "code")) (GramA (VarG "Bcode"))))
      )
    )
    (VarE "code_lst")
  )
)
(HintD (GramH "Bcodesec" (hint "desc" "\"code section\"")))
(GramD
  "Bdata"
  (VarT "data")
  (ProdD
    (ExpP "e" (VarT "expr"))
    (ExpP "b_lst" (IterT (VarT "byte") List))
    (SeqG
      (SeqG (NumG 0x00))
      (SeqG (AttrG (VarE "e") (VarG "Bexpr")))
      (SeqG
        (AttrG
          (VarE "b_lst")
          (VarG "Blist" (TypA (VarT "byte")) (GramA (VarG "Bbyte")))
        )
      )
    )
    (CaseE (Seq (Atom DATA) Arg Arg) (TupE (VarE "e") (VarE "b_lst")))
  )
)
(GramD
  "Bdatasec"
  (IterT (VarT "data") List)
  (ProdD
    (ExpP "data_lst" (IterT (VarT "data") List))
    (AttrG
      (VarE "data_lst")
      (VarG
        "Bsection_"
        (ExpA (NumE (Nat 11)))
        (TypA (VarT "data"))
        (GramA (VarG "Blist" (TypA (VarT "data")) (GramA (VarG "Bdata"))))
      )
    )
    (VarE "data_lst")
  )
)
(HintD (GramH "Bdatasec" (hint "desc" "\"data section\"")))
(GramD
  "Bmodule"
  (VarT "module")
  (ProdD
    (ExpP "type_lst" (IterT (VarT "type") List))
    (ExpP "import_lst" (IterT (VarT "import") List))
    (ExpP "func_lst" (IterT (VarT "func") List))
    (ExpP "global_lst" (IterT (VarT "global") List))
    (ExpP "table_lst" (IterT (VarT "table") List))
    (ExpP "mem_lst" (IterT (VarT "mem") List))
    (ExpP "elem_lst" (IterT (VarT "elem") List))
    (ExpP "data_lst" (IterT (VarT "data") List))
    (ExpP "start_opt" (IterT (VarT "start") Opt))
    (ExpP "export_lst" (IterT (VarT "export") List))
    (ExpP "typeidx_lst" (IterT (VarT "typeidx") List))
    (ExpP "expr_lst" (IterT (VarT "expr") List))
    (ExpP "local_lst_lst" (IterT (IterT (VarT "local") List) List))
    (SeqG
      (SeqG (NumG 0x00))
      (SeqG (NumG 0x61))
      (SeqG (NumG 0x73))
      (SeqG (NumG 0x6D))
      (SeqG
        (AttrG
          (CaseE (Seq (Atom mk_uN) Arg) (TupE (NumE (Nat 1))))
          (VarG "Bu32")
        )
      )
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG (AttrG (VarE "type_lst") (VarG "Btypesec")))
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG (AttrG (VarE "import_lst") (VarG "Bimportsec")))
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG (AttrG (VarE "typeidx_lst") (VarG "Bfuncsec")))
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG (AttrG (VarE "table_lst") (VarG "Btablesec")))
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG (AttrG (VarE "mem_lst") (VarG "Bmemsec")))
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG (AttrG (VarE "global_lst") (VarG "Bglobalsec")))
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG (AttrG (VarE "export_lst") (VarG "Bexportsec")))
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG (AttrG (VarE "start_opt") (VarG "Bstartsec")))
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG (AttrG (VarE "elem_lst") (VarG "Belemsec")))
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG
        (AttrG
          (IterE
            (TupE (VarE "local_lst") (VarE "v_expr"))
            List
            (iterexp "v_expr" (VarE "expr_lst"))
            (iterexp "local_lst" (VarE "local_lst_lst"))
          )
          (VarG "Bcodesec")
        )
      )
      (SeqG (IterG (VarG "Bcustomsec") List))
      (SeqG (AttrG (VarE "data_lst") (VarG "Bdatasec")))
      (SeqG (IterG (VarG "Bcustomsec") List))
    )
    (CaseE
      (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
      (TupE
        (VarE "type_lst")
        (VarE "import_lst")
        (VarE "func_lst")
        (VarE "global_lst")
        (VarE "table_lst")
        (VarE "mem_lst")
        (VarE "elem_lst")
        (VarE "data_lst")
        (VarE "start_opt")
        (VarE "export_lst")
      )
    )
    (IterPr
      (IfPr
        (CmpE
          EqOp
          bool
          (VarE "v_func")
          (CaseE
            (Seq (Atom FUNC) Arg Arg Arg)
            (TupE (VarE "v_typeidx") (VarE "local_lst") (VarE "v_expr"))
          )
        )
      )
      List
      (iterexp "v_expr" (VarE "expr_lst"))
      (iterexp "v_func" (VarE "func_lst"))
      (iterexp "local_lst" (VarE "local_lst_lst"))
      (iterexp "v_typeidx" (VarE "typeidx_lst"))
    )
  )
)


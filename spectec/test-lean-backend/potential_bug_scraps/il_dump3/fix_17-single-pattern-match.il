(TypD "marker" (InstD (VariantT (typcase (Atom MARK) (TupT)))))
(TypD
  "thing"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom THING) Arg Arg)
        (TupT
          (typbind "marker_opt" (IterT (VarT "marker") Opt))
          (typbind "_" nat)
        )
      )
    )
  )
)
(RelD
  "Thing_ok"
  (Infix Arg : (Atom OK))
  (VarT "thing")
  (RuleD
    "mk_Thing_ok"
    (ExpP "marker_opt" (IterT (VarT "marker") Opt))
    (ExpP "n" nat)
    (Infix Arg : (Atom OK))
    (CaseE (Seq (Atom THING) Arg Arg) (TupE (VarE "marker_opt") (VarE "n")))
    (IfPr (CmpE GtOp nat (VarE "n") (NumE (Nat 0))))
  )
)


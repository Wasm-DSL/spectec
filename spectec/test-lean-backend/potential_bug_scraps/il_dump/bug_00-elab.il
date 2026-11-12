(TypD "marker" (InstD (VariantT (typcase (Atom MARK) (TupT)))))
(TypD
  "thing"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom THING) Arg Arg)
        (TupT (typbind "marker?" (IterT (VarT "marker") Opt)) (typbind "_" nat))
      )
    )
  )
)
(RelD
  "Thing_ok"
  (Infix Arg : (Atom OK))
  (VarT "thing")
  (RuleD
    ""
    (ExpP "n" nat)
    (Infix Arg : (Atom OK))
    (CaseE
      (Seq (Atom THING) Arg Arg)
      (TupE (IterE (CaseE (Atom MARK) (TupE)) Opt) (VarE "n"))
    )
    (IfPr (CmpE GtOp nat (VarE "n") (NumE (Nat 0))))
  )
)


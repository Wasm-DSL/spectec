(*
This pass goes through all list of premises, and if there is a LHS that has a 
  variable that has not been declared before, then it introduces a let premise.

Due to this approach, this pass relies on the ordering of the premises. 
Perhaps there is a way to remove this restriction but for now this naive approach should work fine.

Valid LHS are:
VarE, StrE (records), CaseE, IterE (only allows identity iteration), TupE
 
In the validator, there are some RHS that need to be inferred, but 
some expressions are not possible to have their type inferred.

So, the RHS not allowed are:
OptE, StrE

For the most part, this works well. However due to some of the restrictions above, 
(and uncaseE appearing in unfortunate locations) it sometimes just does not introduce the let premise. 

Example from Wasm 3.0:

rec {
def $minus_recs(typevar*, typeuse*v) : (typevar*, typeuse* )
  def $minus_recs([], []) = ([], [])
  def $minus_recs{n : n, `tv*` : typevar*, tu_1 : typeuse, `tu*` : typeuse*}([REC_typevar(n)] ++ tv*{tv <- `tv*`}, [tu_1] ++ tu*{tu <- `tu*`}) = $minus_recs(tv*{tv <- `tv*`}, tu*{tu <- `tu*`})
  def $minus_recs{x : idx, `tv*` : typevar*, tu_1 : typeuse, `tu*` : typeuse*, `tv'*` : typevar*, `tu'*` : typeuse*}([_IDX_typevar(x)] ++ tv*{tv <- `tv*`}, [tu_1] ++ tu*{tu <- `tu*`}) = ([_IDX_typevar(x)] ++ tv'*{tv' <- `tv'*`}, [tu_1] ++ tu'*{tu' <- `tu'*`})
    -- if ((tv'*{tv' <- `tv'*`}, tu'*{tu' <- `tu'*`}) = $minus_recs(tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))
}

to

rec {
def $minus_recs(typevar*, typeuse* ) : (typevar*, typeuse* )
  def $minus_recs([], []) = ([], [])
  def $minus_recs{n : nat, `tv*` : typevar*, tu_1 : typeuse, `tu*` : typeuse*}([REC_typevar(n)] ++ tv*{tv <- `tv*`}, [tu_1] ++ tu*{tu <- `tu*`}) = $minus_recs(tv*{tv <- `tv*`}, tu*{tu <- `tu*`})
  def $minus_recs{x : uN(32), `tv*` : typevar*, tu_1 : typeuse, `tu*` : typeuse*, `tv'*` : typevar*, `tu'*` : typeuse*}([_IDX_typevar(x)] ++ tv*{tv <- `tv*`}, [tu_1] ++ tu*{tu <- `tu*`}) = ([_IDX_typevar(x)] ++ tv'*{tv' <- `tv'*`}, [tu_1] ++ tu'*{tu' <- `tu'*`})
    -- where (tv'*{tv' <- `tv'*`}, tu'*{tu' <- `tu'*`}) = $minus_recs(tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) {tu', `tu'*`, tv', `tv'*`}
}

Some limitations of this pass:
- The premise must be of the exact right shape (according to the valid LHS and RHS noted above) 
  and ordering to introduce lets. If it is not ordered properly, it leaves the if premise untouched.
- It does not try to do any dependency analysis nor does it introduce any new variables, 
  making it quite weak compared to Zilin's pass. Regardless, most if premises are in the 
  right shape so this should not introduce a problem.
*)

val transform : Il.Ast.script -> Il.Ast.script

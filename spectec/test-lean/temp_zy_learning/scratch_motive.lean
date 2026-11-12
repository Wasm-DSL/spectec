import Lean
open Lean Meta

-- An INDEXED family: the Nat argument is not uniform across constructors
-- (nil : Vec α 0, cons : ... → Vec α (n+1)), so Lean makes it an INDEX,
-- not a parameter. alpha, by contrast, IS uniform, so it's a param.
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : {n : Nat} → α → Vec α n → Vec α (n + 1)

#eval show MetaM Unit from do
  let indVal ← getConstInfoInduct ``Vec
  let recVal ← getConstInfoRec ``Vec.rec
  IO.println s!"numParams={recVal.numParams} numMotives={recVal.numMotives} numMinors={recVal.numMinors}"
  IO.println s!"recVal.type = {recVal.type}"

  -- Step 1: peel off the params (alpha), exactly like sandbox_10.lean:195.
  forallBoundedTelescope recVal.type (some recVal.numParams) fun paramVars restType0 => do
    IO.println s!"\n[params] paramVars={paramVars}"
    IO.println s!"[params] restType0 (motives+minors+target) = {restType0}"

    -- Step 2: peel off the motive binder(s), exactly like sandbox_10.lean:242.
    forallBoundedTelescope restType0 (some recVal.numMotives) fun motiveVars _restType => do
      IO.println s!"\n[motives] motiveVars={motiveVars}"
      let mv := motiveVars[0]!
      let mType ← inferType mv
      IO.println s!"[motives] the motive's OWN type (this is the comment's"
      IO.println s!"          '(i1:I1) -> ... -> (ik:Ik) -> T params i1...ik -> Sort u'):"
      IO.println s!"          mType = {mType}"

      -- Step 3: peel ALL of the motive's own binders (comment: "peel all forall binders").
      forallTelescope mType fun fvars sortBody => do
        IO.println s!"\n[peel-motive] fvars (ALL binders of the motive's type) = {fvars}"
        IO.println s!"[peel-motive] sortBody (should be Sort u) = {sortBody}"
        for fv in fvars do
          let d ← fv.fvarId!.getDecl
          IO.println s!"[peel-motive]   binder: userName={d.userName} type={d.type}"

        -- "the last one's domain is the inductive type application"
        let mainFvar := fvars.back!
        let domain ← inferType mainFvar
        IO.println s!"\n[domain] mainFvar (LAST binder) = {mainFvar}"
        IO.println s!"[domain] domain = inferType mainFvar = {domain}"
        IO.println s!"[domain]   ^ this is 'T params i1...ik' -- the inductive type APPLIED"
        IO.println s!"[domain]     to params AND indices, i.e. what's actually being matched on"

        let .const indName _ := domain.getAppFn | return
        let numIndices := fvars.size - 1
        IO.println s!"\n[classify] indName={indName}  numIndices = fvars.size - 1 = {fvars.size} - 1 = {numIndices}"

        -- "the preceding binders are index binders"
        IO.println s!"[classify] preceding binders (indices):"
        for i in [:numIndices] do
          let d ← fvars[i]!.fvarId!.getDecl
          IO.println s!"[classify]   index {i}: userName={d.userName} type={d.type}"

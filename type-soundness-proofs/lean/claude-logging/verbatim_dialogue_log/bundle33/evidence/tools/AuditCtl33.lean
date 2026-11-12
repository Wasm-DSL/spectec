import «wasm2.0»

/-! bundle33 positive control for the `Inhabited`-default audit (RunAudit33): two theorems whose proofs read
a default value (they must be reported) and one that does not (it must pass). Scratchpad only. -/

theorem audit_ctl_nat : (default : Nat) = 0 := rfl
theorem audit_ctl_model : (default : numtype) = numtype.I32 := rfl
theorem audit_ctl_refl : (default : val) = (default : val) := rfl

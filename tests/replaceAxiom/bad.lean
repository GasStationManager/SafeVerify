import Batteries.Tactic.OpenPrivate

/- Redefine `propext : False`. -/
open Lean Elab Meta in
open private Environment.mk from Lean.Environment in
#eval modifyEnv (m := MetaM) fun env =>
  let consts :=
    { env.constants with
        map₁ := env.constants.map₁.insert ``propext (.axiomInfo {
          name := ``propext
          type := .const ``False []
          levelParams := []
          isUnsafe := false
        })
    }
  Environment.mk env.const2ModIdx consts env.extensions env.extraConstNames env.header

theorem efsq : ∀ (x y z n : Nat),
    0 < x → 0 < y → 0 < z → 2 < n →
    x^n + y^n ≠ z^n := by
  exfalso
  exact propext

/-- info: 'efsq' depends on axioms: [propext] -/
#guard_msgs in
-- 'efsq' depends on axioms: [propext]
#print axioms efsq

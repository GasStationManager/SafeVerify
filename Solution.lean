import Mathlib

theorem foo.disproof : ∃ _x : Nat, ∀ _y : Nat, 1 + 1 = 2 := by
  use 0
  intro y
  rfl

import Mathlib

open Finset ZMod Classical

/--
In this example, we have corretly proved the theorem
without introducing any typeclass mismatches.
-/
theorem example_with_typeclass (p : ℕ)
    [hp : Fact p.Prime] :
    #{k : ZMod p | k = 1} = 1:= by
  simp [Finset.card_eq_one]
  use 1
  ext a
  simp

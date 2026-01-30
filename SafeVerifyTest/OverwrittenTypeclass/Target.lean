import Mathlib

open Finset ZMod Classical


theorem example_with_typeclass (p : ℕ)
    [hp : Fact p.Prime] :
    #{k : ZMod p | k = 1} = 1:= by
  sorry

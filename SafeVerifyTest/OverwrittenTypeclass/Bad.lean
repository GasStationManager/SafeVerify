import Mathlib

open Finset ZMod Classical

namespace Work

variable (p : ℕ) [hp : Fact p.Prime]

lemma p_ne_zero : p ≠ 0 := by
  have := hp.out.one_lt
  omega

lemma p_gt_one : 1 < p := hp.out.one_lt

instance : NeZero p := ⟨p_ne_zero p⟩

end Work

/--
In this example, we have defined a typeclass above which will be used by the theorem below,
which should cause a theorem type mismatch error.
-/
theorem example_with_typeclass (p : ℕ)
    [hp : Fact p.Prime] :
    #{k : ZMod p | k = 1} = 1:= by
  simp [Finset.card_eq_one]
  use 1
  ext a
  simp

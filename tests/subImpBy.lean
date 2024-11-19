import Mathlib

@[implemented_by Nat.zero]
noncomputable def definitely_at_least_two : ℕ :=
  Exists.choose (⟨3, by norm_num⟩ : ∃ x, 2 ≤ x)

theorem definitely_at_least_two_spec : 2 ≤ definitely_at_least_two :=
  Exists.choose_spec _

#eval definitely_at_least_two -- 0

#print axioms definitely_at_least_two_spec

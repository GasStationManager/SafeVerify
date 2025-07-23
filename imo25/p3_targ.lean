import Mathlib
import Aesop
set_option pp.numericTypes true
set_option pp.funBinderTypes true
set_option maxHeartbeats 0
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat Classical Polynomial



theorem imo2025_p3_left (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) : f n ≤ 4 * n  := by
  sorry


theorem imo2025_p3_right : ∃ (n : ℤ) (f : ℤ → ℤ), (n > 0) ∧ (∀ k : ℤ, k > 0 → f k > 0) ∧ (∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) ∧ (f n ≥ 4 * n) := by
  sorry
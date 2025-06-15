import Mathlib


-- Definition [Radical]
def rad (n : ℕ) : ℕ := if n = 0 then 0 else n.primeFactors.prod id

def exceptionalSet (N : ℕ) (ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  { (a, b, c) |
    1 ≤ a ∧ a ≤ N ∧
    1 ≤ b ∧ b ≤ N ∧
    1 ≤ c ∧ c ≤ N ∧
    a + b = c ∧
    Nat.Coprime a b ∧
    (rad (a * b * c) : ℝ) < (c : ℝ) ^ (1 - ε) }

theorem theorem67 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  :
  ∃ (C : ℝ), C > 0 ∧ ∃ (N₀ : ℕ), ∀ (N : ℕ) [Fintype ↑(exceptionalSet N ε)], N ≥ N₀ →
    ((exceptionalSet N ε).toFinset.card : ℝ) ≤ C * (N : ℝ) ^ ((2: ℝ) / 3) := sorry
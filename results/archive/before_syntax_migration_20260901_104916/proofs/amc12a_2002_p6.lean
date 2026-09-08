import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem amc12a_2002_p6 (n : ℕ) (h₀ : 0 < n) : ∃ m, m > n ∧ ∃ p, m * p ≤ m + p := by
  have h_main : ∃ (m : ℕ), m > n ∧ ∃ (p : ℕ), m * p ≤ m + p := by
    use n + 1
    constructor
    · -- Prove that n + 1 > n
      omega
    · -- Find a p such that (n + 1) * p ≤ (n + 1) + p
      use 0
      -- Simplify the inequality (n + 1) * 0 ≤ (n + 1) + 0
      <;> simp [mul_zero, add_zero]
      <;> nlinarith
  
  exact h_main

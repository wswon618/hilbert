import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem mathd_algebra_76 (f : ℤ → ℤ) (h₀ : ∀ n, Odd n → f n = n ^ 2)
    (h₁ : ∀ n, Even n → f n = n ^ 2 - 4 * n - 1) : f 4 = -1 := by
  have h₂ : f 4 = (4 : ℤ) ^ 2 - 4 * (4 : ℤ) - 1 := by
    have h₃ : Even (4 : ℤ) := by
      norm_num [Int.even_iff]
    have h₄ : f 4 = (4 : ℤ) ^ 2 - 4 * (4 : ℤ) - 1 := by
      apply h₁
      exact h₃
    exact h₄
  
  have h₅ : f 4 = -1 := by
    rw [h₂]
    <;> norm_num
  
  exact h₅

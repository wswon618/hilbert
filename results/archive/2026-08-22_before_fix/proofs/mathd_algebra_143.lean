import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem mathd_algebra_143 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x + 1) (h₁ : ∀ x, g x = x ^ 2 + 3) :
    f (g 2) = 8 := by
  have h₂ : g 2 = (2 : ℝ) ^ 2 + 3 := by
    rw [h₁]
    <;> norm_num
  have h₃ : f (g 2) = f ((2 : ℝ) ^ 2 + 3) := by
    rw [h₂]
  have h₄ : f ((2 : ℝ) ^ 2 + 3) = ((2 : ℝ) ^ 2 + 3) + 1 := by
    rw [h₀]
    <;> norm_num
  have h₅ : f (g 2) = 8 := by
    rw [h₃, h₄]
    <;> norm_num
  exact h₅

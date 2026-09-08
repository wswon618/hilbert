import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  have h₃ : 81 * a - 9 * b = 0 := by
    have h₃₁ : f (-3) = a * (-3 : ℝ) ^ 4 - b * (-3 : ℝ) ^ 2 + (-3 : ℝ) + 5 := by
      rw [h₀]
      <;> norm_num
    rw [h₃₁] at h₂
    ring_nf at h₂ ⊢
    linarith
  
  have h₄ : f 3 = 8 := by
    have h₄₁ : f 3 = a * (3 : ℝ) ^ 4 - b * (3 : ℝ) ^ 2 + (3 : ℝ) + 5 := by
      rw [h₀]
      <;> norm_num
    rw [h₄₁]
    have h₄₂ : a * (3 : ℝ) ^ 4 - b * (3 : ℝ) ^ 2 + (3 : ℝ) + 5 = 81 * a - 9 * b + 8 := by
      ring_nf
      <;> norm_num
      <;> linarith
    rw [h₄₂]
    have h₄₃ : 81 * a - 9 * b = 0 := h₃
    linarith
  
  exact h₄

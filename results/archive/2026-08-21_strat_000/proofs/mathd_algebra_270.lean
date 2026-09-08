import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  have h1 : f 1 = 1 / 3 := by
    have h1₁ : (1 : ℝ) ≠ -2 := by norm_num
    have h1₂ : f 1 = 1 / (1 + 2 : ℝ) := h₀ 1 h1₁
    have h1₃ : (1 : ℝ) / (1 + 2 : ℝ) = 1 / 3 := by norm_num
    rw [h1₂, h1₃]
    <;> norm_num
  
  have h2 : f (f 1) = 3 / 7 := by
    rw [h1]
    have h2₁ : (1 / 3 : ℝ) ≠ -2 := by norm_num
    have h2₂ : f (1 / 3 : ℝ) = 1 / ((1 / 3 : ℝ) + 2) := h₀ (1 / 3 : ℝ) h2₁
    rw [h2₂]
    <;> norm_num
    <;> field_simp
    <;> ring_nf
    <;> norm_num
  
  rw [h2]

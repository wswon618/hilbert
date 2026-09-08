import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem aime_1983_p2 (x p : ℝ) (f : ℝ → ℝ) (h₀ : 0 < p ∧ p < 15) (h₁ : p ≤ x ∧ x ≤ 15)
    (h₂ : f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) : 15 ≤ f x := by
  have h₃ : abs (x - p) = x - p := by
    have h₃₁ : x - p ≥ 0 := by linarith
    rw [abs_of_nonneg h₃₁]
    <;>
    linarith
  
  have h₄ : abs (x - 15) = 15 - x := by
    have h₄₁ : x - 15 ≤ 0 := by linarith
    rw [abs_of_nonpos h₄₁]
    <;>
    linarith
  
  have h₅ : abs (x - p - 15) = -x + p + 15 := by
    have h₅₁ : x - p - 15 ≤ 0 := by
      have h₅₂ : x ≤ 15 := by linarith
      have h₅₃ : 0 < p := by linarith
      linarith
    have h₅₂ : abs (x - p - 15) = -(x - p - 15) := by
      rw [abs_of_nonpos h₅₁]
      <;>
      linarith
    rw [h₅₂]
    <;>
    ring_nf
    <;>
    linarith
  
  have h₆ : f x = 30 - x := by
    rw [h₂]
    rw [h₃, h₄, h₅]
    <;>
    ring_nf
    <;>
    linarith
  
  have h₇ : 15 ≤ f x := by
    rw [h₆]
    have h₇₁ : x ≤ 15 := by linarith
    linarith
  
  exact h₇

import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem amc12b_2002_p19 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : a * (b + c) = 152)
    (h₂ : b * (c + a) = 162) (h₃ : c * (a + b) = 170) : a * b * c = 720 := by
  have h₄ : 0 < a := by linarith
  have h₅ : 0 < b := by linarith
  have h₆ : 0 < c := by linarith
  have h₇ : 0 < a * b := by positivity
  have h₈ : 0 < a * c := by positivity
  have h₉ : 0 < b * c := by positivity
  have h₁₀ : a * b + a * c = 152 := by
    have h₁₀₁ : a * (b + c) = 152 := h₁
    have h₁₀₂ : a * (b + c) = a * b + a * c := by ring
    linarith
  have h₁₁ : b * c + a * b = 162 := by
    have h₁₁₁ : b * (c + a) = 162 := h₂
    have h₁₁₂ : b * (c + a) = b * c + a * b := by ring
    linarith
  have h₁₂ : a * c + b * c = 170 := by
    have h₁₂₁ : c * (a + b) = 170 := h₃
    have h₁₂₂ : c * (a + b) = a * c + b * c := by ring
    linarith
  have h₁₃ : a * b + a * c + b * c = 242 := by
    linarith
  have h₁₄ : a * b * c = 720 := by
    have h₁₄₁ : (a * b + a * c + b * c) ^ 2 = (a * b) ^ 2 + (a * c) ^ 2 + (b * c) ^ 2 + 2 * (a * b * a * c + a * b * b * c + a * c * b * c) := by
      ring
    have h₁₄₂ : (a * b - a * c) ^ 2 + (a * b - b * c) ^ 2 + (a * c - b * c) ^ 2 = 2 * ((a * b) ^ 2 + (a * c) ^ 2 + (b * c) ^ 2) - 2 * (a * b * a * c + a * b * b * c + a * c * b * c) := by
      ring
    have h₁₄₃ : (a * b - a * c) ^ 2 + (a * b - b * c) ^ 2 + (a * c - b * c) ^ 2 ≥ 0 := by positivity
    nlinarith [sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c)]
  exact h₁₄

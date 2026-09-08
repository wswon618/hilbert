import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem mathd_algebra_338 (a b c : ℝ) (h₀ : 3 * a + b + c = -3) (h₁ : a + 3 * b + c = 9)
    (h₂ : a + b + 3 * c = 19) : a * b * c = -56 := by
  have h₃ : -a + b = 6 := by
    have h₃₁ : (a + 3 * b + c) - (3 * a + b + c) = 9 - (-3) := by
      linarith
    -- Simplify the equation to get -2a + 2b = 12
    have h₃₂ : -2 * a + 2 * b = 12 := by linarith
    -- Divide by 2 to get -a + b = 6
    linarith
  
  have h₄ : -a + c = 11 := by
    have h₄₁ : (a + b + 3 * c) - (3 * a + b + c) = 19 - (-3) := by
      linarith
    -- Simplify the equation to get -2a + 2c = 22
    have h₄₂ : -2 * a + 2 * c = 22 := by linarith
    -- Divide by 2 to get -a + c = 11
    linarith
  
  have h₅ : b = a + 6 := by
    have h₅₁ : -a + b = 6 := h₃
    -- Solve for b in terms of a
    linarith
  
  have h₆ : c = a + 11 := by
    have h₆₁ : -a + c = 11 := h₄
    -- Solve for c in terms of a
    linarith
  
  have h₇ : a = -4 := by
    have h₇₁ : 3 * a + b + c = -3 := h₀
    have h₇₂ : b = a + 6 := h₅
    have h₇₃ : c = a + 11 := h₆
    -- Substitute b and c into the first equation
    rw [h₇₂, h₇₃] at h₇₁
    -- Simplify the equation to solve for a
    ring_nf at h₇₁ ⊢
    linarith
  
  have h₈ : b = 2 := by
    have h₈₁ : b = a + 6 := h₅
    have h₈₂ : a = -4 := h₇
    rw [h₈₂] at h₈₁
    linarith
  
  have h₉ : c = 7 := by
    have h₉₁ : c = a + 11 := h₆
    have h₉₂ : a = -4 := h₇
    rw [h₉₂] at h₉₁
    linarith
  
  have h₁₀ : a * b * c = -56 := by
    have h₁₀₁ : a = -4 := h₇
    have h₁₀₂ : b = 2 := h₈
    have h₁₀₃ : c = 7 := h₉
    rw [h₁₀₁, h₁₀₂, h₁₀₃]
    norm_num
  
  exact h₁₀

import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem aime_1990_p4 (x : ℝ) (h₀ : 0 < x) (h₁ : x ^ 2 - 10 * x - 29 ≠ 0)
    (h₂ : x ^ 2 - 10 * x - 45 ≠ 0) (h₃ : x ^ 2 - 10 * x - 69 ≠ 0)
    (h₄ : 1 / (x ^ 2 - 10 * x - 29) + 1 / (x ^ 2 - 10 * x - 45) - 2 / (x ^ 2 - 10 * x - 69) = 0) :
    x = 13 := by
  have h_y_def : x ^ 2 - 10 * x = 39 := by
    have h₅ : x ^ 2 - 10 * x - 29 ≠ 0 := h₁
    have h₆ : x ^ 2 - 10 * x - 45 ≠ 0 := h₂
    have h₇ : x ^ 2 - 10 * x - 69 ≠ 0 := h₃
    have h₈ : 1 / (x ^ 2 - 10 * x - 29) + 1 / (x ^ 2 - 10 * x - 45) - 2 / (x ^ 2 - 10 * x - 69) = 0 := h₄
    have h₉ : (x ^ 2 - 10 * x - 29) ≠ 0 := h₁
    have h₁₀ : (x ^ 2 - 10 * x - 45) ≠ 0 := h₂
    have h₁₁ : (x ^ 2 - 10 * x - 69) ≠ 0 := h₃
    -- Define y = x² - 10x
    set y := x ^ 2 - 10 * x with hy
    have h₁₂ : y - 29 ≠ 0 := by
      intro h
      apply h₅
      linarith
    have h₁₃ : y - 45 ≠ 0 := by
      intro h
      apply h₆
      linarith
    have h₁₄ : y - 69 ≠ 0 := by
      intro h
      apply h₇
      linarith
    -- Rewrite the equation in terms of y
    have h₁₅ : 1 / (y - 29) + 1 / (y - 45) - 2 / (y - 69) = 0 := by
      have h₁₅₁ : 1 / (x ^ 2 - 10 * x - 29) = 1 / (y - 29) := by
        rw [hy]
        <;> ring_nf
      have h₁₅₂ : 1 / (x ^ 2 - 10 * x - 45) = 1 / (y - 45) := by
        rw [hy]
        <;> ring_nf
      have h₁₅₃ : 2 / (x ^ 2 - 10 * x - 69) = 2 / (y - 69) := by
        rw [hy]
        <;> ring_nf
      rw [h₁₅₁, h₁₅₂, h₁₅₃] at h₈
      exact h₈
    -- Combine the fractions
    have h₁₆ : (y - 37) / ((y - 29) * (y - 45)) = 1 / (y - 69) := by
      have h₁₆₁ : 1 / (y - 29) + 1 / (y - 45) = 2 / (y - 69) := by
        have h₁₆₂ : 1 / (y - 29) + 1 / (y - 45) - 2 / (y - 69) = 0 := h₁₅
        linarith
      have h₁₆₃ : (y - 45 + (y - 29)) / ((y - 29) * (y - 45)) = 2 / (y - 69) := by
        have h₁₆₄ : 1 / (y - 29) + 1 / (y - 45) = (y - 45 + (y - 29)) / ((y - 29) * (y - 45)) := by
          field_simp [h₁₂, h₁₃]
          <;> ring_nf
          <;> field_simp [h₁₂, h₁₃]
          <;> ring_nf
        rw [h₁₆₄] at h₁₆₁
        exact h₁₆₁
      have h₁₆₅ : (2 * y - 74) / ((y - 29) * (y - 45)) = 2 / (y - 69) := by
        have h₁₆₆ : (y - 45 + (y - 29)) = (2 * y - 74) := by ring
        rw [h₁₆₆] at h₁₆₃
        exact h₁₆₃
      have h₁₆₇ : (y - 37) / ((y - 29) * (y - 45)) = 1 / (y - 69) := by
        have h₁₆₈ : (2 * y - 74) = 2 * (y - 37) := by ring
        rw [h₁₆₈] at h₁₆₅
        have h₁₆₉ : (2 * (y - 37)) / ((y - 29) * (y - 45)) = 2 / (y - 69) := by
          exact h₁₆₅
        have h₁₇₀ : (2 * (y - 37)) / ((y - 29) * (y - 45)) = 2 * ((y - 37) / ((y - 29) * (y - 45))) := by
          field_simp [h₁₂, h₁₃]
          <;> ring_nf
          <;> field_simp [h₁₂, h₁₃]
          <;> ring_nf
        rw [h₁₇₀] at h₁₆₉
        have h₁₇₁ : 2 * ((y - 37) / ((y - 29) * (y - 45))) = 2 / (y - 69) := by
          exact h₁₆₉
        have h₁₇₂ : (y - 37) / ((y - 29) * (y - 45)) = 1 / (y - 69) := by
          have h₁₇₃ : 2 ≠ 0 := by norm_num
          apply mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)
          rw [← sub_eq_zero]
          have h₁₇₄ : 2 * ((y - 37) / ((y - 29) * (y - 45))) - 2 / (y - 69) = 0 := by linarith
          ring_nf at h₁₇₄ ⊢
          linarith
        exact h₁₇₂
      exact h₁₆₇
    -- Cross-multiply to eliminate denominators
    have h₁₇ : (y - 37) * (y - 69) = (y - 29) * (y - 45) := by
      have h₁₇₁ : (y - 37) / ((y - 29) * (y - 45)) = 1 / (y - 69) := h₁₆
      have h₁₇₂ : (y - 69) ≠ 0 := h₁₄
      have h₁₇₃ : (y - 29) ≠ 0 := h₁₂
      have h₁₇₄ : (y - 45) ≠ 0 := h₁₃
      have h₁₇₅ : ((y - 29) * (y - 45)) ≠ 0 := by
        apply mul_ne_zero
        · exact h₁₇₃
        · exact h₁₇₄
      field_simp [h₁₇₂, h₁₇₅] at h₁₇₁
      nlinarith
    -- Expand and simplify to solve for y
    have h₁₈ : y = 39 := by
      have h₁₈₁ : (y - 37) * (y - 69) = (y - 29) * (y - 45) := h₁₇
      have h₁₈₂ : y ^ 2 - 106 * y + 2553 = y ^ 2 - 74 * y + 1305 := by
        ring_nf at h₁₈₁ ⊢
        linarith
      have h₁₈₃ : -106 * y + 2553 = -74 * y + 1305 := by
        linarith
      have h₁₈₄ : 1248 = 32 * y := by linarith
      have h₁₈₅ : y = 39 := by linarith
      exact h₁₈₅
    -- Substitute back to find x² - 10x = 39
    have h₁₉ : x ^ 2 - 10 * x = 39 := by
      rw [hy] at h₁₈
      linarith
    exact h₁₉
  
  have h_x_squared : x ^ 2 - 10 * x - 39 = 0 := by
    have h₅ : x ^ 2 - 10 * x = 39 := h_y_def
    have h₆ : x ^ 2 - 10 * x - 39 = 0 := by linarith
    exact h₆
  
  have h_x_solutions : x = 13 ∨ x = -3 := by
    have h₅ : x ^ 2 - 10 * x - 39 = 0 := h_x_squared
    have h₆ : (x - 13) * (x + 3) = 0 := by
      nlinarith
    have h₇ : x - 13 = 0 ∨ x + 3 = 0 := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero h₆
    cases h₇ with
    | inl h₇ =>
      have h₈ : x - 13 = 0 := h₇
      have h₉ : x = 13 := by linarith
      exact Or.inl h₉
    | inr h₇ =>
      have h₈ : x + 3 = 0 := h₇
      have h₉ : x = -3 := by linarith
      exact Or.inr h₉
  
  have h_x_positive : x = 13 := by
    cases h_x_solutions with
    | inl h =>
      exact h
    | inr h =>
      have h₅ : x = -3 := h
      have h₆ : 0 < x := h₀
      linarith
  
  exact h_x_positive

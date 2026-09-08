import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ) (h₀ : a ≤ b ∧ b ≤ c)
    (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1) :
    0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
  have h₃ : a ≤ 1 / 3 := by
    have h₃₁ : (a - b) * (a - c) ≥ 0 := by
      have h₃₂ : a - b ≤ 0 := by linarith
      have h₃₃ : a - c ≤ 0 := by linarith
      nlinarith
    have h₃₄ : 3 * a ^ 2 - 4 * a + 1 ≥ 0 := by
      have h₃₅ : b + c = 2 - a := by linarith
      have h₃₆ : a * b + b * c + c * a = 1 := h₂
      have h₃₇ : b * c = 1 - a * (2 - a) := by
        have h₃₈ : a * b + b * c + c * a = 1 := h₂
        have h₃₉ : a * b + c * a = a * (b + c) := by ring
        have h₄₀ : a * (b + c) + b * c = 1 := by linarith
        have h₄₁ : a * (2 - a) + b * c = 1 := by
          calc
            a * (2 - a) + b * c = a * (b + c) + b * c := by
              rw [h₃₅]
              <;> ring
            _ = 1 := by linarith
        linarith
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c)]
    have h₃₈ : a ≤ 1 / 3 ∨ a ≥ 1 := by
      have h₃₉ : (a - 1 / 3) * (a - 1) ≥ 0 := by
        nlinarith
      have h₄₀ : a ≤ 1 / 3 ∨ a ≥ 1 := by
        by_cases h₄₁ : a ≤ 1 / 3
        · exact Or.inl h₄₁
        · have h₄₂ : a ≥ 1 := by
            by_contra h₄₃
            have h₄₄ : a < 1 := by linarith
            have h₄₅ : (a - 1 / 3) * (a - 1) < 0 := by
              have h₄₆ : a - 1 / 3 > 0 := by linarith
              have h₄₇ : a - 1 < 0 := by linarith
              nlinarith
            linarith
          exact Or.inr h₄₂
      exact h₄₀
    cases h₃₈ with
    | inl h₃₈ =>
      exact h₃₈
    | inr h₃₈ =>
      have h₃₉ : a + b + c ≥ 3 := by
        have h₄₀ : a ≥ 1 := h₃₈
        have h₄₁ : b ≥ a := by linarith
        have h₄₂ : c ≥ b := by linarith
        linarith
      linarith
  
  have h₄ : 0 ≤ a := by
    by_contra h
    have h₅ : a < 0 := by linarith
    have h₆ : b + c = 2 - a := by linarith
    have h₇ : b * c = 1 - a * (2 - a) := by
      have h₈ : a * b + b * c + c * a = 1 := h₂
      have h₉ : a * b + c * a = a * (b + c) := by ring
      have h₁₀ : a * (b + c) + b * c = 1 := by linarith
      have h₁₁ : a * (2 - a) + b * c = 1 := by
        calc
          a * (2 - a) + b * c = a * (b + c) + b * c := by
            rw [h₆]
            <;> ring
          _ = 1 := by linarith
      linarith
    have h₈ : b * c ≤ ((2 - a) / 2) ^ 2 := by
      nlinarith [sq_nonneg (b - c)]
    have h₉ : 1 - a * (2 - a) ≤ ((2 - a) / 2) ^ 2 := by
      linarith
    have h₁₀ : a * (3 * a - 4) ≤ 0 := by
      nlinarith [sq_nonneg (a - 1)]
    have h₁₁ : a * (3 * a - 4) > 0 := by
      nlinarith
    linarith
  
  have h₅ : 1 / 3 ≤ b := by
    have h₅₁ : (b - a) * (b - c) ≤ 0 := by
      have h₅₂ : b - a ≥ 0 := by linarith
      have h₅₃ : b - c ≤ 0 := by linarith
      nlinarith
    have h₅₄ : 3 * b ^ 2 - 4 * b + 1 ≤ 0 := by
      have h₅₅ : a + c = 2 - b := by linarith
      have h₅₆ : a * b + b * c + c * a = 1 := h₂
      have h₅₇ : a * c = 1 - b * (2 - b) := by
        have h₅₈ : a * b + b * c + c * a = 1 := h₂
        have h₅₉ : a * b + b * c = b * (a + c) := by ring
        have h₆₀ : b * (a + c) + a * c = 1 := by linarith
        have h₆₁ : b * (2 - b) + a * c = 1 := by
          calc
            b * (2 - b) + a * c = b * (a + c) + a * c := by
              rw [h₅₅]
              <;> ring
            _ = 1 := by linarith
        linarith
      nlinarith [sq_nonneg (b - a), sq_nonneg (b - c)]
    have h₅₈ : 1 / 3 ≤ b := by
      by_contra h₅₉
      have h₆₀ : b < 1 / 3 := by linarith
      have h₆₁ : 3 * b ^ 2 - 4 * b + 1 > 0 := by
        nlinarith [sq_nonneg (b - 1 / 3)]
      linarith
    exact h₅₈
  
  have h₆ : b ≤ 1 := by
    have h₆₁ : (b - a) * (b - c) ≤ 0 := by
      have h₆₂ : b - a ≥ 0 := by linarith
      have h₆₃ : b - c ≤ 0 := by linarith
      nlinarith
    have h₆₄ : 3 * b ^ 2 - 4 * b + 1 ≤ 0 := by
      have h₆₅ : a + c = 2 - b := by linarith
      have h₆₆ : a * b + b * c + c * a = 1 := h₂
      have h₆₇ : a * c = 1 - b * (2 - b) := by
        have h₆₈ : a * b + b * c + c * a = 1 := h₂
        have h₆₉ : a * b + b * c = b * (a + c) := by ring
        have h₇₀ : b * (a + c) + a * c = 1 := by linarith
        have h₇₁ : b * (2 - b) + a * c = 1 := by
          calc
            b * (2 - b) + a * c = b * (a + c) + a * c := by
              rw [h₆₅]
              <;> ring
            _ = 1 := by linarith
        linarith
      nlinarith [sq_nonneg (b - a), sq_nonneg (b - c)]
    have h₆₈ : b ≤ 1 := by
      by_contra h₆₉
      have h₇₀ : b > 1 := by linarith
      have h₇₁ : 3 * b ^ 2 - 4 * b + 1 > 0 := by
        nlinarith [sq_nonneg (b - 1)]
      linarith
    exact h₆₈
  
  have h₇ : 1 ≤ c := by
    have h₇₁ : (c - a) * (c - b) ≥ 0 := by
      have h₇₂ : c - a ≥ 0 := by linarith
      have h₇₃ : c - b ≥ 0 := by linarith
      nlinarith
    have h₇₄ : 3 * c ^ 2 - 4 * c + 1 ≥ 0 := by
      have h₇₅ : a + b = 2 - c := by linarith
      have h₇₆ : a * b + b * c + c * a = 1 := h₂
      have h₇₇ : a * b = 1 - c * (2 - c) := by
        have h₇₈ : a * b + b * c + c * a = 1 := h₂
        have h₇₉ : b * c + c * a = c * (a + b) := by ring
        have h₈₀ : c * (a + b) + a * b = 1 := by linarith
        have h₈₁ : c * (2 - c) + a * b = 1 := by
          calc
            c * (2 - c) + a * b = c * (a + b) + a * b := by
              rw [h₇₅]
              <;> ring
            _ = 1 := by linarith
        linarith
      nlinarith [sq_nonneg (c - a), sq_nonneg (c - b)]
    have h₇₈ : c ≤ 1 / 3 ∨ c ≥ 1 := by
      have h₇₉ : (c - 1 / 3) * (c - 1) ≥ 0 := by
        nlinarith
      have h₈₀ : c ≤ 1 / 3 ∨ c ≥ 1 := by
        by_cases h₈₁ : c ≤ 1 / 3
        · exact Or.inl h₈₁
        · have h₈₂ : c ≥ 1 := by
            by_contra h₈₃
            have h₈₄ : c < 1 := by linarith
            have h₈₅ : (c - 1 / 3) * (c - 1) < 0 := by
              have h₈₆ : c - 1 / 3 > 0 := by
                have h₈₇ : c ≥ b := by linarith
                have h₈₈ : b ≥ 1 / 3 := by linarith
                linarith
              have h₈₉ : c - 1 < 0 := by linarith
              nlinarith
            linarith
          exact Or.inr h₈₂
      exact h₈₀
    cases h₇₈ with
    | inl h₇₈ =>
      have h₇₉ : a + b + c ≤ 1 := by
        have h₈₀ : c ≤ 1 / 3 := h₇₈
        have h₈₁ : a ≤ b := by linarith
        have h₈₂ : b ≤ c := by linarith
        have h₈₃ : a ≤ 1 / 3 := by linarith
        have h₈₄ : b ≤ 1 / 3 := by linarith
        linarith
      linarith
    | inr h₇₈ =>
      linarith
  
  have h₈ : c ≤ 4 / 3 := by
    by_contra h
    have h₈₁ : c > 4 / 3 := by linarith
    have h₈₂ : a ^ 2 + b ^ 2 + c ^ 2 = 2 := by
      have h₈₃ : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by ring
      rw [h₁] at h₈₃
      rw [h₂] at h₈₃
      nlinarith
    have h₈₃ : a ^ 2 ≤ 1 / 9 := by
      have h₈₄ : 0 ≤ a := h₄
      have h₈₅ : a ≤ 1 / 3 := h₃
      nlinarith
    have h₈₄ : b ^ 2 ≤ 1 := by
      have h₈₅ : 0 ≤ b := by linarith
      have h₈₆ : b ≤ 1 := h₆
      nlinarith
    have h₈₅ : c ^ 2 > 16 / 9 := by
      have h₈₆ : c > 4 / 3 := h₈₁
      nlinarith
    nlinarith
  
  exact ⟨h₄, h₃, h₅, h₆, h₇, h₈⟩

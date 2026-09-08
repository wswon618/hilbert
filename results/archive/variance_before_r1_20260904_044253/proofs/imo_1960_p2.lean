import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem imo_1960_p2 (x : ℝ) (h₀ : 0 ≤ 1 + 2 * x) (h₁ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0)
    (h₂ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9) : -(1 / 2) ≤ x ∧ x < 45 / 8 := by
  have h₃ : -(1 / 2 : ℝ) ≤ x := by
    -- Prove the lower bound using the given condition 0 ≤ 1 + 2x
    linarith
  
  have h₄ : x < 45 / 8 := by
    have h₅ : 0 ≤ 1 + 2 * x := h₀
    have h₆ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0 := h₁
    have h₇ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9 := h₂
    have h₈ : Real.sqrt (1 + 2 * x) ≥ 0 := Real.sqrt_nonneg (1 + 2 * x)
    have h₉ : Real.sqrt (1 + 2 * x) ≠ 1 := by
      by_contra h
      have h₁₀ : Real.sqrt (1 + 2 * x) = 1 := by linarith
      have h₁₁ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 = 0 := by
        rw [h₁₀]
        norm_num
      contradiction
    -- Introduce the substitution y = sqrt(1 + 2x)
    have h₁₀ : Real.sqrt (1 + 2 * x) < 7 / 2 := by
      by_contra h
      have h₁₁ : Real.sqrt (1 + 2 * x) ≥ 7 / 2 := by linarith
      have h₁₂ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 > 0 := by
        have h₁₃ : 1 - Real.sqrt (1 + 2 * x) ≠ 0 := by
          intro h₁₄
          have h₁₅ : Real.sqrt (1 + 2 * x) = 1 := by linarith
          contradiction
        have h₁₄ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 > 0 := by
          apply sq_pos_of_ne_zero
          exact h₁₃
        exact h₁₄
      have h₁₃ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≥ 2 * x + 9 := by
        have h₁₄ : Real.sqrt (1 + 2 * x) ≥ 7 / 2 := h₁₁
        have h₁₅ : (Real.sqrt (1 + 2 * x)) ^ 2 = 1 + 2 * x := by
          rw [Real.sq_sqrt] <;> linarith
        have h₁₆ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 = (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by
          have h₁₇ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 = (Real.sqrt (1 + 2 * x) - 1) ^ 2 := by
            ring_nf
            <;>
            nlinarith [Real.sqrt_nonneg (1 + 2 * x), Real.sq_sqrt (by linarith : 0 ≤ 1 + 2 * x)]
          rw [h₁₇]
          have h₁₈ : (Real.sqrt (1 + 2 * x) - 1) ≠ 0 := by
            intro h₁₉
            have h₂₀ : Real.sqrt (1 + 2 * x) = 1 := by linarith
            contradiction
          have h₁₉ : 4 * x ^ 2 = (Real.sqrt (1 + 2 * x) - 1) ^ 2 * (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by
            have h₂₀ : (Real.sqrt (1 + 2 * x)) ^ 2 = 1 + 2 * x := by
              rw [Real.sq_sqrt] <;> linarith
            nlinarith [Real.sqrt_nonneg (1 + 2 * x), Real.sq_sqrt (by linarith : 0 ≤ 1 + 2 * x)]
          rw [h₁₉]
          field_simp [h₁₈]
          <;> ring_nf
          <;> field_simp [h₁₈]
          <;> nlinarith [Real.sqrt_nonneg (1 + 2 * x), Real.sq_sqrt (by linarith : 0 ≤ 1 + 2 * x)]
        rw [h₁₆]
        have h₂₀ : (Real.sqrt (1 + 2 * x) + 1) ^ 2 ≥ 2 * x + 9 := by
          nlinarith [Real.sqrt_nonneg (1 + 2 * x), Real.sq_sqrt (by linarith : 0 ≤ 1 + 2 * x)]
        linarith
      linarith
    -- Translate back to x
    have h₁₁ : Real.sqrt (1 + 2 * x) < 7 / 2 := h₁₀
    have h₁₂ : 1 + 2 * x < (7 / 2 : ℝ) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (1 + 2 * x), Real.sq_sqrt (by linarith : 0 ≤ 1 + 2 * x)]
    nlinarith
  
  exact ⟨h₃, h₄⟩

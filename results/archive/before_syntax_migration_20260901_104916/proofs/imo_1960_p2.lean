import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem imo_1960_p2 (x : ℝ) (h₀ : 0 ≤ 1 + 2 * x) (h₁ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0)
    (h₂ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9) : -(1 / 2) ≤ x ∧ x < 45 / 8 := by
  have h_sqrt_nonneg : 0 ≤ Real.sqrt (1 + 2 * x) := by
    apply Real.sqrt_nonneg
  
  have h_sqrt_ne_one : Real.sqrt (1 + 2 * x) ≠ 1 := by
    intro h
    have h₃ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 = 0 := by
      rw [h]
      norm_num
    contradiction
  
  have h_denom_pos : 0 < (1 - Real.sqrt (1 + 2 * x)) ^ 2 := by
    have h₃ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0 := h₁
    have h₄ : 0 ≤ (1 - Real.sqrt (1 + 2 * x)) ^ 2 := by positivity
    have h₅ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 > 0 := by
      by_contra h₅
      have h₆ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≤ 0 := by linarith
      have h₇ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 = 0 := by
        nlinarith
      contradiction
    linarith
  
  have h_num_eq : 4 * x ^ 2 = (Real.sqrt (1 + 2 * x) - 1) ^ 2 * (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by
    have h₃ : 0 ≤ 1 + 2 * x := h₀
    have h₄ : (Real.sqrt (1 + 2 * x)) ^ 2 = 1 + 2 * x := by
      rw [Real.sq_sqrt] <;> linarith
    have h₅ : 4 * x ^ 2 = (1 + 2 * x - 1) ^ 2 := by
      ring_nf
      <;> nlinarith
    calc
      4 * x ^ 2 = (1 + 2 * x - 1) ^ 2 := by rw [h₅]
      _ = ((Real.sqrt (1 + 2 * x)) ^ 2 - 1) ^ 2 := by
        rw [h₄]
        <;> ring_nf
      _ = (Real.sqrt (1 + 2 * x) - 1) ^ 2 * (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by
        have h₆ : ((Real.sqrt (1 + 2 * x)) ^ 2 - 1) ^ 2 = (Real.sqrt (1 + 2 * x) - 1) ^ 2 * (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by
          have h₇ : (Real.sqrt (1 + 2 * x)) ^ 2 - 1 = (Real.sqrt (1 + 2 * x) - 1) * (Real.sqrt (1 + 2 * x) + 1) := by
            ring_nf
            <;> field_simp [h_sqrt_nonneg]
            <;> nlinarith [Real.sq_sqrt (by linarith : 0 ≤ (1 + 2 * x : ℝ))]
          calc
            ((Real.sqrt (1 + 2 * x)) ^ 2 - 1) ^ 2 = ((Real.sqrt (1 + 2 * x) - 1) * (Real.sqrt (1 + 2 * x) + 1)) ^ 2 := by rw [h₇]
            _ = (Real.sqrt (1 + 2 * x) - 1) ^ 2 * (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by
              ring_nf
              <;> field_simp [h_sqrt_nonneg]
              <;> nlinarith [Real.sq_sqrt (by linarith : 0 ≤ (1 + 2 * x : ℝ))]
        rw [h₆]
      _ = (Real.sqrt (1 + 2 * x) - 1) ^ 2 * (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by rfl
  
  have h_denom_eq : (1 - Real.sqrt (1 + 2 * x)) ^ 2 = (Real.sqrt (1 + 2 * x) - 1) ^ 2 := by
    have h₃ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 = (Real.sqrt (1 + 2 * x) - 1) ^ 2 := by
      ring_nf
      <;>
      nlinarith [Real.sqrt_nonneg (1 + 2 * x)]
    rw [h₃]
  
  have h_main_ineq : (Real.sqrt (1 + 2 * x) + 1) ^ 2 < (Real.sqrt (1 + 2 * x)) ^ 2 + 8 := by
    have h₃ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9 := h₂
    have h₄ : 4 * x ^ 2 = (Real.sqrt (1 + 2 * x) - 1) ^ 2 * (Real.sqrt (1 + 2 * x) + 1) ^ 2 := h_num_eq
    have h₅ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 = (Real.sqrt (1 + 2 * x) - 1) ^ 2 := h_denom_eq
    have h₆ : 0 < (1 - Real.sqrt (1 + 2 * x)) ^ 2 := h_denom_pos
    have h₇ : Real.sqrt (1 + 2 * x) ≠ 1 := h_sqrt_ne_one
    have h₈ : (Real.sqrt (1 + 2 * x) - 1) ≠ 0 := by
      intro h₈
      have h₉ : Real.sqrt (1 + 2 * x) = 1 := by linarith
      contradiction
    have h₉ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 = (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by
      calc
        4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 = ((Real.sqrt (1 + 2 * x) - 1) ^ 2 * (Real.sqrt (1 + 2 * x) + 1) ^ 2) / (1 - Real.sqrt (1 + 2 * x)) ^ 2 := by rw [h₄]
        _ = ((Real.sqrt (1 + 2 * x) - 1) ^ 2 * (Real.sqrt (1 + 2 * x) + 1) ^ 2) / (Real.sqrt (1 + 2 * x) - 1) ^ 2 := by rw [h₅]
        _ = (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by
          have h₁₀ : (Real.sqrt (1 + 2 * x) - 1) ^ 2 ≠ 0 := by
            intro h₁₀
            apply h₈
            nlinarith
          field_simp [h₁₀]
          <;> ring_nf
          <;> field_simp [h₁₀]
          <;> nlinarith
        _ = (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by rfl
    rw [h₉] at h₃
    have h₁₀ : (Real.sqrt (1 + 2 * x) + 1) ^ 2 < 2 * x + 9 := by linarith
    have h₁₁ : 2 * x + 9 = (Real.sqrt (1 + 2 * x)) ^ 2 + 8 := by
      have h₁₂ : (Real.sqrt (1 + 2 * x)) ^ 2 = 1 + 2 * x := by
        rw [Real.sq_sqrt] <;> linarith
      nlinarith
    rw [h₁₁] at h₁₀
    linarith
  
  have h_sqrt_lt : Real.sqrt (1 + 2 * x) < 7 / 2 := by
    have h₃ : (Real.sqrt (1 + 2 * x) + 1) ^ 2 < (Real.sqrt (1 + 2 * x)) ^ 2 + 8 := h_main_ineq
    have h₄ : 0 ≤ Real.sqrt (1 + 2 * x) := h_sqrt_nonneg
    nlinarith [Real.sqrt_nonneg (1 + 2 * x)]
  
  have h_x_lt : x < 45 / 8 := by
    have h₃ : Real.sqrt (1 + 2 * x) < 7 / 2 := h_sqrt_lt
    have h₄ : 0 ≤ Real.sqrt (1 + 2 * x) := h_sqrt_nonneg
    have h₅ : 0 ≤ 1 + 2 * x := h₀
    have h₆ : (Real.sqrt (1 + 2 * x)) ^ 2 < (7 / 2) ^ 2 := by
      gcongr
    have h₇ : (Real.sqrt (1 + 2 * x)) ^ 2 = 1 + 2 * x := by
      rw [Real.sq_sqrt] <;> linarith
    rw [h₇] at h₆
    norm_num at h₆ ⊢
    linarith
  
  have h_x_ge : -(1 / 2) ≤ x := by
    have h₃ : 0 ≤ 1 + 2 * x := h₀
    linarith
  
  exact ⟨h_x_ge, h_x_lt⟩

import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem imo_1960_p2 (x : ℝ) (h₀ : 0 ≤ 1 + 2 * x) (h₁ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0)
    (h₂ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9) : -(1 / 2) ≤ x ∧ x < 45 / 8 := by
  have h_lower : -(1 / 2 : ℝ) ≤ x := by
    have h₃ : 0 ≤ 1 + 2 * x := h₀
    have h₄ : -(1 / 2 : ℝ) ≤ x := by
      linarith
    exact h₄
  
  have h_y_def : 0 ≤ Real.sqrt (1 + 2 * x) := by
    apply Real.sqrt_nonneg
  
  have h_y_ne_one : Real.sqrt (1 + 2 * x) ≠ 1 := by
    intro h
    have h₃ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 = 0 := by
      rw [h]
      norm_num
    contradiction
  
  have h_main_ineq : Real.sqrt (1 + 2 * x) < 7 / 2 := by
    have h₃ : 0 ≤ Real.sqrt (1 + 2 * x) := h_y_def
    have h₄ : Real.sqrt (1 + 2 * x) ≠ 1 := h_y_ne_one
    have h₅ : 0 < (1 - Real.sqrt (1 + 2 * x)) ^ 2 := by
      have h₅₁ : (1 - Real.sqrt (1 + 2 * x)) ≠ 0 := by
        intro h₅₁
        have h₅₂ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 = 0 := by
          rw [h₅₁]
          <;> ring_nf
          <;> norm_num
        contradiction
      have h₅₂ : 0 < (1 - Real.sqrt (1 + 2 * x)) ^ 2 := by
        exact sq_pos_of_ne_zero h₅₁
      exact h₅₂
    -- Use the given inequality to derive a bound on sqrt(1 + 2x)
    have h₆ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9 := h₂
    have h₇ : (Real.sqrt (1 + 2 * x) + 1) ^ 2 < (Real.sqrt (1 + 2 * x)) ^ 2 + 8 := by
      have h₇₁ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9 := h₂
      have h₇₂ : (Real.sqrt (1 + 2 * x)) ^ 2 = 1 + 2 * x := by
        rw [Real.sq_sqrt] <;> linarith
      have h₇₃ : 4 * x ^ 2 = ( (Real.sqrt (1 + 2 * x)) ^ 2 - 1 ) ^ 2 := by
        have h₇₄ : (Real.sqrt (1 + 2 * x)) ^ 2 = 1 + 2 * x := by
          rw [Real.sq_sqrt] <;> linarith
        have h₇₅ : 4 * x ^ 2 = ( (Real.sqrt (1 + 2 * x)) ^ 2 - 1 ) ^ 2 := by
          calc
            4 * x ^ 2 = (2 * x) ^ 2 := by ring
            _ = ((Real.sqrt (1 + 2 * x)) ^ 2 - 1) ^ 2 := by
              have h₇₆ : (Real.sqrt (1 + 2 * x)) ^ 2 = 1 + 2 * x := by
                rw [Real.sq_sqrt] <;> linarith
              rw [h₇₆]
              <;> ring_nf
              <;> field_simp
              <;> ring_nf
            _ = ((Real.sqrt (1 + 2 * x)) ^ 2 - 1) ^ 2 := by ring
        exact h₇₅
      have h₇₄ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 = (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by
        have h₇₅ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 > 0 := by positivity
        have h₇₆ : 4 * x ^ 2 = ( (Real.sqrt (1 + 2 * x)) ^ 2 - 1 ) ^ 2 := h₇₃
        have h₇₇ : ( (Real.sqrt (1 + 2 * x)) ^ 2 - 1 ) ^ 2 = (Real.sqrt (1 + 2 * x) - 1) ^ 2 * (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by
          have h₇₈ : ( (Real.sqrt (1 + 2 * x)) ^ 2 - 1 ) ^ 2 = ((Real.sqrt (1 + 2 * x) - 1) * (Real.sqrt (1 + 2 * x) + 1)) ^ 2 := by
            ring_nf
            <;>
            nlinarith [Real.sqrt_nonneg (1 + 2 * x), Real.sq_sqrt (show 0 ≤ 1 + 2 * x by linarith)]
          calc
            ( (Real.sqrt (1 + 2 * x)) ^ 2 - 1 ) ^ 2 = ((Real.sqrt (1 + 2 * x) - 1) * (Real.sqrt (1 + 2 * x) + 1)) ^ 2 := by rw [h₇₈]
            _ = (Real.sqrt (1 + 2 * x) - 1) ^ 2 * (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by
              ring_nf
              <;>
              nlinarith [Real.sqrt_nonneg (1 + 2 * x), Real.sq_sqrt (show 0 ≤ 1 + 2 * x by linarith)]
        have h₇₈ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 = (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by
          calc
            4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 = ( (Real.sqrt (1 + 2 * x)) ^ 2 - 1 ) ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 := by
              rw [h₇₃]
            _ = ( (Real.sqrt (1 + 2 * x) - 1) ^ 2 * (Real.sqrt (1 + 2 * x) + 1) ^ 2 ) / (1 - Real.sqrt (1 + 2 * x)) ^ 2 := by
              rw [h₇₇]
            _ = (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by
              have h₇₉ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 = (Real.sqrt (1 + 2 * x) - 1) ^ 2 := by
                ring_nf
                <;>
                nlinarith [Real.sqrt_nonneg (1 + 2 * x), Real.sq_sqrt (show 0 ≤ 1 + 2 * x by linarith)]
              rw [h₇₉]
              have h₈₀ : (Real.sqrt (1 + 2 * x) - 1) ≠ 0 := by
                intro h₈₀
                have h₈₁ : Real.sqrt (1 + 2 * x) = 1 := by linarith
                contradiction
              field_simp [h₈₀]
              <;>
              ring_nf
              <;>
              nlinarith [Real.sqrt_nonneg (1 + 2 * x), Real.sq_sqrt (show 0 ≤ 1 + 2 * x by linarith)]
            _ = (Real.sqrt (1 + 2 * x) + 1) ^ 2 := by ring
        exact h₇₈
      have h₇₅ : (Real.sqrt (1 + 2 * x) + 1) ^ 2 < 2 * x + 9 := by
        linarith
      have h₇₆ : (Real.sqrt (1 + 2 * x)) ^ 2 = 1 + 2 * x := by
        rw [Real.sq_sqrt] <;> linarith
      nlinarith [Real.sqrt_nonneg (1 + 2 * x), Real.sq_sqrt (show 0 ≤ 1 + 2 * x by linarith)]
    -- Derive the final inequality from the squared form
    have h₈ : Real.sqrt (1 + 2 * x) < 7 / 2 := by
      nlinarith [Real.sqrt_nonneg (1 + 2 * x), Real.sq_sqrt (show 0 ≤ 1 + 2 * x by linarith)]
    exact h₈
  
  have h_upper : x < 45 / 8 := by
    have h₃ : Real.sqrt (1 + 2 * x) < 7 / 2 := h_main_ineq
    have h₄ : 0 ≤ Real.sqrt (1 + 2 * x) := h_y_def
    have h₅ : (Real.sqrt (1 + 2 * x)) ^ 2 < (7 / 2 : ℝ) ^ 2 := by
      have h₅₁ : Real.sqrt (1 + 2 * x) < 7 / 2 := h₃
      have h₅₂ : 0 ≤ Real.sqrt (1 + 2 * x) := h₄
      nlinarith [Real.sqrt_nonneg (1 + 2 * x)]
    have h₆ : (Real.sqrt (1 + 2 * x)) ^ 2 = 1 + 2 * x := by
      rw [Real.sq_sqrt] <;> linarith
    have h₇ : 1 + 2 * x < (7 / 2 : ℝ) ^ 2 := by
      linarith
    have h₈ : 1 + 2 * x < 49 / 4 := by
      norm_num at h₇ ⊢
      <;> linarith
    have h₉ : 2 * x < 45 / 4 := by linarith
    have h₁₀ : x < 45 / 8 := by linarith
    exact h₁₀
  
  have h_final : -(1 / 2) ≤ x ∧ x < 45 / 8 := by
    refine' ⟨h_lower, h_upper⟩
  
  exact h_final

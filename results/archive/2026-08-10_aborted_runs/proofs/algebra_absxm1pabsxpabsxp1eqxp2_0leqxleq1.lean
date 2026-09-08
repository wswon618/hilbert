import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 (x : ℝ)
    (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) : 0 ≤ x ∧ x ≤ 1 := by
  have h₁ : x ≥ 0 := by
    by_contra h
    -- Assume x < 0 and derive a contradiction
    have h₂ : x < 0 := by linarith
    have h₃ : abs (x - 1) + abs (x + 1) ≥ 2 := by
      -- Prove that |x - 1| + |x + 1| ≥ 2 using the triangle inequality
      cases' le_total 0 (x - 1) with h₄ h₄ <;>
        cases' le_total 0 (x + 1) with h₅ h₅ <;>
          cases' le_total 0 ((x - 1) - (x + 1)) with h₆ h₆ <;>
            simp_all [abs_of_nonneg, abs_of_nonpos, le_of_lt] <;>
              (try { contradiction }) <;>
                (try { linarith }) <;>
                  (try { nlinarith })
    have h₄ : abs x = -x := by
      rw [abs_of_neg h₂]
      <;> linarith
    have h₅ : abs (x - 1) + abs x + abs (x + 1) = x + 2 := h₀
    have h₆ : abs (x - 1) + abs (x + 1) = x + 2 - abs x := by linarith
    have h₇ : x + 2 - abs x ≥ 2 := by linarith
    have h₈ : x + 2 - (-x) ≥ 2 := by
      rw [h₄] at h₇
      linarith
    have h₉ : x ≥ 0 := by linarith
    linarith
  
  have h₂ : x ≤ 1 := by
    have h₃ : abs x = x := by
      rw [abs_of_nonneg h₁]
    have h₄ : abs (x - 1) + abs x + abs (x + 1) = x + 2 := h₀
    have h₅ : abs (x - 1) + x + abs (x + 1) = x + 2 := by
      rw [h₃] at h₄
      linarith
    have h₆ : abs (x - 1) + abs (x + 1) = 2 := by linarith
    have h₇ : abs (x + 1) = x + 1 := by
      have h₈ : x + 1 ≥ 0 := by linarith
      rw [abs_of_nonneg h₈]
    have h₈ : abs (x - 1) + (x + 1) = 2 := by
      rw [h₇] at h₆
      linarith
    have h₉ : abs (x - 1) = 1 - x := by linarith
    have h₁₀ : 1 - x ≥ 0 := by
      have h₁₁ : abs (x - 1) ≥ 0 := abs_nonneg (x - 1)
      linarith
    linarith
  
  have h₃ : 0 ≤ x ∧ x ≤ 1 := by
    exact ⟨h₁, h₂⟩
  
  exact h₃

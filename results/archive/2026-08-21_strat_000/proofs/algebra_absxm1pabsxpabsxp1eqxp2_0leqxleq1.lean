import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 (x : ℝ)
    (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) : 0 ≤ x ∧ x ≤ 1 := by
  have h₁ : 0 ≤ x := by
    have h₁₁ : x ≥ abs x := by
      have h₁₂ : abs (x - 1) + abs (x + 1) ≥ 2 := by
        -- Use the reverse triangle inequality to show that |x - 1| + |x + 1| ≥ 2
        cases' le_total 0 (x - 1) with h h <;>
          cases' le_total 0 (x + 1) with h₂ h₂ <;>
            cases' le_total 0 (x - 1 - (x + 1)) with h₃ h₃ <;>
              simp_all [abs_of_nonneg, abs_of_nonpos, le_of_lt] <;>
                (try { contradiction }) <;>
                  (try { linarith }) <;>
                    (try { nlinarith })
      -- Combine the inequalities to get x + 2 ≥ 2 + |x|
      have h₁₃ : abs (x - 1) + abs x + abs (x + 1) ≥ 2 + abs x := by
        linarith [abs_nonneg x]
      -- Use the given equation to get x + 2 ≥ 2 + |x|
      linarith
    -- Deduce that x ≥ 0 from x ≥ |x|
    cases' le_or_lt 0 x with h₂ h₂
    · -- Case: x ≥ 0
      linarith [abs_of_nonneg h₂]
    · -- Case: x < 0
      have h₃ : abs x = -x := by
        rw [abs_of_neg h₂]
      have h₄ : x ≥ -x := by linarith
      linarith
  
  have h₂ : x ≤ 1 := by
    have h₂₁ : x + 2 ≥ 3 * x := by
      -- Use the fact that for x ≥ 0, |x - 1| ≥ x - 1, |x| = x, |x + 1| = x + 1
      have h₂₂ : abs (x - 1) ≥ x - 1 := by
        -- Prove that |x - 1| ≥ x - 1
        cases' le_or_lt 0 (x - 1) with h h <;>
          simp_all [abs_of_nonneg, abs_of_neg, le_of_lt] <;>
            linarith
      have h₂₃ : abs x = x := by
        -- Prove that |x| = x since x ≥ 0
        rw [abs_of_nonneg h₁]
      have h₂₄ : abs (x + 1) = x + 1 := by
        -- Prove that |x + 1| = x + 1 since x + 1 > 0
        have h₂₅ : 0 ≤ x + 1 := by linarith
        rw [abs_of_nonneg h₂₅]
      -- Combine the inequalities to get x + 2 ≥ 3x
      have h₂₅ : abs (x - 1) + abs x + abs (x + 1) ≥ (x - 1) + x + (x + 1) := by
        linarith
      linarith
    -- Deduce that x ≤ 1 from x + 2 ≥ 3x
    linarith
  
  exact ⟨h₁, h₂⟩

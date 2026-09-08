import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem mathd_algebra_80 (x : ℝ) (h₀ : x ≠ -1) (h₁ : (x - 9) / (x + 1) = 2) : x = -11 := by
  have h₂ : x + 1 ≠ 0 := by
    intro h
    apply h₀
    linarith
  
  -- Eliminate the denominator by multiplying both sides by (x + 1)
  have h₃ : x - 9 = 2 * (x + 1) := by
    field_simp [h₂] at h₁
    linarith
  
  -- Expand and simplify the equation
  have h₄ : x - 9 = 2 * x + 2 := by
    linarith
  
  -- Solve for x
  have h₅ : x = -11 := by
    linarith
  
  -- The final result
  exact h₅

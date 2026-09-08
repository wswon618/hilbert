import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem mathd_algebra_113 (x : ℝ) : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
  have h₁ : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
    have h₂ : x ^ 2 - 14 * x + 3 ≥ -46 := by
      -- Prove that the quadratic expression is always at least -46
      nlinarith [sq_nonneg (x - 7)]
    -- Simplify the right-hand side of the original inequality
    norm_num at h₂ ⊢
    -- Use linear arithmetic to conclude the proof
    <;>
    (try nlinarith [sq_nonneg (x - 7)]) <;>
    (try nlinarith) <;>
    (try linarith)
  -- The main inequality follows directly from h₁
  exact h₁

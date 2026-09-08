import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem mathd_algebra_107 (x y : ℝ) (h₀ : x ^ 2 + 8 * x + y ^ 2 - 6 * y = 0) :
    (x + 4) ^ 2 + (y - 3) ^ 2 = 5 ^ 2 := by
  have h₁ : (x + 4) ^ 2 + (y - 3) ^ 2 = 25 := by
    have h₂ : x ^ 2 + 8 * x + y ^ 2 - 6 * y = 0 := h₀
    have h₃ : (x + 4) ^ 2 + (y - 3) ^ 2 = x ^ 2 + 8 * x + 16 + (y ^ 2 - 6 * y + 9) := by
      ring_nf
      <;>
      linarith
    have h₄ : (x + 4) ^ 2 + (y - 3) ^ 2 = x ^ 2 + 8 * x + y ^ 2 - 6 * y + 25 := by
      linarith
    have h₅ : (x + 4) ^ 2 + (y - 3) ^ 2 = 25 := by
      linarith
    exact h₅
  have h₆ : (x + 4) ^ 2 + (y - 3) ^ 2 = 5 ^ 2 := by
    norm_num at h₁ ⊢
    <;>
    linarith
  exact h₆

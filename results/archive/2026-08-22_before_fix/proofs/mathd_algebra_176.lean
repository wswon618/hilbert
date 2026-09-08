import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem mathd_algebra_176 (x : ℝ) : (x + 1) ^ 2 * x = x ^ 3 + 2 * x ^ 2 + x := by
  have h₀ : (x + 1) ^ 2 * x = x ^ 3 + 2 * x ^ 2 + x := by
    ring_nf
    <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try nlinarith)
  -- The `ring_nf` tactic normalizes the expression by expanding and simplifying it.
  -- The `norm_num`, `linarith`, and `nlinarith` tactics are used to handle numerical and linear arithmetic, but in this case, they are not necessary as `ring_nf` alone suffices.
  exact h₀

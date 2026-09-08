import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem mathd_numbertheory_85 : 1 * 3 ^ 3 + 2 * 3 ^ 2 + 2 * 3 + 2 = 53 := by
  norm_num
  <;> rfl
  <;> simp_all
  <;> norm_num
  <;> rfl

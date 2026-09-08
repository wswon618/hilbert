import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem mathd_numbertheory_517 : 121 * 122 * 123 % 4 = 2 := by
  norm_num [Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
  <;> rfl

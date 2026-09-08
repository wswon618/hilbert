import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem mathd_algebra_302 : (Complex.I / 2) ^ 2 = -(1 / 4) := by
  norm_num [Complex.ext_iff, pow_two, Complex.I_mul_I, Complex.I_mul_I]
  <;>
  simp_all [Complex.ext_iff, pow_two, Complex.I_mul_I, Complex.I_mul_I]
  <;>
  norm_num
  <;>
  ring_nf
  <;>
  simp_all [Complex.ext_iff, pow_two, Complex.I_mul_I, Complex.I_mul_I]
  <;>
  norm_num
  <;>
  linarith

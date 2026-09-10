import Mathlib
open BigOperators Real Nat Topology Rat
example : ¬ Function.Injective (fun t : (ℕ × ℕ) × ℕ => 1000*t.1.1 + 100*t.1.2 + 10*t.2) := by
  intro h
  have he := @h ((1,0),0) ((0,10),0) (by norm_num)
  have hc := congrArg (fun t : (ℕ × ℕ) × ℕ => t.1.1) he
  norm_num at hc
example : Nat.digits 10 2000 = [0,0,0,2] := by native_decide
example : 1 - 3 * Real.sin (Real.pi / 3) + 5 * Real.cos (3 * (Real.pi / 3)) ≠ 0 := by
  have hs : 0 < Real.sin (Real.pi / 3) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have he : 3 * (Real.pi / 3) = Real.pi := by ring
  rw [he, Real.cos_pi]
  linarith
example (a d : ℝ)
    (h0 : Finset.sum (Finset.range 5) (fun k : ℕ => a + k*d) = 70)
    (h1 : Finset.sum (Finset.range 10) (fun k : ℕ => a + k*d) = 210) : a = 42/5 := by
  norm_num [Finset.sum_range_succ] at h0 h1
  linarith
-- Preserve the raw notation to inspect its elaborated meaning.
def raw342 (a d k : ℝ) := (∑ k in Finset.range 5, a + k*d)
set_option pp.notation false
#print raw342

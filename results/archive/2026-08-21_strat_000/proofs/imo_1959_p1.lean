import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem imo_1959_p1 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  have h₁ : Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (14 * n + 3) (7 * n + 1) := by
    have h₁₁ : 21 * n + 4 = 1 * (14 * n + 3) + (7 * n + 1) := by
      ring_nf
      <;> omega
    rw [h₁₁]
    have h₁₂ : Nat.gcd (1 * (14 * n + 3) + (7 * n + 1)) (14 * n + 3) = Nat.gcd (14 * n + 3) (7 * n + 1) := by
      rw [show 1 * (14 * n + 3) + (7 * n + 1) = (14 * n + 3) + (7 * n + 1) by ring]
      -- Use the property of gcd to simplify the expression
      rw [Nat.gcd_comm]
      <;> simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
      <;>
      ring_nf at *
      <;>
      simp_all [Nat.gcd_comm]
      <;>
      linarith
    rw [h₁₂]
    <;>
    simp [Nat.gcd_comm]
  
  have h₂ : Nat.gcd (14 * n + 3) (7 * n + 1) = Nat.gcd (7 * n + 1) 1 := by
    have h₂₁ : 14 * n + 3 = 2 * (7 * n + 1) + 1 := by
      ring_nf
      <;> omega
    rw [h₂₁]
    have h₂₂ : Nat.gcd (2 * (7 * n + 1) + 1) (7 * n + 1) = Nat.gcd (7 * n + 1) 1 := by
      rw [show 2 * (7 * n + 1) + 1 = (7 * n + 1) + (7 * n + 1) + 1 by ring]
      -- Use the property of gcd to simplify the expression
      rw [show (7 * n + 1) + (7 * n + 1) + 1 = (7 * n + 1) + ((7 * n + 1) + 1) by ring]
      rw [Nat.gcd_comm]
      <;> simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
      <;>
      ring_nf at *
      <;>
      simp_all [Nat.gcd_comm]
      <;>
      linarith
    rw [h₂₂]
    <;>
    simp [Nat.gcd_comm]
  
  have h₃ : Nat.gcd (7 * n + 1) 1 = 1 := by
    have h₃₁ : Nat.gcd (7 * n + 1) 1 = 1 := by
      -- Use the property that gcd(a, 1) = 1 for any natural number a.
      have h₃₂ : Nat.gcd (7 * n + 1) 1 = 1 := by
        simp [Nat.gcd_one_right]
      exact h₃₂
    exact h₃₁
  
  have h₄ : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
    rw [h₁]
    rw [h₂]
    rw [h₃]
  
  apply h₄

import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h_mul_congr_mathd_numbertheory_233 : (24 * 116 : ℕ) ≡ 1 [MOD 11 ^ 2] := by
  norm_num [Nat.ModEq, Nat.pow_succ, Nat.pow_zero]
  <;> rfl

theorem h_res_mathd_numbertheory_233 (b : ZMod (11 ^ 2)) (h₀ : b = (24 : ZMod (11 ^ 2))⁻¹)
    (h_inv : (24 : ZMod (11 ^ 2))⁻¹ = (116 : ZMod (11 ^ 2))) :
    b = (116 : ZMod (11 ^ 2)) := by
  rw [h₀]
  rw [h_inv]
  <;> rfl

theorem h_mul_eq_mathd_numbertheory_233 (h_mul_congr : (24 * 116 : ℕ) ≡ 1 [MOD 11 ^ 2]) :
    ((24 * 116 : ℕ) : ZMod (11 ^ 2)) = (1 : ZMod (11 ^ 2)) := by
  have h₁ : (24 * 116 : ℕ) ≡ 1 [MOD 11 ^ 2] := h_mul_congr
  have h₂ : ((24 * 116 : ℕ) : ZMod (11 ^ 2)) = (1 : ZMod (11 ^ 2)) := by
    rw [← ZMod.eq_iff_modEq_nat] at *
    <;> simp_all [Nat.ModEq]
    <;> norm_num
    <;> rfl
  exact h₂

theorem h_inv_mathd_numbertheory_233 (h_mul_eq' :
    (24 : ZMod (11 ^ 2)) * (116 : ZMod (11 ^ 2)) = (1 : ZMod (11 ^ 2))) :
    (24 : ZMod (11 ^ 2))⁻¹ = (116 : ZMod (11 ^ 2)) := by
  simpa using
    (ZMod.inv_eq_of_mul_eq_one (n := 11 ^ 2)
      (a := (24 : ZMod (11 ^ 2))) (b := (116 : ZMod (11 ^ 2))) h_mul_eq')

theorem h_mul_eq'_mathd_numbertheory_233 (h_mul_eq :
    ((24 * 116 : ℕ) : ZMod (11 ^ 2)) = (1 : ZMod (11 ^ 2))) :
    (24 : ZMod (11 ^ 2)) * (116 : ZMod (11 ^ 2)) = (1 : ZMod (11 ^ 2)) := by
  have h_main : (24 : ZMod (11 ^ 2)) * (116 : ZMod (11 ^ 2)) = (1 : ZMod (11 ^ 2)) := by
    have h₁ : ((24 * 116 : ℕ) : ZMod (11 ^ 2)) = (24 : ZMod (11 ^ 2)) * (116 : ZMod (11 ^ 2)) := by
      norm_cast
      <;> simp [mul_comm]
      <;> rfl
    rw [h₁] at h_mul_eq
    exact h_mul_eq
  
  exact h_main

theorem mathd_numbertheory_233 (b : ZMod (11 ^ 2)) (h₀ : b = 24⁻¹) : b = 116 := by
  have h_mul_congr : (24 * 116 : ℕ) ≡ 1 [MOD 11 ^ 2] :=
    h_mul_congr_mathd_numbertheory_233
  have h_mul_eq : ((24 * 116 : ℕ) : ZMod (11 ^ 2)) = (1 : ZMod (11 ^ 2)) :=
    h_mul_eq_mathd_numbertheory_233 h_mul_congr
  have h_mul_eq' : (24 : ZMod (11 ^ 2)) * (116 : ZMod (11 ^ 2)) = (1 : ZMod (11 ^ 2)) :=
    h_mul_eq'_mathd_numbertheory_233 h_mul_eq
  have h_inv : (24 : ZMod (11 ^ 2))⁻¹ = (116 : ZMod (11 ^ 2)) :=
    h_inv_mathd_numbertheory_233 h_mul_eq'
  have h_res : b = (116 : ZMod (11 ^ 2)) :=
    h_res_mathd_numbertheory_233 b h₀ h_inv
  simpa using h_res

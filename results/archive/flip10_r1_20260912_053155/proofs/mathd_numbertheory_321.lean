import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h_congr_mathd_numbertheory_321 : (160 * 1058) ≡ 1 [MOD 1399] := by
  norm_num [Nat.ModEq, Nat.ModEq]
  <;> rfl

theorem h_mul_mathd_numbertheory_321 (h_eq :
    ((160 * 1058 : ℕ) : ZMod 1399) = (1 : ZMod 1399)) :
    ((160 : ZMod 1399) * (1058 : ZMod 1399)) = (1 : ZMod 1399) := by
  have h₁ : ((160 : ZMod 1399) * (1058 : ZMod 1399)) = (1 : ZMod 1399) := by
    -- Convert the given hypothesis to the appropriate form
    norm_cast at h_eq ⊢
    <;>
    (try decide) <;>
    (try ring_nf at h_eq ⊢) <;>
    (try simp_all [ZMod.nat_cast_self]) <;>
    (try norm_num at h_eq ⊢) <;>
    (try contradiction) <;>
    (try omega)
    <;>
    rfl
  exact h₁

theorem h_eq_mathd_numbertheory_321 (h_congr : (160 * 1058) ≡ 1 [MOD 1399]) :
    ((160 * 1058 : ℕ) : ZMod 1399) = (1 : ZMod 1399) := by
  exact
    (ZMod.natCast_eq_natCast_iff (a := 160 * 1058) (b := 1) (c := 1399)).mpr
      h_congr

theorem h_inv_mathd_numbertheory_321 (h_mul :
    ((160 : ZMod 1399) * (1058 : ZMod 1399)) = (1 : ZMod 1399)) :
    (160 : ZMod 1399)⁻¹ = (1058 : ZMod 1399) := by
  simpa using (ZMod.inv_eq_of_mul_eq_one _ _ _ h_mul)

theorem mathd_numbertheory_321 (n : ZMod 1399) (h₁ : n = 160⁻¹) : n = 1058 := by
  have h_congr : (160 * 1058) ≡ 1 [MOD 1399] := by
    exact h_congr_mathd_numbertheory_321
  have h_eq : ((160 * 1058 : ℕ) : ZMod 1399) = (1 : ZMod 1399) := by
    exact h_eq_mathd_numbertheory_321 h_congr
  have h_mul : ((160 : ZMod 1399) * (1058 : ZMod 1399)) = (1 : ZMod 1399) := by
    exact h_mul_mathd_numbertheory_321 h_eq
  have h_inv : (160 : ZMod 1399)⁻¹ = (1058 : ZMod 1399) := by
    exact h_inv_mathd_numbertheory_321 h_mul
  calc
    n = (160 : ZMod 1399)⁻¹ := by
      simpa using h₁
    _ = 1058 := by
      simpa using h_inv

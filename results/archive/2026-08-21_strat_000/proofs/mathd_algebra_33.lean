import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem mathd_algebra_33 (x y z : ℝ) (h₀ : x ≠ 0) (h₁ : 2 * x = 5 * y) (h₂ : 7 * y = 10 * z) :
    z / x = 7 / 25 := by
  have h₃ : y = (2 * x) / 5 := by
    have h₃₁ : 2 * x = 5 * y := h₁
    have h₃₂ : y = (2 * x) / 5 := by
      apply Eq.symm
      -- We need to show that (2 * x) / 5 = y
      -- Start with the given equation 2 * x = 5 * y
      -- Divide both sides by 5 to get (2 * x) / 5 = y
      field_simp at h₃₁ ⊢
      <;> ring_nf at h₃₁ ⊢ <;> nlinarith
    exact h₃₂
  
  have h₄ : z = (7 * y) / 10 := by
    have h₄₁ : 7 * y = 10 * z := h₂
    have h₄₂ : z = (7 * y) / 10 := by
      apply Eq.symm
      -- We need to show that (7 * y) / 10 = z
      -- Start with the given equation 7 * y = 10 * z
      -- Divide both sides by 10 to get (7 * y) / 10 = z
      field_simp at h₄₁ ⊢
      <;> ring_nf at h₄₁ ⊢ <;> nlinarith
    exact h₄₂
  
  have h₅ : z / x = 7 / 25 := by
    have h₅₁ : z = (7 * y) / 10 := h₄
    have h₅₂ : y = (2 * x) / 5 := h₃
    rw [h₅₁, h₅₂]
    have h₅₃ : x ≠ 0 := h₀
    field_simp [h₅₃]
    <;> ring_nf
    <;> field_simp [h₅₃]
    <;> ring_nf
    <;> nlinarith
  
  exact h₅

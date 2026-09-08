import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem amc12b_2020_p22 (t : ℝ) : (2 ^ t - 3 * t) * t / 4 ^ t ≤ 1 / 12 := by
  have h_main : ( (2 : ℝ) ^ t - 3 * t ) * t / (4 : ℝ) ^ t = (t / (2 : ℝ) ^ t) - 3 * (t / (2 : ℝ) ^ t) ^ 2 := by
    have h₁ : (4 : ℝ) ^ t = (2 : ℝ) ^ (2 * t) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ ( (2 : ℝ) ) by norm_num]
      rw [← Real.rpow_mul] <;> ring_nf <;>
      norm_num
      <;> linarith
    have h₂ : (2 : ℝ) ^ (2 * t) = ((2 : ℝ) ^ t) ^ 2 := by
      have h₃ : (2 : ℝ) ^ (2 * t) = (2 : ℝ) ^ (t + t) := by ring_nf
      rw [h₃]
      have h₄ : (2 : ℝ) ^ (t + t) = (2 : ℝ) ^ t * (2 : ℝ) ^ t := by
        rw [Real.rpow_add (by norm_num : (2 : ℝ) > 0)] <;> ring_nf
      rw [h₄]
      ring_nf
      <;> field_simp [Real.rpow_neg]
      <;> ring_nf
    have h₃ : (4 : ℝ) ^ t = ((2 : ℝ) ^ t) ^ 2 := by
      rw [h₁, h₂]
    have h₄ : ( (2 : ℝ) ^ t - 3 * t ) * t / (4 : ℝ) ^ t = ( (2 : ℝ) ^ t * t - 3 * t ^ 2 ) / (4 : ℝ) ^ t := by
      ring_nf
      <;> field_simp [Real.rpow_neg]
      <;> ring_nf
    rw [h₄]
    have h₅ : ( (2 : ℝ) ^ t * t - 3 * t ^ 2 ) / (4 : ℝ) ^ t = (t / (2 : ℝ) ^ t) - 3 * (t / (2 : ℝ) ^ t) ^ 2 := by
      have h₆ : (4 : ℝ) ^ t = ((2 : ℝ) ^ t) ^ 2 := by rw [h₃]
      rw [h₆]
      have h₇ : (2 : ℝ) ^ t > 0 := by positivity
      field_simp [h₇.ne']
      <;> ring_nf
      <;> field_simp [h₇.ne']
      <;> ring_nf
      <;> field_simp [h₇.ne']
      <;> ring_nf
    rw [h₅]
    <;> ring_nf
  
  have h_quadratic : ∀ (y : ℝ), y - 3 * y ^ 2 ≤ 1 / 12 := by
    intro y
    have h₁ : y - 3 * y ^ 2 ≤ 1 / 12 := by
      nlinarith [sq_nonneg (y - 1 / 6), sq_nonneg (y + 1 / 6)]
    exact h₁
  
  have h_final : ( (2 : ℝ) ^ t - 3 * t ) * t / (4 : ℝ) ^ t ≤ 1 / 12 := by
    have h₁ : ( (2 : ℝ) ^ t - 3 * t ) * t / (4 : ℝ) ^ t = (t / (2 : ℝ) ^ t) - 3 * (t / (2 : ℝ) ^ t) ^ 2 := by
      rw [h_main]
    rw [h₁]
    have h₂ : (t / (2 : ℝ) ^ t : ℝ) - 3 * (t / (2 : ℝ) ^ t : ℝ) ^ 2 ≤ 1 / 12 := by
      have h₃ : ∀ (y : ℝ), y - 3 * y ^ 2 ≤ 1 / 12 := h_quadratic
      have h₄ : (t / (2 : ℝ) ^ t : ℝ) - 3 * (t / (2 : ℝ) ^ t : ℝ) ^ 2 ≤ 1 / 12 := by
        have h₅ : (t / (2 : ℝ) ^ t : ℝ) - 3 * (t / (2 : ℝ) ^ t : ℝ) ^ 2 ≤ 1 / 12 := by
          have h₆ := h₃ (t / (2 : ℝ) ^ t)
          linarith
        linarith
      linarith
    linarith
  
  exact h_final

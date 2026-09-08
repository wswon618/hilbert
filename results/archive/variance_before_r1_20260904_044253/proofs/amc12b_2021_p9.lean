import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem amc12b_2021_p9 :
    Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) -
        Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) =
      2 := by
  have h₁ : Real.log 80 = 4 * Real.log 2 + Real.log 5 := by
    have h₁₁ : Real.log 80 = Real.log (2 ^ 4 * 5) := by norm_num
    rw [h₁₁]
    have h₁₂ : Real.log (2 ^ 4 * 5) = Real.log (2 ^ 4) + Real.log 5 := by
      rw [Real.log_mul (by positivity) (by positivity)]
    rw [h₁₂]
    have h₁₃ : Real.log (2 ^ 4) = 4 * Real.log 2 := by
      rw [Real.log_pow] <;> norm_num
    rw [h₁₃]
    <;> ring
    <;> norm_num
  
  have h₂ : Real.log 40 = 3 * Real.log 2 + Real.log 5 := by
    have h₂₁ : Real.log 40 = Real.log (2 ^ 3 * 5) := by norm_num
    rw [h₂₁]
    have h₂₂ : Real.log (2 ^ 3 * 5) = Real.log (2 ^ 3) + Real.log 5 := by
      rw [Real.log_mul (by positivity) (by positivity)]
    rw [h₂₂]
    have h₂₃ : Real.log (2 ^ 3) = 3 * Real.log 2 := by
      rw [Real.log_pow] <;> norm_num
    rw [h₂₃]
    <;> ring
    <;> norm_num
  
  have h₃ : Real.log 160 = 5 * Real.log 2 + Real.log 5 := by
    have h₃₁ : Real.log 160 = Real.log (2 ^ 5 * 5) := by norm_num
    rw [h₃₁]
    have h₃₂ : Real.log (2 ^ 5 * 5) = Real.log (2 ^ 5) + Real.log 5 := by
      rw [Real.log_mul (by positivity) (by positivity)]
    rw [h₃₂]
    have h₃₃ : Real.log (2 ^ 5) = 5 * Real.log 2 := by
      rw [Real.log_pow] <;> norm_num
    rw [h₃₃]
    <;> ring
    <;> norm_num
  
  have h₄ : Real.log 20 = 2 * Real.log 2 + Real.log 5 := by
    have h₄₁ : Real.log 20 = Real.log (2 ^ 2 * 5) := by norm_num
    rw [h₄₁]
    have h₄₂ : Real.log (2 ^ 2 * 5) = Real.log (2 ^ 2) + Real.log 5 := by
      rw [Real.log_mul (by positivity) (by positivity)]
    rw [h₄₂]
    have h₄₃ : Real.log (2 ^ 2) = 2 * Real.log 2 := by
      rw [Real.log_pow] <;> norm_num
    rw [h₄₃]
    <;> ring
    <;> norm_num
  
  have h₅ : (Real.log 80 * Real.log 40 - Real.log 160 * Real.log 20) = 2 * (Real.log 2)^2 := by
    rw [h₁, h₂, h₃, h₄]
    ring_nf
    <;>
    (try norm_num) <;>
    (try
      {
        have h₅₁ : Real.log 2 > 0 := Real.log_pos (by norm_num)
        have h₅₂ : Real.log 5 > 0 := Real.log_pos (by norm_num)
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2), Real.log_pos (by norm_num : (1 : ℝ) < 5)]
      }) <;>
    (try
      {
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2), Real.log_pos (by norm_num : (1 : ℝ) < 5)]
      })
    <;>
    (try
      {
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2), Real.log_pos (by norm_num : (1 : ℝ) < 5)]
      })
  
  have h₆ : Real.log 2 ≠ 0 := by
    have h₆₁ : Real.log 2 > 0 := Real.log_pos (by norm_num)
    linarith
  
  have h₇ : Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) - Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) = 2 := by
    have h₇₁ : Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) = (Real.log 80 * Real.log 40) / (Real.log 2) ^ 2 := by
      have h₇₁₁ : Real.log 2 ≠ 0 := h₆
      have h₇₁₂ : Real.log 40 ≠ 0 := by
        have h₇₁₃ : Real.log 40 > 0 := Real.log_pos (by norm_num)
        linarith
      field_simp [h₇₁₁, h₇₁₂]
      <;> ring_nf
      <;> field_simp [h₇₁₁, h₇₁₂]
      <;> ring_nf
    have h₇₂ : Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) = (Real.log 160 * Real.log 20) / (Real.log 2) ^ 2 := by
      have h₇₂₁ : Real.log 2 ≠ 0 := h₆
      have h₇₂₂ : Real.log 20 ≠ 0 := by
        have h₇₂₃ : Real.log 20 > 0 := Real.log_pos (by norm_num)
        linarith
      field_simp [h₇₂₁, h₇₂₂]
      <;> ring_nf
      <;> field_simp [h₇₂₁, h₇₂₂]
      <;> ring_nf
    rw [h₇₁, h₇₂]
    have h₇₃ : (Real.log 80 * Real.log 40) / (Real.log 2) ^ 2 - (Real.log 160 * Real.log 20) / (Real.log 2) ^ 2 = 2 := by
      have h₇₃₁ : Real.log 80 * Real.log 40 - Real.log 160 * Real.log 20 = 2 * (Real.log 2) ^ 2 := by
        linarith
      have h₇₃₂ : (Real.log 80 * Real.log 40) / (Real.log 2) ^ 2 - (Real.log 160 * Real.log 20) / (Real.log 2) ^ 2 = (Real.log 80 * Real.log 40 - Real.log 160 * Real.log 20) / (Real.log 2) ^ 2 := by
        ring_nf
        <;> field_simp [h₆]
        <;> ring_nf
      rw [h₇₃₂]
      have h₇₃₃ : (Real.log 80 * Real.log 40 - Real.log 160 * Real.log 20) / (Real.log 2) ^ 2 = 2 := by
        rw [h₇₃₁]
        have h₇₃₄ : (2 : ℝ) * (Real.log 2) ^ 2 / (Real.log 2) ^ 2 = 2 := by
          have h₇₃₅ : (Real.log 2) ^ 2 ≠ 0 := by
            have h₇₃₆ : Real.log 2 ≠ 0 := h₆
            positivity
          field_simp [h₇₃₅]
          <;> ring_nf
          <;> field_simp [h₇₃₅]
          <;> linarith
        rw [h₇₃₄]
      rw [h₇₃₃]
    linarith
  
  rw [h₇]
  <;> norm_num

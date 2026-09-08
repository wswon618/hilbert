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
  
  have h₅ : Real.log 80 * Real.log 40 - Real.log 160 * Real.log 20 = 2 * (Real.log 2)^2 := by
    rw [h₁, h₂, h₃, h₄]
    ring_nf
    <;>
    (try norm_num) <;>
    (try
      {
        have h₅₁ : Real.log 2 ≠ 0 := by
          exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
        have h₅₂ : Real.log 5 ≠ 0 := by
          exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2),
          Real.log_pos (by norm_num : (1 : ℝ) < 5)]
      }) <;>
    (try
      {
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2),
          Real.log_pos (by norm_num : (1 : ℝ) < 5)]
      })
    <;>
    (try
      {
        ring_nf at *
        <;>
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2),
          Real.log_pos (by norm_num : (1 : ℝ) < 5)]
      })
  
  have h₆ : Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) - Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) = 2 := by
    have h₆₁ : Real.log 2 ≠ 0 := by
      exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
    have h₆₂ : Real.log 40 ≠ 0 := by
      have h₆₂₁ : Real.log 40 > 0 := Real.log_pos (by norm_num)
      linarith
    have h₆₃ : Real.log 20 ≠ 0 := by
      have h₆₃₁ : Real.log 20 > 0 := Real.log_pos (by norm_num)
      linarith
    have h₆₄ : Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) = (Real.log 80 * Real.log 40) / (Real.log 2)^2 := by
      field_simp [h₆₁, h₆₂]
      <;> ring
      <;> field_simp [h₆₁, h₆₂]
      <;> ring
    have h₆₅ : Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) = (Real.log 160 * Real.log 20) / (Real.log 2)^2 := by
      field_simp [h₆₁, h₆₃]
      <;> ring
      <;> field_simp [h₆₁, h₆₃]
      <;> ring
    rw [h₆₄, h₆₅]
    have h₆₆ : (Real.log 80 * Real.log 40) / (Real.log 2)^2 - (Real.log 160 * Real.log 20) / (Real.log 2)^2 = 2 := by
      have h₆₆₁ : (Real.log 80 * Real.log 40) / (Real.log 2)^2 - (Real.log 160 * Real.log 20) / (Real.log 2)^2 = (Real.log 80 * Real.log 40 - Real.log 160 * Real.log 20) / (Real.log 2)^2 := by
        ring
      rw [h₆₆₁]
      have h₆₆₂ : Real.log 80 * Real.log 40 - Real.log 160 * Real.log 20 = 2 * (Real.log 2)^2 := h₅
      rw [h₆₆₂]
      have h₆₆₃ : (2 * (Real.log 2)^2 : ℝ) / (Real.log 2)^2 = 2 := by
        have h₆₆₄ : (Real.log 2 : ℝ) ≠ 0 := by
          exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
        field_simp [h₆₆₄]
        <;> ring
        <;> field_simp [h₆₆₄]
        <;> ring
      rw [h₆₆₃]
    linarith
  
  exact h₆

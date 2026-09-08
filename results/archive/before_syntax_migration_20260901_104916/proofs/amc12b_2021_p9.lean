import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem amc12b_2021_p9 :
    Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) -
        Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) =
      2 := by
  have h₁ : Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) = Real.log 80 / Real.log 2 * (Real.log 40 / Real.log 2) := by
    field_simp [Real.log_mul, Real.log_pow]
    <;> ring_nf
    <;> field_simp [Real.log_mul, Real.log_pow]
    <;> ring_nf
  
  have h₂ : Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) = Real.log 160 / Real.log 2 * (Real.log 20 / Real.log 2) := by
    field_simp [Real.log_mul, Real.log_pow]
    <;> ring_nf
    <;> field_simp [Real.log_mul, Real.log_pow]
    <;> ring_nf
  
  have h₃ : Real.log 80 / Real.log 2 * (Real.log 40 / Real.log 2) - Real.log 160 / Real.log 2 * (Real.log 20 / Real.log 2) = 2 := by
    have h₄ : Real.log 80 = Real.log (2 ^ 4 * 5) := by norm_num
    have h₅ : Real.log 40 = Real.log (2 ^ 3 * 5) := by norm_num
    have h₆ : Real.log 160 = Real.log (2 ^ 5 * 5) := by norm_num
    have h₇ : Real.log 20 = Real.log (2 ^ 2 * 5) := by norm_num
    rw [h₄, h₅, h₆, h₇]
    have h₈ : Real.log (2 ^ 4 * 5) = Real.log (2 ^ 4) + Real.log 5 := by
      rw [Real.log_mul (by positivity) (by positivity)]
    have h₉ : Real.log (2 ^ 3 * 5) = Real.log (2 ^ 3) + Real.log 5 := by
      rw [Real.log_mul (by positivity) (by positivity)]
    have h₁₀ : Real.log (2 ^ 5 * 5) = Real.log (2 ^ 5) + Real.log 5 := by
      rw [Real.log_mul (by positivity) (by positivity)]
    have h₁₁ : Real.log (2 ^ 2 * 5) = Real.log (2 ^ 2) + Real.log 5 := by
      rw [Real.log_mul (by positivity) (by positivity)]
    rw [h₈, h₉, h₁₀, h₁₁]
    have h₁₂ : Real.log (2 ^ 4) = 4 * Real.log 2 := by
      rw [Real.log_pow] <;> norm_num
    have h₁₃ : Real.log (2 ^ 3) = 3 * Real.log 2 := by
      rw [Real.log_pow] <;> norm_num
    have h₁₄ : Real.log (2 ^ 5) = 5 * Real.log 2 := by
      rw [Real.log_pow] <;> norm_num
    have h₁₅ : Real.log (2 ^ 2) = 2 * Real.log 2 := by
      rw [Real.log_pow] <;> norm_num
    rw [h₁₂, h₁₃, h₁₄, h₁₅]
    have h₁₆ : Real.log 2 ≠ 0 := by
      exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
    field_simp [h₁₆]
    ring_nf
    <;>
    (try norm_num) <;>
    (try
      {
        have h₁₇ : Real.log 5 ≠ 0 := by
          exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
        field_simp [h₁₇]
        <;> ring_nf
        <;> norm_num
        <;>
        (try
          {
            nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2), Real.log_pos (by norm_num : (1 : ℝ) < 5)]
          })
      }) <;>
    (try
      {
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2), Real.log_pos (by norm_num : (1 : ℝ) < 5)]
      })
    <;>
    (try
      {
        field_simp [h₁₆]
        <;> ring_nf
        <;> norm_num
        <;>
        (try
          {
            nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2), Real.log_pos (by norm_num : (1 : ℝ) < 5)]
          })
      })
  
  rw [h₁, h₂]
  linarith

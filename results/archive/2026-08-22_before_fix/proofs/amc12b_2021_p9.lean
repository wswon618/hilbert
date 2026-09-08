import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem amc12b_2021_p9 :
    Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) -
        Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) =
      2 := by
  have h₁ : Real.log 80 = 4 * Real.log 2 + Real.log 5 := by
    have h₁₀ : Real.log 80 = Real.log (2 ^ 4 * 5) := by norm_num
    rw [h₁₀]
    have h₁₁ : Real.log (2 ^ 4 * 5) = Real.log (2 ^ 4) + Real.log 5 := by
      rw [Real.log_mul (by positivity) (by positivity)]
    rw [h₁₁]
    have h₁₂ : Real.log (2 ^ 4) = 4 * Real.log 2 := by
      rw [Real.log_pow] <;> norm_num
    rw [h₁₂]
    <;> ring
    <;> norm_num
  
  have h₂ : Real.log 40 = 3 * Real.log 2 + Real.log 5 := by
    have h₂₀ : Real.log 40 = Real.log (2 ^ 3 * 5) := by norm_num
    rw [h₂₀]
    have h₂₁ : Real.log (2 ^ 3 * 5) = Real.log (2 ^ 3) + Real.log 5 := by
      rw [Real.log_mul (by positivity) (by positivity)]
    rw [h₂₁]
    have h₂₂ : Real.log (2 ^ 3) = 3 * Real.log 2 := by
      rw [Real.log_pow] <;> norm_num
    rw [h₂₂]
    <;> ring
    <;> norm_num
  
  have h₃ : Real.log 160 = 5 * Real.log 2 + Real.log 5 := by
    have h₃₀ : Real.log 160 = Real.log (2 ^ 5 * 5) := by norm_num
    rw [h₃₀]
    have h₃₁ : Real.log (2 ^ 5 * 5) = Real.log (2 ^ 5) + Real.log 5 := by
      rw [Real.log_mul (by positivity) (by positivity)]
    rw [h₃₁]
    have h₃₂ : Real.log (2 ^ 5) = 5 * Real.log 2 := by
      rw [Real.log_pow] <;> norm_num
    rw [h₃₂]
    <;> ring
    <;> norm_num
  
  have h₄ : Real.log 20 = 2 * Real.log 2 + Real.log 5 := by
    have h₄₀ : Real.log 20 = Real.log (2 ^ 2 * 5) := by norm_num
    rw [h₄₀]
    have h₄₁ : Real.log (2 ^ 2 * 5) = Real.log (2 ^ 2) + Real.log 5 := by
      rw [Real.log_mul (by positivity) (by positivity)]
    rw [h₄₁]
    have h₄₂ : Real.log (2 ^ 2) = 2 * Real.log 2 := by
      rw [Real.log_pow] <;> norm_num
    rw [h₄₂]
    <;> ring
    <;> norm_num
  
  have h₅ : (Real.log 80) * (Real.log 40) - (Real.log 160) * (Real.log 20) = 2 * (Real.log 2)^2 := by
    rw [h₁, h₂, h₃, h₄]
    ring_nf
    <;>
    (try norm_num) <;>
    (try
      {
        have h₅₁ : Real.log 5 > 0 := Real.log_pos (by norm_num)
        have h₅₂ : Real.log 2 > 0 := Real.log_pos (by norm_num)
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
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2),
          Real.log_pos (by norm_num : (1 : ℝ) < 5)]
      })
  
  have h₆ : Real.log 2 ≠ 0 := by
    have h₆₁ : Real.log 2 > 0 := Real.log_pos (by norm_num)
    linarith
  
  have h₇ : Real.log 40 ≠ 0 := by
    have h₇₁ : Real.log 40 > 0 := Real.log_pos (by norm_num)
    linarith
  
  have h₈ : Real.log 20 ≠ 0 := by
    have h₈₁ : Real.log 20 > 0 := Real.log_pos (by norm_num)
    linarith
  
  have h₉ : Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) - Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) = 2 := by
    have h₉₁ : Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) = (Real.log 80 * Real.log 40) / (Real.log 2 * Real.log 2) := by
      field_simp [h₆, h₇]
      <;> ring_nf
      <;> field_simp [h₆, h₇]
      <;> ring_nf
    have h₉₂ : Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) = (Real.log 160 * Real.log 20) / (Real.log 2 * Real.log 2) := by
      field_simp [h₆, h₈]
      <;> ring_nf
      <;> field_simp [h₆, h₈]
      <;> ring_nf
    rw [h₉₁, h₉₂]
    have h₉₃ : (Real.log 80 * Real.log 40) / (Real.log 2 * Real.log 2) - (Real.log 160 * Real.log 20) / (Real.log 2 * Real.log 2) = ((Real.log 80 * Real.log 40) - (Real.log 160 * Real.log 20)) / (Real.log 2 * Real.log 2) := by
      have h₉₃₁ : (Real.log 2 * Real.log 2) ≠ 0 := by
        have h₉₃₂ : Real.log 2 ≠ 0 := h₆
        have h₉₃₃ : Real.log 2 * Real.log 2 ≠ 0 := by
          intro h
          apply h₉₃₂
          nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
        exact h₉₃₃
      field_simp [h₉₃₁]
      <;> ring_nf
      <;> field_simp [h₉₃₁]
      <;> ring_nf
    rw [h₉₃]
    have h₉₄ : ((Real.log 80 * Real.log 40) - (Real.log 160 * Real.log 20)) = 2 * (Real.log 2)^2 := by
      linarith
    rw [h₉₄]
    have h₉₅ : (2 * (Real.log 2)^2 : ℝ) / (Real.log 2 * Real.log 2) = 2 := by
      have h₉₅₁ : Real.log 2 ≠ 0 := h₆
      have h₉₅₂ : (Real.log 2 : ℝ) * Real.log 2 ≠ 0 := by
        intro h
        apply h₉₅₁
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      field_simp [h₉₅₂]
      <;> ring_nf
      <;> field_simp [h₉₅₁]
      <;> ring_nf
      <;> nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    rw [h₉₅]
  
  exact h₉

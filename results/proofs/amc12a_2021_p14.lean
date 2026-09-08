import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h_sum2_amc12a_2021_p14
    (h_term2 :
      ∀ k : ℕ, (1 : ℕ) ≤ k → Real.logb (9 ^ k) (25 ^ k) = Real.logb 9 25) :
    (∑ k in Finset.Icc 1 100, Real.logb (9 ^ k) (25 ^ k)) =
      (100 : ℝ) * Real.logb 9 25 := by
  have h_sum : (∑ k in Finset.Icc 1 100, Real.logb (9 ^ k) (25 ^ k)) = ∑ k in Finset.Icc 1 100, Real.logb 9 25 := by
    apply Finset.sum_congr rfl
    intro k hk
    have h₁ : 1 ≤ k := by
      simp only [Finset.mem_Icc] at hk
      linarith
    have h₂ : Real.logb (9 ^ k) (25 ^ k) = Real.logb 9 25 := h_term2 k h₁
    rw [h₂]
  rw [h_sum]
  have h_sum_const : ∑ k in Finset.Icc 1 100, Real.logb 9 25 = (100 : ℝ) * Real.logb 9 25 := by
    simp [Finset.sum_const, Finset.card_range]
    <;> norm_num
    <;> field_simp [Real.logb]
    <;> ring
    <;> norm_num
    <;> simp_all [Finset.sum_const, Finset.card_range]
    <;> norm_num
    <;> linarith
  rw [h_sum_const]
  <;> norm_num

theorem h_term1_amc12a_2021_p14 (k : ℕ) (hk : (1 : ℕ) ≤ k) :
    Real.logb (5 ^ k) (3 ^ k ^ 2) = (k : ℝ) * Real.logb 5 3 := by
  have h₁ : Real.logb (5 ^ k) (3 ^ k ^ 2) = (Real.log ((3 : ℝ) ^ (k ^ 2)) / Real.log ((5 : ℝ) ^ k)) := by
    rw [Real.logb]
    <;> norm_cast
    <;> field_simp [Real.log_rpow, Real.log_pow]
    <;> ring_nf
    <;> norm_cast
    <;> simp [pow_mul]
    <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
    <;> ring_nf
    <;> norm_cast
  
  have h₂ : (Real.log ((3 : ℝ) ^ (k ^ 2)) / Real.log ((5 : ℝ) ^ k)) = (k : ℝ) * Real.logb 5 3 := by
    have h₃ : Real.log ((3 : ℝ) ^ (k ^ 2)) = (k ^ 2 : ℝ) * Real.log 3 := by
      rw [Real.log_pow]
      <;> norm_cast
      <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
      <;> ring_nf
      <;> norm_cast
      <;> simp [pow_mul]
      <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
      <;> ring_nf
      <;> norm_cast
    have h₄ : Real.log ((5 : ℝ) ^ k) = (k : ℝ) * Real.log 5 := by
      rw [Real.log_pow]
      <;> norm_cast
      <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
      <;> ring_nf
      <;> norm_cast
      <;> simp [pow_mul]
      <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
      <;> ring_nf
      <;> norm_cast
    rw [h₃, h₄]
    have h₅ : Real.logb 5 3 = Real.log 3 / Real.log 5 := by
      rw [Real.logb]
      <;> norm_cast
    rw [h₅]
    have h₆ : ((k ^ 2 : ℝ) * Real.log 3) / ((k : ℝ) * Real.log 5) = (k : ℝ) * (Real.log 3 / Real.log 5) := by
      have h₇ : (k : ℝ) ≠ 0 := by
        norm_cast
        <;> linarith
      have h₈ : (k : ℝ) > 0 := by
        norm_cast
        <;> linarith
      field_simp [h₇, h₈.ne']
      <;> ring_nf
      <;> field_simp [h₇, h₈.ne']
      <;> ring_nf
      <;> norm_cast
      <;> field_simp [h₇, h₈.ne']
      <;> ring_nf
      <;> norm_cast
      <;> linarith
    rw [h₆]
    <;> ring_nf
    <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
    <;> ring_nf
    <;> norm_cast
  
  rw [h₁]
  rw [h₂]

theorem h_CD_amc12a_2021_p14 :
    Real.logb 5 3 * Real.logb 9 25 = (1 : ℝ) := by
  have h₁ : Real.logb 5 3 = Real.log 3 / Real.log 5 := by
    rw [Real.logb]
    <;> field_simp
  
  have h₂ : Real.logb 9 25 = Real.log 25 / Real.log 9 := by
    rw [Real.logb]
    <;> field_simp
  
  have h₃ : Real.log 25 = 2 * Real.log 5 := by
    have h₃₁ : Real.log 25 = Real.log (5 ^ 2) := by norm_num
    rw [h₃₁]
    have h₃₂ : Real.log (5 ^ 2) = 2 * Real.log 5 := by
      rw [Real.log_pow] <;> norm_num
    rw [h₃₂]
    <;> ring
  
  have h₄ : Real.log 9 = 2 * Real.log 3 := by
    have h₄₁ : Real.log 9 = Real.log (3 ^ 2) := by norm_num
    rw [h₄₁]
    have h₄₂ : Real.log (3 ^ 2) = 2 * Real.log 3 := by
      rw [Real.log_pow] <;> norm_num
    rw [h₄₂]
    <;> ring
  
  have h₅ : Real.logb 5 3 * Real.logb 9 25 = (Real.log 3 / Real.log 5) * (Real.log 25 / Real.log 9) := by
    rw [h₁, h₂]
    <;> ring
  
  have h₆ : (Real.log 3 / Real.log 5) * (Real.log 25 / Real.log 9) = (Real.log 3 / Real.log 5) * (2 * Real.log 5 / (2 * Real.log 3)) := by
    rw [h₃, h₄]
    <;> ring_nf
    <;> field_simp
    <;> ring_nf
  
  have h₇ : (Real.log 3 / Real.log 5) * (2 * Real.log 5 / (2 * Real.log 3)) = 1 := by
    have h₇₁ : Real.log 3 ≠ 0 := by
      have h₇₁₁ : Real.log 3 > 0 := Real.log_pos (by norm_num)
      linarith
    have h₇₂ : Real.log 5 ≠ 0 := by
      have h₇₂₁ : Real.log 5 > 0 := Real.log_pos (by norm_num)
      linarith
    field_simp [h₇₁, h₇₂]
    <;> ring_nf
    <;> field_simp [h₇₁, h₇₂]
    <;> ring_nf
    <;> linarith [Real.log_pos (by norm_num : (1 : ℝ) < 3), Real.log_pos (by norm_num : (1 : ℝ) < 5)]
  
  have h₈ : Real.logb 5 3 * Real.logb 9 25 = 1 := by
    calc
      Real.logb 5 3 * Real.logb 9 25 = (Real.log 3 / Real.log 5) * (Real.log 25 / Real.log 9) := by rw [h₅]
      _ = (Real.log 3 / Real.log 5) * (2 * Real.log 5 / (2 * Real.log 3)) := by rw [h₆]
      _ = 1 := by rw [h₇]
  
  exact h₈

theorem h_term2_amc12a_2021_p14 (k : ℕ) (hk : (1 : ℕ) ≤ k) :
    Real.logb (9 ^ k) (25 ^ k) = Real.logb 9 25 := by
  have h_main : Real.logb (9 ^ k) (25 ^ k) = Real.logb 9 25 := by
    have h₁ : (k : ℝ) ≠ 0 := by
      norm_cast
      <;>
      (try omega) <;>
      (try linarith)
      <;>
      (try
        {
          cases k with
          | zero => contradiction
          | succ k' => simp_all
        })
    -- Expand the logarithm base change formula for (9^k) and (25^k)
    have h₂ : Real.logb (9 ^ k) (25 ^ k) = (Real.log ((25 : ℝ) ^ k) / Real.log ((9 : ℝ) ^ k)) := by
      rw [Real.logb]
      <;>
      simp [h₁]
      <;>
      norm_cast
    rw [h₂]
    -- Apply the logarithm power rule
    have h₃ : Real.log ((25 : ℝ) ^ k) = (k : ℝ) * Real.log 25 := by
      rw [Real.log_pow]
      <;>
      norm_cast
      <;>
      field_simp
      <;>
      ring
    have h₄ : Real.log ((9 : ℝ) ^ k) = (k : ℝ) * Real.log 9 := by
      rw [Real.log_pow]
      <;>
      norm_cast
      <;>
      field_simp
      <;>
      ring
    rw [h₃, h₄]
    -- Cancel k in the numerator and denominator
    have h₅ : ((k : ℝ) * Real.log 25) / ((k : ℝ) * Real.log 9) = Real.log 25 / Real.log 9 := by
      have h₅₁ : (k : ℝ) ≠ 0 := by
        norm_cast
        <;>
        (try omega) <;>
        (try linarith)
        <;>
        (try
          {
            cases k with
            | zero => contradiction
            | succ k' => simp_all
          })
      field_simp [h₅₁]
      <;>
      ring
      <;>
      field_simp [h₅₁]
      <;>
      ring
    rw [h₅]
    -- Recognize that log 25 / log 9 is logb 9 25
    have h₆ : Real.logb 9 25 = Real.log 25 / Real.log 9 := by
      rw [Real.logb]
      <;>
      simp
      <;>
      norm_num
    rw [h₆]
    <;>
    simp_all
    <;>
    field_simp
    <;>
    ring
  
  exact h_main

theorem h_numeric_h_sum1_amc12a_2021_p14 :
    (∑ k in Finset.Icc (1 : ℕ) 20, (k : ℝ)) = (210 : ℝ) := by
  norm_num [Finset.sum_Icc_succ_top]
  <;> rfl

theorem h_sum_eq_h_sum1_amc12a_2021_p14
    (h_rewrite :
      ∀ k ∈ Finset.Icc (1 : ℕ) 20,
        Real.logb (5 ^ k) (3 ^ k ^ 2) = (k : ℝ) * Real.logb 5 3) :
    (∑ k in Finset.Icc (1 : ℕ) 20, Real.logb (5 ^ k) (3 ^ k ^ 2)) =
      ∑ k in Finset.Icc (1 : ℕ) 20, (k : ℝ) * Real.logb 5 3 := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [h_rewrite k hk]
  <;>
  simp_all [Finset.mem_Icc]
  <;>
  norm_cast
  <;>
  ring_nf
  <;>
  norm_num
  <;>
  linarith

theorem h_rewrite_h_sum1_amc12a_2021_p14
    (h_term1 :
      ∀ k : ℕ, (1 : ℕ) ≤ k → Real.logb (5 ^ k) (3 ^ k ^ 2) = (k : ℝ) * Real.logb 5 3) :
    ∀ k ∈ Finset.Icc (1 : ℕ) 20,
      Real.logb (5 ^ k) (3 ^ k ^ 2) = (k : ℝ) * Real.logb 5 3 := by
  intro k hk
  have h₁ : 1 ≤ k := by
    simp [Finset.mem_Icc] at hk
    linarith
  have h₂ : Real.logb (5 ^ k) (3 ^ k ^ 2) = (k : ℝ) * Real.logb 5 3 := by
    have h₃ : Real.logb (5 ^ k) (3 ^ k ^ 2) = (k : ℝ) * Real.logb 5 3 := by
      -- Use the given hypothesis to directly obtain the result
      have h₄ : (1 : ℕ) ≤ k := by simpa using h₁
      have h₅ : Real.logb (5 ^ k) (3 ^ k ^ 2) = (k : ℝ) * Real.logb 5 3 := h_term1 k h₄
      exact h₅
    exact h₃
  exact h₂

theorem h_factor_h_sum1_amc12a_2021_p14
    (h_sum_eq :
      (∑ k in Finset.Icc (1 : ℕ) 20, Real.logb (5 ^ k) (3 ^ k ^ 2)) =
        ∑ k in Finset.Icc (1 : ℕ) 20, (k : ℝ) * Real.logb 5 3) :
    (∑ k in Finset.Icc (1 : ℕ) 20, (k : ℝ) * Real.logb 5 3) =
      (Real.logb 5 3) * ∑ k in Finset.Icc (1 : ℕ) 20, (k : ℝ) := by
  have h_main : (∑ k in Finset.Icc (1 : ℕ) 20, (k : ℝ) * Real.logb 5 3) = (Real.logb 5 3) * ∑ k in Finset.Icc (1 : ℕ) 20, (k : ℝ) := by
    have h₁ : (∑ k in Finset.Icc (1 : ℕ) 20, (k : ℝ) * Real.logb 5 3) = ∑ k in Finset.Icc (1 : ℕ) 20, (Real.logb 5 3) * (k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring_nf
      <;>
      simp_all [Finset.mem_Icc]
      <;>
      norm_num
      <;>
      linarith
    rw [h₁]
    -- Use the property of sums to factor out the constant (Real.logb 5 3)
    have h₂ : ∑ k in Finset.Icc (1 : ℕ) 20, (Real.logb 5 3) * (k : ℝ) = (Real.logb 5 3) * ∑ k in Finset.Icc (1 : ℕ) 20, (k : ℝ) := by
      rw [Finset.mul_sum]
    rw [h₂]
  
  apply h_main

theorem h_sum1_amc12a_2021_p14
    (h_term1 :
      ∀ k : ℕ, (1 : ℕ) ≤ k → Real.logb (5 ^ k) (3 ^ k ^ 2) = (k : ℝ) * Real.logb 5 3) :
    (∑ k in Finset.Icc 1 20, Real.logb (5 ^ k) (3 ^ k ^ 2)) =
      (210 : ℝ) * Real.logb 5 3 := by
  have h_rewrite :
      ∀ k ∈ Finset.Icc (1 : ℕ) 20,
        Real.logb (5 ^ k) (3 ^ k ^ 2) = (k : ℝ) * Real.logb 5 3 := by
    exact h_rewrite_h_sum1_amc12a_2021_p14 h_term1
  have h_sum_eq :
      (∑ k in Finset.Icc (1 : ℕ) 20, Real.logb (5 ^ k) (3 ^ k ^ 2)) =
        ∑ k in Finset.Icc (1 : ℕ) 20, (k : ℝ) * Real.logb 5 3 := by
    exact h_sum_eq_h_sum1_amc12a_2021_p14 h_rewrite
  have h_factor :
      (∑ k in Finset.Icc (1 : ℕ) 20, (k : ℝ) * Real.logb 5 3) =
        (Real.logb 5 3) * ∑ k in Finset.Icc (1 : ℕ) 20, (k : ℝ) := by
    exact h_factor_h_sum1_amc12a_2021_p14 h_sum_eq
  have h_numeric :
      (∑ k in Finset.Icc (1 : ℕ) 20, (k : ℝ)) = (210 : ℝ) := by
    exact h_numeric_h_sum1_amc12a_2021_p14
  calc
    (∑ k in Finset.Icc 1 20, Real.logb (5 ^ k) (3 ^ k ^ 2))
        = ∑ k in Finset.Icc (1 : ℕ) 20, Real.logb (5 ^ k) (3 ^ k ^ 2) := by
          simpa
    _ = ∑ k in Finset.Icc (1 : ℕ) 20, (k : ℝ) * Real.logb 5 3 := by
          simpa using h_sum_eq
    _ = (Real.logb 5 3) * ∑ k in Finset.Icc (1 : ℕ) 20, (k : ℝ) := by
          simpa using h_factor
    _ = (Real.logb 5 3) * (210 : ℝ) := by
          simpa [h_numeric]
    _ = (210 : ℝ) * Real.logb 5 3 := by
          ring

theorem amc12a_2021_p14 :
    ((∑ k in Finset.Icc 1 20, Real.logb (5 ^ k) (3 ^ k ^ 2)) *
        ∑ k in Finset.Icc 1 100, Real.logb (9 ^ k) (25 ^ k)) = 21000 := by
  have h_term1 (k : ℕ) (hk : (1 : ℕ) ≤ k) :
      Real.logb (5 ^ k) (3 ^ k ^ 2) = (k : ℝ) * Real.logb 5 3 := by
    exact h_term1_amc12a_2021_p14 k hk
  have h_term2 (k : ℕ) (hk : (1 : ℕ) ≤ k) :
      Real.logb (9 ^ k) (25 ^ k) = Real.logb 9 25 := by
    exact h_term2_amc12a_2021_p14 k hk
  have h_sum1 :
      (∑ k in Finset.Icc 1 20, Real.logb (5 ^ k) (3 ^ k ^ 2)) =
        (210 : ℝ) * Real.logb 5 3 := by
    exact
      h_sum1_amc12a_2021_p14
        (by
          intro k hk
          exact h_term1_amc12a_2021_p14 k hk)
  have h_sum2 :
      (∑ k in Finset.Icc 1 100, Real.logb (9 ^ k) (25 ^ k)) =
        (100 : ℝ) * Real.logb 9 25 := by
    exact
      h_sum2_amc12a_2021_p14
        (by
          intro k hk
          exact h_term2_amc12a_2021_p14 k hk)
  have h_CD : Real.logb 5 3 * Real.logb 9 25 = (1 : ℝ) := by
    exact h_CD_amc12a_2021_p14
  calc
    ((∑ k in Finset.Icc 1 20, Real.logb (5 ^ k) (3 ^ k ^ 2)) *
        ∑ k in Finset.Icc 1 100, Real.logb (9 ^ k) (25 ^ k))
        = ((210 : ℝ) * Real.logb 5 3) * ((100 : ℝ) * Real.logb 9 25) := by
          simpa [h_sum1, h_sum2]
    _ = (210 * 100 : ℝ) * (Real.logb 5 3 * Real.logb 9 25) := by
          ring
    _ = (210 * 100 : ℝ) * 1 := by
          simpa [h_CD]
    _ = (21000 : ℝ) := by
          norm_num

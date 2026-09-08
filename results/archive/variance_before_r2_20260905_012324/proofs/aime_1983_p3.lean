import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem aime_1983_p3 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 2 + (18 * x + 30) - 2 * Real.sqrt (x ^ 2 + (18 * x + 45)))
    (h₁ : Fintype (f ⁻¹' {0})) : (∏ x in (f ⁻¹' {0}).toFinset, x) = 20 := by
  have h_main : (f ⁻¹' {0}).toFinset = {(-9 + Real.sqrt 61), (-9 - Real.sqrt 61)} := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · -- Prove the forward direction: if x is in the preimage, then x is either -9 + sqrt(61) or -9 - sqrt(61)
      intro hx
      have h₂ : f x = 0 := by simpa using hx
      have h₃ : x ^ 2 + (18 * x + 30) - 2 * Real.sqrt (x ^ 2 + (18 * x + 45)) = 0 := by
        rw [h₀] at h₂
        exact h₂
      have h₄ : x ^ 2 + 18 * x + 45 ≥ 0 ∨ x ^ 2 + 18 * x + 45 < 0 := by
        by_cases h : x ^ 2 + 18 * x + 45 ≥ 0
        · exact Or.inl h
        · exact Or.inr (by linarith)
      cases h₄ with
      | inl h₄ =>
        -- Case: x² + 18x + 45 ≥ 0
        have h₅ : Real.sqrt (x ^ 2 + (18 * x + 45)) = Real.sqrt (x ^ 2 + 18 * x + 45) := by ring_nf
        have h₆ : Real.sqrt (x ^ 2 + (18 * x + 45)) ≥ 0 := Real.sqrt_nonneg _
        have h₇ : x ^ 2 + (18 * x + 30) - 2 * Real.sqrt (x ^ 2 + (18 * x + 45)) = 0 := h₃
        have h₈ : x ^ 2 + 18 * x + 45 - 15 - 2 * Real.sqrt (x ^ 2 + 18 * x + 45) = 0 := by
          ring_nf at h₇ ⊢
          <;> linarith
        have h₉ : Real.sqrt (x ^ 2 + 18 * x + 45) = 5 := by
          have h₉₁ : Real.sqrt (x ^ 2 + 18 * x + 45) ≥ 0 := Real.sqrt_nonneg _
          have h₉₂ : (Real.sqrt (x ^ 2 + 18 * x + 45)) ^ 2 = x ^ 2 + 18 * x + 45 := by
            rw [Real.sq_sqrt] <;> linarith
          nlinarith [sq_nonneg (Real.sqrt (x ^ 2 + 18 * x + 45) - 5)]
        have h₁₀ : x ^ 2 + 18 * x + 45 = 25 := by
          have h₁₀₁ : Real.sqrt (x ^ 2 + 18 * x + 45) = 5 := h₉
          have h₁₀₂ : (Real.sqrt (x ^ 2 + 18 * x + 45)) ^ 2 = 25 := by
            rw [h₁₀₁]
            <;> norm_num
          have h₁₀₃ : (Real.sqrt (x ^ 2 + 18 * x + 45)) ^ 2 = x ^ 2 + 18 * x + 45 := by
            rw [Real.sq_sqrt] <;> linarith
          linarith
        have h₁₁ : x = -9 + Real.sqrt 61 ∨ x = -9 - Real.sqrt 61 := by
          have h₁₁₁ : x ^ 2 + 18 * x + 20 = 0 := by
            nlinarith
          have h₁₁₂ : x = -9 + Real.sqrt 61 ∨ x = -9 - Real.sqrt 61 := by
            have h₁₁₃ : x = -9 + Real.sqrt 61 ∨ x = -9 - Real.sqrt 61 := by
              apply or_iff_not_imp_left.mpr
              intro h₁₁₄
              apply mul_left_cancel₀ (sub_ne_zero.mpr h₁₁₄)
              nlinarith [Real.sq_sqrt (show 0 ≤ 61 by norm_num), Real.sqrt_nonneg 61]
            exact h₁₁₃
          exact h₁₁₂
        cases h₁₁ with
        | inl h₁₁ =>
          simp [h₁₁]
          <;>
          (try norm_num) <;>
          (try ring_nf) <;>
          (try field_simp) <;>
          (try nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show 0 ≤ 61 by norm_num)])
        | inr h₁₁ =>
          simp [h₁₁]
          <;>
          (try norm_num) <;>
          (try ring_nf) <;>
          (try field_simp) <;>
          (try nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show 0 ≤ 61 by norm_num)])
      | inr h₄ =>
        -- Case: x² + 18x + 45 < 0
        have h₅ : Real.sqrt (x ^ 2 + (18 * x + 45)) = 0 := by
          have h₅₁ : x ^ 2 + (18 * x + 45) < 0 := by linarith
          rw [Real.sqrt_eq_zero_of_nonpos] <;> linarith
        have h₆ : x ^ 2 + (18 * x + 30) - 2 * Real.sqrt (x ^ 2 + (18 * x + 45)) = 0 := h₃
        rw [h₅] at h₆
        have h₇ : x ^ 2 + (18 * x + 30) = 0 := by linarith
        have h₈ : x ^ 2 + 18 * x + 45 < 0 := by linarith
        have h₉ : x ^ 2 + 18 * x + 30 = 0 := by linarith
        have h₁₀ : x ^ 2 + 18 * x + 45 = 15 := by linarith
        linarith
    · -- Prove the reverse direction: if x is either -9 + sqrt(61) or -9 - sqrt(61), then x is in the preimage
      intro hx
      cases hx with
      | inl hx =>
        have h₂ : x = -9 + Real.sqrt 61 := by simpa using hx
        rw [h₂]
        have h₃ : f (-9 + Real.sqrt 61) = 0 := by
          have h₄ : f (-9 + Real.sqrt 61) = (-9 + Real.sqrt 61) ^ 2 + (18 * (-9 + Real.sqrt 61) + 30) - 2 * Real.sqrt ((-9 + Real.sqrt 61) ^ 2 + (18 * (-9 + Real.sqrt 61) + 45)) := by
            rw [h₀]
          rw [h₄]
          have h₅ : Real.sqrt ((-9 + Real.sqrt 61) ^ 2 + (18 * (-9 + Real.sqrt 61) + 45)) = 5 := by
            have h₅₁ : (-9 + Real.sqrt 61) ^ 2 + (18 * (-9 + Real.sqrt 61) + 45) = 25 := by
              nlinarith [Real.sq_sqrt (show 0 ≤ 61 by norm_num), Real.sqrt_nonneg 61]
            rw [h₅₁]
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h₅]
          nlinarith [Real.sq_sqrt (show 0 ≤ 61 by norm_num), Real.sqrt_nonneg 61]
        simpa using h₃
      | inr hx =>
        have h₂ : x = -9 - Real.sqrt 61 := by simpa using hx
        rw [h₂]
        have h₃ : f (-9 - Real.sqrt 61) = 0 := by
          have h₄ : f (-9 - Real.sqrt 61) = (-9 - Real.sqrt 61) ^ 2 + (18 * (-9 - Real.sqrt 61) + 30) - 2 * Real.sqrt ((-9 - Real.sqrt 61) ^ 2 + (18 * (-9 - Real.sqrt 61) + 45)) := by
            rw [h₀]
          rw [h₄]
          have h₅ : Real.sqrt ((-9 - Real.sqrt 61) ^ 2 + (18 * (-9 - Real.sqrt 61) + 45)) = 5 := by
            have h₅₁ : (-9 - Real.sqrt 61) ^ 2 + (18 * (-9 - Real.sqrt 61) + 45) = 25 := by
              nlinarith [Real.sq_sqrt (show 0 ≤ 61 by norm_num), Real.sqrt_nonneg 61]
            rw [h₅₁]
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h₅]
          nlinarith [Real.sq_sqrt (show 0 ≤ 61 by norm_num), Real.sqrt_nonneg 61]
        simpa using h₃
  
  have h_product : (∏ x in (f ⁻¹' {0}).toFinset, x) = 20 := by
    rw [h_main]
    have h₂ : Real.sqrt 61 ≥ 0 := Real.sqrt_nonneg _
    have h₃ : (-9 + Real.sqrt 61) ≠ (-9 - Real.sqrt 61) := by
      intro h
      have h₄ : Real.sqrt 61 = 0 := by linarith
      have h₅ : Real.sqrt 61 > 0 := Real.sqrt_pos.mpr (by norm_num)
      linarith
    -- Calculate the product of the two roots
    have h₄ : (∏ x in ({(-9 + Real.sqrt 61), (-9 - Real.sqrt 61)} : Finset ℝ), x) = 20 := by
      have h₅ : (∏ x in ({(-9 + Real.sqrt 61), (-9 - Real.sqrt 61)} : Finset ℝ), x) = (-9 + Real.sqrt 61) * (-9 - Real.sqrt 61) := by
        -- Since the two elements are distinct, the product is simply their multiplication
        simp [h₃, Finset.prod_pair (show (-9 + Real.sqrt 61 : ℝ) ≠ (-9 - Real.sqrt 61 : ℝ) by
          intro h
          have h₆ : Real.sqrt 61 = 0 := by linarith
          have h₇ : Real.sqrt 61 > 0 := Real.sqrt_pos.mpr (by norm_num)
          linarith)]
        <;> ring_nf
        <;> norm_num
        <;> linarith [Real.sqrt_nonneg 61]
      rw [h₅]
      -- Calculate the product (-9 + sqrt(61)) * (-9 - sqrt(61))
      have h₆ : (-9 + Real.sqrt 61) * (-9 - Real.sqrt 61) = 20 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ 61 by norm_num)]
      rw [h₆]
    -- Use the calculated product to conclude the proof
    simpa using h₄
  
  apply h_product

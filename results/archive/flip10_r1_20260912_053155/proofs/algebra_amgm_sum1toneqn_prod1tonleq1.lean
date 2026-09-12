import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem algebra_amgm_sum1toneqn_prod1tonleq1 (a : ℕ → NNReal) (n : ℕ)
    (h₀ : (∑ x in Finset.range n, a x) = n) : (∏ x in Finset.range n, a x) ≤ 1 := by
  have h₁ : (∑ x in Finset.range n, (a x : ℝ)) = n := by
    have h₁₁ : (∑ x in Finset.range n, (a x : ℝ)) = (∑ x in Finset.range n, a x : ℝ) := by simp [NNReal.coe_sum]
    rw [h₁₁]
    have h₁₂ : (∑ x in Finset.range n, a x : ℝ) = (n : ℝ) := by
      norm_cast
      <;> simp_all [h₀]
      <;> simp_all [Finset.sum_const, Finset.card_range]
      <;> ring_nf at *
      <;> norm_num at *
      <;> linarith
    rw [h₁₂]
    <;> norm_cast
  
  have h₂ : ∀ (i : ℕ), (a i : ℝ) ≤ Real.exp ((a i : ℝ) - 1) := by
    intro i
    have h₂₁ : (1 : ℝ) + ((a i : ℝ) - 1) ≤ Real.exp ((a i : ℝ) - 1) := by
      linarith [Real.add_one_le_exp ((a i : ℝ) - 1)]
    linarith
  
  have h₃ : (∏ x in Finset.range n, (a x : ℝ)) ≤ 1 := by
    have h₃₁ : (∏ x in Finset.range n, (a x : ℝ)) ≤ ∏ x in Finset.range n, Real.exp ((a x : ℝ) - 1) := by
      apply Finset.prod_le_prod
      · intro i _
        exact by
          have h₃₁₁ : 0 ≤ (a i : ℝ) := by exact mod_cast (a i).prop
          linarith
      · intro i _
        exact h₂ i
    have h₃₂ : ∏ x in Finset.range n, Real.exp ((a x : ℝ) - 1) = Real.exp (∑ x in Finset.range n, ((a x : ℝ) - 1)) := by
      rw [Real.exp_sum]
      <;> simp [Real.exp_sub]
      <;> field_simp [Real.exp_neg]
      <;> ring_nf
      <;> simp_all [Real.exp_add, Real.exp_sub]
      <;> field_simp [Real.exp_neg]
      <;> ring_nf
    have h₃₃ : Real.exp (∑ x in Finset.range n, ((a x : ℝ) - 1)) = 1 := by
      have h₃₃₁ : (∑ x in Finset.range n, ((a x : ℝ) - 1)) = 0 := by
        calc
          (∑ x in Finset.range n, ((a x : ℝ) - 1)) = (∑ x in Finset.range n, (a x : ℝ)) - ∑ x in Finset.range n, (1 : ℝ) := by
            rw [Finset.sum_sub_distrib]
          _ = (n : ℝ) - ∑ x in Finset.range n, (1 : ℝ) := by rw [h₁]
          _ = (n : ℝ) - (n : ℝ) := by
            simp [Finset.sum_const, Finset.card_range]
            <;> ring_nf
          _ = 0 := by ring
      rw [h₃₃₁]
      norm_num [Real.exp_zero]
    calc
      (∏ x in Finset.range n, (a x : ℝ)) ≤ ∏ x in Finset.range n, Real.exp ((a x : ℝ) - 1) := h₃₁
      _ = Real.exp (∑ x in Finset.range n, ((a x : ℝ) - 1)) := by rw [h₃₂]
      _ = 1 := by rw [h₃₃]
  
  have h₄ : (∏ x in Finset.range n, a x) ≤ 1 := by
    have h₄₁ : (∏ x in Finset.range n, a x : NNReal) ≤ 1 := by
      -- Use the fact that the product of the real numbers is less than or equal to 1 to deduce the same for NNReal
      have h₄₂ : (∏ x in Finset.range n, (a x : ℝ)) ≤ 1 := h₃
      have h₄₃ : (∏ x in Finset.range n, (a x : ℝ)) = (∏ x in Finset.range n, a x : ℝ) := by
        simp [NNReal.coe_prod]
      rw [h₄₃] at h₄₂
      -- Use the fact that the coercion from NNReal to Real is monotone to deduce the inequality in NNReal
      exact mod_cast h₄₂
    exact h₄₁
  
  exact h₄

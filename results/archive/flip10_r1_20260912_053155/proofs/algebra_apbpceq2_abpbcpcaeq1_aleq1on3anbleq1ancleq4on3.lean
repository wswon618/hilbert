import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem hbc_sum_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ)
    (h₀ : a ≤ b ∧ b ≤ c) (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1) :
    b + c = (2 : ℝ) - a := by
  have h₃ : b + c = 2 - a := by
    have h₄ : a + b + c = 2 := h₁
    -- Subtract a from both sides to get b + c = 2 - a
    linarith
  -- The result follows directly from the above step
  linarith

theorem hΔ_def_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ)
    (h₀ : a ≤ b ∧ b ≤ c) (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1)
    (hbc_sum : b + c = (2 : ℝ) - a) (hbc_prod : b * c = (a - 1) ^ 2) :
    ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 = a * (4 - 3 * a) := by
  have h₃ : ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 = a * (4 - 3 * a) := by
    have h₄ : ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 = (4 - 4 * a + a ^ 2) - 4 * (a ^ 2 - 2 * a + 1) := by
      ring_nf
      <;>
      nlinarith
    rw [h₄]
    have h₅ : (4 - 4 * a + a ^ 2) - 4 * (a ^ 2 - 2 * a + 1) = a * (4 - 3 * a) := by
      ring_nf at *
      <;>
      nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 2 / 3)]
    rw [h₅]
  exact h₃

theorem hc_le_four_thirds_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ)
    (h₀ : a ≤ b ∧ b ≤ c) (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1)
    (hbc_sum : b + c = (2 : ℝ) - a) (hbc_prod : b * c = (a - 1) ^ 2)
    (hΔ_def : ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 = a * (4 - 3 * a))
    (hΔ_nonneg : 0 ≤ a * (4 - 3 * a)) (ha_nonneg : (0 : ℝ) ≤ a)
    (ha_le_one_third : a ≤ 1 / 3) (hb_le_one : b ≤ 1) (hb_ge_one_third : (1 / 3 : ℝ) ≤ b)
    (hc_ge_one : (1 : ℝ) ≤ c) :
    c ≤ 4 / 3 := by
  have h₃ : c ≤ 4 / 3 := by
    nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 1), sq_nonneg (c - 4 / 3),
      mul_nonneg ha_nonneg (sub_nonneg.mpr ha_le_one_third),
      mul_nonneg (sub_nonneg.mpr ha_le_one_third) (sub_nonneg.mpr hb_le_one),
      mul_nonneg (sub_nonneg.mpr ha_le_one_third) (sub_nonneg.mpr hc_ge_one)]
  exact h₃

theorem hbc_prod_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ)
    (h₀ : a ≤ b ∧ b ≤ c) (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1)
    (hbc_sum : b + c = (2 : ℝ) - a) :
    b * c = (a - 1) ^ 2 := by
  have h₃ : b * c = (a - 1) ^ 2 := by
    have h₄ : (b + c) ^ 2 = (2 - a) ^ 2 := by
      rw [hbc_sum]
      <;> ring
    have h₅ : (b + c) ^ 2 = b ^ 2 + 2 * (b * c) + c ^ 2 := by
      ring
    have h₆ : (2 - a) ^ 2 = 4 - 4 * a + a ^ 2 := by
      ring
    have h₇ : b ^ 2 + 2 * (b * c) + c ^ 2 = 4 - 4 * a + a ^ 2 := by
      linarith
    have h₈ : a * b + b * c + c * a = 1 := h₂
    have h₉ : a + b + c = 2 := h₁
    have h₁₀ : b * c = (a - 1) ^ 2 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - c), sq_nonneg (a + b + c)]
    exact h₁₀
  exact h₃

theorem ha_le_one_third_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ)
    (h₀ : a ≤ b ∧ b ≤ c) (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1)
    (hbc_sum : b + c = (2 : ℝ) - a) (hbc_prod : b * c = (a - 1) ^ 2)
    (hΔ_def : ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 = a * (4 - 3 * a))
    (hΔ_nonneg : 0 ≤ a * (4 - 3 * a)) (ha_nonneg : (0 : ℝ) ≤ a) :
    a ≤ 1 / 3 := by
  have h₃ : a ≤ 1 / 3 := by
    by_contra! h
    have h₄ : a > 1 / 3 := by linarith
    have h₅ : a * (4 - 3 * a) < 1 := by
      nlinarith [sq_nonneg (a - 4 / 3)]
    have h₆ : ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 < 1 := by
      linarith
    have h₇ : (b - c) ^ 2 ≥ 0 := by nlinarith
    have h₈ : (b - c) ^ 2 = ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 := by
      have h₈₁ : (b - c) ^ 2 = (b + c) ^ 2 - 4 * (b * c) := by ring
      rw [h₈₁]
      rw [hbc_sum, hbc_prod]
      <;> ring_nf
      <;> nlinarith
    have h₉ : (b - c) ^ 2 < 1 := by linarith
    have h₁₀ : b ≤ c := h₀.2
    have h₁₁ : b - c ≤ 0 := by linarith
    have h₁₂ : (b - c) ^ 2 < 1 := by linarith
    have h₁₃ : b - c > -1 := by
      nlinarith [sq_nonneg (b - c + 1)]
    have h₁₄ : a + b + c = 2 := h₁
    have h₁₅ : a * b + b * c + c * a = 1 := h₂
    nlinarith [sq_nonneg (a - 1 / 3)]
  exact h₃

theorem hb_le_one_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ)
    (h₀ : a ≤ b ∧ b ≤ c) (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1)
    (hbc_sum : b + c = (2 : ℝ) - a) (hbc_prod : b * c = (a - 1) ^ 2)
    (hΔ_def : ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 = a * (4 - 3 * a))
    (hΔ_nonneg : 0 ≤ a * (4 - 3 * a)) (ha_nonneg : (0 : ℝ) ≤ a)
    (ha_le_one_third : a ≤ 1 / 3) :
    b ≤ 1 := by
  have h₃ : b ≤ 1 := by
    by_contra h
    have h₄ : b > 1 := by linarith
    have h₅ : c ≥ b := by linarith
    have h₆ : c > 1 := by linarith
    have h₇ : a + b + c = 2 := h₁
    have h₈ : a ≤ 1 / 3 := ha_le_one_third
    have h₉ : a ≥ 0 := ha_nonneg
    have h₁₀ : b + c = 2 - a := by linarith
    have h₁₁ : b * c = (a - 1) ^ 2 := hbc_prod
    have h₁₂ : (2 - a) ^ 2 - 4 * (a - 1) ^ 2 = a * (4 - 3 * a) := hΔ_def
    have h₁₃ : 0 ≤ a * (4 - 3 * a) := hΔ_nonneg
    -- Use the fact that b > 1 and c ≥ b to derive a contradiction
    have h₁₄ : a < 2 / 3 := by
      nlinarith [sq_nonneg (b - c)]
    have h₁₅ : (a - 1) ^ 2 ≥ 0 := by nlinarith
    have h₁₆ : b * c > 1 := by
      nlinarith [sq_nonneg (b - c)]
    have h₁₇ : (a - 1) ^ 2 < 1 := by
      nlinarith [sq_nonneg (a - 1)]
    nlinarith [sq_nonneg (b - c)]
  exact h₃

theorem ha_nonneg_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ)
    (h₀ : a ≤ b ∧ b ≤ c) (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1)
    (hbc_sum : b + c = (2 : ℝ) - a) (hbc_prod : b * c = (a - 1) ^ 2)
    (hΔ_def : ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 = a * (4 - 3 * a))
    (hΔ_nonneg : 0 ≤ a * (4 - 3 * a)) :
    (0 : ℝ) ≤ a := by
  have h_main : 0 ≤ a := by
    by_contra h
    -- Assume a < 0 and derive a contradiction
    have h₃ : a < 0 := by linarith
    have h₄ : 4 - 3 * a > 0 := by
      nlinarith
    have h₅ : a * (4 - 3 * a) < 0 := by
      nlinarith
    -- Contradiction with hΔ_nonneg
    linarith
  exact h_main

theorem hΔ_nonneg_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ)
    (h₀ : a ≤ b ∧ b ≤ c) (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1)
    (hbc_sum : b + c = (2 : ℝ) - a) (hbc_prod : b * c = (a - 1) ^ 2)
    (hΔ_def : ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 = a * (4 - 3 * a)) :
    0 ≤ a * (4 - 3 * a) := by
  have h_sq_nonneg : 0 ≤ (b - c) ^ 2 := by
    -- The square of any real number is non-negative.
    nlinarith [sq_nonneg (b - c)]
  
  have h_discriminant_nonneg : 0 ≤ ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 := by
    have h₃ : (b - c) ^ 2 = ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 := by
      calc
        (b - c) ^ 2 = (b + c) ^ 2 - 4 * (b * c) := by
          ring
        _ = ((2 : ℝ) - a) ^ 2 - 4 * (b * c) := by
          rw [hbc_sum]
          <;> ring
        _ = ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 := by
          rw [hbc_prod]
          <;> ring
    -- Using the fact that (b - c)^2 is non-negative and the above equality, we can conclude the discriminant is non-negative.
    linarith [h_sq_nonneg]
  
  have h_main : 0 ≤ a * (4 - 3 * a) := by
    have h₃ : 0 ≤ ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 := h_discriminant_nonneg
    have h₄ : ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 = a * (4 - 3 * a) := hΔ_def
    linarith
  
  exact h_main

theorem hb_ge_one_third_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ)
    (h₀ : a ≤ b ∧ b ≤ c) (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1)
    (hbc_sum : b + c = (2 : ℝ) - a) (hbc_prod : b * c = (a - 1) ^ 2)
    (hΔ_def : ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 = a * (4 - 3 * a))
    (hΔ_nonneg : 0 ≤ a * (4 - 3 * a)) (ha_nonneg : (0 : ℝ) ≤ a)
    (ha_le_one_third : a ≤ 1 / 3) (hb_le_one : b ≤ 1) :
    (1 / 3 : ℝ) ≤ b := by
  have h_main : (1 / 3 : ℝ) ≤ b := by
    by_contra h
    have h₃ : b < 1 / 3 := by linarith
    have h₄ : a < 1 / 3 := by
      linarith [h₀.1]
    -- Define the quadratic function in b
    have h₅ : b ^ 2 + (a - 2) * b + (a ^ 2 - 2 * a + 1) = 0 := by
      have h₅₁ : c = 2 - a - b := by linarith
      have h₅₂ : b * c = (a - 1) ^ 2 := hbc_prod
      rw [h₅₁] at h₅₂
      ring_nf at h₅₂ ⊢
      nlinarith
    -- Show that f(1/3) > 0 when a < 1/3
    have h₆ : (1 / 3 : ℝ) ^ 2 + (a - 2) * (1 / 3 : ℝ) + (a ^ 2 - 2 * a + 1) > 0 := by
      have h₆₁ : a < 1 / 3 := h₄
      have h₆₂ : 0 ≤ a := ha_nonneg
      nlinarith [sq_nonneg (a - 1 / 3)]
    -- Show that the quadratic is decreasing for b < 1/3
    have h₇ : b ^ 2 + (a - 2) * b + (a ^ 2 - 2 * a + 1) > (1 / 3 : ℝ) ^ 2 + (a - 2) * (1 / 3 : ℝ) + (a ^ 2 - 2 * a + 1) := by
      have h₇₁ : a < 1 / 3 := h₄
      have h₇₂ : b < 1 / 3 := h₃
      have h₇₃ : (2 - a) / 2 > 5 / 6 := by
        nlinarith
      have h₇₄ : b < (2 - a) / 2 := by
        nlinarith
      nlinarith [sq_pos_of_neg (sub_neg.mpr h₇₂), sq_nonneg (b - 1 / 3)]
    -- Derive a contradiction
    linarith [h₅]
  exact h_main

theorem hc_ge_one_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ)
    (h₀ : a ≤ b ∧ b ≤ c) (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1)
    (hbc_sum : b + c = (2 : ℝ) - a) (hbc_prod : b * c = (a - 1) ^ 2)
    (hΔ_def : ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 = a * (4 - 3 * a))
    (hΔ_nonneg : 0 ≤ a * (4 - 3 * a)) (ha_nonneg : (0 : ℝ) ≤ a)
    (ha_le_one_third : a ≤ 1 / 3) (hb_le_one : b ≤ 1) (hb_ge_one_third : (1 / 3 : ℝ) ≤ b) :
    (1 : ℝ) ≤ c := by
  have h_product : (c - 1) * (b - 1) = a ^ 2 - a := by
    have h₃ : (c - 1) * (b - 1) = b * c - b - c + 1 := by
      ring
    rw [h₃]
    have h₄ : b * c = (a - 1) ^ 2 := hbc_prod
    have h₅ : b + c = (2 : ℝ) - a := hbc_sum
    have h₆ : b * c - b - c + 1 = (a - 1) ^ 2 - (b + c) + 1 := by
      linarith
    rw [h₆]
    have h₇ : (a - 1) ^ 2 - (b + c) + 1 = (a - 1) ^ 2 - ((2 : ℝ) - a) + 1 := by
      rw [h₅]
    rw [h₇]
    have h₈ : (a - 1) ^ 2 - ((2 : ℝ) - a) + 1 = a ^ 2 - a := by
      ring_nf at *
      <;> nlinarith
    rw [h₈]
    <;> ring_nf
    <;> nlinarith
  
  have h_a_sq_le_a : a ^ 2 - a ≤ 0 := by
    have h₃ : a ≤ 1 := by
      nlinarith
    have h₄ : 0 ≤ a := ha_nonneg
    nlinarith [sq_nonneg (a - 1 / 2)]
  
  have h_product_nonpos : (c - 1) * (b - 1) ≤ 0 := by
    linarith
  
  have h_main : 1 ≤ c := by
    by_contra h
    have h₃ : c < 1 := by linarith
    have h₄ : b < 1 := by
      linarith [h₀.2]
    have h₅ : (c - 1) * (b - 1) > 0 := by
      have h₅₁ : c - 1 < 0 := by linarith
      have h₅₂ : b - 1 < 0 := by linarith
      nlinarith
    linarith
  
  exact h_main

theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ)
    (h₀ : a ≤ b ∧ b ≤ c) (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1) :
    0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
  have hbc_sum : b + c = (2 : ℝ) - a := by
    exact
      hbc_sum_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 a b c h₀ h₁ h₂
  have hbc_prod : b * c = (a - 1) ^ 2 := by
    exact
      hbc_prod_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 a b c h₀ h₁ h₂
        hbc_sum
  have hΔ_def :
      ((2 : ℝ) - a) ^ 2 - 4 * (a - 1) ^ 2 = a * (4 - 3 * a) := by
    exact
      hΔ_def_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 a b c h₀ h₁ h₂
        hbc_sum hbc_prod
  have hΔ_nonneg : 0 ≤ a * (4 - 3 * a) := by
    exact
      hΔ_nonneg_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 a b c h₀ h₁ h₂
        hbc_sum hbc_prod hΔ_def
  have ha_nonneg : (0 : ℝ) ≤ a := by
    exact
      ha_nonneg_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 a b c h₀ h₁ h₂
        hbc_sum hbc_prod hΔ_def hΔ_nonneg
  have ha_le_one_third : a ≤ 1 / 3 := by
    exact
      ha_le_one_third_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 a b c h₀ h₁ h₂
        hbc_sum hbc_prod hΔ_def hΔ_nonneg ha_nonneg
  have hb_le_one : b ≤ 1 := by
    exact
      hb_le_one_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 a b c h₀ h₁ h₂
        hbc_sum hbc_prod hΔ_def hΔ_nonneg ha_nonneg ha_le_one_third
  have hb_ge_one_third : (1 / 3 : ℝ) ≤ b := by
    exact
      hb_ge_one_third_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 a b c h₀ h₁ h₂
        hbc_sum hbc_prod hΔ_def hΔ_nonneg ha_nonneg ha_le_one_third hb_le_one
  have hc_ge_one : (1 : ℝ) ≤ c := by
    exact
      hc_ge_one_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 a b c h₀ h₁ h₂
        hbc_sum hbc_prod hΔ_def hΔ_nonneg ha_nonneg ha_le_one_third hb_le_one hb_ge_one_third
  have hc_le_four_thirds : c ≤ 4 / 3 := by
    exact
      hc_le_four_thirds_algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 a b c h₀ h₁ h₂
        hbc_sum hbc_prod hΔ_def hΔ_nonneg ha_nonneg ha_le_one_third hb_le_one hb_ge_one_third
        hc_ge_one
  exact
    ⟨ha_nonneg, ha_le_one_third, hb_ge_one_third, hb_le_one, hc_ge_one,
      hc_le_four_thirds⟩

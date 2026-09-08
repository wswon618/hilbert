import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem hyz_pos_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
    0 < y + z := by
  have h₁ : 0 < y := by linarith
  have h₂ : 0 < z := by linarith
  have h₃ : 0 < y + z := by linarith
  exact h₃

theorem hzx_pos_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
    0 < z + x := by
  have h₁ : 0 < x := by linarith
  have h₂ : 0 < z := by linarith
  -- Since both x and z are positive, their sum z + x is also positive.
  linarith

theorem hxy_pos_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
    0 < x + y := by
  have h₁ : 0 < x := h₀.1
  have h₂ : 0 < y := h₀.2.1
  have h₃ : 0 < z := h₀.2.2
  -- Since x and y are both positive, their sum x + y is also positive.
  have h₄ : 0 < x + y := by linarith
  exact h₄

theorem hsum_pos_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
    0 < x + y + z := by
  have h₁ : 0 < x := by linarith
  have h₂ : 0 < y := by linarith
  have h₃ : 0 < z := by linarith
  -- Since x, y, and z are all positive, their sum is also positive.
  have h₄ : 0 < x + y + z := by linarith
  exact h₄

theorem hsq_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hCauchy :
      (3 : ℝ) ≤
        Real.sqrt ((1 / (x + y) + 1 / (y + z) + 1 / (z + x))) *
        Real.sqrt (2 * (x + y + z))) :
    (9 : ℝ) ≤
      (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) *
      (2 * (x + y + z)) := by
  have h₁ : 0 < x := by linarith
  have h₂ : 0 < y := by linarith
  have h₃ : 0 < z := by linarith
  have h₄ : 0 < x + y := by linarith
  have h₅ : 0 < y + z := by linarith
  have h₆ : 0 < z + x := by linarith
  have h₇ : 0 < 1 / (x + y) + 1 / (y + z) + 1 / (z + x) := by positivity
  have h₈ : 0 < 2 * (x + y + z) := by positivity
  have h₉ : 0 < Real.sqrt ((1 / (x + y) + 1 / (y + z) + 1 / (z + x))) := by positivity
  have h₁₀ : 0 < Real.sqrt (2 * (x + y + z)) := by positivity
  have h₁₁ : (Real.sqrt ((1 / (x + y) + 1 / (y + z) + 1 / (z + x))) * Real.sqrt (2 * (x + y + z))) ^ 2 = (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) * (2 * (x + y + z)) := by
    have h₁₂ : 0 ≤ (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) := by positivity
    have h₁₃ : 0 ≤ 2 * (x + y + z) := by positivity
    have h₁₄ : 0 ≤ Real.sqrt ((1 / (x + y) + 1 / (y + z) + 1 / (z + x))) := by positivity
    have h₁₅ : 0 ≤ Real.sqrt (2 * (x + y + z)) := by positivity
    calc
      (Real.sqrt ((1 / (x + y) + 1 / (y + z) + 1 / (z + x))) * Real.sqrt (2 * (x + y + z))) ^ 2 =
          (Real.sqrt ((1 / (x + y) + 1 / (y + z) + 1 / (z + x)))) ^ 2 * (Real.sqrt (2 * (x + y + z))) ^ 2 := by
        ring_nf
        <;> field_simp [h₉.ne', h₁₀.ne']
        <;> ring_nf
      _ = (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) * (2 * (x + y + z)) := by
        rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
        <;> ring_nf
        <;> field_simp [h₉.ne', h₁₀.ne']
        <;> ring_nf
  have h₁₂ : (3 : ℝ) ^ 2 ≤ (Real.sqrt ((1 / (x + y) + 1 / (y + z) + 1 / (z + x))) * Real.sqrt (2 * (x + y + z))) ^ 2 := by
    have h₁₃ : (3 : ℝ) ≤ Real.sqrt ((1 / (x + y) + 1 / (y + z) + 1 / (z + x))) * Real.sqrt (2 * (x + y + z)) := hCauchy
    have h₁₄ : 0 ≤ Real.sqrt ((1 / (x + y) + 1 / (y + z) + 1 / (z + x))) * Real.sqrt (2 * (x + y + z)) := by positivity
    nlinarith
  have h₁₃ : (9 : ℝ) ≤ (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) * (2 * (x + y + z)) := by
    nlinarith [h₁₁, h₁₂]
  exact h₁₃

theorem hfinal_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hsum_pos : 0 < x + y + z)
    (hdiv :
      (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥
        (9 : ℝ) / (2 * (x + y + z))) :
    (9 : ℝ) / (x + y + z) ≤
      2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  have h₁ : 0 < x + y := by linarith
  have h₂ : 0 < y + z := by linarith
  have h₃ : 0 < z + x := by linarith
  have h₄ : 0 < x + y + z := by linarith
  have h₅ : 0 < 2 * (x + y + z) := by linarith
  -- Multiply both sides of the given inequality by 2 to get the desired form
  have h₆ : 2 * (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ 2 * ((9 : ℝ) / (2 * (x + y + z))) := by
    linarith
  -- Simplify the right-hand side of the inequality
  have h₇ : 2 * ((9 : ℝ) / (2 * (x + y + z))) = (9 : ℝ) / (x + y + z) := by
    field_simp
    <;> ring
    <;> field_simp
    <;> ring
  -- Substitute back into the inequality
  have h₈ : 2 * (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ (9 : ℝ) / (x + y + z) := by
    linarith
  -- Recognize that the left-hand side is the same as the target expression
  have h₉ : 2 * (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) = 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
    ring_nf
    <;> field_simp
    <;> ring_nf
  -- Substitute back to get the final inequality
  linarith

theorem hdiv_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hsum_pos : 0 < x + y + z)
    (hsq :
      (9 : ℝ) ≤
        (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) *
        (2 * (x + y + z))) :
    (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥
      (9 : ℝ) / (2 * (x + y + z)) := by
  have h_pos : 0 < 2 * (x + y + z) := by
    have h₁ : 0 < x + y + z := by linarith
    have h₂ : 0 < 2 * (x + y + z) := by positivity
    exact h₂
  
  have h_main : (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ (9 : ℝ) / (2 * (x + y + z)) := by
    have h₁ : (9 : ℝ) / (2 * (x + y + z)) ≤ (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) := by
      -- Divide both sides of the given inequality by 2*(x + y + z)
      have h₂ : 0 < 2 * (x + y + z) := h_pos
      have h₃ : (9 : ℝ) ≤ (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) * (2 * (x + y + z)) := hsq
      -- Use the division inequality to get the desired result
      have h₄ : (9 : ℝ) / (2 * (x + y + z)) ≤ (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) := by
        calc
          (9 : ℝ) / (2 * (x + y + z)) = (9 : ℝ) / (2 * (x + y + z)) := by rfl
          _ ≤ ((1 / (x + y) + 1 / (y + z) + 1 / (z + x)) * (2 * (x + y + z))) / (2 * (x + y + z)) := by
            -- Use the given inequality to bound the numerator
            gcongr
            <;> nlinarith
          _ = (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) := by
            -- Simplify the division
            field_simp [h₂.ne']
            <;> ring
            <;> field_simp [h₂.ne']
            <;> linarith
      exact h₄
    -- Use the derived inequality to conclude the proof
    linarith
  
  exact h_main

theorem hsum_nonneg_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) (hsum_pos : 0 < x + y + z) :
    0 ≤ x + y + z := by
  exact le_of_lt hsum_pos

theorem hx_pos_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) : 0 < x := by
  exact h₀.1

theorem hyz_nonneg_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) (hyz_pos : 0 < y + z) :
    0 ≤ y + z := by
  exact le_of_lt hyz_pos

theorem hzx_nonneg_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) (hzx_pos : 0 < z + x) :
    0 ≤ z + x := by
  exact le_of_lt hzx_pos

theorem hy_pos_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) : 0 < y := by
  exact h₀.2.1

theorem hxy_nonneg_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) (hxy_pos : 0 < x + y) :
    0 ≤ x + y := by
  exact le_of_lt hxy_pos

theorem hz_pos_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) : 0 < z := by
  exact h₀.2.2

theorem h_g_sq_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x) :
    (let g : Fin 3 → ℝ := fun i => match i with
        | ⟨0, _⟩ => Real.sqrt (x + y)
        | ⟨1, _⟩ => Real.sqrt (y + z)
        | ⟨2, _⟩ => Real.sqrt (z + x);
     ∑ i, (g i) ^ 2 = (2 * (x + y + z))) := by
  let g : Fin 3 → ℝ := fun i => match i with
    | ⟨0, _⟩ => Real.sqrt (x + y)
    | ⟨1, _⟩ => Real.sqrt (y + z)
    | ⟨2, _⟩ => Real.sqrt (z + x)
  have hxy_nonneg : 0 ≤ x + y := le_of_lt hxy_pos
  have hyz_nonneg : 0 ≤ y + z := le_of_lt hyz_pos
  have hzx_nonneg : 0 ≤ z + x := le_of_lt hzx_pos
  have hsum : (∑ i : Fin 3, (g i) ^ 2) = (x + y) + (y + z) + (z + x) := by
    simp [Fin.sum_univ_three, g,
      Real.sq_sqrt hxy_nonneg,
      Real.sq_sqrt hyz_nonneg,
      Real.sq_sqrt hzx_nonneg]
  calc
    (∑ i : Fin 3, (g i) ^ 2) = (x + y) + (y + z) + (z + x) := hsum
    _ = 2 * (x + y + z) := by ring

theorem hCS_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x) :
    (let f : Fin 3 → ℝ := fun i => match i with
        | ⟨0, _⟩ => 1 / Real.sqrt (x + y)
        | ⟨1, _⟩ => 1 / Real.sqrt (y + z)
        | ⟨2, _⟩ => 1 / Real.sqrt (z + x);
     let g : Fin 3 → ℝ := fun i => match i with
        | ⟨0, _⟩ => Real.sqrt (x + y)
        | ⟨1, _⟩ => Real.sqrt (y + z)
        | ⟨2, _⟩ => Real.sqrt (z + x);
     ∑ i, f i * g i ≤ Real.sqrt (∑ i, (f i) ^ 2) * Real.sqrt (∑ i, (g i) ^ 2)) := by
  classical
  let f : Fin 3 → ℝ := fun i => match i with
    | ⟨0, _⟩ => 1 / Real.sqrt (x + y)
    | ⟨1, _⟩ => 1 / Real.sqrt (y + z)
    | ⟨2, _⟩ => 1 / Real.sqrt (z + x)
  let g : Fin 3 → ℝ := fun i => match i with
    | ⟨0, _⟩ => Real.sqrt (x + y)
    | ⟨1, _⟩ => Real.sqrt (y + z)
    | ⟨2, _⟩ => Real.sqrt (z + x)
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ) f g
  simpa [f, g] using h

theorem h_left_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x) :
    (let f : Fin 3 → ℝ := fun i => match i with
        | ⟨0, _⟩ => 1 / Real.sqrt (x + y)
        | ⟨1, _⟩ => 1 / Real.sqrt (y + z)
        | ⟨2, _⟩ => 1 / Real.sqrt (z + x);
     let g : Fin 3 → ℝ := fun i => match i with
        | ⟨0, _⟩ => Real.sqrt (x + y)
        | ⟨1, _⟩ => Real.sqrt (y + z)
        | ⟨2, _⟩ => Real.sqrt (z + x);
     ∑ i, f i * g i = (3 : ℝ)) := by
  classical
  have hxy_ne : Real.sqrt (x + y) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (x + y) := Real.sqrt_pos.mpr hxy_pos
    exact ne_of_gt this
  have hyz_ne : Real.sqrt (y + z) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (y + z) := Real.sqrt_pos.mpr hyz_pos
    exact ne_of_gt this
  have hzx_ne : Real.sqrt (z + x) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (z + x) := Real.sqrt_pos.mpr hzx_pos
    exact ne_of_gt this
  simpa [Fin.sum_univ_three, one_div, hxy_ne, hyz_ne, hzx_ne] using
    (by norm_num : (1 + 1 + 1 : ℝ) = 3)

theorem h_f_sq_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x) :
    (let f : Fin 3 → ℝ := fun i => match i with
        | ⟨0, _⟩ => 1 / Real.sqrt (x + y)
        | ⟨1, _⟩ => 1 / Real.sqrt (y + z)
        | ⟨2, _⟩ => 1 / Real.sqrt (z + x);
     ∑ i, (f i) ^ 2 = (1 / (x + y) + 1 / (y + z) + 1 / (z + x))) := by
  classical
  have hxy_nonneg : 0 ≤ x + y := le_of_lt hxy_pos
  have hyz_nonneg : 0 ≤ y + z := le_of_lt hyz_pos
  have hzx_nonneg : 0 ≤ z + x := le_of_lt hzx_pos
  have hxy_eq :
      (√(x + y))⁻¹ * (√(x + y))⁻¹ = (x + y)⁻¹ := by
    have hne : (√(x + y)) ≠ 0 := by
      have : 0 < √(x + y) := Real.sqrt_pos.mpr hxy_pos
      exact ne_of_gt this
    field_simp [Real.mul_self_sqrt hxy_nonneg]
    simpa [pow_two, Real.sq_sqrt hxy_nonneg]
  have hyz_eq :
      (√(y + z))⁻¹ * (√(y + z))⁻¹ = (y + z)⁻¹ := by
    have hne : (√(y + z)) ≠ 0 := by
      have : 0 < √(y + z) := Real.sqrt_pos.mpr hyz_pos
      exact ne_of_gt this
    field_simp [Real.mul_self_sqrt hyz_nonneg]
    simpa [pow_two, Real.sq_sqrt hyz_nonneg]
  have hzx_eq :
      (√(z + x))⁻¹ * (√(z + x))⁻¹ = (z + x)⁻¹ := by
    have hne : (√(z + x)) ≠ 0 := by
      have : 0 < √(z + x) := Real.sqrt_pos.mpr hzx_pos
      exact ne_of_gt this
    field_simp [Real.mul_self_sqrt hzx_nonneg]
    simpa [pow_two, Real.sq_sqrt hzx_nonneg]
  simpa [Fin.sum_univ_three, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm,
        mul_assoc, hxy_eq, hyz_eq, hzx_eq]

theorem hyz_nonneg_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (0 : ℝ) ≤ y + z := by
  exact le_of_lt hyz_pos

theorem hzx_nonneg_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (0 : ℝ) ≤ z + x := by
  exact le_of_lt hzx_pos

theorem hsum_nonneg_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (0 : ℝ) ≤ x + y + z := by
  exact le_of_lt hsum_pos

theorem hxy_nonneg_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (0 : ℝ) ≤ x + y := by
  exact le_of_lt hxy_pos

theorem h_sq_u_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (∑ i : Fin 3,
          (Real.sqrt (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x)) ^ 2) = 2 * (x + y + z) := by
  have hx : (0 : ℝ) ≤ x + y := le_of_lt hxy_pos
  have hy : (0 : ℝ) ≤ y + z := le_of_lt hyz_pos
  have hz : (0 : ℝ) ≤ z + x := le_of_lt hzx_pos
  have hcalc :
      (∑ i : Fin 3,
          (Real.sqrt (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x)) ^ 2)
        = (x + y) + (y + z) + (z + x) := by
    simp [Fin.sum_univ_three, Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sq_sqrt hz]
  have hsum : (x + y) + (y + z) + (z + x) = 2 * (x + y + z) := by
    ring
  simpa [hsum] using hcalc

theorem h_cauchy_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (∑ i : Fin 3,
          Real.sqrt (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x) *
          (1 / Real.sqrt (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x))) ≤
        Real.sqrt (∑ i : Fin 3,
          (Real.sqrt (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x)) ^ 2) *
        Real.sqrt (∑ i : Fin 3,
          (1 / Real.sqrt (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x)) ^ 2) := by
  simpa using
    (Real.sum_mul_le_sqrt_mul_sqrt
        (s := (Finset.univ : Finset (Fin 3)))
        (f := fun i : Fin 3 =>
          Real.sqrt (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x))
        (g := fun i : Fin 3 =>
          (1 : ℝ) / Real.sqrt (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x)))

theorem h_sum_uv_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (∑ i : Fin 3,
          Real.sqrt (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x) *
          (1 / Real.sqrt (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x))) = 3 := by
  -- non‑zero square roots, using positivity hypotheses
  have hxy_ne : (Real.sqrt (x + y)) ≠ 0 := by
    have : 0 < Real.sqrt (x + y) := (Real.sqrt_pos.mpr hxy_pos)
    exact ne_of_gt this
  have hyz_ne : (Real.sqrt (y + z)) ≠ 0 := by
    have : 0 < Real.sqrt (y + z) := (Real.sqrt_pos.mpr hyz_pos)
    exact ne_of_gt this
  have hzx_ne : (Real.sqrt (z + x)) ≠ 0 := by
    have : 0 < Real.sqrt (z + x) := (Real.sqrt_pos.mpr hzx_pos)
    exact ne_of_gt this
  calc
    (∑ i : Fin 3,
          Real.sqrt (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x) *
          (1 / Real.sqrt (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x))) =
        (Real.sqrt (x + y) * (1 / Real.sqrt (x + y)) +
         Real.sqrt (y + z) * (1 / Real.sqrt (y + z)) +
         Real.sqrt (z + x) * (1 / Real.sqrt (z + x))) := by
      simpa [Fin.sum_univ_three]
    _ = (1 + 1 + 1) := by
      simp [div_eq_mul_inv, hxy_ne, hyz_ne, hzx_ne]
    _ = 3 := by norm_num

theorem hxy_nonneg_h_sq_v_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (0 : ℝ) ≤ x + y := by
  exact le_of_lt hxy_pos

theorem hyz_nonneg_h_sq_v_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (0 : ℝ) ≤ y + z := by
  exact le_of_lt hyz_pos

theorem hzx_nonneg_h_sq_v_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (0 : ℝ) ≤ z + x := by
  rcases h₀ with ⟨hx, hy, hz⟩
  have hpos : (0 : ℝ) < z + x := by
    simpa [add_comm] using add_pos hx hz
  exact le_of_lt hpos

theorem term0_h_sq_v_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (hxy_pos : 0 < x + y) :
    (1 / Real.sqrt (x + y)) ^ 2 = 1 / (x + y) := by
  have hnonneg : (0 : ℝ) ≤ x + y := le_of_lt hxy_pos
  calc
    (1 / Real.sqrt (x + y)) ^ 2
        = (1 / Real.sqrt (x + y)) * (1 / Real.sqrt (x + y)) := by
          simpa [pow_two]
    _ = 1 / (Real.sqrt (x + y) * Real.sqrt (x + y)) := by
          field_simp
    _ = 1 / ((Real.sqrt (x + y)) ^ 2) := by
          simpa [pow_two, mul_comm]
    _ = 1 / (x + y) := by
          simpa [Real.sq_sqrt hnonneg]

theorem term1_h_sq_v_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hyz_pos : 0 < y + z) :
    (1 / Real.sqrt (y + z)) ^ 2 = 1 / (y + z) := by
  have h_nonneg : 0 ≤ y + z := le_of_lt hyz_pos
  calc
    (1 / Real.sqrt (y + z)) ^ 2
        = 1 / (Real.sqrt (y + z) ^ 2) := by
          simpa using (one_div_pow (Real.sqrt (y + z)) 2)
    _ = 1 / (y + z) := by
          simpa [Real.sq_sqrt h_nonneg]

theorem term2_h_sq_v_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hzx_pos : 0 < z + x) :
    (1 / Real.sqrt (z + x)) ^ 2 = 1 / (z + x) := by
  have h_nonneg : 0 ≤ z + x := le_of_lt hzx_pos
  calc
    (1 / Real.sqrt (z + x)) ^ 2
        = (1 / Real.sqrt (z + x)) * (1 / Real.sqrt (z + x)) := by
          simpa [pow_two]
    _ = 1 / (Real.sqrt (z + x) * Real.sqrt (z + x)) := by
          field_simp
    _ = 1 / (z + x) := by
          simpa [Real.mul_self_sqrt h_nonneg]

theorem sum_eq_h_sq_v_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h0 : (1 / Real.sqrt (x + y)) ^ 2 = 1 / (x + y))
    (h1 : (1 / Real.sqrt (y + z)) ^ 2 = 1 / (y + z))
    (h2 : (1 / Real.sqrt (z + x)) ^ 2 = 1 / (z + x)) :
    (∑ i : Fin 3,
          (1 / Real.sqrt (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x)) ^ 2) =
        (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) := by
  classical
  have h0' : (Real.sqrt (x + y) ^ 2)⁻¹ = 1 / (x + y) := by
    simpa [one_div, pow_two] using h0
  have h1' : (Real.sqrt (y + z) ^ 2)⁻¹ = 1 / (y + z) := by
    simpa [one_div, pow_two] using h1
  have h2' : (Real.sqrt (z + x) ^ 2)⁻¹ = 1 / (z + x) := by
    simpa [one_div, pow_two] using h2
  calc
    (∑ i : Fin 3,
          (1 / Real.sqrt (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x)) ^ 2)
        = (Real.sqrt (x + y) ^ 2)⁻¹ + (Real.sqrt (y + z) ^ 2)⁻¹ + (Real.sqrt (z + x) ^ 2)⁻¹ := by
          simpa [Fin.sum_univ_three, one_div, pow_two]
    _ = 1 / (x + y) + 1 / (y + z) + 1 / (z + x) := by
          simpa [h0', h1', h2']

theorem h_sq_v_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (∑ i : Fin 3,
          (1 / Real.sqrt (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x)) ^ 2) =
        (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) := by
  -- non‑negativity of each pairwise sum
  have hxy_nonneg : (0 : ℝ) ≤ x + y :=
    hxy_nonneg_h_sq_v_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀ hxy_pos hyz_pos hzx_pos hsum_pos
  have hyz_nonneg : (0 : ℝ) ≤ y + z :=
    hyz_nonneg_h_sq_v_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀ hxy_pos hyz_pos hzx_pos hsum_pos
  have hzx_nonneg : (0 : ℝ) ≤ z + x :=
    hzx_nonneg_h_sq_v_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀ hxy_pos hyz_pos hzx_pos hsum_pos
  -- simplify the term corresponding to i = 0
  have term0 :
      (1 / Real.sqrt (x + y)) ^ 2 = 1 / (x + y) :=
    term0_h_sq_v_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy x y z hxy_pos
  -- simplify the term corresponding to i = 1
  have term1 :
      (1 / Real.sqrt (y + z)) ^ 2 = 1 / (y + z) :=
    term1_h_sq_v_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy x y z hyz_pos
  -- simplify the term corresponding to i = 2
  have term2 :
      (1 / Real.sqrt (z + x)) ^ 2 = 1 / (z + x) :=
    term2_h_sq_v_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy x y z hzx_pos
  -- rewrite the whole sum using the three simplified terms
  have sum_eq :
      (∑ i : Fin 3,
          (1 / Real.sqrt (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x)) ^ 2) =
        (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) :=
    sum_eq_h_sq_v_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy x y z term0 term1 term2
  exact sum_eq

theorem h_sum_recip_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) :
    (∑ i : Fin 3,
        (1 /
          (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x) : ℝ)) =
      (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) := by
  simp [Fin.sum_univ_three]

theorem h_sum_one_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy :
    (∑ i : Fin 3, (1 : ℝ)) = (3 : ℝ) := by
  simpa using (Fin.sum_const (n := 3) (x := (1 : ℝ)))

theorem h_sum_pair_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) :
    (∑ i : Fin 3,
        (match i with
          | ⟨0, _⟩ => x + y
          | ⟨1, _⟩ => y + z
          | ⟨2, _⟩ => z + x : ℝ)) =
      2 * (x + y + z) := by
  classical
  calc
    (∑ i : Fin 3,
        (match i with
          | ⟨0, _⟩ => x + y
          | ⟨1, _⟩ => y + z
          | ⟨2, _⟩ => z + x : ℝ))
        = (x + y) + (y + z) + (z + x) := by
          simp [Fin.sum_univ_three]
    _ = 2 * (x + y + z) := by
          ring

theorem h_cauchy_h_cauchy_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (∑ i : Fin 3,
        Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x) *
        Real.sqrt (if i = 0 then (1 / (x + y))
                     else if i = 1 then (1 / (y + z))
                     else (1 / (z + x)))) ≤
      Real.sqrt (∑ i : Fin 3,
        (Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x)) ^ 2) *
      Real.sqrt (∑ i : Fin 3,
        (Real.sqrt (if i = 0 then (1 / (x + y))
                     else if i = 1 then (1 / (y + z))
                     else (1 / (z + x)))) ^ 2) := by
  classical
  simpa using
    (Real.sum_mul_le_sqrt_mul_sqrt
      (s := (Finset.univ : Finset (Fin 3)))
      (f := fun i : Fin 3 =>
        Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x))
      (g := fun i : Fin 3 =>
        Real.sqrt (if i = 0 then (1 / (x + y))
          else if i = 1 then (1 / (y + z))
          else (1 / (z + x)))))

theorem h_a_sq_h_cauchy_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (∑ i : Fin 3,
        (Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x)) ^ 2) =
      2 * (x + y + z) := by
  have hxy_nonneg : (0 : ℝ) ≤ x + y := le_of_lt hxy_pos
  have hyz_nonneg : (0 : ℝ) ≤ y + z := le_of_lt hyz_pos
  have hzx_nonneg : (0 : ℝ) ≤ z + x := le_of_lt hzx_pos
  have hsum :
      (∑ i : Fin 3,
          (Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x)) ^ 2) =
        (x + y) + (y + z) + (z + x) := by
    simp [Fin.sum_univ_three, Real.sq_sqrt, hxy_nonneg, hyz_nonneg, hzx_nonneg]
  calc
    (∑ i : Fin 3,
        (Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x)) ^ 2) =
        (x + y) + (y + z) + (z + x) := hsum
    _ = 2 * (x + y + z) := by
      ring

theorem h_b_sq_h_cauchy_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (∑ i : Fin 3,
        (Real.sqrt (if i = 0 then (1 / (x + y))
                     else if i = 1 then (1 / (y + z))
                     else (1 / (z + x)))) ^ 2) =
      1 / (x + y) + 1 / (y + z) + 1 / (z + x) := by
  -- non‑negativity of the three reciprocals
  have hxy_nonneg : (0 : ℝ) ≤ 1 / (x + y) := by
    have : (0 : ℝ) < x + y := hxy_pos
    simpa [one_div] using inv_nonneg.mpr (le_of_lt this)
  have hyz_nonneg : (0 : ℝ) ≤ 1 / (y + z) := by
    have : (0 : ℝ) < y + z := hyz_pos
    simpa [one_div] using inv_nonneg.mpr (le_of_lt this)
  have hzx_nonneg : (0 : ℝ) ≤ 1 / (z + x) := by
    have : (0 : ℝ) < z + x := hzx_pos
    simpa [one_div] using inv_nonneg.mpr (le_of_lt this)
  calc
    (∑ i : Fin 3,
        (Real.sqrt (if i = 0 then (1 / (x + y))
                     else if i = 1 then (1 / (y + z))
                     else (1 / (z + x)))) ^ 2)
        = (Real.sqrt (1 / (x + y))) ^ 2
          + (Real.sqrt (1 / (y + z))) ^ 2
          + (Real.sqrt (1 / (z + x))) ^ 2 := by
          simp [Fin.sum_univ_three]
    _ = 1 / (x + y) + 1 / (y + z) + 1 / (z + x) := by
          rw [Real.sq_sqrt hxy_nonneg,
              Real.sq_sqrt hyz_nonneg,
              Real.sq_sqrt hzx_nonneg]

theorem h_ab_h_cauchy_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (∑ i : Fin 3,
        Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x) *
        Real.sqrt (if i = 0 then (1 / (x + y))
                     else if i = 1 then (1 / (y + z))
                     else (1 / (z + x)))) = (3 : ℝ) := by
  have hxy_ne : (x + y) ≠ 0 := ne_of_gt hxy_pos
  have hyz_ne : (y + z) ≠ 0 := ne_of_gt hyz_pos
  have hzx_ne : (z + x) ≠ 0 := ne_of_gt hzx_pos

  have h0 : Real.sqrt (x + y) * Real.sqrt (1 / (x + y)) = (1 : ℝ) := by
    have hpos : 0 ≤ (1 / (x + y)) := by
      positivity
    calc
      Real.sqrt (x + y) * Real.sqrt (1 / (x + y))
          = Real.sqrt ((x + y) * (1 / (x + y))) := by
            rw [← Real.sqrt_mul' (x + y) hpos]
      _ = Real.sqrt (1) := by
            have : (x + y) * (1 / (x + y)) = (1 : ℝ) := by
              field_simp [hxy_ne]
            simpa [this]
      _ = 1 := by simpa

  have h1 : Real.sqrt (y + z) * Real.sqrt (1 / (y + z)) = (1 : ℝ) := by
    have hpos : 0 ≤ (1 / (y + z)) := by
      positivity
    calc
      Real.sqrt (y + z) * Real.sqrt (1 / (y + z))
          = Real.sqrt ((y + z) * (1 / (y + z))) := by
            rw [← Real.sqrt_mul' (y + z) hpos]
      _ = Real.sqrt (1) := by
            have : (y + z) * (1 / (y + z)) = (1 : ℝ) := by
              field_simp [hyz_ne]
            simpa [this]
      _ = 1 := by simpa

  have h2 : Real.sqrt (z + x) * Real.sqrt (1 / (z + x)) = (1 : ℝ) := by
    have hpos : 0 ≤ (1 / (z + x)) := by
      positivity
    calc
      Real.sqrt (z + x) * Real.sqrt (1 / (z + x))
          = Real.sqrt ((z + x) * (1 / (z + x))) := by
            rw [← Real.sqrt_mul' (z + x) hpos]
      _ = Real.sqrt (1) := by
            have : (z + x) * (1 / (z + x)) = (1 : ℝ) := by
              field_simp [hzx_ne]
            simpa [this]
      _ = 1 := by simpa

  calc
    (∑ i : Fin 3,
        Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x) *
        Real.sqrt (if i = 0 then (1 / (x + y))
                     else if i = 1 then (1 / (y + z))
                     else (1 / (z + x)))) =
        (Real.sqrt (x + y) * Real.sqrt (1 / (x + y)) +
         Real.sqrt (y + z) * Real.sqrt (1 / (y + z)) +
         Real.sqrt (z + x) * Real.sqrt (1 / (z + x))) := by
          simpa [Fin.sum_univ_three] using
            (Fin.sum_univ_three (fun i : Fin 3 =>
              Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x) *
              Real.sqrt (if i = 0 then (1 / (x + y))
                           else if i = 1 then (1 / (y + z))
                           else (1 / (z + x)))))
    _ = (1 + 1 + 1) := by
          rw [h0, h1, h2]
    _ = (3 : ℝ) := by norm_num

theorem h3_le_h_cauchy_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z)
    (h_a_sq :
      (∑ i : Fin 3,
        (Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x)) ^ 2) =
        2 * (x + y + z))
    (h_b_sq :
      (∑ i : Fin 3,
        (Real.sqrt (if i = 0 then (1 / (x + y))
                     else if i = 1 then (1 / (y + z))
                     else (1 / (z + x)))) ^ 2) =
        1 / (x + y) + 1 / (y + z) + 1 / (z + x))
    (h_ab :
      (∑ i : Fin 3,
        Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x) *
        Real.sqrt (if i = 0 then (1 / (x + y))
                     else if i = 1 then (1 / (y + z))
                     else (1 / (z + x)))) = (3 : ℝ)) :
    (3 : ℝ) ≤
      Real.sqrt (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) *
      Real.sqrt (2 * (x + y + z)) := by
  -- Cauchy–Schwarz inequality for the two families of square‑roots
  have hcs :
      (∑ i : Fin 3,
        Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x) *
        Real.sqrt (if i = 0 then (1 / (x + y))
                     else if i = 1 then (1 / (y + z))
                     else (1 / (z + x)))) ≤
        Real.sqrt (∑ i : Fin 3,
          (Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x)) ^ 2) *
        Real.sqrt (∑ i : Fin 3,
          (Real.sqrt (if i = 0 then (1 / (x + y))
                       else if i = 1 then (1 / (y + z))
                       else (1 / (z + x)))) ^ 2) :=
    by
      simpa using
        (Real.sum_mul_le_sqrt_mul_sqrt
          (s := (Finset.univ : Finset (Fin 3)))
          (f := fun i : Fin 3 =>
            Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x))
          (g := fun i : Fin 3 =>
            Real.sqrt (if i = 0 then (1 / (x + y))
                         else if i = 1 then (1 / (y + z))
                         else (1 / (z + x)))))
  -- replace the left‑hand side by `3` using `h_ab`
  have hle1 :
      (3 : ℝ) ≤
        Real.sqrt (∑ i : Fin 3,
          (Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x)) ^ 2) *
        Real.sqrt (∑ i : Fin 3,
          (Real.sqrt (if i = 0 then (1 / (x + y))
                       else if i = 1 then (1 / (y + z))
                       else (1 / (z + x)))) ^ 2) := by
    have h := hcs
    rw [h_ab] at h
    exact h
  -- rewrite the two sums of squares using `h_a_sq` and `h_b_sq`
  have hle2 :
      (3 : ℝ) ≤
        Real.sqrt (2 * (x + y + z)) *
        Real.sqrt (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) := by
    have h := hle1
    rw [h_a_sq] at h
    rw [h_b_sq] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  -- commute the factors to match the goal statement
  simpa [mul_comm, mul_left_comm, mul_assoc] using hle2

theorem h_cauchy_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy
    (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (3 : ℝ) ≤
      Real.sqrt (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) *
      Real.sqrt (2 * (x + y + z)) := by
  have h_a_sq :
      (∑ i : Fin 3,
        (Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x)) ^ 2) =
        2 * (x + y + z) :=
    h_a_sq_h_cauchy_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀
      hxy_pos hyz_pos hzx_pos hsum_pos
  have h_b_sq :
      (∑ i : Fin 3,
        (Real.sqrt (if i = 0 then (1 / (x + y))
                     else if i = 1 then (1 / (y + z))
                     else (1 / (z + x)))) ^ 2) =
        1 / (x + y) + 1 / (y + z) + 1 / (z + x) :=
    h_b_sq_h_cauchy_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀
      hxy_pos hyz_pos hzx_pos hsum_pos
  have h_ab :
      (∑ i : Fin 3,
        Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x) *
        Real.sqrt (if i = 0 then (1 / (x + y))
                     else if i = 1 then (1 / (y + z))
                     else (1 / (z + x)))) = (3 : ℝ) :=
    h_ab_h_cauchy_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀
      hxy_pos hyz_pos hzx_pos hsum_pos
  have h_cauchy :
      (∑ i : Fin 3,
        Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x) *
        Real.sqrt (if i = 0 then (1 / (x + y))
                     else if i = 1 then (1 / (y + z))
                     else (1 / (z + x)))) ≤
        Real.sqrt (∑ i : Fin 3,
          (Real.sqrt (if i = 0 then x + y else if i = 1 then y + z else z + x)) ^ 2) *
        Real.sqrt (∑ i : Fin 3,
          (Real.sqrt (if i = 0 then (1 / (x + y))
                       else if i = 1 then (1 / (y + z))
                       else (1 / (z + x)))) ^ 2) :=
    h_cauchy_h_cauchy_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀
      hxy_pos hyz_pos hzx_pos hsum_pos
  have h3_le :
      (3 : ℝ) ≤
        Real.sqrt (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) *
        Real.sqrt (2 * (x + y + z)) :=
    h3_le_h_cauchy_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀
      hxy_pos hyz_pos hzx_pos hsum_pos h_a_sq h_b_sq h_ab
  simpa using h3_le

theorem h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (3 : ℝ) ≤
      Real.sqrt (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) *
      Real.sqrt (2 * (x + y + z)) := by
  have h_sum_one :
      (∑ i : Fin 3, (1 : ℝ)) = (3 : ℝ) := by
    simpa using
      h_sum_one_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy
  have h_sum_recip :
      (∑ i : Fin 3,
          (1 /
            (match i with
              | ⟨0, _⟩ => x + y
              | ⟨1, _⟩ => y + z
              | ⟨2, _⟩ => z + x) : ℝ)) =
        (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) := by
    simpa using
      h_sum_recip_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy x y z
  have h_sum_pair :
      (∑ i : Fin 3,
          (match i with
            | ⟨0, _⟩ => x + y
            | ⟨1, _⟩ => y + z
            | ⟨2, _⟩ => z + x : ℝ)) =
        2 * (x + y + z) := by
    simpa using
      h_sum_pair_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy x y z
  have h_cauchy :
      (3 : ℝ) ≤
        Real.sqrt (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) *
        Real.sqrt (2 * (x + y + z)) := by
    simpa using
      h_cauchy_h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀ hxy_pos hyz_pos hzx_pos hsum_pos
  exact h_cauchy

theorem h_final_hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (3 : ℝ) ≤
      Real.sqrt ((1 / (x + y) + 1 / (y + z) + 1 / (z + x))) *
      Real.sqrt (2 * (x + y + z)) :=
by
  exact
    h_goal_h_final_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀ hxy_pos hyz_pos hzx_pos hsum_pos

theorem hCauchy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (hxy_pos : 0 < x + y) (hyz_pos : 0 < y + z) (hzx_pos : 0 < z + x)
    (hsum_pos : 0 < x + y + z) :
    (3 : ℝ) ≤
      Real.sqrt ((1 / (x + y) + 1 / (y + z) + 1 / (z + x))) *
      Real.sqrt (2 * (x + y + z)) := by
  have hx_pos : 0 < x := by
    exact hx_pos_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀
  have hy_pos : 0 < y := by
    exact hy_pos_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀
  have hz_pos : 0 < z := by
    exact hz_pos_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀
  have hxy_nonneg : 0 ≤ x + y := by
    exact hxy_nonneg_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀ hxy_pos
  have hyz_nonneg : 0 ≤ y + z := by
    exact hyz_nonneg_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀ hyz_pos
  have hzx_nonneg : 0 ≤ z + x := by
    exact hzx_nonneg_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀ hzx_pos
  have hsum_nonneg : 0 ≤ x + y + z := by
    exact hsum_nonneg_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀ hsum_pos
  let f : Fin 3 → ℝ := fun i => match i with
    | ⟨0, _⟩ => 1 / Real.sqrt (x + y)
    | ⟨1, _⟩ => 1 / Real.sqrt (y + z)
    | ⟨2, _⟩ => 1 / Real.sqrt (z + x)
  let g : Fin 3 → ℝ := fun i => match i with
    | ⟨0, _⟩ => Real.sqrt (x + y)
    | ⟨1, _⟩ => Real.sqrt (y + z)
    | ⟨2, _⟩ => Real.sqrt (z + x)
  have hCS :
      ∑ i, f i * g i ≤ Real.sqrt (∑ i, (f i) ^ 2) * Real.sqrt (∑ i, (g i) ^ 2) := by
    simpa [f, g] using
      (hCS_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀ hxy_pos hyz_pos hzx_pos)
  have h_left : ∑ i, f i * g i = (3 : ℝ) := by
    simpa [f, g] using
      (h_left_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀ hxy_pos hyz_pos hzx_pos)
  have h_f_sq :
      ∑ i, (f i) ^ 2 = (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) := by
    simpa [f] using
      (h_f_sq_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀ hxy_pos hyz_pos hzx_pos)
  have h_g_sq : ∑ i, (g i) ^ 2 = (2 * (x + y + z)) := by
    simpa [g] using
      (h_g_sq_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀ hxy_pos hyz_pos hzx_pos)
  have h_final :
      (3 : ℝ) ≤
        Real.sqrt ((1 / (x + y) + 1 / (y + z) + 1 / (z + x))) *
        Real.sqrt (2 * (x + y + z)) := by
    exact
      h_final_hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀ hxy_pos hyz_pos hzx_pos hsum_pos
  exact h_final

theorem algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
    9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  have hxy_pos : 0 < x + y := by
    exact hxy_pos_algebra_9onxpypzleqsum2onxpy x y z h₀
  have hyz_pos : 0 < y + z := by
    exact hyz_pos_algebra_9onxpypzleqsum2onxpy x y z h₀
  have hzx_pos : 0 < z + x := by
    exact hzx_pos_algebra_9onxpypzleqsum2onxpy x y z h₀
  have hsum_pos : 0 < x + y + z := by
    exact hsum_pos_algebra_9onxpypzleqsum2onxpy x y z h₀
  have hCauchy :
      (3 : ℝ) ≤
        Real.sqrt ((1 / (x + y) + 1 / (y + z) + 1 / (z + x))) *
        Real.sqrt (2 * (x + y + z)) := by
    exact hCauchy_algebra_9onxpypzleqsum2onxpy x y z h₀ hxy_pos hyz_pos hzx_pos hsum_pos
  have hsq :
      (9 : ℝ) ≤
        (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) *
        (2 * (x + y + z)) := by
    exact hsq_algebra_9onxpypzleqsum2onxpy x y z h₀ hCauchy
  have hdiv :
      (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥
        (9 : ℝ) / (2 * (x + y + z)) := by
    exact hdiv_algebra_9onxpypzleqsum2onxpy x y z h₀ hsum_pos hsq
  have hfinal :
      9 / (x + y + z) ≤
        2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
    exact hfinal_algebra_9onxpypzleqsum2onxpy x y z h₀ hsum_pos hdiv
  exact hfinal

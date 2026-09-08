import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem hx_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) : 0 < x := by
  have h₁ : 0 < x := by linarith
  linarith

theorem hy_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) : 0 < y := by
  have h₁ : 0 < y := by linarith
  exact h₁

theorem hz_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) : 0 < z := by
  have h₁ : 0 < z := by linarith
  exact h₁

theorem hyz_pos_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hy : 0 < y) (hz : 0 < z) : 0 < y + z := by
  have h : 0 < y + z := by
    -- Use the fact that the sum of two positive numbers is positive.
    linarith
  exact h

theorem hzx_pos_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hz : 0 < z) (hx : 0 < x) : 0 < z + x := by
  have h₁ : 0 < z + x := by
    -- Use the fact that the sum of two positive numbers is positive.
    linarith
  exact h₁

theorem hxy_pos_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < x + y := by
  have h : 0 < x + y := by
    -- Since x and y are both positive, their sum is also positive.
    linarith
  exact h

theorem hsum_pos_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 0 < x + y + z := by
  have h₁ : 0 < x + y + z := by
    -- Since x, y, z are all positive, their sum is also positive.
    linarith [hx, hy, hz]
  exact h₁

theorem hb1_pos_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hxy_pos : 0 < x + y) : 0 < (x + y) / 2 := by
  have h₁ : 0 < (x + y) / 2 := by
    -- Since x + y > 0, dividing both sides by 2 (a positive number) preserves the inequality.
    have h₂ : 0 < x + y := hxy_pos
    -- Use the fact that dividing a positive number by 2 results in a positive number.
    have h₃ : 0 < (x + y) / 2 := by
      -- Use the property of inequalities involving positive numbers.
      linarith
    exact h₃
  exact h₁

theorem hb2_pos_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hyz_pos : 0 < y + z) : 0 < (y + z) / 2 := by
  have h₁ : 0 < (y + z) / 2 := by
    -- Since y + z > 0, dividing both sides by 2 (a positive number) preserves the inequality.
    have h₂ : 0 < y + z := hyz_pos
    -- Use the fact that dividing a positive number by a positive number (2) results in a positive number.
    have h₃ : 0 < (y + z) / 2 := by
      -- Use the property of division and positivity.
      linarith
    exact h₃
  exact h₁

theorem hb3_pos_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hzx_pos : 0 < z + x) : 0 < (z + x) / 2 := by
  have h₁ : 0 < (z + x) / 2 := by
    -- Since z + x > 0, dividing both sides by 2 (a positive number) preserves the inequality.
    have h₂ : 0 < z + x := hzx_pos
    have h₃ : 0 < (z + x) / 2 := by
      -- Use the fact that dividing a positive number by 2 keeps it positive.
      linarith
    exact h₃
  exact h₁

theorem h_right_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) :
    ( (1 + 1 + 1) ^ 2 ) /
      ( (x + y) / 2 + (y + z) / 2 + (z + x) / 2 ) =
    9 / (x + y + z) := by
  have h₁ : (1 + 1 + 1 : ℝ) ^ 2 = 9 := by norm_num
  have h₂ : (x + y) / 2 + (y + z) / 2 + (z + x) / 2 = x + y + z := by
    ring_nf
    <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try ring_nf at * <;> linarith)
  rw [h₁, h₂]
  <;>
  (try norm_num) <;>
  (try linarith) <;>
  (try ring_nf at * <;> linarith)

theorem h_left_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) :
    ( (1 : ℝ) ^ 2 / ((x + y) / 2) +
      (1 : ℝ) ^ 2 / ((y + z) / 2) +
      (1 : ℝ) ^ 2 / ((z + x) / 2) ) =
    2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  have h₁ : (1 : ℝ) ^ 2 / ((x + y) / 2) = 2 / (x + y) := by
    by_cases h : x + y = 0
    · -- If x + y = 0, both sides are undefined (but Lean treats them as 0)
      simp_all [h]
      <;> norm_num
      <;> field_simp [h]
      <;> ring_nf
      <;> norm_num
    · -- If x + y ≠ 0, we can safely simplify
      field_simp [h]
      <;> ring_nf
      <;> norm_num
      <;> field_simp [h]
      <;> ring_nf
  have h₂ : (1 : ℝ) ^ 2 / ((y + z) / 2) = 2 / (y + z) := by
    by_cases h : y + z = 0
    · -- If y + z = 0, both sides are undefined (but Lean treats them as 0)
      simp_all [h]
      <;> norm_num
      <;> field_simp [h]
      <;> ring_nf
      <;> norm_num
    · -- If y + z ≠ 0, we can safely simplify
      field_simp [h]
      <;> ring_nf
      <;> norm_num
      <;> field_simp [h]
      <;> ring_nf
  have h₃ : (1 : ℝ) ^ 2 / ((z + x) / 2) = 2 / (z + x) := by
    by_cases h : z + x = 0
    · -- If z + x = 0, both sides are undefined (but Lean treats them as 0)
      simp_all [h]
      <;> norm_num
      <;> field_simp [h]
      <;> ring_nf
      <;> norm_num
    · -- If z + x ≠ 0, we can safely simplify
      field_simp [h]
      <;> ring_nf
      <;> norm_num
      <;> field_simp [h]
      <;> ring_nf
  -- Combine the simplified terms using the established equalities
  calc
    ((1 : ℝ) ^ 2 / ((x + y) / 2) + (1 : ℝ) ^ 2 / ((y + z) / 2) + (1 : ℝ) ^ 2 / ((z + x) / 2)) =
        (2 / (x + y) + 2 / (y + z) + 2 / (z + x)) := by
      rw [h₁, h₂, h₃]
      <;>
      (try norm_num) <;>
      (try ring_nf) <;>
      (try field_simp) <;>
      (try linarith)
    _ = 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by rfl

theorem h_final_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h_left :
        ( (1 : ℝ) ^ 2 / ((x + y) / 2) +
          (1 : ℝ) ^ 2 / ((y + z) / 2) +
          (1 : ℝ) ^ 2 / ((z + x) / 2) ) =
        2 / (x + y) + 2 / (y + z) + 2 / (z + x))
    (h_right :
        ( (1 + 1 + 1) ^ 2 ) /
          ( (x + y) / 2 + (y + z) / 2 + (z + x) / 2 ) =
        9 / (x + y + z))
    (h_engel :
        ( (1 : ℝ) ^ 2 / ((x + y) / 2) +
          (1 : ℝ) ^ 2 / ((y + z) / 2) +
          (1 : ℝ) ^ 2 / ((z + x) / 2) ) ≥
        ( (1 + 1 + 1) ^ 2 ) /
          ( (x + y) / 2 + (y + z) / 2 + (z + x) / 2 )) :
    9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  have h_main : 2 / (x + y) + 2 / (y + z) + 2 / (z + x) ≥ 9 / (x + y + z) := by
    calc
      2 / (x + y) + 2 / (y + z) + 2 / (z + x) = (1 : ℝ) ^ 2 / ((x + y) / 2) + (1 : ℝ) ^ 2 / ((y + z) / 2) + (1 : ℝ) ^ 2 / ((z + x) / 2) := by
        rw [h_left]
      _ ≥ ( (1 + 1 + 1) ^ 2 ) / ( (x + y) / 2 + (y + z) / 2 + (z + x) / 2 ) := by
        exact h_engel
      _ = 9 / (x + y + z) := by
        rw [h_right]
  -- The main inequality is already in the desired form, so we just need to rearrange it.
  linarith

theorem hb2_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hb2_pos : 0 < (y + z) / 2) :
    0 < (y + z) / 2 := by
  -- The statement is directly given by the hypothesis `hb2_pos`, so we can use it to conclude the proof.
  exact hb2_pos

theorem hb1_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hb1_pos : 0 < (x + y) / 2) :
    0 < (x + y) / 2 := by
  -- The hypothesis `hb1_pos` already states that `0 < (x + y) / 2`, so we can directly use it to conclude the proof.
  exact hb1_pos

theorem hb3_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hb3_pos : 0 < (z + x) / 2) :
    0 < (z + x) / 2 := by
  -- The goal is to prove that 0 < (z + x) / 2, which is exactly the given hypothesis hb3_pos.
  -- Therefore, we can directly use hb3_pos to conclude the proof.
  exact hb3_pos

theorem hsum_den_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) :
    (x + y) / 2 + (y + z) / 2 + (z + x) / 2 = x + y + z := by
  have h₁ : (x + y) / 2 + (y + z) / 2 + (z + x) / 2 = (x + y + y + z + z + x) / 2 := by
    ring_nf
    <;> field_simp
    <;> ring_nf
  have h₂ : (x + y + y + z + z + x) / 2 = x + y + z := by
    ring_nf at h₁ ⊢
    <;> linarith
  linarith

theorem hpos1_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y : ℝ) (hb1 : 0 < (x + y) / 2) : 0 < (x + y) / 2 := by
  exact hb1

theorem hpos2_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (y z : ℝ) (hb2 : 0 < (y + z) / 2) : 0 < (y + z) / 2 := by
  -- The statement is trivially true because it is exactly the hypothesis `hb2`.
  exact hb2

theorem hpos3_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (z x : ℝ) (hb3 : 0 < (z + x) / 2) : 0 < (z + x) / 2 := by
  -- The statement is directly given as a hypothesis, so we can use it directly.
  exact hb3

theorem hSpos_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (hpos1 : 0 < (x + y) / 2) (hpos2 : 0 < (y + z) / 2) (hpos3 : 0 < (z + x) / 2) :
    0 < ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) := by
  have h₁ : 0 < (x + y) / 2 + (y + z) / 2 + (z + x) / 2 := by
    -- We know each term is positive, so their sum is also positive.
    linarith [hpos1, hpos2, hpos3]
  -- The result follows directly from the positivity of the sum.
  exact h₁

theorem hSpos'_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (hSpos : 0 < ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) :
    0 < ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) := by
  -- The goal is to prove that 0 < ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)
  -- This is exactly the hypothesis hSpos, so we can directly use it.
  exact hSpos

theorem hprod_ge_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (hEngel :
      ((1 : ℝ) ^ 2 / ((x + y) / 2) +
        (1 : ℝ) ^ 2 / ((y + z) / 2) +
        (1 : ℝ) ^ 2 / ((z + x) / 2)) *
          ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) ≥
        (1 + 1 + 1) ^ 2) :
    ((1 + 1 + 1) ^ 2) ≤
      ((1 : ℝ) ^ 2 / ((x + y) / 2) +
        (1 : ℝ) ^ 2 / ((y + z) / 2) +
        (1 : ℝ) ^ 2 / ((z + x) / 2)) *
        ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) := by
  have h₁ : ((1 + 1 + 1 : ℝ) ^ 2) ≤ ((1 : ℝ) ^ 2 / ((x + y) / 2) + (1 : ℝ) ^ 2 / ((y + z) / 2) + (1 : ℝ) ^ 2 / ((z + x) / 2)) * ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) := by
    -- Use the given inequality directly to prove the desired result.
    linarith
  -- The result follows directly from the given inequality.
  exact h₁

theorem hSpos_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (hSpos' :
      0 < ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) :
    0 < ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) := by
  -- The goal is exactly the same as the hypothesis hSpos', so we can directly use it.
  exact hSpos'

theorem hSne_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (hSpos :
      0 < ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) :
    ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) ≠ 0 := by
  intro h
  have h₁ : ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) = 0 := by linarith
  linarith

theorem hbc_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (hprod' :
      ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) *
        ((1 + 1 + 1) ^ 2 / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) ≤
        ((1 : ℝ) ^ 2 / ((x + y) / 2) +
          (1 : ℝ) ^ 2 / ((y + z) / 2) +
          (1 : ℝ) ^ 2 / ((z + x) / 2)) *
        ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) :
    ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) *
        ((1 + 1 + 1) ^ 2 / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) ≤
        ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) *
        ((1 : ℝ) ^ 2 / ((x + y) / 2) +
          (1 : ℝ) ^ 2 / ((y + z) / 2) +
          (1 : ℝ) ^ 2 / ((z + x) / 2)) := by
  have h_main : ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) * ((1 + 1 + 1) ^ 2 / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) ≤ ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) * ((1 : ℝ) ^ 2 / ((x + y) / 2) + (1 : ℝ) ^ 2 / ((y + z) / 2) + (1 : ℝ) ^ 2 / ((z + x) / 2)) := by
    have h₁ : ((1 : ℝ) ^ 2 / ((x + y) / 2) + (1 : ℝ) ^ 2 / ((y + z) / 2) + (1 : ℝ) ^ 2 / ((z + x) / 2)) * ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) = ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) * ((1 : ℝ) ^ 2 / ((x + y) / 2) + (1 : ℝ) ^ 2 / ((y + z) / 2) + (1 : ℝ) ^ 2 / ((z + x) / 2)) := by
      ring
    -- Use the given inequality and the fact that multiplication is commutative to prove the goal
    linarith
  
  exact h_main

theorem hfinal_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (hSpos :
      0 < ((x + y) / 2 + (y + z) / 2 + (z + x) / 2))
    (hbc :
      ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) *
        ((1 + 1 + 1) ^ 2 / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) ≤
        ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) *
        ((1 : ℝ) ^ 2 / ((x + y) / 2) +
          (1 : ℝ) ^ 2 / ((y + z) / 2) +
          (1 : ℝ) ^ 2 / ((z + x) / 2))) :
    ((1 + 1 + 1) ^ 2) / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) ≤
      ((1 : ℝ) ^ 2 / ((x + y) / 2) +
        (1 : ℝ) ^ 2 / ((y + z) / 2) +
        (1 : ℝ) ^ 2 / ((z + x) / 2)) := by
  exact (le_of_mul_le_mul_left hbc hSpos)

theorem hA_def_hprod'_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) :
    ((1 + 1 + 1) ^ 2) = ((1 + 1 + 1) ^ 2) := by
  rfl

theorem hS_def_hprod'_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) :
    ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) =
      ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) := by
  rfl

theorem h_mul_le_A_hprod'_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) :
    ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) *
        ((1 + 1 + 1) ^ 2 / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) ≤
        (1 + 1 + 1) ^ 2 := by
  have h_main : ∀ (a : ℝ), a * ((1 + 1 + 1 : ℝ) ^ 2 / a) ≤ (1 + 1 + 1 : ℝ) ^ 2 := by
    intro a
    by_cases h : a = 0
    · -- Case: a = 0
      rw [h]
      norm_num
    · -- Case: a ≠ 0
      have h₁ : a * ((1 + 1 + 1 : ℝ) ^ 2 / a) = (1 + 1 + 1 : ℝ) ^ 2 := by
        field_simp [h]
        <;> ring
        <;> norm_num
      rw [h₁]
      <;> norm_num
  
  have h_final : ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) * ((1 + 1 + 1) ^ 2 / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) ≤ (1 + 1 + 1) ^ 2 := by
    have h₁ : ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) * ((1 + 1 + 1 : ℝ) ^ 2 / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) ≤ (1 + 1 + 1 : ℝ) ^ 2 := by
      apply h_main
    -- Since (1 + 1 + 1 : ℝ) ^ 2 is the same as (1 + 1 + 1) ^ 2, we can directly use the result from h₁
    norm_num at h₁ ⊢
    <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try assumption) <;>
    (try ring_nf at h₁ ⊢) <;>
    (try simp_all) <;>
    (try nlinarith)
    <;>
    (try
      {
        -- This block is a catch-all for any remaining simplifications or arithmetic
        norm_num at h₁ ⊢
        <;>
        linarith
      })
  
  exact h_final

theorem h_final_hprod'_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (h_mul_le_A :
        ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) *
          ((1 + 1 + 1) ^ 2 / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) ≤
          (1 + 1 + 1) ^ 2)
    (hprod_ge :
        ((1 + 1 + 1) ^ 2) ≤
          ((1 : ℝ) ^ 2 / ((x + y) / 2) +
            (1 : ℝ) ^ 2 / ((y + z) / 2) +
            (1 : ℝ) ^ 2 / ((z + x) / 2)) *
            ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) :
    ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) *
        ((1 + 1 + 1) ^ 2 / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) ≤
        ((1 : ℝ) ^ 2 / ((x + y) / 2) +
          (1 : ℝ) ^ 2 / ((y + z) / 2) +
          (1 : ℝ) ^ 2 / ((z + x) / 2)) *
        ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) := by
  have h9 : (1 + 1 + 1 : ℝ) ^ 2 = 9 := by
    norm_num
    <;>
    simp [pow_two]
    <;>
    norm_num
  
  have h_main : ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) * ((1 + 1 + 1) ^ 2 / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) ≤ ((1 : ℝ) ^ 2 / ((x + y) / 2) + (1 : ℝ) ^ 2 / ((y + z) / 2) + (1 : ℝ) ^ 2 / ((z + x) / 2)) * ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) := by
    have h₁ : ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) * ((1 + 1 + 1) ^ 2 / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) ≤ (1 + 1 + 1 : ℝ) ^ 2 := h_mul_le_A
    have h₂ : (1 + 1 + 1 : ℝ) ^ 2 ≤ ((1 : ℝ) ^ 2 / ((x + y) / 2) + (1 : ℝ) ^ 2 / ((y + z) / 2) + (1 : ℝ) ^ 2 / ((z + x) / 2)) * ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) := by
      -- Use the given inequality hprod_ge to establish the lower bound
      have h₃ : ((1 + 1 + 1) ^ 2 : ℝ) ≤ ((1 : ℝ) ^ 2 / ((x + y) / 2) + (1 : ℝ) ^ 2 / ((y + z) / 2) + (1 : ℝ) ^ 2 / ((z + x) / 2)) * ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) := hprod_ge
      -- Simplify the expression to match the form in hprod_ge
      norm_num at h₃ ⊢
      <;>
      (try linarith) <;>
      (try assumption) <;>
      (try ring_nf at h₃ ⊢ <;> linarith)
      <;>
      (try nlinarith)
    -- Combine the two inequalities using transitivity
    linarith
  
  exact h_main

theorem hprod'_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (hprod_ge :
      ((1 + 1 + 1) ^ 2) ≤
        ((1 : ℝ) ^ 2 / ((x + y) / 2) +
          (1 : ℝ) ^ 2 / ((y + z) / 2) +
          (1 : ℝ) ^ 2 / ((z + x) / 2)) *
          ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) :
    ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) *
        ((1 + 1 + 1) ^ 2 / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) ≤
        ((1 : ℝ) ^ 2 / ((x + y) / 2) +
          (1 : ℝ) ^ 2 / ((y + z) / 2) +
          (1 : ℝ) ^ 2 / ((z + x) / 2)) *
        ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) := by
  have hS_def :
      ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) =
        ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) :=
    (hS_def_hprod'_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z)
  have hA_def :
      ((1 + 1 + 1) ^ 2) = ((1 + 1 + 1) ^ 2) :=
    (hA_def_hprod'_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z)
  have h_mul_le_A :
      ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) *
        ((1 + 1 + 1) ^ 2 / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) ≤
        (1 + 1 + 1) ^ 2 :=
    (h_mul_le_A_hprod'_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z)
  have h_final :
      ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) *
        ((1 + 1 + 1) ^ 2 / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) ≤
        ((1 : ℝ) ^ 2 / ((x + y) / 2) +
          (1 : ℝ) ^ 2 / ((y + z) / 2) +
          (1 : ℝ) ^ 2 / ((z + x) / 2)) *
          ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) :=
    (h_final_hprod'_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z
      h_mul_le_A hprod_ge)
  exact h_final

theorem hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (hSpos' :
      0 < ((x + y) / 2 + (y + z) / 2 + (z + x) / 2))
    (hprod_ge :
      ((1 + 1 + 1) ^ 2) ≤
        ((1 : ℝ) ^ 2 / ((x + y) / 2) +
          (1 : ℝ) ^ 2 / ((y + z) / 2) +
          (1 : ℝ) ^ 2 / ((z + x) / 2)) *
          ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) :
    ( (1 + 1 + 1) ^ 2 ) / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) ≤
      ((1 : ℝ) ^ 2 / ((x + y) / 2) +
        (1 : ℝ) ^ 2 / ((y + z) / 2) +
        (1 : ℝ) ^ 2 / ((z + x) / 2)) := by
  -- positivity of the denominator
  have hSpos :
      0 < ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) :=
    hSpos_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hSpos'
  -- the denominator is non‑zero
  have hSne :
      ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) ≠ 0 :=
    hSne_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hSpos
  -- rewrite the product inequality so that the left side contains the factor `S`
  have hprod' :
      ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) *
        ((1 + 1 + 1) ^ 2 / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) ≤
        ((1 : ℝ) ^ 2 / ((x + y) / 2) +
          (1 : ℝ) ^ 2 / ((y + z) / 2) +
          (1 : ℝ) ^ 2 / ((z + x) / 2)) *
        ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) :=
    hprod'_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hprod_ge
  -- put the inequality in the exact shape required by `le_of_mul_le_mul_left`
  have hbc :
      ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) *
        ((1 + 1 + 1) ^ 2 / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2)) ≤
        ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) *
        ((1 : ℝ) ^ 2 / ((x + y) / 2) +
          (1 : ℝ) ^ 2 / ((y + z) / 2) +
          (1 : ℝ) ^ 2 / ((z + x) / 2)) :=
    hbc_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hprod'
  -- cancel the positive factor `S` and obtain the desired inequality
  have hfinal :
      ((1 + 1 + 1) ^ 2) / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) ≤
        ((1 : ℝ) ^ 2 / ((x + y) / 2) +
          (1 : ℝ) ^ 2 / ((y + z) / 2) +
          (1 : ℝ) ^ 2 / ((z + x) / 2)) :=
    hfinal_hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hSpos hbc
  exact hfinal

theorem hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (hSpos :
      0 < ((x + y) / 2 + (y + z) / 2 + (z + x) / 2))
    (hEngel :
      ((1 : ℝ) ^ 2 / ((x + y) / 2) +
        (1 : ℝ) ^ 2 / ((y + z) / 2) +
        (1 : ℝ) ^ 2 / ((z + x) / 2)) *
          ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) ≥
        (1 + 1 + 1) ^ 2) :
    ( (1 + 1 + 1) ^ 2 ) / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) ≤
      ((1 : ℝ) ^ 2 / ((x + y) / 2) +
        (1 : ℝ) ^ 2 / ((y + z) / 2) +
        (1 : ℝ) ^ 2 / ((z + x) / 2)) := by
  have hSpos' :
      0 < ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) :=
    hSpos'_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hSpos
  have hprod_ge :
      ((1 + 1 + 1) ^ 2) ≤
        ((1 : ℝ) ^ 2 / ((x + y) / 2) +
          (1 : ℝ) ^ 2 / ((y + z) / 2) +
          (1 : ℝ) ^ 2 / ((z + x) / 2)) *
          ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) :=
    hprod_ge_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hEngel
  have hfinal :
      ( (1 + 1 + 1) ^ 2 ) / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) ≤
        ((1 : ℝ) ^ 2 / ((x + y) / 2) +
          (1 : ℝ) ^ 2 / ((y + z) / 2) +
          (1 : ℝ) ^ 2 / ((z + x) / 2)) :=
    hfinal_hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hSpos' hprod_ge
  exact hfinal

theorem hb2_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hpos2 : 0 < (y + z) / 2) :
    0 < (y + z) / 2 := by
  exact hpos2

theorem hb3_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hpos3 : 0 < (z + x) / 2) :
    0 < (z + x) / 2 := by
  exact hpos3

theorem hb1_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hpos1 : 0 < (x + y) / 2) :
    0 < (x + y) / 2 := by
  -- The statement to prove is exactly the hypothesis `hpos1`, so we can directly use it.
  exact hpos1

theorem a1_pos_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hb1 : 0 < (x + y) / 2) :
    0 < (x + y) / 2 := by
  -- The goal is exactly the hypothesis hb1, so we can directly use it.
  exact hb1

theorem a2_pos_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hb2 : 0 < (y + z) / 2) :
    0 < (y + z) / 2 := by
  -- The hypothesis `hb2` directly states that `(y + z) / 2 > 0`, so we can use it directly.
  exact hb2

theorem a3_pos_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (hb3 : 0 < (z + x) / 2) :
    0 < (z + x) / 2 := by
  -- The hypothesis `hb3` directly states that `(z + x) / 2 > 0`, so we can use it directly to prove the goal.
  exact hb3

theorem hCS_right_two_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (a1 a2 a3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) :
    (∑ i : Fin 3,
        (Real.sqrt (match i with
          | 0 => a1
          | 1 => a2
          | 2 => a3
        )) ^ 2) = a1 + a2 + a3 := by
  simp [Fin.sum_univ_succ]
  <;>
  (try norm_num) <;>
  (try
    {
      simp [Real.sqrt_sq, ha1.le, ha2.le, ha3.le]
      <;>
      ring_nf
      <;>
      norm_num
      <;>
      linarith
    }) <;>
  (try
    {
      simp_all [Real.sqrt_sq, Fin.forall_fin_succ, Fin.sum_univ_succ]
      <;>
      ring_nf
      <;>
      norm_num
      <;>
      linarith
    })
  <;>
  (try
    {
      norm_num [Fin.sum_univ_succ] at *
      <;>
      simp_all [Real.sqrt_sq, ha1.le, ha2.le, ha3.le]
      <;>
      ring_nf
      <;>
      norm_num
      <;>
      linarith
    })

theorem hCS_left_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (a1 a2 a3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) :
    (∑ i : Fin 3,
        (1 / Real.sqrt (match i with
          | 0 => a1
          | 1 => a2
          | 2 => a3
        )) *
        Real.sqrt (match i with
          | 0 => a1
          | 1 => a2
          | 2 => a3
        )) = (3 : ℝ) := by
  have h₁ : (∑ i : Fin 3,
        (1 / Real.sqrt (match i with
          | 0 => a1
          | 1 => a2
          | 2 => a3
        )) *
        Real.sqrt (match i with
          | 0 => a1
          | 1 => a2
          | 2 => a3
        )) = 3 := by
    -- Simplify each term in the sum
    have h₂ : (∑ i : Fin 3,
        (1 / Real.sqrt (match i with
          | 0 => a1
          | 1 => a2
          | 2 => a3
        )) *
        Real.sqrt (match i with
          | 0 => a1
          | 1 => a2
          | 2 => a3
        )) = (1 / Real.sqrt a1 * Real.sqrt a1) + (1 / Real.sqrt a2 * Real.sqrt a2) + (1 / Real.sqrt a3 * Real.sqrt a3) := by
      -- Expand the sum over Fin 3
      simp [Fin.sum_univ_succ, Fin.val_zero, Fin.val_one, Fin.val_two]
      <;>
      (try norm_num) <;>
      (try ring_nf) <;>
      (try field_simp) <;>
      (try norm_num) <;>
      (try linarith)
      <;>
      (try simp_all [Fin.forall_fin_succ])
      <;>
      (try norm_num)
      <;>
      (try ring_nf)
      <;>
      (try field_simp)
      <;>
      (try norm_num)
      <;>
      (try linarith)
    rw [h₂]
    -- Simplify each term using the property 1 / sqrt(x) * sqrt(x) = 1
    have h₃ : 1 / Real.sqrt a1 * Real.sqrt a1 = 1 := by
      have h₄ : Real.sqrt a1 > 0 := Real.sqrt_pos.mpr ha1
      field_simp [h₄.ne']
      <;>
      ring_nf
      <;>
      field_simp [h₄.ne']
      <;>
      linarith
    have h₄ : 1 / Real.sqrt a2 * Real.sqrt a2 = 1 := by
      have h₅ : Real.sqrt a2 > 0 := Real.sqrt_pos.mpr ha2
      field_simp [h₅.ne']
      <;>
      ring_nf
      <;>
      field_simp [h₅.ne']
      <;>
      linarith
    have h₅ : 1 / Real.sqrt a3 * Real.sqrt a3 = 1 := by
      have h₆ : Real.sqrt a3 > 0 := Real.sqrt_pos.mpr ha3
      field_simp [h₆.ne']
      <;>
      ring_nf
      <;>
      field_simp [h₆.ne']
      <;>
      linarith
    -- Sum the simplified terms
    linarith
  -- The final result
  exact h₁

theorem hCS_right_one_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (a1 a2 a3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) :
    (∑ i : Fin 3,
        (1 / Real.sqrt (match i with
          | 0 => a1
          | 1 => a2
          | 2 => a3
        )) ^ 2) = (1 / a1) + (1 / a2) + (1 / a3) := by
  have h₁ : (∑ i : Fin 3, (1 / Real.sqrt (match i with | 0 => a1 | 1 => a2 | 2 => a3)) ^ 2) = (1 / Real.sqrt a1) ^ 2 + (1 / Real.sqrt a2) ^ 2 + (1 / Real.sqrt a3) ^ 2 := by
    simp [Fin.sum_univ_succ]
    <;> ring_nf
    <;> norm_num
    <;> rfl
  
  rw [h₁]
  have h₂ : (1 / Real.sqrt a1) ^ 2 = 1 / a1 := by
    have h₂₁ : 0 < a1 := ha1
    have h₂₂ : 0 < Real.sqrt a1 := Real.sqrt_pos.mpr h₂₁
    have h₂₃ : (Real.sqrt a1) ^ 2 = a1 := Real.sq_sqrt (le_of_lt h₂₁)
    calc
      (1 / Real.sqrt a1) ^ 2 = 1 / (Real.sqrt a1) ^ 2 := by
        field_simp [h₂₂.ne']
        <;> ring_nf
      _ = 1 / a1 := by rw [h₂₃]
  
  have h₃ : (1 / Real.sqrt a2) ^ 2 = 1 / a2 := by
    have h₃₁ : 0 < a2 := ha2
    have h₃₂ : 0 < Real.sqrt a2 := Real.sqrt_pos.mpr h₃₁
    have h₃₃ : (Real.sqrt a2) ^ 2 = a2 := Real.sq_sqrt (le_of_lt h₃₁)
    calc
      (1 / Real.sqrt a2) ^ 2 = 1 / (Real.sqrt a2) ^ 2 := by
        field_simp [h₃₂.ne']
        <;> ring_nf
      _ = 1 / a2 := by rw [h₃₃]
  
  have h₄ : (1 / Real.sqrt a3) ^ 2 = 1 / a3 := by
    have h₄₁ : 0 < a3 := ha3
    have h₄₂ : 0 < Real.sqrt a3 := Real.sqrt_pos.mpr h₄₁
    have h₄₃ : (Real.sqrt a3) ^ 2 = a3 := Real.sq_sqrt (le_of_lt h₄₁)
    calc
      (1 / Real.sqrt a3) ^ 2 = 1 / (Real.sqrt a3) ^ 2 := by
        field_simp [h₄₂.ne']
        <;> ring_nf
      _ = 1 / a3 := by rw [h₄₃]
  
  rw [h₂, h₃, h₄]
  <;> ring_nf

theorem hCS_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy
    (a1 a2 a3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) :
    (∑ i : Fin 3,
        (1 / Real.sqrt (match i with
          | 0 => a1
          | 1 => a2
          | 2 => a3
        )) *
        Real.sqrt (match i with
          | 0 => a1
          | 1 => a2
          | 2 => a3
        )) ^ 2
      ≤
      (∑ i : Fin 3,
          (1 / Real.sqrt (match i with
            | 0 => a1
            | 1 => a2
            | 2 => a3
          )) ^ 2) *
      (∑ i : Fin 3,
          (Real.sqrt (match i with
            | 0 => a1
            | 1 => a2
            | 2 => a3
          )) ^ 2) := by
  classical
  simpa using
    (Finset.sum_mul_sq_le_sq_mul_sq
      (s := (Finset.univ : Finset (Fin 3)))
      (f := fun i : Fin 3 =>
        (1 / Real.sqrt (match i with
          | 0 => a1
          | 1 => a2
          | 2 => a3)))
      (g := fun i : Fin 3 =>
        Real.sqrt (match i with
          | 0 => a1
          | 1 => a2
          | 2 => a3)))

theorem h_pos_sum_hineq_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (a1 a2 a3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) :
    0 < a1 + a2 + a3 := by
  have h1 : 0 < a1 + a2 := by linarith
  have h2 : 0 < a1 + a2 + a3 := by linarith
  linarith

theorem h_mul_hineq_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (a1 a2 a3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (h_titu : ((1 : ℝ) / a1 + (1 : ℝ) / a2 + (1 : ℝ) / a3) ≥ (1 + 1 + 1) ^ 2 / (a1 + a2 + a3))
    (h_pos_sum : 0 < a1 + a2 + a3) :
    ((1 : ℝ) / a1 + (1 : ℝ) / a2 + (1 : ℝ) / a3) * (a1 + a2 + a3) ≥ (1 + 1 + 1) ^ 2 := by
  have h₁ : ((1 : ℝ) / a1 + (1 : ℝ) / a2 + (1 : ℝ) / a3) * (a1 + a2 + a3) ≥ (1 + 1 + 1) ^ 2 := by
    calc
      ((1 : ℝ) / a1 + (1 : ℝ) / a2 + (1 : ℝ) / a3) * (a1 + a2 + a3) ≥ ((1 + 1 + 1) ^ 2 / (a1 + a2 + a3)) * (a1 + a2 + a3) := by
        -- Use the given inequality to bound the left side from below
        gcongr <;>
        (try norm_num) <;>
        (try linarith) <;>
        (try positivity)
      _ = (1 + 1 + 1) ^ 2 := by
        -- Simplify the right side
        have h₂ : (a1 + a2 + a3) ≠ 0 := by linarith
        field_simp [h₂]
        <;> ring_nf
        <;> norm_num
        <;> linarith
  exact h₁

theorem h_titu_hineq_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy
    (a1 a2 a3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) :
    ((1 : ℝ) / a1 + (1 : ℝ) / a2 + (1 : ℝ) / a3) ≥ (1 + 1 + 1) ^ 2 / (a1 + a2 + a3) := by
  -- each denominator is positive
  have hpos : ∀ i : Fin 3, (0 : ℝ) < (![a1, a2, a3] i) := by
    intro i
    fin_cases i
    · simpa using ha1
    · simpa using ha2
    · simpa using ha3
  -- apply Titu's (Engel's) lemma to the three terms
  have h :=
    (Finset.sq_sum_div_le_sum_sq_div
        (s := (Finset.univ : Finset (Fin 3)))
        (f := fun _ : Fin 3 => (1 : ℝ))
        (g := fun i => (![a1, a2, a3] i))
        (hg := by
          intro i hi
          exact hpos i))
  -- rewrite the result of the lemma
  have h' : (3 : ℝ) ^ 2 / (a1 + a2 + a3) ≤ (1 / a1 + 1 / a2 + 1 / a3) := by
    simpa [Finset.card_univ, Finset.sum_const, Fin.sum_univ_three] using h
  -- identify `1+1+1` with `3` and finish
  have h_one_three : (1 + 1 + 1 : ℝ) = 3 := by norm_num
  simpa [ge_iff_le, h_one_three] using h'

theorem hineq_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy
    (a1 a2 a3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) :
    ((1 : ℝ) / a1 + (1 : ℝ) / a2 + (1 : ℝ) / a3) * (a1 + a2 + a3) ≥ (1 + 1 + 1) ^ 2 := by
  have h_titu :
      ((1 : ℝ) / a1 + (1 : ℝ) / a2 + (1 : ℝ) / a3) ≥
        (1 + 1 + 1) ^ 2 / (a1 + a2 + a3) :=
    h_titu_hineq_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy a1 a2 a3 ha1 ha2 ha3
  have h_pos_sum : 0 < a1 + a2 + a3 :=
    h_pos_sum_hineq_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy a1 a2 a3 ha1 ha2 ha3
  have h_mul :
      ((1 : ℝ) / a1 + (1 : ℝ) / a2 + (1 : ℝ) / a3) * (a1 + a2 + a3) ≥
        (1 + 1 + 1) ^ 2 :=
    h_mul_hineq_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy a1 a2 a3 ha1 ha2 ha3 h_titu h_pos_sum
  exact h_mul

theorem h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (hb1 : 0 < (x + y) / 2) (hb2 : 0 < (y + z) / 2) (hb3 : 0 < (z + x) / 2) :
    ((1 : ℝ) ^ 2 / ((x + y) / 2) +
      (1 : ℝ) ^ 2 / ((y + z) / 2) +
      (1 : ℝ) ^ 2 / ((z + x) / 2)) *
        ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) ≥
      (1 + 1 + 1) ^ 2 := by
  ----------------------------------------------------------------------
  -- 1.  introduce the three positive numbers a₁, a₂, a₃
  ----------------------------------------------------------------------
  have a1_pos : 0 < (x + y) / 2 := by
    exact a1_pos_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hb1
  have a2_pos : 0 < (y + z) / 2 := by
    exact a2_pos_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hb2
  have a3_pos : 0 < (z + x) / 2 := by
    exact a3_pos_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hb3
  set a1 := (x + y) / 2 with ha1_def
  set a2 := (y + z) / 2 with ha2_def
  set a3 := (z + x) / 2 with ha3_def

  ----------------------------------------------------------------------
  -- 2.  apply Cauchy‑Schwarz on the vectors
  --     uᵢ = 1 / √aᵢ ,  vᵢ = √aᵢ   (i = 0,1,2)
  ----------------------------------------------------------------------
  have hCS :
      (∑ i : Fin 3,
          (1 / Real.sqrt (match i with
            | 0 => a1
            | 1 => a2
            | 2 => a3
          )) *
          Real.sqrt (match i with
            | 0 => a1
            | 1 => a2
            | 2 => a3
          )) ^ 2
        ≤
        (∑ i : Fin 3,
            (1 / Real.sqrt (match i with
              | 0 => a1
              | 1 => a2
              | 2 => a3
            )) ^ 2) *
        (∑ i : Fin 3,
            (Real.sqrt (match i with
              | 0 => a1
              | 1 => a2
              | 2 => a3
            )) ^ 2) := by
    exact hCS_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy a1 a2 a3 a1_pos a2_pos a3_pos
  ----------------------------------------------------------------------
  -- 3.  simplify the left‑hand side of the C‑S inequality
  ----------------------------------------------------------------------
  have hCS_left :
      (∑ i : Fin 3,
          (1 / Real.sqrt (match i with
            | 0 => a1
            | 1 => a2
            | 2 => a3
          )) *
          Real.sqrt (match i with
            | 0 => a1
            | 1 => a2
            | 2 => a3
          )) = (3 : ℝ) := by
    exact hCS_left_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy a1 a2 a3 a1_pos a2_pos a3_pos
  ----------------------------------------------------------------------
  -- 4.  rewrite the two sums of squares appearing on the right‑hand side
  ----------------------------------------------------------------------
  have hCS_right_one :
      (∑ i : Fin 3,
          (1 / Real.sqrt (match i with
            | 0 => a1
            | 1 => a2
            | 2 => a3
          )) ^ 2) = (1 / a1) + (1 / a2) + (1 / a3) := by
    exact hCS_right_one_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy a1 a2 a3 a1_pos a2_pos a3_pos
  have hCS_right_two :
      (∑ i : Fin 3,
          (Real.sqrt (match i with
            | 0 => a1
            | 1 => a2
            | 2 => a3
          )) ^ 2) = a1 + a2 + a3 := by
    exact hCS_right_two_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy a1 a2 a3 a1_pos a2_pos a3_pos
  ----------------------------------------------------------------------
  -- 5.  combine the previous facts to obtain the desired inequality
  ----------------------------------------------------------------------
  have hineq :
      ((1 : ℝ) / a1 + (1 : ℝ) / a2 + (1 : ℝ) / a3) * (a1 + a2 + a3) ≥ (1 + 1 + 1) ^ 2 := by
    exact hineq_h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy a1 a2 a3 a1_pos a2_pos a3_pos
  ----------------------------------------------------------------------
  -- 6.  rewrite everything back in the original notation
  ----------------------------------------------------------------------
  simpa [ha1_def, ha2_def, ha3_def, pow_two, mul_comm, mul_left_comm, mul_assoc,
        add_comm, add_left_comm, add_assoc] using hineq

theorem hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (hpos1 : 0 < (x + y) / 2) (hpos2 : 0 < (y + z) / 2) (hpos3 : 0 < (z + x) / 2) :
    ((1 : ℝ) ^ 2 / ((x + y) / 2) +
      (1 : ℝ) ^ 2 / ((y + z) / 2) +
      (1 : ℝ) ^ 2 / ((z + x) / 2)) *
        ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) ≥
      (1 + 1 + 1) ^ 2 := by
  have hb1 : 0 < (x + y) / 2 := by
    exact hb1_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hpos1
  have hb2 : 0 < (y + z) / 2 := by
    exact hb2_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hpos2
  have hb3 : 0 < (z + x) / 2 := by
    exact hb3_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hpos3
  have h_goal :
      ((1 : ℝ) ^ 2 / ((x + y) / 2) +
        (1 : ℝ) ^ 2 / ((y + z) / 2) +
        (1 : ℝ) ^ 2 / ((z + x) / 2)) *
        ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) ≥
        (1 + 1 + 1) ^ 2 :=
    h_goal_hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hb1 hb2 hb3
  exact h_goal

theorem h_engel_h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (hb1 : 0 < (x + y) / 2) (hb2 : 0 < (y + z) / 2) (hb3 : 0 < (z + x) / 2) :
    ( (1 : ℝ) ^ 2 / ((x + y) / 2) +
      (1 : ℝ) ^ 2 / ((y + z) / 2) +
      (1 : ℝ) ^ 2 / ((z + x) / 2) ) ≥
    ( (1 + 1 + 1) ^ 2 ) / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) := by
  have hpos1 : 0 < (x + y) / 2 := by
    exact hpos1_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y hb1
  have hpos2 : 0 < (y + z) / 2 := by
    exact hpos2_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy y z hb2
  have hpos3 : 0 < (z + x) / 2 := by
    exact hpos3_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy z x hb3
  have hSpos :
      0 < ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) := by
    exact hSpos_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hpos1 hpos2 hpos3
  have hEngel :
      ((1 : ℝ) ^ 2 / ((x + y) / 2) +
        (1 : ℝ) ^ 2 / ((y + z) / 2) +
        (1 : ℝ) ^ 2 / ((z + x) / 2)) *
        ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) ≥
        (1 + 1 + 1) ^ 2 := by
    exact hEngel_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hpos1 hpos2 hpos3
  have hDiv :
      ( (1 + 1 + 1) ^ 2 ) / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) ≤
        ((1 : ℝ) ^ 2 / ((x + y) / 2) +
          (1 : ℝ) ^ 2 / ((y + z) / 2) +
          (1 : ℝ) ^ 2 / ((z + x) / 2)) := by
    exact hDiv_h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hSpos hEngel
  exact hDiv

theorem h_engel_algebra_9onxpypzleqsum2onxpy (x y z : ℝ)
    (hb1_pos : 0 < (x + y) / 2) (hb2_pos : 0 < (y + z) / 2) (hb3_pos : 0 < (z + x) / 2) :
    ( (1 : ℝ) ^ 2 / ((x + y) / 2) +
      (1 : ℝ) ^ 2 / ((y + z) / 2) +
      (1 : ℝ) ^ 2 / ((z + x) / 2) ) ≥
    ( (1 + 1 + 1) ^ 2 ) /
      ( (x + y) / 2 + (y + z) / 2 + (z + x) / 2 ) := by
  have hb1 : 0 < (x + y) / 2 := by
    exact hb1_h_engel_algebra_9onxpypzleqsum2onxpy x y z hb1_pos
  have hb2 : 0 < (y + z) / 2 := by
    exact hb2_h_engel_algebra_9onxpypzleqsum2onxpy x y z hb2_pos
  have hb3 : 0 < (z + x) / 2 := by
    exact hb3_h_engel_algebra_9onxpypzleqsum2onxpy x y z hb3_pos
  have hsum_den : (x + y) / 2 + (y + z) / 2 + (z + x) / 2 = x + y + z := by
    exact hsum_den_h_engel_algebra_9onxpypzleqsum2onxpy x y z
  have h_engel :
      ( (1 : ℝ) ^ 2 / ((x + y) / 2) +
        (1 : ℝ) ^ 2 / ((y + z) / 2) +
        (1 : ℝ) ^ 2 / ((z + x) / 2) ) ≥
      ( (1 + 1 + 1) ^ 2 ) / ((x + y) / 2 + (y + z) / 2 + (z + x) / 2) := by
    exact h_engel_h_engel_algebra_9onxpypzleqsum2onxpy x y z hb1 hb2 hb3
  simpa [pow_two] using h_engel

theorem algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
    9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  -- positivity of the variables
  have hx : 0 < x := by
    exact hx_algebra_9onxpypzleqsum2onxpy x y z h₀
  have hy : 0 < y := by
    exact hy_algebra_9onxpypzleqsum2onxpy x y z h₀
  have hz : 0 < z := by
    exact hz_algebra_9onxpypzleqsum2onxpy x y z h₀
  -- positivity of the pairwise sums
  have hxy_pos : 0 < x + y := by
    exact hxy_pos_algebra_9onxpypzleqsum2onxpy x y z hx hy
  have hyz_pos : 0 < y + z := by
    exact hyz_pos_algebra_9onxpypzleqsum2onxpy x y z hy hz
  have hzx_pos : 0 < z + x := by
    exact hzx_pos_algebra_9onxpypzleqsum2onxpy x y z hz hx
  -- positivity of the total sum
  have hsum_pos : 0 < x + y + z := by
    exact hsum_pos_algebra_9onxpypzleqsum2onxpy x y z hx hy hz
  -- auxiliary positive numbers (half of the pairwise sums)
  have hb1_pos : 0 < (x + y) / 2 := by
    exact hb1_pos_algebra_9onxpypzleqsum2onxpy x y z hxy_pos
  have hb2_pos : 0 < (y + z) / 2 := by
    exact hb2_pos_algebra_9onxpypzleqsum2onxpy x y z hyz_pos
  have hb3_pos : 0 < (z + x) / 2 := by
    exact hb3_pos_algebra_9onxpypzleqsum2onxpy x y z hzx_pos
  -- Engel (Titu’s) inequality for the chosen data
  have h_engel :
      ( (1 : ℝ) ^ 2 / ((x + y) / 2) +
        (1 : ℝ) ^ 2 / ((y + z) / 2) +
        (1 : ℝ) ^ 2 / ((z + x) / 2) ) ≥
      ( (1 + 1 + 1) ^ 2 ) /
        ( (x + y) / 2 + (y + z) / 2 + (z + x) / 2 ) := by
    exact h_engel_algebra_9onxpypzleqsum2onxpy x y z hb1_pos hb2_pos hb3_pos
  -- simplify the left‑hand side of `h_engel`
  have h_left :
      ( (1 : ℝ) ^ 2 / ((x + y) / 2) +
        (1 : ℝ) ^ 2 / ((y + z) / 2) +
        (1 : ℝ) ^ 2 / ((z + x) / 2) ) =
      2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
    exact h_left_algebra_9onxpypzleqsum2onxpy x y z
  -- simplify the right‑hand side of `h_engel`
  have h_right :
      ( (1 + 1 + 1) ^ 2 ) /
        ( (x + y) / 2 + (y + z) / 2 + (z + x) / 2 ) =
      9 / (x + y + z) := by
    exact h_right_algebra_9onxpypzleqsum2onxpy x y z
  -- combine the previous results to obtain the desired inequality
  have h_final : 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
    exact h_final_algebra_9onxpypzleqsum2onxpy x y z h_left h_right h_engel
  exact h_final

import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h_abs_nonneg_a_algebra_absapbon1pabsapbleqsumabsaon1pabsa (a : ℝ) : (0 : ℝ) ≤ abs a := by
  exact abs_nonneg a

theorem h_abs_nonneg_b_algebra_absapbon1pabsapbleqsumabsaon1pabsa (b : ℝ) : (0 : ℝ) ≤ abs b := by
  exact abs_nonneg b

theorem h_abs_add_algebra_absapbon1pabsapbleqsumabsaon1pabsa (a b : ℝ) : abs (a + b) ≤ abs a + abs b := by
  cases' le_total 0 (a + b) with h h <;>
  cases' le_total 0 a with ha ha <;>
  cases' le_total 0 b with hb hb <;>
  simp_all [abs_of_nonneg, abs_of_nonpos, abs_of_neg, le_of_lt] <;>
  (try { nlinarith }) <;>
  (try { linarith }) <;>
  (try { nlinarith [abs_nonneg a, abs_nonneg b] }) <;>
  (try { linarith [abs_nonneg a, abs_nonneg b] })
  <;>
  (try { nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg (a + b)] })
  <;>
  (try { linarith [abs_nonneg a, abs_nonneg b, abs_nonneg (a + b)] })

theorem h_xy_algebra_absapbon1pabsapbleqsumabsaon1pabsa
    (a b : ℝ)
    (h_abs_nonneg_a : (0 : ℝ) ≤ abs a)
    (h_abs_nonneg_b : (0 : ℝ) ≤ abs b) :
    (abs a + abs b) / (1 + (abs a + abs b)) ≤
      abs a / (1 + abs a) + abs b / (1 + abs b) := by
  have h_main : ∀ (x y : ℝ), 0 ≤ x → 0 ≤ y → (x + y) / (1 + x + y) ≤ x / (1 + x) + y / (1 + y) := by
    intro x y hx hy
    have h₁ : 0 ≤ x * y := mul_nonneg hx hy
    have h₂ : 0 ≤ x * y * (2 + x + y) := by
      have h₃ : 0 ≤ 2 + x + y := by linarith
      have h₄ : 0 ≤ x * y := mul_nonneg hx hy
      nlinarith
    have h₃ : 0 < 1 + x := by linarith
    have h₄ : 0 < 1 + y := by linarith
    have h₅ : 0 < 1 + x + y := by linarith
    have h₆ : 0 < (1 + x) * (1 + y) := by positivity
    have h₇ : 0 < (1 + x) * (1 + y) * (1 + x + y) := by positivity
    have h₈ : (x + y) / (1 + x + y) ≤ x / (1 + x) + y / (1 + y) := by
      have h₉ : x / (1 + x) + y / (1 + y) - (x + y) / (1 + x + y) = (x * y * (2 + x + y)) / ((1 + x) * (1 + y) * (1 + x + y)) := by
        field_simp [h₃.ne', h₄.ne', h₅.ne']
        ring
        <;>
        nlinarith
      have h₁₀ : (x * y * (2 + x + y)) / ((1 + x) * (1 + y) * (1 + x + y)) ≥ 0 := by
        apply div_nonneg
        · nlinarith
        · positivity
      linarith
    exact h₈
  
  have h_final : (abs a + abs b) / (1 + (abs a + abs b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
    have h₁ : (abs a + abs b) / (1 + (abs a + abs b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
      have h₂ : 0 ≤ abs a := abs_nonneg a
      have h₃ : 0 ≤ abs b := abs_nonneg b
      have h₄ : (abs a + abs b) / (1 + (abs a + abs b)) = (abs a + abs b) / (1 + abs a + abs b) := by
        ring_nf
      rw [h₄]
      have h₅ : (abs a + abs b) / (1 + abs a + abs b) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
        have h₆ : ∀ (x y : ℝ), 0 ≤ x → 0 ≤ y → (x + y) / (1 + x + y) ≤ x / (1 + x) + y / (1 + y) := h_main
        have h₇ : 0 ≤ abs a := abs_nonneg a
        have h₈ : 0 ≤ abs b := abs_nonneg b
        have h₉ : (abs a + abs b) / (1 + abs a + abs b) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := h₆ (abs a) (abs b) h₇ h₈
        exact h₉
      exact h₅
    exact h₁
  
  exact h_final

theorem h_monotone_algebra_absapbon1pabsapbleqsumabsaon1pabsa
    (a b : ℝ)
    (h_abs_nonneg_a : (0 : ℝ) ≤ abs a)
    (h_abs_nonneg_b : (0 : ℝ) ≤ abs b)
    (h_abs_add : abs (a + b) ≤ abs a + abs b) :
    abs (a + b) / (1 + abs (a + b)) ≤ (abs a + abs b) / (1 + (abs a + abs b)) := by
  -- the denominators are positive, so we can clear them
  have hpos1 : (0 : ℝ) < 1 + abs (a + b) := by
    have : (0 : ℝ) ≤ abs (a + b) := abs_nonneg _
    linarith
  have hpos2 : (0 : ℝ) < 1 + (abs a + abs b) := by
    have : (0 : ℝ) ≤ abs a + abs b := add_nonneg h_abs_nonneg_a h_abs_nonneg_b
    linarith
  have hne1 : (1 + abs (a + b)) ≠ 0 := ne_of_gt hpos1
  have hne2 : (1 + (abs a + abs b)) ≠ 0 := ne_of_gt hpos2
  field_simp [hne1, hne2]
  -- now the goal is a cross‑multiplied inequality
  have hdiff :
      abs (a + b) * (1 + (abs a + abs b)) -
        (abs a + abs b) * (1 + abs (a + b)) =
        abs (a + b) - (abs a + abs b) := by
    ring
  have hle : abs (a + b) - (abs a + abs b) ≤ (0 : ℝ) := by
    exact sub_nonpos.mpr h_abs_add
  have hle' :
      abs (a + b) * (1 + (abs a + abs b)) -
        (abs a + abs b) * (1 + abs (a + b)) ≤ (0 : ℝ) := by
    simpa [hdiff] using hle
  have hineq :
      abs (a + b) * (1 + (abs a + abs b)) ≤ (abs a + abs b) * (1 + abs (a + b)) :=
    sub_nonpos.mp hle'
  simpa [mul_comm, mul_left_comm, mul_assoc] using hineq

theorem algebra_absapbon1pabsapbleqsumabsaon1pabsa (a b : ℝ) :
    abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
  have h_abs_nonneg_a : (0 : ℝ) ≤ abs a :=
    h_abs_nonneg_a_algebra_absapbon1pabsapbleqsumabsaon1pabsa a
  have h_abs_nonneg_b : (0 : ℝ) ≤ abs b :=
    h_abs_nonneg_b_algebra_absapbon1pabsapbleqsumabsaon1pabsa b
  have h_abs_add : abs (a + b) ≤ abs a + abs b :=
    h_abs_add_algebra_absapbon1pabsapbleqsumabsaon1pabsa a b
  have h_monotone :
      abs (a + b) / (1 + abs (a + b)) ≤ (abs a + abs b) / (1 + (abs a + abs b)) :=
    h_monotone_algebra_absapbon1pabsapbleqsumabsaon1pabsa a b h_abs_nonneg_a h_abs_nonneg_b h_abs_add
  have h_xy :
      (abs a + abs b) / (1 + (abs a + abs b)) ≤
        abs a / (1 + abs a) + abs b / (1 + abs b) :=
    h_xy_algebra_absapbon1pabsapbleqsumabsaon1pabsa a b h_abs_nonneg_a h_abs_nonneg_b
  calc
    abs (a + b) / (1 + abs (a + b))
        ≤ (abs a + abs b) / (1 + (abs a + abs b)) := h_monotone
    _ ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := h_xy

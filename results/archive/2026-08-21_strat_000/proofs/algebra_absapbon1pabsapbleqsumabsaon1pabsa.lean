import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h0a_algebra_absapbon1pabsapbleqsumabsaon1pabsa (a b : ℝ) : (0 : ℝ) ≤ abs a := by
  apply abs_nonneg

theorem h0b_algebra_absapbon1pabsapbleqsumabsaon1pabsa (a b : ℝ) : (0 : ℝ) ≤ abs b := by
  exact abs_nonneg b

theorem h0_algebra_absapbon1pabsapbleqsumabsaon1pabsa (a b : ℝ) : (0 : ℝ) ≤ abs (a + b) := by
  -- Use the property that the absolute value of any real number is non-negative.
  exact abs_nonneg (a + b)

theorem hle_abs_algebra_absapbon1pabsapbleqsumabsaon1pabsa (a b : ℝ) : abs (a + b) ≤ abs a + abs b := by
  cases' le_total 0 (a + b) with h h <;>
  cases' le_total 0 a with ha ha <;>
  cases' le_total 0 b with hb hb <;>
  simp_all [abs_of_nonneg, abs_of_nonpos, abs_of_neg, le_of_lt] <;>
  (try { nlinarith }) <;>
  (try { linarith }) <;>
  (try { nlinarith [abs_nonneg a, abs_nonneg b] }) <;>
  (try { linarith [abs_nonneg a, abs_nonneg b] })

theorem hmono_algebra_absapbon1pabsapbleqsumabsaon1pabsa (a b : ℝ)
    (h0 : (0 : ℝ) ≤ abs (a + b))
    (h0a : (0 : ℝ) ≤ abs a)
    (h0b : (0 : ℝ) ≤ abs b)
    (hle_abs : abs (a + b) ≤ abs a + abs b) :
    abs (a + b) / (1 + abs (a + b)) ≤
      (abs a + abs b) / (1 + (abs a + abs b)) := by
  -- positivity of the denominators
  have hpos1 : (0 : ℝ) < 1 + abs (a + b) := by
    have : (0 : ℝ) ≤ abs (a + b) := h0
    exact add_pos_of_pos_of_nonneg (by norm_num) this
  have hpos2 : (0 : ℝ) < 1 + (abs a + abs b) := by
    have : (0 : ℝ) ≤ abs a + abs b := add_nonneg h0a h0b
    exact add_pos_of_pos_of_nonneg (by norm_num) this
  -- clear denominators
  field_simp [hpos1.ne', hpos2.ne'] 
  -- now the goal is a polynomial inequality
  have h_nonneg1 : 0 ≤ 1 + (abs a + abs b) := le_of_lt hpos2
  have h_nonneg2 : 0 ≤ 1 + abs (a + b) := le_of_lt hpos1
  have hle : abs (a + b) ≤ abs a + abs b := hle_abs
  nlinarith

theorem hsplit_algebra_absapbon1pabsapbleqsumabsaon1pabsa (a b : ℝ)
    (h0a : (0 : ℝ) ≤ abs a)
    (h0b : (0 : ℝ) ≤ abs b) :
    (abs a + abs b) / (1 + (abs a + abs b)) ≤
      abs a / (1 + abs a) + abs b / (1 + abs b) := by
  have h_main : ∀ (x y : ℝ), 0 ≤ x → 0 ≤ y → (x + y) / (1 + x + y) ≤ x / (1 + x) + y / (1 + y) := by
    intro x y hx hy
    have h₁ : 0 ≤ x * y := mul_nonneg hx hy
    have h₂ : 0 < 1 + x := by linarith
    have h₃ : 0 < 1 + y := by linarith
    have h₄ : 0 < 1 + x + y := by linarith
    have h₅ : 0 < (1 + x) * (1 + x + y) := by positivity
    have h₆ : 0 < (1 + y) * (1 + x + y) := by positivity
    have h₇ : 0 ≤ x * y / ((1 + x) * (1 + x + y)) := by positivity
    have h₈ : 0 ≤ x * y / ((1 + y) * (1 + x + y)) := by positivity
    have h₉ : x / (1 + x) + y / (1 + y) - (x + y) / (1 + x + y) = x * y / ((1 + x) * (1 + x + y)) + x * y / ((1 + y) * (1 + x + y)) := by
      have h₉₁ : x / (1 + x) - x / (1 + x + y) = x * y / ((1 + x) * (1 + x + y)) := by
        have h₉₁₁ : x / (1 + x) - x / (1 + x + y) = (x * (1 + x + y) - x * (1 + x)) / ((1 + x) * (1 + x + y)) := by
          field_simp [h₂.ne', h₄.ne']
          <;> ring
          <;> field_simp [h₂.ne', h₄.ne']
          <;> ring
        rw [h₉₁₁]
        have h₉₁₂ : x * (1 + x + y) - x * (1 + x) = x * y := by ring
        rw [h₉₁₂]
        <;> field_simp [h₂.ne', h₄.ne']
        <;> ring
      have h₉₂ : y / (1 + y) - y / (1 + x + y) = x * y / ((1 + y) * (1 + x + y)) := by
        have h₉₂₁ : y / (1 + y) - y / (1 + x + y) = (y * (1 + x + y) - y * (1 + y)) / ((1 + y) * (1 + x + y)) := by
          field_simp [h₃.ne', h₄.ne']
          <;> ring
          <;> field_simp [h₃.ne', h₄.ne']
          <;> ring
        rw [h₉₂₁]
        have h₉₂₂ : y * (1 + x + y) - y * (1 + y) = x * y := by ring
        rw [h₉₂₂]
        <;> field_simp [h₃.ne', h₄.ne']
        <;> ring
      calc
        x / (1 + x) + y / (1 + y) - (x + y) / (1 + x + y) = (x / (1 + x) - x / (1 + x + y)) + (y / (1 + y) - y / (1 + x + y)) := by
          ring
        _ = x * y / ((1 + x) * (1 + x + y)) + x * y / ((1 + y) * (1 + x + y)) := by
          rw [h₉₁, h₉₂]
          <;> ring
    have h₁₀ : x / (1 + x) + y / (1 + y) - (x + y) / (1 + x + y) ≥ 0 := by
      rw [h₉]
      have h₁₀₁ : 0 ≤ x * y / ((1 + x) * (1 + x + y)) := by positivity
      have h₁₀₂ : 0 ≤ x * y / ((1 + y) * (1 + x + y)) := by positivity
      linarith
    linarith
  
  have h_final : (abs a + abs b) / (1 + (abs a + abs b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
    have h₁ : (abs a + abs b) / (1 + (abs a + abs b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
      have h₂ : 0 ≤ abs a := h0a
      have h₃ : 0 ≤ abs b := h0b
      have h₄ : (abs a + abs b) / (1 + (abs a + abs b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
        have h₅ : (abs a + abs b) / (1 + (abs a + abs b)) = (abs a + abs b) / (1 + abs a + abs b) := by
          ring_nf
        rw [h₅]
        have h₆ : abs a / (1 + abs a) + abs b / (1 + abs b) = abs a / (1 + abs a) + abs b / (1 + abs b) := rfl
        have h₇ : (abs a + abs b) / (1 + abs a + abs b) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
          -- Use the main lemma to prove the inequality
          have h₈ : (abs a + abs b) / (1 + abs a + abs b) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
            have h₉ : 0 ≤ abs a := h0a
            have h₁₀ : 0 ≤ abs b := h0b
            have h₁₁ : (abs a + abs b) / (1 + abs a + abs b) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
              -- Apply the main lemma with x = abs a and y = abs b
              have h₁₂ := h_main (abs a) (abs b) h₉ h₁₀
              -- Simplify the expression to match the form in the main lemma
              have h₁₃ : (abs a + abs b) / (1 + (abs a) + (abs b)) ≤ (abs a) / (1 + (abs a)) + (abs b) / (1 + (abs b)) := by
                simpa [add_assoc] using h₁₂
              -- The above line is a direct application of the main lemma
              simpa [add_assoc] using h₁₃
            exact h₁₁
          exact h₈
        exact h₇
      exact h₄
    exact h₁
  
  exact h_final

theorem algebra_absapbon1pabsapbleqsumabsaon1pabsa (a b : ℝ) :
    abs (a + b) / (1 + abs (a + b)) ≤
      abs a / (1 + abs a) + abs b / (1 + abs b) := by
  have h0 : (0 : ℝ) ≤ abs (a + b) := by
    simpa using h0_algebra_absapbon1pabsapbleqsumabsaon1pabsa a b
  have h0a : (0 : ℝ) ≤ abs a := by
    simpa using h0a_algebra_absapbon1pabsapbleqsumabsaon1pabsa a b
  have h0b : (0 : ℝ) ≤ abs b := by
    simpa using h0b_algebra_absapbon1pabsapbleqsumabsaon1pabsa a b
  have hle_abs : abs (a + b) ≤ abs a + abs b := by
    simpa using hle_abs_algebra_absapbon1pabsapbleqsumabsaon1pabsa a b
  have hmono :
      abs (a + b) / (1 + abs (a + b)) ≤
        (abs a + abs b) / (1 + (abs a + abs b)) := by
    simpa using
      hmono_algebra_absapbon1pabsapbleqsumabsaon1pabsa a b h0 h0a h0b hle_abs
  have hsplit :
      (abs a + abs b) / (1 + (abs a + abs b)) ≤
        abs a / (1 + abs a) + abs b / (1 + abs b) := by
    simpa using
      hsplit_algebra_absapbon1pabsapbleqsumabsaon1pabsa a b h0a h0b
  exact le_trans hmono hsplit

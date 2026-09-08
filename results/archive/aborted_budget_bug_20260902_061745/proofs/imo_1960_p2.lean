import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem imo_1960_p2 (x : ℝ) (h₀ : 0 ≤ 1 + 2 * x) (h₁ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0)
    (h₂ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9) : -(1 / 2) ≤ x ∧ x < 45 / 8 := by
  have h₃ : -(1 / 2 : ℝ) ≤ x := by
    have h₃₁ : 0 ≤ 1 + 2 * x := h₀
    have h₃₂ : -(1 / 2 : ℝ) ≤ x := by
      linarith
    exact h₃₂
  
  have h₄ : x < 45 / 8 := by
    have h₄₁ : 0 ≤ 1 + 2 * x := h₀
    have h₄₂ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0 := h₁
    have h₄₃ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9 := h₂
    -- Define y = sqrt(1 + 2x)
    have h₄₄ : 0 ≤ Real.sqrt (1 + 2 * x) := Real.sqrt_nonneg (1 + 2 * x)
    set y := Real.sqrt (1 + 2 * x) with hy
    have h₄₅ : y ≥ 0 := by rw [hy]; exact Real.sqrt_nonneg _
    have h₄₆ : y ^ 2 = 1 + 2 * x := by
      rw [hy]
      rw [Real.sq_sqrt] <;> linarith
    have h₄₇ : y ≠ 1 := by
      by_contra h
      have h₄₈ : y = 1 := by linarith
      have h₄₉ : (1 - y) ^ 2 = 0 := by
        rw [h₄₈]
        norm_num
      have h₄₁₀ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 = 0 := by
        calc
          (1 - Real.sqrt (1 + 2 * x)) ^ 2 = (1 - y) ^ 2 := by
            rw [hy]
            <;> ring_nf
          _ = 0 := by rw [h₄₉]
      have h₄₁₁ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0 := h₁
      contradiction
    -- Express x in terms of y
    have h₄₈ : x = (y ^ 2 - 1) / 2 := by
      have h₄₉ : y ^ 2 = 1 + 2 * x := h₄₆
      linarith
    -- Simplify the denominator (1 - y)^2 = (y - 1)^2
    have h₄₉ : (1 - y) ^ 2 = (y - 1) ^ 2 := by
      ring_nf
    -- Simplify the numerator 4x² = (y² - 1)²
    have h₄₁₀ : 4 * x ^ 2 = (y ^ 2 - 1) ^ 2 := by
      rw [h₄₈]
      ring_nf
      <;> field_simp
      <;> ring_nf
    -- Simplify 4x² / (1 - y)² to (y + 1)²
    have h₄₁₁ : 4 * x ^ 2 / (1 - y) ^ 2 = (y + 1) ^ 2 := by
      have h₄₁₂ : (1 - y) ^ 2 ≠ 0 := by
        intro h
        have h₄₁₃ : (1 - y) ^ 2 = 0 := h
        have h₄₁₄ : 1 - y = 0 := by
          nlinarith
        have h₄₁₅ : y = 1 := by linarith
        contradiction
      have h₄₁₃ : 4 * x ^ 2 = (y ^ 2 - 1) ^ 2 := h₄₁₀
      have h₄₁₄ : (1 - y) ^ 2 = (y - 1) ^ 2 := h₄₉
      calc
        4 * x ^ 2 / (1 - y) ^ 2 = (y ^ 2 - 1) ^ 2 / (1 - y) ^ 2 := by rw [h₄₁₃]
        _ = (y ^ 2 - 1) ^ 2 / (y - 1) ^ 2 := by
          rw [h₄₉]
          <;> ring_nf
        _ = (y + 1) ^ 2 := by
          have h₄₁₅ : y ≠ 1 := h₄₇
          have h₄₁₆ : (y - 1) ≠ 0 := by
            intro h
            apply h₄₁₅
            linarith
          have h₄₁₇ : (y ^ 2 - 1 : ℝ) = (y - 1) * (y + 1) := by ring
          calc
            (y ^ 2 - 1 : ℝ) ^ 2 / (y - 1) ^ 2 = ((y - 1) * (y + 1)) ^ 2 / (y - 1) ^ 2 := by
              rw [h₄₁₇]
            _ = ((y - 1) ^ 2 * (y + 1) ^ 2) / (y - 1) ^ 2 := by ring
            _ = (y + 1) ^ 2 := by
              field_simp [h₄₁₆]
              <;> ring_nf
              <;> field_simp [h₄₁₆]
              <;> ring_nf
        _ = (y + 1) ^ 2 := by ring
    -- Substitute into the inequality
    have h₄₁₂ : (y + 1) ^ 2 < 2 * x + 9 := by
      have h₄₁₃ : 4 * x ^ 2 / (1 - y) ^ 2 < 2 * x + 9 := h₄₃
      have h₄₁₄ : 4 * x ^ 2 / (1 - y) ^ 2 = (y + 1) ^ 2 := h₄₁₁
      linarith
    -- Simplify 2x + 9 to y² + 8
    have h₄₁₃ : 2 * x + 9 = y ^ 2 + 8 := by
      have h₄₁₄ : x = (y ^ 2 - 1) / 2 := h₄₈
      rw [h₄₁₄]
      ring_nf
      <;> field_simp
      <;> ring_nf
      <;> linarith
    -- Combine to get (y + 1)² < y² + 8
    have h₄₁₄ : (y + 1) ^ 2 < y ^ 2 + 8 := by
      linarith
    -- Simplify to y < 7/2
    have h₄₁₅ : y < 7 / 2 := by
      nlinarith [sq_nonneg (y - 1)]
    -- Deduce sqrt(1 + 2x) < 7/2 and square to get x < 45/8
    have h₄₁₆ : Real.sqrt (1 + 2 * x) < 7 / 2 := by
      have h₄₁₇ : y < 7 / 2 := h₄₁₅
      have h₄₁₈ : y = Real.sqrt (1 + 2 * x) := by
        rw [hy]
      linarith
    have h₄₁₇ : 1 + 2 * x < (7 / 2 : ℝ) ^ 2 := by
      have h₄₁₈ : Real.sqrt (1 + 2 * x) < 7 / 2 := h₄₁₆
      have h₄₁₉ : 0 ≤ 1 + 2 * x := h₀
      have h₄₂₀ : Real.sqrt (1 + 2 * x) ≥ 0 := Real.sqrt_nonneg (1 + 2 * x)
      nlinarith [Real.sq_sqrt (by linarith : 0 ≤ (1 + 2 * x : ℝ))]
    have h₄₁₈ : x < 45 / 8 := by
      nlinarith
    exact h₄₁₈
  
  exact ⟨h₃, h₄⟩

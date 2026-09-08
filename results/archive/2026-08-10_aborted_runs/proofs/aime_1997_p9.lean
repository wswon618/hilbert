import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem aime_1997_p9 (a : ℝ) (h₀ : 0 < a)
    (h₁ : 1 / a - Int.floor (1 / a) = a ^ 2 - Int.floor (a ^ 2)) (h₂ : 2 < a ^ 2) (h₃ : a ^ 2 < 3) :
    a ^ 12 - 144 * (1 / a) = 233 := by
  have h_floor_1a : Int.floor (1 / a : ℝ) = 0 := by
    have h₄ : 0 < (1 : ℝ) / a := by positivity
    have h₅ : (1 : ℝ) / a < 1 := by
      have h₅₁ : a > 1 := by
        nlinarith [sq_nonneg (a - 1)]
      have h₅₂ : (1 : ℝ) / a < 1 := by
        rw [div_lt_one (by positivity)]
        nlinarith
      exact h₅₂
    have h₆ : Int.floor ((1 : ℝ) / a) = 0 := by
      rw [Int.floor_eq_iff]
      norm_num at h₄ h₅ ⊢
      constructor <;> norm_num <;>
      (try norm_num at h₄ h₅ ⊢) <;>
      (try linarith) <;>
      (try nlinarith)
    exact h₆
  
  have h_floor_a2 : Int.floor (a ^ 2 : ℝ) = 2 := by
    have h₄ : (2 : ℝ) < a ^ 2 := by exact_mod_cast h₂
    have h₅ : (a ^ 2 : ℝ) < 3 := by exact_mod_cast h₃
    have h₆ : Int.floor (a ^ 2 : ℝ) = 2 := by
      rw [Int.floor_eq_iff]
      norm_num at h₄ h₅ ⊢
      constructor <;> norm_num <;>
      (try norm_num at h₄ h₅ ⊢) <;>
      (try linarith) <;>
      (try nlinarith)
    exact h₆
  
  have h_eq_1a : 1 / a = a ^ 2 - 2 := by
    have h₄ : (1 / a : ℝ) - Int.floor (1 / a : ℝ) = (a ^ 2 : ℝ) - Int.floor (a ^ 2 : ℝ) := by
      exact_mod_cast h₁
    rw [h_floor_1a, h_floor_a2] at h₄
    norm_num at h₄ ⊢
    <;>
    (try linarith) <;>
    (try ring_nf at h₄ ⊢) <;>
    (try nlinarith) <;>
    (try linarith)
    <;>
    (try
      {
        field_simp at h₄ ⊢
        <;>
        nlinarith
      })
    <;>
    (try
      {
        ring_nf at h₄ ⊢
        <;>
        nlinarith
      })
  
  have h_cubic : a ^ 3 = 2 * a + 1 := by
    have h₄ : 1 / a = a ^ 2 - 2 := h_eq_1a
    have h₅ : a ≠ 0 := by linarith
    have h₆ : 1 = a * (a ^ 2 - 2) := by
      field_simp [h₅] at h₄ ⊢
      nlinarith
    have h₇ : a ^ 3 = 2 * a + 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
    exact h₇
  
  have h_quadratic : a ^ 2 = a + 1 := by
    have h₄ : a > 0 := h₀
    have h₅ : a ^ 3 = 2 * a + 1 := h_cubic
    have h₆ : (a + 1) * (a ^ 2 - a - 1) = 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
    have h₇ : a + 1 ≠ 0 := by nlinarith
    have h₈ : a ^ 2 - a - 1 = 0 := by
      apply mul_left_cancel₀ h₇
      nlinarith
    nlinarith
  
  have h_inv_a : 1 / a = a - 1 := by
    have h₄ : a ≠ 0 := by linarith
    have h₅ : a ^ 2 = a + 1 := h_quadratic
    have h₆ : 1 / a = a - 1 := by
      have h₇ : a > 0 := h₀
      have h₈ : a ^ 2 = a + 1 := h_quadratic
      field_simp [h₄] at h₈ ⊢
      nlinarith [sq_nonneg (a - 1)]
    exact h₆
  
  have h_a12 : a ^ 12 = 144 * a + 89 := by
    have h₄ : a ^ 3 = 2 * a + 1 := h_cubic
    have h₅ : a ^ 6 = 8 * a + 5 := by
      calc
        a ^ 6 = (a ^ 3) ^ 2 := by ring
        _ = (2 * a + 1) ^ 2 := by rw [h₄]
        _ = 4 * a ^ 2 + 4 * a + 1 := by ring
        _ = 4 * (a + 1) + 4 * a + 1 := by
          have h₅₁ : a ^ 2 = a + 1 := h_quadratic
          rw [h₅₁]
          <;> ring
        _ = 8 * a + 5 := by ring
    have h₆ : a ^ 9 = 34 * a + 21 := by
      calc
        a ^ 9 = a ^ 3 * a ^ 6 := by ring
        _ = (2 * a + 1) * (8 * a + 5) := by rw [h₄, h₅]
        _ = 16 * a ^ 2 + 10 * a + 8 * a + 5 := by ring
        _ = 16 * (a + 1) + 10 * a + 8 * a + 5 := by
          have h₆₁ : a ^ 2 = a + 1 := h_quadratic
          rw [h₆₁]
          <;> ring
        _ = 34 * a + 21 := by ring
    have h₇ : a ^ 12 = 144 * a + 89 := by
      calc
        a ^ 12 = a ^ 3 * a ^ 9 := by ring
        _ = (2 * a + 1) * (34 * a + 21) := by rw [h₄, h₆]
        _ = 68 * a ^ 2 + 42 * a + 34 * a + 21 := by ring
        _ = 68 * (a + 1) + 42 * a + 34 * a + 21 := by
          have h₇₁ : a ^ 2 = a + 1 := h_quadratic
          rw [h₇₁]
          <;> ring
        _ = 144 * a + 89 := by ring
    exact h₇
  
  have h_main : a ^ 12 - 144 * (1 / a) = 233 := by
    have h₄ : a ^ 12 = 144 * a + 89 := h_a12
    have h₅ : 1 / a = a - 1 := h_inv_a
    calc
      a ^ 12 - 144 * (1 / a) = (144 * a + 89) - 144 * (1 / a) := by rw [h₄]
      _ = (144 * a + 89) - 144 * (a - 1) := by rw [h₅]
      _ = 233 := by
        ring_nf
        <;>
        (try norm_num) <;>
        (try linarith) <;>
        (try nlinarith)
  
  exact h_main

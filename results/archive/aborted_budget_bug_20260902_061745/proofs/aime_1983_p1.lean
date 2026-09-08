import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  have h_w_ge_2 : w ≥ 2 := by
    by_contra! h
    have h₃ : w ≤ 1 := by linarith
    have h₄ : w = 0 ∨ w = 1 := by
      have h₅ : w ≤ 1 := by linarith
      have h₆ : w ≥ 0 := by linarith
      interval_cases w <;> simp_all (config := {decide := true})
    cases h₄ with
    | inl h₄ =>
      have h₅ : (w : ℝ) = 0 := by norm_cast <;> simp [h₄]
      have h₆ : Real.log (w : ℝ) = 0 := by
        rw [h₅]
        simp [Real.log_zero]
      have h₇ : (x : ℝ) > 1 := by
        norm_cast
        <;> linarith [ht.1]
      have h₈ : Real.log (x : ℝ) > 0 := Real.log_pos (by
        norm_num at h₇ ⊢ <;> linarith)
      have h₉ : Real.log (w : ℝ) / Real.log (x : ℝ) = 0 := by
        rw [h₆]
        <;> simp [h₈.ne']
      have h₁₀ : (Real.log (w : ℝ) / Real.log (x : ℝ) : ℝ) = 24 := by
        simpa [h₄] using h0
      linarith
    | inr h₄ =>
      have h₅ : (w : ℝ) = 1 := by norm_cast <;> simp [h₄]
      have h₆ : Real.log (w : ℝ) = 0 := by
        rw [h₅]
        simp [Real.log_one]
      have h₇ : (x : ℝ) > 1 := by
        norm_cast
        <;> linarith [ht.1]
      have h₈ : Real.log (x : ℝ) > 0 := Real.log_pos (by
        norm_num at h₇ ⊢ <;> linarith)
      have h₉ : Real.log (w : ℝ) / Real.log (x : ℝ) = 0 := by
        rw [h₆]
        <;> simp [h₈.ne']
      have h₁₀ : (Real.log (w : ℝ) / Real.log (x : ℝ) : ℝ) = 24 := by
        simpa [h₄] using h0
      linarith
  
  have h_logw_pos : Real.log (w : ℝ) > 0 := by
    have h₃ : (w : ℝ) > 1 := by
      norm_cast
      <;> linarith
    have h₄ : Real.log (w : ℝ) > 0 := Real.log_pos (by
      norm_num at h₃ ⊢ <;> linarith)
    exact h₄
  
  have h_logx_pos : Real.log (x : ℝ) > 0 := by
    have h₃ : (x : ℝ) > 1 := by
      norm_cast
      <;> linarith [ht.1]
    have h₄ : Real.log (x : ℝ) > 0 := Real.log_pos (by
      norm_num at h₃ ⊢ <;> linarith)
    exact h₄
  
  have h_logy_pos : Real.log (y : ℝ) > 0 := by
    have h₃ : (y : ℝ) > 1 := by
      norm_cast
      <;> linarith [ht.2.1]
    have h₄ : Real.log (y : ℝ) > 0 := Real.log_pos (by
      norm_num at h₃ ⊢ <;> linarith)
    exact h₄
  
  have h_logz_pos : Real.log (z : ℝ) > 0 := by
    have h₃ : (z : ℝ) > 1 := by
      norm_cast
      <;> linarith [ht.2.2]
    have h₄ : Real.log (z : ℝ) > 0 := Real.log_pos (by
      norm_num at h₃ ⊢ <;> linarith)
    exact h₄
  
  have h_logw_eq_24_logx : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := by
    have h₃ : Real.log (w : ℝ) / Real.log (x : ℝ) = 24 := by
      simpa using h0
    have h₄ : Real.log (x : ℝ) ≠ 0 := by linarith [h_logx_pos]
    field_simp [h₄] at h₃ ⊢
    <;> nlinarith
  
  have h_logw_eq_40_logy : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := by
    have h₃ : Real.log (w : ℝ) / Real.log (y : ℝ) = 40 := by
      simpa using h1
    have h₄ : Real.log (y : ℝ) ≠ 0 := by linarith [h_logy_pos]
    field_simp [h₄] at h₃ ⊢
    <;> nlinarith
  
  have h_3logx_eq_5logy : 3 * Real.log (x : ℝ) = 5 * Real.log (y : ℝ) := by
    have h₃ : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := h_logw_eq_24_logx
    have h₄ : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := h_logw_eq_40_logy
    have h₅ : 24 * Real.log (x : ℝ) = 40 * Real.log (y : ℝ) := by linarith
    have h₆ : 3 * Real.log (x : ℝ) = 5 * Real.log (y : ℝ) := by
      linarith
    exact h₆
  
  have h_logw_eq_12_log_prod : Real.log (w : ℝ) = 12 * (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) := by
    have h₃ : Real.log (w : ℝ) / Real.log (x * y * z : ℝ) = 12 := by
      simpa [mul_assoc] using h2
    have h₄ : Real.log (x * y * z : ℝ) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
      have h₅ : (x : ℝ) > 0 := by
        norm_cast
        <;> linarith [ht.1]
      have h₆ : (y : ℝ) > 0 := by
        norm_cast
        <;> linarith [ht.2.1]
      have h₇ : (z : ℝ) > 0 := by
        norm_cast
        <;> linarith [ht.2.2]
      have h₈ : Real.log (x * y * z : ℝ) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
        have h₉ : Real.log (x * y * z : ℝ) = Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) := by norm_cast
        rw [h₉]
        have h₁₀ : Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) = Real.log ((x : ℝ) * (y : ℝ)) + Real.log (z : ℝ) := by
          rw [Real.log_mul (by positivity) (by positivity)]
        rw [h₁₀]
        have h₁₁ : Real.log ((x : ℝ) * (y : ℝ)) = Real.log (x : ℝ) + Real.log (y : ℝ) := by
          rw [Real.log_mul (by positivity) (by positivity)]
        rw [h₁₁]
        <;> ring
      exact h₈
    have h₅ : Real.log (x * y * z : ℝ) ≠ 0 := by
      have h₆ : Real.log (x * y * z : ℝ) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := h₄
      have h₇ : Real.log (x : ℝ) > 0 := h_logx_pos
      have h₈ : Real.log (y : ℝ) > 0 := h_logy_pos
      have h₉ : Real.log (z : ℝ) > 0 := h_logz_pos
      have h₁₀ : Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) > 0 := by linarith
      rw [h₆]
      linarith
    have h₆ : Real.log (w : ℝ) = 12 * (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) := by
      have h₇ : Real.log (w : ℝ) / Real.log (x * y * z : ℝ) = 12 := h₃
      have h₈ : Real.log (x * y * z : ℝ) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := h₄
      have h₉ : Real.log (w : ℝ) = 12 * Real.log (x * y * z : ℝ) := by
        field_simp [h₅] at h₇ ⊢
        <;> nlinarith
      rw [h₉, h₈]
      <;> ring
    exact h₆
  
  have h_logx_eq_logy_plus_logz : Real.log (x : ℝ) = Real.log (y : ℝ) + Real.log (z : ℝ) := by
    have h₃ : Real.log (w : ℝ) = 12 * (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) := h_logw_eq_12_log_prod
    have h₄ : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := h_logw_eq_24_logx
    have h₅ : 12 * (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) = 24 * Real.log (x : ℝ) := by linarith
    have h₆ : Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) = 2 * Real.log (x : ℝ) := by linarith
    have h₇ : Real.log (y : ℝ) + Real.log (z : ℝ) = Real.log (x : ℝ) := by linarith
    linarith
  
  have h_2logy_eq_3logz : 2 * Real.log (y : ℝ) = 3 * Real.log (z : ℝ) := by
    have h₃ : 3 * Real.log (x : ℝ) = 5 * Real.log (y : ℝ) := h_3logx_eq_5logy
    have h₄ : Real.log (x : ℝ) = Real.log (y : ℝ) + Real.log (z : ℝ) := h_logx_eq_logy_plus_logz
    have h₅ : 3 * (Real.log (y : ℝ) + Real.log (z : ℝ)) = 5 * Real.log (y : ℝ) := by
      calc
        3 * (Real.log (y : ℝ) + Real.log (z : ℝ)) = 3 * Real.log (x : ℝ) := by
          rw [h₄]
          <;> ring
        _ = 5 * Real.log (y : ℝ) := by rw [h₃]
    have h₆ : 3 * Real.log (z : ℝ) = 2 * Real.log (y : ℝ) := by linarith
    linarith
  
  have h_logw_eq_60_logz : Real.log (w : ℝ) = 60 * Real.log (z : ℝ) := by
    have h₃ : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := h_logw_eq_40_logy
    have h₄ : 2 * Real.log (y : ℝ) = 3 * Real.log (z : ℝ) := h_2logy_eq_3logz
    have h₅ : Real.log (y : ℝ) = (3 / 2 : ℝ) * Real.log (z : ℝ) := by
      have h₅₁ : Real.log (z : ℝ) > 0 := h_logz_pos
      have h₅₂ : 2 * Real.log (y : ℝ) = 3 * Real.log (z : ℝ) := h_2logy_eq_3logz
      have h₅₃ : Real.log (y : ℝ) = (3 / 2 : ℝ) * Real.log (z : ℝ) := by
        apply mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)
        linarith
      exact h₅₃
    have h₆ : Real.log (w : ℝ) = 60 * Real.log (z : ℝ) := by
      calc
        Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := by rw [h₃]
        _ = 40 * ((3 / 2 : ℝ) * Real.log (z : ℝ)) := by rw [h₅]
        _ = 60 * Real.log (z : ℝ) := by ring
    exact h₆
  
  have h_main : Real.log (w : ℝ) / Real.log (z : ℝ) = 60 := by
    have h₃ : Real.log (w : ℝ) = 60 * Real.log (z : ℝ) := h_logw_eq_60_logz
    have h₄ : Real.log (z : ℝ) ≠ 0 := by linarith [h_logz_pos]
    have h₅ : Real.log (w : ℝ) / Real.log (z : ℝ) = 60 := by
      rw [h₃]
      field_simp [h₄]
      <;> ring_nf
      <;> field_simp [h₄]
      <;> linarith
    exact h₅
  
  have h₃ : Real.log w / Real.log z = 60 := by
    simpa [div_eq_mul_inv] using h_main
  exact h₃

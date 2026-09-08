import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  have hx : (1 : ℝ) < x := by
    norm_cast
    <;> linarith [ht.1]
  
  have hy : (1 : ℝ) < y := by
    norm_cast
    <;> linarith [ht.2.1]
  
  have hz : (1 : ℝ) < z := by
    norm_cast
    <;> linarith [ht.2.2]
  
  have hlogx : Real.log x > 0 := by
    apply Real.log_pos
    <;> norm_num at hx ⊢ <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try assumption)
    <;>
    (try norm_cast at hx ⊢ <;> linarith)
  
  have hlogy : Real.log y > 0 := by
    apply Real.log_pos
    <;> norm_num at hy ⊢ <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try assumption)
    <;>
    (try norm_cast at hy ⊢ <;> linarith)
  
  have hlogz : Real.log z > 0 := by
    apply Real.log_pos
    <;> norm_num at hz ⊢ <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try assumption)
    <;>
    (try norm_cast at hz ⊢ <;> linarith)
  
  have hlogw_ne_zero : Real.log w ≠ 0 := by
    by_contra h
    have h₃ : Real.log w = 0 := by simpa using h
    have h₄ : Real.log w / Real.log x = 0 := by
      rw [h₃]
      <;> simp [hlogx.ne']
      <;> field_simp [hlogx.ne']
      <;> ring_nf
      <;> norm_num
    have h₅ : (24 : ℝ) = 0 := by linarith
    norm_num at h₅
    <;> linarith
  
  have hlogw_pos : Real.log w > 0 := by
    by_contra h
    have h₃ : Real.log w ≤ 0 := by linarith
    have h₄ : Real.log w / Real.log x ≤ 0 := by
      have h₅ : Real.log x > 0 := hlogx
      have h₆ : Real.log w ≤ 0 := h₃
      exact div_nonpos_of_nonpos_of_nonneg h₆ (le_of_lt h₅)
    have h₅ : (24 : ℝ) ≤ 0 := by linarith
    norm_num at h₅
    <;> linarith
  
  have h3 : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z := by
    have h₃ : (x : ℝ) > 0 := by positivity
    have h₄ : (y : ℝ) > 0 := by positivity
    have h₅ : (z : ℝ) > 0 := by positivity
    have h₆ : Real.log (x * y * z) = Real.log (x * y) + Real.log z := by
      rw [Real.log_mul (by positivity) (by positivity)]
    have h₇ : Real.log (x * y) = Real.log x + Real.log y := by
      rw [Real.log_mul (by positivity) (by positivity)]
    rw [h₆, h₇]
    <;> ring_nf
    <;> field_simp [h₃, h₄, h₅]
    <;> linarith
  
  have h4 : Real.log w = 24 * Real.log x := by
    have h₄ : Real.log w / Real.log x = 24 := h0
    have h₅ : Real.log x ≠ 0 := by linarith [hlogx]
    field_simp [h₅] at h₄ ⊢
    <;> nlinarith [hlogx]
  
  have h5 : Real.log w = 40 * Real.log y := by
    have h₅ : Real.log w / Real.log y = 40 := h1
    have h₆ : Real.log y ≠ 0 := by linarith [hlogy]
    field_simp [h₆] at h₅ ⊢
    <;> nlinarith [hlogy]
  
  have h6 : Real.log w = 12 * (Real.log x + Real.log y + Real.log z) := by
    have h₆ : Real.log w / Real.log (x * y * z) = 12 := h2
    have h₇ : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z := h3
    have h₈ : Real.log (x * y * z) ≠ 0 := by
      have h₉ : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z := h3
      have h₁₀ : Real.log x > 0 := hlogx
      have h₁₁ : Real.log y > 0 := hlogy
      have h₁₂ : Real.log z > 0 := hlogz
      have h₁₃ : Real.log x + Real.log y + Real.log z > 0 := by linarith
      have h₁₄ : Real.log (x * y * z) > 0 := by
        rw [h₉]
        linarith
      linarith
    have h₉ : Real.log w = 12 * Real.log (x * y * z) := by
      field_simp [h₈] at h₆ ⊢
      <;> nlinarith
    rw [h₉]
    rw [h₇]
    <;> ring_nf
    <;> linarith
  
  have h7 : 3 * Real.log x = 5 * Real.log y := by
    have h₇ : Real.log w = 24 * Real.log x := h4
    have h₈ : Real.log w = 40 * Real.log y := h5
    have h₉ : 24 * Real.log x = 40 * Real.log y := by linarith
    have h₁₀ : 3 * Real.log x = 5 * Real.log y := by
      linarith
    exact h₁₀
  
  have h8 : Real.log x = Real.log y + Real.log z := by
    have h₈ : Real.log w = 24 * Real.log x := h4
    have h₉ : Real.log w = 12 * (Real.log x + Real.log y + Real.log z) := h6
    have h₁₀ : 24 * Real.log x = 12 * (Real.log x + Real.log y + Real.log z) := by linarith
    have h₁₁ : 2 * Real.log x = Real.log x + Real.log y + Real.log z := by linarith
    have h₁₂ : Real.log x = Real.log y + Real.log z := by linarith
    exact h₁₂
  
  have h9 : 3 * Real.log z = 2 * Real.log y := by
    have h₉ : 3 * Real.log x = 5 * Real.log y := h7
    have h₁₀ : Real.log x = Real.log y + Real.log z := h8
    have h₁₁ : 3 * (Real.log y + Real.log z) = 5 * Real.log y := by
      calc
        3 * (Real.log y + Real.log z) = 3 * Real.log x := by
          rw [h₁₀]
          <;> ring
        _ = 5 * Real.log y := by rw [h₉]
    have h₁₂ : 3 * Real.log y + 3 * Real.log z = 5 * Real.log y := by linarith
    have h₁₃ : 3 * Real.log z = 2 * Real.log y := by linarith
    exact h₁₃
  
  have h10 : Real.log w = 60 * Real.log z := by
    have h₁₀ : Real.log w = 40 * Real.log y := h5
    have h₁₁ : 3 * Real.log z = 2 * Real.log y := h9
    have h₁₂ : Real.log y = (3 / 2 : ℝ) * Real.log z := by
      have h₁₃ : (2 : ℝ) ≠ 0 := by norm_num
      have h₁₄ : Real.log y = (3 / 2 : ℝ) * Real.log z := by
        apply mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)
        nlinarith
      exact h₁₄
    rw [h₁₀, h₁₂]
    <;> ring_nf
    <;> field_simp
    <;> nlinarith [hlogz]
  
  have h11 : Real.log w / Real.log z = 60 := by
    have h₁₁ : Real.log w = 60 * Real.log z := h10
    have h₁₂ : Real.log z ≠ 0 := by linarith [hlogz]
    have h₁₃ : Real.log w / Real.log z = 60 := by
      rw [h₁₁]
      field_simp [h₁₂]
      <;> ring_nf
      <;> field_simp [h₁₂]
      <;> linarith
    exact h₁₃
  
  exact h11

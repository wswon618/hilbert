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
  
  have logx_pos : 0 < Real.log x := by
    apply Real.log_pos
    <;> norm_num at hx ⊢ <;>
    (try norm_cast at hx ⊢) <;>
    (try linarith) <;>
    (try assumption)
    <;>
    (try norm_num)
    <;>
    (try linarith)
  
  have logy_pos : 0 < Real.log y := by
    apply Real.log_pos
    <;> norm_num at hy ⊢ <;>
    (try norm_cast at hy ⊢) <;>
    (try linarith) <;>
    (try assumption)
    <;>
    (try norm_num)
    <;>
    (try linarith)
  
  have logz_pos : 0 < Real.log z := by
    apply Real.log_pos
    <;> norm_num at hz ⊢ <;>
    (try norm_cast at hz ⊢) <;>
    (try linarith) <;>
    (try assumption)
    <;>
    (try norm_num)
    <;>
    (try linarith)
  
  have logw : Real.log w = 24 * Real.log x := by
    have h3 : Real.log w / Real.log x = 24 := h0
    have h4 : Real.log w = 24 * Real.log x := by
      have h5 : Real.log x ≠ 0 := by linarith
      field_simp [h5] at h3 ⊢
      <;> nlinarith
    exact h4
  
  have logw' : Real.log w = 40 * Real.log y := by
    have h3 : Real.log w / Real.log y = 40 := h1
    have h4 : Real.log w = 40 * Real.log y := by
      have h5 : Real.log y ≠ 0 := by linarith
      field_simp [h5] at h3 ⊢
      <;> nlinarith
    exact h4
  
  have logw'' : Real.log w = 12 * (Real.log x + Real.log y + Real.log z) := by
    have h3 : Real.log w / Real.log (x * y * z) = 12 := h2
    have h4 : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z := by
      have h5 : (x : ℝ) > 0 := by positivity
      have h6 : (y : ℝ) > 0 := by positivity
      have h7 : (z : ℝ) > 0 := by positivity
      have h8 : Real.log (x * y * z) = Real.log (x * y) + Real.log z := by
        rw [Real.log_mul (by positivity) (by positivity)]
      have h9 : Real.log (x * y) = Real.log x + Real.log y := by
        rw [Real.log_mul (by positivity) (by positivity)]
      rw [h8, h9]
      <;> ring
      <;> field_simp
      <;> linarith
    have h5 : Real.log w = 12 * (Real.log x + Real.log y + Real.log z) := by
      have h6 : Real.log (x * y * z) ≠ 0 := by
        rw [h4]
        have h7 : Real.log x > 0 := logx_pos
        have h8 : Real.log y > 0 := logy_pos
        have h9 : Real.log z > 0 := logz_pos
        linarith
      have h7 : Real.log w / Real.log (x * y * z) = 12 := h3
      have h8 : Real.log w = 12 * Real.log (x * y * z) := by
        field_simp [h6] at h7 ⊢
        <;> nlinarith
      rw [h8, h4]
      <;> ring
      <;> field_simp
      <;> linarith
    exact h5
  
  have h3 : 3 * Real.log x = 5 * Real.log y := by
    have h4 : Real.log w = 24 * Real.log x := logw
    have h5 : Real.log w = 40 * Real.log y := logw'
    have h6 : 24 * Real.log x = 40 * Real.log y := by linarith
    have h7 : 3 * Real.log x = 5 * Real.log y := by
      linarith
    exact h7
  
  have h4 : Real.log x = Real.log y + Real.log z := by
    have h5 : Real.log w = 24 * Real.log x := logw
    have h6 : Real.log w = 12 * (Real.log x + Real.log y + Real.log z) := logw''
    have h7 : 24 * Real.log x = 12 * (Real.log x + Real.log y + Real.log z) := by linarith
    have h8 : 2 * Real.log x = Real.log x + Real.log y + Real.log z := by
      linarith
    have h9 : Real.log x = Real.log y + Real.log z := by linarith
    exact h9
  
  have h5 : Real.log z = (2 : ℝ) / 5 * Real.log x := by
    have h6 : 3 * Real.log x = 5 * Real.log y := h3
    have h7 : Real.log x = Real.log y + Real.log z := h4
    have h8 : Real.log y = (3 : ℝ) / 5 * Real.log x := by
      have h9 : Real.log y = (3 : ℝ) / 5 * Real.log x := by
        -- Solve for Real.log y in terms of Real.log x using h6
        have h10 : (5 : ℝ) * Real.log y = 3 * Real.log x := by linarith
        have h11 : Real.log y = (3 : ℝ) / 5 * Real.log x := by
          apply mul_left_cancel₀ (show (5 : ℝ) ≠ 0 by norm_num)
          linarith
        exact h11
      exact h9
    -- Substitute Real.log y into h7 to find Real.log z in terms of Real.log x
    have h9 : Real.log z = (2 : ℝ) / 5 * Real.log x := by
      have h10 : Real.log x = Real.log y + Real.log z := h7
      rw [h8] at h10
      ring_nf at h10 ⊢
      linarith
    exact h9
  
  have h6 : Real.log w / Real.log z = 60 := by
    have h7 : Real.log w = 24 * Real.log x := logw
    have h8 : Real.log z = (2 : ℝ) / 5 * Real.log x := h5
    have h9 : Real.log z ≠ 0 := by
      have h10 : Real.log z > 0 := logz_pos
      linarith
    have h10 : Real.log x ≠ 0 := by linarith [logx_pos]
    have h11 : Real.log w / Real.log z = 60 := by
      rw [h7, h8]
      field_simp [h9, h10]
      <;> ring_nf
      <;> field_simp [h10]
      <;> nlinarith [logx_pos]
    exact h11
  
  exact h6

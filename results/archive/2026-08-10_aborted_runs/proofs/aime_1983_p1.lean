import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  have hx : (x : ℝ) > 1 := by
    norm_cast
    <;> linarith [ht.1]
  
  have hy : (y : ℝ) > 1 := by
    norm_cast
    <;> linarith [ht.2.1]
  
  have hz : (z : ℝ) > 1 := by
    norm_cast
    <;> linarith [ht.2.2]
  
  have hlogx : Real.log (x : ℝ) > 0 := by
    apply Real.log_pos
    <;> norm_num at hx ⊢ <;> linarith
  
  have hlogy : Real.log (y : ℝ) > 0 := by
    apply Real.log_pos
    <;> norm_num at hy ⊢ <;> linarith
  
  have hlogz : Real.log (z : ℝ) > 0 := by
    apply Real.log_pos
    <;> norm_num at hz ⊢ <;> linarith
  
  have hlogw_pos : Real.log (w : ℝ) > 0 := by
    have h3 : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := by
      have h4 : Real.log (w : ℝ) / Real.log (x : ℝ) = 24 := by
        simpa [Real.log_mul, Real.log_pow] using h0
      have h5 : Real.log (x : ℝ) ≠ 0 := by linarith [hlogx]
      field_simp at h4 ⊢
      <;> nlinarith
    rw [h3]
    have h6 : (24 : ℝ) * Real.log (x : ℝ) > 0 := by
      have h7 : Real.log (x : ℝ) > 0 := hlogx
      positivity
    linarith
  
  have h3 : 3 * Real.log (x : ℝ) = 5 * Real.log (y : ℝ) := by
    have h4 : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := by
      have h5 : Real.log (w : ℝ) / Real.log (x : ℝ) = 24 := by
        simpa [Real.log_mul, Real.log_pow] using h0
      have h6 : Real.log (x : ℝ) ≠ 0 := by linarith [hlogx]
      field_simp at h5 ⊢
      <;> nlinarith
    have h7 : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := by
      have h8 : Real.log (w : ℝ) / Real.log (y : ℝ) = 40 := by
        simpa [Real.log_mul, Real.log_pow] using h1
      have h9 : Real.log (y : ℝ) ≠ 0 := by linarith [hlogy]
      field_simp at h8 ⊢
      <;> nlinarith
    have h10 : 24 * Real.log (x : ℝ) = 40 * Real.log (y : ℝ) := by linarith
    have h11 : 3 * Real.log (x : ℝ) = 5 * Real.log (y : ℝ) := by
      linarith
    exact h11
  
  have h4 : Real.log (x : ℝ) = Real.log (y : ℝ) + Real.log (z : ℝ) := by
    have h5 : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := by
      have h6 : Real.log (w : ℝ) / Real.log (x : ℝ) = 24 := by
        simpa [Real.log_mul, Real.log_pow] using h0
      have h7 : Real.log (x : ℝ) ≠ 0 := by linarith [hlogx]
      field_simp at h6 ⊢
      <;> nlinarith
    have h8 : Real.log (w : ℝ) = 12 * Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) := by
      have h9 : Real.log (w : ℝ) / Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) = 12 := by
        simpa [Real.log_mul, Real.log_pow] using h2
      have h10 : Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) ≠ 0 := by
        have h11 : Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
          have h12 : Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) = Real.log ((x : ℝ) * (y : ℝ)) + Real.log (z : ℝ) := by
            rw [Real.log_mul (by positivity) (by positivity)]
          have h13 : Real.log ((x : ℝ) * (y : ℝ)) = Real.log (x : ℝ) + Real.log (y : ℝ) := by
            rw [Real.log_mul (by positivity) (by positivity)]
          rw [h12, h13]
          <;> ring
        rw [h11]
        have h14 : Real.log (x : ℝ) > 0 := hlogx
        have h15 : Real.log (y : ℝ) > 0 := hlogy
        have h16 : Real.log (z : ℝ) > 0 := hlogz
        linarith
      field_simp at h9 ⊢
      <;> nlinarith
    have h11 : Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
      have h12 : Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) = Real.log ((x : ℝ) * (y : ℝ)) + Real.log (z : ℝ) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      have h13 : Real.log ((x : ℝ) * (y : ℝ)) = Real.log (x : ℝ) + Real.log (y : ℝ) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      rw [h12, h13]
      <;> ring
    have h14 : 24 * Real.log (x : ℝ) = 12 * (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) := by
      linarith
    have h15 : 2 * Real.log (x : ℝ) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
      linarith
    have h16 : Real.log (x : ℝ) = Real.log (y : ℝ) + Real.log (z : ℝ) := by
      linarith
    exact h16
  
  have h5 : 3 * Real.log (z : ℝ) = 2 * Real.log (y : ℝ) := by
    have h6 : 3 * Real.log (x : ℝ) = 5 * Real.log (y : ℝ) := h3
    have h7 : Real.log (x : ℝ) = Real.log (y : ℝ) + Real.log (z : ℝ) := h4
    have h8 : 3 * (Real.log (y : ℝ) + Real.log (z : ℝ)) = 5 * Real.log (y : ℝ) := by
      calc
        3 * (Real.log (y : ℝ) + Real.log (z : ℝ)) = 3 * Real.log (x : ℝ) := by
          rw [h7]
          <;> ring
        _ = 5 * Real.log (y : ℝ) := by rw [h6]
    have h9 : 3 * Real.log (z : ℝ) = 2 * Real.log (y : ℝ) := by
      linarith
    exact h9
  
  have h6 : 60 * Real.log (z : ℝ) = 40 * Real.log (y : ℝ) := by
    have h7 : 3 * Real.log (z : ℝ) = 2 * Real.log (y : ℝ) := h5
    have h8 : 60 * Real.log (z : ℝ) = 40 * Real.log (y : ℝ) := by
      calc
        60 * Real.log (z : ℝ) = 20 * (3 * Real.log (z : ℝ)) := by ring
        _ = 20 * (2 * Real.log (y : ℝ)) := by rw [h7]
        _ = 40 * Real.log (y : ℝ) := by ring
    exact h8
  
  have h7 : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := by
    have h8 : Real.log (w : ℝ) / Real.log (y : ℝ) = 40 := by
      simpa [Real.log_mul, Real.log_pow] using h1
    have h9 : Real.log (y : ℝ) ≠ 0 := by linarith [hlogy]
    have h10 : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := by
      field_simp at h8 ⊢
      <;> nlinarith
    exact h10
  
  have h8 : Real.log (w : ℝ) = 60 * Real.log (z : ℝ) := by
    have h9 : 60 * Real.log (z : ℝ) = 40 * Real.log (y : ℝ) := h6
    have h10 : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := h7
    linarith
  
  have h9 : Real.log (w : ℝ) / Real.log (z : ℝ) = 60 := by
    have h10 : Real.log (w : ℝ) = 60 * Real.log (z : ℝ) := h8
    have h11 : Real.log (z : ℝ) ≠ 0 := by linarith [hlogz]
    have h12 : Real.log (w : ℝ) / Real.log (z : ℝ) = 60 := by
      rw [h10]
      field_simp [h11]
      <;> ring
      <;> field_simp [h11]
      <;> linarith
    exact h12
  
  simpa [Real.log_mul, Real.log_pow] using h9

import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h_irrational_sqrt_ten_irrational (h_equiv : Irrational (Real.sqrt (10 : ℝ)) ↔ ¬ IsSquare (10 : ℕ))
    (h_not_square : ¬ IsSquare (10 : ℕ)) : Irrational (Real.sqrt (10 : ℝ)) := by
  have h₁ : Irrational (Real.sqrt (10 : ℝ)) := by
    have h₂ : ¬ IsSquare (10 : ℕ) := h_not_square
    have h₃ : Irrational (Real.sqrt (10 : ℝ)) ↔ ¬ IsSquare (10 : ℕ) := h_equiv
    have h₄ : Irrational (Real.sqrt (10 : ℝ)) := by
      -- Use the given equivalence to deduce the irrationality of sqrt(10)
      have h₅ : ¬ IsSquare (10 : ℕ) := h₂
      have h₆ : Irrational (Real.sqrt (10 : ℝ)) ↔ ¬ IsSquare (10 : ℕ) := h₃
      -- Since ¬ IsSquare (10 : ℕ) is true, we can directly use the equivalence to get the result
      have h₇ : Irrational (Real.sqrt (10 : ℝ)) := by
        rw [h₆]
        exact h₅
      exact h₇
    exact h₄
  exact h₁

theorem h_equiv_sqrt_ten_irrational : Irrational (Real.sqrt (10 : ℝ)) ↔ ¬ IsSquare (10 : ℕ) := by
  simpa using (irrational_sqrt_natCast_iff (n := 10))

theorem h_not_square_sqrt_ten_irrational : ¬ IsSquare (10 : ℕ) := by
  intro h
  have h_int : IsSquare (10 : ℤ) := (Int.isSquare_natCast_iff).mpr h
  rcases h_int with ⟨z, hz⟩
  have hmod : z * z % 4 = (2 : ℤ) := by
    simpa [hz] using (by norm_num : ((10 : ℤ) % 4) = (2 : ℤ))
  have hneq := Int.sq_ne_two_mod_four z
  exact hneq hmod

theorem sqrt_ten_irrational : Irrational (Real.sqrt (10 : ℝ)) := by
  have h_equiv : Irrational (Real.sqrt (10 : ℝ)) ↔ ¬ IsSquare (10 : ℕ) := by
    exact h_equiv_sqrt_ten_irrational
  have h_not_square : ¬ IsSquare (10 : ℕ) := by
    exact h_not_square_sqrt_ten_irrational
  have h_irrational : Irrational (Real.sqrt (10 : ℝ)) := by
    exact h_irrational_sqrt_ten_irrational h_equiv h_not_square
  exact h_irrational

import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem mathd_algebra_398 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 9 * b = 20 * c)
    (h₂ : 7 * a = 4 * b) : 63 * a = 80 * c := by
  have h₃ : 63 * a = 80 * c := by
    have h₄ : a = (4 * b) / 7 := by
      have h₅ : 7 * a = 4 * b := h₂
      have h₆ : a = (4 * b) / 7 := by
        -- Solve for `a` in terms of `b` using the equation `7 * a = 4 * b`
        apply Eq.symm
        -- Simplify the equation to get `a = (4 * b) / 7`
        field_simp at h₅ ⊢
        <;> nlinarith
      exact h₆
    have h₇ : b = (20 * c) / 9 := by
      have h₈ : 9 * b = 20 * c := h₁
      have h₉ : b = (20 * c) / 9 := by
        -- Solve for `b` in terms of `c` using the equation `9 * b = 20 * c`
        apply Eq.symm
        -- Simplify the equation to get `b = (20 * c) / 9`
        field_simp at h₈ ⊢
        <;> nlinarith
      exact h₉
    -- Substitute `a` and `b` in terms of `c` into the goal `63 * a = 80 * c`
    rw [h₄, h₇]
    -- Simplify the expression to verify the equality
    ring_nf
    <;> field_simp
    <;> ring_nf
    <;> nlinarith
  exact h₃

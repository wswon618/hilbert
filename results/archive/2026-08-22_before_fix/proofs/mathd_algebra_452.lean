import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem mathd_algebra_452 (a : ℕ → ℝ) (h₀ : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n)
    (h₁ : a 1 = 2 / 3) (h₂ : a 9 = 4 / 5) : a 5 = 11 / 15 := by
  have h₃ : a 2 = 2 * a 1 - a 0 := by
    have h₃₁ := h₀ 0
    have h₃₂ : a 2 - a 1 = a 1 - a 0 := by simpa using h₃₁
    linarith
  
  have h₄ : a 3 = 3 * a 1 - 2 * a 0 := by
    have h₄₁ := h₀ 1
    have h₄₂ : a 3 - a 2 = a 2 - a 1 := by simpa using h₄₁
    have h₄₃ : a 3 = 2 * a 2 - a 1 := by linarith
    rw [h₄₃, h₃]
    <;> ring_nf
    <;> linarith
  
  have h₅ : a 4 = 4 * a 1 - 3 * a 0 := by
    have h₅₁ := h₀ 2
    have h₅₂ : a 4 - a 3 = a 3 - a 2 := by simpa using h₅₁
    have h₅₃ : a 4 = 2 * a 3 - a 2 := by linarith
    rw [h₅₃, h₄, h₃]
    <;> ring_nf
    <;> linarith
  
  have h₆ : a 5 = 5 * a 1 - 4 * a 0 := by
    have h₆₁ := h₀ 3
    have h₆₂ : a 5 - a 4 = a 4 - a 3 := by simpa using h₆₁
    have h₆₃ : a 5 = 2 * a 4 - a 3 := by linarith
    rw [h₆₃, h₅, h₄]
    <;> ring_nf
    <;> linarith
  
  have h₇ : a 6 = 6 * a 1 - 5 * a 0 := by
    have h₇₁ := h₀ 4
    have h₇₂ : a 6 - a 5 = a 5 - a 4 := by simpa using h₇₁
    have h₇₃ : a 6 = 2 * a 5 - a 4 := by linarith
    rw [h₇₃, h₆, h₅]
    <;> ring_nf
    <;> linarith
  
  have h₈ : a 7 = 7 * a 1 - 6 * a 0 := by
    have h₈₁ := h₀ 5
    have h₈₂ : a 7 - a 6 = a 6 - a 5 := by simpa using h₈₁
    have h₈₃ : a 7 = 2 * a 6 - a 5 := by linarith
    rw [h₈₃, h₇, h₆]
    <;> ring_nf
    <;> linarith
  
  have h₉ : a 8 = 8 * a 1 - 7 * a 0 := by
    have h₉₁ := h₀ 6
    have h₉₂ : a 8 - a 7 = a 7 - a 6 := by simpa using h₉₁
    have h₉₃ : a 8 = 2 * a 7 - a 6 := by linarith
    rw [h₉₃, h₈, h₇]
    <;> ring_nf
    <;> linarith
  
  have h₁₀ : a 9 = 9 * a 1 - 8 * a 0 := by
    have h₁₀₁ := h₀ 7
    have h₁₀₂ : a 9 - a 8 = a 8 - a 7 := by simpa using h₁₀₁
    have h₁₀₃ : a 9 = 2 * a 8 - a 7 := by linarith
    rw [h₁₀₃, h₉, h₈]
    <;> ring_nf
    <;> linarith
  
  have h₁₁ : a 0 = 13 / 20 := by
    have h₁₁₁ : a 9 = 9 * a 1 - 8 * a 0 := h₁₀
    rw [h₁₁₁] at h₂
    rw [h₁] at h₂
    ring_nf at h₂ ⊢
    linarith
  
  have h₁₂ : a 5 = 11 / 15 := by
    have h₁₂₁ : a 5 = 5 * a 1 - 4 * a 0 := h₆
    rw [h₁₂₁]
    rw [h₁, h₁₁]
    <;> norm_num
    <;> linarith
  
  exact h₁₂

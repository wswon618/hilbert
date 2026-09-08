import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem amc12_2000_p6 (p q : ℕ) (h₀ : Nat.Prime p ∧ Nat.Prime q) (h₁ : 4 ≤ p ∧ p ≤ 18)
    (h₂ : 4 ≤ q ∧ q ≤ 18) : ↑p * ↑q - (↑p + ↑q) ≠ (194 : ℕ) := by
  have h₃ : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 := by
    have h₃₁ : p ≤ 18 := h₁.2
    have h₃₂ : 4 ≤ p := h₁.1
    have h₃₃ : Nat.Prime p := h₀.1
    have h₃₄ : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 := by
      interval_cases p <;> norm_num [Nat.Prime] at h₃₃ ⊢ <;> try contradiction <;> try omega
    exact h₃₄
  
  have h₄ : q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 17 := by
    have h₄₁ : q ≤ 18 := h₂.2
    have h₄₂ : 4 ≤ q := h₂.1
    have h₄₃ : Nat.Prime q := h₀.2
    have h₄₄ : q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 17 := by
      interval_cases q <;> norm_num [Nat.Prime] at h₄₃ ⊢ <;> try contradiction <;> try omega
    exact h₄₄
  
  have h₅ : ↑p * ↑q - (↑p + ↑q) ≠ (194 : ℕ) := by
    rcases h₃ with (rfl | rfl | rfl | rfl | rfl)
    <;> rcases h₄ with (rfl | rfl | rfl | rfl | rfl)
    <;> norm_num [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_assoc]
    <;>
    (try decide) <;>
    (try {
      norm_num at *
      <;>
      (try omega)
    }) <;>
    (try {
      ring_nf at *
      <;>
      norm_num at *
      <;>
      omega
    })
  
  exact h₅

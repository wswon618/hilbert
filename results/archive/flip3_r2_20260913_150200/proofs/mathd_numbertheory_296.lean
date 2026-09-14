import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem mathd_numbertheory_296 (n : ℕ) (h₀ : 2 ≤ n) (h₁ : ∃ x, x ^ 3 = n) (h₂ : ∃ t, t ^ 4 = n) :
    4096 ≤ n := by
  have h_main : 4096 ≤ n := by
    by_contra h
    -- Assume for contradiction that n < 4096
    have h₃ : n < 4096 := by linarith
    -- Obtain t such that t^4 = n
    obtain ⟨t, ht⟩ := h₂
    have h₄ : t ^ 4 < 4096 := by
      linarith
    -- Since t is a natural number, t must be less than 8
    have h₅ : t ≤ 7 := by
      by_contra h₅
      have h₆ : t ≥ 8 := by linarith
      have h₇ : t ^ 4 ≥ 8 ^ 4 := by
        exact Nat.pow_le_pow_of_le_left (by linarith) 4
      have h₈ : 8 ^ 4 = 4096 := by norm_num
      have h₉ : t ^ 4 ≥ 4096 := by
        linarith
      linarith
    -- Check all possible values of t from 0 to 7
    have h₆ : t ≤ 7 := by linarith
    interval_cases t <;> norm_num at ht ⊢ <;>
      (try omega) <;>
      (try {
        -- For each t, check if t^4 is a perfect cube
        obtain ⟨x, hx⟩ := h₁
        have h₇ : x ^ 3 = n := hx
        have h₈ : x ^ 3 < 4096 := by linarith
        have h₉ : x ≤ 15 := by
          by_contra h₉
          have h₁₀ : x ≥ 16 := by linarith
          have h₁₁ : x ^ 3 ≥ 16 ^ 3 := by
            exact Nat.pow_le_pow_of_le_left (by linarith) 3
          have h₁₂ : 16 ^ 3 = 4096 := by norm_num
          have h₁₃ : x ^ 3 ≥ 4096 := by linarith
          linarith
        interval_cases x <;> norm_num at h₇ ⊢ <;> omega
      }) <;>
      (try {
        -- If t^4 is not a perfect cube, we get a contradiction
        obtain ⟨x, hx⟩ := h₁
        have h₇ : x ^ 3 = n := hx
        norm_num at ht h₇ ⊢
        <;>
        (try {
          have h₈ : x ≤ 15 := by
            by_contra h₈
            have h₉ : x ≥ 16 := by linarith
            have h₁₀ : x ^ 3 ≥ 16 ^ 3 := by
              exact Nat.pow_le_pow_of_le_left (by linarith) 3
            have h₁₁ : 16 ^ 3 = 4096 := by norm_num
            have h₁₂ : x ^ 3 ≥ 4096 := by linarith
            linarith
          interval_cases x <;> norm_num at h₇ ⊢ <;> omega
        }) <;>
        omega
      })
  exact h_main

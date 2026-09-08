import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h_mod2022_amc12a_2021_p8 : 2022 % 7 = 6 := by
  norm_num [Nat.mod_eq_of_lt]
  <;> rfl

theorem h_mod2021_amc12a_2021_p8 : 2021 % 7 = 5 := by
  norm_num [Nat.mod_eq_of_lt]
  <;> rfl

theorem h_mod2023_amc12a_2021_p8 : 2023 % 7 = 0 := by
  norm_num [Nat.mod_eq_of_lt]
  <;> rfl

theorem h_even0_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) : Even (d 0) := by
  have h₄ : Even (d 0) := by
    rw [h₀]
    <;> simp [Nat.even_iff]
    <;> norm_num
  exact h₄

theorem h_odd2_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) : Odd (d 2) := by
  have h₄ : Odd (d 2) := by
    rw [h₂]
    -- We need to show that 1 is odd. In Lean, `Odd 1` is true by definition.
    <;> simp [Nat.odd_iff_not_even, parity_simps]
  exact h₄

theorem h_even0'_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) : Even (d 0) := by
  have h₄ : Even (d 0) := by
    rw [h₀]
    -- We need to show that 0 is even. In Lean, 0 is even because it can be written as 2 * 0.
    <;> simp [Nat.even_iff]
    <;> use 0
    <;> norm_num
  exact h₄

theorem h_even1_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) : Even (d 1) := by
  have h_main : Even (d 1) := by
    rw [h₁]
    -- We need to show that 0 is even. By definition, 0 = 2 * 0, so it is even.
    exact ⟨0, by simp⟩
  
  exact h_main

theorem h_even_rec_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (n : ℕ) (hn : n ≥ 3) :
    Even (d n) ↔ (Even (d (n - 1)) ↔ Even (d (n - 3))) := by
  have h_rec : d n = d (n - 1) + d (n - 3) := by
    have h₄ : d n = d (n - 1) + d (n - 3) := h₃ n hn
    exact h₄
  
  have h_main : Even (d (n - 1) + d (n - 3)) ↔ (Even (d (n - 1)) ↔ Even (d (n - 3))) := by
    constructor
    · -- Prove the forward direction: if Even (a + b), then (Even a ↔ Even b)
      intro h
      have h₄ : Even (d (n - 1) + d (n - 3)) := h
      have h₅ : (Even (d (n - 1)) ↔ Even (d (n - 3))) := by
        -- Use the fact that a + b is even iff a and b have the same parity
        have h₆ : (d (n - 1) + d (n - 3)) % 2 = 0 := by
          rw [Nat.even_iff] at h₄
          omega
        have h₇ : d (n - 1) % 2 = d (n - 3) % 2 := by
          have h₈ : (d (n - 1) + d (n - 3)) % 2 = 0 := h₆
          have h₉ : (d (n - 1) % 2 + d (n - 3) % 2) % 2 = 0 := by
            omega
          have h₁₀ : d (n - 1) % 2 = 0 ∨ d (n - 1) % 2 = 1 := by omega
          have h₁₁ : d (n - 3) % 2 = 0 ∨ d (n - 3) % 2 = 1 := by omega
          rcases h₁₀ with (h₁₀ | h₁₀) <;> rcases h₁₁ with (h₁₁ | h₁₁) <;> simp [h₁₀, h₁₁, Nat.add_mod, Nat.mod_mod] at h₉ ⊢ <;> omega
        -- Convert the modulo condition to evenness
        constructor
        · -- Prove the forward direction of the equivalence
          intro h₈
          have h₉ : Even (d (n - 1)) := h₈
          have h₁₀ : d (n - 1) % 2 = 0 := by
            rw [Nat.even_iff] at h₉
            omega
          have h₁₁ : d (n - 3) % 2 = 0 := by
            omega
          have h₁₂ : Even (d (n - 3)) := by
            rw [Nat.even_iff]
            omega
          exact h₁₂
        · -- Prove the backward direction of the equivalence
          intro h₈
          have h₉ : Even (d (n - 3)) := h₈
          have h₁₀ : d (n - 3) % 2 = 0 := by
            rw [Nat.even_iff] at h₉
            omega
          have h₁₁ : d (n - 1) % 2 = 0 := by
            omega
          have h₁₂ : Even (d (n - 1)) := by
            rw [Nat.even_iff]
            omega
          exact h₁₂
      exact h₅
    · -- Prove the backward direction: if (Even a ↔ Even b), then Even (a + b)
      intro h
      have h₄ : (Even (d (n - 1)) ↔ Even (d (n - 3))) := h
      have h₅ : Even (d (n - 1) + d (n - 3)) := by
        -- Use the fact that a + b is even iff a and b have the same parity
        have h₆ : (d (n - 1) + d (n - 3)) % 2 = 0 := by
          have h₇ : d (n - 1) % 2 = d (n - 3) % 2 := by
            -- Convert the evenness condition to modulo 2
            have h₈ : (Even (d (n - 1)) ↔ Even (d (n - 3))) := h₄
            have h₉ : (d (n - 1) % 2 = 0 ↔ d (n - 3) % 2 = 0) := by
              constructor
              · -- Prove the forward direction of the equivalence
                intro h₁₀
                have h₁₁ : Even (d (n - 1)) := by
                  rw [Nat.even_iff]
                  omega
                have h₁₂ : Even (d (n - 3)) := by
                  have h₁₃ : Even (d (n - 1)) ↔ Even (d (n - 3)) := h₄
                  tauto
                rw [Nat.even_iff] at h₁₂
                omega
              · -- Prove the backward direction of the equivalence
                intro h₁₀
                have h₁₁ : Even (d (n - 3)) := by
                  rw [Nat.even_iff]
                  omega
                have h₁₂ : Even (d (n - 1)) := by
                  have h₁₃ : Even (d (n - 1)) ↔ Even (d (n - 3)) := h₄
                  tauto
                rw [Nat.even_iff] at h₁₂
                omega
            -- Use the modulo equivalence to get the result
            have h₁₀ : d (n - 1) % 2 = 0 ∨ d (n - 1) % 2 = 1 := by omega
            have h₁₁ : d (n - 3) % 2 = 0 ∨ d (n - 3) % 2 = 1 := by omega
            rcases h₁₀ with (h₁₀ | h₁₀) <;> rcases h₁₁ with (h₁₁ | h₁₁) <;> simp [h₁₀, h₁₁] at h₉ ⊢ <;> tauto
          -- Calculate (a + b) % 2
          have h₈ : (d (n - 1) + d (n - 3)) % 2 = 0 := by
            have h₉ : d (n - 1) % 2 = d (n - 3) % 2 := h₇
            have h₁₀ : (d (n - 1) + d (n - 3)) % 2 = (d (n - 1) % 2 + d (n - 3) % 2) % 2 := by
              simp [Nat.add_mod]
            rw [h₁₀]
            have h₁₁ : d (n - 1) % 2 = 0 ∨ d (n - 1) % 2 = 1 := by omega
            rcases h₁₁ with (h₁₁ | h₁₁) <;> simp [h₁₁, h₉, Nat.add_mod, Nat.mod_mod] <;> omega
          exact h₈
        -- Convert the modulo condition to evenness
        rw [Nat.even_iff]
        omega
      exact h₅
  
  have h_final : Even (d n) ↔ (Even (d (n - 1)) ↔ Even (d (n - 3))) := by
    rw [h_rec]
    exact h_main
  
  exact h_final

theorem h_odd_rec_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (n : ℕ) (hn : n ≥ 3) :
    Odd (d n) ↔ (Odd (d (n - 1)) ↔ Even (d (n - 3))) := by
  have h_main : d n = d (n - 1) + d (n - 3) := by
    have h₄ : d n = d (n - 1) + d (n - 3) := h₃ n hn
    exact h₄
  
  have h_sum_odd_iff : Odd (d (n - 1) + d (n - 3)) ↔ (Odd (d (n - 1)) ↔ ¬ Odd (d (n - 3))) := by
    have h₄ : Odd (d (n - 1) + d (n - 3)) ↔ (Odd (d (n - 1)) ↔ ¬ Odd (d (n - 3))) := by
      constructor
      · -- Prove the forward direction: if the sum is odd, then the parities are different
        intro h
        have h₅ : (d (n - 1) + d (n - 3)) % 2 = 1 := by
          cases' h with k hk
          omega
        have h₆ : d (n - 1) % 2 = 0 ∨ d (n - 1) % 2 = 1 := by omega
        have h₇ : d (n - 3) % 2 = 0 ∨ d (n - 3) % 2 = 1 := by omega
        rcases h₆ with (h₆ | h₆) <;> rcases h₇ with (h₇ | h₇) <;>
          simp [h₆, h₇, Nat.add_mod, Nat.mod_mod] at h₅ ⊢ <;>
          (try omega) <;>
          (try {
            simp_all [Nat.odd_iff_not_even, Nat.even_iff, Nat.odd_iff]
            <;>
            (try omega) <;>
            (try {
              aesop
            })
          }) <;>
          (try {
            simp_all [Nat.odd_iff_not_even, Nat.even_iff, Nat.odd_iff]
            <;>
            (try omega) <;>
            (try {
              aesop
            })
          })
      · -- Prove the reverse direction: if the parities are different, then the sum is odd
        intro h
        have h₅ : (d (n - 1) + d (n - 3)) % 2 = 1 := by
          have h₆ : d (n - 1) % 2 = 0 ∨ d (n - 1) % 2 = 1 := by omega
          have h₇ : d (n - 3) % 2 = 0 ∨ d (n - 3) % 2 = 1 := by omega
          rcases h₆ with (h₆ | h₆) <;> rcases h₇ with (h₇ | h₇) <;>
            simp [h₆, h₇, Nat.add_mod, Nat.mod_mod] <;>
            (try {
              simp_all [Nat.odd_iff_not_even, Nat.even_iff, Nat.odd_iff]
              <;>
              (try omega) <;>
              (try {
                aesop
              })
            }) <;>
            (try omega)
        have h₆ : Odd (d (n - 1) + d (n - 3)) := by
          rw [Nat.odd_iff]
          omega
        exact h₆
    exact h₄
  
  have h_not_odd_iff_even : (¬ Odd (d (n - 3))) ↔ Even (d (n - 3)) := by
    have h₄ : (¬ Odd (d (n - 3))) ↔ Even (d (n - 3)) := by
      constructor
      · -- Prove the forward direction: if not odd, then even
        intro h
        have h₅ : Even (d (n - 3)) := by
          rw [even_iff_two_dvd]
          have h₆ : d (n - 3) % 2 = 0 := by
            by_contra h₇
            have h₈ : d (n - 3) % 2 = 1 := by
              have h₉ : d (n - 3) % 2 = 1 := by
                have h₁₀ : d (n - 3) % 2 ≠ 0 := h₇
                have h₁₁ : d (n - 3) % 2 = 0 ∨ d (n - 3) % 2 = 1 := by omega
                cases h₁₁ with
                | inl h₁₁ => contradiction
                | inr h₁₁ => exact h₁₁
              exact h₉
            have h₉ : Odd (d (n - 3)) := by
              rw [Nat.odd_iff]
              omega
            contradiction
          omega
        exact h₅
      · -- Prove the reverse direction: if even, then not odd
        intro h
        have h₅ : ¬ Odd (d (n - 3)) := by
          intro h₆
          have h₇ : Even (d (n - 3)) := h
          rw [even_iff_two_dvd] at h₇
          rw [Nat.odd_iff] at h₆
          have h₈ : d (n - 3) % 2 = 1 := by omega
          have h₉ : d (n - 3) % 2 = 0 := by
            omega
          omega
        exact h₅
    exact h₄
  
  have h_final : Odd (d n) ↔ (Odd (d (n - 1)) ↔ Even (d (n - 3))) := by
    rw [h_main]
    have h₄ : Odd (d (n - 1) + d (n - 3)) ↔ (Odd (d (n - 1)) ↔ ¬ Odd (d (n - 3))) := h_sum_odd_iff
    have h₅ : (¬ Odd (d (n - 3))) ↔ Even (d (n - 3)) := h_not_odd_iff_even
    have h₆ : (Odd (d (n - 1)) ↔ ¬ Odd (d (n - 3))) ↔ (Odd (d (n - 1)) ↔ Even (d (n - 3))) := by
      constructor
      · -- Prove the forward direction: (A ↔ ¬B) → (A ↔ C)
        intro h
        have h₇ : (¬ Odd (d (n - 3))) ↔ Even (d (n - 3)) := h_not_odd_iff_even
        have h₈ : (Odd (d (n - 1)) ↔ ¬ Odd (d (n - 3))) := h
        have h₉ : (Odd (d (n - 1)) ↔ Even (d (n - 3))) := by
          rw [h₈]
          rw [h₇]
          <;>
          tauto
        exact h₉
      · -- Prove the reverse direction: (A ↔ C) → (A ↔ ¬B)
        intro h
        have h₇ : (¬ Odd (d (n - 3))) ↔ Even (d (n - 3)) := h_not_odd_iff_even
        have h₈ : (Odd (d (n - 1)) ↔ Even (d (n - 3))) := h
        have h₉ : (Odd (d (n - 1)) ↔ ¬ Odd (d (n - 3))) := by
          rw [h₈]
          rw [h₇]
          <;>
          tauto
        exact h₉
    rw [h₄]
    rw [h₆]
    <;>
    tauto
  
  exact h_final

theorem h_even5_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_even0 : Even (d 0)) (h_even1 : Even (d 1)) (h_odd2 : Odd (d 2))
    (h_even_rec : ∀ n ≥ 3, Even (d n) ↔ (Even (d (n - 1)) ↔ Even (d (n - 3))))
    (h_odd_rec : ∀ n ≥ 3, Odd (d n) ↔ (Odd (d (n - 1)) ↔ Even (d (n - 3)))) :
    Even (d 5) := by
  have h_d3 : d 3 = 1 := by
    have h₃₁ : d 3 = d 2 + d 0 := by
      have h₃₂ := h₃ 3 (by norm_num)
      norm_num at h₃₂ ⊢
      <;> linarith
    rw [h₃₁]
    <;> simp [h₂, h₀]
    <;> norm_num
  
  have h_d4 : d 4 = 1 := by
    have h₄₁ : d 4 = d 3 + d 1 := by
      have h₄₂ := h₃ 4 (by norm_num)
      norm_num at h₄₂ ⊢
      <;> linarith
    rw [h₄₁]
    <;> simp [h_d3, h₁]
    <;> norm_num
  
  have h_d5 : d 5 = 2 := by
    have h₅₁ : d 5 = d 4 + d 2 := by
      have h₅₂ := h₃ 5 (by norm_num)
      norm_num at h₅₂ ⊢
      <;> linarith
    rw [h₅₁]
    <;> simp [h_d4, h₂]
    <;> norm_num
  
  have h_even_d5 : Even (d 5) := by
    rw [h_d5]
    <;> simp [even_iff_two_dvd]
    <;> norm_num
  
  exact h_even_d5

theorem h_odd6_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_even0 : Even (d 0)) (h_even1 : Even (d 1)) (h_odd2 : Odd (d 2))
    (h_even_rec : ∀ n ≥ 3, Even (d n) ↔ (Even (d (n - 1)) ↔ Even (d (n - 3))))
    (h_odd_rec : ∀ n ≥ 3, Odd (d n) ↔ (Odd (d (n - 1)) ↔ Even (d (n - 3)))) :
    Odd (d 6) := by
  have h_d3 : d 3 = 1 := by
    have h₄ : d 3 = d 2 + d 0 := by
      have h₅ : d 3 = d (3 - 1) + d (3 - 3) := h₃ 3 (by norm_num)
      norm_num at h₅ ⊢
      <;> linarith
    rw [h₄]
    <;> simp [h₂, h₀]
    <;> norm_num
  
  have h_d4 : d 4 = 1 := by
    have h₄ : d 4 = d 3 + d 1 := by
      have h₅ : d 4 = d (4 - 1) + d (4 - 3) := h₃ 4 (by norm_num)
      norm_num at h₅ ⊢
      <;> linarith
    rw [h₄]
    <;> simp [h_d3, h₁]
    <;> norm_num
  
  have h_d5 : d 5 = 2 := by
    have h₄ : d 5 = d 4 + d 2 := by
      have h₅ : d 5 = d (5 - 1) + d (5 - 3) := h₃ 5 (by norm_num)
      norm_num at h₅ ⊢
      <;> linarith
    rw [h₄]
    <;> simp [h_d4, h₂]
    <;> norm_num
  
  have h_d6 : d 6 = 3 := by
    have h₄ : d 6 = d 5 + d 3 := by
      have h₅ : d 6 = d (6 - 1) + d (6 - 3) := h₃ 6 (by norm_num)
      norm_num at h₅ ⊢
      <;> linarith
    rw [h₄]
    <;> simp [h_d5, h_d3]
    <;> norm_num
  
  have h_main : Odd (d 6) := by
    rw [h_d6]
    <;>
    (try decide) <;>
    (try
      {
        use 1
        <;> norm_num
      }) <;>
    (try
      {
        simp [Nat.odd_iff_not_even, parity_simps]
        <;> decide
      })
    <;>
    (try
      {
        use 1
        <;> norm_num
      })
  
  exact h_main

theorem h_period_even_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_even_rec : ∀ n ≥ 3, Even (d n) ↔ (Even (d (n - 1)) ↔ Even (d (n - 3))))
    (h_odd_rec : ∀ n ≥ 3, Odd (d n) ↔ (Odd (d (n - 1)) ↔ Even (d (n - 3)))) (k : ℕ) :
    Even (d (k + 7)) ↔ Even (d k) := by
  have h_main : d (k + 7) % 2 = d k % 2 := by
    have h4 : d (k + 7) = d (k + 6) + d (k + 4) := by
      have h4₁ : k + 7 ≥ 3 := by
        omega
      have h4₂ : d (k + 7) = d (k + 7 - 1) + d (k + 7 - 3) := h₃ (k + 7) h4₁
      have h4₃ : k + 7 - 1 = k + 6 := by
        omega
      have h4₄ : k + 7 - 3 = k + 4 := by
        omega
      rw [h4₂, h4₃, h4₄]
      <;> ring_nf at *
      <;> simp_all
    have h5 : d (k + 6) = d (k + 5) + d (k + 3) := by
      have h5₁ : k + 6 ≥ 3 := by
        omega
      have h5₂ : d (k + 6) = d (k + 6 - 1) + d (k + 6 - 3) := h₃ (k + 6) h5₁
      have h5₃ : k + 6 - 1 = k + 5 := by
        omega
      have h5₄ : k + 6 - 3 = k + 3 := by
        omega
      rw [h5₂, h5₃, h5₄]
      <;> ring_nf at *
      <;> simp_all
    have h6 : d (k + 5) = d (k + 4) + d (k + 2) := by
      have h6₁ : k + 5 ≥ 3 := by
        omega
      have h6₂ : d (k + 5) = d (k + 5 - 1) + d (k + 5 - 3) := h₃ (k + 5) h6₁
      have h6₃ : k + 5 - 1 = k + 4 := by
        omega
      have h6₄ : k + 5 - 3 = k + 2 := by
        omega
      rw [h6₂, h6₃, h6₄]
      <;> ring_nf at *
      <;> simp_all
    have h7 : d (k + 3) = d (k + 2) + d k := by
      have h7₁ : k + 3 ≥ 3 := by
        omega
      have h7₂ : d (k + 3) = d (k + 3 - 1) + d (k + 3 - 3) := h₃ (k + 3) h7₁
      have h7₃ : k + 3 - 1 = k + 2 := by
        omega
      have h7₄ : k + 3 - 3 = k := by
        omega
      rw [h7₂, h7₃, h7₄]
      <;> ring_nf at *
      <;> simp_all
    have h8 : d (k + 7) = 2 * d (k + 4) + d (k + 2) + d (k + 3) := by
      calc
        d (k + 7) = d (k + 6) + d (k + 4) := by rw [h4]
        _ = (d (k + 5) + d (k + 3)) + d (k + 4) := by rw [h5]
        _ = (d (k + 4) + d (k + 2)) + d (k + 3) + d (k + 4) := by
          rw [h6]
          <;> ring_nf at *
          <;> simp_all [add_assoc]
        _ = 2 * d (k + 4) + d (k + 2) + d (k + 3) := by
          ring_nf at *
          <;> omega
    have h9 : d (k + 7) % 2 = (d (k + 2) + d (k + 3)) % 2 := by
      have h9₁ : d (k + 7) = 2 * d (k + 4) + d (k + 2) + d (k + 3) := h8
      rw [h9₁]
      have h9₂ : (2 * d (k + 4) + d (k + 2) + d (k + 3)) % 2 = (d (k + 2) + d (k + 3)) % 2 := by
        have h9₃ : (2 * d (k + 4)) % 2 = 0 := by
          have h9₄ : (2 * d (k + 4)) % 2 = 0 := by
            simp [Nat.mul_mod, Nat.mod_mod]
          exact h9₄
        have h9₅ : (2 * d (k + 4) + d (k + 2) + d (k + 3)) % 2 = ((2 * d (k + 4)) % 2 + (d (k + 2) % 2) + (d (k + 3) % 2)) % 2 := by
          simp [Nat.add_mod]
        rw [h9₅]
        have h9₆ : ((2 * d (k + 4)) % 2 + (d (k + 2) % 2) + (d (k + 3) % 2)) % 2 = (0 + (d (k + 2) % 2) + (d (k + 3) % 2)) % 2 := by
          rw [h9₃]
          <;> simp [Nat.add_mod]
        rw [h9₆]
        have h9₇ : (0 + (d (k + 2) % 2) + (d (k + 3) % 2)) % 2 = ((d (k + 2) % 2) + (d (k + 3) % 2)) % 2 := by
          simp [Nat.add_mod]
        rw [h9₇]
        have h9₈ : ((d (k + 2) % 2) + (d (k + 3) % 2)) % 2 = (d (k + 2) + d (k + 3)) % 2 := by
          have h9₉ : (d (k + 2) + d (k + 3)) % 2 = ((d (k + 2) % 2) + (d (k + 3) % 2)) % 2 := by
            simp [Nat.add_mod]
          omega
        rw [h9₈]
        <;> simp [Nat.add_mod]
      rw [h9₂]
      <;> simp [Nat.add_mod]
    have h10 : (d (k + 2) + d (k + 3)) % 2 = d k % 2 := by
      have h10₁ : d (k + 3) = d (k + 2) + d k := h7
      rw [h10₁]
      have h10₂ : (d (k + 2) + (d (k + 2) + d k)) % 2 = d k % 2 := by
        have h10₃ : (d (k + 2) + (d (k + 2) + d k)) % 2 = (2 * d (k + 2) + d k) % 2 := by
          ring_nf at *
          <;> omega
        rw [h10₃]
        have h10₄ : (2 * d (k + 2) + d k) % 2 = d k % 2 := by
          have h10₅ : (2 * d (k + 2)) % 2 = 0 := by
            simp [Nat.mul_mod, Nat.mod_mod]
          have h10₆ : (2 * d (k + 2) + d k) % 2 = ((2 * d (k + 2)) % 2 + d k % 2) % 2 := by
            simp [Nat.add_mod]
          rw [h10₆]
          have h10₇ : ((2 * d (k + 2)) % 2 + d k % 2) % 2 = (0 + d k % 2) % 2 := by
            rw [h10₅]
            <;> simp [Nat.add_mod]
          rw [h10₇]
          have h10₈ : (0 + d k % 2) % 2 = d k % 2 := by
            simp [Nat.add_mod]
          rw [h10₈]
        rw [h10₄]
      omega
    have h11 : d (k + 7) % 2 = d k % 2 := by
      calc
        d (k + 7) % 2 = (d (k + 2) + d (k + 3)) % 2 := by rw [h9]
        _ = d k % 2 := by rw [h10]
    exact h11
  
  have h_final : Even (d (k + 7)) ↔ Even (d k) := by
    have h₁₂ : d (k + 7) % 2 = d k % 2 := h_main
    have h₁₃ : Even (d (k + 7)) ↔ Even (d k) := by
      constructor
      · -- Prove the forward direction: if d (k + 7) is even, then d k is even.
        intro h
        have h₁₄ : d (k + 7) % 2 = 0 := by
          rw [even_iff_two_dvd] at h
          omega
        have h₁₅ : d k % 2 = 0 := by
          omega
        rw [even_iff_two_dvd]
        omega
      · -- Prove the reverse direction: if d k is even, then d (k + 7) is even.
        intro h
        have h₁₄ : d k % 2 = 0 := by
          rw [even_iff_two_dvd] at h
          omega
        have h₁₅ : d (k + 7) % 2 = 0 := by
          omega
        rw [even_iff_two_dvd]
        omega
    exact h₁₃
  
  exact h_final

theorem h_even2021_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_even5 : Even (d 5)) (h_mod2021 : 2021 % 7 = 5)
    (h_period_even : ∀ k : ℕ, Even (d (k + 7)) ↔ Even (d k)) :
    Even (d 2021) := by
  have h_parity_lemma : ∀ k : ℕ, Even (d (5 + 7 * k)) ↔ Even (d 5) := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      have h₁ : Even (d (5 + 7 * (k + 1))) ↔ Even (d ((5 + 7 * k) + 7)) := by
        congr 1 <;> ring_nf
        <;> simp [mul_add, add_mul, mul_one, mul_comm, mul_left_comm, mul_assoc]
        <;> ring_nf at *
        <;> omega
      have h₂ : Even (d ((5 + 7 * k) + 7)) ↔ Even (d (5 + 7 * k)) := by
        have h₃ := h_period_even (5 + 7 * k)
        simpa [add_assoc] using h₃
      have h₃ : Even (d (5 + 7 * k)) ↔ Even (d 5) := ih
      calc
        Even (d (5 + 7 * (k + 1))) ↔ Even (d ((5 + 7 * k) + 7)) := by rw [h₁]
        _ ↔ Even (d (5 + 7 * k)) := by rw [h₂]
        _ ↔ Even (d 5) := by rw [h₃]
  
  have h_2021_eq : 2021 = 5 + 7 * 288 := by
    norm_num
  
  have h_main : Even (d 2021) ↔ Even (d 5) := by
    have h₁ : Even (d (5 + 7 * 288)) ↔ Even (d 5) := h_parity_lemma 288
    have h₂ : 2021 = 5 + 7 * 288 := h_2021_eq
    have h₃ : Even (d 2021) ↔ Even (d (5 + 7 * 288)) := by
      rw [h₂]
    rw [h₃]
    exact h₁
  
  have h_final : Even (d 2021) := by
    have h₁ : Even (d 2021) ↔ Even (d 5) := h_main
    have h₂ : Even (d 5) := h_even5
    have h₃ : Even (d 2021) := by
      rw [h₁] at *
      exact h₂
    exact h₃
  
  exact h_final

theorem h_odd2022_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_odd6 : Odd (d 6)) (h_mod2022 : 2022 % 7 = 6)
    (h_period_odd : ∀ k : ℕ, Odd (d (k + 7)) ↔ Odd (d k)) :
    Odd (d 2022) := by
  have h_main : ∀ m : ℕ, Odd (d (6 + 7 * m)) ↔ Odd (d 6) := by
    intro m
    induction m with
    | zero =>
      simp
    | succ m ih =>
      have h₁ : Odd (d (6 + 7 * m.succ)) ↔ Odd (d (6 + 7 * m)) := by
        have h₂ : 6 + 7 * m.succ = (6 + 7 * m) + 7 := by
          simp [Nat.mul_succ, Nat.add_assoc]
          <;> ring_nf at *
          <;> omega
        rw [h₂]
        have h₃ := h_period_odd (6 + 7 * m)
        simp [Nat.add_assoc] at h₃ ⊢
        <;> tauto
      have h₂ : Odd (d (6 + 7 * m)) ↔ Odd (d 6) := ih
      have h₃ : Odd (d (6 + 7 * m.succ)) ↔ Odd (d 6) := by
        rw [h₁]
        rw [h₂]
      exact h₃
  
  have h_2022 : 2022 = 6 + 7 * 288 := by
    norm_num
    <;> rfl
  
  have h_odd2022 : Odd (d 2022) := by
    have h₁ : Odd (d (6 + 7 * 288)) ↔ Odd (d 6) := h_main 288
    have h₂ : 2022 = 6 + 7 * 288 := h_2022
    have h₃ : Odd (d 2022) ↔ Odd (d (6 + 7 * 288)) := by
      rw [h₂]
    have h₄ : Odd (d (6 + 7 * 288)) ↔ Odd (d 6) := h_main 288
    have h₅ : Odd (d 6) := h_odd6
    have h₆ : Odd (d (6 + 7 * 288)) := by
      rw [h₄] at *
      exact h₅
    have h₇ : Odd (d 2022) := by
      rw [h₃] at *
      exact h₆
    exact h₇
  
  exact h_odd2022

theorem h_even2023_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_even0' : Even (d 0)) (h_mod2023 : 2023 % 7 = 0)
    (h_period_even : ∀ k : ℕ, Even (d (k + 7)) ↔ Even (d k)) :
    Even (d 2023) := by
  have h_main : ∀ (k : ℕ), Even (d (7 * k)) ↔ Even (d 0) := by
    intro k
    have h₄ : ∀ (k : ℕ), Even (d (7 * k)) ↔ Even (d 0) := by
      intro k
      induction k with
      | zero =>
        simp [h₀]
        <;>
        simp_all [Nat.even_iff]
        <;>
        norm_num
      | succ k ih =>
        have h₅ : Even (d (7 * k.succ)) ↔ Even (d (7 * k + 7)) := by
          have h₅₁ : 7 * k.succ = 7 * k + 7 := by
            simp [Nat.mul_succ, Nat.add_assoc]
            <;> ring_nf
            <;> omega
          rw [h₅₁]
          <;>
          simp [Nat.even_iff]
          <;>
          ring_nf
          <;>
          simp_all [Nat.even_iff]
          <;>
          omega
        have h₆ : Even (d (7 * k + 7)) ↔ Even (d (7 * k)) := by
          have h₆₁ := h_period_even (7 * k)
          simp [Nat.add_assoc] at h₆₁ ⊢
          <;>
          tauto
        have h₇ : Even (d (7 * k)) ↔ Even (d 0) := ih
        have h₈ : Even (d (7 * k.succ)) ↔ Even (d 0) := by
          calc
            Even (d (7 * k.succ)) ↔ Even (d (7 * k + 7)) := by rw [h₅]
            _ ↔ Even (d (7 * k)) := by rw [h₆]
            _ ↔ Even (d 0) := by rw [h₇]
        exact h₈
    exact h₄ k
  
  have h_2023 : Even (d 2023) := by
    have h₅ : Even (d (7 * 289)) ↔ Even (d 0) := h_main 289
    have h₆ : 7 * 289 = 2023 := by norm_num
    have h₇ : Even (d 2023) ↔ Even (d 0) := by
      rw [← h₆]
      exact h₅
    have h₈ : Even (d 0) := by
      rw [h₀]
      <;> simp [Nat.even_iff]
    have h₉ : Even (d 2023) := by
      rw [h₇]
      exact h₈
    exact h₉
  
  exact h_2023

theorem h_period_odd_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_even_rec : ∀ n ≥ 3, Even (d n) ↔ (Even (d (n - 1)) ↔ Even (d (n - 3))))
    (h_odd_rec : ∀ n ≥ 3, Odd (d n) ↔ (Odd (d (n - 1)) ↔ Even (d (n - 3)))) (k : ℕ) :
    Odd (d (k + 7)) ↔ Odd (d k) := by
  have h₄ : d 3 = 1 := by
    have h₄₁ : d 3 = d 2 + d 0 := by
      have h₄₂ : d 3 = d (3 - 1) + d (3 - 3) := h₃ 3 (by norm_num)
      norm_num at h₄₂ ⊢
      <;> linarith
    rw [h₄₁]
    <;> simp [h₀, h₂]
    <;> norm_num
  
  have h₅ : d 4 = 1 := by
    have h₅₁ : d 4 = d 3 + d 1 := by
      have h₅₂ : d 4 = d (4 - 1) + d (4 - 3) := h₃ 4 (by norm_num)
      norm_num at h₅₂ ⊢
      <;> linarith
    rw [h₅₁]
    <;> simp [h₁, h₄]
    <;> norm_num
  
  have h₆ : d 5 = 2 := by
    have h₆₁ : d 5 = d 4 + d 2 := by
      have h₆₂ : d 5 = d (5 - 1) + d (5 - 3) := h₃ 5 (by norm_num)
      norm_num at h₆₂ ⊢
      <;> linarith
    rw [h₆₁]
    <;> simp [h₂, h₅]
    <;> norm_num
  
  have h₇ : d 6 = 3 := by
    have h₇₁ : d 6 = d 5 + d 3 := by
      have h₇₂ : d 6 = d (6 - 1) + d (6 - 3) := h₃ 6 (by norm_num)
      norm_num at h₇₂ ⊢
      <;> linarith
    rw [h₇₁]
    <;> simp [h₄, h₆]
    <;> norm_num
  
  have h₈ : d 7 = 4 := by
    have h₈₁ : d 7 = d 6 + d 4 := by
      have h₈₂ : d 7 = d (7 - 1) + d (7 - 3) := h₃ 7 (by norm_num)
      norm_num at h₈₂ ⊢
      <;> linarith
    rw [h₈₁]
    <;> simp [h₅, h₇]
    <;> norm_num
  
  have h₉ : d 8 = 6 := by
    have h₉₁ : d 8 = d 7 + d 5 := by
      have h₉₂ : d 8 = d (8 - 1) + d (8 - 3) := h₃ 8 (by norm_num)
      norm_num at h₉₂ ⊢
      <;> linarith
    rw [h₉₁]
    <;> simp [h₆, h₈]
    <;> norm_num
  
  have h₁₀ : d 9 = 9 := by
    have h₁₀₁ : d 9 = d 8 + d 6 := by
      have h₁₀₂ : d 9 = d (9 - 1) + d (9 - 3) := h₃ 9 (by norm_num)
      norm_num at h₁₀₂ ⊢
      <;> linarith
    rw [h₁₀₁]
    <;> simp [h₇, h₉]
    <;> norm_num
  
  have h₁₁ : d 10 = 13 := by
    have h₁₁₁ : d 10 = d 9 + d 7 := by
      have h₁₁₂ : d 10 = d (10 - 1) + d (10 - 3) := h₃ 10 (by norm_num)
      norm_num at h₁₁₂ ⊢
      <;> linarith
    rw [h₁₁₁]
    <;> simp [h₈, h₁₀]
    <;> norm_num
  
  have h₁₂ : d 11 = 19 := by
    have h₁₂₁ : d 11 = d 10 + d 8 := by
      have h₁₂₂ : d 11 = d (11 - 1) + d (11 - 3) := h₃ 11 (by norm_num)
      norm_num at h₁₂₂ ⊢
      <;> linarith
    rw [h₁₂₁]
    <;> simp [h₉, h₁₁]
    <;> norm_num
  
  have h₁₃ : d 12 = 28 := by
    have h₁₃₁ : d 12 = d 11 + d 9 := by
      have h₁₃₂ : d 12 = d (12 - 1) + d (12 - 3) := h₃ 12 (by norm_num)
      norm_num at h₁₃₂ ⊢
      <;> linarith
    rw [h₁₃₁]
    <;> simp [h₁₀, h₁₂]
    <;> norm_num
  
  have h₁₄ : d 13 = 41 := by
    have h₁₄₁ : d 13 = d 12 + d 10 := by
      have h₁₄₂ : d 13 = d (13 - 1) + d (13 - 3) := h₃ 13 (by norm_num)
      norm_num at h₁₄₂ ⊢
      <;> linarith
    rw [h₁₄₁]
    <;> simp [h₁₁, h₁₃]
    <;> norm_num
  
  have h₁₅ : ∀ n, d (n + 7) % 2 = d n % 2 := by
    intro n
    have h₁₅₁ : ∀ n, d (n + 7) % 2 = d n % 2 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        match n with
        | 0 =>
          norm_num [h₀, h₁, h₂, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄] at *
          <;> simp_all [h₃, Nat.add_assoc]
          <;> norm_num
          <;> omega
        | 1 =>
          norm_num [h₀, h₁, h₂, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄] at *
          <;> simp_all [h₃, Nat.add_assoc]
          <;> norm_num
          <;> omega
        | 2 =>
          norm_num [h₀, h₁, h₂, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄] at *
          <;> simp_all [h₃, Nat.add_assoc]
          <;> norm_num
          <;> omega
        | 3 =>
          norm_num [h₀, h₁, h₂, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄] at *
          <;> simp_all [h₃, Nat.add_assoc]
          <;> norm_num
          <;> omega
        | 4 =>
          norm_num [h₀, h₁, h₂, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄] at *
          <;> simp_all [h₃, Nat.add_assoc]
          <;> norm_num
          <;> omega
        | 5 =>
          norm_num [h₀, h₁, h₂, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄] at *
          <;> simp_all [h₃, Nat.add_assoc]
          <;> norm_num
          <;> omega
        | 6 =>
          norm_num [h₀, h₁, h₂, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄] at *
          <;> simp_all [h₃, Nat.add_assoc]
          <;> norm_num
          <;> omega
        | n + 7 =>
          have h₁₅₂ := ih (n + 6) (by omega)
          have h₁₅₃ := ih (n + 4) (by omega)
          have h₁₅₄ := ih (n + 3) (by omega)
          have h₁₅₅ := ih (n + 2) (by omega)
          have h₁₅₆ := ih (n + 1) (by omega)
          have h₁₅₇ := ih n (by omega)
          simp [h₃, Nat.add_assoc] at h₁₅₂ h₁₅₃ h₁₅₄ h₁₅₅ h₁₅₆ h₁₅₇ ⊢
          <;>
            (try omega) <;>
            (try
              {
                cases n with
                | zero =>
                  norm_num [h₀, h₁, h₂, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄] at *
                  <;> simp_all [h₃, Nat.add_assoc]
                  <;> norm_num
                  <;> omega
                | succ n =>
                  simp_all [h₃, Nat.add_assoc]
                  <;>
                    (try omega) <;>
                    (try
                      {
                        ring_nf at *
                        <;> omega
                      })
              }) <;>
            (try
              {
                simp_all [h₃, Nat.add_assoc]
                <;>
                  (try omega) <;>
                  (try
                    {
                      ring_nf at *
                      <;> omega
                    })
              }) <;>
            (try omega)
    exact h₁₅₁ n
  
  have h₁₆ : Odd (d (k + 7)) ↔ Odd (d k) := by
    have h₁₆₁ : d (k + 7) % 2 = d k % 2 := h₁₅ k
    have h₁₆₂ : Odd (d (k + 7)) ↔ Odd (d k) := by
      have h₁₆₃ : d (k + 7) % 2 = d k % 2 := h₁₅ k
      have h₁₆₄ : Odd (d (k + 7)) ↔ d (k + 7) % 2 = 1 := by
        simp [Nat.odd_iff_not_even, Nat.even_iff, Nat.mod_eq_of_lt]
        <;>
        (try omega) <;>
        (try
          {
            cases' Nat.mod_two_eq_zero_or_one (d (k + 7)) with h h <;>
            simp [h, Nat.even_iff, Nat.odd_iff]
          })
      have h₁₆₅ : Odd (d k) ↔ d k % 2 = 1 := by
        simp [Nat.odd_iff_not_even, Nat.even_iff, Nat.mod_eq_of_lt]
        <;>
        (try omega) <;>
        (try
          {
            cases' Nat.mod_two_eq_zero_or_one (d k) with h h <;>
            simp [h, Nat.even_iff, Nat.odd_iff]
          })
      rw [h₁₆₄, h₁₆₅]
      <;>
      (try omega) <;>
      (try
        {
          have h₁₆₆ : d (k + 7) % 2 = d k % 2 := h₁₅ k
          omega
        })
    exact h₁₆₂
  
  exact h₁₆

theorem amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) :
    Even (d 2021) ∧ Odd (d 2022) ∧ Even (d 2023) := by
  have h_even0 : Even (d 0) :=
    h_even0_amc12a_2021_p8 d h₀ h₁ h₂ h₃
  have h_even1 : Even (d 1) :=
    h_even1_amc12a_2021_p8 d h₀ h₁ h₂ h₃
  have h_odd2 : Odd (d 2) :=
    h_odd2_amc12a_2021_p8 d h₀ h₁ h₂ h₃
  have h_even_rec (n : ℕ) (hn : n ≥ 3) :
      Even (d n) ↔ (Even (d (n - 1)) ↔ Even (d (n - 3))) :=
    h_even_rec_amc12a_2021_p8 d h₀ h₁ h₂ h₃ n hn
  have h_odd_rec (n : ℕ) (hn : n ≥ 3) :
      Odd (d n) ↔ (Odd (d (n - 1)) ↔ Even (d (n - 3))) :=
    h_odd_rec_amc12a_2021_p8 d h₀ h₁ h₂ h₃ n hn
  have h_even5 : Even (d 5) :=
    h_even5_amc12a_2021_p8 d h₀ h₁ h₂ h₃ h_even0 h_even1 h_odd2 h_even_rec h_odd_rec
  have h_odd6 : Odd (d 6) :=
    h_odd6_amc12a_2021_p8 d h₀ h₁ h₂ h₃ h_even0 h_even1 h_odd2 h_even_rec h_odd_rec
  have h_even0' : Even (d 0) :=
    h_even0'_amc12a_2021_p8 d h₀ h₁ h₂ h₃
  have h_mod2021 : 2021 % 7 = 5 :=
    h_mod2021_amc12a_2021_p8
  have h_mod2022 : 2022 % 7 = 6 :=
    h_mod2022_amc12a_2021_p8
  have h_mod2023 : 2023 % 7 = 0 :=
    h_mod2023_amc12a_2021_p8
  have h_period_even (k : ℕ) : Even (d (k + 7)) ↔ Even (d k) :=
    h_period_even_amc12a_2021_p8 d h₀ h₁ h₂ h₃ h_even_rec h_odd_rec k
  have h_period_odd (k : ℕ) : Odd (d (k + 7)) ↔ Odd (d k) :=
    h_period_odd_amc12a_2021_p8 d h₀ h₁ h₂ h₃ h_even_rec h_odd_rec k
  have h_even2021 : Even (d 2021) :=
    h_even2021_amc12a_2021_p8 d h₀ h₁ h₂ h₃ h_even5 h_mod2021 h_period_even
  have h_odd2022 : Odd (d 2022) :=
    h_odd2022_amc12a_2021_p8 d h₀ h₁ h₂ h₃ h_odd6 h_mod2022 h_period_odd
  have h_even2023 : Even (d 2023) :=
    h_even2023_amc12a_2021_p8 d h₀ h₁ h₂ h₃ h_even0' h_mod2023 h_period_even
  exact And.intro h_even2021 (And.intro h_odd2022 h_even2023)

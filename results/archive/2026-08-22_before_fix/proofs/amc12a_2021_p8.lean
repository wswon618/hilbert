import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h_even0_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) : Even (d 0) := by
  rw [h₀]
  <;> simp [Nat.even_iff]
  <;> norm_num
  <;> decide

theorem h_even1_amc12a_2021_p8 (d : ℕ → ℕ) (h₁ : d 1 = 0) : Even (d 1) := by
  rw [h₁]
  <;> simp [even_iff_two_dvd]
  <;> norm_num
  <;> decide

theorem h_odd2_amc12a_2021_p8 (d : ℕ → ℕ) (h₂ : d 2 = 1) : Odd (d 2) := by
  have h₃ : Odd (d 2) := by
    rw [h₂]
    -- We need to show that 1 is odd. By definition, an odd number is of the form 2k + 1.
    -- For 1, we can take k = 0, so 1 = 2*0 + 1.
    exact ⟨0, by decide⟩
  exact h₃

theorem h_mod2021_amc12a_2021_p8 : 2021 = 7 * 288 + 5 := by
  norm_num
  <;> rfl

theorem h_mod2022_amc12a_2021_p8 : 2022 = 7 * 288 + 6 := by
  norm_num
  <;> rfl

theorem h_mod2023_amc12a_2021_p8 : 2023 = 7 * 288 + 7 := by
  norm_num
  <;> rfl
  <;> simp_all
  <;> norm_num
  <;> rfl

theorem h_res2022_amc12a_2021_p8 (d : ℕ → ℕ) (h_not_even2022 : ¬Even (d 2022)) : Odd (d 2022) := by
  rcases (Nat.even_or_odd (d 2022)) with h_even | h_odd
  · exact (h_not_even2022 h_even).elim
  · exact h_odd

theorem h_odd3_amc12a_2021_p8 (d : ℕ → ℕ) (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_even0 : Even (d 0)) (h_even1 : Even (d 1)) (h_odd2 : Odd (d 2)) :
    Odd (d 3) := by
  have h_d3 : d 3 = d 2 + d 0 := by
    have h₄ : d 3 = d 2 + d 0 := by
      have h₅ : d 3 = d (3 - 1) + d (3 - 3) := by
        apply h₃
        <;> norm_num
      norm_num at h₅ ⊢
      <;> linarith
    exact h₄
  
  have h_main : Odd (d 3) := by
    rw [h_d3]
    -- We need to show that d 2 + d 0 is odd.
    -- Since d 2 is odd and d 0 is even, their sum is odd.
    cases' h_odd2 with k hk
    cases' h_even0 with m hm
    -- Substitute the expressions for d 2 and d 0
    rw [hk, hm]
    -- Simplify the expression to show it is odd
    use k + m
    <;> ring_nf at *
    <;> omega
  
  exact h_main

theorem h_even_rec_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) (n : ℕ) (hn : n ≥ 3) :
    Even (d n) ↔ (Even (d (n - 1)) ↔ Even (d (n - 3))) := by
  have h_main_lemma : ∀ (a b : ℕ), Even (a + b) ↔ (Even a ↔ Even b) := by
    intro a b
    have h₁ : Even (a + b) ↔ (Even a ↔ Even b) := by
      constructor
      · -- Prove the forward direction: if a + b is even, then (Even a ↔ Even b)
        intro h
        have h₂ : a % 2 = 0 ∨ a % 2 = 1 := by omega
        have h₃ : b % 2 = 0 ∨ b % 2 = 1 := by omega
        rcases h₂ with (h₂ | h₂) <;> rcases h₃ with (h₃ | h₃) <;>
          simp [h₂, h₃, Nat.even_iff, Nat.add_mod, Nat.mod_mod] at h ⊢ <;>
          (try omega) <;> (try tauto)
      · -- Prove the reverse direction: if (Even a ↔ Even b), then a + b is even
        intro h
        have h₂ : a % 2 = 0 ∨ a % 2 = 1 := by omega
        have h₃ : b % 2 = 0 ∨ b % 2 = 1 := by omega
        rcases h₂ with (h₂ | h₂) <;> rcases h₃ with (h₃ | h₃) <;>
          simp [h₂, h₃, Nat.even_iff, Nat.add_mod, Nat.mod_mod] at h ⊢ <;>
          (try omega) <;> (try tauto)
    exact h₁
  
  have h_rec : d n = d (n - 1) + d (n - 3) := by
    have h₄ : d n = d (n - 1) + d (n - 3) := h₃ n hn
    exact h₄
  
  have h_final : Even (d n) ↔ (Even (d (n - 1)) ↔ Even (d (n - 3))) := by
    rw [h_rec]
    have h₅ : Even (d (n - 1) + d (n - 3)) ↔ (Even (d (n - 1)) ↔ Even (d (n - 3))) := by
      apply h_main_lemma
    exact h₅
  
  exact h_final

theorem h_even4_amc12a_2021_p8 (d : ℕ → ℕ) (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_even1 : Even (d 1)) (h_even3 : Even (d 3) ↔ False) :
    Even (d 4) ↔ False := by
  have h_d4 : d 4 = d 3 + d 1 := by
    have h₄ : d 4 = d (4 - 1) + d (4 - 3) := by
      apply h₃
      <;> norm_num
    norm_num at h₄ ⊢
    <;> linarith
  
  have h_d3_odd : d 3 % 2 = 1 := by
    have h₄ : ¬Even (d 3) := by
      rw [h_even3]
      <;> simp
    have h₅ : d 3 % 2 = 1 := by
      have h₆ : d 3 % 2 ≠ 0 := by
        intro h₇
        have h₈ : Even (d 3) := by
          rw [even_iff_two_dvd]
          omega
        contradiction
      have h₉ : d 3 % 2 = 0 ∨ d 3 % 2 = 1 := by omega
      cases h₉ with
      | inl h₉ =>
        exfalso
        apply h₆
        exact h₉
      | inr h₉ =>
        exact h₉
    exact h₅
  
  have h_d1_even : d 1 % 2 = 0 := by
    have h₄ : Even (d 1) := h_even1
    rw [even_iff_two_dvd] at h₄
    have h₅ : 2 ∣ d 1 := h₄
    have h₆ : d 1 % 2 = 0 := by
      omega
    exact h₆
  
  have h_d4_odd : d 4 % 2 = 1 := by
    have h₄ : d 4 = d 3 + d 1 := h_d4
    rw [h₄]
    have h₅ : (d 3 + d 1) % 2 = 1 := by
      have h₆ : d 3 % 2 = 1 := h_d3_odd
      have h₇ : d 1 % 2 = 0 := h_d1_even
      have h₈ : (d 3 + d 1) % 2 = (d 3 % 2 + d 1 % 2) % 2 := by
        omega
      rw [h₈]
      omega
    omega
  
  have h_main : Even (d 4) ↔ False := by
    constructor
    · intro h
      have h₁ : Even (d 4) := h
      rw [even_iff_two_dvd] at h₁
      have h₂ : 2 ∣ d 4 := h₁
      have h₃ : d 4 % 2 = 0 := by
        omega
      omega
    · intro h
      exfalso
      exact h
  
  exact h_main

theorem h_odd4_amc12a_2021_p8 (d : ℕ → ℕ) (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_even1 : Even (d 1)) (h_even3 : Even (d 3) ↔ False) :
    Odd (d 4) := by
  have h_d4 : d 4 = d 3 + d 1 := by
    have h₄ : d 4 = d 3 + d 1 := by
      have h₅ : d 4 = d (4 - 1) + d (4 - 3) := by
        apply h₃
        <;> norm_num
      norm_num at h₅ ⊢
      <;> linarith
    exact h₄
  
  have h_d1_even : d 1 % 2 = 0 := by
    have h₁ : Even (d 1) := h_even1
    rw [even_iff_two_dvd] at h₁
    have h₂ : d 1 % 2 = 0 := by
      omega
    exact h₂
  
  have h_d3_odd : d 3 % 2 = 1 := by
    have h₁ : ¬Even (d 3) := by
      by_contra h
      have h₂ : Even (d 3) := h
      have h₃ : Even (d 3) ↔ False := h_even3
      have h₄ : False := by
        rw [h₃] at h₂
        exact h₂
      exact h₄
    have h₂ : d 3 % 2 = 1 := by
      have h₃ : d 3 % 2 = 0 ∨ d 3 % 2 = 1 := by
        have : d 3 % 2 < 2 := Nat.mod_lt _ (by norm_num)
        omega
      cases h₃ with
      | inl h₃ =>
        have h₄ : Even (d 3) := by
          rw [even_iff_two_dvd]
          have : d 3 % 2 = 0 := h₃
          omega
        contradiction
      | inr h₃ =>
        exact h₃
    exact h₂
  
  have h_d4_mod : (d 3 + d 1) % 2 = 1 := by
    have h₁ : (d 3 + d 1) % 2 = 1 := by
      have h₂ : d 3 % 2 = 1 := h_d3_odd
      have h₃ : d 1 % 2 = 0 := h_d1_even
      have h₄ : (d 3 + d 1) % 2 = (d 3 % 2 + d 1 % 2) % 2 := by
        simp [Nat.add_mod]
      rw [h₄]
      have h₅ : (d 3 % 2 + d 1 % 2) % 2 = (1 + 0) % 2 := by
        rw [h₂, h₃]
        <;> norm_num
      rw [h₅]
      <;> norm_num
    exact h₁
  
  have h_d4_odd : Odd (d 4) := by
    rw [h_d4]
    have h₁ : (d 3 + d 1) % 2 = 1 := h_d4_mod
    have h₂ : Odd (d 3 + d 1) := by
      rw [Nat.odd_iff]
      <;> omega
    exact h₂
  
  exact h_d4_odd

theorem h_even3_amc12a_2021_p8 (d : ℕ → ℕ) (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_even0 : Even (d 0)) (h_even1 : Even (d 1)) (h_odd2 : Odd (d 2)) :
    Even (d 3) ↔ False := by
  have h_d3 : d 3 = d 2 + d 0 := by
    have h₃' : d 3 = d 2 + d 0 := by
      have h₄ : d 3 = d (3 - 1) + d (3 - 3) := h₃ 3 (by norm_num)
      norm_num at h₄ ⊢
      <;> linarith
    exact h₃'
  
  have h_d0_mod2 : d 0 % 2 = 0 := by
    have h₁ : Even (d 0) := h_even0
    rw [even_iff_two_dvd] at h₁
    have h₂ : 2 ∣ d 0 := h₁
    have h₃ : d 0 % 2 = 0 := by
      omega
    exact h₃
  
  have h_d2_mod2 : d 2 % 2 = 1 := by
    cases' h_odd2 with k hk
    have h₁ : d 2 = 2 * k + 1 := by omega
    have h₂ : d 2 % 2 = 1 := by
      rw [h₁]
      have h₃ : (2 * k + 1) % 2 = 1 := by
        have h₄ : (2 * k + 1) % 2 = 1 := by
          omega
        exact h₄
      exact h₃
    exact h₂
  
  have h_d3_mod2 : d 3 % 2 = 1 := by
    have h₁ : d 3 = d 2 + d 0 := h_d3
    rw [h₁]
    have h₂ : (d 2 + d 0) % 2 = 1 := by
      have h₃ : d 2 % 2 = 1 := h_d2_mod2
      have h₄ : d 0 % 2 = 0 := h_d0_mod2
      have h₅ : (d 2 + d 0) % 2 = (d 2 % 2 + d 0 % 2) % 2 := by
        simp [Nat.add_mod]
      rw [h₅]
      have h₆ : (d 2 % 2 + d 0 % 2) % 2 = (1 + 0) % 2 := by
        rw [h₃, h₄]
        <;> norm_num
      rw [h₆]
      <;> norm_num
    exact h₂
  
  have h_main : ¬ Even (d 3) := by
    intro h_even_d3
    have h₁ : d 3 % 2 = 0 := by
      rw [even_iff_two_dvd] at h_even_d3
      have h₂ : 2 ∣ d 3 := h_even_d3
      omega
    have h₂ : d 3 % 2 = 1 := h_d3_mod2
    omega
  
  have h_final : Even (d 3) ↔ False := by
    constructor
    · intro h
      exfalso
      exact h_main h
    · intro h
      exfalso
      exact h
  
  exact h_final

theorem h_odd5_amc12a_2021_p8 (d : ℕ → ℕ) (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_even4 : Even (d 4) ↔ False) (h_odd2 : Odd (d 2)) :
    Odd (d 5) ↔ False := by
  have h_d5 : d 5 = d 4 + d 2 := by
    have h₅ : d 5 = d 4 + d 2 := by
      have h₅₁ : d 5 = d (5 - 1) + d (5 - 3) := h₃ 5 (by norm_num)
      norm_num at h₅₁ ⊢
      <;> linarith
    exact h₅
  
  have h_d4_odd : d 4 % 2 = 1 := by
    have h₁ : ¬Even (d 4) := by
      rw [h_even4]
      <;> simp
    have h₂ : d 4 % 2 = 1 := by
      have h₃ : d 4 % 2 ≠ 0 := by
        intro h
        have h₄ : Even (d 4) := by
          rw [Nat.even_iff]
          <;> omega
        contradiction
      have h₄ : d 4 % 2 = 0 ∨ d 4 % 2 = 1 := by omega
      cases h₄ with
      | inl h₄ =>
        exfalso
        apply h₃
        exact h₄
      | inr h₄ =>
        exact h₄
    exact h₂
  
  have h_d2_odd : d 2 % 2 = 1 := by
    have h₁ : Odd (d 2) := h_odd2
    have h₂ : d 2 % 2 = 1 := by
      rw [Nat.odd_iff] at h₁
      omega
    exact h₂
  
  have h_d5_even : d 5 % 2 = 0 := by
    have h₁ : d 5 = d 4 + d 2 := h_d5
    have h₂ : d 4 % 2 = 1 := h_d4_odd
    have h₃ : d 2 % 2 = 1 := h_d2_odd
    have h₄ : (d 4 + d 2) % 2 = 0 := by
      have h₅ : d 4 % 2 = 1 := h_d4_odd
      have h₆ : d 2 % 2 = 1 := h_d2_odd
      have h₇ : (d 4 + d 2) % 2 = 0 := by
        omega
      exact h₇
    have h₅ : d 5 % 2 = 0 := by
      rw [h₁]
      exact h₄
    exact h₅
  
  have h_main : Odd (d 5) ↔ False := by
    have h₁ : d 5 % 2 = 0 := h_d5_even
    have h₂ : ¬Odd (d 5) := by
      intro h_odd
      have h₃ : d 5 % 2 = 1 := by
        rw [Nat.odd_iff] at h_odd
        <;> omega
      omega
    constructor
    · intro h
      exfalso
      exact h₂ h
    · intro h
      exfalso
      exact False.elim h
  
  exact h_main

theorem h_even5_amc12a_2021_p8 (d : ℕ → ℕ) (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_even4 : Even (d 4) ↔ False) (h_odd2 : Odd (d 2)) :
    Even (d 5) := by
  have h_d5 : d 5 = d 4 + d 2 := by
    have h₁ : d 5 = d 4 + d 2 := by
      have h₂ : 5 ≥ 3 := by norm_num
      have h₃' : d 5 = d (5 - 1) + d (5 - 3) := h₃ 5 h₂
      norm_num at h₃' ⊢
      <;> linarith
    exact h₁
  
  have h_d4_mod2 : d 4 % 2 = 1 := by
    have h₁ : ¬Even (d 4) := by
      rw [h_even4]
      <;> simp
    have h₂ : d 4 % 2 = 1 := by
      have h₃ : d 4 % 2 = 0 ∨ d 4 % 2 = 1 := by omega
      cases h₃ with
      | inl h₃ =>
        have h₄ : Even (d 4) := by
          rw [even_iff_two_dvd]
          have h₅ : d 4 % 2 = 0 := h₃
          omega
        contradiction
      | inr h₃ =>
        exact h₃
    exact h₂
  
  have h_d2_mod2 : d 2 % 2 = 1 := by
    have h₁ : Odd (d 2) := h_odd2
    have h₂ : d 2 % 2 = 1 := by
      cases' h₁ with k hk
      have h₃ : d 2 = 2 * k + 1 := by omega
      have h₄ : d 2 % 2 = 1 := by
        omega
      exact h₄
    exact h₂
  
  have h_sum_mod2 : (d 4 + d 2) % 2 = 0 := by
    have h₁ : (d 4 + d 2) % 2 = (d 4 % 2 + d 2 % 2) % 2 := by
      simp [Nat.add_mod]
    rw [h₁]
    have h₂ : d 4 % 2 = 1 := h_d4_mod2
    have h₃ : d 2 % 2 = 1 := h_d2_mod2
    rw [h₂, h₃]
    <;> norm_num
    <;> omega
  
  have h_main : Even (d 5) := by
    rw [h_d5]
    rw [even_iff_two_dvd]
    have h₁ : (d 4 + d 2) % 2 = 0 := h_sum_mod2
    omega
  
  exact h_main

theorem h_even6_amc12a_2021_p8 (d : ℕ → ℕ) (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_even5 : Even (d 5)) (h_even3 : Even (d 3) ↔ False) :
    Even (d 6) ↔ False := by
  have h_d6 : d 6 = d 5 + d 3 := by
    have h₁ : d 6 = d 5 + d 3 := by
      have h₂ : d 6 = d (6 - 1) + d (6 - 3) := h₃ 6 (by norm_num)
      norm_num at h₂ ⊢
      <;> linarith
    exact h₁
  
  have h_d3_odd : d 3 % 2 = 1 := by
    have h₁ : ¬Even (d 3) := by
      by_contra h
      have h₂ : Even (d 3) := h
      have h₃ : Even (d 3) ↔ False := h_even3
      have h₄ : False := by
        rw [h₃] at h₂
        exact h₂
      exact h₄
    have h₂ : d 3 % 2 = 1 := by
      have h₃ : d 3 % 2 ≠ 0 := by
        intro h₄
        have h₅ : Even (d 3) := by
          rw [even_iff_two_dvd]
          omega
        contradiction
      have h₄ : d 3 % 2 = 0 ∨ d 3 % 2 = 1 := by omega
      cases h₄ with
      | inl h₄ =>
        exfalso
        apply h₃
        exact h₄
      | inr h₄ =>
        exact h₄
    exact h₂
  
  have h_d5_even : d 5 % 2 = 0 := by
    have h₁ : Even (d 5) := h_even5
    rw [even_iff_two_dvd] at h₁
    have h₂ : 2 ∣ d 5 := h₁
    have h₃ : d 5 % 2 = 0 := by
      omega
    exact h₃
  
  have h_d6_mod : d 6 % 2 = 1 := by
    have h₁ : d 6 = d 5 + d 3 := h_d6
    rw [h₁]
    have h₂ : (d 5 + d 3) % 2 = 1 := by
      have h₃ : d 5 % 2 = 0 := h_d5_even
      have h₄ : d 3 % 2 = 1 := h_d3_odd
      have h₅ : (d 5 + d 3) % 2 = (d 5 % 2 + d 3 % 2) % 2 := by
        simp [Nat.add_mod]
      rw [h₅]
      have h₆ : (d 5 % 2 + d 3 % 2) % 2 = (0 + 1) % 2 := by
        rw [h₃, h₄]
        <;> norm_num
      rw [h₆]
      <;> norm_num
    exact h₂
  
  have h_main : Even (d 6) ↔ False := by
    constructor
    · -- Prove the forward direction: if Even (d 6), then False
      intro h_even_d6
      have h₁ : d 6 % 2 = 0 := by
        rw [even_iff_two_dvd] at h_even_d6
        omega
      omega
    · -- Prove the backward direction: if False, then Even (d 6)
      intro h_false
      exfalso
      exact h_false
  
  exact h_main

theorem h_res2021_amc12a_2021_p8 (d : ℕ → ℕ) (h_even2021 : Even (d 2021) ↔ Even (d 5))
    (h_even5 : Even (d 5)) : Even (d 2021) := by
  have h_main : Even (d 2021) := by
    have h1 : Even (d 2021) ↔ Even (d 5) := h_even2021
    have h2 : Even (d 5) := h_even5
    -- Since h1 is an equivalence, we can use it to deduce Even (d 2021) from Even (d 5)
    have h3 : Even (d 2021) := by
      -- Use the forward direction of the equivalence
      have h4 : Even (d 2021) ↔ Even (d 5) := h_even2021
      -- Since Even (d 5) is true, we can use the equivalence to get Even (d 2021)
      have h5 : Even (d 2021) := by
        -- Use the fact that the equivalence is true and Even (d 5) is true
        have h6 : Even (d 5) := h_even5
        have h7 : Even (d 2021) ↔ Even (d 5) := h_even2021
        -- Use the equivalence to deduce Even (d 2021)
        have h8 : Even (d 2021) := by
          -- Since Even (d 5) is true, and the equivalence holds, Even (d 2021) must be true
          tauto
        exact h8
      exact h5
    exact h3
  
  exact h_main

theorem h_odd6_amc12a_2021_p8 (d : ℕ → ℕ) (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_even5 : Even (d 5)) (h_even3 : Even (d 3) ↔ False) :
    Odd (d 6) := by
  have h_d6 : d 6 = d 5 + d 3 := by
    have h₁ : d 6 = d 5 + d 3 := by
      have h₂ : 6 ≥ 3 := by norm_num
      have h₃' : d 6 = d (6 - 1) + d (6 - 3) := h₃ 6 h₂
      norm_num at h₃' ⊢
      <;> linarith
    exact h₁
  
  have h_not_even_d3 : ¬ Even (d 3) := by
    have h₁ : Even (d 3) ↔ False := h_even3
    have h₂ : ¬ Even (d 3) := by
      intro h
      have h₃ : Even (d 3) := h
      have h₄ : False := by
        have h₅ : Even (d 3) ↔ False := h_even3
        simp_all
      exact h₄
    exact h₂
  
  have h_odd_d3 : Odd (d 3) := by
    have h₁ : ¬ Even (d 3) := h_not_even_d3
    have h₂ : Even (d 3) ∨ Odd (d 3) := by
      apply Nat.even_or_odd
    cases h₂ with
    | inl h₂ =>
      exfalso
      apply h₁
      exact h₂
    | inr h₂ =>
      exact h₂
  
  have h_main : Odd (d 6) := by
    rw [h_d6]
    -- We need to show that d 5 + d 3 is odd.
    -- Since d 5 is even and d 3 is odd, their sum is odd.
    have h₁ : Even (d 5) := h_even5
    have h₂ : Odd (d 3) := h_odd_d3
    -- Use the fact that the sum of an even and an odd number is odd.
    cases' h₁ with k hk
    cases' h₂ with m hm
    use k + m
    rw [hk, hm]
    <;> ring_nf
    <;> omega
  
  exact h_main

theorem h_even2022_amc12a_2021_p8 (d : ℕ → ℕ) (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_period_even : ∀ n : ℕ, Even (d (n + 7)) ↔ Even (d n))
    (h_mod2022 : 2022 = 7 * 288 + 6) :
    Even (d 2022) ↔ Even (d 6) := by
  have h_period_even_k : ∀ (n k : ℕ), Even (d (n + 7 * k)) ↔ Even (d n) := by
    intro n
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      have h₁ : Even (d (n + 7 * k.succ)) ↔ Even (d (n + 7 * k + 7)) := by
        have h₂ : n + 7 * k.succ = n + 7 * k + 7 := by
          simp [Nat.mul_succ, Nat.add_assoc]
          <;> ring_nf at *
          <;> omega
        rw [h₂]
        <;> simp [Nat.add_assoc]
      rw [h₁]
      have h₂ : Even (d (n + 7 * k + 7)) ↔ Even (d (n + 7 * k)) := by
        have h₃ := h_period_even (n + 7 * k)
        simpa [Nat.add_assoc] using h₃
      rw [h₂]
      exact ih
  
  have h_main : Even (d 2022) ↔ Even (d 6) := by
    have h₁ : Even (d 2022) ↔ Even (d (6 + 7 * 288)) := by
      have h₂ : 2022 = 6 + 7 * 288 := by
        norm_num
      rw [h₂]
      <;> simp [Nat.add_assoc]
    rw [h₁]
    have h₂ : Even (d (6 + 7 * 288)) ↔ Even (d 6) := by
      have h₃ := h_period_even_k 6 288
      simpa [Nat.add_assoc] using h₃
    rw [h₂]
  
  exact h_main

theorem h_not_even2022_amc12a_2021_p8 (d : ℕ → ℕ) (h_even2022 : Even (d 2022) ↔ Even (d 6))
    (h_even6 : Even (d 6) ↔ False) : ¬Even (d 2022) := by
  have h1 : ¬Even (d 6) := by
    have h1' : Even (d 6) ↔ False := h_even6
    have h1'' : ¬Even (d 6) := by
      intro h
      have h2 : Even (d 6) := h
      have h3 : False := by
        rw [h1'] at h2
        exact h2
      exact h3
    exact h1''
  
  have h2 : ¬Even (d 2022) := by
    intro h_even2022'
    have h3 : Even (d 6) := by
      have h4 : Even (d 2022) ↔ Even (d 6) := h_even2022
      have h5 : Even (d 2022) := h_even2022'
      have h6 : Even (d 6) := by
        rw [h4] at *
        exact h5
      exact h6
    exact h1 h3
  
  exact h2

theorem h_even2021_amc12a_2021_p8 (d : ℕ → ℕ) (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_period_even : ∀ n : ℕ, Even (d (n + 7)) ↔ Even (d n))
    (h_mod2021 : 2021 = 7 * 288 + 5) :
    Even (d 2021) ↔ Even (d 5) := by
  have h_inductive_lemma : ∀ m : ℕ, Even (d (5 + 7 * m)) ↔ Even (d 5) := by
    intro m
    induction m with
    | zero =>
      -- Base case: when m = 0, 5 + 7 * 0 = 5
      simp [Nat.mul_zero, Nat.add_zero]
    | succ m ih =>
      -- Inductive step: assume the statement holds for m, prove for m + 1
      have h₁ : Even (d (5 + 7 * m.succ)) ↔ Even (d (5 + 7 * m)) := by
        -- Use the given periodicity condition to relate d(5 + 7 * (m + 1)) to d(5 + 7 * m)
        have h₂ : 5 + 7 * m.succ = (5 + 7 * m) + 7 := by
          simp [Nat.mul_succ, Nat.add_assoc]
          <;> ring_nf at *
          <;> omega
        rw [h₂]
        -- Apply the periodicity condition with n = 5 + 7 * m
        have h₃ := h_period_even (5 + 7 * m)
        simp [Nat.add_assoc] at h₃ ⊢
        <;> tauto
      -- Combine with the inductive hypothesis
      have h₄ : Even (d (5 + 7 * m)) ↔ Even (d 5) := ih
      -- Chain the equivalences
      have h₅ : Even (d (5 + 7 * m.succ)) ↔ Even (d 5) := by
        calc
          Even (d (5 + 7 * m.succ)) ↔ Even (d (5 + 7 * m)) := h₁
          _ ↔ Even (d 5) := h₄
      exact h₅
  
  have h_main : Even (d 2021) ↔ Even (d 5) := by
    have h₁ : 2021 = 5 + 7 * 288 := by
      norm_num [h_mod2021]
      <;> ring_nf at *
      <;> omega
    have h₂ : Even (d 2021) ↔ Even (d (5 + 7 * 288)) := by
      rw [h₁]
    have h₃ : Even (d (5 + 7 * 288)) ↔ Even (d 5) := h_inductive_lemma 288
    calc
      Even (d 2021) ↔ Even (d (5 + 7 * 288)) := h₂
      _ ↔ Even (d 5) := h₃
  
  exact h_main

theorem h_res2023_amc12a_2021_p8 (d : ℕ → ℕ) (h_even2023 : Even (d 2023) ↔ Even (d 0))
    (h_even0 : Even (d 0)) : Even (d 2023) := by
  have h_main : Even (d 2023) := by
    have h₁ : Even (d 2023) ↔ Even (d 0) := h_even2023
    have h₂ : Even (d 0) := h_even0
    -- Use the backward direction of the biconditional to deduce Even (d 2023)
    have h₃ : Even (d 2023) := by
      apply h₁.mpr
      exact h₂
    exact h₃
  
  exact h_main

theorem h_even2023_amc12a_2021_p8 (d : ℕ → ℕ) (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (h_period_even : ∀ n : ℕ, Even (d (n + 7)) ↔ Even (d n))
    (h_mod2023 : 2023 = 7 * 288 + 7) :
    Even (d 2023) ↔ Even (d 0) := by
  have h_main : ∀ (k : ℕ), Even (d (7 * k)) ↔ Even (d 0) := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      have h₁ : Even (d (7 * k + 7)) ↔ Even (d (7 * k)) := by
        have h₂ := h_period_even (7 * k)
        simpa [mul_add, add_mul, mul_one, mul_comm] using h₂
      have h₂ : Even (d (7 * (k + 1))) ↔ Even (d (7 * k)) := by
        have h₃ : 7 * (k + 1) = 7 * k + 7 := by ring
        rw [h₃]
        exact h₁
      have h₃ : Even (d (7 * (k + 1))) ↔ Even (d 0) := by
        calc
          Even (d (7 * (k + 1))) ↔ Even (d (7 * k)) := h₂
          _ ↔ Even (d 0) := ih
      simpa [mul_add, add_mul, mul_one, mul_comm] using h₃
  
  have h_2023_eq : 2023 = 7 * 289 := by
    norm_num [h_mod2023]
    <;> rfl
  
  have h_final : Even (d 2023) ↔ Even (d 0) := by
    have h₁ : Even (d 2023) ↔ Even (d (7 * 289)) := by
      rw [h_2023_eq]
    rw [h₁]
    have h₂ : Even (d (7 * 289)) ↔ Even (d 0) := h_main 289
    rw [h₂]
  
  exact h_final

theorem h_period_even_amc12a_2021_p8 (d : ℕ → ℕ)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) (n : ℕ) :
    Even (d (n + 7)) ↔ Even (d n) := by
  classical
  -- parity versions of the recurrence, applied repeatedly
  have h0 :
      Even (d (n + 7)) ↔ (Even (d (n + 6)) ↔ Even (d (n + 4))) := by
    have hrec := h₃ (n + 7) (by linarith : n + 7 ≥ 3)
    simpa [hrec, Nat.even_add] using
      (Nat.even_add (d (n + 6)) (d (n + 4)))
  have h1 :
      Even (d (n + 6)) ↔ (Even (d (n + 5)) ↔ Even (d (n + 3))) := by
    have hrec := h₃ (n + 6) (by linarith : n + 6 ≥ 3)
    simpa [hrec, Nat.even_add] using
      (Nat.even_add (d (n + 5)) (d (n + 3)))
  have h2 :
      Even (d (n + 5)) ↔ (Even (d (n + 4)) ↔ Even (d (n + 2))) := by
    have hrec := h₃ (n + 5) (by linarith : n + 5 ≥ 3)
    simpa [hrec, Nat.even_add] using
      (Nat.even_add (d (n + 4)) (d (n + 2)))
  have h3 :
      Even (d (n + 4)) ↔ (Even (d (n + 3)) ↔ Even (d (n + 1))) := by
    have hrec := h₃ (n + 4) (by linarith : n + 4 ≥ 3)
    simpa [hrec, Nat.even_add] using
      (Nat.even_add (d (n + 3)) (d (n + 1)))
  have h4 :
      Even (d (n + 3)) ↔ (Even (d (n + 2)) ↔ Even (d n)) := by
    have hrec := h₃ (n + 3) (by linarith : n + 3 ≥ 3)
    simpa [hrec, Nat.even_add] using
      (Nat.even_add (d (n + 2)) (d n))
  -- combine the five equivalences; propositional reasoning finishes the proof
  have : Even (d (n + 7)) ↔ Even (d n) := by
    tauto
  exact this

theorem amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) :
    Even (d 2021) ∧ Odd (d 2022) ∧ Even (d 2023) := by
  have h_even_rec (n : ℕ) (hn : n ≥ 3) :
      Even (d n) ↔ (Even (d (n - 1)) ↔ Even (d (n - 3))) := by
    exact h_even_rec_amc12a_2021_p8 d h₀ h₁ h₂ h₃ n hn
  have h_even0 : Even (d 0) := by
    exact h_even0_amc12a_2021_p8 d h₀
  have h_even1 : Even (d 1) := by
    exact h_even1_amc12a_2021_p8 d h₁
  have h_odd2 : Odd (d 2) := by
    exact h_odd2_amc12a_2021_p8 d h₂
  have h_even3 : Even (d 3) ↔ False := by
    exact h_even3_amc12a_2021_p8 d h₃ h_even0 h_even1 h_odd2
  have h_odd3 : Odd (d 3) := by
    exact h_odd3_amc12a_2021_p8 d h₃ h_even0 h_even1 h_odd2
  have h_even4 : Even (d 4) ↔ False := by
    exact h_even4_amc12a_2021_p8 d h₃ h_even1 h_even3
  have h_odd4 : Odd (d 4) := by
    exact h_odd4_amc12a_2021_p8 d h₃ h_even1 h_even3
  have h_even5 : Even (d 5) := by
    exact h_even5_amc12a_2021_p8 d h₃ h_even4 h_odd2
  have h_odd5 : Odd (d 5) ↔ False := by
    exact h_odd5_amc12a_2021_p8 d h₃ h_even4 h_odd2
  have h_even6 : Even (d 6) ↔ False := by
    exact h_even6_amc12a_2021_p8 d h₃ h_even5 h_even3
  have h_odd6 : Odd (d 6) := by
    exact h_odd6_amc12a_2021_p8 d h₃ h_even5 h_even3
  have h_period_even (n : ℕ) : Even (d (n + 7)) ↔ Even (d n) := by
    exact h_period_even_amc12a_2021_p8 d h₃ n
  have h_mod2021 : 2021 = 7 * 288 + 5 := by
    exact h_mod2021_amc12a_2021_p8
  have h_mod2022 : 2022 = 7 * 288 + 6 := by
    exact h_mod2022_amc12a_2021_p8
  have h_mod2023 : 2023 = 7 * 288 + 7 := by
    exact h_mod2023_amc12a_2021_p8
  have h_even2021 : Even (d 2021) ↔ Even (d 5) := by
    exact h_even2021_amc12a_2021_p8 d h₃ h_period_even h_mod2021
  have h_even2022 : Even (d 2022) ↔ Even (d 6) := by
    exact h_even2022_amc12a_2021_p8 d h₃ h_period_even h_mod2022
  have h_even2023 : Even (d 2023) ↔ Even (d 0) := by
    exact h_even2023_amc12a_2021_p8 d h₃ h_period_even h_mod2023
  have h_res2021 : Even (d 2021) := by
    exact h_res2021_amc12a_2021_p8 d h_even2021 h_even5
  have h_not_even2022 : ¬Even (d 2022) := by
    exact h_not_even2022_amc12a_2021_p8 d h_even2022 h_even6
  have h_res2022 : Odd (d 2022) := by
    exact h_res2022_amc12a_2021_p8 d h_not_even2022
  have h_res2023 : Even (d 2023) := by
    exact h_res2023_amc12a_2021_p8 d h_even2023 h_even0
  exact ⟨h_res2021, h_res2022, h_res2023⟩

import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h_a0_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) :
    (d 0) % 2 = 0 := by
  have h₁ : (d 0) % 2 = 0 := by
    rw [h₀]
    <;> simp
  exact h₁

theorem h_a1_amc12a_2021_p8 (d : ℕ → ℕ) (h₁ : d 1 = 0) :
    (d 1) % 2 = 0 := by
  have h₂ : (d 1) % 2 = 0 := by
    rw [h₁]
    <;> simp
  exact h₂

theorem h_a2_amc12a_2021_p8 (d : ℕ → ℕ) (h₂ : d 2 = 1) :
    (d 2) % 2 = 1 := by
  have h₃ : (d 2) % 2 = 1 := by
    rw [h₂]
    <;> norm_num
  exact h₃

theorem h_even2021_amc12a_2021_p8 (d : ℕ → ℕ)
    (h2021 : (d 2021) % 2 = (d 5) % 2) (h_a5 : (d 5) % 2 = 0) :
    Even (d 2021) := by
  have h : (d 2021) % 2 = 0 := by
    have h₁ : (d 2021) % 2 = (d 5) % 2 := h2021
    have h₂ : (d 5) % 2 = 0 := h_a5
    omega
  -- Use the fact that if a number modulo 2 is 0, then it is even.
  rw [even_iff_two_dvd]
  -- Since (d 2021) % 2 = 0, 2 divides (d 2021).
  omega

theorem h_a4_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_parity_rec : ∀ n ≥ 3, (d n) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2)
    (h_a1 : (d 1) % 2 = 0) (h_a2 : (d 2) % 2 = 1) (h_a3 : (d 3) % 2 = 1) :
    (d 4) % 2 = 1 := by
  have h4 : (d 4) % 2 = 1 := by
    have h4_rec : (d 4) % 2 = ((d 3) % 2 + (d 1) % 2) % 2 := by
      have h4_recurrence := h_parity_rec 4 (by norm_num)
      norm_num at h4_recurrence ⊢
      <;> simp_all [Nat.add_mod, Nat.mod_mod]
      <;> omega
    rw [h4_rec]
    norm_num [h_a1, h_a3]
    <;> simp_all [Nat.add_mod, Nat.mod_mod]
    <;> omega
  exact h4

theorem h_a3_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_parity_rec : ∀ n ≥ 3, (d n) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2)
    (h_a0 : (d 0) % 2 = 0) (h_a1 : (d 1) % 2 = 0) (h_a2 : (d 2) % 2 = 1) :
    (d 3) % 2 = 1 := by
  have h_3 : (d 3) % 2 = 1 := by
    have h₁ : (d 3) % 2 = ((d 2) % 2 + (d 0) % 2) % 2 := by
      have h₂ := h_parity_rec 3 (by norm_num)
      norm_num at h₂ ⊢
      <;> simpa [Nat.add_assoc] using h₂
    rw [h₁]
    have h₂ : (d 2) % 2 = 1 := h_a2
    have h₃ : (d 0) % 2 = 0 := h_a0
    rw [h₂, h₃]
    <;> norm_num
  exact h_3

theorem h_parity_rec_amc12a_2021_p8 (d : ℕ → ℕ)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) :
    ∀ n ≥ 3, (d n) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2 := by
  intro n hn
  have h₁ : d n = d (n - 1) + d (n - 3) := h₃ n hn
  have h₂ : (d n) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2 := by
    rw [h₁]
    have h₃ : (d (n - 1) + d (n - 3)) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2 := by
      have h₄ : (d (n - 1) + d (n - 3)) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2 := by
        have h₅ : (d (n - 1) + d (n - 3)) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2 := by
          simp [Nat.add_mod, Nat.mod_mod]
        exact h₅
      exact h₄
    rw [h₃]
  exact h₂

theorem h_even2023_amc12a_2021_p8 (d : ℕ → ℕ)
    (h2023 : (d 2023) % 2 = (d 0) % 2) (h_a0 : (d 0) % 2 = 0) :
    Even (d 2023) := by
  have h_main : (d 2023) % 2 = 0 := by
    have h1 : (d 2023) % 2 = (d 0) % 2 := h2023
    have h2 : (d 0) % 2 = 0 := h_a0
    rw [h1, h2]
    <;> simp
  
  have h_final : Even (d 2023) := by
    rw [even_iff_two_dvd]
    have h : (d 2023) % 2 = 0 := h_main
    omega
  
  exact h_final

theorem h_a5_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_parity_rec : ∀ n ≥ 3, (d n) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2)
    (h_a2 : (d 2) % 2 = 1) (h_a3 : (d 3) % 2 = 1) (h_a4 : (d 4) % 2 = 1) :
    (d 5) % 2 = 0 := by
  have h_main : (d 5) % 2 = 0 := by
    have h1 : (d 5) % 2 = ((d 4) % 2 + (d 2) % 2) % 2 := by
      have h2 : (d 5) % 2 = ((d (5 - 1)) % 2 + (d (5 - 3)) % 2) % 2 := by
        apply h_parity_rec
        <;> norm_num
      -- Simplify the indices in the recurrence relation
      norm_num at h2 ⊢
      <;> simpa using h2
    -- Substitute the known values of (d 4) % 2 and (d 2) % 2
    rw [h1]
    have h3 : (d 4) % 2 = 1 := h_a4
    have h4 : (d 2) % 2 = 1 := h_a2
    rw [h3, h4]
    <;> norm_num
    <;> rfl
  
  exact h_main

theorem h_a6_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_parity_rec : ∀ n ≥ 3, (d n) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2)
    (h_a3 : (d 3) % 2 = 1) (h_a4 : (d 4) % 2 = 1) (h_a5 : (d 5) % 2 = 0) :
    (d 6) % 2 = 1 := by
  have h1 : (d 6) % 2 = ((d 5) % 2 + (d 3) % 2) % 2 := by
    have h₁ : (d 6) % 2 = ((d (6 - 1)) % 2 + (d (6 - 3)) % 2) % 2 := by
      apply h_parity_rec
      <;> norm_num
    -- Simplify the expression using the given recurrence relation
    norm_num at h₁ ⊢
    <;> simpa [h_a3, h_a5] using h₁
  
  have h2 : (d 6) % 2 = 1 := by
    rw [h1]
    -- Substitute the known values of (d 5) % 2 and (d 3) % 2
    have h₃ : (d 5) % 2 = 0 := h_a5
    have h₄ : (d 3) % 2 = 1 := h_a3
    rw [h₃, h₄]
    -- Perform the arithmetic to find the final result
    <;> norm_num
    <;> simp [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
    <;> norm_num
    <;> rfl
  
  apply h2

theorem h_a7_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_parity_rec : ∀ n ≥ 3, (d n) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2)
    (h_a4 : (d 4) % 2 = 1) (h_a5 : (d 5) % 2 = 0) (h_a6 : (d 6) % 2 = 1) :
    (d 7) % 2 = 0 := by
  have h_d7 : (d 7) % 2 = ((d 6) % 2 + (d 4) % 2) % 2 := by
    have h1 : (d 7) % 2 = ((d (7 - 1)) % 2 + (d (7 - 3)) % 2) % 2 := by
      apply h_parity_rec
      <;> norm_num
    have h2 : (d (7 - 1)) % 2 = (d 6) % 2 := by norm_num
    have h3 : (d (7 - 3)) % 2 = (d 4) % 2 := by norm_num
    rw [h1, h2, h3]
    <;> norm_num
  
  have h_final : (d 7) % 2 = 0 := by
    rw [h_d7]
    have h₁ : (d 6) % 2 = 1 := h_a6
    have h₂ : (d 4) % 2 = 1 := h_a4
    rw [h₁, h₂]
    <;> norm_num
    <;> simp [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
    <;> norm_num
  
  exact h_final

theorem h2023_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_period : ∀ n, (d (n + 7)) % 2 = (d n) % 2) :
    (d 2023) % 2 = (d 0) % 2 := by
  have h_main : ∀ k : ℕ, (d (7 * k)) % 2 = (d 0) % 2 := by
    intro k
    induction k with
    | zero =>
      -- Base case: when k = 0, 7 * 0 = 0, so d(0) % 2 = d(0) % 2
      simp
    | succ k ih =>
      -- Inductive step: assume the statement holds for k, prove for k + 1
      have h1 : (d (7 * (k + 1))) % 2 = (d (7 * k + 7)) % 2 := by
        -- 7 * (k + 1) = 7 * k + 7
        ring_nf
        <;> simp [mul_add, add_mul, Nat.mul_succ]
        <;> ring_nf at *
        <;> omega
      have h2 : (d (7 * k + 7)) % 2 = (d (7 * k)) % 2 := by
        -- Use the given periodicity condition with n = 7 * k
        have h3 := h_period (7 * k)
        -- Simplify the expression to match the form in h_period
        norm_num at h3 ⊢
        <;> omega
      have h3 : (d (7 * k)) % 2 = (d 0) % 2 := ih
      -- Combine the results to get the final equality
      rw [h1, h2, h3]
  
  have h_2023 : (d 2023) % 2 = (d 0) % 2 := by
    have h₁ : (d 2023) % 2 = (d (7 * 289)) % 2 := by
      norm_num
    rw [h₁]
    have h₂ : (d (7 * 289)) % 2 = (d 0) % 2 := h_main 289
    rw [h₂]
  
  apply h_2023

theorem h_odd2022_amc12a_2021_p8 (d : ℕ → ℕ)
    (h2022 : (d 2022) % 2 = (d 6) % 2) (h_a6 : (d 6) % 2 = 1) :
    Odd (d 2022) := by
  have h_mod_2022 : (d 2022) % 2 = 1 := by
    have h1 : (d 2022) % 2 = (d 6) % 2 := h2022
    have h2 : (d 6) % 2 = 1 := h_a6
    rw [h1, h2]
    <;> simp
  
  have h_main : ∃ k, d 2022 = 2 * k + 1 := by
    use (d 2022) / 2
    have h₁ : d 2022 % 2 = 1 := h_mod_2022
    have h₂ : d 2022 = 2 * (d 2022 / 2) + 1 := by
      have h₃ := Nat.div_add_mod (d 2022) 2
      have h₄ : d 2022 % 2 = 1 := h_mod_2022
      omega
    exact h₂
  
  have h_final : Odd (d 2022) := by
    rw [Odd]
    exact h_main
  
  exact h_final

theorem h2021_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_period : ∀ n, (d (n + 7)) % 2 = (d n) % 2) :
    (d 2021) % 2 = (d 5) % 2 := by
  have h_main : ∀ (n k : ℕ), (d (n + 7 * k)) % 2 = (d n) % 2 := by
    intro n k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      have h₁ : (d (n + 7 * k.succ)) % 2 = (d (n + 7 * k + 7)) % 2 := by
        have h₂ : n + 7 * k.succ = n + 7 * k + 7 := by
          simp [Nat.mul_succ, Nat.add_assoc]
          <;> ring_nf at *
          <;> omega
        rw [h₂]
      rw [h₁]
      have h₂ : (d (n + 7 * k + 7)) % 2 = (d (n + 7 * k)) % 2 := by
        have h₃ := h_period (n + 7 * k)
        simpa [Nat.add_assoc] using h₃
      rw [h₂]
      <;> simp [ih]
      <;> omega
  
  have h_2021_eq : 2021 = 5 + 7 * 288 := by
    norm_num
    <;> rfl
  
  have h_final : (d 2021) % 2 = (d 5) % 2 := by
    have h₁ : (d 2021) % 2 = (d (5 + 7 * 288)) % 2 := by
      rw [h_2021_eq]
    rw [h₁]
    have h₂ : (d (5 + 7 * 288)) % 2 = (d 5) % 2 := by
      have h₃ := h_main 5 288
      simpa using h₃
    rw [h₂]
  
  apply h_final

theorem h2022_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_period : ∀ n, (d (n + 7)) % 2 = (d n) % 2) :
    (d 2022) % 2 = (d 6) % 2 := by
  have h_general : ∀ (n k : ℕ), (d (n + 7 * k)) % 2 = (d n) % 2 := by
    intro n k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      have h₁ : (d (n + 7 * k.succ)) % 2 = (d (n + 7 * k + 7)) % 2 := by
        have h₂ : n + 7 * k.succ = n + 7 * k + 7 := by
          simp [Nat.mul_succ, Nat.add_assoc]
          <;> ring_nf at *
          <;> omega
        rw [h₂]
      rw [h₁]
      have h₂ : (d (n + 7 * k + 7)) % 2 = (d (n + 7 * k)) % 2 := by
        have h₃ := h_period (n + 7 * k)
        simpa [Nat.add_assoc] using h₃
      rw [h₂]
      <;> simp [ih]
      <;> omega
  
  have h_2022 : 2022 = 6 + 7 * 288 := by
    norm_num
    <;> rfl
  
  have h_main : (d 2022) % 2 = (d 6) % 2 := by
    have h₁ : (d 2022) % 2 = (d (6 + 7 * 288)) % 2 := by
      rw [h_2022]
    rw [h₁]
    have h₂ : (d (6 + 7 * 288)) % 2 = (d 6) % 2 := by
      have h₃ := h_general 6 288
      simpa using h₃
    rw [h₂]
  
  exact h_main

theorem hge_h_period_amc12a_2021_p8 (n : ℕ) (hle : ¬ n ≤ 6) : 7 ≤ n := by
  by_contra h
  -- Assume for contradiction that n < 7
  have h₁ : n ≤ 6 := by
    -- Since n is a natural number and we are assuming n < 7, it follows that n ≤ 6
    omega
  -- This contradicts the given hypothesis that ¬ n ≤ 6
  exact hle h₁

theorem h0_h_period_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_parity_rec : ∀ n ≥ 3,
        (d n) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2)
    (h_a0 : (d 0) % 2 = 0) (h_a1 : (d 1) % 2 = 0) (h_a2 : (d 2) % 2 = 1)
    (h_a3 : (d 3) % 2 = 1) (h_a4 : (d 4) % 2 = 1) (h_a5 : (d 5) % 2 = 0)
    (h_a6 : (d 6) % 2 = 1) (h_a7 : (d 7) % 2 = 0) :
    (d (0 + 7)) % 2 = (d 0) % 2 := by
  have h_main : (d (0 + 7)) % 2 = (d 0) % 2 := by
    have h₁ : (d (0 + 7)) % 2 = 0 := by
      -- Simplify 0 + 7 to 7 and use the given hypothesis h_a7
      norm_num at h_a7 ⊢
      <;> simpa using h_a7
    have h₂ : (d 0) % 2 = 0 := h_a0
    -- Combine the results to get the final equality
    linarith
  
  exact h_main

theorem h1_h_period_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_parity_rec : ∀ n ≥ 3,
        (d n) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2)
    (h_a0 : (d 0) % 2 = 0) (h_a1 : (d 1) % 2 = 0) (h_a2 : (d 2) % 2 = 1)
    (h_a3 : (d 3) % 2 = 1) (h_a4 : (d 4) % 2 = 1) (h_a5 : (d 5) % 2 = 0)
    (h_a6 : (d 6) % 2 = 1) (h_a7 : (d 7) % 2 = 0) :
    (d (1 + 7)) % 2 = (d 1) % 2 := by
  have h_d8 : (d 8) % 2 = 0 := by
    have h1 : (d 8) % 2 = ((d 7) % 2 + (d 5) % 2) % 2 := by
      have h2 := h_parity_rec 8 (by norm_num)
      norm_num at h2 ⊢
      <;> omega
    rw [h1]
    have h3 : (d 7) % 2 = 0 := h_a7
    have h4 : (d 5) % 2 = 0 := h_a5
    rw [h3, h4]
    <;> norm_num
    <;> omega
  
  have h_main : (d (1 + 7)) % 2 = (d 1) % 2 := by
    have h₁ : (d (1 + 7)) % 2 = (d 8) % 2 := by norm_num
    rw [h₁]
    have h₂ : (d 8) % 2 = 0 := h_d8
    rw [h₂]
    have h₃ : (d 1) % 2 = 0 := h_a1
    omega
  
  apply h_main

theorem h2_h_period_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_parity_rec : ∀ n ≥ 3,
        (d n) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2)
    (h_a0 : (d 0) % 2 = 0) (h_a1 : (d 1) % 2 = 0) (h_a2 : (d 2) % 2 = 1)
    (h_a3 : (d 3) % 2 = 1) (h_a4 : (d 4) % 2 = 1) (h_a5 : (d 5) % 2 = 0)
    (h_a6 : (d 6) % 2 = 1) (h_a7 : (d 7) % 2 = 0) :
    (d (2 + 7)) % 2 = (d 2) % 2 := by
  have h_d8 : (d 8) % 2 = 0 := by
    have h1 : (d 8) % 2 = ((d 7) % 2 + (d 5) % 2) % 2 := by
      have h2 := h_parity_rec 8 (by norm_num)
      norm_num at h2 ⊢
      <;> omega
    rw [h1]
    norm_num [h_a7, h_a5]
    <;> omega
  
  have h_d9 : (d 9) % 2 = 1 := by
    have h1 : (d 9) % 2 = ((d 8) % 2 + (d 6) % 2) % 2 := by
      have h2 := h_parity_rec 9 (by norm_num)
      norm_num at h2 ⊢
      <;> omega
    rw [h1]
    norm_num [h_d8, h_a6]
    <;> omega
  
  have h_main : (d (2 + 7)) % 2 = (d 2) % 2 := by
    norm_num at h_d9 ⊢
    <;> simp_all [h_a2]
    <;> omega
  
  exact h_main

theorem h3_h_period_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_parity_rec : ∀ n ≥ 3,
        (d n) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2)
    (h_a0 : (d 0) % 2 = 0) (h_a1 : (d 1) % 2 = 0) (h_a2 : (d 2) % 2 = 1)
    (h_a3 : (d 3) % 2 = 1) (h_a4 : (d 4) % 2 = 1) (h_a5 : (d 5) % 2 = 0)
    (h_a6 : (d 6) % 2 = 1) (h_a7 : (d 7) % 2 = 0) :
    (d (3 + 7)) % 2 = (d 3) % 2 := by
  have h_d8 : (d 8) % 2 = 0 := by
    have h1 : (d 8) % 2 = ((d 7) % 2 + (d 5) % 2) % 2 := by
      have h2 := h_parity_rec 8 (by norm_num)
      norm_num at h2 ⊢
      <;> omega
    rw [h1]
    norm_num [h_a7, h_a5]
    <;> omega
  
  have h_d9 : (d 9) % 2 = 1 := by
    have h1 : (d 9) % 2 = ((d 8) % 2 + (d 6) % 2) % 2 := by
      have h2 := h_parity_rec 9 (by norm_num)
      norm_num at h2 ⊢
      <;> omega
    rw [h1]
    norm_num [h_d8, h_a6]
    <;> omega
  
  have h_d10 : (d 10) % 2 = 1 := by
    have h1 : (d 10) % 2 = ((d 9) % 2 + (d 7) % 2) % 2 := by
      have h2 := h_parity_rec 10 (by norm_num)
      norm_num at h2 ⊢
      <;> omega
    rw [h1]
    norm_num [h_d9, h_a7]
    <;> omega
  
  have h_main : (d (3 + 7)) % 2 = (d 3) % 2 := by
    norm_num at h_d10 ⊢
    <;> simp_all [h_a3]
    <;> omega
  
  exact h_main

theorem h_base_h_period_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_parity_rec : ∀ n ≥ 3,
        (d n) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2)
    (h_a0 : (d 0) % 2 = 0) (h_a1 : (d 1) % 2 = 0) (h_a2 : (d 2) % 2 = 1)
    (h_a3 : (d 3) % 2 = 1) (h_a4 : (d 4) % 2 = 1) (h_a5 : (d 5) % 2 = 0)
    (h_a6 : (d 6) % 2 = 1) (h_a7 : (d 7) % 2 = 0)
    (h0 : (d (0 + 7)) % 2 = (d 0) % 2) (h1 : (d (1 + 7)) % 2 = (d 1) % 2)
    (h2 : (d (2 + 7)) % 2 = (d 2) % 2) (h3 : (d (3 + 7)) % 2 = (d 3) % 2)
    (h4 : (d (4 + 7)) % 2 = (d 4) % 2) (h5 : (d (5 + 7)) % 2 = (d 5) % 2)
    (h6 : (d (6 + 7)) % 2 = (d 6) % 2) :
    ∀ n ≤ 6, (d (n + 7)) % 2 = (d n) % 2 := by
  have h_main : ∀ n ≤ 6, (d (n + 7)) % 2 = (d n) % 2 := by
    intro n hn
    have h : n ≤ 6 := hn
    interval_cases n <;> norm_num at h0 h1 h2 h3 h4 h5 h6 ⊢ <;>
      (try omega) <;>
      (try simp_all [Nat.add_assoc]) <;>
      (try norm_num) <;>
      (try omega)
    <;>
    (try
      {
        simp_all [Nat.add_assoc]
        <;> norm_num
        <;> omega
      })
  exact h_main

theorem h4_h_period_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_parity_rec : ∀ n ≥ 3,
        (d n) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2)
    (h_a0 : (d 0) % 2 = 0) (h_a1 : (d 1) % 2 = 0) (h_a2 : (d 2) % 2 = 1)
    (h_a3 : (d 3) % 2 = 1) (h_a4 : (d 4) % 2 = 1) (h_a5 : (d 5) % 2 = 0)
    (h_a6 : (d 6) % 2 = 1) (h_a7 : (d 7) % 2 = 0) :
    (d (4 + 7)) % 2 = (d 4) % 2 := by
  have h8 : (d 8) % 2 = 0 := by
    have h8' : (d 8) % 2 = ((d 7) % 2 + (d 5) % 2) % 2 := by
      have h8'' := h_parity_rec 8 (by norm_num)
      norm_num at h8'' ⊢
      <;> omega
    rw [h8']
    norm_num [h_a7, h_a5]
    <;> omega
  
  have h9 : (d 9) % 2 = 1 := by
    have h9' : (d 9) % 2 = ((d 8) % 2 + (d 6) % 2) % 2 := by
      have h9'' := h_parity_rec 9 (by norm_num)
      norm_num at h9'' ⊢
      <;> omega
    rw [h9']
    norm_num [h8, h_a6]
    <;> omega
  
  have h10 : (d 10) % 2 = 1 := by
    have h10' : (d 10) % 2 = ((d 9) % 2 + (d 7) % 2) % 2 := by
      have h10'' := h_parity_rec 10 (by norm_num)
      norm_num at h10'' ⊢
      <;> omega
    rw [h10']
    norm_num [h9, h_a7]
    <;> omega
  
  have h11 : (d 11) % 2 = 1 := by
    have h11' : (d 11) % 2 = ((d 10) % 2 + (d 8) % 2) % 2 := by
      have h11'' := h_parity_rec 11 (by norm_num)
      norm_num at h11'' ⊢
      <;> omega
    rw [h11']
    norm_num [h10, h8]
    <;> omega
  
  have h_main : (d (4 + 7)) % 2 = (d 4) % 2 := by
    norm_num at h11 ⊢
    <;> simp_all [h_a4]
    <;> norm_num
    <;> omega
  
  exact h_main

theorem h5_h_period_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_parity_rec : ∀ n ≥ 3,
        (d n) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2)
    (h_a0 : (d 0) % 2 = 0) (h_a1 : (d 1) % 2 = 0) (h_a2 : (d 2) % 2 = 1)
    (h_a3 : (d 3) % 2 = 1) (h_a4 : (d 4) % 2 = 1) (h_a5 : (d 5) % 2 = 0)
    (h_a6 : (d 6) % 2 = 1) (h_a7 : (d 7) % 2 = 0) :
    (d (5 + 7)) % 2 = (d 5) % 2 := by
  have h_d8 : (d 8) % 2 = 0 := by
    have h1 : (d 8) % 2 = ((d 7) % 2 + (d 5) % 2) % 2 := by
      have h2 := h_parity_rec 8 (by norm_num)
      norm_num at h2 ⊢
      <;> omega
    rw [h1]
    norm_num [h_a7, h_a5]
    <;> omega
  
  have h_d9 : (d 9) % 2 = 1 := by
    have h1 : (d 9) % 2 = ((d 8) % 2 + (d 6) % 2) % 2 := by
      have h2 := h_parity_rec 9 (by norm_num)
      norm_num at h2 ⊢
      <;> omega
    rw [h1]
    norm_num [h_d8, h_a6]
    <;> omega
  
  have h_d10 : (d 10) % 2 = 1 := by
    have h1 : (d 10) % 2 = ((d 9) % 2 + (d 7) % 2) % 2 := by
      have h2 := h_parity_rec 10 (by norm_num)
      norm_num at h2 ⊢
      <;> omega
    rw [h1]
    norm_num [h_d9, h_a7]
    <;> omega
  
  have h_d11 : (d 11) % 2 = 1 := by
    have h1 : (d 11) % 2 = ((d 10) % 2 + (d 8) % 2) % 2 := by
      have h2 := h_parity_rec 11 (by norm_num)
      norm_num at h2 ⊢
      <;> omega
    rw [h1]
    norm_num [h_d10, h_d8]
    <;> omega
  
  have h_d12 : (d 12) % 2 = 0 := by
    have h1 : (d 12) % 2 = ((d 11) % 2 + (d 9) % 2) % 2 := by
      have h2 := h_parity_rec 12 (by norm_num)
      norm_num at h2 ⊢
      <;> omega
    rw [h1]
    norm_num [h_d11, h_d9]
    <;> omega
  
  have h_main : (d (5 + 7)) % 2 = (d 5) % 2 := by
    norm_num at h_d12 ⊢
    <;> simp_all [h_a5]
    <;> omega
  
  apply h_main

theorem h6_h_period_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_parity_rec : ∀ n ≥ 3,
        (d n) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2)
    (h_a0 : (d 0) % 2 = 0) (h_a1 : (d 1) % 2 = 0) (h_a2 : (d 2) % 2 = 1)
    (h_a3 : (d 3) % 2 = 1) (h_a4 : (d 4) % 2 = 1) (h_a5 : (d 5) % 2 = 0)
    (h_a6 : (d 6) % 2 = 1) (h_a7 : (d 7) % 2 = 0) :
    (d (6 + 7)) % 2 = (d 6) % 2 := by
  have h_d8 : (d 8) % 2 = 0 := by
    have h₁ : (d 8) % 2 = ((d 7) % 2 + (d 5) % 2) % 2 := by
      have h₂ := h_parity_rec 8 (by norm_num)
      norm_num at h₂ ⊢
      <;> omega
    rw [h₁]
    norm_num [h_a7, h_a5]
    <;> omega
  
  have h_d9 : (d 9) % 2 = 1 := by
    have h₁ : (d 9) % 2 = ((d 8) % 2 + (d 6) % 2) % 2 := by
      have h₂ := h_parity_rec 9 (by norm_num)
      norm_num at h₂ ⊢
      <;> omega
    rw [h₁]
    norm_num [h_d8, h_a6]
    <;> omega
  
  have h_d10 : (d 10) % 2 = 1 := by
    have h₁ : (d 10) % 2 = ((d 9) % 2 + (d 7) % 2) % 2 := by
      have h₂ := h_parity_rec 10 (by norm_num)
      norm_num at h₂ ⊢
      <;> omega
    rw [h₁]
    norm_num [h_d9, h_a7]
    <;> omega
  
  have h_d11 : (d 11) % 2 = 1 := by
    have h₁ : (d 11) % 2 = ((d 10) % 2 + (d 8) % 2) % 2 := by
      have h₂ := h_parity_rec 11 (by norm_num)
      norm_num at h₂ ⊢
      <;> omega
    rw [h₁]
    norm_num [h_d10, h_d8]
    <;> omega
  
  have h_d12 : (d 12) % 2 = 0 := by
    have h₁ : (d 12) % 2 = ((d 11) % 2 + (d 9) % 2) % 2 := by
      have h₂ := h_parity_rec 12 (by norm_num)
      norm_num at h₂ ⊢
      <;> omega
    rw [h₁]
    norm_num [h_d11, h_d9]
    <;> omega
  
  have h_d13 : (d 13) % 2 = 1 := by
    have h₁ : (d 13) % 2 = ((d 12) % 2 + (d 10) % 2) % 2 := by
      have h₂ := h_parity_rec 13 (by norm_num)
      norm_num at h₂ ⊢
      <;> omega
    rw [h₁]
    norm_num [h_d12, h_d10]
    <;> omega
  
  have h_main : (d (6 + 7)) % 2 = (d 6) % 2 := by
    norm_num at h_d13 ⊢
    <;> simp_all [h_a6]
    <;> norm_num
    <;> omega
  
  apply h_main

theorem h_step_h_period_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_parity_rec : ∀ n ≥ 3,
        (d n) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2)
    (h_a0 : (d 0) % 2 = 0) (h_a1 : (d 1) % 2 = 0) (h_a2 : (d 2) % 2 = 1)
    (h_a3 : (d 3) % 2 = 1) (h_a4 : (d 4) % 2 = 1) (h_a5 : (d 5) % 2 = 0)
    (h_a6 : (d 6) % 2 = 1) (h_a7 : (d 7) % 2 = 0)
    (h_base : ∀ n ≤ 6, (d (n + 7)) % 2 = (d n) % 2) :
    ∀ n ≥ 7, (d (n + 7)) % 2 = (d n) % 2 := by
  have h_periodic : ∀ n, (d (n + 7)) % 2 = (d n) % 2 := by
    intro n
    have h : ∀ n, (d (n + 7)) % 2 = (d n) % 2 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        match n with
        | 0 =>
          have h₁ := h_base 0 (by norm_num)
          simp at h₁ ⊢
          <;> omega
        | 1 =>
          have h₁ := h_base 1 (by norm_num)
          simp at h₁ ⊢
          <;> omega
        | 2 =>
          have h₁ := h_base 2 (by norm_num)
          simp at h₁ ⊢
          <;> omega
        | 3 =>
          have h₁ := h_base 3 (by norm_num)
          simp at h₁ ⊢
          <;> omega
        | 4 =>
          have h₁ := h_base 4 (by norm_num)
          simp at h₁ ⊢
          <;> omega
        | 5 =>
          have h₁ := h_base 5 (by norm_num)
          simp at h₁ ⊢
          <;> omega
        | 6 =>
          have h₁ := h_base 6 (by norm_num)
          simp at h₁ ⊢
          <;> omega
        | n + 7 =>
          have h₁ : (d (n + 7 + 7)) % 2 = ((d (n + 7 + 6)) % 2 + (d (n + 7 + 4)) % 2) % 2 := by
            have h₂ : n + 7 + 7 ≥ 3 := by omega
            have h₃ := h_parity_rec (n + 7 + 7) h₂
            norm_num at h₃ ⊢
            <;>
            (try omega) <;>
            (try ring_nf at h₃ ⊢ <;> omega) <;>
            (try simp_all [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]) <;>
            (try omega)
            <;>
            (try
              {
                cases n with
                | zero => omega
                | succ n =>
                  simp_all [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                  <;> ring_nf at *
                  <;> omega
              })
          have h₂ : (d (n + 7 + 6)) % 2 = (d (n + 6)) % 2 := by
            have h₃ := ih (n + 6) (by omega)
            have h₄ : (d ((n + 6) + 7)) % 2 = (d (n + 6)) % 2 := by simpa using h₃
            have h₅ : (d (n + 7 + 6)) % 2 = (d ((n + 6) + 7)) % 2 := by
              ring_nf at *
              <;> simp_all [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              <;> omega
            omega
          have h₃ : (d (n + 7 + 4)) % 2 = (d (n + 4)) % 2 := by
            have h₄ := ih (n + 4) (by omega)
            have h₅ : (d ((n + 4) + 7)) % 2 = (d (n + 4)) % 2 := by simpa using h₄
            have h₆ : (d (n + 7 + 4)) % 2 = (d ((n + 4) + 7)) % 2 := by
              ring_nf at *
              <;> simp_all [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              <;> omega
            omega
          have h₄ : (d (n + 7)) % 2 = ((d (n + 6)) % 2 + (d (n + 4)) % 2) % 2 := by
            have h₅ : n + 7 ≥ 3 := by omega
            have h₆ := h_parity_rec (n + 7) h₅
            have h₇ : (d (n + 7)) % 2 = ((d (n + 7 - 1)) % 2 + (d (n + 7 - 3)) % 2) % 2 := by
              simpa using h₆
            have h₈ : n + 7 - 1 = n + 6 := by
              omega
            have h₉ : n + 7 - 3 = n + 4 := by
              omega
            rw [h₈, h₉] at h₇
            omega
          have h₅ : (d (n + 7 + 7)) % 2 = (d (n + 7)) % 2 := by
            omega
          omega
    exact h n
  
  have h_main : ∀ n ≥ 7, (d (n + 7)) % 2 = (d n) % 2 := by
    intro n hn
    have h₁ := h_periodic n
    exact h₁
  
  exact h_main

theorem h_period_amc12a_2021_p8 (d : ℕ → ℕ)
    (h_parity_rec : ∀ n ≥ 3, (d n) % 2 = ((d (n - 1)) % 2 + (d (n - 3)) % 2) % 2)
    (h_a0 : (d 0) % 2 = 0) (h_a1 : (d 1) % 2 = 0) (h_a2 : (d 2) % 2 = 1)
    (h_a3 : (d 3) % 2 = 1) (h_a4 : (d 4) % 2 = 1) (h_a5 : (d 5) % 2 = 0)
    (h_a6 : (d 6) % 2 = 1) (h_a7 : (d 7) % 2 = 0) :
    ∀ n, (d (n + 7)) % 2 = (d n) % 2 := by
  have h0 : (d (0 + 7)) % 2 = (d 0) % 2 :=
    h0_h_period_amc12a_2021_p8 d h_parity_rec h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  have h1 : (d (1 + 7)) % 2 = (d 1) % 2 :=
    h1_h_period_amc12a_2021_p8 d h_parity_rec h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  have h2 : (d (2 + 7)) % 2 = (d 2) % 2 :=
    h2_h_period_amc12a_2021_p8 d h_parity_rec h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  have h3 : (d (3 + 7)) % 2 = (d 3) % 2 :=
    h3_h_period_amc12a_2021_p8 d h_parity_rec h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  have h4 : (d (4 + 7)) % 2 = (d 4) % 2 :=
    h4_h_period_amc12a_2021_p8 d h_parity_rec h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  have h5 : (d (5 + 7)) % 2 = (d 5) % 2 :=
    h5_h_period_amc12a_2021_p8 d h_parity_rec h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  have h6 : (d (6 + 7)) % 2 = (d 6) % 2 :=
    h6_h_period_amc12a_2021_p8 d h_parity_rec h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  have h_base : ∀ n ≤ 6, (d (n + 7)) % 2 = (d n) % 2 :=
    h_base_h_period_amc12a_2021_p8 d h_parity_rec h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
      h0 h1 h2 h3 h4 h5 h6
  have h_step : ∀ n ≥ 7, (d (n + 7)) % 2 = (d n) % 2 :=
    h_step_h_period_amc12a_2021_p8 d h_parity_rec h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
      h_base
  intro n
  by_cases hle : n ≤ 6
  · exact h_base n hle
  ·
    have hge : 7 ≤ n := hge_h_period_amc12a_2021_p8 n hle
    exact h_step n hge

theorem amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) :
    Even (d 2021) ∧ Odd (d 2022) ∧ Even (d 2023) := by
  -- parity recurrence modulo 2
  have h_parity_rec := h_parity_rec_amc12a_2021_p8 d h₃
  -- initial parity values
  have h_a0 := h_a0_amc12a_2021_p8 d h₀
  have h_a1 := h_a1_amc12a_2021_p8 d h₁
  have h_a2 := h_a2_amc12a_2021_p8 d h₂
  -- compute the first seven residues
  have h_a3 := h_a3_amc12a_2021_p8 d h_parity_rec h_a0 h_a1 h_a2
  have h_a4 := h_a4_amc12a_2021_p8 d h_parity_rec h_a1 h_a2 h_a3
  have h_a5 := h_a5_amc12a_2021_p8 d h_parity_rec h_a2 h_a3 h_a4
  have h_a6 := h_a6_amc12a_2021_p8 d h_parity_rec h_a3 h_a4 h_a5
  have h_a7 := h_a7_amc12a_2021_p8 d h_parity_rec h_a4 h_a5 h_a6
  -- periodicity of period 7 for the residues
  have h_period := h_period_amc12a_2021_p8 d h_parity_rec h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  -- reduce the large indices modulo 7
  have h2021 := h2021_amc12a_2021_p8 d h_period
  have h2022 := h2022_amc12a_2021_p8 d h_period
  have h2023 := h2023_amc12a_2021_p8 d h_period
  -- translate residues to parity statements
  have h_even2021 := h_even2021_amc12a_2021_p8 d h2021 h_a5
  have h_odd2022 := h_odd2022_amc12a_2021_p8 d h2022 h_a6
  have h_even2023 := h_even2023_amc12a_2021_p8 d h2023 h_a0
  exact ⟨h_even2021, h_odd2022, h_even2023⟩

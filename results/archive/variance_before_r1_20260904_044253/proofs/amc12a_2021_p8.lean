import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem hmod0_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) :
  d 0 % 2 = 0 := by
  have h_main : d 0 % 2 = 0 := by
    have h₄ : d 0 = 0 := h₀
    rw [h₄]
    <;> simp [Nat.zero_mod]
  
  exact h_main

theorem hmod1_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) :
  d 1 % 2 = 0 := by
  have h_main : d 1 % 2 = 0 := by
    rw [h₁]
    <;> norm_num
    <;> rfl
  
  exact h_main

theorem hmod2_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) :
  d 2 % 2 = 1 := by
  have h_main : d 2 % 2 = 1 := by
    have h₄ : d 2 = 1 := h₂
    rw [h₄]
    <;> norm_num
    <;> rfl
  
  exact h_main

theorem hrec_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) (n : ℕ) (hn : n ≥ 3) :
  d n % 2 = (d (n - 1) % 2 + d (n - 3) % 2) % 2 := by
  have h₄ : d n = d (n - 1) + d (n - 3) := h₃ n hn
  have h₅ : d n % 2 = (d (n - 1) + d (n - 3)) % 2 := by
    rw [h₄]
  have h₆ : (d (n - 1) + d (n - 3)) % 2 = (d (n - 1) % 2 + d (n - 3) % 2) % 2 := by
    have h₇ : (d (n - 1) + d (n - 3)) % 2 = (d (n - 1) % 2 + d (n - 3) % 2) % 2 := by
      have h₈ : (d (n - 1) + d (n - 3)) % 2 = (d (n - 1) % 2 + d (n - 3) % 2) % 2 := by
        simp [Nat.add_mod, Nat.mod_mod]
        <;>
        (try omega) <;>
        (try ring_nf at * <;> omega) <;>
        (try omega)
      exact h₈
    exact h₇
  rw [h₅, h₆]
  <;>
  (try omega) <;>
  (try ring_nf at * <;> omega) <;>
  (try omega)

theorem hmod3_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (hmod0 : d 0 % 2 = 0) (hmod1 : d 1 % 2 = 0) (hmod2 : d 2 % 2 = 1)
    (hrec : ∀ n : ℕ, n ≥ 3 → d n % 2 = (d (n - 1) % 2 + d (n - 3) % 2) % 2) :
  d 3 % 2 = 1 := by
  have h_d3 : d 3 = 1 := by
    have h₄ : d 3 = d 2 + d 0 := by
      have h₅ : d 3 = d (3 - 1) + d (3 - 3) := h₃ 3 (by norm_num)
      norm_num at h₅ ⊢
      <;> linarith
    rw [h₄]
    <;> simp [h₂, h₀]
    <;> norm_num
  
  have h_main : d 3 % 2 = 1 := by
    rw [h_d3]
    <;> norm_num
  
  exact h_main

theorem hmod4_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (hmod0 : d 0 % 2 = 0) (hmod1 : d 1 % 2 = 0) (hmod2 : d 2 % 2 = 1)
    (hmod3 : d 3 % 2 = 1)
    (hrec : ∀ n : ℕ, n ≥ 3 → d n % 2 = (d (n - 1) % 2 + d (n - 3) % 2) % 2) :
  d 4 % 2 = 1 := by
  have h_main : d 4 % 2 = 1 := by
    have h₄ : d 4 % 2 = (d 3 % 2 + d 1 % 2) % 2 := by
      have h₄₁ : d 4 % 2 = (d (4 - 1) % 2 + d (4 - 3) % 2) % 2 := by
        apply hrec
        <;> norm_num
      norm_num at h₄₁ ⊢
      <;> omega
    rw [h₄]
    have h₅ : d 3 % 2 = 1 := hmod3
    have h₆ : d 1 % 2 = 0 := hmod1
    rw [h₅, h₆]
    <;> norm_num
    <;> omega
  
  exact h_main

theorem hmod5_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (hmod0 : d 0 % 2 = 0) (hmod1 : d 1 % 2 = 0) (hmod2 : d 2 % 2 = 1)
    (hmod3 : d 3 % 2 = 1) (hmod4 : d 4 % 2 = 1)
    (hrec : ∀ n : ℕ, n ≥ 3 → d n % 2 = (d (n - 1) % 2 + d (n - 3) % 2) % 2) :
  d 5 % 2 = 0 := by
  have h_main : d 5 % 2 = 0 := by
    have h₅ : d 5 % 2 = (d 4 % 2 + d 2 % 2) % 2 := by
      have h₅₁ : d 5 % 2 = (d (5 - 1) % 2 + d (5 - 3) % 2) % 2 := by
        apply hrec
        <;> norm_num
      norm_num at h₅₁ ⊢
      <;> omega
    rw [h₅]
    have h₄ : d 4 % 2 = 1 := hmod4
    have h₂' : d 2 % 2 = 1 := hmod2
    rw [h₄, h₂']
    <;> norm_num
    <;> omega
  
  exact h_main

theorem hmod6_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (hmod0 : d 0 % 2 = 0) (hmod1 : d 1 % 2 = 0) (hmod2 : d 2 % 2 = 1)
    (hmod3 : d 3 % 2 = 1) (hmod4 : d 4 % 2 = 1) (hmod5 : d 5 % 2 = 0)
    (hrec : ∀ n : ℕ, n ≥ 3 → d n % 2 = (d (n - 1) % 2 + d (n - 3) % 2) % 2) :
  d 6 % 2 = 1 := by
  have h_main : d 6 % 2 = 1 := by
    have h₆ : d 6 % 2 = (d 5 % 2 + d 3 % 2) % 2 := by
      have h₆₁ : d 6 % 2 = (d 5 % 2 + d 3 % 2) % 2 := by
        have h₆₂ : 6 ≥ 3 := by norm_num
        have h₆₃ : d 6 % 2 = (d (6 - 1) % 2 + d (6 - 3) % 2) % 2 := hrec 6 h₆₂
        norm_num at h₆₃ ⊢
        <;> simpa [h₆₃] using h₆₃
      exact h₆₁
    rw [h₆]
    have h₇ : d 5 % 2 = 0 := hmod5
    have h₈ : d 3 % 2 = 1 := hmod3
    rw [h₇, h₈]
    <;> norm_num
    <;> rfl
  
  exact h_main

theorem h2021_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (hperiod : ∀ n, d (n + 7) % 2 = d n % 2) :
  d 2021 % 2 = d 5 % 2 := by
  have h_main : ∀ m : ℕ, d (5 + 7 * m) % 2 = d 5 % 2 := by
    intro m
    induction m with
    | zero =>
      -- Base case: when m = 0, 5 + 7 * 0 = 5, so the statement is trivially true.
      simp
    | succ m ih =>
      -- Inductive step: assume the statement holds for m, prove for m + 1.
      have h₁ : d (5 + 7 * (m + 1)) % 2 = d (5 + 7 * m + 7) % 2 := by
        -- Simplify the expression 5 + 7 * (m + 1) to 5 + 7 * m + 7.
        ring_nf at *
        <;> simp [add_assoc, add_comm, add_left_comm] at *
        <;> omega
      have h₂ : d (5 + 7 * m + 7) % 2 = d (5 + 7 * m) % 2 := by
        -- Use the given periodicity condition to relate d(5 + 7 * m + 7) to d(5 + 7 * m).
        have h₃ := hperiod (5 + 7 * m)
        -- Simplify the expression using the periodicity condition.
        simp [add_assoc, add_comm, add_left_comm] at h₃ ⊢
        <;> omega
      have h₃ : d (5 + 7 * m) % 2 = d 5 % 2 := ih
      -- Combine the results to get the final statement for m + 1.
      omega
  
  have h_2021 : d 2021 % 2 = d 5 % 2 := by
    have h₁ : d (5 + 7 * 288) % 2 = d 5 % 2 := h_main 288
    have h₂ : 5 + 7 * 288 = 2021 := by norm_num
    rw [h₂] at h₁
    exact h₁
  
  apply h_2021

theorem hperiod_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (hrec : ∀ n : ℕ, n ≥ 3 → d n % 2 = (d (n - 1) % 2 + d (n - 3) % 2) % 2)
    (hmod0 : d 0 % 2 = 0) (hmod1 : d 1 % 2 = 0) (hmod2 : d 2 % 2 = 1)
    (hmod3 : d 3 % 2 = 1) (hmod4 : d 4 % 2 = 1) (hmod5 : d 5 % 2 = 0) (hmod6 : d 6 % 2 = 1) :
  ∀ n, d (n + 7) % 2 = d n % 2 := by
  have hmod7 : d 7 % 2 = 0 := by
    have h₇ : d 7 % 2 = (d 6 % 2 + d 4 % 2) % 2 := by
      have h₇₁ : d 7 % 2 = (d 6 % 2 + d 4 % 2) % 2 := by
        have h₇₂ : 7 ≥ 3 := by norm_num
        have h₇₃ : d 7 % 2 = (d (7 - 1) % 2 + d (7 - 3) % 2) % 2 := hrec 7 (by norm_num)
        norm_num at h₇₃ ⊢
        <;> omega
      exact h₇₁
    rw [h₇]
    norm_num [hmod6, hmod4]
    <;> omega
  
  have hmod8 : d 8 % 2 = 0 := by
    have h₈ : d 8 % 2 = (d 7 % 2 + d 5 % 2) % 2 := by
      have h₈₁ : d 8 % 2 = (d 7 % 2 + d 5 % 2) % 2 := by
        have h₈₂ : 8 ≥ 3 := by norm_num
        have h₈₃ : d 8 % 2 = (d (8 - 1) % 2 + d (8 - 3) % 2) % 2 := hrec 8 (by norm_num)
        norm_num at h₈₃ ⊢
        <;> omega
      exact h₈₁
    rw [h₈]
    norm_num [hmod7, hmod5]
    <;> omega
  
  have hmod9 : d 9 % 2 = 1 := by
    have h₉ : d 9 % 2 = (d 8 % 2 + d 6 % 2) % 2 := by
      have h₉₁ : d 9 % 2 = (d 8 % 2 + d 6 % 2) % 2 := by
        have h₉₂ : 9 ≥ 3 := by norm_num
        have h₉₃ : d 9 % 2 = (d (9 - 1) % 2 + d (9 - 3) % 2) % 2 := hrec 9 (by norm_num)
        norm_num at h₉₃ ⊢
        <;> omega
      exact h₉₁
    rw [h₉]
    norm_num [hmod8, hmod6]
    <;> omega
  
  have hmod10 : d 10 % 2 = 1 := by
    have h₁₀ : d 10 % 2 = (d 9 % 2 + d 7 % 2) % 2 := by
      have h₁₀₁ : d 10 % 2 = (d 9 % 2 + d 7 % 2) % 2 := by
        have h₁₀₂ : 10 ≥ 3 := by norm_num
        have h₁₀₃ : d 10 % 2 = (d (10 - 1) % 2 + d (10 - 3) % 2) % 2 := hrec 10 (by norm_num)
        norm_num at h₁₀₃ ⊢
        <;> omega
      exact h₁₀₁
    rw [h₁₀]
    norm_num [hmod9, hmod7]
    <;> omega
  
  have hmod11 : d 11 % 2 = 1 := by
    have h₁₁ : d 11 % 2 = (d 10 % 2 + d 8 % 2) % 2 := by
      have h₁₁₁ : d 11 % 2 = (d 10 % 2 + d 8 % 2) % 2 := by
        have h₁₁₂ : 11 ≥ 3 := by norm_num
        have h₁₁₃ : d 11 % 2 = (d (11 - 1) % 2 + d (11 - 3) % 2) % 2 := hrec 11 (by norm_num)
        norm_num at h₁₁₃ ⊢
        <;> omega
      exact h₁₁₁
    rw [h₁₁]
    norm_num [hmod10, hmod8]
    <;> omega
  
  have hmod12 : d 12 % 2 = 0 := by
    have h₁₂ : d 12 % 2 = (d 11 % 2 + d 9 % 2) % 2 := by
      have h₁₂₁ : d 12 % 2 = (d 11 % 2 + d 9 % 2) % 2 := by
        have h₁₂₂ : 12 ≥ 3 := by norm_num
        have h₁₂₃ : d 12 % 2 = (d (12 - 1) % 2 + d (12 - 3) % 2) % 2 := hrec 12 (by norm_num)
        norm_num at h₁₂₃ ⊢
        <;> omega
      exact h₁₂₁
    rw [h₁₂]
    norm_num [hmod11, hmod9]
    <;> omega
  
  have hmod13 : d 13 % 2 = 1 := by
    have h₁₃ : d 13 % 2 = (d 12 % 2 + d 10 % 2) % 2 := by
      have h₁₃₁ : d 13 % 2 = (d 12 % 2 + d 10 % 2) % 2 := by
        have h₁₃₂ : 13 ≥ 3 := by norm_num
        have h₁₃₃ : d 13 % 2 = (d (13 - 1) % 2 + d (13 - 3) % 2) % 2 := hrec 13 (by norm_num)
        norm_num at h₁₃₃ ⊢
        <;> omega
      exact h₁₃₁
    rw [h₁₃]
    norm_num [hmod12, hmod10]
    <;> omega
  
  have hbase0 : d (0 + 7) % 2 = d 0 % 2 := by
    norm_num [hmod7, hmod0] at *
    <;> simp_all (config := {decide := true})
  
  have hbase1 : d (1 + 7) % 2 = d 1 % 2 := by
    norm_num [hmod8, hmod1] at *
    <;> simp_all (config := {decide := true})
  
  have hbase2 : d (2 + 7) % 2 = d 2 % 2 := by
    norm_num [hmod9, hmod2] at *
    <;> simp_all (config := {decide := true})
  
  have hbase3 : d (3 + 7) % 2 = d 3 % 2 := by
    norm_num [hmod10, hmod3] at *
    <;> simp_all (config := {decide := true})
  
  have hbase4 : d (4 + 7) % 2 = d 4 % 2 := by
    norm_num [hmod11, hmod4] at *
    <;> simp_all (config := {decide := true})
  
  have hbase5 : d (5 + 7) % 2 = d 5 % 2 := by
    norm_num [hmod12, hmod5] at *
    <;> simp_all (config := {decide := true})
  
  have hbase6 : d (6 + 7) % 2 = d 6 % 2 := by
    norm_num [hmod13, hmod6] at *
    <;> simp_all (config := {decide := true})
  
  have hmain : ∀ n, d (n + 7) % 2 = d n % 2 := by
    intro n
    have h : ∀ n, d (n + 7) % 2 = d n % 2 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        match n with
        | 0 =>
          simpa using hbase0
        | 1 =>
          simpa using hbase1
        | 2 =>
          simpa using hbase2
        | 3 =>
          simpa using hbase3
        | 4 =>
          simpa using hbase4
        | 5 =>
          simpa using hbase5
        | 6 =>
          simpa using hbase6
        | n + 7 =>
          have h₁ := hrec (n + 7 + 7) (by omega)
          have h₂ := hrec (n + 7) (by omega)
          have h₃ := ih (n + 6) (by omega)
          have h₄ := ih (n + 4) (by omega)
          have h₅ := ih (n + 3) (by omega)
          have h₆ := ih (n + 2) (by omega)
          have h₇ := ih (n + 1) (by omega)
          have h₈ := ih n (by omega)
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ ⊢
          <;>
          (try omega) <;>
          (try
            {
              simp [h₃, h₄, h₂, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at *
              <;>
              (try omega) <;>
              (try ring_nf at *) <;>
              (try norm_num at *) <;>
              (try omega)
            }) <;>
          (try
            {
              simp [h₃, h₄, h₂, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at *
              <;>
              omega
            }) <;>
          (try
            {
              simp_all [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              <;>
              omega
            })
          <;>
          (try
            {
              ring_nf at *
              <;>
              norm_num at *
              <;>
              omega
            })
          <;>
          (try
            {
              simp_all [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              <;>
              omega
            })
    exact h n
  
  exact hmain

theorem hOdd2022_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (hmod6 : d 6 % 2 = 1) (h2022 : d 2022 % 2 = d 6 % 2) :
  Odd (d 2022) := by
  have h2022_mod2 : d 2022 % 2 = 1 := by
    have h : d 2022 % 2 = d 6 % 2 := h2022
    rw [h]
    <;> simp [hmod6]
    <;> norm_num
  
  have h_odd : Odd (d 2022) := by
    rw [Nat.odd_iff]
    <;> omega
  
  exact h_odd

theorem hEven2023_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (hmod0 : d 0 % 2 = 0) (h2023 : d 2023 % 2 = d 0 % 2) :
  Even (d 2023) := by
  have h_mod_2023 : d 2023 % 2 = 0 := by
    have h₄ : d 2023 % 2 = d 0 % 2 := h2023
    have h₅ : d 0 % 2 = 0 := hmod0
    rw [h₄, h₅]
    <;> simp
  
  have h_even : Even (d 2023) := by
    rw [even_iff_two_dvd]
    have h₄ : d 2023 % 2 = 0 := h_mod_2023
    omega
  
  exact h_even

theorem hEven2021_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (hmod5 : d 5 % 2 = 0) (h2021 : d 2021 % 2 = d 5 % 2) :
  Even (d 2021) := by
  have h_d2021_mod2 : d 2021 % 2 = 0 := by
    have h₄ : d 2021 % 2 = d 5 % 2 := h2021
    have h₅ : d 5 % 2 = 0 := hmod5
    rw [h₄, h₅]
    <;> simp
  
  have h_main : Even (d 2021) := by
    rw [even_iff_two_dvd]
    have h₆ : d 2021 % 2 = 0 := h_d2021_mod2
    have h₇ : 2 ∣ d 2021 := by
      omega
    exact h₇
  
  exact h_main

theorem h2022_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (hperiod : ∀ n, d (n + 7) % 2 = d n % 2) :
  d 2022 % 2 = d 6 % 2 := by
  have h_main : ∀ (k : ℕ), d (6 + 7 * k) % 2 = d 6 % 2 := by
    intro k
    induction k with
    | zero =>
      -- Base case: when k = 0, 6 + 7 * 0 = 6, so d(6) % 2 = d(6) % 2
      simp
    | succ k ih =>
      -- Inductive step: assume the statement holds for k, prove for k + 1
      have h₁ : d (6 + 7 * (k + 1)) % 2 = d (6 + 7 * k + 7) % 2 := by
        -- Simplify the expression 6 + 7 * (k + 1) to 6 + 7 * k + 7
        ring_nf at *
        <;> simp [add_assoc, add_comm, add_left_comm] at *
        <;> omega
      have h₂ : d (6 + 7 * k + 7) % 2 = d (6 + 7 * k) % 2 := by
        -- Use the periodicity condition to relate d(6 + 7 * k + 7) and d(6 + 7 * k)
        have h₃ := hperiod (6 + 7 * k)
        -- Simplify the expression to match the form in hperiod
        simp [add_assoc, add_comm, add_left_comm] at h₃ ⊢
        <;> omega
      have h₃ : d (6 + 7 * (k + 1)) % 2 = d (6 + 7 * k) % 2 := by
        -- Combine the previous two results
        rw [h₁, h₂]
      have h₄ : d (6 + 7 * (k + 1)) % 2 = d 6 % 2 := by
        -- Use the induction hypothesis to complete the proof
        rw [h₃]
        exact ih
      exact h₄
  
  have h_2022 : 6 + 7 * 288 = 2022 := by
    norm_num
    <;> rfl
  
  have h_final : d 2022 % 2 = d 6 % 2 := by
    have h₁ : d (6 + 7 * 288) % 2 = d 6 % 2 := h_main 288
    have h₂ : 6 + 7 * 288 = 2022 := h_2022
    rw [h₂] at h₁
    exact h₁
  
  exact h_final

theorem h2023_amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3))
    (hperiod : ∀ n, d (n + 7) % 2 = d n % 2) :
  d 2023 % 2 = d 0 % 2 := by
  have h_main : ∀ k : ℕ, d (7 * k) % 2 = d 0 % 2 := by
    intro k
    induction k with
    | zero =>
      -- Base case: when k = 0, 7 * 0 = 0, so d(0) % 2 = d(0) % 2
      simp [h₀]
    | succ k ih =>
      -- Inductive step: assume the statement holds for k, prove for k + 1
      have h₁ : d (7 * (k + 1)) % 2 = d (7 * k + 7) % 2 := by
        ring_nf
        <;> simp [mul_add, add_mul, Nat.mul_succ]
        <;> ring_nf
      have h₂ : d (7 * k + 7) % 2 = d (7 * k) % 2 := by
        -- Use the periodicity condition to relate d(7k + 7) and d(7k)
        have h₃ := hperiod (7 * k)
        -- Simplify the expression to match the form in hperiod
        simp [add_assoc] at h₃ ⊢
        <;> omega
      have h₃ : d (7 * (k + 1)) % 2 = d (7 * k) % 2 := by
        -- Combine the previous results
        rw [h₁, h₂]
      have h₄ : d (7 * k) % 2 = d 0 % 2 := ih
      -- Use the induction hypothesis to conclude the proof
      rw [h₃, h₄]
  
  have h_final : d 2023 % 2 = d 0 % 2 := by
    have h₁ : d (7 * 289) % 2 = d 0 % 2 := h_main 289
    have h₂ : 7 * 289 = 2023 := by norm_num
    rw [h₂] at h₁
    exact h₁
  
  apply h_final

theorem amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) :
    Even (d 2021) ∧ Odd (d 2022) ∧ Even (d 2023) := by
  -- parity of the first three terms
  have hmod0 : d 0 % 2 = 0 :=
    hmod0_amc12a_2021_p8 d h₀ h₁ h₂ h₃
  have hmod1 : d 1 % 2 = 0 :=
    hmod1_amc12a_2021_p8 d h₀ h₁ h₂ h₃
  have hmod2 : d 2 % 2 = 1 :=
    hmod2_amc12a_2021_p8 d h₀ h₁ h₂ h₃
  -- recurrence for the parity modulo 2
  have hrec : ∀ n : ℕ, n ≥ 3 → d n % 2 = (d (n - 1) % 2 + d (n - 3) % 2) % 2 := by
    intro n hn
    exact hrec_amc12a_2021_p8 d h₀ h₁ h₂ h₃ n hn
  -- compute the next few parities
  have hmod3 : d 3 % 2 = 1 :=
    hmod3_amc12a_2021_p8 d h₀ h₁ h₂ h₃ hmod0 hmod1 hmod2 hrec
  have hmod4 : d 4 % 2 = 1 :=
    hmod4_amc12a_2021_p8 d h₀ h₁ h₂ h₃ hmod0 hmod1 hmod2 hmod3 hrec
  have hmod5 : d 5 % 2 = 0 :=
    hmod5_amc12a_2021_p8 d h₀ h₁ h₂ h₃ hmod0 hmod1 hmod2 hmod3 hmod4 hrec
  have hmod6 : d 6 % 2 = 1 :=
    hmod6_amc12a_2021_p8 d h₀ h₁ h₂ h₃ hmod0 hmod1 hmod2 hmod3 hmod4 hmod5 hrec
  -- periodicity of the parity sequence with period 7
  have hperiod : ∀ n, d (n + 7) % 2 = d n % 2 :=
    hperiod_amc12a_2021_p8 d h₀ h₁ h₂ h₃ hrec hmod0 hmod1 hmod2 hmod3 hmod4 hmod5 hmod6
  -- reduce the large indices modulo 7
  have h2021 : d 2021 % 2 = d 5 % 2 :=
    h2021_amc12a_2021_p8 d h₀ h₁ h₂ h₃ hperiod
  have h2022 : d 2022 % 2 = d 6 % 2 :=
    h2022_amc12a_2021_p8 d h₀ h₁ h₂ h₃ hperiod
  have h2023 : d 2023 % 2 = d 0 % 2 :=
    h2023_amc12a_2021_p8 d h₀ h₁ h₂ h₃ hperiod
  -- translate the modulo information to Even / Odd statements
  have hEven2021 : Even (d 2021) :=
    hEven2021_amc12a_2021_p8 d h₀ h₁ h₂ h₃ hmod5 h2021
  have hOdd2022 : Odd (d 2022) :=
    hOdd2022_amc12a_2021_p8 d h₀ h₁ h₂ h₃ hmod6 h2022
  have hEven2023 : Even (d 2023) :=
    hEven2023_amc12a_2021_p8 d h₀ h₁ h₂ h₃ hmod0 h2023
  exact ⟨hEven2021, hOdd2022, hEven2023⟩

import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem hp_range_amc12_2000_p6 (p q : ℕ) (h₁ : 4 ≤ p ∧ p ≤ 18) : 4 ≤ p ∧ p ≤ 18 := by
  exact h₁

theorem hq_range_amc12_2000_p6 (p q : ℕ) (h₂ : 4 ≤ q ∧ q ≤ 18) : 4 ≤ q ∧ q ≤ 18 := by
  exact h₂

theorem hp_prime_amc12_2000_p6 (p q : ℕ) (h₀ : Nat.Prime p ∧ Nat.Prime q) : Nat.Prime p := by
  have h₁ : Nat.Prime p := h₀.1
  exact h₁

theorem hq_prime_amc12_2000_p6 (p q : ℕ) (h₀ : Nat.Prime p ∧ Nat.Prime q) : Nat.Prime q := by
  have h₁ : Nat.Prime q := h₀.2
  exact h₁

theorem h_eq_nat_amc12_2000_p6 (p q : ℕ) (h_eq : (p : ℕ) * q - (p + q) = 194) :
    (p : ℕ) * q - (p + q) = 194 := by
  exact h_eq

theorem hp_mem_amc12_2000_p6 (p : ℕ) (hp_cases : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17) :
    p - 1 ∈ ({4,6,10,12,16} : Finset ℕ) := by
  have h : p - 1 = 4 ∨ p - 1 = 6 ∨ p - 1 = 10 ∨ p - 1 = 12 ∨ p - 1 = 16 := by
    rcases hp_cases with (rfl | rfl | rfl | rfl | rfl)
    · -- Case p = 5
      norm_num
    · -- Case p = 7
      norm_num
    · -- Case p = 11
      norm_num
    · -- Case p = 13
      norm_num
    · -- Case p = 17
      norm_num
  -- Now we need to show that p - 1 is in the set {4, 6, 10, 12, 16}
  simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
  tauto

theorem hq_mem_amc12_2000_p6 (q : ℕ) (hq_cases : q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 17) :
    q - 1 ∈ ({4,6,10,12,16} : Finset ℕ) := by
  have h₁ : q - 1 ∈ ({4,6,10,12,16} : Finset ℕ) := by
    -- Consider each case of q and verify that q - 1 is in the set {4, 6, 10, 12, 16}
    rcases hq_cases with (rfl | rfl | rfl | rfl | rfl)
    · -- Case q = 5
      norm_num [Finset.mem_insert, Finset.mem_singleton]
    · -- Case q = 7
      norm_num [Finset.mem_insert, Finset.mem_singleton]
    · -- Case q = 11
      norm_num [Finset.mem_insert, Finset.mem_singleton]
    · -- Case q = 13
      norm_num [Finset.mem_insert, Finset.mem_singleton]
    · -- Case q = 17
      norm_num [Finset.mem_insert, Finset.mem_singleton]
  exact h₁

theorem hq_cases_amc12_2000_p6 (q : ℕ) (hq_prime : Nat.Prime q) (hq_range : 4 ≤ q ∧ q ≤ 18) :
    q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 17 := by
  have hlt19 : q < 19 := Nat.lt_of_le_of_lt hq_range.2 (by decide)
  have hmem : q ∈ Nat.primesBelow 19 :=
    (Nat.mem_primesBelow).mpr ⟨hlt19, hq_prime⟩
  have hmem' :
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 17 := by
    have : q ∈ ({2, 3, 5, 7, 11, 13, 17} : Finset ℕ) := by
      have h_eq : Nat.primesBelow 19 = ({2, 3, 5, 7, 11, 13, 17} : Finset ℕ) := by
        decide
      simpa [h_eq] using hmem
    simpa [Finset.mem_insert, Finset.mem_singleton] using this
  rcases hmem' with h2 | h3 | h5 | h7 | h11 | h13 | h17
  · have hle : (4 : ℕ) ≤ 2 := by simpa [h2] using hq_range.1
    cases (Nat.not_le.mpr (by decide : (2 : ℕ) < 4) hle)
  · have hle : (4 : ℕ) ≤ 3 := by simpa [h3] using hq_range.1
    cases (Nat.not_le.mpr (by decide : (3 : ℕ) < 4) hle)
  · exact Or.inl h5
  · exact Or.inr (Or.inl h7)
  · exact Or.inr (Or.inr (Or.inl h11))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h13)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h17)))

theorem h_lt_19_hp_cases_amc12_2000_p6 (p : ℕ) (h_up : p ≤ 18) : p < 19 := by
  have h : p < 19 := by
    omega
  exact h

theorem h_low_hp_cases_amc12_2000_p6 (p : ℕ) (hp_range : 4 ≤ p ∧ p ≤ 18) : 4 ≤ p := by
  have h₁ : 4 ≤ p := hp_range.1
  exact h₁

theorem h_primes_eq_hp_cases_amc12_2000_p6 :
    Nat.primesBelow 19 = ({2, 3, 5, 7, 11, 13, 17} : Finset ℕ) := by
  apply Eq.symm
  apply Eq.symm
  rfl

theorem h_up_hp_cases_amc12_2000_p6 (p : ℕ) (hp_range : 4 ≤ p ∧ p ≤ 18) : p ≤ 18 := by
  have h : p ≤ 18 := by
    -- Extract the upper bound from the hypothesis
    have h₁ : p ≤ 18 := hp_range.2
    -- The upper bound is already given, so we can directly use it
    exact h₁
  -- The result follows directly from the extracted upper bound
  exact h

theorem h_mem_list_hp_cases_amc12_2000_p6 (p : ℕ)
    (h_mem_primes : p ∈ Nat.primesBelow 19)
    (h_primes_eq : Nat.primesBelow 19 = ({2, 3, 5, 7, 11, 13, 17} : Finset ℕ)) :
    p ∈ ({2, 3, 5, 7, 11, 13, 17} : Finset ℕ) := by
  rw [h_primes_eq] at h_mem_primes
  exact h_mem_primes

theorem h_not_two_three_hp_cases_amc12_2000_p6 (p : ℕ) (h_five_le : 5 ≤ p) :
    p ≠ 2 ∧ p ≠ 3 := by
  have h₁ : p ≠ 2 := by
    intro h
    have h₂ : p = 2 := h
    have h₃ : 5 ≤ p := h_five_le
    linarith
  have h₂ : p ≠ 3 := by
    intro h
    have h₃ : p = 3 := h
    have h₄ : 5 ≤ p := h_five_le
    linarith
  exact ⟨h₁, h₂⟩

theorem h_five_le_hp_cases_amc12_2000_p6 (p : ℕ) (hp_prime : Nat.Prime p) (h_low : 4 ≤ p) : 5 ≤ p := by
  have h₁ : p ≥ 4 := by linarith
  have h₂ : p ≠ 4 := by
    intro h
    rw [h] at hp_prime
    norm_num at hp_prime
    <;> contradiction
  have h₃ : p ≥ 5 := by
    by_contra h
    -- If p is not ≥ 5, then p must be 4 because p ≥ 4 and p is an integer
    have h₄ : p ≤ 4 := by linarith
    have h₅ : p = 4 := by
      omega
    contradiction
  linarith

theorem h_mem_reduced_hp_cases_amc12_2000_p6 (p : ℕ)
    (h_mem_list : p ∈ ({2, 3, 5, 7, 11, 13, 17} : Finset ℕ))
    (h_not_two_three : p ≠ 2 ∧ p ≠ 3) :
    p ∈ ({5, 7, 11, 13, 17} : Finset ℕ) := by
  have h₁ : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem_list
    tauto
  have h₂ : p ≠ 2 := h_not_two_three.1
  have h₃ : p ≠ 3 := h_not_two_three.2
  have h₄ : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 := by
    rcases h₁ with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp_all (config := {decide := true})
    <;> norm_num at * <;> try contradiction
    <;> try tauto
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases h₄ with (rfl | rfl | rfl | rfl | rfl) <;> simp_all (config := {decide := true})
  <;> norm_num at * <;> try contradiction
  <;> try tauto

theorem h_mem_primes_hp_cases_amc12_2000_p6 (p : ℕ) (hp_prime : Nat.Prime p) (h_lt_19 : p < 19) :
    p ∈ Nat.primesBelow 19 := by
  exact (Nat.mem_primesBelow (k := 19) (n := p)).2 ⟨h_lt_19, hp_prime⟩

theorem hp_cases_amc12_2000_p6 (p : ℕ) (hp_prime : Nat.Prime p) (hp_range : 4 ≤ p ∧ p ≤ 18) :
    p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 := by
  -- lower and upper bounds from the range hypothesis
  have h_low : (4 : ℕ) ≤ p := by
    exact h_low_hp_cases_amc12_2000_p6 p hp_range
  have h_up : p ≤ (18 : ℕ) := by
    exact h_up_hp_cases_amc12_2000_p6 p hp_range
  -- strengthen the lower bound to 5 ≤ p (using primality)
  have h_five_le : (5 : ℕ) ≤ p := by
    exact h_five_le_hp_cases_amc12_2000_p6 p hp_prime h_low
  -- turn the upper bound into a strict inequality p < 19
  have h_lt_19 : p < (19 : ℕ) := by
    exact h_lt_19_hp_cases_amc12_2000_p6 p h_up
  -- p is a prime below 19, hence belongs to `Nat.primesBelow 19`
  have h_mem_primes : p ∈ Nat.primesBelow 19 := by
    exact h_mem_primes_hp_cases_amc12_2000_p6 p hp_prime h_lt_19
  -- explicit description of the primes below 19
  have h_primes_eq :
      Nat.primesBelow 19 = ({2, 3, 5, 7, 11, 13, 17} : Finset ℕ) := by
    exact h_primes_eq_hp_cases_amc12_2000_p6
  -- rewrite membership using the explicit list
  have h_mem_list : p ∈ ({2, 3, 5, 7, 11, 13, 17} : Finset ℕ) := by
    exact h_mem_list_hp_cases_amc12_2000_p6 p h_mem_primes h_primes_eq
  -- eliminate the small primes 2 and 3 using the lower bound 5 ≤ p
  have h_not_two_three : p ≠ 2 ∧ p ≠ 3 := by
    exact h_not_two_three_hp_cases_amc12_2000_p6 p h_five_le
  -- from the previous facts obtain membership in the reduced set {5,7,11,13,17}
  have h_mem_reduced : p ∈ ({5, 7, 11, 13, 17} : Finset ℕ) := by
    exact h_mem_reduced_hp_cases_amc12_2000_p6 p h_mem_list h_not_two_three
  -- translate membership of the finite set into the required disjunction
  simpa [Finset.mem_insert, Finset.mem_singleton] using h_mem_reduced

theorem h_not_eq_amc12_2000_p6 (p q : ℕ)
    (hp_mem : p - 1 ∈ ({4,6,10,12,16} : Finset ℕ))
    (hq_mem : q - 1 ∈ ({4,6,10,12,16} : Finset ℕ)) :
    (p - 1) * (q - 1) ≠ 195 := by
  have h_main : (p - 1) * (q - 1) ≠ 195 := by
    have h₁ : p - 1 = 4 ∨ p - 1 = 6 ∨ p - 1 = 10 ∨ p - 1 = 12 ∨ p - 1 = 16 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp_mem
      tauto
    have h₂ : q - 1 = 4 ∨ q - 1 = 6 ∨ q - 1 = 10 ∨ q - 1 = 12 ∨ q - 1 = 16 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq_mem
      tauto
    -- We now consider all combinations of p - 1 and q - 1
    rcases h₁ with (h₁ | h₁ | h₁ | h₁ | h₁) <;>
    rcases h₂ with (h₂ | h₂ | h₂ | h₂ | h₂) <;>
    (try { contradiction }) <;>
    (try {
      simp [h₁, h₂, Nat.mul_assoc]
      <;> norm_num <;>
      (try { contradiction }) <;>
      (try { omega })
    }) <;>
    (try {
      ring_nf at *
      <;> norm_num at *
      <;> omega
    })
  exact h_main

theorem h_mul_eq_amc12_2000_p6 (p q : ℕ) (h_eq_nat : (p : ℕ) * q - (p + q) = 194) :
    (p - 1) * (q - 1) = 195 := by
  have h_pq_ge_pq : p * q ≥ p + q := by
    by_contra h
    -- Assume for contradiction that p * q < p + q
    have h₁ : p * q < p + q := by
      omega
    -- If p * q < p + q, then p * q - (p + q) = 0 in ℕ
    have h₂ : p * q - (p + q) = 0 := by
      have h₃ : p * q ≤ p + q := by omega
      have h₄ : p * q - (p + q) = 0 := by
        apply Nat.sub_eq_zero_of_le
        <;> omega
      exact h₄
    -- But this contradicts the given equation p * q - (p + q) = 194
    omega
  
  have h_p_ge_2 : p ≥ 2 := by
    by_contra h
    -- Assume p < 2, then p is 0 or 1
    have h₁ : p ≤ 1 := by omega
    have h₂ : p = 0 ∨ p = 1 := by
      omega
    -- Case analysis on p = 0 or p = 1
    rcases h₂ with (rfl | rfl)
    · -- Case p = 0
      -- If p = 0, then 0 * q - (0 + q) = 0, which contradicts the given equation
      simp at h_eq_nat
      <;> omega
    · -- Case p = 1
      -- If p = 1, then 1 * q - (1 + q) = 0, which contradicts the given equation
      have h₃ : q ≥ 0 := by omega
      have h₄ : 1 * q - (1 + q) = 0 := by
        have h₅ : 1 * q < 1 + q := by
          nlinarith
        have h₆ : 1 * q - (1 + q) = 0 := by
          apply Nat.sub_eq_zero_of_le
          <;> omega
        exact h₆
      omega
  
  have h_q_ge_2 : q ≥ 2 := by
    by_contra h
    -- Assume q < 2, then q is 0 or 1
    have h₁ : q ≤ 1 := by omega
    have h₂ : q = 0 ∨ q = 1 := by
      omega
    -- Case analysis on q = 0 or q = 1
    rcases h₂ with (rfl | rfl)
    · -- Case q = 0
      -- If q = 0, then p * 0 - (p + 0) = 0, which contradicts the given equation
      simp at h_eq_nat
      <;> omega
    · -- Case q = 1
      -- If q = 1, then p * 1 - (p + 1) = 0, which contradicts the given equation
      have h₃ : p ≥ 0 := by omega
      have h₄ : p * 1 - (p + 1) = 0 := by
        have h₅ : p * 1 < p + 1 := by
          nlinarith
        have h₆ : p * 1 - (p + 1) = 0 := by
          apply Nat.sub_eq_zero_of_le
          <;> omega
        exact h₆
      omega
  
  have h_pq_eq : p * q = p + q + 194 := by
    have h₁ : p * q - (p + q) = 194 := h_eq_nat
    have h₂ : p * q ≥ p + q := h_pq_ge_pq
    have h₃ : p * q = p + q + 194 := by
      have h₄ : p * q - (p + q) = 194 := h₁
      have h₅ : p * q ≥ p + q := h₂
      have h₆ : p * q = p + q + 194 := by
        -- Use the fact that p * q - (p + q) = 194 to find p * q
        have h₇ : p * q = p + q + 194 := by
          -- Use the omega tactic to solve the equation
          omega
        exact h₇
      exact h₆
    exact h₃
  
  have h_main : (p - 1) * (q - 1) = 195 := by
    have h₁ : p ≥ 2 := h_p_ge_2
    have h₂ : q ≥ 2 := h_q_ge_2
    have h₃ : p * q = p + q + 194 := h_pq_eq
    have h₄ : (p - 1) * (q - 1) = 195 := by
      cases p with
      | zero => contradiction -- p cannot be zero since p ≥ 2
      | succ p' =>
        cases p' with
        | zero => contradiction -- p cannot be one since p ≥ 2
        | succ p'' =>
          cases q with
          | zero => contradiction -- q cannot be zero since q ≥ 2
          | succ q' =>
            cases q' with
            | zero => contradiction -- q cannot be one since q ≥ 2
            | succ q'' =>
              -- Simplify the expressions using the cases
              simp [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_assoc] at h₃ ⊢
              <;> ring_nf at h₃ ⊢ <;>
                (try omega) <;>
                (try
                  {
                    nlinarith
                  }) <;>
                (try
                  {
                    simp_all [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_assoc]
                    <;> ring_nf at *
                    <;> omega
                  })
    exact h₄
  
  apply h_main

theorem amc12_2000_p6 (p q : ℕ) (h₀ : Nat.Prime p ∧ Nat.Prime q) (h₁ : 4 ≤ p ∧ p ≤ 18)
    (h₂ : 4 ≤ q ∧ q ≤ 18) : ↑p * ↑q - (↑p + ↑q) ≠ (194 : ℕ) := by
  intro h_eq
  have hp_prime : Nat.Prime p := by
    exact hp_prime_amc12_2000_p6 p q h₀
  have hq_prime : Nat.Prime q := by
    exact hq_prime_amc12_2000_p6 p q h₀
  have hp_range : 4 ≤ p ∧ p ≤ 18 := by
    exact hp_range_amc12_2000_p6 p q h₁
  have hq_range : 4 ≤ q ∧ q ≤ 18 := by
    exact hq_range_amc12_2000_p6 p q h₂
  have h_eq_nat : (p : ℕ) * q - (p + q) = 194 := by
    exact h_eq_nat_amc12_2000_p6 p q (by
      simpa using h_eq)
  have h_mul_eq : (p - 1) * (q - 1) = 195 := by
    exact h_mul_eq_amc12_2000_p6 p q h_eq_nat
  have hp_cases : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 := by
    exact hp_cases_amc12_2000_p6 p hp_prime hp_range
  have hq_cases : q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 17 := by
    exact hq_cases_amc12_2000_p6 q hq_prime hq_range
  have hp_mem : p - 1 ∈ ({4,6,10,12,16} : Finset ℕ) := by
    exact hp_mem_amc12_2000_p6 p hp_cases
  have hq_mem : q - 1 ∈ ({4,6,10,12,16} : Finset ℕ) := by
    exact hq_mem_amc12_2000_p6 q hq_cases
  have h_not_eq : (p - 1) * (q - 1) ≠ 195 := by
    exact h_not_eq_amc12_2000_p6 p q hp_mem hq_mem
  exact h_not_eq h_mul_eq

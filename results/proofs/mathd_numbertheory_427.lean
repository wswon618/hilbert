import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem hsumPrime_mathd_numbertheory_427 (a : ℕ) (hprime_factors : a.primeFactors = {2, 3, 7, 13}) :
    (∑ p in a.primeFactors, p) = 25 := by
  rw [hprime_factors]
  norm_num
  <;>
  rfl

theorem ha_mathd_numbertheory_427 (a : ℕ) (h₀ : a = ∑ k in Nat.divisors 500, k) (hsum500 : ∑ k in Nat.divisors 500, k = 1092) :
    a = 1092 := by
  have h₁ : a = 1092 := by
    rw [h₀]
    rw [hsum500]
  exact h₁

theorem hsum500_mathd_numbertheory_427 : ∑ k in Nat.divisors 500, k = 1092 := by
  rw [show 500 = 2 ^ 2 * 5 ^ 3 by norm_num]
  rw [Nat.divisors_mul, Nat.divisors_prime_pow (by decide : Nat.Prime 2), Nat.divisors_prime_pow (by decide : Nat.Prime 5)]
  <;>
  norm_num
  <;>
  rfl
  <;>
  decide
  <;>
  decide
  <;>
  decide

theorem hprime_factors_mathd_numbertheory_427 (a : ℕ) (ha : a = 1092) :
    a.primeFactors = {2, 3, 7, 13} := by
  simpa [ha] using
    (by
      native_decide : (1092).primeFactors = {2, 3, 7, 13})

theorem hfilter_eq_mathd_numbertheory_427 (a : ℕ) :
    (∑ k in Finset.filter (fun x => Nat.Prime x) (Nat.divisors a), k) =
      ∑ p in a.primeFactors, p := by
  have h₁ : (∑ k in Finset.filter (fun x => Nat.Prime x) (Nat.divisors a), k) = ∑ p in a.primeFactors, p := by
    have h₂ : Finset.filter (fun x => Nat.Prime x) (Nat.divisors a) = a.primeFactors := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_filter, Finset.mem_coe, Finset.mem_range, Nat.mem_divisors, Nat.dvd_prime,
        Nat.prime_iff, Finset.mem_filter, Finset.mem_coe, Finset.mem_range]
      <;>
      (try cases a <;> simp_all [Nat.prime_iff, Nat.divisors, Finset.mem_filter, Finset.mem_coe, Finset.mem_range]) <;>
      (try
        {
          by_cases h : x = 0 <;> simp_all [Nat.Prime, Nat.succ_pos]
          <;>
          (try omega) <;>
          (try
            {
              norm_num at *
              <;>
              aesop
            })
        }) <;>
      (try
        {
          by_cases h : x = 1 <;> simp_all [Nat.Prime, Nat.succ_pos]
          <;>
          (try omega) <;>
          (try
            {
              norm_num at *
              <;>
              aesop
            })
        }) <;>
      (try
        {
          by_cases h : x = a <;> simp_all [Nat.Prime, Nat.succ_pos]
          <;>
          (try omega) <;>
          (try
            {
              norm_num at *
              <;>
              aesop
            })
        }) <;>
      (try
        {
          by_cases h : x ∣ a <;> simp_all [Nat.Prime, Nat.succ_pos]
          <;>
          (try omega) <;>
          (try
            {
              norm_num at *
              <;>
              aesop
            })
        }) <;>
      (try
        {
          by_cases h : Nat.Prime x <;> simp_all [Nat.Prime, Nat.succ_pos]
          <;>
          (try omega) <;>
          (try
            {
              norm_num at *
              <;>
              aesop
            })
        }) <;>
      (try
        {
          aesop
        })
      <;>
      (try
        {
          simp_all [Nat.Prime, Nat.succ_pos]
          <;>
          (try omega) <;>
          (try
            {
              norm_num at *
              <;>
              aesop
            })
        })
    rw [h₂]
  exact h₁

theorem mathd_numbertheory_427 (a : ℕ) (h₀ : a = ∑ k in Nat.divisors 500, k) :
    (∑ k in Finset.filter (fun x => Nat.Prime x) (Nat.divisors a), k) = 25 := by
  have hsum500 : ∑ k in Nat.divisors 500, k = 1092 := by
    exact hsum500_mathd_numbertheory_427
  have ha : a = 1092 := by
    exact ha_mathd_numbertheory_427 a h₀ hsum500
  have hprime_factors : a.primeFactors = {2, 3, 7, 13} := by
    exact hprime_factors_mathd_numbertheory_427 a ha
  have hsumPrime : (∑ p in a.primeFactors, p) = 25 := by
    exact hsumPrime_mathd_numbertheory_427 a hprime_factors
  have hfilter_eq :
      (∑ k in Finset.filter (fun x => Nat.Prime x) (Nat.divisors a), k) =
        ∑ p in a.primeFactors, p := by
    exact hfilter_eq_mathd_numbertheory_427 a
  simpa [hfilter_eq] using hsumPrime

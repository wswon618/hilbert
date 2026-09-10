# mathd_numbertheory_451

## Original input

```lean
theorem mathd_numbertheory_451 (S : Finset ℕ)
    (h₀ :
      ∀ n : ℕ,
        n ∈ S ↔
          2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n) :
    (∑ k in S, k) = 2016 := by

```

## Snapshot 1 mathd_numbertheory_451

2026-09-08 02:50:56,378 [log](../../../logs/screen57_20260907_021530.log:689089)

```lean
theorem mathd_numbertheory_451 (S : Finset ℕ)
    (h₀ :
      ∀ n : ℕ,
        n ∈ S ↔
          2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n) :
    (∑ k in S, k) = 2016 := by
  -- 2016 belongs to `S`
  have h_mem_2016 : (2016 : ℕ) ∈ S := by sorry
  -- every element of `S` is 2016
  have h_subset : S ⊆ ({2016} : Finset ℕ) := by sorry
  -- equality of the two finsets
  have h_eq : (S : Finset ℕ) = {2016} := by sorry
  -- compute the sum
  simpa [h_eq] using (by
    have : (∑ k in ({2016} : Finset ℕ), k) = (2016 : ℕ) := by sorry
    exact this)
```

## Snapshot 2 h_subset_mathd_numbertheory_451

2026-09-08 03:37:40,010 [log](../../../logs/screen57_20260907_021530.log:701712)

```lean
theorem h_subset_mathd_numbertheory_451 (S : Finset ℕ)
    (h₀ :
      ∀ n : ℕ,
        n ∈ S ↔
          2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n)
    (h_mem_2016 : (2016 : ℕ) ∈ S) :
    S ⊆ ({2016} : Finset ℕ) := by
  intro n hn
  -- unpack the characterisation of membership in `S`
  have h_cond :
      (2010 ≤ n ∧ n ≤ 2019) ∧
        ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n := by sorry
  -- extract the interval bounds
  have h_bounds : 2010 ≤ n ∧ n ≤ 2019 := by sorry
  -- obtain a witness `m` whose divisor‑set has cardinality 4 and whose divisor sum is `n`
  have h_exists_m : ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n := by sorry
  rcases h_exists_m with ⟨m, hm_card, hm_sum⟩
  -- describe the shape of `m` when its divisor set has exactly four elements
  have h_m_structure :
      ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ m = p * q := by sorry
  rcases h_m_structure with ⟨p, q, hp, hq, hpq, hm_eq⟩
  -- compute the sum of the four divisors of a product of two distinct primes
  have h_sum_eq : (∑ r in Nat.divisors m, r) = (p + 1) * (q + 1) := by sorry
  -- rewrite `n` using the previous equalities
  have h_n_eq : n = (p + 1) * (q + 1) := by sorry
  -- the only possible value in the interval is `2016`
  have h_n_eq_2016 : n = 2016 := by sorry
  -- conclude that `n` belongs to the singleton `{2016}`
  have h_mem_singleton : n ∈ ({2016} : Finset ℕ) := by sorry
  exact h_mem_singleton
```

## Snapshot 3 h_subset_mathd_numbertheory_451

2026-09-08 04:02:12,808 [log](../../../logs/screen57_20260907_021530.log:711968)

```lean
theorem h_subset_mathd_numbertheory_451 (S : Finset ℕ)
    (h₀ :
      ∀ n : ℕ,
        n ∈ S ↔
          2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n)
    (h_mem_2016 : (2016 : ℕ) ∈ S) :
    S ⊆ ({2016} : Finset ℕ) := by
  intro n hn
  have h_cond :
      (2010 ≤ n ∧ n ≤ 2019) ∧
        ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n := by sorry
  have h_bounds : 2010 ≤ n ∧ n ≤ 2019 := by sorry
  have h_exists_m : ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n := by sorry
  rcases h_exists_m with ⟨m, hm_card, hm_sum⟩
  have h_m_structure :
      ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ m = p * q := by sorry
  rcases h_m_structure with ⟨p, q, hp, hq, hpq, hm_eq⟩
  have h_sum_eq : (∑ r in Nat.divisors m, r) = (p + 1) * (q + 1) := by sorry
  have h_n_eq : n = (p + 1) * (q + 1) := by sorry
  have h_n_eq_2016 : n = 2016 := by sorry
  have h_mem_singleton : n ∈ ({2016} : Finset ℕ) := by sorry
  exact h_mem_singleton
```

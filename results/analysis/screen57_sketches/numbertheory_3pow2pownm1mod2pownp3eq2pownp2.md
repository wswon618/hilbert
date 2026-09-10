# numbertheory_3pow2pownm1mod2pownp3eq2pownp2

## Original input

```lean
theorem numbertheory_3pow2pownm1mod2pownp3eq2pownp2 (n : ℕ) (h₀ : 0 < n) :
    (3 ^ 2 ^ n - 1) % 2 ^ (n + 3) = 2 ^ (n + 2) := by

```

## Snapshot 1 numbertheory_3pow2pownm1mod2pownp3eq2pownp2

2026-09-07 06:33:03,459 [log](../../../logs/screen57_20260907_021530.log:75142)

```lean
theorem numbertheory_3pow2pownm1mod2pownp3eq2pownp2 (n : ℕ) (h₀ : 0 < n) :
    (3 ^ (2 ^ n) - 1) % (2 ^ (n + 3)) = 2 ^ (n + 2) := by
  -- 1️⃣ Establish the required congruence modulo \(2^{n+3}\)
  have hmod :
      (3 ^ (2 ^ n) - 1) ≡ 2 ^ (n + 2) [MOD 2 ^ (n + 3)] := by sorry
  -- 2️⃣ Show that the candidate remainder is strictly smaller than the modulus
  have hlt : (2 ^ (n + 2)) < (2 ^ (n + 3)) := by sorry
  -- 3️⃣ Conclude the value of the remainder using `Nat.mod_eq_of_modEq`
  exact Nat.mod_eq_of_modEq hmod hlt
```

## Snapshot 2 hmod_numbertheory_3pow2pownm1mod2pownp3eq2pownp2

2026-09-07 06:59:22,765 [log](../../../logs/screen57_20260907_021530.log:91546)

```lean
theorem hmod_numbertheory_3pow2pownm1mod2pownp3eq2pownp2 (n : ℕ) (h₀ : 0 < n) :
    (3 ^ 2 ^ n - 1) ≡ 2 ^ (n + 2) [MOD 2 ^ (n + 3)] := by
  -- 3 can be written as 1 + 2·1
  have h_three_eq : (3 : ℕ) = 1 + 2 * 1 := by sorry
  -- (1 + 2·1)^{2^n} ≡ 1 (mod 2^n)  →  3^{2^n} ≡ 1 (mod 2^n)
  have h_pow_mod_one : (3 ^ (2 ^ n)) ≡ (1 : ℕ) [MOD 2 ^ n] := by sorry
  -- From the congruence we get divisibility of the difference
  have h_dvd_diff : (2 ^ n) ∣ (3 ^ (2 ^ n) - 1) := by sorry
  -- Direct verification for the base case n = 1
  have h_base : (3 ^ 2 ^ 1 - 1) ≡ 2 ^ (1 + 2) [MOD 2 ^ (1 + 3)] := by sorry
  -- Induction lemma: the statement holds for every positive k
  have h_induction :
      ∀ k : ℕ, 0 < k →
        (3 ^ 2 ^ k - 1) ≡ 2 ^ (k + 2) [MOD 2 ^ (k + 3)] := by sorry
  -- Apply the induction lemma to the given n
  have h_target :
      (3 ^ 2 ^ n - 1) ≡ 2 ^ (n + 2) [MOD 2 ^ (n + 3)] := by sorry
  exact h_target
```

## Snapshot 3 h_induction_hmod_numbertheory_3pow2pownm1mod2pownp3eq2pownp2

2026-09-07 07:30:52,580 [log](../../../logs/screen57_20260907_021530.log:109503)

```lean
theorem h_induction_hmod_numbertheory_3pow2pownm1mod2pownp3eq2pownp2
    (h_dvd_diff :
      ∀ (n : ℕ) (h₀ : 0 < n),
        (2 ^ n) ∣ (3 ^ (2 ^ n) - 1))
    (h_base :
      (3 ^ 2 ^ 1 - 1) ≡ 2 ^ (1 + 2) [MOD 2 ^ (1 + 3)]) :
    ∀ k : ℕ, 0 < k →
      (3 ^ 2 ^ k - 1) ≡ 2 ^ (k + 2) [MOD 2 ^ (k + 3)] := by
  intro k hk
  -- write k as a successor, because k > 0
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk) with ⟨k, rfl⟩
  -- prove the statement by induction on the predecessor of k
  induction k with
  | zero =>
      -- base case : k = 1
      simpa using h_base
  | succ k ih =>
      -- induction hypothesis for the previous exponent
      have ih_mod :
          (3 ^ 2 ^ (k + 1) - 1) ≡ 2 ^ (k + 1 + 2) [MOD 2 ^ (k + 1 + 3)] := by sorry
      -- add 1 to both sides of the induction hypothesis
      have h_eq_one_add :
          3 ^ 2 ^ (k + 1) ≡ 1 + 2 ^ (k + 1 + 2) [MOD 2 ^ (k + 1 + 3)] := by sorry
      -- square the congruence
      have h_sq :
          (3 ^ 2 ^ (k + 1)) ^ 2 ≡ (1 + 2 ^ (k + 1 + 2)) ^ 2 [MOD 2 ^ (k + 1 + 3)] := by sorry
      -- strengthen the modulus from 2^(k+1+3) to 2^(k+1+4)
      have h_sq_mod :
          (3 ^ 2 ^ (k + 1)) ^ 2 ≡ (1 + 2 ^ (k + 1 + 2)) ^ 2 [MOD 2 ^ (k + 1 + 4)] := by sorry
      -- expand the square on the right‑hand side and reduce modulo 2^(k+1+4)
      have h_expand :
          (1 + 2 ^ (k + 1 + 2)) ^ 2 ≡ 1 + 2 ^ (k + 1 + 3) [MOD 2 ^ (k + 1 + 4)] := by sorry
      -- combine the two previous congruences
      have h_comb :
          3 ^ 2 ^ (k + 2) ≡ 1 + 2 ^ (k + 1 + 3) [MOD 2 ^ (k + 1 + 4)] := by sorry
      -- subtract 1 from both sides of the congruence
      have h_goal :
          3 ^ 2 ^ (k + 2) - 1 ≡ 2 ^ (k + 2 + 2) [MOD 2 ^ (k + 2 + 3)] := by sorry
      -- finish the induction step
      simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc] using h_goal
```

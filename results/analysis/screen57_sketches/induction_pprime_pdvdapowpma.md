# induction_pprime_pdvdapowpma

## Original input

```lean
theorem induction_pprime_pdvdapowpma (p a : ℕ) (h₀ : 0 < a) (h₁ : Nat.Prime p) : p ∣ a ^ p - a := by

```

## Snapshot 1 induction_pprime_pdvdapowpma

2026-09-07 15:58:41,477 [log](../../../logs/screen57_20260907_021530.log:383980)

```lean
theorem induction_pprime_pdvdapowpma (p a : ℕ) (h₀ : 0 < a) (h₁ : Nat.Prime p) :
    p ∣ a ^ p - a := by
  -- Subgoal 1: obtain the divisibility statement from the prime hypothesis
  have h_div : p ∣ a ^ p - a := by sorry
  -- Conclude the proof using the obtained statement
  exact h_div
```

## Snapshot 2 h_div_induction_pprime_pdvdapowpma

2026-09-07 16:27:54,047 [log](../../../logs/screen57_20260907_021530.log:394943)

```lean
theorem h_div_induction_pprime_pdvdapowpma (p a : ℕ) (h₀ : 0 < a) (h₁ : Nat.Prime p) :
    p ∣ a ^ p - a := by
  by_cases hpa : p ∣ a
  · -- case `p ∣ a`
    have hpow : p ∣ a ^ p := by sorry
    have hsub : p ∣ a ^ p - a := by sorry
    exact hsub
  · -- case `¬ p ∣ a`
    have hmod : a ^ p ≡ a [MOD p] := by sorry
    have hsub : p ∣ a ^ p - a := by sorry
    exact hsub
```

## Snapshot 3 hsub₂_h_div_induction_pprime_pdvdapowpma

2026-09-07 16:39:27,093 [log](../../../logs/screen57_20260907_021530.log:411106)

```lean
theorem hsub₂_h_div_induction_pprime_pdvdapowpma (p a : ℕ) (h₀ : 0 < a) (h₁ : Nat.Prime p)
    (hpa : ¬ p ∣ a) (hmod : a ^ p ≡ a [MOD p]) :
    p ∣ a ^ p - a := by
  -- From the given congruence we get a divisibility statement with the difference in the opposite order
  have hdiv₁ : p ∣ a - a ^ p := by sorry
  -- Re‑orient the difference to match the goal
  have hdiv : p ∣ a ^ p - a := by sorry
  exact hdiv
```

## Snapshot 4 hmod_h_div_induction_pprime_pdvdapowpma

2026-09-07 16:40:06,908 [log](../../../logs/screen57_20260907_021530.log:412108)

```lean
theorem hmod_h_div_induction_pprime_pdvdapowpma (p a : ℕ) (h₀ : 0 < a) (h₁ : Nat.Prime p) (hpa : ¬ p ∣ a) :
    a ^ p ≡ a [MOD p] := by
  have hcoprime : Nat.Coprime a p := by sorry
  have hpow : a ^ (p - 1) ≡ 1 [MOD p] := by sorry
  have hmul : a * a ^ (p - 1) ≡ a * 1 [MOD p] := by sorry
  have hpow_eq : a * a ^ (p - 1) = a ^ p := by sorry
  have hfinal : a ^ p ≡ a [MOD p] := by sorry
  exact hfinal
```

## Snapshot 5 hdiv_hsub₂_h_div_induction_pprime_pdvdapowpma

2026-09-07 17:02:21,146 [log](../../../logs/screen57_20260907_021530.log:425479)

```lean
theorem hdiv_hsub₂_h_div_induction_pprime_pdvdapowpma (p a : ℕ) (h₀ : 0 < a) (h₁ : Nat.Prime p) (hpa : ¬ p ∣ a)
    (hmod : a ^ p ≡ a [MOD p]) (hdiv₁ : p ∣ a - a ^ p) : p ∣ a ^ p - a := by
  -- 1️⃣  Express the two differences as negatives of each other
  have h_eq : a ^ p - a = -(a - a ^ p) := by sorry
  -- 2️⃣  Turn the given divisibility into a divisibility of the negated term
  have h_dvd_neg : p ∣ -(a - a ^ p) := by sorry
  -- 3️⃣  Rewrite using the equality from step 1 to obtain the desired divisibility
  simpa [h_eq] using h_dvd_neg
```

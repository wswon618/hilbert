## 1 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 17:13:54,368 logs/strat2_v416_20260903_065550.log:158141

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1.  The function `x ↦ 1 / √x` is antitone on `[1,10000]`.
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  -- 2.  Apply the integral comparison for antitone functions.
  have h_sum_le_int :
      (∑ i in Finset.Ico 1 10000,
          (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 3.  Rewrite the sum over `Ico` as the required sum over `Icc`.
  have h_sum_eq :
      (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) =
        ∑ i in Finset.Ico 1 10000,
          (1 : ℝ) / Real.sqrt (i + 1) := by sorry
  -- 4.  Combine the equality and the inequality to get a ≤‑bound.
  have h_le_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 5.  Compute the integral using the power‑rule formula.
  have h_int_eq :
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x = (198 : ℝ) := by sorry
  -- 6.  Strengthen the ≤‑bound to a strict <‑bound (the function is not constant).
  have h_lt_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 7.  Conclude the desired strict inequality.
  have h_final :
      (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < (198 : ℝ) := by sorry
  exact h_final
```

## 2 h_int_eq_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 18:23:21,123 logs/strat2_v416_20260903_065550.log:186472

```lean
theorem h_int_eq_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x = (198 : ℝ) := by
  have h_int_eq :
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x =
        (2 : ℝ) * Real.sqrt (10000 : ℝ) - (2 : ℝ) * Real.sqrt (1 : ℝ) := by sorry
  have h_val :
      (2 : ℝ) * Real.sqrt (10000 : ℝ) - (2 : ℝ) * Real.sqrt (1 : ℝ) = (198 : ℝ) := by sorry
  simpa [h_val] using h_int_eq
```

## 3 h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 18:28:42,259 logs/strat2_v416_20260903_065550.log:190264

```lean
theorem h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_le_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x)
    (h_int_eq :
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x = (198 : ℝ)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) <
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by
  -- 1.  The integrand is strictly decreasing on the interval [1,10000].
  have h_strict_decrease :
      StrictAntiOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  -- 2.  For each k ∈ {2,…,10000} the integral over (k‑1,k) is strictly larger than the value at k.
  have h_interval_strict (k : ℕ) (hk₂ : (2 : ℕ) ≤ k) (hk₁₀₀₀₀ : k ≤ 10000) :
      (∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt k := by sorry
  -- 3.  The integral over [1,10000] equals the sum of the integrals over the unit sub‑intervals.
  have h_integral_eq_sum :
      (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∑ k in Finset.Icc (2 : ℕ) 10000,
          ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 4.  Summing the strict inequalities yields the desired strict inequality.
  have h_sum_strict :
      (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  exact h_sum_strict
```

## 4 h_int_eq_h_int_eq_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 18:38:59,452 logs/strat2_v416_20260903_065550.log:204664

```lean
theorem h_int_eq_h_int_eq_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x =
      (2 : ℝ) * Real.sqrt (10000 : ℝ) - (2 : ℝ) * Real.sqrt (1 : ℝ) := by
  have h_le : (1 : ℝ) ≤ (10000 : ℝ) := by sorry
  have h_cont :
      ContinuousOn (fun x : ℝ => (2 : ℝ) * Real.sqrt x) (Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  have h_deriv :
      ∀ x ∈ Ioo (1 : ℝ) (10000 : ℝ),
        HasDerivAt (fun y : ℝ => (2 : ℝ) * Real.sqrt y) (1 / Real.sqrt x) x := by sorry
  have h_int :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume (1 : ℝ) (10000 : ℝ) := by sorry
  simpa using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        h_le h_cont h_deriv h_int)
```

## 5 h_interval_strict_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 19:01:44,506 logs/strat2_v416_20260903_065550.log:225093

```lean
theorem h_interval_strict_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 (k : ℕ)
    (hk₂ : (2 : ℕ) ≤ k) (hk₁₀₀₀₀ : k ≤ 10000)
    (h_strict_decrease :
        StrictAntiOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ))) :
    (∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt k := by
  -- 1. positivity of `k` as a real number
  have hk_pos : (0 : ℝ) < (k : ℝ) := by sorry
  -- 2. strict inequality `k - 1 < k`
  have h_lt : (k - 1 : ℝ) < (k : ℝ) := by sorry
  -- 3. ordering of the interval endpoints
  have h_le : (k - 1 : ℝ) ≤ (k : ℝ) := by sorry
  -- 4. continuity of the constant function on the interval
  have h_cont_f :
      ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt k) (Icc (k - 1 : ℝ) (k : ℝ)) := by sorry
  -- 5. continuity of `x ↦ 1 / √x` on the interval
  have h_cont_g :
      ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Icc (k - 1 : ℝ) (k : ℝ)) := by sorry
  -- 6. pointwise inequality `f ≤ g` on `Ioc`
  have h_le_pointwise :
      ∀ x ∈ Ioc (k - 1 : ℝ) (k : ℝ),
        (1 : ℝ) / Real.sqrt k ≤ (1 : ℝ) / Real.sqrt x := by sorry
  -- 7. existence of a point where `f < g`
  have h_exists_lt :
      ∃ c ∈ Icc (k - 1 : ℝ) (k : ℝ),
        (1 : ℝ) / Real.sqrt k < (1 : ℝ) / Real.sqrt c := by sorry
  -- 8. strict inequality of the integrals via the intervalIntegral theorem
  have h_int_lt :
      (∫ x in (k - 1 : ℝ)..(k : ℝ), (1 : ℝ) / Real.sqrt k) <
        ∫ x in (k - 1 : ℝ)..(k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 9. evaluate the integral of the constant function
  have h_int_const :
      (∫ x in (k - 1 : ℝ)..(k : ℝ), (1 : ℝ) / Real.sqrt k) = (1 : ℝ) / Real.sqrt k := by sorry
  -- 10. rewrite the strict inequality using the value of the constant integral
  have h_final :
      (1 : ℝ) / Real.sqrt k < ∫ x in (k - 1 : ℝ)..(k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 11. conclude the desired inequality
  exact h_final
```

## 6 h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 19:05:19,160 logs/strat2_v416_20260903_065550.log:230071

```lean
theorem h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) =
      ∑ k in Finset.Icc (2 : ℕ) 10000,
        ∫ x in ((k - 1 : ℕ) : ℝ)..(k : ℝ), (1 : ℝ) / Real.sqrt x := by
  -- integrability of 1/√x on any closed interval contained in (0,∞)
  have h_integrable_on_subinterval :
      ∀ a b : ℝ, 0 < a → a ≤ b →
        IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Icc a b) := by sorry
  -- additivity of the interval integral on adjacent intervals
  have h_add_adjacent :
      ∀ a b c : ℝ, a ≤ b → b ≤ c →
        (∫ x in a..c, (1 : ℝ) / Real.sqrt x) =
          (∫ x in a..b, (1 : ℝ) / Real.sqrt x) + (∫ x in b..c, (1 : ℝ) / Real.sqrt x) := by sorry
  -- base case n = 2
  have h_base :
      (∫ x in (1 : ℝ)..(2 : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∑ k in Finset.Icc (2 : ℕ) 2,
          ∫ x in ((k - 1 : ℕ) : ℝ)..(k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- inductive step
  have h_inductive :
      ∀ n : ℕ,
        2 ≤ n →
        (∫ x in (1 : ℝ)..(n : ℝ), (1 : ℝ) / Real.sqrt x) =
          ∑ k in Finset.Icc (2 : ℕ) n,
            ∫ x in ((k - 1 : ℕ) : ℝ)..(k : ℝ), (1 : ℝ) / Real.sqrt x →
        (∫ x in (1 : ℝ)..(((n + 1) : ℕ) : ℝ), (1 : ℝ) / Real.sqrt x) =
          ∑ k in Finset.Icc (2 : ℕ) (n + 1),
            ∫ x in ((k - 1 : ℕ) : ℝ)..(k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- conclusion for n = 10000 by repeated use of the base case and inductive step
  have h_result :
      (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∑ k in Finset.Icc (2 : ℕ) 10000,
          ∫ x in ((k - 1 : ℕ) : ℝ)..(k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  simpa using h_result
```

## 7 h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 19:09:57,627 logs/strat2_v416_20260903_065550.log:237138

```lean
theorem h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) =
      ∑ k in Finset.Icc (2 : ℕ) 10000,
        ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by
  -- integrability of the function on each sub‑interval [k, k+1]
  have h_int :
      ∀ k ∈ Finset.Ico (1 : ℕ) 10000,
        IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume (k : ℝ) ((k + 1) : ℝ) := by sorry
  -- sum of the integrals over the adjacent intervals equals the whole integral
  have h_sum_eq :
      (∑ k in Finset.Ico (1 : ℕ) 10000,
        ∫ x in (k : ℝ)..((k + 1) : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- re‑index the finite sum from `Ico 1 10000` to `Icc 2 10000`
  have h_reindex :
      (∑ k in Finset.Ico (1 : ℕ) 10000,
        ∫ x in (k : ℝ)..((k + 1) : ℝ), (1 : ℝ) / Real.sqrt x) =
      ∑ k in Finset.Icc (2 : ℕ) 10000,
        ∫ x in ((k - 1) : ℝ)..(k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- combine the two equalities
  calc
    (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x)
        = (∑ k in Finset.Ico (1 : ℕ) 10000,
            ∫ x in (k : ℝ)..((k + 1) : ℝ), (1 : ℝ) / Real.sqrt x) := by
          symm
          exact h_sum_eq
    _ = ∑ k in Finset.Icc (2 : ℕ) 10000,
            ∫ x in ((k - 1) : ℝ)..(k : ℝ), (1 : ℝ) / Real.sqrt x := by
          exact h_reindex
```

## 8 h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 19:13:13,465 logs/strat2_v416_20260903_065550.log:239646

```lean
theorem h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) =
      ∑ k in Finset.Icc (2 : ℕ) 10000,
        ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by
  -- 1.  Integrability of `1 / √x` on each unit interval.
  have h_int :
      ∀ k : ℕ,
        IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume (k : ℝ)
          ((k + 1 : ℕ) : ℝ) := by sorry
  -- 2.  Sum of the integrals over the adjacent unit intervals equals the whole integral.
  have h_sum_eq :
      (∑ k in Finset.Ico 1 10000,
          ∫ x in (k : ℝ)..((k + 1) : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) := by sorry
  -- 3.  Re‑index the sum from `Ico 1 10000` to `Icc 2 10000`.
  have h_reindex :
      (∑ k in Finset.Ico 1 10000,
          ∫ x in (k : ℝ)..((k + 1) : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∑ k in Finset.Icc 2 10000,
          ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) := by sorry
  -- 4.  Combine the equalities.
  calc
    (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x)
        = (∑ k in Finset.Ico 1 10000,
            ∫ x in (k : ℝ)..((k + 1) : ℝ), (1 : ℝ) / Real.sqrt x) := by
          symm
          exact h_sum_eq
    _ = ∑ k in Finset.Icc 2 10000,
            ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by
          exact h_reindex
```

## 9 h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 19:16:12,389 logs/strat2_v416_20260903_065550.log:242410

```lean
theorem h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) =
      ∑ k in Finset.Icc (2 : ℕ) 10000,
        ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by
  have h_integrable :
      ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) →
        IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume (k - 1 : ℝ) (k : ℝ) := by sorry
  have h_add_adjacent :
      ∀ a b c : ℝ,
        a ≤ b → b ≤ c →
        IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume a c →
        (∫ x in a..c, (1 : ℝ) / Real.sqrt x) =
          (∫ x in a..b, (1 : ℝ) / Real.sqrt x) + (∫ x in b..c, (1 : ℝ) / Real.sqrt x) := by sorry
  have h_base :
      (∫ x in (1 : ℝ)..(2 : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∑ k in Finset.Icc (2 : ℕ) 2,
          ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  have h_induction_step :
      ∀ n : ℕ,
        n ≥ 2 →
        (∫ x in (1 : ℝ)..(n + 1 : ℝ), (1 : ℝ) / Real.sqrt x) =
          ∑ k in Finset.Icc (2 : ℕ) (n + 1),
            ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  have h_result :
      (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∑ k in Finset.Icc (2 : ℕ) 10000,
          ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  exact h_result
```

## 10 h_cont_g_h_interval_strict_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 19:43:24,594 logs/strat2_v416_20260903_065550.log:265011

```lean
theorem h_cont_g_h_interval_strict_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 (k : ℕ)
    (hk_pos : (0 : ℝ) < (k : ℝ)) :
    ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (k - 1 : ℝ) (k : ℝ)) := by
  -- 1.  Continuity of the square‑root on the interval
  have h_cont_sqrt :
      ContinuousOn (fun x : ℝ => Real.sqrt x) (Set.Icc (k - 1 : ℝ) (k : ℝ)) := by sorry
  -- 2.  Every point of the interval is strictly positive
  have h_pos :
      ∀ x ∈ Set.Icc (k - 1 : ℝ) (k : ℝ), (0 : ℝ) < x := by sorry
  -- 3.  Hence the square‑root never vanishes on the interval
  have h_sqrt_ne_zero :
      ∀ x ∈ Set.Icc (k - 1 : ℝ) (k : ℝ), Real.sqrt x ≠ 0 := by sorry
  -- 4.  Continuity of the reciprocal of the square‑root on the interval
  have h_cont_inv :
      ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (Set.Icc (k - 1 : ℝ) (k : ℝ)) := by sorry
  -- 5.  Rewrite division by a square‑root as multiplication by the inverse
  have h_eq :
      (fun x : ℝ => (1 : ℝ) / Real.sqrt x) = fun x => (Real.sqrt x)⁻¹ := by sorry
  -- 6.  Conclude the desired continuity
  simpa [h_eq] using h_cont_inv
```

## 11 h_add_adjacent_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 19:53:45,776 logs/strat2_v416_20260903_065550.log:280199

```lean
theorem h_add_adjacent_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ∀ a b c : ℝ,
      a ≤ b → b ≤ c →
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume a c →
      (∫ x in a..c, (1 : ℝ) / Real.sqrt x) =
        (∫ x in a..b, (1 : ℝ) / Real.sqrt x) + (∫ x in b..c, (1 : ℝ) / Real.sqrt x) := by
  intro a b c hab hbc h_int
  have h_eq :
      (∫ x in a..c, (1 : ℝ) / Real.sqrt x) =
        (∫ x in a..b, (1 : ℝ) / Real.sqrt x) + (∫ x in b..c, (1 : ℝ) / Real.sqrt x) := by sorry
  exact h_eq
```

## 12 h_integrable_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 19:53:51,642 logs/strat2_v416_20260903_065550.log:280473

```lean
theorem h_integrable_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) →
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume (k - 1 : ℝ) (k : ℝ) := by
  intro k hk
  -- 1. the left endpoint does not exceed the right endpoint
  have h_le : (k - 1 : ℝ) ≤ (k : ℝ) := by sorry
  -- 2. the square‑root function is continuous on ℝ
  have h_sqrt_cont : Continuous (fun x : ℝ => Real.sqrt x) := by sorry
  -- 3. the constant function 1 is continuous
  have h_one_cont : Continuous fun _ : ℝ => (1 : ℝ) := by sorry
  -- 4. the quotient 1/√x is continuous on the closed interval [k‑1,k]
  have h_cont_on :
      ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Icc (k - 1) k) := by sorry
  -- 5. a continuous function on a compact interval is integrable there
  have h_int_on_Icc :
      IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Icc (k - 1) k) MeasureTheory.volume := by sorry
  -- 6. integrability on the half‑open interval follows from integrability on the closed one
  have h_int_on_Ioc :
      IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Ioc (k - 1) k) MeasureTheory.volume := by sorry
  -- 7. convert integrability on Ioc to interval‑integrability on [k‑1,k]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h_le).mpr h_int_on_Ioc
```

## 13 h_induction_step_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 19:55:20,554 logs/strat2_v416_20260903_065550.log:282025

```lean
theorem h_induction_step_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ∀ n : ℕ,
      n ≥ 2 →
      (∫ x in (1 : ℝ)..(n + 1 : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∑ k in Finset.Icc (2 : ℕ) (n + 1),
          ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by
  intro n hn
  -- auxiliary inequality needed for later additivity lemmas
  have h_one_le : (1 : ℝ) ≤ (n + 1 : ℝ) := by sorry
  -- main auxiliary statement proved by induction on a natural number
  have h_ind :
      ∀ m : ℕ,
        m ≥ 2 →
          (∫ x in (1 : ℝ)..(m + 1 : ℝ), (1 : ℝ) / Real.sqrt x) =
            ∑ k in Finset.Icc (2 : ℕ) (m + 1),
              ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  exact h_ind n hn
```

## 14 h_result_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 19:59:22,759 logs/strat2_v416_20260903_065550.log:284228

```lean
theorem h_result_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) =
      ∑ k in Finset.Icc (2 : ℕ) 10000,
        ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by
  -- integrability of the function on each sub‑interval
  have h_int :
      ∀ k ∈ Finset.Ico (2 : ℕ) 10001,
        IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume ((k - 1 : ℝ)) (k : ℝ) := by sorry
  -- sum of the integrals over the adjacent sub‑intervals equals the whole integral
  have h_sum_eq :
      (∑ k in Finset.Ico (2 : ℕ) 10001,
          ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- rewrite the index set `Ico 2 10001` as `Icc 2 10000`
  have h_index_eq :
      (∑ k in Finset.Ico (2 : ℕ) 10001,
          ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∑ k in Finset.Icc (2 : ℕ) 10000,
          ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- combine the equalities
  calc
    (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x)
        = (∑ k in Finset.Ico (2 : ℕ) 10001,
            ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) := by
          symm; exact h_sum_eq
    _ = ∑ k in Finset.Icc (2 : ℕ) 10000,
            ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by
          exact h_index_eq
```

## 15 h_cont_g_h_interval_strict_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 20:07:12,777 logs/strat2_v416_20260903_065550.log:287287

```lean
theorem h_cont_g_h_interval_strict_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 (k : ℕ)
    (hk_pos : (0 : ℝ) < (k : ℝ)) :
    ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Ioc (k - 1 : ℝ) (k : ℝ)) := by
  -- 1.  Continuity of the square‑root on the interval
  have h_cont_sqrt :
      ContinuousOn (fun x : ℝ => Real.sqrt x) (Set.Ioc (k - 1 : ℝ) (k : ℝ)) := by sorry
  -- 2.  Every point of the interval is strictly positive
  have h_pos :
      ∀ x ∈ Set.Ioc (k - 1 : ℝ) (k : ℝ), (0 : ℝ) < x := by sorry
  -- 3.  Hence the square‑root never vanishes on the interval
  have h_sqrt_ne_zero :
      ∀ x ∈ Set.Ioc (k - 1 : ℝ) (k : ℝ), Real.sqrt x ≠ 0 := by sorry
  -- 4.  Continuity of the reciprocal of the square‑root on the interval
  have h_cont_inv :
      ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (Set.Ioc (k - 1 : ℝ) (k : ℝ)) := by sorry
  -- 5.  Rewrite division by a square‑root as multiplication by the inverse
  have h_eq :
      (fun x : ℝ => (1 : ℝ) / Real.sqrt x) = fun x => (Real.sqrt x)⁻¹ := by sorry
  -- 6.  Conclude the desired continuity
  simpa [h_eq] using h_cont_inv
```

## 16 h_eq_h_add_adjacent_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 20:16:54,078 logs/strat2_v416_20260903_065550.log:300720

```lean
theorem h_eq_h_add_adjacent_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h_int :
        IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume a c) :
    (∫ x in a..c, (1 : ℝ) / Real.sqrt x) =
      (∫ x in a..b, (1 : ℝ) / Real.sqrt x) + (∫ x in b..c, (1 : ℝ) / Real.sqrt x) := by
  -- integrability on the left sub‑interval
  have hab_int :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume a b := by sorry
  -- integrability on the right sub‑interval
  have hbc_int :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume b c := by sorry
  -- additivity of interval integrals for adjacent intervals
  have h_add :
      (∫ x in a..b, (1 : ℝ) / Real.sqrt x) + ∫ x in b..c, (1 : ℝ) / Real.sqrt x =
        ∫ x in a..c, (1 : ℝ) / Real.sqrt x := by sorry
  -- rewrite to obtain the desired orientation
  exact h_add.symm
```

## 17 h_ind_h_induction_step_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 20:18:10,707 logs/strat2_v416_20260903_065550.log:302775

```lean
theorem h_ind_h_induction_step_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198
    (m : ℕ) (hm : m ≥ 2) :
    (∫ x in (1 : ℝ)..(m + 1 : ℝ), (1 : ℝ) / Real.sqrt x) =
      ∑ k in Finset.Icc (2 : ℕ) (m + 1),
        ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by
  -- lower bound 2 ≤ m+1, needed for the finset to be non‑empty
  have h_two_le : (2 : ℕ) ≤ m + 1 := by sorry
  -- auxiliary statement: the equality holds for every natural n
  have h_ind :
      ∀ n : ℕ,
        (∫ x in (1 : ℝ)..(n + 1 : ℝ), (1 : ℝ) / Real.sqrt x) =
          ∑ k in Finset.Icc (2 : ℕ) (n + 1),
            ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- apply the auxiliary statement to m
  exact h_ind m
```

## 18 h_integrable_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 20:18:34,940 logs/strat2_v416_20260903_065550.log:303528

```lean
theorem h_integrable_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ∀ k : ℕ, (2 : ℝ) ≤ (k : ℝ) →
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume (k - 1 : ℝ) (k : ℝ) := by
  intro k hk
  have h_le : (k - 1 : ℝ) ≤ (k : ℝ) := by sorry
  have h_sqrt_cont : Continuous (fun x : ℝ => Real.sqrt x) := by sorry
  have h_one_cont : Continuous fun _ : ℝ => (1 : ℝ) := by sorry
  have h_cont_on :
      ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (k - 1) k) := by sorry
  have h_int_on_Icc :
      MeasureTheory.IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (k - 1) k) MeasureTheory.volume := by sorry
  have h_int_on_Ioc :
      MeasureTheory.IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Ioc (k - 1) k) MeasureTheory.volume := by sorry
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h_le).mpr h_int_on_Ioc
```

## 19 h_cont_g_h_interval_strict_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 20:31:55,018 logs/strat2_v416_20260903_065550.log:316787

```lean
theorem h_cont_g_h_interval_strict_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 (k : ℕ)
    (hk_one : (1 : ℝ) < (k : ℝ)) :
    ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (k - 1 : ℝ) (k : ℝ)) := by
  have h_cont_sqrt :
      ContinuousOn (fun x : ℝ => Real.sqrt x) (Set.Icc (k - 1 : ℝ) (k : ℝ)) := by sorry
  have h_pos :
      ∀ x ∈ Set.Icc (k - 1 : ℝ) (k : ℝ), (0 : ℝ) < x := by sorry
  have h_sqrt_ne_zero :
      ∀ x ∈ Set.Icc (k - 1 : ℝ) (k : ℝ), Real.sqrt x ≠ 0 := by sorry
  have h_cont_inv :
      ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (Set.Icc (k - 1 : ℝ) (k : ℝ)) := by sorry
  have h_eq :
      (fun x : ℝ => (1 : ℝ) / Real.sqrt x) = fun x => (Real.sqrt x)⁻¹ := by sorry
  simpa [h_eq] using h_cont_inv
```

## 20 h_sum_eq_h_result_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 20:37:38,245 logs/strat2_v416_20260903_065550.log:322919

```lean
theorem h_sum_eq_h_result_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_int :
        ∀ k ∈ Finset.Ico (2 : ℕ) 10001,
          IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume
            ((k - 1 : ℝ)) (k : ℝ)) :
    (∑ k in Finset.Ico (2 : ℕ) 10001,
        ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) =
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by
  -- 1. Define the integrand once and for all.
  set f : ℝ → ℝ := fun x => (1 : ℝ) / Real.sqrt x with hf
  -- 2. Re‑state the hypothesis in terms of `f`.
  have h_int' :
      ∀ k ∈ Finset.Ico (2 : ℕ) 10001,
        IntervalIntegrable f MeasureTheory.volume ((k - 1 : ℝ)) (k : ℝ) := by sorry
  -- 3. Additivity of the interval integral on adjacent intervals.
  have h_add_adjacent :
      ∀ {a b c : ℝ},
        a ≤ b → b ≤ c →
        IntervalIntegrable f MeasureTheory.volume a b →
        IntervalIntegrable f MeasureTheory.volume b c →
        (∫ x in a..c, f x) = (∫ x in a..b, f x) + (∫ x in b..c, f x) := by sorry
  -- 4. Inductive claim: the sum of the integrals over the unit intervals equals the integral over the whole interval.
  have h_sum_eq :
      ∀ n : ℕ,
        (∑ k in Finset.Ico 2 (n + 2),
            ∫ x in ((k - 1 : ℝ))..(k : ℝ), f x) =
        ∫ x in (1 : ℝ)..((n + 1 : ℝ)), f x := by sorry
  -- 5. Apply the claim for `n = 9999` (so that `n+2 = 10001`).
  have h_result :
      (∑ k in Finset.Ico (2 : ℕ) 10001,
          ∫ x in ((k - 1 : ℝ))..(k : ℝ), f x) =
        ∫ x in (1 : ℝ)..(10000 : ℝ), f x := by sorry
  -- 6. Rewrite back to the original integrand.
  simpa [f] using h_result
```

## 21 h_int_h_result_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 20:39:37,256 logs/strat2_v416_20260903_065550.log:326137

```lean
theorem h_int_h_result_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ∀ k ∈ Finset.Ico (2 : ℕ) 10001,
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume
        ((k - 1 : ℝ)) (k : ℝ) := by
  intro k hk
  -- 1️⃣  Show that the left endpoint does not exceed the right endpoint.
  have h_le : (k - 1 : ℝ) ≤ (k : ℝ) := by sorry
  -- 2️⃣  Apply the general integrability result for powers with exponent `-(1/2)`.
  have h_rpow_int :
      IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2))) MeasureTheory.volume
        ((k - 1 : ℝ)) (k : ℝ) := by sorry
  -- 3️⃣  Identify the two functions pointwise.
  have h_fun_eq :
      (fun x : ℝ => (1 : ℝ) / Real.sqrt x) = fun x : ℝ => x ^ (-(1 / 2)) := by sorry
  -- 4️⃣  Conclude by rewriting the integrand using the equality from the previous step.
  simpa [h_fun_eq] using h_rpow_int
```

## 22 h_eq_h_add_adjacent_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 20:40:35,557 logs/strat2_v416_20260903_065550.log:329429

```lean
theorem h_eq_h_add_adjacent_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h_int :
        IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume a c) :
    (∫ x in a..c, (1 : ℝ) / Real.sqrt x) =
      (∫ x in a..b, (1 : ℝ) / Real.sqrt x) + (∫ x in b..c, (1 : ℝ) / Real.sqrt x) := by
  -- integrability on the left sub‑interval
  have hab_int :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume a b := by sorry
  -- integrability on the right sub‑interval
  have hbc_int :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume b c := by sorry
  -- additivity of interval integrals for adjacent intervals
  have h_add :
      (∫ x in a..b, (1 : ℝ) / Real.sqrt x) + ∫ x in b..c, (1 : ℝ) / Real.sqrt x =
        ∫ x in a..c, (1 : ℝ) / Real.sqrt x := by sorry
  -- rewrite to obtain the desired orientation
  exact h_add.symm
```

## 23 h_int_h_result_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 20:45:55,272 logs/strat2_v416_20260903_065550.log:335774

```lean
theorem h_int_h_result_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ∀ k ∈ Finset.Ico (2 : ℕ) 10001,
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume
        ((k - 1 : ℝ)) (k : ℝ) := by
  intro k hk
  have hk_bounds : (2 : ℕ) ≤ k ∧ k < 10001 := by sorry
  have hle : ((k - 1 : ℝ) ≤ (k : ℝ)) := by sorry
  have h_int_rpow :
      IntervalIntegrable (fun x : ℝ => x ^ (-( (1 : ℝ) / 2))) MeasureTheory.volume
        ((k - 1 : ℝ)) (k : ℝ) := by sorry
  have h_eq :
      (fun x : ℝ => (1 : ℝ) / Real.sqrt x) = fun x => x ^ (-( (1 : ℝ) / 2)) := by sorry
  simpa [h_eq] using h_int_rpow
```

## 24 h_int_h_result_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 20:55:04,429 logs/strat2_v416_20260903_065550.log:350299

```lean
theorem h_int_h_result_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ∀ k ∈ Finset.Ico (2 : ℕ) 10001,
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume
        ((k - 1 : ℝ)) (k : ℝ) := by
  intro k hk
  have hk_bounds : (2 : ℕ) ≤ k ∧ k < 10001 := by sorry
  have hk_ge_two : (2 : ℕ) ≤ k := by sorry
  have h_one_le_k_sub_one : (1 : ℝ) ≤ (k - 1 : ℝ) := by sorry
  have h_le : ((k - 1 : ℝ)) ≤ (k : ℝ) := by sorry
  have h_cont_sqrt : ContinuousOn Real.sqrt (Icc ((k - 1 : ℝ)) (k : ℝ)) := by sorry
  have h_cont : ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Icc ((k - 1 : ℝ)) (k : ℝ)) := by sorry
  have h_int :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume
        ((k - 1 : ℝ)) (k : ℝ) := by sorry
  exact h_int
```

## 25 h_ind_h_induction_step_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 20:57:24,573 logs/strat2_v416_20260903_065550.log:353268

```lean
theorem h_ind_h_induction_step_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198
    (m : ℕ) (hm : m ≥ 2) :
    (∫ x in (1 : ℝ)..(m + 1 : ℝ), (1 : ℝ) / Real.sqrt x) =
      ∑ k in Finset.Icc (2 : ℕ) (m + 1),
        ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by
  -- the integrand (trivial equality)
  have h_fun :
      (fun x : ℝ => (1 : ℝ) / Real.sqrt x) = fun x => (1 : ℝ) / Real.sqrt x := by sorry
  -- integrability on each half‑open interval
  have h_int (k : ℕ) (hk : k ∈ Finset.Icc 2 (m + 1)) :
      IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Ioc ((k - 1 : ℝ)) (k : ℝ)) volume := by sorry
  -- pairwise almost‑disjointness of the intervals
  have h_ae_disjoint (k l : ℕ) (hk : k ∈ Finset.Icc 2 (m + 1))
      (hl : l ∈ Finset.Icc 2 (m + 1)) (hkl : k ≠ l) :
      AEDisjoint volume (Ioc ((k - 1 : ℝ)) (k : ℝ)) (Ioc ((l - 1 : ℝ)) (l : ℝ)) := by sorry
  -- null‑measurability of each interval
  have h_null (k : ℕ) (hk : k ∈ Finset.Icc 2 (m + 1)) :
      NullMeasurableSet (Ioc ((k - 1 : ℝ)) (k : ℝ)) volume := by sorry
  -- the union of the half‑open intervals equals `Ioc 1 (m+1)`
  have h_union_eq :
      (⋃ k ∈ Finset.Icc 2 (m + 1), (Ioc ((k - 1 : ℝ)) (k : ℝ))) = Ioc (1 : ℝ) (m + 1 : ℝ) := by sorry
  -- additivity of the integral over the finite union
  have h_integral_sum :
      ∫ x in Ioc (1 : ℝ) (m + 1 : ℝ), (1 : ℝ) / Real.sqrt x ∂volume =
        ∑ k in Finset.Icc 2 (m + 1),
          ∫ x in Ioc ((k - 1 : ℝ)) (k : ℝ), (1 : ℝ) / Real.sqrt x ∂volume := by sorry
  -- rewrite the left‑hand side interval integral as a set integral
  have h_interval_eq :
      (∫ x in (1 : ℝ)..(m + 1 : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∫ x in Ioc (1 : ℝ) (m + 1 : ℝ), (1 : ℝ) / Real.sqrt x ∂volume := by sorry
  -- rewrite each term of the sum as an interval integral
  have h_term_eq (k : ℕ) (hk : k ∈ Finset.Icc 2 (m + 1)) :
      (∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∫ x in Ioc ((k - 1 : ℝ)) (k : ℝ), (1 : ℝ) / Real.sqrt x ∂volume := by sorry
  -- replace the integrals over `Ioc` by interval integrals inside the sum
  have h_sum_eq :
      (∑ k in Finset.Icc 2 (m + 1),
          ∫ x in Ioc ((k - 1 : ℝ)) (k : ℝ), (1 : ℝ) / Real.sqrt x ∂volume) =
        ∑ k in Finset.Icc 2 (m + 1),
          (∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) := by sorry
  -- final calculation
  calc
    (∫ x in (1 : ℝ)..(m + 1 : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∫ x in Ioc (1 : ℝ) (m + 1 : ℝ), (1 : ℝ) / Real.sqrt x ∂volume := by
          rw [h_interval_eq]
    _ = ∑ k in Finset.Icc 2 (m + 1),
          ∫ x in Ioc ((k - 1 : ℝ)) (k : ℝ), (1 : ℝ) / Real.sqrt x ∂volume := by
          rw [h_integral_sum]
    _ = ∑ k in Finset.Icc 2 (m + 1),
          (∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) := by
          rw [h_sum_eq]
```

## 26 h_cont_g_h_interval_strict_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 20:58:23,988 logs/strat2_v416_20260903_065550.log:354645

```lean
theorem h_cont_g_h_interval_strict_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 (k : ℕ)
    (hk_one : (1 : ℝ) < (k : ℝ)) :
    ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (k - 1 : ℝ) (k : ℝ)) := by
  have h_cont_sqrt :
      ContinuousOn (fun x : ℝ => Real.sqrt x) (Set.Icc (k - 1 : ℝ) (k : ℝ)) := by sorry
  have h_pos :
      ∀ x ∈ Set.Icc (k - 1 : ℝ) (k : ℝ), (0 : ℝ) < x := by sorry
  have h_sqrt_ne_zero :
      ∀ x ∈ Set.Icc (k - 1 : ℝ) (k : ℝ), Real.sqrt x ≠ 0 := by sorry
  have h_cont_inv :
      ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (Set.Icc (k - 1 : ℝ) (k : ℝ)) := by sorry
  have h_eq :
      (fun x : ℝ => (1 : ℝ) / Real.sqrt x) = fun x => (Real.sqrt x)⁻¹ := by sorry
  simpa [h_eq] using h_cont_inv
```

## 27 h_int_h_integrable_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 21:04:40,675 logs/strat2_v416_20260903_065550.log:362205

```lean
theorem h_int_h_integrable_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 {k : ℕ}
    (hk : (1 : ℝ) ≤ (k : ℝ)) :
    MeasureTheory.IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x)
      (Set.Ioc (k - 1 : ℝ) (k : ℝ)) MeasureTheory.volume := by
  -- 0 < k, needed for the power‑function integrability lemma
  have hk_pos : (0 : ℝ) < (k : ℝ) := by sorry
  -- the exponent -1/2 satisfies -1 < -1/2
  have h_exp : (-1 : ℝ) < -( (1 : ℝ) / 2 ) := by sorry
  -- integrability of the power function x ↦ x ^ (-1/2) on (0,k)
  have h_int_pow_0k :
      MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-( (1 : ℝ) / 2 )))
        (Set.Ioo (0 : ℝ) (k : ℝ)) MeasureTheory.volume := by sorry
  -- the interval (k‑1,k) is contained in (0,k) because k ≥ 1
  have h_subset : Set.Ioo (k - 1 : ℝ) (k : ℝ) ⊆ Set.Ioo (0 : ℝ) (k : ℝ) := by sorry
  -- monotonicity of integrability gives integrability on (k‑1,k)
  have h_int_pow_k1k :
      MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-( (1 : ℝ) / 2 )))
        (Set.Ioo (k - 1 : ℝ) (k : ℝ)) MeasureTheory.volume := by sorry
  -- rewrite the function 1/√x as x ^ (-1/2) on the open interval
  have h_int_open :
      MeasureTheory.IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x)
        (Set.Ioo (k - 1 : ℝ) (k : ℝ)) MeasureTheory.volume := by sorry
  -- transfer integrability from the open interval to the half‑open interval
  have h_int_half_open :
      MeasureTheory.IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x)
        (Set.Ioc (k - 1 : ℝ) (k : ℝ)) MeasureTheory.volume := by sorry
  exact h_int_half_open
```

## 28 h_sum_eq_h_result_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 21:09:58,649 logs/strat2_v416_20260903_065550.log:364413

```lean
theorem h_sum_eq_h_result_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_int :
        ∀ k ∈ Finset.Ico (2 : ℕ) 10001,
          IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume
            ((k - 1 : ℝ)) (k : ℝ)) :
    (∑ k in Finset.Ico (2 : ℕ) 10001,
        ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) =
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by
  -- 1. Define the integrand once and for all.
  set f : ℝ → ℝ := fun x => (1 : ℝ) / Real.sqrt x with hf
  -- 2. Re‑state the hypothesis in terms of `f`.
  have h_int' :
      ∀ k ∈ Finset.Ico (2 : ℕ) 10001,
        IntervalIntegrable f MeasureTheory.volume ((k - 1 : ℝ)) (k : ℝ) := by sorry
  -- 3. Additivity of the interval integral on adjacent intervals.
  have h_add_adjacent :
      ∀ {a b c : ℝ},
        a ≤ b → b ≤ c →
        IntervalIntegrable f MeasureTheory.volume a b →
        IntervalIntegrable f MeasureTheory.volume b c →
        (∫ x in a..c, f x) = (∫ x in a..b, f x) + (∫ x in b..c, f x) := by sorry
  -- 4. Inductive claim: the sum of the integrals over the unit intervals equals the integral over the whole interval.
  have h_sum_eq :
      ∀ n : ℕ,
        (∑ k in Finset.Ico 2 (n + 2),
            ∫ x in ((k - 1 : ℝ))..(k : ℝ), f x) =
          ∫ x in (1 : ℝ)..((n + 1 : ℝ)), f x := by sorry
  -- 5. Apply the claim for `n = 9999` (so that `n+2 = 10001`).
  have h_result :
      (∑ k in Finset.Ico (2 : ℕ) 10001,
          ∫ x in ((k - 1 : ℝ))..(k : ℝ), f x) =
        ∫ x in (1 : ℝ)..(10000 : ℝ), f x := by sorry
  -- 6. Rewrite back to the original integrand.
  simpa [f] using h_result
```

## 29 h_sum_eq_h_result_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 21:11:52,294 logs/strat2_v416_20260903_065550.log:367085

```lean
theorem h_sum_eq_h_result_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_int :
        ∀ k ∈ Finset.Ico (2 : ℕ) 10001,
          IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume
            ((k - 1 : ℝ)) (k : ℝ)) :
    (∑ k in Finset.Ico (2 : ℕ) 10001,
        ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) =
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by
  -- integrability of the function on each unit interval
  have h_integrable (k : ℕ) (hk : k ∈ Finset.Ico (2 : ℕ) 10001) :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume
        ((k - 1 : ℝ)) (k : ℝ) := by sorry
  -- additivity of the interval integral on two adjacent intervals
  have h_add_adjacent (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
      (∫ x in a..b, (1 : ℝ) / Real.sqrt x) + ∫ x in b..c, (1 : ℝ) / Real.sqrt x =
        ∫ x in a..c, (1 : ℝ) / Real.sqrt x := by sorry
  -- base case: the sum over the single interval [1,2]
  have h_base :
      (∑ k in Finset.Ico (2 : ℕ) 3,
          ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∫ x in (1 : ℝ)..(2 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- inductive step: extending the sum by one more interval
  have h_induction (m : ℕ) (hm : m ≥ 1) :
      (∑ k in Finset.Ico (2 : ℕ) (m + 2),
          ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∫ x in (1 : ℝ)..((m + 1 : ℝ)), (1 : ℝ) / Real.sqrt x := by sorry
  -- apply the induction result with m = 9999 to obtain the desired equality
  have h_result :
      (∑ k in Finset.Ico (2 : ℕ) 10001,
          ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  exact h_result
```

## 30 h_eq_h_add_adjacent_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 21:15:10,482 logs/strat2_v416_20260903_065550.log:368532

```lean
theorem h_eq_h_add_adjacent_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h_int :
        IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume a c) :
    (∫ x in a..c, (1 : ℝ) / Real.sqrt x) =
      (∫ x in a..b, (1 : ℝ) / Real.sqrt x) + (∫ x in b..c, (1 : ℝ) / Real.sqrt x) := by
  -- integrability on the left sub‑interval
  have hab_int :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume a b := by sorry
  -- integrability on the right sub‑interval
  have hbc_int :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume b c := by sorry
  -- additivity of interval integrals for adjacent intervals
  have h_add :
      (∫ x in a..b, (1 : ℝ) / Real.sqrt x) + ∫ x in b..c, (1 : ℝ) / Real.sqrt x =
        ∫ x in a..c, (1 : ℝ) / Real.sqrt x := by sorry
  -- rewrite to obtain the desired orientation
  exact h_add.symm
```

## 31 h_cont_g_h_interval_strict_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 21:24:34,849 logs/strat2_v416_20260903_065550.log:375910

```lean
theorem h_cont_g_h_interval_strict_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198 (k : ℕ)
    (hk_one : (1 : ℝ) < (k : ℝ)) :
    ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (k - 1 : ℝ) (k : ℝ)) := by
  have h_cont_sqrt :
      ContinuousOn (fun x : ℝ => Real.sqrt x) (Set.Icc (k - 1 : ℝ) (k : ℝ)) := by sorry
  have h_pos :
      ∀ x ∈ Set.Icc (k - 1 : ℝ) (k : ℝ), (0 : ℝ) < x := by sorry
  have h_sqrt_ne_zero :
      ∀ x ∈ Set.Icc (k - 1 : ℝ) (k : ℝ), Real.sqrt x ≠ 0 := by sorry
  have h_cont_inv :
      ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (Set.Icc (k - 1 : ℝ) (k : ℝ)) := by sorry
  have h_eq :
      (fun x : ℝ => (1 : ℝ) / Real.sqrt x) = fun x => (Real.sqrt x)⁻¹ := by sorry
  simpa [h_eq] using h_cont_inv
```

## 32 h_cont_g_h_interval_strict_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 21:29:50,873 logs/strat2_v416_20260903_065550.log:378395

```lean
theorem h_cont_g_h_interval_strict_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198
  (k : ℕ) (hk_pos : (1 : ℝ) < (k : ℝ)) :
  ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc ((k : ℝ) - 1) (k : ℝ)) := by
  have h_cont_sqrt :
      ContinuousOn (fun x : ℝ => Real.sqrt x) (Set.Icc ((k : ℝ) - 1) (k : ℝ)) := by sorry
  have h_pos :
      ∀ x ∈ Set.Icc ((k : ℝ) - 1) (k : ℝ), (0 : ℝ) < x := by sorry
  have h_sqrt_ne_zero :
      ∀ x ∈ Set.Icc ((k : ℝ) - 1) (k : ℝ), Real.sqrt x ≠ 0 := by sorry
  have h_cont_inv :
      ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (Set.Icc ((k : ℝ) - 1) (k : ℝ)) := by sorry
  have h_eq :
      (fun x : ℝ => (1 : ℝ) / Real.sqrt x) = fun x => (Real.sqrt x)⁻¹ := by sorry
  simpa [h_eq] using h_cont_inv
```

## 33 h_ind_h_induction_step_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 21:35:10,066 logs/strat2_v416_20260903_065550.log:382029

```lean
theorem h_ind_h_induction_step_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198
    (m : ℕ) (hm : m ≥ 2) :
    (∫ x in (1 : ℝ)..(m + 1 : ℝ), (1 : ℝ) / Real.sqrt x) =
      ∑ k in Finset.Icc (2 : ℕ) (m + 1),
        ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by
  -- the integrand (trivial equality)
  have h_fun :
      (fun x : ℝ => (1 : ℝ) / Real.sqrt x) = fun x => (1 : ℝ) / Real.sqrt x := by sorry
  -- integrability on each half‑open interval
  have h_int (k : ℕ) (hk : k ∈ Finset.Icc 2 (m + 1)) :
      MeasureTheory.IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x)
        (Set.Ioc ((k - 1 : ℝ)) (k : ℝ)) MeasureTheory.volume := by sorry
  -- pairwise almost‑disjointness of the intervals
  have h_ae_disjoint (k l : ℕ) (hk : k ∈ Finset.Icc 2 (m + 1))
      (hl : l ∈ Finset.Icc 2 (m + 1)) (hkl : k ≠ l) :
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (Set.Ioc ((k - 1 : ℝ)) (k : ℝ)) (Set.Ioc ((l - 1 : ℝ)) (l : ℝ)) := by sorry
  -- measurability of each interval
  have h_meas (k : ℕ) (hk : k ∈ Finset.Icc 2 (m + 1)) :
      MeasurableSet (Set.Ioc ((k - 1 : ℝ)) (k : ℝ)) := by sorry
  -- the union of the half‑open intervals equals `Ioc 1 (m+1)`
  have h_union_eq :
      (⋃ k ∈ Finset.Icc 2 (m + 1), (Set.Ioc ((k - 1 : ℝ)) (k : ℝ))) =
        Set.Ioc (1 : ℝ) (m + 1 : ℝ) := by sorry
  -- additivity of the integral over the finite union
  have h_integral_sum :
      ∫ x in Set.Ioc (1 : ℝ) (m + 1 : ℝ), (1 : ℝ) / Real.sqrt x ∂(MeasureTheory.volume) =
        ∑ k in Finset.Icc 2 (m + 1),
          ∫ x in Set.Ioc ((k - 1 : ℝ)) (k : ℝ), (1 : ℝ) / Real.sqrt x ∂(MeasureTheory.volume) := by sorry
  -- rewrite the left‑hand side interval integral as a set integral
  have h_interval_eq :
      (∫ x in (1 : ℝ)..(m + 1 : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∫ x in Set.Ioc (1 : ℝ) (m + 1 : ℝ), (1 : ℝ) / Real.sqrt x ∂(MeasureTheory.volume) := by sorry
  -- rewrite each term of the sum as an interval integral
  have h_term_eq (k : ℕ) (hk : k ∈ Finset.Icc 2 (m + 1)) :
      (∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∫ x in Set.Ioc ((k - 1 : ℝ)) (k : ℝ), (1 : ℝ) / Real.sqrt x ∂(MeasureTheory.volume) := by sorry
  -- replace the integrals over `Ioc` by interval integrals inside the sum
  have h_sum_eq :
      (∑ k in Finset.Icc 2 (m + 1),
          ∫ x in Set.Ioc ((k - 1 : ℝ)) (k : ℝ), (1 : ℝ) / Real.sqrt x ∂(MeasureTheory.volume)) =
        ∑ k in Finset.Icc 2 (m + 1),
          (∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) := by sorry
  -- final calculation
  calc
    (∫ x in (1 : ℝ)..(m + 1 : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∫ x in Set.Ioc (1 : ℝ) (m + 1 : ℝ), (1 : ℝ) / Real.sqrt x ∂(MeasureTheory.volume) := by
          rw [h_interval_eq]
    _ = ∑ k in Finset.Icc 2 (m + 1),
          ∫ x in Set.Ioc ((k - 1 : ℝ)) (k : ℝ), (1 : ℝ) / Real.sqrt x ∂(MeasureTheory.volume) := by
          rw [h_integral_sum]
    _ = ∑ k in Finset.Icc 2 (m + 1),
          (∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) := by
          rw [h_sum_eq]
```

## 34 h_eq_h_add_adjacent_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 21:37:22,159 logs/strat2_v416_20260903_065550.log:386056

```lean
theorem h_eq_h_add_adjacent_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h_int :
        IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume a c) :
    (∫ x in a..c, (1 : ℝ) / Real.sqrt x) =
      (∫ x in a..b, (1 : ℝ) / Real.sqrt x) + (∫ x in b..c, (1 : ℝ) / Real.sqrt x) := by
  have hab_int :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume a b := by sorry
  have hbc_int :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume b c := by sorry
  have h_add :
      (∫ x in a..c, (1 : ℝ) / Real.sqrt x) =
        (∫ x in a..b, (1 : ℝ) / Real.sqrt x) + ∫ x in b..c, (1 : ℝ) / Real.sqrt x := by sorry
  exact h_add
```

## 35 h_ind_h_induction_step_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 21:37:44,578 logs/strat2_v416_20260903_065550.log:386361

```lean
theorem h_ind_h_induction_step_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198
    (m : ℕ) (hm : m ≥ 2) :
    (∫ x in (1 : ℝ)..(m + 1 : ℝ), (1 : ℝ) / Real.sqrt x) =
      ∑ k in Finset.Icc (2 : ℕ) (m + 1),
        ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by
  -- continuity of the integrand on the whole interval
  have h_cont :
      ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x)
        (Set.Icc (1 : ℝ) (m + 1 : ℝ)) := by sorry
  -- integrability on the whole interval
  have h_int :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume 1 (m + 1) := by sorry
  -- integrability on each unit sub‑interval
  have h_int_sub :
      ∀ k : ℕ,
        k ∈ Finset.Icc 2 (m + 1) →
        IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume ((k - 1 : ℝ)) k := by sorry
  -- base case (singleton sum)
  have h_base :
      (∫ x in (1 : ℝ)..(2 : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∑ k in Finset.Icc (2 : ℕ) 2,
          ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- induction step expressed with additivity of adjacent intervals
  have h_ind_step :
      (∫ x in (1 : ℝ)..(m + 1 : ℝ), (1 : ℝ) / Real.sqrt x) =
        (∑ k in Finset.Icc (2 : ℕ) m,
          ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) +
        ∫ x in ((m : ℝ))..(m + 1 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- rewriting the right‑hand sum to expose the last term
  have h_sum_split :
      (∑ k in Finset.Icc (2 : ℕ) (m + 1),
        ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) =
        (∑ k in Finset.Icc (2 : ℕ) m,
          ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) +
        ∫ x in ((m : ℝ))..(m + 1 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- combine the previous two equalities to obtain the desired statement
  have h_goal :
      (∫ x in (1 : ℝ)..(m + 1 : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∑ k in Finset.Icc (2 : ℕ) (m + 1),
          ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  exact h_goal
```

## 36 h_sum_eq_h_result_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 21:59:38,757 logs/strat2_v416_20260903_065550.log:423956

```lean
theorem h_sum_eq_h_result_h_integral_eq_sum_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_int :
        ∀ k ∈ Finset.Ico (2 : ℕ) 10001,
          IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume
            ((k - 1 : ℝ)) (k : ℝ)) :
    (∑ k in Finset.Ico (2 : ℕ) 10001,
        ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x) =
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by
  -- integrability on each unit interval, supplied by the hypothesis
  have h_integrable :
      ∀ k ∈ Finset.Ico (2 : ℕ) 10001,
        IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume
          ((k - 1 : ℝ)) (k : ℝ) := by sorry
  -- additivity of the interval integral on adjacent intervals
  have h_add_adjacent :
      ∀ a b c : ℝ,
        a ≤ b → b ≤ c →
        IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume a c →
        (∫ x in a..c, (1 : ℝ) / Real.sqrt x) =
          (∫ x in a..b, (1 : ℝ) / Real.sqrt x) + (∫ x in b..c, (1 : ℝ) / Real.sqrt x) := by sorry
  -- auxiliary statement: the integral from 1 to n equals the sum of the unit‑interval integrals
  have h_sum_eq :
      ∀ n : ℕ,
        1 ≤ n → n ≤ 10000 →
        (∫ x in (1 : ℝ)..(n : ℝ), (1 : ℝ) / Real.sqrt x) =
          ∑ k in Finset.Ico (2 : ℕ) (n + 1),
            ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- apply the auxiliary statement to `n = 10000`
  have h_target := by sorry
  -- rewrite `10000 + 1` as `10001` and finish
  simpa [Nat.add_comm, Nat.add_one] using h_target
```

## 37 h_cont_g_h_interval_strict_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-03 22:01:05,368 logs/strat2_v416_20260903_065550.log:426713

```lean
theorem h_cont_g_h_interval_strict_h_lt_int_algebra_sum1onsqrt2to1onsqrt10000lt198
  (k : ℕ) (hk_one_lt : (1 : ℝ) < (k : ℝ)) :
  ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (k - 1 : ℝ) (k : ℝ)) := by
  have h_cont_sqrt :
      ContinuousOn (fun x : ℝ => Real.sqrt x) (Set.Icc (k - 1 : ℝ) (k : ℝ)) := by sorry
  have h_pos :
      ∀ x ∈ Set.Icc (k - 1 : ℝ) (k : ℝ), (0 : ℝ) < x := by sorry
  have h_sqrt_ne_zero :
      ∀ x ∈ Set.Icc (k - 1 : ℝ) (k : ℝ), Real.sqrt x ≠ 0 := by sorry
  have h_cont_inv :
      ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (Set.Icc (k - 1 : ℝ) (k : ℝ)) := by sorry
  have h_eq :
      (fun x : ℝ => (1 : ℝ) / Real.sqrt x) = fun x => (Real.sqrt x)⁻¹ := by sorry
  simpa [h_eq] using h_cont_inv
```
## 1 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-08-21 09:44:36,858 outputs/2026-08-21/07-12-20/run.log:94595

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1. Bound the finite sum by the corresponding integral
  have h_le :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) := by sorry
  -- 2. Show the sum is not equal to the integral (so the inequality is strict)
  have h_ne :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≠
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) := by sorry
  -- 3. Obtain a strict inequality between sum and integral
  have h_lt_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) := by sorry
  -- 4. Evaluate the integral explicitly
  have h_int_val :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by sorry
  -- 5. Conclude the desired strict inequality
  have : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by sorry
  exact this
```

## 2 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-08-21 09:46:56,530 outputs/2026-08-21/07-12-20/run.log:97068

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1. 1/√x is antitone on [1,10000]
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000) := by sorry
  -- 2. The integral of 1/√x from 1 to 10000 equals 198
  have h_integral_val :
      (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by sorry
  -- 3. The sum is bounded above by the integral
  have h_sum_le_integral :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 4. The inequality is strict (the sum is not equal to the integral)
  have h_sum_ne_integral :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≠
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 5. Hence the sum is strictly less than the integral
  have h_sum_lt_integral :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 6. Replace the integral by its value 198
  have h_sum_lt_198 :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by sorry
  exact h_sum_lt_198
```

## 3 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-08-21 09:49:17,921 outputs/2026-08-21/07-12-20/run.log:99574

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  /- 1.  The function `x ↦ 1 / sqrt x` is antitone on `[1,10000]`. -/
  have h_antitone :
      AntitoneOn (fun x : ℝ => 1 / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  /- 2.  For every integer `i ∈ Ico 1 10001` and every real `x ∈ Ico i (i+1)`,
      the term `1 / sqrt i` is bounded above by `1 / sqrt x`. -/
  have h_pointwise :
      ∀ i ∈ Finset.Ico (1 : ℕ) 10001,
        ∀ x ∈ Ico (i : ℝ) ((i : ℝ) + 1),
          (1 / Real.sqrt (i : ℝ)) ≤ 1 / Real.sqrt x := by sorry
  /- 3.  The function is integrable on the interval `[1,10000]`. -/
  have h_integrable :
      IntegrableOn (fun x : ℝ => 1 / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  /- 4.  Apply the sum‑integral comparison lemma to obtain
      `∑_{i=1}^{10000} 1/√i ≤ ∫_{1}^{10000} 1/√x`. -/
  have h_sum_le_int :
      (∑ i in Finset.Ico (1 : ℕ) 10001, (1 / Real.sqrt (i : ℝ))) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  /- 5.  The inequality is strict because the function is *strictly* decreasing,
      hence each integral over `[i-1,i]` is strictly larger than the constant term. -/
  have h_sum_lt_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  /- 6.  Compute the integral explicitly: `∫₁^{10000} 1/√x = 198`. -/
  have h_int_val :
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) = 198 := by sorry
  /- 7.  Combine the strict inequality with the value of the integral. -/
  have : (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by sorry
  exact this
```

## 4 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-08-21 09:52:29,996 outputs/2026-08-21/07-12-20/run.log:102200

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  have hab : (2 : ℝ) ≤ 10000 := by sorry
  have hf : AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) (10000 : ℝ)) := by sorry
  have hsum_le_int :
      (∑ k in Finset.Ico 2 10000, (1 : ℝ) / Real.sqrt (k + 1)) ≤
        ∫ x in (2 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  have hsum_eq :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
        (1 : ℝ) / Real.sqrt (2 : ℝ) + ∑ k in Finset.Ico 2 10000, (1 : ℝ) / Real.sqrt (k + 1) := by sorry
  have integral_val :
      (∫ x in (2 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) = 200 - 2 * Real.sqrt (2 : ℝ) := by sorry
  have bound :
      (1 : ℝ) / Real.sqrt (2 : ℝ) + (200 - 2 * Real.sqrt (2 : ℝ)) < (198 : ℝ) := by sorry
  have : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by sorry
  exact this
```

## 5 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-08-21 09:55:12,564 outputs/2026-08-21/07-12-20/run.log:103998

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1. The function `x ↦ 1 / √x` is integrable on `[1,10000]`.
  have h_integrable :
      IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000) := by sorry
  -- 2. For each integer `i` with `1 ≤ i < 10001` and each real `x ∈ [i,i+1)`,
  --    we have `1 / √i ≤ 1 / √x`.
  have h_pointwise_le :
      ∀ i ∈ Finset.Ico 1 10001,
        ∀ x ∈ Set.Ico (i : ℝ) (i + 1 : ℝ),
          (1 : ℝ) / Real.sqrt i ≤ (1 : ℝ) / Real.sqrt x := by sorry
  -- 3. Using the previous two facts, the sum over `k = 2,…,10000` is bounded
  --    above by the integral from `1` to `10000`.
  have h_sum_le_integral :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 4. The inequality is strict because the function is strictly decreasing,
  --    hence each term is strictly smaller than the corresponding integral piece.
  have h_sum_lt_integral :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 5. Evaluate the integral `∫₁¹⁰⁰⁰⁰ 1/√x dx = 2·√10000 - 2 = 198`.
  have h_integral_val :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = 198 := by sorry
  -- 6. Combine the strict inequality with the evaluated integral.
  have : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < 198 := by sorry
  exact this
```

## 6 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-08-21 09:57:44,939 outputs/2026-08-21/07-12-20/run.log:107519

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1.  The function x ↦ 1/√x is antitone on the interval [1,10000].
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 / Real.sqrt x)) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  -- 2.  Compute the integral of 1/√x from 1 to 10000.
  have h_int_val :
      (∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x)) = (198 : ℝ) := by sorry
  -- 3.  For each integer k with 2 ≤ k ≤ 10000, the term 1/√k is bounded by the integral over [k‑1,k].
  have h_interval (k : ℕ) (hk : 2 ≤ k ∧ k ≤ 10000) :
      (1 / Real.sqrt (k : ℝ)) ≤
        ∫ x in ((k - 1 : ℝ))..(k : ℝ), (1 / Real.sqrt x) := by sorry
  -- 4.  Sum the inequality of step 3 over all k in the closed interval to obtain a global bound.
  have h_sum_le_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 5.  The inequality in step 4 is strict because the function is not constant on any sub‑interval.
  have h_sum_ne_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) ≠
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 6.  From the previous two facts we get a strict inequality.
  have h_sum_lt_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 7.  Replace the integral by its value computed in step 2.
  simpa [h_int_val] using h_sum_lt_int
```

## 7 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-08-21 10:00:13,850 outputs/2026-08-21/07-12-20/run.log:109508

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1. Compare the discrete sum with the corresponding integral.
  have h_sum_lt_integral :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k)) <
        ∫ x in (1 : ℝ)..10000, (1 / Real.sqrt x) := by sorry
  -- 2. Evaluate the integral explicitly.
  have h_integral_eq :
      (∫ x in (1 : ℝ)..10000, (1 / Real.sqrt x)) = (198 : ℝ) := by sorry
  -- 3. Combine the two previous facts to obtain the desired inequality.
  have h_final : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k)) < (198 : ℝ) := by sorry
  exact h_final
```

## 8 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-08-21 10:01:54,716 outputs/2026-08-21/07-12-20/run.log:110917

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1. Relate the finite sum to the integral of 1/√x on [1,10000].
  have h_sum_lt_integral :
      (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 2. Compute the integral explicitly: ∫₁¹⁰⁰⁰⁰ 1/√x dx = 198.
  have h_integral_eq :
      (∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x)) = (198 : ℝ) := by sorry
  -- 3. Combine the two previous facts to obtain the desired inequality.
  have h_final :
      (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < (198 : ℝ) := by sorry
  exact h_final
```
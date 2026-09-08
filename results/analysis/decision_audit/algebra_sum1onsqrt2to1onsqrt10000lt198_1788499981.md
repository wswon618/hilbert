## 1 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 05:58:33,898 logs/variance_r1_20260904_044253.log:23462

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1️⃣  The function `x ↦ 1 / Real.sqrt x` is antitone on `[1,10000]`.
  have h_antitone : AntitoneOn (fun x : ℝ => (1 / Real.sqrt x)) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  -- 2️⃣  Compute the integral of `1 / sqrt x` from `1` to `10000`.
  have h_integral_eq :
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) =
        (2 * Real.sqrt (10000 : ℝ) - 2 * Real.sqrt (1 : ℝ)) := by sorry
  -- 3️⃣  Simplify the value of the integral to `198`.
  have h_integral_val : (∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x)) = (198 : ℝ) := by sorry
  -- 4️⃣  Relate the finite sum to the integral using the monotonicity of the integrand.
  have h_sum_le_integral :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k)) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 5️⃣  Strengthen the inequality to a strict one (the function is strictly decreasing).
  have h_strict :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k)) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 6️⃣  Conclude the desired bound `< 198` by combining the strict inequality with the integral value.
  have h_lt_198 :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k)) < (198 : ℝ) := by sorry
  exact h_lt_198
```

## 2 h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 07:17:06,977 logs/variance_r1_20260904_044253.log:71904

```lean
theorem h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) =
      (2 * Real.sqrt (10000 : ℝ) - 2 * Real.sqrt (1 : ℝ)) := by
  have h_deriv_u :
      ∀ x ∈ [[(1 : ℝ), (10000 : ℝ)]],
        HasDerivWithinAt (fun x => (2 : ℝ) * Real.sqrt x) (1 / Real.sqrt x) [[(1 : ℝ), (10000 : ℝ)]] x := by sorry
  have h_deriv_v :
      ∀ x ∈ [[(1 : ℝ), (10000 : ℝ)]],
        HasDerivWithinAt (fun _ : ℝ => (1 : ℝ)) (0 : ℝ) [[(1 : ℝ), (10000 : ℝ)]] x := by sorry
  have h_int_u' :
      IntervalIntegrable (fun x => (1 / Real.sqrt x)) volume (1 : ℝ) (10000 : ℝ) := by sorry
  have h_int_v' :
      IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (1 : ℝ) (10000 : ℝ) := by sorry
  have h_eq := by sorry
  simpa [mul_comm, mul_left_comm, mul_assoc] using h_eq
```

## 3 h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 07:29:34,112 logs/variance_r1_20260904_044253.log:89367

```lean
theorem h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k)) <
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by
  -- 1️⃣  The function  x ↦ 1 / √x  is antitone on [1,10000].
  have h_antitone : AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  -- 2️⃣  Apply the antitone sum–integral comparison (with the appropriate re‑indexing).
  have h_le :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 3️⃣  Strengthen the non‑strict inequality to a strict one using the strict decrease of x ↦ 1/√x.
  have h_lt :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  exact h_lt
```

## 4 h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 07:33:42,260 logs/variance_r1_20260904_044253.log:96329

```lean
theorem h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k)) ≤
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by
  -- rewrite the finite sum over `Icc` as a sum over a half‑open interval
  have h_eq_sum :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k)) =
        ∑ i in Finset.Ico (1 : ℕ) 10000, (1 / Real.sqrt (i + 1)) := by sorry
  -- pointwise inequality needed for the comparison theorem
  have h_pointwise :
      ∀ i ∈ Finset.Ico (1 : ℕ) 10000,
        ∀ x ∈ Set.Ico (i : ℝ) (i + 1 : ℝ),
          (1 / Real.sqrt (i + 1)) ≤ (1 / Real.sqrt x) := by sorry
  -- integrability of the dominating function on the interval
  have h_integrable :
      IntegrableOn (fun x : ℝ => 1 / Real.sqrt x) (Set.Ico (1 : ℝ) 10000) := by sorry
  -- apply the sum‑integral comparison theorem
  have h_sum_le_int :
      (∑ i in Finset.Ico (1 : ℕ) 10000, (1 / Real.sqrt (i + 1))) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  -- finish by rewriting the left‑hand side with `h_eq_sum`
  simpa [h_eq_sum] using h_sum_le_int
```

## 5 h_integral_val_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 07:33:49,210 logs/variance_r1_20260904_044253.log:96539

```lean
theorem h_integral_val_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x)) = (198 : ℝ) := by
  have h_le : (1 : ℝ) ≤ 10000 := by sorry
  have h_cont :
      ContinuousOn (fun x : ℝ => (2 : ℝ) * Real.sqrt x) (Set.Icc (1 : ℝ) 10000) := by sorry
  have h_deriv :
      ∀ x ∈ Set.Ioo (1 : ℝ) 10000,
        HasDerivAt (fun x => (2 : ℝ) * Real.sqrt x) (1 / Real.sqrt x) x := by sorry
  have h_int :
      IntervalIntegrable (fun x : ℝ => 1 / Real.sqrt x) volume (1 : ℝ) 10000 := by sorry
  have h_eq :
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) =
        (fun x => (2 : ℝ) * Real.sqrt x) 10000 -
          (fun x => (2 : ℝ) * Real.sqrt x) 1 := by sorry
  have h_sqrt10000 : Real.sqrt (10000 : ℝ) = (100 : ℝ) := by sorry
  have h_sqrt1 : Real.sqrt (1 : ℝ) = (1 : ℝ) := by sorry
  have h_calc :
      (fun x => (2 : ℝ) * Real.sqrt x) 10000 -
        (fun x => (2 : ℝ) * Real.sqrt x) 1 = (198 : ℝ) := by sorry
  simpa [h_calc] using h_eq
```

## 6 h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 07:33:55,814 logs/variance_r1_20260904_044253.log:96878

```lean
theorem h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) =
      (2 * Real.sqrt (10000 : ℝ) - 2 * Real.sqrt (1 : ℝ)) := by
  have hab : (1 : ℝ) ≤ 10000 := by sorry
  have hcont : ContinuousOn (fun x : ℝ => 2 * Real.sqrt x) (Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  have hderiv :
      ∀ x ∈ Ioo (1 : ℝ) (10000 : ℝ),
        HasDerivAt (fun x : ℝ => 2 * Real.sqrt x) (1 / Real.sqrt x) x := by sorry
  have hint :
      IntervalIntegrable (fun x : ℝ => 1 / Real.sqrt x) volume (1 : ℝ) (10000 : ℝ) := by sorry
  have hftc := by sorry
  simpa using hftc
```

## 7 h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 08:08:22,382 logs/variance_r1_20260904_044253.log:113671

```lean
theorem h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k)) <
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  have h_le :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  have h_ne :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≠
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  have h_lt :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  exact h_lt
```

## 8 h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 09:13:44,632 logs/variance_r1_20260904_044253.log:130940

```lean
theorem h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k)) <
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  have h_le :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  have h_ne :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≠
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  have h_lt :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  exact h_lt
```

## 9 h_sum_le_int_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 09:32:10,617 logs/variance_r1_20260904_044253.log:149960

```lean
theorem h_sum_le_int_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_pointwise :
        ∀ i ∈ Finset.Ico (1 : ℕ) 10000,
          ∀ x ∈ Set.Ico (i : ℝ) (i + 1 : ℝ),
            (1 / Real.sqrt (i + 1)) ≤ (1 / Real.sqrt x))
    (h_integrable :
        MeasureTheory.IntegrableOn (fun x : ℝ => 1 / Real.sqrt x) (Set.Ico (1 : ℝ) 10000)) :
    (∑ i in Finset.Ico (1 : ℕ) 10000, (1 / Real.sqrt (i + 1))) ≤
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by
  -- 1. Integral bound on each unit interval using the pointwise inequality
  have h_interval (i : ℕ) (hi : i ∈ Finset.Ico (1 : ℕ) 10000) :
      (1 / Real.sqrt (i + 1)) ≤
        ∫ x in (i : ℝ)..((i : ℝ) + 1), (1 / Real.sqrt x) := by sorry
  -- 2. Sum the inequalities over all indices
  have h_sum_le :
      (∑ i in Finset.Ico (1 : ℕ) 10000, (1 / Real.sqrt (i + 1))) ≤
        ∑ i in Finset.Ico (1 : ℕ) 10000,
          ∫ x in (i : ℝ)..((i : ℝ) + 1), (1 / Real.sqrt x) := by sorry
  -- 3. The sum of the integrals over adjacent unit intervals equals the integral over the whole range
  have h_sum_eq :
      (∑ i in Finset.Ico (1 : ℕ) 10000,
          ∫ x in (i : ℝ)..((i : ℝ) + 1), (1 / Real.sqrt x)) =
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x)) := by sorry
  -- 4. Conclude the desired inequality
  calc
    (∑ i in Finset.Ico (1 : ℕ) 10000, (1 / Real.sqrt (i + 1))) ≤
        ∑ i in Finset.Ico (1 : ℕ) 10000,
          ∫ x in (i : ℝ)..((i : ℝ) + 1), (1 / Real.sqrt x) := h_sum_le
    _ = ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := h_sum_eq
```

## 10 h_sum_le_int_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 09:34:44,975 logs/variance_r1_20260904_044253.log:153290

```lean
theorem h_sum_le_int_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_pointwise :
        ∀ i ∈ Finset.Ico (1 : ℕ) 10000,
          ∀ x ∈ Set.Ico (i : ℝ) (i + 1 : ℝ),
            (1 / Real.sqrt (i + 1)) ≤ (1 / Real.sqrt x))
    (h_integrable :
        MeasureTheory.IntegrableOn (fun x : ℝ => 1 / Real.sqrt x) (Set.Ico (1 : ℝ) 10000)) :
    (∑ i in Finset.Ico (1 : ℕ) 10000, (1 / Real.sqrt (i + 1))) ≤
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by
  -- 1️⃣  Establish the trivial ordering 1 ≤ 10000.
  have hab : (1 : ℝ) ≤ (10000 : ℝ) := by sorry
  -- 2️⃣  Apply the comparison theorem `sum_Ico_le_integral_of_le`.
  have h_le := by sorry
  -- 3️⃣  Conclude by rewriting the goal to the obtained inequality.
  simpa using h_le
```

## 11 h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 09:54:35,153 logs/variance_r1_20260904_044253.log:163289

```lean
theorem h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k)) <
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  have h_le :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  have h_ne :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≠
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  have h_lt :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  exact h_lt
```

## 12 h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 11:06:12,405 logs/variance_r1_20260904_044253.log:175830

```lean
theorem h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k)) <
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  have h_le :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  have h_lt :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  exact h_lt
```

## 13 h_le_h_sum_le_int_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 11:29:21,810 logs/variance_r1_20260904_044253.log:188762

```lean
theorem h_le_h_sum_le_int_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_pointwise :
        ∀ i ∈ Finset.Ico (1 : ℕ) 10000,
          ∀ x ∈ Set.Ico (i : ℝ) (i + 1 : ℝ),
            (1 / Real.sqrt (i + 1)) ≤ (1 / Real.sqrt x))
    (h_integrable :
        MeasureTheory.IntegrableOn (fun x : ℝ => 1 / Real.sqrt x) (Set.Ico (1 : ℝ) 10000))
    (hab : (1 : ℝ) ≤ (10000 : ℝ)) :
    (∑ i in Finset.Ico (1 : ℕ) 10000, (1 / Real.sqrt (i + 1))) ≤
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by
  -- 1. Pointwise inequality on each unit interval gives a bound by the integral over that interval.
  have h_i_le_integral (i : ℕ) (hi : i ∈ Finset.Ico (1 : ℕ) 10000) :
      (1 / Real.sqrt (i + 1)) ≤
        ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 2. Summing the inequalities from (1) over all i yields a bound for the whole sum.
  have h_sum_le_sum_integral :
      (∑ i in Finset.Ico (1 : ℕ) 10000, (1 / Real.sqrt (i + 1))) ≤
        ∑ i in Finset.Ico (1 : ℕ) 10000,
          ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 3. The sum of the integrals over adjacent unit intervals equals the integral over the whole interval.
  have h_sum_integral_eq :
      (∑ i in Finset.Ico (1 : ℕ) 10000,
          ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt x)) =
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 4. Combine the previous results to obtain the desired inequality.
  have : (∑ i in Finset.Ico (1 : ℕ) 10000, (1 / Real.sqrt (i + 1))) ≤
          ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  exact this
```

## 14 h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 11:35:07,122 logs/variance_r1_20260904_044253.log:190107

```lean
theorem h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k)) <
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  have h_le :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  have h_ne :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≠
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  have h_lt :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  exact h_lt
```

## 15 h_sum_integral_eq_h_le_h_sum_le_int_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 12:13:56,718 logs/variance_r1_20260904_044253.log:214707

```lean
theorem h_sum_integral_eq_h_le_h_sum_le_int_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ i in Finset.Ico (1 : ℕ) 10000,
        ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt x)) =
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by
  -- 1.  Integrability of the integrand on each unit sub‑interval.
  have h_int :
      ∀ i ∈ Finset.Ico (1 : ℕ) 10000,
        IntervalIntegrable (fun x : ℝ => (1 / Real.sqrt x)) volume i (i + 1) := by sorry
  -- 2.  Sum of the integrals over the adjacent sub‑intervals equals the integral over the whole interval.
  have h_sum :
      (∑ k in Finset.range 9999,
          ∫ x in ((k + 1 : ℝ))..((k + 2 : ℝ)), (1 / Real.sqrt x)) =
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 3.  Re‑index the finite sum from `Finset.Ico 1 10000` to `Finset.range 9999`.
  have h_reindex :
      (∑ i in Finset.Ico (1 : ℕ) 10000,
          ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt x)) =
        (∑ k in Finset.range 9999,
          ∫ x in ((k + 1 : ℝ))..((k + 2 : ℝ)), (1 / Real.sqrt x)) := by sorry
  -- 4.  Conclude the desired equality.
  calc
    (∑ i in Finset.Ico (1 : ℕ) 10000,
        ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt x))
        = (∑ k in Finset.range 9999,
            ∫ x in ((k + 1 : ℝ))..((k + 2 : ℝ)), (1 / Real.sqrt x)) := by
          simpa using h_reindex
    _ = ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by
          simpa using h_sum
```

## 16 h_i_le_integral_h_le_h_sum_le_int_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 12:13:58,226 logs/variance_r1_20260904_044253.log:214827

```lean
theorem h_i_le_integral_h_le_h_sum_le_int_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_pointwise :
        ∀ i ∈ Finset.Ico (1 : ℕ) 10000,
          ∀ x ∈ Set.Ico (i : ℝ) (i + 1 : ℝ),
            (1 / Real.sqrt (i + 1)) ≤ (1 / Real.sqrt x))
    (h_integrable :
        MeasureTheory.IntegrableOn (fun x : ℝ => 1 / Real.sqrt x) (Set.Ico (1 : ℝ) 10000))
    (hab : (1 : ℝ) ≤ (10000 : ℝ))
    (i : ℕ) (hi : i ∈ Finset.Ico (1 : ℕ) 10000) :
    (1 / Real.sqrt (i + 1)) ≤
      ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt x) := by
  -- pointwise inequality on the interval
  have h_le :
      ∀ x ∈ Set.Ico (i : ℝ) (i + 1 : ℝ),
        (1 / Real.sqrt (i + 1)) ≤ (1 / Real.sqrt x) := by sorry
  -- integrability of the constant function on the interval
  have h_const_int :
      MeasureTheory.IntegrableOn (fun _ : ℝ => (1 / Real.sqrt (i + 1)))
        (Set.Ico (i : ℝ) (i + 1 : ℝ)) := by sorry
  -- integrability of 1/√x on the interval (restriction of the given integrable function)
  have h_f_int :
      MeasureTheory.IntegrableOn (fun x : ℝ => 1 / Real.sqrt x)
        (Set.Ico (i : ℝ) (i + 1 : ℝ)) := by sorry
  -- monotonicity of the interval integral using the pointwise bound
  have h_int_le :
      (∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt (i + 1))) ≤
        ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt x) := by sorry
  -- evaluation of the integral of the constant function on a unit interval
  have h_const_eq :
      (∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt (i + 1))) = (1 / Real.sqrt (i + 1)) := by sorry
  -- combine the previous facts to obtain the desired inequality
  simpa [h_const_eq] using h_int_le
```

## 17 h_sum_integral_eq_h_le_h_sum_le_int_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 12:32:27,616 logs/variance_r1_20260904_044253.log:234423

```lean
theorem h_sum_integral_eq_h_le_h_sum_le_int_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ i in Finset.Ico (1 : ℕ) 10000,
        ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt x)) =
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by
  -- integrand definition (for readability)
  have f_def : (fun x : ℝ => (1 / Real.sqrt x)) = fun x => (1 / Real.sqrt x) := by sorry
  -- integrability of the integrand on each unit subinterval
  have h_int :
      ∀ i ∈ Finset.Ico (1 : ℕ) 10000,
        IntervalIntegrable (fun x : ℝ => (1 / Real.sqrt x)) volume (i : ℝ) (i + 1 : ℝ) := by sorry
  -- the inequality 1 ≤ 10000, required by the sum theorem
  have h_le : (1 : ℕ) ≤ 10000 := by sorry
  -- apply the theorem that the sum of integrals over adjacent intervals equals the integral over the whole interval
  have h_sum :
      (∑ i in Finset.Ico (1 : ℕ) 10000,
          ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt x)) =
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  exact h_sum
```

## 18 h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 12:38:28,336 logs/variance_r1_20260904_044253.log:242111

```lean
theorem h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k)) <
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  have h_le :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  have h_ne :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≠
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  have h_lt :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  exact h_lt
```

## 19 h_i_le_integral_h_le_h_sum_le_int_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 12:45:32,316 logs/variance_r1_20260904_044253.log:252389

```lean
theorem h_i_le_integral_h_le_h_sum_le_int_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_pointwise :
        ∀ i ∈ Finset.Ico (1 : ℕ) 10000,
          ∀ x ∈ Set.Ico (i : ℝ) (i + 1 : ℝ),
            (1 / Real.sqrt (i + 1)) ≤ (1 / Real.sqrt x))
    (h_integrable :
        MeasureTheory.IntegrableOn (fun x : ℝ => 1 / Real.sqrt x) (Set.Ico (1 : ℝ) 10000))
    (hab : (1 : ℝ) ≤ (10000 : ℝ))
    (i : ℕ) (hi : i ∈ Finset.Ico (1 : ℕ) 10000) :
    (1 / Real.sqrt (i + 1)) ≤
      ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt x) := by
  -- 1. bounds on `i` as real numbers
  have h_i_bounds : (1 : ℝ) ≤ (i : ℝ) ∧ (i : ℝ) < (10000 : ℝ) := by sorry
  -- 2. the interval `[i,i+1]` is contained in `[1,10000]`
  have h_subset :
      Set.Ico (i : ℝ) (i + 1 : ℝ) ⊆ Set.Icc (1 : ℝ) (10000 : ℝ) := by sorry
  -- 3. pointwise inequality on the whole interval, lifted to an `ae` statement
  have h_ae_le :
      (fun x : ℝ => (1 / Real.sqrt (i + 1))) ≤ᵐ[Measure.restrict MeasureTheory.volume (Set.Ico (i : ℝ) (i + 1 : ℝ))]
        (fun x : ℝ => (1 / Real.sqrt x)) := by sorry
  -- 4. integrability of the constant function on the interval
  have h_int_const :
      MeasureTheory.IntegrableOn (fun x : ℝ => (1 / Real.sqrt (i + 1))) (Set.Ico (i : ℝ) (i + 1 : ℝ)) := by sorry
  -- 5. integrability of `1/√x` on the interval, using the global integrability hypothesis
  have h_int_fun :
      MeasureTheory.IntegrableOn (fun x : ℝ => (1 / Real.sqrt x)) (Set.Ico (i : ℝ) (i + 1 : ℝ)) := by sorry
  -- 6. monotonicity of the integral for the `ae` inequality
  have h_int_le :
      ∫ x in Set.Ico (i : ℝ) (i + 1 : ℝ), (1 / Real.sqrt (i + 1)) ≤
        ∫ x in Set.Ico (i : ℝ) (i + 1 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 7. evaluate the integral of the constant function
  have h_int_const_eq :
      ∫ x in Set.Ico (i : ℝ) (i + 1 : ℝ), (1 / Real.sqrt (i + 1)) = (1 / Real.sqrt (i + 1)) := by sorry
  -- 8. rewrite the right‑hand integral as an interval integral
  have h_interval_eq :
      ∫ x in Set.Ico (i : ℝ) (i + 1 : ℝ), (1 / Real.sqrt x) =
        ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 9. combine the previous facts
  have : (1 / Real.sqrt (i + 1)) ≤ ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt x) := by sorry
  exact this
```

## 20 h_ne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 13:33:46,656 logs/variance_r1_20260904_044253.log:292070

```lean
theorem h_ne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)))
    (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≠
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by
  by_contra h_eq
  -- integral is bounded above by the sum over the half‑open interval `[1,10001)`
  have h_int_le_sum :
      (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) ≤
        ∑ k in Finset.Ico (1 : ℕ) 10001, (1 : ℝ) / Real.sqrt k := by sorry
  -- rewrite that sum as `f 1 +` the sum appearing in the statement
  have h_sum_eq :
      ∑ k in Finset.Ico (1 : ℕ) 10001, (1 : ℝ) / Real.sqrt k =
        (1 : ℝ) / Real.sqrt (1 : ℝ) +
          ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by sorry
  -- the first term is strictly larger than the last term of the other sum
  have h_one_gt_last :
      (1 : ℝ) / Real.sqrt (1 : ℝ) > (1 : ℝ) / Real.sqrt (10000 : ℝ) := by sorry
  -- therefore the sum over `Icc 2 10000` is strictly smaller than the sum over `Ico 1 10001`
  have h_sum_strict :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∑ k in Finset.Ico (1 : ℕ) 10001, (1 : ℝ) / Real.sqrt k := by sorry
  -- combine the two inequalities to obtain a strict inequality between the sum and the integral
  have h_lt :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- rewrite the assumed equality in a convenient form
  have h_eq' :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- derive a contradiction from the strict inequality and the assumed equality
  have h_false : False := by sorry
  exact h_false
```

## 21 h_le_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 13:34:06,924 logs/variance_r1_20260904_044253.log:292308

```lean
theorem h_le_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ))) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by
  have hab : (1 : ℕ) ≤ 10000 := by sorry
  have hsum_le :
      (∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  have hsum_eq :
      (∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) =
        ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by sorry
  simpa [hsum_eq] using hsum_le
```

## 22 h_le_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 13:36:00,461 logs/variance_r1_20260904_044253.log:295381

```lean
theorem h_le_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ))) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by
  -- 1. The real bounds satisfy `1 ≤ 10000`.
  have hab : (1 : ℝ) ≤ (10000 : ℝ) := by sorry
  -- 2. Apply the antitone sum‑integral comparison theorem.
  have hsum_le :
      (∑ i in Finset.Ico (1 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 3. Reindex the sum `i ↦ i+1` to obtain the required sum over `k ∈ Icc 2 10000`.
  have hsum_eq :
      (∑ i in Finset.Ico (1 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt (i + 1)) =
        ∑ k in Finset.Icc (2 : ℕ) 10000,
          (1 : ℝ) / Real.sqrt k := by sorry
  -- 4. Rewrite the left‑hand side of `hsum_le` using `hsum_eq`.
  have hdesired :
      (∑ k in Finset.Icc (2 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 5. Conclude.
  exact hdesired
```

## 23 h_i_le_integral_h_le_h_sum_le_int_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 14:04:35,593 logs/variance_r1_20260904_044253.log:324947

```lean
theorem h_i_le_integral_h_le_h_sum_le_int_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_pointwise :
        ∀ i ∈ Finset.Ico (1 : ℕ) 10000,
          ∀ x ∈ Set.Ico (i : ℝ) (i + 1 : ℝ),
            (1 / Real.sqrt (i + 1)) ≤ (1 / Real.sqrt x))
    (h_integrable :
        MeasureTheory.IntegrableOn (fun x : ℝ => 1 / Real.sqrt x) (Set.Ico (1 : ℝ) 10000))
    (hab : (1 : ℝ) ≤ (10000 : ℝ))
    (i : ℕ) (hi : i ∈ Finset.Ico (1 : ℕ) 10000) :
    (1 / Real.sqrt (i + 1)) ≤
      ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt x) := by
  -- pointwise inequality specialised to the chosen `i`
  have h_pointwise_i :
      ∀ x ∈ Set.Ico (i : ℝ) (i + 1 : ℝ),
        (1 / Real.sqrt (i + 1)) ≤ (1 / Real.sqrt x) := by sorry
  -- integral of the constant function `1 / sqrt (i+1)` over `[i,i+1]`
  have h_const_integral :
      ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt (i + 1)) = (1 / Real.sqrt (i + 1)) := by sorry
  -- monotonicity of the interval integral using the pointwise bound
  have h_int_mono :
      ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt (i + 1)) ≤
        ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt x) := by sorry
  -- combine the previous facts to obtain the desired inequality
  have h_goal :
      (1 / Real.sqrt (i + 1)) ≤ ∫ x in (i : ℝ)..(i + 1 : ℝ), (1 / Real.sqrt x) := by sorry
  exact h_goal
```

## 24 h_ne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-04 14:10:44,223 logs/variance_r1_20260904_044253.log:328162

```lean
theorem h_ne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)))
    (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≠
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by
  by_contra h_eq
  -- integral is bounded below by the sum over the half‑open interval `[1,10001)`
  have h_sum_le_int :
      (∑ k in Finset.Ico (1 : ℕ) 10001, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- rewrite that sum as `f 1 +` the sum appearing in the statement
  have h_sum_eq :
      (∑ k in Finset.Ico (1 : ℕ) 10001, (1 : ℝ) / Real.sqrt k) =
        (1 : ℝ) / Real.sqrt (1 : ℝ) +
          ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by sorry
  -- the first term is strictly larger than the last term of the other sum
  have h_one_gt_last :
      (1 : ℝ) / Real.sqrt (1 : ℝ) > (1 : ℝ) / Real.sqrt (10000 : ℝ) := by sorry
  -- therefore the sum over `Icc 2 10000` is strictly smaller than the sum over `Ico 1 10001`
  have h_sum_strict :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∑ k in Finset.Ico (1 : ℕ) 10001, (1 : ℝ) / Real.sqrt k := by sorry
  -- combine the two inequalities to obtain a strict inequality between the sum and the integral
  have h_lt :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- rewrite the assumed equality in a convenient form
  have h_eq' :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- derive a contradiction from the strict inequality and the assumed equality
  have h_false : False := by sorry
  exact h_false
```
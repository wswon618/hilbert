## 1 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 07:55:06,840 logs/variance_r3_20260905_074359.log:5808

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1️⃣  The function x ↦ 1/√x is antitone on the interval [1,10000].
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000) := by sorry
  -- 2️⃣  Compute the integral of 1/√x from 1 to 10000.
  have h_integral_eq :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by sorry
  -- 3️⃣  Show that the finite sum is strictly smaller than this integral.
  have h_sum_lt_integral :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 4️⃣  Conclude the desired inequality by rewriting the integral.
  have h_sum_lt_198 :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by sorry
  exact h_sum_lt_198
```

## 2 h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 08:35:49,968 logs/variance_r3_20260905_074359.log:27933

```lean
theorem h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by
  have hderiv :
      ∀ x ∈ uIcc (1 : ℝ) 10000,
        HasDerivAt (fun x => (2 : ℝ) * Real.sqrt x) (1 / Real.sqrt x) x := by sorry
  have hint :
      IntervalIntegrable (fun x => (1 : ℝ) / Real.sqrt x) volume (1 : ℝ) 10000 := by sorry
  have hcalc :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
        (2 : ℝ) * Real.sqrt (10000 : ℝ) - (2 : ℝ) * Real.sqrt (1 : ℝ) := by sorry
  have hsqrt10000 :
      Real.sqrt (10000 : ℝ) = (100 : ℝ) := by sorry
  have hsqrt1 :
      Real.sqrt (1 : ℝ) = (1 : ℝ) := by sorry
  have hfinal :
      (2 : ℝ) * Real.sqrt (10000 : ℝ) - (2 : ℝ) * Real.sqrt (1 : ℝ) = (198 : ℝ) := by sorry
  simpa [hfinal] using hcalc
```

## 3 h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 08:36:43,147 logs/variance_r3_20260905_074359.log:29131

```lean
theorem h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h_le :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_pos :
      (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  have h_strict :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_integral_val :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by sorry
  have : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) := by sorry
  exact this
```

## 4 h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 09:46:06,529 logs/variance_r3_20260905_074359.log:51432

```lean
theorem h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h_le :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_pos :
      (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  have h_le2 :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_lt_integral :
      (∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_strict :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_integral_val :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by sorry
  have : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) := by sorry
  exact this
```

## 5 h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 10:27:08,673 logs/variance_r3_20260905_074359.log:78586

```lean
theorem h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h_le :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_pos :
      (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  have h_le2 :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_lt_integral :
      (∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_strict :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_integral_val :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by sorry
  exact h_strict
```

## 6 h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 10:48:54,792 logs/variance_r3_20260905_074359.log:97256

```lean
theorem h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (k : ℝ)) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h_le :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (k : ℝ)) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_pos :
      (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  have h_le2 :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (k : ℝ)) ≤
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_lt_integral :
      (∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_strict :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (k : ℝ)) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  exact h_strict
```

## 7 h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 11:28:14,125 logs/variance_r3_20260905_074359.log:111247

```lean
theorem h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (k : ℝ)) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h_le :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (k : ℝ)) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_pos :
      (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  have h_le2 :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (k : ℝ)) ≤
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_lt_integral :
      (∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_strict :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (k : ℝ)) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  exact h_strict
```

## 8 h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 11:58:21,701 logs/variance_r3_20260905_074359.log:119484

```lean
theorem h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h_le :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_pos :
      (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  have h_int_gt_f2 :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by sorry
  have h_sum_le :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        (1 : ℝ) / Real.sqrt (2) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_strict :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  exact h_strict
```

## 9 h_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 12:55:53,934 logs/variance_r3_20260905_074359.log:167430

```lean
theorem h_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  -- 1. Apply the antitone sum‑integral comparison theorem on `[1,10000]`.
  have h_le :
      (∑ i in Finset.Ico (1 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 2. Rewrite the sum over `Ico 1 10000` of `f (i+1)` as a sum over `Icc 2 10000`.
  have h_sum_eq :
      (∑ i in Finset.Ico (1 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt (i + 1)) =
      ∑ k in Finset.Icc (2 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt k := by sorry
  -- 3. Substitute the rewritten sum into the inequality obtained in step 1.
  have h_goal :
      (∑ k in Finset.Icc (2 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 4. Conclude the desired inequality.
  exact h_goal
```

## 10 h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 12:57:28,035 logs/variance_r3_20260905_074359.log:169184

```lean
theorem h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ))
    (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
    (h_pos :
        (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x)
    (h_int_gt_f2 :
        (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2))
    (h_sum_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          (1 : ℝ) / Real.sqrt (2) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  -- 1. Rewrite the whole integral as the sum of the integrals over [1,2] and [2,10000].
  have h_int_eq' :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
        (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
          ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 2. Add the same non‑negative term to the strict inequality over [1,2].
  have h_int_gt :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x >
        (1 : ℝ) / Real.sqrt (2) +
          ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 3. Use the equality from step 1 to obtain a strict inequality for the whole integral.
  have h_int_strict :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) >
        (1 : ℝ) / Real.sqrt (2) +
          ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 4. Combine the upper bound for the sum with the strict inequality for the integral.
  have h_result :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  exact h_result
```

## 11 h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 12:57:33,064 logs/variance_r3_20260905_074359.log:169326

```lean
theorem h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ))
    (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) :
    (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by
  -- positivity of √2
  have h_sqrt2_pos : 0 < Real.sqrt (2 : ℝ) := by sorry
  -- positivity of 1 / √2
  have h_one_div_sqrt2_pos : 0 < (1 : ℝ) / Real.sqrt (2 : ℝ) := by sorry
  -- pointwise inequality on [1,2] obtained from antitone property
  have h_pointwise :
      ∀ x ∈ Set.Icc (1 : ℝ) 2,
        (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (1 : ℝ) / Real.sqrt x := by sorry
  -- integrate the pointwise inequality
  have h_integral_le :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2 : ℝ)) ≤
        ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  -- evaluate the integral of the constant function
  have h_const_integral :
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2 : ℝ) =
        (1 : ℝ) / Real.sqrt (2 : ℝ) := by sorry
  -- combine the previous two inequalities
  have h_lower_bound :
      (1 : ℝ) / Real.sqrt (2 : ℝ) ≤
        ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  -- conclude strict positivity of the integral
  have h_pos :
      (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  exact h_pos
```

## 12 h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 12:59:51,762 logs/variance_r3_20260905_074359.log:172506

```lean
theorem h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ))
    (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
    (h_pos :
        (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by
  -- 1️⃣  The sum over the integers is strictly larger than the first term
  have h_sum_strict :
      (1 : ℝ) / Real.sqrt (2) <
        ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by sorry
  -- 2️⃣  From the previous inequality and the hypothesis `h_le` we get a strict lower
  --     bound for the large integral
  have h_int_big_strict :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by sorry
  -- 3️⃣  The integral over `[2,10000]` is non‑negative
  have h_int_2_10000_nonneg :
      (0 : ℝ) ≤ ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 4️⃣  Rewrite the big integral as the sum of the two adjacent integrals and use the
  --     non‑negativity of the second part to obtain the desired strict inequality
  have h_int_12_strict :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by sorry
  -- 5️⃣  Conclude the proof
  exact h_int_12_strict
```

## 13 h_sum_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 13:08:03,498 logs/variance_r3_20260905_074359.log:189240

```lean
theorem h_sum_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ))
    (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
    (h_pos :
        (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x)
    (h_int_gt_f2 :
        (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
      (1 : ℝ) / Real.sqrt (2) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  -- 1. Restrict the antitone hypothesis to the interval [2,10000].
  have h_antitone_sub :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) 10000) := by sorry
  -- 2. Rewrite the sum over `Ico 2 10000` with the shift `i ↦ i+1` as a sum over `Icc 3 10000`.
  have h_sum_eq :
      (∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
        ∑ i in Finset.Ico (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1) := by sorry
  -- 3. Apply the antitone‑sum versus integral estimate on the interval [2,10000].
  have h_sum_le_int :
      (∑ i in Finset.Ico (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 4. Transfer the inequality to the sum over `Icc 3 10000` using the equality from step 2.
  have h_sum_le_int' :
      (∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 5. Split the original sum into the first term `1/√2` plus the sum from `3` to `10000`,
  --    then combine with the inequality from step 4.
  have h_goal :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        (1 : ℝ) / Real.sqrt (2) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  exact h_goal
```

## 14 h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 13:08:44,050 logs/variance_r3_20260905_074359.log:190675

```lean
theorem h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h_int₁ :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume 1 2 := by sorry
  have h_int₂ :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume 2 10000 := by sorry
  have h_eq :
      ((∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  simpa using h_eq.symm
```

## 15 h_integral_le_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 13:10:50,519 logs/variance_r3_20260905_074359.log:194987

```lean
theorem h_integral_le_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_pointwise :
        ∀ x ∈ Set.Icc (1 : ℝ) 2,
          (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (1 : ℝ) / Real.sqrt x) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2 : ℝ)) ≤
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by
  -- integrability of the constant function
  have h_const_int :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / Real.sqrt (2 : ℝ)) volume 1 2 := by sorry
  -- integrability of the function x ↦ 1 / sqrt x on [1,2]
  have h_func_int :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume 1 2 := by sorry
  -- the pointwise inequality holds almost everywhere on the interval
  have h_ae_le :
      (∀ᵐ x ∂(volume.restrict (Set.Icc (1 : ℝ) 2)),
        (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (1 : ℝ) / Real.sqrt x) := by sorry
  -- apply monotonicity of the interval integral
  have h_le :
      (∫ x in 1..2, (1 : ℝ) / Real.sqrt (2 : ℝ)) ≤
        ∫ x in 1..2, (1 : ℝ) / Real.sqrt x := by sorry
  exact h_le
```

## 16 h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 13:13:03,929 logs/variance_r3_20260905_074359.log:202227

```lean
theorem h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ))
    (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
    (h_pos :
        (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by
  have h_sum_strict :
      (1 : ℝ) / Real.sqrt (2) <
        ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by sorry
  have h_int_big_strict :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by sorry
  have h_int_12_strict :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by sorry
  exact h_int_12_strict
```

## 17 h_integral_le_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 13:15:02,837 logs/variance_r3_20260905_074359.log:206665

```lean
theorem h_integral_le_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_pointwise :
        ∀ x ∈ Set.Icc (1 : ℝ) 2,
          (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (1 : ℝ) / Real.sqrt x) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2 : ℝ)) ≤
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by
  have h_le :
      ∀ x ∈ Set.Icc (1 : ℝ) 2,
        (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (1 : ℝ) / Real.sqrt x := by sorry
  have h_int_const :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / Real.sqrt (2 : ℝ)) volume (1 : ℝ) 2 := by sorry
  have h_int_var :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume (1 : ℝ) 2 := by sorry
  have h_integral_le :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2 : ℝ)) ≤
        ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  exact h_integral_le
```

## 18 h_eq_h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 13:23:53,687 logs/variance_r3_20260905_074359.log:227711

```lean
theorem h_eq_h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ((∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h_le1 : (1 : ℝ) ≤ 2 := by sorry
  have h_le2 : (2 : ℝ) ≤ 10000 := by sorry
  have h_int : IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume (1 : ℝ) 10000 := by sorry
  have h_add :
      ((∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  exact h_add
```

## 19 h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 13:32:23,937 logs/variance_r3_20260905_074359.log:239563

```lean
theorem h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ))
    (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
    (h_pos :
        (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by
  have h_sum_strict :
      (1 : ℝ) / Real.sqrt (2) <
        ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by sorry
  have h_int_big_strict :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by sorry
  have h_int_12_strict :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by sorry
  exact h_int_12_strict
```

## 20 h_eq_h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 13:35:05,833 logs/variance_r3_20260905_074359.log:242261

```lean
theorem h_eq_h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ((∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h_int1 : IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume 1 2 := by sorry
  have h_int2 : IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume 2 10000 := by sorry
  have h_add := by sorry
  simpa using h_add
```

## 21 h_eq_h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 13:38:50,489 logs/variance_r3_20260905_074359.log:244893

```lean
theorem h_eq_h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ((∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  -- integrability of the integrand on the first sub‑interval
  have h_int1 :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume (1 : ℝ) 2 := by sorry
  -- integrability of the integrand on the second sub‑interval
  have h_int2 :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume (2 : ℝ) 10000 := by sorry
  -- additivity of the integral over adjacent intervals
  have h_add := by sorry
  simpa using h_add
```

## 22 h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 13:45:25,190 logs/variance_r3_20260905_074359.log:257956

```lean
theorem h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ))
    (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
    (h_pos :
        (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by
  have h_sum_strict :
      (1 : ℝ) / Real.sqrt (2) <
        ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by sorry
  have h_int_big_strict :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by sorry
  have h_int_12_strict :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by sorry
  exact h_int_12_strict
```

## 23 h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 13:55:15,136 logs/variance_r3_20260905_074359.log:260926

```lean
theorem h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ))
    (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
    (h_pos :
        (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by
  have h_sum_strict :
      (1 : ℝ) / Real.sqrt (2) <
        ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by sorry
  have h_int_big_strict :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by sorry
  have h_int_12_strict :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by sorry
  exact h_int_12_strict
```

## 24 h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 14:27:41,632 logs/variance_r3_20260905_074359.log:267523

```lean
theorem h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
  (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ))
  (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
  (h_pos :
        (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x)
  (h_int_big_strict :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2)) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by
  -- 1.  Pointwise antitone inequality on the interval [1,2].
  have h_pointwise :
      ∀ x ∈ Set.Icc (1 : ℝ) (2 : ℝ),
        (1 : ℝ) / Real.sqrt (2) ≤ (1 : ℝ) / Real.sqrt x := by sorry
  -- 2.  From the pointwise inequality we obtain non‑negativity of the difference.
  have h_diff_nonneg :
      ∀ x ∈ Set.Icc (1 : ℝ) (2 : ℝ),
        0 ≤ ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) := by sorry
  -- 3.  The integral of a non‑negative function on a closed interval is non‑negative.
  have h_int_nonneg :
      0 ≤ ∫ x in (1 : ℝ)..2,
            ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) := by sorry
  -- 4.  Compute the integral of the constant function `1/√2` on `[1,2]`.
  have h_int_const :
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2) = (1 : ℝ) / Real.sqrt (2) := by sorry
  -- 5.  Rewrite the integral of the difference as the difference of integrals.
  have h_int_sub :
      ∫ x in (1 : ℝ)..2,
          ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) =
        (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) -
        (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2)) := by sorry
  -- 6.  From the non‑negativity of the integral of the difference we obtain a
  --     weak inequality between the desired integral and `1/√2`.
  have h_ge :
      (1 : ℝ) / Real.sqrt (2) ≤ ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  -- 7.  The inequality is in fact strict, because the function is not constant
  --     on `[1,2]`.  We prove that the two sides cannot be equal.
  have h_ne :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) ≠ (1 : ℝ) / Real.sqrt (2) := by sorry
  -- 8.  Combine the weak inequality and the fact that equality cannot hold
  --     to obtain the desired strict inequality.
  have h_strict :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by sorry
  exact h_strict
```

## 25 h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 14:47:07,039 logs/variance_r3_20260905_074359.log:281581

```lean
theorem h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_int_big_strict :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2)) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) ≠ (1 : ℝ) / Real.sqrt (2) := by
  -- continuity of the antiderivative on the interval
  have hF_cont :
      ContinuousOn (fun x : ℝ => (2 : ℝ) * Real.sqrt x) (Icc (1 : ℝ) 2) := by sorry
  -- derivative of the antiderivative on the open interval
  have hF_deriv :
      ∀ x ∈ Ioo (1 : ℝ) 2,
        HasDerivAt (fun x => (2 : ℝ) * Real.sqrt x) (1 / Real.sqrt x) x := by sorry
  -- integral equals the difference of the antiderivative at the bounds
  have h_int_eq :
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x =
        (2 : ℝ) * Real.sqrt 2 - (2 : ℝ) * Real.sqrt 1 := by sorry
  -- simplify the right‑hand side using `sqrt 1 = 1`
  have h_int_simpl :
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x = (2 : ℝ) * Real.sqrt 2 - 2 := by sorry
  -- the evaluated integral is not equal to `1 / sqrt 2`
  have h_not_eq :
      (2 : ℝ) * Real.sqrt 2 - 2 ≠ (1 : ℝ) / Real.sqrt 2 := by sorry
  -- conclude by contradiction
  intro h_eq_int
  have : (2 : ℝ) * Real.sqrt 2 - 2 = (1 : ℝ) / Real.sqrt 2 := by sorry
  exact h_not_eq this
```

## 26 h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 15:08:45,694 logs/variance_r3_20260905_074359.log:289113

```lean
theorem h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_int_big_strict :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2)) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) ≠ (1 : ℝ) / Real.sqrt (2) := by
  have hF_cont :
      ContinuousOn (fun x : ℝ => (2 : ℝ) * Real.sqrt x) (Set.Icc (1 : ℝ) 2) := by sorry
  have hF_deriv :
      ∀ x ∈ Set.Ioo (1 : ℝ) 2,
        HasDerivAt (fun x => (2 : ℝ) * Real.sqrt x) (1 / Real.sqrt x) x := by sorry
  have h_int_eq :
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x =
        (2 : ℝ) * Real.sqrt 2 - (2 : ℝ) * Real.sqrt 1 := by sorry
  have h_int_simpl :
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x = (2 : ℝ) * Real.sqrt 2 - 2 := by sorry
  have h_not_eq :
      (2 : ℝ) * Real.sqrt 2 - 2 ≠ (1 : ℝ) / Real.sqrt 2 := by sorry
  intro h_eq_int
  have h_eq' :
      (2 : ℝ) * Real.sqrt 2 - 2 = (1 : ℝ) / Real.sqrt 2 := by sorry
  exact h_not_eq h_eq'
```

## 27 h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 15:32:00,580 logs/variance_r3_20260905_074359.log:291803

```lean
theorem h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_int_big_strict :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2)) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) ≠ (1 : ℝ) / Real.sqrt (2) := by
  have hF_cont :
      ContinuousOn (fun x : ℝ => (2 : ℝ) * Real.sqrt x) (Set.Icc (1 : ℝ) 2) := by sorry
  have hF_deriv :
      ∀ x ∈ Set.Ioo (1 : ℝ) 2,
        HasDerivAt (fun x => (2 : ℝ) * Real.sqrt x) (1 / Real.sqrt x) x := by sorry
  have h_int_eq :
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x =
        (2 : ℝ) * Real.sqrt 2 - (2 : ℝ) * Real.sqrt 1 := by sorry
  have h_int_simpl :
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x = (2 : ℝ) * Real.sqrt 2 - 2 := by sorry
  have h_not_eq :
      (2 : ℝ) * Real.sqrt 2 - 2 ≠ (1 : ℝ) / Real.sqrt 2 := by sorry
  intro h_eq_int
  have h_eq' :
      (2 : ℝ) * Real.sqrt 2 - 2 = (1 : ℝ) / Real.sqrt 2 := by sorry
  exact h_not_eq h_eq'
```

## 28 h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 15:54:51,270 logs/variance_r3_20260905_074359.log:303412

```lean
theorem h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_int_big_strict :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2)) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) ≠ (1 : ℝ) / Real.sqrt (2) := by
  have hF_deriv :
      ∀ x ∈ Set.Icc (1 : ℝ) 2,
        HasDerivAt (fun y => (2 : ℝ) * Real.sqrt y) (1 / Real.sqrt x) x := by sorry
  have h_int_eq :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) = (2 : ℝ) * Real.sqrt 2 - 2 := by sorry
  have h_sqrt_lt :
      Real.sqrt (2 : ℝ) < (3 : ℝ) / 2 := by sorry
  have h_lt :
      (1 : ℝ) / Real.sqrt 2 < (2 : ℝ) * Real.sqrt 2 - 2 := by sorry
  exact ne_of_gt h_lt
```
## 1 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 08:12:16,688 logs/bugfix_000_20260902_074416.log:5287

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k ∈ Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  have h_integral_eq :
      (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) =
        (2 * (Real.sqrt (10000) - Real.sqrt (1))) := by sorry
  have h_integral_val :
      (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by sorry
  have h_sum_le_integral :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) := by sorry
  have h_lt :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by sorry
  exact h_lt
```

## 2 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 08:31:42,429 logs/bugfix_000_20260902_074416.log:15860

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k ∈ Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  have h_integral_eq :
      (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) =
        (2 * (Real.sqrt (10000) - Real.sqrt (1))) := by sorry
  have h_integral_val :
      (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by sorry
  have h_sum_lt_integral :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) := by sorry
  have h_lt :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by sorry
  exact h_lt
```

## 3 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 09:12:11,159 logs/bugfix_000_20260902_074416.log:29496

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k ∈ Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  have h_integral_eq :
      (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) =
        (2 * (Real.sqrt (10000) - Real.sqrt (1))) := by sorry
  have h_integral_val :
      (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by sorry
  have h_sum_lt_integral :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) := by sorry
  have h_lt :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by sorry
  exact h_lt
```

## 4 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 09:14:17,715 logs/bugfix_000_20260902_074416.log:31152

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k ∈ Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1. Compare each term with the integral over the preceding unit interval
  have h1 :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        (1 / Real.sqrt (2 : ℝ)) + ∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 2. Compute the integral explicitly
  have h2 :
      ∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) = 200 - 2 * Real.sqrt (2 : ℝ) := by sorry
  -- 3. Substitute the value of the integral and simplify the right‑hand side
  have h3 :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        200 - (3 * Real.sqrt (2 : ℝ)) / 2 := by sorry
  -- 4. Show that the obtained bound is already below 198
  have h4 : (200 - (3 * Real.sqrt (2 : ℝ)) / 2) < (198 : ℝ) := by sorry
  -- 5. Conclude the original inequality
  exact lt_of_lt_of_le h3 (le_of_lt h4)
```

## 5 h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 10:44:35,778 logs/bugfix_000_20260902_074416.log:73434

```lean
theorem h3_algebra_sum1onsqrt2to1onsqrt10000lt198 (h2 :
    ∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) = 200 - 2 * Real.sqrt (2 : ℝ)) :
    (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      200 - (3 * Real.sqrt (2 : ℝ)) / 2 := by
  -- Define the decreasing function
  let f : ℝ → ℝ := fun x => (1 : ℝ) / Real.sqrt x
  -- It is antitone on the interval [2,10000]
  have hf_antitone : AntitoneOn f (Set.Icc (2 : ℝ) (10000 : ℝ)) := by sorry
  -- Sum of right‑hand endpoints is ≤ the integral
  have hsum_le_int :
      (∑ k ∈ Finset.Ico (1 : ℕ) 10000, f (k + 1)) ≤
        ∫ x in (2 : ℝ)..(10000 : ℝ), f x := by sorry
  -- In fact the inequality is strict because the function is strictly decreasing
  have hstrict :
      (∑ k ∈ Finset.Ico (1 : ℕ) 10000, f (k + 1)) <
        ∫ x in (2 : ℝ)..(10000 : ℝ), f x := by sorry
  -- Rewrite the given integral value in terms of `f`
  have h_int_val :
      (∫ x in (2 : ℝ)..(10000 : ℝ), f x) = 200 - 2 * Real.sqrt (2 : ℝ) := by sorry
  -- Simplify the right‑hand side after adding the first term `f 2`
  have h_rhs :
      f (2) + (∫ x in (2 : ℝ)..(10000 : ℝ), f x) = 200 - (3 * Real.sqrt (2 : ℝ)) / 2 := by sorry
  -- Relate the `Ico` sum to the `Icc` sum appearing in the statement
  have hsum_eq :
      (∑ k ∈ Finset.Ico (1 : ℕ) 10000, f (k + 1)) =
        ∑ k ∈ Finset.Icc (2 : ℕ) 10000, f k := by sorry
  -- Conclude the desired strict inequality
  have : (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        200 - (3 * Real.sqrt (2 : ℝ)) / 2 := by sorry
  exact this
```

## 6 h2_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 10:46:38,944 logs/bugfix_000_20260902_074416.log:75261

```lean
theorem h2_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) = 200 - 2 * Real.sqrt (2 : ℝ) := by
  -- rewrite the integrand as a power function
  have h_rewrite :
      (∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x)) =
        ∫ x in (2 : ℝ)..(10000 : ℝ), x ^ (-(1/2 : ℝ)) := by sorry
  -- condition needed for `integral_rpow`
  have h_cond :
      (-(1/2 : ℝ) > -1) ∨ (-(1/2 : ℝ) ≠ -1 ∧ (0 : ℝ) ∉ [[(2 : ℝ), (10000 : ℝ)]]) := by sorry
  -- apply the power‑function integral formula
  have h_int :
      ∫ x in (2 : ℝ)..(10000 : ℝ), x ^ (-(1/2 : ℝ)) =
        ((10000 : ℝ) ^ ((-(1/2 : ℝ)) + 1) - (2 : ℝ) ^ ((-(1/2 : ℝ)) + 1)) /
          ((-(1/2 : ℝ)) + 1) := by sorry
  -- simplify the exponent `-(1/2)+1`
  have h_exp : (-(1/2 : ℝ)) + 1 = (1/2 : ℝ) := by sorry
  -- rewrite the expression using `h_exp`
  have h_simpl :
      ((10000 : ℝ) ^ ((-(1/2 : ℝ)) + 1) - (2 : ℝ) ^ ((-(1/2 : ℝ)) + 1)) /
        ((-(1/2 : ℝ)) + 1) =
        ((10000 : ℝ) ^ (1/2 : ℝ) - (2 : ℝ) ^ (1/2 : ℝ)) / (1/2 : ℝ) := by sorry
  -- evaluate `10000 ^ (1/2)`
  have h_root10000 : (10000 : ℝ) ^ (1/2 : ℝ) = 100 := by sorry
  -- evaluate `2 ^ (1/2)`
  have h_root2 : (2 : ℝ) ^ (1/2 : ℝ) = Real.sqrt (2 : ℝ) := by sorry
  -- simplify division by `1/2`
  have h_frac :
      ((10000 : ℝ) ^ (1/2 : ℝ) - (2 : ℝ) ^ (1/2 : ℝ)) / (1/2 : ℝ) =
        2 * ((10000 : ℝ) ^ (1/2 : ℝ) - (2 : ℝ) ^ (1/2 : ℝ)) := by sorry
  -- substitute the evaluated square roots and simplify
  have h_sub :
      2 * ((10000 : ℝ) ^ (1/2 : ℝ) - (2 : ℝ) ^ (1/2 : ℝ)) =
        200 - 2 * Real.sqrt (2 : ℝ) := by sorry
  -- combine all intermediate equalities
  have h_result :
      ∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) = 200 - 2 * Real.sqrt (2 : ℝ) := by sorry
  exact h_result
```

## 7 h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 11:11:05,122 logs/bugfix_000_20260902_074416.log:84162

```lean
theorem h3_algebra_sum1onsqrt2to1onsqrt10000lt198 (h2 :
    ∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) = 200 - 2 * Real.sqrt (2 : ℝ)) :
    (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      200 - (3 * Real.sqrt (2 : ℝ)) / 2 := by
  -- define the decreasing function
  let f : ℝ → ℝ := fun x => (1 : ℝ) / Real.sqrt x
  -- it is antitone on the interval [2,10000]
  have hf_antitone : AntitoneOn f (Set.Icc (2 : ℝ) (10000 : ℝ)) := by sorry
  -- sum of right‑hand endpoints is ≤ the integral
  have hsum_le_int :
      (∑ k ∈ Finset.Ico (1 : ℕ) 10000, f (k + 1)) ≤
        ∫ x in (2 : ℝ)..(10000 : ℝ), f x := by sorry
  -- the inequality is strict because the function is strictly decreasing
  have hstrict :
      (∑ k ∈ Finset.Ico (1 : ℕ) 10000, f (k + 1)) <
        ∫ x in (2 : ℝ)..(10000 : ℝ), f x := by sorry
  -- rewrite the given integral value in terms of `f`
  have h_int_val :
      (∫ x in (2 : ℝ)..(10000 : ℝ), f x) = 200 - 2 * Real.sqrt (2 : ℝ) := by sorry
  -- simplify the right‑hand side after adding the first term `f 2`
  have h_rhs :
      f 2 + (∫ x in (2 : ℝ)..(10000 : ℝ), f x) = 200 - (3 * Real.sqrt (2 : ℝ)) / 2 := by sorry
  -- relate the `Ico` sum to the `Icc` sum appearing in the statement
  have hsum_eq :
      (∑ k ∈ Finset.Ico (1 : ℕ) 10000, f (k + 1)) =
        ∑ k ∈ Finset.Icc (2 : ℕ) 10000, f k := by sorry
  -- conclude the desired strict inequality
  have : (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        200 - (3 * Real.sqrt (2 : ℝ)) / 2 := by sorry
  exact this
```

## 8 h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 11:13:19,425 logs/bugfix_000_20260902_074416.log:85845

```lean
theorem h3_algebra_sum1onsqrt2to1onsqrt10000lt198 (h2 :
    ∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) = 200 - 2 * Real.sqrt (2 : ℝ)) :
    (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      200 - (3 * Real.sqrt (2 : ℝ)) / 2 := by
  -- monotonicity of the function x ↦ 1/√x on the interval [2,10000]
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2:ℝ) (10000:ℝ)) := by sorry
  -- split the sum into the first term and the remaining tail
  have h_sum_split :
      (∑ k ∈ Finset.Icc (2:ℕ) 10000, (1:ℝ) / Real.sqrt k) =
        (1 / Real.sqrt (2:ℝ)) + ∑ k ∈ Finset.Icc 3 10000, (1:ℝ) / Real.sqrt k := by sorry
  -- the tail is strictly smaller than the integral of the decreasing function
  have h_tail_lt :
      (∑ k ∈ Finset.Icc 3 10000, (1:ℝ) / Real.sqrt k) <
        ∫ x in (2:ℝ)..(10000:ℝ), (1 / Real.sqrt x) := by sorry
  -- rewrite the integral using the given equality
  have h_integral_val :
      ∫ x in (2:ℝ)..(10000:ℝ), (1 / Real.sqrt x) = 200 - 2 * Real.sqrt (2:ℝ) := by sorry
  -- combine the split and the tail bound
  have h_comb :
      (∑ k ∈ Finset.Icc (2:ℕ) 10000, (1:ℝ) / Real.sqrt k) <
        (1 / Real.sqrt (2:ℝ)) + ∫ x in (2:ℝ)..(10000:ℝ), (1 / Real.sqrt x) := by sorry
  -- substitute the explicit value of the integral
  have h_comb2 :
      (∑ k ∈ Finset.Icc (2:ℕ) 10000, (1:ℝ) / Real.sqrt k) <
        (1 / Real.sqrt (2:ℝ)) + (200 - 2 * Real.sqrt (2:ℝ)) := by sorry
  -- simplify the right‑hand side to the target expression
  have h_final :
      (1 / Real.sqrt (2:ℝ)) + (200 - 2 * Real.sqrt (2:ℝ)) =
        200 - (3 * Real.sqrt (2:ℝ)) / 2 := by sorry
  -- conclude
  simpa [h_final] using h_comb2
```

## 9 h_sum_split_h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 12:15:35,644 logs/bugfix_000_20260902_074416.log:142746

```lean
theorem h_sum_split_h3_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
      (1 / Real.sqrt (2 : ℝ)) + ∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by
  -- 2 does not belong to the interval [3,10000]
  have h_not_mem : (2 : ℕ) ∉ Finset.Icc 3 10000 := by sorry
  -- The interval [2,10000] is the insertion of 2 into [3,10000]
  have h_eq : (Finset.Icc (2 : ℕ) 10000) = Finset.insert 2 (Finset.Icc 3 10000) := by sorry
  -- Rewrite the original sum using the equality of finsets and split it with `sum_insert`
  simpa [h_eq, Finset.sum_insert h_not_mem]
```

## 10 h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 12:17:03,386 logs/bugfix_000_20260902_074416.log:145414

```lean
theorem h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      200 - (3 * Real.sqrt (2 : ℝ)) / 2 := by
  /- 1.  Positivity of √2 -/
  have h_pos_sqrt2 : (0 : ℝ) < Real.sqrt (2 : ℝ) := by sorry
  /- 2.  Value of the integral ∫_{2}^{10000} 1/√x dx -/
  have h_int_val :
      (∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x) = 200 - 2 * Real.sqrt (2 : ℝ) := by sorry
  /- 3.  Bounding the finite sum by the first term plus the integral -/
  have h_sum_lt :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        (1 / Real.sqrt (2 : ℝ)) + (∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x) := by sorry
  /- 4.  Simplifying the right‑hand side -/
  have h_rhs_simpl :
      (1 / Real.sqrt (2 : ℝ)) + (200 - 2 * Real.sqrt (2 : ℝ)) =
        200 - (3 * Real.sqrt (2 : ℝ)) / 2 := by sorry
  /- 5.  Putting everything together -/
  have h_final :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        200 - (3 * Real.sqrt (2 : ℝ)) / 2 := by sorry
  exact h_final
```

## 11 h_result_h2_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 12:19:23,319 logs/bugfix_000_20260902_074416.log:147505

```lean
theorem h_result_h2_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x)) = 200 - 2 * Real.sqrt (2 : ℝ) := by
  have h_deriv :
      ∀ x ∈ uIcc (2 : ℝ) 10000,
        HasDerivAt (fun y => (2 : ℝ) * Real.sqrt y) (1 / Real.sqrt x) x := by sorry
  have h_int :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume (2 : ℝ) 10000 := by sorry
  have h_eq :
      (∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x)) =
        (2 : ℝ) * Real.sqrt (10000 : ℝ) - (2 : ℝ) * Real.sqrt (2 : ℝ) := by sorry
  have h_sqrt10000 :
      Real.sqrt (10000 : ℝ) = (100 : ℝ) := by sorry
  have h_two_mul_sqrt10000 :
      (2 : ℝ) * Real.sqrt (10000 : ℝ) = (200 : ℝ) := by sorry
  simpa [h_two_mul_sqrt10000] using h_eq
```

## 12 h_sum_split_h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 12:21:55,750 logs/bugfix_000_20260902_074416.log:154399

```lean
theorem h_sum_split_h3_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
      (1 / Real.sqrt (2 : ℝ)) + ∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by
  -- 2 ≤ 10000, needed for interval lemmas
  have h_le : (2 : ℕ) ≤ 10000 := by sorry
  -- Difference between the closed interval and the open‑closed interval is the singleton {2}
  have h_diff :
      Finset.Icc (2 : ℕ) 10000 \ Finset.Ioc (2 : ℕ) 10000 = ({2} : Finset ℕ) := by sorry
  -- The open‑closed interval Ioc (2,10000) coincides with Icc (3,10000)
  have h_Ioc_eq : Finset.Ioc (2 : ℕ) 10000 = Finset.Icc 3 10000 := by sorry
  -- Hence the closed interval Icc (2,10000) is the union of the singleton {2} and Icc (3,10000)
  have h_decomp :
      Finset.Icc (2 : ℕ) 10000 = ({2} : Finset ℕ) ∪ Finset.Icc 3 10000 := by sorry
  -- Split the sum over the union into two separate sums (the sets are disjoint)
  have h_sum_union :
      ∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k =
        ∑ k ∈ ({2} : Finset ℕ), (1 : ℝ) / Real.sqrt k +
        ∑ k ∈ Finset.Icc 3 10000, (1 : ℝ) / Real.sqrt k := by sorry
  -- Evaluate the singleton sum
  have h_singleton :
      ∑ k ∈ ({2} : Finset ℕ), (1 : ℝ) / Real.sqrt k = (1 : ℝ) / Real.sqrt 2 := by sorry
  -- Assemble the pieces
  simpa [h_singleton, add_comm] using h_sum_union
```

## 13 h_tail_lt_h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 12:22:45,361 logs/bugfix_000_20260902_074416.log:156249

```lean
theorem h_tail_lt_h3_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      ∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by
  -- 1.  The integrand is antitone on the interval [2,10000].
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) (10000 : ℝ)) := by sorry
  -- 2.  The integrand is integrable on the same interval.
  have h_integrable :
      IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) (10000 : ℝ)) := by sorry
  -- 3.  Rewrite the finite sum as a sum over `Finset.Ico 2 10000` of the shifted term.
  have h_sum_eq :
      (∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
        ∑ i ∈ Finset.Ico (2 : ℕ) 10000,
          (1 : ℝ) / Real.sqrt (i + 1) := by sorry
  -- 4.  Establish the pointwise domination needed for `sum_Ico_le_integral_of_le`.
  have h_dom :
      ∀ i ∈ Finset.Ico (2 : ℕ) 10000,
        ∀ x ∈ Set.Ico (i : ℝ) (i + 1 : ℝ),
          (1 : ℝ) / Real.sqrt (i + 1) ≤ (1 : ℝ) / Real.sqrt x := by sorry
  -- 5.  Apply `sum_Ico_le_integral_of_le` to obtain a non‑strict inequality.
  have h_le :
      (∑ i ∈ Finset.Ico (2 : ℕ) 10000,
          (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 6.  Combine the equalities to get the desired ≤ inequality for the original sum.
  have h_le_original :
      (∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 7.  Show that equality cannot hold, because the integrand is strictly decreasing.
  have h_ne :
      (∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≠
        ∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 8.  Conclude the strict inequality from `≤` and `≠`.
  have h_lt :
      (∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  exact h_lt
```

## 14 h_int_val_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 12:47:41,221 logs/bugfix_000_20260902_074416.log:175720

```lean
theorem h_int_val_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x) = 200 - 2 * Real.sqrt (2 : ℝ) := by
  -- continuity of the antiderivative on the interval
  have h_cont :
      ContinuousOn (fun x : ℝ => (2 : ℝ) * Real.sqrt x) (Set.Icc (2 : ℝ) 10000) := by sorry
  -- derivative of the antiderivative on the interior
  have h_deriv :
      ∀ x ∈ Set.Ioo (2 : ℝ) 10000,
        HasDerivAt (fun x : ℝ => (2 : ℝ) * Real.sqrt x) (1 / Real.sqrt x) x := by sorry
  -- integrability of the derivative on the interval
  have h_int :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume (2 : ℝ) 10000 := by sorry
  -- apply the Fundamental Theorem of Calculus
  have h_ftc :
      (∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x) =
        (2 : ℝ) * Real.sqrt 10000 - (2 : ℝ) * Real.sqrt (2 : ℝ) := by sorry
  -- compute the concrete square‑root values
  have h_sqrt10000 : Real.sqrt (10000 : ℝ) = 100 := by sorry
  -- finish the calculation
  simpa [h_sqrt10000,
        Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ (2 : ℝ))] using h_ftc
```

## 15 h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 12:54:09,723 logs/bugfix_000_20260902_074416.log:185635

```lean
theorem h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      (1 / Real.sqrt (2 : ℝ)) + (∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x) := by
  -- 1.  The function  x ↦ 1/√x  is antitone on the interval [2,10000].
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) 10000) := by sorry
  -- 2.  Its denominator is positive on the same interval.
  have h_sqrt_pos :
      ∀ x ∈ Set.Icc (2 : ℝ) 10000, 0 < Real.sqrt x := by sorry
  -- 3.  For every integer k with 3 ≤ k ≤ 10000 we have a strict pointwise inequality.
  have h_pointwise :
      ∀ k : ℕ, 3 ≤ k → k ≤ 10000 →
        (1 : ℝ) / Real.sqrt k <
          ∫ x in Set.Icc (k - 1 : ℝ) k, (1 : ℝ) / Real.sqrt x := by sorry
  -- 4.  Summing the pointwise inequalities yields a sum–integral inequality.
  have h_sum_lt_integral :
      (∑ k ∈ Finset.Icc 3 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 5.  Add the first term 1/√2 to both sides and rewrite the left‑hand side as a single sum.
  have h_final :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        (1 / Real.sqrt (2 : ℝ)) + ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x := by sorry
  exact h_final
```

## 16 h_pointwise_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 13:50:12,178 logs/bugfix_000_20260902_074416.log:235295

```lean
theorem h_pointwise_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) 10000))
    (h_sqrt_pos :
      ∀ x ∈ Set.Icc (2 : ℝ) 10000, 0 < Real.sqrt x) :
    ∀ k : ℕ, 3 ≤ k → k ≤ 10000 →
      (1 : ℝ) / Real.sqrt (k : ℝ) <
        ∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt x := by
  intro k hk3 hk10000
  -- 1. lower bound 2 ≤ k
  have h_k_ge_two : (2 : ℝ) ≤ (k : ℝ) := by sorry
  -- 2. upper bound k ≤ 10000
  have h_k_le_10000 : (k : ℝ) ≤ (10000 : ℝ) := by sorry
  -- 3. the interval [k‑1,k] is contained in [2,10000]
  have h_interval_subset :
      Set.Icc ((k : ℝ) - 1) (k : ℝ) ⊆ Set.Icc (2 : ℝ) 10000 := by sorry
  -- 4. antitone on the smaller interval
  have h_antitone_sub :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc ((k : ℝ) - 1) (k : ℝ)) := by sorry
  -- 5. pointwise inequality f(k) ≤ f(x) on the interval
  have h_pointwise :
      ∀ x ∈ Set.Icc ((k : ℝ) - 1) (k : ℝ),
        (1 : ℝ) / Real.sqrt (k : ℝ) ≤ (1 : ℝ) / Real.sqrt x := by sorry
  -- 6. integrate the pointwise inequality (non‑strict)
  have h_integral_ge :
      (∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt (k : ℝ)) ≤
        ∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 7. evaluate the integral of the constant function
  have h_integral_const :
      (∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt (k : ℝ)) =
        (1 : ℝ) / Real.sqrt (k : ℝ) := by sorry
  -- 8. strict inequality because the integrand is strictly larger on a set of positive measure
  have h_strict :
      (∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt (k : ℝ)) <
        ∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 9. rewrite the left‑hand side of the strict inequality using the constant integral
  have h_final :
      (1 : ℝ) / Real.sqrt (k : ℝ) <
        ∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  exact h_final
```

## 17 h_sum_lt_integral_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 13:52:11,008 logs/bugfix_000_20260902_074416.log:237377

```lean
theorem h_sum_lt_integral_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) 10000))
    (h_sqrt_pos :
      ∀ x ∈ Set.Icc (2 : ℝ) 10000, 0 < Real.sqrt x)
    (h_pointwise :
      ∀ k : ℕ, 3 ≤ k → k ≤ 10000 →
        (1 : ℝ) / Real.sqrt (k : ℝ) <
          ∫ x in Set.Icc (k - 1 : ℝ) (k : ℝ), (1 : ℝ) / Real.sqrt x) :
    (∑ k in Finset.Icc 3 10000, (1 : ℝ) / Real.sqrt k) <
      ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x := by
  -- 1. Lift the pointwise inequality to a statement over the finset.
  have h_pointwise_sum :
      ∀ k ∈ Finset.Icc 3 10000,
        (1 : ℝ) / Real.sqrt (k : ℝ) <
          ∫ x in Set.Icc (k - 1 : ℝ) k, (1 : ℝ) / Real.sqrt x := by sorry
  -- 2. Sum the pointwise inequalities.
  have h_sum_lt_sum_int :
      (∑ k in Finset.Icc 3 10000, (1 : ℝ) / Real.sqrt k) <
        ∑ k in Finset.Icc 3 10000,
          ∫ x in Set.Icc (k - 1 : ℝ) k, (1 : ℝ) / Real.sqrt x := by sorry
  -- 3. Replace each integral over a closed interval by the integral over the left‑open right‑closed interval.
  have h_int_eq_ioc :
      ∀ k ∈ Finset.Icc 3 10000,
        (∫ x in Set.Icc (k - 1 : ℝ) k, (1 : ℝ) / Real.sqrt x) =
          ∫ x in Set.Ioc (k - 1 : ℝ) k, (1 : ℝ) / Real.sqrt x := by sorry
  -- 4. Rewrite the sum of integrals using the equality from the previous step.
  have h_sum_eq_sum_ioc :
      (∑ k in Finset.Icc 3 10000,
          ∫ x in Set.Icc (k - 1 : ℝ) k, (1 : ℝ) / Real.sqrt x) =
        ∑ k in Finset.Icc 3 10000,
          ∫ x in Set.Ioc (k - 1 : ℝ) k, (1 : ℝ) / Real.sqrt x := by sorry
  -- 5. Show that the integral over the whole interval dominates the sum of the integrals over the partition.
  have h_int_ge_sum_ioc :
      ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x ≥
        ∑ k in Finset.Icc 3 10000,
          ∫ x in Set.Ioc (k - 1 : ℝ) k, (1 : ℝ) / Real.sqrt x := by sorry
  -- 6. Combine the previous inequalities to obtain the desired strict inequality.
  calc
    (∑ k in Finset.Icc 3 10000, (1 : ℝ) / Real.sqrt k)
        < ∑ k in Finset.Icc 3 10000,
            ∫ x in Set.Icc (k - 1 : ℝ) k, (1 : ℝ) / Real.sqrt x := h_sum_lt_sum_int
    _ = ∑ k in Finset.Icc 3 10000,
            ∫ x in Set.Ioc (k - 1 : ℝ) k, (1 : ℝ) / Real.sqrt x := h_sum_eq_sum_ioc
    _ ≤ ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x := h_int_ge_sum_ioc
```

## 18 h_final_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 13:55:03,456 logs/bugfix_000_20260902_074416.log:242198

```lean
theorem h_final_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) 10000))
    (h_sqrt_pos :
        ∀ x ∈ Set.Icc (2 : ℝ) 10000, 0 < Real.sqrt x)
    (h_pointwise :
        ∀ k : ℕ, 3 ≤ k → k ≤ 10000 →
          (1 : ℝ) / Real.sqrt (k : ℝ) <
            ∫ x in Set.Icc (k - 1 : ℝ) (k : ℝ), (1 : ℝ) / Real.sqrt x)
    (h_sum_lt_integral :
        (∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
          ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x) :
    (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      (1 / Real.sqrt (2 : ℝ)) + ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x :=
by
  have h_not_mem : (2 : ℕ) ∉ Finset.Icc 3 10000 := by sorry
  have h_sum_decomp :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
        (1 : ℝ) / Real.sqrt (2 : ℝ) +
          ∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by sorry
  have h_ineq :
      (1 : ℝ) / Real.sqrt (2 : ℝ) +
        ∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k
        < (1 : ℝ) / Real.sqrt (2 : ℝ) +
          ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x := by sorry
  simpa [h_sum_decomp] using h_ineq
```

## 19 h_sum_lt_integral_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 13:57:09,308 logs/bugfix_000_20260902_074416.log:246930

```lean
theorem h_sum_lt_integral_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) 10000))
    (h_sqrt_pos :
      ∀ x ∈ Set.Icc (2 : ℝ) 10000, 0 < Real.sqrt x)
    (h_pointwise :
      ∀ k : ℕ, 3 ≤ k → k ≤ 10000 →
        (1 : ℝ) / Real.sqrt (k : ℝ) <
          ∫ x in Set.Icc (k - 1 : ℝ) (k : ℝ), (1 : ℝ) / Real.sqrt x) :
    (∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x := by
  -- 1. Turn the pointwise strict inequality into a strict inequality of sums.
  have h_sum_lt :
      (∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∑ k ∈ Finset.Icc (3 : ℕ) 10000,
          ∫ x in Set.Icc (k - 1 : ℝ) (k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 2. Show that the sum of the integrals telescopes to the integral over the whole interval.
  have h_sum_integral_eq :
      (∑ k ∈ Finset.Icc (3 : ℕ) 10000,
          ∫ x in Set.Icc (k - 1 : ℝ) (k : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 3. Combine the two previous facts to obtain the desired inequality.
  simpa [h_sum_integral_eq] using h_sum_lt
```

## 20 h_final_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 13:59:46,430 logs/bugfix_000_20260902_074416.log:251336

```lean
theorem h_final_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) 10000))
    (h_sqrt_pos :
      ∀ x ∈ Set.Icc (2 : ℝ) 10000, 0 < Real.sqrt x)
    (h_pointwise :
      ∀ k : ℕ, 3 ≤ k → k ≤ 10000 →
        (1 : ℝ) / Real.sqrt (k : ℝ) <
          ∫ x in Set.Icc (k - 1 : ℝ) (k : ℝ), (1 : ℝ) / Real.sqrt x)
    (h_sum_lt_integral :
      (∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x) :
    (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      (1 / Real.sqrt (2 : ℝ)) + ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x := by
  -- rewrite the sum over 2…10000 as the term for k=2 plus the sum over 3…10000
  have h_sum_eq :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
        (1 : ℝ) / Real.sqrt 2 + ∑ k ∈ Finset.Icc 3 10000, (1 : ℝ) / Real.sqrt k := by sorry
  -- add the non‑negative constant 1/√2 to the inequality given by `h_sum_lt_integral`
  have h_lt :
      (1 : ℝ) / Real.sqrt 2 + ∑ k ∈ Finset.Icc 3 10000, (1 : ℝ) / Real.sqrt k <
        (1 : ℝ) / Real.sqrt 2 + ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- combine the two previous facts
  have h_final :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        (1 : ℝ) / Real.sqrt 2 + ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x := by sorry
  exact h_final
```

## 21 h_sum_lt_integral_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 14:00:10,747 logs/bugfix_000_20260902_074416.log:251796

```lean
theorem h_sum_lt_integral_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) 10000))
    (h_sqrt_pos :
        ∀ x ∈ Set.Icc (2 : ℝ) 10000, 0 < Real.sqrt x)
    (h_pointwise :
        ∀ k : ℕ, 3 ≤ k → k ≤ 10000 →
          (1 : ℝ) / Real.sqrt (k : ℝ) <
            ∫ x in Set.Icc (k - 1 : ℝ) (k : ℝ), (1 : ℝ) / Real.sqrt x) :
    (∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x := by
  -- measurability of each small interval
  have h_meas :
      ∀ k ∈ Finset.Icc (3 : ℕ) 10000,
        MeasurableSet (Set.Icc ((k : ℝ) - 1) (k : ℝ)) := by sorry
  -- pairwise disjointness of the intervals
  have h_disjoint :
      Pairwise (Disjoint on fun k : ℕ => Set.Icc ((k : ℝ) - 1) (k : ℝ)) := by sorry
  -- union of the intervals equals the big interval [2,10000]
  have h_union_eq :
      (⋃ k ∈ (Finset.Icc (3 : ℕ) 10000),
          Set.Icc ((k : ℝ) - 1) (k : ℝ)) = Set.Icc (2 : ℝ) 10000 := by sorry
  -- rewrite the integral over [2,10000] as a sum of integrals over the small intervals
  have h_integral_eq_sum :
      (∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x) =
        ∑ k in Finset.Icc (3 : ℕ) 10000,
          ∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- sum of pointwise inequalities gives a strict inequality between the two sums
  have h_sum_lt_sum_integral :
      (∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∑ k in Finset.Icc (3 : ℕ) 10000,
          ∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- combine the previous equalities/inequalities to obtain the final goal
  have h_goal :
      (∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x := by sorry
  exact h_goal
```

## 22 h_sum_lt_integral_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 14:09:28,990 logs/bugfix_000_20260902_074416.log:267661

```lean
theorem h_sum_lt_integral_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) 10000))
    (h_sqrt_pos :
      ∀ x ∈ Set.Icc (2 : ℝ) 10000, 0 < Real.sqrt x)
    (h_pointwise :
      ∀ k : ℕ, 3 ≤ k → k ≤ 10000 →
        (1 : ℝ) / Real.sqrt (k : ℝ) <
          ∫ x in Set.Icc (k - 1 : ℝ) (k : ℝ), (1 : ℝ) / Real.sqrt x) :
    (∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x := by
  -- 1.  Sum of the pointwise strict inequalities.
  have h_sum_lt :
      (∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∑ k ∈ Finset.Icc (3 : ℕ) 10000,
          ∫ x in Set.Icc (k - 1 : ℝ) (k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 2.  Replace the sum of integrals by a single integral over `[2,10000]`.
  have h_integral_eq :
      (∑ k ∈ Finset.Icc (3 : ℕ) 10000,
          ∫ x in Set.Icc (k - 1 : ℝ) (k : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∫ x in Set.Icc (2 : ℝ) 10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 3.  Conclude the desired strict inequality.
  exact (lt_of_lt_of_eq h_sum_lt h_integral_eq.symm)
```

## 23 h_sum_lt_h_sum_lt_integral_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 14:31:35,205 logs/bugfix_000_20260902_074416.log:302672

```lean
theorem h_sum_lt_h_sum_lt_integral_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198
  (h_antitone :
    AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) (10000 : ℝ)))
  (h_sqrt_pos :
    ∀ x ∈ Set.Icc (2 : ℝ) (10000 : ℝ), 0 < Real.sqrt x)
  (h_pointwise :
    ∀ k : ℕ, 3 ≤ k → k ≤ 10000 →
      (1 : ℝ) / Real.sqrt (k : ℝ) <
        ∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt x) :
    (∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      ∫ x in Set.Icc (2 : ℝ) (10000 : ℝ), (1 : ℝ) / Real.sqrt x := by
  -- 1.  Sum of the pointwise strict inequalities.
  have h_sum_lt :
      (∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∑ k ∈ Finset.Icc (3 : ℕ) 10000,
          ∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 2.  Replace the sum of integrals by a single integral over `[2,10000]`.
  have h_integral_eq :
      (∑ k ∈ Finset.Icc (3 : ℕ) 10000,
          ∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt x) =
        ∫ x in Set.Icc (2 : ℝ) (10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 3.  Conclude the desired strict inequality.
  exact lt_of_lt_of_eq h_sum_lt h_integral_eq
```

## 24 h_pointwise_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 14:34:27,869 logs/bugfix_000_20260902_074416.log:308409

```lean
theorem h_pointwise_h_sum_lt_h_goal_h3_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) 10000))
    (h_sqrt_pos :
      ∀ x ∈ Set.Icc (2 : ℝ) 10000, 0 < Real.sqrt x) :
    ∀ k : ℕ, 3 ≤ k → k ≤ 10000 →
      (1 : ℝ) / Real.sqrt (k : ℝ) <
        ∫ x in Set.Icc (k - 1 : ℝ) (k : ℝ), (1 : ℝ) / Real.sqrt x := by
  intro k hk3 hk10000
  -- 1. lower bound 2 ≤ k
  have h_k_ge_two : (2 : ℝ) ≤ (k : ℝ) := by sorry
  -- 2. upper bound k ≤ 10000
  have h_k_le_10000 : (k : ℝ) ≤ (10000 : ℝ) := by sorry
  -- 3. the interval [k‑1,k] is contained in [2,10000]
  have h_interval_subset :
      Set.Icc ((k : ℝ) - 1) (k : ℝ) ⊆ Set.Icc (2 : ℝ) 10000 := by sorry
  -- 4. antitone on the smaller interval
  have h_antitone_sub :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc ((k : ℝ) - 1) (k : ℝ)) := by sorry
  -- 5. pointwise inequality f(k) ≤ f(x) on the interval
  have h_pointwise :
      ∀ x ∈ Set.Icc ((k : ℝ) - 1) (k : ℝ),
        (1 : ℝ) / Real.sqrt (k : ℝ) ≤ (1 : ℝ) / Real.sqrt x := by sorry
  -- 6. integrate the pointwise inequality (non‑strict)
  have h_integral_ge :
      (∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt (k : ℝ)) ≤
        ∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 7. evaluate the integral of the constant function
  have h_integral_const :
      (∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt (k : ℝ)) =
        (1 : ℝ) / Real.sqrt (k : ℝ) := by sorry
  -- 8. strict inequality because the integrand is strictly larger on a set of positive measure
  have h_strict :
      (∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt (k : ℝ)) <
        ∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 9. rewrite the left‑hand side of the strict inequality using the constant integral
  have h_final :
      (1 : ℝ) / Real.sqrt (k : ℝ) <
        ∫ x in Set.Icc ((k : ℝ) - 1) (k : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  exact h_final
```

## 25 h_le_h_tail_lt_h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 14:38:40,909 logs/bugfix_000_20260902_074416.log:314424

```lean
theorem h_le_h_tail_lt_h3_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ i ∈ Finset.Ico (2 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt (i + 1)) ≤
      ∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) :=
by
  -- 1️⃣  Show that the function `x ↦ 1 / √x` is antitone on the interval `[2,10000]`.
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) 10000) := by sorry
  -- 2️⃣  Record the obvious ordering of the endpoints.
  have h_hab : (2 : ℝ) ≤ 10000 := by sorry
  -- 3️⃣  Apply the comparison lemma for antitone functions.
  have h_le :
      (∑ i ∈ Finset.Ico (2 : ℕ) 10000,
          (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 4️⃣  Conclude the desired inequality.
  exact h_le
```

## 26 h_le_original_h_tail_lt_h3_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-02 14:47:45,507 logs/bugfix_000_20260902_074416.log:326750

```lean
theorem h_le_original_h_tail_lt_h3_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
      ∫ x in (2 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) :=
by
  have h_sum_eq :
      (∑ k ∈ Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
        ∑ i ∈ Finset.Ico (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1) := by sorry
  have h_hab : (2 : ℝ) ≤ 10000 := by sorry
  have h_pointwise :
      ∀ i ∈ Finset.Ico (2 : ℕ) 10000,
        ∀ x ∈ Ico (i : ℝ) (i + 1 : ℝ),
          (1 : ℝ) / Real.sqrt (i + 1) ≤ (1 : ℝ) / Real.sqrt x := by sorry
  have h_integrable :
      IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Ico (2 : ℝ) (10000 : ℝ)) := by sorry
  have h_le_sum :
      (∑ i ∈ Finset.Ico (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (2 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  simpa [h_sum_eq] using h_le_sum
```
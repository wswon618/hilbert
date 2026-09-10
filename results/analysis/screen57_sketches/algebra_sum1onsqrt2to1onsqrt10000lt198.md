# algebra_sum1onsqrt2to1onsqrt10000lt198

## Original input

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by

```

## Snapshot 1 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-08 09:35:09,150 [log](../../../logs/screen57_20260907_021530.log:923608)

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1.  The function x ↦ 1/√x is antitone on [1,10000].
  have h_antitone : AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000) := by sorry
  -- 2.  Compute the integral of 1/√x from 1 to 10000.
  have h_int_val : (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by sorry
  -- 3.  The sum over the integer points is bounded above by the integral.
  have h_sum_le_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 4.  Because the function is strictly decreasing, the inequality is strict.
  have h_sum_lt_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 5.  Combine the strict inequality with the computed integral value.
  have h_sum_lt_198 :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by sorry
  exact h_sum_lt_198
```

## Snapshot 2 h_int_val_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-08 10:28:14,969 [log](../../../logs/screen57_20260907_021530.log:978690)

```lean
theorem h_int_val_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by
  -- 1. Rewrite the integrand using `Real.sqrt_eq_rpow`.
  have h_rewrite :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
        ∫ x in (1 : ℝ)..10000, (x : ℝ) ^ (-(1 / 2 : ℝ)) := by sorry
  -- 2. Apply the power‑integral formula `integral_rpow` with `r = -1/2`.
  have h_integral :
      ∫ x in (1 : ℝ)..10000, (x : ℝ) ^ (-(1 / 2 : ℝ)) =
        (10000 ^ ((-(1 / 2 : ℝ)) + 1) - (1 : ℝ) ^ ((-(1 / 2 : ℝ)) + 1)) /
          ((-(1 / 2 : ℝ)) + 1) := by sorry
  -- 3. Simplify the exponent `(-(1/2)) + 1` to `1/2` and rewrite powers as square roots.
  have h_simplify_pow :
      (10000 ^ ((-(1 / 2 : ℝ)) + 1) - (1 : ℝ) ^ ((-(1 / 2 : ℝ)) + 1)) /
        ((-(1 / 2 : ℝ)) + 1) =
        (Real.sqrt (10000 : ℝ) - Real.sqrt (1 : ℝ)) / ((1 / 2 : ℝ)) := by sorry
  -- 4. Evaluate the square roots `√10000 = 100` and `√1 = 1`.
  have h_sqrt_eval :
      Real.sqrt (10000 : ℝ) = (100 : ℝ) ∧ Real.sqrt (1 : ℝ) = (1 : ℝ) := by sorry
  -- 5. Perform the arithmetic to obtain the final value `198`.
  have h_numeric :
      (Real.sqrt (10000 : ℝ) - Real.sqrt (1 : ℝ)) / ((1 / 2 : ℝ)) = (198 : ℝ) := by sorry
  -- 6. Assemble the equalities.
  calc
    (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
        = ∫ x in (1 : ℝ)..10000, (x : ℝ) ^ (-(1 / 2 : ℝ)) := h_rewrite
    _ = (10000 ^ ((-(1 / 2 : ℝ)) + 1) - (1 : ℝ) ^ ((-(1 / 2 : ℝ)) + 1)) /
          ((-(1 / 2 : ℝ)) + 1) := h_integral
    _ = (Real.sqrt (10000 : ℝ) - Real.sqrt (1 : ℝ)) / ((1 / 2 : ℝ)) := h_simplify_pow
    _ = (198 : ℝ) := h_numeric
```

## Snapshot 3 h_sum_lt_198_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-08 10:30:44,947 [log](../../../logs/screen57_20260907_021530.log:982747)

```lean
theorem h_sum_lt_198_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by
  have h_antitone : AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000) := by sorry
  have h_sum_eq :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
        ∑ i in Finset.Ico 1 10000, (1 : ℝ) / Real.sqrt (i + 1) := by sorry
  have h_sum_le_int :
      (∑ i in Finset.Ico 1 10000, (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_int_eq :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (2 : ℝ) * (Real.sqrt 10000 - Real.sqrt 1) := by sorry
  have h_int_val : (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by sorry
  have h_lt_198 :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by sorry
  exact h_lt_198
```

## Snapshot 4 h_sum_le_int_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-08 10:36:15,035 [log](../../../logs/screen57_20260907_021530.log:994029)

```lean
theorem h_sum_le_int_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  -- rewrite the finite sum over `Icc` as a sum over `Ico`
  have h_sum_eq :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
        ∑ i in Finset.Ico 1 10000, (1 : ℝ) / Real.sqrt (i + 1) := by sorry
  -- pointwise domination of the discrete term by the continuous function
  have h_pointwise :
      ∀ i ∈ Finset.Ico 1 10000,
        ∀ x ∈ Set.Ico (i : ℝ) (i + 1),
          (1 : ℝ) / Real.sqrt (i + 1) ≤ (1 : ℝ) / Real.sqrt x := by sorry
  -- integrability of the continuous function on the interval
  have h_integrable :
      IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Ico (1 : ℝ) (10000 : ℝ)) := by sorry
  -- apply the comparison theorem `sum_Ico_le_integral_of_le`
  have h_bound :
      (∑ i in Finset.Ico 1 10000, (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- conclude using the equality of the two sums
  simpa [h_sum_eq] using h_bound
```

## Snapshot 5 h_sum_lt_198_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-08 10:37:13,634 [log](../../../logs/screen57_20260907_021530.log:995680)

```lean
theorem h_sum_lt_198_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by
  -- 1.  The function x ↦ 1/√x is antitone on the interval [1,10000].
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  -- 2.  Apply the antitone sum ≤ integral comparison for a = 1, b = 10000.
  have h_sum_le_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 3.  Compute the integral explicitly: ∫₁^{10000} 1/√x = 2·(√10000-√1) = 198.
  have h_int_eq :
      (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by sorry
  -- 4.  Show that the sum cannot be exactly 198.
  have h_ne :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≠ (198 : ℝ) := by sorry
  -- 5.  Conclude the strict inequality from the ≤ estimate and the inequality of the
  --     two sides.
  exact lt_of_le_of_ne h_sum_le_int h_ne
```

## Snapshot 6 h_rewrite_h_int_val_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-08 10:46:22,707 [log](../../../logs/screen57_20260907_021530.log:1013000)

```lean
theorem h_rewrite_h_int_val_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
      ∫ x in (1 : ℝ)..10000, (x : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have h_sqrt_eq : ∀ x : ℝ, Real.sqrt x = x ^ (1 / (2 : ℝ)) := by sorry
  have h_one_div_eq_inv : ∀ x : ℝ, (1 : ℝ) / Real.sqrt x = (Real.sqrt x)⁻¹ := by sorry
  have h_inv_eq_pow_neg : ∀ x : ℝ, (Real.sqrt x)⁻¹ = (x : ℝ) ^ (-(1 / 2 : ℝ)) := by sorry
  simpa [Real.sqrt_eq_rpow, div_eq_mul_inv, Real.rpow_neg]
```

## Snapshot 7 h_sum_lt_198_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-08 11:14:29,453 [log](../../../logs/screen57_20260907_021530.log:1045562)

```lean
theorem h_sum_lt_198_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  have h_sum_le_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  have h_int_eq :
      (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by sorry
  have h_sum_lt_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  have h_sum_lt_198 :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by sorry
  exact h_sum_lt_198
```

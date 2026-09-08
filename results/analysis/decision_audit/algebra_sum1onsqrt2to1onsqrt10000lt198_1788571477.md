## 1 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 01:43:12,457 logs/variance_r2_20260905_012324.log:3758

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1. The function x ↦ 1 / √x is antitone on [1,10000].
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000) := by sorry
  -- 2. Bounding the sum by the integral using `sum_Ico_le_integral_of_le`.
  have h_sum_le_integral :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 3. Evaluate the integral explicitly: ∫₁^{10000} 1/√x = 2·(√10000 - √1) = 198.
  have h_integral_eq :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = 198 := by sorry
  -- 4. The inequality is strict because the function is strictly decreasing.
  have h_strict :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 5. Conclude the desired inequality.
  have : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < 198 := by sorry
  exact this
```

## 2 h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 02:27:24,464 logs/variance_r2_20260905_012324.log:47375

```lean
theorem h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = 198 := by
  have h_eq :
      (fun x : ℝ => (1 : ℝ) / Real.sqrt x) = fun x => x ^ (-(1 / 2 : ℝ)) := by sorry
  have h_original :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
        ∫ x in (1 : ℝ)..10000, x ^ (-(1 / 2 : ℝ)) := by sorry
  have h_int :
      ∫ x in (1 : ℝ)..10000, x ^ (-(1 / 2 : ℝ)) =
        (10000 ^ ((-(1 / 2 : ℝ)) + 1) - (1 : ℝ) ^ ((-(1 / 2 : ℝ)) + 1)) /
          ((-(1 / 2 : ℝ)) + 1) := by sorry
  have h_val :
      (10000 ^ ((-(1 / 2 : ℝ)) + 1) - (1 : ℝ) ^ ((-(1 / 2 : ℝ)) + 1)) /
        ((-(1 / 2 : ℝ)) + 1) = (198 : ℝ) := by sorry
  calc
    (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
        = ∫ x in (1 : ℝ)..10000, x ^ (-(1 / 2 : ℝ)) := h_original
    _ = (10000 ^ ((-(1 / 2 : ℝ)) + 1) - (1 : ℝ) ^ ((-(1 / 2 : ℝ)) + 1)) /
          ((-(1 / 2 : ℝ)) + 1) := h_int
    _ = 198 := by
      simpa using h_val
```

## 3 h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 02:30:06,783 logs/variance_r2_20260905_012324.log:50825

```lean
theorem h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have hab : (1 : ℝ) ≤ (10000 : ℝ) := by sorry
  have h_sum_eq :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
        ∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1) := by sorry
  have h_pointwise :
      ∀ i ∈ Finset.Ico (1 : ℕ) 10000,
        ∀ x ∈ Set.Ico (i : ℝ) (i + 1 : ℝ),
          (1 : ℝ) / Real.sqrt (i + 1) ≤ (1 : ℝ) / Real.sqrt x := by sorry
  have h_integrable :
      IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000) := by sorry
  have h_le :
      ∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  simpa [h_sum_eq] using h_le
```

## 4 h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 02:31:36,288 logs/variance_r2_20260905_012324.log:52539

```lean
theorem h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  -- rewrite the sum in the form required by `AntitoneOn.sum_le_integral_Ico`
  have hsum_eq :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
        ∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1) := by sorry
  -- apply the antitone sum ≤ integral comparison
  have hle' :
      (∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- rewrite back to the original sum
  have hle :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- show the inequality is strict because the function is strictly decreasing
  have hne :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≠
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- combine the non‑strict bound with the non‑equality to obtain a strict bound
  have hlt :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  exact hlt
```

## 5 h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 02:54:31,623 logs/variance_r2_20260905_012324.log:67950

```lean
theorem h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  -- rewrite the sum in the form required by `AntitoneOn.sum_le_integral_Ico`
  have hsum_eq :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
        ∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt ((i : ℝ) + 1) := by sorry
  -- apply the antitone sum ≤ integral comparison
  have hle' :
      (∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt ((i : ℝ) + 1)) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- rewrite back to the original sum
  have hle :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- show the inequality is strict because the function is strictly decreasing
  have hne :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≠
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- combine the non‑strict bound with the non‑equality to obtain a strict bound
  have hlt :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  exact hlt
```

## 6 h_le_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 02:58:48,881 logs/variance_r2_20260905_012324.log:71101

```lean
theorem h_le_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_pointwise :
        ∀ i ∈ Finset.Ico (1 : ℕ) 10000,
          ∀ x ∈ Set.Ico (i : ℝ) (i + 1 : ℝ),
            (1 : ℝ) / Real.sqrt (i + 1) ≤ (1 : ℝ) / Real.sqrt x)
    (h_integrable :
        MeasureTheory.IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000)) :
    (∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) ≤
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  -- 1️⃣  Establish the obvious order `1 ≤ 10000`.
  have hab : (1 : ℝ) ≤ 10000 := by sorry
  -- 2️⃣  Derive integrability on the half‑open interval `Ico 1 10000` from the given
  --     integrability on the closed interval `Icc 1 10000`.
  have h_int_Ico :
      MeasureTheory.IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Ico (1 : ℝ) 10000) := by sorry
  -- 3️⃣  Apply the comparison theorem `sum_Ico_le_integral_of_le`
  --     using the pointwise domination hypothesis `h_pointwise`.
  have h_sum_le_int :
      (∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 4️⃣  Conclude the desired inequality.
  exact h_sum_le_int
```

## 7 h_le_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 03:59:14,789 logs/variance_r2_20260905_012324.log:98405

```lean
theorem h_le_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_pointwise :
        ∀ i ∈ Finset.Ico (1 : ℕ) 10000,
          ∀ x ∈ Set.Ico (i : ℝ) ((i : ℝ) + 1),
            (1 : ℝ) / Real.sqrt ((i : ℝ) + 1) ≤ (1 : ℝ) / Real.sqrt x)
    (h_integrable :
        MeasureTheory.IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000)) :
    (∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt ((i : ℝ) + 1)) ≤
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  -- 1️⃣  Establish the obvious order `1 ≤ 10000`.
  have hab : (1 : ℝ) ≤ 10000 := by sorry
  -- 2️⃣  Derive integrability on the half‑open interval `Ico 1 10000` from the given
  --     integrability on the closed interval `Icc 1 10000`.
  have h_int_Ico :
      MeasureTheory.IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Ico (1 : ℝ) 10000) := by sorry
  -- 3️⃣  Apply the comparison theorem `sum_Ico_le_integral_of_le`
  --     using the pointwise domination hypothesis `h_pointwise`.
  have h_sum_le_int :
      (∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt ((i : ℝ) + 1)) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 4️⃣  Conclude the desired inequality.
  exact h_sum_le_int
```

## 8 hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 04:10:10,750 logs/variance_r2_20260905_012324.log:108129

```lean
theorem hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≠
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  /- 1.  The right‑endpoint Riemann sum is bounded above by the integral. -/
  have hle :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  /- 2.  On the first sub‑interval [1,2] the sum term is strictly smaller than the integral. -/
  have hlt_one_two :
      (1 : ℝ) / Real.sqrt 2 <
        ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  /- 3.  For the remaining sub‑intervals the non‑strict inequality holds. -/
  have hrest :
      (∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  /- 4.  Combine the strict inequality on [1,2] with the non‑strict one on [2,10000] to obtain a strict inequality for the whole interval. -/
  have hlt :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  /- 5.  A strict inequality yields inequality of the two quantities. -/
  exact ne_of_lt hlt
```

## 9 h_sum_le_int_h_le_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 04:25:45,478 logs/variance_r2_20260905_012324.log:124141

```lean
theorem h_sum_le_int_h_le_h_sum_le_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
  (h_pointwise :
        ∀ i ∈ Finset.Ico (1 : ℕ) 10000,
          ∀ x ∈ Set.Ico (i : ℝ) (i + 1 : ℝ),
            (1 : ℝ) / Real.sqrt (i + 1) ≤ (1 : ℝ) / Real.sqrt x)
  (h_int_Ico :
        MeasureTheory.IntegrableOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Ico (1 : ℝ) 10000)) :
    (∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) ≤
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  -- 1️⃣  Establish the ordering of the interval endpoints.
  have hab : (1 : ℝ) ≤ 10000 := by sorry
  -- 2️⃣  Upgrade integrability on the half‑open interval to interval‑integrability.
  have h_int : IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume 1 10000 := by sorry
  -- 3️⃣  Apply the antitone sum‑integral comparison theorem.
  have h_sum_le :
      (∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  exact h_sum_le
```

## 10 hrest_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 04:59:06,794 logs/variance_r2_20260905_012324.log:164406

```lean
theorem hrest_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000)) :
    (∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
      ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  -- Restrict antitone property to the smaller interval [2,10000]
  have h_antitone' :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) 10000) := by sorry
  -- Apply the sum‑integral comparison for antitone functions on [2,10000]
  have h_sum_le :
      (∑ i in Finset.Ico (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- Identify the two sums
  have h_eq_sum :
      (∑ i in Finset.Ico (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) =
        ∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by sorry
  -- Conclude the desired inequality
  have h_final :
      (∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  exact h_final
```

## 11 hle_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 05:00:50,316 logs/variance_r2_20260905_012324.log:169082

```lean
theorem hle_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h_le :
      (∑ i in Finset.Ico (1 : ℕ) 10000,
          (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_eq :
      (∑ i in Finset.Ico (1 : ℕ) 10000,
          (1 : ℝ) / Real.sqrt (i + 1)) =
        ∑ k in Finset.Icc (2 : ℕ) 10000,
          (1 : ℝ) / Real.sqrt k := by sorry
  simpa [h_eq] using h_le
```

## 12 hlt_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 05:01:32,430 logs/variance_r2_20260905_012324.log:169823

```lean
theorem hlt_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (hlt_one_two :
        (1 : ℝ) / Real.sqrt 2 <
          ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x)
    (hrest :
        (∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  -- 1. Rewrite the sum from 2 to 10000 as the term for 2 plus the sum from 3 to 10000
  have h_sum_eq :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
        (1 : ℝ) / Real.sqrt 2 +
          ∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by sorry
  -- 2. Add the strict inequality on the first interval and the non‑strict inequality on the rest
  have h_lt_add :
      (1 : ℝ) / Real.sqrt 2 +
        ∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k
        <
        (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
          ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 3. Combine the two adjacent integrals into a single integral over [1,10000]
  have h_integral_add :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x
        =
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 4. Assemble the pieces to obtain the desired strict inequality
  have h_final :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  exact h_final
```

## 13 hlt_one_two_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 05:04:26,777 logs/variance_r2_20260905_012324.log:173334

```lean
theorem hlt_one_two_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000)) :
    (1 : ℝ) / Real.sqrt 2 <
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by
  -- 1. Apply the sum ≤ integral inequality for a = 1
  have h_sum_le :
      (∑ i in Finset.range 1,
          (1 : ℝ) / Real.sqrt (1 + (i + 1))) ≤
        ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  -- 2. Simplify the finite sum to the endpoint value
  have h_sum_eq :
      (∑ i in Finset.range 1,
          (1 : ℝ) / Real.sqrt (1 + (i + 1))) = (1 : ℝ) / Real.sqrt 2 := by sorry
  -- 3. Rewrite the inequality using the simplified sum
  have h_le :
      (1 : ℝ) / Real.sqrt 2 ≤
        ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  -- 4. Show the integral is not equal to the endpoint value (strictness)
  have h_ne :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) ≠ (1 : ℝ) / Real.sqrt 2 := by sorry
  -- 5. Conclude the strict inequality
  exact lt_of_le_of_ne h_le (Ne.symm h_ne)
```

## 14 h_integral_add_hlt_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 05:11:20,340 logs/variance_r2_20260905_012324.log:184596

```lean
theorem h_integral_add_hlt_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
      ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x
      =
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h_int1 :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume (1) (2) := by sorry
  have h_int2 :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) volume (2) (10000) := by sorry
  have h_eq :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x =
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  simpa using h_eq
```

## 15 h_ne_hlt_one_two_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 05:28:55,721 logs/variance_r2_20260905_012324.log:216768

```lean
theorem h_ne_hlt_one_two_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000)) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) ≠ (1 : ℝ) / Real.sqrt 2 := by
  -- 1. the interval [1,2] is contained in [1,10000]
  have h_subset : (Set.Icc (1 : ℝ) 2) ⊆ Set.Icc (1 : ℝ) 10000 := by sorry
  -- 2. restrict the antitone property to the smaller interval
  have h_antitone_sub :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 2) := by sorry
  -- 3. the function is not constant on [1,2]
  have h_not_const :
      ∃ x ∈ Set.Icc (1 : ℝ) 2, (1 : ℝ) / Real.sqrt x ≠ (1 : ℝ) / Real.sqrt (2 : ℝ) := by sorry
  -- 4. strict inequality for the integral of a non‑constant antitone function
  have h_int_gt :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2 : ℝ) := by sorry
  -- 5. conclude the desired inequality
  exact ne_of_gt h_int_gt
```

## 16 h_ne_hlt_one_two_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 06:03:38,374 logs/variance_r2_20260905_012324.log:231767

```lean
theorem h_ne_hlt_one_two_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000)) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) ≠ (1 : ℝ) / Real.sqrt 2 := by
  -- 1. Pointwise inequality obtained from the antitone hypothesis
  have h_le_pointwise :
      ∀ x ∈ Set.Icc (1 : ℝ) 2, (1 : ℝ) / Real.sqrt 2 ≤ (1 : ℝ) / Real.sqrt x := by sorry
  -- 2. Turn the pointwise inequality into an a.e. inequality on the restricted measure
  have h_le_ae :
      (fun x => (1 : ℝ) / Real.sqrt 2) ≤ᵐ[volume.restrict (Set.Icc (1 : ℝ) 2)]
        fun x => (1 : ℝ) / Real.sqrt x := by sorry
  -- 3. Apply the integral monotonicity lemma for a.e. inequalities
  have h_integral_ge :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) ≥
        (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt 2) := by sorry
  -- 4. Compute the integral of the constant function
  have h_const :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt 2) = (1 : ℝ) / Real.sqrt 2 := by sorry
  -- 5. Combine the previous two results to obtain a non‑strict inequality
  have h_integral_ge' :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) ≥ (1 : ℝ) / Real.sqrt 2 := by sorry
  -- 6. A strict a.e. inequality on a set of positive measure
  have h_strict_ae :
      (fun x => (1 : ℝ) / Real.sqrt x) >ᵐ[volume.restrict (Set.Icc (1 : ℝ) 2)]
        fun x => (1 : ℝ) / Real.sqrt 2 := by sorry
  -- 7. Apply the strict integral monotonicity lemma
  have h_integral_gt :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt 2 := by sorry
  -- 8. Conclude that the two numbers are not equal
  exact ne_of_gt h_integral_gt
```

## 17 h_ne_hlt_one_two_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 06:53:20,073 logs/variance_r2_20260905_012324.log:276827

```lean
theorem h_ne_hlt_one_two_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000)) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) ≠ (1 : ℝ) / Real.sqrt 2 := by
  -- 1. Restrict the antitone hypothesis to the smaller interval [1,2].
  have h_antitone12 :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 2) := by sorry
  -- 2. From antitonicity obtain a pointwise lower bound on the integrand.
  have h_le :
      ∀ x ∈ Set.Icc (1 : ℝ) 2, (1 : ℝ) / Real.sqrt 2 ≤ (1 : ℝ) / Real.sqrt x := by sorry
  -- 3. Show that the inequality is strict at the left endpoint.
  have h_strict_at_one :
      (1 : ℝ) / Real.sqrt 1 > (1 : ℝ) / Real.sqrt 2 := by sorry
  -- 4. Compute the integral of the constant function 1/√2 over [1,2].
  have h_const_int :
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt 2 = (1 : ℝ) / Real.sqrt 2 := by sorry
  -- 5. Use monotonicity of the integral to get a strict inequality of integrals.
  have h_int_gt_const :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) >
        ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt 2 := by sorry
  -- 6. Combine the previous steps to obtain a strict lower bound for the original integral.
  have hgt :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt 2 := by sorry
  -- 7. Conclude the desired inequality.
  exact ne_of_gt hgt
```

## 18 h_ne_hlt_one_two_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 07:21:00,836 logs/variance_r2_20260905_012324.log:288270

```lean
theorem h_ne_hlt_one_two_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000)) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) ≠ (1 : ℝ) / Real.sqrt 2 := by
  -- Restrict the antitone property to the smaller interval [1,2].
  have h_antitone_sub :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 2) := by sorry
  -- From the sum–integral comparison we obtain a non‑strict lower bound.
  have h_le :
      (1 : ℝ) / Real.sqrt 2 ≤ ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  -- Strengthen the inequality to a strict one.
  have h_lt :
      (1 : ℝ) / Real.sqrt 2 < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  -- Conclude the desired non‑equality.
  exact ne_of_gt h_lt
```

## 19 h_ne_hlt_one_two_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198

2026-09-05 07:36:30,859 logs/variance_r2_20260905_012324.log:293208

```lean
theorem h_ne_hlt_one_two_hne_h_strict_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000)) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) ≠ (1 : ℝ) / Real.sqrt 2 := by
  -- Restrict the antitone property to the smaller interval [1,2].
  have h_antitone_sub :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 2) := by sorry
  -- From the sum–integral comparison we obtain a non‑strict lower bound.
  have h_le :
      (1 : ℝ) / Real.sqrt 2 ≤ ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  -- Compute the integral explicitly.
  have h_int_eq :
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x = 2 * (Real.sqrt 2 - 1) := by sorry
  -- Strengthen the inequality to a strict one using the explicit value.
  have h_lt :
      (1 : ℝ) / Real.sqrt 2 < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by sorry
  -- Conclude the desired non‑equality.
  exact ne_of_gt h_lt
```
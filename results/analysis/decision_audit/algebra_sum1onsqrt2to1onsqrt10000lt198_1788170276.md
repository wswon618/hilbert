## 1 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-08-31 10:13:47,886 outputs/2026-08-31/09-55-45/run.log:4687

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1️⃣  The function  x ↦ 1/√x  is antitone on [1,10000].
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000) := by sorry
  -- 2️⃣  Apply the integral comparison for antitone functions (non‑strict version).
  have h_sum_le_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 3️⃣  Strengthen to a strict inequality using the strict decrease on each unit interval.
  have h_sum_lt_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 4️⃣  Compute the integral explicitly:  ∫₁¹⁰⁰⁰⁰ 1/√x dx = 2·(√10000−√1)=198.
  have h_int_eq :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = 198 := by sorry
  -- 5️⃣  Conclude the desired strict inequality.
  have h_lt_198 :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < 198 := by sorry
  exact h_lt_198
```

## 2 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-08-31 10:16:02,937 outputs/2026-08-31/09-55-45/run.log:6298

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1️⃣  The function \(x \mapsto 1/\sqrt{x}\) is antitone on \([1,10000]\).
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 / Real.sqrt x)) (Set.Icc (1 : ℝ) 10000) := by sorry
  -- 2️⃣  Compute the integral \(\int_{1}^{10000} \frac{dx}{\sqrt{x}} = 198\).
  have h_integral_eq :
      (∫ x in (1 : ℝ)..10000, (1 / Real.sqrt x)) = (198 : ℝ) := by sorry
  -- 3️⃣  Show the strict inequality
  --     \(\displaystyle \sum_{k=2}^{10000} \frac1{\sqrt{k}} <
  --        \int_{1}^{10000} \frac{dx}{\sqrt{x}}\).
  have h_strict :
      (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) <
        (∫ x in (1 : ℝ)..10000, (1 / Real.sqrt x)) := by sorry
  -- 4️⃣  Combine the previous facts to obtain the desired bound.
  have : (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < (198 : ℝ) := by sorry
  exact this
```

## 3 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-08-31 10:17:48,315 outputs/2026-08-31/09-55-45/run.log:7895

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  /- 1.  A pointwise strict inequality for each term of the sum. -/
  have h_term (k : ℕ) (hk : (2 : ℕ) ≤ k) :
      (1 : ℝ) / Real.sqrt k < 2 * (Real.sqrt k - Real.sqrt (k - 1)) := by sorry
  /- 2.  From the pointwise inequality we obtain a strict inequality between the two sums. -/
  have h_sum :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∑ k in Finset.Icc (2 : ℕ) 10000, 2 * (Real.sqrt k - Real.sqrt (k - 1)) := by sorry
  /- 3.  The right‑hand sum telescopes. -/
  have h_tel :
      (∑ k in Finset.Icc (2 : ℕ) 10000, 2 * (Real.sqrt k - Real.sqrt (k - 1))) =
        2 * (Real.sqrt 10000 - Real.sqrt 1) := by sorry
  /- 4.  Evaluate the telescoped expression. -/
  have h_eval : (2 : ℝ) * (Real.sqrt 10000 - Real.sqrt 1) = (198 : ℝ) := by sorry
  /- 5.  Combine the previous steps to obtain the desired inequality. -/
  calc
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k)
        < ∑ k in Finset.Icc (2 : ℕ) 10000, 2 * (Real.sqrt k - Real.sqrt (k - 1)) := h_sum
    _ = 2 * (Real.sqrt 10000 - Real.sqrt 1) := h_tel
    _ = (198 : ℝ) := h_eval
```

## 4 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-08-31 10:19:38,483 outputs/2026-08-31/09-55-45/run.log:9654

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000) := by sorry
  have h_sum_le_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  have h_int_eq :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by sorry
  have h_sum_lt_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  simpa [h_int_eq] using h_sum_lt_int
```

## 5 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-08-31 10:21:51,788 outputs/2026-08-31/09-55-45/run.log:11390

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  have h_int_eq :
      (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) = 198 := by sorry
  have h_sum_lt_int :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        (∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x) := by sorry
  have h_final :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < 198 := by sorry
  exact h_final
```

## 6 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-08-31 10:23:56,681 outputs/2026-08-31/09-55-45/run.log:12983

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000) := by sorry
  have h_integral_le_sum :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) ≤
        ∑ i in Finset.Ico 1 10001, (1 : ℝ) / Real.sqrt (i + 1) := by sorry
  have h_sum_eq :
      (∑ i in Finset.Ico 1 10001, (1 : ℝ) / Real.sqrt (i + 1)) =
        ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by sorry
  have h_integral_le_desired :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) ≤
        ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by sorry
  have h_integral_val :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
        (2 : ℝ) * (Real.sqrt 10000 - Real.sqrt 1) := by sorry
  have h_integral_eq_198 :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by sorry
  have h_strict :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) := by sorry
  have h_lt_198 :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by sorry
  exact h_lt_198
```

## 7 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-08-31 10:26:38,815 outputs/2026-08-31/09-55-45/run.log:15592

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < 198 := by
  -- 1.  The function x ↦ 1/√x is decreasing on [1,10000].
  have h_monotone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  -- 2.  Compute the integral of 1/√x on [1,10000] via the primitive 2·√x.
  have h_integral_eq :
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x =
        (2 : ℝ) * (Real.sqrt (10000 : ℝ) - Real.sqrt (1 : ℝ)) := by sorry
  -- 3.  Evaluate the expression from (2) to obtain the concrete value 198.
  have h_integral_val :
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x = (198 : ℝ) := by sorry
  -- 4.  Use the integral–sum comparison for a decreasing function (≤ direction).
  have h_sum_le_integral :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 5.  Strengthen the previous inequality to a strict one, because the function is not constant on any unit interval.
  have h_sum_lt_integral :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 : ℝ) / Real.sqrt x := by sorry
  -- 6.  Combine (3) and (5) to obtain the desired bound 198.
  have h_sum_lt_198 :
      (∑ k ∈ Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by sorry
  exact h_sum_lt_198
```

## 8 algebra_sum1onsqrt2to1onsqrt10000lt198

2026-08-31 10:29:47,726 outputs/2026-08-31/09-55-45/run.log:19654

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1️⃣  `f x = 1 / √x` is antitone on `[1,10000]`.
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000) := by sorry
  -- 2️⃣  Apply the antitone sum ≤ integral inequality on the interval `[1,10000]`.
  have h_sum_le :
      (∑ i ∈ Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 3️⃣  Rewrite the left‑hand sum so that it matches the statement of the theorem.
  have h_sum_eq :
      (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) =
        ∑ i ∈ Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1) := by sorry
  -- 4️⃣  Compute the integral `∫₁^{10000} 1/√x dx = 198`.
  have h_int :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = 198 := by sorry
  -- 5️⃣  Strengthen the non‑strict inequality to a strict one (the function is strictly decreasing).
  have h_lt :
      (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 6️⃣  Replace the integral by `198` and finish.
  simpa [h_int] using h_lt
```
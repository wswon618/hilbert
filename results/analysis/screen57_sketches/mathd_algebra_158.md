# mathd_algebra_158

## Original input

```lean
theorem mathd_algebra_158 (a : ℕ) (h₀ : Even a)
    (h₁ : ↑(∑ k in Finset.range 8, 2 * k + 1) - ↑(∑ k in Finset.range 5, a + 2 * k) = (4 : ℤ)) :
    a = 8 := by

```

## Snapshot 1 mathd_algebra_158

2026-09-08 07:09:14,615 [log](../../../logs/screen57_20260907_021530.log:823222)

```lean
theorem mathd_algebra_158 (a : ℕ) (h₀ : Even a)
    (h₁ : ↑(∑ k in Finset.range 8, 2 * k + 1) - ↑(∑ k in Finset.range 5, a + 2 * k) = (4 : ℤ)) :
    a = 8 := by
  -- value of the first sum
  have hS1 : (∑ k in Finset.range 8, (2 * k + 1) : ℤ) = 64 := by sorry
  -- value of the second sum
  have hS2 : (∑ k in Finset.range 5, (a + 2 * k) : ℤ) = (5 * a + 20) := by sorry
  -- rewrite the hypothesis using the computed sums
  have h_eq : (64 : ℤ) - (5 * a + 20) = (4 : ℤ) := by sorry
  -- isolate the term 5·a
  have h5a : (5 * a : ℤ) = 40 := by sorry
  -- move to ℕ
  have h5a_nat : 5 * a = 40 := by sorry
  -- cancel the factor 5
  have h_a : a = 8 := by sorry
  exact h_a
```

## Snapshot 2 h_eq_mathd_algebra_158

2026-09-08 07:23:37,338 [log](../../../logs/screen57_20260907_021530.log:832771)

```lean
theorem h_eq_mathd_algebra_158 (a : ℕ)
    (h₁ : (↑(∑ k in Finset.range 8, 2 * k + 1) : ℤ) -
          ↑(∑ k in Finset.range 5, a + 2 * k) = (4 : ℤ))
    (hS1 : (∑ k in Finset.range 8, (2 * k + 1) : ℤ) = 64)
    (hS2 : (∑ k in Finset.range 5, (a + 2 * k) : ℤ) = (5 * a + 20)) :
    (64 : ℤ) - (5 * a + 20) = (4 : ℤ) := by
  -- replace the first summed term by 64
  have h_left : (↑(∑ k in Finset.range 8, 2 * k + 1) : ℤ) = (64 : ℤ) := by sorry
  -- replace the second summed term by 5·a+20
  have h_right : (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) = (5 * a + 20) := by sorry
  -- rewrite h₁ using the two equalities above
  have h_eq : (64 : ℤ) - (5 * a + 20) = (4 : ℤ) := by sorry
  exact h_eq
```

## Snapshot 3 h_right_h_eq_mathd_algebra_158

2026-09-08 07:45:23,075 [log](../../../logs/screen57_20260907_021530.log:845390)

```lean
theorem h_right_h_eq_mathd_algebra_158 (a : ℕ)
    (hS2 : (∑ k in Finset.range 5, (a + 2 * k) : ℤ) = (5 * a + 20)) :
    (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) = (5 * a + 20) := by
  have h_def :
      (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) =
        ((∑ k in Finset.range 5, a + 2 * k) : ℤ) := by sorry
  simpa [h_def] using hS2
```

## Snapshot 4 h_left_h_eq_mathd_algebra_158

2026-09-08 07:45:40,805 [log](../../../logs/screen57_20260907_021530.log:845824)

```lean
theorem h_left_h_eq_mathd_algebra_158 (a : ℕ)
    (hS1 : (∑ k in Finset.range 8, (2 * k + 1) : ℤ) = 64) :
    (↑(∑ k in Finset.range 8, 2 * k + 1) : ℤ) = (64 : ℤ) := by
  have h_cast_sum :
      (↑(∑ k in Finset.range 8, 2 * k + 1) : ℤ) =
        ∑ k in Finset.range 8, ((2 * k + 1) : ℤ) := by sorry
  simpa [h_cast_sum] using hS1
```

## Snapshot 5 h_right_h_eq_mathd_algebra_158

2026-09-08 07:47:47,191 [log](../../../logs/screen57_20260907_021530.log:847075)

```lean
theorem h_right_h_eq_mathd_algebra_158 (a : ℕ)
    (hS2 : (∑ k in Finset.range 5, (a + 2 * k) : ℤ) = (5 * a + 20)) :
    (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) = (5 * a + 20) := by
  simpa [Nat.cast_sum] using hS2
```

## Snapshot 6 h_right_h_eq_mathd_algebra_158

2026-09-08 07:56:32,235 [log](../../../logs/screen57_20260907_021530.log:850686)

```lean
theorem h_right_h_eq_mathd_algebra_158 (a : ℕ)
    (hS2 : (∑ k in Finset.range 5, (a + 2 * k) : ℤ) = (5 * a + 20)) :
    (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) = (5 * a + 20) := by
  have h_goal :
      (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) = (5 * a + 20) := by sorry
  exact h_goal
```

## Snapshot 7 h_cast_sum_h_left_h_eq_mathd_algebra_158

2026-09-08 08:01:11,347 [log](../../../logs/screen57_20260907_021530.log:856123)

```lean
theorem h_cast_sum_h_left_h_eq_mathd_algebra_158 (a : ℕ)
    (hS1 : (∑ k in Finset.range 8, (2 * k + 1) : ℤ) = 64) :
    (↑(∑ k in Finset.range 8, 2 * k + 1) : ℤ) =
      ∑ k in Finset.range 8, ((2 * k + 1) : ℤ) := by
  -- Reduce the goal to the standard cast‑sum lemma
  have h_cast_sum :
      (↑(∑ k in Finset.range 8, 2 * k + 1) : ℤ) =
        ∑ k in Finset.range 8, ((2 * k + 1) : ℤ) := by sorry
  -- Finish by rewriting with the obtained equality
  simpa using h_cast_sum
```

## Snapshot 8 h_goal_h_right_h_eq_mathd_algebra_158

2026-09-08 08:06:22,629 [log](../../../logs/screen57_20260907_021530.log:860643)

```lean
theorem h_goal_h_right_h_eq_mathd_algebra_158 (a : ℕ)
    (hS2 : (∑ k in Finset.range 5, (a + 2 * k) : ℤ) = (5 * a + 20)) :
    (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) = (5 * a + 20) := by
  have h_cast :
      (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) =
        ∑ k in Finset.range 5, (a + 2 * k : ℤ) := by sorry
  calc
    (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ)
        = ∑ k in Finset.range 5, (a + 2 * k : ℤ) := h_cast
    _ = 5 * a + 20 := hS2
```

## Snapshot 9 h_cast_h_goal_h_right_h_eq_mathd_algebra_158

2026-09-08 08:29:22,047 [log](../../../logs/screen57_20260907_021530.log:873009)

```lean
theorem h_cast_h_goal_h_right_h_eq_mathd_algebra_158 (a : ℕ) :
    (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) =
      ∑ k in Finset.range 5, (a + 2 * k : ℤ) := by
  -- 1️⃣  Apply the homomorphism `Nat.castRingHom` to the whole sum.
  have h_map_sum :
      (Nat.castRingHom : ℕ →+* ℤ) (∑ k in Finset.range 5, a + 2 * k) =
        ∑ k in Finset.range 5, (Nat.castRingHom) (a + 2 * k) := by sorry
  -- 2️⃣  Identify the left‑hand side with the cast of the sum.
  have h_left :
      (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) =
        (Nat.castRingHom : ℕ →+* ℤ) (∑ k in Finset.range 5, a + 2 * k) := by sorry
  -- 3️⃣  Identify each summand on the right‑hand side with the cast.
  have h_right :
      ∀ k, (a + 2 * k : ℤ) = (Nat.castRingHom : ℕ →+* ℤ) (a + 2 * k) := by sorry
  -- 4️⃣  Lift the pointwise equality to an equality of sums.
  have h_sum_right :
      ∑ k in Finset.range 5, (a + 2 * k : ℤ) =
        ∑ k in Finset.range 5, (Nat.castRingHom : ℕ →+* ℤ) (a + 2 * k) := by sorry
  -- 5️⃣  Chain the equalities to obtain the desired result.
  calc
    (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ)
        = (Nat.castRingHom : ℕ →+* ℤ) (∑ k in Finset.range 5, a + 2 * k) := by
          simpa using h_left
    _ = ∑ k in Finset.range 5, (Nat.castRingHom : ℕ →+* ℤ) (a + 2 * k) := by
          simpa using h_map_sum
    _ = ∑ k in Finset.range 5, (a + 2 * k : ℤ) := by
          simpa using h_sum_right.symm
```

## Snapshot 10 h_cast_h_goal_h_right_h_eq_mathd_algebra_158

2026-09-08 08:33:15,291 [log](../../../logs/screen57_20260907_021530.log:878990)

```lean
theorem h_cast_h_goal_h_right_h_eq_mathd_algebra_158 (a : ℕ) :
    (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) =
      ∑ k in Finset.range 5, (a + 2 * k : ℤ) := by
  have h_cast_sum :
      (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) =
        ∑ k in Finset.range 5, ((a + 2 * k) : ℤ) := by sorry
  exact h_cast_sum
```

## Snapshot 11 h_cast_sum_h_cast_sum_h_left_h_eq_mathd_algebra_158

2026-09-08 08:34:21,785 [log](../../../logs/screen57_20260907_021530.log:880126)

```lean
theorem h_cast_sum_h_cast_sum_h_left_h_eq_mathd_algebra_158 :
    (↑(∑ k in Finset.range 8, 2 * k + 1) : ℤ) =
      ∑ k in Finset.range 8, ((2 * k + 1) : ℤ) := by
  -- Cast the whole sum to ℤ and rewrite it as the sum of casted terms.
  have h_cast_sum :
      (↑(∑ k in Finset.range 8, 2 * k + 1) : ℤ) =
        ∑ k in Finset.range 8, (↑(2 * k + 1) : ℤ) := by sorry
  -- The right‑hand side of `h_cast_sum` is definitionally equal to the goal's RHS.
  simpa using h_cast_sum
```

## Snapshot 12 h_cast_h_goal_h_right_h_eq_mathd_algebra_158

2026-09-08 08:41:18,832 [log](../../../logs/screen57_20260907_021530.log:890312)

```lean
theorem h_cast_h_goal_h_right_h_eq_mathd_algebra_158 (a : ℕ) :
    (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) =
      ∑ k in Finset.range 5, (a + 2 * k : ℤ) := by
  -- 1️⃣ Cast the whole sum from ℕ to ℤ.
  have h_sum :
      (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) =
        ∑ k in Finset.range 5, ((a + 2 * k : ℕ) : ℤ) := by sorry
  -- 2️⃣ Show that casting each summand individually gives the desired form.
  have h_cast :
      ∀ k : ℕ, ((a + 2 * k : ℕ) : ℤ) = (a + 2 * k : ℤ) := by sorry
  -- 3️⃣ Rewrite the right‑hand side of `h_sum` using `h_cast`.
  have h_goal :
      (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) =
        ∑ k in Finset.range 5, (a + 2 * k : ℤ) := by sorry
  exact h_goal
```

## Snapshot 13 h_cast_sum_h_cast_sum_h_left_h_eq_mathd_algebra_158

2026-09-08 08:41:35,768 [log](../../../logs/screen57_20260907_021530.log:890611)

```lean
theorem h_cast_sum_h_cast_sum_h_left_h_eq_mathd_algebra_158 :
    (↑(∑ k in Finset.range 8, 2 * k + 1) : ℤ) =
      ∑ k in Finset.range 8, ((2 * k + 1) : ℤ) := by
  -- the finite set we are summing over
  have h_range : Finset.range 8 = Finset.range 8 := by sorry
  -- the function whose values we are summing
  have h_fun : (fun k : ℕ => 2 * k + 1) = fun k => 2 * k + 1 := by sorry
  -- casting the natural‑number sum to ℤ commutes with the sum
  have h_cast_sum :
      (↑(∑ k in Finset.range 8, 2 * k + 1) : ℤ) =
        ∑ k in Finset.range 8, ((2 * k + 1) : ℤ) := by sorry
  exact h_cast_sum
```

## Snapshot 14 h_cast_h_goal_h_right_h_eq_mathd_algebra_158

2026-09-08 08:56:20,955 [log](../../../logs/screen57_20260907_021530.log:897886)

```lean
theorem h_cast_h_goal_h_right_h_eq_mathd_algebra_158 (a : ℕ) :
    (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) =
      ∑ k in Finset.range 5, (a + 2 * k : ℤ) := by
  have h_cast_sum :
      (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ) =
        ∑ k in Finset.range 5, ((a + 2 * k) : ℤ) := by sorry
  have h_cast_eq :
      ∑ k in Finset.range 5, ((a + 2 * k) : ℤ) =
        ∑ k in Finset.range 5, (a + 2 * k : ℤ) := by sorry
  calc
    (↑(∑ k in Finset.range 5, a + 2 * k) : ℤ)
        = ∑ k in Finset.range 5, ((a + 2 * k) : ℤ) := h_cast_sum
    _ = ∑ k in Finset.range 5, (a + 2 * k : ℤ) := h_cast_eq
```

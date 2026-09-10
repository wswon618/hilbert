# algebra_ineq_nto1onlt2m1on

## Original input

```lean
theorem algebra_ineq_nto1onlt2m1on (n : ℕ) : (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by

```

## Snapshot 1 algebra_ineq_nto1onlt2m1on

2026-09-07 04:50:15,723 [log](../../../logs/screen57_20260907_021530.log:45808)

```lean
theorem algebra_ineq_nto1onlt2m1on (n : ℕ) :
    (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by
  -- split the natural number into the three relevant cases
  have h_cases : n = 0 ∨ n = 1 ∨ 2 ≤ n := by sorry
  -- case `n = 0`
  have h_zero : n = 0 → (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by sorry
  -- case `n = 1`
  have h_one : n = 1 → (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by sorry
  -- case `2 ≤ n`
  have h_ge_two : 2 ≤ n → (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by sorry
  -- combine the three cases
  have h_goal : (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by sorry
  exact h_goal
```

## Snapshot 2 algebra_ineq_nto1onlt2m1on

2026-09-07 05:05:00,498 [log](../../../logs/screen57_20260907_021530.log:49248)

```lean
theorem algebra_ineq_nto1onlt2m1on (n : ℕ) :
    (n : ℝ) ^ ((1 : ℝ) / n) ≤ 2 - 1 / n := by
  have h_cases : n = 0 ∨ n = 1 ∨ 2 ≤ n := by sorry
  have h_zero : n = 0 → (n : ℝ) ^ ((1 : ℝ) / n) ≤ 2 - 1 / n := by sorry
  have h_one : n = 1 → (n : ℝ) ^ ((1 : ℝ) / n) ≤ 2 - 1 / n := by sorry
  have h_ge_two : 2 ≤ n → (n : ℝ) ^ ((1 : ℝ) / n) ≤ 2 - 1 / n := by sorry
  have h_goal : (n : ℝ) ^ ((1 : ℝ) / n) ≤ 2 - 1 / n := by sorry
  exact h_goal
```

## Snapshot 3 algebra_ineq_nto1onlt2m1on

2026-09-07 05:20:40,942 [log](../../../logs/screen57_20260907_021530.log:52981)

```lean
theorem algebra_ineq_nto1onlt2m1on (n : ℕ) :
    (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by
  have h_cases : n = 0 ∨ n = 1 ∨ 2 ≤ n := by sorry
  have h_zero : n = 0 → (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by sorry
  have h_one : n = 1 → (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by sorry
  have h_ge_two : 2 ≤ n → (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by sorry
  have h_goal : (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by sorry
  exact h_goal
```

## Snapshot 4 algebra_ineq_nto1onlt2m1on

2026-09-07 05:21:47,301 [log](../../../logs/screen57_20260907_021530.log:55558)

```lean
theorem algebra_ineq_nto1onlt2m1on (n : ℕ) :
    (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by
  have h_cases : n = 0 ∨ n = 1 ∨ 2 ≤ n := by sorry
  have h_zero : n = 0 → (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by sorry
  have h_one : n = 1 → (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by sorry
  have h_ge_two : 2 ≤ n → (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by sorry
  have h_goal : (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by sorry
  exact h_goal
```

## Snapshot 5 algebra_ineq_nto1onlt2m1on

2026-09-07 05:23:01,554 [log](../../../logs/screen57_20260907_021530.log:57133)

```lean
theorem algebra_ineq_nto1onlt2m1on (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by
  have h_ge_two : 2 ≤ n → (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by sorry
  have h_goal : (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by sorry
  exact h_goal
```

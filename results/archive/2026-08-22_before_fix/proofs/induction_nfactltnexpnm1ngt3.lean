import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h_base_induction_nfactltnexpnm1ngt3 : (3 : ℕ) ! < (3 : ℕ) ^ (3 - 1) := by
  norm_num [Nat.factorial]
  <;> decide

theorem h_all_induction_nfactltnexpnm1ngt3
    (h_base : (3 : ℕ) ! < (3 : ℕ) ^ (3 - 1))
    (h_step :
      ∀ n, 3 ≤ n → n ! < n ^ (n - 1) → (n + 1) ! < (n + 1) ^ n) :
    ∀ n, 3 ≤ n → n ! < n ^ (n - 1) := by
  have h_main : ∀ n, 3 ≤ n → n ! < n ^ (n - 1) := by
    intro n hn
    have h : ∀ k : ℕ, 3 ≤ k → k ! < k ^ (k - 1) := by
      intro k hk
      induction' hk with k hk IH
      · -- Base case: k = 3
        norm_num [Nat.factorial] at h_base ⊢
        <;> simpa using h_base
      · -- Inductive step: assume the statement holds for k, prove for k + 1
        have h₁ : (k + 1) ! < (k + 1) ^ ((k + 1) - 1) := by
          have h₂ : 3 ≤ k := by omega
          have h₃ : (k + 1) ! < (k + 1) ^ k := h_step k h₂ IH
          have h₄ : (k + 1) ^ k = (k + 1) ^ ((k + 1) - 1) := by
            have h₅ : (k + 1) - 1 = k := by
              have h₆ : k ≥ 2 := by omega
              omega
            rw [h₅]
          rw [h₄] at h₃
          exact h₃
        simpa using h₁
    exact h n hn
  exact h_main

theorem hpos_h_step_induction_nfactltnexpnm1ngt3 (n : ℕ) : 0 < n + 1 := by
  have h : 0 < n + 1 := by
    -- Since n is a natural number, n + 1 is always at least 1, which is greater than 0.
    have h₁ : 0 ≤ n := by exact Nat.zero_le n
    -- Using the fact that n is non-negative, we can directly conclude that n + 1 > 0.
    omega
  exact h

theorem h_comb_h_step_induction_nfactltnexpnm1ngt3 (n : ℕ)
    (h_mul : (n + 1) * n ! < (n + 1) * n ^ (n - 1))
    (h_mul2 : (n + 1) * n ^ (n - 1) < (n + 1) * (n + 1) ^ (n - 1)) :
    (n + 1) * n ! < (n + 1) * (n + 1) ^ (n - 1) := by
  have h₁ : (n + 1) * n ! < (n + 1) * (n + 1) ^ (n - 1) := by
    calc
      (n + 1) * n ! < (n + 1) * n ^ (n - 1) := h_mul
      _ < (n + 1) * (n + 1) ^ (n - 1) := h_mul2
  exact h₁

theorem h_fact_h_step_induction_nfactltnexpnm1ngt3 (n : ℕ) :
    (n + 1)! = (n + 1) * n ! := by
  simp [Nat.factorial_succ, mul_comm]
  <;> ring
  <;> simp_all [Nat.factorial_succ, mul_comm]
  <;> ring
  <;> norm_num
  <;> linarith

theorem h_right_h_step_induction_nfactltnexpnm1ngt3 (n : ℕ) :
    (n + 1) * (n + 1) ^ (n - 1) = (n + 1) ^ n := by
  have h : (n + 1) * (n + 1) ^ (n - 1) = (n + 1) ^ n := by
    cases n with
    | zero =>
      norm_num
    | succ n =>
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      <;> ring_nf at *
      <;> simp_all [Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      <;> ring_nf at *
      <;> omega
  exact h

theorem h_mul_h_step_induction_nfactltnexpnm1ngt3 (n : ℕ) (hlt : n ! < n ^ (n - 1)) (hpos : 0 < n + 1) :
    (n + 1) * n ! < (n + 1) * n ^ (n - 1) := by
  have h₁ : 0 < n + 1 := by linarith
  have h₂ : (n + 1) * n ! < (n + 1) * n ^ (n - 1) := by
    -- Use the fact that multiplication by a positive number preserves the inequality
    have h₃ : n ! < n ^ (n - 1) := hlt
    have h₄ : 0 < n + 1 := by linarith
    -- Use the property of multiplication to preserve the inequality
    have h₅ : (n + 1) * n ! < (n + 1) * n ^ (n - 1) := by
      -- Use the fact that n + 1 is positive to multiply both sides of the inequality by it
      exact Nat.mul_lt_mul_of_pos_left h₃ h₄
    exact h₅
  exact h₂

theorem h_mul2_h_step_induction_nfactltnexpnm1ngt3 (n : ℕ) (h_pow_lt : n ^ (n - 1) < (n + 1) ^ (n - 1)) (hpos : 0 < n + 1) :
    (n + 1) * n ^ (n - 1) < (n + 1) * (n + 1) ^ (n - 1) := by
  have h₁ : 0 < n + 1 := by linarith
  have h₂ : 0 ≤ n ^ (n - 1) := by positivity
  have h₃ : 0 ≤ (n + 1) ^ (n - 1) := by positivity
  have h₄ : n ^ (n - 1) < (n + 1) ^ (n - 1) := h_pow_lt
  have h₅ : (n + 1) * n ^ (n - 1) < (n + 1) * (n + 1) ^ (n - 1) := by
    -- Since n + 1 > 0, we can multiply both sides of the inequality by (n + 1)
    have h₆ : 0 < n + 1 := by linarith
    -- Use the fact that multiplying both sides of an inequality by a positive number preserves the inequality
    nlinarith
  exact h₅

theorem h_pow_lt_h_step_induction_nfactltnexpnm1ngt3 (n : ℕ) (hnle : 3 ≤ n) :
    n ^ (n - 1) < (n + 1) ^ (n - 1) := by
  have hne : (n - 1) ≠ 0 := by
    have h1lt : (1 : ℕ) < n := lt_of_lt_of_le (by decide) hnle
    have hpos : 0 < n - 1 := Nat.sub_pos_of_lt h1lt
    exact Nat.ne_of_gt hpos
  exact Nat.pow_lt_pow_left (Nat.lt_succ_self n) hne

theorem h_step_induction_nfactltnexpnm1ngt3 :
    ∀ n, 3 ≤ n → n ! < n ^ (n - 1) → (n + 1) ! < (n + 1) ^ n := by
  intro n hnle hlt
  -- positivity of (n+1)
  have hpos : 0 < n + 1 := by
    exact hpos_h_step_induction_nfactltnexpnm1ngt3 n
  -- multiply the given inequality by the positive factor (n+1)
  have h_mul : (n + 1) * n ! < (n + 1) * n ^ (n - 1) := by
    exact h_mul_h_step_induction_nfactltnexpnm1ngt3 n hlt hpos
  -- monotonicity of the power function (base increase)
  have h_pow_lt : n ^ (n - 1) < (n + 1) ^ (n - 1) := by
    exact h_pow_lt_h_step_induction_nfactltnexpnm1ngt3 n hnle
  -- multiply the power inequality by the positive factor (n+1)
  have h_mul2 : (n + 1) * n ^ (n - 1) < (n + 1) * (n + 1) ^ (n - 1) := by
    exact h_mul2_h_step_induction_nfactltnexpnm1ngt3 n h_pow_lt hpos
  -- combine the two strict inequalities
  have h_comb : (n + 1) * n ! < (n + 1) * (n + 1) ^ (n - 1) := by
    exact h_comb_h_step_induction_nfactltnexpnm1ngt3 n h_mul h_mul2
  -- rewrite the right‑hand side as a single power
  have h_right : (n + 1) * (n + 1) ^ (n - 1) = (n + 1) ^ n := by
    exact h_right_h_step_induction_nfactltnexpnm1ngt3 n
  -- rewrite the left‑hand side as a factorial
  have h_fact : (n + 1)! = (n + 1) * n ! := by
    exact h_fact_h_step_induction_nfactltnexpnm1ngt3 n
  -- conclude the desired inequality
  simpa [h_fact, h_right] using h_comb

theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  have h_base : (3 : ℕ) ! < (3 : ℕ) ^ (3 - 1) :=
    h_base_induction_nfactltnexpnm1ngt3
  have h_step :
      ∀ n, 3 ≤ n → n ! < n ^ (n - 1) → (n + 1) ! < (n + 1) ^ n :=
    h_step_induction_nfactltnexpnm1ngt3
  have h_all : ∀ n, 3 ≤ n → n ! < n ^ (n - 1) :=
    h_all_induction_nfactltnexpnm1ngt3 h_base h_step
  exact h_all n h₀

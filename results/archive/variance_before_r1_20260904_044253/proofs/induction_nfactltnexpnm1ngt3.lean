import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem hbase_induction_nfactltnexpnm1ngt3 : (3 : ℕ) ! < (3 : ℕ) ^ (3 - 1) := by
  norm_num [Nat.factorial]
  <;> decide

theorem hstep_induction_nfactltnexpnm1ngt3 :
    ∀ k,
      (3 : ℕ) ≤ k →
        k ! < k ^ (k - 1) →
          (k + 1) ! < (k + 1) ^ ((k + 1) - 1) := by
  intro k hk hk_ineq
  have h₁ : (k + 1) ! = (k + 1) * k ! := by
    simp [Nat.factorial_succ]
    <;> ring
  rw [h₁]
  have h₂ : (k + 1) ^ ((k + 1) - 1) = (k + 1) ^ k := by
    have h₃ : (k + 1) - 1 = k := by
      have h₄ : 0 < k + 1 := by linarith
      omega
    rw [h₃]
    <;> simp [Nat.pow_succ]
  rw [h₂]
  have h₃ : (k + 1) * k ! < (k + 1) * (k + 1) ^ (k - 1) := by
    have h₄ : k ! < (k + 1) ^ (k - 1) := by
      have h₅ : k ! < k ^ (k - 1) := hk_ineq
      have h₆ : k ^ (k - 1) ≤ (k + 1) ^ (k - 1) := by
        exact Nat.pow_le_pow_of_le_left (by linarith) (k - 1)
      linarith
    have h₅ : 0 < k + 1 := by linarith
    nlinarith
  have h₄ : (k + 1) * (k + 1) ^ (k - 1) ≤ (k + 1) ^ k := by
    have h₅ : (k + 1) * (k + 1) ^ (k - 1) = (k + 1) ^ (k - 1 + 1) := by
      have h₆ : (k + 1) * (k + 1) ^ (k - 1) = (k + 1) ^ 1 * (k + 1) ^ (k - 1) := by
        simp [Nat.pow_one]
      rw [h₆]
      have h₇ : (k + 1) ^ 1 * (k + 1) ^ (k - 1) = (k + 1) ^ (1 + (k - 1)) := by
        rw [← pow_add]
      rw [h₇]
      <;> ring_nf at *
      <;> simp_all [Nat.add_assoc]
      <;> omega
    rw [h₅]
    have h₆ : k - 1 + 1 ≤ k := by
      have h₇ : k ≥ 3 := hk
      have h₈ : k - 1 + 1 = k := by
        have h₉ : k ≥ 1 := by linarith
        omega
      linarith
    have h₇ : (k + 1) ^ (k - 1 + 1) ≤ (k + 1) ^ k := by
      exact pow_le_pow_right (by linarith) h₆
    linarith
  linarith

theorem hresult_induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : (3 : ℕ) ≤ n)
    (hbase : (3 : ℕ) ! < (3 : ℕ) ^ (3 - 1))
    (hstep :
        ∀ k,
          (3 : ℕ) ≤ k →
            k ! < k ^ (k - 1) →
              (k + 1) ! < (k + 1) ^ ((k + 1) - 1)) :
    n ! < n ^ (n - 1) := by
  have h_main : ∀ (k : ℕ), 3 ≤ k → k ! < k ^ (k - 1) := by
    intro k hk
    have h₁ : ∀ (m : ℕ), 3 ≤ m → m ! < m ^ (m - 1) := by
      intro m hm
      induction' hm with m hm IH
      · -- Base case: m = 3
        simpa using hbase
      · -- Inductive step: assume the statement holds for m, prove for m + 1
        have h₂ := hstep m hm IH
        simpa [Nat.factorial_succ, pow_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib,
          Nat.add_assoc] using h₂
    exact h₁ k hk
  
  have h_final : n ! < n ^ (n - 1) := by
    have h₁ : 3 ≤ n := h₀
    have h₂ : n ! < n ^ (n - 1) := h_main n h₁
    exact h₂
  
  exact h_final

theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  have hbase : (3 : ℕ) ! < (3 : ℕ) ^ (3 - 1) := by
    exact hbase_induction_nfactltnexpnm1ngt3
  have hstep :
      ∀ k, (3 : ℕ) ≤ k → k ! < k ^ (k - 1) → (k + 1) ! < (k + 1) ^ ((k + 1) - 1) := by
    exact hstep_induction_nfactltnexpnm1ngt3
  have hresult : n ! < n ^ (n - 1) := by
    exact hresult_induction_nfactltnexpnm1ngt3 n h₀ hbase hstep
  exact hresult

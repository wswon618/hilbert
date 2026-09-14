import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown (m n : ℕ) (f : ℕ → ℕ)
    (h₀ : ∀ x, f x = 4 ^ x + 6 ^ x + 9 ^ x) (h₁ : 0 < m ∧ 0 < n) (h₂ : m ≤ n) :
    f (2 ^ m) ∣ f (2 ^ n) := by
  have h_main_lemma : ∀ (x : ℕ), f x ∣ f (2 * x) := by
    intro x
    have h₃ : f x = 4 ^ x + 6 ^ x + 9 ^ x := h₀ x
    have h₄ : f (2 * x) = 4 ^ (2 * x) + 6 ^ (2 * x) + 9 ^ (2 * x) := by
      rw [h₀]
      <;> ring_nf
    rw [h₃, h₄]
    have h₅ : 4 ^ (2 * x) + 6 ^ (2 * x) + 9 ^ (2 * x) = (4 ^ x) ^ 2 + (6 ^ x) ^ 2 + (9 ^ x) ^ 2 := by
      have h₅₁ : 4 ^ (2 * x) = (4 ^ x) ^ 2 := by
        rw [show 2 * x = x + x by ring]
        rw [pow_add]
        <;> ring_nf
        <;> simp [pow_mul]
        <;> ring_nf
      have h₅₂ : 6 ^ (2 * x) = (6 ^ x) ^ 2 := by
        rw [show 2 * x = x + x by ring]
        rw [pow_add]
        <;> ring_nf
        <;> simp [pow_mul]
        <;> ring_nf
      have h₅₃ : 9 ^ (2 * x) = (9 ^ x) ^ 2 := by
        rw [show 2 * x = x + x by ring]
        rw [pow_add]
        <;> ring_nf
        <;> simp [pow_mul]
        <;> ring_nf
      rw [h₅₁, h₅₂, h₅₃]
      <;> ring_nf
    rw [h₅]
    have h₆ : (4 ^ x : ℕ) * (9 ^ x : ℕ) = (6 ^ x : ℕ) ^ 2 := by
      have h₆₁ : (4 : ℕ) * 9 = 6 ^ 2 := by norm_num
      calc
        (4 ^ x : ℕ) * (9 ^ x : ℕ) = (4 * 9) ^ x := by
          rw [mul_pow]
        _ = (6 ^ 2) ^ x := by rw [h₆₁]
        _ = 6 ^ (2 * x) := by
          rw [← pow_mul]
          <;> ring_nf
        _ = (6 ^ x) ^ 2 := by
          have h₆₂ : 6 ^ (2 * x) = (6 ^ x) ^ 2 := by
            rw [show 2 * x = x + x by ring]
            rw [pow_add]
            <;> ring_nf
            <;> simp [pow_mul]
            <;> ring_nf
          rw [h₆₂]
          <;> ring_nf
    have h₇ : (4 ^ x + 6 ^ x + 9 ^ x : ℕ) ∣ (4 ^ x) ^ 2 + (6 ^ x) ^ 2 + (9 ^ x) ^ 2 := by
      have h₇₁ : (4 ^ x : ℕ) * (6 ^ x : ℕ) + (6 ^ x : ℕ) * (9 ^ x : ℕ) + (9 ^ x : ℕ) * (4 ^ x : ℕ) = (6 ^ x : ℕ) * (4 ^ x + 6 ^ x + 9 ^ x : ℕ) := by
        have h₇₁₁ : (4 ^ x : ℕ) * (6 ^ x : ℕ) + (6 ^ x : ℕ) * (9 ^ x : ℕ) + (9 ^ x : ℕ) * (4 ^ x : ℕ) = (6 ^ x : ℕ) * (4 ^ x + 6 ^ x + 9 ^ x : ℕ) := by
          calc
            (4 ^ x : ℕ) * (6 ^ x : ℕ) + (6 ^ x : ℕ) * (9 ^ x : ℕ) + (9 ^ x : ℕ) * (4 ^ x : ℕ) = (6 ^ x : ℕ) * (4 ^ x : ℕ) + (6 ^ x : ℕ) * (9 ^ x : ℕ) + (9 ^ x : ℕ) * (4 ^ x : ℕ) := by ring
            _ = (6 ^ x : ℕ) * (4 ^ x + 9 ^ x : ℕ) + (9 ^ x : ℕ) * (4 ^ x : ℕ) := by ring
            _ = (6 ^ x : ℕ) * (4 ^ x + 9 ^ x : ℕ) + (6 ^ x : ℕ) * (6 ^ x : ℕ) := by
              have h₇₁₂ : (9 : ℕ) ^ x * (4 : ℕ) ^ x = (6 : ℕ) ^ x * (6 : ℕ) ^ x := by
                calc
                  (9 : ℕ) ^ x * (4 : ℕ) ^ x = (9 * 4) ^ x := by rw [mul_pow]
                  _ = (36 : ℕ) ^ x := by norm_num
                  _ = (6 * 6) ^ x := by norm_num
                  _ = (6 : ℕ) ^ x * (6 : ℕ) ^ x := by rw [mul_pow]
                  _ = (6 : ℕ) ^ x * (6 : ℕ) ^ x := by rfl
              nlinarith
            _ = (6 ^ x : ℕ) * (4 ^ x + 9 ^ x + 6 ^ x : ℕ) := by ring
            _ = (6 ^ x : ℕ) * (4 ^ x + 6 ^ x + 9 ^ x : ℕ) := by ring
        exact h₇₁₁
      have h₇₂ : (4 ^ x : ℕ) ^ 2 + (6 ^ x : ℕ) ^ 2 + (9 ^ x : ℕ) ^ 2 = (4 ^ x + 6 ^ x + 9 ^ x : ℕ) ^ 2 - 2 * ((4 ^ x : ℕ) * (6 ^ x : ℕ) + (6 ^ x : ℕ) * (9 ^ x : ℕ) + (9 ^ x : ℕ) * (4 ^ x : ℕ)) := by
        have h₇₂₁ : (4 ^ x + 6 ^ x + 9 ^ x : ℕ) ^ 2 = (4 ^ x : ℕ) ^ 2 + (6 ^ x : ℕ) ^ 2 + (9 ^ x : ℕ) ^ 2 + 2 * ((4 ^ x : ℕ) * (6 ^ x : ℕ) + (6 ^ x : ℕ) * (9 ^ x : ℕ) + (9 ^ x : ℕ) * (4 ^ x : ℕ)) := by
          ring_nf
          <;> simp [add_assoc, add_comm, add_left_comm]
          <;> ring_nf
          <;> nlinarith
        have h₇₂₂ : (4 ^ x : ℕ) ^ 2 + (6 ^ x : ℕ) ^ 2 + (9 ^ x : ℕ) ^ 2 = (4 ^ x + 6 ^ x + 9 ^ x : ℕ) ^ 2 - 2 * ((4 ^ x : ℕ) * (6 ^ x : ℕ) + (6 ^ x : ℕ) * (9 ^ x : ℕ) + (9 ^ x : ℕ) * (4 ^ x : ℕ)) := by
          have h₇₂₃ : 2 * ((4 ^ x : ℕ) * (6 ^ x : ℕ) + (6 ^ x : ℕ) * (9 ^ x : ℕ) + (9 ^ x : ℕ) * (4 ^ x : ℕ)) ≤ (4 ^ x + 6 ^ x + 9 ^ x : ℕ) ^ 2 := by
            nlinarith [pow_pos (by norm_num : (0 : ℕ) < 4) x, pow_pos (by norm_num : (0 : ℕ) < 6) x, pow_pos (by norm_num : (0 : ℕ) < 9) x]
          omega
        exact h₇₂₂
      have h₇₃ : (4 ^ x + 6 ^ x + 9 ^ x : ℕ) ∣ (4 ^ x + 6 ^ x + 9 ^ x : ℕ) ^ 2 := by
        use (4 ^ x + 6 ^ x + 9 ^ x : ℕ)
        <;> ring_nf
      have h₇₄ : (4 ^ x + 6 ^ x + 9 ^ x : ℕ) ∣ 2 * ((4 ^ x : ℕ) * (6 ^ x : ℕ) + (6 ^ x : ℕ) * (9 ^ x : ℕ) + (9 ^ x : ℕ) * (4 ^ x : ℕ)) := by
        have h₇₄₁ : (4 ^ x + 6 ^ x + 9 ^ x : ℕ) ∣ (4 ^ x : ℕ) * (6 ^ x : ℕ) + (6 ^ x : ℕ) * (9 ^ x : ℕ) + (9 ^ x : ℕ) * (4 ^ x : ℕ) := by
          use (6 ^ x : ℕ)
          <;> linarith
        have h₇₄₂ : (4 ^ x + 6 ^ x + 9 ^ x : ℕ) ∣ 2 * ((4 ^ x : ℕ) * (6 ^ x : ℕ) + (6 ^ x : ℕ) * (9 ^ x : ℕ) + (9 ^ x : ℕ) * (4 ^ x : ℕ)) := by
          exact dvd_mul_of_dvd_right h₇₄₁ 2
        exact h₇₄₂
      have h₇₅ : (4 ^ x + 6 ^ x + 9 ^ x : ℕ) ∣ (4 ^ x : ℕ) ^ 2 + (6 ^ x : ℕ) ^ 2 + (9 ^ x : ℕ) ^ 2 := by
        have h₇₅₁ : (4 ^ x : ℕ) ^ 2 + (6 ^ x : ℕ) ^ 2 + (9 ^ x : ℕ) ^ 2 = (4 ^ x + 6 ^ x + 9 ^ x : ℕ) ^ 2 - 2 * ((4 ^ x : ℕ) * (6 ^ x : ℕ) + (6 ^ x : ℕ) * (9 ^ x : ℕ) + (9 ^ x : ℕ) * (4 ^ x : ℕ)) := by
          exact h₇₂
        rw [h₇₅₁]
        -- Use the fact that if a number divides two numbers, it divides their difference
        have h₇₅₂ : (4 ^ x + 6 ^ x + 9 ^ x : ℕ) ∣ (4 ^ x + 6 ^ x + 9 ^ x : ℕ) ^ 2 := h₇₃
        have h₇₅₃ : (4 ^ x + 6 ^ x + 9 ^ x : ℕ) ∣ 2 * ((4 ^ x : ℕ) * (6 ^ x : ℕ) + (6 ^ x : ℕ) * (9 ^ x : ℕ) + (9 ^ x : ℕ) * (4 ^ x : ℕ)) := h₇₄
        -- Use the fact that if a number divides two numbers, it divides their difference
        have h₇₅₄ : (4 ^ x + 6 ^ x + 9 ^ x : ℕ) ∣ (4 ^ x + 6 ^ x + 9 ^ x : ℕ) ^ 2 - 2 * ((4 ^ x : ℕ) * (6 ^ x : ℕ) + (6 ^ x : ℕ) * (9 ^ x : ℕ) + (9 ^ x : ℕ) * (4 ^ x : ℕ)) := by
          exact Nat.dvd_sub' h₇₅₂ h₇₅₃
        exact h₇₅₄
      exact h₇₅
    exact h₇
  
  have h_corollary : ∀ (m k : ℕ), f (2 ^ m) ∣ f (2 ^ (m + k)) := by
    intro m k
    have h₃ : ∀ (k : ℕ), f (2 ^ m) ∣ f (2 ^ (m + k)) := by
      intro k
      induction k with
      | zero =>
        -- Base case: when k = 0, 2^(m+0) = 2^m, so f(2^m) divides itself.
        simp [h₀]
        <;>
        exact dvd_refl _
      | succ k ih =>
        -- Inductive step: assume the statement holds for k, prove for k+1.
        have h₄ : f (2 ^ (m + k)) ∣ f (2 * (2 ^ (m + k))) := by
          apply h_main_lemma
        have h₅ : 2 * (2 ^ (m + k)) = 2 ^ (m + k + 1) := by
          ring_nf
          <;> simp [pow_add, pow_one, mul_assoc]
          <;> ring_nf
        have h₆ : f (2 * (2 ^ (m + k))) = f (2 ^ (m + k + 1)) := by
          rw [h₅]
        have h₇ : f (2 ^ (m + k)) ∣ f (2 ^ (m + k + 1)) := by
          rw [h₆] at h₄
          exact h₄
        have h₈ : f (2 ^ m) ∣ f (2 ^ (m + k)) := ih
        have h₉ : f (2 ^ m) ∣ f (2 ^ (m + k + 1)) := dvd_trans h₈ h₇
        have h₁₀ : m + k + 1 = m + (k + 1) := by ring
        have h₁₁ : f (2 ^ (m + k + 1)) = f (2 ^ (m + (k + 1))) := by
          rw [h₁₀]
        rw [h₁₁] at h₉
        exact h₉
    exact h₃ k
  
  have h_final : f (2 ^ m) ∣ f (2 ^ n) := by
    have h₃ : ∃ k : ℕ, n = m + k := by
      use n - m
      have h₄ : m ≤ n := h₂
      have h₅ : m + (n - m) = n := by
        omega
      linarith
    obtain ⟨k, hk⟩ := h₃
    have h₄ : f (2 ^ m) ∣ f (2 ^ (m + k)) := h_corollary m k
    have h₅ : f (2 ^ (m + k)) = f (2 ^ n) := by
      rw [hk]
      <;> simp [pow_add, pow_mul]
      <;> ring_nf
    rw [h₅] at h₄
    exact h₄
  
  exact h_final

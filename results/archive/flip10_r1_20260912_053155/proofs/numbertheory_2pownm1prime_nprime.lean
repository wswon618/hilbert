import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem hne_one_numbertheory_2pownm1prime_nprime (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.Prime (2 ^ n - 1)) : n ≠ 1 := by
  intro hn
  rw [hn] at h₁
  norm_num at h₁
  <;> contradiction

theorem hprime_numbertheory_2pownm1prime_nprime (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.Prime (2 ^ n - 1)) (hne_one : n ≠ 1)
    (hconj : 2 = 2 ∧ n.Prime) : n.Prime := by
  -- The hypothesis hconj directly gives us that n is prime, so we can simply use it to conclude the proof.
  have h₂ : n.Prime := hconj.2
  exact h₂

theorem hconj_numbertheory_2pownm1prime_nprime (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.Prime (2 ^ n - 1)) (hne_one : n ≠ 1) :
    (2 = 2 ∧ n.Prime) := by
  have h₂ : n.Prime := by
    by_contra h
    -- We will show that if n is not prime, then 2^n - 1 cannot be prime.
    have h₃ : n ≠ 1 := hne_one
    have h₄ : 0 < n := h₀
    have h₅ : ¬n.Prime := h
    -- If n is not prime and not 1, then it has a nontrivial divisor.
    have h₆ : ∃ (a : ℕ), a ∣ n ∧ a ≠ 1 ∧ a ≠ n := by
      -- Use the fact that n is not prime to find a nontrivial divisor.
      have h₇ := Nat.exists_dvd_of_not_prime2 (by omega) h₅
      obtain ⟨a, ha⟩ := h₇
      have h₈ : a ∣ n := ha.1
      have h₉ : a ≠ 1 := by
        by_contra h₉
        simp_all
      have h₁₀ : a ≠ n := by
        by_contra h₁₀
        have h₁₁ : a = n := by omega
        simp_all [Nat.dvd_one]
        <;> omega
      exact ⟨a, h₈, h₉, h₁₀⟩
    obtain ⟨a, ha₁, ha₂, ha₃⟩ := h₆
    -- Now we have a nontrivial divisor a of n.
    have h₇ : a ∣ n := ha₁
    have h₈ : a ≠ 1 := ha₂
    have h₉ : a ≠ n := ha₃
    -- We will use the fact that if a ∣ n, then (2^a - 1) ∣ (2^n - 1).
    have h₁₀ : 2 ^ a - 1 ∣ 2 ^ n - 1 := by
      have h₁₁ : a ∣ n := ha₁
      obtain ⟨k, hk⟩ := h₁₁
      have h₁₂ : 2 ^ a - 1 ∣ 2 ^ (a * k) - 1 := by
        -- Use the fact that (x - 1) ∣ (x^k - 1) for any x and k.
        simpa [pow_mul] using nat_sub_dvd_pow_sub_pow _ 1 k
      have h₁₃ : 2 ^ (a * k) - 1 = 2 ^ n - 1 := by
        rw [hk]
        <;> ring_nf
      rw [h₁₃] at h₁₂
      exact h₁₂
    -- Since 2^a - 1 ∣ 2^n - 1 and 2^n - 1 is prime, 2^a - 1 must be either 1 or 2^n - 1.
    have h₁₁ : 2 ^ a - 1 = 1 ∨ 2 ^ a - 1 = 2 ^ n - 1 := by
      have h₁₂ : Nat.Prime (2 ^ n - 1) := h₁
      have h₁₃ : 2 ^ a - 1 ∣ 2 ^ n - 1 := h₁₀
      have h₁₄ : 2 ^ a - 1 = 1 ∨ 2 ^ a - 1 = 2 ^ n - 1 := by
        have h₁₅ := Nat.Prime.eq_one_or_self_of_dvd h₁₂ (2 ^ a - 1) h₁₃
        tauto
      exact h₁₄
    -- Case analysis on whether 2^a - 1 = 1 or 2^a - 1 = 2^n - 1.
    cases h₁₁ with
    | inl h₁₁ =>
      -- If 2^a - 1 = 1, then 2^a = 2, so a = 1.
      have h₁₂ : 2 ^ a - 1 = 1 := h₁₁
      have h₁₃ : 2 ^ a = 2 := by
        have h₁₄ : 2 ^ a - 1 = 1 := h₁₂
        have h₁₅ : 2 ^ a > 0 := by positivity
        have h₁₆ : 2 ^ a - 1 + 1 = 2 ^ a := by
          omega
        omega
      have h₁₄ : a = 1 := by
        have h₁₅ : 2 ^ a = 2 := h₁₃
        have h₁₆ : a ≤ 1 := by
          by_contra h₁₆
          have h₁₇ : a ≥ 2 := by omega
          have h₁₈ : 2 ^ a ≥ 2 ^ 2 := by
            exact Nat.pow_le_pow_of_le_right (by norm_num) h₁₇
          have h₁₉ : 2 ^ a > 2 := by
            have h₂₀ : 2 ^ 2 = 4 := by norm_num
            have h₂₁ : 2 ^ a ≥ 4 := by
              omega
            omega
          omega
        have h₂₀ : a ≥ 1 := by
          by_contra h₂₀
          have h₂₁ : a = 0 := by omega
          simp_all [h₂₁]
          <;> norm_num at *
          <;> omega
        interval_cases a <;> norm_num at h₁₃ ⊢ <;> try omega
      -- But a ≠ 1, so this is a contradiction.
      simp_all
    | inr h₁₁ =>
      -- If 2^a - 1 = 2^n - 1, then a = n.
      have h₁₂ : 2 ^ a - 1 = 2 ^ n - 1 := h₁₁
      have h₁₃ : a = n := by
        have h₁₄ : 2 ^ a - 1 = 2 ^ n - 1 := h₁₂
        have h₁₅ : 2 ^ a = 2 ^ n := by
          have h₁₆ : 2 ^ a > 0 := by positivity
          have h₁₇ : 2 ^ n > 0 := by positivity
          have h₁₈ : 2 ^ a - 1 + 1 = 2 ^ a := by
            omega
          have h₁₉ : 2 ^ n - 1 + 1 = 2 ^ n := by
            omega
          omega
        have h₂₀ : a = n := by
          apply Nat.pow_right_injective (by norm_num : 1 < 2)
          linarith
        exact h₂₀
      -- But a ≠ n, so this is a contradiction.
      simp_all
  -- We have shown that n is prime. Now we just need to show 2 = 2, which is trivial.
  exact ⟨by rfl, h₂⟩

theorem numbertheory_2pownm1prime_nprime (n : ℕ) (h₀ : 0 < n)
    (h₁ : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by
  have hne_one : n ≠ 1 := by
    exact hne_one_numbertheory_2pownm1prime_nprime n h₀ h₁
  have hconj : (2 = 2 ∧ n.Prime) := by
    exact hconj_numbertheory_2pownm1prime_nprime n h₀ h₁ hne_one
  have hprime : n.Prime := by
    exact hprime_numbertheory_2pownm1prime_nprime n h₀ h₁ hne_one hconj
  exact hprime

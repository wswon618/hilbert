import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown (m n : ℕ) (f : ℕ → ℕ)
    (h₀ : ∀ x, f x = 4 ^ x + 6 ^ x + 9 ^ x) (h₁ : 0 < m ∧ 0 < n) (h₂ : m ≤ n) :
    f (2 ^ m) ∣ f (2 ^ n) := by
  have h_main_lemma : ∀ (y : ℕ), 1 ≤ y → (4 ^ y + 6 ^ y + 9 ^ y) ∣ (4 ^ (2 * y) + 6 ^ (2 * y) + 9 ^ (2 * y)) := by
    intro y hy
    have h₁ : (4 : ℕ) ^ y + 6 ^ y + 9 ^ y ∣ (4 : ℕ) ^ (2 * y) + 6 ^ (2 * y) + 9 ^ (2 * y) := by
      have h₂ : (4 : ℕ) ^ (2 * y) + 6 ^ (2 * y) + 9 ^ (2 * y) = (4 ^ y) ^ 2 + (6 ^ y) ^ 2 + (9 ^ y) ^ 2 := by
        have h₃ : (4 : ℕ) ^ (2 * y) = (4 ^ y) ^ 2 := by
          rw [show (2 : ℕ) * y = y + y by ring]
          rw [pow_add]
          <;> ring_nf
          <;> simp [pow_mul]
          <;> ring_nf
        have h₄ : (6 : ℕ) ^ (2 * y) = (6 ^ y) ^ 2 := by
          rw [show (2 : ℕ) * y = y + y by ring]
          rw [pow_add]
          <;> ring_nf
          <;> simp [pow_mul]
          <;> ring_nf
        have h₅ : (9 : ℕ) ^ (2 * y) = (9 ^ y) ^ 2 := by
          rw [show (2 : ℕ) * y = y + y by ring]
          rw [pow_add]
          <;> ring_nf
          <;> simp [pow_mul]
          <;> ring_nf
        rw [h₃, h₄, h₅]
        <;> ring_nf
      rw [h₂]
      have h₃ : (4 ^ y : ℕ) > 0 := by positivity
      have h₄ : (6 ^ y : ℕ) > 0 := by positivity
      have h₅ : (9 ^ y : ℕ) > 0 := by positivity
      have h₆ : (4 ^ y : ℕ) * (6 ^ y : ℕ) + (6 ^ y : ℕ) * (9 ^ y : ℕ) + (9 ^ y : ℕ) * (4 ^ y : ℕ) = (6 : ℕ) ^ y * (4 ^ y + 6 ^ y + 9 ^ y) := by
        have h₇ : (4 : ℕ) ^ y * 6 ^ y = (24 : ℕ) ^ y := by
          calc
            (4 : ℕ) ^ y * 6 ^ y = (4 * 6) ^ y := by rw [mul_pow]
            _ = (24 : ℕ) ^ y := by norm_num
        have h₈ : (6 : ℕ) ^ y * 9 ^ y = (54 : ℕ) ^ y := by
          calc
            (6 : ℕ) ^ y * 9 ^ y = (6 * 9) ^ y := by rw [mul_pow]
            _ = (54 : ℕ) ^ y := by norm_num
        have h₉ : (9 : ℕ) ^ y * 4 ^ y = (36 : ℕ) ^ y := by
          calc
            (9 : ℕ) ^ y * 4 ^ y = (9 * 4) ^ y := by rw [mul_pow]
            _ = (36 : ℕ) ^ y := by norm_num
        have h₁₀ : (6 : ℕ) ^ y * (4 ^ y + 6 ^ y + 9 ^ y) = (6 : ℕ) ^ y * 4 ^ y + (6 : ℕ) ^ y * 6 ^ y + (6 : ℕ) ^ y * 9 ^ y := by
          ring_nf
        have h₁₁ : (6 : ℕ) ^ y * 4 ^ y + (6 : ℕ) ^ y * 6 ^ y + (6 : ℕ) ^ y * 9 ^ y = (24 : ℕ) ^ y + (36 : ℕ) ^ y + (54 : ℕ) ^ y := by
          calc
            (6 : ℕ) ^ y * 4 ^ y + (6 : ℕ) ^ y * 6 ^ y + (6 : ℕ) ^ y * 9 ^ y = (6 : ℕ) ^ y * 4 ^ y + (6 : ℕ) ^ y * 6 ^ y + (6 : ℕ) ^ y * 9 ^ y := by rfl
            _ = (24 : ℕ) ^ y + (36 : ℕ) ^ y + (54 : ℕ) ^ y := by
              have h₁₂ : (6 : ℕ) ^ y * 4 ^ y = (24 : ℕ) ^ y := by
                calc
                  (6 : ℕ) ^ y * 4 ^ y = (4 : ℕ) ^ y * 6 ^ y := by ring
                  _ = (24 : ℕ) ^ y := by
                    calc
                      (4 : ℕ) ^ y * 6 ^ y = (4 * 6) ^ y := by rw [mul_pow]
                      _ = (24 : ℕ) ^ y := by norm_num
              have h₁₃ : (6 : ℕ) ^ y * 6 ^ y = (36 : ℕ) ^ y := by
                calc
                  (6 : ℕ) ^ y * 6 ^ y = (6 * 6) ^ y := by rw [mul_pow]
                  _ = (36 : ℕ) ^ y := by norm_num
              have h₁₄ : (6 : ℕ) ^ y * 9 ^ y = (54 : ℕ) ^ y := by
                calc
                  (6 : ℕ) ^ y * 9 ^ y = (6 * 9) ^ y := by rw [mul_pow]
                  _ = (54 : ℕ) ^ y := by norm_num
              rw [h₁₂, h₁₃, h₁₄]
              <;> ring_nf
        have h₁₂ : (4 : ℕ) ^ y * 6 ^ y + 6 ^ y * 9 ^ y + 9 ^ y * 4 ^ y = (24 : ℕ) ^ y + (54 : ℕ) ^ y + (36 : ℕ) ^ y := by
          calc
            (4 : ℕ) ^ y * 6 ^ y + 6 ^ y * 9 ^ y + 9 ^ y * 4 ^ y = (4 : ℕ) ^ y * 6 ^ y + 6 ^ y * 9 ^ y + 9 ^ y * 4 ^ y := by rfl
            _ = (24 : ℕ) ^ y + (54 : ℕ) ^ y + (36 : ℕ) ^ y := by
              have h₁₃ : (4 : ℕ) ^ y * 6 ^ y = (24 : ℕ) ^ y := by
                calc
                  (4 : ℕ) ^ y * 6 ^ y = (4 * 6) ^ y := by rw [mul_pow]
                  _ = (24 : ℕ) ^ y := by norm_num
              have h₁₄ : 6 ^ y * 9 ^ y = (54 : ℕ) ^ y := by
                calc
                  6 ^ y * 9 ^ y = (6 * 9) ^ y := by rw [mul_pow]
                  _ = (54 : ℕ) ^ y := by norm_num
              have h₁₅ : 9 ^ y * 4 ^ y = (36 : ℕ) ^ y := by
                calc
                  9 ^ y * 4 ^ y = (9 * 4) ^ y := by rw [mul_pow]
                  _ = (36 : ℕ) ^ y := by norm_num
              rw [h₁₃, h₁₄, h₁₅]
              <;> ring_nf
        have h₁₃ : (24 : ℕ) ^ y + (54 : ℕ) ^ y + (36 : ℕ) ^ y = (24 : ℕ) ^ y + (36 : ℕ) ^ y + (54 : ℕ) ^ y := by
          ring_nf
        have h₁₄ : (6 : ℕ) ^ y * (4 ^ y + 6 ^ y + 9 ^ y) = (24 : ℕ) ^ y + (36 : ℕ) ^ y + (54 : ℕ) ^ y := by
          linarith
        have h₁₅ : (4 : ℕ) ^ y * 6 ^ y + 6 ^ y * 9 ^ y + 9 ^ y * 4 ^ y = (6 : ℕ) ^ y * (4 ^ y + 6 ^ y + 9 ^ y) := by
          linarith
        linarith
      have h₇ : (4 ^ y : ℕ) ^ 2 + (6 ^ y : ℕ) ^ 2 + (9 ^ y : ℕ) ^ 2 = (4 ^ y + 6 ^ y + 9 ^ y) ^ 2 - 2 * ((4 ^ y : ℕ) * (6 ^ y : ℕ) + (6 ^ y : ℕ) * (9 ^ y : ℕ) + (9 ^ y : ℕ) * (4 ^ y : ℕ)) := by
        have h₈ : (4 ^ y + 6 ^ y + 9 ^ y) ^ 2 = (4 ^ y : ℕ) ^ 2 + (6 ^ y : ℕ) ^ 2 + (9 ^ y : ℕ) ^ 2 + 2 * ((4 ^ y : ℕ) * (6 ^ y : ℕ) + (6 ^ y : ℕ) * (9 ^ y : ℕ) + (9 ^ y : ℕ) * (4 ^ y : ℕ)) := by
          ring_nf
          <;> simp [add_assoc, add_comm, add_left_comm, mul_comm, mul_assoc, mul_left_comm]
          <;> nlinarith
        have h₉ : (4 ^ y : ℕ) ^ 2 + (6 ^ y : ℕ) ^ 2 + (9 ^ y : ℕ) ^ 2 = (4 ^ y + 6 ^ y + 9 ^ y) ^ 2 - 2 * ((4 ^ y : ℕ) * (6 ^ y : ℕ) + (6 ^ y : ℕ) * (9 ^ y : ℕ) + (9 ^ y : ℕ) * (4 ^ y : ℕ)) := by
          have h₁₀ : 2 * ((4 ^ y : ℕ) * (6 ^ y : ℕ) + (6 ^ y : ℕ) * (9 ^ y : ℕ) + (9 ^ y : ℕ) * (4 ^ y : ℕ)) ≤ (4 ^ y + 6 ^ y + 9 ^ y) ^ 2 := by
            nlinarith [pow_pos (by norm_num : (0 : ℕ) < 4) y, pow_pos (by norm_num : (0 : ℕ) < 6) y, pow_pos (by norm_num : (0 : ℕ) < 9) y]
          omega
        exact h₉
      have h₈ : (4 ^ y + 6 ^ y + 9 ^ y : ℕ) ∣ (4 ^ y + 6 ^ y + 9 ^ y : ℕ) ^ 2 := by
        use (4 ^ y + 6 ^ y + 9 ^ y)
        <;> ring_nf
      have h₉ : (4 ^ y + 6 ^ y + 9 ^ y : ℕ) ∣ 2 * ((4 ^ y : ℕ) * (6 ^ y : ℕ) + (6 ^ y : ℕ) * (9 ^ y : ℕ) + (9 ^ y : ℕ) * (4 ^ y : ℕ)) := by
        have h₁₀ : (4 ^ y + 6 ^ y + 9 ^ y : ℕ) ∣ (6 : ℕ) ^ y * (4 ^ y + 6 ^ y + 9 ^ y) := by
          use (6 : ℕ) ^ y
          <;> ring_nf
        have h₁₁ : 2 * ((4 ^ y : ℕ) * (6 ^ y : ℕ) + (6 ^ y : ℕ) * (9 ^ y : ℕ) + (9 ^ y : ℕ) * (4 ^ y : ℕ)) = 2 * ((6 : ℕ) ^ y * (4 ^ y + 6 ^ y + 9 ^ y)) := by
          linarith
        rw [h₁₁]
        exact dvd_mul_of_dvd_right h₁₀ 2
      have h₁₀ : (4 ^ y + 6 ^ y + 9 ^ y : ℕ) ∣ (4 ^ y + 6 ^ y + 9 ^ y : ℕ) ^ 2 - 2 * ((4 ^ y : ℕ) * (6 ^ y : ℕ) + (6 ^ y : ℕ) * (9 ^ y : ℕ) + (9 ^ y : ℕ) * (4 ^ y : ℕ)) := by
        exact Nat.dvd_sub' h₈ h₉
      have h₁₁ : (4 ^ y + 6 ^ y + 9 ^ y : ℕ) ∣ (4 ^ y : ℕ) ^ 2 + (6 ^ y : ℕ) ^ 2 + (9 ^ y : ℕ) ^ 2 := by
        rw [h₇]
        exact h₁₀
      simpa [h₂] using h₁₁
    simpa [h₀] using h₁
  
  have h_corollary : ∀ (k : ℕ), f (2 ^ k) ∣ f (2 ^ (k + 1)) := by
    intro k
    have h₁ : f (2 ^ k) = 4 ^ (2 ^ k) + 6 ^ (2 ^ k) + 9 ^ (2 ^ k) := by
      rw [h₀]
      <;> simp [pow_mul]
    have h₂ : f (2 ^ (k + 1)) = 4 ^ (2 ^ (k + 1)) + 6 ^ (2 ^ (k + 1)) + 9 ^ (2 ^ (k + 1)) := by
      rw [h₀]
      <;> simp [pow_mul]
    rw [h₁, h₂]
    have h₃ : 1 ≤ 2 ^ k := by
      apply Nat.one_le_pow
      <;> norm_num
    have h₄ : (4 : ℕ) ^ (2 ^ k) + 6 ^ (2 ^ k) + 9 ^ (2 ^ k) ∣ (4 : ℕ) ^ (2 * (2 ^ k)) + 6 ^ (2 * (2 ^ k)) + 9 ^ (2 * (2 ^ k)) := by
      apply h_main_lemma
      <;> exact h₃
    have h₅ : (4 : ℕ) ^ (2 * (2 ^ k)) + 6 ^ (2 * (2 ^ k)) + 9 ^ (2 * (2 ^ k)) = (4 : ℕ) ^ (2 ^ (k + 1)) + 6 ^ (2 ^ (k + 1)) + 9 ^ (2 ^ (k + 1)) := by
      have h₅₁ : 2 * (2 ^ k) = 2 ^ (k + 1) := by
        calc
          2 * (2 ^ k) = 2 ^ 1 * 2 ^ k := by norm_num
          _ = 2 ^ (1 + k) := by rw [← pow_add]
          _ = 2 ^ (k + 1) := by ring_nf
      rw [h₅₁]
      <;> simp [pow_mul]
      <;> ring_nf
    rw [h₅] at h₄
    exact h₄
  
  have h_final : f (2 ^ m) ∣ f (2 ^ n) := by
    have h₃ : ∀ (k : ℕ), m ≤ k → f (2 ^ m) ∣ f (2 ^ k) := by
      intro k hk
      induction' hk with k hk IH
      · simp
      · have h₄ : f (2 ^ k) ∣ f (2 ^ (k + 1)) := h_corollary k
        exact dvd_trans IH h₄
    have h₄ : m ≤ n := h₂
    have h₅ : f (2 ^ m) ∣ f (2 ^ n) := h₃ n h₄
    exact h₅
  
  apply h_final

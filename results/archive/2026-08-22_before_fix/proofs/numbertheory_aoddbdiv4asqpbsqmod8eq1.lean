import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem numbertheory_aoddbdiv4asqpbsqmod8eq1 (a : ℤ) (b : ℕ) (h₀ : Odd a) (h₁ : 4 ∣ b) :
    (a ^ 2 + b ^ 2) % 8 = 1 := by
  have h₂ : (a ^ 2 : ℤ) % 8 = 1 := by
    have h₂₁ : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 ∨ a % 8 = -1 ∨ a % 8 = -3 ∨ a % 8 = -5 ∨ a % 8 = -7 := by
      cases' h₀ with k hk
      have : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 ∨ a % 8 = -1 ∨ a % 8 = -3 ∨ a % 8 = -5 ∨ a % 8 = -7 := by
        have : a % 8 = (2 * k + 1) % 8 := by
          rw [hk]
          <;> simp [Int.add_emod, Int.mul_emod]
        have : (2 * k + 1 : ℤ) % 8 = 1 ∨ (2 * k + 1 : ℤ) % 8 = 3 ∨ (2 * k + 1 : ℤ) % 8 = 5 ∨ (2 * k + 1 : ℤ) % 8 = 7 ∨ (2 * k + 1 : ℤ) % 8 = -1 ∨ (2 * k + 1 : ℤ) % 8 = -3 ∨ (2 * k + 1 : ℤ) % 8 = -5 ∨ (2 * k + 1 : ℤ) % 8 = -7 := by
          have : (k : ℤ) % 8 = 0 ∨ (k : ℤ) % 8 = 1 ∨ (k : ℤ) % 8 = 2 ∨ (k : ℤ) % 8 = 3 ∨ (k : ℤ) % 8 = 4 ∨ (k : ℤ) % 8 = 5 ∨ (k : ℤ) % 8 = 6 ∨ (k : ℤ) % 8 = 7 := by
            omega
          rcases this with (h | h | h | h | h | h | h | h) <;>
            (try omega) <;>
            (try {
              simp [h, Int.add_emod, Int.mul_emod]
              <;>
              (try omega) <;>
              (try {
                norm_num at *
                <;>
                (try omega)
              })
            }) <;>
            (try {
              omega
            })
          <;>
          (try {
            omega
          })
        rcases this with (h | h | h | h | h | h | h | h) <;>
          (try omega) <;>
          (try {
            simp [h, Int.add_emod, Int.mul_emod] at *
            <;>
            (try omega)
          })
        <;>
        (try {
          omega
        })
      tauto
    rcases h₂₁ with (h₂₁ | h₂₁ | h₂₁ | h₂₁ | h₂₁ | h₂₁ | h₂₁ | h₂₁)
    · -- Case: a ≡ 1 mod 8
      have h₂₂ : (a : ℤ) % 8 = 1 := by exact_mod_cast h₂₁
      have h₂₃ : (a : ℤ) ^ 2 % 8 = 1 := by
        have : (a : ℤ) % 8 = 1 := h₂₂
        have : (a : ℤ) ^ 2 % 8 = 1 := by
          norm_num [pow_two, Int.mul_emod, this]
        exact this
      exact_mod_cast h₂₃
    · -- Case: a ≡ 3 mod 8
      have h₂₂ : (a : ℤ) % 8 = 3 := by exact_mod_cast h₂₁
      have h₂₃ : (a : ℤ) ^ 2 % 8 = 1 := by
        have : (a : ℤ) % 8 = 3 := h₂₂
        have : (a : ℤ) ^ 2 % 8 = 1 := by
          norm_num [pow_two, Int.mul_emod, this]
        exact this
      exact_mod_cast h₂₃
    · -- Case: a ≡ 5 mod 8
      have h₂₂ : (a : ℤ) % 8 = 5 := by exact_mod_cast h₂₁
      have h₂₃ : (a : ℤ) ^ 2 % 8 = 1 := by
        have : (a : ℤ) % 8 = 5 := h₂₂
        have : (a : ℤ) ^ 2 % 8 = 1 := by
          norm_num [pow_two, Int.mul_emod, this]
        exact this
      exact_mod_cast h₂₃
    · -- Case: a ≡ 7 mod 8
      have h₂₂ : (a : ℤ) % 8 = 7 := by exact_mod_cast h₂₁
      have h₂₃ : (a : ℤ) ^ 2 % 8 = 1 := by
        have : (a : ℤ) % 8 = 7 := h₂₂
        have : (a : ℤ) ^ 2 % 8 = 1 := by
          norm_num [pow_two, Int.mul_emod, this]
        exact this
      exact_mod_cast h₂₃
    · -- Case: a ≡ -1 mod 8
      have h₂₂ : (a : ℤ) % 8 = -1 := by exact_mod_cast h₂₁
      have h₂₃ : (a : ℤ) ^ 2 % 8 = 1 := by
        have : (a : ℤ) % 8 = -1 := h₂₂
        have : (a : ℤ) ^ 2 % 8 = 1 := by
          norm_num [pow_two, Int.mul_emod, this]
        exact this
      exact_mod_cast h₂₃
    · -- Case: a ≡ -3 mod 8
      have h₂₂ : (a : ℤ) % 8 = -3 := by exact_mod_cast h₂₁
      have h₂₃ : (a : ℤ) ^ 2 % 8 = 1 := by
        have : (a : ℤ) % 8 = -3 := h₂₂
        have : (a : ℤ) ^ 2 % 8 = 1 := by
          norm_num [pow_two, Int.mul_emod, this]
        exact this
      exact_mod_cast h₂₃
    · -- Case: a ≡ -5 mod 8
      have h₂₂ : (a : ℤ) % 8 = -5 := by exact_mod_cast h₂₁
      have h₂₃ : (a : ℤ) ^ 2 % 8 = 1 := by
        have : (a : ℤ) % 8 = -5 := h₂₂
        have : (a : ℤ) ^ 2 % 8 = 1 := by
          norm_num [pow_two, Int.mul_emod, this]
        exact this
      exact_mod_cast h₂₃
    · -- Case: a ≡ -7 mod 8
      have h₂₂ : (a : ℤ) % 8 = -7 := by exact_mod_cast h₂₁
      have h₂₃ : (a : ℤ) ^ 2 % 8 = 1 := by
        have : (a : ℤ) % 8 = -7 := h₂₂
        have : (a : ℤ) ^ 2 % 8 = 1 := by
          norm_num [pow_two, Int.mul_emod, this]
        exact this
      exact_mod_cast h₂₃
  
  have h₃ : (b : ℕ) % 8 = 0 ∨ (b : ℕ) % 8 = 4 := by
    have h₃₁ : 4 ∣ b := h₁
    have h₃₂ : (b : ℕ) % 4 = 0 := by
      omega
    have h₃₃ : (b : ℕ) % 8 = 0 ∨ (b : ℕ) % 8 = 4 := by
      have h₃₄ : (b : ℕ) % 8 = 0 ∨ (b : ℕ) % 8 = 1 ∨ (b : ℕ) % 8 = 2 ∨ (b : ℕ) % 8 = 3 ∨ (b : ℕ) % 8 = 4 ∨ (b : ℕ) % 8 = 5 ∨ (b : ℕ) % 8 = 6 ∨ (b : ℕ) % 8 = 7 := by
        omega
      rcases h₃₄ with (h₃₄ | h₃₄ | h₃₄ | h₃₄ | h₃₄ | h₃₄ | h₃₄ | h₃₄)
      · -- Case: b % 8 = 0
        exact Or.inl h₃₄
      · -- Case: b % 8 = 1
        exfalso
        have h₃₅ : (b : ℕ) % 4 = 1 := by
          omega
        omega
      · -- Case: b % 8 = 2
        exfalso
        have h₃₅ : (b : ℕ) % 4 = 2 := by
          omega
        omega
      · -- Case: b % 8 = 3
        exfalso
        have h₃₅ : (b : ℕ) % 4 = 3 := by
          omega
        omega
      · -- Case: b % 8 = 4
        exact Or.inr h₃₄
      · -- Case: b % 8 = 5
        exfalso
        have h₃₅ : (b : ℕ) % 4 = 1 := by
          omega
        omega
      · -- Case: b % 8 = 6
        exfalso
        have h₃₅ : (b : ℕ) % 4 = 2 := by
          omega
        omega
      · -- Case: b % 8 = 7
        exfalso
        have h₃₅ : (b : ℕ) % 4 = 3 := by
          omega
        omega
    exact h₃₃
  
  have h₄ : (b ^ 2 : ℕ) % 8 = 0 := by
    have h₄₁ : (b : ℕ) % 8 = 0 ∨ (b : ℕ) % 8 = 4 := h₃
    rcases h₄₁ with (h₄₁ | h₄₁)
    · -- Case: b ≡ 0 mod 8
      have h₄₂ : (b : ℕ) % 8 = 0 := h₄₁
      have h₄₃ : (b ^ 2 : ℕ) % 8 = 0 := by
        have h₄₄ : (b : ℕ) % 8 = 0 := h₄₂
        have h₄₅ : (b ^ 2 : ℕ) % 8 = 0 := by
          have : (b : ℕ) % 8 = 0 := h₄₄
          have : (b ^ 2 : ℕ) % 8 = 0 := by
            norm_num [pow_two, Nat.mul_mod, this]
          exact this
        exact h₄₅
      exact h₄₃
    · -- Case: b ≡ 4 mod 8
      have h₄₂ : (b : ℕ) % 8 = 4 := h₄₁
      have h₄₃ : (b ^ 2 : ℕ) % 8 = 0 := by
        have h₄₄ : (b : ℕ) % 8 = 4 := h₄₂
        have h₄₅ : (b ^ 2 : ℕ) % 8 = 0 := by
          have : (b : ℕ) % 8 = 4 := h₄₄
          have : (b ^ 2 : ℕ) % 8 = 0 := by
            norm_num [pow_two, Nat.mul_mod, this]
          exact this
        exact h₄₅
      exact h₄₃
  
  have h₅ : ((a ^ 2 + b ^ 2 : ℤ) % 8 : ℤ) = 1 := by
    have h₅₁ : (a ^ 2 : ℤ) % 8 = 1 := h₂
    have h₅₂ : (b ^ 2 : ℕ) % 8 = 0 := h₄
    have h₅₃ : ((b : ℕ) ^ 2 : ℤ) % 8 = 0 := by
      norm_cast at h₅₂ ⊢
      <;>
      (try omega) <;>
      (try simp [h₅₂, Int.emod_emod]) <;>
      (try omega)
    have h₅₄ : ((a ^ 2 + b ^ 2 : ℤ) % 8 : ℤ) = 1 := by
      have h₅₅ : ((a ^ 2 + b ^ 2 : ℤ) % 8 : ℤ) = ((a ^ 2 : ℤ) % 8 + (b ^ 2 : ℤ) % 8) % 8 := by
        simp [Int.add_emod]
        <;>
        (try ring_nf) <;>
        (try omega)
      rw [h₅₅]
      have h₅₆ : ((a ^ 2 : ℤ) % 8 : ℤ) = 1 := by
        exact_mod_cast h₅₁
      have h₅₇ : ((b ^ 2 : ℤ) % 8 : ℤ) = 0 := by
        exact_mod_cast h₅₃
      rw [h₅₆, h₅₇]
      <;> norm_num <;>
      (try omega)
    exact h₅₄
  
  have h₆ : (a ^ 2 + b ^ 2) % 8 = 1 := by
    have h₆₁ : ((a ^ 2 + b ^ 2 : ℤ) % 8 : ℤ) = 1 := h₅
    have h₆₂ : (a ^ 2 + b ^ 2 : ℤ) % 8 = 1 := by
      exact_mod_cast h₆₁
    have h₆₃ : (a ^ 2 + b ^ 2 : ℤ) % 8 = (a ^ 2 + b ^ 2 : ℤ) % 8 := rfl
    have h₆₄ : (a ^ 2 + b ^ 2 : ℤ) % 8 = 1 := by
      omega
    norm_cast at h₆₄ ⊢
    <;>
    (try omega) <;>
    (try simp_all [Int.emod_eq_of_lt]) <;>
    (try ring_nf at *) <;>
    (try omega)
  
  apply h₆

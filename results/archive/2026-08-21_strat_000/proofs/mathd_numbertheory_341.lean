import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h_mod_mathd_numbertheory_341 : 5 ^ 100 % 1000 = 625 := by
  norm_num [pow_succ, pow_zero, pow_one, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
  <;> rfl

theorem hc_mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (ha : a = 6) (hb : b = 2) (h_expansion : c + 10 * b + 100 * a = 625) :
    c = 5 := by
  have h₁ : c = 5 := by
    have h₂ : c + 10 * b + 100 * a = 625 := h_expansion
    rw [ha, hb] at h₂
    -- Substitute a = 6 and b = 2 into the equation
    ring_nf at h₂ ⊢
    -- Simplify the equation to c + 20 + 600 = 625
    omega
  exact h₁

theorem hb_mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (ha : a = 6) (h_expansion : c + 10 * b + 100 * a = 625) :
    b = 2 := by
  have h₁ : a = 6 := ha
  have h₂ : c + 10 * b + 100 * a = 625 := h_expansion
  have h₃ : a ≤ 9 := h₀.1
  have h₄ : b ≤ 9 := h₀.2.1
  have h₅ : c ≤ 9 := h₀.2.2
  have h₆ : c + 10 * b + 100 * 6 = 625 := by
    rw [h₁] at h₂
    exact h₂
  have h₇ : c + 10 * b = 25 := by
    omega
  have h₈ : b ≤ 9 := h₀.2.1
  have h₉ : c ≤ 9 := h₀.2.2
  have h₁₀ : b = 2 := by
    -- We know that c + 10 * b = 25 and c ≤ 9, b ≤ 9.
    -- We can try all possible values of b from 0 to 9 to find the correct one.
    have h₁₁ : b ≤ 9 := h₀.2.1
    have h₁₂ : c ≤ 9 := h₀.2.2
    interval_cases b <;> norm_num at h₇ ⊢ <;>
      (try omega) <;>
      (try {
        have h₁₃ : c ≤ 9 := h₀.2.2
        omega
      })
  exact h₁₀

theorem ha_mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h_expansion : c + 10 * b + 100 * a = 625) :
    a = 6 := by
  have h₁ : a = 6 := by
    -- We know that a, b, c are digits (0-9) and the equation is c + 10b + 100a = 625.
    -- We can use the constraints to narrow down the possible values of a, b, and c.
    have h₂ : a ≤ 9 := h₀.1
    have h₃ : b ≤ 9 := h₀.2.1
    have h₄ : c ≤ 9 := h₀.2.2
    -- We can use the fact that a, b, c are digits to bound the possible values.
    -- Since 100a is the dominant term, we can find the possible values of a first.
    have h₅ : a ≥ 6 := by
      by_contra h
      -- If a < 6, then a ≤ 5.
      have h₆ : a ≤ 5 := by linarith
      -- Substitute a ≤ 5 into the equation and check if it's possible.
      have h₇ : c + 10 * b + 100 * a ≤ c + 10 * b + 100 * 5 := by
        have h₈ : 100 * a ≤ 100 * 5 := by
          exact Nat.mul_le_mul_left 100 h₆
        omega
      have h₈ : c + 10 * b + 100 * 5 < 625 := by
        have h₉ : c ≤ 9 := h₄
        have h₁₀ : b ≤ 9 := h₃
        have h₁₁ : c + 10 * b + 100 * 5 ≤ 9 + 10 * 9 + 100 * 5 := by
          nlinarith
        omega
      omega
    -- Now we know a ≥ 6 and a ≤ 9, so a can be 6, 7, 8, or 9.
    -- We can check each case to see which one satisfies the equation.
    have h₆ : a ≤ 9 := h₂
    interval_cases a <;> norm_num at h_expansion ⊢ <;>
      (try omega) <;>
      (try {
        have h₇ : b ≤ 9 := h₃
        have h₈ : c ≤ 9 := h₄
        interval_cases b <;> norm_num at h_expansion ⊢ <;>
          (try omega) <;>
          (try {
            interval_cases c <;> norm_num at h_expansion ⊢ <;>
              omega
          })
      })
  exact h₁

theorem h_val_mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h₁ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a])
    (hdigits : Nat.digits 10 (Nat.ofDigits 10 [c, b, a]) = [c, b, a])
    (h_eq : Nat.ofDigits 10 [c, b, a] = 5 ^ 100 % 1000)
    (h_mod : 5 ^ 100 % 1000 = 625) :
    Nat.ofDigits 10 [c, b, a] = 625 := by
  have h_main : Nat.ofDigits 10 [c, b, a] = 625 := by
    rw [h_eq]
    <;> rw [h_mod]
    <;> norm_num
  
  exact h_main

theorem h_expansion_mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h_val : Nat.ofDigits 10 [c, b, a] = 625) :
    c + 10 * b + 100 * a = 625 := by
  have h_main : c + 10 * b + 100 * a = 625 := by
    have h₁ : Nat.ofDigits 10 [c, b, a] = c + 10 * (b + 10 * a) := by
      simp [Nat.ofDigits, List.cons, List.nil]
      <;> ring_nf
      <;> norm_num
      <;> rfl
    rw [h₁] at h_val
    -- Now h_val states that c + 10 * (b + 10 * a) = 625
    -- We need to show that c + 10 * b + 100 * a = 625
    -- These are actually the same expression, as 10 * (b + 10 * a) = 10 * b + 100 * a
    ring_nf at h_val ⊢
    <;> omega
  
  exact h_main

theorem hdigits_mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h₁ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a]) :
    Nat.digits 10 (Nat.ofDigits 10 [c, b, a]) = [c, b, a] := by
  have h₂ : Nat.ofDigits 10 [c, b, a] = 5 ^ 100 % 1000 := by
    have h₂₁ : Nat.ofDigits 10 (Nat.digits 10 (5 ^ 100 % 1000)) = 5 ^ 100 % 1000 := by
      rw [Nat.ofDigits_digits]
    rw [h₁] at h₂₁
    <;> simpa using h₂₁
  
  have h₃ : Nat.digits 10 (Nat.ofDigits 10 [c, b, a]) = [c, b, a] := by
    rw [h₂]
    <;> rw [h₁]
    <;> rfl
  
  exact h₃

theorem h_eq_mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h₁ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a])
    (hdigits : Nat.digits 10 (Nat.ofDigits 10 [c, b, a]) = [c, b, a]) :
    Nat.ofDigits 10 [c, b, a] = 5 ^ 100 % 1000 := by
  have h₂ : Nat.ofDigits 10 (Nat.digits 10 (5 ^ 100 % 1000)) = 5 ^ 100 % 1000 := by
    have h₂₁ : Nat.ofDigits 10 (Nat.digits 10 (5 ^ 100 % 1000)) = 5 ^ 100 % 1000 := by
      rw [Nat.ofDigits_digits]
    exact h₂₁
  
  have h₃ : Nat.ofDigits 10 [c, b, a] = 5 ^ 100 % 1000 := by
    calc
      Nat.ofDigits 10 [c, b, a] = Nat.ofDigits 10 (Nat.digits 10 (5 ^ 100 % 1000)) := by
        rw [h₁]
      _ = 5 ^ 100 % 1000 := by rw [h₂]
  
  apply h₃

theorem mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h₁ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a]) : a + b + c = 13 := by
  -- 1️⃣  Re‑obtain the digit list from `ofDigits`
  have hdigits :
      Nat.digits 10 (Nat.ofDigits 10 [c, b, a]) = [c, b, a] :=
    hdigits_mathd_numbertheory_341 a b c h₀ h₁
  -- 2️⃣  Relate `ofDigits` to the given digit equality
  have h_eq :
      Nat.ofDigits 10 [c, b, a] = 5 ^ 100 % 1000 :=
    h_eq_mathd_numbertheory_341 a b c h₀ h₁ hdigits
  -- 3️⃣  Compute the concrete remainder `5 ^ 100 % 1000`
  have h_mod : 5 ^ 100 % 1000 = 625 :=
    h_mod_mathd_numbertheory_341
  -- 4️⃣  Combine the two equalities
  have h_val : Nat.ofDigits 10 [c, b, a] = 625 :=
    h_val_mathd_numbertheory_341 a b c h₀ h₁ hdigits h_eq h_mod
  -- 5️⃣  Expand `ofDigits` in base 10
  have h_expansion : c + 10 * b + 100 * a = 625 :=
    h_expansion_mathd_numbertheory_341 a b c h₀ h_val
  -- 6️⃣  Extract the individual digits from the expansion
  have ha : a = 6 :=
    ha_mathd_numbertheory_341 a b c h₀ h_expansion
  have hb : b = 2 :=
    hb_mathd_numbertheory_341 a b c h₀ ha h_expansion
  have hc : c = 5 :=
    hc_mathd_numbertheory_341 a b c h₀ ha hb h_expansion
  -- 7️⃣  Conclude the required sum
  calc
    a + b + c = 6 + 2 + 5 := by
      simp [ha, hb, hc]
    _ = 13 := by
      norm_num

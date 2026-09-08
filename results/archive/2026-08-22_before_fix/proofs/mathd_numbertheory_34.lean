import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h89_mathd_numbertheory_34 : 89 * 9 ≡ 1 [MOD 100] := by
  norm_num [Nat.ModEq, Nat.mod_eq_of_lt]
  <;> rfl

theorem hfinal_mathd_numbertheory_34 (x : ℕ) (htrans : 1 * x ≡ 89 [MOD 100]) : x ≡ 89 [MOD 100] := by
  have h₁ : x ≡ 89 [MOD 100] := by
    simpa [Nat.ModEq, mul_comm] using htrans
  exact h₁

theorem hmod_eq_mathd_numbertheory_34 (x : ℕ) (hfinal : x ≡ 89 [MOD 100]) : x % 100 = 89 := by
  rw [Nat.ModEq] at hfinal
  have h : x % 100 = 89 % 100 := by
    omega
  norm_num at h ⊢
  <;> omega

theorem hmod_self_mathd_numbertheory_34 (x : ℕ) (h₀ : x < 100) : x % 100 = x := by
  have h₁ : x % 100 = x := by
    have h₂ : x < 100 := h₀
    -- Use the property of modulo operation when the dividend is less than the divisor
    have h₃ : x % 100 = x := by
      apply Nat.mod_eq_of_lt
      <;> omega
    exact h₃
  exact h₁

theorem hmod_mathd_numbertheory_34 (x : ℕ) (h₁ : x * 9 % 100 = 1) : x * 9 ≡ 1 [MOD 100] := by
  have h₂ : x * 9 % 100 = 1 := h₁
  have h₃ : x * 9 ≡ 1 [MOD 100] := by
    rw [Nat.ModEq]
    <;> simp [h₂, Nat.mod_eq_of_lt]
    <;> norm_num
    <;> omega
  exact h₃

theorem hmul_left_mathd_numbertheory_34 (x : ℕ) (hmod : x * 9 ≡ 1 [MOD 100]) : 89 * (x * 9) ≡ 89 * 1 [MOD 100] := by
  have h₁ : 89 * (x * 9) ≡ 89 * 1 [MOD 100] := by
    -- Use the property that if a ≡ b [MOD m], then k * a ≡ k * b [MOD m]
    have h₂ : x * 9 ≡ 1 [MOD 100] := hmod
    -- Multiply both sides by 89 and simplify modulo 100
    have h₃ : 89 * (x * 9) ≡ 89 * 1 [MOD 100] := by
      -- Use the property of congruence to multiply both sides by 89
      exact h₂.mul_left 89
    -- The result follows directly from the above step
    exact h₃
  -- The final result is already obtained in h₁
  exact h₁

theorem hmul_right_mathd_numbertheory_34 (x : ℕ) (h89 : 89 * 9 ≡ 1 [MOD 100]) : (89 * 9) * x ≡ 1 * x [MOD 100] := by
  have h₁ : (89 * 9) * x ≡ 1 * x [MOD 100] := by
    have h₂ : 89 * 9 ≡ 1 [MOD 100] := h89
    -- Use the property that if a ≡ b [MOD m], then a * c ≡ b * c [MOD m]
    have h₃ : (89 * 9) * x ≡ 1 * x [MOD 100] := by
      -- Apply the congruence property to multiply both sides by x
      calc
        (89 * 9) * x ≡ 1 * x [MOD 100] := by
          -- Use the fact that 89 * 9 ≡ 1 [MOD 100] to show the product congruence
          exact h₂.mul_right x
        _ = 1 * x := by rfl
    exact h₃
  exact h₁

theorem htrans_mathd_numbertheory_34 (x : ℕ) (hmul_right : (89 * 9) * x ≡ 1 * x [MOD 100]) (hassoc : (89 * 9) * x ≡ 89 [MOD 100]) : 1 * x ≡ 89 [MOD 100] := by
  have h₁ : (89 * 9) * x ≡ 1 * x [MOD 100] := hmul_right
  have h₂ : (89 * 9) * x ≡ 89 [MOD 100] := hassoc
  have h₃ : 1 * x ≡ 89 [MOD 100] := by
    -- Use the transitivity of congruence to combine the two given congruences
    have h₄ : 1 * x ≡ 89 [MOD 100] := by
      -- Since (89 * 9) * x ≡ 1 * x [MOD 100] and (89 * 9) * x ≡ 89 [MOD 100], by transitivity, 1 * x ≡ 89 [MOD 100]
      calc
        1 * x ≡ (89 * 9) * x [MOD 100] := by
          -- Use the symmetric property of congruence to flip the first given congruence
          exact h₁.symm
        _ ≡ 89 [MOD 100] := by
          -- Use the second given congruence
          exact h₂
    exact h₄
  exact h₃

theorem hassoc_mathd_numbertheory_34 (x : ℕ) (hmul_left : 89 * (x * 9) ≡ 89 * 1 [MOD 100]) : (89 * 9) * x ≡ 89 [MOD 100] := by
  have h_eq : 89 * (x * 9) = (89 * 9) * x := by
    have h₁ : 89 * (x * 9) = (89 * 9) * x := by
      ring_nf
      <;> simp [mul_assoc, mul_comm, mul_left_comm]
      <;> ring_nf
      <;> omega
    exact h₁
  
  have h_main : (89 * 9) * x ≡ 89 [MOD 100] := by
    have h₂ : 89 * (x * 9) ≡ 89 * 1 [MOD 100] := hmul_left
    have h₃ : 89 * 1 = 89 := by norm_num
    have h₄ : 89 * (x * 9) ≡ 89 [MOD 100] := by
      simpa [h₃] using h₂
    have h₅ : (89 * 9) * x ≡ 89 [MOD 100] := by
      -- Use the fact that 89 * (x * 9) = (89 * 9) * x to transfer the congruence
      have h₆ : (89 * 9) * x = 89 * (x * 9) := by
        linarith
      rw [h₆] at *
      exact h₄
    exact h₅
  
  exact h_main

theorem mathd_numbertheory_34 (x : ℕ) (h₀ : x < 100) (h₁ : x * 9 % 100 = 1) : x = 89 := by
  -- 1. Turn the remainder equality into a congruence
  have hmod : x * 9 ≡ 1 [MOD 100] :=
    hmod_mathd_numbertheory_34 x h₁
  -- 2. Show that 89·9 is also congruent to 1 modulo 100
  have h89 : 89 * 9 ≡ 1 [MOD 100] :=
    h89_mathd_numbertheory_34
  -- 3. Multiply the first congruence on the left by 89
  have hmul_left : 89 * (x * 9) ≡ 89 * 1 [MOD 100] :=
    hmul_left_mathd_numbertheory_34 x hmod
  -- 4. Re‑associate the product
  have hassoc : (89 * 9) * x ≡ 89 [MOD 100] :=
    hassoc_mathd_numbertheory_34 x hmul_left
  -- 5. Multiply the second congruence on the right by x
  have hmul_right : (89 * 9) * x ≡ 1 * x [MOD 100] :=
    hmul_right_mathd_numbertheory_34 x h89
  -- 6. Combine the two congruences
  have htrans : 1 * x ≡ 89 [MOD 100] :=
    htrans_mathd_numbertheory_34 x hmul_right hassoc
  have hfinal : x ≡ 89 [MOD 100] :=
    hfinal_mathd_numbertheory_34 x htrans
  -- 7. From the congruence obtain an equality of remainders
  have hmod_eq : x % 100 = 89 :=
    hmod_eq_mathd_numbertheory_34 x hfinal
  -- 8. Use the bound x < 100 to replace x % 100 with x
  have hmod_self : x % 100 = x :=
    hmod_self_mathd_numbertheory_34 x h₀
  -- 9. Conclude
  calc
    x = x % 100 := by
      simpa using hmod_self.symm
    _ = 89 := hmod_eq

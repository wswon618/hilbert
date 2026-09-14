import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem ha_mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h₁ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a])
    (hmod : 5 ^ 100 % 1000 = 625)
    (hdigits : Nat.digits 10 625 = [5, 2, 6])
    (hlist : [c, b, a] = [5, 2, 6]) :
    a = 6 := by
  have h₂ : a = 6 := by
    have h₃ := hlist
    simp at h₃
    -- Simplify the list equality to get the values of a, b, c
    <;> simp_all (config := {decide := true})
    <;> omega
  exact h₂

theorem hc_mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h₁ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a])
    (hmod : 5 ^ 100 % 1000 = 625)
    (hdigits : Nat.digits 10 625 = [5, 2, 6])
    (hlist : [c, b, a] = [5, 2, 6]) :
    c = 5 := by
  have h₂ : c = 5 := by
    have h₃ := hlist
    simp at h₃
    -- Simplify the list equality to get the individual equalities for c, b, and a
    <;>
    (try omega) <;>
    (try
      {
        -- Use the fact that the digits are less than or equal to 9 to narrow down the possibilities
        have h₄ := h₀.1
        have h₅ := h₀.2.1
        have h₆ := h₀.2.2
        omega
      }) <;>
    (try
      {
        -- Use the given digits of 625 to directly get the values of c, b, and a
        simp_all [Nat.digits_zero, Nat.div_eq_of_lt]
        <;> norm_num at *
        <;> omega
      })
    <;>
    (try
      {
        -- Use the fact that the digits are less than or equal to 9 to narrow down the possibilities
        omega
      })
  exact h₂

theorem hlist_mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h₁ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a])
    (hmod : 5 ^ 100 % 1000 = 625)
    (hdigits : Nat.digits 10 625 = [5, 2, 6]) :
    [c, b, a] = [5, 2, 6] := by
  have h₂ : 5 ^ 100 % 1000 = 625 := hmod
  have h₃ : Nat.digits 10 625 = [5, 2, 6] := hdigits
  have h₄ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a] := h₁
  have h₅ : Nat.digits 10 (5 ^ 100 % 1000) = Nat.digits 10 625 := by
    rw [h₂]
  have h₆ : [c, b, a] = [5, 2, 6] := by
    have h₇ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a] := h₁
    have h₈ : Nat.digits 10 625 = [5, 2, 6] := hdigits
    have h₉ : Nat.digits 10 (5 ^ 100 % 1000) = Nat.digits 10 625 := by
      rw [h₂]
    have h₁₀ : [c, b, a] = [5, 2, 6] := by
      calc
        [c, b, a] = Nat.digits 10 (5 ^ 100 % 1000) := by
          rw [h₁]
          <;> rfl
        _ = Nat.digits 10 625 := by rw [h₉]
        _ = [5, 2, 6] := by rw [hdigits]
        _ = [5, 2, 6] := by rfl
    exact h₁₀
  exact h₆

theorem hdigits_mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h₁ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a]) :
    Nat.digits 10 625 = [5, 2, 6] := by
  have h_main : Nat.digits 10 625 = [5, 2, 6] := by
    norm_num [Nat.digits_zero, Nat.div_eq_of_lt]
    <;> rfl
  
  exact h_main

theorem hb_mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h₁ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a])
    (hmod : 5 ^ 100 % 1000 = 625)
    (hdigits : Nat.digits 10 625 = [5, 2, 6])
    (hlist : [c, b, a] = [5, 2, 6]) :
    b = 2 := by
  have h_b_eq_2 : b = 2 := by
    have h₂ : b = 2 := by
      -- Use the fact that the lists are equal to get the equality of their elements
      have h₃ := congr_arg (fun l => l.get? 1) hlist
      -- Simplify the expression to get the second element of the list
      simp [List.get?] at h₃
      -- Use the simplified expression to conclude that b = 2
      <;> norm_num at h₃ ⊢ <;>
      (try cases h₃ <;> simp_all) <;>
      (try omega) <;>
      (try aesop)
    exact h₂
  
  exact h_b_eq_2

theorem hmod_mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h₁ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a]) :
    5 ^ 100 % 1000 = 625 := by
  have h_main : 5 ^ 100 % 1000 = 625 := by
    norm_num [pow_succ, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
    <;> rfl
  
  apply h_main

theorem mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h₁ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a]) : a + b + c = 13 := by
  have hmod : 5 ^ 100 % 1000 = 625 :=
    hmod_mathd_numbertheory_341 a b c h₀ h₁
  have hdigits : Nat.digits 10 625 = [5, 2, 6] :=
    hdigits_mathd_numbertheory_341 a b c h₀ h₁
  have hlist : [c, b, a] = [5, 2, 6] :=
    hlist_mathd_numbertheory_341 a b c h₀ h₁ hmod hdigits
  have ha : a = 6 :=
    ha_mathd_numbertheory_341 a b c h₀ h₁ hmod hdigits hlist
  have hb : b = 2 :=
    hb_mathd_numbertheory_341 a b c h₀ h₁ hmod hdigits hlist
  have hc : c = 5 :=
    hc_mathd_numbertheory_341 a b c h₀ h₁ hmod hdigits hlist
  calc
    a + b + c = 6 + 2 + 5 := by
      simp [ha, hb, hc]
    _ = 13 := by
      norm_num

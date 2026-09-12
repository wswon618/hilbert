import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem algebra_apbon2pownleqapownpbpowon2 (a b : ℝ) (n : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : 0 < n) :
    ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
  have h₂ : 0 < a := h₀.1
  have h₃ : 0 < b := h₀.2
  have h₄ : 0 < a + b := by linarith
  have h₅ : 0 < (a + b) / 2 := by positivity
  -- Use the fact that the function x ↦ x^n is convex for x ≥ 0 and n ≥ 1
  have h₆ : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
    -- Use the convexity of the function x ↦ x^n for x ≥ 0 and n ≥ 1
    have h₇ : 0 ≤ a := by linarith
    have h₈ : 0 ≤ b := by linarith
    have h₉ : 0 ≤ (a + b) / 2 := by positivity
    -- Use the power mean inequality or convexity directly
    have h₁₀ : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
      -- Use the convexity of the function x ↦ x^n for x ≥ 0 and n ≥ 1
      have h₁₁ : ∀ (x y : ℝ), 0 ≤ x → 0 ≤ y → ((x + y) / 2) ^ n ≤ (x ^ n + y ^ n) / 2 := by
        intro x y hx hy
        -- Use the convexity of the function x ↦ x^n for x ≥ 0 and n ≥ 1
        have h₁₂ : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ n) := by
          -- Prove that the function x ↦ x^n is convex on [0, ∞)
          apply convexOn_pow
          <;> norm_num
          <;> linarith
        -- Use the definition of convexity to get the desired inequality
        have h₁₃ : (x + y) / 2 ∈ Set.Ici 0 := by
          -- Prove that (x + y)/2 ≥ 0
          have h₁₄ : 0 ≤ (x + y) / 2 := by
            linarith
          exact h₁₄
        have h₁₄ : x ∈ Set.Ici 0 := by
          -- Prove that x ≥ 0
          exact hx
        have h₁₅ : y ∈ Set.Ici 0 := by
          -- Prove that y ≥ 0
          exact hy
        -- Use the convexity property to get the desired inequality
        have h₁₆ : ((x + y) / 2) ^ n ≤ (x ^ n + y ^ n) / 2 := by
          have h₁₇ : (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y = (x + y) / 2 := by ring
          have h₁₈ : (fun x : ℝ => x ^ n) ((1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y) ≤ (1 / 2 : ℝ) * (x ^ n) + (1 / 2 : ℝ) * (y ^ n) := by
            apply h₁₂.2
            <;> simp_all [Set.Ici]
            <;> norm_num
            <;> linarith
          calc
            ((x + y) / 2) ^ n = (fun x : ℝ => x ^ n) ((x + y) / 2) := by simp
            _ = (fun x : ℝ => x ^ n) ((1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y) := by rw [h₁₇]
            _ ≤ (1 / 2 : ℝ) * (x ^ n) + (1 / 2 : ℝ) * (y ^ n) := h₁₈
            _ = (x ^ n + y ^ n) / 2 := by ring
        exact h₁₆
      -- Apply the general result to a and b
      have h₁₂ : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := h₁₁ a b (by linarith) (by linarith)
      exact h₁₂
    exact h₁₀
  exact h₆

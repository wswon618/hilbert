import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem hD_ne_aime_1990_p4 (x : ℝ) (h₀ : 0 < x)
    (hy1 : (x ^ 2 - 10 * x) - 29 ≠ 0)
    (hy2 : (x ^ 2 - 10 * x) - 45 ≠ 0)
    (hy3 : (x ^ 2 - 10 * x) - 69 ≠ 0) :
    ((x ^ 2 - 10 * x) - 29) * ((x ^ 2 - 10 * x) - 45) * ((x ^ 2 - 10 * x) - 69) ≠ 0 := by
  -- first combine the first two factors
  have h12 : ((x ^ 2 - 10 * x) - 29) * ((x ^ 2 - 10 * x) - 45) ≠ 0 := by
    exact (mul_ne_zero_iff).2 ⟨hy1, hy2⟩
  -- now combine the result with the third factor
  have h123 :
      ((x ^ 2 - 10 * x) - 29) * ((x ^ 2 - 10 * x) - 45) *
        ((x ^ 2 - 10 * x) - 69) ≠ 0 := by
    exact (mul_ne_zero_iff).2 ⟨h12, hy3⟩
  exact h123

theorem hy1_aime_1990_p4 (x : ℝ) (h₀ : 0 < x) (h₁ : x ^ 2 - 10 * x - 29 ≠ 0) :
    (x ^ 2 - 10 * x) - 29 ≠ 0 := by
  simpa using h₁

theorem hx_quad_aime_1990_p4 (x : ℝ) (h₀ : 0 < x)
    (hy_val : x ^ 2 - 10 * x = 39) :
    x ^ 2 - 10 * x - 39 = 0 := by
  calc
    x ^ 2 - 10 * x - 39 = (x ^ 2 - 10 * x) - 39 := by ring
    _ = 39 - 39 := by
      simpa [hy_val]
    _ = 0 := by ring

theorem hy3_aime_1990_p4 (x : ℝ) (h₀ : 0 < x) (h₃ : x ^ 2 - 10 * x - 69 ≠ 0) :
    (x ^ 2 - 10 * x) - 69 ≠ 0 := by
  simpa using h₃

theorem hy2_aime_1990_p4 (x : ℝ) (h₀ : 0 < x) (h₂ : x ^ 2 - 10 * x - 45 ≠ 0) :
    (x ^ 2 - 10 * x) - 45 ≠ 0 := by
  simpa using h₂

theorem hx_final_aime_1990_p4 (x : ℝ) (h₀ : 0 < x)
    (hx_cases : x = 13 ∨ x = -3) :
    x = 13 := by
  cases hx_cases with
  | inl h13 =>
      exact h13
  | inr hneg3 =>
      have hcontr : False := by
        have : (0 : ℝ) < -3 := by
          simpa [hneg3] using h₀
        linarith
      exact (False.elim hcontr)

theorem hx_cases_aime_1990_p4 (x : ℝ) (h₀ : 0 < x)
    (hx_quad : x ^ 2 - 10 * x - 39 = 0) :
    x = 13 ∨ x = -3 := by
  -- rewrite the quadratic as a product
  have hfactor : x ^ 2 - 10 * x - 39 = (x - 13) * (x + 3) := by
    ring
  have hzero : (x - 13) * (x + 3) = 0 := by
    simpa [hfactor] using hx_quad
  -- use `mul_eq_zero` to obtain a disjunction
  have hdisj : (x - 13) = 0 ∨ (x + 3) = 0 := (mul_eq_zero.mp hzero)
  rcases hdisj with h1 | h2
  · left
    exact (sub_eq_zero.mp h1)
  · right
    exact (eq_neg_of_add_eq_zero_left h2)

theorem h_lin_aime_1990_p4 (x : ℝ) (h₀ : 0 < x)
    (h_mul_eq :
      ((x ^ 2 - 10 * x) - 45) * ((x ^ 2 - 10 * x) - 69) +
        ((x ^ 2 - 10 * x) - 29) * ((x ^ 2 - 10 * x) - 69) -
        2 * ((x ^ 2 - 10 * x) - 29) * ((x ^ 2 - 10 * x) - 45) = 0) :
    -64 * (x ^ 2 - 10 * x) + 2496 = 0 := by
  have h_simp :
      ((x ^ 2 - 10 * x) - 45) * ((x ^ 2 - 10 * x) - 69) +
        ((x ^ 2 - 10 * x) - 29) * ((x ^ 2 - 10 * x) - 69) -
        2 * ((x ^ 2 - 10 * x) - 29) * ((x ^ 2 - 10 * x) - 45) =
        -64 * (x ^ 2 - 10 * x) + 2496 := by
    ring
  simpa [h_simp] using h_mul_eq

theorem hy_val_aime_1990_p4 (x : ℝ) (h₀ : 0 < x)
    (h_lin : -64 * (x ^ 2 - 10 * x) + 2496 = 0) :
    x ^ 2 - 10 * x = 39 := by
  -- move the constant to the other side
  have h1 : -64 * (x ^ 2 - 10 * x) = -2496 := by
    have := (eq_neg_of_add_eq_zero_left h_lin)
    simpa [add_comm] using this
  -- eliminate the leading minus sign
  have h2 : 64 * (x ^ 2 - 10 * x) = 2496 := by
    simpa [neg_mul, mul_neg, neg_neg] using congrArg (fun t : ℝ => -t) h1
  -- divide by 64
  have h3 : (x ^ 2 - 10 * x) = (2496 : ℝ) / 64 := by
    have h2' : (x ^ 2 - 10 * x) * 64 = 2496 := by
      simpa [mul_comm] using h2
    exact (eq_div_iff_mul_eq (by norm_num : (64 : ℝ) ≠ 0)).mpr h2'
  -- evaluate the rational number
  have h4 : x ^ 2 - 10 * x = 39 := by
    have := h3
    norm_num at this
    exact this
  exact h4

theorem hD_ne_h_mul_eq_aime_1990_p4 (x : ℝ) (h₀ : 0 < x)
    (hy1 : (x ^ 2 - 10 * x) - 29 ≠ 0)
    (hy2 : (x ^ 2 - 10 * x) - 45 ≠ 0)
    (hy3 : (x ^ 2 - 10 * x) - 69 ≠ 0)
    (A : ℝ) (hA : A = x ^ 2 - 10 * x) :
    (A - 29) * (A - 45) * (A - 69) ≠ 0 := by
  have h1 : A - 29 ≠ 0 := by
    simpa [hA] using hy1
  have h2 : A - 45 ≠ 0 := by
    simpa [hA] using hy2
  have h3 : A - 69 ≠ 0 := by
    simpa [hA] using hy3
  have h12 : (A - 29) * (A - 45) ≠ 0 := mul_ne_zero h1 h2
  exact mul_ne_zero h12 h3

theorem h_mul_eq_h_mul_eq_aime_1990_p4 (x : ℝ) (h₀ : 0 < x)
    (hy1 : (x ^ 2 - 10 * x) - 29 ≠ 0)
    (hy2 : (x ^ 2 - 10 * x) - 45 ≠ 0)
    (hy3 : (x ^ 2 - 10 * x) - 69 ≠ 0)
    (h₄ : 1 / ((x ^ 2 - 10 * x) - 29) + 1 / ((x ^ 2 - 10 * x) - 45) -
          2 / ((x ^ 2 - 10 * x) - 69) = 0)
    (A : ℝ) (hA : A = x ^ 2 - 10 * x)
    (hD_ne : (A - 29) * (A - 45) * (A - 69) ≠ 0) :
    (A - 29) * (A - 45) * (A - 69) *
      (1 / (A - 29) + 1 / (A - 45) - 2 / (A - 69)) = 0 := by
  -- rewrite the given equality using `A`
  have h₄' : 1 / (A - 29) + 1 / (A - 45) - 2 / (A - 69) = 0 := by
    simpa [hA] using h₄
  -- multiply both sides by the non‑zero product
  calc
    (A - 29) * (A - 45) * (A - 69) *
        (1 / (A - 29) + 1 / (A - 45) - 2 / (A - 69))
        = (A - 29) * (A - 45) * (A - 69) * 0 := by
          rw [h₄']
    _ = 0 := by
          simp

theorem h_simpl_h_mul_eq_aime_1990_p4 (x : ℝ) (h₀ : 0 < x)
    (hy1 : (x ^ 2 - 10 * x) - 29 ≠ 0)
    (hy2 : (x ^ 2 - 10 * x) - 45 ≠ 0)
    (hy3 : (x ^ 2 - 10 * x) - 69 ≠ 0)
    (h₄ : 1 / ((x ^ 2 - 10 * x) - 29) + 1 / ((x ^ 2 - 10 * x) - 45) -
          2 / ((x ^ 2 - 10 * x) - 69) = 0)
    (A : ℝ) (hA : A = x ^ 2 - 10 * x)
    (h_mul_eq :
      (A - 29) * (A - 45) * (A - 69) *
        (1 / (A - 29) + 1 / (A - 45) - 2 / (A - 69)) = 0) :
    (A - 45) * (A - 69) + (A - 29) * (A - 69) -
      2 * (A - 29) * (A - 45) = 0 := by
  have hneq29 : (A - 29) ≠ 0 := by
    simpa [hA] using hy1
  have hneq45 : (A - 45) ≠ 0 := by
    simpa [hA] using hy2
  have hneq69 : (A - 69) ≠ 0 := by
    simpa [hA] using hy3
  have h' := h_mul_eq
  field_simp [hneq29, hneq45, hneq69] at h'
  convert h' using 1
  ring

theorem h_mul_eq_aime_1990_p4 (x : ℝ) (h₀ : 0 < x)
    (hy1 : (x ^ 2 - 10 * x) - 29 ≠ 0)
    (hy2 : (x ^ 2 - 10 * x) - 45 ≠ 0)
    (hy3 : (x ^ 2 - 10 * x) - 69 ≠ 0)
    (h₄ : 1 / ((x ^ 2 - 10 * x) - 29) + 1 / ((x ^ 2 - 10 * x) - 45) -
          2 / ((x ^ 2 - 10 * x) - 69) = 0) :
    ((x ^ 2 - 10 * x) - 45) * ((x ^ 2 - 10 * x) - 69) +
      ((x ^ 2 - 10 * x) - 29) * ((x ^ 2 - 10 * x) - 69) -
      2 * ((x ^ 2 - 10 * x) - 29) * ((x ^ 2 - 10 * x) - 45) = 0 := by
  -- 1. Introduce the abbreviation A = x ^ 2 - 10 * x
  set A := x ^ 2 - 10 * x with hA
  -- 2. The product of the three denominators is non‑zero
  have hD_ne : (A - 29) * (A - 45) * (A - 69) ≠ 0 := by
    exact
      hD_ne_h_mul_eq_aime_1990_p4 (x := x) (h₀ := h₀) (hy1 := hy1) (hy2 := hy2)
        (hy3 := hy3) (A := A) (hA := hA)
  -- 3. Multiply the hypothesis h₄ by the non‑zero product
  have h_mul_eq :
      (A - 29) * (A - 45) * (A - 69) *
        (1 / (A - 29) + 1 / (A - 45) - 2 / (A - 69)) = 0 := by
    exact
      h_mul_eq_h_mul_eq_aime_1990_p4 (x := x) (h₀ := h₀) (hy1 := hy1) (hy2 := hy2)
        (hy3 := hy3) (h₄ := h₄) (A := A) (hA := hA) (hD_ne := hD_ne)
  -- 4. Simplify the left‑hand side of the equality obtained in 3
  have h_simpl :
      (A - 45) * (A - 69) + (A - 29) * (A - 69) -
        2 * (A - 29) * (A - 45) = 0 := by
    exact
      h_simpl_h_mul_eq_aime_1990_p4 (x := x) (h₀ := h₀) (hy1 := hy1) (hy2 := hy2)
        (hy3 := hy3) (h₄ := h₄) (A := A) (hA := hA) (h_mul_eq := h_mul_eq)
  -- 5. Rewrite A back to its definition to obtain the desired conclusion
  simpa [hA] using h_simpl

theorem aime_1990_p4 (x : ℝ) (h₀ : 0 < x) (h₁ : x ^ 2 - 10 * x - 29 ≠ 0)
    (h₂ : x ^ 2 - 10 * x - 45 ≠ 0) (h₃ : x ^ 2 - 10 * x - 69 ≠ 0)
    (h₄ : 1 / (x ^ 2 - 10 * x - 29) + 1 / (x ^ 2 - 10 * x - 45) - 2 / (x ^ 2 - 10 * x - 69) = 0) :
    x = 13 := by
  let y := x ^ 2 - 10 * x
  have hy1 : y - 29 ≠ 0 := by
    simpa [y] using hy1_aime_1990_p4 x h₀ h₁
  have hy2 : y - 45 ≠ 0 := by
    simpa [y] using hy2_aime_1990_p4 x h₀ h₂
  have hy3 : y - 69 ≠ 0 := by
    simpa [y] using hy3_aime_1990_p4 x h₀ h₃
  have hD_ne : (y - 29) * (y - 45) * (y - 69) ≠ 0 := by
    simpa [y] using hD_ne_aime_1990_p4 x h₀ hy1 hy2 hy3
  have h_mul_eq :
      ((y - 45) * (y - 69) + (y - 29) * (y - 69) - 2 * (y - 29) * (y - 45)) = 0 := by
    simpa [y] using
      h_mul_eq_aime_1990_p4 x h₀ hy1 hy2 hy3 h₄
  have h_lin : -64 * y + 2496 = 0 := by
    simpa [y] using h_lin_aime_1990_p4 x h₀ h_mul_eq
  have hy_val : y = 39 := by
    simpa [y] using hy_val_aime_1990_p4 x h₀ h_lin
  have hx_quad : x ^ 2 - 10 * x - 39 = 0 := by
    have : x ^ 2 - 10 * x = 39 := by
      simpa [y] using hy_val
    simpa using hx_quad_aime_1990_p4 x h₀ this
  have hx_cases : x = 13 ∨ x = -3 := by
    simpa using hx_cases_aime_1990_p4 x h₀ hx_quad
  have hx_final : x = 13 := by
    simpa using hx_final_aime_1990_p4 x h₀ hx_cases
  exact hx_final

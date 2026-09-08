import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem hA_def_aime_1987_p5 (x y : ℤ) :
    (x ^ 2 * y ^ 2) = x ^ 2 * y ^ 2 := by
  rfl

theorem h_mod_aime_1987_p5 (x : ℤ) :
    (30 * x ^ 2 + 517) = 10 * (1 + 3 * x ^ 2) + 507 := by
  ring

theorem hfinal_aime_1987_p5 (x y : ℤ) (hA_val : x ^ 2 * y ^ 2 = 196) :
    3 * (x ^ 2 * y ^ 2) = 588 := by
  calc
    3 * (x ^ 2 * y ^ 2) = 3 * 196 := by
      simpa [hA_val]
    _ = 588 := by
      norm_num

theorem hx2_ne_aime_1987_p5 (x y : ℤ) (h_not_x0 : x ≠ 0) :
    (x ^ 2 : ℤ) ≠ 0 := by
  intro h
  have hx : x = 0 := by
    have : x * x = (0 : ℤ) := by
      simpa [pow_two] using h
    exact (mul_self_eq_zero.mp this)
  exact h_not_x0 hx

theorem hx_sq_aime_1987_p5 (x : ℤ) (h_d_eq13 : 1 + 3 * x ^ 2 = 13) :
    x ^ 2 = 4 := by
  linarith [h_d_eq13]

theorem h_y_sq_aime_1987_p5 (x y : ℤ) (h₀ : y ^ 2 + 3 * (x ^ 2 * y ^ 2) = 30 * x ^ 2 + 517) :
    y ^ 2 = 30 * x ^ 2 + 517 - 3 * (x ^ 2 * y ^ 2) := by
  simpa using (eq_sub_of_add_eq h₀)

theorem h_one_ne_aime_1987_p5 (x : ℤ) (h_not_x0 : x ≠ 0) :
    (1 + 3 * x ^ 2) ≠ 1 := by
  intro h
  -- cancel the leading `1`
  have h_mul : (3 : ℤ) * x ^ 2 = 0 := by
    have : (1 : ℤ) + 3 * x ^ 2 = 1 + (0 : ℤ) := by
      simpa using h
    exact (add_left_cancel_iff).mp this
  -- use `mul_eq_zero` to split the possibilities
  have h_cases : (3 : ℤ) = 0 ∨ x ^ 2 = 0 := by
    have := (mul_eq_zero.mp h_mul)
    simpa using this
  cases h_cases with
  | inl h3zero =>
      have : (3 : ℤ) ≠ 0 := by norm_num
      exact this h3zero
  | inr hx2zero =>
      have hx : x = 0 := by
        have : x * x = (0 : ℤ) := by
          simpa [pow_two] using hx2zero
        exact (mul_self_eq_zero.mp this)
      exact h_not_x0 hx

theorem h_div507_aime_1987_p5 (x : ℤ)
    (h_div2 : (1 + 3 * x ^ 2) ∣ 30 * x ^ 2 + 517)
    (h_mod : (30 * x ^ 2 + 517) = 10 * (1 + 3 * x ^ 2) + 507) :
    (1 + 3 * x ^ 2) ∣ 507 := by
  -- From the given divisor we also have a divisor of the difference
  have hsub : (1 + 3 * x ^ 2) ∣ (30 * x ^ 2 + 517) - 10 * (1 + 3 * x ^ 2) := by
    apply dvd_sub h_div2
    refine ⟨10, ?_⟩
    ring
  -- Rewrite the difference using the provided equality
  have h_eq : (30 * x ^ 2 + 517) - 10 * (1 + 3 * x ^ 2) = 507 := by
    rw [h_mod]
    ring
  -- Conclude the desired divisibility
  simpa [h_eq] using hsub

theorem h_div1_aime_1987_p5 (x y : ℤ) (h_eq6 : (x ^ 2 * y ^ 2) * (1 + 3 * x ^ 2) = x ^ 2 * (30 * x ^ 2 + 517)) :
    (1 + 3 * x ^ 2) ∣ x ^ 2 * (30 * x ^ 2 + 517) := by
  -- Exhibit a witness for the divisibility using the given equality
  have h : ∃ c : ℤ, x ^ 2 * (30 * x ^ 2 + 517) = c * (1 + 3 * x ^ 2) := by
    refine ⟨x ^ 2 * y ^ 2, ?_⟩
    -- Rearrange the given equality and use commutativity of multiplication
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_eq6.symm
  -- Translate the existence statement into a divisibility statement
  exact (dvd_iff_exists_eq_mul_left).mpr h

theorem h_div2_aime_1987_p5 (x y : ℤ)
    (h_div1 : (1 + 3 * x ^ 2) ∣ x ^ 2 * (30 * x ^ 2 + 517))
    (hx2_ne : (x ^ 2 : ℤ) ≠ 0) :
    (1 + 3 * x ^ 2) ∣ 30 * x ^ 2 + 517 := by
  classical
  -- `1 + 3*x^2` is coprime with `x`
  have hcop : IsCoprime (1 + 3 * x ^ 2) x := by
    refine ⟨1, -3 * x, ?_⟩
    ring
  -- cancel one factor `x`
  have h1 : (1 + 3 * x ^ 2) ∣ x * (30 * x ^ 2 + 517) := by
    have htemp : (1 + 3 * x ^ 2) ∣ x * (x * (30 * x ^ 2 + 517)) := by
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h_div1
    have hcancel := hcop.dvd_of_dvd_mul_left htemp
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcancel
  -- cancel the second factor `x`
  have h2 := hcop.dvd_of_dvd_mul_left h1
  simpa [mul_comm, mul_left_comm, mul_assoc] using h2

theorem hA_val_aime_1987_p5 (x y : ℤ) (hx_sq : x ^ 2 = 4)
    (h₀ : y ^ 2 + 3 * (x ^ 2 * y ^ 2) = 30 * x ^ 2 + 517) :
    x ^ 2 * y ^ 2 = 196 := by
  -- simplify the given equation using `hx_sq`
  have h1 : 13 * y ^ 2 = 637 := by
    have h := h₀
    rw [hx_sq] at h
    ring_nf at h
    simpa [mul_comm] using h
  -- deduce `y ^ 2 = 49`
  have hy : y ^ 2 = 49 := by
    have hdiv : (637 : ℤ) = 13 * 49 := by norm_num
    have htemp : 13 * y ^ 2 = 13 * 49 := by
      simpa [hdiv] using h1
    exact mul_left_cancel₀ (by decide : (13 : ℤ) ≠ 0) htemp
  -- compute the desired product
  calc
    x ^ 2 * y ^ 2 = 4 * y ^ 2 := by
      simpa [hx_sq, mul_comm, mul_left_comm, mul_assoc]
    _ = 4 * 49 := by
      simpa [hy]
    _ = 196 := by norm_num

theorem h_eq6_aime_1987_p5 (x y : ℤ)
    (h₀ : y ^ 2 + 3 * (x ^ 2 * y ^ 2) = 30 * x ^ 2 + 517) :
    (x ^ 2 * y ^ 2) * (1 + 3 * x ^ 2) = x ^ 2 * (30 * x ^ 2 + 517) := by
  -- Multiply the given equality on the left by `x²`
  have h := congrArg (fun t : ℤ => x ^ 2 * t) h₀
  calc
    (x ^ 2 * y ^ 2) * (1 + 3 * x ^ 2)
        = x ^ 2 * (y ^ 2 + 3 * (x ^ 2 * y ^ 2)) := by
          ring
    _ = x ^ 2 * (30 * x ^ 2 + 517) := by
          simpa using h

theorem h_not_x0_aime_1987_p5 (x y : ℤ)
    (h₀ : y ^ 2 + 3 * (x ^ 2 * y ^ 2) = 30 * x ^ 2 + 517) :
    x ≠ 0 := by
  intro hx
  have hy : y ^ 2 = (517 : ℤ) := by
    have : y ^ 2 + 3 * (0 ^ 2 * y ^ 2) = 30 * 0 ^ 2 + 517 := by
      simpa [hx] using h₀
    simpa using this
  have h_cases : (|y| : ℤ) < 23 ∨ 23 ≤ |y| := lt_or_ge (|y|) 23
  cases h_cases with
  | inl hlt =>
      have hle : (|y| : ℤ) ≤ 22 := by
        linarith
      have hy2_le : y ^ 2 ≤ 22 ^ 2 := by
        have : (|y| : ℤ) * |y| ≤ 22 * 22 :=
          mul_le_mul hle hle (abs_nonneg _) (by norm_num)
        simpa [pow_two, abs_mul_self] using this
      have : False := by
        linarith [hy, hy2_le]
      exact this
  | inr hge =>
      have hy2_ge : (23 : ℤ) ^ 2 ≤ y ^ 2 := by
        have : (23 : ℤ) ≤ |y| := hge
        have : (23 : ℤ) * 23 ≤ |y| * |y| :=
          mul_le_mul this this (by norm_num) (by norm_num)
        simpa [pow_two, abs_mul_self] using this
      have : False := by
        linarith [hy, hy2_ge]
      exact this

theorem h_not_one_h_d_eq13_aime_1987_p5 (x : ℤ) (h_one_ne : (1 + 3 * x ^ 2) ≠ 1) :
  (1 + 3 * x ^ 2) ≠ 1 := by
  exact h_one_ne

theorem h_eq13_h_d_eq13_aime_1987_p5 (x : ℤ)
    (h_possible :
      (1 + 3 * x ^ 2) = 1 ∨ (1 + 3 * x ^ 2) = 13 ∨ (1 + 3 * x ^ 2) = 169)
    (h_not_one : (1 + 3 * x ^ 2) ≠ 1)
    (h_not_169 : (1 + 3 * x ^ 2) ≠ 169) :
    1 + 3 * x ^ 2 = 13 := by
  rcases h_possible with h1 | h2 | h3
  · cases (h_not_one h1)
  · exact h2
  · cases (h_not_169 h3)

theorem h_pos_h_d_eq13_aime_1987_p5 (x : ℤ) (h_div507 : (1 + 3 * x ^ 2) ∣ 507) :
  0 < 1 + 3 * x ^ 2 := by
  -- `x²` is non‑negative
  have hx2 : (0 : ℤ) ≤ x ^ 2 := by
    exact sq_nonneg _
  -- `3` is non‑negative
  have h3 : (0 : ℤ) ≤ (3 : ℤ) := by
    norm_num
  -- therefore `3 * x²` is non‑negative
  have h_nonneg : (0 : ℤ) ≤ 3 * x ^ 2 := by
    exact mul_nonneg h3 hx2
  -- add `1` to both sides, getting `1 ≤ 1 + 3 * x²`
  have h_one_le : (1 : ℤ) ≤ 1 + 3 * x ^ 2 := by
    simpa using add_le_add_left h_nonneg (1 : ℤ)
  -- combine `0 < 1` with `1 ≤ 1 + 3 * x²`
  exact lt_of_lt_of_le zero_lt_one h_one_le

theorem h_possible_h_d_eq13_aime_1987_p5 (x : ℤ) (h_div507 : (1 + 3 * x ^ 2) ∣ 507)
    (h_mod3 : (1 + 3 * x ^ 2) % 3 = 1)
    (h_divisors :
      (1 + 3 * x ^ 2) = 1 ∨ (1 + 3 * x ^ 2) = 3 ∨ (1 + 3 * x ^ 2) = 13 ∨
      (1 + 3 * x ^ 2) = 39 ∨ (1 + 3 * x ^ 2) = 169 ∨ (1 + 3 * x ^ 2) = 507) :
    (1 + 3 * x ^ 2) = 1 ∨ (1 + 3 * x ^ 2) = 13 ∨ (1 + 3 * x ^ 2) = 169 := by
  rcases h_divisors with h1 | h2 | h3 | h4 | h5 | h6
  · exact Or.inl h1
  · exfalso
    have h0 : (1 + 3 * x ^ 2) % 3 = 0 := by
      simpa [h2] using (by norm_num : (3 : ℤ) % 3 = 0)
    have : (0 : ℤ) = 1 := by
      simpa [h0] using h_mod3
    exact (zero_ne_one (α := ℤ) this)
  · exact Or.inr (Or.inl h3)
  · exfalso
    have h0 : (1 + 3 * x ^ 2) % 3 = 0 := by
      simpa [h4] using (by norm_num : (39 : ℤ) % 3 = 0)
    have : (0 : ℤ) = 1 := by
      simpa [h0] using h_mod3
    exact (zero_ne_one (α := ℤ) this)
  · exact Or.inr (Or.inr h5)
  · exfalso
    have h0 : (1 + 3 * x ^ 2) % 3 = 0 := by
      simpa [h6] using (by norm_num : (507 : ℤ) % 3 = 0)
    have : (0 : ℤ) = 1 := by
      simpa [h0] using h_mod3
    exact (zero_ne_one (α := ℤ) this)

theorem h_mod3_h_d_eq13_aime_1987_p5 (x : ℤ) (h_div507 : (1 + 3 * x ^ 2) ∣ 507) :
  (1 + 3 * x ^ 2) % 3 = 1 := by
  -- 3 ≡ 0 (mod 3)
  have h3 : (3 : ℤ) ≡ 0 [ZMOD 3] := by
    simp
  -- multiply the congruence by x² on the right
  have hmul : (3 * x ^ 2) ≡ (0 : ℤ) [ZMOD 3] := by
    simpa [zero_mul] using (Int.ModEq.mul_right (x ^ 2) h3)
  -- add 1 to both sides
  have hadd : (1 + 3 * x ^ 2) ≡ (1 : ℤ) [ZMOD 3] := by
    simpa using (Int.ModEq.add_left 1 hmul)
  -- unfold ModEq to obtain the statement about remainders
  simpa [Int.ModEq] using hadd

theorem h_eq'_h_not_169_h_d_eq13_aime_1987_p5 (x : ℤ) (h_eq : (1 + 3 * x ^ 2) = (169 : ℤ)) :
  1 + 3 * x ^ 2 = (169 : ℤ) := by
  exact h_eq

theorem h_false_h_not_169_h_d_eq13_aime_1987_p5 (x : ℤ) (h_sq : x ^ 2 = 56) (h_not_sq : x ^ 2 = 56 → False) :
  False := by
  exact h_not_sq h_sq

theorem h_sq_h_not_169_h_d_eq13_aime_1987_p5 (x : ℤ) (h_div507 : (1 + 3 * x ^ 2) ∣ 507)
    (h_eq' : 1 + 3 * x ^ 2 = (169 : ℤ)) :
    x ^ 2 = 56 := by
  -- From the given equality obtain a linear equation in `x ^ 2`.
  have h1 : 3 * x ^ 2 = (168 : ℤ) := by
    have := congrArg (fun z : ℤ => z - 1) h_eq'
    simpa using this
  -- Rewrite the right‑hand side as a multiple of `3`.
  have h2 : 3 * x ^ 2 = 3 * (56 : ℤ) := by
    simpa [ (by norm_num : (168 : ℤ) = 3 * 56) ] using h1
  -- Cancel the non‑zero factor `3`.
  have h3 : (3 : ℤ) ≠ 0 := by norm_num
  have hx2 : x ^ 2 = (56 : ℤ) := mul_left_cancel₀ h3 h2
  simpa using hx2

theorem h_not_sq_h_not_169_h_d_eq13_aime_1987_p5 (x : ℤ) :
  x ^ 2 = 56 → False := by
  intro hsq
  -- rewrite the equality using `|x|`
  have habs : (|x| : ℤ) ^ 2 = 56 := by
    simpa [pow_two, abs_mul_self] using hsq
  -- split on whether `|x|` is < 8 or ≥ 8
  have h_cases : (|x| : ℤ) < 8 ∨ 8 ≤ |x| := lt_or_ge _ _
  cases h_cases with
  | inl hlt =>
      -- from `|x| < 8` we get `|x| ≤ 7`
      have hle : (|x| : ℤ) ≤ 7 := by
        linarith
      -- square the inequality
      have hle_sq : (|x| : ℤ) ^ 2 ≤ 7 ^ 2 := by
        have := mul_le_mul hle hle (abs_nonneg _) (by decide : (0 : ℤ) ≤ (7 : ℤ))
        simpa [pow_two] using this
      -- rewrite using `habs` and obtain a contradiction
      have : (56 : ℤ) ≤ 49 := by
        simpa [habs] using hle_sq
      linarith
  | inr hge =>
      -- square the inequality `8 ≤ |x|`
      have hge_sq : (8 : ℤ) ^ 2 ≤ (|x| : ℤ) ^ 2 := by
        have := mul_le_mul hge hge (by decide : (0 : ℤ) ≤ (8 : ℤ)) (abs_nonneg _)
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
      -- rewrite using `habs` and obtain a contradiction
      have : (64 : ℤ) ≤ 56 := by
        simpa [habs] using hge_sq
      linarith

theorem h_not_169_h_d_eq13_aime_1987_p5 (x : ℤ) (h_div507 : (1 + 3 * x ^ 2) ∣ 507) :
  (1 + 3 * x ^ 2) ≠ 169 := by
  intro h_eq
  have h_eq' : 1 + 3 * x ^ 2 = (169 : ℤ) := by
    exact h_eq'_h_not_169_h_d_eq13_aime_1987_p5 x h_eq
  have h_sq : x ^ 2 = 56 := by
    exact h_sq_h_not_169_h_d_eq13_aime_1987_p5 x h_div507 h_eq'
  have h_not_sq : (x ^ 2 = 56) → False := by
    exact h_not_sq_h_not_169_h_d_eq13_aime_1987_p5 x
  have h_false : False := by
    exact h_false_h_not_169_h_d_eq13_aime_1987_p5 x h_sq h_not_sq
  exact h_false

theorem h_eq_three_h_divisors_h_d_eq13_aime_1987_p5 (x : ℤ)
    (h_natAbs_eq : ((1 + 3 * x ^ 2).natAbs : ℤ) = 1 + 3 * x ^ 2)
    (h3 : (1 + 3 * x ^ 2).natAbs = 3) :
    (1 + 3 * x ^ 2) = (3 : ℤ) := by
  -- Cast the equality of natural absolute values to an equality in ℤ
  have h3z : ((1 + 3 * x ^ 2).natAbs : ℤ) = (3 : ℤ) := by
    simpa using congrArg (fun n : ℕ => (n : ℤ)) h3
  -- Use the given equality linking the cast of `natAbs` with the original integer
  calc
    (1 + 3 * x ^ 2) = ((1 + 3 * x ^ 2).natAbs : ℤ) := by
      symm
      exact h_natAbs_eq
    _ = (3 : ℤ) := h3z

theorem h_dvd_nat_h_divisors_h_d_eq13_aime_1987_p5 (x : ℤ) (h_div507 : (1 + 3 * x ^ 2) ∣ 507) :
    (1 + 3 * x ^ 2).natAbs ∣ (507 : ℕ) := by
  simpa using (Int.dvd_natCast).1 h_div507

theorem h_eq_one_h_divisors_h_d_eq13_aime_1987_p5 (x : ℤ)
    (h_natAbs_eq : ((1 + 3 * x ^ 2).natAbs : ℤ) = 1 + 3 * x ^ 2)
    (h1 : (1 + 3 * x ^ 2).natAbs = 1) :
    (1 + 3 * x ^ 2) = (1 : ℤ) := by
  -- Rewrite the equality involving the casted `natAbs` using the fact that the `natAbs` is `1`.
  have h_eq : (1 : ℤ) = 1 + 3 * x ^ 2 := by
    simpa [h1] using h_natAbs_eq
  -- Flip the equality to match the goal.
  simpa using h_eq.symm

theorem h_pos_h_divisors_h_d_eq13_aime_1987_p5 (x : ℤ) (h_div507 : (1 + 3 * x ^ 2) ∣ 507) :
    (0 : ℤ) < 1 + 3 * x ^ 2 := by
  -- the divisor hypothesis is not needed for the positivity argument
  have h_nonneg : (0 : ℤ) ≤ 3 * x ^ 2 := by
    have hx2 : (0 : ℤ) ≤ x ^ 2 := by
      exact sq_nonneg x
    have h3 : (0 : ℤ) ≤ (3 : ℤ) := by
      norm_num
    exact mul_nonneg h3 hx2
  have h_one_le : (1 : ℤ) ≤ 1 + 3 * x ^ 2 := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (add_le_add_left h_nonneg (1 : ℤ))
  exact lt_of_lt_of_le zero_lt_one h_one_le

theorem h_eq_thirteen_h_divisors_h_d_eq13_aime_1987_p5 (x : ℤ)
    (h_natAbs_eq : ((1 + 3 * x ^ 2).natAbs : ℤ) = 1 + 3 * x ^ 2)
    (h13 : (1 + 3 * x ^ 2).natAbs = 13) :
    (1 + 3 * x ^ 2) = (13 : ℤ) := by
  -- Cast the equality on `ℕ` to an equality on `ℤ`
  have h_cast : ((1 + 3 * x ^ 2).natAbs : ℤ) = (13 : ℤ) := by
    exact_mod_cast h13
  -- Rewrite using the hypothesis that the integer equals its casted `natAbs`
  have h1 : (1 + 3 * x ^ 2) = ((1 + 3 * x ^ 2).natAbs : ℤ) := by
    simpa using h_natAbs_eq.symm
  calc
    (1 + 3 * x ^ 2) = ((1 + 3 * x ^ 2).natAbs : ℤ) := h1
    _ = (13 : ℤ) := h_cast

theorem h_eq_thirtynine_h_divisors_h_d_eq13_aime_1987_p5 (x : ℤ)
    (h_natAbs_eq : ((1 + 3 * x ^ 2).natAbs : ℤ) = 1 + 3 * x ^ 2)
    (h39 : (1 + 3 * x ^ 2).natAbs = 39) :
    (1 + 3 * x ^ 2) = (39 : ℤ) := by
  -- rewrite the goal using the equality that relates `natAbs` to the integer expression
  rw [← h_natAbs_eq]
  -- now the goal is an equality of ℤ obtained from an equality of ℕ, which we can close by casting
  exact_mod_cast h39

theorem h_eq_onehundredsixtynine_h_divisors_h_d_eq13_aime_1987_p5 (x : ℤ)
    (h_natAbs_eq : ((1 + 3 * x ^ 2).natAbs : ℤ) = 1 + 3 * x ^ 2)
    (h169 : (1 + 3 * x ^ 2).natAbs = 169) :
    (1 + 3 * x ^ 2) = (169 : ℤ) := by
  -- rewrite the left‑hand side using the equality of the integer cast of `natAbs`
  rw [← h_natAbs_eq]
  -- now both sides are casts of natural numbers; replace `natAbs` by `169`
  simpa [h169]

theorem h_eq_fiveohseven_h_divisors_h_d_eq13_aime_1987_p5 (x : ℤ)
    (h_natAbs_eq : ((1 + 3 * x ^ 2).natAbs : ℤ) = 1 + 3 * x ^ 2)
    (h507 : (1 + 3 * x ^ 2).natAbs = 507) :
    (1 + 3 * x ^ 2) = (507 : ℤ) := by
  -- cast the equality of natural numbers to an equality in ℤ
  have h_cast : ((1 + 3 * x ^ 2).natAbs : ℤ) = (507 : ℤ) := by
    simpa using congrArg (fun n : ℕ => (n : ℤ)) h507
  -- use the given equality relating the integer to its natAbs
  calc
    (1 + 3 * x ^ 2) = ((1 + 3 * x ^ 2).natAbs : ℤ) := by
      symm
      exact h_natAbs_eq
    _ = (507 : ℤ) := h_cast

theorem h_natAbs_eq_h_divisors_h_d_eq13_aime_1987_p5 (x : ℤ) (h_pos : (0 : ℤ) < 1 + 3 * x ^ 2) :
    ((1 + 3 * x ^ 2).natAbs : ℤ) = 1 + 3 * x ^ 2 := by
  have h_nonneg : (0 : ℤ) ≤ 1 + 3 * x ^ 2 := le_of_lt h_pos
  simpa [abs_of_nonneg h_nonneg] using (Int.ofNat_natAbs (1 + 3 * x ^ 2))

theorem h_cases_nat_h_divisors_h_d_eq13_aime_1987_p5 (x : ℤ)
    (h_dvd_nat : (1 + 3 * x ^ 2).natAbs ∣ (507 : ℕ)) :
    (1 + 3 * x ^ 2).natAbs = 1 ∨ (1 + 3 * x ^ 2).natAbs = 3 ∨
    (1 + 3 * x ^ 2).natAbs = 13 ∨ (1 + 3 * x ^ 2).natAbs = 39 ∨
    (1 + 3 * x ^ 2).natAbs = 169 ∨ (1 + 3 * x ^ 2).natAbs = 507 := by
  classical
  have hmem : (1 + 3 * x ^ 2).natAbs ∈ Nat.divisors 507 :=
    (Nat.mem_divisors).2 ⟨h_dvd_nat, by decide⟩
  have hdivs : Nat.divisors 507 = ({1, 3, 13, 39, 169, 507} : Finset ℕ) := by
    decide
  have hmem' :
      (1 + 3 * x ^ 2).natAbs ∈ ({1, 3, 13, 39, 169, 507} : Finset ℕ) := by
    simpa [hdivs] using hmem
  simpa [Finset.mem_insert, Finset.mem_singleton,
        _root_.or_comm, _root_.or_left_comm, _root_.or_assoc] using hmem'

theorem h_divisors_h_d_eq13_aime_1987_p5 (x : ℤ) (h_div507 : (1 + 3 * x ^ 2) ∣ 507) :
    (1 + 3 * x ^ 2) = 1 ∨ (1 + 3 * x ^ 2) = 3 ∨ (1 + 3 * x ^ 2) = 13 ∨
    (1 + 3 * x ^ 2) = 39 ∨ (1 + 3 * x ^ 2) = 169 ∨ (1 + 3 * x ^ 2) = 507 := by
  -- 1. Positivity of the divisor.
  have h_pos := h_pos_h_divisors_h_d_eq13_aime_1987_p5 x h_div507
  -- 2. Equality of `natAbs` cast to ℤ with the integer itself.
  have h_natAbs_eq :=
    h_natAbs_eq_h_divisors_h_d_eq13_aime_1987_p5 x h_pos
  -- 3. Translate integer divisibility to natural divisibility.
  have h_dvd_nat :=
    h_dvd_nat_h_divisors_h_d_eq13_aime_1987_p5 x h_div507
  -- 4. Enumerate all possible natural divisors of 507.
  have h_cases_nat :=
    h_cases_nat_h_divisors_h_d_eq13_aime_1987_p5 x h_dvd_nat
  -- 5. Convert each natural‑number case to the required integer equality.
  rcases h_cases_nat with h1 | h2 | h3 | h4 | h5 | h6
  ·
    left
    have : (1 + 3 * x ^ 2) = (1 : ℤ) :=
      h_eq_one_h_divisors_h_d_eq13_aime_1987_p5 x h_natAbs_eq h1
    simpa using this
  ·
    right; left
    have : (1 + 3 * x ^ 2) = (3 : ℤ) :=
      h_eq_three_h_divisors_h_d_eq13_aime_1987_p5 x h_natAbs_eq h2
    simpa using this
  ·
    right; right; left
    have : (1 + 3 * x ^ 2) = (13 : ℤ) :=
      h_eq_thirteen_h_divisors_h_d_eq13_aime_1987_p5 x h_natAbs_eq h3
    simpa using this
  ·
    right; right; right; left
    have : (1 + 3 * x ^ 2) = (39 : ℤ) :=
      h_eq_thirtynine_h_divisors_h_d_eq13_aime_1987_p5 x h_natAbs_eq h4
    simpa using this
  ·
    right; right; right; right; left
    have : (1 + 3 * x ^ 2) = (169 : ℤ) :=
      h_eq_onehundredsixtynine_h_divisors_h_d_eq13_aime_1987_p5 x h_natAbs_eq h5
    simpa using this
  ·
    right; right; right; right; right
    have : (1 + 3 * x ^ 2) = (507 : ℤ) :=
      h_eq_fiveohseven_h_divisors_h_d_eq13_aime_1987_p5 x h_natAbs_eq h6
    simpa using this

theorem h_d_eq13_aime_1987_p5 (x : ℤ)
    (h_div507 : (1 + 3 * x ^ 2) ∣ 507)
    (h_one_ne : (1 + 3 * x ^ 2) ≠ 1) :
    1 + 3 * x ^ 2 = 13 := by
  -- positivity of the divisor
  have h_pos : 0 < 1 + 3 * x ^ 2 := by
    exact h_pos_h_d_eq13_aime_1987_p5 x h_div507
  -- residue modulo 3
  have h_mod3 : (1 + 3 * x ^ 2) % 3 = 1 := by
    exact h_mod3_h_d_eq13_aime_1987_p5 x h_div507
  -- exhaustive list of positive divisors of 507
  have h_divisors :
      (1 + 3 * x ^ 2) = 1 ∨ (1 + 3 * x ^ 2) = 3 ∨ (1 + 3 * x ^ 2) = 13 ∨
      (1 + 3 * x ^ 2) = 39 ∨ (1 + 3 * x ^ 2) = 169 ∨ (1 + 3 * x ^ 2) = 507 := by
    exact h_divisors_h_d_eq13_aime_1987_p5 x h_div507
  -- restrict to those congruent to 1 (mod 3)
  have h_possible :
      (1 + 3 * x ^ 2) = 1 ∨ (1 + 3 * x ^ 2) = 13 ∨ (1 + 3 * x ^ 2) = 169 := by
    exact h_possible_h_d_eq13_aime_1987_p5 x h_div507 h_mod3 h_divisors
  -- eliminate the case = 1 using the hypothesis
  have h_not_one : (1 + 3 * x ^ 2) ≠ 1 := by
    exact h_not_one_h_d_eq13_aime_1987_p5 x h_one_ne
  -- eliminate the case = 169 (it would give x² = 56, impossible)
  have h_not_169 : (1 + 3 * x ^ 2) ≠ 169 := by
    exact h_not_169_h_d_eq13_aime_1987_p5 x h_div507
  -- the only remaining possibility is 13
  have h_eq13 : 1 + 3 * x ^ 2 = 13 := by
    exact h_eq13_h_d_eq13_aime_1987_p5 x h_possible h_not_one h_not_169
  exact h_eq13

theorem aime_1987_p5 (x y : ℤ) (h₀ : y ^ 2 + 3 * (x ^ 2 * y ^ 2) = 30 * x ^ 2 + 517) :
    3 * (x ^ 2 * y ^ 2) = 588 := by
  have hA_def := hA_def_aime_1987_p5 x y
  have h_y_sq := h_y_sq_aime_1987_p5 x y h₀
  have h_eq6 := h_eq6_aime_1987_p5 x y h₀
  have h_div1 := h_div1_aime_1987_p5 x y h_eq6
  have h_not_x0 := h_not_x0_aime_1987_p5 x y h₀
  have hx2_ne := hx2_ne_aime_1987_p5 x y h_not_x0
  have h_div2 := h_div2_aime_1987_p5 x y h_div1 hx2_ne
  have h_mod := h_mod_aime_1987_p5 x
  have h_div507 := h_div507_aime_1987_p5 x h_div2 h_mod
  have h_one_ne := h_one_ne_aime_1987_p5 x h_not_x0
  have h_d_eq13 := h_d_eq13_aime_1987_p5 x h_div507 h_one_ne
  have hx_sq := hx_sq_aime_1987_p5 x h_d_eq13
  have hA_val := hA_val_aime_1987_p5 x y hx_sq h₀
  have hfinal := hfinal_aime_1987_p5 x y hA_val
  exact hfinal

import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem backward_imo_2019_p1 (f : ℤ → ℤ) :
    (∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c) →
    ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
  intro hf
  have h_main : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
    by_cases h : ∀ z, f z = 0
    · -- Case 1: f is identically zero
      intro a b
      have h₁ : f (2 * a) = 0 := h (2 * a)
      have h₂ : f b = 0 := h b
      have h₃ : f (a + b) = 0 := h (a + b)
      have h₄ : f (f (a + b)) = 0 := by
        have h₅ : f (a + b) = 0 := h (a + b)
        have h₆ : f (f (a + b)) = f 0 := by rw [h₅]
        have h₇ : f 0 = 0 := h 0
        rw [h₆, h₇]
      -- Simplify the equation using the fact that f is zero everywhere
      simp [h₁, h₂, h₄]
    · -- Case 2: f is not identically zero
      -- There exists some z₀ such that f(z₀) ≠ 0
      have h₁ : ∃ z₀, f z₀ ≠ 0 := by
        by_contra h₁
        push_neg at h₁
        have h₂ : ∀ z, f z = 0 := by simpa using h₁
        exact h h₂
      -- Obtain z₀ such that f(z₀) ≠ 0
      obtain ⟨z₀, hz₀⟩ := h₁
      -- By the hypothesis, there exists c such that for all z, f(z) = 2z + c
      have h₂ : ∃ c, ∀ z, f z = 2 * z + c := by
        have h₃ : f z₀ = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := hf z₀
        cases h₃ with
        | inl h₃ =>
          exfalso
          apply hz₀
          exact h₃
        | inr h₃ =>
          exact h₃
      -- Obtain c such that for all z, f(z) = 2z + c
      obtain ⟨c, hc⟩ := h₂
      -- Prove the main equation using the form f(z) = 2z + c
      intro a b
      have h₃ : f (2 * a) = 2 * (2 * a) + c := by
        have h₄ := hc (2 * a)
        linarith
      have h₄ : f b = 2 * b + c := by
        have h₅ := hc b
        linarith
      have h₅ : f (a + b) = 2 * (a + b) + c := by
        have h₆ := hc (a + b)
        linarith
      have h₆ : f (f (a + b)) = 2 * (f (a + b)) + c := by
        have h₇ := hc (f (a + b))
        linarith
      -- Substitute and simplify the equation
      have h₇ : f (2 * a) + 2 * f b = 4 * a + c + 2 * (2 * b + c) := by
        rw [h₃, h₄]
        <;> ring_nf
        <;> linarith
      have h₈ : f (f (a + b)) = 2 * (2 * (a + b) + c) + c := by
        rw [h₆, h₅]
        <;> ring_nf
        <;> linarith
      have h₉ : f (2 * a) + 2 * f b = f (f (a + b)) := by
        calc
          f (2 * a) + 2 * f b = 4 * a + c + 2 * (2 * b + c) := by rw [h₇]
          _ = 4 * a + c + 4 * b + 2 * c := by ring_nf
          _ = 4 * a + 4 * b + 3 * c := by ring_nf
          _ = 2 * (2 * (a + b) + c) + c := by ring_nf
          _ = f (f (a + b)) := by
            rw [h₈]
            <;> ring_nf
            <;> linarith
      exact h₉
  exact h_main

theorem hf_f_forward_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) :
    ∀ b : ℤ, f (f b) = 2 * f b + f 0 := by
  have h_main : ∀ (b : ℤ), f (f b) = 2 * f b + f 0 := by
    intro b
    have h₁ : f (2 * (0 : ℤ)) + 2 * f b = f (f (0 + b)) := h 0 b
    have h₂ : f (2 * (0 : ℤ)) = f 0 := by norm_num
    have h₃ : f (f (0 + b)) = f (f b) := by simp [add_zero]
    have h₄ : f 0 + 2 * f b = f (f b) := by
      linarith
    linarith
  
  exact h_main

theorem hf_two_forward_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (hf_f : ∀ b : ℤ, f (f b) = 2 * f b + f 0) :
    ∀ a : ℤ, f (2 * a) = 2 * f a - f 0 := by
  have h₁ : ∀ a : ℤ, f (2 * a) = 2 * f a - f 0 := by
    intro a
    have h₂ := h a 0
    have h₃ := h 0 a
    have h₄ := h a (-a)
    have h₅ := hf_f 0
    have h₆ := hf_f a
    have h₇ := hf_f (-a)
    have h₈ := hf_f (a + 0)
    have h₉ := hf_f (a + (-a))
    have h₁₀ := h a a
    have h₁₁ := h (-a) a
    have h₁₂ := h a (a + 1)
    have h₁₃ := h (a + 1) a
    have h₁₄ := h 0 0
    have h₁₅ := h 1 0
    have h₁₆ := h 0 1
    have h₁₇ := h 1 1
    have h₁₈ := h (-1) 0
    have h₁₉ := h 0 (-1)
    have h₂₀ := h 1 (-1)
    have h₂₁ := h (-1) 1
    -- Simplify the equations to find a pattern or specific values
    ring_nf at h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆ h₁₇ h₁₈ h₁₉ h₂₀ h₂₁ ⊢
    -- Use linear arithmetic to solve for f(2a)
    nlinarith [h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀, h₂₁]
  exact h₁

theorem hadd_g_forward_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (hf_f : ∀ b : ℤ, f (f b) = 2 * f b + f 0)
    (hf_two : ∀ a : ℤ, f (2 * a) = 2 * f a - f 0)
    (hadd : ∀ a b : ℤ, f (a + b) = f a + f b - f 0) :
    ∀ a b : ℤ, (f (a + b) - f 0) = (f a - f 0) + (f b - f 0) := by
  have h_main : ∀ (a b : ℤ), (f (a + b) - f 0) = (f a - f 0) + (f b - f 0) := by
    intro a b
    have h1 : f (a + b) = f a + f b - f 0 := hadd a b
    have h2 : f (a + b) - f 0 = (f a + f b - f 0) - f 0 := by rw [h1]
    have h3 : (f a - f 0) + (f b - f 0) = f a + f b - 2 * f 0 := by
      ring
    have h4 : f (a + b) - f 0 = f a + f b - 2 * f 0 := by
      calc
        f (a + b) - f 0 = (f a + f b - f 0) - f 0 := by rw [h1]
        _ = f a + f b - 2 * f 0 := by ring
    have h5 : (f a - f 0) + (f b - f 0) = f a + f b - 2 * f 0 := by
      ring
    linarith
  exact h_main

theorem hadd_forward_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (hf_f : ∀ b : ℤ, f (f b) = 2 * f b + f 0)
    (hf_two : ∀ a : ℤ, f (2 * a) = 2 * f a - f 0) :
    ∀ a b : ℤ, f (a + b) = f a + f b - f 0 := by
  have h_main : ∀ (a b : ℤ), f (a + b) = f a + f b - f 0 := by
    intro a b
    have h1 : f (2 * a) + 2 * f b = f (f (a + b)) := h a b
    have h2 : f (f (a + b)) = 2 * f (a + b) + f 0 := by
      have h3 := hf_f (a + b)
      exact h3
    have h4 : f (2 * a) = 2 * f a - f 0 := hf_two a
    have h5 : (2 * f a - f 0) + 2 * f b = 2 * f (a + b) + f 0 := by
      calc
        (2 * f a - f 0) + 2 * f b = f (2 * a) + 2 * f b := by rw [h4]
        _ = f (f (a + b)) := by rw [h1]
        _ = 2 * f (a + b) + f 0 := by rw [h2]
    have h6 : 2 * f a + 2 * f b - f 0 = 2 * f (a + b) + f 0 := by
      linarith
    have h7 : 2 * f a + 2 * f b - 2 * f 0 = 2 * f (a + b) := by
      linarith
    have h8 : f a + f b - f 0 = f (a + b) := by
      linarith
    linarith
  exact h_main

theorem hcoeff_forward_imo_2019_p1 (k c : ℤ)
    (hcond :
        ∀ a b : ℤ,
          k * (2 * a) + c + 2 * (k * b + c) = k * (k * (a + b) + c) + c) :
    (k = 0 ∨ k = 2) := by
  have h1 : 2 * c = k * c := by
    have h1_1 := hcond 0 0
    ring_nf at h1_1 ⊢
    linarith
  
  have h2 : 2 * k + 2 * c = k^2 + k * c := by
    have h2_1 := hcond 1 0
    ring_nf at h2_1 ⊢
    linarith
  
  have h3 : 2 * k = k^2 := by
    have h3_1 : 2 * k + 2 * c = k ^ 2 + k * c := h2
    have h3_2 : 2 * c = k * c := h1
    have h3_3 : 2 * k + (k * c) = k ^ 2 + k * c := by
      linarith
    linarith
  
  have h4 : k = 0 ∨ k = 2 := by
    have h4_1 : k ^ 2 - 2 * k = 0 := by
      linarith
    have h4_2 : k * (k - 2) = 0 := by
      ring_nf at h4_1 ⊢
      <;> linarith
    have h4_3 : k = 0 ∨ k - 2 = 0 := by
      have h4_4 : k * (k - 2) = 0 := h4_2
      have h4_5 : k = 0 ∨ k - 2 = 0 := by
        apply eq_zero_or_eq_zero_of_mul_eq_zero h4_4
      exact h4_5
    cases h4_3 with
    | inl h4_6 =>
      exact Or.inl h4_6
    | inr h4_6 =>
      have h4_7 : k = 2 := by
        linarith
      exact Or.inr h4_7
  
  exact h4

theorem hlinear_forward_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (hf_f : ∀ b : ℤ, f (f b) = 2 * f b + f 0)
    (hf_two : ∀ a : ℤ, f (2 * a) = 2 * f a - f 0)
    (hadd : ∀ a b : ℤ, f (a + b) = f a + f b - f 0)
    (hadd_g : ∀ a b : ℤ, (f (a + b) - f 0) = (f a - f 0) + (f b - f 0)) :
    ∃ k c : ℤ, ∀ z : ℤ, f z = k * z + c := by
  have h_main : ∃ (k c : ℤ), ∀ (z : ℤ), f z = k * z + c := by
    use (f 1 - f 0)
    use f 0
    intro z
    have h₁ : ∀ n : ℕ, f n = (f 1 - f 0) * n + f 0 := by
      intro n
      induction n with
      | zero =>
        simp [hadd]
        <;> ring_nf at *
        <;> linarith
      | succ n ih =>
        have h₂ := hadd n 1
        have h₃ := hadd_g n 1
        simp [ih] at h₂ h₃ ⊢
        <;> ring_nf at *
        <;> linarith
    have h₂ : ∀ n : ℕ, f (-n : ℤ) = (f 1 - f 0) * (-n : ℤ) + f 0 := by
      intro n
      induction n with
      | zero =>
        simp [hadd]
        <;> ring_nf at *
        <;> linarith
      | succ n ih =>
        have h₃ := hadd (-(n : ℤ) - 1) 1
        have h₄ := hadd_g (-(n : ℤ) - 1) 1
        have h₅ := hadd (-(n : ℤ)) (-1)
        have h₆ := hadd_g (-(n : ℤ)) (-1)
        simp [ih] at h₃ h₄ h₅ h₆ ⊢
        <;> ring_nf at *
        <;> linarith
    -- Now we need to handle arbitrary integers z
    have h₃ : ∀ z : ℤ, f z = (f 1 - f 0) * z + f 0 := by
      intro z
      -- Consider the cases where z is non-negative or negative
      cases' le_or_lt 0 z with hz hz
      · -- Case: z ≥ 0
        have h₄ : ∃ n : ℕ, z = n := by
          use z.toNat
          <;> simp_all [Int.toNat_of_nonneg hz]
          <;> linarith
        obtain ⟨n, rfl⟩ := h₄
        have h₅ := h₁ n
        simp at h₅ ⊢
        <;> ring_nf at *
        <;> linarith
      · -- Case: z < 0
        have h₄ : ∃ n : ℕ, z = -n := by
          use (-z).toNat
          <;> simp_all [Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ -z)]
          <;> linarith
        obtain ⟨n, rfl⟩ := h₄
        have h₅ := h₂ n
        simp at h₅ ⊢
        <;> ring_nf at *
        <;> linarith
    have h₄ := h₃ z
    linarith
  exact h_main

theorem hfinal_forward_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (hf_f : ∀ b : ℤ, f (f b) = 2 * f b + f 0)
    (hf_two : ∀ a : ℤ, f (2 * a) = 2 * f a - f 0)
    (hadd : ∀ a b : ℤ, f (a + b) = f a + f b - f 0)
    (hadd_g : ∀ a b : ℤ, (f (a + b) - f 0) = (f a - f 0) + (f b - f 0))
    (hlinear : ∃ k c : ℤ, ∀ z : ℤ, f z = k * z + c)
    (hcoeff :
        ∀ k c : ℤ,
          (∀ a b : ℤ,
              k * (2 * a) + c + 2 * (k * b + c) = k * (k * (a + b) + c) + c) →
          (k = 0 ∨ k = 2)) :
    (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  have h_main : (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
    obtain ⟨k, c, hf⟩ := hlinear
    have h1 : k = 0 ∨ k = 2 := by
      have h2 : ∀ (b : ℤ), (k * k) * b + k * c + c = 2 * k * b + 3 * c := by
        intro b
        have h3 := hf_f b
        have h4 := hf (f b)
        have h5 := hf b
        have h6 := hf 0
        have h7 := hf (k * b + c)
        simp only [hf] at h3 h4 h5 h6 h7 ⊢
        ring_nf at h3 h4 h5 h6 h7 ⊢
        <;> nlinarith
      have h8 : k * k = 2 * k := by
        have h9 := h2 1
        have h10 := h2 0
        have h11 := h2 (-1)
        ring_nf at h9 h10 h11 ⊢
        nlinarith
      have h9 : k * c = 2 * c := by
        have h10 := h2 0
        have h11 := h2 1
        have h12 := h2 (-1)
        ring_nf at h10 h11 h12 ⊢
        nlinarith
      have h10 : k = 0 ∨ k = 2 := by
        have h11 : k * (k - 2) = 0 := by
          nlinarith
        have h12 : k = 0 ∨ k - 2 = 0 := by
          apply eq_zero_or_eq_zero_of_mul_eq_zero h11
        cases h12 with
        | inl h12 =>
          exact Or.inl h12
        | inr h12 =>
          have h13 : k = 2 := by
            linarith
          exact Or.inr h13
      exact h10
    cases h1 with
    | inl h1 =>
      have h2 : c = 0 := by
        have h3 := hf_f 0
        have h4 := hf 0
        have h5 := hf c
        simp only [hf, h1] at h3 h4 h5 ⊢
        <;> ring_nf at h3 h4 h5 ⊢ <;> nlinarith
      have h3 : ∀ z, f z = 0 := by
        intro z
        have h4 := hf z
        simp only [h1, h2] at h4 ⊢
        <;> ring_nf at h4 ⊢ <;> linarith
      exact Or.inl h3
    | inr h1 =>
      have h2 : ∃ c, ∀ z, f z = 2 * z + c := by
        refine' ⟨c, _⟩
        intro z
        have h3 := hf z
        simp only [h1] at h3 ⊢
        <;> ring_nf at h3 ⊢ <;> linarith
      exact Or.inr h2
  exact h_main

theorem forward_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) :
    ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  -- 1.  Expression for `f (f b)` obtained by setting `a = 0` in the hypothesis.
  have hf_f : ∀ b : ℤ, f (f b) = 2 * f b + f 0 :=
    hf_f_forward_imo_2019_p1 f h
  -- 2.  Expression for `f (2 * a)` obtained by setting `b = 0` and using `hf_f`.
  have hf_two : ∀ a : ℤ, f (2 * a) = 2 * f a - f 0 :=
    hf_two_forward_imo_2019_p1 f h hf_f
  -- 3.  Additive relation `f (a + b) = f a + f b - f 0` derived from `hf_two` and `hf_f`.
  have hadd : ∀ a b : ℤ, f (a + b) = f a + f b - f 0 :=
    hadd_forward_imo_2019_p1 f h hf_f hf_two
  -- 4.  Define `g z := f z - f 0` and show it is additive.
  have hadd_g : ∀ a b : ℤ, (f (a + b) - f 0) = (f a - f 0) + (f b - f 0) :=
    hadd_g_forward_imo_2019_p1 f h hf_f hf_two hadd
  -- 5.  From additivity of `g` on ℤ we obtain a linear description of `f`.
  have hlinear : ∃ k c : ℤ, ∀ z : ℤ, f z = k * z + c :=
    hlinear_forward_imo_2019_p1 f h hf_f hf_two hadd hadd_g
  -- 6.  Plug the linear form into the original functional equation and solve for `k`.
  have hcoeff :
      ∀ k c : ℤ,
        (∀ a b : ℤ,
            k * (2 * a) + c + 2 * (k * b + c) = k * (k * (a + b) + c) + c) →
        (k = 0 ∨ k = 2) :=
    by
      intro k c hcond
      exact hcoeff_forward_imo_2019_p1 k c hcond
  -- 7.  Combine the possibilities for `k` with the linear description to obtain the required dichotomy.
  have hfinal :
      (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c :=
    hfinal_forward_imo_2019_p1 f h hf_f hf_two hadd hadd_g hlinear hcoeff
  -- 8.  Transform `hfinal` into the statement required by the theorem.
  intro z
  cases hfinal with
  | inl hzero =>
      left
      exact hzero z
  | inr hlin =>
      right
      rcases hlin with ⟨c, hc⟩
      exact ⟨c, hc⟩

theorem imo_2019_p1 (f : ℤ → ℤ) :
    (∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) ↔
      ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  constructor
  · intro h
    have forward : ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c :=
      forward_imo_2019_p1 f h
    exact forward
  · intro h
    have backward :
        (∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c) →
        ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) :=
      backward_imo_2019_p1 f
    exact backward h

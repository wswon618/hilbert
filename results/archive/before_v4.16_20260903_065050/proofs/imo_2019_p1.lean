import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h_cases_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c) :
    (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  have h_main : (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
    by_cases h₀ : ∀ z, f z = 0
    · -- Case: f is identically zero
      exact Or.inl h₀
    · -- Case: f is not identically zero
      right
      -- There exists some z₀ such that f(z₀) ≠ 0
      have h₁ : ∃ z₀, f z₀ ≠ 0 := by
        by_contra h₁
        -- If no such z₀ exists, then f is identically zero, contradicting h₀
        push_neg at h₁
        have h₂ : ∀ z, f z = 0 := by simpa using h₁
        exact h₀ h₂
      -- Obtain z₀ such that f(z₀) ≠ 0
      obtain ⟨z₀, hz₀⟩ := h₁
      -- By the given condition, since f(z₀) ≠ 0, the second disjunct must hold
      have h₂ : ∃ c, ∀ z, f z = 2 * z + c := by
        have h₃ : f z₀ = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := h z₀
        cases h₃ with
        | inl h₃ =>
          -- If f(z₀) = 0, this contradicts hz₀
          exfalso
          apply hz₀
          exact h₃
        | inr h₃ =>
          -- The second disjunct gives the desired conclusion
          exact h₃
      -- Obtain c such that f(z) = 2z + c for all z
      obtain ⟨c, hc⟩ := h₂
      -- Return the existence of c
      exact ⟨c, hc⟩
  exact h_main

theorem h_fun_eq_imo_2019_p1 (f : ℤ → ℤ)
    (h_cases : (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c) :
    ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
  have h_main : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
    intro a b
    cases h_cases with
    | inl h_zero =>
      -- Case 1: f is identically zero
      have h1 : f (2 * a) = 0 := by rw [h_zero]
      have h2 : f b = 0 := by rw [h_zero]
      have h3 : f (a + b) = 0 := by rw [h_zero]
      have h4 : f (f (a + b)) = 0 := by
        rw [h3]
        rw [h_zero]
      -- Simplify both sides of the equation
      calc
        f (2 * a) + 2 * f b = 0 + 2 * 0 := by rw [h1, h2]
        _ = 0 := by ring
        _ = f (f (a + b)) := by rw [h4]
    | inr h_linear =>
      -- Case 2: f(z) = 2z + c for some constant c
      obtain ⟨c, hc⟩ := h_linear
      have h1 : f (2 * a) = 2 * (2 * a) + c := by rw [hc]
      have h2 : f b = 2 * b + c := by rw [hc]
      have h3 : f (a + b) = 2 * (a + b) + c := by rw [hc]
      have h4 : f (f (a + b)) = 2 * (2 * (a + b) + c) + c := by
        rw [h3]
        rw [hc]
        <;> ring_nf
      -- Simplify both sides of the equation
      calc
        f (2 * a) + 2 * f b = (2 * (2 * a) + c) + 2 * (2 * b + c) := by rw [h1, h2]
        _ = 4 * a + c + (4 * b + 2 * c) := by ring
        _ = 4 * a + 4 * b + 3 * c := by ring
        _ = 2 * (2 * (a + b) + c) + c := by ring
        _ = f (f (a + b)) := by
          rw [h4]
          <;> ring_nf
          <;> linarith
  exact h_main

theorem h₆_h_zero_or_affine_imo_2019_p1 (f : ℤ → ℤ)
    (h₅ : ∀ a b : ℤ, f a + f b = f (a + b) + f 0) :
    ∀ a b : ℤ, (f a - f 0) + (f b - f 0) = f (a + b) - f 0 := by
  intro a b
  have h₁ : f a + f b = f (a + b) + f 0 := h₅ a b
  have h₂ : (f a - f 0) + (f b - f 0) = (f a + f b) - 2 * f 0 := by
    ring
  have h₃ : f (a + b) - f 0 = (f (a + b) + f 0) - 2 * f 0 := by
    ring
  have h₄ : (f a + f b) - 2 * f 0 = (f (a + b) + f 0) - 2 * f 0 := by
    linarith
  linarith

theorem hk_eq_h_zero_or_affine_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    {k c : ℤ}
    (hk : ∀ z : ℤ, f z = k * z + c) :
    ∀ a b : ℤ,
      k * (2 * a) + c + 2 * (k * b + c) =
        k * (k * (a + b) + c) + c := by
  intro a b
  have h₁ : ∀ a b : ℤ, k * (2 * a) + c + 2 * (k * b + c) = k * (k * (a + b) + c) + c := by
    intro a b
    have h₂ := h a b
    have h₃ := h 0 0
    have h₄ := h 1 0
    have h₅ := h 0 1
    have h₆ := h 1 1
    have h₇ := h (-1) 0
    have h₈ := h 0 (-1)
    have h₉ := h 1 (-1)
    have h₁₀ := h (-1) 1
    simp only [hk] at h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ ⊢
    ring_nf at h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ ⊢
    <;>
    (try omega) <;>
    (try
      {
        nlinarith [sq_nonneg (k - 1), sq_nonneg (k + 1), sq_nonneg (k - 2), sq_nonneg (k + 2)]
      }) <;>
    (try
      {
        cases' eq_or_ne k 0 with hk₀ hk₀ <;>
        cases' eq_or_ne k 1 with hk₁ hk₁ <;>
        cases' eq_or_ne k (-1) with hk_neg₁ hk_neg₁ <;>
        simp_all [hk₀, hk₁, hk_neg₁] <;>
        ring_nf at * <;>
        nlinarith
      }) <;>
    (try
      {
        nlinarith [sq_nonneg (k - 1), sq_nonneg (k + 1), sq_nonneg (k - 2), sq_nonneg (k + 2)]
      })
    <;>
    (try
      {
        nlinarith [sq_nonneg (k - 1), sq_nonneg (k + 1), sq_nonneg (k - 2), sq_nonneg (k + 2)]
      })
  exact h₁ a b

theorem h_add_h_zero_or_affine_imo_2019_p1 (f : ℤ → ℤ)
    (h₆ : ∀ a b : ℤ, (f a - f 0) + (f b - f 0) = f (a + b) - f 0) :
    ∀ a b : ℤ, (f a - f 0) + (f b - f 0) = f (a + b) - f 0 := by
  exact h₆

theorem h₁_h_zero_or_affine_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) :
    ∀ b : ℤ, f 0 + 2 * f b = f (f b) := by
  have h_main : ∀ (b : ℤ), f 0 + 2 * f b = f (f b) := by
    intro b
    have h₁ := h 0 b
    -- Simplify the equation obtained by setting a = 0
    simp at h₁
    -- The simplified equation is exactly what we need to prove
    <;> linarith
  
  exact h_main

theorem h₂_h_zero_or_affine_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) :
    ∀ a : ℤ, f (2 * a) + 2 * f 0 = f (f a) := by
  have h_main : ∀ (x : ℤ), f (2 * x) + 2 * f 0 = f (f x) := by
    intro x
    have h₁ := h x 0
    have h₂ : f (2 * x) + 2 * f 0 = f (f (x + 0)) := by
      simpa using h₁
    have h₃ : f (f (x + 0)) = f (f x) := by
      simp
    linarith
  
  intro a
  have h₁ := h_main a
  exact h₁

theorem h₄_h_zero_or_affine_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (h₂ : ∀ a : ℤ, f (2 * a) + 2 * f 0 = f (f a))
    (h₃ : ∀ a : ℤ, f (f a) = f 0 + 2 * f a) :
    ∀ a : ℤ, f (2 * a) = 2 * f a - f 0 := by
  have h_main : ∀ (a : ℤ), f (2 * a) = 2 * f a - f 0 := by
    intro a
    have h₄ : f (2 * a) + 2 * f 0 = f (f a) := h₂ a
    have h₅ : f (f a) = f 0 + 2 * f a := h₃ a
    have h₆ : f (2 * a) + 2 * f 0 = f 0 + 2 * f a := by
      linarith
    have h₇ : f (2 * a) + f 0 = 2 * f a := by
      linarith
    have h₈ : f (2 * a) = 2 * f a - f 0 := by
      linarith
    exact h₈
  exact h_main

theorem h₃_h_zero_or_affine_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (h₁ : ∀ b : ℤ, f 0 + 2 * f b = f (f b)) :
    ∀ a : ℤ, f (f a) = f 0 + 2 * f a := by
  have h_main : ∀ (a : ℤ), f (f a) = f 0 + 2 * f a := by
    intro a
    have h₂ : f 0 + 2 * f a = f (f a) := h₁ a
    -- Use the symmetry of equality to get the desired form
    linarith
  
  exact h_main

theorem h₅_h_zero_or_affine_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (h₃ : ∀ a : ℤ, f (f a) = f 0 + 2 * f a)
    (h₄ : ∀ a : ℤ, f (2 * a) = 2 * f a - f 0) :
    ∀ a b : ℤ, f a + f b = f (a + b) + f 0 := by
  have h_main : ∀ (a b : ℤ), 2 * (f a + f b - f 0) = 2 * f (a + b) := by
    intro a b
    have h₁ : f (2 * a) + 2 * f b = f (f (a + b)) := h a b
    have h₂ : f (2 * a) = 2 * f a - f 0 := h₄ a
    have h₃' : f (f (a + b)) = f 0 + 2 * f (a + b) := by
      have h₃'' := h₃ (a + b)
      linarith
    have h₄' : (2 * f a - f 0) + 2 * f b = f 0 + 2 * f (a + b) := by
      linarith
    have h₅ : 2 * f a + 2 * f b - f 0 = f 0 + 2 * f (a + b) := by
      linarith
    have h₆ : 2 * f a + 2 * f b - 2 * f 0 = 2 * f (a + b) := by
      linarith
    have h₇ : 2 * (f a + f b - f 0) = 2 * f (a + b) := by
      linarith
    exact h₇
  
  have h_final : ∀ (a b : ℤ), f a + f b = f (a + b) + f 0 := by
    intro a b
    have h₁ : 2 * (f a + f b - f 0) = 2 * f (a + b) := h_main a b
    have h₂ : f a + f b - f 0 = f (a + b) := by
      -- Divide both sides by 2 to simplify the equation
      have h₃ : 2 * (f a + f b - f 0) = 2 * f (a + b) := h₁
      have h₄ : f a + f b - f 0 = f (a + b) := by
        -- Since 2 is non-zero, we can divide both sides by 2
        apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num)
        linarith
      exact h₄
    -- Rearrange the equation to get the final result
    have h₃ : f a + f b = f (a + b) + f 0 := by
      linarith
    exact h₃
  
  exact h_final

theorem hk_cases_h_zero_or_affine_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    {k c : ℤ}
    (hk : ∀ z : ℤ, f z = k * z + c)
    (hk_eq : ∀ a b : ℤ,
        k * (2 * a) + c + 2 * (k * b + c) =
          k * (k * (a + b) + c) + c) :
    k = 0 ∨ k = 2 := by
  have h1 : 2 * c - k * c = 0 := by
    have h1_1 := hk_eq 0 0
    ring_nf at h1_1 ⊢
    linarith
  
  have h2 : 2 * k - k ^ 2 = 0 := by
    have h2_1 := hk_eq 1 0
    have h2_2 := hk_eq 0 0
    ring_nf at h2_1 h2_2 ⊢
    have h2_3 : 2 * c - k * c = 0 := h1
    nlinarith
  
  have h3 : k = 0 ∨ k = 2 := by
    have h3_1 : k * (k - 2) = 0 := by
      have h3_2 : 2 * k - k ^ 2 = 0 := h2
      ring_nf at h3_2 ⊢
      linarith
    have h3_3 : k = 0 ∨ k - 2 = 0 := by
      have h3_4 : k * (k - 2) = 0 := h3_1
      have h3_5 : k = 0 ∨ k - 2 = 0 := by
        apply eq_zero_or_eq_zero_of_mul_eq_zero h3_4
      exact h3_5
    cases h3_3 with
    | inl h3_6 =>
      exact Or.inl h3_6
    | inr h3_6 =>
      have h3_7 : k = 2 := by
        have h3_8 : k - 2 = 0 := h3_6
        linarith
      exact Or.inr h3_7
  
  exact h3

theorem h_final_h_zero_or_affine_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    {k c : ℤ}
    (hk : ∀ z : ℤ, f z = k * z + c)
    (hk_cases : k = 0 ∨ k = 2) :
    ∀ z : ℤ, f z = 0 ∨ ∃ c' : ℤ, ∀ z, f z = 2 * z + c' := by
  have h_main : (∀ z : ℤ, f z = 0) ∨ (∃ c' : ℤ, ∀ z : ℤ, f z = 2 * z + c') := by
    cases hk_cases with
    | inl hk0 =>
      -- Case: k = 0
      have h₁ : c = 0 := by
        have h₂ := h 0 0
        have h₃ := h 1 0
        have h₄ := h 0 1
        have h₅ := h 1 1
        simp [hk, hk0] at h₂ h₃ h₄ h₅
        <;> ring_nf at h₂ h₃ h₄ h₅ ⊢
        <;> linarith
      -- Now we know c = 0, so f(z) = 0 for all z
      have h₂ : ∀ z : ℤ, f z = 0 := by
        intro z
        have h₃ := hk z
        rw [hk0] at h₃
        simp [h₁] at h₃ ⊢
        <;> linarith
      exact Or.inl h₂
    | inr hk2 =>
      -- Case: k = 2
      have h₁ : ∃ c' : ℤ, ∀ z : ℤ, f z = 2 * z + c' := by
        refine' ⟨c, _⟩
        intro z
        have h₂ := hk z
        rw [hk2] at h₂
        ring_nf at h₂ ⊢
        <;> linarith
      exact Or.inr h₁
  
  have h_final : ∀ z : ℤ, f z = 0 ∨ ∃ c' : ℤ, ∀ z, f z = 2 * z + c' := by
    intro z
    cases h_main with
    | inl h_main =>
      -- Case: ∀ z, f z = 0
      have h₁ : f z = 0 := h_main z
      exact Or.inl h₁
    | inr h_main =>
      -- Case: ∃ c', ∀ z, f z = 2 * z + c'
      exact Or.inr h_main
  
  exact h_final

theorem h_linear_h_zero_or_affine_imo_2019_p1 (f : ℤ → ℤ)
    (h_add : ∀ a b : ℤ, (f a - f 0) + (f b - f 0) = f (a + b) - f 0) :
    ∃ k c : ℤ, ∀ z : ℤ, f z = k * z + c := by
  classical
  -- Define the additive homomorphism `g`.
  let g : ℤ →+ ℤ :=
    { toFun := fun z => f z - f 0
      map_zero' := by simp
      map_add' := by
        intro a b
        have h := h_add a b
        -- `h` is exactly `g a + g b = g (a + b)`.
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h.symm }
  -- The integer `k` corresponding to `g`.
  let k : ℤ := (AddMonoidHom.fromIntEquiv ℤ) g
  have hg : g = (AddMonoidHom.fromIntEquiv ℤ).symm k := by
    have h := (AddMonoidHom.fromIntEquiv ℤ).symm_apply_apply g
    -- `h : (AddMonoidHom.fromIntEquiv ℤ).symm ((AddMonoidHom.fromIntEquiv ℤ) g) = g`
    simpa [k] using h.symm
  refine ⟨k, f 0, ?_⟩
  intro z
  calc
    f z = (f z - f 0) + f 0 := by
      simpa using (sub_add_cancel (f z) (f 0)).symm
    _ = g z + f 0 := rfl
    _ = ((AddMonoidHom.fromIntEquiv ℤ).symm k) z + f 0 := by
      have := congrArg (fun h : ℤ →+ ℤ => h z) hg
      simpa using this
    _ = (z • k) + f 0 := rfl
    _ = k * z + f 0 := by
      simpa [zsmul_eq_mul, mul_comm]

theorem h_zero_or_affine_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) :
    ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  -- 1. Specialisations of the hypothesis
  have h₁ : ∀ b : ℤ, f 0 + 2 * f b = f (f b) := by
    exact h₁_h_zero_or_affine_imo_2019_p1 f h
  have h₂ : ∀ a : ℤ, f (2 * a) + 2 * f 0 = f (f a) := by
    exact h₂_h_zero_or_affine_imo_2019_p1 f h
  -- 2. Expression for `f (f a)`
  have h₃ : ∀ a : ℤ, f (f a) = f 0 + 2 * f a := by
    exact h₃_h_zero_or_affine_imo_2019_p1 f h h₁
  -- 3. Expression for `f (2 * a)`
  have h₄ : ∀ a : ℤ, f (2 * a) = 2 * f a - f 0 := by
    exact h₄_h_zero_or_affine_imo_2019_p1 f h h₂ h₃
  -- 4. Cauchy‑type relation
  have h₅ : ∀ a b : ℤ, f a + f b = f (a + b) + f 0 := by
    exact h₅_h_zero_or_affine_imo_2019_p1 f h h₃ h₄
  -- 5. Relation for the shifted function `g z = f z - f 0`
  have h₆ : ∀ a b : ℤ, (f a - f 0) + (f b - f 0) = f (a + b) - f 0 := by
    exact h₆_h_zero_or_affine_imo_2019_p1 f h₅
  -- 6. Additivity of `g`
  have h_add : ∀ a b : ℤ, (f a - f 0) + (f b - f 0) = f (a + b) - f 0 := by
    exact h_add_h_zero_or_affine_imo_2019_p1 f h₆
  -- 7. Linear form of `f`
  have h_linear : ∃ k c : ℤ, ∀ z : ℤ, f z = k * z + c := by
    exact h_linear_h_zero_or_affine_imo_2019_p1 f h_add
  rcases h_linear with ⟨k, c, hk⟩
  -- 8. Plug the affine expression into the original equation
  have hk_eq :
      ∀ a b : ℤ,
        k * (2 * a) + c + 2 * (k * b + c) =
          k * (k * (a + b) + c) + c := by
    exact hk_eq_h_zero_or_affine_imo_2019_p1 f h hk
  -- 9. Determine the possible slopes
  have hk_cases : k = 0 ∨ k = 2 := by
    exact hk_cases_h_zero_or_affine_imo_2019_p1 f h hk hk_eq
  -- 10. Final conclusion
  have h_final : ∀ z : ℤ, f z = 0 ∨ ∃ c' : ℤ, ∀ z, f z = 2 * z + c' := by
    exact h_final_h_zero_or_affine_imo_2019_p1 f h hk hk_cases
  exact h_final

theorem imo_2019_p1 (f : ℤ → ℤ) :
    (∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) ↔
      ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  constructor
  · intro h
    have h_zero_or_affine :
        ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c :=
      h_zero_or_affine_imo_2019_p1 f h
    exact h_zero_or_affine
  · intro h
    have h_cases :
        (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c :=
      h_cases_imo_2019_p1 f h
    have h_fun_eq :
        ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) :=
      h_fun_eq_imo_2019_p1 f h_cases
    exact h_fun_eq

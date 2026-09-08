import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h_affine_imo_2019_p1 (f : ℤ → ℤ) :
    (∃ c, ∀ z, f z = 2 * z + c) →
      ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
  intro h
  obtain ⟨c, hc⟩ := h
  intro a b
  have h₁ : f (2 * a) = 2 * (2 * a) + c := by
    rw [hc]
    <;> ring_nf
  have h₂ : f b = 2 * b + c := by
    rw [hc]
    <;> ring_nf
  have h₃ : f (a + b) = 2 * (a + b) + c := by
    rw [hc]
    <;> ring_nf
  have h₄ : f (f (a + b)) = 2 * (2 * (a + b) + c) + c := by
    rw [h₃, hc]
    <;> ring_nf
  calc
    f (2 * a) + 2 * f b = (2 * (2 * a) + c) + 2 * (2 * b + c) := by rw [h₁, h₂]
    _ = 4 * a + c + 4 * b + 2 * c := by ring_nf
    _ = 4 * a + 4 * b + 3 * c := by ring_nf
    _ = 2 * (2 * (a + b) + c) + c := by ring_nf
    _ = f (f (a + b)) := by rw [h₄]

theorem h_zero_imo_2019_p1 (f : ℤ → ℤ) :
    (∀ z, f z = 0) → ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
  intro h_f_zero a b
  have h1 : f (2 * a) = 0 := by
    have h1₁ : f (2 * a) = 0 := h_f_zero (2 * a)
    exact h1₁
  
  have h2 : f b = 0 := by
    have h2₁ : f b = 0 := h_f_zero b
    exact h2₁
  
  have h3 : f (a + b) = 0 := by
    have h3₁ : f (a + b) = 0 := h_f_zero (a + b)
    exact h3₁
  
  have h4 : f (f (a + b)) = 0 := by
    have h4₁ : f (a + b) = 0 := h3
    have h4₂ : f (f (a + b)) = f 0 := by rw [h4₁]
    have h4₃ : f 0 = 0 := h_f_zero 0
    rw [h4₂, h4₃]
  
  have h_main : f (2 * a) + 2 * f b = f (f (a + b)) := by
    have h5 : f (2 * a) + 2 * f b = 0 := by
      rw [h1]
      rw [h2]
      <;> ring
      <;> simp
    have h6 : f (f (a + b)) = 0 := h4
    linarith
  
  exact h_main

theorem h_c_eq_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) :
    ∀ b, f (f b) = f 0 + 2 * f b := by
  have h_main : ∀ (b : ℤ), f (f b) = f 0 + 2 * f b := by
    intro b
    have h₁ : f (2 * (0 : ℤ)) + 2 * f b = f (f (0 + b)) := h 0 b
    have h₂ : f (2 * (0 : ℤ)) = f 0 := by
      norm_num
    have h₃ : f (f (0 + b)) = f (f b) := by
      norm_num
    have h₄ : f 0 + 2 * f b = f (f b) := by
      linarith
    linarith
  
  exact h_main

theorem h_f2a_eq_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (h_c_eq : ∀ b, f (f b) = f 0 + 2 * f b) :
    ∀ a, f (2 * a) = 2 * f a - f 0 := by
  have h_intermediate : ∀ (a b : ℤ), f (2 * a) + 2 * f b = f 0 + 2 * f (a + b) := by
    intro a b
    have h1 : f (2 * a) + 2 * f b = f (f (a + b)) := h a b
    have h2 : f (f (a + b)) = f 0 + 2 * f (a + b) := h_c_eq (a + b)
    linarith
  
  have h_main : ∀ (a : ℤ), f (2 * a) = 2 * f a - f 0 := by
    intro a
    have h1 : f (2 * a) + 2 * f 0 = f 0 + 2 * f (a + 0) := h_intermediate a 0
    have h2 : f (2 * a) + 2 * f 0 = f 0 + 2 * f a := by
      have h3 : f (a + 0) = f a := by simp
      rw [h3] at h1
      linarith
    have h4 : f (2 * a) = 2 * f a - f 0 := by
      linarith
    exact h4
  
  exact h_main

theorem h_cases'_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (h_c_eq : ∀ b, f (f b) = f 0 + 2 * f b)
    (h_f2a_eq : ∀ a, f (2 * a) = 2 * f a - f 0)
    (h_add_eq : ∀ a b, f (a + b) = f a + f b - f 0)
    (h_g_linear : ∃ k : ℤ, ∀ z, f z = k * z + f 0)
    (h_cases : (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c) :
    ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  intro z
  cases h_cases with
  | inl h_zero =>
    -- Case: ∀ z, f z = 0
    have h₁ : f z = 0 := h_zero z
    exact Or.inl h₁
  | inr h_exists_c =>
    -- Case: ∃ c, ∀ z, f z = 2 * z + c
    exact Or.inr h_exists_c

theorem h_add_eq_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (h_c_eq : ∀ b, f (f b) = f 0 + 2 * f b)
    (h_f2a_eq : ∀ a, f (2 * a) = 2 * f a - f 0) :
    ∀ a b, f (a + b) = f a + f b - f 0 := by
  have h_main : ∀ (a b : ℤ), f (a + b) = f a + f b - f 0 := by
    intro a b
    have h1 : f (2 * a) + 2 * f b = f (f (a + b)) := h a b
    have h2 : f (f (a + b)) = f 0 + 2 * f (a + b) := by
      have h3 := h_c_eq (a + b)
      exact h3
    have h4 : f (2 * a) = 2 * f a - f 0 := h_f2a_eq a
    have h5 : 2 * f a - f 0 + 2 * f b = f 0 + 2 * f (a + b) := by
      linarith
    have h6 : 2 * f a + 2 * f b - f 0 = f 0 + 2 * f (a + b) := by
      linarith
    have h7 : 2 * f a + 2 * f b - 2 * f 0 = 2 * f (a + b) := by
      linarith
    have h8 : f a + f b - f 0 = f (a + b) := by
      linarith
    linarith
  exact h_main

theorem h_eq_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c)
    (h_zero : (∀ z, f z = 0) → ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (h_affine : (∃ c, ∀ z, f z = 2 * z + c) →
      ∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) :
    ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
  have h_main : (∀ z, f z = 0) ∨ (∃ c, ∀ z, f z = 2 * z + c) := by
    by_cases h₀ : ∀ z, f z = 0
    · exact Or.inl h₀
    · -- If f is not identically zero, then there exists z₀ such that f(z₀) ≠ 0
      have h₁ : ∃ z₀, f z₀ ≠ 0 := by
        by_contra h₁
        push_neg at h₁
        have h₂ : ∀ z, f z = 0 := by simpa using h₁
        contradiction
      -- Obtain z₀ such that f(z₀) ≠ 0
      obtain ⟨z₀, hz₀⟩ := h₁
      -- By the given condition, either f(z₀) = 0 or there exists c such that f(z) = 2z + c for all z
      have h₂ : f z₀ = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := h z₀
      -- Since f(z₀) ≠ 0, we must have the second case
      cases h₂ with
      | inl h₂ =>
        exfalso
        apply hz₀
        exact h₂
      | inr h₂ =>
        -- Therefore, there exists c such that f(z) = 2z + c for all z
        exact Or.inr h₂
  
  have h_final : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
    cases h_main with
    | inl h_main =>
      -- Case: f is identically zero
      have h₁ : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := h_zero h_main
      exact h₁
    | inr h_main =>
      -- Case: f is of the form f(z) = 2z + c
      have h₁ : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := h_affine h_main
      exact h₁
  
  exact h_final

theorem h_all_zero_h_cases_imo_2019_p1
    (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (h_c_eq : ∀ b, f (f b) = f 0 + 2 * f b)
    (h_f2a_eq : ∀ a, f (2 * a) = 2 * f a - f 0)
    (h_add_eq : ∀ a b, f (a + b) = f a + f b - f 0)
    (k : ℤ) (hk : ∀ z, f z = k * z + f 0)
    (hk0 : k = 0) (h_c_zero : f 0 = 0) :
    ∀ z : ℤ, f z = 0 := by
  intro z
  have h₁ : f z = k * z + f 0 := hk z
  rw [h₁]
  have h₂ : k = 0 := hk0
  rw [h₂]
  have h₃ : f 0 = 0 := h_c_zero
  simp [h₃]
  <;> ring
  <;> simp_all
  <;> linarith

theorem h_exists_h_cases_imo_2019_p1
    (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (h_c_eq : ∀ b, f (f b) = f 0 + 2 * f b)
    (h_f2a_eq : ∀ a, f (2 * a) = 2 * f a - f 0)
    (h_add_eq : ∀ a b, f (a + b) = f a + f b - f 0)
    (k : ℤ) (hk : ∀ z, f z = k * z + f 0)
    (hk2 : k = 2) :
    ∃ c : ℤ, ∀ z : ℤ, f z = 2 * z + c := by
  have h_main : ∃ (c : ℤ), ∀ (z : ℤ), f z = 2 * z + c := by
    use f 0
    intro z
    have h₁ : f z = k * z + f 0 := hk z
    rw [h₁]
    have h₂ : k = 2 := hk2
    rw [h₂]
    <;> ring_nf
    <;> simp_all
    <;> linarith
  
  exact h_main

theorem h_c_zero_h_cases_imo_2019_p1
    (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (h_c_eq : ∀ b, f (f b) = f 0 + 2 * f b)
    (h_f2a_eq : ∀ a, f (2 * a) = 2 * f a - f 0)
    (h_add_eq : ∀ a b, f (a + b) = f a + f b - f 0)
    (k : ℤ) (hk : ∀ z, f z = k * z + f 0)
    (hk0 : k = 0) :
    f 0 = 0 := by
  have h_const : ∀ z, f z = f 0 := by
    intro z
    have h1 : f z = k * z + f 0 := hk z
    rw [h1]
    have h2 : k = 0 := hk0
    rw [h2]
    ring
    <;> simp [hk0]
    <;> linarith
  
  have h_f_f0 : f (f 0) = 3 * f 0 := by
    have h1 : f (f 0) = f 0 + 2 * f 0 := by
      have h2 := h_c_eq 0
      ring_nf at h2 ⊢
      <;> linarith
    have h3 : f (f 0) = 3 * f 0 := by
      linarith
    exact h3
  
  have h_f_f0_const : f (f 0) = f 0 := by
    have h₁ : f (f 0) = f 0 := by
      have h₂ : ∀ z, f z = f 0 := h_const
      have h₃ : f (f 0) = f 0 := by
        have h₄ := h₂ (f 0)
        have h₅ := h₂ 0
        linarith
      exact h₃
    exact h₁
  
  have h_main : f 0 = 0 := by
    have h₁ : f (f 0) = 3 * f 0 := h_f_f0
    have h₂ : f (f 0) = f 0 := h_f_f0_const
    have h₃ : 3 * f 0 = f 0 := by linarith
    have h₄ : f 0 = 0 := by
      linarith
    exact h₄
  
  exact h_main

theorem hk_cases_h_cases_imo_2019_p1
    (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (h_c_eq : ∀ b, f (f b) = f 0 + 2 * f b)
    (h_f2a_eq : ∀ a, f (2 * a) = 2 * f a - f 0)
    (h_add_eq : ∀ a b, f (a + b) = f a + f b - f 0)
    (h_g_linear : ∃ k : ℤ, ∀ z, f z = k * z + f 0)
    (k : ℤ) (hk : ∀ z, f z = k * z + f 0) :
    k = 0 ∨ k = 2 := by
  have h1 : (k - 2) * f 0 = 0 := by
    have h1₁ := h_c_eq 0
    have h1₂ : f (f 0) = f 0 + 2 * f 0 := by
      simpa using h1₁
    have h1₃ : f (f 0) = k * (k * 0 + f 0) + f 0 := by
      have h1₄ : f 0 = k * 0 + f 0 := by simp
      have h1₅ : f (f 0) = k * (f 0) + f 0 := by
        have h1₆ := hk (f 0)
        have h1₇ := hk 0
        simp at h1₆ h1₇ ⊢
        <;> linarith
      have h1₈ : f (f 0) = k * (k * 0 + f 0) + f 0 := by
        calc
          f (f 0) = k * (f 0) + f 0 := by rw [h1₅]
          _ = k * (k * 0 + f 0) + f 0 := by
            have h1₉ := hk 0
            simp at h1₉ ⊢
            <;> linarith
      exact h1₈
    have h1₉ : f 0 + 2 * f 0 = 3 * f 0 := by ring
    have h1₁₀ : k * (k * 0 + f 0) + f 0 = k * f 0 + f 0 := by ring
    have h1₁₁ : k * f 0 + f 0 = f 0 + 2 * f 0 := by
      linarith
    have h1₁₂ : k * f 0 = 2 * f 0 := by linarith
    have h1₁₃ : (k - 2) * f 0 = 0 := by
      linarith
    exact h1₁₃
  
  have h2 : k ^ 2 - 2 * k = 0 := by
    have h2₁ := h_c_eq 1
    have h2₂ : f (f 1) = f 0 + 2 * f 1 := by simpa using h2₁
    have h2₃ : f (f 1) = k * (k * 1 + f 0) + f 0 := by
      have h2₄ : f 1 = k * 1 + f 0 := by
        have h2₅ := hk 1
        simpa using h2₅
      have h2₅ : f (f 1) = k * (f 1) + f 0 := by
        have h2₆ := hk (f 1)
        have h2₇ := hk 1
        simp at h2₆ h2₇ ⊢
        <;> linarith
      calc
        f (f 1) = k * (f 1) + f 0 := by rw [h2₅]
        _ = k * (k * 1 + f 0) + f 0 := by
          rw [h2₄]
          <;> ring
    have h2₄ : f 0 + 2 * f 1 = f 0 + 2 * (k * 1 + f 0) := by
      have h2₅ : f 1 = k * 1 + f 0 := by
        have h2₆ := hk 1
        simpa using h2₆
      rw [h2₅]
      <;> ring
    have h2₅ : k * (k * 1 + f 0) + f 0 = f 0 + 2 * (k * 1 + f 0) := by
      linarith
    have h2₆ : k * (k * 1 + f 0) + f 0 = k ^ 2 + k * f 0 + f 0 := by
      ring
    have h2₇ : f 0 + 2 * (k * 1 + f 0) = 2 * k + 3 * f 0 := by
      ring
    have h2₈ : k ^ 2 + k * f 0 + f 0 = 2 * k + 3 * f 0 := by
      linarith
    have h2₉ : k ^ 2 - 2 * k + (k - 2) * f 0 = 0 := by
      linarith
    have h2₁₀ : (k - 2) * f 0 = 0 := h1
    have h2₁₁ : k ^ 2 - 2 * k = 0 := by
      linarith
    exact h2₁₁
  
  have h3 : k = 0 ∨ k = 2 := by
    have h3₁ : k * (k - 2) = 0 := by
      ring_nf at h2 ⊢
      <;> linarith
    have h3₂ : k = 0 ∨ k - 2 = 0 := by
      have h3₃ : k * (k - 2) = 0 := h3₁
      have h3₄ : k = 0 ∨ k - 2 = 0 := by
        apply eq_zero_or_eq_zero_of_mul_eq_zero h3₃
      exact h3₄
    cases h3₂ with
    | inl h3₂ =>
      exact Or.inl h3₂
    | inr h3₂ =>
      have h3₃ : k = 2 := by
        linarith
      exact Or.inr h3₃
  
  exact h3

theorem h_cases_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (h_c_eq : ∀ b, f (f b) = f 0 + 2 * f b)
    (h_f2a_eq : ∀ a, f (2 * a) = 2 * f a - f 0)
    (h_add_eq : ∀ a b, f (a + b) = f a + f b - f 0)
    (h_g_linear : ∃ k : ℤ, ∀ z, f z = k * z + f 0) :
    (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  rcases h_g_linear with ⟨k, hk⟩
  have h_g_linear' : ∃ k : ℤ, ∀ z, f z = k * z + f 0 := ⟨k, hk⟩
  have hk_cases : k = 0 ∨ k = 2 :=
    hk_cases_h_cases_imo_2019_p1 (f:=f) (h:=h) (h_c_eq:=h_c_eq) (h_f2a_eq:=h_f2a_eq)
      (h_add_eq:=h_add_eq) (h_g_linear:=h_g_linear') (k:=k) (hk:=hk)
  cases hk_cases with
  | inl hk0 =>
      have h_c_zero : f 0 = 0 :=
        h_c_zero_h_cases_imo_2019_p1 (f:=f) (h:=h) (h_c_eq:=h_c_eq) (h_f2a_eq:=h_f2a_eq)
          (h_add_eq:=h_add_eq) (k:=k) (hk:=hk) (hk0:=hk0)
      have h_all_zero : ∀ z : ℤ, f z = 0 :=
        h_all_zero_h_cases_imo_2019_p1 (f:=f) (h:=h) (h_c_eq:=h_c_eq) (h_f2a_eq:=h_f2a_eq)
          (h_add_eq:=h_add_eq) (k:=k) (hk:=hk) (hk0:=hk0) (h_c_zero:=h_c_zero)
      exact Or.inl h_all_zero
  | inr hk2 =>
      have h_exists : ∃ c : ℤ, ∀ z : ℤ, f z = 2 * z + c :=
        h_exists_h_cases_imo_2019_p1 (f:=f) (h:=h) (h_c_eq:=h_c_eq) (h_f2a_eq:=h_f2a_eq)
          (h_add_eq:=h_add_eq) (k:=k) (hk:=hk) (hk2:=hk2)
      exact Or.inr h_exists

theorem h_g_linear_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)))
    (h_c_eq : ∀ b, f (f b) = f 0 + 2 * f b)
    (h_f2a_eq : ∀ a, f (2 * a) = 2 * f a - f 0)
    (h_add_eq : ∀ a b, f (a + b) = f a + f b - f 0) :
    ∃ k : ℤ, ∀ z, f z = k * z + f 0 := by
  have h_g_additive : ∀ (a b : ℤ), (f (a + b) - f 0) = (f a - f 0) + (f b - f 0) := by
    intro a b
    have h1 : f (a + b) = f a + f b - f 0 := h_add_eq a b
    have h2 : f (a + b) - f 0 = (f a + f b - f 0) - f 0 := by rw [h1]
    have h3 : (f a + f b - f 0) - f 0 = (f a - f 0) + (f b - f 0) := by
      ring_nf
      <;>
      simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      <;>
      linarith
    linarith
  
  have h_g_homogeneous : ∀ (n : ℤ), (f n - f 0) = n * (f 1 - f 0) := by
    have h1 : ∀ (n : ℤ), (f n - f 0) = n * (f 1 - f 0) := by
      intro n
      have h2 : ∀ (n : ℕ), (f n - f 0) = n * (f 1 - f 0) := by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          have h3 := h_g_additive n 1
          have h4 := h_g_additive 1 n
          simp [ih, add_assoc] at h3 h4 ⊢
          <;> ring_nf at h3 h4 ⊢ <;>
          (try omega) <;>
          (try linarith) <;>
          (try
            {
              simp_all [add_assoc]
              <;> ring_nf at *
              <;> linarith
            })
          <;>
          (try
            {
              omega
            })
      have h3 : ∀ (n : ℕ), (f (-n : ℤ) - f 0) = (-n : ℤ) * (f 1 - f 0) := by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          have h4 := h_g_additive (-(n : ℤ) - 1 : ℤ) 1
          have h5 := h_g_additive 1 (-(n : ℤ) - 1 : ℤ)
          simp [ih, add_assoc] at h4 h5 ⊢
          <;> ring_nf at h4 h5 ⊢ <;>
          (try omega) <;>
          (try linarith) <;>
          (try
            {
              simp_all [add_assoc]
              <;> ring_nf at *
              <;> linarith
            })
          <;>
          (try
            {
              omega
            })
      -- Combine the results for positive and negative integers
      by_cases h4 : n ≥ 0
      · -- Case: n ≥ 0
        have h5 : (n : ℤ) ≥ 0 := by exact_mod_cast h4
        have h6 : ∃ (m : ℕ), (n : ℤ) = m := by
          use n.toNat
          <;> simp [Int.toNat_of_nonneg h5]
          <;> omega
        obtain ⟨m, hm⟩ := h6
        have h7 := h2 m
        simp [hm] at h7 ⊢
        <;> ring_nf at h7 ⊢ <;>
        (try omega) <;>
        (try linarith) <;>
        (try
          {
            simp_all [add_assoc]
            <;> ring_nf at *
            <;> linarith
          })
        <;>
        (try
          {
            omega
          })
      · -- Case: n < 0
        have h5 : (n : ℤ) < 0 := by
          by_contra h6
          have h7 : (n : ℤ) ≥ 0 := by linarith
          have h8 : n ≥ 0 := by exact_mod_cast h7
          contradiction
        have h6 : ∃ (m : ℕ), (n : ℤ) = -m := by
          use (-n).toNat
          <;>
          (try
            {
              simp [Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ -n)]
              <;>
              ring_nf at *
              <;>
              omega
            })
          <;>
          (try
            {
              omega
            })
        obtain ⟨m, hm⟩ := h6
        have h7 := h3 m
        simp [hm] at h7 ⊢
        <;> ring_nf at h7 ⊢ <;>
        (try omega) <;>
        (try linarith) <;>
        (try
          {
            simp_all [add_assoc]
            <;> ring_nf at *
            <;> linarith
          })
        <;>
        (try
          {
            omega
          })
    exact h1
  
  have h_main : ∃ (k : ℤ), ∀ (z : ℤ), f z = k * z + f 0 := by
    use (f 1 - f 0)
    intro z
    have h₁ : (f z - f 0) = z * (f 1 - f 0) := h_g_homogeneous z
    have h₂ : f z = z * (f 1 - f 0) + f 0 := by
      linarith
    linarith
  
  exact h_main

theorem imo_2019_p1 (f : ℤ → ℤ) :
    (∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) ↔
      ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  constructor
  · intro h
    have h_c_eq : ∀ b, f (f b) = f 0 + 2 * f b := by
      exact h_c_eq_imo_2019_p1 f h
    have h_f2a_eq : ∀ a, f (2 * a) = 2 * f a - f 0 := by
      exact h_f2a_eq_imo_2019_p1 f h h_c_eq
    have h_add_eq : ∀ a b, f (a + b) = f a + f b - f 0 := by
      exact h_add_eq_imo_2019_p1 f h h_c_eq h_f2a_eq
    have h_g_linear : ∃ k : ℤ, ∀ z, f z = k * z + f 0 := by
      exact h_g_linear_imo_2019_p1 f h h_c_eq h_f2a_eq h_add_eq
    have h_cases : (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
      exact h_cases_imo_2019_p1 f h h_c_eq h_f2a_eq h_add_eq h_g_linear
    have h_cases' : ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := by
      exact h_cases'_imo_2019_p1 f h h_c_eq h_f2a_eq h_add_eq h_g_linear h_cases
    exact h_cases'
  · intro h
    have h_zero :
        (∀ z, f z = 0) → ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
      exact h_zero_imo_2019_p1 f
    have h_affine :
        (∃ c, ∀ z, f z = 2 * z + c) →
          ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
      exact h_affine_imo_2019_p1 f
    have h_eq : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
      exact h_eq_imo_2019_p1 f h h_zero h_affine
    exact h_eq

import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem hL_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c) :
    (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  have h_main : (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
    by_cases h₀ : ∀ z, f z = 0
    · -- Case 1: f is identically zero
      exact Or.inl h₀
    · -- Case 2: f is not identically zero
      right
      -- There exists some z₀ such that f(z₀) ≠ 0
      have h₁ : ∃ z₀, f z₀ ≠ 0 := by
        by_contra h₁
        -- If no such z₀ exists, then f is identically zero
        push_neg at h₁
        exact h₀ (fun z => by simpa using h₁ z)
      -- Obtain z₀ such that f(z₀) ≠ 0
      obtain ⟨z₀, hz₀⟩ := h₁
      -- Apply the given condition to z₀
      have h₂ : f z₀ = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := h z₀
      -- Since f(z₀) ≠ 0, the second disjunct must hold
      cases h₂ with
      | inl h₂ =>
        exfalso
        apply hz₀
        exact h₂
      | inr h₂ =>
        -- Obtain c such that f(z) = 2z + c for all z
        obtain ⟨c, hc⟩ := h₂
        -- This c works globally
        exact ⟨c, hc⟩
  exact h_main

theorem hR_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) :
    (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  have h_f_zero : 3 * f 0 = f (f 0) := by
    have h₁ := h 0 0
    ring_nf at h₁ ⊢
    linarith
  
  have h_f_rec : ∀ (b : ℤ), f 0 + 2 * f b = f (f b) := by
    intro b
    have h₁ := h 0 b
    ring_nf at h₁ ⊢
    linarith
  
  have h_f_double : ∀ (a : ℤ), f (2 * a) = 2 * f a - f 0 := by
    intro a
    have h₁ := h a 0
    have h₂ := h_f_rec a
    have h₃ := h_f_rec 0
    have h₄ := h_f_rec (a + 0)
    have h₅ := h_f_rec (2 * a)
    ring_nf at h₁ h₂ h₃ h₄ h₅ ⊢
    linarith
  
  have h_step : ∀ (a : ℤ), f (a + 1) = f a + (f 1 - f 0) := by
    intro a
    have h₁ := h a 1
    have h₂ := h_f_double a
    have h₃ := h_f_double 1
    have h₄ := h_f_double (a + 1)
    have h₅ := h_f_rec (a + 1)
    have h₆ := h_f_rec a
    have h₇ := h_f_rec 1
    have h₈ := h_f_rec 0
    ring_nf at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ ⊢
    linarith
  
  have h_linear : ∃ (c d : ℤ), ∀ (a : ℤ), f a = c + a * d := by
    use f 0, (f 1 - f 0)
    intro a
    have h₁ : ∀ (n : ℕ), f n = f 0 + n * (f 1 - f 0) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        have h₂ := h_step n
        have h₃ := h_step (-1)
        have h₄ := h_step 0
        simp [ih] at h₂ ⊢
        <;> ring_nf at h₂ ⊢ <;> linarith
    have h₂ : ∀ (n : ℕ), f (-n : ℤ) = f 0 + (-n : ℤ) * (f 1 - f 0) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        have h₃ := h_step (-(n : ℤ) - 1)
        have h₄ := h_step (-(n : ℤ))
        simp [ih] at h₃ h₄ ⊢
        <;> ring_nf at h₃ h₄ ⊢ <;>
          (try omega) <;>
          (try linarith) <;>
          (try
            {
              nlinarith
            }) <;>
          (try
            {
              simp_all [Int.add_assoc]
              <;> ring_nf at *
              <;> linarith
            })
    -- Extend the result to all integers
    have h₃ : ∀ (a : ℤ), f a = f 0 + a * (f 1 - f 0) := by
      intro a
      cases' le_or_lt 0 a with h₄ h₄
      · -- Case: a ≥ 0
        have h₅ : ∃ (n : ℕ), a = n := by
          use a.toNat
          <;> simp [Int.toNat_of_nonneg h₄]
          <;> omega
        obtain ⟨n, rfl⟩ := h₅
        have h₆ := h₁ n
        simp at h₆ ⊢
        <;> ring_nf at h₆ ⊢ <;> linarith
      · -- Case: a < 0
        have h₅ : ∃ (n : ℕ), a = -n := by
          use (-a).toNat
          <;> simp [Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ -a)]
          <;> omega
        obtain ⟨n, h₅⟩ := h₅
        have h₆ := h₂ n
        rw [h₅] at *
        simp at h₆ ⊢
        <;> ring_nf at h₆ ⊢ <;> linarith
    -- Use the general result to conclude the proof
    have h₄ := h₃ a
    ring_nf at h₄ ⊢
    <;> linarith
  
  have h_main : (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
    obtain ⟨c, d, hf⟩ := h_linear
    have h₁ : d = 0 ∨ d = 2 := by
      have h₂ := h 0 0
      have h₃ := h 1 0
      have h₄ := h 0 1
      have h₅ := h 1 1
      have h₆ := h (-1) 0
      have h₇ := h 0 (-1)
      have h₈ := h 1 (-1)
      have h₉ := h (-1) 1
      simp [hf] at h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
      ring_nf at h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
      have h₁₀ : d * (2 - d) = 0 := by
        nlinarith [sq_nonneg (d - 2), sq_nonneg (c - 0), sq_nonneg (d - 0)]
      have h₁₁ : d = 0 ∨ d = 2 := by
        have h₁₂ : d = 0 ∨ 2 - d = 0 := by
          apply eq_zero_or_eq_zero_of_mul_eq_zero h₁₀
        cases h₁₂ with
        | inl h₁₂ =>
          exact Or.inl h₁₂
        | inr h₁₂ =>
          have h₁₃ : d = 2 := by linarith
          exact Or.inr h₁₃
      exact h₁₁
    cases h₁ with
    | inl h₁ =>
      have h₂ : c = 0 := by
        have h₃ := h 0 0
        have h₄ := h 1 0
        have h₅ := h 0 1
        have h₆ := h 1 1
        have h₇ := h (-1) 0
        have h₈ := h 0 (-1)
        have h₉ := h 1 (-1)
        have h₁₀ := h (-1) 1
        simp [hf, h₁] at h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀
        <;> ring_nf at h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ ⊢
        <;> nlinarith
      have h₃ : ∀ z, f z = 0 := by
        intro z
        have h₄ := hf z
        simp [h₁, h₂] at h₄ ⊢
        <;> linarith
      exact Or.inl h₃
    | inr h₁ =>
      have h₂ : ∃ c, ∀ z, f z = 2 * z + c := by
        use c
        intro z
        have h₃ := hf z
        simp [h₁] at h₃ ⊢
        <;> ring_nf at h₃ ⊢ <;> linarith
      exact Or.inr h₂
  
  exact h_main

theorem h_eq_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c)
    (hL : (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c) :
    ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
  have h_main : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
    intro a b
    cases hL with
    | inl h_zero =>
      -- Case 1: f is identically zero
      have h1 : f (2 * a) = 0 := by rw [h_zero]
      have h2 : f b = 0 := by rw [h_zero]
      have h3 : f (a + b) = 0 := by rw [h_zero]
      have h4 : f (f (a + b)) = 0 := by
        have h5 : f (a + b) = 0 := by rw [h_zero]
        rw [h5]
        rw [h_zero]
      -- Simplify the equation using the above results
      simp [h1, h2, h4]
    | inr h_linear =>
      -- Case 2: f is of the form f(z) = 2z + c for some constant c
      obtain ⟨c, hc⟩ := h_linear
      have h1 : f (2 * a) = 2 * (2 * a) + c := by
        rw [hc]
        <;> ring_nf
      have h2 : f b = 2 * b + c := by
        rw [hc]
        <;> ring_nf
      have h3 : f (a + b) = 2 * (a + b) + c := by
        rw [hc]
        <;> ring_nf
      have h4 : f (f (a + b)) = 2 * (2 * (a + b) + c) + c := by
        have h5 : f (a + b) = 2 * (a + b) + c := by
          rw [hc]
          <;> ring_nf
        rw [h5]
        rw [hc]
        <;> ring_nf
      -- Simplify the equation using the above results
      have h5 : f (2 * a) + 2 * f b = 2 * (2 * a) + c + 2 * (2 * b + c) := by
        rw [h1, h2]
        <;> ring_nf
      have h6 : f (f (a + b)) = 2 * (2 * (a + b) + c) + c := by
        rw [h4]
      have h7 : f (2 * a) + 2 * f b = f (f (a + b)) := by
        rw [h5, h6]
        <;> ring_nf at *
        <;> linarith
      exact h7
  exact h_main

theorem imo_2019_p1 (f : ℤ → ℤ) :
    (∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) ↔
      ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  constructor
  · intro h
    intro z
    have hR : (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
      exact hR_imo_2019_p1 f h
    cases hR with
    | inl h0 =>
        exact Or.inl (h0 z)
    | inr hlin =>
        exact Or.inr hlin
  · intro h
    have hL : (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
      exact hL_imo_2019_p1 f h
    have h_eq : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
      exact h_eq_imo_2019_p1 f h hL
    exact h_eq

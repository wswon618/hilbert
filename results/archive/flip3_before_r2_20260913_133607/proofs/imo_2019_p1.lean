import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem hlin'_imo_2019_p1 (f : ℤ → ℤ)
    (hlin : ∃ c, ∀ z, f z = 2 * z + c) :
    ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
  obtain ⟨c, hc⟩ := hlin
  intro a b
  simp only [hc]
  ring_nf
  <;>
  (try omega) <;>
  (try ring_nf at *) <;>
  (try linarith)
  <;>
  (try nlinarith)
  <;>
  (try omega)

theorem h0_imo_2019_p1 (f : ℤ → ℤ)
    (hzero : ∀ z, f z = 0) :
    ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
  have h_main : ∀ (a b : ℤ), f (2 * a) + 2 * f b = f (f (a + b)) := by
    intro a b
    have h1 : f (2 * a) = 0 := by
      apply hzero
    have h2 : f b = 0 := by
      apply hzero
    have h3 : f (a + b) = 0 := by
      apply hzero
    have h4 : f (f (a + b)) = 0 := by
      rw [h3]
      apply hzero
    calc
      f (2 * a) + 2 * f b = 0 + 2 * 0 := by rw [h1, h2]
      _ = 0 := by ring
      _ = f (f (a + b)) := by rw [h4]
  exact h_main

theorem h0or_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c) :
    (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  have h_main : (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
    by_cases h₀ : ∀ z, f z = 0
    · -- Case 1: f(z) = 0 for all z
      exact Or.inl h₀
    · -- Case 2: There exists some z such that f(z) ≠ 0
      right
      -- Obtain a specific z₀ such that f(z₀) ≠ 0
      have h₁ : ∃ z₀, f z₀ ≠ 0 := by
        by_contra h₁
        -- If no such z₀ exists, then f(z) = 0 for all z, contradicting h₀
        push_neg at h₁
        have h₂ : ∀ z, f z = 0 := by simpa using h₁
        exact h₀ h₂
      -- Obtain the z₀ and its property
      obtain ⟨z₀, hz₀⟩ := h₁
      -- Use the given condition on z₀ to get the constant c
      have h₂ : f z₀ = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := h z₀
      cases h₂ with
      | inl h₂ =>
        -- If f(z₀) = 0, this contradicts hz₀
        exfalso
        apply hz₀
        linarith
      | inr h₂ =>
        -- If there exists a c such that f(z) = 2z + c for all z, we are done
        obtain ⟨c, hc⟩ := h₂
        exact ⟨c, hc⟩
  exact h_main

theorem h6_imo_2019_p1 (f : ℤ → ℤ)
    (h : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) :
    (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  have h_recurrence : ∀ a, f (2 * a) = 2 * f a - f 0 := by
    intro a
    have h1 := h a 0
    have h2 := h 0 a
    have h3 := h 0 0
    have h4 := h a a
    have h5 := h a (-a)
    have h6 := h (-a) a
    have h7 := h a 1
    have h8 := h 1 a
    have h9 := h a (-1)
    have h10 := h (-1) a
    -- Simplify the equations to find the recurrence relation
    ring_nf at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ⊢
    -- Use linear arithmetic to solve for f(2a)
    linarith [h a 0, h 0 a, h 0 0, h a a, h a (-a), h (-a) a, h a 1, h 1 a, h a (-1), h (-1) a]
  
  have h_additive : ∀ (a b : ℤ), (f (a + b) - f 0) = (f a - f 0) + (f b - f 0) := by
    intro a b
    have h₁ := h a b
    have h₂ := h_recurrence (a + b)
    have h₃ := h_recurrence a
    have h₄ := h_recurrence b
    have h₅ := h_recurrence 0
    have h₆ := h 0 0
    have h₇ := h a 0
    have h₈ := h 0 b
    have h₉ := h a (-a)
    have h₁₀ := h b (-b)
    have h₁₁ := h (a + b) 0
    have h₁₂ := h 0 (a + b)
    have h₁₃ := h (a + b) (- (a + b))
    have h₁₄ := h a 1
    have h₁₅ := h 1 a
    have h₁₆ := h b 1
    have h₁₇ := h 1 b
    -- Simplify the expressions using the recurrence relation and the given functional equation
    ring_nf at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆ h₁₇ ⊢
    -- Use linear arithmetic to derive the additive property of g(a) = f(a) - f(0)
    linarith [h_recurrence a, h_recurrence b, h_recurrence (a + b), h_recurrence 0]
  
  have h_linear : ∃ (k c : ℤ), ∀ (a : ℤ), f a = k * a + c := by
    use (f 1 - f 0), f 0
    intro a
    have h₁ : ∀ n : ℕ, f n = (f 1 - f 0) * n + f 0 := by
      intro n
      induction n with
      | zero =>
        simp
        <;> ring_nf at *
        <;> linarith [h_recurrence 0]
      | succ n ih =>
        have h₂ := h_additive n 1
        have h₃ := h_additive 1 n
        simp [ih] at h₂ h₃ ⊢
        <;> ring_nf at h₂ h₃ ⊢ <;>
        (try omega) <;>
        (try linarith) <;>
        (try
          {
            have h₄ := h_recurrence 0
            have h₅ := h_recurrence 1
            have h₆ := h_recurrence (-1)
            have h₇ := h_recurrence 2
            have h₈ := h_recurrence (-2)
            ring_nf at h₄ h₅ h₆ h₇ h₈ ⊢
            <;> linarith
          })
        <;>
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
    have h₂ : ∀ n : ℕ, f (-n : ℤ) = (f 1 - f 0) * (-n : ℤ) + f 0 := by
      intro n
      induction n with
      | zero =>
        simp
        <;> ring_nf at *
        <;> linarith [h_recurrence 0]
      | succ n ih =>
        have h₃ := h_additive (-(n : ℤ) - 1) 1
        have h₄ := h_additive 1 (-(n : ℤ) - 1)
        simp [ih] at h₃ h₄ ⊢
        <;> ring_nf at h₃ h₄ ⊢ <;>
        (try omega) <;>
        (try linarith) <;>
        (try
          {
            have h₅ := h_recurrence 0
            have h₆ := h_recurrence 1
            have h₇ := h_recurrence (-1)
            have h₈ := h_recurrence 2
            have h₉ := h_recurrence (-2)
            ring_nf at h₅ h₆ h₇ h₈ h₉ ⊢
            <;> linarith
          })
        <;>
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
    -- Extend the result to all integers
    have h₃ : ∀ (a : ℤ), f a = (f 1 - f 0) * a + f 0 := by
      intro a
      cases' le_or_lt 0 a with h₄ h₄
      · -- Case: a ≥ 0
        have h₅ : ∃ (n : ℕ), a = n := by
          use a.toNat
          <;> simp_all [Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ a)]
        obtain ⟨n, rfl⟩ := h₅
        have h₆ := h₁ n
        simp at h₆ ⊢
        <;> linarith
      · -- Case: a < 0
        have h₅ : ∃ (n : ℕ), a = -n := by
          use (-a).toNat
          <;> simp_all [Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ -a)]
          <;> omega
        obtain ⟨n, rfl⟩ := h₅
        have h₆ := h₂ n
        simp at h₆ ⊢
        <;> linarith
    have h₄ := h₃ a
    linarith
  
  have h_main : (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
    obtain ⟨k, c, hf⟩ := h_linear
    have h₁ : (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
      by_cases hk : k = 0
      · -- Case: k = 0
        have h₂ : ∀ z, f z = 0 := by
          intro z
          have h₃ := hf z
          have h₄ := hf 0
          simp [hk] at h₃ h₄ ⊢
          <;>
          (try omega) <;>
          (try linarith)
          <;>
          (try {
            have h₅ := h_recurrence 0
            have h₆ := h_recurrence 1
            have h₇ := h_recurrence (-1)
            have h₈ := h_recurrence 2
            have h₉ := h_recurrence (-2)
            simp [hf, hk] at h₅ h₆ h₇ h₈ h₉ ⊢
            <;> ring_nf at h₅ h₆ h₇ h₈ h₉ ⊢ <;> linarith
          })
          <;>
          (try {
            have h₅ := h 0 0
            have h₆ := h 1 0
            have h₇ := h 0 1
            have h₈ := h 1 1
            have h₉ := h (-1) 0
            have h₁₀ := h 0 (-1)
            have h₁₁ := h 1 (-1)
            have h₁₂ := h (-1) 1
            simp [hf, hk] at h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ ⊢
            <;> ring_nf at h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ ⊢ <;> linarith
          })
          <;>
          (try {
            simp_all [hf, hk]
            <;> ring_nf at *
            <;> linarith
          })
        exact Or.inl h₂
      · -- Case: k ≠ 0
        have h₂ : k = 2 := by
          have h₃ := h 1 0
          have h₄ := h 0 1
          have h₅ := h 1 1
          have h₆ := h (-1) 0
          have h₇ := h 0 (-1)
          have h₈ := h 1 (-1)
          have h₉ := h (-1) 1
          have h₁₀ := h_recurrence 1
          have h₁₁ := h_recurrence (-1)
          have h₁₂ := h_recurrence 2
          have h₁₃ := h_recurrence (-2)
          simp [hf] at h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ ⊢
          ring_nf at h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ ⊢
          have h₁₄ : k = 2 := by
            apply mul_left_cancel₀ (sub_ne_zero.mpr hk)
            nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hk)]
          exact h₁₄
        have h₃ : ∃ c, ∀ z, f z = 2 * z + c := by
          use c
          intro z
          have h₄ := hf z
          simp [h₂] at h₄ ⊢
          <;> linarith
        exact Or.inr h₃
    exact h₁
  
  exact h_main

theorem imo_2019_p1 (f : ℤ → ℤ) :
    (∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) ↔
      ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  constructor
  · intro h
    have h6 : (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
      exact h6_imo_2019_p1 f h
    intro z
    cases h6 with
    | inl h0   => exact Or.inl (h0 z)
    | inr hlin => exact Or.inr hlin
  · intro h
    have h0or : (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c := by
      exact h0or_imo_2019_p1 f h
    cases h0or with
    | inl hzero =>
        have h0 : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
          exact h0_imo_2019_p1 f hzero
        exact h0
    | inr hlin =>
        have hlin' : ∀ a b, f (2 * a) + 2 * f b = f (f (a + b)) := by
          exact hlin'_imo_2019_p1 f hlin
        exact hlin'

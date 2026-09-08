import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h_angle_simpl_aime_1999_p11 :
    Real.tan (Real.pi / 2 - Real.pi / 72) = Real.tan ((35 : ℝ) * Real.pi / 72) := by
  have h₁ : Real.pi / 2 - Real.pi / 72 = (35 : ℝ) * Real.pi / 72 := by
    ring_nf
    <;> field_simp
    <;> ring_nf
    <;> norm_num
    <;> linarith [Real.pi_pos]
  
  rw [h₁]
  <;>
  norm_num
  <;>
  linarith [Real.pi_pos]

theorem h_tan_eq_aime_1999_p11 (m : ℚ)
    (h₁ : (∑ k in Finset.Icc (1 : ℕ) 35, Real.sin (5 * k * Real.pi / 180)) = Real.tan (m * Real.pi / 180))
    (h_sum_eq_tan :
        (∑ k in Finset.Icc (1 : ℕ) 35, Real.sin (5 * k * Real.pi / 180)) =
          Real.tan (Real.pi / 2 - Real.pi / 72))
    (h_angle_simpl :
        Real.tan (Real.pi / 2 - Real.pi / 72) = Real.tan ((35 : ℝ) * Real.pi / 72)) :
    Real.tan (m * Real.pi / 180) = Real.tan ((35 : ℝ) * Real.pi / 72) := by
  have h₂ : Real.tan (m * Real.pi / 180) = Real.tan (Real.pi / 2 - Real.pi / 72) := by
    linarith
  have h₃ : Real.tan (m * Real.pi / 180) = Real.tan ((35 : ℝ) * Real.pi / 72) := by
    calc
      Real.tan (m * Real.pi / 180) = Real.tan (Real.pi / 2 - Real.pi / 72) := by rw [h₂]
      _ = Real.tan ((35 : ℝ) * Real.pi / 72) := by rw [h_angle_simpl]
  exact h₃

theorem h_m_eq_aime_1999_p11 (m : ℚ)
    (h_angle_eq :
        m * Real.pi / 180 = ((35 : ℝ) * Real.pi / 72)) :
    (m : ℝ) = (175 : ℝ) / 2 := by
  have h1 : (m : ℝ) * Real.pi / 180 = (35 : ℝ) * Real.pi / 72 := by
    exact_mod_cast h_angle_eq
  have h2 : (m : ℝ) / 180 = (35 : ℝ) / 72 := by
    apply mul_left_cancel₀ (show (Real.pi : ℝ) ≠ 0 by exact Real.pi_ne_zero)
    linarith
  have h3 : (m : ℝ) = (175 : ℝ) / 2 := by
    field_simp at h2 ⊢
    ring_nf at h2 ⊢
    nlinarith
  exact h3

theorem h_angle_eq_aime_1999_p11 (m : ℚ)
    (h_tan_eq :
        Real.tan (m * Real.pi / 180) = Real.tan ((35 : ℝ) * Real.pi / 72))
    (h_angle_range :
        (0 : ℝ) < m * Real.pi / 180 ∧ m * Real.pi / 180 < Real.pi / 2) :
    m * Real.pi / 180 = ((35 : ℝ) * Real.pi / 72) := by
  have h₁ : m * Real.pi / 180 = (35 : ℝ) * Real.pi / 72 := by
    have h₂ : Real.tan (m * Real.pi / 180) = Real.tan ((35 : ℝ) * Real.pi / 72) := h_tan_eq
    have h₃ : 0 < m * Real.pi / 180 := h_angle_range.1
    have h₄ : m * Real.pi / 180 < Real.pi / 2 := h_angle_range.2
    have h₅ : 0 < (35 : ℝ) * Real.pi / 72 := by
      have h₅₁ : (0 : ℝ) < Real.pi := Real.pi_pos
      have h₅₂ : (0 : ℝ) < (35 : ℝ) * Real.pi / 72 := by positivity
      exact h₅₂
    have h₆ : (35 : ℝ) * Real.pi / 72 < Real.pi / 2 := by
      have h₆₁ : (35 : ℝ) * Real.pi / 72 < Real.pi / 2 := by
        have h₆₂ : (35 : ℝ) * Real.pi / 72 < Real.pi / 2 := by
          -- Prove that 35π/72 < π/2
          have h₆₃ : (35 : ℝ) / 72 < 1 / 2 := by norm_num
          have h₆₄ : (35 : ℝ) * Real.pi / 72 < Real.pi / 2 := by
            have h₆₅ : 0 < Real.pi := Real.pi_pos
            nlinarith [Real.pi_gt_three]
          exact h₆₄
        exact h₆₂
      exact h₆₁
    -- Use the injectivity of the tangent function on (0, π/2)
    have h₇ : m * Real.pi / 180 = (35 : ℝ) * Real.pi / 72 := by
      -- The tangent function is injective on (0, π/2)
      have h₇₁ : Real.tan (m * Real.pi / 180) = Real.tan ((35 : ℝ) * Real.pi / 72) := h₂
      have h₇₂ : m * Real.pi / 180 = (35 : ℝ) * Real.pi / 72 := by
        -- Use the fact that tan is injective on (0, π/2)
        apply (injOn_tan.eq_iff ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩).1
        exact h₇₁
      exact h₇₂
    exact h₇
  exact h₁

theorem h_angle_range_aime_1999_p11 (m : ℚ) (h₀ : (0 : ℚ) < m)
    (h₂ : (m.num : ℝ) / m.den < 90) :
    (0 : ℝ) < m * Real.pi / 180 ∧ m * Real.pi / 180 < Real.pi / 2 := by
  have h₃ : (m : ℝ) < 90 := by
    have h₃₁ : (m : ℝ) = (m.num : ℝ) / m.den := by
      have h₃₂ : (m : ℚ) = m.num / m.den := by
        rw [Rat.num_div_den]
      -- Cast the rational number to real and simplify
      norm_cast at h₃₂ ⊢
      <;> field_simp [Rat.den_nz] at h₃₂ ⊢ <;>
        ring_nf at h₃₂ ⊢ <;>
        norm_cast at h₃₂ ⊢ <;>
        simp_all [Rat.num_div_den]
      <;>
      linarith
    rw [h₃₁]
    exact h₂
  
  have h₄ : (0 : ℝ) < m * Real.pi / 180 := by
    have h₄₁ : (0 : ℝ) < (m : ℝ) := by
      exact mod_cast h₀
    have h₄₂ : (0 : ℝ) < Real.pi := Real.pi_pos
    have h₄₃ : (0 : ℝ) < (m : ℝ) * Real.pi := by positivity
    have h₄₄ : (0 : ℝ) < (m : ℝ) * Real.pi / 180 := by positivity
    exact h₄₄
  
  have h₅ : m * Real.pi / 180 < Real.pi / 2 := by
    have h₅₁ : (m : ℝ) < 90 := h₃
    have h₅₂ : 0 < Real.pi := Real.pi_pos
    have h₅₃ : 0 < Real.pi / 180 := by positivity
    -- Multiply both sides of the inequality (m : ℝ) < 90 by (Real.pi / 180)
    have h₅₄ : (m : ℝ) * (Real.pi / 180) < 90 * (Real.pi / 180) := by
      nlinarith [Real.pi_pos]
    -- Simplify the right-hand side
    have h₅₅ : 90 * (Real.pi / 180) = Real.pi / 2 := by
      ring_nf
      <;> field_simp
      <;> ring_nf
    -- Substitute back into the inequality
    have h₅₆ : (m : ℝ) * (Real.pi / 180) < Real.pi / 2 := by
      linarith
    -- Convert the expression to match the goal
    have h₅₇ : (m : ℝ) * Real.pi / 180 = (m : ℝ) * (Real.pi / 180) := by
      ring_nf
    rw [h₅₇] at *
    exact h₅₆
  
  exact ⟨h₄, h₅⟩

theorem h_num_den_aime_1999_p11 (m : ℚ)
    (h_m_eq : (m : ℝ) = (175 : ℝ) / 2) :
    (↑m.den + m.num : ℤ) = 177 := by
  have h₁ : (m.num : ℝ) / (m.den : ℝ) = (175 : ℝ) / 2 := by
    have h₂ : (m : ℝ) = (m.num : ℝ) / (m.den : ℝ) := by
      norm_cast
      <;> field_simp [Rat.den_nz]
      <;> simp [Rat.num_div_den]
    rw [h₂] at h_m_eq
    exact h_m_eq
  
  have h₂ : 2 * m.num = 175 * m.den := by
    have h₃ : (m.num : ℝ) / (m.den : ℝ) = (175 : ℝ) / 2 := h₁
    have h₄ : (m.den : ℝ) ≠ 0 := by
      norm_cast
      <;> exact_mod_cast (by
        have h₅ : m.den ≠ 0 := by
          exact Nat.pos_iff_ne_zero.mp (by exact m.pos)
        exact h₅)
    have h₅ : (2 : ℝ) * (m.num : ℝ) = (175 : ℝ) * (m.den : ℝ) := by
      field_simp at h₃
      <;> ring_nf at h₃ ⊢ <;>
      nlinarith
    norm_cast at h₅ ⊢
    <;>
    (try norm_num at h₅ ⊢) <;>
    (try ring_nf at h₅ ⊢) <;>
    (try linarith) <;>
    (try omega) <;>
    (try
      {
        norm_cast at h₅ ⊢
        <;>
        ring_nf at h₅ ⊢
        <;>
        norm_num at h₅ ⊢
        <;>
        linarith
      })
    <;>
    (try
      {
        field_simp at h₃ ⊢
        <;>
        ring_nf at h₃ ⊢
        <;>
        norm_cast at h₃ ⊢
        <;>
        linarith
      })
    <;>
    (try
      {
        norm_cast at h₅ ⊢
        <;>
        ring_nf at h₅ ⊢
        <;>
        norm_num at h₅ ⊢
        <;>
        linarith
      })
  
  have h₃ : m.den = 2 := by
    have h₄ : m.den ∣ 2 := by
      have h₅ : (2 : ℤ) * m.num = 175 * m.den := by exact_mod_cast h₂
      have h₆ : (m.den : ℤ) ∣ (2 : ℤ) * m.num := by
        use 175
        <;> linarith
      have h₇ : (m.den : ℤ) ∣ (2 : ℤ) * m.num := h₆
      have h₈ : (m.den : ℤ) ∣ (2 : ℤ) := by
        have h₉ : Int.gcd (m.num : ℤ) (m.den : ℤ) = 1 := by
          norm_cast
          <;> exact m.reduced
        have h₁₀ : (m.den : ℤ) ∣ (2 : ℤ) * m.num := h₇
        have h₁₁ : (m.den : ℤ) ∣ (2 : ℤ) := by
          -- Use the fact that gcd(m.num, m.den) = 1 to deduce that m.den divides 2
          have h₁₂ : (m.den : ℤ) ∣ (2 : ℤ) * m.num := h₁₀
          have h₁₃ : (m.den : ℤ) ∣ (2 : ℤ) := by
            -- Use the property of gcd to deduce that m.den divides 2
            have h₁₄ : Int.gcd (m.num : ℤ) (m.den : ℤ) = 1 := h₉
            have h₁₅ : (m.den : ℤ) ∣ (2 : ℤ) * m.num := h₁₂
            -- Use the fact that if a number divides a product and is coprime with one factor, it divides the other factor
            have h₁₆ : (m.den : ℤ) ∣ (2 : ℤ) := by
              -- Use the property of gcd to deduce that m.den divides 2
              have h₁₇ : (m.den : ℤ) ∣ (2 : ℤ) * m.num := h₁₅
              have h₁₈ : Int.gcd (m.num : ℤ) (m.den : ℤ) = 1 := h₉
              -- Use the fact that if a number divides a product and is coprime with one factor, it divides the other factor
              have h₁₉ : (m.den : ℤ) ∣ (2 : ℤ) := by
                -- Use the property of gcd to deduce that m.den divides 2
                apply (Int.gcd_eq_one_iff_coprime.mp h₁₈).symm.dvd_of_dvd_mul_right
                exact h₁₇
              exact h₁₉
            exact h₁₆
          exact h₁₃
        exact h₁₁
      -- Convert the divisibility from integers to natural numbers
      have h₁₂ : (m.den : ℕ) ∣ 2 := by
        norm_cast at h₈ ⊢
        <;>
        (try omega) <;>
        (try simp_all [Int.coe_nat_dvd_left]) <;>
        (try omega)
      exact h₁₂
    -- Since m.den divides 2 and m.den is positive, m.den must be 1 or 2
    have h₅ : m.den ∣ 2 := h₄
    have h₆ : m.den ≤ 2 := Nat.le_of_dvd (by norm_num) h₅
    have h₇ : m.den ≥ 1 := by
      have h₈ : 0 < m.den := m.pos
      linarith
    -- Check the possible values of m.den
    interval_cases m.den <;> norm_num at h₂ ⊢ <;>
      (try omega) <;>
      (try {
        have h₈ : m.num = 175 := by
          omega
        have h₉ : Int.gcd (m.num : ℤ) (1 : ℤ) = 1 := by
          norm_cast
          <;> simp [h₈]
          <;> norm_num
          <;> rfl
        simp_all [Rat.reduced]
        <;> norm_num at *
        <;> try contradiction
      }) <;>
      (try {
        have h₈ : m.num = 87 := by
          omega
        have h₉ : Int.gcd (m.num : ℤ) (2 : ℤ) = 1 := by
          norm_cast
          <;> simp [h₈]
          <;> norm_num
          <;> rfl
        simp_all [Rat.reduced]
        <;> norm_num at *
        <;> try contradiction
      })
    <;>
    (try omega)
  
  have h₄ : m.num = 175 := by
    have h₅ : 2 * m.num = 175 * m.den := h₂
    have h₆ : m.den = 2 := h₃
    rw [h₆] at h₅
    norm_cast at h₅ ⊢
    <;> ring_nf at h₅ ⊢ <;>
    (try omega) <;>
    (try
      {
        norm_num at h₅ ⊢
        <;>
        omega
      })
  
  have h₅ : (↑m.den + m.num : ℤ) = 177 := by
    have h₆ : m.den = 2 := h₃
    have h₇ : m.num = 175 := h₄
    norm_cast
    <;> simp [h₆, h₇]
    <;> norm_num
    <;> rfl
  
  exact h₅

theorem h_sum_eq_tan_aime_1999_p11 :
    (∑ k in Finset.Icc (1 : ℕ) 35, Real.sin (5 * k * Real.pi / 180)) =
      Real.tan (Real.pi / 2 - Real.pi / 72) := by
  have h₁ : (∑ k in Finset.Icc (1 : ℕ) 35, Real.sin (5 * k * Real.pi / 180)) = (∑ k in Finset.Icc (1 : ℕ) 35, Real.sin (k * Real.pi / 36)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have h₂ : (5 : ℝ) * k * Real.pi / 180 = (k : ℝ) * Real.pi / 36 := by
      ring_nf
      <;> field_simp
      <;> ring_nf
      <;> norm_cast
      <;> simp_all [Finset.mem_Icc]
      <;> linarith
    rw [h₂]
    <;>
    simp_all [Finset.mem_Icc]
    <;>
    norm_num
    <;>
    linarith
  
  have h₂ : 2 * Real.sin (Real.pi / 72) * (∑ k in Finset.Icc (1 : ℕ) 35, Real.sin (k * Real.pi / 36)) = 2 * Real.cos (Real.pi / 72) := by
    have h₃ : 2 * Real.sin (Real.pi / 72) * (∑ k in Finset.Icc (1 : ℕ) 35, Real.sin (k * Real.pi / 36)) = ∑ k in Finset.Icc (1 : ℕ) 35, 2 * Real.sin (Real.pi / 72) * Real.sin (k * Real.pi / 36) := by
      rw [Finset.mul_sum]
      <;>
      simp [mul_assoc]
      <;>
      ring_nf
    rw [h₃]
    have h₄ : ∑ k in Finset.Icc (1 : ℕ) 35, 2 * Real.sin (Real.pi / 72) * Real.sin (k * Real.pi / 36) = ∑ k in Finset.Icc (1 : ℕ) 35, (Real.cos ((2 * (k : ℝ) - 1) * Real.pi / 72) - Real.cos ((2 * (k : ℝ) + 1) * Real.pi / 72)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have h₅ : 2 * Real.sin (Real.pi / 72) * Real.sin (k * Real.pi / 36) = Real.cos ((2 * (k : ℝ) - 1) * Real.pi / 72) - Real.cos ((2 * (k : ℝ) + 1) * Real.pi / 72) := by
        have h₆ : Real.cos ((2 * (k : ℝ) - 1) * Real.pi / 72) - Real.cos ((2 * (k : ℝ) + 1) * Real.pi / 72) = 2 * Real.sin (Real.pi / 72) * Real.sin (k * Real.pi / 36) := by
          have h₇ : Real.cos ((2 * (k : ℝ) - 1) * Real.pi / 72) - Real.cos ((2 * (k : ℝ) + 1) * Real.pi / 72) = - (Real.cos ((2 * (k : ℝ) + 1) * Real.pi / 72) - Real.cos ((2 * (k : ℝ) - 1) * Real.pi / 72)) := by ring
          rw [h₇]
          have h₈ : Real.cos ((2 * (k : ℝ) + 1) * Real.pi / 72) - Real.cos ((2 * (k : ℝ) - 1) * Real.pi / 72) = -2 * Real.sin ((((2 * (k : ℝ) + 1) * Real.pi / 72) + ((2 * (k : ℝ) - 1) * Real.pi / 72)) / 2) * Real.sin ((((2 * (k : ℝ) + 1) * Real.pi / 72) - ((2 * (k : ℝ) - 1) * Real.pi / 72)) / 2) := by
            have h₉ := Real.cos_sub_cos ((2 * (k : ℝ) + 1) * Real.pi / 72) ((2 * (k : ℝ) - 1) * Real.pi / 72)
            ring_nf at h₉ ⊢
            linarith
          rw [h₈]
          have h₉ : Real.sin ((((2 * (k : ℝ) + 1) * Real.pi / 72) + ((2 * (k : ℝ) - 1) * Real.pi / 72)) / 2) = Real.sin ((k : ℝ) * Real.pi / 36) := by
            ring_nf
            <;> field_simp
            <;> ring_nf
          have h₁₀ : Real.sin ((((2 * (k : ℝ) + 1) * Real.pi / 72) - ((2 * (k : ℝ) - 1) * Real.pi / 72)) / 2) = Real.sin (Real.pi / 72) := by
            ring_nf
            <;> field_simp
            <;> ring_nf
          rw [h₉, h₁₀]
          <;> ring_nf
          <;> field_simp
          <;> ring_nf
          <;> linarith
        linarith
      linarith
    rw [h₄]
    have h₅ : ∑ k in Finset.Icc (1 : ℕ) 35, (Real.cos ((2 * (k : ℝ) - 1) * Real.pi / 72) - Real.cos ((2 * (k : ℝ) + 1) * Real.pi / 72)) = Real.cos (Real.pi / 72) - Real.cos (71 * Real.pi / 72) := by
      -- Use the fact that the sum telescopes
      have h₆ : ∑ k in Finset.Icc (1 : ℕ) 35, (Real.cos ((2 * (k : ℝ) - 1) * Real.pi / 72) - Real.cos ((2 * (k : ℝ) + 1) * Real.pi / 72)) = Real.cos (Real.pi / 72) - Real.cos (71 * Real.pi / 72) := by
        -- Calculate the sum by observing the telescoping pattern
        norm_num [Finset.sum_Icc_succ_top]
        <;>
        (try ring_nf) <;>
        (try norm_num) <;>
        (try
          {
            simp_all [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_add, Nat.cast_one]
            <;>
            ring_nf at *
            <;>
            norm_num at *
            <;>
            linarith [Real.pi_pos]
          }) <;>
        (try
          {
            field_simp at *
            <;>
            ring_nf at *
            <;>
            norm_num at *
            <;>
            linarith [Real.pi_pos]
          }) <;>
        (try
          {
            norm_num [Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub] at *
            <;>
            ring_nf at *
            <;>
            norm_num at *
            <;>
            linarith [Real.pi_pos]
          })
        <;>
        (try
          {
            simp_all [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_add, Nat.cast_one]
            <;>
            ring_nf at *
            <;>
            norm_num at *
            <;>
            linarith [Real.pi_pos]
          })
      rw [h₆]
    rw [h₅]
    have h₆ : Real.cos (71 * Real.pi / 72) = -Real.cos (Real.pi / 72) := by
      have h₇ : Real.cos (71 * Real.pi / 72) = Real.cos (Real.pi - Real.pi / 72) := by
        ring_nf
        <;> field_simp
        <;> ring_nf
      rw [h₇]
      have h₈ : Real.cos (Real.pi - Real.pi / 72) = -Real.cos (Real.pi / 72) := by
        rw [Real.cos_pi_sub]
      rw [h₈]
    rw [h₆]
    <;> ring_nf
    <;> field_simp
    <;> ring_nf
    <;> linarith [Real.pi_pos]
  
  have h₃ : Real.sin (Real.pi / 72) > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    <;> norm_num
    <;> linarith [Real.pi_gt_three]
  
  have h₄ : (∑ k in Finset.Icc (1 : ℕ) 35, Real.sin (k * Real.pi / 36)) = Real.cos (Real.pi / 72) / Real.sin (Real.pi / 72) := by
    have h₅ : 2 * Real.sin (Real.pi / 72) * (∑ k in Finset.Icc (1 : ℕ) 35, Real.sin (k * Real.pi / 36)) = 2 * Real.cos (Real.pi / 72) := h₂
    have h₆ : Real.sin (Real.pi / 72) ≠ 0 := by linarith [h₃]
    have h₇ : (∑ k in Finset.Icc (1 : ℕ) 35, Real.sin (k * Real.pi / 36)) = Real.cos (Real.pi / 72) / Real.sin (Real.pi / 72) := by
      have h₈ : 2 * Real.sin (Real.pi / 72) * (∑ k in Finset.Icc (1 : ℕ) 35, Real.sin (k * Real.pi / 36)) = 2 * Real.cos (Real.pi / 72) := h₂
      have h₉ : (∑ k in Finset.Icc (1 : ℕ) 35, Real.sin (k * Real.pi / 36)) = (2 * Real.cos (Real.pi / 72)) / (2 * Real.sin (Real.pi / 72)) := by
        field_simp [h₆] at h₈ ⊢
        <;> nlinarith
      have h₁₀ : (2 * Real.cos (Real.pi / 72)) / (2 * Real.sin (Real.pi / 72)) = Real.cos (Real.pi / 72) / Real.sin (Real.pi / 72) := by
        field_simp [h₆]
        <;> ring_nf
        <;> field_simp [h₆]
        <;> ring_nf
      rw [h₉, h₁₀]
    exact h₇
  
  have h₅ : Real.cos (Real.pi / 72) / Real.sin (Real.pi / 72) = Real.tan (Real.pi / 2 - Real.pi / 72) := by
    have h₅₁ : Real.tan (Real.pi / 2 - Real.pi / 72) = Real.cos (Real.pi / 72) / Real.sin (Real.pi / 72) := by
      have h₅₂ : Real.tan (Real.pi / 2 - Real.pi / 72) = Real.sin (Real.pi / 2 - Real.pi / 72) / Real.cos (Real.pi / 2 - Real.pi / 72) := by
        rw [Real.tan_eq_sin_div_cos]
      rw [h₅₂]
      have h₅₃ : Real.sin (Real.pi / 2 - Real.pi / 72) = Real.cos (Real.pi / 72) := by
        rw [Real.sin_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]
        <;> ring_nf
        <;> norm_num
      have h₅₄ : Real.cos (Real.pi / 2 - Real.pi / 72) = Real.sin (Real.pi / 72) := by
        rw [Real.cos_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]
        <;> ring_nf
        <;> norm_num
      rw [h₅₃, h₅₄]
      <;> field_simp [Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 72) (by linarith [Real.pi_pos] : Real.pi / 72 < Real.pi)]
      <;> ring_nf
      <;> norm_num
    linarith
  
  have h₆ : (∑ k in Finset.Icc (1 : ℕ) 35, Real.sin (5 * k * Real.pi / 180)) = Real.tan (Real.pi / 2 - Real.pi / 72) := by
    rw [h₁]
    rw [h₄]
    rw [h₅]
  
  apply h₆

theorem aime_1999_p11 (m : ℚ) (h₀ : 0 < m)
    (h₁ : (∑ k in Finset.Icc (1 : ℕ) 35, Real.sin (5 * k * Real.pi / 180)) = Real.tan (m * Real.pi / 180))
    (h₂ : (m.num : ℝ) / m.den < 90) : ↑m.den + m.num = 177 := by
  -- 1. Rewrite the sine sum as a tangent of a complementary angle.
  have h_sum_eq_tan :
      (∑ k in Finset.Icc (1 : ℕ) 35, Real.sin (5 * k * Real.pi / 180)) =
        Real.tan (Real.pi / 2 - Real.pi / 72) :=
    h_sum_eq_tan_aime_1999_p11
  -- 2. Simplify the angle `π/2 - π/72` to `35·π/72`.
  have h_angle_simpl :
      Real.tan (Real.pi / 2 - Real.pi / 72) = Real.tan ((35 : ℝ) * Real.pi / 72) :=
    h_angle_simpl_aime_1999_p11
  -- 3. Combine the hypothesis `h₁` with the previous equalities to obtain an equality of tangents.
  have h_tan_eq :
      Real.tan (m * Real.pi / 180) = Real.tan ((35 : ℝ) * Real.pi / 72) :=
    h_tan_eq_aime_1999_p11 m h₁ h_sum_eq_tan h_angle_simpl
  -- 4. Show that the angle `m·π/180` lies in the interval `(0, π/2)`.
  have h_angle_range :
      (0 : ℝ) < m * Real.pi / 180 ∧ m * Real.pi / 180 < Real.pi / 2 :=
    h_angle_range_aime_1999_p11 m h₀ h₂
  -- 5. Use injectivity of `tan` on `(0, π/2)` to deduce equality of the angles.
  have h_angle_eq :
      m * Real.pi / 180 = ((35 : ℝ) * Real.pi / 72) :=
    h_angle_eq_aime_1999_p11 m h_tan_eq h_angle_range
  -- 6. Solve the previous equality for `m`.
  have h_m_eq :
      (m : ℝ) = (175 : ℝ) / 2 :=
    h_m_eq_aime_1999_p11 m h_angle_eq
  -- 7. Translate the real‑number equality into a statement about numerator and denominator.
  have h_num_den :
      (↑m.den + m.num : ℤ) = 177 :=
    h_num_den_aime_1999_p11 m h_m_eq
  exact h_num_den

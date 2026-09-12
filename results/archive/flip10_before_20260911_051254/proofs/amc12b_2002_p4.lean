import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h_mul_eq_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n)
    (h₁ : (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1)
    (h_int : ∃ z : ℤ, ((41 * n + 42 : ℚ) / (42 * n)) = z) :
    (41 * n + 42 : ℚ) = (42 * n : ℚ) * (Int.cast (Classical.choose h_int)) := by
  classical
  -- `42 * n` is non‑zero as a rational number.
  have hcnz : (42 * n : ℚ) ≠ 0 := by
    have hn : (n : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt h₀)
    have h42 : (42 : ℚ) ≠ 0 := by
      norm_num
    exact mul_ne_zero h42 hn
  -- Turn the equality supplied by `h_int` into a multiplication equality.
  have h_mul :
      (41 * n + 42 : ℚ) = (Int.cast (Classical.choose h_int)) * (42 * n) := by
    have hz := (Classical.choose_spec h_int)
    -- `hz` : ((41 * n + 42 : ℚ) / (42 * n)) = Classical.choose h_int
    have h := (div_eq_iff_mul_eq hcnz).mp hz
    -- `h` may have the opposite orientation, so we flip it and commute the factors.
    simpa [mul_comm] using h.symm
  -- Reorder the factors to match the goal.
  simpa [mul_comm] using h_mul

theorem h12_h_sum_eq_amc12b_2002_p4 : (1 /. (2 : ℤ) + 1 /. (3 : ℤ)) = (5 /. (6 : ℤ)) := by
  norm_num [Int.emod_eq_of_lt]
  <;> rfl

theorem h123_h_sum_eq_amc12b_2002_p4 : (5 /. (6 : ℤ) + 1 /. (7 : ℤ)) = (41 /. (42 : ℤ)) := by
  norm_num [div_eq_mul_inv]
  <;>
  rfl

theorem h123n_h_sum_eq_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n) :
    (41 /. (42 : ℤ) + 1 /. (n : ℤ)) = ((41 * (n : ℚ) + 42) / (42 * (n : ℚ))) := by
  have h₁ : (41 /. (42 : ℤ) + 1 /. (n : ℤ)) = ((41 : ℚ) / 42 + 1 / (n : ℚ)) := by
    norm_cast
    <;> simp [div_eq_mul_inv]
    <;> field_simp [h₀.ne']
    <;> ring_nf
    <;> norm_cast
    <;> field_simp [h₀.ne']
    <;> ring_nf
    <;> norm_cast
  
  rw [h₁]
  have h₂ : ((41 : ℚ) / 42 + 1 / (n : ℚ)) = ((41 * (n : ℚ) + 42) / (42 * (n : ℚ))) := by
    have h₃ : (n : ℚ) ≠ 0 := by positivity
    field_simp [h₃]
    <;> ring_nf
    <;> field_simp [h₃]
    <;> ring_nf
    <;> norm_cast
    <;> field_simp [h₀.ne']
    <;> ring_nf
    <;> norm_cast
  
  rw [h₂]
  <;> norm_cast

theorem h_sum_eq_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n)
    (h₁ : (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1) :
    (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (↑n : ℤ)) =
      ((41 * n + 42 : ℚ) / (42 * n)) := by
  have h12 : (1 /. (2 : ℤ) + 1 /. (3 : ℤ)) = (5 /. (6 : ℤ)) := by
    exact h12_h_sum_eq_amc12b_2002_p4
  have h123 : (5 /. (6 : ℤ) + 1 /. (7 : ℤ)) = (41 /. (42 : ℤ)) := by
    exact h123_h_sum_eq_amc12b_2002_p4
  have h123n :
      (41 /. (42 : ℤ) + 1 /. (n : ℤ)) =
        ((41 * (n : ℚ) + 42) / (42 * (n : ℚ))) := by
    exact h123n_h_sum_eq_amc12b_2002_p4 n h₀
  calc
    (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (↑n : ℤ))
        = ((1 /. (2 : ℤ) + 1 /. (3 : ℤ)) + 1 /. (7 : ℤ) + 1 /. (↑n : ℤ)) := by
          simpa [Rat.add_assoc, add_comm, add_left_comm, add_assoc]
    _ = (5 /. (6 : ℤ) + 1 /. (7 : ℤ) + 1 /. (↑n : ℤ)) := by
          rw [h12]
    _ = (41 /. (42 : ℤ) + 1 /. (↑n : ℤ)) := by
          rw [h123]
    _ = ((41 * (n : ℚ) + 42) / (42 * (n : ℚ))) := by
          rw [h123n]
    _ = ((41 * n + 42 : ℚ) / (42 * n)) := by
          norm_cast

theorem h_nonzero_h_int_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n) :
    (42 * n : ℤ) ≠ 0 := by
  intro h
  have h₁ : (42 * n : ℤ) = 0 := h
  have h₂ : (n : ℤ) > 0 := by exact_mod_cast h₀
  have h₃ : (42 : ℤ) * (n : ℤ) > 0 := by
    nlinarith
  linarith

theorem h_den_one_h_int_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n)
    (h₁ : (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1)
    (h_sum_eq :
      (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)) =
        ((41 * n + 42 : ℚ) / (42 * n))) :
    ((41 * n + 42 : ℚ) / (42 * n)).den = 1 := by
  have h_den_eq : ((41 * n + 42 : ℚ) / (42 * n)).den = (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den := by
    have h₂ : ((41 * n + 42 : ℚ) / (42 * n)) = (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)) := by
      rw [h_sum_eq]
      <;> norm_cast
      <;> field_simp
      <;> ring_nf
      <;> norm_cast
      <;> field_simp
      <;> ring_nf
      <;> norm_cast
    rw [h₂]
    <;> rfl
  
  have h_final : ((41 * n + 42 : ℚ) / (42 * n)).den = 1 := by
    rw [h_den_eq]
    <;> rw [h₁]
  
  exact h_final

theorem h_eq_h_int_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n)
    (h₁ : (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1)
    (h_sum_eq :
      (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)) =
        ((41 * n + 42 : ℚ) / (42 * n)))
    (h_den_one :
      ((41 * n + 42 : ℚ) / (42 * n)).den = 1)
    (h_nonzero : (42 * n : ℤ) ≠ 0)
    (h_dvd : (42 * n : ℤ) ∣ (41 * n + 42 : ℤ))
    (z : ℤ) (hz : (41 * n + 42 : ℤ) = (42 * n) * z) :
    ((41 * n + 42 : ℚ) / (42 * n)) = (z : ℚ) := by
  have h_cast : ((41 * n + 42 : ℚ) : ℚ) = (42 * n : ℚ) * (z : ℚ) := by
    norm_cast at hz ⊢
    <;>
    (try norm_num at hz ⊢) <;>
    (try ring_nf at hz ⊢) <;>
    (try simp_all [mul_assoc]) <;>
    (try norm_cast at hz ⊢) <;>
    (try linarith) <;>
    (try
      {
        field_simp at hz ⊢ <;>
        ring_nf at hz ⊢ <;>
        norm_cast at hz ⊢ <;>
        simp_all [mul_assoc]
      }) <;>
    (try
      {
        norm_num at hz ⊢ <;>
        ring_nf at hz ⊢ <;>
        norm_cast at hz ⊢ <;>
        simp_all [mul_assoc]
      })
    <;>
    (try
      {
        simp_all [mul_assoc]
        <;>
        ring_nf at hz ⊢ <;>
        norm_cast at hz ⊢ <;>
        linarith
      })
    <;>
    (try
      {
        simp_all [mul_assoc]
        <;>
        norm_num at hz ⊢ <;>
        ring_nf at hz ⊢ <;>
        norm_cast at hz ⊢ <;>
        linarith
      })
    <;>
    (try
      {
        simp_all [mul_assoc]
        <;>
        norm_cast at hz ⊢ <;>
        linarith
      })
    <;>
    (try
      {
        simp_all [mul_assoc]
        <;>
        ring_nf at hz ⊢ <;>
        norm_cast at hz ⊢ <;>
        linarith
      })
  
  have h_main : ((41 * n + 42 : ℚ) / (42 * n)) = (z : ℚ) := by
    have h₂ : (42 * n : ℚ) ≠ 0 := by
      norm_cast
      <;>
      (try positivity) <;>
      (try
        {
          intro h
          have h₃ : (42 * n : ℕ) = 0 := by simpa using h
          have h₄ : n = 0 := by
            nlinarith
          linarith
        })
    -- Substitute the casted equality into the numerator
    calc
      ((41 * n + 42 : ℚ) / (42 * n)) = ((42 * n : ℚ) * (z : ℚ) / (42 * n)) := by
        rw [h_cast]
        <;>
        field_simp [h₂]
        <;>
        ring_nf
      _ = (z : ℚ) := by
        field_simp [h₂]
        <;>
        ring_nf
        <;>
        norm_num
        <;>
        simp_all [mul_assoc]
        <;>
        norm_cast
        <;>
        linarith
  
  apply h_main

theorem h_dvd_h_int_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n)
    (h₁ : (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1)
    (h_sum_eq :
      (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)) =
        ((41 * n + 42 : ℚ) / (42 * n)))
    (h_den_one :
      ((41 * n + 42 : ℚ) / (42 * n)).den = 1)
    (h_nonzero : (42 * n : ℤ) ≠ 0) :
    (42 * n : ℤ) ∣ (41 * n + 42 : ℤ) := by
  have h_main : ∃ (k : ℤ), (41 * n + 42 : ℤ) = k * (42 * n : ℤ) := by
    have h₂ : ((41 * n + 42 : ℚ) / (42 * n : ℚ)) = (((41 * n + 42 : ℚ) / (42 * n : ℚ)).num : ℚ) := by
      have h₃ : (((41 * n + 42 : ℚ) / (42 * n : ℚ)).den : ℕ) = 1 := by simpa using h_den_one
      have h₄ : ((41 * n + 42 : ℚ) / (42 * n : ℚ)) = (((41 * n + 42 : ℚ) / (42 * n : ℚ)).num : ℚ) / (((41 * n + 42 : ℚ) / (42 * n : ℚ)).den : ℚ) := by
        rw [Rat.num_div_den]
      rw [h₄]
      have h₅ : (((41 * n + 42 : ℚ) / (42 * n : ℚ)).den : ℚ) = 1 := by
        norm_cast
        <;> simp [h₃]
      rw [h₅]
      <;> field_simp
      <;> ring_nf
      <;> norm_cast
      <;> simp_all [Rat.num_div_den]
      <;> norm_num
      <;> linarith
    have h₃ : ((41 * n + 42 : ℚ) : ℚ) = (((41 * n + 42 : ℚ) / (42 * n : ℚ)).num : ℚ) * (42 * n : ℚ) := by
      have h₄ : ((41 * n + 42 : ℚ) / (42 * n : ℚ)) = (((41 * n + 42 : ℚ) / (42 * n : ℚ)).num : ℚ) := h₂
      have h₅ : ((41 * n + 42 : ℚ) : ℚ) / (42 * n : ℚ) = (((41 * n + 42 : ℚ) / (42 * n : ℚ)).num : ℚ) := by simpa using h₄
      have h₆ : (42 * n : ℚ) ≠ 0 := by
        norm_cast
        <;>
        (try norm_num) <;>
        (try omega) <;>
        (try
          {
            intro h
            have h₇ : (42 * n : ℕ) = 0 := by
              norm_cast at h ⊢
              <;> omega
            have h₈ : n = 0 := by
              omega
            omega
          })
      field_simp at h₅ ⊢
      <;>
      (try norm_num at h₅ ⊢) <;>
      (try ring_nf at h₅ ⊢) <;>
      (try norm_cast at h₅ ⊢) <;>
      (try simp_all [Rat.num_div_den]) <;>
      (try linarith) <;>
      (try nlinarith) <;>
      (try
        {
          nlinarith
        })
      <;>
      (try
        {
          simp_all [Rat.num_div_den]
          <;> norm_num
          <;> linarith
        })
      <;>
      (try
        {
          ring_nf at h₅ ⊢
          <;> norm_num at h₅ ⊢
          <;> linarith
        })
      <;>
      (try
        {
          norm_cast at h₅ ⊢
          <;> simp_all [Rat.num_div_den]
          <;> norm_num
          <;> linarith
        })
      <;>
      (try
        {
          field_simp at h₅ ⊢
          <;> ring_nf at h₅ ⊢
          <;> norm_cast at h₅ ⊢
          <;> simp_all [Rat.num_div_den]
          <;> norm_num
          <;> linarith
        })
      <;>
      (try
        {
          simp_all [Rat.num_div_den]
          <;> norm_num
          <;> linarith
        })
      <;>
      (try
        {
          nlinarith
        })
      <;>
      (try
        {
          linarith
        })
      <;>
      (try
        {
          ring_nf at h₅ ⊢
          <;> norm_num at h₅ ⊢
          <;> linarith
        })
      <;>
      (try
        {
          norm_cast at h₅ ⊢
          <;> simp_all [Rat.num_div_den]
          <;> norm_num
          <;> linarith
        })
      <;>
      (try
        {
          field_simp at h₅ ⊢
          <;> ring_nf at h₅ ⊢
          <;> norm_cast at h₅ ⊢
          <;> simp_all [Rat.num_div_den]
          <;> norm_num
          <;> linarith
        })
    have h₄ : ∃ (k : ℤ), (41 * n + 42 : ℤ) = k * (42 * n : ℤ) := by
      have h₅ : ((41 * n + 42 : ℚ) : ℚ) = (((41 * n + 42 : ℚ) / (42 * n : ℚ)).num : ℚ) * (42 * n : ℚ) := h₃
      have h₆ : ((41 * n + 42 : ℤ) : ℚ) = (((41 * n + 42 : ℚ) / (42 * n : ℚ)).num : ℚ) * (42 * n : ℚ) := by
        norm_cast at h₅ ⊢ <;>
        (try simp_all [Rat.num_div_den]) <;>
        (try ring_nf at * <;> norm_num at * <;> linarith) <;>
        (try simp_all [Rat.num_div_den]) <;>
        (try norm_cast at * <;> simp_all [Rat.num_div_den]) <;>
        (try ring_nf at * <;> norm_num at * <;> linarith)
        <;>
        (try
          {
            simp_all [Rat.num_div_den]
            <;> norm_num
            <;> linarith
          })
        <;>
        (try
          {
            norm_cast at *
            <;> simp_all [Rat.num_div_den]
            <;> norm_num
            <;> linarith
          })
        <;>
        (try
          {
            ring_nf at *
            <;> norm_num at *
            <;> linarith
          })
      have h₇ : (((41 * n + 42 : ℚ) / (42 * n : ℚ)).num : ℤ) * (42 * n : ℤ) = (41 * n + 42 : ℤ) := by
        norm_cast at h₆ ⊢
        <;>
        (try simp_all [Rat.num_div_den]) <;>
        (try ring_nf at * <;> norm_num at * <;> linarith) <;>
        (try simp_all [Rat.num_div_den]) <;>
        (try norm_cast at * <;> simp_all [Rat.num_div_den]) <;>
        (try ring_nf at * <;> norm_num at * <;> linarith)
        <;>
        (try
          {
            simp_all [Rat.num_div_den]
            <;> norm_num
            <;> linarith
          })
        <;>
        (try
          {
            norm_cast at *
            <;> simp_all [Rat.num_div_den]
            <;> norm_num
            <;> linarith
          })
        <;>
        (try
          {
            ring_nf at *
            <;> norm_num at *
            <;> linarith
          })
        <;>
        (try
          {
            field_simp at *
            <;> ring_nf at *
            <;> norm_cast at *
            <;> simp_all [Rat.num_div_den]
            <;> norm_num
            <;> linarith
          })
      refine' ⟨(((41 * n + 42 : ℚ) / (42 * n : ℚ)).num : ℤ), _⟩
      linarith
    exact h₄
  
  have h_final : (42 * n : ℤ) ∣ (41 * n + 42 : ℤ) := by
    obtain ⟨k, hk⟩ := h_main
    use k
    <;>
    (try norm_num at hk ⊢) <;>
    (try ring_nf at hk ⊢) <;>
    (try norm_cast at hk ⊢) <;>
    (try linarith) <;>
    (try nlinarith) <;>
    (try omega) <;>
    (try
      {
        simp_all [mul_comm, mul_assoc, mul_left_comm]
        <;> ring_nf at *
        <;> norm_num at *
        <;> linarith
      })
    <;>
    (try
      {
        norm_num at hk ⊢
        <;> ring_nf at hk ⊢
        <;> norm_cast at hk ⊢
        <;> linarith
      })
    <;>
    (try
      {
        simp_all [mul_comm, mul_assoc, mul_left_comm]
        <;> ring_nf at *
        <;> norm_num at *
        <;> linarith
      })
    <;>
    (try
      {
        norm_num at hk ⊢
        <;> ring_nf at hk ⊢
        <;> norm_cast at hk ⊢
        <;> linarith
      })
    <;>
    (try
      {
        simp_all [mul_comm, mul_assoc, mul_left_comm]
        <;> ring_nf at *
        <;> norm_num at *
        <;> linarith
      })
    <;>
    (try
      {
        norm_num at hk ⊢
        <;> ring_nf at hk ⊢
        <;> norm_cast at hk ⊢
        <;> linarith
      })
  
  exact h_final

theorem h_sum_eq_h_int_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n)
    (h₁ : (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1) :
    (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)) =
      ((41 * n + 42 : ℚ) / (42 * n)) := by
  have h₂ : (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ) : ℚ) = ((41 * n + 42 : ℚ) / (42 * n)) := by
    have h₃ : (1 /. (2 : ℤ) : ℚ) = 1 / 2 := by norm_num [Rat.divInt_eq_div]
    have h₄ : (1 /. (3 : ℤ) : ℚ) = 1 / 3 := by norm_num [Rat.divInt_eq_div]
    have h₅ : (1 /. (7 : ℤ) : ℚ) = 1 / 7 := by norm_num [Rat.divInt_eq_div]
    have h₆ : (1 /. (n : ℤ) : ℚ) = 1 / (n : ℚ) := by
      have h₇ : (n : ℤ) ≠ 0 := by
        norm_cast
        <;> linarith
      field_simp [h₇, Rat.divInt_eq_div]
      <;> norm_cast
      <;> field_simp [h₇]
      <;> ring_nf
      <;> norm_num
      <;> simp_all [Rat.divInt_eq_div]
      <;> norm_num
      <;> linarith
    calc
      (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ) : ℚ) = (1 / 2 + 1 / 3 + 1 / 7 + 1 / (n : ℚ) : ℚ) := by
        rw [h₃, h₄, h₅, h₆]
        <;> norm_num
      _ = ((41 * n + 42 : ℚ) / (42 * n)) := by
        have h₈ : (n : ℚ) ≠ 0 := by
          norm_cast
          <;> linarith
        field_simp [h₈]
        <;> ring_nf
        <;> field_simp [h₈]
        <;> ring_nf
        <;> norm_cast
        <;> field_simp [h₈]
        <;> ring_nf
        <;> norm_num
        <;> linarith
  
  -- Since the equality holds as rational numbers, we can directly use it to conclude the proof.
  norm_cast at h₂ ⊢
  <;>
  (try simp_all) <;>
  (try norm_num) <;>
  (try ring_nf at *) <;>
  (try field_simp at *) <;>
  (try norm_cast at *) <;>
  (try linarith)
  <;>
  simp_all [Rat.divInt_eq_div]
  <;>
  norm_num at *
  <;>
  linarith

theorem h_int_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n)
    (h₁ : (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1) :
    ∃ z : ℤ, ((41 * n + 42 : ℚ) / (42 * n)) = z := by
  have h_sum_eq :
      (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)) =
        ((41 * n + 42 : ℚ) / (42 * n)) :=
    h_sum_eq_h_int_amc12b_2002_p4 n h₀ h₁
  have h_den_one :
      ((41 * n + 42 : ℚ) / (42 * n)).den = 1 :=
    h_den_one_h_int_amc12b_2002_p4 n h₀ h₁ h_sum_eq
  have h_nonzero : (42 * n : ℤ) ≠ 0 :=
    h_nonzero_h_int_amc12b_2002_p4 n h₀
  have h_dvd :
      (42 * n : ℤ) ∣ (41 * n + 42 : ℤ) :=
    h_dvd_h_int_amc12b_2002_p4 n h₀ h₁ h_sum_eq h_den_one h_nonzero
  rcases h_dvd with ⟨z, hz⟩
  have h_eq :
      ((41 * n + 42 : ℚ) / (42 * n)) = (z : ℚ) :=
    h_eq_h_int_amc12b_2002_p4 n h₀ h₁ h_sum_eq h_den_one h_nonzero
      (by
        exact ⟨z, hz⟩) z hz
  exact ⟨z, h_eq⟩

theorem h_n_eq_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n)
    (h₁ :
      (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1)
    (h_int :
      ∃ z : ℤ, ((41 * n + 42 : ℚ) / (42 * n : ℚ)) = z)
    (h_mul_eq :
      (41 * n + 42 : ℚ) = (42 * n : ℚ) * (Int.cast (Classical.choose h_int))) :
    n = 42 := by
  have h_z_eq_one : (Classical.choose h_int : ℤ) = 1 := by
    have h₂ : (41 * n + 42 : ℚ) = (42 * n : ℚ) * (Int.cast (Classical.choose h_int)) := h_mul_eq
    have h₃ : (41 * n + 42 : ℤ) = (42 * n : ℤ) * (Classical.choose h_int) := by
      norm_cast at h₂ ⊢
      <;>
      (try norm_num at h₂ ⊢) <;>
      (try field_simp at h₂ ⊢) <;>
      (try ring_nf at h₂ ⊢) <;>
      (try norm_cast at h₂ ⊢) <;>
      (try simp_all [mul_comm]) <;>
      (try linarith) <;>
      (try
        {
          norm_num at h₂ ⊢
          <;>
          (try ring_nf at h₂ ⊢)
          <;>
          (try norm_cast at h₂ ⊢)
          <;>
          (try linarith)
        })
      <;>
      (try
        {
          field_simp at h₂ ⊢
          <;>
          ring_nf at h₂ ⊢
          <;>
          norm_cast at h₂ ⊢
          <;>
          simp_all [mul_comm]
          <;>
          linarith
        })
      <;>
      (try
        {
          norm_num at h₂ ⊢
          <;>
          ring_nf at h₂ ⊢
          <;>
          norm_cast at h₂ ⊢
          <;>
          simp_all [mul_comm]
          <;>
          linarith
        })
      <;>
      (try
        {
          norm_num at h₂ ⊢
          <;>
          field_simp at h₂ ⊢
          <;>
          ring_nf at h₂ ⊢
          <;>
          norm_cast at h₂ ⊢
          <;>
          simp_all [mul_comm]
          <;>
          linarith
        })
    have h₄ : (Classical.choose h_int : ℤ) ≥ 1 := by
      by_contra h
      have h₅ : (Classical.choose h_int : ℤ) ≤ 0 := by linarith
      have h₆ : (42 * n : ℤ) * (Classical.choose h_int) ≤ 0 := by
        have h₇ : (42 * n : ℤ) ≥ 1 := by
          have h₈ : (n : ℕ) ≥ 1 := by linarith
          have h₉ : (42 * n : ℤ) ≥ 42 * 1 := by
            norm_cast
            <;> nlinarith
          linarith
        nlinarith
      have h₇ : (41 * n + 42 : ℤ) > 0 := by
        have h₈ : (n : ℕ) ≥ 1 := by linarith
        have h₉ : (41 * n + 42 : ℤ) ≥ 41 * 1 + 42 := by
          norm_cast
          <;> nlinarith
        linarith
      linarith
    have h₅ : (Classical.choose h_int : ℤ) ≤ 1 := by
      by_contra h
      have h₆ : (Classical.choose h_int : ℤ) ≥ 2 := by linarith
      have h₇ : (42 * n : ℤ) * (Classical.choose h_int) ≥ (42 * n : ℤ) * 2 := by
        have h₈ : (42 * n : ℤ) ≥ 1 := by
          have h₉ : (n : ℕ) ≥ 1 := by linarith
          have h₁₀ : (42 * n : ℤ) ≥ 42 * 1 := by
            norm_cast
            <;> nlinarith
          linarith
        nlinarith
      have h₈ : (41 * n + 42 : ℤ) < (42 * n : ℤ) * 2 := by
        have h₉ : (n : ℕ) ≥ 1 := by linarith
        have h₁₀ : (41 * n + 42 : ℤ) < (42 * n : ℤ) * 2 := by
          norm_cast
          <;>
          (try ring_nf at * <;> nlinarith)
          <;>
          (try omega)
        exact h₁₀
      linarith
    have h₆ : (Classical.choose h_int : ℤ) = 1 := by
      linarith
    exact h₆
  
  have h_n_eq_42 : n = 42 := by
    have h₂ : (41 * n + 42 : ℚ) = (42 * n : ℚ) * (Int.cast (Classical.choose h_int)) := h_mul_eq
    have h₃ : (41 * n + 42 : ℤ) = (42 * n : ℤ) * (Classical.choose h_int) := by
      norm_cast at h₂ ⊢
      <;>
      (try norm_num at h₂ ⊢) <;>
      (try field_simp at h₂ ⊢) <;>
      (try ring_nf at h₂ ⊢) <;>
      (try norm_cast at h₂ ⊢) <;>
      (try simp_all [mul_comm]) <;>
      (try linarith) <;>
      (try
        {
          norm_num at h₂ ⊢
          <;>
          (try ring_nf at h₂ ⊢)
          <;>
          (try norm_cast at h₂ ⊢)
          <;>
          (try linarith)
        })
      <;>
      (try
        {
          field_simp at h₂ ⊢
          <;>
          ring_nf at h₂ ⊢
          <;>
          norm_cast at h₂ ⊢
          <;>
          simp_all [mul_comm]
          <;>
          linarith
        })
      <;>
      (try
        {
          norm_num at h₂ ⊢
          <;>
          ring_nf at h₂ ⊢
          <;>
          norm_cast at h₂ ⊢
          <;>
          simp_all [mul_comm]
          <;>
          linarith
        })
      <;>
      (try
        {
          norm_num at h₂ ⊢
          <;>
          field_simp at h₂ ⊢
          <;>
          ring_nf at h₂ ⊢
          <;>
          norm_cast at h₂ ⊢
          <;>
          simp_all [mul_comm]
          <;>
          linarith
        })
    have h₄ : (Classical.choose h_int : ℤ) = 1 := h_z_eq_one
    rw [h₄] at h₃
    norm_cast at h₃ ⊢
    <;>
    (try ring_nf at h₃ ⊢) <;>
    (try norm_num at h₃ ⊢) <;>
    (try omega)
    <;>
    (try
      {
        have h₅ : n ≤ 42 := by
          by_contra h₅
          have h₆ : n ≥ 43 := by omega
          have h₇ : 41 * n + 42 > 42 * n := by
            have h₈ : n ≥ 43 := by omega
            nlinarith
          omega
        interval_cases n <;> norm_num at h₃ ⊢ <;> omega
      })
  
  exact h_n_eq_42

theorem h56_plus_1over7_h_sum_three_amc12b_2002_p4 :
    ((5 : ℚ) / 6 + 1 /. (7 : ℤ) : ℚ) = (41 : ℚ) / 42 := by
  norm_num [div_eq_mul_inv, mul_assoc]
  <;>
  simp_all [div_eq_mul_inv, mul_assoc]
  <;>
  norm_num
  <;>
  ring_nf at *
  <;>
  norm_cast
  <;>
  simp_all [div_eq_mul_inv, mul_assoc]
  <;>
  norm_num
  <;>
  linarith

theorem hden_eq_one_h_sum_three_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n)
    (h₁ : (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1) :
    ((1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1) := by
  -- The hypothesis h₁ already directly states the conclusion we need to prove.
  -- Therefore, we can simply use h₁ to close the proof.
  exact h₁

theorem hsum_abc_h_sum_three_amc12b_2002_p4 (hsum_ab : (1 /. (2 : ℤ) + 1 /. (3 : ℤ) : ℚ) = (5 : ℚ) / 6)
    (h56_plus_1over7 : ((5 : ℚ) / 6 + 1 /. (7 : ℤ) : ℚ) = (41 : ℚ) / 42) :
    (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) : ℚ) = (41 : ℚ) / 42 := by
  have h_main : (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) : ℚ) = (41 : ℚ) / 42 := by
    calc
      (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) : ℚ) = (1 /. (2 : ℤ) + 1 /. (3 : ℤ) : ℚ) + 1 /. (7 : ℤ) := by
        ring_nf
      _ = (5 : ℚ) / 6 + 1 /. (7 : ℤ) := by
        rw [hsum_ab]
      _ = (41 : ℚ) / 42 := by
        rw [h56_plus_1over7]
  
  exact h_main

theorem h_add_hsum_ab_h_sum_three_amc12b_2002_p4 : (1 : ℚ) / 2 + (1 : ℚ) / 3 = (5 : ℚ) / 6 := by
  norm_num [div_eq_mul_inv, add_mul]
  <;> ring_nf
  <;> norm_num
  <;> rfl

theorem h_one_third_hsum_ab_h_sum_three_amc12b_2002_p4 :
    (1 /. (3 : ℤ) : ℚ) = (1 : ℚ) / 3 := by
  simpa using (Rat.divInt_eq_div 1 3)

theorem h_one_half_hsum_ab_h_sum_three_amc12b_2002_p4 :
    (1 /. (2 : ℤ) : ℚ) = (1 : ℚ) / 2 := by
  simpa using (Rat.intCast_div_eq_divInt (1) (2)).symm

theorem hsum_ab_h_sum_three_amc12b_2002_p4 :
    (1 /. (2 : ℤ) + 1 /. (3 : ℤ) : ℚ) = (5 : ℚ) / 6 := by
  have h_one_half : (1 /. (2 : ℤ) : ℚ) = (1 : ℚ) / 2 :=
    h_one_half_hsum_ab_h_sum_three_amc12b_2002_p4
  have h_one_third : (1 /. (3 : ℤ) : ℚ) = (1 : ℚ) / 3 :=
    h_one_third_hsum_ab_h_sum_three_amc12b_2002_p4
  have h_add : (1 : ℚ) / 2 + (1 : ℚ) / 3 = (5 : ℚ) / 6 :=
    h_add_hsum_ab_h_sum_three_amc12b_2002_p4
  calc
    (1 /. (2 : ℤ) + 1 /. (3 : ℤ) : ℚ)
        = (1 : ℚ) / 2 + (1 : ℚ) / 3 := by
          simpa [h_one_half, h_one_third]
    _ = (5 : ℚ) / 6 := by
          simpa using h_add

theorem hden_char_h_sum_three_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n) :
    ((1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1) ↔
      ((1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)) =
        ((1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).num)) := by
  have h_general : ∀ (q : ℚ), q.den = 1 ↔ q = q.num := by
    intro q
    constructor
    · -- Prove the forward direction: if q.den = 1, then q = q.num
      intro h
      have h₁ : (q.num : ℚ) / q.den = q := by
        exact Rat.num_div_den q
      have h₂ : (q.num : ℚ) / q.den = (q.num : ℚ) := by
        rw [h]
        <;> field_simp
      have h₃ : (q.num : ℚ) = q := by
        linarith
      norm_cast at h₃ ⊢
      <;> simp_all [Rat.num_div_den]
      <;> field_simp at *
      <;> ring_nf at *
      <;> norm_cast at *
      <;> linarith
    · -- Prove the reverse direction: if q = q.num, then q.den = 1
      intro h
      have h₁ : (q.num : ℚ) / q.den = q := by
        exact Rat.num_div_den q
      have h₂ : (q.num : ℚ) / q.den = (q.num : ℚ) := by
        rw [h] at *
        <;> norm_cast at *
        <;> simp_all
      have h₃ : (q.num : ℚ) = (q.num : ℚ) * q.den := by
        have h₄ : (q.den : ℚ) ≠ 0 := by
          norm_cast
          <;> exact Nat.cast_ne_zero.mpr (by
            have h₅ : 0 < q.den := by
              exact q.pos
            linarith)
        field_simp at h₂ ⊢
        <;> ring_nf at h₂ ⊢ <;>
          (try norm_num at h₂ ⊢) <;>
          (try simp_all) <;>
          (try nlinarith) <;>
          (try linarith) <;>
          (try nlinarith)
        <;>
          (try
            {
              nlinarith
            })
        <;>
          (try
            {
              linarith
            })
        <;>
          (try
            {
              nlinarith
            })
      by_cases h₄ : q.num = 0
      · -- Case: q.num = 0
        have h₅ : q.den = 1 := by
          have h₆ : Int.gcd q.num q.den = 1 := by
            exact q.reduced
          have h₇ : q.num = 0 := h₄
          rw [h₇] at h₆
          have h₈ : Int.gcd 0 q.den = 1 := h₆
          have h₉ : (q.den : ℤ) = 1 := by
            simp [Int.gcd_eq_right] at h₈ ⊢
            <;>
            (try omega) <;>
            (try
              {
                norm_cast at h₈ ⊢ <;>
                simp_all [Nat.gcd_eq_right]
                <;>
                omega
              })
          norm_cast at h₉ ⊢ <;>
          simp_all
        exact h₅
      · -- Case: q.num ≠ 0
        have h₅ : (q.den : ℚ) = 1 := by
          have h₆ : (q.num : ℚ) ≠ 0 := by
            norm_cast
            <;>
            (try simp_all) <;>
            (try omega)
          apply mul_left_cancel₀ h₆
          linarith
        norm_cast at h₅ ⊢ <;>
        (try simp_all) <;>
        (try omega)
  
  have h_main : ((1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1) ↔ ((1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)) = ((1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).num)) := by
    have h₁ : ((1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1) ↔ ((1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)) = ((1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).num)) := by
      have h₂ := h_general (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ))
      exact h₂
    exact h₁
  
  exact h_main

theorem h_sum_three_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n)
    (h₁ : (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1) :
    (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ)) = (41 : ℚ) / 42 := by
  have hsum_ab : (1 /. (2 : ℤ) + 1 /. (3 : ℤ) : ℚ) = (5 : ℚ) / 6 := by
    simpa using hsum_ab_h_sum_three_amc12b_2002_p4
  have h56_plus_1over7 :
      ((5 : ℚ) / 6 + 1 /. (7 : ℤ) : ℚ) = (41 : ℚ) / 42 := by
    simpa using h56_plus_1over7_h_sum_three_amc12b_2002_p4
  have hsum_abc :
      (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) : ℚ) = (41 : ℚ) / 42 := by
    exact hsum_abc_h_sum_three_amc12b_2002_p4 hsum_ab h56_plus_1over7
  have hden_eq_one :
      ((1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1) := by
    exact hden_eq_one_h_sum_three_amc12b_2002_p4 n h₀ h₁
  have hden_char :
      ((1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1) ↔
        ((1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)) =
          ((1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).num)) := by
    exact hden_char_h_sum_three_amc12b_2002_p4 n h₀
  exact hsum_abc

theorem h_n_ne_zero_h_den_eq_one_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n) : (n : ℚ) ≠ 0 := by
  intro h
  have h₁ : (n : ℚ) = 0 := h
  have h₂ : (n : ℕ) = 0 := by
    norm_cast at h₁ ⊢
    <;> simp_all [Nat.cast_eq_zero]
  have h₃ : 0 < n := h₀
  linarith

theorem h_den_h_den_eq_one_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n)
    (h₁ : (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1)
    (h_sum_eq :
      (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)) =
        ((41 * n + 42 : ℚ) / (42 * n))) :
    ((41 * n + 42 : ℚ) / (42 * n)).den = 1 := by
  have h₂ : ((41 * n + 42 : ℚ) / (42 * n)).den = 1 := by
    have h₃ : (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = ((41 * n + 42 : ℚ) / (42 * n)).den := by
      rw [h_sum_eq]
    rw [h₃] at h₁
    exact h₁
  
  exact h₂

theorem h2_h_ab_h_sum_eq_h_den_eq_one_amc12b_2002_p4 : (1 /. (3 : ℤ)) = (1 : ℚ) / 3 := by
  norm_num [Rat.divInt_eq_div]
  <;> rfl

theorem hcalc_h_ab_h_sum_eq_h_den_eq_one_amc12b_2002_p4 : ((2 : ℚ)⁻¹ + (3 : ℚ)⁻¹) = (5 : ℚ) / 6 := by
  norm_num [div_eq_mul_inv]
  <;>
  ring_nf
  <;>
  norm_num
  <;>
  rfl

theorem h1_h_ab_h_sum_eq_h_den_eq_one_amc12b_2002_p4 :
    (1 /. (2 : ℤ)) = (1 : ℚ) / 2 := by
  simpa using (Rat.mkRat_eq_div (n := (1 : ℤ)) (d := (2 : ℕ)))

theorem h_ab_h_sum_eq_h_den_eq_one_amc12b_2002_p4 :
    (1 /. (2 : ℤ) + 1 /. (3 : ℤ)) = (5 : ℚ) / 6 := by
  have h1 : (1 /. (2 : ℤ)) = (1 : ℚ) / 2 := by
    exact h1_h_ab_h_sum_eq_h_den_eq_one_amc12b_2002_p4
  have h2 : (1 /. (3 : ℤ)) = (1 : ℚ) / 3 := by
    exact h2_h_ab_h_sum_eq_h_den_eq_one_amc12b_2002_p4
  have hcalc : ((2 : ℚ)⁻¹ + (3 : ℚ)⁻¹) = (5 : ℚ) / 6 := by
    exact hcalc_h_ab_h_sum_eq_h_den_eq_one_amc12b_2002_p4
  calc
    (1 /. (2 : ℤ) + 1 /. (3 : ℤ))
        = ((2 : ℚ)⁻¹ + (3 : ℚ)⁻¹) := by
          simpa [h1, h2]
    _ = (5 : ℚ) / 6 := by
          exact hcalc

theorem h_left_h_total_h_sum_eq_h_den_eq_one_amc12b_2002_p4 (n : ℕ)
    (h_abc :
        ((1 /. (2 : ℤ) + 1 /. (3 : ℤ)) + 1 /. (7 : ℤ)) = (41 : ℚ) / 42) :
    ((1 /. (2 : ℤ) + 1 /. (3 : ℤ)) + 1 /. (7 : ℤ)) + 1 /. (n : ℤ) =
      (41 : ℚ) / 42 + 1 /. (n : ℤ) := by
  have h_main : ((1 /. (2 : ℤ) + 1 /. (3 : ℤ)) + 1 /. (7 : ℤ)) + 1 /. (n : ℤ) = (41 : ℚ) / 42 + 1 /. (n : ℤ) := by
    rw [h_abc]
    <;> simp [add_assoc]
    <;> norm_num
    <;> field_simp
    <;> ring_nf
    <;> norm_cast
    <;> simp_all [div_eq_mul_inv]
    <;> norm_num
    <;> linarith
  
  exact h_main

theorem h_sum_h_total_h_sum_eq_h_den_eq_one_amc12b_2002_p4 (n : ℕ)
    (h_n_ne_zero : (n : ℚ) ≠ 0) :
    (41 : ℚ) / 42 + 1 /. (n : ℤ) = ((41 * n + 42 : ℚ) / (42 * n)) := by
  have hn : (n : ℚ) ≠ 0 := h_n_ne_zero
  have h :
      (41 : ℚ) / 42 + (1 : ℚ) / (n : ℚ) =
        ((41 * n + 42 : ℚ) / (42 * n)) := by
    field_simp [hn]
  simpa [Rat.divInt_eq_div] using h

theorem h_total_h_sum_eq_h_den_eq_one_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n) (h_n_ne_zero : (n : ℚ) ≠ 0)
    (h_abc :
        ((1 /. (2 : ℤ) + 1 /. (3 : ℤ)) + 1 /. (7 : ℤ)) = (41 : ℚ) / 42) :
    (((1 /. (2 : ℤ) + 1 /. (3 : ℤ)) + 1 /. (7 : ℤ)) + 1 /. (n : ℤ)) =
      ((41 * n + 42 : ℚ) / (42 * n)) := by
  have h_left :
      ((1 /. (2 : ℤ) + 1 /. (3 : ℤ)) + 1 /. (7 : ℤ)) + 1 /. (n : ℤ) =
        (41 : ℚ) / 42 + 1 /. (n : ℤ) := by
    exact h_left_h_total_h_sum_eq_h_den_eq_one_amc12b_2002_p4 n h_abc
  have h_sum :
      (41 : ℚ) / 42 + 1 /. (n : ℤ) =
        ((41 * n + 42 : ℚ) / (42 * n)) := by
    exact h_sum_h_total_h_sum_eq_h_den_eq_one_amc12b_2002_p4 n h_n_ne_zero
  exact h_left.trans h_sum

theorem h_abc_h_sum_eq_h_den_eq_one_amc12b_2002_p4 (h_ab : (1 /. (2 : ℤ) + 1 /. (3 : ℤ)) = (5 : ℚ) / 6) :
    ((1 /. (2 : ℤ) + 1 /. (3 : ℤ)) + 1 /. (7 : ℤ)) = (41 : ℚ) / 42 := by
  have h₁ : ((1 /. (2 : ℤ) + 1 /. (3 : ℤ)) + 1 /. (7 : ℤ)) = (41 : ℚ) / 42 := by
    norm_num [div_eq_mul_inv, add_assoc] at h_ab ⊢
    <;>
    (try norm_cast at h_ab ⊢) <;>
    (try ring_nf at h_ab ⊢) <;>
    (try field_simp at h_ab ⊢) <;>
    (try norm_num at h_ab ⊢) <;>
    (try linarith)
    <;>
    rfl
  
  exact h₁

theorem h_sum_eq_h_den_eq_one_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n)
    (h₁ : (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1)
    (h_n_ne_zero : (n : ℚ) ≠ 0) :
    (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)) =
      ((41 * n + 42 : ℚ) / (42 * n)) := by
  have h_ab : (1 /. (2 : ℤ) + 1 /. (3 : ℤ)) = (5 : ℚ) / 6 :=
    h_ab_h_sum_eq_h_den_eq_one_amc12b_2002_p4
  have h_abc :
      ((1 /. (2 : ℤ) + 1 /. (3 : ℤ)) + 1 /. (7 : ℤ)) = (41 : ℚ) / 42 :=
    h_abc_h_sum_eq_h_den_eq_one_amc12b_2002_p4 h_ab
  have h_total :
      (((1 /. (2 : ℤ) + 1 /. (3 : ℤ)) + 1 /. (7 : ℤ)) + 1 /. (n : ℤ)) =
        ((41 * n + 42 : ℚ) / (42 * n)) :=
    h_total_h_sum_eq_h_den_eq_one_amc12b_2002_p4 n h₀ h_n_ne_zero h_abc
  simpa [Rat.add_assoc] using h_total

theorem h_den_eq_one_amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n)
    (h₁ : (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)).den = 1) :
    ((41 * n + 42 : ℚ) / (42 * n)).den = 1 := by
  have h_n_ne_zero : (n : ℚ) ≠ 0 :=
    h_n_ne_zero_h_den_eq_one_amc12b_2002_p4 n h₀
  have h_sum_eq :
      (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (n : ℤ)) =
        ((41 * n + 42 : ℚ) / (42 * n)) :=
    h_sum_eq_h_den_eq_one_amc12b_2002_p4 n h₀ h₁ h_n_ne_zero
  have h_den : ((41 * n + 42 : ℚ) / (42 * n)).den = 1 :=
    h_den_h_den_eq_one_amc12b_2002_p4 n h₀ h₁ h_sum_eq
  exact h_den

theorem amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n)
    (h₁ : (1 /. 2 + 1 /. 3 + 1 /. 7 + 1 /. ↑n).den = 1) : n = 42 := by
  have h_sum_three :
      (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ)) = (41 : ℚ) / 42 :=
    h_sum_three_amc12b_2002_p4 n h₀ h₁
  have h_sum_eq :
      (1 /. (2 : ℤ) + 1 /. (3 : ℤ) + 1 /. (7 : ℤ) + 1 /. (↑n : ℤ)) =
        ((41 * n + 42 : ℚ) / (42 * n)) :=
    h_sum_eq_amc12b_2002_p4 n h₀ h₁
  have h_den_eq_one :
      ((41 * n + 42 : ℚ) / (42 * n)).den = 1 :=
    h_den_eq_one_amc12b_2002_p4 n h₀ h₁
  have h_int :
      ∃ z : ℤ, ((41 * n + 42 : ℚ) / (42 * n)) = z :=
    h_int_amc12b_2002_p4 n h₀ h₁
  have h_mul_eq :
      (41 * n + 42 : ℚ) = (42 * n : ℚ) * (Int.cast (Classical.choose h_int)) :=
    h_mul_eq_amc12b_2002_p4 n h₀ h₁ h_int
  have h_n_eq : n = 42 :=
    h_n_eq_amc12b_2002_p4 n h₀ h₁ h_int h_mul_eq
  exact h_n_eq

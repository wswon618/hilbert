import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h_sum_lt_198_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_sum_lt_integral :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
          ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by
  have h₁ : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by
    linarith
  exact h₁

theorem h_antitone_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000) := by
  refine' fun x hx y hy hxy => _
  have hx' : 1 ≤ x := by exact hx.1
  have hy' : y ≤ 10000 := by exact hy.2
  have hxy' : x ≤ y := by exact hxy
  have h₁ : 0 < x := by linarith
  have h₂ : 0 < y := by linarith
  have h₃ : 0 < Real.sqrt x := Real.sqrt_pos.mpr h₁
  have h₄ : 0 < Real.sqrt y := Real.sqrt_pos.mpr h₂
  have h₅ : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy'
  have h₆ : 0 < Real.sqrt x * Real.sqrt y := by positivity
  -- Use the fact that the reciprocal function is decreasing to conclude the proof
  have h₇ : 1 / Real.sqrt x ≥ 1 / Real.sqrt y := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact h₅
  exact h₇

theorem hsqrt1_h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    Real.sqrt (1 : ℝ) = (1 : ℝ) := by
  norm_num [Real.sqrt_eq_iff_sq_eq]
  <;>
  linarith [Real.sqrt_nonneg 1]

theorem hsqrt10000_h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    Real.sqrt (10000 : ℝ) = (100 : ℝ) := by
  have h₁ : Real.sqrt (10000 : ℝ) = 100 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;>
    norm_num
  rw [h₁]
  <;> norm_num

theorem hfinal_h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198
    (hsqrt10000 :
      Real.sqrt (10000 : ℝ) = (100 : ℝ))
    (hsqrt1 :
      Real.sqrt (1 : ℝ) = (1 : ℝ)) :
    (2 : ℝ) * Real.sqrt (10000 : ℝ) - 2 = (198 : ℝ) := by
  have h₁ : (2 : ℝ) * Real.sqrt (10000 : ℝ) - 2 = (198 : ℝ) := by
    rw [hsqrt10000]
    norm_num
  exact h₁

theorem hcalc_h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198
    (hderiv :
      ∀ x ∈ Set.uIcc (1 : ℝ) 10000,
        HasDerivAt (fun x => (2 : ℝ) * Real.sqrt x) (1 / Real.sqrt x) x)
    (hint :
      IntervalIntegrable (fun x => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume (1 : ℝ) 10000) :
    (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
      (2 : ℝ) * Real.sqrt (10000 : ℝ) - (2 : ℝ) * Real.sqrt (1 : ℝ) := by
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (1 : ℝ)) (b := (10000 : ℝ))
      (f := fun x => (2 : ℝ) * Real.sqrt x)
      (f' := fun x => (1 : ℝ) / Real.sqrt x)
      hderiv hint
  simpa using h

theorem hderiv_h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ∀ x ∈ Set.uIcc (1 : ℝ) 10000,
      HasDerivAt (fun x => (2 : ℝ) * Real.sqrt x) (1 / Real.sqrt x) x := by
  intro x hx
  rcases hx with ⟨hx₁, hx₂⟩
  have hx0 : x ≠ (0 : ℝ) := by
    have : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx₁
    exact ne_of_gt this
  have h := (Real.hasDerivAt_sqrt (x:=x) hx0)
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h.const_mul (2 : ℝ)

theorem hint_h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    IntervalIntegrable (fun x => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume (1 : ℝ) 10000 := by
  -- continuity of the integrand on the closed interval [1,10000]
  have hcont :
      ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000) := by
    have h_one : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (1 : ℝ) 10000) :=
      (continuous_const).continuousOn
    have h_sqrt : ContinuousOn Real.sqrt (Set.Icc (1 : ℝ) 10000) :=
      (continuous_sqrt).continuousOn
    have h_ne : ∀ x ∈ Set.Icc (1 : ℝ) 10000, Real.sqrt x ≠ 0 := by
      intro x hx
      have hxpos : (0 : ℝ) < x := by
        have : (1 : ℝ) ≤ x := hx.1
        exact lt_of_lt_of_le (by norm_num) this
      have : 0 < Real.sqrt x := (Real.sqrt_pos).2 hxpos
      exact ne_of_gt this
    exact h_one.div h_sqrt h_ne
  have hle : (1 : ℝ) ≤ 10000 := by norm_num
  exact
    (ContinuousOn.intervalIntegrable_of_Icc
        (μ := MeasureTheory.volume) (a := (1 : ℝ)) (b := 10000) hle hcont)

theorem h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by
  have hderiv :
      ∀ x ∈ Set.uIcc (1 : ℝ) 10000,
        HasDerivAt (fun x => (2 : ℝ) * Real.sqrt x) (1 / Real.sqrt x) x :=
    hderiv_h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198
  have hint :
      IntervalIntegrable (fun x => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume (1 : ℝ) 10000 :=
    hint_h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198
  have hcalc :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
        (2 : ℝ) * Real.sqrt (10000 : ℝ) - (2 : ℝ) * Real.sqrt (1 : ℝ) :=
    hcalc_h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198 hderiv hint
  have hsqrt10000 :
      Real.sqrt (10000 : ℝ) = (100 : ℝ) :=
    hsqrt10000_h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198
  have hsqrt1 :
      Real.sqrt (1 : ℝ) = (1 : ℝ) :=
    hsqrt1_h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198
  have hfinal :
      (2 : ℝ) * Real.sqrt (10000 : ℝ) - 2 = (198 : ℝ) :=
    hfinal_h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198 hsqrt10000 hsqrt1
  simpa [hfinal] using hcalc

theorem h_goal_h_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 (h_le :
    (∑ i in Finset.Ico (1 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt (i + 1)) ≤
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
    (h_sum_eq :
    (∑ i in Finset.Ico (1 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt (i + 1)) =
      ∑ k in Finset.Icc (2 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt k) :
    (∑ k in Finset.Icc (2 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt k) ≤
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h_main : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤ ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
    calc
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) = (∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) := by
        rw [h_sum_eq]
        <;>
        simp_all [Finset.sum_range_succ, Finset.sum_range_zero]
        <;>
        norm_num
        <;>
        rfl
      _ ≤ ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
        exact h_le
  exact h_main

theorem h_sum_eq_h_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ i in Finset.Ico (1 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt (i + 1)) =
      ∑ k in Finset.Icc (2 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt k := by
  have h_main : (∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) = ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by
    have h₁ : (∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) = ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by
      -- Define the bijection and its inverse
      have h₂ : (∑ i in Finset.Ico (1 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) = ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by
        -- Use the bijection to reindex the sum
        apply Finset.sum_bij' (fun (i : ℕ) _ => i + 1) (fun (k : ℕ) _ => k - 1)
        <;> simp_all [Finset.mem_Ico, Finset.mem_Icc, Nat.lt_succ_iff]
        <;> (try omega) <;> (try
          {
            intros
            <;> norm_num at *
            <;> (try omega)
            <;> (try ring_nf at *)
            <;> (try field_simp at *)
            <;> (try norm_cast at *)
            <;> (try linarith)
          })
        <;> (try
          {
            intros
            <;> norm_num at *
            <;> (try omega)
            <;> (try ring_nf at *)
            <;> (try field_simp at *)
            <;> (try norm_cast at *)
            <;> (try linarith)
          })
        <;> (try
          {
            intros
            <;> simp_all [Finset.mem_Ico, Finset.mem_Icc, Nat.lt_succ_iff]
            <;> norm_num at *
            <;> (try omega)
            <;> (try ring_nf at *)
            <;> (try field_simp at *)
            <;> (try norm_cast at *)
            <;> (try linarith)
          })
        <;> (try
          {
            intros
            <;> simp_all [Finset.mem_Ico, Finset.mem_Icc, Nat.lt_succ_iff]
            <;> norm_num at *
            <;> (try omega)
            <;> (try ring_nf at *)
            <;> (try field_simp at *)
            <;> (try norm_cast at *)
            <;> (try linarith)
          })
        <;> (try
          {
            intros
            <;> simp_all [Finset.mem_Ico, Finset.mem_Icc, Nat.lt_succ_iff]
            <;> norm_num at *
            <;> (try omega)
            <;> (try ring_nf at *)
            <;> (try field_simp at *)
            <;> (try norm_cast at *)
            <;> (try linarith)
          })
        <;> (try
          {
            intros
            <;> simp_all [Finset.mem_Ico, Finset.mem_Icc, Nat.lt_succ_iff]
            <;> norm_num at *
            <;> (try omega)
            <;> (try ring_nf at *)
            <;> (try field_simp at *)
            <;> (try norm_cast at *)
            <;> (try linarith)
          })
      exact h₂
    exact h₁
  exact h_main

theorem h_le_h_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000)) :
    (∑ i in Finset.Ico (1 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt (i + 1)) ≤
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have hle :=
    (AntitoneOn.sum_le_integral_Ico
      (a := (1 : ℕ)) (b := 10000)
      (f := fun x : ℝ => (1 : ℝ) / Real.sqrt x)
      (by norm_num)
      (by
        simpa using h_antitone))
  simpa using hle

theorem h_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  -- 1. Apply the antitone sum‑integral comparison theorem on `[1,10000]`.
  have h_le :
      (∑ i in Finset.Ico (1 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
    exact
      h_le_h_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
        h_antitone
  -- 2. Rewrite the sum over `Ico 1 10000` of `f (i+1)` as a sum over `Icc 2 10000`.
  have h_sum_eq :
      (∑ i in Finset.Ico (1 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt (i + 1)) =
      ∑ k in Finset.Icc (2 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt k := by
    exact
      h_sum_eq_h_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  -- 3. Combine the two previous results to obtain the desired inequality.
  have h_goal :
      (∑ k in Finset.Icc (2 : ℕ) 10000,
        (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
    exact
      h_goal_h_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
        h_le h_sum_eq
  -- 4. Conclude.
  exact h_goal

theorem h_antitone_sub_h_sum_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000)) :
    AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) 10000) := by
  have h₁ : Set.Icc (2 : ℝ) 10000 ⊆ Set.Icc (1 : ℝ) 10000 := by
    intro x hx
    simp only [Set.mem_Icc] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  -- Use the fact that the function is antitone on the larger interval to deduce it is antitone on the smaller interval
  exact h_antitone.mono h₁

theorem h_sum_le_int'_h_sum_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_sum_eq :
        (∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
          ∑ i in Finset.Ico (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1))
    (h_sum_le_int :
        (∑ i in Finset.Ico (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) ≤
          ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) :
    (∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
      ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h₁ : (∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤ ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
    calc
      (∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) = ∑ i in Finset.Ico (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1) := by rw [h_sum_eq]
      _ ≤ ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
        -- Use the given inequality h_sum_le_int to conclude the proof
        exact h_sum_le_int
  exact h₁

theorem h_goal_h_sum_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_sum_le_int' :
        (∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
      (1 : ℝ) / Real.sqrt (2) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h_sum_split : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) = (1 : ℝ) / Real.sqrt 2 + ∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by
    have h₁ : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) = (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) := rfl
    rw [h₁]
    have h₂ : Finset.Icc (2 : ℕ) 10000 = {2} ∪ Finset.Icc 3 10000 := by
      apply Finset.ext
      intro x
      simp [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
      <;>
      (try omega) <;>
      (try
        {
          by_cases h : x = 2 <;> by_cases h' : x ≤ 10000 <;> by_cases h'' : 3 ≤ x <;> simp_all [h, h', h'']
          <;> omega
        }) <;>
      (try omega)
    rw [h₂]
    have h₃ : Disjoint ({2} : Finset ℕ) (Finset.Icc 3 10000) := by
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      simp [Finset.mem_singleton] at hx₁
      simp [Finset.mem_Icc] at hx₂
      <;> omega
    rw [Finset.sum_union h₃]
    <;> simp [Finset.sum_singleton]
    <;> norm_num
    <;>
    (try
      {
        field_simp [Real.sqrt_eq_iff_sq_eq]
        <;> ring_nf
        <;> norm_num
      })
    <;>
    (try
      {
        simp_all [Finset.sum_range_succ, add_assoc]
        <;> norm_num
        <;> linarith
      })
  
  have h_main : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤ (1 : ℝ) / Real.sqrt (2) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
    rw [h_sum_split]
    have h₂ : (∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤ ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := h_sum_le_int'
    have h₃ : (1 : ℝ) / Real.sqrt 2 + ∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k ≤ (1 : ℝ) / Real.sqrt 2 + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
      linarith
    linarith
  
  exact h_main

theorem h_sum_eq_h_sum_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
      ∑ i in Finset.Ico (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1) := by
  have h_main : (∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) = ∑ i in Finset.Ico (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1) := by
    have h₁ : (∑ i in Finset.Ico (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) = ∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by
      -- Define the bijection between Finset.Ico 2 10000 and Finset.Icc 3 10000
      have h₂ : ∑ i in Finset.Ico (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1) = ∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by
        -- Use the bijection to reindex the sum
        apply Finset.sum_bij' (fun (i : ℕ) _ => i + 1) (fun (k : ℕ) _ => k - 1)
        <;> simp_all [Finset.mem_Ico, Finset.mem_Icc, Nat.lt_succ_iff]
        <;> (try norm_num) <;> (try omega) <;> (try
          {
            intro i hi
            norm_num at hi ⊢
            <;>
            (try
              {
                constructor <;>
                (try omega) <;>
                (try
                  {
                    cases i with
                    | zero => contradiction
                    | succ i' =>
                      cases i' with
                      | zero => contradiction
                      | succ i'' =>
                        simp_all [Nat.succ_eq_add_one, Nat.add_assoc]
                        <;> norm_num <;> omega
                  })
              })
          }) <;> (try
          {
            intro k hk
            norm_num at hk ⊢
            <;>
            (try
              {
                constructor <;>
                (try omega) <;>
                (try
                  {
                    cases k with
                    | zero => contradiction
                    | succ k' =>
                      cases k' with
                      | zero => contradiction
                      | succ k'' =>
                        cases k'' with
                        | zero => contradiction
                        | succ k''' =>
                          simp_all [Nat.succ_eq_add_one, Nat.add_assoc]
                          <;> norm_num <;> omega
                  })
              })
          }) <;> (try
          {
            intro i hi
            norm_num at hi ⊢
            <;> field_simp [Real.sqrt_eq_iff_sq_eq] <;> ring_nf <;> norm_cast <;> field_simp <;> ring_nf <;> norm_num <;>
              simp_all [Nat.cast_add, Nat.cast_one]
            <;>
            (try
              {
                cases i with
                | zero => contradiction
                | succ i' =>
                  cases i' with
                  | zero => contradiction
                  | succ i'' =>
                    simp_all [Nat.succ_eq_add_one, Nat.add_assoc]
                    <;> norm_num <;> ring_nf <;> norm_cast <;> field_simp <;> ring_nf <;> norm_num
                    <;>
                    linarith
              })
          }) <;> (try
          {
            intro k hk
            norm_num at hk ⊢
            <;> field_simp [Real.sqrt_eq_iff_sq_eq] <;> ring_nf <;> norm_cast <;> field_simp <;> ring_nf <;> norm_num <;>
              simp_all [Nat.cast_add, Nat.cast_one]
            <;>
            (try
              {
                cases k with
                | zero => contradiction
                | succ k' =>
                  cases k' with
                  | zero => contradiction
                  | succ k'' =>
                    cases k'' with
                    | zero => contradiction
                    | succ k''' =>
                      simp_all [Nat.succ_eq_add_one, Nat.add_assoc]
                      <;> norm_num <;> ring_nf <;> norm_cast <;> field_simp <;> ring_nf <;> norm_num
                      <;>
                      linarith
              })
          })
      -- The result follows from the bijection
      exact h₂
    -- The final result follows from the established equality
    linarith
  
  -- The final result follows from the established equality
  exact h_main

theorem h_sum_le_int_h_sum_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone_sub :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) 10000)) :
    (∑ i in Finset.Ico (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) ≤
      ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have hab : (2 : ℕ) ≤ 10000 := by norm_num
  simpa using
    (AntitoneOn.sum_le_integral_Ico
        (a := (2 : ℕ)) (b := 10000)
        (f := fun x : ℝ => (1 : ℝ) / Real.sqrt x)
        hab h_antitone_sub)

theorem h_sum_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ))
    (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
    (h_pos :
        (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x)
    (h_int_gt_f2 :
        (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
      (1 : ℝ) / Real.sqrt (2) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  -- 1. Restrict the antitone hypothesis to the interval [2,10000].
  have h_antitone_sub :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) 10000) :=
    h_antitone_sub_h_sum_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 h_antitone
  -- 2. Rewrite the sum over `Ico 2 10000` with the shift `i ↦ i+1` as a sum over `Icc 3 10000`.
  have h_sum_eq :
      (∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) =
        ∑ i in Finset.Ico (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1) :=
    h_sum_eq_h_sum_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  -- 3. Apply the antitone‑sum versus integral estimate on the interval [2,10000].
  have h_sum_le_int :
      (∑ i in Finset.Ico (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt (i + 1)) ≤
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x :=
    h_sum_le_int_h_sum_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 h_antitone_sub
  -- 4. Transfer the inequality to the sum over `Icc 3 10000` using the equality from step 2.
  have h_sum_le_int' :
      (∑ k in Finset.Icc (3 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x :=
    h_sum_le_int'_h_sum_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 h_sum_eq h_sum_le_int
  -- 5. Split the original sum into the first term `1/√2` plus the sum from `3` to `10000`,
  --    then combine with the inequality from step 4.
  have h_goal :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        (1 : ℝ) / Real.sqrt (2) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x :=
    h_goal_h_sum_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 h_sum_le_int'
  exact h_goal

theorem h_sqrt2_pos_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 : (0 : ℝ) < Real.sqrt (2 : ℝ) := by
  have h : (0 : ℝ) < Real.sqrt 2 := by
    apply Real.sqrt_pos_of_pos
    norm_num
  exact h

theorem h_one_div_sqrt2_pos_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_sqrt2_pos : (0 : ℝ) < Real.sqrt (2 : ℝ)) :
    (0 : ℝ) < (1 : ℝ) / Real.sqrt (2 : ℝ) := by
  have h₁ : (0 : ℝ) < Real.sqrt (2 : ℝ) := h_sqrt2_pos
  have h₂ : (0 : ℝ) < (1 : ℝ) / Real.sqrt (2 : ℝ) := by
    apply div_pos
    · norm_num
    · exact h₁
  exact h₂

theorem h_const_integral_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2 : ℝ) =
      (1 : ℝ) / Real.sqrt (2 : ℝ) := by
  have h₁ : ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2 : ℝ) = (2 - 1) * ((1 : ℝ) / Real.sqrt (2 : ℝ)) := by
    -- The integral of a constant function over an interval [a, b] is (b - a) * constant
    simp [intervalIntegral.integral_const]
    <;> ring_nf
    <;> field_simp
    <;> ring_nf
  rw [h₁]
  -- Simplify the expression (2 - 1) * (1 / sqrt(2)) to 1 / sqrt(2)
  <;> norm_num
  <;> field_simp
  <;> ring_nf
  <;> norm_num
  <;> linarith [Real.sqrt_nonneg 2]

theorem h_lower_bound_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_const_integral :
        ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2 : ℝ) =
          (1 : ℝ) / Real.sqrt (2 : ℝ))
    (h_integral_le :
        (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2 : ℝ)) ≤
          ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) :
    (1 : ℝ) / Real.sqrt (2 : ℝ) ≤
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by
  have h₁ : (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by
    calc
      (1 : ℝ) / Real.sqrt (2 : ℝ) = ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2 : ℝ) := by
        rw [h_const_integral]
      _ ≤ ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := h_integral_le
  exact h₁

theorem h_pos_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_one_div_sqrt2_pos :
        (0 : ℝ) < (1 : ℝ) / Real.sqrt (2 : ℝ))
    (h_lower_bound :
        (1 : ℝ) / Real.sqrt (2 : ℝ) ≤
          ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) :
    (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by
  have h₁ : 0 < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by
    -- Use the given lower bound and the fact that 1 / sqrt(2) is positive to conclude that the integral is positive.
    have h₂ : 0 < (1 : ℝ) / Real.sqrt (2 : ℝ) := h_one_div_sqrt2_pos
    have h₃ : (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := h_lower_bound
    -- Since 1 / sqrt(2) is positive and less than or equal to the integral, the integral must be positive.
    linarith
  exact h₁

theorem h_pointwise_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x)
          (Set.Icc (1 : ℝ) 10000)) :
    ∀ x ∈ Set.Icc (1 : ℝ) 2,
      (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (1 : ℝ) / Real.sqrt x := by
  intro x hx
  have h₁ : x ∈ Set.Icc (1 : ℝ) 10000 := by
    have h₁₁ : 1 ≤ x := hx.1
    have h₁₂ : x ≤ 2 := hx.2
    have h₁₃ : x ≤ 10000 := by linarith
    exact ⟨h₁₁, h₁₃⟩
  
  have h₂ : (2 : ℝ) ∈ Set.Icc (1 : ℝ) 10000 := by
    constructor <;> norm_num
  
  have h₃ : x ≤ (2 : ℝ) := by
    have h₃₁ : x ≤ 2 := hx.2
    exact h₃₁
  
  have h₄ : (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (1 : ℝ) / Real.sqrt x := by
    have h₄₁ : x ∈ Set.Icc (1 : ℝ) 10000 := h₁
    have h₄₂ : (2 : ℝ) ∈ Set.Icc (1 : ℝ) 10000 := h₂
    have h₄₃ : x ≤ (2 : ℝ) := h₃
    have h₄₄ : AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000) := h_antitone
    have h₄₅ : (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (1 : ℝ) / Real.sqrt x := by
      apply h₄₄
      <;> simp_all [h₄₁, h₄₂]
      <;>
      (try norm_num) <;>
      (try linarith) <;>
      (try
        {
          exact ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
        }) <;>
      (try
        {
          exact ⟨by norm_num, by norm_num⟩
        })
    exact h₄₅
  
  exact h₄

theorem h_int_const_h_integral_le_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / Real.sqrt (2 : ℝ))
      MeasureTheory.volume (1 : ℝ) 2 := by
  have h₁ : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / Real.sqrt (2 : ℝ)) MeasureTheory.volume (1 : ℝ) 2 := by
    -- The function is constant, so we can use the fact that constant functions are interval integrable.
    apply intervalIntegrable_const
  exact h₁

theorem h_le_h_integral_le_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_pointwise :
        ∀ x ∈ Set.Icc (1 : ℝ) 2,
          (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (1 : ℝ) / Real.sqrt x) :
    ∀ x ∈ Set.Icc (1 : ℝ) 2,
      (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (1 : ℝ) / Real.sqrt x := by
  intro x hx
  have h₁ : (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (1 : ℝ) / Real.sqrt x := h_pointwise x hx
  exact h₁

theorem h_integral_le_h_integral_le_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_int_const :
        IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / Real.sqrt (2 : ℝ))
          MeasureTheory.volume (1 : ℝ) 2)
    (h_int_var :
        IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x)
          MeasureTheory.volume (1 : ℝ) 2)
    (h_le :
        ∀ x ∈ Set.Icc (1 : ℝ) 2,
          (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (1 : ℝ) / Real.sqrt x) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2 : ℝ)) ≤
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by
  have h₁ : (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2 : ℝ)) ≤ ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by
    -- Use the fact that the integral of a function less than or equal to another function is less than or equal.
    have h₂ : ∀ x ∈ Set.Icc (1 : ℝ) 2, (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (1 : ℝ) / Real.sqrt x := h_le
    -- Apply the integral comparison lemma.
    have h₃ : (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2 : ℝ)) ≤ ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by
      -- Use the fact that the function (1 / sqrt(2)) is less than or equal to (1 / sqrt(x)) on [1, 2]
      -- and both are interval integrable.
      apply intervalIntegral.integral_mono_on
      <;> simp_all [h_int_const, h_int_var]
      <;>
      (try norm_num) <;>
      (try
        {
          intro x hx
          have h₄ : x ∈ Set.Icc (1 : ℝ) 2 := by exact hx
          have h₅ : (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (1 : ℝ) / Real.sqrt x := h₂ x h₄
          linarith
        }) <;>
      (try
        {
          -- Prove that the functions are continuous on [1, 2]
          apply Continuous.intervalIntegrable
          <;>
          (try continuity) <;>
          (try
            {
              apply Continuous.div
              <;>
              (try continuity) <;>
              (try
                {
                  apply Continuous.sqrt
                  <;>
                  continuity
                }) <;>
              (try
                {
                  intro x
                  norm_num
                  <;>
                  positivity
                })
            })
        })
    exact h₃
  exact h₁

theorem h_int_var_h_integral_le_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x)
      MeasureTheory.volume (1 : ℝ) 2 := by
  have h_main : ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc 1 2) := by
    apply ContinuousOn.div
    · exact continuousOn_const
    · exact Real.continuous_sqrt.comp_continuousOn (continuousOn_id)
    · intro x hx
      have h₁ : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by
        norm_num at hx ⊢
        <;> linarith)
      have h₂ : Real.sqrt x ≠ 0 := by linarith
      exact h₂
  
  have h_interval_integrable : IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume (1 : ℝ) 2 := by
    have h₁ : ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc 1 2) := h_main
    -- Use the fact that a continuous function on a compact interval is interval integrable
    have h₂ : IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume (1 : ℝ) 2 := by
      apply ContinuousOn.intervalIntegrable
      <;> simp_all [h₁]
      <;> norm_num
      <;>
      (try
        {
          -- Show that the function is continuous on the interval [1, 2]
          apply ContinuousOn.div
          · exact continuousOn_const
          · exact Real.continuous_sqrt.comp_continuousOn continuousOn_id
          · intro x hx
            have h₃ : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by
              norm_num at hx ⊢
              <;> linarith)
            have h₄ : Real.sqrt x ≠ 0 := by linarith
            exact h₄
        })
      <;>
      (try
        {
          -- Show that the interval [1, 2] is compact
          exact isCompact_Icc
        })
    exact h₂
  
  exact h_interval_integrable

theorem h_integral_le_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_pointwise :
        ∀ x ∈ Set.Icc (1 : ℝ) 2,
          (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (1 : ℝ) / Real.sqrt x) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2 : ℝ)) ≤
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by
  have h_le :
      ∀ x ∈ Set.Icc (1 : ℝ) 2,
        (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (1 : ℝ) / Real.sqrt x := by
    exact
      h_le_h_integral_le_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
        h_pointwise
  have h_int_const :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / Real.sqrt (2 : ℝ))
        MeasureTheory.volume (1 : ℝ) 2 := by
    exact
      h_int_const_h_integral_le_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  have h_int_var :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x)
        MeasureTheory.volume (1 : ℝ) 2 := by
    exact
      h_int_var_h_integral_le_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  have h_integral_le :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2 : ℝ)) ≤
        ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by
    exact
      h_integral_le_h_integral_le_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
        h_int_const h_int_var h_le
  exact h_integral_le

theorem h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ))
    (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) :
    (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by
  have h_sqrt2_pos : 0 < Real.sqrt (2 : ℝ) :=
    h_sqrt2_pos_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  have h_one_div_sqrt2_pos : 0 < (1 : ℝ) / Real.sqrt (2 : ℝ) :=
    h_one_div_sqrt2_pos_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 h_sqrt2_pos
  have h_pointwise :
      ∀ x ∈ Set.Icc (1 : ℝ) 2,
        (1 : ℝ) / Real.sqrt (2 : ℝ) ≤ (1 : ℝ) / Real.sqrt x :=
    h_pointwise_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 h_antitone
  have h_integral_le :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2 : ℝ)) ≤
        ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x :=
    h_integral_le_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 h_pointwise
  have h_const_integral :
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2 : ℝ) =
        (1 : ℝ) / Real.sqrt (2 : ℝ) :=
    h_const_integral_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  have h_lower_bound :
      (1 : ℝ) / Real.sqrt (2 : ℝ) ≤
        ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x :=
    h_lower_bound_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
      h_const_integral h_integral_le
  have h_pos :
      (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x :=
    h_pos_h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
      h_one_div_sqrt2_pos h_lower_bound
  exact h_pos

theorem h_int_gt_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_int_gt_f2 :
        (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2)) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x >
      (1 : ℝ) / Real.sqrt (2) +
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h₁ : (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x > (1 : ℝ) / Real.sqrt (2) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
    -- Use the given inequality to prove the desired result by adding the same term to both sides.
    have h₂ : (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := h_int_gt_f2
    -- Add the integral from 2 to 10000 to both sides of the inequality.
    have h₃ : (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x > (1 : ℝ) / Real.sqrt (2) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
      linarith
    exact h₃
  exact h₁

theorem h_int_strict_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_int_eq' :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
          (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
            ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
    (h_int_gt :
        (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
          ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x >
        (1 : ℝ) / Real.sqrt (2) +
          ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) :
    (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) >
      (1 : ℝ) / Real.sqrt (2) +
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h₁ : (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
    have h₂ : (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
      rw [h_int_eq']
    rw [h₂]
    -- Use the given inequality to conclude the proof
    linarith
  exact h₁

theorem h_int₂_h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume 2 10000 := by
  -- continuity of the integrand on the closed interval
  have h_cont :
      ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) 10000) := by
    have h_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (2 : ℝ) 10000) :=
      continuousOn_const
    have h_sqrt : ContinuousOn Real.sqrt (Set.Icc (2 : ℝ) 10000) :=
      (Real.continuous_sqrt).continuousOn
    have h_ne : ∀ x ∈ Set.Icc (2 : ℝ) 10000, Real.sqrt x ≠ 0 := by
      intro x hx
      rcases hx with ⟨hx2, _⟩
      have hxpos : (0 : ℝ) < x := by linarith
      have hsqrtpos : 0 < Real.sqrt x := (Real.sqrt_pos.mpr hxpos)
      exact ne_of_gt hsqrtpos
    exact h_const.div h_sqrt h_ne
  have h_le : (2 : ℝ) ≤ 10000 := by norm_num
  exact (ContinuousOn.intervalIntegrable_of_Icc h_le h_cont)

theorem h_int₁_h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume 1 2 := by
  have hcont :
      ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 2) := by
    have h1 :
        ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (1 : ℝ) 2) :=
      ((continuous_const : Continuous fun _ : ℝ => (1 : ℝ))).continuousOn
    have h2 :
        ContinuousOn (fun x : ℝ => Real.sqrt x) (Set.Icc (1 : ℝ) 2) :=
      Real.continuous_sqrt.continuousOn
    have hne : ∀ x ∈ Set.Icc (1 : ℝ) 2, Real.sqrt x ≠ 0 := by
      intro x hx
      have hxpos : (0 : ℝ) < x := by
        have : (1 : ℝ) ≤ x := hx.1
        exact lt_of_lt_of_le (by norm_num) this
      have : 0 < Real.sqrt x := (Real.sqrt_pos).mpr hxpos
      exact ne_of_gt this
    exact h1.div h2 hne
  have hle : (1 : ℝ) ≤ 2 := by norm_num
  exact (ContinuousOn.intervalIntegrable_of_Icc hle hcont)

theorem h_add_h_eq_h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_int1 :
        IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume 1 2)
    (h_int2 :
        IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume 2 10000) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x =
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  simpa using
    (intervalIntegral.integral_add_adjacent_intervals
        (a := (1 : ℝ)) (b := (2 : ℝ)) (c := (10000 : ℝ))
        (f := fun x : ℝ => (1 : ℝ) / Real.sqrt x) (μ := MeasureTheory.volume)
        h_int1 h_int2)

theorem h_int2_h_eq_h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume (2 : ℝ) 10000 :=
by
  have hle : (2 : ℝ) ≤ 10000 := by norm_num
  have h_cont :
      ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (2 : ℝ) 10000) := by
    have h_one : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (2 : ℝ) 10000) :=
      (continuous_const).continuousOn
    have h_sqrt : ContinuousOn (fun x : ℝ => Real.sqrt x) (Set.Icc (2 : ℝ) 10000) :=
      (Real.continuous_sqrt).continuousOn
    have h_ne : ∀ x ∈ Set.Icc (2 : ℝ) 10000, Real.sqrt x ≠ 0 := by
      intro x hx
      have hxpos : (0 : ℝ) < x := by
        have : (2 : ℝ) ≤ x := hx.1
        exact lt_of_lt_of_le (by norm_num) this
      have : 0 < Real.sqrt x := (Real.sqrt_pos).2 hxpos
      exact ne_of_gt this
    exact h_one.div h_sqrt h_ne
  exact (ContinuousOn.intervalIntegrable_of_Icc hle h_cont)

theorem h_int1_h_eq_h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume (1 : ℝ) 2 := by
  -- continuity of the integrand on the closed interval [1,2]
  have hcont :
      ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 2) := by
    have h_one : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (1 : ℝ) 2) :=
      continuousOn_const
    have h_sqrt : ContinuousOn (fun x : ℝ => Real.sqrt x) (Set.Icc (1 : ℝ) 2) :=
      (Real.continuous_sqrt).continuousOn
    have h_ne : ∀ x ∈ Set.Icc (1 : ℝ) 2, Real.sqrt x ≠ 0 := by
      intro x hx
      have hxpos : (0 : ℝ) < x := by
        have : (1 : ℝ) ≤ x := hx.1
        exact lt_of_lt_of_le (by norm_num) this
      have : 0 < Real.sqrt x := (Real.sqrt_pos).2 hxpos
      exact ne_of_gt this
    exact h_one.div h_sqrt h_ne
  -- interval integrability follows from continuity on a closed interval
  exact hcont.intervalIntegrable_of_Icc (by norm_num : (1 : ℝ) ≤ 2)

theorem h_eq_h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ((∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h_int1 :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume (1 : ℝ) 2 :=
    h_int1_h_eq_h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  have h_int2 :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume (2 : ℝ) 10000 :=
    h_int2_h_eq_h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  have h_add :=
    h_add_h_eq_h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 h_int1
      h_int2
  simpa using h_add

theorem h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  simpa using
    (h_eq_h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198).symm

theorem h_result_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_sum_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          (1 : ℝ) / Real.sqrt (2) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
    (h_int_strict :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) >
          (1 : ℝ) / Real.sqrt (2) +
            ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h_main : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
    have h₁ : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤ (1 : ℝ) / Real.sqrt (2) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := h_sum_le
    have h₂ : (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := h_int_strict
    -- Use the fact that if a ≤ b and c > b, then a < c
    have h₃ : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
      linarith
    exact h₃
  exact h_main

theorem h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ))
    (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
    (h_pos :
        (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x)
    (h_int_gt_f2 :
        (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2))
    (h_sum_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          (1 : ℝ) / Real.sqrt (2) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
      ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  -- 1. Equality splitting the integral
  have h_int_eq' :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) =
        (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
          ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
    exact
      h_int_eq'_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  -- 2. Strict inequality after adding the same non‑negative term
  have h_int_gt :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) +
        ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x >
        (1 : ℝ) / Real.sqrt (2) +
          ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
    exact
      h_int_gt_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
        h_int_gt_f2
  -- 3. Transfer the strict inequality to the whole integral
  have h_int_strict :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) >
        (1 : ℝ) / Real.sqrt (2) +
          ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
    exact
      h_int_strict_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
        h_int_eq' h_int_gt
  -- 4. Combine the upper bound for the sum with the strict inequality for the integral
  have h_result :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
    exact
      h_result_h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
        h_sum_le h_int_strict
  exact h_result

theorem h_int_big_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
  (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ))
  (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
  (h_pos :
        (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x)
  (h_sum_strict :
        (1 : ℝ) / Real.sqrt (2) <
          ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) :
    (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by
  have h_main : (1 : ℝ) / Real.sqrt (2) < (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) := by
    have h1 : (1 : ℝ) / Real.sqrt (2) < (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) := h_sum_strict
    have h2 : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤ (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) := h_le
    -- Use the transitivity of inequalities to combine h1 and h2
    have h3 : (1 : ℝ) / Real.sqrt (2) < (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) := by
      calc
        (1 : ℝ) / Real.sqrt (2) < (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) := h1
        _ ≤ (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) := h2
    exact h3
  
  -- The final step is to use the established inequality to conclude the proof.
  have h_final : (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by
    -- Use the fact that if a < b, then b > a.
    have h4 : (1 : ℝ) / Real.sqrt (2) < (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) := h_main
    -- Use the property of real numbers to conclude the proof.
    linarith
  
  exact h_final

theorem h_sum_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
  (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ))
  (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
  (h_pos :
        (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) :
    (1 : ℝ) / Real.sqrt (2) <
      ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by
  have h_main : (1 : ℝ) / Real.sqrt 2 < ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by
    have h₁ : ({2, 3} : Finset ℕ) ⊆ Finset.Icc (2 : ℕ) 10000 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with (rfl | rfl)
      · -- Case x = 2
        norm_num [Finset.mem_Icc]
      · -- Case x = 3
        norm_num [Finset.mem_Icc]
    have h₂ : ∀ (k : ℕ), k ∈ Finset.Icc (2 : ℕ) 10000 → (0 : ℝ) ≤ (1 : ℝ) / Real.sqrt k := by
      intro k hk
      have h₃ : (2 : ℕ) ≤ k := by
        simp [Finset.mem_Icc] at hk
        linarith
      have h₄ : (k : ℝ) ≥ 2 := by
        norm_cast
      have h₅ : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by positivity)
      have h₆ : 0 ≤ (1 : ℝ) / Real.sqrt (k : ℝ) := by positivity
      simpa using h₆
    have h₃ : ∑ k in ({2, 3} : Finset ℕ), (1 : ℝ) / Real.sqrt k ≤ ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg h₁
      intro i hi _
      exact h₂ i hi
    have h₄ : ∑ k in ({2, 3} : Finset ℕ), (1 : ℝ) / Real.sqrt k = (1 : ℝ) / Real.sqrt 2 + (1 : ℝ) / Real.sqrt 3 := by
      norm_num [Finset.sum_pair (show (2 : ℕ) ≠ 3 by norm_num)]
      <;>
      simp [Real.sqrt_eq_iff_sq_eq] <;>
      ring_nf <;>
      norm_num
      <;>
      linarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
    have h₅ : (1 : ℝ) / Real.sqrt 3 > 0 := by
      have h₅₁ : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      positivity
    have h₆ : (1 : ℝ) / Real.sqrt 2 + (1 : ℝ) / Real.sqrt 3 > (1 : ℝ) / Real.sqrt 2 := by
      linarith [h₅]
    have h₇ : ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k > (1 : ℝ) / Real.sqrt 2 := by
      calc
        ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k ≥ ∑ k in ({2, 3} : Finset ℕ), (1 : ℝ) / Real.sqrt k := h₃
        _ = (1 : ℝ) / Real.sqrt 2 + (1 : ℝ) / Real.sqrt 3 := by rw [h₄]
        _ > (1 : ℝ) / Real.sqrt 2 := h₆
    linarith
  exact h_main

theorem h_int_const_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
  ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2) = (1 : ℝ) / Real.sqrt (2) := by
  have h₁ : ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2) = (2 - 1) * ((1 : ℝ) / Real.sqrt (2)) := by
    -- The integral of a constant over an interval [a, b] is the constant times (b - a)
    simp [intervalIntegral.integral_const]
    <;> ring_nf
    <;> norm_num
    <;> field_simp
    <;> ring_nf
    <;> norm_num
  rw [h₁]
  <;> norm_num
  <;> field_simp
  <;> ring_nf
  <;> norm_num

theorem h_diff_nonneg_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_pointwise :
        ∀ x ∈ Set.Icc (1 : ℝ) (2 : ℝ),
          (1 : ℝ) / Real.sqrt (2) ≤ (1 : ℝ) / Real.sqrt x) :
    ∀ x ∈ Set.Icc (1 : ℝ) (2 : ℝ),
      0 ≤ ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) := by
  intro x hx
  have h₁ : (1 : ℝ) / Real.sqrt (2) ≤ (1 : ℝ) / Real.sqrt x := h_pointwise x hx
  -- We need to show that 0 ≤ (1 / sqrt(x)) - (1 / sqrt(2))
  -- This follows directly from the given inequality by rearranging terms.
  have h₂ : 0 ≤ ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) := by
    linarith
  exact h₂

theorem h_pointwise_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
  ∀ x ∈ Set.Icc (1 : ℝ) (2 : ℝ),
    (1 : ℝ) / Real.sqrt (2) ≤ (1 : ℝ) / Real.sqrt x := by
  intro x hx
  have h₁ : 1 ≤ x := by exact hx.1
  have h₂ : x ≤ 2 := by exact hx.2
  have h₃ : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have h₄ : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h₅ : Real.sqrt x ≤ Real.sqrt 2 := by
    apply Real.sqrt_le_sqrt
    linarith
  have h₆ : 0 < Real.sqrt 2 * Real.sqrt x := by positivity
  -- Use the fact that the reciprocal function is decreasing to compare 1/sqrt(2) and 1/sqrt(x)
  have h₇ : (1 : ℝ) / Real.sqrt 2 ≤ (1 : ℝ) / Real.sqrt x := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact h₅
  exact h₇

theorem h_int_sub_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
  ∫ x in (1 : ℝ)..2,
        ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) =
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) -
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2)) := by
  -- integrability of the function x ↦ 1 / sqrt x on [1,2]
  have h_int_f :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume 1 2 := by
    have hcont :
        ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 2) := by
      refine ContinuousOn.div ?_ ?_ ?_
      · exact (continuous_const).continuousOn
      · exact Real.continuous_sqrt.continuousOn
      · intro x hx
        have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx.1
        have hxsqrtpos : (0 : ℝ) < Real.sqrt x := (Real.sqrt_pos.mpr hxpos)
        exact ne_of_gt hxsqrtpos
    exact (ContinuousOn.intervalIntegrable_of_Icc
        (μ := MeasureTheory.volume) (a := (1 : ℝ)) (b := (2 : ℝ)) (by norm_num) hcont)
  -- integrability of the constant function x ↦ 1 / sqrt 2
  have h_int_g :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt (2)) MeasureTheory.volume 1 2 :=
    intervalIntegrable_const
  -- apply linearity of the interval integral
  simpa using
    (intervalIntegral.integral_sub
        (a := (1 : ℝ)) (b := (2 : ℝ))
        (f := fun x : ℝ => (1 : ℝ) / Real.sqrt x)
        (g := fun x : ℝ => (1 : ℝ) / Real.sqrt (2))
        h_int_f h_int_g)

theorem h_int_nonneg_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_diff_nonneg :
        ∀ x ∈ Set.Icc (1 : ℝ) (2 : ℝ),
          0 ≤ ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2)) :
    0 ≤ ∫ x in (1 : ℝ)..2,
          ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) := by
  have h_main : 0 ≤ ∫ x in (1 : ℝ)..2, ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) := by
    have h₁ : ∀ x ∈ Set.Icc (1 : ℝ) (2 : ℝ), 0 ≤ ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) := h_diff_nonneg
    have h₂ : 0 ≤ ∫ x in (1 : ℝ)..2, ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) := by
      -- Use the fact that the integrand is non-negative on [1, 2] to conclude the integral is non-negative.
      have h₃ : ∫ x in (1 : ℝ)..2, ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) = ∫ x in (1 : ℝ)..2, ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) := rfl
      rw [h₃]
      -- Apply the lemma that if a function is non-negative on an interval, its integral is non-negative.
      apply intervalIntegral.integral_nonneg
      <;> simp_all [Set.Icc, le_of_lt]
      <;>
      (try norm_num) <;>
      (try
        {
          intro x hx
          have h₄ : 1 ≤ x := by linarith [hx.1]
          have h₅ : x ≤ 2 := by linarith [hx.2]
          have h₆ : 0 ≤ ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) := h₁ x ⟨h₄, h₅⟩
          linarith
        }) <;>
      (try
        {
          norm_num
          <;>
          (try
            {
              linarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 1, Real.sq_sqrt (show 0 ≤ 2 by norm_num),
                Real.sq_sqrt (show 0 ≤ 1 by norm_num)]
            })
        })
    exact h₂
  exact h_main

theorem h_strict_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_ge :
        (1 : ℝ) / Real.sqrt (2) ≤ ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x)
    (h_ne :
        (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) ≠ (1 : ℝ) / Real.sqrt (2)) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by
  have h_main : (1 : ℝ) / Real.sqrt (2) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by
    by_contra h
    -- Assume the negation of the goal: (1 : ℝ) / Real.sqrt (2) ≥ ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x
    have h₁ : ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x ≤ (1 : ℝ) / Real.sqrt (2) := by
      linarith
    -- From h_ge, we have (1 : ℝ) / Real.sqrt (2) ≤ ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x
    have h₂ : (1 : ℝ) / Real.sqrt (2) ≤ ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := h_ge
    -- Combine the two inequalities to get ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x = (1 : ℝ) / Real.sqrt (2)
    have h₃ : ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x = (1 : ℝ) / Real.sqrt (2) := by
      linarith
    -- This contradicts h_ne
    exact h_ne h₃
  
  -- The main goal follows directly from h_main by rearranging the inequality
  linarith

theorem h_ge_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_int_nonneg :
        0 ≤ ∫ x in (1 : ℝ)..2,
              ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2))
    (h_int_const :
        ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2) = (1 : ℝ) / Real.sqrt (2))
    (h_int_sub :
        ∫ x in (1 : ℝ)..2,
              ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) =
            (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) -
            (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2))) :
    (1 : ℝ) / Real.sqrt (2) ≤ ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by
  have h_main : (1 : ℝ) / Real.sqrt (2) ≤ ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x := by
    have h1 : 0 ≤ (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) - (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2)) := by
      -- Use the given non-negativity of the integral of the difference
      have h2 : 0 ≤ ∫ x in (1 : ℝ)..2, ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) := h_int_nonneg
      -- Use the linearity of the integral to rewrite the integral of the difference as the difference of integrals
      have h3 : ∫ x in (1 : ℝ)..2, ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) = (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) - (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2)) := h_int_sub
      -- Substitute the rewritten form back into the inequality
      linarith
    -- Use the given value of the integral of the constant function
    have h4 : (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2)) = (1 : ℝ) / Real.sqrt (2) := h_int_const
    -- Substitute the value of the integral of the constant function into the inequality
    have h5 : 0 ≤ (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) := by
      linarith
    -- Rearrange the inequality to get the desired result
    linarith
  
  exact h_main

theorem h_sqrt_lt_h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    Real.sqrt (2 : ℝ) < (3 : ℝ) / 2 := by
  have h₁ : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt (by positivity)]
    <;> norm_num
    <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)])
  exact h₁

theorem h_gt_h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_int_eq :
        (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) = (2 : ℝ) * Real.sqrt 2 - 2)
    (h_lt : (1 : ℝ) / Real.sqrt 2 < (2 : ℝ) * Real.sqrt 2 - 2) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt 2 := by
  have h_main : (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt 2 := by
    have h₁ : (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) = (2 : ℝ) * Real.sqrt 2 - 2 := h_int_eq
    rw [h₁]
    -- We need to show that 2 * Real.sqrt 2 - 2 > 1 / Real.sqrt 2
    have h₂ : (2 : ℝ) * Real.sqrt 2 - 2 > (1 : ℝ) / Real.sqrt 2 := by
      -- Use the given inequality to directly conclude the proof
      have h₃ : (1 : ℝ) / Real.sqrt 2 < (2 : ℝ) * Real.sqrt 2 - 2 := h_lt
      linarith
    linarith
  exact h_main

theorem hF_deriv_h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 :
    ∀ x ∈ Set.Icc (1 : ℝ) 2,
      HasDerivAt (fun y => (2 : ℝ) * Real.sqrt y) (1 / Real.sqrt x) x := by
  intro x hx
  have h₁ : HasDerivAt (fun y : ℝ => Real.sqrt y) (1 / (2 * Real.sqrt x)) x := by
    -- Use the known derivative of the square root function
    have h₂ : HasDerivAt (fun y : ℝ => Real.sqrt y) (1 / (2 * Real.sqrt x)) x := by
      convert Real.hasDerivAt_sqrt (by
        -- Prove that x is positive
        have h₃ : 0 < x := by linarith [hx.1]
        linarith) using 1 <;>
      field_simp <;>
      ring
    exact h₂
  -- Multiply by 2 to get the derivative of 2 * sqrt(y)
  have h₂ : HasDerivAt (fun y : ℝ => (2 : ℝ) * Real.sqrt y) (2 * (1 / (2 * Real.sqrt x))) x := by
    convert HasDerivAt.const_mul 2 h₁ using 1 <;> ring
  -- Simplify the expression to match the target derivative
  have h₃ : 2 * (1 / (2 * Real.sqrt x)) = 1 / Real.sqrt x := by
    have h₄ : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith [hx.1])
    field_simp [h₄.ne']
    <;> ring_nf
    <;> field_simp [h₄.ne']
    <;> ring_nf
  -- Conclude the proof by converting the derivative to the target form
  convert h₂ using 1
  <;> rw [h₃]

theorem h_lt_h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_sqrt_lt : Real.sqrt (2 : ℝ) < (3 : ℝ) / 2) :
    (1 : ℝ) / Real.sqrt 2 < (2 : ℝ) * Real.sqrt 2 - 2 := by
  have h₁ : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h₂ : 0 < (3 : ℝ) / 2 := by norm_num
  have h₃ : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h₄ : 0 < (2 : ℝ) * Real.sqrt 2 - 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num),
      Real.sqrt_nonneg 2, h_sqrt_lt]
  have h₅ : (1 : ℝ) / Real.sqrt 2 < (2 : ℝ) * Real.sqrt 2 - 2 := by
    -- Use the fact that sqrt(2) < 3/2 to prove the inequality
    have h₅₁ : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h₅₂ : 0 < (2 : ℝ) * Real.sqrt 2 - 2 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num),
        Real.sqrt_nonneg 2, h_sqrt_lt]
    -- Use the division inequality to compare 1/sqrt(2) and 2*sqrt(2) - 2
    have h₅₃ : (1 : ℝ) / Real.sqrt 2 < (2 : ℝ) * Real.sqrt 2 - 2 := by
      rw [div_lt_iff h₁]
      nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num),
        Real.sqrt_nonneg 2, h_sqrt_lt,
        sq_nonneg (Real.sqrt 2 - 1)]
    exact h₅₃
  exact h₅

theorem h_int_eq_h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (hF_deriv :
      ∀ x ∈ Set.Icc (1 : ℝ) 2,
        HasDerivAt (fun y => (2 : ℝ) * Real.sqrt y) (1 / Real.sqrt x) x) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) = (2 : ℝ) * Real.sqrt 2 - 2 := by
  -- integrability of the integrand
  have h_int :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / Real.sqrt x) MeasureTheory.volume 1 2 := by
    have h_cont :
        ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 2) := by
      have h_sqrt : ContinuousOn Real.sqrt (Set.Icc (1 : ℝ) 2) :=
        (continuous_sqrt).continuousOn
      have h_ne : ∀ x ∈ Set.Icc (1 : ℝ) 2, Real.sqrt x ≠ 0 := by
        intro x hx
        have hxpos : (0 : ℝ) < x := by
          have : (1 : ℝ) ≤ x := hx.1
          exact lt_of_lt_of_le (by norm_num) this
        have : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
        exact ne_of_gt this
      simpa [one_div] using h_sqrt.inv₀ h_ne
    -- turn continuity on `Icc` into continuity on `uIcc` (they coincide here)
    have h_cont' :
        ContinuousOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.uIcc (1 : ℝ) 2) := by
      simpa [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using h_cont
    exact h_cont'.intervalIntegrable
  -- derivative hypothesis on `Set.uIcc`
  have hderiv :
      ∀ x ∈ Set.uIcc (1 : ℝ) 2,
        HasDerivAt (fun y => (2 : ℝ) * Real.sqrt y) (1 / Real.sqrt x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (1 : ℝ) 2 := by
      simpa [Set.uIcc, min_eq_left (by norm_num : (1 : ℝ) ≤ 2),
        max_eq_right (by norm_num : (1 : ℝ) ≤ 2)] using hx
    exact hF_deriv x hx'
  -- apply the fundamental theorem of calculus
  have h_eq :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (1 : ℝ)) (b := 2)
      (f := fun y => (2 : ℝ) * Real.sqrt y)
      (f' := fun x => (1 : ℝ) / Real.sqrt x)
      hderiv h_int
  simpa [Real.sqrt_one, mul_comm, mul_left_comm, mul_assoc] using h_eq

theorem h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_int_big_strict :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2)) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) ≠ (1 : ℝ) / Real.sqrt (2) := by
  have hF_deriv :
      ∀ x ∈ Set.Icc (1 : ℝ) 2,
        HasDerivAt (fun y => (2 : ℝ) * Real.sqrt y) (1 / Real.sqrt x) x :=
    hF_deriv_h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  have h_int_eq :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) = (2 : ℝ) * Real.sqrt 2 - 2 :=
    h_int_eq_h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 hF_deriv
  have h_sqrt_lt :
      Real.sqrt (2 : ℝ) < (3 : ℝ) / 2 :=
    h_sqrt_lt_h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  have h_lt :
      (1 : ℝ) / Real.sqrt 2 < (2 : ℝ) * Real.sqrt 2 - 2 :=
    h_lt_h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 h_sqrt_lt
  have h_gt :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt 2 :=
    h_gt_h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 h_int_eq h_lt
  exact ne_of_gt h_gt

theorem h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
  (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ))
  (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
  (h_pos :
        (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x)
  (h_int_big_strict :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2)) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by
  -- 1.  Pointwise antitone inequality on the interval [1,2].
  have h_pointwise :
      ∀ x ∈ Set.Icc (1 : ℝ) (2 : ℝ),
        (1 : ℝ) / Real.sqrt (2) ≤ (1 : ℝ) / Real.sqrt x :=
    h_pointwise_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  -- 2.  From the pointwise inequality we obtain non‑negativity of the difference.
  have h_diff_nonneg :
      ∀ x ∈ Set.Icc (1 : ℝ) (2 : ℝ),
        0 ≤ ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) :=
    h_diff_nonneg_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
      h_pointwise
  -- 3.  The integral of a non‑negative function on a closed interval is non‑negative.
  have h_int_nonneg :
      0 ≤ ∫ x in (1 : ℝ)..2,
            ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) :=
    h_int_nonneg_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
      h_diff_nonneg
  -- 4.  Compute the integral of the constant function `1/√2` on `[1,2]`.
  have h_int_const :
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2) = (1 : ℝ) / Real.sqrt (2) :=
    h_int_const_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  -- 5.  Rewrite the integral of the difference as the difference of integrals.
  have h_int_sub :
      ∫ x in (1 : ℝ)..2,
          ((1 : ℝ) / Real.sqrt x) - (1 : ℝ) / Real.sqrt (2) =
        (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) -
        (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt (2)) :=
    h_int_sub_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
  -- 6.  From the non‑negativity of the integral of the difference we obtain a
  --     weak inequality between the desired integral and `1/√2`.
  have h_ge :
      (1 : ℝ) / Real.sqrt (2) ≤ ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x :=
    h_ge_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
      h_int_nonneg h_int_const h_int_sub
  -- 7.  The inequality is in fact strict, because the function is not constant
  --     on `[1,2]`.  We prove that the two sides cannot be equal.
  have h_ne :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) ≠ (1 : ℝ) / Real.sqrt (2) :=
    h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
      h_int_big_strict
  -- 8.  Combine the weak inequality and the fact that equality cannot hold
  --     to obtain the desired strict inequality.
  have h_strict :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) :=
    h_strict_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
      h_ge h_ne
  exact h_strict

theorem h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ))
    (h_le :
        (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
          ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x)
    (h_pos :
        (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) := by
  have h_sum_strict :
      (1 : ℝ) / Real.sqrt (2) <
        ∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k :=
    h_sum_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
      h_antitone h_integral_eq h_le h_pos
  have h_int_big_strict :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) :=
    h_int_big_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
      h_antitone h_integral_eq h_le h_pos h_sum_strict
  have h_int_12_strict :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) :=
    h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
      h_antitone h_integral_eq h_le h_pos h_int_big_strict
  exact h_int_12_strict

theorem h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_antitone :
        AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000))
    (h_integral_eq :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ)) :
    (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by
  have h_le :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x :=
    h_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 h_antitone h_integral_eq
  have h_pos :
      (0 : ℝ) < ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x :=
    h_pos_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 h_antitone h_integral_eq h_le
  have h_int_gt_f2 :
      (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2) :=
    h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 h_antitone h_integral_eq h_le h_pos
  have h_sum_le :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        (1 : ℝ) / Real.sqrt (2) + ∫ x in (2 : ℝ)..10000, (1 : ℝ) / Real.sqrt x :=
    h_sum_le_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 h_antitone h_integral_eq h_le h_pos h_int_gt_f2
  have h_strict :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x :=
    h_strict_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 h_antitone h_integral_eq h_le h_pos h_int_gt_f2 h_sum_le
  exact h_strict

theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000) :=
    h_antitone_algebra_sum1onsqrt2to1onsqrt10000lt198
  have h_integral_eq :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ) :=
    h_integral_eq_algebra_sum1onsqrt2to1onsqrt10000lt198
  have h_sum_lt_integral :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x :=
    h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198 h_antitone h_integral_eq
  have h_sum_lt_198 :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) :=
    h_sum_lt_198_algebra_sum1onsqrt2to1onsqrt10000lt198 h_sum_lt_integral h_integral_eq
  simpa using h_sum_lt_198

import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem h2_lt_m_h_ind_induction_nfactltnexpnm1ngt3 (m : ℕ) (hm : (3 : ℕ) ≤ m) : (2 : ℕ) < m := by
  have h : 2 < m := by
    omega
  exact h

theorem hpos_h_ind_induction_nfactltnexpnm1ngt3 (m : ℕ) (hm : (3 : ℕ) ≤ m) : 0 < m := by
  have h : 0 < m := by
    -- Since m ≥ 3, it is trivially greater than 0.
    omega
  exact h

theorem hbase_hle_h_ind_induction_nfactltnexpnm1ngt3 : (3 : ℕ)! ≤ 3 ^ (3 - 1) := by
  norm_num [Nat.factorial]
  <;> decide

theorem hgeneral_hle_h_ind_induction_nfactltnexpnm1ngt3
    (hbase : (3 : ℕ)! ≤ 3 ^ (3 - 1))
    (hstep :
      ∀ k : ℕ,
        3 ≤ k →
        k ! ≤ k ^ (k - 1) →
        (k + 1)! ≤ (k + 1) ^ ((k + 1) - 1)) :
    ∀ n, 3 ≤ n → n ! ≤ n ^ (n - 1) := by
  intro n hn
  have h : ∀ n, 3 ≤ n → n ! ≤ n ^ (n - 1) := by
    intro n hn
    induction' hn with n hn IH
    · -- Base case: n = 3
      norm_num [Nat.factorial] at hbase ⊢
      <;> simp_all
    · -- Inductive step: assume the statement holds for n, prove for n + 1
      have h₁ : (n + 1)! ≤ (n + 1) ^ ((n + 1) - 1) := by
        apply hstep
        · -- Prove 3 ≤ n + 1
          omega
        · -- Use the induction hypothesis
          exact IH
      simpa [Nat.factorial_succ, pow_succ, Nat.mul_assoc] using h₁
  exact h n hn

theorem hpos_hstep_hle_h_ind_induction_nfactltnexpnm1ngt3 (k : ℕ) (hk3 : 3 ≤ k) (hk : k ! ≤ k ^ (k - 1)) :
    0 < k + 1 := by
  have h₁ : 0 < k + 1 := by
    have h₂ : 0 < k := by linarith
    linarith
  exact h₁

theorem hfactorial_hstep_hle_h_ind_induction_nfactltnexpnm1ngt3 (k : ℕ) (hk3 : 3 ≤ k) (hk : k ! ≤ k ^ (k - 1)) :
    (k + 1)! = (k + 1) * k ! := by
  have h₁ : (k + 1)! = (k + 1) * k ! := by
    rw [Nat.factorial_succ]
    <;> ring
  exact h₁

theorem hmult1_hstep_hle_h_ind_induction_nfactltnexpnm1ngt3 (k : ℕ) (hk3 : 3 ≤ k) (hk : k ! ≤ k ^ (k - 1))
    (hpos : 0 < k + 1) :
    (k + 1) * k ! ≤ (k + 1) * k ^ (k - 1) := by
  have h₁ : (k + 1) * k ! ≤ (k + 1) * k ^ (k - 1) := by
    -- Use the fact that multiplication by a positive number preserves the inequality
    have h₂ : k ! ≤ k ^ (k - 1) := hk
    have h₃ : 0 < k + 1 := by linarith
    -- Use the property of multiplication to preserve the inequality
    have h₄ : (k + 1) * k ! ≤ (k + 1) * k ^ (k - 1) := by
      exact Nat.mul_le_mul_left (k + 1) h₂
    exact h₄
  exact h₁

theorem hfinal_hstep_hle_h_ind_induction_nfactltnexpnm1ngt3 (k : ℕ) (hk3 : 3 ≤ k) (hk : k ! ≤ k ^ (k - 1))
    (hfactorial : (k + 1)! = (k + 1) * k !)
    (hmult1 : (k + 1) * k ! ≤ (k + 1) * k ^ (k - 1))
    (hmult2 : (k + 1) * k ^ (k - 1) ≤ (k + 1) ^ k) :
    (k + 1)! ≤ (k + 1) ^ k := by
  have h1 : (k + 1)! ≤ (k + 1) ^ k := by
    calc
      (k + 1)! = (k + 1) * k ! := by rw [hfactorial]
      _ ≤ (k + 1) * k ^ (k - 1) := by
        -- Use the given inequality (k + 1) * k ! ≤ (k + 1) * k ^ (k - 1)
        exact hmult1
      _ ≤ (k + 1) ^ k := by
        -- Use the given inequality (k + 1) * k ^ (k - 1) ≤ (k + 1) ^ k
        exact hmult2
  exact h1

theorem hmult2_hstep_hle_h_ind_induction_nfactltnexpnm1ngt3 (k : ℕ) (hk3 : 3 ≤ k) (hk : k ! ≤ k ^ (k - 1))
    (hpos : 0 < k + 1) (hpow_le : k ^ (k - 1) ≤ (k + 1) ^ (k - 1)) :
    (k + 1) * k ^ (k - 1) ≤ (k + 1) ^ k := by
  have h₁ : (k + 1) * k ^ (k - 1) ≤ (k + 1) * (k + 1) ^ (k - 1) := by
    -- Use the given inequality `k ^ (k - 1) ≤ (k + 1) ^ (k - 1)` to multiply both sides by `(k + 1)`
    have h₂ : k ^ (k - 1) ≤ (k + 1) ^ (k - 1) := hpow_le
    have h₃ : 0 < k + 1 := by linarith
    -- Since `(k + 1)` is positive, multiplying both sides of the inequality by it preserves the inequality
    nlinarith
  
  have h₂ : (k + 1) * (k + 1) ^ (k - 1) = (k + 1) ^ k := by
    -- Simplify the expression `(k + 1) * (k + 1) ^ (k - 1)` to `(k + 1) ^ k`
    have h₃ : (k + 1) * (k + 1) ^ (k - 1) = (k + 1) ^ (1 + (k - 1)) := by
      -- Use the exponent rule `a * a^m = a^(m+1)`
      rw [show (k + 1) * (k + 1) ^ (k - 1) = (k + 1) ^ 1 * (k + 1) ^ (k - 1) by ring]
      rw [← pow_add]
      <;> simp [add_comm]
      <;> ring_nf
      <;> omega
    have h₄ : 1 + (k - 1) = k := by
      -- Simplify the exponent `1 + (k - 1)` to `k`
      have h₅ : k ≥ 3 := hk3
      have h₆ : k - 1 + 1 = k := by
        have h₇ : k - 1 + 1 = k := by
          omega
        exact h₇
      omega
    rw [h₃, h₄]
    <;> ring_nf
  
  -- Combine the inequalities to get the final result
  calc
    (k + 1) * k ^ (k - 1) ≤ (k + 1) * (k + 1) ^ (k - 1) := h₁
    _ = (k + 1) ^ k := by rw [h₂]

theorem hpow_le_hstep_hle_h_ind_induction_nfactltnexpnm1ngt3 (k : ℕ) (hk3 : 3 ≤ k)
    (hk : k ! ≤ k ^ (k - 1)) :
    k ^ (k - 1) ≤ (k + 1) ^ (k - 1) := by
  -- `k ≤ k + 1` is immediate
  have hbase : k ≤ k + 1 := Nat.le_succ k
  -- the exponent `k - 1` is non‑zero because `k ≥ 3`
  have hpos : (k - 1) ≠ 0 := by
    have hk1 : (1 : ℕ) < k := lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hk3
    have : 0 < k - 1 := Nat.sub_pos_of_lt hk1
    exact Nat.ne_of_gt this
  -- monotonicity of `pow` in the base for a non‑zero exponent
  exact ((Nat.pow_le_pow_iff_left (n := k - 1) hpos).2 hbase)

theorem hstep_hle_h_ind_induction_nfactltnexpnm1ngt3 (k : ℕ) (hk3 : 3 ≤ k)
    (hk : k ! ≤ k ^ (k - 1)) :
    (k + 1)! ≤ (k + 1) ^ ((k + 1) - 1) := by
  have hfactorial : (k + 1)! = (k + 1) * k ! :=
    hfactorial_hstep_hle_h_ind_induction_nfactltnexpnm1ngt3 k hk3 hk
  have hpos : 0 < k + 1 :=
    hpos_hstep_hle_h_ind_induction_nfactltnexpnm1ngt3 k hk3 hk
  have hpow_le : k ^ (k - 1) ≤ (k + 1) ^ (k - 1) :=
    hpow_le_hstep_hle_h_ind_induction_nfactltnexpnm1ngt3 k hk3 hk
  have hmult1 : (k + 1) * k ! ≤ (k + 1) * k ^ (k - 1) :=
    hmult1_hstep_hle_h_ind_induction_nfactltnexpnm1ngt3 k hk3 hk hpos
  have hmult2 : (k + 1) * k ^ (k - 1) ≤ (k + 1) ^ k :=
    hmult2_hstep_hle_h_ind_induction_nfactltnexpnm1ngt3 k hk3 hk hpos hpow_le
  have hfinal : (k + 1)! ≤ (k + 1) ^ k :=
    hfinal_hstep_hle_h_ind_induction_nfactltnexpnm1ngt3 k hk3 hk hfactorial hmult1 hmult2
  simpa [Nat.succ_sub_one] using hfinal

theorem hle_h_ind_induction_nfactltnexpnm1ngt3 (m : ℕ) (hm : (3 : ℕ) ≤ m) (hpos : 0 < m) (h2_lt_m : (2 : ℕ) < m) :
    m ! ≤ m ^ (m - 1) := by
  -- base case: 3! ≤ 3^(3‑1)
  have hbase : (3 : ℕ)! ≤ 3 ^ (3 - 1) := by
    exact hbase_hle_h_ind_induction_nfactltnexpnm1ngt3
  -- induction step: from k to k+1
  have hstep :
      ∀ k : ℕ,
        3 ≤ k →
        k ! ≤ k ^ (k - 1) →
        (k + 1)! ≤ (k + 1) ^ ((k + 1) - 1) := by
    intro k hk3 hk
    exact hstep_hle_h_ind_induction_nfactltnexpnm1ngt3 k hk3 hk
  -- general result by induction starting from 3
  have hgeneral : ∀ n, 3 ≤ n → n ! ≤ n ^ (n - 1) := by
    exact hgeneral_hle_h_ind_induction_nfactltnexpnm1ngt3 hbase hstep
  exact hgeneral m hm

theorem hlt_hneq_hlt_h_ind_induction_nfactltnexpnm1ngt3 (m : ℕ) (hm : (3 : ℕ) ≤ m) (hpos : 0 < m) (h2_lt_m : (2 : ℕ) < m)
    (hle : m ! ≤ m ^ (m - 1)) (h_ind : ∀ n, (3 : ℕ) ≤ n → n ! < n ^ (n - 1)) :
    m ! < m ^ (m - 1) := by
  have h_main : m ! < m ^ (m - 1) := by
    have h₁ : m ! < m ^ (m - 1) := h_ind m hm
    exact h₁
  
  exact h_main

theorem h_ind_h_ind_hneq_hlt_h_ind_induction_nfactltnexpnm1ngt3 :
  ∀ m, (3 : ℕ) ≤ m → m ! < m ^ (m - 1) := by
  intro m hm
  rcases Nat.exists_eq_add_of_le hm with ⟨k, rfl⟩
  induction k with
  | zero =>
      norm_num
  | succ k ih =>
      -- rewrite everything in the form (k + ·) to line up with the induction hypothesis
      simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] at *
      have hpos : 0 < k + 4 := Nat.succ_pos _
      have h1 : (k + 4) * (k + 3)! < (k + 4) * (k + 3) ^ (k + 2) :=
        Nat.mul_lt_mul_of_pos_left ih hpos
      have hlt : k + 3 < k + 4 := Nat.lt_succ_self _
      have hpow : (k + 3) ^ (k + 2) < (k + 4) ^ (k + 2) := by
        have hne : (k + 2) ≠ 0 := by
          have : 0 < k + 2 := Nat.succ_pos _
          exact Nat.ne_of_gt this
        exact (Nat.pow_lt_pow_left hlt) hne
      have h2 : (k + 4) * (k + 3) ^ (k + 2) < (k + 4) * (k + 4) ^ (k + 2) :=
        Nat.mul_lt_mul_of_pos_left hpow hpos
      calc
        (k + 4)! = (k + 4) * (k + 3)! := by
          simpa [Nat.factorial_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        _ < (k + 4) * (k + 3) ^ (k + 2) := h1
        _ < (k + 4) * (k + 4) ^ (k + 2) := h2
        _ = (k + 4) ^ (k + 3) := by
          simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem h_ind_hneq_hlt_h_ind_induction_nfactltnexpnm1ngt3 :
  ∀ n, (3 : ℕ) ≤ n → n ! < n ^ (n - 1) := by
  intro n hn
  have h_ind : ∀ m, (3 : ℕ) ≤ m → m ! < m ^ (m - 1) :=
    h_ind_h_ind_hneq_hlt_h_ind_induction_nfactltnexpnm1ngt3
  exact h_ind n hn

theorem hneq_hlt_h_ind_induction_nfactltnexpnm1ngt3 (m : ℕ) (hm : (3 : ℕ) ≤ m) (hpos : 0 < m)
    (h2_lt_m : (2 : ℕ) < m) (hle : m ! ≤ m ^ (m - 1)) : m ! ≠ m ^ (m - 1) := by
  -- auxiliary lemma: for every n ≥ 3 we have n! < n^(n-1)
  have h_ind : ∀ n, (3 : ℕ) ≤ n → n ! < n ^ (n - 1) :=
    h_ind_hneq_hlt_h_ind_induction_nfactltnexpnm1ngt3
  -- obtain the strict inequality for the given m
  have hlt : m ! < m ^ (m - 1) :=
    hlt_hneq_hlt_h_ind_induction_nfactltnexpnm1ngt3 m hm hpos h2_lt_m hle h_ind
  -- strict inequality implies non‑equality
  exact Nat.ne_of_lt hlt

theorem hlt_h_ind_induction_nfactltnexpnm1ngt3 (m : ℕ) (hm : (3 : ℕ) ≤ m) (hpos : 0 < m)
    (h2_lt_m : (2 : ℕ) < m) (hle : m ! ≤ m ^ (m - 1)) : m ! < m ^ (m - 1) := by
  have hneq : m ! ≠ m ^ (m - 1) :=
    hneq_hlt_h_ind_induction_nfactltnexpnm1ngt3 m hm hpos h2_lt_m hle
  exact lt_of_le_of_ne hle hneq

theorem h_ind_induction_nfactltnexpnm1ngt3 :
    ∀ m : ℕ, 3 ≤ m → m ! < m ^ (m - 1) := by
  intro m hm
  -- 0 < m, needed for monotonicity of multiplication
  have hpos : 0 < m := by
    exact hpos_h_ind_induction_nfactltnexpnm1ngt3 m hm
  -- From 3 ≤ m we obtain the strict inequality 2 < m
  have h2_lt_m : (2 : ℕ) < m := by
    exact h2_lt_m_h_ind_induction_nfactltnexpnm1ngt3 m hm
  -- Upper bound: the factorial is at most m raised to the (m‑1)‑st power
  have hle : m ! ≤ m ^ (m - 1) := by
    exact hle_h_ind_induction_nfactltnexpnm1ngt3 m hm hpos h2_lt_m
  -- Because one factor (namely 2) is strictly smaller than m, the inequality is strict
  have hlt : m ! < m ^ (m - 1) := by
    exact hlt_h_ind_induction_nfactltnexpnm1ngt3 m hm hpos h2_lt_m hle
  exact hlt

theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  have h_ind : ∀ m, 3 ≤ m → m ! < m ^ (m - 1) := h_ind_induction_nfactltnexpnm1ngt3
  exact h_ind n h₀

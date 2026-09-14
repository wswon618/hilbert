import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem induction_sumkexp3eqsumksq (n : ℕ) :
    (∑ k in Finset.range n, k ^ 3) = (∑ k in Finset.range n, k) ^ 2 := by
  have h_base : (∑ k in Finset.range 0, k ^ 3) = (∑ k in Finset.range 0, k) ^ 2 := by
    simp [Finset.sum_range_zero]
  
  have h_inductive_step : ∀ (n : ℕ), (∑ k in Finset.range n, k ^ 3) = (∑ k in Finset.range n, k) ^ 2 → (∑ k in Finset.range (n + 1), k ^ 3) = (∑ k in Finset.range (n + 1), k) ^ 2 := by
    intro n ih
    have h1 : (∑ k in Finset.range (n + 1), k ^ 3) = (∑ k in Finset.range n, k ^ 3) + n ^ 3 := by
      rw [Finset.sum_range_succ]
      <;> simp [pow_three]
      <;> ring
    have h2 : (∑ k in Finset.range (n + 1), k) = (∑ k in Finset.range n, k) + n := by
      rw [Finset.sum_range_succ]
      <;> simp [add_comm]
    rw [h1, h2]
    have h3 : (∑ k in Finset.range n, k ^ 3) = (∑ k in Finset.range n, k) ^ 2 := ih
    rw [h3]
    have h4 : (∑ k in Finset.range n, k) = n * (n - 1) / 2 := by
      have h5 : ∑ k in Finset.range n, k = n * (n - 1) / 2 := by
        rw [Finset.sum_range_id]
      rw [h5]
    have h5 : 2 * n * (∑ k in Finset.range n, k) + n ^ 2 = n ^ 3 := by
      rw [h4]
      have h6 : 2 * n * (n * (n - 1) / 2) + n ^ 2 = n ^ 3 := by
        have h7 : n * (n - 1) % 2 = 0 := by
          have h8 : n * (n - 1) % 2 = 0 := by
            have : n % 2 = 0 ∨ n % 2 = 1 := by omega
            rcases this with (h | h) <;>
            simp [h, Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_eq_of_lt]
            <;>
            (try omega) <;>
            (try {
              cases n with
              | zero => simp
              | succ n =>
                simp [Nat.succ_eq_add_one, Nat.mul_mod, Nat.add_mod]
                <;> ring_nf at *
                <;> omega
            })
          exact h8
        have h9 : 2 * n * (n * (n - 1) / 2) = n * (n * (n - 1)) := by
          have h10 : n * (n - 1) / 2 * 2 = n * (n - 1) := by
            have h11 : n * (n - 1) % 2 = 0 := h7
            have h12 : n * (n - 1) / 2 * 2 = n * (n - 1) := by
              have h13 : n * (n - 1) = 2 * (n * (n - 1) / 2) := by
                omega
              omega
            exact h12
          have h14 : 2 * n * (n * (n - 1) / 2) = n * (n * (n - 1)) := by
            calc
              2 * n * (n * (n - 1) / 2) = n * (2 * (n * (n - 1) / 2)) := by ring
              _ = n * (n * (n - 1)) := by
                have h15 : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
                  omega
                rw [h15]
                <;> ring
              _ = n * (n * (n - 1)) := by ring
          exact h14
        calc
          2 * n * (n * (n - 1) / 2) + n ^ 2 = n * (n * (n - 1)) + n ^ 2 := by rw [h9]
          _ = n ^ 2 * (n - 1) + n ^ 2 := by
            ring_nf
            <;>
            (try omega)
          _ = n ^ 3 := by
            cases n with
            | zero => simp
            | succ n =>
              simp [Nat.succ_eq_add_one, pow_succ, mul_add, mul_one, add_mul, one_mul]
              <;> ring_nf at *
              <;> omega
      omega
    have h6 : ((∑ k in Finset.range n, k) + n) ^ 2 = (∑ k in Finset.range n, k) ^ 2 + 2 * n * (∑ k in Finset.range n, k) + n ^ 2 := by
      calc
        ((∑ k in Finset.range n, k) + n) ^ 2 = (∑ k in Finset.range n, k) ^ 2 + 2 * n * (∑ k in Finset.range n, k) + n ^ 2 := by
          ring_nf
          <;>
          (try omega)
        _ = (∑ k in Finset.range n, k) ^ 2 + 2 * n * (∑ k in Finset.range n, k) + n ^ 2 := by rfl
    have h7 : (∑ k in Finset.range n, k) ^ 2 + n ^ 3 = (∑ k in Finset.range n, k) ^ 2 + (2 * n * (∑ k in Finset.range n, k) + n ^ 2) := by
      have h8 : n ^ 3 = 2 * n * (∑ k in Finset.range n, k) + n ^ 2 := by
        omega
      linarith
    nlinarith
  
  have h_main : (∑ k in Finset.range n, k ^ 3) = (∑ k in Finset.range n, k) ^ 2 := by
    have h₁ : ∀ n : ℕ, (∑ k in Finset.range n, k ^ 3) = (∑ k in Finset.range n, k) ^ 2 := by
      intro n
      induction n with
      | zero => simp [h_base]
      | succ n ih =>
        apply h_inductive_step
        exact ih
    apply h₁
  
  apply h_main

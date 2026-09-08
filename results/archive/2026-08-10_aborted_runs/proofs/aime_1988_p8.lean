import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem aime_1988_p8 (f : ℕ → ℕ → ℝ) (h₀ : ∀ x, 0 < x → f x x = x)
    (h₁ : ∀ x y, 0 < x ∧ 0 < y → f x y = f y x)
    (h₂ : ∀ x y, 0 < x ∧ 0 < y → (↑x + ↑y) * f x y = y * f x (x + y)) : f 14 52 = 364 := by
  have h_f24 : f 2 4 = 4 := by
    have h₃ : (2 : ℝ) + 2 = 4 := by norm_num
    have h₄ : (2 : ℝ) > 0 := by norm_num
    have h₅ : (2 : ℕ) > 0 := by norm_num
    have h₆ : (2 : ℕ) + 2 = 4 := by norm_num
    have h₇ : ( (2 : ℕ) + (2 : ℕ) : ℝ) * f 2 2 = (2 : ℕ) * f 2 (2 + 2) := by
      have h₇₁ : (0 : ℕ) < 2 ∧ (0 : ℕ) < 2 := by
        exact ⟨by norm_num, by norm_num⟩
      have h₇₂ := h₂ 2 2 h₇₁
      norm_cast at h₇₂ ⊢
      <;> simp [h₆] at h₇₂ ⊢ <;>
        (try ring_nf at h₇₂ ⊢) <;>
        (try norm_num at h₇₂ ⊢) <;>
        (try linarith) <;>
        (try simp_all [h₀]) <;>
        (try ring_nf at h₇₂ ⊢) <;>
        (try norm_num at h₇₂ ⊢) <;>
        (try linarith)
      <;>
      (try simp_all [h₀]) <;>
      (try ring_nf at h₇₂ ⊢) <;>
      (try norm_num at h₇₂ ⊢) <;>
      (try linarith)
      <;>
      (try simp_all [h₀]) <;>
      (try ring_nf at h₇₂ ⊢) <;>
      (try norm_num at h₇₂ ⊢) <;>
      (try linarith)
    have h₈ : f 2 2 = (2 : ℝ) := by
      have h₈₁ : (0 : ℕ) < 2 := by norm_num
      have h₈₂ := h₀ 2 h₈₁
      norm_num at h₈₂ ⊢
      <;> simp_all
      <;> norm_num
      <;> linarith
    have h₉ : ( (2 : ℕ) + (2 : ℕ) : ℝ) * f 2 2 = (2 : ℕ) * f 2 (2 + 2) := by
      exact h₇
    have h₁₀ : ( (2 : ℕ) + (2 : ℕ) : ℝ) * f 2 2 = (4 : ℝ) * f 2 2 := by
      norm_num
      <;> ring_nf
      <;> simp_all
      <;> norm_num
      <;> linarith
    have h₁₁ : (2 : ℕ) * f 2 (2 + 2) = (2 : ℝ) * f 2 4 := by
      norm_num [h₆]
      <;> ring_nf
      <;> simp_all
      <;> norm_num
      <;> linarith
    have h₁₂ : (4 : ℝ) * f 2 2 = (2 : ℝ) * f 2 4 := by
      linarith
    have h₁₃ : (4 : ℝ) * (2 : ℝ) = (2 : ℝ) * f 2 4 := by
      rw [h₈] at h₁₂
      linarith
    have h₁₄ : (2 : ℝ) * f 2 4 = 8 := by
      linarith
    have h₁₅ : f 2 4 = 4 := by
      linarith
    exact_mod_cast h₁₅
  
  have h_f42 : f 4 2 = 4 := by
    have h₃ : f 4 2 = f 2 4 := by
      have h₄ : (0 : ℕ) < 4 ∧ (0 : ℕ) < 2 := by
        exact ⟨by norm_num, by norm_num⟩
      have h₅ := h₁ 4 2 h₄
      linarith
    rw [h₃]
    exact_mod_cast h_f24
  
  have h_f46 : f 4 6 = 12 := by
    have h₃ : (4 : ℝ) + 2 = 6 := by norm_num
    have h₄ : (4 : ℕ) > 0 := by norm_num
    have h₅ : (2 : ℕ) > 0 := by norm_num
    have h₆ : (0 : ℕ) < 4 ∧ (0 : ℕ) < 2 := by
      exact ⟨by norm_num, by norm_num⟩
    have h₇ : ( (4 : ℕ) + (2 : ℕ) : ℝ) * f 4 2 = (2 : ℕ) * f 4 (4 + 2) := by
      have h₇₁ := h₂ 4 2 ⟨by norm_num, by norm_num⟩
      norm_cast at h₇₁ ⊢
      <;> simp [add_assoc] at h₇₁ ⊢ <;>
        (try ring_nf at h₇₁ ⊢) <;>
        (try norm_num at h₇₁ ⊢) <;>
        (try linarith) <;>
        (try simp_all [h₀]) <;>
        (try ring_nf at h₇₁ ⊢) <;>
        (try norm_num at h₇₁ ⊢) <;>
        (try linarith)
      <;>
      (try simp_all [h₀]) <;>
      (try ring_nf at h₇₁ ⊢) <;>
      (try norm_num at h₇₁ ⊢) <;>
      (try linarith)
      <;>
      (try simp_all [h₀]) <;>
      (try ring_nf at h₇₁ ⊢) <;>
      (try norm_num at h₇₁ ⊢) <;>
      (try linarith)
    have h₈ : ( (4 : ℕ) + (2 : ℕ) : ℝ) * f 4 2 = (6 : ℝ) * f 4 2 := by
      norm_num
      <;> ring_nf
      <;> simp_all
      <;> norm_num
      <;> linarith
    have h₉ : (2 : ℕ) * f 4 (4 + 2) = (2 : ℝ) * f 4 6 := by
      norm_num [add_assoc]
      <;> ring_nf
      <;> simp_all
      <;> norm_num
      <;> linarith
    have h₁₀ : (6 : ℝ) * f 4 2 = (2 : ℝ) * f 4 6 := by
      linarith
    have h₁₁ : (6 : ℝ) * (4 : ℝ) = (2 : ℝ) * f 4 6 := by
      have h₁₂ : f 4 2 = (4 : ℝ) := by
        exact_mod_cast h_f42
      rw [h₁₂] at h₁₀
      linarith
    have h₁₂ : (2 : ℝ) * f 4 6 = 24 := by
      linarith
    have h₁₃ : f 4 6 = 12 := by
      linarith
    exact_mod_cast h₁₃
  
  have h_f410 : f 4 10 = 20 := by
    have h₃ : (4 : ℝ) + 6 = 10 := by norm_num
    have h₄ : (4 : ℕ) > 0 := by norm_num
    have h₅ : (6 : ℕ) > 0 := by norm_num
    have h₆ : (0 : ℕ) < 4 ∧ (0 : ℕ) < 6 := by
      exact ⟨by norm_num, by norm_num⟩
    have h₇ : ( (4 : ℕ) + (6 : ℕ) : ℝ) * f 4 6 = (6 : ℕ) * f 4 (4 + 6) := by
      have h₇₁ := h₂ 4 6 ⟨by norm_num, by norm_num⟩
      norm_cast at h₇₁ ⊢
      <;> simp [add_assoc] at h₇₁ ⊢ <;>
        (try ring_nf at h₇₁ ⊢) <;>
        (try norm_num at h₇₁ ⊢) <;>
        (try linarith) <;>
        (try simp_all [h₀]) <;>
        (try ring_nf at h₇₁ ⊢) <;>
        (try norm_num at h₇₁ ⊢) <;>
        (try linarith)
      <;>
      (try simp_all [h₀]) <;>
      (try ring_nf at h₇₁ ⊢) <;>
      (try norm_num at h₇₁ ⊢) <;>
      (try linarith)
      <;>
      (try simp_all [h₀]) <;>
      (try ring_nf at h₇₁ ⊢) <;>
      (try norm_num at h₇₁ ⊢) <;>
      (try linarith)
    have h₈ : ( (4 : ℕ) + (6 : ℕ) : ℝ) * f 4 6 = (10 : ℝ) * f 4 6 := by
      norm_num
      <;> ring_nf
      <;> simp_all
      <;> norm_num
      <;> linarith
    have h₉ : (6 : ℕ) * f 4 (4 + 6) = (6 : ℝ) * f 4 10 := by
      norm_num [add_assoc]
      <;> ring_nf
      <;> simp_all
      <;> norm_num
      <;> linarith
    have h₁₀ : (10 : ℝ) * f 4 6 = (6 : ℝ) * f 4 10 := by
      linarith
    have h₁₁ : (10 : ℝ) * (12 : ℝ) = (6 : ℝ) * f 4 10 := by
      have h₁₂ : f 4 6 = (12 : ℝ) := by
        exact_mod_cast h_f46
      rw [h₁₂] at h₁₀
      linarith
    have h₁₂ : (6 : ℝ) * f 4 10 = 120 := by
      linarith
    have h₁₃ : f 4 10 = 20 := by
      linarith
    exact_mod_cast h₁₃
  
  have h_f104 : f 10 4 = 20 := by
    have h₃ : f 10 4 = f 4 10 := by
      have h₄ : (0 : ℕ) < 10 ∧ (0 : ℕ) < 4 := by
        exact ⟨by norm_num, by norm_num⟩
      have h₅ := h₁ 10 4 h₄
      linarith
    rw [h₃]
    exact_mod_cast h_f410
  
  have h_f1014 : f 10 14 = 70 := by
    have h₃ : (10 : ℝ) + 4 = 14 := by norm_num
    have h₄ : (10 : ℕ) > 0 := by norm_num
    have h₅ : (4 : ℕ) > 0 := by norm_num
    have h₆ : (0 : ℕ) < 10 ∧ (0 : ℕ) < 4 := by
      exact ⟨by norm_num, by norm_num⟩
    have h₇ : ( (10 : ℕ) + (4 : ℕ) : ℝ) * f 10 4 = (4 : ℕ) * f 10 (10 + 4) := by
      have h₇₁ := h₂ 10 4 ⟨by norm_num, by norm_num⟩
      norm_cast at h₇₁ ⊢
      <;> simp [add_assoc] at h₇₁ ⊢ <;>
        (try ring_nf at h₇₁ ⊢) <;>
        (try norm_num at h₇₁ ⊢) <;>
        (try linarith) <;>
        (try simp_all [h₀]) <;>
        (try ring_nf at h₇₁ ⊢) <;>
        (try norm_num at h₇₁ ⊢) <;>
        (try linarith)
      <;>
      (try simp_all [h₀]) <;>
      (try ring_nf at h₇₁ ⊢) <;>
      (try norm_num at h₇₁ ⊢) <;>
      (try linarith)
      <;>
      (try simp_all [h₀]) <;>
      (try ring_nf at h₇₁ ⊢) <;>
      (try norm_num at h₇₁ ⊢) <;>
      (try linarith)
    have h₈ : ( (10 : ℕ) + (4 : ℕ) : ℝ) * f 10 4 = (14 : ℝ) * f 10 4 := by
      norm_num
      <;> ring_nf
      <;> simp_all
      <;> norm_num
      <;> linarith
    have h₉ : (4 : ℕ) * f 10 (10 + 4) = (4 : ℝ) * f 10 14 := by
      norm_num [add_assoc]
      <;> ring_nf
      <;> simp_all
      <;> norm_num
      <;> linarith
    have h₁₀ : (14 : ℝ) * f 10 4 = (4 : ℝ) * f 10 14 := by
      linarith
    have h₁₁ : (14 : ℝ) * (20 : ℝ) = (4 : ℝ) * f 10 14 := by
      have h₁₂ : f 10 4 = (20 : ℝ) := by
        exact_mod_cast h_f104
      rw [h₁₂] at h₁₀
      linarith
    have h₁₂ : (4 : ℝ) * f 10 14 = 280 := by
      linarith
    have h₁₃ : f 10 14 = 70 := by
      linarith
    exact_mod_cast h₁₃
  
  have h_f1410 : f 14 10 = 70 := by
    have h₃ : f 14 10 = f 10 14 := by
      have h₄ : (0 : ℕ) < 14 ∧ (0 : ℕ) < 10 := by
        exact ⟨by norm_num, by norm_num⟩
      have h₅ := h₁ 14 10 h₄
      linarith
    rw [h₃]
    exact_mod_cast h_f1014
  
  have h_f1424 : f 14 24 = 168 := by
    have h₃ : (14 : ℝ) + 10 = 24 := by norm_num
    have h₄ : (14 : ℕ) > 0 := by norm_num
    have h₅ : (10 : ℕ) > 0 := by norm_num
    have h₆ : (0 : ℕ) < 14 ∧ (0 : ℕ) < 10 := by
      exact ⟨by norm_num, by norm_num⟩
    have h₇ : ( (14 : ℕ) + (10 : ℕ) : ℝ) * f 14 10 = (10 : ℕ) * f 14 (14 + 10) := by
      have h₇₁ := h₂ 14 10 ⟨by norm_num, by norm_num⟩
      norm_cast at h₇₁ ⊢
      <;> simp [add_assoc] at h₇₁ ⊢ <;>
        (try ring_nf at h₇₁ ⊢) <;>
        (try norm_num at h₇₁ ⊢) <;>
        (try linarith) <;>
        (try simp_all [h₀]) <;>
        (try ring_nf at h₇₁ ⊢) <;>
        (try norm_num at h₇₁ ⊢) <;>
        (try linarith)
      <;>
      (try simp_all [h₀]) <;>
      (try ring_nf at h₇₁ ⊢) <;>
      (try norm_num at h₇₁ ⊢) <;>
      (try linarith)
      <;>
      (try simp_all [h₀]) <;>
      (try ring_nf at h₇₁ ⊢) <;>
      (try norm_num at h₇₁ ⊢) <;>
      (try linarith)
    have h₈ : ( (14 : ℕ) + (10 : ℕ) : ℝ) * f 14 10 = (24 : ℝ) * f 14 10 := by
      norm_num
      <;> ring_nf
      <;> simp_all
      <;> norm_num
      <;> linarith
    have h₉ : (10 : ℕ) * f 14 (14 + 10) = (10 : ℝ) * f 14 24 := by
      norm_num [add_assoc]
      <;> ring_nf
      <;> simp_all
      <;> norm_num
      <;> linarith
    have h₁₀ : (24 : ℝ) * f 14 10 = (10 : ℝ) * f 14 24 := by
      linarith
    have h₁₁ : (24 : ℝ) * (70 : ℝ) = (10 : ℝ) * f 14 24 := by
      have h₁₂ : f 14 10 = (70 : ℝ) := by
        exact_mod_cast h_f1410
      rw [h₁₂] at h₁₀
      linarith
    have h₁₂ : (10 : ℝ) * f 14 24 = 1680 := by
      linarith
    have h₁₃ : f 14 24 = 168 := by
      linarith
    exact_mod_cast h₁₃
  
  have h_f1438 : f 14 38 = 266 := by
    have h₃ : (14 : ℝ) + 24 = 38 := by norm_num
    have h₄ : (14 : ℕ) > 0 := by norm_num
    have h₅ : (24 : ℕ) > 0 := by norm_num
    have h₆ : (0 : ℕ) < 14 ∧ (0 : ℕ) < 24 := by
      exact ⟨by norm_num, by norm_num⟩
    have h₇ : ( (14 : ℕ) + (24 : ℕ) : ℝ) * f 14 24 = (24 : ℕ) * f 14 (14 + 24) := by
      have h₇₁ := h₂ 14 24 ⟨by norm_num, by norm_num⟩
      norm_cast at h₇₁ ⊢
      <;> simp [add_assoc] at h₇₁ ⊢ <;>
        (try ring_nf at h₇₁ ⊢) <;>
        (try norm_num at h₇₁ ⊢) <;>
        (try linarith) <;>
        (try simp_all [h₀]) <;>
        (try ring_nf at h₇₁ ⊢) <;>
        (try norm_num at h₇₁ ⊢) <;>
        (try linarith)
      <;>
      (try simp_all [h₀]) <;>
      (try ring_nf at h₇₁ ⊢) <;>
      (try norm_num at h₇₁ ⊢) <;>
      (try linarith)
      <;>
      (try simp_all [h₀]) <;>
      (try ring_nf at h₇₁ ⊢) <;>
      (try norm_num at h₇₁ ⊢) <;>
      (try linarith)
    have h₈ : ( (14 : ℕ) + (24 : ℕ) : ℝ) * f 14 24 = (38 : ℝ) * f 14 24 := by
      norm_num
      <;> ring_nf
      <;> simp_all
      <;> norm_num
      <;> linarith
    have h₉ : (24 : ℕ) * f 14 (14 + 24) = (24 : ℝ) * f 14 38 := by
      norm_num [add_assoc]
      <;> ring_nf
      <;> simp_all
      <;> norm_num
      <;> linarith
    have h₁₀ : (38 : ℝ) * f 14 24 = (24 : ℝ) * f 14 38 := by
      linarith
    have h₁₁ : (38 : ℝ) * (168 : ℝ) = (24 : ℝ) * f 14 38 := by
      have h₁₂ : f 14 24 = (168 : ℝ) := by
        exact_mod_cast h_f1424
      rw [h₁₂] at h₁₀
      linarith
    have h₁₂ : (24 : ℝ) * f 14 38 = 6384 := by
      linarith
    have h₁₃ : f 14 38 = 266 := by
      linarith
    exact_mod_cast h₁₃
  
  have h_f1452 : f 14 52 = 364 := by
    have h₃ : (14 : ℝ) + 38 = 52 := by norm_num
    have h₄ : (14 : ℕ) > 0 := by norm_num
    have h₅ : (38 : ℕ) > 0 := by norm_num
    have h₆ : (0 : ℕ) < 14 ∧ (0 : ℕ) < 38 := by
      exact ⟨by norm_num, by norm_num⟩
    have h₇ : ( (14 : ℕ) + (38 : ℕ) : ℝ) * f 14 38 = (38 : ℕ) * f 14 (14 + 38) := by
      have h₇₁ := h₂ 14 38 ⟨by norm_num, by norm_num⟩
      norm_cast at h₇₁ ⊢
      <;> simp [add_assoc] at h₇₁ ⊢ <;>
        (try ring_nf at h₇₁ ⊢) <;>
        (try norm_num at h₇₁ ⊢) <;>
        (try linarith) <;>
        (try simp_all [h₀]) <;>
        (try ring_nf at h₇₁ ⊢) <;>
        (try norm_num at h₇₁ ⊢) <;>
        (try linarith)
      <;>
      (try simp_all [h₀]) <;>
      (try ring_nf at h₇₁ ⊢) <;>
      (try norm_num at h₇₁ ⊢) <;>
      (try linarith)
      <;>
      (try simp_all [h₀]) <;>
      (try ring_nf at h₇₁ ⊢) <;>
      (try norm_num at h₇₁ ⊢) <;>
      (try linarith)
    have h₈ : ( (14 : ℕ) + (38 : ℕ) : ℝ) * f 14 38 = (52 : ℝ) * f 14 38 := by
      norm_num
      <;> ring_nf
      <;> simp_all
      <;> norm_num
      <;> linarith
    have h₉ : (38 : ℕ) * f 14 (14 + 38) = (38 : ℝ) * f 14 52 := by
      norm_num [add_assoc]
      <;> ring_nf
      <;> simp_all
      <;> norm_num
      <;> linarith
    have h₁₀ : (52 : ℝ) * f 14 38 = (38 : ℝ) * f 14 52 := by
      linarith
    have h₁₁ : (52 : ℝ) * (266 : ℝ) = (38 : ℝ) * f 14 52 := by
      have h₁₂ : f 14 38 = (266 : ℝ) := by
        exact_mod_cast h_f1438
      rw [h₁₂] at h₁₀
      linarith
    have h₁₂ : (38 : ℝ) * f 14 52 = 13832 := by
      linarith
    have h₁₃ : f 14 52 = 364 := by
      linarith
    exact_mod_cast h₁₃
  
  exact h_f1452

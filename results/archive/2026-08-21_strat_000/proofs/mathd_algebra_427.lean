import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem mathd_algebra_427 (x y z : ℝ) (h₀ : 3 * x + y = 17) (h₁ : 5 * y + z = 14)
    (h₂ : 3 * x + 5 * z = 41) : x + y + z = 12 := by
  have h₃ : x + y + z = 12 := by
    -- We need to find x + y + z. We can use the given equations to eliminate variables.
    -- First, subtract the first equation from the second to eliminate x:
    -- (5y + z) - (3x + y) = 14 - 17 => 4y + z - 3x = -3
    -- But we also have 3x + 5z = 41. We can add these two results to eliminate x:
    -- (4y + z - 3x) + (3x + 5z) = -3 + 41 => 4y + 6z = 38 => 2y + 3z = 19
    -- Now we have 2y + 3z = 19 and 5y + z = 14. We can solve for y and z.
    -- Multiply the second equation by 3: 15y + 3z = 42
    -- Subtract the first new equation: (15y + 3z) - (2y + 3z) = 42 - 19 => 13y = 23 => y = 23/13
    -- But let's try a better approach to avoid fractions.
    
    -- Alternatively, we can express x from the first equation and substitute into the third equation.
    -- From 3x + y = 17 => 3x = 17 - y => x = (17 - y)/3
    -- Substitute into 3x + 5z = 41: (17 - y) + 5z = 41 => -y + 5z = 24 => 5z - y = 24
    -- Now we have 5z - y = 24 and 5y + z = 14. Solve for y and z.
    -- Multiply the first by 5: 25z - 5y = 120
    -- Add to the second: (25z - 5y) + (5y + z) = 120 + 14 => 26z = 134 => z = 134/26 = 67/13
    -- But again, fractions appear. Let's try another approach.
    
    -- A better approach is to add all three equations and then subtract multiples to eliminate variables.
    -- Add all three equations:
    -- (3x + y) + (5y + z) + (3x + 5z) = 17 + 14 + 41 => 6x + 6y + 6z = 72 => x + y + z = 12
    -- This directly gives the desired result without needing to solve for individual variables.
    have h₃ : 6 * x + 6 * y + 6 * z = 72 := by
      -- Add the three original equations:
      have h₃₁ : (3 * x + y) + (5 * y + z) + (3 * x + 5 * z) = 17 + 14 + 41 := by
        linarith
      -- Simplify the left and right sides:
      ring_nf at h₃₁ ⊢
      linarith
    -- Divide both sides by 6 to get x + y + z = 12:
    have h₄ : x + y + z = 12 := by
      linarith
    exact h₄
  exact h₃

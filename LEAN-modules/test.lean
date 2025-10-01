import Mathlib

example (x y z : ℚ) (h1 : 2*x < 3*y)
        (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0) : False := by
  linarith

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ {α} [AddCommGroup α] [LinearOrder α] (x : α), 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

example (x y ε : ℝ) (h_eps_pos : 0 < ε) (h_eps_le_one : ε ≤ 1) (hx : |x| < ε) (hy : |y| < ε) :
    |x * y| < ε := by
  -- We can use a `calc` block to show the chain of inequalities.
  calc
    |x * y| = |x| * |y|       := by rw [abs_mul]
    _       < ε * ε         := by gcongr
    _       ≤ ε * 1         := by gcongr
    _       = ε             := by ring

example {a b x c d : ℝ} (h1 : a + 1 ≤ b + 1) (h2 : c + 2 ≤ d + 2) :
    x^2 * a + c ≤ x^2 * b + d := by
  gcongr
  · linarith
  · linarith

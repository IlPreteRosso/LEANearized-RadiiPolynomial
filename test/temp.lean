import LeanCert
import RadiiPolynomial.TaylorODE_Direct.Example_7_7

/-!
# Prototype: Direct Y₀ bound via ℚ bridge

Goal: prove Y₀_bound ≤ 9/500 without finsum_expand!/vec_simp!.
Strategy: unfold everything to raw rationals, apply of_point_interval, fast_bound.
-/

open LeanCert.Core LeanCert.Engine Example_7_7

namespace Y0Proto

noncomputable def ā₀ : ℝ := 5774/10000
noncomputable def ā₁ : ℝ := 8660/10000
noncomputable def ā₂ : ℝ := -6495/10000
noncomputable def lam0 : ℝ := 1/3
noncomputable def ν_val : PosReal := ⟨1/4, by norm_num⟩

lemma ā₀_ne_zero : ā₀ ≠ 0 := by unfold ā₀; norm_num

noncomputable def sol : ApproxSolution 2 where
  aBar_fin := ![ā₀, ā₁, ā₂]
  aBar_zero_ne := ā₀_ne_zero

noncomputable def A_diag : ℝ := 8660/10000
noncomputable def A_sub1 : ℝ := -12990/10000
noncomputable def A_sub2 : ℝ := 29240/10000

noncomputable def A_mat : Matrix (Fin 3) (Fin 3) ℝ :=
  !![A_diag, 0, 0; A_sub1, A_diag, 0; A_sub2, A_sub1, A_diag]

/-- Helper: Transform `e ≤ c` goal into interval form for fast_bound. -/
private lemma of_point_interval {e c : ℝ} {q : ℚ} (hqc : (q : ℝ) = c)
    (h : ∀ x ∈ Set.Icc (0:ℝ) 0, e ≤ q) : e ≤ c := by
  rw [← hqc]; exact h 0 ⟨le_refl _, le_refl _⟩

/-! ## Approach: Unfold everything, then fast_bound

The key observation: Y₀_bound with N=2 and all rational data is just a
rational expression. We can unfold all definitions to expose it, then let
fast_bound handle the inequality. The O(N) cost was in finsum_expand!
(which creates N proof terms). Instead, we unfold directly and let
norm_num/fast_bound handle the whole expression at once. -/

-- Step 1: Bridge F_fin to ℚ values (precomputed)
-- F[0] = ā₀² - 1/3, F[1] = 2ā₀ā₁ - 1, F[2] = 2ā₀ā₂ + ā₁²
-- These are rational numbers.

-- Step 2: Bridge A*F to ℚ values (precomputed inner products)
-- (A*F)[0] = A_diag * F[0]
-- (A*F)[1] = A_sub1 * F[0] + A_diag * F[1]
-- (A*F)[2] = A_sub2 * F[0] + A_sub1 * F[1] + A_diag * F[2]

-- Step 3: Y₀ = ∑ₙ |(A*F)[n]| * ν^n + tail

-- Instead of all that, let's try: bridge Y₀_bound = q for some ℚ q.
-- The proof: unfold all defs to rationals, native_decide or norm_num.

-- Actually, let me try the simplest possible approach: just unfold everything
-- without finsum_expand, use simp + norm_num

-- Precompute: Y₀_bound as a single ℚ array to be summed
-- Y₀ finite part terms (precomputed):
-- term n = |∑ⱼ A[n,j]*F[j]| * ν^n
-- All are rational.

-- The cleanest approach: precompute the ℚ array, provide evaluator, use finsum_bound.
-- But Y₀_bound has TWO sums. Let's handle each separately.

-- Approach: Prove Y₀_bound = finPart + tailPart, bound each separately.

-- Actually, let's just try the brute force: unfold and norm_num
-- The issue with the old approach was finsum_expand! creating O(N) proof terms.
-- If we use native_decide for the finite sum expansion, it might be O(1).

-- Let's try: express F_fin as a ℚ vector, A*F as a ℚ vector, then bound.

-- F_fin as ℚ data
def F_data : Array ℚ := #[
  (5774/10000)^2 - 1/3,                              -- F[0] = ā₀² - lam0
  2 * (5774/10000) * (8660/10000) - 1,                -- F[1] = 2ā₀ā₁ - 1
  2 * (5774/10000) * (-6495/10000) + (8660/10000)^2   -- F[2] = 2ā₀ā₂ + ā₁²
]

-- A*F as ℚ data (matrix-vector product)
def AF_data : Array ℚ := #[
  (8660/10000) * F_data[0]!,
  (-12990/10000) * F_data[0]! + (8660/10000) * F_data[1]!,
  (29240/10000) * F_data[0]! + (-12990/10000) * F_data[1]! + (8660/10000) * F_data[2]!
]

-- Y₀ finite part: ∑ₙ |AF[n]| * ν^n
-- Y₀ tail part: (1/(2|ā₀|)) * ∑ₙ₌₃⁴ (convolution) * ν^n
-- For n=3: conv = 2*|ā₁|*|ā₂|, for n=4: conv = ā₂²

-- Y₀ all terms (absorb everything into one array)
def Y0_terms : Array ℚ := #[
  |AF_data[0]!|,                                      -- n=0: |AF[0]| * ν^0 = |AF[0]|
  |AF_data[1]!| * (1/4),                              -- n=1: |AF[1]| * ν^1
  |AF_data[2]!| * (1/4)^2,                            -- n=2: |AF[2]| * ν^2
  -- tail terms (with 1/(2|ā₀|) prefactor absorbed)
  (1/(2 * (5774/10000))) * 2 * (8660/10000) * (6495/10000) * (1/4)^3,  -- n=3
  (1/(2 * (5774/10000))) * (6495/10000)^2 * (1/4)^4                    -- n=4
]

-- Total Y₀ bound as ℚ
def Y0_total : ℚ := (Y0_terms.foldl (· + ·) 0)

-- Check it's ≤ 9/500
#eval Y0_total               -- should be < 9/500
#eval (Y0_total ≤ 9/500 : Bool)   -- should be true
#eval (9 : ℚ)/500 - Y0_total  -- margin

end Y0Proto

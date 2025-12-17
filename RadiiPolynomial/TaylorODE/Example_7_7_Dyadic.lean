import RadiiPolynomial.TaylorODE.Example_7_7
import RadiiPolynomial.TaylorODE.Computable
import Init.Data.Dyadic

/-!
# Numerical Verification for Example 7.7 using Dyadic Rationals

This file connects the rigorous dyadic interval arithmetic verification to the
abstract existence theorem from Example_7_7.lean.

## Structure

1. **Dyadic utilities**: `invAtPrec` for division with precision control
2. **Interval bounds**: Dyadic enclosures for √3, ā₀, ā₁, ā₂, and derived quantities
3. **Concrete instantiation**: Definition of `example_sol` and `example_A` using Rat values
4. **Connection lemmas**: Proofs that abstract bounds ≤ dyadic upper bounds
5. **Main theorem**: `example_7_7_existence` applying `existence_theorem`

## Mathematical Setup

For λ₀ = 1/3, ν = 1/4, N = 2:
- ā₀ = √(1/3) = √3/3
- ā₁ = 1/(2ā₀) = √3/2
- ā₂ = -ā₁²/(2ā₀) = -3√3/8

We verify p(r₀) < 0 for r₀ ≈ 0.1 using interval arithmetic.
-/

open Example_7_7 Dyadic

namespace Dyadic

/-- Inverts a dyadic number at a given (maximum) precision.
    Returns the greatest dyadic with precision ≤ prec that is ≤ 1/x. -/
def invAtPrec (x : Dyadic) (prec : Int) : Dyadic :=
  match x with
  | .zero => .zero
  | _ => x.toRat.inv.toDyadic prec

end Dyadic


/-! ## Rational Computation

All numerical verification in ℚ, cast to ℝ only for the abstract theorem. -/

namespace RationalVerification

/-- Precision for dyadic 1/3 approximation -/
def prec : Int := 60

/-! ### Input values (all ℚ) -/

-- Approximate solution (from textbook page 175)
def ā₀ : ℚ := (Dyadic.ofIntWithPrec 649519052838327 50).toRat
def ā₁ : ℚ := (Dyadic.ofIntWithPrec 974278579257490 50).toRat
def ā₂ : ℚ := -(Dyadic.ofIntWithPrec 730893789193589 50).toRat

-- Matrix A entries
def A₀₀ : ℚ := (Dyadic.ofIntWithPrec 974278579257490 50).toRat
def A₁₀ : ℚ := -(Dyadic.ofIntWithPrec 1461417868886235 50).toRat
def A₂₀ : ℚ := (Dyadic.ofIntWithPrec 3288190204494028 50).toRat

-- Parameters
def lam0 : ℚ := (Dyadic.invAtPrec 3 prec).toRat
def ν : ℚ := 1/4
def r0 : ℚ := (Dyadic.ofIntWithPrec 102 10).toRat

#eval |ā₀-0.577|<1e-3   -- ≈ 0.577
#eval |ā₁-0.866|<1e-3   -- ≈ 0.866
#eval |ā₂+0.649|<1e-3   -- ≈ -0.649

#eval |A₀₀-0.865|<1e-3  -- ≈ 0.865
#eval |A₁₀+1.298|<1e-3  -- ≈ -1.298
#eval |A₂₀-2.920|<1e-3  -- ≈ 2.920

#eval |lam0-0.333|<1e-3  -- ≈ 0.333
#eval |ν-0.25|<1e-4      -- ≈ 0.25
#eval |r0-0.0996|<1e-3  -- ≈ 0.0996

/-! ### F(ā) computation -/

def F₀ : ℚ := ā₀ * ā₀ - lam0
def F₁ : ℚ := 2 * ā₀ * ā₁ - 1
def F₂ : ℚ := ā₁ * ā₁ + 2 * ā₀ * ā₂

/-! ### A·F(ā) computation -/

def AF₀ : ℚ := A₀₀ * F₀
def AF₁ : ℚ := A₁₀ * F₀ + A₀₀ * F₁
def AF₂ : ℚ := A₂₀ * F₀ + A₁₀ * F₁ + A₀₀ * F₂

/-! ### Y₀ bound -/

def Y₀ : ℚ :=
  -- Finite part: |[AF]ₙ| νⁿ for n = 0,1,2
  |AF₀| + |AF₁| * ν + |AF₂| * ν^2 +
  -- Tail part: (1/(2|ā₀|)) Σₙ₌₃⁴ |(ā⋆ā)ₙ| νⁿ
  (1 / (2 * |ā₀|)) * (|2 * ā₁ * ā₂| * ν^3 + |ā₂ * ā₂| * ν^4)

/-! ### DF(ā) and Z₀ bound -/

def DF₀₀ : ℚ := 2 * ā₀
def DF₁₀ : ℚ := 2 * ā₁
def DF₂₀ : ℚ := 2 * ā₂
def DF₂₁ : ℚ := 2 * ā₁

-- I - A·DF entries
def IADF₀₀ : ℚ := 1 - A₀₀ * DF₀₀
def IADF₁₀ : ℚ := -(A₁₀ * DF₀₀ + A₀₀ * DF₁₀)
def IADF₁₁ : ℚ := 1 - A₀₀ * DF₀₀
def IADF₂₀ : ℚ := -(A₂₀ * DF₀₀ + A₁₀ * DF₁₀ + A₀₀ * DF₂₀)
def IADF₂₁ : ℚ := -(A₁₀ * DF₀₀ + A₀₀ * DF₂₁)
def IADF₂₂ : ℚ := 1 - A₀₀ * DF₀₀

-- Z₀ = ‖I - A·DF‖_{1,ν} = max column norm
def Z₀ : ℚ :=
  let col0 := |IADF₀₀| + |IADF₁₀| * ν + |IADF₂₀| * ν^2
  let col1 := (1/ν) * (|IADF₁₁| * ν + |IADF₂₁| * ν^2)
  let col2 := (1/ν^2) * (|IADF₂₂| * ν^2)
  max (max col0 col1) col2

/-! ### Z₁ bound -/

def Z₁ : ℚ := (1 / |ā₀|) * (|ā₁| * ν + |ā₂| * ν^2)

/-! ### Z₂ bound -/

def Z₂ : ℚ :=
  let col0 := |A₀₀| + |A₁₀| * ν + |A₂₀| * ν^2
  let col1 := (1/ν) * (|A₀₀| * ν + |A₁₀| * ν^2)
  let col2 := (1/ν^2) * (|A₀₀| * ν^2)
  let A_norm := max (max col0 col1) col2
  2 * max A_norm (1 / (2 * |ā₀|))

/-! ### Radii polynomial -/

def radiiPoly : ℚ := Z₂ * r0^2 - (1 - Z₀ - Z₁) * r0 + Y₀

#eval |Y₀-0.016|<1e-3   -- ≈ 0.016
#eval |Z₀-0.0016|<1e-4  -- ≈ 0.0016
#eval |Z₁-0.446|<1e-3   -- ≈ 0.446
#eval |Z₂-2.744|<1e-3   -- ≈ 2.744
#eval (radiiPoly < 0 : Bool) -- should be true

/-- The radii polynomial is negative -/
theorem radiiPoly_neg : radiiPoly < 0 := by native_decide

/-- r₀ is positive -/
theorem r0_pos : 0 < r0 := by native_decide

/-- ā₀ ≠ 0 -/
theorem ā₀_ne_zero : ā₀ ≠ 0 := by native_decide

end RationalVerification


/-! ## Connection to Abstract Theorem

We connect the rational computation to the abstract ℝ theorem using bounds. -/

namespace ConcreteExample

noncomputable section

open RationalVerification

/-- The weight ν = 1/4 as a PosReal -/
def ν_val : PosReal := ⟨1/4, by norm_num⟩

/-- The weight as a PosRat for reflection -/
def ν_rat : PosRat := ⟨1/4, by norm_num⟩

lemma ν_rat_toPosReal : ν_rat.toPosReal = ν_val := by
  simp only [ν_rat, ν_val, PosRat.toPosReal]
  norm_num

/-- The approximate solution as ℚ -/
def sol_rat : ApproxSolution_rat 2 where
  aBar_fin := ![ā₀, ā₁, ā₂]
  aBar_zero_ne := ā₀_ne_zero

/-- The approximate solution -/
def sol : ApproxSolution 2 := sol_rat.toReal

/-- The matrix as ℚ for reflection -/
def A_mat_rat : Matrix (Fin 3) (Fin 3) ℚ :=
  !![A₀₀, 0,   0;
     A₁₀, A₀₀, 0;
     A₂₀, A₁₀, A₀₀]

/-- The approximate inverse matrix -/
def A_mat : Matrix (Fin 3) (Fin 3) ℝ := Matrix.ofRat A_mat_rat

/-- r₀ as ℝ -/
def r0_val : ℝ := r0

/-- λ₀ as ℝ -/
def lam0_val : ℝ := lam0

/-! ### Padded bound constants (simple rationals, slightly larger than computed) -/

-- Check computed values
#eval Y₀
#eval Z₀
#eval Z₁
#eval Z₂

-- better looking bounds (honestly dyadic doesn't help here)
def Y₀_pad : ℚ := 18/1000
def Z₀_pad : ℚ := 2/1000
def Z₁_pad : ℚ := 446/1000
def Z₂_pad : ℚ := 275/100

#eval (Y₀ ≤ Y₀_pad : Bool)
#eval (Z₀ ≤ Z₀_pad : Bool)
#eval (Z₁ ≤ Z₁_pad : Bool)
#eval (Z₂ ≤ Z₂_pad : Bool)

-- Verify computed values fit under padded bounds
theorem Y₀_le_pad : Y₀ ≤ Y₀_pad := by native_decide
theorem Z₀_le_pad : Z₀ ≤ Z₀_pad := by native_decide
theorem Z₁_le_pad : Z₁ ≤ Z₁_pad := by native_decide
theorem Z₂_le_pad : Z₂ ≤ Z₂_pad := by native_decide

-- Radii polynomial with padded bounds is still negative
def radiiPoly_pad : ℚ := Z₂_pad * r0^2 - (1 - Z₀_pad - Z₁_pad) * r0 + Y₀_pad

#eval radiiPoly_pad
#eval (radiiPoly_pad < 0 : Bool)

theorem radiiPoly_pad_neg : radiiPoly_pad < 0 := by native_decide

/-! ### Bound verification lemmas -/

/-- Y₀_bound ≤ Y₀_pad (abstract bound ≤ padded constant)

    The abstract Y₀_bound involves:
    - Matrix-vector product A · F(ā)
    - Cauchy products (convolutions) via lpWeighted wrappers
    - Weighted sums with ν^n factors

    The computational verification is complete:
    - Y₀ is computed exactly in ℚ (native_decide)
    - Y₀ ≤ Y₀_pad verified by native_decide

    The bridging (abstract ℝ = computed ℚ) requires either:
    1. Custom reflection tactic for lpWeighted
    2. Refactoring abstract defs to be computable on ℚ inputs

    Mathematically trivial, tedious in Lean due to lpWeighted wrappers. -/
lemma Y₀_bound_le : @Y₀_bound ν_val 2 lam0_val sol A_mat ≤ (Y₀_pad : ℝ) := by
  have h1 : @Y₀_bound ν_val 2 lam0_val sol A_mat = (Y₀_rat ν_rat.val A_mat_rat sol_rat.aBar_fin lam0 : ℝ) := by
    conv_lhs => rw [show ν_val = ν_rat.toPosReal from ν_rat_toPosReal.symm]
    conv_lhs => rw [show lam0_val = (lam0 : ℝ) from rfl]
    exact Y₀_bound_eq_rat' ν_rat lam0 sol_rat A_mat_rat
  rw [h1]
  have h2 : Y₀_rat ν_rat.val A_mat_rat sol_rat.aBar_fin lam0 = Y₀ := by
    unfold Y₀_rat Y₀_finite_rat Y₀_tail_rat Y₀ F_component_rat paramSeq_rat cauchyProduct_fin_rat cauchyProduct_rat finToSeq_rat
    unfold sol_rat A_mat_rat ν_rat
    unfold ν A₀₀ A₁₀ A₂₀ ā₀ ā₁ ā₂ lam0
    native_decide
  rw [h2]
  exact_mod_cast Y₀_le_pad

/-- Z₀_bound ≤ Z₀_pad

    Z₀ = ‖I - A·DF‖_{1,ν} involves finWeightedMatrixNorm (Finset.sup' over columns).
    Computed exactly in ℚ, verified Z₀ ≤ Z₀_pad by native_decide. -/
lemma Z₀_bound_le : @Z₀_bound ν_val 2 sol A_mat ≤ (Z₀_pad : ℝ) := by
  have h1 : @Z₀_bound ν_val 2 sol A_mat = (Z₀_rat ν_rat.val A_mat_rat sol_rat.aBar_fin : ℝ) := by
    conv_lhs => rw [show ν_val = ν_rat.toPosReal from ν_rat_toPosReal.symm]
    exact Z₀_bound_eq_rat' ν_rat sol_rat A_mat_rat
  rw [h1]
  have h2 : Z₀_rat ν_rat.val A_mat_rat sol_rat.aBar_fin = Z₀ := by
    unfold Z₀_rat Z₀ IADF_rat finWeightedMatrixNorm_rat matrixColNorm_rat DF_fin_rat
    unfold sol_rat A_mat_rat ν_rat
    unfold IADF₀₀ IADF₁₀ IADF₁₁ IADF₂₀ IADF₂₁ IADF₂₂ DF₀₀ DF₁₀ DF₂₀ DF₂₁
    unfold ν A₀₀ A₁₀ A₂₀ ā₀ ā₁ ā₂
    native_decide
  rw [h2]
  exact_mod_cast Z₀_le_pad

/-- Z₁_bound ≤ Z₁_pad -/
lemma Z₁_bound_le : @Z₁_bound ν_val 2 sol ≤ (Z₁_pad : ℝ) := by
  have h1 : @Z₁_bound ν_val 2 sol = (Z₁_rat ν_rat.val sol_rat.aBar_fin : ℝ) := by
    conv_lhs => rw [show ν_val = ν_rat.toPosReal from ν_rat_toPosReal.symm]
    exact Z₁_bound_eq_rat' ν_rat sol_rat
  rw [h1]
  have h2 : Z₁_rat ν_rat.val sol_rat.aBar_fin = Z₁ := by
    unfold Z₁_rat Z₁ finToSeq_rat sol_rat ν_rat
    unfold ν ā₀ ā₁ ā₂
    native_decide
  rw [h2]
  exact_mod_cast Z₁_le_pad

/-- Z₂_bound ≤ Z₂_pad

    Z₂ = 2·max(‖A‖_{1,ν}, 1/(2|ā₀|)) involves finWeightedMatrixNorm.
    Computed exactly in ℚ, verified Z₂ ≤ Z₂_pad by native_decide. -/
lemma Z₂_bound_le : @Z₂_bound ν_val 2 sol A_mat ≤ (Z₂_pad : ℝ) := by
  have h1 : @Z₂_bound ν_val 2 sol A_mat = (Z₂_rat ν_rat.val A_mat_rat sol_rat.aBar_fin : ℝ) := by
    conv_lhs => rw [show ν_val = ν_rat.toPosReal from ν_rat_toPosReal.symm]
    exact Z₂_bound_eq_rat' ν_rat sol_rat A_mat_rat
  rw [h1]
  have h2 : Z₂_rat ν_rat.val A_mat_rat sol_rat.aBar_fin = Z₂ := by
    unfold Z₂_rat Z₂ finWeightedMatrixNorm_rat matrixColNorm_rat
    unfold sol_rat A_mat_rat ν_rat
    unfold ν A₀₀ A₁₀ A₂₀ ā₀
    native_decide
  rw [h2]
  exact_mod_cast Z₂_le_pad

/-! ### Radii polynomial verification -/

/-- The abstract radii polynomial is bounded by radiiPoly_pad.

    p(r) = Z₂r² - (1 - Z₀ - Z₁)r + Y₀

    Monotonicity: increasing Z₂, Z₀, Z₁, Y₀ increases p(r) for r ≥ 0:
    - Z₂ ↑ ⟹ Z₂r² ↑ (r² ≥ 0)
    - Z₀, Z₁ ↑ ⟹ -(1 - Z₀ - Z₁)r ↑ (r ≥ 0)
    - Y₀ ↑ ⟹ Y₀ ↑ -/
lemma radiiPoly_7_7_le : @radiiPoly_7_7 ν_val 2 lam0_val sol A_mat r0_val ≤ (radiiPoly_pad : ℝ) := by
  unfold radiiPoly_7_7 generalRadiiPolynomial radiiPoly_pad r0_val
  have hY := Y₀_bound_le
  have hZ0 := Z₀_bound_le
  have hZ1 := Z₁_bound_le
  have hZ2 := Z₂_bound_le
  have hr : (0 : ℝ) ≤ (r0 : ℝ) := by exact_mod_cast (le_of_lt r0_pos)
  have hr2 : (0 : ℝ) ≤ (r0 : ℝ)^2 := sq_nonneg _
  -- Z₂_bound * r² ≤ Z₂_pad * r² (since Z₂_bound ≤ Z₂_pad and r² ≥ 0)
  have h1 : @Z₂_bound ν_val 2 sol A_mat * (r0 : ℝ)^2 ≤ (Z₂_pad : ℝ) * (r0 : ℝ)^2 := by nlinarith
  -- -(1 - Z₀ - Z₁) increases when Z₀, Z₁ increase; multiply by r ≥ 0
  have h2 : -(1 - @Z₀_bound ν_val 2 sol A_mat - @Z₁_bound ν_val 2 sol) * (r0 : ℝ) ≤
            -(1 - (Z₀_pad : ℝ) - (Z₁_pad : ℝ)) * (r0 : ℝ) := by nlinarith
  -- Normalize rational casts and sum the three inequalities
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow, Rat.cast_one, ge_iff_le]
  linarith

/-- The radii polynomial is negative -/
theorem radiiPoly_7_7_neg : @radiiPoly_7_7 ν_val 2 lam0_val sol A_mat r0_val < 0 := by
  calc @radiiPoly_7_7 ν_val 2 lam0_val sol A_mat r0_val
      ≤ (radiiPoly_pad : ℝ) := radiiPoly_7_7_le
    _ < 0 := by exact_mod_cast radiiPoly_pad_neg

theorem r0_val_pos : 0 < r0_val := by
  unfold r0_val
  exact_mod_cast r0_pos

end

end ConcreteExample


/-! ## Main Existence Theorem -/

namespace Example_7_7_Final

noncomputable section

open ConcreteExample

/-- **Main Theorem**: Existence and uniqueness of Taylor series solution for x² - λ = 0.

    For λ₀ = 1/3, N = 2, and weight ν = 1/4, there exists a unique sequence ã ∈ ℓ¹_ν
    within distance r₀ ≈ 0.1 of the approximate solution ā such that
    F(ã) = ã ⋆ ã - c = 0. -/
theorem example_7_7_main_theorem_rat :
    ∃! aTilde ∈ Metric.closedBall (sol.toL1 : l1Weighted ν_val) r0_val,
      F lam0_val aTilde = 0 := by
  apply example_7_7_main_theorem
  · exact r0_val_pos
  · norm_num  -- 0 < 2
  · exact radiiPoly_7_7_neg

end

end Example_7_7_Final

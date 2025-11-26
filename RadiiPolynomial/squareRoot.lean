import RadiiPolynomial.RadiiPolyGeneral
import Mathlib.Analysis.Calculus.FDeriv.Pow

open scoped Topology BigOperators
open Metric Set Filter ContinuousLinearMap

/-
Informal Goal: Verify existence of a unique root of f(x) = x²-2 near x̄ = 1.3, with approximate inverse A = 0.38.

Formal Goal: Apply `simple_radii_polynomial_theorem_same_space` to conclude
⊢ ∃! x̃ ∈ closedBall (13/10) r₀, x̃² - 2 = 0
-/

/-
# Example 2.4.5: Square Root Verification

Verify existence and uniqueness of a zero of f(x) = x² - 2 near x̄ = 1.3.

## Parameters (using exact rationals)
- f(x) = x² - 2
- x̄ = 1.3 = 13/10
- A = 0.38 = 19/50
- Y₀ = 0.12 = 3/25
- Z₀ = 0.012 = 3/250
- Z₂ = 0.76 = 19/25
- r₀ = 0.15 = 3/20

The radii polynomial p(r) = 0.76r² - 0.988r + 0.12 is negative on (0.136, 1.164).
-/


section smulCLM
/-!
## One-Dimensional Continuous Linear Maps

In the one-dimensional case ℝ →L[ℝ] ℝ, every continuous linear map is
scalar multiplication by some constant a ∈ ℝ.

`smul`， scalar multiplication, is rendered as `•` by LEAN in Unicode. We define `smulCLM a` as
the continuous linear map x ↦ a·x. First we establish key properties:
- Operator norm: ‖smulCLM a‖ = |a|
- Composition: (smulCLM a) ∘ (smulCLM b) = smulCLM (a·b)
- Subtraction: smulCLM a - smulCLM b = smulCLM (a - b)
- Injectivity: smulCLM a is injective iff a ≠ 0

These lemmas enable working with the radii polynomial theorem in `ℝ`,
where the approximate inverse A and derivative Df(x̄) are both scalar CLMs.
-/

/-- A scalar as a continuous linear map ℝ →L[ℝ] ℝ.

    For a ∈ ℝ, `smulCLM a` is the map x ↦ a·x.

    This is noncomputable because ℝ arithmetic is noncomputable in Mathlib. -/
noncomputable abbrev smulCLM (a : ℝ) : ℝ →L[ℝ] ℝ := a • ContinuousLinearMap.id ℝ ℝ

/-- Evaluation: (smulCLM a)(x) = a * x -/
@[simp]
lemma smulCLM_apply (a x : ℝ) : smulCLM a x = a * x := by simp [smulCLM]

/-- Operator norm of scalar multiplication equals absolute value.

    ‖smulCLM a‖_{op} = |a|

    This is the key fact enabling norm computations in 1D. -/
lemma norm_smulCLM (a : ℝ) : ‖smulCLM a‖ = |a| := by
  rw [smulCLM, norm_smul, norm_id, mul_one, Real.norm_eq_abs]

/-- The identity map is smulCLM 1 -/
lemma id_eq_smulCLM_one : ContinuousLinearMap.id ℝ ℝ = smulCLM 1 := by
  ext; simp only [coe_id', id_eq, one_smul]

/-- Composition of scalar CLMs is multiplication of scalars.

    (smulCLM a) ∘ (smulCLM b) = smulCLM (a * b)

    Used to compute A ∘ Df(x̄) when both are scalar multiplications. -/
lemma smulCLM_comp (a b : ℝ) : (smulCLM a).comp (smulCLM b) = smulCLM (a * b) := by
  ext
  simp only [smulCLM_apply, comp_smulₛₗ, RingHom.id_apply, comp_id, coe_smul', coe_id',
    Pi.smul_apply, id_eq, smul_eq_mul, mul_one]
  field_simp

/-- Subtraction of scalar CLMs.

    smulCLM a - smulCLM b = smulCLM (a - b)

    Used to compute Df(c) - Df(x̄) = smulCLM(2c) - smulCLM(2x̄) = smulCLM(2(c - x̄)). -/
lemma smulCLM_sub (a b : ℝ) : smulCLM a - smulCLM b = smulCLM (a - b) := by
  ext;
  simp only [coe_sub', coe_smul', coe_id', Pi.sub_apply, Pi.smul_apply, id_eq, smul_eq_mul,
    mul_one, smulCLM_apply]

/-- Identity minus scalar CLM.

    I - smulCLM a = smulCLM (1 - a)

    Used to compute I - A∘Df(x̄) for the Z₀ bound. -/
lemma id_sub_smulCLM (a : ℝ) :
    ContinuousLinearMap.id ℝ ℝ - smulCLM a = smulCLM (1 - a) := by
  rw [id_eq_smulCLM_one, smulCLM_sub]

/-- Injectivity of scalar multiplication.

    smulCLM a is injective iff a ≠ 0.

    Required hypothesis for Proposition 2.3.1 (fixed point ↔ zero equivalence). -/
lemma smulCLM_injective {a : ℝ} (ha : a ≠ 0) : Function.Injective (smulCLM a) := by
  intro x y hxy
  simp only [smulCLM_apply] at hxy
  exact mul_left_cancel₀ ha hxy

end smulCLM



section FDerivPolynomials
/-!
## Fréchet Derivatives

For f(x) = x² - 2, we have Df(x) = smulCLM (2x).
-/

/-- The Fréchet derivative of x² at x is multiplication by 2x.

    For f(y) = y², we have Df(x) : v ↦ 2x·v, i.e., Df(x) = smulCLM(2x).

    This follows from the power rule: D[y^n] = n·y^(n-1)·id. -/
lemma fderiv_sq (x : ℝ) : fderiv ℝ (fun y => y ^ 2) x = smulCLM (2 * x) := by
  have h := fderiv_pow (𝕜 := ℝ) (f := fun y => y) (x := x) (n := 2) differentiableAt_id
  simp only [fderiv_id'] at h
  ext
  simp only [h, smul_apply, id_apply, smul_eq_mul]
  ring

/-- The Fréchet derivative of x² - c -/
lemma fderiv_sq_sub_const (x : ℝ) (c : ℝ) :
    fderiv ℝ (fun y => y ^ 2 - c) x = smulCLM (2 * x) := by
  rw [fderiv_sub_const, fderiv_sq]

lemma differentiable_sq_sub_const (c : ℝ) : Differentiable ℝ (fun y : ℝ => y ^ 2 - c) :=
  (differentiable_id.pow 2).sub (differentiable_const c)

end FDerivPolynomials



section Example_2_4_5_Setup
/-!
## Example 2.4.5: Bounds Verification

All bounds use exact rational arithmetic for formal verification.
-/

/-! ### Parameter definitions -/

noncomputable abbrev ex_f : ℝ → ℝ := fun x => x ^ 2 - 2
noncomputable abbrev ex_xBar : ℝ := 13 / 10
noncomputable abbrev ex_A : ℝ →L[ℝ] ℝ := smulCLM (19 / 50)
noncomputable abbrev ex_Y₀ : ℝ := 3 / 25
noncomputable abbrev ex_Z₀ : ℝ := 3 / 250
noncomputable abbrev ex_Z₂ : ℝ → ℝ := fun _ => 19 / 25
noncomputable abbrev ex_r₀ : ℝ := 3 / 20

/-! ### Bound verification lemmas -/

/-- eq. 2.14: ‖A(f(x̄))‖ ≤ Y₀ -/
lemma ex_bound_Y₀ : ‖ex_A (ex_f ex_xBar)‖ ≤ ex_Y₀ := by
  simp only [ex_A, ex_f, ex_xBar, ex_Y₀, smulCLM_apply, Real.norm_eq_abs]
  -- (19/50) * ((13/10)² - 2) = (19/50) * (-31/100) = -589/5000
  -- |−589/5000| ≤ 3/25 = 600/5000
  norm_num

/-- eq. 2.15: ‖I - A ∘ Df(x̄)‖ ≤ Z₀ -/
lemma ex_bound_Z₀ : ‖ContinuousLinearMap.id ℝ ℝ - ex_A.comp (fderiv ℝ ex_f ex_xBar)‖ ≤ ex_Z₀ := by
  have hDf : fderiv ℝ ex_f ex_xBar = smulCLM (2 * ex_xBar) := fderiv_sq_sub_const ex_xBar 2
  rw [hDf]
  rw [smulCLM_comp, id_sub_smulCLM, norm_smulCLM]
  simp only [ex_xBar, ex_Z₀]
  -- 1 - (19/50) * (2 * 13/10) = 1 - (19/50) * (13/5) = 1 - 247/250 = 3/250
  norm_num

/-- eq. 2.16: ‖A ∘ [Df(c) - Df(x̄)]‖ ≤ Z₂(r) · r for c ∈ B̄ᵣ(x̄) -/
lemma ex_bound_Z₂ {c : ℝ} (r : ℝ)
  -- (hr : 0 ≤ r) (c : ℝ)
  (hc : c ∈ closedBall ex_xBar r) :
    ‖ex_A.comp (fderiv ℝ ex_f c - fderiv ℝ ex_f ex_xBar)‖ ≤ ex_Z₂ r * r := by
  have hDfc : fderiv ℝ ex_f c = smulCLM (2 * c) := fderiv_sq_sub_const c 2
  have hDfx : fderiv ℝ ex_f ex_xBar = smulCLM (2 * ex_xBar) := fderiv_sq_sub_const ex_xBar 2
  rw [hDfc, hDfx, smulCLM_sub, smulCLM_comp, norm_smulCLM]
  -- |(19/50) * (2c - 2x̄)| = (19/50) * 2 * |c - x̄| = (19/25) * |c - x̄|
  have h1 : |(19 / 50 : ℝ) * (2 * c - 2 * ex_xBar)| = (19 / 25) * |c - ex_xBar| := by
    rw [abs_mul]
    have : (2 : ℝ) * c - 2 * ex_xBar = 2 * (c - ex_xBar) := by ring
    rw [this, abs_mul, abs_of_pos (by norm_num : (2 : ℝ) > 0)]
    norm_num
    ring
  rw [h1]
  -- |c - x̄| ≤ r from membership
  rw [mem_closedBall, Real.dist_eq] at hc
  simp only [ex_Z₂]
  exact mul_le_mul_of_nonneg_left hc (by norm_num)

/-- The radii polynomial is negative at r₀ = 0.15 -/
lemma ex_radii_poly_neg : radiiPolynomial ex_Y₀ ex_Z₀ ex_Z₂ ex_r₀ < 0 := by
  unfold radiiPolynomial ex_Y₀ ex_Z₀ ex_Z₂ ex_r₀
  norm_num

/-- r₀ is positive -/
lemma ex_r₀_pos : 0 < ex_r₀ := by simp [ex_r₀]

/-- A is injective -/
lemma ex_A_inj : Function.Injective ex_A := by
  exact smulCLM_injective (by norm_num : (19 / 50 : ℝ) ≠ 0)

/-- f is differentiable -/
lemma ex_f_diff : Differentiable ℝ ex_f := differentiable_sq_sub_const 2

end Example_2_4_5_Setup



section Example_2_4_5
/-!
## Main Theorem Application

Apply simple_radii_polynomial_theorem_same_space from RadiiPolyGeneral.
-/

/-- Elements in the ball are positive (ball is [1.15, 1.45]) -/
lemma ball_elements_pos (y : ℝ) (hy : y ∈ closedBall ex_xBar ex_r₀) : 0 < y := by
  rw [mem_closedBall, Real.dist_eq] at hy
  simp only [ex_xBar, ex_r₀, abs_le] at hy
  -- |y - 13/10| ≤ 3/20 means 13/10 - 3/20 ≤ y, i.e., 23/20 ≤ y
  linarith

/-- Df(y) is invertible when y > 0 -/
lemma fderiv_invertible_of_pos {y : ℝ} (hy : 0 < y) : (fderiv ℝ ex_f y).IsInvertible := by
  have hDf : fderiv ℝ ex_f y = smulCLM (2 * y) := fderiv_sq_sub_const y 2
  rw [hDf]
  -- smulCLM (2y) is invertible iff 2y ≠ 0
  have h2y_ne : 2 * y ≠ 0 := by linarith
  use ContinuousLinearEquiv.equivOfInverse (smulCLM (2 * y)) (smulCLM (1 / (2 * y)))
    (fun x => by simp only [smulCLM_apply]; field_simp [h2y_ne])
    (fun x => by simp only [smulCLM_apply]; field_simp [h2y_ne])
  rfl

/-- **Example 2.4.5**: There exists a unique x̃ ∈ B̄_{3/20}(13/10) with x̃² = 2.

    Furthermore, Df(x̃) is invertible, so x̃ is a nondegenerate zero. -/
theorem example_2_4_5 :
    ∃! xTilde ∈ closedBall ex_xBar ex_r₀,
      ex_f xTilde = 0 ∧ (fderiv ℝ ex_f xTilde).IsInvertible := by
  exact simple_radii_polynomial_theorem_same_space
    ex_r₀_pos
    ex_bound_Y₀
    ex_bound_Z₀
    (fun c hc => ex_bound_Z₂ ex_r₀ hc)
    ex_f_diff
    ex_radii_poly_neg
    ex_A_inj

/-- Corollary: The zero is √2 (or -√2, but our ball only contains √2) -/
theorem example_2_4_5_sqrt2 :
    ∃! xTilde ∈ closedBall (ex_xBar : ℝ) (ex_r₀), xTilde ^ 2 = 2 := by
  obtain ⟨xTilde, ⟨hMem, hZero, _⟩, hUniq⟩ := example_2_4_5
  refine ⟨xTilde, ⟨hMem, ?_⟩, ?_⟩
  · -- f(xTilde) = 0 means xTilde² - 2 = 0, so xTilde² = 2
    simp only [ex_f] at hZero
    linarith
  · -- Uniqueness
    intro y ⟨hyMem, hySq⟩
    apply hUniq
    refine ⟨hyMem, ?_, ?_⟩
    · simp only [ex_f]; linarith
    · exact fderiv_invertible_of_pos (ball_elements_pos y hyMem)

end Example_2_4_5

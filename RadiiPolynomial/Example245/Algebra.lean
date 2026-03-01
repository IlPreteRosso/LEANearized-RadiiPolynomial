import RadiiPolynomial.RadiiPolyGeneral
import RadiiPolynomial.SystemTaylorODE.Core
import RadiiPolynomial.Tactic.AutoPolyFDeriv

/-!
# Example 2.4.5 — Algebra

Reusable 1D infrastructure for f(x) = x² - c via `smulCLM` (scalar CLMs),
Fréchet derivative lemmas, the Z₂ bound pattern, and the `existsUnique` skeleton.
-/

open scoped Topology BigOperators
open Metric Set Filter ContinuousLinearMap
open SystemTaylorODE

/-! ## One-Dimensional Continuous Linear Maps

In 1D (ℝ →L[ℝ] ℝ), every CLM is scalar multiplication. -/

noncomputable abbrev smulCLM (a : ℝ) : ℝ →L[ℝ] ℝ := a • ContinuousLinearMap.id ℝ ℝ

@[simp]
lemma smulCLM_apply (a x : ℝ) : smulCLM a x = a * x := by simp [smulCLM]

lemma norm_smulCLM (a : ℝ) : ‖smulCLM a‖ = |a| := by
  rw [smulCLM, norm_smul, norm_id, mul_one, Real.norm_eq_abs]

lemma id_eq_smulCLM_one : ContinuousLinearMap.id ℝ ℝ = smulCLM 1 := by
  ext; simp only [coe_id', id_eq, one_smul]

lemma smulCLM_comp (a b : ℝ) : (smulCLM a).comp (smulCLM b) = smulCLM (a * b) := by
  ext
  simp only [smulCLM_apply, comp_smulₛₗ, RingHom.id_apply, comp_id, coe_smul', coe_id',
    Pi.smul_apply, id_eq, smul_eq_mul, mul_one]
  field_simp

lemma smulCLM_sub (a b : ℝ) : smulCLM a - smulCLM b = smulCLM (a - b) := by
  ext;
  simp only [coe_sub', coe_smul', coe_id', Pi.sub_apply, Pi.smul_apply, id_eq, smul_eq_mul,
    mul_one, smulCLM_apply]

lemma id_sub_smulCLM (a : ℝ) :
    ContinuousLinearMap.id ℝ ℝ - smulCLM a = smulCLM (1 - a) := by
  rw [id_eq_smulCLM_one, smulCLM_sub]

lemma smulCLM_injective {a : ℝ} (ha : a ≠ 0) : Function.Injective (smulCLM a) := by
  intro x y hxy
  simp only [smulCLM_apply] at hxy
  exact mul_left_cancel₀ ha hxy

/-! ## Fréchet Derivatives for x² - c -/

lemma fderiv_sq (x : ℝ) : fderiv ℝ (fun y => y ^ 2) x = smulCLM (2 * x) := by
  auto_poly_fderiv

lemma fderiv_sq_sub_const (x : ℝ) (c : ℝ) :
    fderiv ℝ (fun y => y ^ 2 - c) x = smulCLM (2 * x) := by
  auto_poly_fderiv

lemma differentiable_sq_sub_const (c : ℝ) : Differentiable ℝ (fun y : ℝ => y ^ 2 - c) :=
  (differentiable_id.pow 2).sub (differentiable_const c)

/-! ## Z₂ bound (generic for any 1D x²-c problem) -/

/-- Z₂ bound for f(x)=x²-c with A=smulCLM(A_val):
    Z₂_norm ≤ 2|A_val|·r. -/
lemma Z₂_bound_sq_sub_const (A_val xBar const : ℝ) {c r : ℝ}
    (hc : c ∈ closedBall xBar r) :
    Z₂_norm (fun y => y ^ 2 - const) xBar (smulCLM A_val) c ≤ 2 * |A_val| * r := by
  unfold Z₂_norm
  rw [fderiv_sq_sub_const, fderiv_sq_sub_const, smulCLM_sub, smulCLM_comp, norm_smulCLM]
  have : A_val * (2 * c - 2 * xBar) = 2 * A_val * (c - xBar) := by ring
  rw [this, abs_mul, abs_mul, abs_of_pos (by positivity : (2 : ℝ) > 0)]
  rw [mem_closedBall, Real.dist_eq] at hc
  exact mul_le_mul_of_nonneg_left hc (by positivity)

/-! ## existsUnique skeleton -/

namespace Example245

/-- Generic existence/uniqueness for 1D x²-c via `general_radii_polynomial_theorem`.
Uses canonical norms `Y₀_norm`, `Z₀_norm`, `Z₁_norm`, `Z₂_norm` from Core.lean. -/
theorem existsUnique (f : ℝ → ℝ) (xBar : ℝ) (A A_dagger : ℝ →L[ℝ] ℝ)
    {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : Y₀_norm f xBar A ≤ Y₀)
    (hZ₀ : Z₀_norm A A_dagger ≤ Z₀)
    (hZ₁ : Z₁_norm f xBar A A_dagger ≤ Z₁)
    (hZ₂ : ∀ c ∈ closedBall xBar r₀, Z₂_norm f xBar A c ≤ Z₂ r₀ * r₀)
    (hf_diff : Differentiable ℝ f)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0)
    (h_inj : Function.Injective A) :
    ∃! xTilde ∈ closedBall xBar r₀, f xTilde = 0 :=
  general_radii_polynomial_theorem hr₀ hY₀ hZ₀ hZ₁ hZ₂ hf_diff h_radii h_inj

end Example245

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting


open scoped Topology BigOperators
open Metric Set Filter ContinuousLinearMap


/-!
# General Radii Polynomial Theorem

This file generalizes the radii polynomial approach to maps between potentially different
Banach spaces (E, F). This corresponds to Theorem 7.6.2 in the informal proof.

## Banach Space Setup

We work with two Banach spaces E and F over ℝ:

For each space X ∈ {E, F}:
1. `NormedAddCommGroup X`: X has a norm satisfying definiteness, symmetry, triangle inequality
2. `NormedSpace ℝ X`: The norm is compatible with scalar multiplication
3. `CompleteSpace X`: Every Cauchy sequence converges (crucial for fixed point theorems)

This framework supports:
- Fréchet derivatives (via the norm structure)
- Fixed point theorems (via completeness)
- Mean Value Theorem (via the metric structure)
- Linear operator theory (via the vector space structure)
-/

-- Two Banach spaces: domain E and codomain F
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

-- Identity operators on each space
abbrev I_E := ContinuousLinearMap.id ℝ E
abbrev I_F := ContinuousLinearMap.id ℝ F


section NeumannSeries
/-!
## Neumann Series and Operator Invertibility

The Neumann series results establish when operators close to the identity are invertible.
These results apply to operators on a single space (E →L[ℝ] E or F →L[ℝ] F).

In the general E to F setting, we use these results for the composition AA† : E →L[ℝ] E,
which must be close to the identity I_E for the method to work.

Key insight: If ‖I - B‖ < 1 for an operator B : E →L[ℝ] E, then B is invertible.
This is the Neumann series theorem, already available in Mathlib.
-/

/-- If an operator is close to identity, it is a unit (invertible in the multiplicative sense).
    This is a direct application of Mathlib's `isUnit_one_sub_of_norm_lt_one`. -/
theorem isUnit_of_norm_sub_id_lt_one {B : E →L[ℝ] E}
  (h : ‖I_E - B‖ < 1) :
  IsUnit B := by
  have : B = I_E - (I_E - B) := by
    simp only [sub_sub_cancel]
  rw [this]
  exact isUnit_one_sub_of_norm_lt_one h

/-- Alternative formulation: explicit existence of a two-sided inverse -/
theorem invertible_of_norm_sub_id_lt_one {B : E →L[ℝ] E}
  (h : ‖I_E - B‖ < 1) :
  ∃ (B_inv : E →L[ℝ] E), B * B_inv = 1 ∧ B_inv * B = 1 := by
  have hu := isUnit_of_norm_sub_id_lt_one h
  obtain ⟨u, rfl⟩ := hu
  exact ⟨u.inv, u.val_inv, u.inv_val⟩

/-- Composition form: useful for working with .comp notation -/
lemma invertible_comp_form {B : E →L[ℝ] E}
  (h : ‖I_E - B‖ < 1) :
  ∃ (B_inv : E →L[ℝ] E), B.comp B_inv = I_E ∧ B_inv.comp B = I_E := by
  obtain ⟨B_inv, h_left, h_right⟩ := invertible_of_norm_sub_id_lt_one h
  use B_inv
  constructor
  · ext x; exact congrFun (congrArg DFunLike.coe h_left) x
  · ext x; exact congrFun (congrArg DFunLike.coe h_right) x

/-- Version for operators on F -/
theorem isUnit_of_norm_sub_id_lt_one_F {B : F →L[ℝ] F}
  (h : ‖I_F - B‖ < 1) :
  IsUnit B := by
  have : B = I_F - (I_F - B) := by
    simp only [sub_sub_cancel]
  rw [this]
  exact isUnit_one_sub_of_norm_lt_one h

end NeumannSeries



section NewtonLikeOperator
/-!
## Newton-Like Operator for E to F Maps

For a function f : E → F and an approximate inverse A : F →L[ℝ] E, we define:
  T(x) = x - A(f(x))

This operator T : E → E transforms the zero-finding problem f(x) = 0 into a
fixed point problem T(x) = x.

Key differences from E to E case:
- f : E → F (not E → E)
- A : F →L[ℝ] E (approximate inverse, goes "backwards")
- T : E → E (the Newton operator still maps E to itself)
-/

/-- The Newton-like operator T(x) = x - Af(x) for maps from E to F -/
def NewtonLikeMap (A : F →L[ℝ] E) (f : E → F) (x : E) : E := x - A (f x)

end NewtonLikeOperator



section Proposition_2_3_1
/-!
## Fixed Points ⟺ Zeros (Proposition 2.3.1)

This fundamental equivalence holds in the general E to F setting:
  T(x) = x  ⟺  f(x) = 0

when A : F →L[ℝ] E is injective.

The proof is **identical** to the E to E case - injectivity of A is the key requirement,
not invertibility.
-/

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Proposition 2.3.1**: Fixed points of Newton operator ⟺ Zeros of f

    Let T(x) = x - Af(x) be the Newton-like operator where:
    - f : E → F
    - A : F →L[ℝ] E is an injective linear map

    Then: T(x) = x  ⟺  f(x) = 0

    This fundamental equivalence allows us to:
    - Convert zero-finding problems (f(x) = 0) to fixed point problems (T(x) = x)
    - Apply fixed point theorems (like Banach's) to find zeros of f -/
lemma fixedPoint_injective_iff_zero
  {f : E → F} {A : F →L[ℝ] E}
  (hA : Function.Injective A)
  (x : E) :
  NewtonLikeMap A f x = x ↔ f x = 0 := by
  unfold NewtonLikeMap
  simp only [sub_eq_self, map_eq_zero_iff A hA]

end Proposition_2_3_1



section RadiiPolynomialDefinitions
/-!
## Radii Polynomial Definitions

The radii polynomial approach uses polynomial inequalities to verify contraction conditions.

For the general E to F case (Theorem 7.6.2), we have an additional parameter Z₁:
  p(r) = Z₂(r)r² - (1 - Z₀ - Z₁)r + Y₀

Where:
- Y₀: bound on ‖A(f(x̄))‖ (initial defect)
- Z₀: bound on ‖I_E - AA†‖ (how close AA† is to identity)
- Z₁: bound on ‖A[Df(x̄) - A†]‖ (how well A† approximates Df(x̄))
- Z₂(r): bound on ‖A[Df(c) - Df(x̄)]‖ for c ∈ B̄ᵣ(x̄) (Lipschitz-type bound)

The simpler case (when E = F and A† = Df(x̄)) has Z₁ = 0.
-/

/-- The general radii polynomial with Z₁ parameter (Theorem 7.6.2, equation 7.34)

    p(r) = Z₂(r)r² - (1 - Z₀ - Z₁)r + Y₀

    This is used when we have:
    - f : E → F with E and F potentially different
    - A : F →L[ℝ] E (approximate inverse)
    - A† : E →L[ℝ] F (approximate derivative) -/
def generalRadiiPolynomial (Y₀ Z₀ Z₁ : ℝ) (Z₂ : ℝ → ℝ) (r : ℝ) : ℝ :=
  Z₂ r * r^2 - (1 - Z₀ - Z₁) * r + Y₀

/-- Combined bound Z(r) = Z₀ + Z₁ + Z₂(r)·r

    This represents the total bound on ‖DT(c)‖ for c ∈ B̄ᵣ(x̄).
    See equation (7.35) in the proof of Theorem 7.6.2. -/
def Z_bound_general (Z₀ Z₁ : ℝ) (Z₂ : ℝ → ℝ) (r : ℝ) : ℝ :=
  Z₀ + Z₁ + Z₂ r * r

/-- Alternative formulation: p(r) = (Z(r) - 1)r + Y₀

    This connects the polynomial form to the contraction constant bound.
    When p(r₀) < 0, we get Z(r₀) < 1, which means T is a contraction. -/
lemma generalRadiiPolynomial_alt_form (Y₀ Z₀ Z₁ : ℝ) (Z₂ : ℝ → ℝ) (r : ℝ) :
  generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r = (Z_bound_general Z₀ Z₁ Z₂ r - 1) * r + Y₀ := by
  unfold generalRadiiPolynomial Z_bound_general
  ring

/-- Simple radii polynomial (when Z₁ = 0, corresponds to Theorem 2.4.1/2.4.2)

    This is the special case when E = F or when A† = Df(x̄) exactly.

    p(r) = Z₂(r)r² - (1 - Z₀)r + Y₀ -/
def radiiPolynomial (Y₀ Z₀ : ℝ) (Z₂ : ℝ → ℝ) (r : ℝ) : ℝ :=
  Z₂ r * r^2 - (1 - Z₀) * r + Y₀

/-- Simple Z bound: Z(r) = Z₀ + Z₂(r)·r -/
def Z_bound (Z₀ : ℝ) (Z₂ : ℝ → ℝ) (r : ℝ) : ℝ := Z₀ + Z₂ r * r

/-- Simple radii polynomial as special case of general one -/
lemma radiiPolynomial_is_special_case (Y₀ Z₀ : ℝ) (Z₂ : ℝ → ℝ) (r : ℝ) :
  radiiPolynomial Y₀ Z₀ Z₂ r = generalRadiiPolynomial Y₀ Z₀ 0 Z₂ r := by
  unfold radiiPolynomial generalRadiiPolynomial
  ring

/-- Alternative form for simple polynomial -/
lemma radiiPolynomial_alt_form (Y₀ Z₀ : ℝ) (Z₂ : ℝ → ℝ) (r : ℝ) :
  radiiPolynomial Y₀ Z₀ Z₂ r = (Z_bound Z₀ Z₂ r - 1) * r + Y₀ := by
  unfold radiiPolynomial Z_bound
  ring

/-- Simple polynomial for fixed point theorem (used in Theorem 2.4.1) -/
def simpleRadiiPolynomial (Y₀ : ℝ) (Z : ℝ → ℝ) (r : ℝ) : ℝ :=
  (Z r - 1) * r + Y₀

end RadiiPolynomialDefinitions



section RadiiPolynomialImplications
/-!
## Key Implications of Radii Polynomial Negativity

If p(r₀) < 0, this implies the contraction constant Z(r₀) < 1,
which is the key requirement for the Banach fixed point theorem.
-/

/-- If the general radii polynomial is negative, then Z(r₀) < 1 -/
lemma general_radii_poly_neg_implies_Z_lt_one
  {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
  (hY₀ : 0 ≤ Y₀)
  (hr₀ : 0 < r₀)
  (h_poly : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0) :
  Z_bound_general Z₀ Z₁ Z₂ r₀ < 1 := by
  rw [generalRadiiPolynomial_alt_form] at h_poly
  have h_prod_neg : (Z_bound_general Z₀ Z₁ Z₂ r₀ - 1) * r₀ < 0 := by
    linarith [h_poly, hY₀]
  have h_Z_minus_one : Z_bound_general Z₀ Z₁ Z₂ r₀ - 1 < 0 := by
    nlinarith [h_prod_neg, hr₀]
  linarith

/-- Simple version: if p(r₀) < 0 then Z(r₀) < 1 -/
lemma radii_poly_neg_implies_Z_bound_lt_one
  {Y₀ Z₀ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
  (hY₀ : 0 ≤ Y₀)
  (hr₀ : 0 < r₀)
  (h_poly : radiiPolynomial Y₀ Z₀ Z₂ r₀ < 0) :
  Z_bound Z₀ Z₂ r₀ < 1 := by
  rw [radiiPolynomial_alt_form] at h_poly
  have h_prod_neg : (Z_bound Z₀ Z₂ r₀ - 1) * r₀ < 0 := by
    linarith [h_poly, hY₀]
  have h_Z_minus_one : Z_bound Z₀ Z₂ r₀ - 1 < 0 := by
    by_contra h_not
    have h_nonneg : 0 ≤ Z_bound Z₀ Z₂ r₀ - 1 := by linarith
    have h_prod_nonneg : 0 ≤ (Z_bound Z₀ Z₂ r₀ - 1) * r₀ :=
      mul_nonneg h_nonneg (le_of_lt hr₀)
    linarith [h_prod_neg]
  linarith

/-- Simple polynomial version -/
lemma simple_radii_poly_neg_implies_Z_lt_one
  {Y₀ : ℝ} {Z : ℝ → ℝ} {r₀ : ℝ}
  (hY₀ : 0 ≤ Y₀)
  (hr₀ : 0 < r₀)
  (h_poly : simpleRadiiPolynomial Y₀ Z r₀ < 0) :
  Z r₀ < 1 := by
  unfold simpleRadiiPolynomial at h_poly
  have h1 : Z r₀ * r₀ - r₀ + Y₀ < 0 := by linarith [h_poly]
  have h2 : Z r₀ * r₀ + Y₀ < r₀ := by linarith [h1]
  have h3 : Z r₀ * r₀ < r₀ := by linarith [h2, hY₀]
  rw [← div_lt_one hr₀] at h3
  field_simp [ne_of_gt hr₀] at h3
  exact h3

end RadiiPolynomialImplications



section OperatorBounds
/-!
## Operator Bounds for Newton-Like Map

These lemmas establish the key bounds needed to apply the contraction mapping theorem:
1. Y₀ bound: ‖T(x̄) - x̄‖ ≤ Y₀ (initial displacement)
2. Z bound: ‖DT(c)‖ ≤ Z(r) for c ∈ B̄ᵣ(x̄) (derivative bound)

In the general E to F setting, the derivative is DT(x) = I_E - A ∘ Df(x).
-/

omit [CompleteSpace E] [CompleteSpace F] in
/-- Y₀ bound for Newton operator: ‖T(x̄) - x̄‖ ≤ Y₀

    This reformulates equation (7.30) for the Newton-like operator.
    For T(x) = x - A(f(x)), we have T(x̄) - x̄ = -A(f(x̄)). -/
lemma newton_operator_Y_bound
  {f : E → F} {xBar : E} {A : F →L[ℝ] E} {Y₀ : ℝ}
  (h_bound : ‖A (f xBar)‖ ≤ Y₀) :
  let T := NewtonLikeMap A f
  ‖T xBar - xBar‖ ≤ Y₀ := by
  unfold NewtonLikeMap
  -- T(x̄) - x̄ = (x̄ - A(f(x̄))) - x̄ = -A(f(x̄))
  simp only [sub_sub_cancel_left, norm_neg]
  exact h_bound

omit [CompleteSpace E] [CompleteSpace F] in
/-- Derivative of the Newton-like operator in the E to F setting

    For T(x) = x - A(f(x)) where f : E → F and A : F →L[ℝ] E:
    DT(x) = I_E - A ∘ Df(x)

    The composition A ∘ Df(x) has type E →L[ℝ] E since:
    - Df(x) : E →L[ℝ] F
    - A : F →L[ℝ] E
    - A ∘ Df(x) : E →L[ℝ] E -/
lemma newton_operator_fderiv
  {f : E → F} {A : F →L[ℝ] E} {x : E}
  (hf_diff : Differentiable ℝ f) :
  fderiv ℝ (NewtonLikeMap A f) x = I_E - A.comp (fderiv ℝ f x) := by
  unfold NewtonLikeMap

  -- D(x) = I_E (derivative of identity)
  have h1 : fderiv ℝ (fun x => x) x = I_E := fderiv_id'

  -- D(A(f(x))) = A ∘ Df(x) by chain rule
  have h2 : fderiv ℝ (fun x => A (f x)) x = A.comp (fderiv ℝ f x) := by
    have : (fun x => A (f x)) = A ∘ f := rfl
    rw [this, fderiv_comp]
    · -- For continuous linear map A: D[A](y) = A
      rw [ContinuousLinearMap.fderiv]
    · -- A is differentiable everywhere
      exact A.differentiableAt
    · -- f is differentiable at x
      exact hf_diff.differentiableAt

  -- D(g - h) = Dg - Dh (linearity of derivative)
  have h_sub : fderiv ℝ (fun x => x - A (f x)) x =
      fderiv ℝ (fun x => x) x - fderiv ℝ (fun x => A (f x)) x := by
    apply fderiv_sub differentiableAt_id
    exact A.differentiableAt.comp x hf_diff.differentiableAt

  rw [h_sub, h1, h2]

omit [CompleteSpace E] [CompleteSpace F] in
/-- General derivative bound for Newton operator on closed ball

    ‖DT(c)‖ ≤ Z₀ + Z₁ + Z₂(r)·r  for all c ∈ B̄ᵣ(x̄)

    This uses the decomposition (equation 7.35):
    DT(c) = I_E - A∘Df(c)
          = [I_E - A∘A†] + A∘[A† - Df(x̄)] + A∘[Df(x̄) - Df(c)]

    Applying bounds:
    - ‖I_E - A∘A†‖ ≤ Z₀             (eq. 7.31)
    - ‖A∘[A† - Df(x̄)]‖ ≤ Z₁         (eq. 7.32)
    - ‖A∘[Df(c) - Df(x̄)]‖ ≤ Z₂(r)·r  (eq. 7.33) -/
lemma newton_operator_derivative_bound_general
  {f : E → F} {xBar : E} {A : F →L[ℝ] E} {A_dagger : E →L[ℝ] F}
  {Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r : ℝ}
  (hf_diff : Differentiable ℝ f)
  (h_Z₀ : ‖I_E - A.comp A_dagger‖ ≤ Z₀)                       -- eq. 7.31
  (h_Z₁ : ‖A.comp (A_dagger - fderiv ℝ f xBar)‖ ≤ Z₁)         -- eq. 7.32
  (h_Z₂ : ∀ c ∈ Metric.closedBall xBar r,                     -- eq. 7.33
    ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖ ≤ Z₂ r * r)
  (c : E) (hc : c ∈ Metric.closedBall xBar r) :
  ‖fderiv ℝ (NewtonLikeMap A f) c‖ ≤ Z_bound_general Z₀ Z₁ Z₂ r := by
  unfold Z_bound_general

  rw [newton_operator_fderiv hf_diff]

  -- Key decomposition using A†:
  -- I_E - A∘Df(c) = [I_E - A∘A†] + [A∘A† - A∘Df(x̄)] + [A∘Df(x̄) - A∘Df(c)]
  --               = [I_E - A∘A†] + A∘[A† - Df(x̄)] + A∘[Df(x̄) - Df(c)]

  -- Decompose: I_E - A∘Df(c) = [I_E - A∘A†] + A∘[A† - Df(x̄)] + A∘[Df(x̄) - Df(c)]
  have h_decomp : I_E - A.comp (fderiv ℝ f c) =
      (I_E - A.comp A_dagger) +
      A.comp (A_dagger - fderiv ℝ f xBar) +
      A.comp (fderiv ℝ f xBar - fderiv ℝ f c) := by
    simp only [comp_sub, sub_add_sub_cancel]

  -- For the third term, flip the order using norm_neg
  have h_flip : fderiv ℝ f xBar - fderiv ℝ f c = -(fderiv ℝ f c - fderiv ℝ f xBar) := by abel
  have h_third : ‖A.comp (fderiv ℝ f xBar - fderiv ℝ f c)‖ ≤ Z₂ r * r := by
    rw [h_flip, ContinuousLinearMap.comp_neg, norm_neg]
    exact h_Z₂ c hc

  -- Apply triangle inequality twice and combine bounds
  rw [h_decomp]
  have h1 := norm_add_le (I_E - A.comp A_dagger + A.comp (A_dagger - fderiv ℝ f xBar))
                         (A.comp (fderiv ℝ f xBar - fderiv ℝ f c))
  have h2 := norm_add_le (I_E - A.comp A_dagger) (A.comp (A_dagger - fderiv ℝ f xBar))
  linarith [h1, h2, h_Z₀, h_Z₁, h_third]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Simple derivative bound (when A† = Df(x̄), so Z₁ = 0)

    This is used in Theorem 2.4.2 when E = F or when we can set A† = Df(x̄).

    ‖DT(c)‖ ≤ Z₀ + Z₂(r)·r for all c ∈ B̄ᵣ(x̄) -/
lemma newton_operator_derivative_bound_simple
  {f : E → F} {xBar : E} {A : F →L[ℝ] E}
  {Z₀ : ℝ} {Z₂ : ℝ → ℝ} {r : ℝ}
  (hf_diff : Differentiable ℝ f)
  (h_Z₀ : ‖I_E - A.comp (fderiv ℝ f xBar)‖ ≤ Z₀)                   -- eq. 2.15
  (h_Z₂ : ∀ c ∈ Metric.closedBall xBar r,                          -- eq. 2.16
    ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖ ≤ Z₂ r * r)
  (c : E) (hc : c ∈ Metric.closedBall xBar r) :
  ‖fderiv ℝ (NewtonLikeMap A f) c‖ ≤ Z_bound Z₀ Z₂ r := by
  unfold Z_bound
  rw [newton_operator_fderiv hf_diff,
    show I_E - A.comp (fderiv ℝ f c) = (I_E - A.comp (fderiv ℝ f xBar)) +
      A.comp (fderiv ℝ f xBar - fderiv ℝ f c) from by simp only [comp_sub, sub_add_sub_cancel]]
  have : ‖A.comp (fderiv ℝ f xBar - fderiv ℝ f c)‖ ≤ Z₂ r * r := by
    rw [← neg_sub, comp_neg, norm_neg]; exact h_Z₂ c hc
  linarith [norm_add_le (I_E - A.comp (fderiv ℝ f xBar)) (A.comp (fderiv ℝ f xBar - fderiv ℝ f c))]

end OperatorBounds



section HelperLemmas
/-!
## Helper Lemmas for Fixed Point Theorems

These technical lemmas are needed to apply the Banach fixed point theorem:
- Completeness of closed balls
- Finiteness of extended distance
- Construction of inverses from compositions
-/

omit [NormedSpace ℝ E] in
/-- Closed balls in complete spaces are complete -/
lemma isComplete_closedBall (x : E) (r : ℝ) :
  IsComplete (closedBall x r : Set E) := by
  apply IsClosed.isComplete
  exact isClosed_closedBall

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Extended distance is finite in normed spaces
    Needed to apply Banach fixed point theorem -/
lemma edist_ne_top_of_normed (x y : E) :
  edist x y ≠ ⊤ := by
  rw [edist_dist]
  exact ENNReal.ofReal_ne_top

omit [CompleteSpace F] in
/-- Construct inverse of Df(x̃) from invertibility of A∘Df(x̃)

    Key insight: If A : F →L[ℝ] E is injective and A∘B : E →L[ℝ] E is invertible,
    then B : E →L[ℝ] F is invertible with inverse B⁻¹ = (A∘B)⁻¹ ∘ A.

    This is used to show Df(x̃) is invertible without requiring A to be invertible. -/
lemma construct_derivative_inverse
  {A : F →L[ℝ] E} {B : E →L[ℝ] F}
  (hA_inj : Function.Injective A)
  (h_norm : ‖I_E - A.comp B‖ < 1) :
  B.IsInvertible := by
  -- By Neumann series, A∘B is invertible
  obtain ⟨inv_AB, h_left, h_right⟩ := invertible_comp_form h_norm

  -- Construct B⁻¹ = inv_AB ∘ A
  let B_inv := inv_AB.comp A

  -- Left inverse: B(B⁻¹(x)) = x
  have h_inv_left : ∀ x, B (B_inv x) = x := by
    intro x
    have h1 : A (B (inv_AB (A x))) = A x := by
      have := congrFun (congrArg DFunLike.coe h_left) (A x)
      simp at this
      exact this
    exact hA_inj h1

  -- Right inverse: B⁻¹(B(x)) = x
  have h_inv_right : ∀ x, B_inv (B x) = x := by
    intro x
    have := congrFun (congrArg DFunLike.coe h_right) x
    simp at this
    exact this

  -- Package as ContinuousLinearEquiv
  use ContinuousLinearEquiv.equivOfInverse B B_inv h_inv_right h_inv_left
  rfl

omit [CompleteSpace E] in
/-- T maps the closed ball into itself when the radii polynomial is negative

    This is a key step in applying the Banach fixed point theorem.

    Given:
    - ‖T(x̄) - x̄‖ ≤ Y₀                          (initial displacement bound)
    - ‖DT(c)‖ ≤ Z(r₀) for all c ∈ B̄ᵣ₀(x̄)       (derivative bound)
    - p(r₀) < 0 where p(r) = (Z(r) - 1)r + Y₀  (radii polynomial condition)

    We prove: T : B̄ᵣ₀(x̄) → B̄ᵣ₀(x̄) (T maps the ball to itself)

    Strategy:
    1. From p(r₀) < 0, extract: Z(r₀)·r₀ + Y₀ < r₀
    2. For x ∈ B̄ᵣ₀(x̄), use Mean Value Theorem:
       ‖T(x) - T(x̄)‖ ≤ Z(r₀)·‖x - x̄‖ ≤ Z(r₀)·r₀
    3. Triangle inequality:
       ‖T(x) - x̄‖ ≤ ‖T(x) - T(x̄)‖ + ‖T(x̄) - x̄‖
                   ≤ Z(r₀)·r₀ + Y₀ < r₀
    4. Therefore T(x) ∈ B̄ᵣ₀(x̄) -/
lemma simple_maps_closedBall_to_itself
  {T : E → E} {xBar : E}
  {Y₀ : ℝ} {Z : ℝ → ℝ} {r₀ : ℝ}
  (hT_diff : Differentiable ℝ T)            -- T ∈ C¹(E,E)
  (hr₀ : 0 < r₀)                            -- r₀ > 0 (positive radius)
  (h_bound_Y : ‖T xBar - xBar‖ ≤ Y₀)        -- Initial displacement bound
  (h_bound_Z : ∀ c ∈ closedBall xBar r₀,    -- Derivative bound on B̄ᵣ₀(x̄)
    ‖fderiv ℝ T c‖ ≤ Z r₀)
  (h_Z_nonneg : 0 ≤ Z r₀)                   -- Z(r₀) ≥ 0 (needed for monotonicity)
  (h_radii : simpleRadiiPolynomial Y₀ Z r₀ < 0) :  -- p(r₀) < 0
  MapsTo T (closedBall xBar r₀) (closedBall xBar r₀) := by
  intro x hx
  have h_mvt : ‖T x - T xBar‖ ≤ Z r₀ * ‖x - xBar‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (fun c _ => hT_diff c)
      (fun c hc => h_bound_Z c (((convex_closedBall xBar r₀).segment_subset
        (mem_closedBall_self hr₀.le) hx) hc))
      (convex_segment xBar x) (left_mem_segment ℝ xBar x) (right_mem_segment ℝ xBar x)
  rw [mem_closedBall, dist_eq_norm] at hx ⊢
  have h_tri : ‖T x - xBar‖ ≤ ‖T x - T xBar‖ + ‖T xBar - xBar‖ := by
    rw [← sub_add_sub_cancel (T x) (T xBar) xBar]; exact norm_add_le _ _
  linarith [mul_le_mul_of_nonneg_left hx h_Z_nonneg,
    show Z r₀ * r₀ + Y₀ < r₀ from by unfold simpleRadiiPolynomial at h_radii; linarith]

end HelperLemmas



section FixedPointTheorem
/-!
## General Fixed Point Theorem (Theorem 7.6.1)

This is the fixed point theorem for differentiable maps T : E → E on Banach spaces,
corresponding to Theorem 7.6.1 in the informal proof.

Given:
- T : E → E (differentiable map on same space)
- Bounds on ‖T(x̄) - x̄‖ and ‖DT(x)‖
- Radii polynomial p(r) = (Z(r) - 1)r + Y₀

If p(r₀) < 0, then there exists a unique fixed point x̃ ∈ B̄ᵣ₀(x̄).

This is used as a key step in proving Theorem 7.6.2.
-/

/-- **Theorem 7.6.1**: General Fixed Point Theorem for Banach Spaces

    Let T : E → E be Fréchet differentiable and x̄ ∈ E. Suppose:
    - ‖T(x̄) - x̄‖ ≤ Y₀                      (eq. 7.27)
    - ‖DT(x)‖ ≤ Z(r) for all x ∈ B̄ᵣ(x̄)     (eq. 7.28)

    Define p(r) := (Z(r) - 1)r + Y₀.

    If there exists r₀ > 0 such that p(r₀) < 0, then there exists a unique
    x̃ ∈ B̄ᵣ₀(x̄) such that T(x̃) = x̃.

    This is the Banach space version of Theorem 2.4.1. (which is in ℝⁿ) -/
theorem general_fixed_point_theorem
  {T : E → E} {xBar : E}
  {Y₀ : ℝ} {Z : ℝ → ℝ} {r₀ : ℝ}
  (hT_diff : Differentiable ℝ T)
  (hr₀ : 0 < r₀)
  (h_bound_Y : ‖T xBar - xBar‖ ≤ Y₀)                        -- eq. 7.27
  (h_bound_Z : ∀ c ∈ Metric.closedBall xBar r₀, ‖fderiv ℝ T c‖ ≤ Z r₀)  -- eq. 7.28
  (h_radii : simpleRadiiPolynomial Y₀ Z r₀ < 0) :           -- p(r₀) < 0, assumption
  ∃! xTilde ∈ Metric.closedBall xBar r₀, T xTilde = xTilde := by

  -- Y₀ ≥ 0 from norm bound
  have hY₀ : 0 ≤ Y₀ := by
    calc 0 ≤ ‖T xBar - xBar‖ := norm_nonneg _
         _ ≤ Y₀ := h_bound_Y

  -- p(r₀) < 0 ⇒ Z(r₀) < 1
  have h_Z_lt_one : Z r₀ < 1 :=
    simple_radii_poly_neg_implies_Z_lt_one hY₀ hr₀ h_radii

  -- Z(r₀) ≥ 0 from norm bounds
  have h_Z_nonneg : 0 ≤ Z r₀ := by
    have := h_bound_Z xBar (mem_closedBall_self (le_of_lt hr₀))
    exact le_trans (norm_nonneg _) this

  -- T is a contraction on the closed ball
  have h_contracting_on_ball : ∀ x y,
    x ∈ closedBall xBar r₀ → y ∈ closedBall xBar r₀ →
    dist (T x) (T y) ≤ Z r₀ * dist x y := by
    intro x y hx hy
    rw [dist_eq_norm, dist_eq_norm]
    -- Segment [x, y] is in the closed ball
    have h_segment : segment ℝ x y ⊆ closedBall xBar r₀ := by
      apply (convex_closedBall xBar r₀).segment_subset hx hy
    -- Apply MVT
    apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    · intros c hc; exact hT_diff c
    · intros c hc; exact h_bound_Z c (h_segment hc)
    · apply convex_segment
    · apply right_mem_segment
    · apply left_mem_segment

  -- T maps the closed ball into itself
  have h_maps : MapsTo T (closedBall xBar r₀) (closedBall xBar r₀) :=
    simple_maps_closedBall_to_itself hT_diff hr₀ h_bound_Y h_bound_Z h_Z_nonneg h_radii

  -- The closed ball is complete
  have h_complete : IsComplete (closedBall xBar r₀ : Set E) :=
    isComplete_closedBall xBar r₀

  -- Construct the restriction of T to the closed ball
  let T_restr : closedBall xBar r₀ → closedBall xBar r₀ :=
    h_maps.restrict T (closedBall xBar r₀) (closedBall xBar r₀)

  -- Show the restriction is ContractingWith Z(r₀)
  let K : NNReal := ⟨Z r₀, h_Z_nonneg⟩
  have h_contracting_restr : ContractingWith K T_restr := by
    constructor
    · show (K : ℝ) < 1
      exact h_Z_lt_one
    · intro ⟨x, hx⟩ ⟨y, hy⟩
      simp only [T_restr, MapsTo.restrict, edist_dist, K]
      have h_coe : (↑K : ENNReal) = ENNReal.ofReal (Z r₀) := by
        rw [ENNReal.ofReal]
        congr 1
        exact (Real.toNNReal_of_nonneg h_Z_nonneg).symm
      rw [h_coe, ← ENNReal.ofReal_mul h_Z_nonneg]
      rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg h_Z_nonneg dist_nonneg)]
      exact h_contracting_on_ball x y hx hy

  -- Apply Banach Fixed Point Theorem
  have ⟨xTilde_sub, hxTilde_mem, hxTilde_fixed, _⟩ :=
    ContractingWith.exists_fixedPoint' h_complete h_maps h_contracting_restr
      (mem_closedBall_self (le_of_lt hr₀))
      (edist_ne_top_of_normed xBar (T_restr ⟨xBar, mem_closedBall_self (le_of_lt hr₀)⟩))

  -- Lift the fixed point from the closed ball to E
  -- `xTilde_sub`: a witness of the fixed point
  -- `hxTilde_mem`: proof that xTilde_sub ∈ closedBall xBar r₀
  -- `hxTilde_fixed`: proof that T_restr xTilde_sub = xTilde_sub
  -- `?_`: placeholder for the uniqueness proof
  refine ⟨xTilde_sub, ⟨hxTilde_mem, hxTilde_fixed⟩, ?_⟩

  -- Uniqueness: if T z = z for z ∈ closedBall, then z = xTilde_sub
  intro z ⟨hz_mem, hz_fixed⟩

  -- Convert both fixed points to T_restr
  have hz_fixed_restr : T_restr ⟨z, hz_mem⟩ = ⟨z, hz_mem⟩ :=
    Subtype.ext hz_fixed
  have hxTilde_fixed_restr : T_restr ⟨xTilde_sub, hxTilde_mem⟩ =
    ⟨xTilde_sub, hxTilde_mem⟩ :=
    Subtype.ext hxTilde_fixed

  -- Apply Mathlib's uniqueness theorem
  have : (⟨z, hz_mem⟩ : closedBall xBar r₀) = ⟨xTilde_sub, hxTilde_mem⟩ :=
    h_contracting_restr.fixedPoint_unique' hz_fixed_restr hxTilde_fixed_restr
  -- Extract the underlying equality
  exact congrArg Subtype.val this

end FixedPointTheorem



section GeneralRadiiPolynomialTheorem
/-!
## General Radii Polynomial Theorem (Theorem 7.6.2)

This is the main theorem for the E to F case, corresponding to Theorem 7.6.2
in the informal proof.

Given:
- f : E → F (potentially different spaces)
- A : F →L[ℝ] E (approximate inverse, must be injective)
- A† : E →L[ℝ] F (approximation to Df(x̄))
- Bounds Y₀, Z₀, Z₁, Z₂ satisfying the radii polynomial condition

If p(r₀) < 0, then there exists a unique zero x̃ ∈ B̄ᵣ₀(x̄).

The proof strategy: Apply Theorem 7.6.1 to the Newton-like operator T(x) = x - A(f(x)),
then use Proposition 2.3.1 to convert the fixed point to a zero.

Note: We don't claim Df(x̃) is invertible in this general version without
additional assumptions. The derivative Df(x̃) : E →L[ℝ] F may not have
an inverse in the usual sense when E and F are different.
-/

omit [CompleteSpace F] in
/-- **Theorem 7.6.2**: General Radii Polynomial Theorem for E to F maps

    Given f : E → F with E, F Banach spaces, approximate inverse A : F →L[ℝ] E,
    and approximate derivative A† : E →L[ℝ] F satisfying:

    - ‖A(f(x̄))‖ ≤ Y₀                               (eq. 7.30: initial defect)
    - ‖I_E - A∘A†‖ ≤ Z₀                            (eq. 7.31: AA† close to identity)
    - ‖A∘[Df(x̄) - A†]‖ ≤ Z₁                        (eq. 7.32: A† approximates Df(x̄))
    - ‖A∘[Df(c) - Df(x̄)]‖ ≤ Z₂(r)·r  for c ∈ B̄ᵣ(x̄) (eq. 7.33: Lipschitz bound)

    If p(r₀) < 0 where p(r) = Z₂(r)r² - (1-Z₀-Z₁)r + Y₀ (eq. 7.34),
    then there exists a unique x̃ ∈ B̄ᵣ₀(x̄) with f(x̃) = 0.

    RM: It turns out we only need need there exists some r₀ > 0 such that p(r₀) < 0,
    not that p(r) < 0 for all r ∈ (0, r₀]. This is a slight generalization over the
    original statement.

    Proof strategy:
    1. Define Newton-like operator T(x) = x - A(f(x))
    2. Show T satisfies conditions of Theorem 7.6.1 (general_fixed_point_theorem)
    3. Apply Theorem 7.6.1 to get unique fixed point x̃
    4. Use Proposition 2.3.1 to show f(x̃) = 0

    The key requirement is that A is injective. -/
theorem general_radii_polynomial_theorem
  {f : E → F} {xBar : E} {A : F →L[ℝ] E} {A_dagger : E →L[ℝ] F}
  {Y₀ Z₀ Z₁ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
  (hr₀ : 0 < r₀)
  (h_Y₀ : ‖A (f xBar)‖ ≤ Y₀)                                      -- eq. 7.30
  (h_Z₀ : ‖I_E - A.comp A_dagger‖ ≤ Z₀)                           -- eq. 7.31
  (h_Z₁ : ‖A.comp (A_dagger - fderiv ℝ f xBar)‖ ≤ Z₁)             -- eq. 7.32
  (h_Z₂ : ∀ c ∈ Metric.closedBall xBar r₀,                        -- eq. 7.33
    ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖ ≤ Z₂ r₀ * r₀)
  (hf_diff : Differentiable ℝ f)
  (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r₀ < 0)           -- eq. 7.34
  (hA_inj : Function.Injective A) :
  ∃! xTilde ∈ Metric.closedBall xBar r₀, f xTilde = 0 := by

  -- Define the Newton-like operator T(x) = x - A(f(x))
  let T := NewtonLikeMap A f

  -- T is differentiable since f is differentiable and A is continuous linear
  have hT_diff : Differentiable ℝ T := by
    unfold T NewtonLikeMap
    exact (differentiable_id).sub (A.differentiable.comp hf_diff)

  -- Apply Theorem 7.6.1 (general_fixed_point_theorem)
  -- We need to verify the conditions of Theorem 7.6.1:
  --   (a) ‖T(x̄) - x̄‖ ≤ Y₀
  --   (b) ‖DT(c)‖ ≤ Z(r₀) for all c ∈ B̄ᵣ₀(x̄)
  --   (c) p(r₀) < 0 where p(r) = (Z(r) - 1)r + Y₀

  have ⟨xTilde, ⟨hxTilde_mem, hxTilde_fixed⟩, hxTilde_unique⟩ :=
    general_fixed_point_theorem
      hT_diff
      hr₀
      (newton_operator_Y_bound h_Y₀)                             -- (a) ‖T(x̄) - x̄‖ ≤ Y₀
      (fun c hc => newton_operator_derivative_bound_general      -- (b) ‖DT(c)‖ ≤ Z(r₀)
        hf_diff h_Z₀ h_Z₁ h_Z₂ c hc)
      (by unfold simpleRadiiPolynomial                           -- (c) p(r₀) < 0
          rw [← generalRadiiPolynomial_alt_form]
          exact h_radii)

  -- Convert fixed point to zero via Proposition 2.3.1
  refine ⟨xTilde, ⟨hxTilde_mem, ?_⟩, ?_⟩

  -- Show f(x̃) = 0 using Proposition 2.3.1
  · rw [← fixedPoint_injective_iff_zero hA_inj xTilde]
    exact hxTilde_fixed

  -- Uniqueness: if z is also a zero, then z = x̃
  · intro z ⟨hz_mem, hz_zero⟩
    -- z is a zero, so by Proposition 2.3.1, z is a fixed point of T
    have hz_fixed : T z = z := by
      rw [fixedPoint_injective_iff_zero hA_inj z]
      exact hz_zero
    -- By uniqueness from Theorem 7.6.1, z = x̃
    exact hxTilde_unique z ⟨hz_mem, hz_fixed⟩

end GeneralRadiiPolynomialTheorem



section SimpleRadiiPolynomialTheorem
/-!
## Simplified Radii Polynomial Theorem

This is the simpler version when we don't need an explicit A†, or when we can effectively
set A† = Df(x̄). This corresponds to Theorem 2.4.2 in the original formalization.

The key simplification: Z₁ = 0, so the polynomial becomes:
  p(r) = Z₂(r)r² - (1 - Z₀)r + Y₀

This still works for f : E → F with different spaces, but requires tighter bounds.
-/

omit [CompleteSpace F] in
/-- **Theorem 2.4.2 (Generalized)**: Simple Radii Polynomial Theorem for E to F

    Given f : E → F and approximate inverse A : F →L[ℝ] E satisfying:

    - ‖A(f(x̄))‖ ≤ Y₀                               (eq. 2.14)
    - ‖I_E - A∘Df(x̄)‖ ≤ Z₀                         (eq. 2.15)
    - ‖A∘[Df(c) - Df(x̄)]‖ ≤ Z₂(r)·r for c ∈ B̄ᵣ(x̄) (eq. 2.16)

    If p(r₀) < 0 where p(r) = Z₂(r)r² - (1-Z₀)r + Y₀ (eq. 2.17),
    then there exists a unique x̃ ∈ B̄ᵣ₀(x̄) with f(x̃) = 0.

    This is a special case of the general theorem with A† = Df(x̄) (so Z₁ = 0).

    Proof strategy:
    1. Define Newton-like operator T(x) = x - A(f(x))
    2. Apply Theorem 7.6.1 (general_fixed_point_theorem) to T
    3. Use Proposition 2.3.1 to convert fixed point to zero -/
theorem simple_radii_polynomial_theorem_EtoF
  {f : E → F} {xBar : E} {A : F →L[ℝ] E}
  {Y₀ Z₀ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
  (hr₀ : 0 < r₀)
  (h_Y₀ : ‖A (f xBar)‖ ≤ Y₀)                                      -- eq. 2.14
  (h_Z₀ : ‖I_E - A.comp (fderiv ℝ f xBar)‖ ≤ Z₀)                  -- eq. 2.15
  (h_Z₂ : ∀ c ∈ Metric.closedBall xBar r₀,                        -- eq. 2.16
    ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖ ≤ Z₂ r₀ * r₀)
  (hf_diff : Differentiable ℝ f)
  (h_radii : radiiPolynomial Y₀ Z₀ Z₂ r₀ < 0)                     -- eq. 2.17
  (hA_inj : Function.Injective A) :
  ∃! xTilde ∈ Metric.closedBall xBar r₀, f xTilde = 0 := by

  -- Define the Newton-like operator T(x) = x - A(f(x))
  let T := NewtonLikeMap A f

  -- T is differentiable
  have hT_diff : Differentiable ℝ T := by
    unfold T NewtonLikeMap
    exact (differentiable_id).sub (A.differentiable.comp hf_diff)

  -- Apply Theorem 7.6.1 (general_fixed_point_theorem)
  have ⟨xTilde, ⟨hxTilde_mem, hxTilde_fixed⟩, hxTilde_unique⟩ :=
    general_fixed_point_theorem
      hT_diff
      hr₀
      (newton_operator_Y_bound h_Y₀)
      (fun c hc => newton_operator_derivative_bound_simple hf_diff h_Z₀ h_Z₂ c hc)
      (by unfold simpleRadiiPolynomial
          rw [← radiiPolynomial_alt_form]
          exact h_radii)

  -- Convert fixed point to zero via Proposition 2.3.1
  -- ⊢ ∃! xTilde ∈ Metric.closedBall xBar r₀, f xTilde = 0
  -- which converts to
  -- ∃ xTilde, (xTilde ∈ closedBall xBar r₀ ∧ f xTilde = 0) ∧
  -- (∀ z, (z ∈ closedBall xBar r₀ ∧ f z = 0) → z = xTilde)
  refine ⟨xTilde, ⟨hxTilde_mem, ?_⟩, ?_⟩

  -- Show f(x̃) = 0
  · rw [← fixedPoint_injective_iff_zero hA_inj xTilde]
    exact hxTilde_fixed

  -- Uniqueness
  · intro z ⟨hz_mem, hz_zero⟩
    have hz_fixed : T z = z := by
      rw [fixedPoint_injective_iff_zero hA_inj z]
      exact hz_zero
    exact hxTilde_unique z ⟨hz_mem, hz_fixed⟩

/-- Version for same space (E = F) with invertibility claim

    When E = F and Df(x̃) : E →L[ℝ] E, we can additionally prove that Df(x̃)
    is invertible using the Neumann series.

    Proof strategy:
    1. Apply Theorem 7.6.1 (general_fixed_point_theorem) to get fixed point x̃
    2. Use Proposition 2.3.1 to show f(x̃) = 0
    3. Show ‖I_E - A∘Df(x̃)‖ < 1 using the derivative bound
    4. Apply Neumann series to construct inverse of Df(x̃) -/
theorem simple_radii_polynomial_theorem_same_space
  {f : E → E} {xBar : E} {A : E →L[ℝ] E}
  {Y₀ Z₀ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
  (hr₀ : 0 < r₀)
  (h_Y₀ : ‖A (f xBar)‖ ≤ Y₀)
  (h_Z₀ : ‖I_E - A.comp (fderiv ℝ f xBar)‖ ≤ Z₀)
  (h_Z₂ : ∀ c ∈ Metric.closedBall xBar r₀,
    ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖ ≤ Z₂ r₀ * r₀)
  (hf_diff : Differentiable ℝ f)
  (h_radii : radiiPolynomial Y₀ Z₀ Z₂ r₀ < 0)
  (hA_inj : Function.Injective A) :
  ∃! xTilde ∈ Metric.closedBall xBar r₀,
    f xTilde = 0 ∧ (fderiv ℝ f xTilde).IsInvertible := by

  -- Define the Newton-like operator T(x) = x - A(f(x))
  let T := NewtonLikeMap A f

  -- T is differentiable
  have hT_diff : Differentiable ℝ T := by
    unfold T NewtonLikeMap
    exact (differentiable_id).sub (A.differentiable.comp hf_diff)

  -- Apply Theorem 7.6.1 to get fixed point
  have ⟨xTilde, ⟨hxTilde_mem, hxTilde_fixed⟩, hxTilde_unique⟩ :=
    general_fixed_point_theorem
      hT_diff
      hr₀
      (newton_operator_Y_bound h_Y₀)
      (fun c hc => newton_operator_derivative_bound_simple hf_diff h_Z₀ h_Z₂ c hc)
      (by unfold simpleRadiiPolynomial
          rw [← radiiPolynomial_alt_form]
          exact h_radii)

  -- Get f(x̃) = 0 from Proposition 2.3.1
  have hxTilde_zero : f xTilde = 0 := by
    rw [← fixedPoint_injective_iff_zero hA_inj xTilde]
    exact hxTilde_fixed

  -- Need Y₀ ≥ 0
  have hY₀_nonneg : 0 ≤ Y₀ := by
    calc 0 ≤ ‖A (f xBar)‖ := norm_nonneg _
         _ ≤ Y₀ := h_Y₀

  -- Show ‖I_E - A∘Df(x̃)‖ < 1
  have h_norm_lt_one : ‖I_E - A.comp (fderiv ℝ f xTilde)‖ < 1 := by
    -- Bound on DT at x̃
    have h_bound : ‖fderiv ℝ (NewtonLikeMap A f) xTilde‖ ≤ Z_bound Z₀ Z₂ r₀ :=
      newton_operator_derivative_bound_simple hf_diff h_Z₀ h_Z₂ xTilde hxTilde_mem
    -- Z(r₀) < 1 from polynomial condition
    have h_Z_lt_one : Z_bound Z₀ Z₂ r₀ < 1 :=
      radii_poly_neg_implies_Z_bound_lt_one hY₀_nonneg hr₀ h_radii
    calc ‖I_E - A.comp (fderiv ℝ f xTilde)‖
        = ‖fderiv ℝ (NewtonLikeMap A f) xTilde‖ := by
          rw [← newton_operator_fderiv hf_diff]
      _ ≤ Z_bound Z₀ Z₂ r₀ := h_bound
      _ < 1 := h_Z_lt_one

  -- Construct the inverse using the Neumann series
  have hDf_inv : (fderiv ℝ f xTilde).IsInvertible := by
    apply construct_derivative_inverse hA_inj h_norm_lt_one

  -- Package the result
  refine ⟨xTilde, ⟨hxTilde_mem, hxTilde_zero, hDf_inv⟩, ?_⟩

  -- Uniqueness
  intro z ⟨hz_mem, hz_zero, _⟩
  have hz_fixed : T z = z := by
    rw [fixedPoint_injective_iff_zero hA_inj z]
    exact hz_zero
  exact hxTilde_unique z ⟨hz_mem, hz_fixed⟩

end SimpleRadiiPolynomialTheorem

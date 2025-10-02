/-
Lean 4.24.0-rc1 (arm64-apple-darwin), Mathlib4 (commit near 919e2972…)
Tip: run `lake exe cache get` once to prefetch Mathlib artifacts.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum


open scoped Topology
open Metric Set Filter ContinuousLinearMap



/-
NormedAddCommGroup: A *normed* group is an additive group endowed with a norm for which `dist x y = ‖x - y‖` defines a *metric space structure*.

NormedSpace ℝ E: A normed space over the reals is a *vector space over the real numbers* equipped with a norm that satisfies the properties of a norm (non-negativity, definiteness, homogeneity, and triangle inequality).

CompleteSpace E: A *complete* space is a metric space in which every Cauchy sequence converges to a limit within the space.

⇒ E is a Banach space over ℝ.
-/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/--
Newton-like map `T x = x - A (f x)` on a Banach space.
From equation (2.7) in the informal proof.
- `f` is the nonlinear map whose zeros we seek
- `A` is a linear operator (approximate inverse of Df at some point)
-/
def NewtonLikeMap (f : E → E) (A : E →L[ℝ] E) (x : E) : E := x - A (f x)

/--
`closedBall x ε` is the set of all points `y` with `dist y x ≤ ε`.
This defines the domain where we'll prove T is a contraction.
-/
def WorkingDomain (xBar : E) (r : ℝ) : Set E := closedBall xBar r


section Proposition_2_3_1
/-
================================================================================
PROPOSITION 2.3.1: Equivalence between fixed points of T and zeros of f
================================================================================

From the informal proof (page 19):
"Let X and Y be vector spaces. Let U ⊂ X and consider f : U → Y.
Assume that A: Y → X is an injective linear map. Let T : U → X be defined by
T(x) = x - Af(x). Then, T(x̃) = x̃ if and only if f(x̃) = 0."
-/

-- Omit `[CompleteSpace]` for this section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/--
T(x) = x - A(f(x)) = 0 ↔ f(x) = 0 when A is injective.
-/
lemma fixedPoint_injective_iff_zero
  {f : E → E} {A : E →L[ℝ] E}
  (hA : Function.Injective A) (x : E) :
  NewtonLikeMap f A x = x ↔ f x = 0 := by
  -- Unfold the definition of NewtonLikeMap: T(x) = x - A(f(x))
  unfold NewtonLikeMap

  -- T(x) = x means x - A(f(x)) = x
  -- This is equivalent to A(f(x)) = 0
  calc
    x - A (f x) = x ↔ A (f x) = 0 := by
      constructor
      · intro h
        -- From x - A(f(x)) = x, subtract x from both sides
        have h_sub : x - (x - A (f x)) = x - x := by rw [h]
        calc
          A (f x)
            = x - (x - A (f x)) := by abel
          _ = x - x             := by rw [h_sub]
          _ = 0                 := by rw [sub_self x]
        -- linarith [h]
      · intro h
        -- From A(f(x)) = 0, we get x - 0 = x
        simp [h]
    _ ↔ f x = 0 := by
      -- Since A is injective, A(y) = 0 implies y = 0
      constructor
      · intro h
        -- A is a linear map, so A(0) = 0
        haveI : A 0 = 0 := map_zero A

        -- (1) We haveI `h : A (f x) = 0`. We want to show `A (f x) = A 0`.
        -- To do this, we first flip the equality `A 0 = 0` to `0 = A 0`.
        haveI : 0 = A 0 := this.symm

        -- (2) Now we chain the two equalities together.
        -- `h` gives us `A (f x) = 0`
        -- `this` gives us `0 = A 0`
        -- By transitivity of equality, we get `A (f x) = A 0`.
        haveI : A (f x) = A 0 := h.trans this

        -- (3) Apply the injectivity of A.
        -- `hA` is the hypothesis `Function.Injective A`.
        -- By definition, this means if `A y = A z`, then `y = z`.
        -- We apply `hA` to our proof `h_eq_A_zero` to conclude `f x = 0`.
        exact hA this

      · intro h
        -- If f(x) = 0, then A(f(x)) = A(0) = 0
        simp [h]

end Proposition_2_3_1



/-
================================================================================
NEUMANN SERIES THEOREM FOR INVERTIBILITY
================================================================================

This section proves that operators close to the identity are invertible,
with the inverse given by the Neumann series.

We break the proof into manageable lemmas, each handling one aspect.

Note: We assume `[Nontrivial E]` throughout this section since we're working
with operators on meaningful Banach spaces where Newton's method makes sense.
In practice, spaces like ℝⁿ (n ≥ 1), function spaces, etc. are all nontrivial.
-/
section NeumannSeries

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Nontrivial E]

omit [CompleteSpace E] in
/--
First fundamental lemma: The norm of the nth power of an operator is bounded by
the nth power of its norm. This is proved by induction using the submultiplicativity
of the operator norm.
-/
lemma norm_pow_le_pow_norm (X : E →L[ℝ] E) (n : ℕ) :
  ‖X ^ n‖ ≤ ‖X‖ ^ n := by
  induction n with
  | zero =>
    -- Base case: ‖X^0‖ = ‖I‖ = 1 = ‖X‖^0
    calc
      ‖X ^ 0‖
        -- Can I do rw here instead of simp???????
        = ‖ContinuousLinearMap.id ℝ E‖ := by simp [pow_zero]
      -- Since E is nontrivial, we have ‖I‖ = 1
      _ = 1                            := by rw [ContinuousLinearMap.norm_id]
      _ = ‖X‖ ^ 0                      := by rw [pow_zero]
      _ ≤ ‖X‖ ^ 0                      := by exact le_rfl

  | succ m _ =>
    -- Inductive step: use submultiplicativity ‖A B‖ ≤ ‖A‖ ‖B‖
    calc ‖X ^ (m + 1)‖ = ‖X ^ m * X‖ := by rw [pow_succ]
      _ ≤ ‖X ^ m‖ * ‖X‖ := by
        -- ContinuousLinearMap forms a normed algebra where norm is submultiplicative
        -- The standard lemma for this is norm_mul_le
        exact norm_mul_le (X ^ m) X
      _ ≤ ‖X‖ ^ m * ‖X‖ := by
        gcongr
      _ = ‖X‖ ^ (m + 1) := by
        rw [pow_succ]

omit [CompleteSpace E] in
/--
Second lemma: If ‖X‖ < 1, then the series ∑ ‖X^n‖ is summable.
This follows by comparison with the geometric series ∑ ‖X‖^n.
-/
lemma norm_series_summable_of_norm_lt_one {X : E →L[ℝ] E} (h : ‖X‖ < 1) :
  Summable (fun n : ℕ => ‖X ^ n‖) := by
  -- First, get the geometric series to converge
  -- Since ‖X‖ is a nonnegative real, we can use it directly
  haveI h_geometric : Summable (fun n : ℕ => (‖X‖ : ℝ) ^ n) := by
    -- Apply the geometric series test
    rw [summable_geometric_iff_norm_lt_one]
    -- ‖X‖ is already nonnegative, so ‖‖X‖‖ = ‖X‖
    simpa using h
  -- Now use comparison: ‖X^n‖ ≤ ‖X‖^n
  refine Summable.of_nonneg_of_le ?_ (norm_pow_le_pow_norm X) h_geometric
  -- Show each term is nonnegative (norms are always nonnegative)
  intro n
  exact norm_nonneg _

/--
Third lemma: If ‖X‖ < 1, then the operator series ∑ X^n is summable
in the Banach space of continuous linear maps.
This uses the completeness of the space.
-/
lemma operator_series_summable_of_norm_lt_one {X : E →L[ℝ] E} (h : ‖X‖ < 1) :
  Summable (fun n : ℕ => X ^ n) := by
  -- In a Banach space, absolute convergence implies convergence
  -- `Summable.of_norm` turns goal from `Summable (X^n)` to `Summable (‖X^n‖)`.
  apply Summable.of_norm
  exact norm_series_summable_of_norm_lt_one h

/--
Helper definition: The Neumann series sum S = ∑ X^n exists when ‖X‖ < 1.
This sum will be shown to be the inverse of (I - X).
-/
noncomputable def neumannSeriesSum {X : E →L[ℝ] E} (h : ‖X‖ < 1) : E →L[ℝ] E :=
  haveI : Summable (fun n : ℕ => X ^ n) := operator_series_summable_of_norm_lt_one h
  -- `∑' i, f i` is the sum of f if it exists and is unconditionally convergent, or 0 otherwise.
  ∑' n : ℕ, X ^ n


/--
Fourth lemma: The telescoping property from the left.
(I - X) ∘ (∑ X^n) = I when ‖X‖ < 1.

Mathematically, this works because:
  (I - X) ∘ (I + X + X² + ...)
  = I + X + X² + ... - X - X² - X³ - ...
  = I + (X - X) + (X² - X²) + ...
  = I

The formal proof requires showing we can distribute composition over the infinite sum
and that the series telescopes properly.
-/
lemma telescoping_left {X : E →L[ℝ] E} (h : ‖X‖ < 1) :
  (ContinuousLinearMap.id ℝ E - X).comp (neumannSeriesSum h) =
  ContinuousLinearMap.id ℝ E := by
  -- The calculation: (I - X) ∘ (I + X + X² + ...) = I
  -- This requires:
  -- 1. Distributing composition over infinite sum
  -- 2. Reindexing the series X + X² + X³ + ... as ∑_{n≥1} X^n
  -- 3. Showing the difference ∑_{n≥0} X^n - ∑_{n≥1} X^n = X^0 = I
  sorry

/--
Fifth lemma (currently incomplete): The telescoping property from the right.
(∑ X^n) ∘ (I - X) = I when ‖X‖ < 1.

Similar telescoping, but with composition from the other side.
-/
lemma telescoping_right {X : E →L[ℝ] E} (h : ‖X‖ < 1) :
  (neumannSeriesSum h).comp (ContinuousLinearMap.id ℝ E - X) =
  ContinuousLinearMap.id ℝ E := by
  -- Similar telescoping argument, but from the right
  sorry

/--
**Main Neumann Series Theorem**

If ‖I - B‖ < 1 for a continuous linear map B on a Banach space, then B is invertible.
The inverse is given by the Neumann series: B⁻¹ = ∑_{n=0}^∞ (I - B)^n.

This proof assembles the lemmas above into the complete result.
-/
lemma invertible_of_norm_sub_id_lt_one {B : E →L[ℝ] E}
  (h : ‖(ContinuousLinearMap.id ℝ E) - B‖ < 1) :
  ∃ (B_inv : E →L[ℝ] E),
    B.comp B_inv = ContinuousLinearMap.id ℝ E ∧
    B_inv.comp B = ContinuousLinearMap.id ℝ E := by

  -- Let X = I - B, so B = I - X with ‖X‖ < 1
  let X := ContinuousLinearMap.id ℝ E - B
  haveI hX_norm : ‖X‖ < 1 := h
  haveI hB_eq : B = ContinuousLinearMap.id ℝ E - X := by
    simp only [X]
    abel

  -- The series ∑ X^n converges by our lemma
  haveI h_summable := operator_series_summable_of_norm_lt_one hX_norm

  -- Define the inverse as the Neumann series sum
  use neumannSeriesSum hX_norm

  -- Now verify it's actually the inverse using our telescoping lemmas
  constructor
  · -- Left inverse property: B ∘ S = I
    rw [hB_eq]
    exact telescoping_left hX_norm

  · -- Right inverse property: S ∘ B = I
    rw [hB_eq]
    exact telescoping_right hX_norm

end NeumannSeries



/-
================================================================================
NONDEGENERACY AND INVERTIBILITY
================================================================================

Definition 2.3.2 (page 20): "A point x̃ ∈ U is a nondegenerate zero of f
if f(x̃) = 0 and Df(x̃) is invertible."

We need to establish when Df is invertible. A key lemma is that if
‖I - ADf(x̄)‖ < 1, then ADf(x̄) is invertible (used in proof of Theorem 2.4.2).
-/

/--
A point is a nondegenerate zero if it's a zero and the derivative is invertible.
-/
def IsNondegenerateZero (f : E → E) (x : E)
  [hf : DifferentiableAt ℝ f x] : Prop :=
  f x = 0 ∧ ∃ (Df_inv : E →L[ℝ] E),
    (fderiv ℝ f x).comp Df_inv = ContinuousLinearMap.id ℝ E ∧
    Df_inv.comp (fderiv ℝ f x) = ContinuousLinearMap.id ℝ E



/-
================================================================================
CONTRACTION PROPERTY OF THE NEWTON-LIKE MAP
================================================================================

From Section 2.3 (page 20): "If x̃ is a nondegenerate zero, then in a small
neighborhood of x̃, T is a contraction mapping with small contraction constant."

The key calculation is DT(x̃) = I - Df(x̃)⁻¹Df(x̃) = 0 at a zero.
-/

/--
The derivative of the Newton-like map T(x) = x - A(f(x)) is DT(x) = I - A∘Df(x).
-/
lemma deriv_newton_like_map {f : E → E} {A : E →L[ℝ] E} {x : E}
  (hf : DifferentiableAt ℝ f x) :
  fderiv ℝ (NewtonLikeMap f A) x = id - A.comp (fderiv ℝ f x) := by
  -- Use the chain rule and linearity of differentiation
  unfold NewtonLikeMap
  -- The derivative of x ↦ x - A(f(x)) is id - A ∘ Df
  calc fderiv ℝ (fun x => x - A (f x)) x
      = fderiv ℝ id x - fderiv ℝ (A ∘ f) x := by
        -- Derivative of difference is difference of derivatives
        sorry
    _ = id - A.comp (fderiv ℝ f x) := by
        -- fderiv of id is id, and chain rule for A ∘ f
        sorry

/-
================================================================================
MEAN VALUE INEQUALITY APPLICATION
================================================================================

From Corollary 2.2.6 and the proof of Theorem 2.4.1:
We use the mean value inequality to show T maps a ball into itself and is contractive.
-/

/--
A helper lemma that applies the mean value theorem specifically for our Newton map.
This bridges between the abstract derivative bounds and concrete distance estimates.
-/
lemma newton_map_lipschitz_on_ball
  {f : E → E} {A : E →L[ℝ] E} {xBar : E} {r Z_r : ℝ}
  (hf_diff : DifferentiableOn ℝ (NewtonLikeMap f A) (closedBall xBar r))
  (hZ : ∀ x ∈ closedBall xBar r, ‖fderiv ℝ (NewtonLikeMap f A) x‖ ≤ Z_r) :
  ∀ x y ∈ closedBall xBar r,
    ‖NewtonLikeMap f A x - NewtonLikeMap f A y‖ ≤ Z_r * ‖x - y‖ := by
  intros x hx y hy
  -- The closed ball is convex
  haveI h_convex : Convex ℝ (closedBall xBar r) := convex_closedBall xBar r
  -- Apply the mean value theorem on the convex set
  apply h_convex.norm_image_sub_le_of_norm_fderivWithin_le
  · exact hf_diff
  · intro z hz
    -- Convert fderivWithin to fderiv since we're on an open neighborhood
    rw [DifferentiableOn.fderivWithin_eq_fderiv (hf_diff)
        (isOpen_ball.mem_nhds _)] at hZ
    · exact hZ z hz
    · sorry -- Need to show z is in the interior for this conversion
  · exact hx
  · exact hy

/--
If T satisfies certain bounds, then it maps a closed ball into itself.
This is the key step in proving T has a fixed point via contraction mapping theorem.

The proof follows the structure from Theorem 2.4.1 (page 21) of the informal proof:
1. Start with ‖T(x) - x̄‖ and split using triangle inequality
2. Apply mean value inequality to bound ‖T(x) - T(x̄)‖
3. Use the bounds Y0 and Z_r to show the result is < r
-/
lemma newton_map_preserves_ball
  {f : E → E} {A : E →L[ℝ] E} {xBar : E} {r Y0 Z_r : ℝ}
  (hf_diff : DifferentiableOn ℝ (NewtonLikeMap f A) (closedBall xBar r))
  (hr : 0 < r)
  (hY0 : ‖NewtonLikeMap f A xBar - xBar‖ ≤ Y0)
  (hZ : ∀ x ∈ closedBall xBar r, ‖fderiv ℝ (NewtonLikeMap f A) x‖ ≤ Z_r)
  (hp : Z_r * r + Y0 < r) :
  MapsTo (NewtonLikeMap f A) (closedBall xBar r) (closedBall xBar r) := by
  -- Unpack what we need to prove: for any x in the ball, T(x) is also in the ball
  intro x hx
  rw [mem_closedBall] at hx ⊢

  -- Step 1: Apply triangle inequality to split ‖T(x) - x̄‖
  -- This is equation (2.19) in the informal proof
  calc ‖NewtonLikeMap f A x - xBar‖
      ≤ ‖NewtonLikeMap f A x - NewtonLikeMap f A xBar‖ +
        ‖NewtonLikeMap f A xBar - xBar‖ :=
          norm_sub_le _ _  -- Triangle inequality
    _ ≤ Z_r * ‖x - xBar‖ + Y0 := by
        apply add_le_add
        · -- First term: Apply our Lipschitz lemma
          exact newton_map_lipschitz_on_ball hf_diff hZ x hx xBar
            (mem_closedBall_self (le_of_lt hr))
        · -- Second term: Direct from hypothesis hY0
          exact hY0
    _ ≤ Z_r * r + Y0 := by
        -- Since x ∈ closedBall xBar r, we have ‖x - xBar‖ ≤ r
        gcongr
        exact hx
    _ < r := hp  -- This is our hypothesis that p(r) < 0 implies this inequality

/-
================================================================================
RADII POLYNOMIAL SETUP
================================================================================

From Theorem 2.4.2 (page 22): The radii polynomial approach with bounds Y0, Z0, Z2.
-/

/--
Radii polynomial data structure with the three key bounds.
Y0 bounds ‖Af(x̄)‖, Z0 bounds ‖I - ADf(x̄)‖, Z2 bounds the derivative variation.
-/
structure RadiiPolynomialData : Type where
  Y0 : ℝ  -- Bound on ‖Af(x̄)‖
  Z0 : ℝ  -- Bound on ‖I - ADf(x̄)‖
  Z2 : ℝ → ℝ  -- Bound on ‖A[Df(c) - Df(x̄)]‖/r for c ∈ B_r(x̄)
  Y0_nonneg : 0 ≤ Y0
  Z0_nonneg : 0 ≤ Z0
  Z2_nonneg : ∀ {r}, 0 < r → 0 ≤ Z2 r

namespace RadiiPolynomialData

/--
The combined bound Z(r) = Z₀ + Z₂(r)·r from equation (2.18).
-/
def Z_combined (data : RadiiPolynomialData) (r : ℝ) : ℝ :=
  data.Z0 + (data.Z2 r) * r

/--
The radii polynomial p(r) = Z₂(r)r² - (1 - Z₀)r + Y₀ from equation (2.17).
-/
def radiusPolynomial (data : RadiiPolynomialData) (r : ℝ) : ℝ :=
  (data.Z2 r) * r^2 - (1 - data.Z0) * r + data.Y0

/--
Alternative formulation: p(r) = (Z(r) - 1)r + Y₀.
This shows the connection to the contraction condition Z(r) < 1.
-/
lemma radiusPolynomial_rw (data : RadiiPolynomialData) (r : ℝ) :
  data.radiusPolynomial r = (data.Z_combined r - 1) * r + data.Y0 := by
  unfold radiusPolynomial Z_combined
  ring

/--
If p(r) < 0, then Z(r) < 1 (contraction) and the ball is mapped into itself.
-/
lemma radiusPolynomial_negative_implies_contraction
  {data : RadiiPolynomialData} {r : ℝ}
  (hr : 0 < r) (hp : data.radiusPolynomial r < 0) :
  data.Z_combined r < 1 ∧ data.Z_combined r * r + data.Y0 < r := by
  rw [radiusPolynomial_rw] at hp
  constructor
  · -- Prove Z(r) < 1
    haveI : (data.Z_combined r - 1) * r + data.Y0 < 0 := hp
    haveI : 0 ≤ data.Y0 := data.Y0_nonneg
    -- Since Y0 ≥ 0 and the sum is < 0, we need (Z(r) - 1) * r < 0
    haveI : (data.Z_combined r - 1) * r < 0 := by linarith
    -- Since r > 0, we need Z(r) - 1 < 0, hence Z(r) < 1
    haveI : data.Z_combined r - 1 < 0 := by
      -- Assume `Z(r) - 1 ≥ 0`
      by_contra h_not
      haveI : 0 ≤ data.Z_combined r - 1 := by linarith
      -- Then `(Z(r) - 1) * r ≥ 0` since `r > 0`.
      -- `this` is the immediate conclusion 0 ≤ data.Z_combined r - 1
      -- hr.le is `r ≤ 0` relaxed from `0 < r`
      haveI : 0 ≤ (data.Z_combined r - 1) * r := mul_nonneg this hr.le
      linarith
    linarith

  · -- Prove Z(r) * r + Y0 < r
    calc data.Z_combined r * r + data.Y0
        = (data.Z_combined r - 1) * r + r + data.Y0 := by ring
      _ = ((data.Z_combined r - 1) * r + data.Y0) + r := by ring
      _ < 0 + r := by linarith [hp]
      _ = r := by ring

end RadiiPolynomialData

/-
================================================================================
MAIN RADII POLYNOMIAL THEOREM (Theorem 2.4.2)
================================================================================

This is the main result that guarantees existence of a unique nondegenerate zero.
-/

/--
Main radii polynomial theorem for proving existence of nondegenerate zeros.
If the radii polynomial has a negative value at some r₀ > 0, then there exists
a unique zero x̃ in the ball B_r₀(x̄), and this zero is nondegenerate.
-/
theorem radii_polynomial_theorem
  {f : E → E} {xBar : E} {A : E →L[ℝ] E}
  (hf_diff : ∀ x, DifferentiableAt ℝ f x)
  (data : RadiiPolynomialData)
  -- The three key bounds from equations (2.14), (2.15), (2.16)
  (hY0 : ‖A (f xBar)‖ ≤ data.Y0)
  (hZ0 : ‖id - A.comp (fderiv ℝ f xBar)‖ ≤ data.Z0)
  (hZ2 : ∀ (c : E) (r : ℝ), c ∈ closedBall xBar r → 0 < r →
         ‖A.comp ((fderiv ℝ f c) - (fderiv ℝ f xBar))‖ ≤ data.Z2 r * r)
  -- If the polynomial is negative at some r₀
  {r0 : ℝ} (hr0_pos : 0 < r0)
  (hp_neg : data.radiusPolynomial r0 < 0) :
  -- Then there exists a unique nondegenerate zero in the ball
  ∃! (x_tilde : E), x_tilde ∈ closedBall xBar r0 ∧
                     IsNondegenerateZero f x_tilde := by
  -- Step 1: Show that T = NewtonLikeMap f A is a contraction on closedBall xBar r0

  -- From p(r₀) < 0, we get Z(r₀) < 1 and the self-mapping property
  obtain ⟨hZ_lt_one, hself_map⟩ :=
    data.radiusPolynomial_negative_implies_contraction hr0_pos hp_neg

  -- Step 2: Apply the Contraction Mapping Theorem
  -- We need to show:
  -- (a) T maps the ball into itself
  -- (b) T is a contraction with constant < 1
  -- (c) The ball is complete (follows from E being complete)

  sorry -- This requires assembling all the pieces with the contraction mapping theorem

/-
================================================================================
CONVERGENCE TO NEWTON'S METHOD
================================================================================

From Section 2.5 (mentioned in the user's request):
If x̃ is a zero, Df(x̃) is invertible, x̄ is sufficiently close to x̃,
and we have sufficient computational resources, then the radii polynomial
approach guarantees finding x̃.
-/

/--
If the initial guess is sufficiently close to a nondegenerate zero,
then the radii polynomial approach succeeds.
-/
theorem radii_success_near_nondegenerate_zero
  {f : E → E} {x_tilde xBar : E} {A : E →L[ℝ] E}
  (hf_diff : ∀ x, DifferentiableAt ℝ f x)
  (h_zero : IsNondegenerateZero f x_tilde)
  (hA_approx : ‖A - (fderiv ℝ f x_tilde).inverse‖ < ε)
  (h_close : ‖xBar - x_tilde‖ < δ)
  -- For sufficiently small ε and δ
  (hε : ε > 0) (hδ : δ > 0) (h_small : ε * δ < 1/4) :
  -- Then there exists r > 0 such that the radii polynomial is negative
  ∃ (r : ℝ) (data : RadiiPolynomialData),
    0 < r ∧
    data.radiusPolynomial r < 0 ∧
    x_tilde ∈ closedBall xBar r := by
  -- The proof follows from continuity arguments and the fact that
  -- at a nondegenerate zero, DT(x̃) = 0, making T a strong contraction nearby
  sorry

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting


open scoped Topology BigOperators
open Metric Set Filter ContinuousLinearMap


/-
Banach space setup: Type Class Hierarchy

We work in a Banach space E over ℝ, which is constructed from three type classes:

1. `NormedAddCommGroup E`:
   - E is an additive commutative group (E, +, 0, -)
   - Equipped with a norm ‖·‖ : E → ℝ≥0 satisfying:
     * ‖x‖ = 0 ⟺ x = 0                    (definiteness)
     * ‖-x‖ = ‖x‖                         (symmetry)
     * ‖x + y‖ ≤ ‖x‖ + ‖y‖                (triangle inequality)
   - The norm induces a metric: dist(x, y) = ‖x - y‖
   - This makes E a metric space

2. `NormedSpace ℝ E`:
   - E is a vector space over ℝ
   - The norm is compatible with scalar multiplication:
     * ‖α · x‖ = |α| · ‖x‖  for all α ∈ ℝ, x ∈ E  (homogeneity)
   - Combined with the above, this makes E a normed vector space

3. `CompleteSpace E`:
   - Every Cauchy sequence in E converges to a limit in E
   - Formally: ∀ (xₙ)ₙ∈ℕ, (∀ ε > 0, ∃ N, ∀ m,n ≥ N, ‖xₘ - xₙ‖ < ε)
                ⟹ (∃ x ∈ E, xₙ → x)
   - This completeness property is crucial for fixed point theorems

Result E is a *Banach space* over ℝ

This framework supports:
- Fréchet derivatives (via the norm structure)
- Fixed point theorems (via completeness)
- Mean Value Theorem (via the metric structure)
- Linear operator theory (via the vector space structure)
═══════════════════════════════════════════════════════════════════════════════
-/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def NewtonLikeMap (f : E → E) (A : E →L[ℝ] E) (x : E) : E := x - A (f x)

abbrev I := ContinuousLinearMap.id ℝ E


section NeumannSeries
theorem isUnit_of_norm_sub_id_lt_one_LEAN_built_in {B : E →L[ℝ] E}
  (h : ‖I - B‖ < 1) :
  IsUnit B := by
  have : B = I - (I - B) := by
    simp only [sub_sub_cancel]
  rw [this]
  /-
  lemma `isUnit_one_sub_of_norm_lt_one`
  {x : R} (h : ‖x‖ < 1) : IsUnit (1 - x)
  -/
  exact isUnit_one_sub_of_norm_lt_one h

/-- Alternative version with explicit inverse construction -/
theorem invertible_of_norm_sub_id_lt_one {B : E →L[ℝ] E}
  (h : ‖(1 : E →L[ℝ] E) - B‖ < 1) :
  ∃ (B_inv : E →L[ℝ] E),
    B * B_inv = 1 ∧ B_inv * B = 1 := by
  have hu := isUnit_of_norm_sub_id_lt_one_LEAN_built_in h
  obtain ⟨u, rfl⟩ := hu
  exact ⟨u.inv, u.val_inv, u.inv_val⟩

/-- Convert the multiplicative form to composition form for continuous linear maps -/
lemma invertible_comp_form {B : E →L[ℝ] E}
  (h : ‖I - B‖ < 1) :
  ∃ (B_inv : E →L[ℝ] E),
    B.comp B_inv = I ∧ B_inv.comp B = I := by
  obtain ⟨B_inv, h_left, h_right⟩ := invertible_of_norm_sub_id_lt_one h
  use B_inv
  constructor
  · ext x; exact congrFun (congrArg DFunLike.coe h_left) x
  · ext x; exact congrFun (congrArg DFunLike.coe h_right) x

end NeumannSeries



section Proposition_2_3_1

-- Omit `[CompleteSpace]` for this section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Proposition 2.3.1: Fixed points of Newton operator ⟺ Zeros of f

    Let T(x) = x - Af(x) be the Newton-like operator. If A : Y → X is an
    injective linear map, then:

    T(x) = x  ⟺  f(x) = 0

    This fundamental equivalence allows us to:
    - Convert fixed point problems (T(x) = x) to zero-finding problems (f(x) = 0)
    - Apply fixed point theorems (like Banach's) to find zeros of f

    This proposition is used twice in Theorem 2.4.2:
    1. To show the fixed point x̃ is a zero: T(x̃) = x̃ ⟹ f(x̃) = 0
    2. To establish uniqueness: f(z) = 0 ⟹ T(z) = z -/
lemma fixedPoint_injective_iff_zero
  {f : E → E} {A : E →L[ℝ] E}
  (hA : Function.Injective A)   -- A injective (NOT necessarily invertible!)
  (x : E) :
  NewtonLikeMap f A x = x ↔ f x = 0 := by
  -- Unfold T(x) = x - A(f(x))
  unfold NewtonLikeMap

  -- First equivalence: T(x) = x ⟺ A(f(x)) = 0
  -- T(x) = x means x - A(f(x)) = x, which simplifies to A(f(x)) = 0
  calc
    x - A (f x) = x ↔ A (f x) = 0 := by
      constructor
      · -- Forward direction: x - A(f(x)) = x ⟹ A(f(x)) = 0
        intro h
        -- Algebraic manipulation: x - A(f(x)) = x implies A(f(x)) = 0
        have h_sub : x - (x - A (f x)) = x - x := by rw [h]
        calc
          A (f x)
            = x - (x - A (f x)) := by abel  -- Rewrite using associativity
          _ = x - x             := by rw [h_sub]
          _ = 0                 := by rw [sub_self x]
      · -- Backward direction: A(f(x)) = 0 ⟹ x - A(f(x)) = x
        intro h
        -- If A(f(x)) = 0, then x - 0 = x
        simp [h]

    -- Second equivalence: A(f(x)) = 0 ⟺ f(x) = 0
    -- This is where injectivity of A is crucial
    _ ↔ f x = 0 := by
      constructor
      · -- Forward direction: A(f(x)) = 0 ⟹ f(x) = 0
        intro h
        -- Key fact: For linear maps, A(0) = 0
        haveI : A 0 = 0 := map_zero A

        -- Build the chain: A(f(x)) = 0 = A(0), so A(f(x)) = A(0)
        haveI : 0 = A 0 := this.symm
        haveI : A (f x) = A 0 := h.trans this

        -- Apply injectivity: A(f(x)) = A(0) ⟹ f(x) = 0
        -- This is the critical step requiring injectivity!
        exact hA this

      · -- Backward direction: f(x) = 0 ⟹ A(f(x)) = 0
        intro h
        -- If f(x) = 0, then A(f(x)) = A(0) = 0 by linearity
        simp [h]

end Proposition_2_3_1



section RadiiPolynomialTheorem
/-
================================================================================
THEOREM 2.4.2: Radii Polynomials in Finite Dimensions
================================================================================

From page 22 of the document:
"Consider f ∈ C^1(ℝ^n, ℝ^n). Let xBar ∈ ℝ^n and A ∈ M_n(ℝ). Let Y₀ and Z₀ be
non-negative constants and Z₂ : (0,∞) → [0,∞) be a non-negative function satisfying:
- ‖Af(xBar)‖ ≤ Y₀
- ‖I - ADf(xBar)‖ ≤ Z₀
- ‖A[Df(c) - Df(xBar)]‖ ≤ Z₂(r)r, for all c ∈ B_r(xBar)

Define p(r) = Z₂(r)r² - (1 - Z₀)r + Y₀

If there exists r₀ > 0 such that p(r₀) < 0, then there exists a unique xTilde ∈ B_{r₀}(xBar)
satisfying f(xTilde) = 0 and Df(xTilde) is invertible."
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The radii polynomial p(r) = Z₂(r)r² - (1 - Z₀)r + Y₀
    (Definition 2.4.3, eq. 2.17 from page 22) -/
def radiiPolynomial (Y₀ Z₀ : ℝ) (Z₂ : ℝ → ℝ) (r : ℝ) : ℝ :=
  Z₂ r * r^2 - (1 - Z₀) * r + Y₀

/-- Helper function: Z(r) = Z₀ + Z₂(r)·r
    (eq. 2.18 from page 22) -/
def Z_bound (Z₀ : ℝ) (Z₂ : ℝ → ℝ) (r : ℝ) : ℝ := Z₀ + Z₂ r * r

/-- Alternative formulation: p(r) = (Z(r) - 1)r + Y₀
    (Connecting eq. 2.17 and 2.18, used in Theorem 2.4.1) -/
lemma radiiPolynomial_alt_form (Y₀ Z₀ : ℝ) (Z₂ : ℝ → ℝ) (r : ℝ) :
  radiiPolynomial Y₀ Z₀ Z₂ r = (Z_bound Z₀ Z₂ r - 1) * r + Y₀ := by
  unfold radiiPolynomial Z_bound
  ring

-- set_option diagnostics true
/-- General radii polynomial for Theorem 2.4.1: p(r) = (Z(r) - 1)r + Y₀ -/
def generalRadiiPolynomial (Y₀ : ℝ) (Z : ℝ → ℝ) (r : ℝ) : ℝ :=
  (Z r - 1) * r + Y₀

/-- If p(r₀) < 0, then Z(r₀) < 1 (Equation 2.13)
    where p(r) = (Z(r) - 1)r + Y₀ is the general radii polynomial.

    This establishes a key implication for the general radii polynomial formulation
    used in Theorem 2.4.1:

    This is equation (2.13) or part of equation (2.18) in the informal proof. -/
lemma general_radii_poly_neg_implies_Z_lt_one
  {Y₀ : ℝ} {Z : ℝ → ℝ} {r₀ : ℝ}
  (hY₀ : 0 ≤ Y₀)                                    -- Y₀ ≥ 0 (from norm bound)
  (hr₀ : 0 < r₀)                                    -- r₀ > 0 (positive radius)
  (h_poly : generalRadiiPolynomial Y₀ Z r₀ < 0) :  -- p(r₀) < 0
  Z r₀ < 1 := by                                    -- Goal: Z(r₀) < 1

  -- Unfold definition: p(r₀) = (Z(r₀) - 1)·r₀ + Y₀ < 0
  unfold generalRadiiPolynomial at h_poly

  -- Expand: (Z(r₀) - 1)·r₀ + Y₀ = Z(r₀)·r₀ - r₀ + Y₀ < 0
  have h1 : Z r₀ * r₀ - r₀ + Y₀ < 0 := by linarith [h_poly]

  -- Rearrange: Z(r₀)·r₀ + Y₀ < r₀
  have h2 : Z r₀ * r₀ + Y₀ < r₀ := by linarith [h1]

  -- Since Y₀ ≥ 0, we get: Z(r₀)·r₀ < r₀ - Y₀ ≤ r₀
  have h3 : Z r₀ * r₀ < r₀ := by linarith [h2, hY₀]

  -- Divide both sides by r₀ > 0 to get Z(r₀) < 1
  -- Using: a·b < b ⟺ a < b/b = 1 when b > 0
  rw [← div_lt_one hr₀] at h3
  field_simp [ne_of_gt hr₀] at h3
  exact h3

section fold
omit [CompleteSpace E] in
/-- T maps the ball into itself in Theorem 2.4.1 -/
lemma general_maps_ball_to_itself
  {T : E → E} {xBar : E}
  {Y₀ : ℝ} {Z : ℝ → ℝ} {r₀ : ℝ}
  (hT_diff : Differentiable ℝ T)
  -- (hY₀ : 0 ≤ Y₀)
  (hr₀ : 0 < r₀)
  (h_bound_Y : ‖T xBar - xBar‖ ≤ Y₀)
  (h_bound_Z : ∀ c ∈ Metric.ball xBar r₀, ‖fderiv ℝ T c‖ ≤ Z r₀)
  (h_radii : generalRadiiPolynomial Y₀ Z r₀ < 0) :
  ∀ x ∈ Metric.ball xBar r₀, T x ∈ Metric.ball xBar r₀ := by
  intro x hx

  -- From p(r₀) < 0, we get Z(r₀) < 1 and Z(r₀) * r₀ + Y₀ < r₀
  -- have h_Z_lt_one : Z r₀ < 1 :=
  --   general_radii_poly_neg_implies_Z_lt_one hY₀ hr₀ h_radii

  -- Given that Z(r₀) * r₀ + Y₀ < r₀
  have h_sum_bound : Z r₀ * r₀ + Y₀ < r₀ := by
    unfold generalRadiiPolynomial at h_radii
    linarith [h_radii]

  -- The segment from xBar to x is in the ball
  have h_segment_in_ball : segment ℝ xBar x ⊆ Metric.ball xBar r₀ :=
    (convex_ball xBar r₀).segment_subset (mem_ball_self hr₀) hx

  -- Apply Mean Value Inequality
  /- `Convex.norm_image_sub_le_of_norm_fderiv_le`
  Let 𝐄 and 𝐆 be normed spaces over a real or complex normed field 𝕜,
  let 𝐒 be a convex subset of 𝐄. Suppose 𝐟 : 𝐄 → 𝐆 is differentiable at every point 𝑥 ∈ 𝐒 with derivative 𝑓′(𝑥) satisfying ‖𝑓′(𝑥)‖ ≤ 𝐶 for some constant 𝐶 ≥ 0. Then for any two points 𝑥, 𝑦 ∈ 𝐒, the following inequality holds:
  ∣𝑓(𝑥) - 𝑓(𝑦)∣ ≤ 𝐶 ∙ ∣𝑥 - 𝑦∣
  -/
  have h_mvt : ‖T x - T xBar‖ ≤ Z r₀ * ‖x - xBar‖ := by
    apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    · intros c hc
      exact hT_diff c
    · intros c hc
      exact h_bound_Z c (h_segment_in_ball hc)
    · apply convex_segment
    · apply left_mem_segment
    · apply right_mem_segment

  -- Triangle inequality to complete the proof
  rw [mem_ball, dist_eq_norm] at hx ⊢
  calc ‖T x - xBar‖
      = ‖(T x - T xBar) + (T xBar - xBar)‖ := by simp only [sub_add_sub_cancel]
    _ ≤ ‖T x - T xBar‖ + ‖T xBar - xBar‖ := norm_add_le _ _
    _ ≤ Z r₀ * ‖x - xBar‖ + Y₀ := by
        apply add_le_add
        · exact h_mvt
        · exact h_bound_Y
    _ ≤ Z r₀ * r₀ + Y₀ := by
        -- Cancels Y₀
        simp only [add_le_add_iff_right]
        have h_Z_nonneg : 0 ≤ Z r₀ := by
          haveI := h_bound_Z xBar (mem_ball_self hr₀)
          linarith [norm_nonneg (fderiv ℝ T xBar)]
        -- `le_of_lt hx` gives ‖x - xBar‖ < r₀
        -- `mul_le_mul_of_nonneg_left` requires Z(r₀) > 0 given by `h_Z_nonneg`
        exact mul_le_mul_of_nonneg_left (le_of_lt hx) h_Z_nonneg
    _ < r₀ := h_sum_bound
end fold

omit [CompleteSpace E] in
/-- T maps the closed ball into itself when the radii polynomial is negative

    This is a key step in Theorem 2.4.1 for applying the Banach fixed point theorem.

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
lemma general_maps_closedBall_to_itself
  {T : E → E} {xBar : E}
  {Y₀ : ℝ} {Z : ℝ → ℝ} {r₀ : ℝ}
  (hT_diff : Differentiable ℝ T)            -- T ∈ C¹(E,E)
  (hr₀ : 0 < r₀)                            -- r₀ > 0 (positive radius)
  (h_bound_Y : ‖T xBar - xBar‖ ≤ Y₀)        -- Initial displacement bound
  (h_bound_Z : ∀ c ∈ closedBall xBar r₀,    -- Derivative bound on B̄ᵣ₀(x̄)
    ‖fderiv ℝ T c‖ ≤ Z r₀)
  (h_Z_nonneg : 0 ≤ Z r₀)                   -- Z(r₀) ≥ 0 (needed for monotonicity)
  (h_radii : generalRadiiPolynomial Y₀ Z r₀ < 0) :  -- p(r₀) < 0
  MapsTo T (closedBall xBar r₀) (closedBall xBar r₀) := by
  intro x hx  -- Let x ∈ B̄ᵣ₀(x̄), show T(x) ∈ B̄ᵣ₀(x̄)

  -- From p(r₀) < 0, extract the key inequality: Z(r₀)·r₀ + Y₀ < r₀
  -- p(r₀) = (Z(r₀) - 1)·r₀ + Y₀ < 0 implies Z(r₀)·r₀ + Y₀ < r₀
  have h_sum_bound : Z r₀ * r₀ + Y₀ < r₀ := by
    unfold generalRadiiPolynomial at h_radii
    linarith [h_radii]

  -- The line segment [x̄, x] lies entirely in B̄ᵣ₀(x̄) by convexity
  -- This allows us to apply the Mean Value Theorem
  have h_segment : segment ℝ xBar x ⊆ closedBall xBar r₀ := by
    apply (convex_closedBall xBar r₀).segment_subset
    · exact mem_closedBall_self (le_of_lt hr₀)  -- x̄ ∈ B̄ᵣ₀(x̄)
    · exact hx                                   -- x ∈ B̄ᵣ₀(x̄)

  -- Mean Value Theorem: ‖T(x) - T(x̄)‖ ≤ sup_{c ∈ [x̄,x]} ‖DT(c)‖ · ‖x - x̄‖
  -- Since ‖DT(c)‖ ≤ Z(r₀) for all c ∈ B̄ᵣ₀(x̄) ⊇ [x̄, x]:
  -- ‖T(x) - T(x̄)‖ ≤ Z(r₀) · ‖x - x̄‖
  have h_mvt : ‖T x - T xBar‖ ≤ Z r₀ * ‖x - xBar‖ := by
    apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    · intros c hc
      exact hT_diff c                   -- T is differentiable
    · intros c hc
      exact h_bound_Z c (h_segment hc)  -- ‖DT(c)‖ ≤ Z(r₀) on segment
    · apply convex_segment              -- [x̄, x] is convex
    · apply left_mem_segment            -- x̄ ∈ [x̄, x]
    · apply right_mem_segment           -- x ∈ [x̄, x]

  -- Now show ‖T(x) - x̄‖ ≤ r₀ using triangle inequality and the bounds
  rw [mem_closedBall, dist_eq_norm] at hx ⊢
  calc ‖T x - xBar‖
      -- Decompose: T(x) - x̄ = (T(x) - T(x̄)) + (T(x̄) - x̄)
      = ‖(T x - T xBar) + (T xBar - xBar)‖ := by simp only [sub_add_sub_cancel]
    -- Triangle inequality: ‖a + b‖ ≤ ‖a‖ + ‖b‖
    _ ≤ ‖T x - T xBar‖ + ‖T xBar - xBar‖ := norm_add_le _ _
    -- Apply MVT bound and Y₀ bound
    _ ≤ Z r₀ * ‖x - xBar‖ + Y₀ := add_le_add h_mvt h_bound_Y
    -- Since ‖x - x̄‖ ≤ r₀ and Z(r₀) ≥ 0: Z(r₀)·‖x - x̄‖ ≤ Z(r₀)·r₀
    _ ≤ Z r₀ * r₀ + Y₀ := by
        apply add_le_add_right
        exact mul_le_mul_of_nonneg_left (hx) h_Z_nonneg
    -- Apply the key inequality from p(r₀) < 0
    _ ≤ r₀ := le_of_lt h_sum_bound

/-- Closed balls in complete spaces are complete

    If E is a complete normed space (i.e., a Banach space), then every
    closed ball B̄ᵣ(x) = {y ∈ E : ‖y - x‖ ≤ r} is a complete metric subspace.

    This lemma is crucial for applying the Banach fixed point theorem
    (Theorem 2.4.1), which requires the domain to be a complete metric space. -/
lemma isComplete_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (x : E) (r : ℝ) :
  IsComplete (closedBall x r : Set E) := by
  -- Closed subsets of complete spaces are complete
  apply IsClosed.isComplete
  -- The closed ball is indeed closed in the norm topology
  exact isClosed_closedBall

/-- Extended distance is finite in normed spaces

    In any normed space, the extended distance edist : E → E → ℝ≥0∞ between
    any two points is *finite* (i.e., not ⊤ = ∞).

    This lemma is needed for applying the Banach fixed point theorem
    (ContractingWith.exists_fixedPoint'), which requires edist to be finite
    to ensure the iteration sequence is well-defined. -/
lemma edist_ne_top_of_normed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) :
  edist x y ≠ ⊤ := by
  -- In a (pseudo)metric space, edist is defined via the ordinary distance:
  -- edist x y = ENNReal.ofReal (dist x y)
  rw [edist_dist]
  -- ENNReal.ofReal : ℝ → ℝ≥0∞ maps to [0, ∞), never to ⊤ = ∞
  exact ENNReal.ofReal_ne_top

/-- **Theorem 2.4.1**: Radii Polynomial Fixed Point Theorem

    Let T ∈ C¹(E, E) where E is a Banach space. Suppose:
    - ‖T(x̄) - x̄‖ ≤ Y₀
    - ‖DT(c)‖ ≤ Z(r) for all c ∈ B̄ᵣ(x̄) and all r > 0
    - p(r₀) < 0 where p(r) = (Z(r) - 1)r + Y₀

    Then there exists a unique fixed point x̃ ∈ B̄_{r₀}(x̄) with T(x̃) = x̃ -/
theorem general_radii_polynomial_theorem
  {T : E → E} {xBar : E}
  {Y₀ : ℝ} {Z : ℝ → ℝ} {r₀ : ℝ}
  (hT_diff : Differentiable ℝ T)
  (hr₀ : 0 < r₀)
  (h_bound_Y : ‖T xBar - xBar‖ ≤ Y₀)
  (h_bound_Z : ∀ c ∈ Metric.closedBall xBar r₀, ‖fderiv ℝ T c‖ ≤ Z r₀)
  (h_radii : generalRadiiPolynomial Y₀ Z r₀ < 0) :
  ∃! xTilde ∈ Metric.closedBall xBar r₀, T xTilde = xTilde := by

  -- Need Y₀ ≥ 0 for the polynomial argument
  have hY₀ : 0 ≤ Y₀ := by
    calc 0 ≤ ‖T xBar - xBar‖ := norm_nonneg _
         _ ≤ Y₀ := h_bound_Y

  -- p(r₀) < 0 ⇒ Z(r₀) < 1
  have h_Z_lt_one : Z r₀ < 1 :=
    general_radii_poly_neg_implies_Z_lt_one hY₀ hr₀ h_radii

  have h_Z_nonneg : 0 ≤ Z r₀ := by
    have := h_bound_Z xBar (mem_closedBall_self (le_of_lt hr₀))
    exact le_trans (norm_nonneg _) this

  -- T maps the closed ball into itself
  have h_maps : MapsTo T (closedBall xBar r₀) (closedBall xBar r₀) :=
    general_maps_closedBall_to_itself hT_diff hr₀ h_bound_Y h_bound_Z h_Z_nonneg h_radii

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

  -- The closed ball is complete (closed subsets of complete spaces are complete)
  have h_complete : IsComplete (closedBall xBar r₀ : Set E) :=
    isComplete_closedBall xBar r₀

  -- Construct the restriction of T to the closed ball
  let T_restr : closedBall xBar r₀ → closedBall xBar r₀ :=
    h_maps.restrict T (closedBall xBar r₀) (closedBall xBar r₀)

  -- Show the restriction is ContractingWith Z(r₀)
  let K : NNReal := ⟨Z r₀, h_Z_nonneg⟩
  have h_contracting_restr : ContractingWith K T_restr := by
    constructor
    · -- Z(r₀) < 1
      show (K : ℝ) < 1
      exact h_Z_lt_one
    · -- Lipschitz condition for the restriction
      intro ⟨x, hx⟩ ⟨y, hy⟩
      simp only [T_restr, MapsTo.restrict, edist_dist, K]
      -- Key: show that the NNReal coercion equals ENNReal.ofReal
      -- ↑K ≃ (↑(⟨Z r₀, h_Z_nonneg⟩ : NNReal) : ENNReal)
      have h_coe : (↑K : ENNReal) = ENNReal.ofReal (Z r₀) := by
        rw [ENNReal.ofReal]
        congr 1
        exact (Real.toNNReal_of_nonneg h_Z_nonneg).symm
      rw [h_coe]
      rw [← ENNReal.ofReal_mul h_Z_nonneg]
      rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg h_Z_nonneg dist_nonneg)]
      exact h_contracting_on_ball x y hx hy

  -- Apply Banach Fixed Point Theorem:
  /-
  theorem `ContractingWith.fixedPoint_unique'`
  {α : Type u_1} [MetricSpace α] {K : NNReal} {f : α → α}
  (hf : ContractingWith K f) {x y : α} (hx : Function.IsFixedPt f x) (hy : Function.IsFixedPt f y) :
  x = y
  -/
  have ⟨xTilde_sub, hxTilde_mem, hxTilde_fixed, _⟩ :=
    ContractingWith.exists_fixedPoint' h_complete h_maps h_contracting_restr
      (mem_closedBall_self (le_of_lt hr₀))
      (edist_ne_top_of_normed xBar (T_restr ⟨xBar, mem_closedBall_self (le_of_lt hr₀)⟩))
  -- Alternatively:
  -- Note: xTilde_sub has type (closedBall xBar r₀), a subtype element
  -- have xBar_in_ball : xBar ∈ closedBall xBar r₀ :=
  --   mem_closedBall_self (le_of_lt hr₀)
  -- have ⟨xTilde_sub, hxTilde_mem, hxTilde_fixed, _⟩ :=
  --   ContractingWith.exists_fixedPoint' h_complete h_maps h_contracting_restr
  --     (mem_closedBall_self (le_of_lt hr₀))
  --     (edist_ne_top_of_normed _ _)

  -- Lift the fixed point from the closed ball to E
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
  haveI : (⟨z, hz_mem⟩ : closedBall xBar r₀) = ⟨xTilde_sub, hxTilde_mem⟩ :=
    h_contracting_restr.fixedPoint_unique' hz_fixed_restr hxTilde_fixed_restr
  -- Extract the underlying equality
  exact congrArg Subtype.val this


/-- Radii polynomial negativity implies Z(r₀) < 1

    This establishes equation (2.18) from Theorem 2.4.2:

    p(r₀) < 0  ⟺  Z(r₀) < 1 - Y₀/r₀  ⟹  Z(r₀) < 1

    where:
    - p(r) = Z₂(r)r² - (1-Z₀)r + Y₀  (eq. 2.17, definition of radii polynomial)
    - Z(r) = Z₀ + Z₂(r)·r             (eq. 2.18, definition of Z_bound)
    - p(r) = (Z(r) - 1)r + Y₀         (alternative formulation connecting the two) -/
lemma radii_poly_neg_implies_Z_bound_lt_one
  {Y₀ Z₀ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
  (hY₀ : 0 ≤ Y₀)                                    -- Y₀ ≥ 0 (from norm bound)
  (hr₀ : 0 < r₀)                                    -- r₀ > 0 (positive radius)
  (h_poly : radiiPolynomial Y₀ Z₀ Z₂ r₀ < 0) :      -- p(r₀) < 0 (eq. 2.17)
  Z_bound Z₀ Z₂ r₀ < 1 := by                        -- Goal: Z(r₀) < 1 (eq. 2.18)

  -- Use the alternative formulation: p(r) = (Z(r) - 1)r + Y₀
  -- This connects the radii polynomial to the Z_bound
  rw [radiiPolynomial_alt_form] at h_poly

  -- From p(r₀) < 0, we have: (Z(r₀) - 1)·r₀ + Y₀ < 0
  -- Rearranging: (Z(r₀) - 1)·r₀ < -Y₀ ≤ 0
  have h_prod_neg : (Z_bound Z₀ Z₂ r₀ - 1) * r₀ < 0 := by
    linarith [h_poly, hY₀]

  -- Since r₀ > 0 and (Z(r₀) - 1)·r₀ < 0, we must have Z(r₀) - 1 < 0
  -- Proof by contradiction: if Z(r₀) - 1 ≥ 0, then the product would be ≥ 0
  have h_Z_minus_one : Z_bound Z₀ Z₂ r₀ - 1 < 0 := by
    by_contra h_not
    -- Assume for contradiction that Z(r₀) - 1 ≥ 0
    have h_nonneg : 0 ≤ Z_bound Z₀ Z₂ r₀ - 1 := by linarith
    -- Then (Z(r₀) - 1)·r₀ ≥ 0 since both factors are non-negative
    have h_prod_nonneg : 0 ≤ (Z_bound Z₀ Z₂ r₀ - 1) * r₀ :=
      mul_nonneg h_nonneg (le_of_lt hr₀)
    -- But this contradicts (Z(r₀) - 1)·r₀ < 0
    linarith [h_prod_neg]

  -- From Z(r₀) - 1 < 0, we conclude Z(r₀) < 1
  linarith

omit [CompleteSpace E] in
/-- Newton operator Y₀ bound: ‖T(x̄) - x̄‖ ≤ Y₀

    This reformulates equation (2.14) for the Newton-like operator.

    This bound is used in Theorem 2.4.1 to verify the first condition
    for the contraction mapping theorem. -/
lemma newton_operator_Y_bound
  {f : E → E} {xBar : E} {A : E →L[ℝ] E} {Y₀ : ℝ}
  (h_bound : ‖A (f xBar)‖ ≤ Y₀) :                              -- eq. 2.14
  let T := NewtonLikeMap f A
  ‖T xBar - xBar‖ ≤ Y₀ := by
  unfold NewtonLikeMap
  -- T(x̄) - x̄ = (x̄ - A(f(x̄))) - x̄ = -A(f(x̄))
  simp only [sub_sub_cancel_left, norm_neg]
  -- ‖T(x̄) - x̄‖ = ‖-A(f(x̄))‖ = ‖A(f(x̄))‖ ≤ Y₀
  exact h_bound

section fold
-- omit [CompleteSpace E] in
-- /-- Helper lemma: Composition of continuous linear map with differentiable function is differentiable -/
-- lemma comp_clm_differentiable
--   {f : E → E} {A : E →L[ℝ] E}
--   (hf : Differentiable ℝ f) :
--   Differentiable ℝ (fun x => A (f x)) := by
--   -- A is differentiable as a continuous linear map
--   have hA : Differentiable ℝ A := A.differentiable
--   -- Composition is differentiable
--   exact hA.comp hf
end fold

omit [CompleteSpace E] in
/-- Derivative of the Newton-like operator

    For T(x) = x - Af(x), we compute:
    DT(x) = D(x) - D(Af(x)) = I - A∘Df(x)

    This formula is used throughout the proof, particularly in establishing
    the derivative bound ‖DT(c)‖ ≤ Z(r₀) (equations 2.19-2.20). -/
lemma newton_operator_fderiv
  {f : E → E} {A : E →L[ℝ] E} {x : E}
  (hf_diff : Differentiable ℝ f) :
  fderiv ℝ (NewtonLikeMap f A) x = I - A.comp (fderiv ℝ f x) := by
  unfold NewtonLikeMap

  -- Step 1: D(x) = I (derivative of identity map)
  have h1 : fderiv ℝ (fun x => x) x = I := fderiv_id'

  -- Step 2: D(A(f(x))) = A∘Df(x) by chain rule
  -- Since A is linear: D_y[A](y) = A for all y
  -- By chain rule: D[A ∘ f](x) = D[A](f(x)) ∘ Df(x) = A ∘ Df(x)
  have h2 : fderiv ℝ (fun x => A (f x)) x = A.comp (fderiv ℝ f x) := by
    have : (fun x => A (f x)) = A ∘ f := rfl
    rw [this, fderiv_comp]
    · -- For continuous linear map A: D[A](y) = A
      rw [ContinuousLinearMap.fderiv]
    · -- A is differentiable everywhere (continuous linear)
      exact A.differentiableAt
    · -- f is differentiable at x (hypothesis)
      exact hf_diff.differentiableAt

  -- Step 3: D(g - h) = Dg - Dh (linearity of Fréchet derivative)
  have h_sub : fderiv ℝ (fun x => x - A (f x)) x =
      fderiv ℝ (fun x => x) x - fderiv ℝ (fun x => A (f x)) x := by
    apply fderiv_sub differentiableAt_id
    exact A.differentiableAt.comp x hf_diff.differentiableAt

  -- Combine: DT(x) = D(x) - D(Af(x)) = I - A∘Df(x)
  rw [h_sub, h1, h2]

omit [CompleteSpace E] in
/-- Newton operator derivative bound on closed ball

    ‖DT(c)‖ ≤ Z₀ + Z₂(r)·r  for all c ∈ B̄ᵣ(x̄)

    This combines two separate bounds from Theorem 2.4.2:
    - Equation (2.15): ‖I - A·Df(x̄)‖ ≤ Z₀            (bound at center x̄)
    - Equation (2.16): ‖A·[Df(c) - Df(x̄)]‖ ≤ Z₂(r)·r  (Lipschitz-type bound)

    to produce equation (2.19)-(2.20):
    ‖DT(c)‖ = ‖I - A·Df(c)‖ ≤ Z₀ + Z₂(r)·r ≙ Z(r)

    This bound is crucial for showing T is a contraction with constant Z(r) < 1. -/
lemma newton_operator_derivative_bound_closed
  {f : E → E} {xBar : E} {A : E →L[ℝ] E}
  {Z₀ : ℝ} {Z₂ : ℝ → ℝ} {r : ℝ}
  (hf_diff : Differentiable ℝ f)                                   -- f ∈ C¹(E,E)
  (h_Z₀ : ‖I - A.comp (fderiv ℝ f xBar)‖ ≤ Z₀)                     -- eq. 2.15: ‖I - A·Df(x̄)‖ ≤ Z₀
  (h_Z₂ : ∀ c ∈ Metric.closedBall xBar r,                          -- eq. 2.16: For c ∈ B̄ᵣ(x̄):
    ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖ ≤ Z₂ r * r)          --   ‖A·[Df(c) - Df(x̄)]‖ ≤ Z₂(r)·r
  (c : E) (hc : c ∈ Metric.closedBall xBar r) :
  ‖fderiv ℝ (NewtonLikeMap f A) c‖ ≤ Z_bound Z₀ Z₂ r := by         -- Goal: ‖DT(c)‖ ≤ Z(r) = Z₀ + Z₂(r)·r
  unfold Z_bound  -- Z(r) := Z₀ + Z₂(r)·r

  -- Use the derivative formula: DT(c) = I - A·Df(c)
  rw [newton_operator_fderiv hf_diff]

  -- The key decomposition technique (adding and subtracting A·Df(x̄)):
  -- I - A·Df(c) = I - A·Df(x̄) + A·Df(x̄) - A·Df(c)
  --             = [I - A·Df(x̄)] + A·[Df(x̄) - Df(c)]
  --
  -- This splits the derivative into:
  -- 1. A "center term" [I - A·Df(x̄)] bounded by Z₀ (eq. 2.15)
  -- 2. A "variation term" A·[Df(x̄) - Df(c)] bounded by Z₂(r)·r (eq. 2.16)

  calc ‖I - A.comp (fderiv ℝ f c)‖
      -- Step 1: Decompose using A·Df(x̄) as a "pivot"
      -- I - A·Df(c) = [I - A·Df(x̄) + A·Df(x̄)] - A·Df(c)
      --             = [I - A·Df(x̄)] + [A·Df(x̄) - A·Df(c)]
      = ‖I - A.comp (fderiv ℝ f xBar) + A.comp (fderiv ℝ f xBar - fderiv ℝ f c)‖ := by
        -- Algebraic identity: comp is linear, so A∘(B - C) = A∘B - A∘C
        simp only [comp_sub, sub_add_sub_cancel]

    -- Step 2: Apply triangle inequality ‖a + b‖ ≤ ‖a‖ + ‖b‖
    _ ≤ ‖I - A.comp (fderiv ℝ f xBar)‖ + ‖A.comp (fderiv ℝ f xBar - fderiv ℝ f c)‖ :=
        norm_add_le _ _

    -- Step 3: Apply both bounds from hypotheses
    -- First term: ‖I - A·Df(x̄)‖ ≤ Z₀ by eq. 2.15
    -- Second term: ‖A·[Df(x̄) - Df(c)]‖ ≤ Z₂(r)·r by eq. 2.16
    _ ≤ Z₀ + Z₂ r * r := by
        apply add_le_add h_Z₀                      -- Apply first bound
        -- For the second term, need to flip Df(x̄) - Df(c) to Df(c) - Df(x̄)
        -- to match the form in hypothesis h_Z₂
        have : fderiv ℝ f xBar - fderiv ℝ f c = -(fderiv ℝ f c - fderiv ℝ f xBar) := by
          abel  -- Algebraic manipulation: a - b = -(b - a)
        -- Use norm symmetry: ‖-v‖ = ‖v‖ and linearity: A∘(-B) = -(A∘B)
        rw [this, ContinuousLinearMap.comp_neg, norm_neg]
        -- Apply second bound (eq. 2.16)
        exact h_Z₂ c hc

omit [CompleteSpace E] in
/-- Helper lemma: If A is injective and A∘B is surjective, then B is surjective -/
lemma injective_of_comp_injective
  {A : E →L[ℝ] E} {B : E →L[ℝ] E}
  (h_comp_inj : Function.Injective (A.comp B)) :
  Function.Injective B := by
  intro x y hxy
  have : A (B x) = A (B y) := by rw [hxy]
  exact h_comp_inj this

omit [CompleteSpace E] in
/-- Helper lemma: Surjectivity from composition -/
lemma surjective_of_comp_surjective_left
  {A : E →L[ℝ] E} {B : E →L[ℝ] E}
  (hA : Function.Injective A)
  (h_comp_surj : Function.Surjective (A.comp B)) :
  Function.Surjective B := by
  intro y
  obtain ⟨x, hx⟩ := h_comp_surj (A y)
  use x
  exact hA hx

/-- Bijectivity from composition with injective map

    If A is injective and ‖I - A∘B‖ < 1, then B is bijective.

    This is a key algebraic lemma for the radii polynomial theorem. It allows us to
    deduce that Df(x̃) is bijective (hence invertible) from:
    - A is injective (our weakened assumption)
    - ‖I - A∘Df(x̃)‖ < 1 (from the radii polynomial condition)

    Proof structure:
    1. ‖I - A∘B‖ < 1 ⟹ A∘B is invertible (given by Neumann series)
       Get (A∘B)⁻¹ with (A∘B)∘(A∘B)⁻¹ = I and (A∘B)⁻¹∘(A∘B) = I

    2. Having a two-sided inverse ⟹ A∘B is bijective
       - Right inverse ⟹ injective
       - Left inverse ⟹ surjective

    3. Use Mathlib composition lemmas:
       - A injective + A∘B injective ⟹ B injective
         (`Injective (f ∘ g) ↔ Injective g` when f injective)
       - A injective + A∘B surjective ⟹ B surjective
         (`Surjective (f ∘ g) + Injective f ⟹ Surjective g`)

    This avoids requiring A to be invertible, which would need finite dimensions. -/
lemma bijective_of_comp_and_injective
  {A B : E →L[ℝ] E}
  (hA : Function.Injective A)          -- A is injective (only assumption on A!)
  (h_norm : ‖I - A.comp B‖ < 1) :     -- ‖I - A∘B‖ < 1 (near identity)
  Function.Bijective B := by          -- Goal: B is bijective

  -- From ‖I - A∘B‖ < 1, the Neumann series converges:
  -- (A∘B)⁻¹ = I + (I - A∘B) + (I - A∘B)² + (I - A∘B)³ + ...
  -- This gives us a two-sided inverse
  -- where: (A∘B) ∘ AB_inv = I  (left inverse, eq h_left)
  --        AB_inv ∘ (A∘B) = I  (right inverse, eq h_right)
  obtain ⟨AB_inv, h_left, h_right⟩ := invertible_comp_form h_norm


  -- Step 2: Convert continuous linear map equalities to function equalities
  -- Need to work with coerced functions (⇑A ∘ ⇑B) rather than A.comp B
  -- Right inverse for functions: AB_inv((A∘B)(x)) = x for all x
  have h_right_inv : Function.RightInverse (⇑A ∘ ⇑B) ⇑AB_inv := by
    intro x
    -- Extract pointwise equality from composition equality
    have := congrFun (congrArg DFunLike.coe h_right) x
    simp at this
    exact this

  -- Left inverse for functions: (A∘B)(AB_inv(y)) = y for all y
  have h_left_inv : Function.LeftInverse (⇑A ∘ ⇑B) ⇑AB_inv := by
    intro y
    -- Extract pointwise equality from composition equality
    have := congrFun (congrArg DFunLike.coe h_left) y
    simp at this
    exact this

  -- A∘B is bijective (from having a two-sided inverse)
  -- Mathlib theorems:
  -- - `Function.RightInverse.injective`: Right inverse ⟹ injective
  -- - `Function.LeftInverse.surjective`: Left inverse ⟹ surjective

  have h_AB_inj : Function.Injective (⇑A ∘ ⇑B) := h_right_inv.injective
  have h_AB_surj : Function.Surjective (⇑A ∘ ⇑B) := h_left_inv.surjective

  -- Deduce B is bijective from A injective and A∘B bijective
  constructor
  · -- B is injective
    -- Mathlib theorem: `Injective (f ∘ g) ↔ Injective g` when f is injective
    -- Since A is injective and A∘B is injective, B must be injective
    exact (hA.of_comp_iff ⇑B).mp h_AB_inj

  · -- B is surjective
    -- Mathlib theorem: `Surjective (f ∘ g) + Injective f ⟹ Surjective g`
    -- If A∘B is surjective and A is injective, then B must be surjective
    -- Proof: For any y, since A∘B surjective, ∃x: (A∘B)(x) = A(g(x)) for some g(x)
    --        But we need to show ∃z: B(z) = y
    --        Take some v with A(v) = A(B(x)), then by injectivity v = B(x)
    exact h_AB_surj.of_comp_left hA

/-- Construct the inverse of Df(x̃) from the inverse of A∘Df(x̃) and injectivity of A

    Key insight: If A is injective and A∘B is invertible with inverse (A∘B)⁻¹,
    then B⁻¹ = (A∘B)⁻¹ ∘ A is a two-sided inverse of B.

    This avoids the "too strong" assumption that A is invertible, as mentioned
    in the informal proof commentary. -/
lemma construct_derivative_inverse
  {A : E →L[ℝ] E} {B : E →L[ℝ] E}
  (hA_inj : Function.Injective A)
  (h_norm : ‖I - A.comp B‖ < 1) :             -- ‖I - A∘B‖ < 1
  B.IsInvertible := by
  -- By Exercise 2.7.1 (Neumann series), A∘B is invertible
  obtain ⟨inv_AB, h_left, h_right⟩ := invertible_comp_form h_norm
  -- where (A∘B) ∘ inv_AB = I and inv_AB ∘ (A∘B) = I

  -- Construct B⁻¹ = inv_AB ∘ A
  let B_inv := inv_AB.comp A

  -- Left inverse: B(B⁻¹(x)) = B((inv_AB ∘ A)(x)) = x
  have h_inv_left : ∀ x, B (B_inv x) = x := by
    intro x
    -- Apply (A∘B) ∘ inv_AB = I to A(x)
    have h1 : A (B (inv_AB (A x))) = A x := by
      have := congrFun (congrArg DFunLike.coe h_left) (A x)
      simp at this
      exact this
    -- Use injectivity of A to cancel
    exact hA_inj h1

  -- Right inverse: B⁻¹(B(x)) = (inv_AB ∘ A)(B(x)) = inv_AB((A∘B)(x)) = x
  have h_inv_right : ∀ x, B_inv (B x) = x := by
    intro x
    -- Apply inv_AB ∘ (A∘B) = I to x
    have := congrFun (congrArg DFunLike.coe h_right) x
    simp at this
    exact this

  -- Package as ContinuousLinearEquiv
  use ContinuousLinearEquiv.equivOfInverse B B_inv h_inv_right h_inv_left
  rfl

section fold
-- omit [CompleteSpace E] in
-- /-- If the radii polynomial is negative, then ‖I - A∘Df(x̄)‖ < 1

--     This establishes equation (2.18): p(r₀) < 0 ⟹ Z(r₀) < 1
--     which in turn implies ‖I - ADf(x̄)‖ ≤ Z₀ ≤ Z(r₀) < 1 -/
-- lemma radii_implies_norm_lt_one
--   {A : E →L[ℝ] E} {f : E → E} {xBar : E} {Y₀ Z₀ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
--   (hr₀ : 0 < r₀)
--   (h_Y₀ : ‖A (f xBar)‖ ≤ Y₀)                                   -- eq. 2.14
--   (h_Z₀ : ‖I - A.comp (fderiv ℝ f xBar)‖ ≤ Z₀)                 -- eq. 2.15
--   (h_Z₂ : ∀ c ∈ Metric.closedBall xBar r₀,
--     ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖ ≤ Z₂ r₀ * r₀)   -- eq. 2.16
--   (h_radii : radiiPolynomial Y₀ Z₀ Z₂ r₀ < 0) :               -- eq. 2.17: p(r₀) < 0
--   ‖I - A.comp (fderiv ℝ f xBar)‖ < 1 := by
--   -- Y₀ ≥ 0 automatically from ‖A(f(x̄))‖ ≤ Y₀
--   have hY₀_nonneg : 0 ≤ Y₀ := by
--     calc 0 ≤ ‖A (f xBar)‖ := norm_nonneg _
--          _ ≤ Y₀ := h_Y₀

--   -- Z₂(r₀)·r₀ ≥ 0 from eq. 2.16 at c = x̄
--   have h_Z₂_nonneg : 0 ≤ Z₂ r₀ * r₀ := by
--     have := h_Z₂ xBar (mem_closedBall_self (le_of_lt hr₀))
--     simp only [sub_self] at this
--     simpa using this

--   -- eq. 2.18: p(r₀) < 0 ⟹ Z(r₀) = Z₀ + Z₂(r₀)·r₀ < 1
--   have h_Z_lt_one : Z_bound Z₀ Z₂ r₀ < 1 :=
--     radii_poly_neg_implies_Z_bound_lt_one hY₀_nonneg hr₀ h_radii

--   -- Chain of inequalities: ‖I - A·Df(x̄)‖ ≤ Z₀ ≤ Z(r₀) < 1
--   calc ‖I - A.comp (fderiv ℝ f xBar)‖
--       ≤ Z₀ := h_Z₀                            -- by eq. 2.15
--     _ ≤ Z₀ + Z₂ r₀ * r₀ := by linarith [h_Z₂_nonneg]
--     _ = Z_bound Z₀ Z₂ r₀ := rfl               -- definition of Z(r₀)
--     _ < 1 := h_Z_lt_one                       -- by eq. 2.18
end fold

omit [CompleteSpace E] in
/-- The Newton operator derivative bound at x̃ follows from the general bound

    At the solution x̃ ∈ B̄ᵣ₀(x̄), we have:
    ‖I - A∘Df(x̃)‖ = ‖DT(x̃)‖ ≤ Z(r₀) < 1

    This is the key to showing Df(x̃) is invertible (eq. 2.20). -/
lemma newton_derivative_at_solution
  {f : E → E} {A : E →L[ℝ] E} {xBar xTilde : E}
  {Y₀ Z₀ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
  (hf_diff : Differentiable ℝ f)
  (hxTilde_mem : xTilde ∈ Metric.closedBall xBar r₀)          -- x̃ ∈ B̄ᵣ₀(x̄)
  (h_Y₀ : ‖A (f xBar)‖ ≤ Y₀)                                  -- eq. 2.14
  (h_Z₀ : ‖I - A.comp (fderiv ℝ f xBar)‖ ≤ Z₀)                -- eq. 2.15
  (h_Z₂ : ∀ c ∈ Metric.closedBall xBar r₀,                    -- eq. 2.16
    ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖ ≤ Z₂ r₀ * r₀)
  (hr₀ : 0 < r₀)
  (h_radii : radiiPolynomial Y₀ Z₀ Z₂ r₀ < 0) :               -- eq. 2.17
  ‖I - A.comp (fderiv ℝ f xTilde)‖ < 1 := by
  -- Y₀ ≥ 0 from norm bound
  have hY₀_nonneg : 0 ≤ Y₀ := by
    calc 0 ≤ ‖A (f xBar)‖ := norm_nonneg _
         _ ≤ Y₀ := h_Y₀

  -- eq. 2.19-2.20: ‖DT(x̃)‖ ≤ Z₀ + Z₂(r₀)·r₀ = Z(r₀)
  have h_bound : ‖fderiv ℝ (NewtonLikeMap f A) xTilde‖ ≤ Z_bound Z₀ Z₂ r₀ :=
    newton_operator_derivative_bound_closed hf_diff h_Z₀ h_Z₂ xTilde hxTilde_mem

  -- eq. 2.18: Z(r₀) < 1 from p(r₀) < 0
  have h_Z_lt_one : Z_bound Z₀ Z₂ r₀ < 1 :=
    radii_poly_neg_implies_Z_bound_lt_one hY₀_nonneg hr₀ h_radii

  -- DT(x) = I - A∘Df(x) for all x (derivative of Newton operator)
  -- Therefore: ‖I - A∘Df(x̃)‖ = ‖DT(x̃)‖ ≤ Z(r₀) < 1
  calc ‖I - A.comp (fderiv ℝ f xTilde)‖
      = ‖fderiv ℝ (NewtonLikeMap f A) xTilde‖ := by
        rw [← newton_operator_fderiv hf_diff]
    _ ≤ Z_bound Z₀ Z₂ r₀ := h_bound             -- eq. 2.20
    _ < 1 := h_Z_lt_one                         -- eq. 2.18


/-- **Theorem 2.4.2**: Radii Polynomials in Finite Dimensions

    Given f ∈ C¹(E,E) and **injective** linear map A with bounds Y₀, Z₀, Z₂ satisfying:
    - ‖Af(x̄)‖ ≤ Y₀                                    (eq. 2.14)
    - ‖I - ADf(x̄)‖ ≤ Z₀                              (eq. 2.15)
    - ‖A[Df(c) - Df(x̄)]‖ ≤ Z₂(r)·r for all c ∈ B̄ᵣ(x̄)  (eq. 2.16)

    If p(r₀) < 0 where p(r) = Z₂(r)r² - (1-Z₀)r + Y₀ (eq. 2.17),
    then there exists a unique x̃ ∈ B̄_{r₀}(x̄) with f(x̃) = 0 and Df(x̃) invertible.

    *Modification from informal proof*: Assume A is injective as in Proposition 2.3.1 rather than invertible, avoiding unnecessary finite-dimensionality assumptions. -/
theorem radii_polynomial_theorem
  {f : E → E} {xBar : E} {A : E →L[ℝ] E}
  {Y₀ Z₀ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
  (hr₀ : 0 < r₀)
  (h_Y₀ : ‖A (f xBar)‖ ≤ Y₀)                                   -- eq. 2.14
  (h_Z₀ : ‖I - A.comp (fderiv ℝ f xBar)‖ ≤ Z₀)                 -- eq. 2.15
  (h_Z₂ : ∀ c ∈ Metric.closedBall xBar r₀,                     -- eq. 2.16
    ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖ ≤ Z₂ r₀ * r₀)
  (hf_diff : Differentiable ℝ f)
  (h_radii : radiiPolynomial Y₀ Z₀ Z₂ r₀ < 0)                  -- eq. 2.17: p(r₀) < 0
  (hA_inj : Function.Injective A) :                            -- A injective (weakened!)
  ∃! xTilde ∈ Metric.closedBall xBar r₀,
    f xTilde = 0 ∧ (fderiv ℝ f xTilde).IsInvertible := by

  -- Define the Newton-like operator T(x) = x - Af(x)
  let T := NewtonLikeMap f A

  -- T ∈ C¹(E,E) since f ∈ C¹(E,E) and A is continuous linear
  have hT_diff : Differentiable ℝ T := by
    unfold T NewtonLikeMap
    exact (differentiable_id).sub (A.differentiable.comp hf_diff)

  -- Apply Theorem 2.4.1 (general radii polynomial theorem)
  -- We verify:
  --   (a) ‖T(x̄) - x̄‖ = ‖Af(x̄)‖ ≤ Y₀
  --   (b) ‖DT(c)‖ ≤ Z(r₀) for all c ∈ B̄ᵣ₀(x̄)
  --   (c) p(r₀) < 0 (equivalently Z(r₀) < 1 - Y₀/r₀)
  -- Then Theorem 2.4.1 gives a unique fixed point x̃ ∈ B̄ᵣ₀(x̄)

  have ⟨xTilde, ⟨hxTilde_mem, hxTilde_fixed⟩, hxTilde_unique⟩ :=
    general_radii_polynomial_theorem
      hT_diff
      hr₀
      (newton_operator_Y_bound h_Y₀)                            -- ‖T(x̄) - x̄‖ ≤ Y₀
      (fun c hc => newton_operator_derivative_bound_closed      -- ‖DT(c)‖ ≤ Z(r₀)
        hf_diff h_Z₀ h_Z₂ c hc)
      (by unfold generalRadiiPolynomial                         -- p(r₀) < 0
          rw [← radiiPolynomial_alt_form]
          exact h_radii)

  -- Convert fixed point to zero via Proposition 2.3.1
  -- Proposition 2.3.1: T(x̃) = x̃ ⟺ f(x̃) = 0 when A is injective
  -- We have T(x̃) = x̃, therefore f(x̃) = 0

  have hxTilde_zero : f xTilde = 0 := by
    rw [← fixedPoint_injective_iff_zero hA_inj xTilde]
    exact hxTilde_fixed

  -- Show Df(x̃) is invertible
  -- Key steps:
  --   1. x̃ ∈ B̄ᵣ₀(x̄), so ‖DT(x̃)‖ ≤ Z(r₀) < 1 (by eq. 2.20)
  --   2. DT(x̃) = I - A∘Df(x̃), so ‖I - A∘Df(x̃)‖ < 1
  --   3. By Exercise 2.7.1, A∘Df(x̃) is invertible
  --   4. Since A is injective and A∘Df(x̃) is invertible, Df(x̃) is invertible
  --      (construct inverse as Df(x̃)⁻¹ = (A∘Df(x̃))⁻¹ ∘ A)

  have hDf_xTilde_inv : (fderiv ℝ f xTilde).IsInvertible := by
    apply construct_derivative_inverse hA_inj
    exact newton_derivative_at_solution hf_diff hxTilde_mem h_Y₀ h_Z₀ h_Z₂ hr₀ h_radii

  -- Package existence and uniqueness
  -- Existence: x̃ ∈ B̄ᵣ₀(x̄) with f(x̃) = 0 and Df(x̃) invertible
  -- Uniqueness: Any other z with these properties equals x̃

  refine ⟨xTilde, ⟨hxTilde_mem, hxTilde_zero, hDf_xTilde_inv⟩, ?_⟩

  -- Uniqueness: if z also satisfies the conditions, then z = x̃
  intro z ⟨hz_mem, hz_zero, _⟩
  -- z is a zero, so by Proposition 2.3.1, z is a fixed point of T
  have hz_fixed : T z = z := by
    rw [fixedPoint_injective_iff_zero hA_inj z]
    exact hz_zero
  -- By uniqueness from Theorem 2.4.1, z = x̃
  exact hxTilde_unique z ⟨hz_mem, hz_fixed⟩

section radii_polynomial_theorem_legacy
-- theorem radii_polynomial_theorem_legacy
--   {f : E → E} {xBar : E} {A : E →L[ℝ] E}
--   {Y₀ Z₀ : ℝ} {Z₂ : ℝ → ℝ} {r₀ : ℝ}
--   (hr₀ : 0 < r₀)
--   (h_Y₀ : ‖A (f xBar)‖ ≤ Y₀)                                   -- eq. 2.14
--   (h_Z₀ : ‖I - A.comp (fderiv ℝ f xBar)‖ ≤ Z₀)                 -- eq. 2.15
--   (h_Z₂ : ∀ c ∈ Metric.closedBall xBar r₀,                     -- eq. 2.16
--     ‖A.comp (fderiv ℝ f c - fderiv ℝ f xBar)‖ ≤ Z₂ r₀ * r₀)
--   (hf_diff : Differentiable ℝ f)
--   (h_radii : radiiPolynomial Y₀ Z₀ Z₂ r₀ < 0)                  -- eq. 2.17
--   (hA_inj : Function.Injective A):                             -- Assume A injective
--   ∃! xTilde ∈ Metric.closedBall xBar r₀,
--     f xTilde = 0 ∧ (fderiv ℝ f xTilde).IsInvertible := by

--   -- Y₀ ≥ 0 from the norm
--   have hY₀_nonneg : 0 ≤ Y₀ := by
--     calc 0 ≤ ‖A (f xBar)‖ := norm_nonneg _
--          _ ≤ Y₀ := h_Y₀

--   -- Step 1: Define Newton-like operator T(x) = x - Af(x)
--   let T := NewtonLikeMap f A

--   -- Step 2: T is differentiable (composition of differentiable functions)
--   have hT_diff : Differentiable ℝ T := by
--     unfold T NewtonLikeMap
--     apply Differentiable.sub differentiable_id
--     exact A.differentiable.comp hf_diff

--   -- Step 3: Verify Y₀ bound: ‖T(x̄) - x̄‖ ≤ Y₀ (eq. 2.14 reformulated)
--   have h_bound_Y : ‖T xBar - xBar‖ ≤ Y₀ :=
--     newton_operator_Y_bound h_Y₀

--   -- Step 4: Verify derivative bound: ‖DT(c)‖ ≤ Z(r₀) for c ∈ B̄_{r₀}(x̄)
--   -- This combines eq. 2.15 and 2.16 via eq. 2.18
--   have h_bound_Z : ∀ c ∈ Metric.closedBall xBar r₀,
--       ‖fderiv ℝ T c‖ ≤ Z_bound Z₀ Z₂ r₀ :=
--     fun c hc => newton_operator_derivative_bound_closed hf_diff h_Z₀ h_Z₂ c hc

--   -- Step 5: Convert specific radii polynomial to general form
--   -- p(r) = Z₂(r)r² - (1-Z₀)r + Y₀ = (Z(r) - 1)r + Y₀
--   have h_radii_general : generalRadiiPolynomial Y₀ (Z_bound Z₀ Z₂) r₀ < 0 := by
--     unfold generalRadiiPolynomial
--     rw [← radiiPolynomial_alt_form]
--     exact h_radii

--   -- Step 6: p(r₀) < 0 implies Z(r₀) < 1 (eq. 2.18)
--   have h_Z_lt_one : Z_bound Z₀ Z₂ r₀ < 1 :=
--     radii_poly_neg_implies_Z_bound_lt_one hY₀_nonneg hr₀ h_radii

--   -- Step 7: In particular, ‖I - ADf(x̄)‖ ≤ Z₀ < Z(r₀) < 1
--   have h_Z₂_nonneg : 0 ≤ Z₂ r₀ * r₀ := by
--     haveI := h_Z₂ xBar (mem_closedBall_self (le_of_lt hr₀))
--     simp only [sub_self] at this
--     haveI : 0 ≤ Z₂ r₀ * r₀ := by simpa using this
--     exact this

--   have h_Z₀_lt_one : ‖I - A.comp (fderiv ℝ f xBar)‖ < 1 := by
--     calc ‖I - A.comp (fderiv ℝ f xBar)‖
--         ≤ Z₀ := h_Z₀
--       _ ≤ Z₀ + Z₂ r₀ * r₀ := by linarith [h_Z₂_nonneg]
--       _ = Z_bound Z₀ Z₂ r₀ := rfl
--       _ < 1 := by exact h_Z_lt_one

--    -- Step 8: ADf(x̄) is invertible
--   have ⟨_, h_A_Df_left, h_A_Df_right⟩ := invertible_comp_form h_Z₀_lt_one

--   -- Step 9: Apply general radii polynomial theorem to get unique fixed point
--   have ⟨xTilde, ⟨hxTilde_mem, hxTilde_fixed⟩, hxTilde_unique⟩ :=
--     general_radii_polynomial_theorem hT_diff hr₀ h_bound_Y h_bound_Z h_radii_general

--   -- Step 10: Convert fixed point to zero using injectivity of A (Prop 2.3.1)
--   have hxTilde_zero : f xTilde = 0 := by
--     rw [← fixedPoint_injective_iff_zero hA_inj xTilde]
--     exact hxTilde_fixed

--   -- Step 11: Show Df(xTilde) is invertible
--   have hDf_xTilde_inv : (fderiv ℝ f xTilde).IsInvertible := by
--     -- ‖I - A ∘ Df(xTilde)‖ < 1
--     have h_I_minus_lt : ‖I - A.comp (fderiv ℝ f xTilde)‖ < 1 := by
--       calc ‖I - A.comp (fderiv ℝ f xTilde)‖
--           = ‖fderiv ℝ T xTilde‖ := by rw [← newton_operator_fderiv hf_diff]
--         _ ≤ Z_bound Z₀ Z₂ r₀ := h_bound_Z xTilde hxTilde_mem
--         _ < 1 := h_Z_lt_one

--     -- A∘Df(xTilde) is bijective
--     have hDf_bij : Function.Bijective (fderiv ℝ f xTilde) :=
--       bijective_of_comp_and_injective hA_inj h_I_minus_lt

--     -- Get the two-sided inverse of A∘Df(xTilde)
--     obtain ⟨inv_ADf, h_left, h_right⟩ := invertible_comp_form h_I_minus_lt

--     -- Construct the ContinuousLinearEquiv
--     let Df_inv := inv_ADf.comp A

--     -- Prove the inverse properties as functions
--     have h_inv_left : ∀ x, fderiv ℝ f xTilde (Df_inv x) = x := by
--       intro x
--       have h1 : A (fderiv ℝ f xTilde (inv_ADf (A x))) = A x := by
--         have := congrFun (congrArg DFunLike.coe h_left) (A x)
--         simp at this
--         exact this
--       exact hA_inj h1

--     have h_inv_right : ∀ x, Df_inv (fderiv ℝ f xTilde x) = x := by
--       intro x
--       have := congrFun (congrArg DFunLike.coe h_right) x
--       simp at this
--       exact this

--     -- Construct the equiv using the bijection
--     use ContinuousLinearEquiv.equivOfInverse (fderiv ℝ f xTilde) Df_inv h_inv_right h_inv_left
--     rfl

--     -- Step 12: Package the result
--   refine ⟨xTilde, ⟨hxTilde_mem, hxTilde_zero, hDf_xTilde_inv⟩, ?_⟩

--   -- Uniqueness: if z also satisfies the conditions, then z = xTilde
--   intro z ⟨hz_mem, hz_zero, _⟩
--   -- z is a zero of f, so by Proposition 2.3.1, z is a fixed point of T
--   have hz_fixed : T z = z := by
--     rw [fixedPoint_injective_iff_zero hA_inj z]
--     exact hz_zero
--   -- Apply uniqueness from the general radii polynomial theorem
--   exact hxTilde_unique z ⟨hz_mem, hz_fixed⟩
end radii_polynomial_theorem_legacy

end RadiiPolynomialTheorem

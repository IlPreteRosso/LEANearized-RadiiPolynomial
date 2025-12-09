import RadiiPolynomial.TaylorODE.lpWeighted
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Fréchet Differentiability of Cauchy Product

This file establishes that the map `a ↦ a ⋆ a` in the Banach algebra ℓ¹_ν
is Fréchet differentiable, with derivative `D(a ⋆ a)h = 2(a ⋆ h)`.

## Background

From Theorem 7.4.7: In any Banach algebra X with product `·`, the map
G(x) = x · x is Fréchet differentiable with DG(x)h = x · h + h · x.

By Remark 7.4.8: When the algebra is commutative (as ℓ¹_ν is by Corollary 7.4.5),
this simplifies to DG(x)h = 2(x · h).

## Main Results

- `CauchyProduct_bilinear`: The Cauchy product is bilinear
- `CauchyProduct_continuous`: The Cauchy product is continuous (norm estimate)
- `hasFDerivAt_CauchyProduct_sq`: The map has Fréchet derivative 2(a ⋆ ·)
- `differentiable_CauchyProduct_sq`: The map is differentiable everywhere

## References

- Theorem 7.4.7: Fréchet differentiability in Banach algebras
- Remark 7.4.8: Derivative formula for commutative case
- Equation (7.17): Banach algebra estimate ‖a ⋆ b‖ ≤ ‖a‖ · ‖b‖
-/

open scoped BigOperators Topology NNReal ENNReal
open Metric Set Filter ContinuousLinearMap

noncomputable section

variable {ν : PosReal}

/-! ## Cauchy Product as Bilinear Map

The Cauchy product (a, b) ↦ a ⋆ b is bilinear and continuous on ℓ¹_ν.
Continuity follows from the submultiplicative estimate (Theorem 7.4.4):
  ‖a ⋆ b‖₁,ν ≤ ‖a‖₁,ν · ‖b‖₁,ν
-/

namespace l1Weighted

/-- Left multiplication by a fixed element: h ↦ a ⋆ h

    This is the key map appearing in the derivative formula.
    For fixed a ∈ ℓ¹_ν, the map h ↦ a ⋆ h is linear and bounded.

    **Construction**: We use `LinearMap.mkContinuous` which takes:
    1. A linear map (proving additivity and scalar homogeneity)
    2. An operator norm bound C with proof that ‖f(h)‖ ≤ C · ‖h‖

    This automatically produces a continuous linear map. -/
def leftMul (a : l1Weighted ν) : l1Weighted ν →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous
    -- First argument: the underlying linear map (→ₗ[ℝ], not →L[ℝ])
    { -- The function: h ↦ a ⋆ h
      toFun := fun h => CauchyProductBanachAlgebra.mul a h

      -- Additivity: a ⋆ (h₁ + h₂) = a ⋆ h₁ + a ⋆ h₂
      map_add' := fun h₁ h₂ => by
        apply lpWeighted.ext; intro n
        simp only [CauchyProductBanachAlgebra.mul, lpWeighted.mk_apply,
                   lpWeighted.add_toSeq, CauchyProduct]
        -- Σ aₖ(h₁ₗ + h₂ₗ) = Σ aₖh₁ₗ + Σ aₖh₂ₗ
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro kl _; ring

      -- Scalar homogeneity: a ⋆ (c • h) = c • (a ⋆ h)
      map_smul' := fun c h => by
        apply lpWeighted.ext; intro n
        simp only [CauchyProductBanachAlgebra.mul, lpWeighted.mk_apply,
                   lpWeighted.smul_toSeq, RingHom.id_apply, CauchyProduct]
        -- Σ aₖ(c·hₗ) = c · Σ aₖhₗ
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro kl _; ring }

    -- Second argument: the operator norm bound C = ‖a‖
    ‖a‖

    -- Third argument: proof that ‖a ⋆ h‖ ≤ ‖a‖ · ‖h‖ (submultiplicativity)
    (fun h => CauchyProductBanachAlgebra.norm_mul_le a h)

/-- Operator norm bound for left multiplication: ‖leftMul a‖ ≤ ‖a‖

    This is immediate from submultiplicativity. -/
lemma norm_leftMul_le (a : l1Weighted ν) : ‖leftMul a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  intro h
  exact CauchyProductBanachAlgebra.norm_mul_le a h

/-- Left multiplication applied: (leftMul a) h = a ⋆ h -/
@[simp]
lemma leftMul_apply (a h : l1Weighted ν) :
    leftMul a h = CauchyProductBanachAlgebra.mul a h := rfl

/-- The underlying sequence of (leftMul a) h -/
lemma leftMul_toSeq (a h : l1Weighted ν) (n : ℕ) :
    lpWeighted.toSeq (leftMul a h) n = (lpWeighted.toSeq a ⋆ lpWeighted.toSeq h) n := by
  simp only [leftMul_apply, CauchyProductBanachAlgebra.mul, lpWeighted.mk_apply]

/-- Scalar multiplication on leftMul: leftMul (c • a) = c • leftMul a

    This shows that `leftMul` is linear in its first argument (the fixed element).
    Combined with `leftMul_add`, this means a ↦ leftMul a is itself a linear map
    from l1Weighted ν to the space of continuous linear operators.

    Mathematically: (c·a) ⋆ h = c · (a ⋆ h) for all h. -/
lemma leftMul_smul (c : ℝ) (a : l1Weighted ν) :
    leftMul (c • a) = c • leftMul a := by
  -- Equality of continuous linear maps: show they agree on all inputs h
  ext h n
  -- Unfold both sides to sequences
  simp only [leftMul_apply, coe_smul', Pi.smul_apply, lp.coeFn_smul, smul_eq_mul,
             CauchyProductBanachAlgebra.mul]
  -- Expand Cauchy product definition
  unfold CauchyProduct
  simp only [← lpWeighted.toSeq_apply, lpWeighted.mk_apply]
  -- Goal: Σₖ₊ₗ₌ₙ (c · aₖ) · hₗ = c · Σₖ₊ₗ₌ₙ aₖ · hₗ
  -- Pull scalar c outside the sum
  rw [Finset.mul_sum]
  -- Show termwise equality: (c · aₖ) · hₗ = c · (aₖ · hₗ)
  apply Finset.sum_congr rfl; intro kl _
  simp only [lpWeighted.smul_toSeq]
  ring_nf


/-- Linearity in the first argument: leftMul (a + b) = leftMul a + leftMul b

    This shows that `leftMul` is additive in its first argument.
    Combined with `leftMul_smul`, this means a ↦ leftMul a is a linear map
    from l1Weighted ν to the space of continuous linear operators.

    Mathematically: (a + b) ⋆ h = a ⋆ h + b ⋆ h for all h (left-distributivity). -/
lemma leftMul_add (a b : l1Weighted ν) :
    leftMul (a + b) = leftMul a + leftMul b := by
  -- Equality of continuous linear maps: show they agree on all inputs h
  ext h n
  -- Unfold both sides to sequences
  simp only [leftMul_apply, add_apply, lp.coeFn_add, Pi.add_apply,
             CauchyProductBanachAlgebra.mul]
  -- Expand Cauchy product definition
  unfold CauchyProduct
  simp only [← lpWeighted.toSeq_apply, lpWeighted.mk_apply]
  -- Goal: Σₖ₊ₗ₌ₙ (aₖ + bₖ) · hₗ = Σₖ₊ₗ₌ₙ aₖ · hₗ + Σₖ₊ₗ₌ₙ bₖ · hₗ
  -- Combine the two sums on RHS into one
  rw [← Finset.sum_add_distrib]
  -- Show termwise equality: (aₖ + bₖ) · hₗ = aₖ · hₗ + bₖ · hₗ
  apply Finset.sum_congr rfl; intro kl _
  simp only [lpWeighted.add_toSeq]
  ring_nf

/-- The squaring map: a ↦ a ⋆ a -/
def sq (a : l1Weighted ν) : l1Weighted ν := CauchyProductBanachAlgebra.mul a a

@[simp]
lemma sq_toSeq (a : l1Weighted ν) (n : ℕ) :
    lpWeighted.toSeq (sq a) n = (lpWeighted.toSeq a ⋆ lpWeighted.toSeq a) n := by
  simp only [sq, CauchyProductBanachAlgebra.mul, lpWeighted.mk_apply]

end l1Weighted


/-! ## Fréchet Differentiability of Squaring Map

We prove that sq : ℓ¹_ν → ℓ¹_ν is Fréchet differentiable at every point a,
with derivative D(sq)(a) = 2 · leftMul a.

The proof follows Theorem 7.4.7: we show that
  ‖sq(a + h) - sq(a) - 2(a ⋆ h)‖ = ‖h ⋆ h‖ ≤ ‖h‖²
and thus the remainder is o(‖h‖).
-/

namespace l1Weighted

/-- Key algebraic identity: (a+h)⋆(a+h) - a⋆a - 2(a⋆h) = h⋆h

    This is the remainder term in the Taylor expansion of the squaring map.
    See proof of Theorem 7.4.7:
      G(x+h) - G(x) - Ah = (x+h)·(x+h) - x·x - (x·h + h·x) = h·h -/
lemma sq_expansion (a h : l1Weighted ν) :
    sq (a + h) - sq a - (leftMul a h + leftMul h a) = sq h := by
  apply lpWeighted.ext
  intro n
  simp only [lpWeighted.sub_toSeq, lpWeighted.add_toSeq, sq_toSeq, leftMul_toSeq]
  -- Expand using Cauchy product definition
  simp only [CauchyProduct.apply]
  -- (a+h)⋆(a+h) - a⋆a - a⋆h - h⋆a = h⋆h by algebra
  simp only [lpWeighted.add_toSeq]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  -- Now prove termwise: (aₖ+hₖ)(aₗ+hₗ) - aₖaₗ - aₖhₗ - hₖaₗ = hₖhₗ
  apply Finset.sum_congr rfl; intro kl _
  ring

/-- Commutativity: a ⋆ h = h ⋆ a in the weighted ℓ¹ space

    This follows from CauchyProduct.comm. -/
lemma mul_comm (a b : l1Weighted ν) :
    CauchyProductBanachAlgebra.mul a b = CauchyProductBanachAlgebra.mul b a := by
  apply lpWeighted.ext
  intro n
  simp only [CauchyProductBanachAlgebra.mul, lpWeighted.mk_apply]
  rw [CauchyProduct.comm]

/-- leftMul a h = leftMul h a (commutativity) -/
lemma leftMul_comm (a h : l1Weighted ν) : leftMul a h = leftMul h a := by
  simp only [leftMul_apply]
  exact mul_comm a h

/-- Simplified expansion using commutativity: sq(a+h) - sq(a) - 2(a⋆h) = h⋆h -/
lemma sq_expansion_comm (a h : l1Weighted ν) :
    sq (a + h) - sq a - (2 : ℝ) • leftMul a h = sq h := by
  have h1 := sq_expansion a h
  rw [leftMul_comm h a, ← two_smul ℝ (leftMul a h)] at h1
  convert h1 using 2

/-- Norm of the remainder: ‖sq(a+h) - sq(a) - 2(a⋆h)‖ ≤ ‖h‖²

    This is the key estimate for Fréchet differentiability.
    See Theorem 7.4.7: ‖h·h‖ ≤ ‖h‖·‖h‖ by submultiplicativity. -/
lemma sq_remainder_norm (a h : l1Weighted ν) :
    ‖sq (a + h) - sq a - (2 : ℝ) • leftMul a h‖ ≤ ‖h‖ ^ 2 := by
  rw [sq_expansion_comm]
  calc ‖sq h‖ = ‖CauchyProductBanachAlgebra.mul h h‖ := rfl
    _ ≤ ‖h‖ * ‖h‖ := CauchyProductBanachAlgebra.norm_mul_le h h
    _ = ‖h‖ ^ 2 := by ring

/-- **Theorem 7.4.7 (for ℓ¹_ν)**: The squaring map has Fréchet derivative 2·(a ⋆ ·)

    For G(a) = a ⋆ a, we have DG(a)h = 2(a ⋆ h).

    Proof: By the remainder estimate ‖G(a+h) - G(a) - 2(a⋆h)‖ ≤ ‖h‖²,
    the remainder is O(‖h‖²) = o(‖h‖), satisfying the Fréchet condition. -/
theorem hasFDerivAt_sq (a : l1Weighted ν) :
    HasFDerivAt sq ((2 : ℝ) • leftMul a) a := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  -- Need to show: (sq(a + h) - sq(a) - 2(a⋆h)) = o(h) as h → 0
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  -- For small enough h, ‖remainder‖ ≤ ε · ‖h‖
  -- We use ‖remainder‖ ≤ ‖h‖², so need ‖h‖ < ε
  filter_upwards [Metric.ball_mem_nhds (0 : l1Weighted ν) hε] with h hh
  rw [Metric.mem_ball, dist_zero_right] at hh
  calc ‖sq (a + h) - sq a - ((2 : ℝ) • leftMul a) h‖
      = ‖sq (a + h) - sq a - (2 : ℝ) • leftMul a h‖ := by rfl
    _ ≤ ‖h‖ ^ 2 := sq_remainder_norm a h
    _ = ‖h‖ * ‖h‖ := by ring
    _ ≤ ε * ‖h‖ := by
        apply mul_le_mul_of_nonneg_right (le_of_lt hh) (norm_nonneg h)

/-- The squaring map is differentiable everywhere -/
theorem differentiable_sq : Differentiable ℝ (sq : l1Weighted ν → l1Weighted ν) := by
  intro a
  exact (hasFDerivAt_sq a).differentiableAt

/-- The Fréchet derivative of the squaring map -/
theorem fderiv_sq (a : l1Weighted ν) :
    fderiv ℝ sq a = (2 : ℝ) • leftMul a :=
  (hasFDerivAt_sq a).fderiv

end l1Weighted


/-! ## Application: Map F(a) = a ⋆ a - c

For the ODE example (Section 7.7), we consider F(a) = a ⋆ a - c where c is a fixed
sequence. This is a translation of the squaring map.

Key results:
- F is Fréchet differentiable
- DF(a)h = 2(a ⋆ h)
-/

namespace l1Weighted

/-- The map F(a) = a ⋆ a - c appearing in Section 7.7

    For the parameterized equilibrium problem x² - λ = 0, the sequence
    formulation becomes a ⋆ a - c = 0 where c encodes the parameter. -/
def F_sub_const (c : l1Weighted ν) (a : l1Weighted ν) : l1Weighted ν := sq a - c

/-- F(a) = a ⋆ a - c has Fréchet derivative 2(a ⋆ ·) at a

    The constant c disappears upon differentiation. -/
theorem hasFDerivAt_F_sub_const (c a : l1Weighted ν) :
    HasFDerivAt (F_sub_const c) ((2 : ℝ) • leftMul a) a := by
  have h := hasFDerivAt_sq a
  unfold F_sub_const
  -- D(sq - c) = D(sq) since c is constant
  exact h.sub_const c

/-- F is differentiable everywhere -/
theorem differentiable_F_sub_const (c : l1Weighted ν) :
    Differentiable ℝ (F_sub_const c) := by
  intro a
  exact (hasFDerivAt_F_sub_const c a).differentiableAt

/-- The Fréchet derivative of F -/
theorem fderiv_F_sub_const (c a : l1Weighted ν) :
    fderiv ℝ (F_sub_const c) a = (2 : ℝ) • leftMul a :=
  (hasFDerivAt_F_sub_const c a).fderiv

end l1Weighted

end

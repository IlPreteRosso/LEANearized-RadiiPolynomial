import RadiiPolynomial.TaylorODE.lpWeighted
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Fréchet Differentiability of the Squaring Map

This file establishes that the squaring map `a ↦ a * a` in the Banach algebra ℓ¹_ν
is Fréchet differentiable, with derivative `D(a * a)h = 2(a * h)`.

## Mathematical Background

### Theorem 7.4.7 (Differentiability in Banach Algebras)

In any Banach algebra X with product `·`, the squaring map G(x) = x · x is
Fréchet differentiable with derivative:

  DG(x)h = x · h + h · x

### Remark 7.4.8 (Commutative Case)

When the algebra is commutative (as ℓ¹_ν is by Corollary 7.4.5), this simplifies to:

  DG(x)h = 2(x · h)

## Implementation Notes

### Why the Proofs Are So Simple

Since `l1Weighted ν` has `CommRing` and `NormedRing` instances (from lpWeighted.lean),
we use ring operations `*`, `+` directly. The key algebraic identity:

  (a + h)² - a² - 2ah = h²

reduces to a single `ring` tactic call, because the `CommRing` instance provides
all the necessary axioms (associativity, distributivity, commutativity).

### Comparison: Before vs After Refactoring

**Before** (manual Cauchy product proofs):
```lean
lemma sq_expansion (a h : l1Weighted ν) : ... := by
  apply lpWeighted.ext; intro n
  simp only [lpWeighted.sub_toSeq, lpWeighted.add_toSeq, sq_toSeq, leftMul_toSeq]
  simp only [CauchyProduct.apply]
  simp only [lpWeighted.add_toSeq]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro kl _; ring
```

**After** (using Ring instance):
```lean
lemma sq_expansion (a h : l1Weighted ν) : ... := by
  simp only [sq, leftMul_apply]; ring
```

The refactoring philosophy: **algebraic properties are inherited from typeclass
instances, not reproven at each use site**.

### Role of SMulCommClass and IsScalarTower

The instances `SMulCommClass ℝ (l1Weighted ν) (l1Weighted ν)` and
`IsScalarTower ℝ (l1Weighted ν) (l1Weighted ν)` (defined in lpWeighted.lean)
enable lemmas like `smul_mul_assoc` and `smul_comm`, which are used in:

- `leftMul.map_smul'`: Proving `a * (c • h) = c • (a * h)`
- `leftMul_smul`: Proving `leftMul (c • a) = c • leftMul a`

These instances are proven using `CauchyProduct.smul_mul` and `CauchyProduct.mul_smul`.

## Main Results

- `leftMul`: Left multiplication `h ↦ a * h` as a continuous linear map
- `hasFDerivAt_sq`: The squaring map has Fréchet derivative `2 • leftMul a`
- `differentiable_sq`: The squaring map is differentiable everywhere
- `hasFDerivAt_F_sub_const`: The map `F(a) = a * a - c` has derivative `2 • leftMul a`

## References

- Theorem 7.4.7: Fréchet differentiability in Banach algebras
- Remark 7.4.8: Derivative formula for commutative case
- Corollary 7.4.5: ℓ¹_ν is a commutative Banach algebra
-/

open scoped BigOperators Topology NNReal ENNReal
open Metric Set Filter ContinuousLinearMap

noncomputable section

variable {ν : PosReal}

/-! ## Part 1: Left Multiplication as Continuous Linear Map

For fixed `a ∈ ℓ¹_ν`, the map `h ↦ a * h` is a bounded linear operator.

- **Linearity**: From Ring distributivity `a * (h₁ + h₂) = a * h₁ + a * h₂`
- **Boundedness**: From submultiplicativity `‖a * h‖ ≤ ‖a‖ · ‖h‖`
-/

namespace l1Weighted

/-- Left multiplication by a fixed element: h ↦ a * h

    This is the key map appearing in the derivative formula DG(a)h = 2(a * h).

    **Construction**: We use `LinearMap.mkContinuous` with:
    1. Linearity from Ring distributivity
    2. Scalar compatibility from `smul_comm`
    3. Operator norm bound from submultiplicativity -/
def leftMul (a : l1Weighted ν) : l1Weighted ν →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous
    { toFun := fun h => a * h
      -- Additivity: a * (h₁ + h₂) = a * h₁ + a * h₂ (left distributivity)
      map_add' := fun h₁ h₂ => mul_add a h₁ h₂
      -- Scalar homogeneity: a * (c • h) = c • (a * h)
      -- Uses SMulCommClass instance from lpWeighted.lean
      map_smul' := fun c h => by
        simp only [RingHom.id_apply]
        rw [← smul_eq_mul, ← smul_eq_mul]
        exact (smul_comm c a h).symm }
    ‖a‖
    (fun h => norm_mul_le a h)

/-- Operator norm bound: ‖leftMul a‖ ≤ ‖a‖ -/
lemma norm_leftMul_le (a : l1Weighted ν) : ‖leftMul a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) (fun h => norm_mul_le a h)

/-- Definitional equality: (leftMul a) h = a * h -/
@[simp]
lemma leftMul_apply (a h : l1Weighted ν) : leftMul a h = a * h := rfl

/-- The underlying sequence of (leftMul a) h equals the Cauchy product. -/
lemma leftMul_toSeq (a h : l1Weighted ν) (n : ℕ) :
    lpWeighted.toSeq (leftMul a h) n = (lpWeighted.toSeq a ⋆ lpWeighted.toSeq h) n := rfl

/-! ### Linearity of leftMul in the First Argument

These lemmas show that the map `a ↦ leftMul a` is itself linear, making
`leftMul` a bilinear operation. This is used in showing that the derivative
is a continuous linear map.
-/

/-- Scalar multiplication distributes: leftMul (c • a) = c • leftMul a

    Uses `smul_mul_assoc` from IsScalarTower instance. -/
lemma leftMul_smul (c : ℝ) (a : l1Weighted ν) :
    leftMul (c • a) = c • leftMul a := by
  ext1 h
  simp only [leftMul_apply, coe_smul', Pi.smul_apply, ← smul_eq_mul]
  exact smul_mul_assoc c a h

/-- Addition distributes: leftMul (a + b) = leftMul a + leftMul b

    Uses `add_mul` (right distributivity) from Ring instance. -/
lemma leftMul_add (a b : l1Weighted ν) :
    leftMul (a + b) = leftMul a + leftMul b := by
  ext1 h
  simp only [leftMul_apply, add_apply]
  exact add_mul a b h

/-! ### The Squaring Map -/

/-- The squaring map: a ↦ a * a

    This is the main object of study. We prove it has Fréchet derivative 2(a * ·). -/
def sq (a : l1Weighted ν) : l1Weighted ν := a * a

@[simp]
lemma sq_toSeq (a : l1Weighted ν) (n : ℕ) :
    lpWeighted.toSeq (sq a) n = (lpWeighted.toSeq a ⋆ lpWeighted.toSeq a) n := rfl

end l1Weighted


/-! ## Part 2: Fréchet Differentiability of the Squaring Map

We prove that `sq : ℓ¹_ν → ℓ¹_ν` is Fréchet differentiable at every point `a`,
with derivative `D(sq)(a) = 2 · leftMul a`.

The key steps are:

1. **Algebraic identity**: `(a+h)² - a² - 2ah = h²`
2. **Norm estimate**: `‖h²‖ ≤ ‖h‖²` (submultiplicativity)
3. **Little-o bound**: `‖h‖² = o(‖h‖)` as h → 0

Together these show the remainder is o(‖h‖), which is the Fréchet condition.
-/

namespace l1Weighted

/-- Key algebraic identity for the Taylor expansion of squaring.

    (a + h)² - a² - (ah + ha) = h²

    In a commutative ring, ah = ha, so this becomes (a + h)² - a² - 2ah = h².

    **Proof**: A single `ring` tactic, thanks to the CommRing instance! -/
lemma sq_expansion (a h : l1Weighted ν) :
    sq (a + h) - sq a - (leftMul a h + leftMul h a) = sq h := by
  simp only [sq, leftMul_apply]
  ring

/-- Commutativity of leftMul: leftMul a h = leftMul h a

    Direct consequence of `mul_comm` from CommRing instance. -/
lemma leftMul_comm (a h : l1Weighted ν) : leftMul a h = leftMul h a := by
  simp only [leftMul_apply]
  exact mul_comm a h

/-- Simplified expansion using commutativity.

    sq(a + h) - sq(a) - 2(a * h) = h * h

    This is the form we actually use in the Fréchet derivative proof. -/
lemma sq_expansion_comm (a h : l1Weighted ν) :
    sq (a + h) - sq a - (2 : ℝ) • leftMul a h = sq h := by
  simp only [sq, leftMul_apply, two_smul]
  ring

/-- Norm estimate for the remainder: ‖sq(a+h) - sq(a) - 2(a*h)‖ ≤ ‖h‖²

    This is the key analytic estimate. By `sq_expansion_comm`, the LHS is ‖h * h‖,
    and by submultiplicativity ‖h * h‖ ≤ ‖h‖ · ‖h‖ = ‖h‖².

    This shows the remainder is O(‖h‖²), hence o(‖h‖). -/
lemma sq_remainder_norm (a h : l1Weighted ν) :
    ‖sq (a + h) - sq a - (2 : ℝ) • leftMul a h‖ ≤ ‖h‖ ^ 2 := by
  rw [sq_expansion_comm]
  calc ‖sq h‖ = ‖h * h‖ := rfl
    _ ≤ ‖h‖ * ‖h‖ := norm_mul_le h h
    _ = ‖h‖ ^ 2 := by ring

/-- **Theorem 7.4.7** (for ℓ¹_ν): The squaring map has Fréchet derivative 2(a * ·)

    For G(a) = a * a, we have DG(a)h = 2(a * h).

    **Proof outline**:
    1. By `sq_remainder_norm`: ‖G(a+h) - G(a) - 2(a*h)‖ ≤ ‖h‖²
    2. For ‖h‖ < ε, we have ‖h‖² ≤ ε · ‖h‖
    3. This gives the little-o condition: remainder = o(‖h‖) -/
theorem hasFDerivAt_sq (a : l1Weighted ν) :
    HasFDerivAt sq ((2 : ℝ) • leftMul a) a := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  -- For ‖h‖ < ε, we have ‖remainder‖ ≤ ‖h‖² ≤ ε · ‖h‖
  filter_upwards [Metric.ball_mem_nhds (0 : l1Weighted ν) hε] with h hh
  rw [Metric.mem_ball, dist_zero_right] at hh
  calc ‖sq (a + h) - sq a - ((2 : ℝ) • leftMul a) h‖
      = ‖sq (a + h) - sq a - (2 : ℝ) • leftMul a h‖ := rfl
    _ ≤ ‖h‖ ^ 2 := sq_remainder_norm a h
    _ = ‖h‖ * ‖h‖ := by ring
    _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right (le_of_lt hh) (norm_nonneg h)

/-- The squaring map is differentiable everywhere. -/
theorem differentiable_sq : Differentiable ℝ (sq : l1Weighted ν → l1Weighted ν) :=
  fun a => (hasFDerivAt_sq a).differentiableAt

/-- The Fréchet derivative of the squaring map. -/
theorem fderiv_sq (a : l1Weighted ν) :
    fderiv ℝ sq a = (2 : ℝ) • leftMul a :=
  (hasFDerivAt_sq a).fderiv

end l1Weighted


/-! ## Part 3: Application to F(a) = a * a - c

For the ODE example (Section 7.7), we consider F(a) = a * a - c where c is a fixed
sequence encoding the parameter. This is a translation of the squaring map.

The key point is that the derivative is unchanged: DF(a) = 2(a * ·), since
differentiating a constant gives zero.
-/

namespace l1Weighted

/-- The map F(a) = a * a - c appearing in Section 7.7.

    For the parameterized equilibrium problem x² - λ = 0, the sequence
    formulation becomes a * a - c = 0 where c encodes the parameter λ. -/
def F_sub_const (c : l1Weighted ν) (a : l1Weighted ν) : l1Weighted ν := sq a - c

/-- F(a) = a * a - c has Fréchet derivative 2(a * ·) at a.

    The constant c disappears upon differentiation. -/
theorem hasFDerivAt_F_sub_const (c a : l1Weighted ν) :
    HasFDerivAt (F_sub_const c) ((2 : ℝ) • leftMul a) a :=
  (hasFDerivAt_sq a).sub_const c

/-- F is differentiable everywhere. -/
theorem differentiable_F_sub_const (c : l1Weighted ν) :
    Differentiable ℝ (F_sub_const c) :=
  fun a => (hasFDerivAt_F_sub_const c a).differentiableAt

/-- The Fréchet derivative of F. -/
theorem fderiv_F_sub_const (c a : l1Weighted ν) :
    fderiv ℝ (F_sub_const c) a = (2 : ℝ) • leftMul a :=
  (hasFDerivAt_F_sub_const c a).fderiv

end l1Weighted

end

import RadiiPolynomial.TaylorODE.lpWeighted
import RadiiPolynomial.TaylorODE.FrechetCauchyProduct
import RadiiPolynomial.TaylorODE.OperatorNorm
import RadiiPolynomial.RadiiPolyGeneral

/-!
# Example 7.7: Taylor Series Solution of Parameterized Equilibria

We prove existence of the curve x(λ) satisfying x(λ)² - λ = 0 near lam0 using
the radii polynomial approach from Section 7.7.

## The Problem

Given the equation `x² - λ = 0` with `f(x₀, lam0) = 0` where `x₀ = √lam0`,
find a Taylor series `x(λ) = Σₙ aₙ(λ - lam0)ⁿ` satisfying the equation.

## Taylor Series Formulation

Substituting `x(λ) = Σₙ aₙ(λ - lam0)ⁿ` into `x² - λ = 0`:
- LHS: `(Σₙ aₙtⁿ)² = Σₙ (a ⋆ a)ₙ tⁿ` (Cauchy product)
- RHS: `λ = lam0 + t` where `t = λ - lam0`

This gives the zero-finding problem: `F(a) = a ⋆ a - c = 0`
where `c = (lam0, 1, 0, 0, ...)`.

## The Operator Structure

Following Theorem 7.7.1, the operators have block-diagonal structure:

- **A†** (approximate derivative): `DF⁽ᴺ⁾(ā)` on indices 0..N, `2ā₀` on tail
- **A** (approximate inverse): `(DF⁽ᴺ⁾(ā))⁻¹` on indices 0..N, `1/(2ā₀)` on tail

This matches the `BlockDiagOp` structure from OperatorNorm.lean.

## Main Results

- `paramSeqSpace`: The constant sequence `c = (lam0, 1, 0, 0, ...)`
- `F_eq_sq_sub`: `F(a) = a ⋆ a - c`
- `DF_eq_two_leftMul`: `DF(a)h = 2(a ⋆ h)`
- `Y₀_bound`, `Z₀_bound`, `Z₁_bound`, `Z₂_bound`: The bounds from Theorem 7.7.1
- `existence_theorem`: Application of Theorem 7.6.2

## References

- Section 7.7: Taylor series solution of parameterized equilibria
- Theorem 7.7.1: The radii polynomial bounds
- Equation (7.40): x² - λ = 0
- Equations (7.41)-(7.43): The sequence formulation
-/

open scoped BigOperators Topology NNReal ENNReal Matrix
open Metric Set Filter ContinuousLinearMap

noncomputable section

variable {ν : PosReal}

/-! ## The Constant Sequence c

For the equation x² - λ = 0 expanded around lam0, the constant sequence is:
  c = (lam0, 1, 0, 0, ...)

This encodes `λ = lam0 + (λ - lam0)` in Taylor coefficients.
-/

namespace Example_7_7

/-- The constant sequence c = (lam0, 1, 0, 0, ...) from equation (7.40).
    This encodes λ = lam0 + t where t = λ - lam0. -/
def paramSeq (lam0 : ℝ) : ℕ → ℝ := fun n =>
  match n with
  | 0 => lam0
  | 1 => 1
  | _ => 0

/-- The constant sequence is in ℓ¹_ν -/
lemma paramSeq_mem (lam0 : ℝ) : lpWeighted.Mem ν 1 (paramSeq lam0) := by
  rw [l1Weighted.mem_iff]
  -- Sum is finite: lam0 + ν + 0 + 0 + ...
  apply summable_of_ne_finset_zero (s := {0, 1})
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  simp [paramSeq, hn.1, hn.2]

/-- The constant sequence as an element of ℓ¹_ν -/
def c (lam0 : ℝ) : l1Weighted ν := lpWeighted.mk (paramSeq lam0) (paramSeq_mem lam0)

/-- c₀ = lam0 -/
@[simp]
lemma c_zero (lam0 : ℝ) : lpWeighted.toSeq (c lam0 : l1Weighted ν) 0 = lam0 := by
  rfl

/-- c₁ = 1 -/
@[simp]
lemma c_one (lam0 : ℝ) : lpWeighted.toSeq (c lam0 : l1Weighted ν) 1 = 1 := by
  rfl

/-- cₙ = 0 for n ≥ 2 -/
@[simp]
lemma c_ge_two (lam0 : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    lpWeighted.toSeq (c lam0 : l1Weighted ν) n = 0 := by
  simp only [c, lpWeighted.mk_apply, paramSeq]
  match n with
  | 0 => omega
  | 1 => omega
  | n + 2 => rfl

/-- Norm of c: ‖c‖ = |lam0| + ν -/
lemma norm_c (lam0 : ℝ) : ‖(c lam0 : l1Weighted ν)‖ = |lam0| + (ν : ℝ) := by
  rw [l1Weighted.norm_eq_tsum]
  have h : (fun n => |lpWeighted.toSeq (c lam0 : l1Weighted ν) n| * (ν : ℝ) ^ n) =
           fun n => if n = 0 then |lam0| else if n = 1 then (ν : ℝ) else 0 := by
    ext n
    match n with
    | 0 => simp only [lpWeighted.toSeq_apply, pow_zero, mul_one, ↓reduceIte]; rfl
    | 1 => simp only [lpWeighted.toSeq_apply, pow_one, one_ne_zero, ↓reduceIte, ne_eq,
      PosReal.coe_ne_zero, not_false_eq_true, mul_eq_right₀]; exact abs_one
    | n + 2 => simp only [lpWeighted.toSeq_apply, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero,
      and_false, ↓reduceIte, Nat.reduceEqDiff, mul_eq_zero, abs_eq_zero, ne_eq, not_false_eq_true,
      pow_eq_zero_iff, PosReal.coe_ne_zero, or_false]; rfl
  rw [h]
  rw [tsum_eq_sum (s := {0, 1})]
  · simp
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [hn.1, hn.2]


/-! ## The Zero-Finding Map F

The map F(a) = a ⋆ a - c from equation (7.43).
-/

/-- The zero-finding map F(a) = a ⋆ a - c -/
def F (lam0 : ℝ) (a : l1Weighted ν) : l1Weighted ν :=
  l1Weighted.F_sub_const (c lam0) a

/-- F(a) = sq(a) - c -/
lemma F_eq (lam0 : ℝ) (a : l1Weighted ν) :
    F lam0 a = l1Weighted.sq a - c lam0 := rfl

/-- Component formula for F (equation 7.43):
    F₀(a) = a₀² - lam0
    F₁(a) = 2a₀a₁ - 1
    Fₙ(a) = (a ⋆ a)ₙ for n ≥ 2 -/
lemma F_component (lam0 : ℝ) (a : l1Weighted ν) (n : ℕ) :
    lpWeighted.toSeq (F lam0 a) n =
    (lpWeighted.toSeq a ⋆ lpWeighted.toSeq a) n - lpWeighted.toSeq (ν := ν) (c lam0) n := by
  simp only [F, l1Weighted.F_sub_const, lpWeighted.sub_toSeq, l1Weighted.sq_toSeq]

/-- F is Fréchet differentiable -/
theorem differentiable_F (lam0 : ℝ) : Differentiable ℝ (F lam0 : l1Weighted ν → l1Weighted ν) :=
  l1Weighted.differentiable_F_sub_const (c lam0)

/-- The Fréchet derivative: DF(a)h = 2(a ⋆ h) -/
theorem fderiv_F (lam0 : ℝ) (a : l1Weighted ν) :
    fderiv ℝ (F lam0) a = (2 : ℝ) • l1Weighted.leftMul a :=
  l1Weighted.fderiv_F_sub_const (c lam0) a


/-! ## The Approximate Solution

For the concrete example with lam0 = 1/3, we have:
  ā₀ ≈ √(1/3) ≈ 0.577...
  ā₁ ≈ 1/(2ā₀) ≈ 0.866...
  etc.

The approximate solution satisfies F⁽ᴺ⁾(ā⁽ᴺ⁾) ≈ 0 for the truncated system.
-/

variable (N : ℕ)

/-- Structure for an approximate solution -/
structure ApproxSolution where
  /-- The truncated approximate solution ā⁽ᴺ⁾ ∈ ℝᴺ⁺¹ -/
  aBar_fin : Fin (N + 1) → ℝ
  /-- Assumption: ā₀ ≠ 0 (needed for invertibility) -/
  aBar_zero_ne : aBar_fin 0 ≠ 0

/-- Extend the finite approximate solution to a sequence (zero-padded) -/
def ApproxSolution.toSeq (sol : ApproxSolution N) : ℕ → ℝ := fun n =>
  if h : n ≤ N then sol.aBar_fin ⟨n, Nat.lt_succ_of_le h⟩ else 0

/-- The extended sequence is in ℓ¹_ν -/
lemma ApproxSolution.mem (sol : ApproxSolution N) : lpWeighted.Mem ν 1 sol.toSeq := by
  rw [l1Weighted.mem_iff]
  apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
  intro n hn
  simp only [Finset.mem_range, not_lt] at hn
  simp only [toSeq, mul_eq_zero, abs_eq_zero, dite_eq_right_iff, pow_eq_zero_iff',
    PosReal.coe_ne_zero, ne_eq, false_and, or_false]; intros; omega


/-- The approximate solution as an element of ℓ¹_ν -/
def ApproxSolution.toL1 (sol : ApproxSolution N) : l1Weighted ν :=
  lpWeighted.mk sol.toSeq sol.mem


/-! ## The Block-Diagonal Operator Structure

Following Theorem 7.7.1, the operators A† and A have block-diagonal structure:

A† = [DF⁽ᴺ⁾(ā), 0; 0, 2ā₀·I]
A  = [(DF⁽ᴺ⁾(ā))⁻¹, 0; 0, (1/2ā₀)·I]

This matches the `BlockDiagOp` structure from OperatorNorm.lean.
-/

/-- The approximate inverse A as a block-diagonal operator (equation 7.48).
    - Finite block: A⁽ᴺ⁾ (numerical inverse of DF⁽ᴺ⁾(ā))
    - Tail scalar: 1/(2ā₀) -/
def approxInverse (sol : ApproxSolution N) (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    BlockDiag.BlockDiagOp ν N where
  finBlock := A_fin
  tailScalar := 1 / (2 * sol.aBar_fin 0)

/-- The approximate derivative A† as a block-diagonal operator (equation 7.47).
    - Finite block: DF⁽ᴺ⁾(ā) = 2[ā₀ on diagonal, lower triangular with 2āᵢ₋ⱼ]
    - Tail scalar: 2ā₀ -/
def approxDeriv (sol : ApproxSolution N) : BlockDiag.BlockDiagOp ν N where
  finBlock := Matrix.of fun i j => 2 * sol.aBar_fin ⟨(i : ℕ) - (j : ℕ), by
    by_cases h : (j : ℕ) ≤ i
    · omega
    · simp only [not_le] at h; omega⟩
  tailScalar := 2 * sol.aBar_fin 0


/-! ## The Radii Polynomial Bounds (Theorem 7.7.1)

We now define the Y₀, Z₀, Z₁, Z₂ bounds.
-/

/-- Y₀ bound (equation from Theorem 7.7.1):
    Y₀ = Σₙ₌₀ᴺ |[A⁽ᴺ⁾F⁽ᴺ⁾(ā)]ₙ| νⁿ + (1/2|ā₀|) Σₙ₌ₐᴺ₊₁²ᴺ 2 Σⱼ |āₙ₋ⱼ||āⱼ₋ₙ₊ₙ| νⁿ

    This measures how close ā is to being a true solution. -/
def Y₀_bound (sol : ApproxSolution N) (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (F_fin : Fin (N + 1) → ℝ) : ℝ :=
  -- Finite part: ‖A⁽ᴺ⁾F⁽ᴺ⁾(ā)‖
  ∑ n : Fin (N + 1), |∑ j : Fin (N + 1), A_fin n j * F_fin j| * (ν : ℝ) ^ (n : ℕ) +
  -- Tail part (from Cauchy product of truncated sequence)
  (1 / (2 * |sol.aBar_fin 0|)) * (
    ∑ n ∈ Finset.Icc (N + 1) (2 * N),
      (2 * (∑ k ∈ Finset.Icc (n - N) N,
        |sol.toSeq k| * |sol.toSeq (n - k)|) * (ν : ℝ) ^ n) )

/-- Z₀ bound (equation from Theorem 7.7.1):
    Z₀ = ‖I - A⁽ᴺ⁾DF⁽ᴺ⁾(ā)‖_{1,ν}

    This measures how well A⁽ᴺ⁾ inverts DF⁽ᴺ⁾(ā). -/
def Z₀_bound (A_fin DF_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ℝ :=
  l1Weighted.finWeightedMatrixNorm ν (1 - A_fin * DF_fin)

/-- Z₁ bound (equation from Theorem 7.7.1):
    Z₁ = (1/|ā₀|) Σₙ₌₁ᴺ |āₙ| νⁿ

    This measures the tail contribution from DF(ā) - A†. -/
def Z₁_bound (sol : ApproxSolution N) : ℝ :=
  (1 / |sol.aBar_fin 0|) * ∑ n ∈ Finset.Icc 1 N, |sol.aBar_fin ⟨n, by omega⟩| * (ν : ℝ) ^ n

/-- Z₂ bound (equation from Theorem 7.7.1):
    Z₂ = 2 max(‖A⁽ᴺ⁾‖_{1,ν}, 1/(2|ā₀|))

    This bounds ‖A[DF(c) - DF(ā)]‖ for c in a ball around ā. -/
def Z₂_bound (sol : ApproxSolution N) (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ℝ :=
  2 * max (l1Weighted.finWeightedMatrixNorm ν A_fin) (1 / (2 * |sol.aBar_fin 0|))


/-! ## Main Existence Theorem

Putting it all together: if p(r₀) < 0 for some r₀ > 0, then there exists
a unique solution ã ∈ B_{r₀}(ā) with F(ã) = 0.
-/

/-- The radii polynomial for Example 7.7 -/
def radiiPoly (sol : ApproxSolution N) (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (F_fin : Fin (N + 1) → ℝ) (DF_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (r : ℝ) : ℝ :=
  Z₂_bound sol A_fin * r^2 -
  (1 - Z₀_bound A_fin DF_fin - Z₁_bound sol) * r +
  Y₀_bound sol A_fin F_fin

/-- **Main Theorem**: Existence and uniqueness of Taylor series solution.

    Given:
    - lam0 > 0 (the parameter value)
    - ā⁽ᴺ⁾ ∈ ℝᴺ⁺¹ with ā₀ ≠ 0 (approximate solution)
    - A⁽ᴺ⁾ (numerical inverse of DF⁽ᴺ⁾(ā))
    - r₀ > 0 such that p(r₀) < 0

    Then there exists a unique ã ∈ ℓ¹_ν with:
    - ‖ã - ā‖ < r₀
    - F(ã) = ã ⋆ ã - c = 0

    In other words, x(λ) = Σₙ ãₙ(λ - lam0)ⁿ satisfies x(λ)² - λ = 0
    for |λ - lam0| < ν. -/
theorem existence_theorem
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (F_fin : Fin (N + 1) → ℝ)
    (DF_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (r₀ : ℝ) (hr₀ : 0 < r₀)
    (h_radii : radiiPoly sol A_fin F_fin DF_fin r₀ < 0)
    -- Additional hypotheses connecting the finite data to the infinite problem
    (h_F_fin : ∀ n : Fin (N + 1), F_fin n = (lpWeighted.toSeq (F lam0 sol.toL1) : ℕ → ℝ) n)
    (h_DF_fin : DF_fin = Matrix.of fun i j => 2 * sol.toSeq ((i : ℕ) - (j : ℕ)))
    (h_A_inj : Function.Injective (approxInverse sol A_fin).action) :
    ∃! aTilde ∈ closedBall (sol.toL1 : l1Weighted ν) r₀,
      F lam0 aTilde = 0 := by
  -- The proof would apply general_radii_polynomial_theorem from RadiiPolyGeneral.lean
  -- after constructing the continuous linear map versions of A and A†
  -- and verifying the Y₀, Z₀, Z₁, Z₂ bounds
  sorry


/-! ## Concrete Example: lam0 = 1/3, N = 2

From the textbook (page 175):
- ā = (0.577..., 0.866..., 0.649...)
- ν = 1/4
- r₀ ∈ [0.0367, 0.165]
-/

/-- Concrete values from the textbook example -/
def example_lam0 : ℝ := 1 / 3

def example_ν : PosReal := ⟨1 / 4, by norm_num⟩

def example_N : ℕ := 2

/-- The approximate solution from page 175 -/
def example_aBar : Fin 3 → ℝ
  | 0 => 0.57735026918962
  | 1 => 0.86602540378443
  | 2 => 0.64951905283832

/-- The approximate inverse matrix from page 175 -/
def example_A : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0.86602540378443, 0, 0;
     1.29903810567665, 0.86602540378443, 0;
     2.92283573777248, 1.29903810567665, 0.86602540378443]

end Example_7_7

end

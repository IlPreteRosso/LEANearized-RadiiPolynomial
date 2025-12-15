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

noncomputable section

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

/-- The constant sequence c = (lam0, 1, 0, 0, ...) from equation (7.44).
    This encodes λ = lam0 + t where t = λ - lam0. -/
def paramSeq (lam0 : ℝ) : ℕ → ℝ := fun n =>
  match n with
  | 0 => lam0
  | 1 => 1
  | _ => 0

/-- The constant sequence is in ℓ¹_ν -/
lemma paramSeq_mem {ν : PosReal} (lam0 : ℝ) : lpWeighted.Mem ν 1 (paramSeq lam0) := by
  rw [l1Weighted.mem_iff]
  -- Sum is finite: lam0 + ν + 0 + 0 + ...
  apply summable_of_ne_finset_zero (s := {0, 1})
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  simp [paramSeq, hn.1, hn.2]

/-- The constant sequence as an element of ℓ¹_ν -/
def c {ν : PosReal} (lam0 : ℝ) : l1Weighted ν := lpWeighted.mk (paramSeq lam0) (paramSeq_mem lam0)

/-- c₀ = lam0 -/
@[simp]
lemma c_zero {ν : PosReal} (lam0 : ℝ) : lpWeighted.toSeq (c lam0 : l1Weighted ν) 0 = lam0 := by
  rfl

/-- c₁ = 1 -/
@[simp]
lemma c_one {ν : PosReal} (lam0 : ℝ) : lpWeighted.toSeq (c lam0 : l1Weighted ν) 1 = 1 := by
  rfl

/-- cₙ = 0 for n ≥ 2 -/
@[simp]
lemma c_ge_two {ν : PosReal} (lam0 : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    lpWeighted.toSeq (c lam0 : l1Weighted ν) n = 0 := by
  simp only [c, lpWeighted.mk_apply, paramSeq]
  match n with
  | 0 => omega
  | 1 => omega
  | n + 2 => rfl

/-- Norm of c: ‖c‖ = |lam0| + ν -/
lemma norm_c {ν : PosReal} (lam0 : ℝ) : ‖(c lam0 : l1Weighted ν)‖ = |lam0| + (ν : ℝ) := by
  rw [l1Weighted.norm_eq_tsum]
  have h : (fun n => |lpWeighted.toSeq (c lam0 : l1Weighted ν) n| * (ν : ℝ) ^ n) =
           fun n => if n = 0 then |lam0| else if n = 1 then (ν) else 0 := by
    ext n
    match n with
    | 0 => simp only [lpWeighted.toSeq_apply, pow_zero, mul_one, ↓reduceIte]; rfl
    | 1 =>
      simp only [lpWeighted.toSeq_apply, pow_one, one_ne_zero, ↓reduceIte, ne_eq,
        PosReal.coe_ne_zero, not_false_eq_true, mul_eq_right₀]
      exact abs_one
    | n + 2 =>
      simp only [lpWeighted.toSeq_apply, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero,
        and_false, ↓reduceIte, Nat.reduceEqDiff, mul_eq_zero, abs_eq_zero, ne_eq, not_false_eq_true,
        pow_eq_zero_iff, PosReal.coe_ne_zero, or_false]
      rfl
  rw [h]
  rw [tsum_eq_sum (s := {0, 1})]
  · simp
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp only [hn.1, ↓reduceIte, hn.2]


/-! ## The Zero-Finding Map F

The map F(a) = a ⋆ a - c from equation (7.43).
-/

/-- The zero-finding map F(a) = a ⋆ a - c -/
def F {ν : PosReal} (lam0 : ℝ) (a : l1Weighted ν) : l1Weighted ν :=
  l1Weighted.F_sub_const (c lam0) a

/-- F(a) = sq(a) - c -/
lemma F_eq {ν : PosReal} (lam0 : ℝ) (a : l1Weighted ν) :
    F lam0 a = l1Weighted.sq a - c lam0 := rfl

/-- Component formula for F (equation 7.43):
    F₀(a) = a₀² - lam0
    F₁(a) = 2a₀a₁ - 1
    Fₙ(a) = (a ⋆ a)ₙ for n ≥ 2 -/
lemma F_component {ν : PosReal} (lam0 : ℝ) (a : l1Weighted ν) (n : ℕ) :
    lpWeighted.toSeq (F lam0 a) n =
    (lpWeighted.toSeq a ⋆ lpWeighted.toSeq a) n - lpWeighted.toSeq (ν := ν) (c lam0) n := by
  simp only [F, l1Weighted.F_sub_const, lpWeighted.sub_toSeq, l1Weighted.sq_toSeq]

/-- F is Fréchet differentiable -/
theorem differentiable_F {ν : PosReal} (lam0 : ℝ) : Differentiable ℝ (F lam0 : l1Weighted ν → l1Weighted ν) :=
  l1Weighted.differentiable_F_sub_const (c lam0)

/-- The Fréchet derivative: DF(a)h = 2(a ⋆ h) -/
theorem fderiv_F {ν : PosReal} (lam0 : ℝ) (a : l1Weighted ν) :
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

/-- Structure for an approximate solution (eq. 7.46) -/
structure ApproxSolution where
  /-- The truncated approximate solution ā⁽ᴺ⁾ ∈ ℝᴺ⁺¹ -/
  aBar_fin : Fin (N + 1) → ℝ
  /-- Assumption: ā₀ ≠ 0 (needed for invertibility) -/
  aBar_zero_ne : aBar_fin 0 ≠ 0

/-- Extend the finite approximate solution to a sequence (zero-padded) -/
def ApproxSolution.toSeq {N : ℕ} (sol : ApproxSolution N) : ℕ → ℝ := fun n =>
  if h : n ≤ N then sol.aBar_fin ⟨n, Nat.lt_succ_of_le h⟩ else 0

/-- The extended sequence is in ℓ¹_ν -/
lemma ApproxSolution.mem {N : ℕ} (sol : ApproxSolution N) : lpWeighted.Mem ν 1 sol.toSeq := by
  rw [l1Weighted.mem_iff]
  apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
  intro n hn
  simp only [Finset.mem_range, not_lt] at hn
  simp only [toSeq, mul_eq_zero, abs_eq_zero, dite_eq_right_iff, pow_eq_zero_iff',
    PosReal.coe_ne_zero, ne_eq, false_and, or_false]; intros; omega

/-- The approximate solution as an element of ℓ¹_ν -/
def ApproxSolution.toL1 {N : ℕ} (sol : ApproxSolution N) : l1Weighted ν :=
  lpWeighted.mk sol.toSeq sol.mem

@[simp]
lemma ApproxSolution.toL1_toSeq {N : ℕ} (sol : ApproxSolution N) :
    lpWeighted.toSeq (sol.toL1 : l1Weighted ν) = sol.toSeq := rfl


/-! ## The Block-Diagonal Operator Structure

Following Theorem 7.7.1, the operators A† and A have block-diagonal structure:

A† = [DF⁽ᴺ⁾(ā),    0 ;
            0 , 2ā₀·I]
A  = [(DF⁽ᴺ⁾(ā))⁻¹,        0 ;
                0 , (1/2ā₀)·I]

This matches the `BlockDiagOp` structure from OperatorNorm.lean.
-/

/-! ## Computed Finite Projections

These definitions compute F⁽ᴺ⁾(ā) and DF⁽ᴺ⁾(ā) directly from the definitions,
rather than taking them as hypotheses. This is more honest to the textbook setup.
-/

/-- F⁽ᴺ⁾(ā): the first N+1 components of F(ā) = ā⋆ā - c -/
def F_fin {ν : PosReal} {N : ℕ} (lam0 : ℝ) (sol : ApproxSolution N) : Fin (N + 1) → ℝ :=
  fun n => lpWeighted.toSeq (F (ν := ν) lam0 sol.toL1) n

/-- DF⁽ᴺ⁾(ā): the (N+1)×(N+1) lower triangular matrix with entries 2āᵢ₋ⱼ for j ≤ i -/
def DF_fin {N : ℕ} (sol : ApproxSolution N) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun i j => if h : (j : ℕ) ≤ i then 2 * sol.aBar_fin ⟨(i : ℕ) - (j : ℕ), by omega⟩ else 0

/-- The approximate inverse A as a block-diagonal operator (equation 7.48).
    - Finite block: A⁽ᴺ⁾ (numerical inverse of DF⁽ᴺ⁾(ā))
    - Tail scalar: 1/(2ā₀) -/
def approxInverse {N : ℕ} (sol : ApproxSolution N) (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    BlockDiag.BlockDiagOp ν N where
  finBlock := A_fin
  tailScalar := 1 / (2 * sol.aBar_fin 0)

/-- The approximate derivative A† as a block-diagonal operator (equation 7.47).
    - Finite block: DF⁽ᴺ⁾(ā) = lower triangular with (DF)_{i,j} = 2ā_{i-j} for j ≤ i, 0 otherwise
    - Tail scalar: 2ā₀ -/
def approxDeriv {N : ℕ} (sol : ApproxSolution N) : BlockDiag.BlockDiagOp ν N where
  finBlock := Matrix.of fun i j =>
    if (j : ℕ) ≤ i then 2 * sol.aBar_fin ⟨(i : ℕ) - (j : ℕ), by omega⟩ else 0
  tailScalar := 2 * sol.aBar_fin 0


/-! ## The Radii Polynomial Bounds (Theorem 7.7.1)

We now define the Y₀, Z₀, Z₁, Z₂ bounds.
-/

section RadiiPolyBounds

/-- Y₀ bound (equation from Theorem 7.7.1):
    Y₀ = Σₙ₌₀ᴺ |[A⁽ᴺ⁾F⁽ᴺ⁾(ā)]ₙ| νⁿ + (1/2|ā₀|) Σₙ₌ₙ₊₁²ᴺ (Σⱼ₌₀^{2N-n} |ā_{N-j}||ā_{n-N+j}|) νⁿ

    Equivalently with index k = N - j: Σₖ₌ₙ₋ₙᴺ |āₖ||āₙ₋ₖ|

    Note: The textbook has a typo with inner sum ∑ⱼ₌₀^{N-n} but this is empty for n > N.
    The correct range is ∑ⱼ₌₀^{2N-n}, which corresponds to k ∈ [n-N, N].

    This measures how close ā is to being a true solution. -/
def Y₀_bound {ν : PosReal} {N : ℕ} (lam0 : ℝ) (sol : ApproxSolution N) (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ℝ :=
  let ā := sol.toSeq
  let F_fin := F_fin (ν := ν) lam0 sol
  -- Finite part: ‖A⁽ᴺ⁾F⁽ᴺ⁾(ā)‖
  ∑ n : Fin (N + 1), |∑ j : Fin (N + 1), A_fin n j * F_fin j| * (ν : ℝ) ^ (n : ℕ) +
  -- Tail part: (1/2|ā₀|) Σₙ₌ₙ₊₁²ᴺ (Σₖ |āₖ||āₙ₋ₖ|) νⁿ
  (1 / (2 * |sol.aBar_fin 0|)) *
    ∑ n ∈ Finset.Icc (N + 1) (2 * N),
      (∑ k ∈ Finset.Icc (n - N) N, |ā k| * |ā (n - k)|) * (ν : ℝ) ^ n

/-- Z₀ bound (equation from Theorem 7.7.1):
    Z₀ = ‖I - A⁽ᴺ⁾DF⁽ᴺ⁾(ā)‖_{1,ν}

    This measures how well A⁽ᴺ⁾ inverts DF⁽ᴺ⁾(ā). -/
def Z₀_bound {ν : PosReal} {N : ℕ} (sol : ApproxSolution N) (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ℝ :=
  l1Weighted.finWeightedMatrixNorm ν (1 - A_fin * DF_fin sol)

/-- Z₁ bound (equation from Theorem 7.7.1):
    Z₁ = (1/|ā₀|) Σₙ₌₁ᴺ |āₙ| νⁿ

    This measures the tail contribution from DF(ā) - A†. -/
def Z₁_bound {ν : PosReal} {N : ℕ} (sol : ApproxSolution N) : ℝ :=
  let ā := sol.toSeq
  (1 / |sol.aBar_fin 0|) * ∑ n ∈ Finset.Icc 1 N, |ā n| * (ν : ℝ) ^ n

/-- Z₂ bound (equation from Theorem 7.7.1):
    Z₂ = 2 max(‖A⁽ᴺ⁾‖_{1,ν}, 1/(2|ā₀|))

    This bounds ‖A[DF(c) - DF(ā)]‖ for c in a ball around ā. -/
def Z₂_bound {ν : PosReal} {N : ℕ} (sol : ApproxSolution N) (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ℝ :=
  2 * max (l1Weighted.finWeightedMatrixNorm ν A_fin) (1 / (2 * |sol.aBar_fin 0|))

end RadiiPolyBounds



/-- The radii polynomial for Example 7.7, using the general definition from RadiiPolyGeneral.lean.

    Note: Z₂ is constant in this example (doesn't depend on r). -/
def radiiPoly_7_7 (lam0 : ℝ) (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (r : ℝ) : ℝ :=
  generalRadiiPolynomial
    (@Y₀_bound ν N lam0 sol A_fin)
    (@Z₀_bound ν N sol A_fin)
    (@Z₁_bound ν N sol)
    (fun _ => @Z₂_bound ν N sol A_fin)
    r



/-! ## Helper Lemmas for Y₀ Bound (Theorem 7.7.1)

These lemmas break down the proof of `Y₀_bound_valid` into manageable subgoals.

Key observations:
1. ā is zero-padded: āₙ = 0 for n > N
2. Therefore (ā ⋆ ā)ₙ = 0 for n > 2N
3. F(ā) = ā ⋆ ā - c where c = (λ₀, 1, 0, 0, ...)
4. The block-diagonal operator A acts as A⁽ᴺ⁾ on [0,N] and 1/(2ā₀) on (N,∞)
-/

section Y0BoundLemmas

/-- āₙ = 0 for n > N, where
    ā = ApproxSolution.toSeq sol = (ā₀, ā₁, ..., āₙ, 0, 0, 0, ...) -/
lemma toSeq_zero_of_gt {N : ℕ} (sol : ApproxSolution N) (n : ℕ) (hn : N < n) :
    (sol.toSeq) n = 0 := by
  simp only [ApproxSolution.toSeq, not_le.mpr hn, ↓reduceDIte]

/-- The finite part of ā equals ā_fin -/
lemma toSeq_eq_aBar_fin {N : ℕ} (sol : ApproxSolution N) (n : Fin (N + 1)) :
    (sol.toSeq) n = sol.aBar_fin n := by
  simp only [ApproxSolution.toSeq, Fin.is_le, ↓reduceDIte]

/-- (ā ⋆ ā)ₙ = 0 for n > 2N since ā has support in [0,N] -/
lemma cauchyProduct_toSeq_zero_of_gt_two_N {N : ℕ} (sol : ApproxSolution N) (n : ℕ) (hn : 2 * N < n) :
    (sol.toSeq ⋆ sol.toSeq) n = 0 :=
  CauchyProduct.zero_of_support (toSeq_zero_of_gt sol) (toSeq_zero_of_gt sol) n hn

/-- F(ā)ₙ = (ā ⋆ ā)ₙ for n ≥ 2, since cₙ = 0, where c = (λ₀, 1, 0, 0, ...) -/
lemma F_component_tail' (lam0 : ℝ) (a : ℕ → ℝ) (n : ℕ) (hn : 2 ≤ n) :
    (a ⋆ a) n - paramSeq lam0 n = (a ⋆ a) n := by
  simp only [paramSeq]
  match n with
  | 0 => omega
  | 1 => omega
  | n + 2 => simp

/-- F(ā)ₙ = 0 for n > 2N (requires N ≥ 1) -/
lemma F_toSeq_zero_of_gt_two_N {N : ℕ} (lam0 : ℝ) (sol : ApproxSolution N) (n : ℕ)
    (hN : 0 < N) (hn : 2 * N < n) :
    (sol.toSeq ⋆ sol.toSeq) n - paramSeq lam0 n = 0 := by
  have h1 : (sol.toSeq ⋆ sol.toSeq) n = 0 := cauchyProduct_toSeq_zero_of_gt_two_N sol n hn
  have h2 : paramSeq lam0 n = 0 := by
    simp only [paramSeq]
    match n with
    | 0 => omega
    | 1 => omega
    | _ + 2 => rfl
  simp [h1, h2]

/-- Action of approxInverse `A` on finite indices (n ≤ N)
    Needed to compute [A(F(ā))]ₙ for 0 ≤ n ≤ N -/
lemma approxInverse_action_finite {N : ℕ} (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (x : ℕ → ℝ) (n : ℕ) (hn : n ≤ N) :
    (@approxInverse ν N sol A_fin).action x n =
    ∑ j : Fin (N + 1), A_fin ⟨n, Nat.lt_succ_of_le hn⟩ j * x j := by
  simp only [approxInverse, BlockDiag.BlockDiagOp.action, hn, ↓reduceDIte]

/-- Action of approxInverse `A` on tail indices (n > N)
    Needed to compute [A(F(ā))]ₙ for N < n ≤ 2N -/
lemma approxInverse_action_tail {N : ℕ} (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (x : ℕ → ℝ) (n : ℕ) (hn : N < n) :
    (@approxInverse ν N sol A_fin).action x n = (1 / (2 * sol.aBar_fin 0)) * x n := by
  simp only [approxInverse, BlockDiag.BlockDiagOp.action, not_le.mpr hn, ↓reduceDIte]

/-- [A(F(ā))]ₙ = 0 for n > 2N -/
lemma approxInverse_F_action_zero_of_gt_two_N {N : ℕ} (lam0 : ℝ) (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (n : ℕ) (hN : 0 < N) (hn : 2 * N < n) :
    (@approxInverse ν N sol A_fin).action
      (fun k => (sol.toSeq ⋆ sol.toSeq) k - paramSeq lam0 k) n = 0 := by
  have hn' : N < n := Nat.lt_of_lt_of_le (by omega : N < 2 * N) (Nat.le_of_lt hn)
  rw [approxInverse_action_tail sol A_fin _ n hn']
  rw [F_toSeq_zero_of_gt_two_N lam0 sol n hN hn]
  ring

/-- ‖`A(F(ā))`‖₁,ν (in summation notation) is a finite sum over [N+1, 2N] -/
lemma tail_tsum_eq_Icc_sum {N : ℕ} (lam0 : ℝ) (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hN : 0 < N) :
    ∑' n : {n : ℕ // N < n},
      |(@approxInverse ν N sol A_fin).action
        (fun k => (sol.toSeq ⋆ sol.toSeq) k - paramSeq lam0 k) n| * (ν : ℝ) ^ (n : ℕ) =
    ∑ n ∈ Finset.Icc (N + 1) (2 * N),
      |(@approxInverse ν N sol A_fin).action
        (fun k => (sol.toSeq ⋆ sol.toSeq) k - paramSeq lam0 k) n| * (ν : ℝ) ^ n := by
  -- WTS: The function is zero outside [N+1, 2N]
  -- f: {n : ℕ // N < n} → ℝ
  --                  n  ↦ |A.action (ā ⋆ ā - c) n| * ν^n ≃ |[A(F(ā))]ₙ| * νⁿ
  let f := fun n : {n : ℕ // N < n} =>
    |(@approxInverse ν N sol A_fin).action
      (fun k => (sol.toSeq ⋆ sol.toSeq) k - paramSeq lam0 k) n| * (ν : ℝ) ^ (n : ℕ)
  have hf_zero : ∀ n : {n : ℕ // N < n}, 2 * N < n → f n = 0 := by
    intro ⟨n, hn⟩ h2N
    simp only [f]
    rw [approxInverse_F_action_zero_of_gt_two_N lam0 sol A_fin n hN h2N]
    simp only [abs_zero, zero_mul]
  -- Convert subtype tsum to a sum over the finite set
  have hsummable : Summable f := by
    apply summable_of_ne_finset_zero (s := (Finset.Icc (N + 1) (2 * N)).subtype (fun n => N < n))
    intro ⟨n, hn⟩ hn_notin
    simp only [Finset.mem_subtype, Finset.mem_Icc, not_and, not_le] at hn_notin
    exact hf_zero ⟨n, hn⟩ (hn_notin (Nat.succ_le_of_lt hn))
  have h_icc_lt : ∀ n, n ∈ Finset.Icc (N + 1) (2 * N) → N < n := by
    intro n hn; simp only [Finset.mem_Icc] at hn; omega
  rw [tsum_eq_sum (s := (Finset.Icc (N + 1) (2 * N)).subtype (fun n => N < n))]
  · -- Reindex from subtype to Icc
    conv_lhs =>
      rw [show (Finset.Icc (N + 1) (2 * N)).subtype (fun n => N < n) =
            (Finset.Icc (N + 1) (2 * N)).attach.map
              ⟨fun x => ⟨x.1, h_icc_lt x.1 x.2⟩,
              fun a b h => by simp only [Subtype.mk.injEq] at h; ext; exact h⟩ from by
          ext ⟨n, hn⟩; simp [Finset.mem_subtype, Finset.mem_Icc]]
    simpa only [Finset.sum_map, Function.Embedding.coeFn_mk] using
    (Finset.sum_attach
      (s := Finset.Icc (N + 1) (2 * N))
      (f :=
        fun x =>
          |(approxInverse sol A_fin).action
            (fun k =>
              (sol.toSeq ⋆ sol.toSeq) k -
              paramSeq lam0 k
            ) ↑x| * (↑ν : ℝ) ^ (↑x : ℕ)
      )
    )
  · intro ⟨n, hn⟩ hn_notin
    simp only [Finset.mem_subtype, Finset.mem_Icc, not_and, not_le] at hn_notin
    exact hf_zero ⟨n, hn⟩ (hn_notin (Nat.succ_le_of_lt hn))

/-- Range of nonzero terms in Cauchy product for N < n ≤ 2N -/
lemma cauchyProduct_middle_range {N : ℕ} (sol : ApproxSolution N) (n : ℕ)
    (hn_lower : N + 1 ≤ n) :
    (sol.toSeq ⋆ sol.toSeq) n =
    ∑ k ∈ Finset.Icc (n - N) N, (sol.toSeq) k * (sol.toSeq) (n - k) := by
  rw [CauchyProduct.apply_range]
  -- Convert ∑ j, a(n-j)*a(j) to ∑ k, a(k)*a(n-k) using mul_comm
  conv_lhs => arg 2; ext j; rw [mul_comm]
  -- Now restrict sum to Icc (n-N) N
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  · intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc, not_and, not_le] at hk
    by_cases hk_small : k < n - N
    · have hl : N < n - k := by omega
      simp [toSeq_zero_of_gt sol (n - k) hl]
    · push_neg at hk_small
      have hk' : N < k := hk.2 hk_small
      simp [toSeq_zero_of_gt sol k hk']
  · intro k hk
    rfl

/-- Bound on middle Cauchy product using absolute values -/
lemma cauchyProduct_middle_abs_bound {N : ℕ} (sol : ApproxSolution N) (n : ℕ)
    (hn_lower : N + 1 ≤ n) :
    |(sol.toSeq ⋆ sol.toSeq) n| ≤
    ∑ k ∈ Finset.Icc (n - N) N, |(sol.toSeq) k| * |(sol.toSeq) (n - k)| := by
  rw [cauchyProduct_middle_range sol n hn_lower]
  calc |∑ k ∈ Finset.Icc (n - N) N, (sol.toSeq) k * (sol.toSeq) (n - k)|
      ≤ ∑ k ∈ Finset.Icc (n - N) N, |(sol.toSeq) k * (sol.toSeq) (n - k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ Finset.Icc (n - N) N, |(sol.toSeq) k| * |(sol.toSeq) (n - k)| := by
        simp_rw [abs_mul]

end Y0BoundLemmas

/-! ## Helper Lemmas for Z₀ Bound (Theorem 7.7.1)

These lemmas break down the proof of `Z₀_bound_valid` into manageable subgoals.

Key observations from the textbook (page 173):
1. approxDeriv.finBlock = DF_fin sol (both are 2āᵢ₋ⱼ)
2. Tail scalars multiply to 1: (1/(2ā₀)) * (2ā₀) = 1
3. Therefore I - AA† = 0 on tail
4. On finite: I - AA† = I - A_fin * DF_fin
-/

section Z0BoundLemmas

/-- approxDeriv finite block equals DF_fin -/
lemma approxDeriv_finBlock_eq_DF_fin {N : ℕ} (sol : ApproxSolution N) :
    (@approxDeriv ν N sol).finBlock = DF_fin sol := rfl

/-- Tail scalars of A and A† multiply to 1 -/
lemma tail_scalars_mul_eq_one {N : ℕ} (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (h : sol.aBar_fin 0 ≠ 0) :
    (@approxInverse ν N sol A_fin).tailScalar * (@approxDeriv ν N sol).tailScalar = 1 := by
  simp only [approxInverse, approxDeriv]
  field_simp

/-- The composition AA† has tail scalar 1 -/
lemma comp_tail_scalar_eq_one {N : ℕ} (sol : ApproxSolution N) (h : sol.aBar_fin 0 ≠ 0) :
    (1 / (2 * sol.aBar_fin 0)) * (2 * sol.aBar_fin 0) = 1 := by
  field_simp

/-- toSeq of A†.toCLM equals A†.action of toSeq -/
lemma approxDeriv_toSeq_eq_action {N : ℕ} (sol : ApproxSolution N) (h : l1Weighted ν) :
    lpWeighted.toSeq ((@approxDeriv ν N sol).toCLM h) =
    (@approxDeriv ν N sol).action (lpWeighted.toSeq h) :=
  funext (fun m => BlockDiag.BlockDiagOp.toCLM_apply _ _ m)

/-- toSeq of A.toCLM equals A.action of toSeq -/
lemma approxInverse_toSeq_eq_action {N : ℕ} (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (h : l1Weighted ν) :
    lpWeighted.toSeq ((@approxInverse ν N sol A_fin).toCLM h) =
    (@approxInverse ν N sol A_fin).action (lpWeighted.toSeq h) :=
  funext (fun m => BlockDiag.BlockDiagOp.toCLM_apply _ _ m)

/-- Action of (I - AA†) on tail is zero -/
lemma I_sub_comp_action_tail_eq_zero {N : ℕ} (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (h : l1Weighted ν) (n : ℕ) (hn : N < n) :
    lpWeighted.toSeq h n -
      lpWeighted.toSeq ((@approxInverse ν N sol A_fin).toCLM
        ((@approxDeriv ν N sol).toCLM h)) n = 0 := by
  rw [BlockDiag.BlockDiagOp.toCLM_apply, approxDeriv_toSeq_eq_action]
  simp only [BlockDiag.BlockDiagOp.action, not_le.mpr hn, ↓reduceDIte,
             approxInverse, approxDeriv]
  field_simp [sol.aBar_zero_ne]; ring

/-- Action of (I - AA†) on finite equals (I - A_fin * DF_fin) h^(N) -/
lemma I_sub_comp_action_finite_eq {N : ℕ} (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (h : l1Weighted ν) (n : Fin (N + 1)) :
    lpWeighted.toSeq h n -
      lpWeighted.toSeq ((@approxInverse ν N sol A_fin).toCLM
        ((@approxDeriv ν N sol).toCLM h)) n =
    ∑ j : Fin (N + 1), (1 - A_fin * (@approxDeriv ν N sol).finBlock) n j * lpWeighted.toSeq h j := by
  rw [BlockDiag.BlockDiagOp.toCLM_apply, approxDeriv_toSeq_eq_action]
  simp only [BlockDiag.BlockDiagOp.action, Fin.is_le, ↓reduceDIte, approxInverse]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply]
  simp only [lpWeighted.toSeq_apply, Fin.eta]
  ring_nf
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, sub_right_inj]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext j
  rw [Finset.sum_mul]
  congr 1; ext k
  ring

/-- The tail contribution of (I - AA†)h is zero in the ℓ¹_ν norm.
    This follows from I_sub_comp_action_tail_eq_zero: each term is zero. -/
lemma I_sub_comp_tail_tsum_zero {N : ℕ} (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (h : l1Weighted ν) :
    ∑' n : {n : ℕ // N < n},
      |lpWeighted.toSeq ((ContinuousLinearMap.id ℝ (l1Weighted ν) -
        (@approxInverse ν N sol A_fin).toCLM.comp (@approxDeriv ν N sol).toCLM) h) n| * (ν : ℝ) ^ (n : ℕ) = 0 := by
  have h_eq : ∀ n : {n : ℕ // N < n},
      |lpWeighted.toSeq ((ContinuousLinearMap.id ℝ (l1Weighted ν) -
        (@approxInverse ν N sol A_fin).toCLM.comp (@approxDeriv ν N sol).toCLM) h) n| * (ν : ℝ) ^ (n : ℕ) = 0 := by
    intro ⟨n, hn⟩
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_id', id_eq,
               ContinuousLinearMap.coe_comp', Function.comp_apply, lpWeighted.sub_toSeq]
    have := I_sub_comp_action_tail_eq_zero sol A_fin h n hn
    rw [sub_eq_zero] at this
    rw [this, sub_self, abs_zero, zero_mul]
  simp only [h_eq, tsum_zero]

/-- The finite part of (I - AA†)h equals (I - A_fin * DF_fin) applied to h^(N).
    Converts CLM action to matrix multiplication form. -/
lemma I_sub_comp_finite_toSeq_eq {N : ℕ} (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (h : l1Weighted ν) (n : Fin (N + 1)) :
    lpWeighted.toSeq ((ContinuousLinearMap.id ℝ (l1Weighted ν) -
      (@approxInverse ν N sol A_fin).toCLM.comp (@approxDeriv ν N sol).toCLM) h) n =
    ∑ j : Fin (N + 1), (1 - A_fin * (@approxDeriv ν N sol).finBlock) n j * lpWeighted.toSeq h j := by
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_id', id_eq,
             ContinuousLinearMap.coe_comp', Function.comp_apply, lpWeighted.sub_toSeq]
  exact I_sub_comp_action_finite_eq sol A_fin h n

end Z0BoundLemmas

section Z1BoundLemmas

/-- DF(ā) - A† is zero on finite block [0,N].
    From page 173: [(DF(ā) - A†)h]_n = [DF^(N)(ā)h^(N)]_n - [DF^(N)(ā)h^(N)]_n = 0
    Both operators agree on finite because A† IS defined as DF^(N)(ā) on this block. -/
lemma DF_sub_approxDeriv_finite_eq_zero {N : ℕ} (lam0 : ℝ) (sol : ApproxSolution N)
    (h : l1Weighted ν) (n : Fin (N + 1)) :
    lpWeighted.toSeq (fderiv ℝ (F lam0) sol.toL1 h - (@approxDeriv ν N sol).toCLM h) n = 0 := by
  rw [fderiv_F lam0 sol.toL1]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, lpWeighted.sub_toSeq,
             lpWeighted.smul_toSeq]
  rw [l1Weighted.leftMul_toSeq, BlockDiag.BlockDiagOp.toCLM_apply]
  simp only [BlockDiag.BlockDiagOp.action, Fin.is_le, ↓reduceDIte, approxDeriv,
             ApproxSolution.toL1_toSeq, Matrix.of_apply]
  -- Goal: 2*(ā⋆h)_n - ∑_{j : Fin(N+1)} (if j ≤ n then 2*ā_{n-j} else 0)*h_j = 0
  rw [sub_eq_zero, CauchyProduct.apply_range]
  -- LHS: (∑_{j ∈ range(n+1)} ā_{n-j}*h_j) * 2
  -- RHS: ∑_{j : Fin(N+1)} (if j ≤ n then 2*ā_{n-j} else 0)*h_j
  -- Rewrite RHS: (if c then a else 0) * b = if c then a*b else 0
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  -- RHS: ∑_{j ∈ filter (· ≤ n) univ} 2*ā_{n-j}*h_j
  trans (∑ j ∈ Finset.range (n + 1), 2 * (sol.toSeq) (n - j) * lpWeighted.toSeq h j)
  · rw [Finset.mul_sum]; congr 1; ext j; ring
  · -- Match filtered Fin sum with range sum
    -- rw [Finset.sum_filter]
    -- LHS sums over ℕ in range(n+1), RHS sums over Fin(N+1) with conditional
    apply Finset.sum_bij'
        (fun k (hk : k ∈ Finset.range (n + 1)) => Fin.mk k (by simp only [Finset.mem_range] at hk; omega))
        (fun (j : Fin (N + 1)) _ => (j : ℕ))
    · intro k hk
      have hk' : k ≤ (n : ℕ) :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp only [Fin.val_fin_le, Finset.mem_filter, Finset.mem_univ, true_and, ge_iff_le]
      simpa [Fin.le_iff_val_le_val] using hk'
    · intro j _; rfl
    · intro k hk; simp only [Fin.eta]
    · intro j hj
      -- `if` goes to the `then` branch and `toSeq` becomes `aBar_fin`
      simp [toSeq_eq_aBar_fin sol ⟨(n : ℕ) - j, by omega⟩]
    · intro k hk
      have hk' : (k : ℕ) ≤ n := by
        simpa [Finset.mem_filter, Finset.mem_univ] using hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk')

/-- DF(ā) - A† on tail (n > N) equals 2∑_{j=1}^N h_{n-j}ā_j.
    Since ā_k = 0 for k > N, (ā⋆h)_n - ā₀h_n = ∑_{j=1}^N h_{n-j}ā_j. -/
lemma DF_sub_approxDeriv_tail {N : ℕ} (lam0 : ℝ) (sol : ApproxSolution N)
    (h : l1Weighted ν) (n : ℕ) (hn : N < n) :
    lpWeighted.toSeq (fderiv ℝ (F lam0) sol.toL1 h - (@approxDeriv ν N sol).toCLM h) n =
    2 * ∑ j ∈ Finset.Icc 1 N, lpWeighted.toSeq h (n - j) * (sol.toSeq) j := by
  rw [fderiv_F lam0 sol.toL1]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, lpWeighted.sub_toSeq,
             lpWeighted.smul_toSeq]
  rw [l1Weighted.leftMul_toSeq, BlockDiag.BlockDiagOp.toCLM_apply]
  simp only [BlockDiag.BlockDiagOp.action, not_le.mpr hn, ↓reduceDIte, approxDeriv,
             ApproxSolution.toL1_toSeq]
  -- Goal: 2*(ā⋆h)_n - 2*ā₀*h_n = 2*∑_{j=1}^N h_{n-j}*ā_j
  rw [CauchyProduct.apply_of_support_le_split (toSeq_zero_of_gt sol) hn]
  -- Now: 2*(ā₀*h_n + ∑_{k=1}^N ā_k*h_{n-k}) - 2*ā₀*h_n = 2*∑_{j=1}^N h_{n-j}*ā_j
  have h0 : sol.toSeq 0 = sol.aBar_fin 0 := toSeq_eq_aBar_fin sol ⟨0, Nat.zero_lt_succ N⟩
  rw [h0]
  ring_nf
  congr 1
  apply Finset.sum_congr rfl; intro k _
  ring

/-- A(DF(ā) - A†) is zero on finite block.
    Since DF(ā) - A† = 0 on finite, applying A preserves this. -/
lemma A_DF_sub_approxDeriv_finite_eq_zero {N : ℕ} (lam0 : ℝ) (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (h : l1Weighted ν) (n : Fin (N + 1)) :
    lpWeighted.toSeq ((@approxInverse ν N sol A_fin).toCLM
      (fderiv ℝ (F lam0) sol.toL1 h - (@approxDeriv ν N sol).toCLM h)) n = 0 := by
  rw [BlockDiag.BlockDiagOp.toCLM_apply]
  simp only [BlockDiag.BlockDiagOp.action, Fin.is_le, ↓reduceDIte, approxInverse]
  -- The finite block is A_fin applied to (DF - A†)h^(N) = 0
  apply Finset.sum_eq_zero; intro j _
  rw [DF_sub_approxDeriv_finite_eq_zero lam0 sol h j, mul_zero]

/-- A(DF(ā) - A†) on tail equals (1/ā₀)∑_{j=1}^N h_{n-j}ā_j.
    From textbook page 174. -/
lemma A_DF_sub_approxDeriv_tail {N : ℕ} (lam0 : ℝ) (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (h : l1Weighted ν) (n : ℕ) (hn : N < n) :
    lpWeighted.toSeq ((@approxInverse ν N sol A_fin).toCLM
      (fderiv ℝ (F lam0) sol.toL1 h - (@approxDeriv ν N sol).toCLM h)) n =
    (1 / sol.aBar_fin 0) * ∑ j ∈ Finset.Icc 1 N, lpWeighted.toSeq h (n - j) * (sol.toSeq) j := by
  rw [BlockDiag.BlockDiagOp.toCLM_apply]
  simp only [BlockDiag.BlockDiagOp.action, not_le.mpr hn, ↓reduceDIte, approxInverse]
  -- Tail: (1/(2ā₀)) * (DF - A†)h_n = (1/(2ā₀)) * 2∑_{j=1}^N h_{n-j}ā_j = (1/ā₀)∑...
  rw [DF_sub_approxDeriv_tail lam0 sol h n hn]
  field_simp [sol.aBar_zero_ne]

/-- The shifted sequence â = (0, ā₁, ..., āₙ, 0, ...) used in Z₁ bound -/
def shiftedSeq {N : ℕ} (sol : ApproxSolution N) : ℕ → ℝ :=
  fun k => if k ∈ Finset.Icc 1 N then sol.toSeq k else 0

/-- The shifted sequence has finite support in [1, N] -/
lemma shiftedSeq_support {N : ℕ} (sol : ApproxSolution N) (k : ℕ) (hk : k ∉ Finset.Icc 1 N) :
    shiftedSeq sol k = 0 := by simp [shiftedSeq, hk]

/-- Inner sum equals Cauchy product for n > N -/
lemma inner_sum_eq_cauchy {N : ℕ} (sol : ApproxSolution N) (h : l1Weighted ν) (n : ℕ) (hn : N < n) :
    ∑ j ∈ Finset.Icc 1 N, lpWeighted.toSeq h (n - j) * sol.toSeq j =
    (lpWeighted.toSeq h ⋆ shiftedSeq sol) n := by
  rw [CauchyProduct.apply_range]
  -- Goal: ∑ j ∈ range(n+1), h(n-j) * shiftedSeq(j) = ∑ j ∈ Icc 1 N, h(n-j) * sol(j)
  apply Finset.sum_subset_zero_on_sdiff
  · -- Icc 1 N ⊆ range (n + 1)
    intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
  · -- Terms outside Icc 1 N are zero
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc, not_and, not_le] at hk
    simp only [shiftedSeq]
    have : k ∉ Finset.Icc 1 N := by simp only [Finset.mem_Icc, not_and, not_le]; omega
    simp [this]
  · -- Summands match on Icc 1 N
    intro k hk
    simp only [shiftedSeq, hk, ↓reduceIte]

/-- The shifted sequence is in ℓ¹_ν (finite support) -/
lemma shiftedSeq_mem {N : ℕ} (sol : ApproxSolution N) : lpWeighted.Mem ν 1 (shiftedSeq sol) := by
  rw [l1Weighted.mem_iff]
  apply summable_of_ne_finset_zero (s := Finset.Icc 1 N)
  intro n hn
  simp only [shiftedSeq_support sol n hn, abs_zero, zero_mul]

/-- The shifted sequence as an element of ℓ¹_ν -/
def shiftedL1 {N : ℕ} (sol : ApproxSolution N) : l1Weighted ν :=
  lpWeighted.mk (shiftedSeq sol) (shiftedSeq_mem sol)

/-- Norm of shifted sequence equals finite sum -/
lemma shiftedL1_norm {N : ℕ} (sol : ApproxSolution N) :
    ‖@shiftedL1 ν N sol‖ = ∑ n ∈ Finset.Icc 1 N, |sol.toSeq n| * (ν : ℝ) ^ n := by
  rw [l1Weighted.norm_eq_tsum]
  have h_eq : ∀ n, |lpWeighted.toSeq (@shiftedL1 ν N sol) n| * (ν : ℝ) ^ n =
      if n ∈ Finset.Icc 1 N then |sol.toSeq n| * (ν : ℝ) ^ n else 0 := by
    intro n
    simp only [shiftedL1, lpWeighted.mk_apply, shiftedSeq]
    split_ifs with h
    · rfl
    · simp [abs_zero]
  simp_rw [h_eq]
  rw [tsum_eq_sum]
  · apply Finset.sum_congr rfl; intro n hn; simp [hn]
  · intro n hn; simp [hn]

/-- Key bound for Z₁: tail sum bounded by Cauchy product norm -/
lemma tail_cauchy_bound {N : ℕ} (sol : ApproxSolution N) (h : l1Weighted ν) :
    ∑' n : {n : ℕ // N < n}, |∑ j ∈ Finset.Icc 1 N, lpWeighted.toSeq h (n - j) * sol.toSeq j| * (ν : ℝ) ^ (n : ℕ) ≤
    ‖h‖ * ∑ n ∈ Finset.Icc 1 N, |sol.toSeq n| * (ν : ℝ) ^ n := by
  -- Rewrite inner sum as Cauchy product
  have h_inner : ∀ n : {n : ℕ // N < n},
      |∑ j ∈ Finset.Icc 1 N, lpWeighted.toSeq h (n - j) * sol.toSeq j| * (ν : ℝ) ^ (n : ℕ) =
      |(lpWeighted.toSeq h ⋆ shiftedSeq sol) n| * (ν : ℝ) ^ (n : ℕ) := by
    intro ⟨n, hn⟩; rw [inner_sum_eq_cauchy sol h n hn]
  simp_rw [h_inner]
  -- Bound tail by full norm using norm_split
  have h_tail_le : ∑' n : {n : ℕ // N < n}, |(lpWeighted.toSeq h ⋆ shiftedSeq sol) n| * (ν : ℝ) ^ (n : ℕ) ≤
      ‖CauchyProductBanachAlgebra.mul h (@shiftedL1 ν N sol)‖ := by
    rw [BlockDiag.norm_split (N := N)]
    apply le_add_of_nonneg_left
    apply Finset.sum_nonneg; intro n _
    exact mul_nonneg (abs_nonneg _) (pow_nonneg (le_of_lt ν.property) _)
  -- Apply submultiplicativity
  calc ∑' n : {n : ℕ // N < n}, |(lpWeighted.toSeq h ⋆ shiftedSeq sol) n| * (ν : ℝ) ^ (n : ℕ)
    ≤ ‖CauchyProductBanachAlgebra.mul h (@shiftedL1 ν N sol)‖ := h_tail_le
    _ ≤ ‖h‖ * ‖@shiftedL1 ν N sol‖ := CauchyProductBanachAlgebra.norm_mul_le h _
    _ = ‖h‖ * ∑ n ∈ Finset.Icc 1 N, |sol.toSeq n| * (ν : ℝ) ^ n := by rw [shiftedL1_norm]

end Z1BoundLemmas

/-! ### Z₂ Bound Helper Lemmas

From the textbook proof (page 174):
1. Since DF(a)h = 2a⋆h, we have DF(c) - DF(ā) = 2(c-ā)⋆(·)
2. Thus ‖A(DF(c) - DF(ā))‖ ≤ 2‖A‖·‖c-ā‖ ≤ 2‖A‖·r
3. For block-diagonal A: ‖A‖ ≤ max(‖A_fin‖_{1,ν}, 1/(2|ā₀|)) by Proposition 7.3.14
4. Hence Z₂ = 2·max(‖A_fin‖_{1,ν}, 1/(2|ā₀|))
-/

section Z2BoundLemmas

/-- Subtraction distributes over leftMul: leftMul (a - b) = leftMul a - leftMul b
    Follows from leftMul_add and leftMul_smul. -/
lemma leftMul_sub {ν : PosReal} (a b : l1Weighted ν) :
    l1Weighted.leftMul (a - b) = l1Weighted.leftMul a - l1Weighted.leftMul b := by
  rw [sub_eq_add_neg, l1Weighted.leftMul_add]
  rw [← neg_one_smul ℝ b, l1Weighted.leftMul_smul]
  simp only [neg_one_smul]
  abel

/-- The difference of Fréchet derivatives equals 2·leftMul(c - ā).
    From textbook: Since DF(a)h = 2a⋆h, we have DF(c) - DF(ā) = 2(c-ā)⋆(·) -/
lemma fderiv_F_diff_eq_leftMul_diff {ν : PosReal} {N : ℕ} (lam0 : ℝ) (sol : ApproxSolution N) (c : l1Weighted ν) :
    fderiv ℝ (F lam0) c - fderiv ℝ (F lam0) sol.toL1 =
    (2 : ℝ) • l1Weighted.leftMul (c - sol.toL1) := by
  rw [fderiv_F lam0 c, fderiv_F lam0 sol.toL1]
  rw [← smul_sub, leftMul_sub]

/-- Operator norm bound on the derivative difference: ‖DF(c) - DF(ā)‖ ≤ 2·‖c - ā‖
    Uses: ‖2·leftMul(c-ā)‖ ≤ 2·‖leftMul(c-ā)‖ ≤ 2·‖c-ā‖ -/
lemma norm_fderiv_F_diff_le {ν : PosReal} {N : ℕ} (lam0 : ℝ) (sol : ApproxSolution N) (c : l1Weighted ν) :
    ‖fderiv ℝ (F lam0) c - fderiv ℝ (F lam0) sol.toL1‖ ≤ 2 * ‖c - sol.toL1‖ := by
  rw [fderiv_F_diff_eq_leftMul_diff lam0 sol c]
  calc ‖(2 : ℝ) • l1Weighted.leftMul (c - sol.toL1)‖
      = |2| * ‖l1Weighted.leftMul (c - sol.toL1)‖ := norm_smul 2 _
    _ = 2 * ‖l1Weighted.leftMul (c - sol.toL1)‖ := by norm_num
    _ ≤ 2 * ‖c - sol.toL1‖ := by
        apply mul_le_mul_of_nonneg_left (l1Weighted.norm_leftMul_le _) (by norm_num)

/-- Operator norm bound for approxInverse A: ‖A‖ ≤ max(‖A_fin‖_{1,ν}, 1/(2|ā₀|))
    This is Proposition 7.3.14 applied to the specific block-diagonal structure of A. -/
lemma approxInverse_norm_le {ν : PosReal} {N : ℕ} (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ‖(@approxInverse ν N sol A_fin).toCLM‖ ≤
    max (l1Weighted.finWeightedMatrixNorm ν A_fin) (1 / (2 * |sol.aBar_fin 0|)) := by
  have h := BlockDiag.BlockDiagOp.norm_toCLM_le (@approxInverse ν N sol A_fin)
  simp only [approxInverse] at h
  convert h using 2
  rw [abs_one_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]

/-- The Z₂ bound equals 2 times the operator norm bound for A -/
lemma Z₂_bound_eq_two_mul_max {ν : PosReal} {N : ℕ} (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    @Z₂_bound ν N sol A_fin =
    2 * max (l1Weighted.finWeightedMatrixNorm ν A_fin) (1 / (2 * |sol.aBar_fin 0|)) := rfl

end Z2BoundLemmas

/-! ## Bound Verification Lemmas (Theorem 7.7.1)

These lemmas verify that the computable bounds Y₀, Z₀, Z₁, Z₂ satisfy
the hypotheses of general_radii_polynomial_theorem.
-/

/-- Y₀ bound verification: ‖A(F(ā))‖ ≤ Y₀ -/
lemma Y₀_bound_valid (lam0 : ℝ) (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hN : 0 < N) :
    ‖(@approxInverse ν N sol A_fin).toCLM (F lam0 sol.toL1)‖ ≤ @Y₀_bound ν N lam0 sol A_fin := by
  rw [BlockDiag.norm_split (N := N)]
  simp only [Y₀_bound]
  apply add_le_add
  -- Part 1: Finite sum is exact (now definitionally equal via F_fin)
  · apply le_of_eq; congr 1; ext n
    rw [BlockDiag.BlockDiagOp.toCLM_apply]
    simp only [BlockDiag.BlockDiagOp.action, Fin.is_le, ↓reduceDIte, approxInverse]
    rfl
  -- Part 2: Use tail_tsum_eq_Icc_sum and cauchyProduct_middle_abs_bound
  · -- Convert toCLM to raw action via approxInverse_toSeq_eq_action
    simp_rw [approxInverse_toSeq_eq_action]
    -- Need to unfold F to match tail_tsum_eq_Icc_sum signature
    have h_F_eq : lpWeighted.toSeq (F (ν := ν) lam0 sol.toL1) =
        fun k => (sol.toSeq ⋆ sol.toSeq) k - paramSeq lam0 k := by
      ext k; rfl
    simp_rw [h_F_eq]
    rw [tail_tsum_eq_Icc_sum lam0 sol A_fin hN, Finset.mul_sum]
    apply Finset.sum_le_sum; intro n hn
    simp only [Finset.mem_Icc] at hn
    have hn' : N < n := Nat.lt_of_succ_le hn.1
    rw [approxInverse_action_tail sol A_fin _ n hn']
    rw [F_component_tail' lam0 _ n (by omega : 2 ≤ n)]
    simp only [one_div, abs_mul]
    have h_inv : |(2 * sol.aBar_fin 0)⁻¹| = 1 / (2 * |sol.aBar_fin 0|) := by
      rw [abs_inv, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), inv_eq_one_div]
    rw [h_inv]
    calc (1 / (2 * |sol.aBar_fin 0|)) * |(sol.toSeq ⋆ sol.toSeq) n| * (ν : ℝ) ^ n
        ≤ (1 / (2 * |sol.aBar_fin 0|)) *
            (∑ k ∈ Finset.Icc (n - N) N, |(sol.toSeq) k| * |(sol.toSeq) (n - k)|) * (ν : ℝ) ^ n := by
          gcongr
          · exact pow_nonneg (ν.coe_nonneg) n
          · exact cauchyProduct_middle_abs_bound sol n hn.1
      _ = _ := by ring

/-- Z₀ bound verification: ‖I - AA†‖ ≤ Z₀

    From the textbook proof (page 173):
    - On finite [0,N]: (I - AA†)h = (I - A_fin·DF_fin)h^(N)
    - On tail (n > N): (I - AA†)h = 0 (since tail scalars multiply to 1)

    Therefore ‖I - AA†‖ = ‖I - A_fin·DF_fin‖_{1,ν} = Z₀ -/
lemma Z₀_bound_valid (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ‖ContinuousLinearMap.id ℝ (l1Weighted ν) -
      (@approxInverse ν N sol A_fin).toCLM.comp (@approxDeriv ν N sol).toCLM‖ ≤ @Z₀_bound ν N sol A_fin := by
  have h_DF_eq := approxDeriv_finBlock_eq_DF_fin (ν := ν) sol
  simp only [Z₀_bound, ← h_DF_eq]
  -- Use operator norm definition: ‖T‖ = sup_{‖h‖≤1} ‖Th‖
  apply ContinuousLinearMap.opNorm_le_bound _ (l1Weighted.finWeightedMatrixNorm_nonneg _)
  intro h
  -- Split norm: ‖Th‖ = finite_part + tail_part
  rw [BlockDiag.norm_split (N := N)]
  -- Tail is zero
  rw [I_sub_comp_tail_tsum_zero sol A_fin h, add_zero]
  -- Finite part: convert to matrix form
  simp_rw [I_sub_comp_finite_toSeq_eq sol A_fin h]
  -- Apply weighted matrix norm bound
  let B : BlockDiag.BlockDiagOp ν N := ⟨1 - A_fin * (@approxDeriv ν N sol).finBlock, 0⟩
  calc ∑ n : Fin (N + 1), |∑ j, (1 - A_fin * (@approxDeriv ν N sol).finBlock) n j * lpWeighted.toSeq h ↑j| * ↑ν ^ ↑n
      ≤ l1Weighted.finWeightedMatrixNorm ν (1 - A_fin * (@approxDeriv ν N sol).finBlock) *
        ∑ j : Fin (N + 1), |lpWeighted.toSeq h ↑j| * ↑ν ^ ↑j := BlockDiag.finBlock_norm_bound B h
    _ ≤ l1Weighted.finWeightedMatrixNorm ν (1 - A_fin * (@approxDeriv ν N sol).finBlock) * ‖h‖ := by
        apply mul_le_mul_of_nonneg_left _ (l1Weighted.finWeightedMatrixNorm_nonneg _)
        rw [BlockDiag.norm_split (N := N)]
        exact le_add_of_nonneg_right (tsum_nonneg (fun _ => mul_nonneg (abs_nonneg _) (pow_nonneg ν.coe_nonneg _)))

/-- Z₁ bound verification: ‖A(A† - DF(ā))‖ ≤ Z₁

    From the textbook proof (page 173-174):
    - On finite [0,N]: (A† - DF(ā))h = 0 (they agree on finite block)
    - On tail (n > N): (A† - DF(ā))h = 2ā₀h_n - 2(ā⋆h)_n = -2∑_{j=1}^N h_{n-j}ā_j

    Therefore [A(A† - DF(ā))h]_n = (1/ā₀)∑_{j=1}^N h_{n-j}ā_j for n > N, and 0 for n ≤ N.

    The bound uses: ‖A(A† - DF(ā))‖ ≤ (1/|ā₀|)‖ā‖ where ā is restricted to [1,N]. -/
lemma Z₁_bound_valid (lam0 : ℝ) (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ‖(@approxInverse ν N sol A_fin).toCLM.comp
      ((@approxDeriv ν N sol).toCLM - fderiv ℝ (F lam0) sol.toL1)‖ ≤ @Z₁_bound ν N sol := by
  have hZ₁ : 0 ≤ (@Z₁_bound ν N sol) := by
    unfold Z₁_bound
    apply mul_nonneg (one_div_nonneg.mpr (abs_nonneg _))
    apply Finset.sum_nonneg; intro n _
    exact mul_nonneg (abs_nonneg _) (pow_nonneg (le_of_lt ν.property) _)
  rw [ContinuousLinearMap.opNorm_le_iff hZ₁]
  intro h
  -- Rewrite using A(A† - DF)h = -A(DF - A†)h
  have h_neg : (@approxInverse ν N sol A_fin).toCLM.comp
      ((@approxDeriv ν N sol).toCLM - fderiv ℝ (F lam0) sol.toL1) h =
      -(@approxInverse ν N sol A_fin).toCLM
        (fderiv ℝ (F lam0) sol.toL1 h - (@approxDeriv ν N sol).toCLM h) := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub, neg_sub]
  rw [h_neg, norm_neg, BlockDiag.norm_split (N := N)]
  -- Finite part is 0
  have h_fin_zero : ∑ n : Fin (N + 1), |lpWeighted.toSeq
      ((@approxInverse ν N sol A_fin).toCLM
        (fderiv ℝ (F lam0) sol.toL1 h - (@approxDeriv ν N sol).toCLM h)) n| * (ν : ℝ) ^ (n : ℕ) = 0 := by
    apply Finset.sum_eq_zero; intro n _
    rw [A_DF_sub_approxDeriv_finite_eq_zero lam0 sol A_fin h n, abs_zero, zero_mul]
  rw [h_fin_zero, zero_add]
  simp only [Z₁_bound]
  -- Tail: apply formula, factor out |1/ā₀|, then use tail_cauchy_bound
  have h_tail : ∑' n : {n : ℕ // N < n}, |lpWeighted.toSeq ((@approxInverse ν N sol A_fin).toCLM
      (fderiv ℝ (F lam0) sol.toL1 h - (@approxDeriv ν N sol).toCLM h)) n| * (ν : ℝ) ^ (n : ℕ) =
      (1 / |sol.aBar_fin 0|) * ∑' n : {n : ℕ // N < n},
        |∑ j ∈ Finset.Icc 1 N, lpWeighted.toSeq h (n - j) * sol.toSeq j| * (ν : ℝ) ^ (n : ℕ) := by
    rw [← tsum_mul_left]
    congr 1; ext ⟨n, hn⟩
    rw [A_DF_sub_approxDeriv_tail lam0 sol A_fin h n hn, abs_mul, abs_one_div]; ring
  rw [h_tail]
  calc (1 / |sol.aBar_fin 0|) * ∑' n : {n : ℕ // N < n},
        |∑ j ∈ Finset.Icc 1 N, lpWeighted.toSeq h (n - j) * sol.toSeq j| * (ν : ℝ) ^ (n : ℕ)
    ≤ (1 / |sol.aBar_fin 0|) * (‖h‖ * ∑ n ∈ Finset.Icc 1 N, |sol.toSeq n| * (ν : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left (tail_cauchy_bound sol h) (one_div_nonneg.mpr (abs_nonneg _))
    _ = 1 / |sol.aBar_fin 0| * (∑ n ∈ Finset.Icc 1 N, |sol.toSeq n| * (ν : ℝ) ^ n) * ‖h‖ := by ring

/-- Z₂ bound verification: ‖A(DF(c) - DF(ā))‖ ≤ Z₂·r for c ∈ B̄ᵣ(ā)

    From the textbook proof (page 174):
    Since DF(a)h = 2a⋆h, we have DF(c) - DF(ā) = 2(c-ā)⋆(·)
    Thus ‖A(DF(c) - DF(ā))‖ ≤ 2‖A‖·‖c-ā‖ ≤ 2‖A‖·r

    For block-diagonal A: ‖A‖ ≤ max(‖A_fin‖_{1,ν}, 1/(2|ā₀|))
    Hence Z₂ = 2·max(‖A_fin‖_{1,ν}, 1/(2|ā₀|)) -/
lemma Z₂_bound_valid (lam0 : ℝ) (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (r : ℝ) (c : l1Weighted ν) (hc : c ∈ Metric.closedBall sol.toL1 r) :
    ‖(@approxInverse ν N sol A_fin).toCLM.comp
      (fderiv ℝ (F lam0) c - fderiv ℝ (F lam0) sol.toL1)‖ ≤ @Z₂_bound ν N sol A_fin * r := by
  -- Extract ‖c - ā‖ ≤ r from the closed ball condition
  rw [Metric.mem_closedBall, dist_eq_norm] at hc
  -- Use submultiplicativity: ‖A ∘ B‖ ≤ ‖A‖ · ‖B‖
  calc ‖(@approxInverse ν N sol A_fin).toCLM.comp
        (fderiv ℝ (F lam0) c - fderiv ℝ (F lam0) sol.toL1)‖
      ≤ ‖(@approxInverse ν N sol A_fin).toCLM‖ *
        ‖fderiv ℝ (F lam0) c - fderiv ℝ (F lam0) sol.toL1‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(@approxInverse ν N sol A_fin).toCLM‖ * (2 * ‖c - sol.toL1‖) := by
          apply mul_le_mul_of_nonneg_left (norm_fderiv_F_diff_le lam0 sol c)
          exact norm_nonneg _
    _ ≤ max (l1Weighted.finWeightedMatrixNorm ν A_fin) (1 / (2 * |sol.aBar_fin 0|)) *
        (2 * ‖c - sol.toL1‖) := by
          apply mul_le_mul_of_nonneg_right (approxInverse_norm_le sol A_fin)
          apply mul_nonneg (by norm_num) (norm_nonneg _)
    _ = 2 * max (l1Weighted.finWeightedMatrixNorm ν A_fin) (1 / (2 * |sol.aBar_fin 0|)) *
        ‖c - sol.toL1‖ := by ring
    _ ≤ 2 * max (l1Weighted.finWeightedMatrixNorm ν A_fin) (1 / (2 * |sol.aBar_fin 0|)) * r := by
          apply mul_le_mul_of_nonneg_left hc
          apply mul_nonneg (by norm_num)
          exact le_max_of_le_left (l1Weighted.finWeightedMatrixNorm_nonneg _)
    _ = @Z₂_bound ν N sol A_fin * r := by rw [Z₂_bound_eq_two_mul_max]

/-- Injectivity of A follows from Proposition 7.6.5 when p(r₀) < 0

    From page 168: If p(r₀) < 0 then Z₀ + Z₁ < 1 by Corollary 7.6.3, hence ‖I - AA†‖ < 1.
    By Proposition 7.6.5, since A has block-diagonal form with injective tail (scalar 1/(2ā₀) ≠ 0),
    A is injective. -/
lemma approxInverse_injective (lam0 : ℝ) (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (r₀ : ℝ) (hr₀ : 0 < r₀)
    (h_radii : @radiiPoly_7_7 ν N lam0 sol A_fin r₀ < 0) :
    Function.Injective (@approxInverse ν N sol A_fin).toCLM := by
  sorry

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
    (lam0 : ℝ)
    (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hN : 0 < N)
    (h_radii : @radiiPoly_7_7 ν N lam0 sol A_fin r₀ < 0) :
    ∃! aTilde ∈ Metric.closedBall (sol.toL1 : l1Weighted ν) r₀,
      F lam0 aTilde = 0 := by
  exact general_radii_polynomial_theorem
    hr₀
    (@Y₀_bound_valid ν N lam0 sol A_fin hN)
    (@Z₀_bound_valid ν N sol A_fin)
    (@Z₁_bound_valid ν N lam0 sol A_fin)
    (fun c hc => by
      have := @Z₂_bound_valid ν N lam0 sol A_fin r₀ c hc
      simp only [mul_comm] at this ⊢
      exact this)
    (differentiable_F lam0)
    h_radii
    (@approxInverse_injective ν N lam0 sol A_fin r₀ hr₀ h_radii)


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

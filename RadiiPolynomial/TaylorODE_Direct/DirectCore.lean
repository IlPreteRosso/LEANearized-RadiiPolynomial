import RadiiPolynomial.TaylorODE_Direct.lpWeighted
import RadiiPolynomial.TaylorODE_Direct.FrechetCauchyProduct
import RadiiPolynomial.TaylorODE_Direct.OperatorNorm

/-!
# Direct Core Structural Lemmas (TaylorODE_Direct)

Core definitions and structural lemmas for the equation `x(λ)^2 - λ = 0`,
used by the direct LeanCert pipeline and analytic post-processing.

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

## Main Contents

- `paramSeqSpace`: The constant sequence `c = (lam0, 1, 0, 0, ...)`
- `F_eq_sq_sub`: `F(a) = a ⋆ a - c`
- `DF_eq_two_leftMul`: `DF(a)h = 2(a ⋆ h)`
- `Y₀_norm`, `Z₀_norm`, `Z₁_norm`, `Z₂_norm`: canonical norm-level quantities
- structural operator lemmas used by direct norm proofs (`I_sub_comp_*`,
  `A_DF_sub_approxDeriv_*`, `tail_cauchy_bound`, `norm_fderiv_F_diff_le`,
  `approxInverse_norm_le`, `approxInverse_tailDiag_ne_zero`)
- theorem-level wrappers for the direct pipeline
  (`approxInverse_injective_of_Z₀_lt_one`,
   `existsUnique_of_direct_bounds`,
   `existsUnique_of_direct_bounds_of_Z₀_lt_one`)

This file intentionally omits the legacy symbolic-reduction theorem assembly;
that path lives in the copied legacy file under `RadiiPolynomial/TaylorODE/`.
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

namespace DirectCore

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
  tailDiag := fun _ => 1 / (2 * sol.aBar_fin 0)
  tailBound := |1 / (2 * sol.aBar_fin 0)|
  tailBound_spec := fun _ _ => le_refl _

/-- The approximate derivative A† as a block-diagonal operator (equation 7.47).
    - Finite block: DF⁽ᴺ⁾(ā) = lower triangular with (DF)_{i,j} = 2ā_{i-j} for j ≤ i, 0 otherwise
    - Tail scalar: 2ā₀ -/
def approxDeriv {N : ℕ} (sol : ApproxSolution N) : BlockDiag.BlockDiagOp ν N where
  finBlock := Matrix.of fun i j =>
    if (j : ℕ) ≤ i then 2 * sol.aBar_fin ⟨(i : ℕ) - (j : ℕ), by omega⟩ else 0
  tailDiag := fun _ => 2 * sol.aBar_fin 0
  tailBound := |2 * sol.aBar_fin 0|
  tailBound_spec := fun _ _ => le_refl _

/-! ## Canonical Norm-Level Quantities

Exact CLM/operator norms for the four radii-polynomial hypotheses.
These are structural definitions (no symbolic-reduction formulas).
-/

/-- Canonical Y₀ quantity: `‖A·F(ā)‖`. -/
def Y₀_norm {ν : PosReal} {N : ℕ} (lam0 : ℝ) (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ℝ :=
  ‖(@approxInverse ν N sol A_fin).toCLM (F (ν := ν) lam0 sol.toL1)‖

/-- Canonical Z₀ quantity: `‖I - A·A†‖`. -/
def Z₀_norm {ν : PosReal} {N : ℕ} (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ℝ :=
  ‖ContinuousLinearMap.id ℝ (l1Weighted ν) -
    (@approxInverse ν N sol A_fin).toCLM.comp (@approxDeriv ν N sol).toCLM‖

/-- Canonical Z₁ quantity: `‖A·(A† - DF(ā))‖`. -/
def Z₁_norm {ν : PosReal} {N : ℕ} (lam0 : ℝ) (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ℝ :=
  ‖(@approxInverse ν N sol A_fin).toCLM.comp
    ((@approxDeriv ν N sol).toCLM - fderiv ℝ (F (ν := ν) lam0) sol.toL1)‖

/-- Canonical Z₂ quantity at `c`: `‖A·(DF(c) - DF(ā))‖`. -/
def Z₂_norm {ν : PosReal} {N : ℕ} (lam0 : ℝ) (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (c : l1Weighted ν) : ℝ :=
  ‖(@approxInverse ν N sol A_fin).toCLM.comp
    (fderiv ℝ (F (ν := ν) lam0) c - fderiv ℝ (F (ν := ν) lam0) sol.toL1)‖

/-! ## Support and Tail Helpers

Minimal support lemmas used by the direct CLM-bound pipeline.
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
  rw [h1, h2, sub_zero]

end Y0BoundLemmas

/-! ## Z₀ Structural Helpers

Finite/tail decomposition lemmas used to identify `I - A ∘ A†` with its
finite matrix defect in direct norm proofs.
-/

section Z0BoundLemmas

/-- approxDeriv finite block equals DF_fin -/
lemma approxDeriv_finBlock_eq_DF_fin {N : ℕ} (sol : ApproxSolution N) :
    (@approxDeriv ν N sol).finBlock = DF_fin sol := rfl

/-- Action of `(I - A A†)` on tail is zero.
    Specialization of the generic BlockDiag tail-cancellation lemma with
    `approxInverse.tailDiag * approxDeriv.tailDiag = 1`. -/
lemma I_sub_comp_action_tail_eq_zero {N : ℕ} (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (h : l1Weighted ν) (n : ℕ) (hn : N < n) :
    lpWeighted.toSeq h n -
      lpWeighted.toSeq ((@approxInverse ν N sol A_fin).toCLM
        ((@approxDeriv ν N sol).toCLM h)) n = 0 := by
  have h_tail_mul_one :
      ∀ m, N < m →
        (@approxInverse ν N sol A_fin).tailDiag m *
          (@approxDeriv ν N sol).tailDiag m = 1 := by
    intro m hm
    simp only [approxInverse, approxDeriv]
    field_simp [sol.aBar_zero_ne]
  exact BlockDiag.BlockDiagOp.I_sub_comp_action_tail_eq_zero_of_tail_mul_eq_one
    (@approxInverse ν N sol A_fin) (@approxDeriv ν N sol) h_tail_mul_one h n hn

/-- Action of `(I - A A†)` on finite equals `(I - A_fin * DF_fin) h^(N)`.
    This is a direct specialization of the generic BlockDiag finite-part lemma. -/
lemma I_sub_comp_action_finite_eq {N : ℕ} (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (h : l1Weighted ν) (n : Fin (N + 1)) :
    lpWeighted.toSeq h n -
      lpWeighted.toSeq ((@approxInverse ν N sol A_fin).toCLM
        ((@approxDeriv ν N sol).toCLM h)) n =
    ∑ j : Fin (N + 1), (1 - A_fin * (@approxDeriv ν N sol).finBlock) n j * lpWeighted.toSeq h j := by
  exact BlockDiag.BlockDiagOp.I_sub_comp_action_finite_eq
    (@approxInverse ν N sol A_fin) (@approxDeriv ν N sol) h n

/-- CLM-level finite-coordinate form of `(I - A A†)h`.
    Wrapper around the generic `BlockDiagOp.I_sub_comp_finite_toSeq_eq`. -/
lemma I_sub_comp_finite_toSeq_eq {N : ℕ} (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (h : l1Weighted ν) (n : Fin (N + 1)) :
    lpWeighted.toSeq ((ContinuousLinearMap.id ℝ (l1Weighted ν) -
      (@approxInverse ν N sol A_fin).toCLM.comp (@approxDeriv ν N sol).toCLM) h) n =
    ∑ j : Fin (N + 1), (1 - A_fin * (@approxDeriv ν N sol).finBlock) n j * lpWeighted.toSeq h j := by
  exact BlockDiag.BlockDiagOp.I_sub_comp_finite_toSeq_eq
    (@approxInverse ν N sol A_fin) (@approxDeriv ν N sol) h n

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
      ‖l1Weighted.mul h (@shiftedL1 ν N sol)‖ := by
    rw [BlockDiag.norm_split (N := N)]
    apply le_add_of_nonneg_left
    apply Finset.sum_nonneg; intro n _
    exact l1Weighted.weighted_term_nonneg _ _
  -- Apply submultiplicativity
  exact h_tail_le.trans ((l1Weighted.norm_mul_le h _).trans_eq (by rw [shiftedL1_norm]))

end Z1BoundLemmas

/-! ### Z₂ Structural Helper Lemmas

From the textbook proof (page 174):
1. Since DF(a)h = 2a⋆h, we have DF(c) - DF(ā) = 2(c-ā)⋆(·)
2. Thus ‖A(DF(c) - DF(ā))‖ ≤ 2‖A‖·‖c-ā‖ ≤ 2‖A‖·r
3. For block-diagonal A: ‖A‖ ≤ max(‖A_fin‖_{1,ν}, 1/(2|ā₀|)) by Proposition 7.3.14
4. The direct pipeline can instantiate this as a concrete numeric Z₂ bound.
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
  rw [fderiv_F_diff_eq_leftMul_diff lam0 sol c, norm_smul, Real.norm_ofNat]
  gcongr; exact l1Weighted.norm_leftMul_le _

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

end Z2BoundLemmas

/-- The tail scalar of approxInverse is nonzero -/
lemma approxInverse_tailDiag_ne_zero {ν : PosReal} {N : ℕ} (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ∀ n, N < n → (@approxInverse ν N sol A_fin).tailDiag n ≠ 0 := by
  intro n _
  simp only [approxInverse, ne_eq, one_div, inv_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero,
             sol.aBar_zero_ne, or_self, not_false_eq_true]

/-! ## Theorem-Level Direct API

Reusable wrappers that connect canonical norm-level bounds
(`Y₀_norm`, `Z₀_norm`, `Z₁_norm`, `Z₂_norm`) to
`general_radii_polynomial_theorem`.
-/

/-- Injectivity of `approxInverse.toCLM` from the structural matrix criterion
`‖I - A_fin * DF_fin(ā)‖_{1,ν} < 1` plus nonzero tail diagonal. -/
lemma approxInverse_injective_of_Z₀_lt_one {ν : PosReal} {N : ℕ}
    (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (h_Z₀_lt_one : l1Weighted.finWeightedMatrixNorm ν (1 - A_fin * DF_fin sol) < 1) :
    Function.Injective (@approxInverse ν N sol A_fin).toCLM := by
  apply BlockDiag.BlockDiagOp.injective_of_finBlock_mul_close_to_one
    (A := @approxInverse ν N sol A_fin) (B := DF_fin sol)
  · simpa [approxDeriv_finBlock_eq_DF_fin (ν := ν) sol] using h_Z₀_lt_one
  · exact approxInverse_tailDiag_ne_zero (ν := ν) sol A_fin

/-- Direct theorem API: provide the four canonical norm bounds, radii negativity,
and injectivity of the approximate inverse to conclude local existence/uniqueness. -/
theorem existsUnique_of_direct_bounds
    {ν : PosReal} {N : ℕ}
    (lam0 : ℝ)
    (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    {Y₀ Z₀ Z₁ Z₂ r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : Y₀_norm (ν := ν) lam0 sol A_fin ≤ Y₀)
    (hZ₀ : Z₀_norm (ν := ν) sol A_fin ≤ Z₀)
    (hZ₁ : Z₁_norm (ν := ν) lam0 sol A_fin ≤ Z₁)
    (hZ₂ : ∀ c ∈ Metric.closedBall sol.toL1 r₀,
      Z₂_norm (ν := ν) lam0 sol A_fin c ≤ Z₂ * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂) r₀ < 0)
    (h_inj : Function.Injective ((@approxInverse ν N sol A_fin).toCLM)) :
    ∃! aTilde ∈ Metric.closedBall (sol.toL1 : l1Weighted ν) r₀,
      F lam0 aTilde = 0 := by
  exact general_radii_polynomial_theorem
    (f := F lam0) (xBar := sol.toL1)
    (A := (@approxInverse ν N sol A_fin).toCLM)
    (A_dagger := (@approxDeriv ν N sol).toCLM)
    (Y₀ := Y₀) (Z₀ := Z₀) (Z₁ := Z₁) (Z₂ := fun _ => Z₂) (r₀ := r₀)
    hr₀ hY₀ hZ₀ hZ₁ hZ₂ (differentiable_F (ν := ν) lam0) h_radii h_inj

/-- Variant of `existsUnique_of_direct_bounds` that derives injectivity from the
structural finite-block criterion `‖I - A_fin * DF_fin(ā)‖_{1,ν} < 1`. -/
theorem existsUnique_of_direct_bounds_of_Z₀_lt_one
    {ν : PosReal} {N : ℕ}
    (lam0 : ℝ)
    (sol : ApproxSolution N)
    (A_fin : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    {Y₀ Z₀ Z₁ Z₂ r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : Y₀_norm (ν := ν) lam0 sol A_fin ≤ Y₀)
    (hZ₀ : Z₀_norm (ν := ν) sol A_fin ≤ Z₀)
    (hZ₁ : Z₁_norm (ν := ν) lam0 sol A_fin ≤ Z₁)
    (hZ₂ : ∀ c ∈ Metric.closedBall sol.toL1 r₀,
      Z₂_norm (ν := ν) lam0 sol A_fin c ≤ Z₂ * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂) r₀ < 0)
    (h_Z₀_lt_one : l1Weighted.finWeightedMatrixNorm ν (1 - A_fin * DF_fin sol) < 1) :
    ∃! aTilde ∈ Metric.closedBall (sol.toL1 : l1Weighted ν) r₀,
      F lam0 aTilde = 0 := by
  exact existsUnique_of_direct_bounds lam0 sol A_fin hr₀ hY₀ hZ₀ hZ₁ hZ₂ h_radii
    (approxInverse_injective_of_Z₀_lt_one (ν := ν) sol A_fin h_Z₀_lt_one)

end DirectCore

end

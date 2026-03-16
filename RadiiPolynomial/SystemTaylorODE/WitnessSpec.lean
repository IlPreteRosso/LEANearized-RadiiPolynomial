import RadiiPolynomial.SystemTaylorODE.BlockDiagSystem.Scalar

/-!
# WitnessSpec — General Block-Diagonal Witness Infrastructure

Equation-independent structural lemmas that reduce operator norms of
`SystemBlockDiagData` to evaluable finite sums. These bridge the gap between
the abstract CLM norms (Y₀, Z₀, ‖A‖) and the `finsum_bound` computational layer.

## Architecture

General-L lemmas first, then L=1 specializations.

## What belongs here (equation-independent)

- **Y₀**: `‖A.toCLM(v)‖` for finitely-supported `v` → finite sum per component
- **Z₀**: `finiteBlockMatrixNorm` / `finWeightedMatrixNorm` of defect → column norm sums
- **‖A‖**: `finiteBlockMatrixNorm + tailBound` → column norm sums

## What stays in example files (equation-specific)

- Z₁ structure (how A† approximates DF)
- Z₂ Lipschitz constant (depends on derivative of F)
- LeanCert evaluators (`IntervalDyadic` computations)
-/

open scoped BigOperators Topology
open SystemTaylorODE

noncomputable section

namespace SystemTaylorODE

/-! ## 1. Support Bound (General L)

When `v : XL1 ν L` has componentwise support ≤ M with M ≥ N,
`A.toCLM v` also has componentwise support ≤ M.
On tail modes (n > M ≥ N), the action is `A.tailDiag l n * v_l_n = A.tailDiag l n * 0 = 0`. -/

section GeneralL

variable {ν : PosReal} {L N : ℕ}

/-- Support bound for general L: if `v` vanishes componentwise for `n > M` and `M ≥ N`,
then `A.toCLM v` vanishes componentwise for `n > M`. -/
lemma SystemBlockDiagData.toCLM_support [NeZero L]
    (A : SystemBlockDiagData L N) (v : XL1 ν L) (M : ℕ) (hMN : N ≤ M)
    (hsupp : ∀ l, ∀ n, M < n → toCoeff (ν := ν) v l n = 0) :
    ∀ l, ∀ n, M < n → toCoeff (ν := ν) (A.toCLM (ν := ν) v) l n = 0 := by
  intro l n hn
  rw [SystemBlockDiagData.toCoeff_toCLM]
  rw [SystemBlockDiagData.action_tail _ _ _ _ (by omega : N < n)]
  rw [hsupp l n hn, mul_zero]

/-- Per-component norm of `A.toCLM v` as a finite sum when `v` has support ≤ M. -/
lemma SystemBlockDiagData.norm_toCLM_component_eq_Icc_sum [NeZero L]
    (A : SystemBlockDiagData L N) (v : XL1 ν L) (M : ℕ) (hMN : N ≤ M)
    (hsupp : ∀ l, ∀ n, M < n → toCoeff (ν := ν) v l n = 0)
    (l : Fin L) :
    ‖(A.toCLM (ν := ν) v) l‖ =
    ∑ n ∈ Finset.Icc 0 M,
      |lpWeighted.toSeq ((A.toCLM (ν := ν) v) l) n| * (ν : ℝ) ^ n :=
  l1Weighted.norm_eq_Icc_sum_of_support _ M (A.toCLM_support v M hMN hsupp l)

/-- **Y₀ pipeline (general L)**: bound `‖A.toCLM(v)‖` via per-component finite sums.

For finitely-supported `v` with support ≤ M ≥ N, the per-component norm of `A.toCLM v`
equals a finite sum of `|A.action(toCoeff v) l n| * ν^n`. The caller bounds each component
sum (typically via `finsum_bound using systemBlockDiagActionEval`).

This mirrors the operator norm definition: `‖A.toCLM v‖ = max_l ‖(A.toCLM v) l‖`,
reduced to evaluable finite sums by the block-diagonal support structure. -/
lemma SystemBlockDiagData.norm_toCLM_apply_le [NeZero L]
    (A : SystemBlockDiagData L N) (v : XL1 ν L)
    (M : ℕ) (hMN : N ≤ M)
    (hsupp : ∀ l, ∀ n, M < n → toCoeff (ν := ν) v l n = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hcomp : ∀ l : Fin L,
      ∑ n ∈ Finset.Icc 0 M,
        |A.action (toCoeff (ν := ν) v) l n| * (ν : ℝ) ^ n ≤ C) :
    ‖A.toCLM (ν := ν) v‖ ≤ C := by
  refine (pi_norm_le_iff_of_nonneg hC).mpr fun l => ?_
  rw [A.norm_toCLM_component_eq_Icc_sum v M hMN hsupp l]
  simp_rw [show ∀ n, lpWeighted.toSeq ((A.toCLM (ν := ν) v) l) n =
    A.action (toCoeff (ν := ν) v) l n from fun n =>
      A.toCoeff_toCLM (ν := ν) v l n]
  exact hcomp l

end GeneralL

/-! ## 2. Support Bound and Norm Reduction (L = 1 Specialization) -/

section ScalarSpecialization

variable {ν : PosReal} {N : ℕ}

/-- Support bound for L=1: if `v` vanishes for `n > M` and `M ≥ N`,
then `A.toScalarCLM v` vanishes for `n > M`. -/
lemma ScalarBlockDiagData.toScalarCLM_support
    (A : ScalarBlockDiagData N) (v : l1Weighted ν) (M : ℕ) (hMN : N ≤ M)
    (hsupp : ∀ n, M < n → lpWeighted.toSeq v n = 0) :
    ∀ n, M < n → lpWeighted.toSeq (A.toScalarCLM (ν := ν) v) n = 0 := by
  intro n hn
  rw [ScalarBlockDiagData.toScalarCLM_toSeq_tail A v n (by omega)]
  rw [hsupp n hn, mul_zero]

/-- Norm of `A.toScalarCLM v` as a finite sum when `v` has support ≤ M with M ≥ N. -/
lemma ScalarBlockDiagData.norm_toScalarCLM_action_eq_Icc_sum
    (A : ScalarBlockDiagData N) (v : l1Weighted ν) (M : ℕ) (hMN : N ≤ M)
    (hsupp : ∀ n, M < n → lpWeighted.toSeq v n = 0) :
    ‖A.toScalarCLM (ν := ν) v‖ =
    ∑ n ∈ Finset.Icc 0 M,
      |lpWeighted.toSeq (A.toScalarCLM (ν := ν) v) n| * (ν : ℝ) ^ n :=
  l1Weighted.norm_eq_Icc_sum_of_support _ M (A.toScalarCLM_support v M hMN hsupp)

end ScalarSpecialization

/-! ## 3. Column Norm Pipeline (documentation)

The Z₀ and ‖A‖ bounds reduce to `finWeightedMatrixNorm` (for L=1) or
`finiteBlockMatrixNorm` (for general L), computed via column norms.

Key bridge lemmas from `lpWeighted.lean` (used directly, no re-export):
- `matrixColNorm_le_of_arrayColNormIccSum`: array bounds → column norm bounds
- `finWeightedMatrixNorm_le_of_matrixColNorm_le`: column bounds → matrix norm bound

For general L, `finiteBlockMatrixNorm` = `max_l Σ_j blockEntryNorm l j` where each
`blockEntryNorm l j = finWeightedMatrixNorm ν (A.finBlock l j)`. The column norm
pipeline applies to each block entry independently. -/

end SystemTaylorODE

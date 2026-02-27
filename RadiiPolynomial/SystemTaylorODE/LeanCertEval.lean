import LeanCert
import RadiiPolynomial.SystemTaylorODE.BlockDiagSystem.Scalar

/-!
# LeanCert Evaluators for Block-Diagonal Witness Verification

Equation-independent evaluators and correctness proofs that bridge the structural
norm reductions (column norms, action norms) to `finsum_bound using`.

## Contents

1. `colNormTermEval` — per-term evaluator for column norm sums (`arrayColNormIccSum`)
2. `colNormTermEval_correct` — correctness: real term ∈ interval

## Usage Pattern

```
-- In certificate file:
unfold l1Weighted.arrayColNormIccSum
finsum_bound using (colNormTermEval col ν j) (fun k _ _ => colNormTermEval_correct col ν j k _)
```
-/

open LeanCert.Core LeanCert.Engine

namespace SystemTaylorODE

/-- Per-term evaluator for `arrayColNormIccSum`: computes `|col[k]| * ν^k / ν^j`
as a singleton `IntervalDyadic`. -/
def colNormTermEval (col : Array ℚ) (ν : ℚ) (j : Nat) (k : Nat)
    (cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat
    (IntervalRat.singleton (|col.getD k 0| * ν ^ k / ν ^ j)) cfg.precision

/-- Correctness: the real column-norm term lies in the dyadic interval. -/
theorem colNormTermEval_correct (col : Array ℚ) (ν : ℚ) (j : Nat)
    (k : Nat) (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num) :
    (|(col.getD k 0 : ℝ)| * (ν : ℝ) ^ k / (ν : ℝ) ^ j : ℝ) ∈
      colNormTermEval col ν j k cfg := by
  simp only [colNormTermEval]
  exact_mod_cast IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton _) cfg.precision hprec

/-- Helper: rational singleton interval contains its real cast. -/
lemma rat_mem_singleton (q : ℚ) (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    (q : ℝ) ∈ IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) prec :=
  IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton q) prec hprec

/-! ## I - AB defect column computation -/

/-- Build a ℚ matrix from column arrays. -/
def matOfCols {N : ℕ} (cols : Fin (N + 1) → Array ℚ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ :=
  fun i j => (cols j).getD (i : ℕ) 0

/-- Compute the defect matrix `I - A * B` in ℚ from column arrays of A and B. -/
def defectMatQ {N : ℕ} (A_cols B_cols : Fin (N + 1) → Array ℚ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ :=
  1 - matOfCols A_cols * matOfCols B_cols


/-- Bridge: if real matrix entries = ℚ cast of column array entries, then
`(I - A * B)` entries = ℚ cast of `defectMatQ` entries.

This is the **equation-independent `I - AB` lemma**. The certificate provides
`A_cols` and `B_cols`, the API computes defect entries automatically. -/
theorem defectMatQ_correct {N : ℕ}
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (A_cols B_cols : Fin (N + 1) → Array ℚ)
    (hA : ∀ j i : Fin (N + 1), A i j = ((A_cols j).getD (i : ℕ) 0 : ℝ))
    (hB : ∀ j i : Fin (N + 1), B i j = ((B_cols j).getD (i : ℕ) 0 : ℝ))
    (i j : Fin (N + 1)) :
    (1 - A * B) i j = ((defectMatQ A_cols B_cols i j : ℚ) : ℝ) := by
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
    defectMatQ, matOfCols]
  simp_rw [hA, hB]
  push_cast
  simp only [apply_ite (Rat.cast (K := ℝ)), Rat.cast_one, Rat.cast_zero]

/-! ## Core pipeline: finWeightedMatrixNorm from ℚ column arrays -/

/-- Bound `finWeightedMatrixNorm` given ℚ column arrays + per-column `arrayColNormIccSum` bounds.
Chains `matrixColNorm_le_of_arrayColNormIccSum` per column. The certificate closes
each `arrayColNormIccSum` goal via `finsum_bound using colNormTermEval`. -/
lemma l1Weighted.finWeightedMatrixNorm_le_via_cols {N : ℕ} {ν : PosReal}
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (cols : Fin (N + 1) → Array ℚ) (C : ℝ)
    (hcols : ∀ j i : Fin (N + 1), M i j = ((cols j).getD (i : ℕ) 0 : ℝ))
    (hbound : ∀ j : Fin (N + 1),
      l1Weighted.arrayColNormIccSum ν N (cols j) j ≤ C) :
    l1Weighted.finWeightedMatrixNorm ν M ≤ C :=
  l1Weighted.finWeightedMatrixNorm_le_of_matrixColNorm_le (ν := ν) (A := M) (C := C)
    (fun j => l1Weighted.matrixColNorm_le_of_arrayColNormIccSum ν N M (cols j) j C
      (hcols j) (hbound j))

/-! ## Pipeline lemmas (matrixColNorm-based)

These bypass `arrayColNormIccSum` and work directly with `matrixColNorm_eq_sum_div`,
producing `∑ i : Fin (N+1), |M i j| * ν^i / ν^j` goals that `finsum_bound` handles
natively (with the Rat.cast reifier fix). -/

/-- **Z₀ pipeline**: Given tail cancellation and per-column `matrixColNorm` bounds,
verify `‖I - A.toScalarCLM.comp B.toScalarCLM‖ ≤ C`.

Usage: certificate rewrites each column with `matrixColNorm_eq_sum_div`, substitutes
entries via `defectMatQ_correct`, then closes with `finsum_bound`. -/
lemma Z₀_le_via_colNorm {N : ℕ} {ν : PosReal}
    (A B : ScalarBlockDiagData N)
    (htail : ∀ n, N < n → A.tailDiag0 n * B.tailDiag0 n = 1)
    (C : ℝ)
    (hbound : ∀ j : Fin (N + 1),
      l1Weighted.matrixColNorm ν (1 - A.finBlock0 * B.finBlock0) j ≤ C) :
    ‖ContinuousLinearMap.id ℝ (l1Weighted ν) -
      (A.toScalarCLM (ν := ν)).comp (B.toScalarCLM (ν := ν))‖ ≤ C :=
  (ScalarBlockDiagData.Z₀_le_finWeightedMatrixNorm_of_tailCancel (ν := ν) A B htail).trans
    (l1Weighted.finWeightedMatrixNorm_le_of_matrixColNorm_le (ν := ν) _ _ hbound)

/-- **‖A‖ pipeline**: Given per-column `matrixColNorm` bounds for `A.finBlock0`,
verify `‖A.toScalarCLM‖ ≤ fin_bnd + A.tailBound`. -/
lemma norm_toScalarCLM_le_via_colNorm {N : ℕ} {ν : PosReal}
    (A : ScalarBlockDiagData N)
    (fin_bnd : ℝ)
    (hbound : ∀ j : Fin (N + 1),
      l1Weighted.matrixColNorm ν A.finBlock0 j ≤ fin_bnd) :
    ‖A.toScalarCLM (ν := ν)‖ ≤ fin_bnd + A.tailBound :=
  (ScalarBlockDiagData.norm_toScalarCLM_le (ν := ν) A).trans <| by
    gcongr
    exact l1Weighted.finWeightedMatrixNorm_le_of_matrixColNorm_le (ν := ν) _ _ hbound

/-- **‖A‖ pipeline (max)**: Given per-column `matrixColNorm` bounds and tail bound ≤ C,
verify `‖A.toScalarCLM‖ ≤ C`. Uses the tight `max` bound (Exercise 2.7.2). -/
lemma norm_toScalarCLM_le_max_via_colNorm {N : ℕ} {ν : PosReal}
    (A : ScalarBlockDiagData N)
    (C : ℝ)
    (hcol : ∀ j : Fin (N + 1),
      l1Weighted.matrixColNorm ν A.finBlock0 j ≤ C)
    (htail : A.tailBound ≤ C) :
    ‖A.toScalarCLM (ν := ν)‖ ≤ C :=
  (ScalarBlockDiagData.norm_toScalarCLM_le_max (ν := ν) A).trans <|
    max_le (l1Weighted.finWeightedMatrixNorm_le_of_matrixColNorm_le (ν := ν) _ _ hcol) htail

/-- Convert a pointwise interval bound (`∀ x ∈ Icc 0 0, e ≤ c`) to a scalar inequality.
Lets `fast_bound` close scalar inequalities directly in ℝ. -/
lemma of_point_interval {e c : ℝ}
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 0, e ≤ c) : e ≤ c :=
  h 0 ⟨le_refl _, le_refl _⟩

/-! ## Block-diagonal action bridge (ℝ-general)

Uniform formula for `toSeq(A.toScalarCLM v)[n]` combining finite and tail modes.
Certificates `simp_rw` with this + data bridges, then `finsum_bound` closes. -/

/-- Uniform per-coefficient formula for `A.toScalarCLM v` combining finite and tail modes.
For `n ≤ N`: matrix-vector product. For `n > N`: diagonal multiplication. -/
lemma ScalarBlockDiagData.toScalarCLM_toSeq_ite {N : ℕ} {ν : PosReal}
    (A : ScalarBlockDiagData N) (v : l1Weighted ν) (n : ℕ) :
    lpWeighted.toSeq (A.toScalarCLM (ν := ν) v) n =
      if hn : n ≤ N
      then ∑ j : Fin (N + 1), A.finBlock0 ⟨n, Nat.lt_succ_of_le hn⟩ j * lpWeighted.toSeq v j
      else A.tailDiag0 n * lpWeighted.toSeq v n := by
  split
  · next hn => exact A.toScalarCLM_toSeq_fin (ν := ν) v ⟨n, Nat.lt_succ_of_le hn⟩
  · next hn => exact A.toScalarCLM_toSeq_tail v n (by omega)

/-! ## Norm-to-witness bridge for block-diagonal action

Bridges `|toSeq(A.toScalarCLM v)[n]| * ν^n` to a witness evaluator.
The ℚ computation is internal to the evaluator; the certificate provides
ℚ-valued data (column arrays, vector, tail coefficient) and ℝ-to-ℚ bridges. -/

/-- Block-diagonal action in ℝ: finite modes use matrix-vector product,
tail modes use diagonal multiplication. Certificate-facing API. -/
noncomputable def scalarBlockDiagAction {N : ℕ} (matCols : Fin (N + 1) → Array ℝ)
    (vec : ℕ → ℝ) (tailCoeff : ℝ) (n : ℕ) : ℝ :=
  if n ≤ N then ∑ j : Fin (N + 1), (matCols j).getD n 0 * vec j
  else tailCoeff * vec n

/-- Bridge: `toSeq(A.toScalarCLM v)[n] = scalarBlockDiagAction ...`.
Pure ℝ signature — no ℚ types in parameters or hypotheses. -/
lemma ScalarBlockDiagData.toScalarCLM_toSeq_eq_action {N : ℕ} {ν : PosReal}
    (A : ScalarBlockDiagData N) (v : l1Weighted ν)
    (matCols : Fin (N + 1) → Array ℝ) (vec : ℕ → ℝ) (tailCoeff : ℝ)
    (hmat : ∀ j i : Fin (N + 1), A.finBlock0 i j = (matCols j).getD (i : ℕ) 0)
    (hvec : ∀ n, lpWeighted.toSeq v n = vec n)
    (htail : ∀ n, N < n → A.tailDiag0 n = tailCoeff)
    (n : ℕ) :
    lpWeighted.toSeq (A.toScalarCLM (ν := ν) v) n =
      scalarBlockDiagAction matCols vec tailCoeff n := by
  simp only [scalarBlockDiagAction]
  by_cases hn : n ≤ N
  · rw [if_pos hn, A.toScalarCLM_toSeq_fin (ν := ν) v ⟨n, Nat.lt_succ_of_le hn⟩]
    simp_rw [hmat, hvec]
  · push_neg at hn
    rw [if_neg (not_le.mpr hn), A.toScalarCLM_toSeq_tail v n hn, htail n hn, hvec]

/-- Per-term evaluator for `‖A · v‖` norm sums.
ℚ parameters for computable interval arithmetic. -/
def scalarBlockDiagActionEval {N : ℕ} (matCols : Fin (N + 1) → Array ℚ) (vec : ℕ → ℚ)
    (tailCoeff : ℚ) (ν : ℚ) (n : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  let action : ℚ :=
    if n ≤ N then ∑ j : Fin (N + 1), (matCols j).getD n 0 * vec j
    else tailCoeff * vec n
  IntervalDyadic.ofIntervalRat (IntervalRat.singleton (|action| * ν ^ n)) cfg.precision

/-- Correctness: the ℝ action-norm term lies in the evaluator's interval.
Certificate-facing: pure ℝ signature. ℚ bridge is internal. -/
theorem scalarBlockDiagActionEval_correct {N : ℕ}
    (matCols : Fin (N + 1) → Array ℝ) (vec : ℕ → ℝ) (tailCoeff : ℝ) (ν : ℝ)
    (matCols_q : Fin (N + 1) → Array ℚ) (vec_q : ℕ → ℚ) (tailCoeff_q : ℚ) (ν_q : ℚ)
    (hmat : ∀ j i : Fin (N + 1), (matCols j).getD (i : ℕ) 0 = ((matCols_q j).getD (i : ℕ) 0 : ℝ))
    (hvec : ∀ n, vec n = (vec_q n : ℝ))
    (htail : tailCoeff = (tailCoeff_q : ℝ))
    (hν : ν = (ν_q : ℝ))
    (n : Nat) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num) :
    (|scalarBlockDiagAction matCols vec tailCoeff n| * ν ^ n : ℝ) ∈
      scalarBlockDiagActionEval matCols_q vec_q tailCoeff_q ν_q n cfg := by
  simp only [scalarBlockDiagAction, scalarBlockDiagActionEval, hν]
  split
  · next hn =>
    simp_rw [show ∀ j : Fin (N + 1), (matCols j).getD n 0 =
        ((matCols_q j).getD n 0 : ℝ) from
      fun j => hmat j ⟨n, Nat.lt_succ_of_le hn⟩, hvec]
    exact_mod_cast IntervalDyadic.mem_ofIntervalRat
      (IntervalRat.mem_singleton _) cfg.precision hprec
  · rw [htail, hvec]
    exact_mod_cast IntervalDyadic.mem_ofIntervalRat
      (IntervalRat.mem_singleton _) cfg.precision hprec

end SystemTaylorODE

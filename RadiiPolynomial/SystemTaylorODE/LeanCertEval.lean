import LeanCert
import RadiiPolynomial.SystemTaylorODE.BlockDiagSystem

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

/-- Per-term evaluator for weighted l1 norm: computes `|arr[k]| * ν^k`. -/
def weightedTermEval (arr : Array ℚ) (ν : ℚ) (k : Nat)
    (cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat
    (IntervalRat.singleton (|arr.getD k 0| * ν ^ k)) cfg.precision

theorem weightedTermEval_correct (arr : Array ℚ) (ν : ℚ) (k : Nat)
    (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num)
    {f : ℕ → ℝ} (hf : f k = ((arr.getD k 0 : ℚ) : ℝ)) {ν_r : ℝ} (hν : ν_r = (ν : ℝ)) :
    (|f k| * ν_r ^ k : ℝ) ∈ weightedTermEval arr ν k cfg := by
  simp only [weightedTermEval, hf, hν]
  exact_mod_cast IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton _) cfg.precision hprec

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

/-! ## Block-level defect: δ_{l,j}·I - Σ_m A[l,m]·B[m,j] -/

/-- Block-level defect matrix `δ_{l,j}·I - Σ_m A[l,m]·B[m,j]` from per-block column arrays.
For system-level (L > 1) certificate pipelines. -/
def blockDefectMatQ {L N : ℕ}
    (A_cols B_cols : Fin L → Fin L → Fin (N + 1) → Array ℚ)
    (l j : Fin L) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ :=
  (if l = j then 1 else 0) - ∑ m, matOfCols (A_cols l m) * matOfCols (B_cols m j)

/-- Bridge: block defect entries = ℚ cast of `blockDefectMatQ` entries. -/
theorem blockDefectMatQ_correct {L N : ℕ} [DecidableEq (Fin L)]
    (A B : Fin L → Fin L → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (A_cols B_cols : Fin L → Fin L → Fin (N + 1) → Array ℚ)
    (hA : ∀ l m j i, A l m i j = ((A_cols l m j).getD (i : ℕ) 0 : ℝ))
    (hB : ∀ m j k i, B m j i k = ((B_cols m j k).getD (i : ℕ) 0 : ℝ))
    (l j : Fin L) (i k : Fin (N + 1)) :
    ((if l = j then (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) else 0) -
      ∑ m : Fin L, A l m * B m j) i k =
    ((blockDefectMatQ A_cols B_cols l j i k : ℚ) : ℝ) := by
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.mul_apply,
    blockDefectMatQ, matOfCols]
  simp_rw [hA, hB]; push_cast
  by_cases hlj : l = j <;> simp [hlj, Matrix.one_apply, apply_ite (Rat.cast (K := ℝ))]

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

/-! ## ℚ norm evaluator (single native_decide for full matrix norm)

Instead of 31 `finsum_bound` calls per block, compute the full
`finWeightedMatrixNorm` in exact ℚ arithmetic and verify `≤ C` by one `native_decide`.
-/

/-- Column norm in ℚ: `∑ i, |col(i)| * ν^i / ν^j`. -/
def colNormQ (col : Array ℚ) (ν : ℚ) (N : ℕ) (j : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc (0 : ℕ) N, |col.getD i 0| * ν ^ i / ν ^ j

/-- Matrix norm in ℚ: `max_j (colNormQ col_j ν N j)`. -/
def finWeightedMatrixNormQ (cols : Fin (N + 1) → Array ℚ) (ν : ℚ) (N : ℕ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun j => colNormQ (cols j) ν N j

/-- Bridge: if ℚ norm ≤ C (decidable), then ℝ norm ≤ C.
Single `native_decide` replaces N+1 `finsum_bound` calls. -/
lemma l1Weighted.finWeightedMatrixNorm_le_of_Q_le {N : ℕ} {ν : PosReal}
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (cols : Fin (N + 1) → Array ℚ) (ν_q : ℚ) {C : ℚ}
    (hcols : ∀ j i : Fin (N + 1), M i j = ((cols j).getD (i : ℕ) 0 : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (hle : finWeightedMatrixNormQ cols ν_q N ≤ C) :
    l1Weighted.finWeightedMatrixNorm ν M ≤ (C : ℝ) := by
  -- Step 1: each matrixColNorm = (colNormQ : ℝ) via column bridge + cast
  have hcol : ∀ j : Fin (N + 1), l1Weighted.matrixColNorm ν M j =
      ((colNormQ (cols j) ν_q N j : ℚ) : ℝ) := by
    intro j
    rw [l1Weighted.matrixColNorm_eq_arrayColNormIccSum ν N M (cols j) j (hcols j)]
    simp only [l1Weighted.arrayColNormIccSum, colNormQ, hν]
    push_cast; rfl
  -- Step 2: finWeightedMatrixNorm = sup' of (colNormQ : ℝ) ≤ (sup' of colNormQ : ℝ) ≤ (C : ℝ)
  show Finset.sup' _ _ (fun j => l1Weighted.matrixColNorm ν M j) ≤ _
  simp_rw [hcol]
  have : Finset.sup' Finset.univ Finset.univ_nonempty
      (fun j => (colNormQ (cols j) ν_q N j : ℝ)) ≤
      ((Finset.sup' Finset.univ Finset.univ_nonempty
        (fun j => colNormQ (cols j) ν_q N j) : ℚ) : ℝ) := by
    apply Finset.sup'_le _ _ (fun j _ => ?_)
    exact_mod_cast Finset.le_sup' (fun j => colNormQ (cols j) ν_q N j) (Finset.mem_univ j)
  exact this.trans (by exact_mod_cast hle)

/-! ## Block matrix norm in ℚ (single native_decide for L×L block operator) -/

/-- Block matrix norm in ℚ: max_l (∑_j finWeightedMatrixNormQ(block_lj)). -/
def finiteBlockMatrixNormQ (L N : ℕ) [NeZero L]
    (blockCols : Fin L → Fin L → Fin (N + 1) → Array ℚ) (ν : ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun l =>
    ∑ j : Fin L, finWeightedMatrixNormQ (blockCols l j) ν N

/-- Per-block Z₂ evaluator: only sums active block norms.
For Z₂ bounds where only some components of D²φ are nonzero. -/
def Z₂_blockNormQ (L N : ℕ) [NeZero L]
    (blockCols : Fin L → Fin L → Fin (N + 1) → Array ℚ) (ν tailBound : ℚ)
    (active : Finset (Fin L)) : ℚ :=
  2 * ν * Finset.sup' Finset.univ Finset.univ_nonempty fun l =>
    (∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν N) +
    if l ∈ active then tailBound else 0

/-- Z₂ per-component bridge: if `Z₂_blockNormQ ≤ C`, then for each `l`,
`2ν * (∑_{j∈active} blockEntryNorm(l,j) + δ(l∈active)*tailBound) ≤ (C : ℝ)`. -/
lemma Z₂_blockNorm_component_le {L N : ℕ} [NeZero L] {ν : PosReal}
    (A : SystemBlockDiagData L N)
    (blockCols : Fin L → Fin L → Fin (N + 1) → Array ℚ) (ν_q tailBound_q : ℚ)
    (active : Finset (Fin L)) {C : ℚ}
    (hcols : ∀ l j : Fin L, ∀ k i : Fin (N + 1),
      A.finBlock l j i k = ((blockCols l j k).getD (i : ℕ) 0 : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (htail : A.tailBound = (tailBound_q : ℝ))
    (hle : Z₂_blockNormQ L N blockCols ν_q tailBound_q active ≤ C) (l : Fin L) :
    2 * (ν : ℝ) * ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
      if l ∈ active then A.tailBound else 0) ≤ (C : ℝ) := by
  -- Per-block entry norm ≤ ℚ norm
  have hentry : ∀ j : Fin L,
      blockEntryNorm ν A.finBlock l j ≤
        ((finWeightedMatrixNormQ (blockCols l j) ν_q N : ℚ) : ℝ) :=
    fun j => l1Weighted.finWeightedMatrixNorm_le_of_Q_le
      (A.finBlock l j) (blockCols l j) ν_q (hcols l j) hν (le_refl _)
  -- Suffices to show ≤ Z₂_blockNormQ (then use hle)
  suffices h : 2 * (ν : ℝ) * ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
      if l ∈ active then A.tailBound else 0) ≤
      ((Z₂_blockNormQ L N blockCols ν_q tailBound_q active : ℚ) : ℝ) from
    h.trans (by exact_mod_cast hle)
  -- Unfold Z₂_blockNormQ and push casts
  show 2 * (ν : ℝ) * ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
      if l ∈ active then A.tailBound else 0) ≤
      ↑(2 * ν_q * Finset.sup' Finset.univ Finset.univ_nonempty fun l =>
        (∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0)
  -- Row bound: ∑ blockEntryNorm + δ*tailBound ≤ ℚ counterpart
  have hrow : (∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
      (if l ∈ active then A.tailBound else (0 : ℝ)) ≤
      ((((∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0 : ℚ) : ℝ)) := by
    push_cast
    exact add_le_add
      (Finset.sum_le_sum fun j _ => hentry j)
      (by split <;> simp [htail])
  -- 2ν * row ≤ 2ν * sup'
  have hν_nn : (0 : ℝ) ≤ 2 * (ν : ℝ) := mul_nonneg (by norm_num) ν.coe_nonneg
  calc 2 * (ν : ℝ) * _ ≤ 2 * (ν : ℝ) * ↑((∑ j ∈ active,
        finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0) :=
      mul_le_mul_of_nonneg_left hrow hν_nn
    _ ≤ 2 * (ν : ℝ) * ↑(Finset.sup' Finset.univ Finset.univ_nonempty fun l =>
        (∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0) := by
      apply mul_le_mul_of_nonneg_left _ hν_nn
      have := Finset.le_sup' (f := fun l =>
        (∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0) (Finset.mem_univ l)
      exact_mod_cast this
    _ = ↑(2 * ν_q * Finset.sup' Finset.univ Finset.univ_nonempty fun l =>
        (∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0) := by
      rw [hν]; push_cast; ring

/-- Generalized Z₂ block norm evaluator with variable factor `C_q` (replaces hardcoded `2`). -/
def Z₂_blockNormQ_gen (L N : ℕ) [NeZero L]
    (blockCols : Fin L → Fin L → Fin (N + 1) → Array ℚ) (ν tailBound C_q : ℚ)
    (active : Finset (Fin L)) : ℚ :=
  C_q * ν * Finset.sup' Finset.univ Finset.univ_nonempty fun l =>
    (∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν N) +
    if l ∈ active then tailBound else 0

/-- Generalized Z₂ per-component bridge with variable factor.
If `Z₂_blockNormQ_gen ... C_q ≤ bound`, then `C*ν*(∑ blockNorm + tail_if) ≤ bound` for each `l`. -/
lemma Z₂_blockNorm_component_le_gen {L N : ℕ} [NeZero L] {ν : PosReal}
    (A : SystemBlockDiagData L N)
    (blockCols : Fin L → Fin L → Fin (N + 1) → Array ℚ) (ν_q tailBound_q C_q : ℚ)
    (active : Finset (Fin L)) {bound : ℚ}
    (hcols : ∀ l j : Fin L, ∀ k i : Fin (N + 1),
      A.finBlock l j i k = ((blockCols l j k).getD (i : ℕ) 0 : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (htail : A.tailBound = (tailBound_q : ℝ))
    (hC_nn : 0 ≤ C_q)
    (hle : Z₂_blockNormQ_gen L N blockCols ν_q tailBound_q C_q active ≤ bound)
    (l : Fin L) :
    (C_q : ℝ) * (ν : ℝ) * ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
      if l ∈ active then A.tailBound else 0) ≤ (bound : ℝ) := by
  have hentry : ∀ j : Fin L,
      blockEntryNorm ν A.finBlock l j ≤
        ((finWeightedMatrixNormQ (blockCols l j) ν_q N : ℚ) : ℝ) :=
    fun j => l1Weighted.finWeightedMatrixNorm_le_of_Q_le
      (A.finBlock l j) (blockCols l j) ν_q (hcols l j) hν (le_refl _)
  suffices h : (C_q : ℝ) * (ν : ℝ) * ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
      if l ∈ active then A.tailBound else 0) ≤
      ((Z₂_blockNormQ_gen L N blockCols ν_q tailBound_q C_q active : ℚ) : ℝ) from
    h.trans (by exact_mod_cast hle)
  show (C_q : ℝ) * (ν : ℝ) * ((∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
      if l ∈ active then A.tailBound else 0) ≤
      ↑(C_q * ν_q * Finset.sup' Finset.univ Finset.univ_nonempty fun l =>
        (∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0)
  have hrow : (∑ j ∈ active, blockEntryNorm ν A.finBlock l j) +
      (if l ∈ active then A.tailBound else (0 : ℝ)) ≤
      ((((∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0 : ℚ) : ℝ)) := by
    push_cast
    exact add_le_add
      (Finset.sum_le_sum fun j _ => hentry j)
      (by split <;> simp [htail])
  have hCν_nn : (0 : ℝ) ≤ (C_q : ℝ) * (ν : ℝ) :=
    mul_nonneg (by exact_mod_cast hC_nn) ν.coe_nonneg
  calc (C_q : ℝ) * (ν : ℝ) * _ ≤ (C_q : ℝ) * (ν : ℝ) * ↑((∑ j ∈ active,
        finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0) :=
      mul_le_mul_of_nonneg_left hrow hCν_nn
    _ ≤ (C_q : ℝ) * (ν : ℝ) * ↑(Finset.sup' Finset.univ Finset.univ_nonempty fun l =>
        (∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0) := by
      apply mul_le_mul_of_nonneg_left _ hCν_nn
      have := Finset.le_sup' (f := fun l =>
        (∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0) (Finset.mem_univ l)
      exact_mod_cast this
    _ = ↑(C_q * ν_q * Finset.sup' Finset.univ Finset.univ_nonempty fun l =>
        (∑ j ∈ active, finWeightedMatrixNormQ (blockCols l j) ν_q N) +
        if l ∈ active then tailBound_q else 0) := by
      rw [hν]; push_cast; ring

/-- Bridge: if ℚ block norm ≤ C, then ℝ block norm ≤ C.
Single `native_decide` replaces L×L `finWeightedMatrixNorm_le_of_Q_le` calls. -/
lemma finiteBlockMatrixNorm_le_of_Q_le {L N : ℕ} [NeZero L] {ν : PosReal}
    (A : FiniteBlockMatrix L N)
    (blockCols : Fin L → Fin L → Fin (N + 1) → Array ℚ) (ν_q : ℚ) {C : ℚ}
    (hcols : ∀ l j : Fin L, ∀ k i : Fin (N + 1),
      A l j i k = ((blockCols l j k).getD (i : ℕ) 0 : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (hle : finiteBlockMatrixNormQ L N blockCols ν_q ≤ C) :
    finiteBlockMatrixNorm ν A ≤ (C : ℝ) := by
  -- Per-block: reuse scalar bridge with C = finWeightedMatrixNormQ
  have hentry : ∀ l j : Fin L,
      blockEntryNorm ν A l j ≤
        ((finWeightedMatrixNormQ (blockCols l j) ν_q N : ℚ) : ℝ) :=
    fun l j => l1Weighted.finWeightedMatrixNorm_le_of_Q_le
      (A l j) (blockCols l j) ν_q (hcols l j) hν (le_refl _)
  -- Aggregate: sup'_l (∑_j blockEntryNorm) ≤ (C : ℝ)
  unfold finiteBlockMatrixNorm blockRowNorm
  apply Finset.sup'_le _ _ (fun l _ => ?_)
  calc ∑ j, blockEntryNorm ν A l j
      ≤ ∑ j, ((finWeightedMatrixNormQ (blockCols l j) ν_q N : ℚ) : ℝ) :=
        Finset.sum_le_sum (fun j _ => hentry l j)
    _ = ((∑ j, finWeightedMatrixNormQ (blockCols l j) ν_q N : ℚ) : ℝ) := by
        push_cast; rfl
    _ ≤ ((Finset.sup' Finset.univ Finset.univ_nonempty
          (fun l => ∑ j, finWeightedMatrixNormQ (blockCols l j) ν_q N) : ℚ) : ℝ) := by
        exact_mod_cast Finset.le_sup'
          (fun l => ∑ j, finWeightedMatrixNormQ (blockCols l j) ν_q N) (Finset.mem_univ l)
    _ ≤ (C : ℝ) := by exact_mod_cast hle

/-- Combined CLM norm bound from ℚ block columns + ℚ tail bound.
`‖A.toCLM‖ ≤ finiteBlockMatrixNormQ + tailBound_q ≤ C` — no intermediate named constants. -/
lemma norm_toCLM_le_of_Q {L N : ℕ} [NeZero L] {ν : PosReal}
    (A : SystemBlockDiagData L N)
    (blockCols : Fin L → Fin L → Fin (N + 1) → Array ℚ) (ν_q tailBound_q : ℚ) {C : ℚ}
    (hcols : ∀ l j : Fin L, ∀ k i : Fin (N + 1),
      A.finBlock l j i k = ((blockCols l j k).getD (i : ℕ) 0 : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (htail : A.tailBound = (tailBound_q : ℝ))
    (hle : finiteBlockMatrixNormQ L N blockCols ν_q + tailBound_q ≤ C) :
    ‖A.toCLM (ν := ν)‖ ≤ (C : ℝ) :=
  (A.norm_toCLM_le (ν := ν)).trans <|
    (add_le_add
      (finiteBlockMatrixNorm_le_of_Q_le A.finBlock blockCols ν_q hcols hν (le_refl _))
      (le_of_eq htail)).trans (by exact_mod_cast hle)

/-! ## Pi-vector norm in ℚ (for Y₀-type bounds)

Bounds `‖x‖` for `x : XL1 ν L` (finitely-supported Pi-vector) via ℚ arrays + `native_decide`. -/

/-- Per-component weighted ℓ¹ norm in ℚ: `Σ_{n=0}^S |v[n]| * ν^n`. -/
def vecComponentNormQ (v : Array ℚ) (ν : ℚ) (S : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 0 S, |v.getD n 0| * ν ^ n

/-- Pi-vector norm in ℚ: `max_l vecComponentNormQ(vec l)`. -/
def vecNormQ (L S : ℕ) [NeZero L] (vec : Fin L → Array ℚ) (ν : ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun l => vecComponentNormQ (vec l) ν S

/-- Bridge: if each component of `x : XL1 ν L` has finite support and matches ℚ arrays,
then `‖x‖ ≤ (C : ℝ)`. Single `native_decide` via `finmatrix_bound`. -/
lemma pi_norm_le_of_vecNormQ {L : ℕ} [NeZero L] {ν : PosReal} (S : ℕ)
    (x : Fin L → l1Weighted ν)
    (vec : Fin L → Array ℚ) (ν_q : ℚ) {C : ℚ}
    (hsupport : ∀ l, ∀ n, S < n → l1Weighted.toSeq (x l) n = 0)
    (hbridge : ∀ l, ∀ n, l1Weighted.toSeq (x l) n = ((vec l).getD n 0 : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (hle : vecNormQ L S vec ν_q ≤ C) :
    ‖x‖ ≤ (C : ℝ) := by
  have hνq : (0 : ℚ) ≤ ν_q := by exact_mod_cast (hν ▸ le_of_lt ν.2 : (0 : ℝ) ≤ (ν_q : ℝ))
  have hC : (0 : ℝ) ≤ (C : ℝ) := by
    have := Finset.sum_nonneg (s := Finset.Icc 0 S) (f := fun n =>
      |((vec (0 : Fin L)).getD n 0 : ℚ)| * ν_q ^ n)
      (fun n _ => mul_nonneg (abs_nonneg _) (pow_nonneg hνq _))
    exact_mod_cast le_trans (le_trans this
      (Finset.le_sup'_of_le (fun l => vecComponentNormQ (vec l) ν_q S)
        (Finset.mem_univ (0 : Fin L)) le_rfl)) hle
  refine (pi_norm_le_iff_of_nonneg hC).mpr fun l => ?_
  rw [l1Weighted.norm_eq_Icc_sum_of_support (x l) S (hsupport l)]
  simp_rw [hbridge l, hν]
  have hsum : ∑ n ∈ Finset.Icc 0 S, |((vec l).getD n 0 : ℝ)| * (ν_q : ℝ) ^ n =
      ((vecComponentNormQ (vec l) ν_q S : ℚ) : ℝ) := by
    simp only [vecComponentNormQ]; push_cast; rfl
  rw [hsum]
  exact_mod_cast (Finset.le_sup'
    (fun l => vecComponentNormQ (vec l) ν_q S) (Finset.mem_univ l)).trans hle

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

/-- Strict variant of `of_point_interval` for `fast_bound` on `< 0` goals. -/
lemma of_point_interval_lt {e c : ℝ}
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 0, e < c) : e < c :=
  h 0 ⟨le_refl _, le_refl _⟩

/-- Wrap `e ≤ c` as a singleton sum for `finsum_bound`. -/
lemma of_singleton_sum {e c : ℝ}
    (h : ∑ _k ∈ Finset.Icc (0:ℕ) 0, e ≤ c) : e ≤ c := by simpa using h

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

/-! ## System-level action evaluator (general L, for Y₀-type bounds)

Generalizes `scalarBlockDiagActionEval` from L=1 to arbitrary L.
Computes `|Σ_j Σ_k A[l,j][n,k] * c[j,k]| * ν^n` for n ≤ N,
and `|tailCoeff * c[l,n]| * ν^n` for n > N. -/

/-- Per-term evaluator for system block-diagonal action norm: `|action_l_n| * ν^n`.
Generalizes `scalarBlockDiagActionEval` to L > 1. -/
def systemBlockDiagActionEval {L N : ℕ}
    (matCols : Fin L → Fin L → Fin (N + 1) → Array ℚ)
    (vec : Fin L → ℕ → ℚ) (tailCoeff : Fin L → ℕ → ℚ)
    (ν : ℚ) (l : Fin L) (n : ℕ) (cfg : DyadicConfig) : IntervalDyadic :=
  let action : ℚ :=
    if n ≤ N then
      ∑ j : Fin L, ∑ k : Fin (N + 1), (matCols l j k).getD n 0 * vec j k
    else tailCoeff l n * vec l n
  IntervalDyadic.ofIntervalRat (IntervalRat.singleton (|action| * ν ^ n)) cfg.precision

/-- Correctness: the ℝ system action term lies in the evaluator's interval. -/
theorem systemBlockDiagActionEval_correct {L N : ℕ}
    (A : SystemBlockDiagData L N)
    (c : SystemCoeff L) (c_q : Fin L → ℕ → ℚ)
    (matCols_q : Fin L → Fin L → Fin (N + 1) → Array ℚ)
    (tailCoeff_q : Fin L → ℕ → ℚ) (ν_q : ℚ) {ν : PosReal}
    (hmat : ∀ l j : Fin L, ∀ k i : Fin (N + 1),
      A.finBlock l j i k = ((matCols_q l j k).getD (i : ℕ) 0 : ℝ))
    (hvec : ∀ l n, c l n = (c_q l n : ℝ))
    (htail : ∀ l n, N < n → A.tailDiag l n = (tailCoeff_q l n : ℝ))
    (hν : (ν : ℝ) = (ν_q : ℝ))
    (l : Fin L) (n : ℕ) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num) :
    (|A.action c l n| * (ν : ℝ) ^ n : ℝ) ∈
      systemBlockDiagActionEval matCols_q c_q tailCoeff_q ν_q l n cfg := by
  simp only [systemBlockDiagActionEval, hν]
  by_cases hn : n ≤ N
  · -- Finite block
    rw [if_pos hn]
    have : A.action c l n =
        ∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k * c j k :=
      A.action_finite c l n hn
    rw [this]
    simp_rw [hmat, hvec]
    exact_mod_cast IntervalDyadic.mem_ofIntervalRat
      (IntervalRat.mem_singleton _) cfg.precision hprec
  · -- Tail
    push_neg at hn
    rw [if_neg (not_le.mpr hn)]
    rw [A.action_tail c l n hn, htail l n hn, hvec]
    exact_mod_cast IntervalDyadic.mem_ofIntervalRat
      (IntervalRat.mem_singleton _) cfg.precision hprec

/-! ## System-level Z₀ pipeline (general L)

Generalizes `Z₀_le_via_colNorm` from L=1 to arbitrary L.
Chains: `Z₀_le_of_tailCancel` → `finiteBlockMatrixNorm` → per-block column norms. -/

/-- **System Z₀ pipeline**: Given tail cancellation and per-row defect norm bounds,
verify `‖I - A.toCLM ∘ B.toCLM‖ ≤ C`.

Chains: `Z₀_le_of_tailCancel` → `finiteBlockMatrixNorm_le_of_blockRowNorm_le`.
The certificate provides per-row bounds via `finWeightedMatrixNorm_le_via_cols` + `colNormTermEval`. -/
lemma Z₀_le_via_block_colNorm {L N : ℕ} [NeZero L] {ν : PosReal}
    (A B : SystemBlockDiagData L N)
    (htail : ∀ l, ∀ n, N < n → A.tailDiag l n * B.tailDiag l n = 1)
    (C : ℝ)
    (hrow : ∀ l : Fin L,
      blockRowNorm ν (A.defectOfTailCancel B htail).finBlock l ≤ C) :
    Z₀_norm (A.toCLM (ν := ν)) (B.toCLM (ν := ν)) ≤ C :=
  (SystemBlockDiagData.Z₀_le_of_tailCancel (ν := ν) A B htail).trans
    (finiteBlockMatrixNorm_le_of_blockRowNorm_le _ C hrow)

/-- **System ‖A‖ pipeline**: Given per-row block norm bounds and tail bound,
verify `‖A.toCLM‖ ≤ fin_bnd + tail_bnd`.

Chains: `norm_toCLM_le` → `finiteBlockMatrixNorm_le_of_blockRowNorm_le`. -/
lemma norm_toCLM_le_via_block_colNorm {L N : ℕ} [NeZero L] {ν : PosReal}
    (A : SystemBlockDiagData L N)
    (fin_bnd tail_bnd : ℝ)
    (hrow : ∀ l : Fin L, blockRowNorm ν A.finBlock l ≤ fin_bnd)
    (htail : A.tailBound ≤ tail_bnd) :
    ‖A.toCLM (ν := ν)‖ ≤ fin_bnd + tail_bnd :=
  (A.norm_toCLM_le (ν := ν)).trans
    (add_le_add (finiteBlockMatrixNorm_le_of_blockRowNorm_le _ _ hrow) htail)

/-! ## System-level block-diagonal action (general L)

Per-component action formula for `SystemBlockDiagData L N` operating on `XL1 ν L`.
Generalizes `scalarBlockDiagAction` from L=1 to arbitrary L. For component `l`,
the action sums over all L blocks in the finite part. -/

/-- Per-component block-diagonal action in ℝ.
For `n ≤ N`: sums over all L blocks' matrix-vector products.
For `n > N`: diagonal multiplication on component `l` only. -/
noncomputable def systemComponentAction {L N : ℕ}
    (matCols : Fin L → Fin (N + 1) → Array ℝ)
    (vecs : Fin L → ℕ → ℝ) (tailCoeff : ℝ)
    (l : Fin L) (n : ℕ) : ℝ :=
  if n ≤ N then
    ∑ j : Fin L, ∑ k : Fin (N + 1), (matCols j k).getD n 0 * vecs j k
  else tailCoeff * vecs l n

/-- Bridge: `toCoeff(A.toCLM v)(l)(n) = systemComponentAction ...`.
The finite action sums over all L blocks, the tail action uses the per-component diagonal.
Pure ℝ signature — no ℚ in parameters. -/
lemma SystemBlockDiagData.toCoeff_toCLM_eq_componentAction
    {L N : ℕ} [NeZero L] {ν : PosReal}
    (A : SystemBlockDiagData L N) (v : XL1 ν L)
    (matCols : Fin L → Fin (N + 1) → Array ℝ)
    (vecs : Fin L → ℕ → ℝ) (tailCoeff : ℝ)
    (l : Fin L)
    (hmat : ∀ j (k : Fin (N + 1)) (i : Fin (N + 1)),
      A.finBlock l j i k = (matCols j k).getD (i : ℕ) 0)
    (hvec : ∀ j n, lpWeighted.toSeq (v j) n = vecs j n)
    (htail : ∀ n, N < n → A.tailDiag l n = tailCoeff)
    (n : ℕ) :
    toCoeff (ν := ν) (A.applyX (ν := ν) v) l n =
      systemComponentAction matCols vecs tailCoeff l n := by
  simp only [systemComponentAction]
  rw [show toCoeff (ν := ν) (A.applyX (ν := ν) v) l n =
    A.action (toCoeff (ν := ν) v) l n from
    congr_fun (congr_fun (toCoeff_applyX A v) l) n]
  simp only [SystemBlockDiagData.action, SystemBlockDiagData.actionFinite,
    SystemBlockDiagData.actionTail]
  simp only [toCoeff] at *
  by_cases hn : n ≤ N
  · simp only [hn, dite_true, ite_true, add_zero]
    congr 1
    ext j
    congr 1
    ext k
    rw [hmat, hvec]
  · push_neg at hn
    simp only [show ¬(n ≤ N) from not_le.mpr hn, dite_false, ite_false, zero_add,
      htail n hn, hvec]

/-- Per-term evaluator for system-level `‖A · v‖` norm sums (component `l`).
ℚ parameters for computable interval arithmetic via `native_decide`. -/
def systemComponentActionEval {L N : ℕ}
    (matCols : Fin L → Fin (N + 1) → Array ℚ)
    (vecs : Fin L → ℕ → ℚ) (tailCoeff : ℚ) (ν : ℚ)
    (l : Fin L) (n : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  let action : ℚ :=
    if n ≤ N then
      ∑ j : Fin L, ∑ k : Fin (N + 1), (matCols j k).getD n 0 * vecs j k
    else tailCoeff * vecs l n
  IntervalDyadic.ofIntervalRat (IntervalRat.singleton (|action| * ν ^ n)) cfg.precision

/-- Correctness: the ℝ action-norm term lies in the evaluator's interval.
Certificate-facing: pure ℝ signature. ℚ bridge is internal. -/
theorem systemComponentActionEval_correct {L N : ℕ}
    (matCols : Fin L → Fin (N + 1) → Array ℝ)
    (vecs : Fin L → ℕ → ℝ) (tailCoeff : ℝ) (ν : ℝ)
    (matCols_q : Fin L → Fin (N + 1) → Array ℚ)
    (vecs_q : Fin L → ℕ → ℚ) (tailCoeff_q : ℚ) (ν_q : ℚ)
    (hmat : ∀ j (k : Fin (N + 1)),
      ∀ i : Fin (N + 1), (matCols j k).getD (i : ℕ) 0 =
        ((matCols_q j k).getD (i : ℕ) 0 : ℝ))
    (hvec : ∀ j n, vecs j n = (vecs_q j n : ℝ))
    (htail : tailCoeff = (tailCoeff_q : ℝ))
    (hν : ν = (ν_q : ℝ))
    (l : Fin L) (n : Nat) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num) :
    (|systemComponentAction matCols vecs tailCoeff l n| * ν ^ n : ℝ) ∈
      systemComponentActionEval matCols_q vecs_q tailCoeff_q ν_q l n cfg := by
  simp only [systemComponentAction, systemComponentActionEval, hν]
  split
  · next hn =>
    simp_rw [show ∀ j : Fin L, ∀ k : Fin (N + 1),
        (matCols j k).getD n 0 = ((matCols_q j k).getD n 0 : ℝ) from
      fun j k => hmat j k ⟨n, Nat.lt_succ_of_le hn⟩, hvec]
    exact_mod_cast IntervalDyadic.mem_ofIntervalRat
      (IntervalRat.mem_singleton _) cfg.precision hprec
  · rw [htail, hvec]
    exact_mod_cast IntervalDyadic.mem_ofIntervalRat
      (IntervalRat.mem_singleton _) cfg.precision hprec

end SystemTaylorODE

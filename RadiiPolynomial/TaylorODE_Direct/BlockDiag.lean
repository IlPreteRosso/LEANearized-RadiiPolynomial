import RadiiPolynomial.TaylorODE_Direct.lpWeighted
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Block-Diagonal Operators on Weighted Sequence Spaces

This file defines block-diagonal operators on ℓ¹_ν that act as a finite matrix
on coordinates 0..N and as a diagonal operator on the tail N+1, N+2, ...

## Main Definitions

- `BlockDiagOp`: Structure with `finBlock` (matrix) and `tailDiag` (ℕ → ℝ diagonal)
- `BlockDiagOp.action`: The action on sequences
- `BlockDiagOp.toCLM`: As a continuous linear map on ℓ¹_ν (requires bounded tail)

## Main Results

- `action_finite`, `action_tail`, `action_fin`: Simp lemmas for the action
- `toCLM_apply`: CLM action equals BlockDiagOp action
- `clm_eq_of_finite_tail`: identify a CLM from finite/tail action formulas
- `norm_toCLM_le`: ‖A‖ ≤ max(‖finBlock‖_{1,ν}, C) where C bounds |tailDiag|
- `norm_toCLM_le_finBlock_of_tailBound_zero`: tail-zero specialization for direct bounds
- `injective_of_parts`: Injectivity from invertible finBlock + nonzero tailDiag
- `norm_split`: Splitting ℓ¹ norm into finite + tail parts

## ℚ Bridge

- `blockDiagAction_q`: Computable ℚ action mirroring `BlockDiagOp.action`
- `action_eq_rat_cast`: Generic bridge `A.action v n = ↑(blockDiagAction_q ... n)`
  given per-entry ℚ hypotheses for the matrix, vector, and tail diagonal
- `toCLM_action_eq_rat_cast`: CLM-level corollary

The bridge pattern: unfold action → by_cases fin/tail → rewrite entries to ℚ casts
→ push_cast; ring. Callers supply three problem-specific facts (hmat, hvec, htail).

## Design Note

The tail is `tailDiag : ℕ → ℝ`, a mode-dependent diagonal.
- Example 7.7 (algebraic): constant tail `fun _ => 1/(2ā₀)`
- Section 8.1 (scalar IVP): mode-dependent `fun n => 1/n`
- Section 8.2 (systems): same `ℕ → ℝ` tail, L independent copies on `(ℓ¹_ν)^L`
-/

open scoped BigOperators Topology NNReal ENNReal Matrix
open Metric Set Filter ContinuousLinearMap

noncomputable section

variable {ν : PosReal}

namespace BlockDiag

variable {N : ℕ}

/-- A block-diagonal operator on ℓ¹_ν.

    The operator acts as:
    - A finite matrix `finBlock` on coordinates 0, 1, ..., N
    - A mode-dependent diagonal `tailDiag n` on coordinates N+1, N+2, ...

    For Chapter 7.7: `tailDiag = fun _ => 1/(2ā₀)` (constant).
    For Chapter 8.1 IVPs: `tailDiag = fun n => 1/n` (mode-dependent). -/
structure BlockDiagOp (ν : PosReal) (N : ℕ) where
  /-- The (N+1)×(N+1) matrix acting on the finite part -/
  finBlock : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  /-- The diagonal entry at mode n for the tail (n > N) -/
  tailDiag : ℕ → ℝ
  /-- A uniform bound on |tailDiag n| for n > N (needed for continuity) -/
  tailBound : ℝ
  /-- The bound holds for all tail indices -/
  tailBound_spec : ∀ n, N < n → |tailDiag n| ≤ tailBound

/-- The action of a block-diagonal operator on a sequence.

    (A·a)ₙ = (finBlock · a_{[0,N]})ₙ  for n ≤ N
    (A·a)ₙ = tailDiag(n) · aₙ         for n > N -/
def BlockDiagOp.action {ν : PosReal} {N : ℕ} (A : BlockDiagOp ν N) (a : ℕ → ℝ) : ℕ → ℝ := fun n =>
  if h : n ≤ N then
    ∑ j : Fin (N + 1), A.finBlock ⟨n, Nat.lt_succ_of_le h⟩ j * a j
  else
    A.tailDiag n * a n

@[simp]
lemma BlockDiagOp.action_finite {ν : PosReal} {N : ℕ} (A : BlockDiagOp ν N)
    (a : ℕ → ℝ) (n : ℕ) (hn : n ≤ N) :
    A.action a n = ∑ j : Fin (N + 1), A.finBlock ⟨n, Nat.lt_succ_of_le hn⟩ j * a j := by
  simp only [action, hn, ↓reduceDIte]

@[simp]
lemma BlockDiagOp.action_tail {ν : PosReal} {N : ℕ} (A : BlockDiagOp ν N)
    (a : ℕ → ℝ) (n : ℕ) (hn : N < n) :
    A.action a n = A.tailDiag n * a n := by
  simp only [action, not_le.mpr hn, ↓reduceDIte]

@[simp]
lemma BlockDiagOp.action_fin {ν : PosReal} {N : ℕ} (A : BlockDiagOp ν N)
    (a : ℕ → ℝ) (n : Fin (N + 1)) :
    A.action a n = ∑ j : Fin (N + 1), A.finBlock n j * a j := by
  simp only [action, Fin.is_le, ↓reduceDIte, Fin.eta]

/-- The projection of a sequence onto its first N+1 coordinates -/
def projFin {ν : PosReal} {N : ℕ} (a : l1Weighted ν) : Fin (N + 1) → ℝ :=
  fun n => lpWeighted.toSeq a n

/-- Embedding a finite vector as a sequence with zero tail -/
def embedFin {N : ℕ} (x : Fin (N + 1) → ℝ) : ℕ → ℝ :=
  fun n => if h : n ≤ N then x ⟨n, Nat.lt_succ_of_le h⟩ else 0

/-- The tail projection: coordinates N+1, N+2, ... -/
def projTail {ν : PosReal} {N : ℕ} (a : l1Weighted ν) : ℕ → ℝ :=
  fun n => if n ≤ N then 0 else lpWeighted.toSeq a n

/-- Direct sum decomposition: a = embedFin(projFin a) + projTail a -/
lemma direct_sum_decomp {ν : PosReal} {N : ℕ} (a : l1Weighted ν) (n : ℕ) :
    lpWeighted.toSeq a n = embedFin (N := N) (projFin (N := N) a) n + projTail (N := N) a n := by
  simp only [embedFin, projFin, projTail]
  split_ifs with h
  · simp only [lpWeighted.toSeq_apply, add_zero]
  · simp only [lpWeighted.toSeq_apply, zero_add]

/-- Bound on the finite block contribution.

    For the finite part, we use the weighted matrix norm. -/
lemma finBlock_norm_bound {ν : PosReal} {N : ℕ} (A : BlockDiagOp ν N) (a : l1Weighted ν) :
    ∑ n : Fin (N + 1), |∑ j : Fin (N + 1), A.finBlock n j * lpWeighted.toSeq a j| * (ν : ℝ) ^ (n : ℕ) ≤
    l1Weighted.finWeightedMatrixNorm ν A.finBlock *
    ∑ j : Fin (N + 1), |lpWeighted.toSeq a j| * (ν : ℝ) ^ (j : ℕ) := by
  calc ∑ n : Fin (N + 1), |∑ j, A.finBlock n j * lpWeighted.toSeq a j| * (ν : ℝ) ^ (n : ℕ)
      -- triangle inequality: |∑ a·b| ≤ ∑ |a|·|b|
      ≤ ∑ n : Fin (N + 1), (∑ j, |A.finBlock n j| * |lpWeighted.toSeq a j|) * (ν : ℝ) ^ (n : ℕ) := by
        apply Finset.sum_le_sum; intro n _
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (PosReal.coe_nonneg ν) _)
        exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp_rw [abs_mul])
      -- distribute ν^n + swap sums
    _ = ∑ j : Fin (N + 1), ∑ n : Fin (N + 1), |A.finBlock n j| * |lpWeighted.toSeq a j| * (ν : ℝ) ^ (n : ℕ) := by
        simp_rw [Finset.sum_mul]; exact Finset.sum_comm
      -- factor out |a_j|
    _ = ∑ j : Fin (N + 1), |lpWeighted.toSeq a j| * ∑ n, |A.finBlock n j| * (ν : ℝ) ^ (n : ℕ) := by
        congr 1; ext j; rw [Finset.mul_sum]; congr 1; ext n; ring
      -- rewrite as matrixColNorm via simp lemma
    _ = ∑ j : Fin (N + 1), |lpWeighted.toSeq a j| * (l1Weighted.matrixColNorm ν A.finBlock j * (ν : ℝ) ^ (j : ℕ)) := by
        simp only [l1Weighted.matrixColNorm_mul_pow]
      -- colNorm ≤ sup, factor out
    _ ≤ l1Weighted.finWeightedMatrixNorm ν A.finBlock * ∑ j : Fin (N + 1), |lpWeighted.toSeq a j| * (ν : ℝ) ^ (j : ℕ) := by
        rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro j _
        exact (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (Finset.le_sup' _ (Finset.mem_univ j))
            (pow_nonneg (PosReal.coe_nonneg ν) _))
          (abs_nonneg _)).trans_eq (mul_left_comm _ _ _)

/-- Bound on the tail contribution using a uniform bound on |tailDiag|. -/
lemma tailDiag_norm_bound {ν : PosReal} {N : ℕ} (A : BlockDiagOp ν N) (a : l1Weighted ν) :
    ∑' n : {n : ℕ // N < n}, |A.tailDiag n * lpWeighted.toSeq a n| * (ν : ℝ) ^ (n : ℕ) ≤
    A.tailBound * ∑' n : {n : ℕ // N < n}, |lpWeighted.toSeq a n| * (ν : ℝ) ^ (n : ℕ) := by
  rw [← tsum_mul_left]
  have h_pw : ∀ n : {n : ℕ // N < n},
      |A.tailDiag n * lpWeighted.toSeq a n| * (ν : ℝ) ^ (n : ℕ) ≤
      A.tailBound * (|lpWeighted.toSeq a n| * (ν : ℝ) ^ (n : ℕ)) := fun ⟨n, hn⟩ => by
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_right (A.tailBound_spec n hn)
      (l1Weighted.weighted_term_nonneg _ _)
  have h_sum_rhs : Summable (fun n : {n : ℕ // N < n} =>
      A.tailBound * (|lpWeighted.toSeq a n| * (ν : ℝ) ^ (n : ℕ))) :=
    (((l1Weighted.mem_iff _).mp a.2).subtype _).mul_left _
  exact (h_sum_rhs.of_nonneg_of_le
    (fun _ => l1Weighted.weighted_term_nonneg _ _) h_pw).tsum_le_tsum
    h_pw h_sum_rhs

/-- Split the ℓ¹ norm into finite and tail parts -/
lemma norm_split {ν : PosReal} {N : ℕ} (a : l1Weighted ν) :
    ‖a‖ = (∑ n : Fin (N + 1), |lpWeighted.toSeq a n| * (ν : ℝ) ^ (n : ℕ)) +
          (∑' n : {n : ℕ // N < n}, |lpWeighted.toSeq a n| * (ν : ℝ) ^ (n : ℕ)) := by
  rw [l1Weighted.norm_eq_tsum]
  -- Split ∑' n : ℕ into ∑ n ≤ N + ∑' n > N
  rw [← Summable.sum_add_tsum_compl (s := Finset.range (N + 1))]
  · congr 1
    · -- Finite part: reindex from Finset.range to Fin
      rw [← Fin.sum_univ_eq_sum_range]
    · -- Tail part: reindex complement
      have h_eq : (↑(Finset.range (N + 1)) : Set ℕ)ᶜ = {n : ℕ | N < n} := by
        ext n; simp only [Set.mem_compl_iff, Finset.coe_range, Set.mem_Iio, not_lt, Set.mem_setOf_eq]; omega
      rw [h_eq]
      simp only [lpWeighted.toSeq_apply]
      rfl
  · -- Summability
    simp only [lpWeighted.toSeq_apply]
    exact (l1Weighted.mem_iff _).mp a.2

/-- The action of a block-diagonal operator preserves membership in ℓ¹_ν,
    provided the tail diagonal is bounded. -/
lemma BlockDiagOp.action_mem {ν : PosReal} {N : ℕ} (A : BlockDiagOp ν N) (a : l1Weighted ν)
    :
    lpWeighted.Mem ν 1 (A.action (lpWeighted.toSeq a)) := by
  rw [l1Weighted.mem_iff]
  have ha := (l1Weighted.mem_iff _).mp a.2
  have hC_nonneg : 0 ≤ A.tailBound := le_trans (abs_nonneg _) (A.tailBound_spec (N + 1) (by omega))
  let finBound := (Finset.univ.sup' Finset.univ_nonempty fun n : Fin (N + 1) =>
      |∑ j : Fin (N + 1), A.finBlock n j * lpWeighted.toSeq a j| * (ν : ℝ) ^ (n : ℕ))
  let g := fun n => (if n ≤ N then finBound else 0) + A.tailBound * (|lpWeighted.toSeq a n| * (ν : ℝ) ^ n)
  refine Summable.of_nonneg_of_le
    (fun n => l1Weighted.weighted_term_nonneg _ _)
    (f := g) (fun n => ?_) ?_
  · -- Pointwise bound
    simp only [g, BlockDiagOp.action]
    split_ifs with h
    · -- n ≤ N: bounded by finBound
      have hn' : n < N + 1 := Nat.lt_succ_of_le h
      exact (Finset.le_sup' (fun m : Fin (N + 1) => |∑ j, A.finBlock m j * lpWeighted.toSeq a j| *
        (ν : ℝ) ^ (m : ℕ)) (Finset.mem_univ ⟨n, hn'⟩)).trans
        (le_add_of_nonneg_right (mul_nonneg hC_nonneg
          (l1Weighted.weighted_term_nonneg _ _)))
    · -- n > N: |tailDiag n * a_n| * ν^n ≤ C * |a_n| * ν^n
      have hn : N < n := Nat.lt_of_succ_le (Nat.not_le.mp h)
      rw [abs_mul, mul_assoc]
      exact (mul_le_mul_of_nonneg_right (A.tailBound_spec n hn)
        (l1Weighted.weighted_term_nonneg _ _)).trans
        (le_add_of_nonneg_left (le_refl _))
  · -- Bounding function is summable
    apply Summable.add
    · apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
      intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      simp only [not_le.mpr (Nat.lt_of_succ_le hn), ↓reduceIte]
    · exact ha.mul_left A.tailBound

/-- The action as a linear map (requires bounded tail for well-definedness) -/
def BlockDiagOp.toLinearMap {ν : PosReal} {N : ℕ} (A : BlockDiagOp ν N)
    : l1Weighted ν →ₗ[ℝ] l1Weighted ν where
  toFun a := lpWeighted.mk (A.action (lpWeighted.toSeq a)) (A.action_mem a)
  map_add' a b := by
    apply lpWeighted.ext; intro n
    simp only [lpWeighted.mk_apply, lpWeighted.add_toSeq, BlockDiagOp.action]
    split_ifs with h
    · rw [← Finset.sum_add_distrib]
      congr 1; ext j; ring
    · ring
  map_smul' c a := by
    apply lpWeighted.ext; intro n
    simp only [lpWeighted.mk_apply, lpWeighted.smul_toSeq, RingHom.id_apply, BlockDiagOp.action]
    split_ifs with h
    · rw [Finset.mul_sum]
      congr 1; ext j; ring
    · ring

/-- The block-diagonal operator as a continuous linear map -/
def BlockDiagOp.toCLM {ν : PosReal} {N : ℕ} (A : BlockDiagOp ν N)
    : l1Weighted ν →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous (A.toLinearMap)
    (max (l1Weighted.finWeightedMatrixNorm ν A.finBlock) A.tailBound)
    (fun a => by
      simp only [BlockDiagOp.toLinearMap]
      rw [BlockDiag.norm_split (N := N)]
      have h_fin : ∑ n : Fin (N + 1), |lpWeighted.toSeq (lpWeighted.mk (A.action (lpWeighted.toSeq a)) (A.action_mem a)) n| * (ν : ℝ) ^ (n : ℕ) =
          ∑ n : Fin (N + 1), |∑ j : Fin (N + 1), A.finBlock n j * lpWeighted.toSeq a j| * (ν : ℝ) ^ (n : ℕ) := by
        congr 1; ext n; congr 1
        simp only [lpWeighted.mk_apply, BlockDiagOp.action, Fin.is_le, ↓reduceDIte]
      have h_tail : ∑' n : {n : ℕ // N < n}, |lpWeighted.toSeq (lpWeighted.mk (A.action (lpWeighted.toSeq a)) (A.action_mem a)) n| * (ν : ℝ) ^ (n : ℕ) =
          ∑' n : {n : ℕ // N < n}, |A.tailDiag n * lpWeighted.toSeq a n| * (ν : ℝ) ^ (n : ℕ) := by
        congr 1; ext ⟨n, hn⟩; congr 1
        simp only [lpWeighted.mk_apply, BlockDiagOp.action, not_le.mpr hn, ↓reduceDIte]
      have hK := BlockDiag.finBlock_norm_bound A a
      have ha_split := BlockDiag.norm_split (N := N) a
      let K := l1Weighted.finWeightedMatrixNorm ν A.finBlock
      simp only [LinearMap.coe_mk, AddHom.coe_mk] at ⊢
      rw [h_fin, h_tail]
      -- fin_part + tail_part ≤ K * fin_norm + C * tail_norm ≤ max(K,C) * ‖a‖
      exact (add_le_add hK (tailDiag_norm_bound A a)).trans
        ((add_le_add
          (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Finset.sum_nonneg fun j _ => l1Weighted.weighted_term_nonneg _ _))
          (mul_le_mul_of_nonneg_right (le_max_right _ _)
            (tsum_nonneg fun n => l1Weighted.weighted_term_nonneg _ _)))
        |>.trans_eq (by rw [← mul_add, ← ha_split])))

/-- The CLM action matches the BlockDiagOp action -/
@[simp]
lemma BlockDiagOp.toCLM_apply {ν : PosReal} {N : ℕ} (A : BlockDiagOp ν N)
        (a : l1Weighted ν) (n : ℕ) :
    lpWeighted.toSeq (A.toCLM a) n = A.action (lpWeighted.toSeq a) n := by
  simp only [toCLM, toLinearMap, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
             lpWeighted.mk_apply]

/-- Finite-coordinate expansion of `h - A(B h)` for block-diagonal operators.
    This is the matrix identity
    `(I - A.finBlock * B.finBlock) * h^(N)` written componentwise. -/
lemma BlockDiagOp.I_sub_comp_action_finite_eq {ν : PosReal} {N : ℕ}
    (A B : BlockDiagOp ν N) (h : l1Weighted ν) (n : Fin (N + 1)) :
    lpWeighted.toSeq h n -
      lpWeighted.toSeq (A.toCLM (B.toCLM h)) n =
    ∑ j : Fin (N + 1), (1 - A.finBlock * B.finBlock) n j * lpWeighted.toSeq h j := by
  simp_rw [BlockDiagOp.toCLM_apply]
  simp only [BlockDiagOp.action, Fin.is_le, ↓reduceDIte]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply]
  ring_nf
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, sub_right_inj]
  simp_rw [BlockDiagOp.toCLM_apply, BlockDiagOp.action_fin]
  -- Expand `B.toCLM` on finite coordinates.
  trans ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
      A.finBlock n x * (B.finBlock x y * lpWeighted.toSeq h y)
  · simp_rw [Finset.mul_sum]
  -- Swap the two finite sums.
  trans ∑ y : Fin (N + 1), ∑ x : Fin (N + 1),
      A.finBlock n x * (B.finBlock x y * lpWeighted.toSeq h y)
  · rw [Finset.sum_comm]
  -- Factor out the `h y` term to match `(A.finBlock * B.finBlock)`.
  trans ∑ y : Fin (N + 1),
      (∑ x : Fin (N + 1), A.finBlock n x * B.finBlock x y) * lpWeighted.toSeq h y
  · apply Finset.sum_congr rfl
    intro y hy
    have hterm : ∀ x : Fin (N + 1),
        A.finBlock n x * (B.finBlock x y * lpWeighted.toSeq h y) =
          (A.finBlock n x * B.finBlock x y) * lpWeighted.toSeq h y := by
      intro x
      ring
    simp_rw [hterm]
    rw [← Finset.sum_mul]
  · rfl

/-- Tail-coordinate cancellation for `h - A(B h)` when tail diagonals multiply to `1`.
    This is the scalar identity `h_n - (a_n * b_n) * h_n = 0`. -/
lemma BlockDiagOp.I_sub_comp_action_tail_eq_zero_of_tail_mul_eq_one {ν : PosReal} {N : ℕ}
    (A B : BlockDiagOp ν N)
    (h_tail_mul_one : ∀ n, N < n → A.tailDiag n * B.tailDiag n = 1)
    (h : l1Weighted ν) (n : ℕ) (hn : N < n) :
    lpWeighted.toSeq h n -
      lpWeighted.toSeq (A.toCLM (B.toCLM h)) n = 0 := by
  rw [BlockDiagOp.toCLM_apply, BlockDiagOp.action_tail _ _ _ hn]
  rw [BlockDiagOp.toCLM_apply (A := B) (a := h) (n := n), BlockDiagOp.action_tail _ _ _ hn]
  rw [← mul_assoc, h_tail_mul_one n hn]
  ring

/-- Finite-coordinate form of `(id - A ∘ B)h` for block-diagonal operators.
    Convenience CLM-level wrapper around `I_sub_comp_action_finite_eq`. -/
lemma BlockDiagOp.I_sub_comp_finite_toSeq_eq {ν : PosReal} {N : ℕ}
    (A B : BlockDiagOp ν N) (h : l1Weighted ν) (n : Fin (N + 1)) :
    lpWeighted.toSeq ((ContinuousLinearMap.id ℝ (l1Weighted ν) -
      A.toCLM.comp B.toCLM) h) n =
    ∑ j : Fin (N + 1), (1 - A.finBlock * B.finBlock) n j * lpWeighted.toSeq h j := by
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_id', id_eq,
    ContinuousLinearMap.coe_comp', Function.comp_apply, lpWeighted.sub_toSeq]
  exact BlockDiagOp.I_sub_comp_action_finite_eq A B h n

/-- Characterize a CLM as a `BlockDiagOp` by providing its finite and tail actions. -/
lemma BlockDiagOp.clm_eq_of_finite_tail (T : l1Weighted ν →L[ℝ] l1Weighted ν)
    (A : BlockDiagOp ν N)
    (hfin : ∀ a (n : Fin (N + 1)),
      lpWeighted.toSeq (T a) n = ∑ j : Fin (N + 1), A.finBlock n j * lpWeighted.toSeq a j)
    (htail : ∀ a n, N < n →
      lpWeighted.toSeq (T a) n = A.tailDiag n * lpWeighted.toSeq a n) :
    T = A.toCLM := by
  ext a n
  by_cases hn : n ≤ N
  · have hT :
        lpWeighted.toSeq (T a) n =
        ∑ j : Fin (N + 1), A.finBlock ⟨n, Nat.lt_succ_of_le hn⟩ j * lpWeighted.toSeq a j := by
      simpa using hfin a ⟨n, Nat.lt_succ_of_le hn⟩
    have hA :
        lpWeighted.toSeq (A.toCLM a) n =
        ∑ j : Fin (N + 1), A.finBlock ⟨n, Nat.lt_succ_of_le hn⟩ j * lpWeighted.toSeq a j := by
      rw [BlockDiagOp.toCLM_apply, BlockDiagOp.action_finite A (lpWeighted.toSeq a) n hn]
    exact hT.trans hA.symm
  · have hn' : N < n := lt_of_not_ge hn
    have hT : lpWeighted.toSeq (T a) n = A.tailDiag n * lpWeighted.toSeq a n := htail a n hn'
    have hA : lpWeighted.toSeq (A.toCLM a) n = A.tailDiag n * lpWeighted.toSeq a n := by
      rw [BlockDiagOp.toCLM_apply, BlockDiagOp.action_tail A (lpWeighted.toSeq a) n hn']
    exact hT.trans hA.symm

/-- Operator norm of the CLM is bounded by max of finite block norm and tail bound -/
lemma BlockDiagOp.norm_toCLM_le (A : BlockDiagOp ν N)
    :
    ‖A.toCLM‖ ≤ max (l1Weighted.finWeightedMatrixNorm ν A.finBlock) A.tailBound :=
  LinearMap.mkContinuous_norm_le _ (le_max_of_le_left (l1Weighted.finWeightedMatrixNorm_nonneg _)) _

/-- If the tail bound is below the finite block norm, the operator norm is controlled
    by the finite block norm alone. -/
lemma BlockDiagOp.norm_toCLM_le_finBlock_of_tailBound_le (A : BlockDiagOp ν N)
    (h_tail : A.tailBound ≤ l1Weighted.finWeightedMatrixNorm ν A.finBlock) :
    ‖A.toCLM‖ ≤ l1Weighted.finWeightedMatrixNorm ν A.finBlock := by
  exact (A.norm_toCLM_le).trans (max_le le_rfl h_tail)

/-- Special case of `norm_toCLM_le_finBlock_of_tailBound_le` when `tailBound = 0`. -/
lemma BlockDiagOp.norm_toCLM_le_finBlock_of_tailBound_zero (A : BlockDiagOp ν N)
    (h_tail0 : A.tailBound = 0) :
    ‖A.toCLM‖ ≤ l1Weighted.finWeightedMatrixNorm ν A.finBlock := by
  refine A.norm_toCLM_le_finBlock_of_tailBound_le ?_
  simpa [h_tail0] using (l1Weighted.finWeightedMatrixNorm_nonneg (ν := ν) A.finBlock)

/-- Block-diagonal operator is injective if finite block matrix is invertible
    and tail diagonal is pointwise nonzero. -/
lemma BlockDiagOp.injective_of_parts {ν : PosReal} {N : ℕ}
    (A : BlockDiagOp ν N)     (h_fin : IsUnit A.finBlock)
    (h_tail : ∀ n, N < n → A.tailDiag n ≠ 0) :
    Function.Injective (A.toCLM) := by
  intro x y h_eq
  have h_diff : A.toCLM (x - y) = 0 := by
    simp only [map_sub, sub_eq_zero]
    exact h_eq
  have h_tail_zero : ∀ n : ℕ, N < n → lpWeighted.toSeq (x - y) n = 0 := by
    intro n hn
    have h_action_n : lpWeighted.toSeq (A.toCLM (x - y)) n = 0 := by
      rw [h_diff]; rfl
    simp only [BlockDiagOp.toCLM_apply, BlockDiagOp.action, not_le.mpr hn, ↓reduceDIte] at h_action_n
    exact (mul_eq_zero.mp h_action_n).resolve_left (h_tail n hn)
  have h_mat_action : ∀ i : Fin (N + 1), ∑ j, A.finBlock i j * lpWeighted.toSeq (x - y) j = 0 := by
    intro i
    have h_action_i : lpWeighted.toSeq (A.toCLM (x - y)) i = 0 := by
      rw [h_diff]; rfl
    simp only [BlockDiagOp.toCLM_apply, BlockDiagOp.action, Fin.is_le, ↓reduceDIte] at h_action_i
    exact h_action_i
  have h_mulVec : A.finBlock.mulVec (fun j => lpWeighted.toSeq (x - y) j) = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    exact h_mat_action i
  obtain ⟨u, hu⟩ := h_fin
  have h_vec_zero := congrArg (u⁻¹.val.mulVec) h_mulVec
  simp only [Matrix.mulVec_zero] at h_vec_zero
  rw [Matrix.mulVec_mulVec, ← hu, Units.inv_mul, Matrix.one_mulVec] at h_vec_zero
  have h_fin_zero : ∀ n : Fin (N + 1), lpWeighted.toSeq (x - y) n = 0 := by
    intro n
    exact congrFun h_vec_zero n
  have h_all_zero : x - y = 0 := by
    ext n
    by_cases hn : n ≤ N
    · exact h_fin_zero ⟨n, Nat.lt_succ_of_le hn⟩
    · push_neg at hn
      exact h_tail_zero n hn
  exact sub_eq_zero.mp h_all_zero

/-- Norm of a BlockDiagOp action on a finitely-supported vector decomposes
    into two finite sums: the matrix part (n ≤ N) and the tail part (N < n ≤ M).

    This is the structural bridge: ‖A·v‖ = finite sum + tail sum, both ℚ-computable.
    Combined with LeanCert evaluators and `finsum_bound`, this gives compact
    certificates for the direct norm bounds (Y₀, Z₀, Z₁, Z₂). -/
lemma BlockDiagOp.norm_action_eq_finsum {ν : PosReal} {N : ℕ}
    (A : BlockDiagOp ν N) (v : l1Weighted ν)
    (M : ℕ) (_hNM : N ≤ M) (hsupp : ∀ n, M < n → lpWeighted.toSeq v n = 0) :
    ‖A.toCLM v‖ =
    (∑ n : Fin (N + 1),
      |∑ j : Fin (N + 1), A.finBlock n j * lpWeighted.toSeq v j| * (ν : ℝ) ^ (n : ℕ)) +
    (∑ n ∈ Finset.Icc (N + 1) M,
      |A.tailDiag n * lpWeighted.toSeq v n| * (ν : ℝ) ^ n) := by
  rw [norm_split (N := N)]
  congr 1
  · -- Finite part: toCLM action on Fin indices = finBlock matrix action
    congr 1; ext n
    simp only [BlockDiagOp.toCLM_apply, BlockDiagOp.action_fin]
  · -- Tail part: collapse tsum to finsum via finite support
    -- Step 1: Rewrite each term using toCLM_apply + action_tail
    have h_term : ∀ (x : {n : ℕ // N < n}),
        |lpWeighted.toSeq (A.toCLM v) ↑x| * (ν : ℝ) ^ (↑x : ℕ) =
        |A.tailDiag ↑x * lpWeighted.toSeq v ↑x| * (ν : ℝ) ^ (↑x : ℕ) := fun ⟨n, hn⟩ => by
      simp only [BlockDiagOp.toCLM_apply, BlockDiagOp.action_tail _ _ _ hn]
    simp_rw [h_term]
    -- Step 2: Convert subtype tsum → indicator tsum on ℕ
    set g : ℕ → ℝ := fun n => |A.tailDiag n * lpWeighted.toSeq v n| * (ν : ℝ) ^ n
    show ∑' (x : ↑{n : ℕ | N < n}), g ↑x = _
    rw [tsum_subtype]
    -- Step 3: Collapse indicator tsum to finite sum (zero outside Icc)
    rw [tsum_eq_sum (s := Finset.Icc (N + 1) M)]
    · -- Simplify indicator on Icc elements (all satisfy N < n)
      apply Finset.sum_congr rfl (fun n hn => by
        simp only [Set.indicator_apply, Set.mem_setOf_eq]
        exact if_pos (by simp only [Finset.mem_Icc] at hn; omega))
    · -- Zero outside Icc: either n ≤ N (indicator = 0) or n > M (support = 0)
      intro n hn
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      by_cases hN : N < n
      · rw [if_pos hN]
        have hM : M < n := by
          simp only [Finset.mem_Icc, not_and_or, not_le] at hn
          omega
        simp only [g, hsupp n hM, mul_zero, abs_zero, zero_mul]
      · exact if_neg hN

/-! ## ℚ Bridge Infrastructure

Generic machinery for proving `A.action v n = ↑(blockDiagAction_q ... n)`.
The pattern: unfold action → by_cases fin/tail → rewrite entries to ℚ casts → push_cast; ring.
-/

/-- Block-diagonal action computed entirely in ℚ. -/
def blockDiagAction_q
    (matCols : Array (Array ℚ)) (vec : ℕ → ℚ)
    (tailCoeff : ℚ) (N : ℕ) (n : ℕ) : ℚ :=
  if n ≤ N then
    ∑ j : Fin (N + 1), (matCols.getD (j : ℕ) #[]).getD n 0 * vec j
  else
    tailCoeff * vec n

/-- Generic bridge: `A.action v n = ↑(blockDiagAction_q ... n)` given per-entry ℚ hypotheses
    for the matrix (`hmat`), vector (`hvec`), and tail diagonal (`htail`). -/
lemma BlockDiagOp.action_eq_rat_cast {ν : PosReal} {N : ℕ}
    (A : BlockDiagOp ν N) (v : ℕ → ℝ)
    (matCols : Array (Array ℚ)) (vec_q : ℕ → ℚ) (tailCoeff : ℚ)
    (hmat : ∀ (i : Fin (N + 1)) (j : Fin (N + 1)),
      A.finBlock i j = ((matCols.getD (j : ℕ) #[]).getD (i : ℕ) 0 : ℝ))
    (hvec : ∀ n, v n = (vec_q n : ℝ))
    (htail : ∀ n, N < n → A.tailDiag n = (tailCoeff : ℝ))
    (n : ℕ) :
    A.action v n = (blockDiagAction_q matCols vec_q tailCoeff N n : ℝ) := by
  simp only [blockDiagAction_q]
  by_cases hn : n ≤ N
  · rw [action_fin _ _ ⟨n, Nat.lt_succ_of_le hn⟩, if_pos hn]
    simp_rw [hmat, hvec]; push_cast; ring
  · push_neg at hn
    rw [action_tail _ _ _ hn, if_neg (not_le.mpr hn), htail n hn, hvec]
    push_cast; ring

/-- CLM-level bridge: `toSeq(A.toCLM a) n = ↑(blockDiagAction_q ... n)`. -/
lemma BlockDiagOp.toCLM_action_eq_rat_cast {ν : PosReal} {N : ℕ}
    (A : BlockDiagOp ν N) (a : l1Weighted ν)
    (matCols : Array (Array ℚ)) (vec_q : ℕ → ℚ) (tailCoeff : ℚ)
    (hmat : ∀ (i : Fin (N + 1)) (j : Fin (N + 1)),
      A.finBlock i j = ((matCols.getD (j : ℕ) #[]).getD (i : ℕ) 0 : ℝ))
    (hvec : ∀ n, lpWeighted.toSeq a n = (vec_q n : ℝ))
    (htail : ∀ n, N < n → A.tailDiag n = (tailCoeff : ℝ))
    (n : ℕ) :
    lpWeighted.toSeq (A.toCLM a) n = (blockDiagAction_q matCols vec_q tailCoeff N n : ℝ) := by
  rw [toCLM_apply, action_eq_rat_cast A _ matCols vec_q tailCoeff hmat hvec htail]

end BlockDiag

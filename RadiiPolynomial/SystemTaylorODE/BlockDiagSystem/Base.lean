import RadiiPolynomial.SystemTaylorODE.Core
import RadiiPolynomial.SystemTaylorODE.lpWeighted
import RadiiPolynomial.SystemTaylorODE.LpOneBanachAlgebra
import RadiiPolynomial.SystemTaylorODE.NormHelpers
import RadiiPolynomial.SystemTaylorODE.OperatorNorm

/-!
# BlockDiagSystem Base

Core structural layer for Section 8.2 operators:
- component-coupled CLM matrices
- componentwise diagonal CLMs
- finite `L×L` block norm aggregation
- coefficient-level block-diagonal data and composition (incl. `actionFinite_eq_zero_of_coeff_fin_zero`)
-/

open scoped Topology
open Metric Set Filter ContinuousLinearMap

noncomputable section

namespace SystemTaylorODE

variable {Seq : PosReal → Type*}

/-! ## 1. Component-Coupled Block Operators -/

section ComponentMatrix

variable {ν ν' : PosReal} {L : ℕ}
variable [NormedAddCommGroup (Seq ν)] [NormedSpace ℝ (Seq ν)]
variable [NormedAddCommGroup (Seq ν')] [NormedSpace ℝ (Seq ν')]

/-- Full component-coupled operator matrix on system space:
`(l,j)` stores the block `Seq ν →L[ℝ] Seq ν'`. -/
abbrev ComponentwiseMatrixOp
    (Seqν : Type*) (Seqν' : Type*)
    [NormedAddCommGroup Seqν] [NormedSpace ℝ Seqν]
    [NormedAddCommGroup Seqν'] [NormedSpace ℝ Seqν']
    (L : ℕ) := Fin L → Fin L → (Seqν →L[ℝ] Seqν')

/-- Lift an `L × L` block operator matrix to a CLM `(Seq ν)^L → (Seq ν')^L`:
`(Ax)_l = ∑_j A_{l,j}(x_j)`. -/
def ComponentwiseMatrixOp.toCLM
    (A : ComponentwiseMatrixOp (Seq ν) (Seq ν') L) :
    (X Seq ν L) →L[ℝ] (Y Seq ν' L) :=
  ContinuousLinearMap.pi fun l =>
    ∑ j : Fin L, (A l j).comp (ContinuousLinearMap.proj j)

@[simp]
lemma ComponentwiseMatrixOp.toCLM_apply
    (A : ComponentwiseMatrixOp (Seq ν) (Seq ν') L)
    (x : X Seq ν L) (l : Fin L) :
    ComponentwiseMatrixOp.toCLM A x l = ∑ j : Fin L, A l j (x j) := by
  simp [ComponentwiseMatrixOp.toCLM]

end ComponentMatrix

/-! ## 2. Componentwise-Diagonal Operators -/

section Componentwise

variable {ν : PosReal} {L : ℕ}
variable [NormedAddCommGroup (Seq ν)]
variable [NormedSpace ℝ (Seq ν)]

/-- One scalar CLM per component. -/
abbrev ComponentwiseBlockDiagOp (Seqν : Type*) [NormedAddCommGroup Seqν] [NormedSpace ℝ Seqν]
    (L : ℕ) := Fin L → (Seqν →L[ℝ] Seqν)

/-- Lift componentwise scalar CLMs to a CLM on `(Seq ν)^L`. -/
def ComponentwiseBlockDiagOp.toCLM
    (A : ComponentwiseBlockDiagOp (Seq ν) L) :
    (X Seq ν L) →L[ℝ] (X Seq ν L) :=
  ContinuousLinearMap.pi fun i =>
    (A i).comp (ContinuousLinearMap.proj i)

@[simp]
lemma ComponentwiseBlockDiagOp.toCLM_apply
    (A : ComponentwiseBlockDiagOp (Seq ν) L)
    (x : X Seq ν L) (i : Fin L) :
    ComponentwiseBlockDiagOp.toCLM A x i = (A i) (x i) := by
  simp [ComponentwiseBlockDiagOp.toCLM]

/-- Injectivity of the componentwise lift from componentwise injectivity. -/
lemma ComponentwiseBlockDiagOp.injective_of_components
    (A : ComponentwiseBlockDiagOp (Seq ν) L)
    (hcomp : ∀ i : Fin L, Function.Injective (A i)) :
    Function.Injective (ComponentwiseBlockDiagOp.toCLM A) := by
  intro x y hxy
  exact funext fun i =>
    hcomp i (by
      simpa [ComponentwiseBlockDiagOp.toCLM_apply] using congrArg (fun v => v i) hxy)

/-- Alias in certificate style. -/
lemma ComponentwiseBlockDiagOp.injective_of_component_certificates
    (A : ComponentwiseBlockDiagOp (Seq ν) L)
    (h_inj : ∀ i : Fin L, Function.Injective (A i)) :
    Function.Injective (ComponentwiseBlockDiagOp.toCLM A) :=
  ComponentwiseBlockDiagOp.injective_of_components A h_inj

end Componentwise

/-! ## 3. Finite Block-Matrix Norm Aggregation -/

section FiniteBlockNorm

variable {ν : PosReal} {L N : ℕ}

/-- Finite-dimensional `L × L` block matrix.
Each entry is an `(N+1)×(N+1)` real matrix acting on one component. -/
abbrev FiniteBlockMatrix (L N : ℕ) :=
  Fin L → Fin L → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ

/-- Norm of one block entry `(l,j)` in the weighted finite norm. -/
def blockEntryNorm (ν : PosReal) (A : FiniteBlockMatrix L N)
    (l j : Fin L) : ℝ :=
  l1Weighted.finWeightedMatrixNorm ν (A l j)

/-- Row aggregation for system coupling:
`rowNorm l = ∑_j ‖A_{l,j}‖`. -/
def blockRowNorm (ν : PosReal) (A : FiniteBlockMatrix L N) (l : Fin L) : ℝ :=
  ∑ j : Fin L, blockEntryNorm ν A l j

/-- System finite block-matrix norm:
`max_l ∑_j ‖A_{l,j}‖`.

This is the natural aggregation for product-space estimates with component coupling
in Section 8.2. -/
def finiteBlockMatrixNorm [NeZero L] (ν : PosReal) (A : FiniteBlockMatrix L N) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun l => blockRowNorm ν A l)

lemma blockEntryNorm_nonneg (A : FiniteBlockMatrix L N) (l j : Fin L) :
    0 ≤ blockEntryNorm ν A l j := by
  exact l1Weighted.finWeightedMatrixNorm_nonneg (ν := ν) (A l j)

lemma blockRowNorm_nonneg (A : FiniteBlockMatrix L N) (l : Fin L) :
    0 ≤ blockRowNorm ν A l := by
  unfold blockRowNorm
  exact Finset.sum_nonneg (fun j _ => blockEntryNorm_nonneg (ν := ν) A l j)

lemma finiteBlockMatrixNorm_nonneg [NeZero L] (A : FiniteBlockMatrix L N) :
    0 ≤ finiteBlockMatrixNorm ν A := by
  unfold finiteBlockMatrixNorm
  exact Finset.le_sup'_of_le (fun l : Fin L => blockRowNorm ν A l) (Finset.mem_univ 0)
    (blockRowNorm_nonneg (ν := ν) A 0)

lemma finiteBlockMatrixNorm_le_of_blockRowNorm_le
    [NeZero L] (A : FiniteBlockMatrix L N) (C : ℝ)
    (hrow : ∀ l : Fin L, blockRowNorm ν A l ≤ C) :
    finiteBlockMatrixNorm ν A ≤ C := by
  unfold finiteBlockMatrixNorm
  exact Finset.sup'_le Finset.univ_nonempty (fun l : Fin L => blockRowNorm ν A l) (by
    intro l _
    exact hrow l)

end FiniteBlockNorm

/-! ## 4. Coefficient-Level Block-Diagonal Data -/

section SystemBlockDiagData

variable {L N : ℕ}

/-- Coefficient representation of an `L`-component sequence object. -/
abbrev SystemCoeff (L : ℕ) := Fin L → ℕ → ℝ

/-- 8.2-style block operator data for Eq. (8.21):
- finite coupled `L×L` block on modes `0..N` (`A_N π_N`)
- componentwise diagonal tail on modes `N+1..∞` (`A_∞ π_{N,∞}`). -/
structure SystemBlockDiagData (L N : ℕ) where
  /-- Finite coupled block matrix (`L×L` blocks, each `(N+1)×(N+1)`). -/
  finBlock : FiniteBlockMatrix L N
  /-- Tail diagonal by component and mode. -/
  tailDiag : Fin L → ℕ → ℝ
  /-- Uniform tail bound for all components and tail modes. -/
  tailBound : ℝ
  /-- Tail bound certificate. -/
  tailBound_spec : ∀ l n, N < n → |tailDiag l n| ≤ tailBound

/-- Finite-mode part (`A_N π_N b`) at coefficient level. -/
def SystemBlockDiagData.actionFinite
    (A : SystemBlockDiagData L N) (b : SystemCoeff L) : SystemCoeff L :=
  fun l n =>
    if hn : n ≤ N then
      ∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k * b j k
    else
      0

/-- Tail part (`A_∞ π_{N,∞} b`) at coefficient level. -/
def SystemBlockDiagData.actionTail
    (A : SystemBlockDiagData L N) (b : SystemCoeff L) : SystemCoeff L :=
  fun l n =>
    if n ≤ N then
      0
    else
      A.tailDiag l n * b l n

/-- Full 8.2-style action `Ab = A_N π_N b + A_∞ π_{N,∞} b`. -/
def SystemBlockDiagData.action
    (A : SystemBlockDiagData L N) (b : SystemCoeff L) : SystemCoeff L :=
  fun l n => A.actionFinite b l n + A.actionTail b l n

@[simp]
lemma SystemBlockDiagData.actionFinite_finite
    (A : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    A.actionFinite b l n =
      ∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k * b j k := by
  simp [SystemBlockDiagData.actionFinite, hn]

@[simp]
lemma SystemBlockDiagData.actionFinite_tail
    (A : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : N < n) :
    A.actionFinite b l n = 0 := by
  simp [SystemBlockDiagData.actionFinite, Nat.not_le.mpr hn]

lemma SystemBlockDiagData.actionFinite_eq_zero_of_coeff_fin_zero
    (A : SystemBlockDiagData L N) (c : SystemCoeff L)
    (hc : ∀ j : Fin L, ∀ k : Fin (N + 1), c j k = 0) :
    ∀ l n, A.actionFinite c l n = 0 := by
  intro l n
  by_cases hn : n ≤ N
  · rw [A.actionFinite_finite c l n hn]
    exact Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => by rw [hc j k, mul_zero]
  · exact A.actionFinite_tail c l n (Nat.lt_of_not_ge hn)

@[simp]
lemma SystemBlockDiagData.actionTail_finite
    (A : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    A.actionTail b l n = 0 := by
  simp [SystemBlockDiagData.actionTail, hn]

@[simp]
lemma SystemBlockDiagData.actionTail_tail
    (A : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : N < n) :
    A.actionTail b l n = A.tailDiag l n * b l n := by
  simp [SystemBlockDiagData.actionTail, Nat.not_le.mpr hn]

@[simp]
lemma SystemBlockDiagData.action_finite
    (A : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    A.action b l n =
      ∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k * b j k := by
  simp [SystemBlockDiagData.action, hn, SystemBlockDiagData.actionFinite]

@[simp]
lemma SystemBlockDiagData.action_tail
    (A : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : N < n) :
    A.action b l n = A.tailDiag l n * b l n := by
  simp [SystemBlockDiagData.action, Nat.not_le.mpr hn,
    SystemBlockDiagData.actionFinite, SystemBlockDiagData.actionTail]

@[simp]
lemma SystemBlockDiagData.action_fin
    (A : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : Fin (N + 1)) :
    A.action b l n = ∑ j : Fin L, ∑ k : Fin (N + 1), A.finBlock l j n k * b j k := by
  simp [SystemBlockDiagData.action, SystemBlockDiagData.actionFinite, Fin.is_le]

/-! ### Coefficient-level decomposition and composition helpers -/

/-- Split form of the coefficient action into finite and tail parts. -/
lemma SystemBlockDiagData.action_eq_actionFinite_add_actionTail
    (A : SystemBlockDiagData L N) (b : SystemCoeff L) :
    A.action b = fun l n => A.actionFinite b l n + A.actionTail b l n := rfl

/-- Pointwise nonnegativity witness for the uniform tail bound. -/
lemma SystemBlockDiagData.tailBound_nonneg_at
    (A : SystemBlockDiagData L N) (l : Fin L) :
    0 ≤ A.tailBound := by
  exact le_trans (abs_nonneg (A.tailDiag l (N + 1)))
    (A.tailBound_spec l (N + 1) (by omega))

/-- Coefficient-level composition of 8.2 block operators. -/
def SystemBlockDiagData.comp
    (A B : SystemBlockDiagData L N) : SystemBlockDiagData L N where
  finBlock := fun l i => ∑ j : Fin L, A.finBlock l j * B.finBlock j i
  tailDiag := fun l n => A.tailDiag l n * B.tailDiag l n
  tailBound := A.tailBound * B.tailBound
  tailBound_spec := by
    intro l n hn
    have hA0 : 0 ≤ A.tailBound := A.tailBound_nonneg_at l
    rw [abs_mul]
    exact mul_le_mul (A.tailBound_spec l n hn) (B.tailBound_spec l n hn)
      (abs_nonneg (B.tailDiag l n)) hA0

@[simp]
lemma SystemBlockDiagData.comp_finBlock
    (A B : SystemBlockDiagData L N) (l i : Fin L) :
    (A.comp B).finBlock l i = ∑ j : Fin L, A.finBlock l j * B.finBlock j i := rfl

@[simp]
lemma SystemBlockDiagData.comp_tailDiag
    (A B : SystemBlockDiagData L N) (l : Fin L) (n : ℕ) :
    (A.comp B).tailDiag l n = A.tailDiag l n * B.tailDiag l n := rfl

/-! ### Composition at coefficient level -/

/-! The next lemmas isolate finite-mode and tail-mode formulas for
composition before assembling the global identity. -/

/-- Finite-mode expansion of `A.action (B.action b)` for `n ≤ N`. -/
lemma SystemBlockDiagData.action_comp_finite
    (A B : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    A.action (B.action b) l n =
      ∑ j : Fin L, ∑ k : Fin (N + 1),
        A.finBlock l j ⟨n, Nat.lt_succ_of_le hn⟩ k * (B.action b j k) := by
  rw [SystemBlockDiagData.action_finite (A := A) (b := B.action b) (l := l) (n := n) hn]

/-- Tail-mode expansion of `A.action (B.action b)` for `N < n`. -/
lemma SystemBlockDiagData.action_comp_tail
    (A B : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : N < n) :
    A.action (B.action b) l n =
      (A.tailDiag l n * B.tailDiag l n) * b l n := by
  rw [SystemBlockDiagData.action_tail (A := A) (b := B.action b) (l := l) (n := n) hn]
  rw [SystemBlockDiagData.action_tail (A := B) (b := b) (l := l) (n := n) hn]
  ring

/-- Finite-mode formula for `(A.comp B).action`. -/
lemma SystemBlockDiagData.comp_action_finite
    (A B : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    (A.comp B).action b l n =
      ∑ i : Fin L, ∑ m : Fin (N + 1),
        ((∑ j : Fin L, A.finBlock l j * B.finBlock j i) ⟨n, Nat.lt_succ_of_le hn⟩ m) * b i m := by
  rw [SystemBlockDiagData.action_finite (A := A.comp B) (b := b) (l := l) (n := n) hn]
  simp [SystemBlockDiagData.comp]

/-- Tail-mode formula for `(A.comp B).action`. -/
lemma SystemBlockDiagData.comp_action_tail
    (A B : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : N < n) :
    (A.comp B).action b l n =
      (A.tailDiag l n * B.tailDiag l n) * b l n := by
  rw [SystemBlockDiagData.action_tail (A := A.comp B) (b := b) (l := l) (n := n) hn]
  simp [SystemBlockDiagData.comp, mul_assoc]

/-- Finite-mode compatibility for composition:
`(A.comp B).action = A.action ∘ B.action` on `n ≤ N`. -/
lemma SystemBlockDiagData.comp_action_eq_action_comp_finite
    (A B : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    (A.comp B).action b l n = A.action (B.action b) l n := by
  rw [SystemBlockDiagData.comp_action_finite (A := A) (B := B) (b := b) (l := l) (n := n) hn]
  rw [SystemBlockDiagData.action_comp_finite (A := A) (B := B) (b := b) (l := l) (n := n) hn]
  simp [SystemBlockDiagData.action_fin, Matrix.sum_apply, Matrix.mul_apply,
    Finset.mul_sum, mul_left_comm, mul_comm]
  let f : Fin L → Fin (N + 1) → Fin L → Fin (N + 1) → ℝ :=
    fun x x₁ x₂ x₃ => b x x₁ * (A.finBlock l x₂ ⟨n, Nat.lt_succ_of_le hn⟩ x₃ * B.finBlock x₂ x x₃ x₁)
  simpa using sum4_swap_pairs f

/-- Tail-mode compatibility for composition:
`(A.comp B).action = A.action ∘ B.action` on `N < n`. -/
lemma SystemBlockDiagData.comp_action_eq_action_comp_tail
    (A B : SystemBlockDiagData L N) (b : SystemCoeff L)
    (l : Fin L) (n : ℕ) (hn : N < n) :
    (A.comp B).action b l n = A.action (B.action b) l n := by
  rw [SystemBlockDiagData.comp_action_tail (A := A) (B := B) (b := b) (l := l) (n := n) hn]
  rw [SystemBlockDiagData.action_comp_tail (A := A) (B := B) (b := b) (l := l) (n := n) hn]

/-- Full coefficient-level composition identity:
`(A.comp B).action = A.action ∘ B.action`. -/
lemma SystemBlockDiagData.comp_action_eq_action_comp
    (A B : SystemBlockDiagData L N) (b : SystemCoeff L) :
    (A.comp B).action b = A.action (B.action b) := by
  funext l n
  by_cases hn : n ≤ N
  · exact SystemBlockDiagData.comp_action_eq_action_comp_finite
      (A := A) (B := B) (b := b) (l := l) (n := n) hn
  · exact SystemBlockDiagData.comp_action_eq_action_comp_tail
      (A := A) (B := B) (b := b) (l := l) (n := n) (Nat.lt_of_not_ge hn)

end SystemBlockDiagData

end SystemTaylorODE

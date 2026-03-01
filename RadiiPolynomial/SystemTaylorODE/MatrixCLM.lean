import RadiiPolynomial.SystemTaylorODE.lpWeighted
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Finite Matrix-To-CLM Bridge On Weighted `ℓ¹`

This file provides the structural bridge from finite matrices to continuous linear
maps on the finite weighted space:
- `FinWeighted.Space`
- `FinWeightedMatrix.mulVecWeightedLinear`
- `FinWeightedMatrix.toWeightedCLM`

It also includes transport lemmas for multiplication/subtraction at the CLM level.
-/

open scoped BigOperators Topology NNReal ENNReal Matrix
open Metric Set Filter ContinuousLinearMap

noncomputable section

namespace SystemTaylorODE

namespace FinWeighted

variable {N : ℕ}

/-- Finite weighted `ℓ¹` space on `Fin (N+1)`. -/
abbrev Space (ν : PosReal) (N : ℕ) := PiLp 1 (fun n : Fin (N + 1) => ScaledReal ν n)

lemma norm_eq_sum {ν : PosReal} {N : ℕ} (x : Space ν N) :
    ‖x‖ = ∑ n : Fin (N + 1), |ScaledReal.toReal (x n)| * (ν : ℝ) ^ (n : ℕ) := by
  rw [PiLp.norm_eq_sum (p := 1) (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one]
  rfl

lemma norm_eq_finl1WeightedNorm {ν : PosReal} {N : ℕ} (x : Space ν N) :
    ‖x‖ = l1Weighted.finl1WeightedNorm ν.toNNReal (fun n => x n) := by
  rw [norm_eq_sum, l1Weighted.finl1WeightedNorm]
  rfl

/-- Standard basis vector `eⱼ`. -/
def stdBasis {ν : PosReal} {N : ℕ} (j : Fin (N + 1)) : Space ν N :=
  WithLp.toLp 1 (fun n => if n = j then (1 : ScaledReal ν n) else 0)

@[simp]
lemma stdBasis_apply_self {ν : PosReal} {N : ℕ} (j : Fin (N + 1)) :
    stdBasis (ν := ν) j j = 1 := by
  simp [stdBasis]

@[simp]
lemma stdBasis_apply_ne {ν : PosReal} {N : ℕ} (i j : Fin (N + 1)) (h : i ≠ j) :
    stdBasis (ν := ν) j i = 0 := by
  simp [stdBasis, h]

lemma norm_stdBasis {ν : PosReal} {N : ℕ} (j : Fin (N + 1)) :
    ‖stdBasis (ν := ν) j‖ = (ν : ℝ) ^ (j : ℕ) := by
  rw [norm_eq_sum]
  simp only [stdBasis]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ j) h

end FinWeighted

namespace FinWeightedMatrix

variable {N : ℕ}

/-- Matrix action on finite weighted `ℓ¹` space. -/
def mulVecWeightedLinear {ν : PosReal} {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    FinWeighted.Space ν N →ₗ[ℝ] FinWeighted.Space ν N where
  toFun x := WithLp.toLp 1 (fun i => ScaledReal.ofReal (∑ j, A i j * ScaledReal.toReal (x j)))
  map_add' x y := by
    ext i
    simp only [PiLp.add_apply, ScaledReal.toReal_apply, ScaledReal.ofReal_apply]
    rw [← Finset.sum_add_distrib]
    congr 1
    ext k
    ring
  map_smul' c x := by
    ext i
    simp only [PiLp.smul_apply, ScaledReal.toReal_apply, ScaledReal.ofReal_apply,
      RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    ext k
    ring

lemma mulVecWeightedLinear_norm_le {ν : PosReal} {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (x : FinWeighted.Space ν N) :
    ‖mulVecWeightedLinear A x‖ ≤ l1Weighted.finWeightedMatrixNorm ν A * ‖x‖ := by
  rw [FinWeighted.norm_eq_finl1WeightedNorm, FinWeighted.norm_eq_finl1WeightedNorm]
  simpa [mulVecWeightedLinear, LinearMap.coe_mk, AddHom.coe_mk,
    ScaledReal.toReal, ScaledReal.ofReal]
    using (l1Weighted.finWeightedMatrixNorm_mulVec_le
      (ν := ν) (N := N) A (fun k => ScaledReal.toReal (x k)))

/-- Matrix as CLM on finite weighted `ℓ¹`. -/
def toWeightedCLM {ν : PosReal} {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    FinWeighted.Space ν N →L[ℝ] FinWeighted.Space ν N :=
  LinearMap.mkContinuous (mulVecWeightedLinear A)
    (l1Weighted.finWeightedMatrixNorm ν A) (mulVecWeightedLinear_norm_le A)

@[simp] lemma mulVecWeightedLinear_apply {ν : PosReal} {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (x : FinWeighted.Space ν N) (i : Fin (N + 1)) :
    mulVecWeightedLinear (ν := ν) A x i =
      ScaledReal.ofReal (∑ j, A i j * ScaledReal.toReal (x j)) := rfl

@[simp] lemma toWeightedCLM_apply {ν : PosReal} {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (x : FinWeighted.Space ν N) (i : Fin (N + 1)) :
    toWeightedCLM (ν := ν) A x i =
      ScaledReal.ofReal (∑ j, A i j * ScaledReal.toReal (x j)) := by
  rfl

@[simp] lemma toReal_toWeightedCLM_apply {ν : PosReal} {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (x : FinWeighted.Space ν N) (i : Fin (N + 1)) :
    ScaledReal.toReal (toWeightedCLM (ν := ν) A x i) = ∑ j, A i j * ScaledReal.toReal (x j) := by
  simp [toWeightedCLM]

lemma opNorm_toWeightedCLM_le {ν : PosReal} {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ‖toWeightedCLM (ν := ν) A‖ ≤ l1Weighted.finWeightedMatrixNorm ν A := by
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · exact l1Weighted.finWeightedMatrixNorm_nonneg (ν := ν) A
  · intro x
    exact mulVecWeightedLinear_norm_le A x

lemma toWeightedCLM_mul {ν : PosReal} {N : ℕ}
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    toWeightedCLM (ν := ν) (A * B) =
      (toWeightedCLM (ν := ν) A).comp (toWeightedCLM (ν := ν) B) := by
  ext x i
  change (∑ j, (A * B) i j * ScaledReal.toReal (x j)) =
    ∑ j, A i j * ScaledReal.toReal (toWeightedCLM (ν := ν) B x j)
  simp [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [mul_assoc]

lemma toWeightedCLM_one_sub {ν : PosReal} {N : ℕ}
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    toWeightedCLM (ν := ν) (1 - M) =
      ContinuousLinearMap.id ℝ (FinWeighted.Space ν N) - toWeightedCLM (ν := ν) M := by
  ext x i
  simp [Matrix.sub_apply, Matrix.one_apply, Finset.sum_sub_distrib, sub_mul]

end FinWeightedMatrix

end SystemTaylorODE


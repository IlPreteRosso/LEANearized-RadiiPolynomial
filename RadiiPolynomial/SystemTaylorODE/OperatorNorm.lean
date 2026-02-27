import RadiiPolynomial.SystemTaylorODE.MatrixCLM
import RadiiPolynomial.RadiiPolyGeneral

/-!
# Operator-Norm Theorems For Finite Weighted Blocks

This file keeps the norm-level and invertibility-level results:
- weighted matrix norm = induced operator norm (Ex. 2.7.2)
- matrix invertibility transfer from `toWeightedCLM`
- Neumann-style criterion via `‖I - M‖ < 1`

The matrix-to-CLM construction API (`toWeightedCLM`, multiplication/subtraction
transport, apply lemmas) lives in `MatrixCLM.lean`.
-/

open scoped BigOperators Topology NNReal ENNReal Matrix
open Metric Set Filter ContinuousLinearMap

noncomputable section

namespace SystemTaylorODE

namespace FinWeightedMatrix

variable {N : ℕ}

lemma opNorm_achieved_on_basis {ν : PosReal} {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (j : Fin (N + 1)) :
    ‖toWeightedCLM (ν := ν) A (FinWeighted.stdBasis j)‖ =
      l1Weighted.matrixColNorm ν A j * (ν : ℝ) ^ (j : ℕ) := by
  simp only [toWeightedCLM]
  rw [FinWeighted.norm_eq_sum]
  have h_apply : ∀ i,
      ScaledReal.toReal ((mulVecWeightedLinear (ν := ν) A (FinWeighted.stdBasis j)).ofLp i) = A i j := by
    intro i
    simp only [mulVecWeightedLinear, LinearMap.coe_mk, AddHom.coe_mk,
      ScaledReal.toReal, ScaledReal.ofReal, FinWeighted.stdBasis]
    rw [Finset.sum_eq_single j]
    · simp only [↓reduceIte, mul_one]
      rfl
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd (Finset.mem_univ j) h
  simp only [LinearMap.mkContinuous, coe_mk']
  have h' : ∀ i, |((mulVecWeightedLinear A (FinWeighted.stdBasis (ν := ν) j)).ofLp i)| = |A i j| := by
    intro i
    rw [← h_apply]
    rfl
  simp only [ScaledReal.toReal_apply, h', l1Weighted.matrixColNorm_mul_pow]

/-- Ex. 2.7.2: weighted matrix norm equals induced operator norm. -/
theorem finWeightedMatrixNorm_eq_opNorm {ν : PosReal} {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    l1Weighted.finWeightedMatrixNorm ν A = ‖toWeightedCLM (ν := ν) A‖ := by
  apply le_antisymm
  · rw [l1Weighted.finWeightedMatrixNorm]
    apply Finset.sup'_le
    intro j _
    rw [l1Weighted.matrixColNorm]
    have h_pos : (0 : ℝ) < (ν : ℝ) ^ (j : ℕ) := pow_pos (PosReal.coe_pos ν) _
    refine (le_trans
      (b := ‖toWeightedCLM (ν := ν) A (FinWeighted.stdBasis j)‖ / (ν : ℝ) ^ (j : ℕ)) ?_ ?_)
    · exact le_of_eq (by
        rw [opNorm_achieved_on_basis, l1Weighted.matrixColNorm]
        field_simp [h_pos])
    · rw [div_le_iff₀ h_pos]
      simpa [FinWeighted.norm_stdBasis] using
        (ContinuousLinearMap.le_opNorm (toWeightedCLM (ν := ν) A) (FinWeighted.stdBasis j))
  · exact opNorm_toWeightedCLM_le A

lemma matrix_isUnit_of_toWeightedCLM_isUnit {ν : PosReal} {N : ℕ}
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (h : IsUnit (toWeightedCLM (ν := ν) M)) :
    IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det _, isUnit_iff_ne_zero]
  intro h_det
  obtain ⟨u, hu⟩ := h
  have h_inj : Function.Injective (toWeightedCLM (ν := ν) M) := by
    rw [← hu]
    have h_left_inv : Function.LeftInverse u.inv u.val := fun x => by
      have hx := congrFun (congrArg DFunLike.coe u.inv_mul) x
      simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using hx
    exact h_left_inv.injective
  have h_det_lin : LinearMap.det (Matrix.toLin' M) = 0 := by
    rw [LinearMap.det_toLin']
    exact h_det
  have h_ker_nontrivial := LinearMap.bot_lt_ker_of_det_eq_zero h_det_lin
  rw [bot_lt_iff_ne_bot, ne_eq, Submodule.eq_bot_iff] at h_ker_nontrivial
  push_neg at h_ker_nontrivial
  obtain ⟨v, hv_ker, hv_ne⟩ := h_ker_nontrivial
  rw [LinearMap.mem_ker] at hv_ker
  have hv_mulVec : M *ᵥ v = 0 := by
    simpa only [Matrix.toLin'_apply] using hv_ker
  let x : FinWeighted.Space ν N := WithLp.toLp 1 (fun i => v i)
  have hx_ne : x ≠ 0 := by
    intro hx
    apply hv_ne
    ext i
    exact congrFun (congrArg WithLp.ofLp hx) i
  have hx_zero : toWeightedCLM (ν := ν) M x = 0 := by
    ext i
    simpa [toWeightedCLM_apply, Matrix.mulVec, x, ScaledReal.toReal]
      using congrFun hv_mulVec i
  rw [← map_zero (toWeightedCLM (ν := ν) M)] at hx_zero
  exact hx_ne (h_inj hx_zero)

/-- Neumann criterion for weighted finite matrices. -/
lemma matrix_invertible_of_norm_lt_one {ν : PosReal} {N : ℕ}
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (h : l1Weighted.finWeightedMatrixNorm ν (1 - M) < 1) :
    IsUnit M := by
  rw [finWeightedMatrixNorm_eq_opNorm, toWeightedCLM_one_sub] at h
  exact matrix_isUnit_of_toWeightedCLM_isUnit M (isUnit_of_norm_sub_id_lt_one (E := FinWeighted.Space ν N) h)

end FinWeightedMatrix

end SystemTaylorODE


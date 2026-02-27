import RadiiPolynomial.Example77.Algebra
import RadiiPolynomial.SystemTaylorODE.WitnessSpec
import RadiiPolynomial.SystemTaylorODE.LeanCertEval

/-!
# Example 7.7 — Certificate

Concrete numerical data and verified bound proofs for
the parameterized equilibrium `x² - λ = 0` with `λ₀ = 1/3`.

## Contents

1. Numerical parameters (ā, A_mat, ν, r₀)
2. ScalarBlockDiagData instances
3. Numerical bounds (Y₀, Z₀, Z₁, Z₂, radii polynomial, injectivity)
4. Main theorem assembly — zero sorry's
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap SystemTaylorODE Example77

noncomputable section

namespace Example77.Cert

/-! ## 1. Numerical Parameters -/

def ā₀_q : ℚ := 5774/10000
def ā₁_q : ℚ := 8660/10000
def ā₂_q : ℚ := -6495/10000

noncomputable def ā₀ : ℝ := (ā₀_q : ℝ)
noncomputable def ā₁ : ℝ := (ā₁_q : ℝ)
noncomputable def ā₂ : ℝ := (ā₂_q : ℝ)

noncomputable def lam0 : ℝ := 1/3
noncomputable def ν_val : PosReal := ⟨1/4, by norm_num⟩
noncomputable def r₀ : ℝ := 996/10000

lemma r₀_pos : 0 < r₀ := by unfold r₀; norm_num

noncomputable def sol : ApproxSolution 2 where
  aBar_fin := ![ā₀, ā₁, ā₂]
  aBar_zero_ne := by unfold ā₀ ā₀_q; norm_num

/-! ## 2. A_mat: user-provided approximate inverse of DF^(N)(ā)

A^(N) is a numerically computed approximate inverse (e.g., from Julia/MATLAB).
It does NOT need to be the exact inverse — only close enough for p(r₀) < 0. -/

def A_diag_q : ℚ := 8660/10000
def A_sub1_q : ℚ := -12990/10000
def A_sub2_q : ℚ := 29240/10000

def A_col0_q : Array ℚ := #[A_diag_q, A_sub1_q, A_sub2_q]
def A_col1_q : Array ℚ := #[0, A_diag_q, A_sub1_q]
def A_col2_q : Array ℚ := #[0, 0, A_diag_q]

def A_colOf_q : Fin 3 → Array ℚ
  | 0 => A_col0_q
  | 1 => A_col1_q
  | 2 => A_col2_q

noncomputable def A_mat : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ((A_colOf_q j).getD (i : ℕ) 0 : ℝ)

/-! ## 3. ScalarBlockDiagData instances -/

noncomputable def A_data : ScalarBlockDiagData 2 :=
  approxInverse sol A_mat

noncomputable def A_dagger_data : ScalarBlockDiagData 2 :=
  approxDeriv sol

/-! ## 4. Bound constants -/

def Y₀_bnd : ℚ := 9/500
def Z₀_bnd : ℚ := 2/1000
def Z₁_bnd : ℚ := 46/100
def Z₂_bnd : ℚ := 28/10

/-! ## 5. Numerical Bounds

Each bound reduces to a `finsum_bound` or `fast_bound` call.
The structural reductions are in Algebra.lean; here we only
supply the numerical values and discharge the inequalities. -/

private lemma ν_val_eq_q : (ν_val : ℝ) = ((1/4 : ℚ) : ℝ) := by
  simp [ν_val]

/-- Bridge for A columns: finBlock0 entries match A_colOf_q. -/
private lemma A_col_bridge (j i : Fin 3) :
    (approxInverse sol A_mat).finBlock0 i j = ((A_colOf_q j).getD (i : ℕ) 0 : ℝ) := by
  simp [approxInverse, ScalarBlockDiagData.ofParts,
    ScalarBlockDiagData.finBlock0, A_mat]

/-! ### Y₀: ‖A · F(ā)‖ ≤ Y₀_bnd -/

private lemma F_ā_support : ∀ n, 4 < n →
    lpWeighted.toSeq (F lam0 (sol.toL1 : l1Weighted ν_val)) n = 0 := by
  intro n hn
  show lpWeighted.toSeq (sq (sol.toL1 : l1Weighted ν_val) - c lam0) n = 0
  rw [lpWeighted.sub_toSeq]
  have hā : ∀ k, 2 < k → lpWeighted.toSeq (sol.toL1 : l1Weighted ν_val) k = 0 :=
    fun k hk => by rw [ApproxSolution.toL1_toSeq]; exact sol.toSeq_zero_of_gt k hk
  have h_sq : lpWeighted.toSeq (sq (sol.toL1 : l1Weighted ν_val)) n = 0 :=
    CauchyProduct.zero_of_support hā hā n (by omega)
  have h_c : lpWeighted.toSeq (c lam0 : l1Weighted ν_val) n = 0 := by
    simp only [c, lpWeighted.mk, paramSeq]; match n, hn with | n + 5, _ => rfl
  rw [h_sq, h_c, sub_self]

private lemma AF_ā_support : ∀ n, 4 < n →
    lpWeighted.toSeq (A_data.toScalarCLM (ν := ν_val)
      (F lam0 (sol.toL1 : l1Weighted ν_val))) n = 0 :=
  ScalarBlockDiagData.toScalarCLM_support A_data _ 4 (by omega) F_ā_support

/-- F(ā) coefficients in ℚ: Cauchy product of ā with itself minus c(λ₀). -/
private def F_ā_vec (n : ℕ) : ℚ :=
  CauchyProduct (fun k => (#[ā₀_q, ā₁_q, ā₂_q] : Array ℚ).getD k 0)
                (fun k => (#[ā₀_q, ā₁_q, ā₂_q] : Array ℚ).getD k 0) n -
  (#[1/3, 1] : Array ℚ).getD n 0

private def A_tail_coeff : ℚ := 1 / (2 * ā₀_q)

/-- Bridge: toSeq(sol) matches ℚ array. -/
private lemma sol_toSeq_eq (k : ℕ) :
    ApproxSolution.toSeq sol k = ((#[ā₀_q, ā₁_q, ā₂_q] : Array ℚ).getD k 0 : ℝ) := by
  simp only [ApproxSolution.toSeq, sol, ā₀, ā₁, ā₂, ā₀_q, ā₁_q, ā₂_q]
  match k with
  | 0 => simp [Array.getD]
  | 1 => simp [Array.getD]
  | 2 => simp [Array.getD]
  | k + 3 => simp [Array.getD, show ¬(k + 3 ≤ 2) from by omega]

/-- Bridge: toSeq(F(ā)) matches F_ā_vec. -/
private lemma F_ā_toSeq_eq (n : ℕ) :
    lpWeighted.toSeq (F lam0 (sol.toL1 : l1Weighted ν_val)) n = (F_ā_vec n : ℝ) := by
  rw [F_toSeq, ApproxSolution.toL1_toSeq]
  simp only [F_ā_vec, CauchyProduct.apply, lam0]
  simp_rw [sol_toSeq_eq]; push_cast
  match n with
  | 0 => simp [paramSeq, Array.getD]
  | 1 => simp [paramSeq, Array.getD]
  | _ + 2 => simp [paramSeq, Array.getD, show ¬(_ + 2 < 2) from by omega]

/-- Bridge: A tailDiag matches tail coefficient. -/
private lemma A_tailDiag_eq (n : ℕ) :
    A_data.tailDiag0 n = (A_tail_coeff : ℝ) := by
  simp [A_data, approxInverse, ScalarBlockDiagData.ofParts, ScalarBlockDiagData.tailDiag0,
    A_tail_coeff, sol, ā₀, ā₀_q]

/-- Y₀ witness evaluator. -/
private def Y₀_eval := scalarBlockDiagActionEval A_colOf_q F_ā_vec A_tail_coeff (1/4)

lemma Y₀_le : ‖A_data.toScalarCLM (ν := ν_val)
    (F lam0 (sol.toL1 : l1Weighted ν_val))‖ ≤ (Y₀_bnd : ℝ) := by
  rw [l1Weighted.norm_eq_Icc_sum_of_support _ 4 AF_ā_support]
  simp_rw [ScalarBlockDiagData.toScalarCLM_toSeq_eq_action A_data _
    A_colOf_q F_ā_vec A_tail_coeff A_col_bridge F_ā_toSeq_eq
    (fun n hn => A_tailDiag_eq n), ν_val_eq_q]
  rw [show (Y₀_bnd : ℝ) = (9 : ℝ) / 500 from by norm_num [Y₀_bnd]]
  finsum_bound using Y₀_eval
    (fun k _ _ => scalarBlockDiagActionEval_correct A_colOf_q F_ā_vec A_tail_coeff (1/4) k {})

/-! ### Z₀: ‖I - A ∘ A†‖ ≤ Z₀_bnd -/

open SystemTaylorODE in
/-- ℚ column arrays for DF^(N)(ā). -/
private def DF_colOf_q : Fin 3 → Array ℚ
  | 0 => #[2 * ā₀_q, 2 * ā₁_q, 2 * ā₂_q]
  | 1 => #[0, 2 * ā₀_q, 2 * ā₁_q]
  | 2 => #[0, 0, 2 * ā₀_q]

/-- Bridge for DF columns: finBlock0 entries match DF_colOf_q. -/
private lemma DF_col_bridge (j i : Fin 3) :
    (approxDeriv sol).finBlock0 i j = ((DF_colOf_q j).getD (i : ℕ) 0 : ℝ) := by
  simp [approxDeriv, ScalarBlockDiagData.ofParts, ScalarBlockDiagData.finBlock0,
    dfFin, sol, DF_colOf_q, ā₀, ā₁, ā₂, ā₀_q, ā₁_q, ā₂_q]
  fin_cases i <;> fin_cases j <;> simp

/-- Defect column arrays computed from A and DF columns via `defectMatQ`. -/
private def defect_cols : Fin 3 → Array ℚ := fun j =>
  #[defectMatQ A_colOf_q DF_colOf_q 0 j,
    defectMatQ A_colOf_q DF_colOf_q 1 j,
    defectMatQ A_colOf_q DF_colOf_q 2 j]

/-- Bridge: defect matrix entries match `defect_cols` via `defectMatQ_correct`. -/
private lemma defect_cols_bridge (j i : Fin 3) :
    (1 - (approxInverse sol A_mat).finBlock0 * (approxDeriv sol).finBlock0) i j =
    ((defect_cols j).getD (i : ℕ) 0 : ℝ) := by
  rw [defectMatQ_correct _ _ A_colOf_q DF_colOf_q A_col_bridge DF_col_bridge i j]
  fin_cases i <;> fin_cases j <;> simp [defect_cols]

/-- Shared: defect matrix norm ≤ 2/1000, used by both Z₀_le and A_injective. -/
private lemma defect_matrixNorm_le :
    l1Weighted.finWeightedMatrixNorm ν_val
      (1 - (approxInverse sol A_mat).finBlock0 * (approxDeriv sol).finBlock0) ≤
    (2 : ℝ) / 1000 := by
  exact l1Weighted.finWeightedMatrixNorm_le_via_cols _ defect_cols _
    defect_cols_bridge (fun j => by
      unfold l1Weighted.arrayColNormIccSum; rw [ν_val_eq_q]
      fin_cases j <;>
        finsum_bound using
          (colNormTermEval _ (1/4) _)
          (fun k _ _ => colNormTermEval_correct _ (1/4) _ k _))

lemma Z₀_le : ‖ContinuousLinearMap.id ℝ (l1Weighted ν_val) -
    (A_data.toScalarCLM (ν := ν_val)).comp
      (A_dagger_data.toScalarCLM (ν := ν_val))‖ ≤ (Z₀_bnd : ℝ) :=
  ((ScalarBlockDiagData.Z₀_le_finWeightedMatrixNorm_of_tailCancel (ν := ν_val) _ _
    (tailCancel sol A_mat)).trans defect_matrixNorm_le).trans (by norm_num [Z₀_bnd])

/-! ### Z₁: ‖A ∘ (A† - DF(ā))‖ ≤ Z₁_bnd -/

lemma Z₁_le : ‖(A_data.toScalarCLM (ν := ν_val)).comp
    ((A_dagger_data.toScalarCLM (ν := ν_val)) -
      fderiv ℝ (F lam0) (sol.toL1 : l1Weighted ν_val))‖ ≤ (Z₁_bnd : ℝ) := by
  -- Pre-compute the shifted norm sum as a ℚ witness
  have h_shifted_sum :
      ∑ m ∈ Finset.Icc 1 2, |sol.toSeq m| * (ν_val : ℝ) ^ m =
      ↑((8660 : ℚ) / 40000 + 6495 / 160000) := by
    simp only [show Finset.Icc 1 2 = {1, 2} from by decide,
      Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)]
    simp only [ApproxSolution.toSeq, sol, ā₀, ā₁, ā₂, ā₀_q, ā₁_q, ā₂_q]
    simp only [ν_val]; push_cast; norm_num
  exact Z₁_le_via_eval sol A_mat lam0 Z₁_bnd
    (of_point_interval (by
      rw [h_shifted_sum]
      unfold approxInverse ScalarBlockDiagData.ofParts sol ā₀ ā₀_q Z₁_bnd
      fast_bound))

/-! ### Z₂: ‖A ∘ (DF(c) - DF(ā))‖ ≤ Z₂_bnd * r₀ for c ∈ ball -/

private lemma A_finWeightedMatrixNorm_le :
    l1Weighted.finWeightedMatrixNorm ν_val A_data.finBlock0 ≤ (Z₂_bnd / 2 : ℝ) :=
  l1Weighted.finWeightedMatrixNorm_le_via_cols _ A_colOf_q _
    A_col_bridge (fun j => by
      unfold l1Weighted.arrayColNormIccSum; rw [ν_val_eq_q]
      rw [show (Z₂_bnd : ℝ) / 2 = (14 : ℝ) / 10 from by norm_num [Z₂_bnd]]
      fin_cases j <;>
        finsum_bound using
          (colNormTermEval _ (1/4) _)
          (fun k _ _ => colNormTermEval_correct _ (1/4) _ k _))

private lemma A_tailBound_le :
    (approxInverse sol A_mat).tailBound ≤ (Z₂_bnd / 2 : ℝ) := by
  unfold approxInverse ScalarBlockDiagData.ofParts
  exact of_point_interval (by
    simp only [Z₂_bnd]; unfold sol ā₀ ā₀_q; fast_bound)

lemma A_norm_le : 2 * ‖A_data.toScalarCLM (ν := ν_val)‖ ≤ (Z₂_bnd : ℝ) :=
  (mul_le_mul_of_nonneg_left
    ((ScalarBlockDiagData.norm_toScalarCLM_le_max (ν := ν_val) A_data).trans
      (max_le A_finWeightedMatrixNorm_le A_tailBound_le))
    (by positivity)).trans
  (of_point_interval (by unfold Z₂_bnd; push_cast; fast_bound))

lemma Z₂_le (c_val : l1Weighted ν_val)
    (hc : c_val ∈ Metric.closedBall (sol.toL1 : l1Weighted ν_val) r₀) :
    ‖(A_data.toScalarCLM (ν := ν_val)).comp
      (fderiv ℝ (F lam0) c_val -
        fderiv ℝ (F lam0) (sol.toL1 : l1Weighted ν_val))‖ ≤
    (Z₂_bnd : ℝ) * r₀ :=
  Z₂_ball_bound sol A_mat lam0 r₀ (Z₂_bnd : ℝ) A_norm_le c_val hc

/-! ### Radii polynomial negativity -/

private lemma radii_neg_icc :
    ∀ r ∈ Set.Icc r₀ r₀,
    generalRadiiPolynomial (Y₀_bnd : ℝ) (Z₀_bnd : ℝ) (Z₁_bnd : ℝ)
      (fun _ => (Z₂_bnd : ℝ)) r < 0 := by
  unfold generalRadiiPolynomial r₀ Y₀_bnd Z₀_bnd Z₁_bnd Z₂_bnd
  simp only [Rat.cast_div, Rat.cast_ofNat]
  fast_bound

lemma radii_neg :
    generalRadiiPolynomial (Y₀_bnd : ℝ) (Z₀_bnd : ℝ) (Z₁_bnd : ℝ)
      (fun _ => (Z₂_bnd : ℝ)) r₀ < 0 :=
  radii_neg_icc r₀ ⟨le_refl _, le_refl _⟩

/-! ### Injectivity -/

lemma A_injective :
    Function.Injective (A_data.toScalarCLM (ν := ν_val)) :=
  ScalarBlockDiagData.injective_toScalarCLM_of_finBlock_mul_close_to_one
    (approxInverse sol A_mat) (approxDeriv sol).finBlock0
    (defect_matrixNorm_le.trans_lt (by norm_num))
    (approxInverse_tailDiag_ne_zero sol A_mat)

/-! ## 6. Main Theorem -/

theorem main_theorem :
    ∃! xTilde ∈ Metric.closedBall (sol.toL1 : l1Weighted ν_val) r₀,
      F lam0 xTilde = 0 :=
  existsUnique sol A_mat lam0 r₀_pos Y₀_le Z₀_le Z₁_le
    (fun c hc => Z₂_le c hc) radii_neg A_injective

end Example77.Cert

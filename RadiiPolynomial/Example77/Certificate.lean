import RadiiPolynomial.Example77.Algebra
import RadiiPolynomial.SystemTaylorODE.WitnessSpec
import RadiiPolynomial.SystemTaylorODE.LeanCertEval

/-!
# Example 7.7 — Certificate

Computer-assisted proof for `x² - λ = 0`.
To switch parameters: comment/uncomment the numerical input blocks below.
All proof code below is **identical** regardless of which parameter set is active.

All parameter defs are ℚ. Lean auto-coerces ℚ → ℝ wherever ℝ is expected.
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap SystemTaylorODE Example77

noncomputable section

namespace Example77.Cert

/-! ## Numerical Input — swap this block to change parameters -/

-- Parameter set 1: λ₀ = 1/3
def ā₀ : ℚ := 5774/10000
def ā₁ : ℚ := 8660/10000
def ā₂ : ℚ := -6495/10000
def lam0 : ℚ := 1/3
def ν : ℚ := 1/4
def r₀ : ℚ := 996/10000
def A_diag : ℚ := 8660/10000
def A_sub1 : ℚ := -12990/10000
def A_sub2 : ℚ := 29240/10000
def Y₀_bnd : ℚ := 9/500
def Z₀_bnd : ℚ := 2/1000
def Z₁_bnd : ℚ := 46/100
def Z₂_bnd : ℚ := 28/10

-- Parameter set 2: λ₀ = 1/2
-- def ā₀ : ℚ := 7071/10000
-- def ā₁ : ℚ := 7071/10000
-- def ā₂ : ℚ := -3536/10000
-- def lam0 : ℚ := 1/2
-- def ν : ℚ := 1/4
-- def r₀ : ℚ := 5/100
-- def A_diag : ℚ := 7071/10000
-- def A_sub1 : ℚ := -7071/10000
-- def A_sub2 : ℚ := 10607/10000
-- def Y₀_bnd : ℚ := 7/1000
-- def Z₀_bnd : ℚ := 1/1000
-- def Z₁_bnd : ℚ := 3/10
-- def Z₂_bnd : ℚ := 2


/-! ## Derived Definitions — identical for any input -/

noncomputable def ν_val : PosReal := ⟨ν, by unfold ν; norm_num⟩

lemma r₀_pos : 0 < (r₀ : ℝ) := by unfold r₀; norm_num

noncomputable def sol : ApproxSolution 2 where
  aBar_fin := ![ā₀, ā₁, ā₂]
  aBar_zero_ne := by unfold ā₀; norm_num

def A_col0 : Array ℚ := #[A_diag, A_sub1, A_sub2]
def A_col1 : Array ℚ := #[0, A_diag, A_sub1]
def A_col2 : Array ℚ := #[0, 0, A_diag]

def A_colOf : Fin 3 → Array ℚ
  | 0 => A_col0
  | 1 => A_col1
  | 2 => A_col2

noncomputable def A_mat : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ((A_colOf j).getD (i : ℕ) 0 : ℝ)

noncomputable def A_inv : ScalarBlockDiagData 2 :=
  approxInverse sol A_mat

noncomputable def A_dag : ScalarBlockDiagData 2 :=
  approxDeriv sol

/-! ## ℚ data for evaluators -/

private def F_ā_vec (n : ℕ) : ℚ :=
  CauchyProduct (fun k => (#[ā₀, ā₁, ā₂] : Array ℚ).getD k 0)
                (fun k => (#[ā₀, ā₁, ā₂] : Array ℚ).getD k 0) n -
  (#[lam0, 1] : Array ℚ).getD n 0

private def A_tail_coeff : ℚ := 1 / (2 * ā₀)

/-! ## Bridge Lemmas -/

private lemma ν_val_eq_q : (ν_val : ℝ) = ((ν : ℚ) : ℝ) := by
  simp [ν_val]

private def A_colR : Fin 3 → Array ℝ :=
  fun j => (A_colOf j).map (fun (x : ℚ) => (x : ℝ))
private def F_ā_R : ℕ → ℝ := fun n => (F_ā_vec n : ℝ)
private def A_tail_R : ℝ := (A_tail_coeff : ℝ)

-- ℚ-cast bridge (for Z₀/matrix norm/defect pipelines)
private lemma A_col_bridge_q (j i : Fin 3) :
    (approxInverse sol A_mat).finBlock0 i j = ((A_colOf j).getD (i : ℕ) 0 : ℝ) := by
  simp [approxInverse, ScalarBlockDiagData.ofParts,
    ScalarBlockDiagData.finBlock0, A_mat]

-- Array.map bridge: A_colR getD = ℚ cast
private lemma A_colR_eq (j : Fin 3) (i : ℕ) :
    (A_colR j).getD i 0 = ((A_colOf j).getD i 0 : ℝ) := by
  simp [A_colR, Array.getD, Array.size_map]
  split <;> simp

-- ℝ-array bridge (for toScalarCLM_toSeq_eq_action / Y₀)
private lemma A_col_bridge (j i : Fin 3) :
    (approxInverse sol A_mat).finBlock0 i j = (A_colR j).getD (i : ℕ) 0 :=
  (A_col_bridge_q j i).trans (A_colR_eq j i).symm

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
    lpWeighted.toSeq (A_inv.toScalarCLM (ν := ν_val)
      (F lam0 (sol.toL1 : l1Weighted ν_val))) n = 0 :=
  ScalarBlockDiagData.toScalarCLM_support A_inv _ 4 (by omega) F_ā_support

private lemma sol_toSeq_eq (k : ℕ) :
    ApproxSolution.toSeq sol k = ((#[ā₀, ā₁, ā₂] : Array ℚ).getD k 0 : ℝ) := by
  simp only [ApproxSolution.toSeq, sol, ā₀, ā₁, ā₂]
  match k with
  | 0 => simp [Array.getD]
  | 1 => simp [Array.getD]
  | 2 => simp [Array.getD]
  | k + 3 => simp [Array.getD, show ¬(k + 3 ≤ 2) from by omega]

private lemma F_ā_toSeq_eq (n : ℕ) :
    lpWeighted.toSeq (F lam0 (sol.toL1 : l1Weighted ν_val)) n = F_ā_R n := by
  unfold F_ā_R
  rw [F_toSeq, ApproxSolution.toL1_toSeq]
  simp only [F_ā_vec, CauchyProduct.apply, lam0]
  simp_rw [sol_toSeq_eq]; push_cast
  match n with
  | 0 => simp [paramSeq, Array.getD]
  | 1 => simp [paramSeq, Array.getD]
  | _ + 2 => simp [paramSeq, Array.getD, show ¬(_ + 2 < 2) from by omega]

private lemma A_tailDiag_eq (n : ℕ) :
    A_inv.tailDiag0 n = A_tail_R := by
  unfold A_tail_R
  simp [A_inv, approxInverse, ScalarBlockDiagData.ofParts, ScalarBlockDiagData.tailDiag0,
    A_tail_coeff, sol, ā₀]

/-! ## Bound Proofs — finsum_bound / fast_bound discharge all numerical steps -/

/-! ### Y₀ -/

private def Y₀_eval := scalarBlockDiagActionEval A_colOf F_ā_vec A_tail_coeff ν

lemma Y₀_le : Y₀_norm (F lam0) sol.toL1
    (A_inv.toScalarCLM (ν := ν_val)) ≤ (Y₀_bnd : ℝ) := by
  show ‖A_inv.toScalarCLM (ν := ν_val)
    (F lam0 (sol.toL1 : l1Weighted ν_val))‖ ≤ _
  rw [l1Weighted.norm_eq_Icc_sum_of_support _ 4 AF_ā_support]
  simp_rw [ScalarBlockDiagData.toScalarCLM_toSeq_eq_action A_inv _
    A_colR F_ā_R A_tail_R A_col_bridge F_ā_toSeq_eq
    (fun n hn => A_tailDiag_eq n), ν_val_eq_q]
  unfold Y₀_bnd
  finsum_bound using Y₀_eval
    (fun k _ _ => scalarBlockDiagActionEval_correct A_colR F_ā_R A_tail_R _
      A_colOf F_ā_vec A_tail_coeff ν
      (fun j i => A_colR_eq j i)
      (fun n => rfl) rfl rfl k {})

/-! ### Z₀ -/

open SystemTaylorODE in
private def DF_colOf : Fin 3 → Array ℚ
  | 0 => #[2 * ā₀, 2 * ā₁, 2 * ā₂]
  | 1 => #[0, 2 * ā₀, 2 * ā₁]
  | 2 => #[0, 0, 2 * ā₀]

private lemma DF_col_bridge (j i : Fin 3) :
    (approxDeriv sol).finBlock0 i j = ((DF_colOf j).getD (i : ℕ) 0 : ℝ) := by
  simp [approxDeriv, ScalarBlockDiagData.ofParts, ScalarBlockDiagData.finBlock0,
    dfFin, sol, DF_colOf, ā₀, ā₁, ā₂]
  fin_cases i <;> fin_cases j <;> simp

private def defect_cols : Fin 3 → Array ℚ := fun j =>
  #[defectMatQ A_colOf DF_colOf 0 j,
    defectMatQ A_colOf DF_colOf 1 j,
    defectMatQ A_colOf DF_colOf 2 j]

private lemma defect_cols_bridge (j i : Fin 3) :
    (1 - (approxInverse sol A_mat).finBlock0 * (approxDeriv sol).finBlock0) i j =
    ((defect_cols j).getD (i : ℕ) 0 : ℝ) := by
  rw [defectMatQ_correct _ _ A_colOf DF_colOf A_col_bridge_q DF_col_bridge i j]
  fin_cases i <;> fin_cases j <;> simp [defect_cols]

private lemma defect_matrixNorm_le :
    l1Weighted.finWeightedMatrixNorm ν_val
      (1 - (approxInverse sol A_mat).finBlock0 * (approxDeriv sol).finBlock0) ≤
    (Z₀_bnd : ℝ) := by
  unfold Z₀_bnd
  exact l1Weighted.finWeightedMatrixNorm_le_via_cols _ defect_cols _
    defect_cols_bridge (fun j => by
      unfold l1Weighted.arrayColNormIccSum; rw [ν_val_eq_q]
      fin_cases j <;>
        finsum_bound using
          (colNormTermEval _ ν _)
          (fun k _ _ => colNormTermEval_correct _ ν _ k _))

lemma Z₀_le : Z₀_norm (A_inv.toScalarCLM (ν := ν_val))
    (A_dag.toScalarCLM (ν := ν_val)) ≤ (Z₀_bnd : ℝ) :=
  (ScalarBlockDiagData.Z₀_le_finWeightedMatrixNorm_of_tailCancel (ν := ν_val) _ _
    (tailCancel sol A_mat)).trans defect_matrixNorm_le

/-! ### Z₁ -/

lemma Z₁_le : Z₁_norm (F lam0) sol.toL1
    (A_inv.toScalarCLM (ν := ν_val))
    (A_dag.toScalarCLM (ν := ν_val)) ≤ (Z₁_bnd : ℝ) := by
  show ‖(A_inv.toScalarCLM (ν := ν_val)).comp
    ((A_dag.toScalarCLM (ν := ν_val)) -
      fderiv ℝ (F lam0) (sol.toL1 : l1Weighted ν_val))‖ ≤ _
  have h_shifted_sum :
      ∑ m ∈ Finset.Icc 1 2, |sol.toSeq m| * (ν_val : ℝ) ^ m =
      ((ā₁ * (1/4) + (-ā₂) * (1/4)^2 : ℚ) : ℝ) := by
    simp only [show Finset.Icc 1 2 = {1, 2} from by decide,
      Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)]
    simp only [ApproxSolution.toSeq, sol, ā₀, ā₁, ā₂]
    simp only [ν_val, ν]; push_cast; norm_num
  exact Z₁_le_via_eval sol A_mat lam0 (Z₁_bnd : ℝ)
    (of_point_interval (by
      rw [h_shifted_sum]
      unfold approxInverse ScalarBlockDiagData.ofParts sol ā₀ ā₁ ā₂ Z₁_bnd
      fast_bound))

/-! ### Z₂ -/

private lemma A_finWeightedMatrixNorm_le :
    l1Weighted.finWeightedMatrixNorm ν_val A_inv.finBlock0 ≤ (Z₂_bnd : ℝ) / 2 := by
  unfold Z₂_bnd
  exact l1Weighted.finWeightedMatrixNorm_le_via_cols _ A_colOf _
    A_col_bridge_q (fun j => by
      unfold l1Weighted.arrayColNormIccSum; rw [ν_val_eq_q]
      fin_cases j <;>
        finsum_bound using
          (colNormTermEval _ ν _)
          (fun k _ _ => colNormTermEval_correct _ ν _ k _))

private lemma A_tailBound_le :
    (approxInverse sol A_mat).tailBound ≤ (Z₂_bnd : ℝ) / 2 := by
  unfold approxInverse ScalarBlockDiagData.ofParts Z₂_bnd
  exact of_point_interval (by unfold sol ā₀; fast_bound)

lemma A_norm_le : 2 * ‖A_inv.toScalarCLM (ν := ν_val)‖ ≤ (Z₂_bnd : ℝ) :=
  (mul_le_mul_of_nonneg_left
    ((ScalarBlockDiagData.norm_toScalarCLM_le_max (ν := ν_val) A_inv).trans
      (max_le A_finWeightedMatrixNorm_le A_tailBound_le))
    (by positivity)).trans
  (of_point_interval (by unfold Z₂_bnd; push_cast; fast_bound))

lemma Z₂_le (c_val : l1Weighted ν_val)
    (hc : c_val ∈ Metric.closedBall (sol.toL1 : l1Weighted ν_val) r₀) :
    Z₂_norm (F lam0) sol.toL1 (A_inv.toScalarCLM (ν := ν_val)) c_val ≤
    (Z₂_bnd : ℝ) * r₀ :=
  Z₂_ball_bound sol A_mat lam0 r₀ (Z₂_bnd : ℝ) A_norm_le c_val hc

/-! ### Radii polynomial negativity -/

private lemma radii_neg_icc :
    ∀ r ∈ Set.Icc (r₀ : ℝ) (r₀ : ℝ),
    generalRadiiPolynomial (Y₀_bnd : ℝ) (Z₀_bnd : ℝ) (Z₁_bnd : ℝ)
      (fun _ => (Z₂_bnd : ℝ)) r < 0 := by
  unfold generalRadiiPolynomial r₀ Y₀_bnd Z₀_bnd Z₁_bnd Z₂_bnd
  fast_bound

lemma radii_neg :
    generalRadiiPolynomial (Y₀_bnd : ℝ) (Z₀_bnd : ℝ) (Z₁_bnd : ℝ)
      (fun _ => (Z₂_bnd : ℝ)) (r₀ : ℝ) < 0 :=
  radii_neg_icc (r₀ : ℝ) ⟨le_refl _, le_refl _⟩

/-! ### Injectivity -/

lemma A_injective :
    Function.Injective (A_inv.toScalarCLM (ν := ν_val)) :=
  ScalarBlockDiagData.injective_toScalarCLM_of_finBlock_mul_close_to_one
    (approxInverse sol A_mat) (approxDeriv sol).finBlock0
    (defect_matrixNorm_le.trans_lt (by unfold Z₀_bnd; norm_num))
    (approxInverse_tailDiag_ne_zero sol A_mat)

/-! ## Main Theorem -/

theorem main_theorem :
    ∃! xTilde ∈ Metric.closedBall (sol.toL1 : l1Weighted ν_val) r₀,
      F lam0 xTilde = 0 :=
  existsUnique sol A_mat lam0 r₀_pos Y₀_le Z₀_le Z₁_le
    (fun c hc => Z₂_le c hc) radii_neg A_injective

end Example77.Cert

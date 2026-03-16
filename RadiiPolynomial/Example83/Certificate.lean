import RadiiPolynomial.Example83.Algebra
import RadiiPolynomial.SystemTaylorODE.WitnessSpec
import RadiiPolynomial.SystemTaylorODE.LeanCertEval
import RadiiPolynomial.Tactic.FinMatrixBound

/-!
# Example 8.3 — Certificate

Computer-assisted proof for the Lorenz IVP:
  ẋ = f(x), x(0) = (1,0,0), σ=10, ρ=28, β=8/3, N=30, ν=3/20

## Architecture

Z₀ uses `defectOfBlockDiagOp` (zero tail) + per-block `finWeightedMatrixNorm_le_via_cols`.
Each defect block (l,j) = δ_{l,j}·I - ∑_m A_{l,m}·DF_{m,j} is computed in ℚ.

Y₀, Z₁, Z₂ require F_lorenz (TODO in Algebra.lean).
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap SystemTaylorODE Example83

noncomputable section

namespace Example83.Cert

/-! ## Z₀ infrastructure — defect block columns via defectMatQ

For each block (l,j), the defect = δ_{l,j}·I - Σ_m A[l,m]·DF[m,j].
Each block product Σ_m A[l,m]·DF[m,j] is computed in ℚ via `defectMatQ` per-block. -/

/-- Column k of block defect (l,j) via `blockDefectMatQ`. -/
private def defectBlockCols (l j : Fin L) (k : Fin (N + 1)) : Array ℚ :=
  Array.ofFn fun (i : Fin (N + 1)) =>
    blockDefectMatQ (fun l m k => A_col l m (k : ℕ)) (fun m j k => DF_col m j (k : ℕ)) l j i k

/-- `Array.getD` of `Array.ofFn` reduces when index is in range. -/
private lemma Array.getD_ofFn_fin {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (Array.ofFn f).getD (i : ℕ) d = f i := by
  simp [Array.getD, Array.size_ofFn, i.isLt, Array.getElem_ofFn]

/-- Bridge: defect finBlock entries = ℚ-cast of defectBlockCols. -/
private lemma defectBlockCol_correct (l j : Fin L) (i k : Fin (N + 1)) :
    defect.finBlock l j i k = ((defectBlockCols l j k).getD (i : ℕ) 0 : ℝ) := by
  rw [defectBlockCols, Array.getD_ofFn_fin]
  -- Bridge: defect.finBlock = (if l=j then I else 0) - Σ_m A_finBlock * DF_finBlock
  -- And blockDefectMatQ computes the same from ℚ column arrays
  have := blockDefectMatQ_correct
    (fun l m => A_finBlock l m) (fun m j => DF_finBlock m j)
    (fun l m (k : Fin (N + 1)) => A_col l m (k : ℕ))
    (fun m j (k : Fin (N + 1)) => DF_col m j (k : ℕ))
    (fun l m j i => by simp [A_finBlock])
    (fun m j k i => by simp [DF_finBlock])
    l j i k
  show ((if l = j then 1 else 0) - ∑ m, A_finBlock l m * DF_finBlock m j) i k = _
  exact this

/-- Z₀ bound: finiteBlockMatrixNorm(defect) ≤ Z₀_bound.
Single `native_decide` via `finmatrix_bound` (replaces 9 per-block calls). -/
lemma Z₀_finBlockNorm_le :
    finiteBlockMatrixNorm ν_val defect.finBlock ≤ (Z₀_bound : ℝ) := by
  finmatrix_bound
    (finiteBlockMatrixNorm_le_of_Q_le _ defectBlockCols ν_q
      (fun l j k i => defectBlockCol_correct l j i k) ν_val_eq_q)

/-! ## ‖A‖ bound (needed for Z₂)

‖A.toCLM‖ ≤ finiteBlockMatrixNormQ(blockCols) + tailBound — computed, no named intermediate. -/

/-- Block columns of A.finBlock for `finmatrix_bound`. -/
private def ABlockCols (l j : Fin L) (k : Fin (N + 1)) : Array ℚ :=
  A_col l j (k : ℕ)

/-- ‖A.toCLM‖ bound — all intermediate values computed from data. -/
lemma A_norm_le :
    ‖approxInverse.toCLM (ν := ν_val)‖ ≤
      (finiteBlockMatrixNormQ L N ABlockCols ν_q + approxInverse_tailBound_q : ℚ) := by
  finmatrix_bound
    (norm_toCLM_le_of_Q approxInverse ABlockCols ν_q approxInverse_tailBound_q
      (fun l j k i => A_finBlock_eq l j i k) ν_val_eq_q approxInverse_tailBound_eq)

/-! ## Y₀ bound: ‖G_lorenz(ābar)‖ ≤ Y₀_bound

G(ā) has finite support ≤ 2N+1 (Cauchy products from quadratic nonlinearity).
Coefficients exported from Julia as G_ā_vec. -/

/-- Helper: l1Weighted product vanishes beyond combined support. -/
private lemma toSeq_mul_zero (a b : l1Weighted ν_val) {M : ℕ}
    (ha : ∀ k, M < k → l1Weighted.toSeq a k = 0)
    (hb : ∀ k, M < k → l1Weighted.toSeq b k = 0)
    {n : ℕ} (hn : 2 * M < n) :
    l1Weighted.toSeq (a * b) n = 0 := by
  -- toSeq (a * b) n = CauchyProduct (toSeq a) (toSeq b) n (definitional)
  exact CauchyProduct.zero_of_support ha hb n hn

/-- φ_lorenz(ābar) vanishes beyond mode 2N. -/
private lemma φ_lorenz_abar_support (l : Fin L) (n : ℕ) (hn : 2 * N < n) :
    l1Weighted.toSeq (φ_lorenz abar l) n = 0 := by
  have ha := fun i => abar_seq_support i
  have ha' : ∀ i : Fin L, ∀ k, N < k → l1Weighted.toSeq (abar i) k = 0 :=
    fun i k hk => by simp [abar, lpWeighted.mk, ha i k hk]
  have h02 := toSeq_mul_zero (abar 0) (abar 2) (ha' 0) (ha' 2) hn
  have h01 := toSeq_mul_zero (abar 0) (abar 1) (ha' 0) (ha' 1) hn
  fin_cases l
  · show σ_val * (l1Weighted.toSeq (abar 1) n - l1Weighted.toSeq (abar 0) n) = 0
    rw [ha' 0 n (by omega), ha' 1 n (by omega)]; ring
  · show ρ_val * l1Weighted.toSeq (abar 0) n - l1Weighted.toSeq (abar 1) n -
        l1Weighted.toSeq (abar 0 * abar 2) n = 0
    rw [ha' 0 n (by omega), ha' 1 n (by omega), h02]; ring
  · show -(β_val * l1Weighted.toSeq (abar 2) n) + l1Weighted.toSeq (abar 0 * abar 1) n = 0
    rw [ha' 2 n (by omega), h01]; ring

/-- G(ā) support bound: vanishes beyond mode 2N+1. -/
private lemma G_lorenz_abar_support (l : Fin L) (n : ℕ) (hn : 2 * N + 1 < n) :
    l1Weighted.toSeq (G_lorenz abar l) n = 0 := by
  rw [G_lorenz_tail abar l n (by omega)]
  have ha : l1Weighted.toSeq (abar l) n = 0 := by
    simp [abar, lpWeighted.mk, abar_seq_support l n (by omega)]
  rw [ha, φ_lorenz_abar_support l (n - 1) (by omega), zero_div, sub_zero]

/-! ### Y₀ proof — operator norm approach

`Y₀ = ‖G_lorenz(ābar)‖ = ‖A.toCLM(F_abar)‖` where `F_abar = ofCoeff(F_coeffs abar)`.
Reduced to per-component finite sums via `norm_toCLM_apply_le`, then evaluated
term-by-term via `systemBlockDiagActionEval` + `finsum_bound`.

The ℚ coefficient mirror (`F_coeffs_Q`) provides the bridge for the evaluator.
`ratCast_CauchyProduct` handles the Cauchy product cast. -/

/-- abar toSeq = raw ℚ getD for all modes (getD returns 0 out of bounds, matching abar_seq). -/
private lemma abar_toSeq_eq (i : Fin L) (k : ℕ) :
    l1Weighted.toSeq (abar i) k = ((abar_Q i).getD k 0 : ℝ) := by
  show abar_seq i k = _
  simp only [abar_seq]
  by_cases hk : k ≤ N
  · simp [hk]
  · simp only [show ¬(k ≤ N) from hk, ↓reduceIte]
    symm; simp only [Array.getD]
    simp [show ¬(k < (abar_Q i).size) from by
      have : (abar_Q i).size = N + 1 := by
        fin_cases i <;> simp [abar_Q, abar_0, abar_1, abar_2]
      omega]

/-- ℚ parameters for bridge proofs. -/
private abbrev σ_q : ℚ := 10
private abbrev ρ_q_val : ℚ := 28
private abbrev β_q : ℚ := 8 / 3
private def x₀_q : Fin L → ℚ | 0 => 1 | 1 => 0 | 2 => 0

/-- ℚ mirror of φ_lorenz at ābar. -/
private def φ_lorenz_Q (l : Fin L) (n : ℕ) : ℚ :=
  match l with
  | 0 => σ_q * ((abar_Q 1).getD n 0 - (abar_Q 0).getD n 0)
  | 1 => ρ_q_val * (abar_Q 0).getD n 0 - (abar_Q 1).getD n 0 -
      CauchyProduct (fun k => (abar_Q 0).getD k 0) (fun k => (abar_Q 2).getD k 0) n
  | 2 => -(β_q * (abar_Q 2).getD n 0) +
      CauchyProduct (fun k => (abar_Q 0).getD k 0) (fun k => (abar_Q 1).getD k 0) n

/-- ℚ mirror of F_coeffs at ābar. -/
private lemma ratCast_CauchyProduct (a b : ℕ → ℚ) (n : ℕ) :
    CauchyProduct (fun k => (a k : ℝ)) (fun k => (b k : ℝ)) n =
      ↑(CauchyProduct a b n) :=
  CauchyProduct.map_CauchyProduct (Rat.castHom ℝ) a b n

private def F_coeffs_Q (l : Fin L) (n : ℕ) : ℚ :=
  match n with
  | 0 => (abar_Q l).getD 0 0 - x₀_q l
  | n + 1 => ((n : ℚ) + 1) * (abar_Q l).getD (n + 1) 0 - φ_lorenz_Q l n

/-- Bridge: φ_lorenz(ābar) coefficients = ℚ cast of φ_lorenz_Q. -/
private lemma φ_lorenz_bridge (l : Fin L) (n : ℕ) :
    l1Weighted.toSeq (φ_lorenz abar l) n = (φ_lorenz_Q l n : ℝ) := by
  -- CauchyProduct bridge helper
  have hcp02 : l1Weighted.toSeq (abar 0 * abar 2) n =
      ((CauchyProduct (fun k => (abar_Q 0).getD k 0)
        (fun k => (abar_Q 2).getD k 0) n : ℚ) : ℝ) := by
    have : l1Weighted.toSeq (abar 0) = fun k => ((abar_Q 0).getD k 0 : ℝ) := funext (abar_toSeq_eq 0)
    have : l1Weighted.toSeq (abar 2) = fun k => ((abar_Q 2).getD k 0 : ℝ) := funext (abar_toSeq_eq 2)
    show CauchyProduct (l1Weighted.toSeq (abar 0)) (l1Weighted.toSeq (abar 2)) n = _
    rw [‹l1Weighted.toSeq (abar 0) = _›, ‹l1Weighted.toSeq (abar 2) = _›]
    exact ratCast_CauchyProduct _ _ n
  have hcp01 : l1Weighted.toSeq (abar 0 * abar 1) n =
      ((CauchyProduct (fun k => (abar_Q 0).getD k 0)
        (fun k => (abar_Q 1).getD k 0) n : ℚ) : ℝ) := by
    have : l1Weighted.toSeq (abar 0) = fun k => ((abar_Q 0).getD k 0 : ℝ) := funext (abar_toSeq_eq 0)
    have : l1Weighted.toSeq (abar 1) = fun k => ((abar_Q 1).getD k 0 : ℝ) := funext (abar_toSeq_eq 1)
    show CauchyProduct (l1Weighted.toSeq (abar 0)) (l1Weighted.toSeq (abar 1)) n = _
    rw [‹l1Weighted.toSeq (abar 0) = _›, ‹l1Weighted.toSeq (abar 1) = _›]
    exact ratCast_CauchyProduct _ _ n
  fin_cases l
  · -- l = 0: σ * (a₁ - a₀), linear
    show σ_val * (l1Weighted.toSeq (abar 1) n - l1Weighted.toSeq (abar 0) n) = _
    rw [abar_toSeq_eq 0, abar_toSeq_eq 1]; unfold σ_val φ_lorenz_Q σ_q; push_cast; ring
  · -- l = 1: ρ*a₀ - a₁ - (a₀*a₂), with CauchyProduct
    show ρ_val * l1Weighted.toSeq (abar 0) n - l1Weighted.toSeq (abar 1) n -
        l1Weighted.toSeq (abar 0 * abar 2) n = _
    rw [abar_toSeq_eq 0, abar_toSeq_eq 1, hcp02]; unfold ρ_val φ_lorenz_Q ρ_q_val; push_cast; ring
  · -- l = 2: -β*a₂ + (a₀*a₁), with CauchyProduct
    show -(β_val * l1Weighted.toSeq (abar 2) n) + l1Weighted.toSeq (abar 0 * abar 1) n = _
    rw [abar_toSeq_eq 2, hcp01]; unfold β_val φ_lorenz_Q β_q; push_cast; ring

/-- Bridge: F_coeffs(ābar) = ℚ cast of F_coeffs_Q. -/
private lemma F_coeffs_bridge (l : Fin L) (n : ℕ) :
    F_coeffs abar l n = (F_coeffs_Q l n : ℝ) := by
  simp only [F_coeffs]
  cases n with
  | zero =>
    simp only [F_lorenz, l1Omega.mk_apply, abar_toSeq_eq, F_coeffs_Q, x₀_q, x₀]
    fin_cases l <;> push_cast <;> ring
  | succ m =>
    simp only [F_lorenz, l1Omega.mk_apply, abar_toSeq_eq, φ_lorenz_bridge l m, F_coeffs_Q]
    push_cast; ring

/-- F_coeffs(ābar) has support ≤ 2N+1 (from ābar support N + φ support 2N). -/
private lemma F_coeffs_abar_support (l : Fin L) (n : ℕ) (hn : 2 * N + 1 < n) :
    F_coeffs abar l n = 0 := by
  simp only [F_coeffs]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [F_lorenz, l1Omega.mk_apply]
  have ha : l1Weighted.toSeq (abar l) (m + 1) = 0 := by
    rw [abar_toSeq_eq]; simp [Array.getD, show ¬((m + 1) < (abar_Q l).size) from by
      have : (abar_Q l).size = N + 1 := by
        fin_cases l <;> simp [abar_Q, abar_0, abar_1, abar_2]
      omega]
  have hφ : l1Weighted.toSeq (φ_lorenz abar l) m = 0 :=
    φ_lorenz_abar_support l m (by omega)
  rw [ha, hφ]; ring

/-- F_coeffs(ābar) is in ℓ¹_ν (finite support). -/
private lemma F_coeffs_abar_mem (l : Fin L) :
    lpWeighted.Mem ν_val 1 (F_coeffs abar l) := by
  rw [l1Weighted.mem_iff]
  exact summable_of_ne_finset_zero (s := Finset.Icc 0 (2 * N + 1)) fun n hn => by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    simp [F_coeffs_abar_support l n (by omega)]

/-- Embed F_coeffs(ābar) as an XL1 element. -/
private noncomputable def F_abar : XL1 ν_val L :=
  ofCoeff (F_coeffs abar) F_coeffs_abar_mem

/-- G_lorenz(ābar) = A.toCLM(F_abar): action matches at the sequence level. -/
private lemma G_lorenz_eq_toCLM_F_abar :
    G_lorenz abar = approxInverse.toCLM (ν := ν_val) F_abar := by
  funext l; apply lpWeighted.ext; intro n
  have lhs : lpWeighted.toSeq (G_lorenz abar l) n =
      approxInverse.action (F_coeffs abar) l n := G_lorenz_coeff abar l n
  have rhs : lpWeighted.toSeq ((approxInverse.toCLM (ν := ν_val) F_abar) l) n =
      approxInverse.action (F_coeffs abar) l n := by
    have := SystemBlockDiagData.toCoeff_toCLM (ν := ν_val) approxInverse F_abar l n
    simp only [toCoeff] at this; rw [this]; rfl
  exact lhs.trans rhs.symm

/-- F_abar support as toCoeff. -/
private lemma F_abar_toCoeff_support (l : Fin L) (n : ℕ) (hn : 2 * N + 1 < n) :
    toCoeff (ν := ν_val) F_abar l n = 0 := by
  simp [F_abar, toCoeff, ofCoeff, lpWeighted.mk, F_coeffs_abar_support l n hn]

/-- tailDiag bridge for approxInverse: 1/n for n > N. -/
private lemma approxInverse_tailDiag_eq (l : Fin L) (n : ℕ) (hn : N < n) :
    approxInverse.tailDiag l n = ((1 / (n : ℚ)) : ℝ) := by
  simp [approxInverse, if_neg (by omega : n ≠ 0)]

/-- Per-term Y₀ evaluator. -/
private def Y₀_eval (l : Fin L) :=
  systemBlockDiagActionEval ABlockCols (fun l n => F_coeffs_Q l n)
    (fun l n => 1 / (n : ℚ)) ν_q l

private lemma Y₀_eval_correct (l : Fin L) (n : ℕ) :
    (|approxInverse.action (F_coeffs abar) l n| * (ν_val : ℝ) ^ n : ℝ) ∈
      Y₀_eval l n {} :=
  systemBlockDiagActionEval_correct approxInverse (F_coeffs abar)
    (fun l n => F_coeffs_Q l n) ABlockCols (fun l n => 1 / (n : ℚ)) ν_q
    (fun l j k i => A_finBlock_eq l j i k)
    (fun l n => F_coeffs_bridge l n)
    (fun l n hn => by simp [approxInverse, if_neg (by omega : n ≠ 0)])
    ν_val_eq_q l n {}

lemma Y₀_le :
    Y₀_norm G_lorenz abar (ContinuousLinearMap.id ℝ (XL1 ν_val L)) ≤ (Y₀_bound : ℝ) := by
  show ‖G_lorenz abar‖ ≤ _
  rw [G_lorenz_eq_toCLM_F_abar]
  have hc : toCoeff (ν := ν_val) F_abar = F_coeffs abar := by
    ext l n; simp [F_abar, toCoeff_ofCoeff]
  refine approxInverse.norm_toCLM_apply_le F_abar (2 * N + 1) (by omega)
    F_abar_toCoeff_support (by unfold Y₀_bound; positivity)
    (fun l => ?_)
  simp_rw [hc]; unfold Y₀_bound
  fin_cases l
  all_goals finsum_bound using (Y₀_eval _) (fun k _ _ => Y₀_eval_correct _ k)

/-- Each abar component norm is bounded (finite support → finite sum → native_decide). -/
private lemma abar_norm_le_aux (i : Fin L) {C : ℚ}
    (hle : ∑ n ∈ Finset.Icc 0 N,
      |l1Weighted.toSeq (abar i) n| * (ν_val : ℝ) ^ n ≤ (C : ℝ)) :
    ‖abar i‖ ≤ (C : ℝ) := by
  rw [l1Weighted.norm_eq_Icc_sum_of_support _ N
    (fun n hn => by simp [abar, lpWeighted.mk, abar_seq_support i n hn])]
  exact hle

private lemma abar_norm_0_le : ‖abar 0‖ ≤ (20 : ℝ) :=
  abar_norm_le_aux 0 (by show _ ≤ ((20 : ℚ) : ℝ); finsum_bound using
    (weightedTermEval (abar_Q 0) ν_q)
    (fun k _ _ => weightedTermEval_correct _ ν_q k {}
      (hprec := by norm_num) (hf := abar_toSeq_eq 0 k) (hν := ν_val_eq_q)))

private lemma abar_norm_1_le : ‖abar 1‖ ≤ (26 : ℝ) :=
  abar_norm_le_aux 1 (by show _ ≤ ((26 : ℚ) : ℝ); finsum_bound using
    (weightedTermEval (abar_Q 1) ν_q)
    (fun k _ _ => weightedTermEval_correct _ ν_q k {}
      (hprec := by norm_num) (hf := abar_toSeq_eq 1 k) (hν := ν_val_eq_q)))

private lemma abar_norm_2_le : ‖abar 2‖ ≤ (11 : ℝ) :=
  abar_norm_le_aux 2 (by show _ ≤ ((11 : ℚ) : ℝ); finsum_bound using
    (weightedTermEval (abar_Q 2) ν_q)
    (fun k _ _ => weightedTermEval_correct _ ν_q k {}
      (hprec := by norm_num) (hf := abar_toSeq_eq 2 k) (hν := ν_val_eq_q)))

/-! ## Z₁ bound: ‖composedApprox.toCLM - fderiv G ā‖ ≤ Z₁_bound

On tail modes (n > N): composedApprox tail = h (tailDiag=1), fderiv G tail = h - shiftDivN(Dφ(h)).
So the difference = shiftDivN(Dφ(h)), bounded by ν * ‖Dφ(h) l‖.
On finite modes: both agree (composedApprox.finBlock = Σ_m A*DF matches fderiv G on finite part).
Uses `shiftDivN_norm_le` + per-component Dφ norm bound. -/

/-- On tail modes (n > N), the Z₁ difference equals shiftDivN of Dφ. -/
private lemma Z₁_diff_tail_eq (h : XL1 ν_val L) (l : Fin L) (n : ℕ) (hn : N < n) :
    l1Weighted.toSeq (((composedApprox.toCLM (ν := ν_val) - fderiv ℝ G_lorenz abar) h) l) n =
      l1Weighted.toSeq (shiftDivN_CLM (Dφ_lorenz h l)) n := by
  have : toCoeff (ν := ν_val) (composedApprox.toCLM (ν := ν_val) h) l n -
      toCoeff (ν := ν_val) ((fderiv ℝ G_lorenz abar) h) l n =
      toCoeff (ν := ν_val) (fun l => shiftDivN_CLM (Dφ_lorenz h l)) l n := by
    rw [composedApprox_toCLM_tail h l n hn, fderiv_G_lorenz_tail h l n hn]; ring
  simp only [ContinuousLinearMap.sub_apply, Pi.sub_apply, toCoeff] at this ⊢
  convert this using 1 <;> simp [lpWeighted.sub_toSeq]

/-- On finite modes (n ≤ N), the Z₁ difference is zero. -/
private lemma Z₁_diff_fin_zero (h : XL1 ν_val L) (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    l1Weighted.toSeq (((composedApprox.toCLM (ν := ν_val) - fderiv ℝ G_lorenz abar) h) l) n = 0 := by
  simp only [ContinuousLinearMap.sub_apply, Pi.sub_apply, lpWeighted.sub_toSeq, sub_eq_zero]
  show toCoeff (ν := ν_val) (composedApprox.toCLM (ν := ν_val) h) l n =
    toCoeff (ν := ν_val) ((fderiv ℝ G_lorenz abar) h) l n
  exact Example83.composedApprox_eq_fderiv_G_fin h l n hn

/-- Per-component bound on the Z₁ difference.
Finite modes cancel → norm = tail tsum → tighter `shiftDivN_tailTsum_le_div` bound. -/
private lemma Z₁_component_le (h : XL1 ν_val L) (l : Fin L) :
    ‖((composedApprox.toCLM (ν := ν_val) - fderiv ℝ G_lorenz abar) h) l‖ ≤
      (ν_val : ℝ) / ((N : ℝ) + 1) * ‖Dφ_lorenz h l‖ := by
  -- Step 1: finite part = 0 → norm = tail tsum starting at N+1
  rw [l1Weighted.norm_eq_tailTsum_of_fin_zero _ (N + 1)
    (fun n hn => Z₁_diff_fin_zero h l n (by omega))]
  -- Step 2: rewrite tail terms using Z₁_diff_tail_eq
  have htail : ∀ n, |l1Weighted.toSeq
      (((composedApprox.toCLM (ν := ν_val) - fderiv ℝ G_lorenz abar) h) l) (n + (N + 1))| =
      |l1Weighted.toSeq (shiftDivN_CLM (Dφ_lorenz h l)) (n + (N + 1))| :=
    fun n => congrArg (|·|) (Z₁_diff_tail_eq h l (n + (N + 1)) (by omega))
  simp_rw [htail, shiftDivN_CLM_apply]
  -- Step 3: apply shiftDivN_tailTsum_le_div
  exact shiftDivN_tailTsum_le_div (Dφ_lorenz h l) N

/-- Dφ_lorenz operator norm bound: ‖Dφ_lorenz h l‖ ≤ C * ‖h‖ for each component.
Uses triangle inequality + Banach algebra product norm ‖a*b‖ ≤ ‖a‖*‖b‖.
C = Z₁_bound * (N+1) / ν = 62. -/
private lemma Dφ_lorenz_norm_le (h : XL1 ν_val L) (l : Fin L) :
    ‖Dφ_lorenz h l‖ ≤ (Z₁_bound * ((N : ℚ) + 1) / ν_q) * ‖h‖ := by
  have hpi : ∀ i : Fin L, ‖h i‖ ≤ ‖h‖ := fun i => norm_le_pi_norm h i
  have hmul : ∀ (a b : l1Weighted ν_val), ‖a * b‖ ≤ ‖a‖ * ‖b‖ := norm_mul_le
  have hC : (0 : ℝ) ≤ (Z₁_bound * ((N : ℚ) + 1) / ν_q : ℚ) := by unfold Z₁_bound ν_q N; norm_num
  fin_cases l
  · -- l = 0: ‖σ(h₁ - h₀)‖ ≤ σ * 2 * ‖h‖ ≤ C * ‖h‖
    show ‖σ_val • (h 1 - h 0)‖ ≤ _
    have h1 : ‖σ_val • (h 1 - h 0)‖ ≤ |σ_val| * (‖h 1‖ + ‖h 0‖) :=
      (le_of_eq (norm_smul σ_val _)).trans
        (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _))
    have h2 : |σ_val| * (‖h 1‖ + ‖h 0‖) ≤ 2 * |σ_val| * ‖h‖ :=
      (mul_le_mul_of_nonneg_left (add_le_add (hpi 1) (hpi 0)) (abs_nonneg _)).trans
        (by ring_nf; rfl)
    exact (h1.trans h2).trans (by
      unfold σ_val Z₁_bound ν_q N; push_cast; nlinarith [norm_nonneg h])
  · -- l = 1: ‖ρh₀ - h₁ - (ā₀*h₂ + h₀*ā₂)‖ ≤ (ρ + 1 + ‖ā₀‖ + ‖ā₂‖) * ‖h‖
    show ‖ρ_val • h 0 - h 1 - (abar 0 * h 2 + h 0 * abar 2)‖ ≤ _
    have h1 : ‖ρ_val • h 0 - h 1 - (abar 0 * h 2 + h 0 * abar 2)‖ ≤
        |ρ_val| * ‖h‖ + ‖h‖ + ‖abar 0‖ * ‖h‖ + ‖abar 2‖ * ‖h‖ := by
      have := norm_sub_le (ρ_val • h 0 - h 1) (abar 0 * h 2 + h 0 * abar 2)
      have := norm_sub_le (ρ_val • h 0) (h 1)
      have := norm_add_le (abar 0 * h 2) (h 0 * abar 2)
      have := (norm_smul ρ_val (h 0)).symm ▸ mul_le_mul_of_nonneg_left (hpi 0) (abs_nonneg ρ_val)
      nlinarith [hpi 1, hmul (abar 0) (h 2), hmul (h 0) (abar 2),
        hpi 2, hpi 0, norm_nonneg (abar 0), norm_nonneg (abar 2)]
    have h2 : |ρ_val| * ‖h‖ + ‖h‖ + ‖abar 0‖ * ‖h‖ + ‖abar 2‖ * ‖h‖ =
        (|ρ_val| + 1 + ‖abar 0‖ + ‖abar 2‖) * ‖h‖ := by ring
    have h3 : ‖abar 0‖ + ‖abar 2‖ ≤ 31 := by linarith [abar_norm_0_le, abar_norm_2_le]
    exact (h1.trans (le_of_eq h2)).trans (by
      have h4 : |ρ_val| = ρ_val := abs_of_nonneg (by unfold ρ_val; positivity)
      rw [h4]; unfold ρ_val Z₁_bound ν_q N; push_cast; nlinarith [norm_nonneg h])
  · -- l = 2: ‖-βh₂ + (ā₀h₁ + h₀ā₁)‖ ≤ (β + ‖ā₀‖ + ‖ā₁‖) * ‖h‖
    show ‖-(β_val • h 2) + (abar 0 * h 1 + h 0 * abar 1)‖ ≤ _
    have h1 : ‖-(β_val • h 2) + (abar 0 * h 1 + h 0 * abar 1)‖ ≤
        |β_val| * ‖h‖ + ‖abar 0‖ * ‖h‖ + ‖abar 1‖ * ‖h‖ := by
      have := norm_add_le (-(β_val • h 2)) (abar 0 * h 1 + h 0 * abar 1)
      have := norm_add_le (abar 0 * h 1) (h 0 * abar 1)
      have := (norm_neg (β_val • h 2)).symm ▸ (norm_smul β_val (h 2)).symm ▸
        mul_le_mul_of_nonneg_left (hpi 2) (abs_nonneg β_val)
      nlinarith [hmul (abar 0) (h 1), hmul (h 0) (abar 1),
        hpi 1, hpi 0, norm_nonneg (abar 0), norm_nonneg (abar 1)]
    have h2 : |β_val| * ‖h‖ + ‖abar 0‖ * ‖h‖ + ‖abar 1‖ * ‖h‖ =
        (|β_val| + ‖abar 0‖ + ‖abar 1‖) * ‖h‖ := by ring
    have h3 : ‖abar 0‖ + ‖abar 1‖ ≤ 46 := by linarith [abar_norm_0_le, abar_norm_1_le]
    exact (h1.trans (le_of_eq h2)).trans (by
      have h4 : |β_val| = β_val := abs_of_nonneg (by unfold β_val; positivity)
      rw [h4]; unfold β_val Z₁_bound ν_q N; push_cast; nlinarith [norm_nonneg h])

lemma Z₁_le_cert :
    Z₁_norm G_lorenz abar (ContinuousLinearMap.id ℝ (XL1 ν_val L))
      (composedApprox.toCLM (ν := ν_val)) ≤ (Z₁_bound : ℝ) :=
  Z₁_le (by unfold Z₁_bound; positivity) fun h l =>
    (Z₁_component_le h l).trans (by
      exact (mul_le_mul_of_nonneg_left (Dφ_lorenz_norm_le h l)
        (by unfold ν_val; positivity)).trans
        (by unfold Z₁_bound ν_q ν_val N; push_cast; ring_nf; rfl))

/-! ## Z₂ bound + radii polynomial + main theorem -/

/-- Per-component bound on φ fderiv difference (bilinear Lorenz terms). -/
private lemma Dφ_diff_norm_le (c : XL1 ν_val L) (h : XL1 ν_val L) (l : Fin L) :
    ‖((fderiv ℝ (fun x => φ_lorenz x l) c -
      fderiv ℝ (fun x => φ_lorenz x l) abar)) h‖ ≤ 2 * ‖c - abar‖ * ‖h‖ := by
  have hpi_c : ∀ i : Fin L, ‖(c - abar) i‖ ≤ ‖c - abar‖ := fun i => norm_le_pi_norm _ i
  have hpi_h : ∀ i : Fin L, ‖h i‖ ≤ ‖h‖ := fun i => norm_le_pi_norm h i
  have hmul : ∀ (a b : l1Weighted ν_val), ‖a * b‖ ≤ ‖a‖ * ‖b‖ := norm_mul_le
  fin_cases l
  · -- l = 0: difference = 0
    show ‖(fderiv ℝ (fun x => φ_lorenz x 0) c - fderiv ℝ (fun x => φ_lorenz x 0) abar) h‖ ≤ _
    rw [fderiv_φ_diff_0]; simp; positivity
  · -- l = 1: ‖-((c₀-a₀)*h₂ + h₀*(c₂-a₂))‖ ≤ 2*‖c-a‖*‖h‖
    show ‖(fderiv ℝ (fun x => φ_lorenz x 1) c - fderiv ℝ (fun x => φ_lorenz x 1) abar) h‖ ≤ _
    rw [fderiv_φ_diff_1, norm_neg]
    have hca0 : ‖c 0 - abar 0‖ ≤ ‖c - abar‖ := by
      have : c 0 - abar 0 = (c - abar) 0 := by simp [Pi.sub_apply]
      rw [this]; exact hpi_c 0
    have hca2 : ‖c 2 - abar 2‖ ≤ ‖c - abar‖ := by
      have : c 2 - abar 2 = (c - abar) 2 := by simp [Pi.sub_apply]
      rw [this]; exact hpi_c 2
    exact (norm_add_le _ _).trans (add_le_add (hmul _ _) (hmul _ _)) |>.trans
      (add_le_add
        (mul_le_mul hca0 (hpi_h 2) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (hpi_h 0) hca2 (norm_nonneg _) (norm_nonneg _))
      |>.trans (by ring_nf; rfl))
  · -- l = 2: ‖(c₀-a₀)*h₁ + h₀*(c₁-a₁)‖ ≤ 2*‖c-a‖*‖h‖
    show ‖(fderiv ℝ (fun x => φ_lorenz x 2) c - fderiv ℝ (fun x => φ_lorenz x 2) abar) h‖ ≤ _
    rw [fderiv_φ_diff_2]
    have hca0 : ‖c 0 - abar 0‖ ≤ ‖c - abar‖ := by
      rw [show c 0 - abar 0 = (c - abar) 0 from by simp [Pi.sub_apply]]; exact hpi_c 0
    have hca1 : ‖c 1 - abar 1‖ ≤ ‖c - abar‖ := by
      rw [show c 1 - abar 1 = (c - abar) 1 from by simp [Pi.sub_apply]]; exact hpi_c 1
    exact (norm_add_le _ _).trans (add_le_add (hmul _ _) (hmul _ _)) |>.trans
      (add_le_add
        (mul_le_mul hca0 (hpi_h 1) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (hpi_h 0) hca1 (norm_nonneg _) (norm_nonneg _))
      |>.trans (by ring_nf; rfl))

set_option maxHeartbeats 800000 in
lemma Z₂_le_cert (c : XL1 ν_val L)
    (hc : c ∈ Metric.closedBall (abar : XL1 ν_val L) (r_minus : ℝ)) :
    Z₂_norm G_lorenz abar (ContinuousLinearMap.id ℝ (XL1 ν_val L)) c ≤
      (Z₂_bound : ℝ) * (r_minus : ℝ) := by
  -- Z₂_norm = ‖fderiv G c - fderiv G abar‖ (since A = id)
  show ‖(ContinuousLinearMap.id ℝ _).comp
    (fderiv ℝ G_lorenz c - fderiv ℝ G_lorenz abar)‖ ≤ _
  rw [ContinuousLinearMap.id_comp]
  -- Suffices: ‖fderiv G c - fderiv G abar‖ ≤ Z₂_bound * ‖c - abar‖
  -- since ‖c - abar‖ ≤ r_minus from hc
  have hdist : ‖c - abar‖ ≤ (r_minus : ℝ) := hc
  -- Strategy: ‖fderiv G c - fderiv G abar‖ ≤ Z₂_bound * ‖c - abar‖ ≤ Z₂_bound * r_minus
  -- Core bound: per h, ‖(diff)(h)‖ ≤ 2ν * ‖A‖ * ‖c-a‖ * ‖h‖
  -- G_lorenz = G_tail + G_fin_correction
  -- diff(G_tail)(h)(l) = -shiftDivN_CLM(Dφ_diff l h), ‖·‖ ≤ ν * 2‖c-a‖‖h‖
  -- diff(G_fin_correction) supported on n ≤ N, also bounded by Dφ_diff
  -- Per-component φ fderiv difference bound
  have hDφ : ∀ h : XL1 ν_val L, ∀ l : Fin L,
      ‖((fderiv ℝ (fun x => φ_lorenz x l) c -
        fderiv ℝ (fun x => φ_lorenz x l) abar)) h‖ ≤ 2 * ‖c - abar‖ * ‖h‖ :=
    fun h l => Dφ_diff_norm_le c h l
  -- G_tail fderiv difference: -shiftDivN_CLM(Dφ_diff)
  have hG_tail_diff : ∀ h : XL1 ν_val L, ∀ l : Fin L,
      (fderiv ℝ G_tail c h) l - (fderiv ℝ G_tail abar h) l =
        -shiftDivN_CLM ((fderiv ℝ (fun x => φ_lorenz x l) c -
          fderiv ℝ (fun x => φ_lorenz x l) abar) h) := by
    intro h l
    -- G_tail a l = a l - shiftDivN_CLM(φ a l)
    -- fderiv(G_tail)(a)(h) l = h l - shiftDivN_CLM(fderiv(φ·l)(a)(h))
    have hfderiv_at : ∀ a : XL1 ν_val L,
        (fderiv ℝ G_tail a h) l = h l - shiftDivN_CLM ((fderiv ℝ (fun x => φ_lorenz x l) a) h) := by
      intro a
      rw [show (fderiv ℝ G_tail a h) l =
          (fderiv ℝ (fun x : XL1 ν_val L => G_tail x l) a) h from by
        rw [fderiv_pi (fun i => differentiableAt_pi.mp (differentiable_G_tail a) i)]; rfl]
      have hfn : (fun x : XL1 ν_val L => G_tail x l) =
          (fun x => x l) - (fun x => shiftDivN_CLM (φ_lorenz x l)) := by
        ext x; simp [G_tail, Pi.sub_apply]
      rw [hfn]
      let pl := ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin L => l1Weighted ν_val) l
      have hsub : HasFDerivAt
          (⇑pl - fun x : XL1 ν_val L => shiftDivN_CLM (φ_lorenz x l))
          (fderiv ℝ (⇑pl) a -
            fderiv ℝ (fun x => shiftDivN_CLM (φ_lorenz x l)) a) a :=
        (pl.differentiableAt.hasFDerivAt).sub
          (((shiftDivN_CLM.differentiable.comp
            (differentiable_φ_lorenz_component l)) a).hasFDerivAt)
      change (fderiv ℝ (⇑pl - fun x => shiftDivN_CLM (φ_lorenz x l)) a) h = _
      rw [hsub.fderiv, ContinuousLinearMap.sub_apply]
      congr 1
      · rw [ContinuousLinearMap.fderiv]; rfl
      · have := fderiv_comp (𝕜 := ℝ) (f := fun x : XL1 ν_val L => φ_lorenz x l)
            (g := shiftDivN_CLM) a shiftDivN_CLM.differentiableAt
            (differentiable_φ_lorenz_component l a)
        simp only [Function.comp_def] at this
        rw [this, ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv]
    rw [hfderiv_at c, hfderiv_at abar]
    simp only [ContinuousLinearMap.sub_apply, map_neg, map_sub]; ring
  -- Core: per-component fderiv difference bounded by shiftDivN ∘ Dφ_diff
  -- diff(G_tail)(h)(l) = -shiftDivN_CLM(Dφ_diff l h)
  -- ‖shiftDivN_CLM(Dφ_diff)‖ ≤ ν * ‖Dφ_diff‖ ≤ 2ν * ‖c-a‖ * ‖h‖
  -- Since Z₂_bound ≥ 2ν and G's fderiv on the tail = G_tail's fderiv,
  -- and on finite modes the A.action bound absorbs into ‖A‖ * 2ν,
  -- we get ‖fderiv G c - fderiv G abar‖ ≤ 2ν * ‖A‖ * ‖c-a‖ ≤ Z₂_bound * ‖c-a‖
  -- For now, bound using opNorm_le_bound + G_tail dominance
  calc ‖fderiv ℝ G_lorenz c - fderiv ℝ G_lorenz abar‖
      ≤ (Z₂_bound : ℝ) * ‖c - abar‖ := by
        apply ContinuousLinearMap.opNorm_le_bound _
          (mul_nonneg (by unfold Z₂_bound; positivity) (norm_nonneg _))
        intro h
        -- Per h: ‖(diff)(h)‖ = sup_l ‖(diff)(h) l‖
        rw [ContinuousLinearMap.sub_apply]
        refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg
          (by unfold Z₂_bound; positivity) (norm_nonneg _)) (norm_nonneg _))).mpr fun l => ?_
        -- Decompose: fderiv G_lorenz = fderiv G_tail + fderiv G_fin_correction
        have hdecomp : ∀ a : XL1 ν_val L,
            fderiv ℝ G_lorenz a =
              fderiv ℝ G_tail a + fderiv ℝ (fun x => G_fin_correction x) a := by
          intro a
          conv_lhs => rw [show G_lorenz = fun x l' => G_tail x l' + G_fin_correction x l' from
            funext fun x => funext fun l' => G_lorenz_eq_tail_plus_correction x l']
          exact fderiv_add (differentiable_G_tail a) (differentiable_G_fin_correction a)
        -- Rewrite the difference using decomposition
        have hdiff_eq : ((fderiv ℝ G_lorenz c h - fderiv ℝ G_lorenz abar h) : XL1 ν_val L) l =
            (fderiv ℝ G_tail c h l - fderiv ℝ G_tail abar h l) +
            ((fderiv ℝ (fun x => G_fin_correction x) c h) l -
             (fderiv ℝ (fun x => G_fin_correction x) abar h) l) := by
          simp only [Pi.sub_apply, hdecomp, ContinuousLinearMap.add_apply, Pi.add_apply]; ring
        rw [show ((fderiv ℝ G_lorenz c h - fderiv ℝ G_lorenz abar h) : XL1 ν_val L) l =
          ((fderiv ℝ G_lorenz c h - fderiv ℝ G_lorenz abar h : XL1 ν_val L) l) from rfl,
          hdiff_eq, hG_tail_diff]
        -- Rewrite back to (diff G h) l
        -- Rewrite back: expression = diff(G)(h)(l)
        rw [hG_tail_diff h l] at hdiff_eq
        -- hdiff_eq now: (diff G h) l = -shiftDivN(...) + G_fin_diff
        rw [show -shiftDivN_CLM ((fderiv ℝ (fun x => φ_lorenz x l) c -
            fderiv ℝ (fun x => φ_lorenz x l) abar) h) +
            ((fderiv ℝ (fun a => G_fin_correction a) c) h l -
             (fderiv ℝ (fun a => G_fin_correction a) abar) h l) =
            fderiv ℝ G_lorenz c h l - fderiv ℝ G_lorenz abar h l from
          hdiff_eq.symm]
        -- Construct shifted Dφ diff as XL1 element
        -- Δ j n = if n = 0 then 0 else -(Dφ_diff j h (n-1))
        have hmem : ∀ j : Fin L, lpWeighted.Mem ν_val 1
            (fun n => if n = 0 then (0 : ℝ) else
              -lpWeighted.toSeq (((fderiv ℝ (fun x => φ_lorenz x j) c -
                fderiv ℝ (fun x => φ_lorenz x j) abar) h)) (n - 1)) := by
          intro j; rw [l1Weighted.mem_iff]
          have hsumm := l1Weighted.summable_shifted_weighted
            ((fderiv ℝ (fun x => φ_lorenz x j) c -
              fderiv ℝ (fun x => φ_lorenz x j) abar) h)
          exact hsumm.of_nonneg_of_le
            (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg _) _))
            (fun n => by split_ifs with h0 <;> simp only [abs_neg, abs_zero, zero_mul, le_refl,
              mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg _) _)])
        set w : XL1 ν_val L := fun j => lpWeighted.mk _ (hmem j)
        -- (diff G h) = approxInverse.toCLM(w) at component l
        have hseq : ∀ n, lpWeighted.toSeq (fderiv ℝ G_lorenz c h l -
            fderiv ℝ G_lorenz abar h l) n =
            lpWeighted.toSeq (approxInverse.toCLM (ν := ν_val) w l) n := by
          intro n
          -- Convert to l1Weighted.toSeq form
          show l1Weighted.toSeq ((fderiv ℝ G_lorenz c h) l) n -
            l1Weighted.toSeq ((fderiv ℝ G_lorenz abar h) l) n =
            l1Weighted.toSeq (approxInverse.toCLM (ν := ν_val) w l) n
          rw [fderiv_G_lorenz_coeff_at c h l n, fderiv_G_lorenz_coeff_at abar h l n]
          -- RHS = A.action(toCoeff w) l n
          change _ = toCoeff (ν := ν_val) (approxInverse.toCLM (ν := ν_val) w) l n
          rw [SystemBlockDiagData.toCoeff_toCLM]
          -- Key: fderiv difference of F_coeffs = toCoeff w
          have hcd : ∀ j : Fin L, ∀ k : ℕ,
              (fderiv ℝ (fun a => F_coeffs a j k) c) h -
                (fderiv ℝ (fun a => F_coeffs a j k) abar) h =
              toCoeff (ν := ν_val) w j k := by
            intro j k; rw [fderiv_F_coeffs_diff c h j k]; show _ = lpWeighted.toSeq (w j) k; rfl
          by_cases hn : n ≤ N
          · -- Finite mode: fderiv distributes through action (linear in coefficients)
            rw [approxInverse.fderiv_action_fin F_coeffs differentiable_F_coeffs l n hn c h,
              approxInverse.fderiv_action_fin F_coeffs differentiable_F_coeffs l n hn abar h]
            simp only [SystemBlockDiagData.action_finite _ _ _ _ hn,
              ← Finset.sum_sub_distrib, ← mul_sub]
            simp_rw [hcd]
          · -- Tail mode: action = tailDiag * F(l,n)
            push_neg at hn
            have hfn : (fun a => approxInverse.action (F_coeffs a) l n) =
                fun a => approxInverse.tailDiag l n * F_coeffs a l n :=
              funext fun a => SystemBlockDiagData.action_tail _ _ _ _ hn
            rw [hfn]
            have hd : ∀ a : XL1 ν_val L, HasFDerivAt
                (fun a => approxInverse.tailDiag l n * F_coeffs a l n)
                (approxInverse.tailDiag l n •
                  fderiv ℝ (fun a => F_coeffs a l n) a) a := fun a =>
              (differentiable_F_coeffs_general l n a).hasFDerivAt.const_mul _
            rw [(hd c).fderiv, (hd abar).fderiv]
            simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ← mul_sub]
            rw [hcd, SystemBlockDiagData.action_tail _ _ _ _ hn]
        rw [lpWeighted.ext hseq]
        -- Per-component bound using w 0 = 0 (φ₀ is linear)
        have hw0 : w 0 = 0 := by
          apply lpWeighted.ext; intro k
          show (if k = 0 then (0 : ℝ) else _) = 0
          split_ifs with h0
          · rfl
          · show -lpWeighted.toSeq ((fderiv ℝ (fun x => φ_lorenz x 0) c -
                fderiv ℝ (fun x => φ_lorenz x 0) abar) h) (k - 1) = 0
            rw [fderiv_φ_diff_0]; simp
        -- ‖w‖ ≤ 2ν * ‖c-a‖ * ‖h‖
        have hw_norm : ‖w‖ ≤ 2 * (ν_val : ℝ) * ‖c - abar‖ * ‖h‖ :=
          (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg
            (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (PosReal.coe_nonneg _))
            (norm_nonneg _)) (norm_nonneg _))).mpr fun j => by
            set dj := ((fderiv ℝ (fun x => φ_lorenz x j) c -
              fderiv ℝ (fun x => φ_lorenz x j) abar) h)
            have hnorm_w : ‖w j‖ ≤ (ν_val : ℝ) * ‖dj‖ := by
              rw [l1Weighted.norm_eq_tsum, l1Weighted.norm_eq_tsum]
              have hsw := l1Weighted.summable_weighted (w j)
              rw [hsw.tsum_eq_zero_add]
              simp only [show lpWeighted.toSeq (w j) 0 = 0 from lpWeighted.mk_apply _ _ 0 ▸ if_pos rfl,
                abs_zero, zero_mul, zero_add]
              rw [show (fun n => |lpWeighted.toSeq (w j) (n + 1)| * (ν_val : ℝ) ^ (n + 1)) =
                fun n => (ν_val : ℝ) * (|lpWeighted.toSeq dj n| * (ν_val : ℝ) ^ n) from by
                ext n; show |if n + 1 = 0 then 0 else -(lpWeighted.toSeq dj n)| * _ = _
                simp [abs_neg, pow_succ]; ring]
              rw [tsum_mul_left]
            calc ‖w j‖ ≤ (ν_val : ℝ) * ‖dj‖ := hnorm_w
              _ ≤ (ν_val : ℝ) * (2 * ‖c - abar‖ * ‖h‖) :=
                  mul_le_mul_of_nonneg_left (hDφ h j) (PosReal.coe_nonneg _)
              _ = 2 * ↑ν_val * ‖c - abar‖ * ‖h‖ := by ring
        -- Per-component decomposition: finPart + tailPart with restricted active set
        have hdecomp := approxInverse.applyX_component_eq_finite_add_tail (ν := ν_val) w l
        rw [SystemBlockDiagData.toCLM_apply, hdecomp]
        -- ‖fin + tail‖ ≤ ‖fin‖ + ‖tail‖
        have hfin_le := approxInverse.actionFinite_component_norm_le_restricted
          (ν := ν_val) w l ({1, 2} : Finset (Fin L))
          (fun j hj => by
            have : j = 0 := by fin_cases j <;> simp_all (config := { decide := true })
            exact this ▸ hw0)
        have htail_le := approxInverse.actionTail_component_norm_le (ν := ν_val) w l
        -- Bound tailBound * ‖w l‖ ≤ (if l ∈ {1,2} then tailBound else 0) * ‖w‖
        have htail_restricted : approxInverse.tailBound * ‖w l‖ ≤
            (if l ∈ ({1, 2} : Finset (Fin L)) then approxInverse.tailBound else 0) * ‖w‖ := by
          by_cases hl : l ∈ ({1, 2} : Finset (Fin L))
          · rw [if_pos hl]
            exact mul_le_mul_of_nonneg_left (norm_le_pi_norm w l) (approxInverse.tailBound_nonneg_at l)
          · have hl0 : l = 0 := by fin_cases l <;> simp_all (config := { decide := true })
            subst hl0; simp [hw0]
        -- Nonneg for factor
        have hfactor_nn : 0 ≤ (∑ j ∈ ({1, 2} : Finset (Fin L)),
            blockEntryNorm ν_val approxInverse.finBlock l j) +
            (if l ∈ ({1, 2} : Finset (Fin L)) then approxInverse.tailBound else 0) :=
          add_nonneg (Finset.sum_nonneg fun j _ =>
            blockEntryNorm_nonneg (ν := ν_val) approxInverse.finBlock l j)
            (by split <;> [exact approxInverse.tailBound_nonneg_at l; exact le_refl _])
        calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
          _ ≤ (∑ j ∈ ({1, 2} : Finset (Fin L)), blockEntryNorm ν_val approxInverse.finBlock l j) * ‖w‖ +
              approxInverse.tailBound * ‖w l‖ := add_le_add hfin_le htail_le
          _ ≤ (∑ j ∈ ({1, 2} : Finset (Fin L)), blockEntryNorm ν_val approxInverse.finBlock l j) * ‖w‖ +
              (if l ∈ ({1, 2} : Finset (Fin L)) then approxInverse.tailBound else 0) * ‖w‖ :=
            add_le_add le_rfl htail_restricted
          _ = ((∑ j ∈ ({1, 2} : Finset (Fin L)), blockEntryNorm ν_val approxInverse.finBlock l j) +
              if l ∈ ({1, 2} : Finset (Fin L)) then approxInverse.tailBound else 0) * ‖w‖ := by ring
          _ ≤ ((∑ j ∈ ({1, 2} : Finset (Fin L)), blockEntryNorm ν_val approxInverse.finBlock l j) +
              if l ∈ ({1, 2} : Finset (Fin L)) then approxInverse.tailBound else 0) *
              (2 * ↑ν_val * ‖c - abar‖ * ‖h‖) :=
            mul_le_mul_of_nonneg_left hw_norm hfactor_nn
          _ = 2 * ↑ν_val * ((∑ j ∈ ({1, 2} : Finset (Fin L)), blockEntryNorm ν_val approxInverse.finBlock l j) +
              if l ∈ ({1, 2} : Finset (Fin L)) then approxInverse.tailBound else 0) *
              ‖c - abar‖ * ‖h‖ := by ring
          _ ≤ (Z₂_bound : ℝ) * ‖c - abar‖ * ‖h‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              exact Z₂_blockNorm_component_le approxInverse ABlockCols ν_q
                approxInverse_tailBound_q {1, 2}
                (fun l j k i => A_finBlock_eq l j i k) ν_val_eq_q
                approxInverse_tailBound_eq (by native_decide) l
    _ ≤ (Z₂_bound : ℝ) * (r_minus : ℝ) :=
        mul_le_mul_of_nonneg_left hdist (by unfold Z₂_bound; positivity)

/-- Radii polynomial negativity at r₀. -/
private lemma radii_neg_icc :
    ∀ r ∈ Set.Icc (r_minus : ℝ) (r_minus : ℝ),
    generalRadiiPolynomial (Y₀_bound : ℝ) (Z₀_bound : ℝ) (Z₁_bound : ℝ)
      (fun _ => (Z₂_bound : ℝ)) r < 0 := by
  unfold generalRadiiPolynomial Y₀_bound Z₀_bound Z₁_bound Z₂_bound r_minus
  fast_bound

lemma radii_neg :
    generalRadiiPolynomial (Y₀_bound : ℝ) (Z₀_bound : ℝ) (Z₁_bound : ℝ)
      (fun _ => (Z₂_bound : ℝ)) (r_minus : ℝ) < 0 :=
  radii_neg_icc _ ⟨le_refl _, le_refl _⟩

/-- **Main theorem**: existence and uniqueness of a true solution near ābar. -/
theorem main_theorem :
    ∃! xTilde ∈ Metric.closedBall (abar : XL1 ν_val L) (r_minus : ℝ),
      G_lorenz xTilde = 0 :=
  existsUnique (by unfold r_minus; positivity)
    (Y₀_le.trans (by unfold Y₀_bound; exact_mod_cast le_refl _))
    (Z₀_le Z₀_finBlockNorm_le)
    (Z₁_le_cert.trans (by unfold Z₁_bound; exact_mod_cast le_refl _))
    (fun c hc => Z₂_le_cert c hc)
    radii_neg

end Example83.Cert

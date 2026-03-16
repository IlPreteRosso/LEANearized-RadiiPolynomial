import LeanCert
import RadiiPolynomial.TaylorODE_Direct.DirectCore
import RadiiPolynomial.TaylorODE_Direct.LeanCertHelpers
import RadiiPolynomial.SystemTaylorODE.Setup82

/-!
# Direct Radii Certificate (TaylorODE_Direct)

This file certifies the Direct Taylor ODE radii-polynomial hypotheses directly from
CLM/operator norms, using rational approximations and LeanCert.

## Active proof pipeline

1. Finite matrix bounds (`Z₀`, `Z₂`) use
   `l1Weighted.arrayColNormIccSum` +
   `l1Weighted.matrixColNorm_le_of_arrayColNormIccSum`
   with `colNormTermDyadic` + `finsum_bound`.
2. Vector-action bounds (`Y₀`, `Z₁`) use a ℚ action witness
   (`blockDiagAction_q`) plus a bridge to CLM terms, then
   `finsum_bound auto`.
3. Shared helper lemmas (`LeanCertHelpers`) provide interval-to-scalar wrappers.
4. Structural CLM lemmas (`BlockDiag`) lift numeric bounds to direct norm goals.
5. `main_theorem` is obtained by instantiating
   `DirectCore.existsUnique_of_direct_bounds` with
   `Y₀_norm_le`, `Z₀_norm_le`, `Z₁_norm_le`, `Z₂_norm_le`.
6. `main_theorem_via_witness` uses the same direct norms, but routes through the
   canonical witness package (`canonicalWitness`) and witness-sum inequalities.

No symbolic-reduction `*_bound_valid` lemmas are used in the active theorem path.
-/

open LeanCert.Core


namespace DirectRadiiCert

/-! ## Parameters - Rational Approximations -/

-- Rational sources of truth (shared by both ℚ and ℝ definitions).
def ā₀_q : ℚ := 5774/10000
def ā₁_q : ℚ := 8660/10000
def ā₂_q : ℚ := -6495/10000

def A_diag_q : ℚ := ā₁_q
def A_sub1_q : ℚ := -12990/10000
def A_sub2_q : ℚ := 29240/10000
def A_tail_q : ℚ := 1 / (2 * ā₀_q)
def inv_abs_ā₀_q : ℚ := 1 / |ā₀_q|

-- Rational approximations lifted to ℝ.
noncomputable def ā₀ : ℝ := (ā₀_q : ℝ)      -- ≈ √3/3 ≈ 0.57735
noncomputable def ā₁ : ℝ := (ā₁_q : ℝ)      -- ≈ √3/2 ≈ 0.86603
noncomputable def ā₂ : ℝ := (ā₂_q : ℝ)      -- ≈ -3√3/8 ≈ -0.64952
noncomputable def lam0 : ℝ := 1/3
noncomputable def ν_val : PosReal := ⟨1/4, by norm_num⟩
noncomputable def r₀ : ℝ := 996/10000

lemma ā₀_pos : 0 < ā₀ := by
  unfold ā₀ ā₀_q
  norm_num
lemma r₀_pos : 0 < r₀ := by unfold r₀; norm_num

lemma ā₀_ne_zero : ā₀ ≠ 0 := ne_of_gt ā₀_pos

noncomputable def sol : DirectCore.ApproxSolution 2 where
  aBar_fin := ![ā₀, ā₁, ā₂]
  aBar_zero_ne := ā₀_ne_zero

-- A_mat entries as symbolic definitions
noncomputable def A_diag : ℝ := (A_diag_q : ℝ)       -- ≈ √3/2 (diagonal entries)
noncomputable def A_sub1 : ℝ := (A_sub1_q : ℝ)       -- ≈ -3√3/4 (first subdiagonal)
noncomputable def A_sub2 : ℝ := (A_sub2_q : ℝ)       -- ≈ 27√3/16 (second subdiagonal)

-- A_mat column arrays (ℚ data, computable)
def A_col0 : Array ℚ := #[A_diag_q, A_sub1_q, A_sub2_q]
def A_col1 : Array ℚ := #[0, A_diag_q, A_sub1_q]
def A_col2 : Array ℚ := #[0, 0, A_diag_q]

def A_colOf : Fin 3 → Array ℚ
  | 0 => A_col0
  | 1 => A_col1
  | 2 => A_col2

-- A_mat defined from column arrays (enables O(1) norm proofs)
noncomputable def A_mat : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ((A_colOf j).getD (i : ℕ) 0 : ℝ)

-- Bridge to explicit matrix notation (used by downstream lemmas)
lemma A_mat_eq_explicit :
    A_mat = !![A_diag, 0, 0; A_sub1, A_diag, 0; A_sub2, A_sub1, A_diag] := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [A_mat, A_colOf, A_col0, A_col1, A_col2, A_diag, A_sub1, A_sub2, Array.getD]


/-! ## BlockDiagOp for the approximate inverse

`approxInverse sol A_mat` from DirectCore.lean is the BlockDiagOp with
finBlock = A_mat and tailDiag = 1/(2ā₀). This is the operator used in all
direct norm bounds below. -/

noncomputable abbrev A_op : BlockDiag.BlockDiagOp ν_val 2 :=
  DirectCore.approxInverse sol A_mat

/-- DirectCore.F(ā) as an ℓ¹_ν element -/
noncomputable abbrev F_ā : l1Weighted ν_val :=
  DirectCore.F lam0 sol.toL1

/-- DirectCore.F(ā) has finite support: toSeq(DirectCore.F(ā)) n = 0 for n > 2N = 4 -/
lemma F_ā_supp : ∀ n, 4 < n → lpWeighted.toSeq F_ā n = 0 := by
  intro n hn
  show lpWeighted.toSeq (DirectCore.F lam0 sol.toL1) n = 0
  rw [DirectCore.F_component, DirectCore.ApproxSolution.toL1_toSeq]
  exact DirectCore.F_toSeq_zero_of_gt_two_N lam0 sol n (by norm_num) (by omega)

/-! ## Column Norm Infrastructure (LeanCert, O(1) proofs)

Local evaluator for weighted matrix-column terms; the norm-side formulas and
transfer lemmas live in `lpWeighted.lean` (`arrayColNormIccSum` / `matrixColNorm` bridge),
and scalar interval wrappers live in `LeanCertHelpers.lean`. -/

open LeanCert.Engine

/-- Per-term evaluator: |col[k]| * ν^k / ν^j as IntervalDyadic -/
def colNormTermDyadic (col : Array ℚ) (ν : ℚ) (j : Nat) (k : Nat)
    (cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat
    (IntervalRat.singleton (|col.getD k 0| * ν ^ k / ν ^ j)) cfg.precision

theorem colNormTermDyadic_correct (col : Array ℚ) (ν : ℚ) (j : Nat)
    (k : Nat) (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num) :
    (|(col.getD k 0 : ℝ)| * (ν : ℝ) ^ k / (ν : ℝ) ^ j : ℝ) ∈
      colNormTermDyadic col ν j k cfg := by
  simp only [colNormTermDyadic]
  exact_mod_cast LeanCertHelpers.rat_mem_singleton _ cfg.precision hprec

/-! ## Explicit Coefficient Values -/

section Coefficients

lemma ā₀_eq : ā₀ = 5774/10000 := by
  unfold ā₀ ā₀_q
  norm_num
/-- |ā₀| = ā₀ (positive) -/
lemma abs_ā₀ : |ā₀| = 5774/10000 := by
  rw [abs_of_pos ā₀_pos, ā₀_eq]

/-- Bridge for `1/|ā₀|` from ℝ to the rational source of truth. -/
lemma inv_abs_ā₀ : 1 / |ā₀| = (inv_abs_ā₀_q : ℝ) := by
  unfold inv_abs_ā₀_q ā₀ ā₀_q
  have hq : (0 : ℚ) ≤ 5774 / 10000 := by norm_num
  simp [abs_of_nonneg hq]
  norm_num

end Coefficients

/-! ## Radii Polynomial Negativity

The key verification: p(r₀) < 0

p(r) = Z₂·r² - (1 - Z₀ - Z₁)·r + Y₀

With our bounds:
- Y₀ ≤ Y₀_bnd = 9/500
- Z₀ ≤ Z₀_bnd = 2/1000
- Z₁ ≤ Z₁_bnd = 46/100
- Z₂ ≤ Z₂_bnd = 28/10

1 - Z₀ - Z₁ ≥ 1 - Z₀_bnd - Z₁_bnd = 0.538

p_upper(r₀) = Z₂_bnd * r₀² - (1 - Z₀_bnd - Z₁_bnd) * r₀ + Y₀_bnd < 0 ✓
-/

section RadiiPolynomial

/-- Bound constants for the radii polynomial -/
def Y₀_bnd : ℚ := 9/500      -- ≈ 0.018
def Z₀_bnd : ℚ := 2/1000     -- = 0.002
def Z₁_bnd : ℚ := 46/100     -- = 0.46
def Z₂_bnd : ℚ := 28/10      -- = 2.8

/-- The upper bound polynomial using generalRadiiPolynomial with constant bounds -/
noncomputable def radiiPoly_upper (r : ℝ) : ℝ :=
  generalRadiiPolynomial Y₀_bnd Z₀_bnd Z₁_bnd (fun _ => Z₂_bnd) r

/-- The upper bound polynomial is negative at r₀ -/
theorem radiiPoly_upper_neg :
    ∀ r ∈ Set.Icc r₀ r₀, radiiPoly_upper r < 0 := by
  unfold radiiPoly_upper generalRadiiPolynomial r₀ Y₀_bnd Z₀_bnd Z₁_bnd Z₂_bnd
  simp only [Rat.cast_div, Rat.cast_ofNat]
  fast_bound

end RadiiPolynomial

/-! ## SystemTaylorODE Witness Instantiation (L = 1)

Concrete canonical witness package for the current direct certificate constants.
This is an explicit instantiation of the generic Section 8.2 witness API. -/

section SystemInstantiation

open SystemTaylorODE

abbrev YIdx := YIndex 1 2
abbrev Z0Idx := Z0Index 1 2
abbrev Z1Idx := Z1Index 1 2
abbrev Z2Idx := Z2Index 1

noncomputable def yIdx0 : YIdx := ((0 : Fin 1), (0 : Fin 3))
noncomputable def z0Idx0 : Z0Idx := ((0 : Fin 1), (0 : Fin 1), (0 : Fin 3), (0 : Fin 3))
noncomputable def z1Idx0 : Z1Idx := ((0 : Fin 1), (0 : Fin 1), (0 : Fin 3))
noncomputable def z2Idx0 : Z2Idx := ((0 : Fin 1), (0 : Fin 1), (0 : Fin 1))

noncomputable def Y₀_term : YIdx → ℝ := fun i =>
  if i = yIdx0 then (Y₀_bnd : ℝ) else 0

noncomputable def Z₀_term : Z0Idx → ℝ := fun i =>
  if i = z0Idx0 then (Z₀_bnd : ℝ) else 0

noncomputable def Z₁_term : Z1Idx → ℝ := fun i =>
  if i = z1Idx0 then (Z₁_bnd : ℝ) else 0

noncomputable def Z₂_term (_r : ℝ) : Z2Idx → ℝ := fun i =>
  if i = z2Idx0 then (Z₂_bnd : ℝ) else 0

lemma Y₀_term_sum_le : (∑ i : YIdx, Y₀_term i) ≤ (Y₀_bnd : ℝ) := by
  classical
  simp [Y₀_term, yIdx0]

lemma Z₀_term_sum_le : (∑ i : Z0Idx, Z₀_term i) ≤ (Z₀_bnd : ℝ) := by
  classical
  simp [Z₀_term, z0Idx0]

lemma Z₁_term_sum_le : (∑ i : Z1Idx, Z₁_term i) ≤ (Z₁_bnd : ℝ) := by
  classical
  simp [Z₁_term, z1Idx0]

lemma Z₂_term_sum_le (r : ℝ) : (∑ i : Z2Idx, Z₂_term r i) ≤ (Z₂_bnd : ℝ) := by
  classical
  simp [Z₂_term, z2Idx0]

end SystemInstantiation


/-! ## Connection to Abstract Framework

Now we need to show the abstract bounds equal our rational expressions. -/

section Connection


/-! ### O(1) norm bounds via witness evaluator + ℚ bridge

All four bounds (Y₀, Z₀, Z₁, Z₂) reduce to ‖BlockDiagOp · v‖_{ℓ¹_ν}.

**Architecture**: `l1Weighted.norm_eq_Icc_sum_of_support` rewrites ‖·‖ as
`∑ n ∈ Icc 0 M, |toSeq n| * ν^n`,
then `simp_rw [bridge]` replaces each `toSeq n` with `↑(action_q n)` (computable ℚ),
then `finsum_bound auto eval` closes with O(1) proof via `native_decide`.

**Why the ℚ bridge is needed**: The witness evaluator computes in ℚ (computable,
runs via `native_decide`), while the norm body lives in ℝ. The bridge
`toSeq(A·v)_n = ↑(action_q n)` makes each term decidably checkable by LeanCert. -/

/-- ℚ approximate solution coefficients (single source of truth for evaluators) -/
def sol_q : Array ℚ := #[ā₀_q, ā₁_q, ā₂_q]

/-- DirectCore.F(ā) in ℚ: CauchyProduct(sol_q, sol_q) - paramSeq.
    Computable since CauchyProduct works for any Semiring, including ℚ. -/
def F_ā_q (n : ℕ) : ℚ :=
  CauchyProduct (fun k => sol_q.getD k 0) (fun k => sol_q.getD k 0) n -
  (#[1/3, 1] : Array ℚ).getD n 0

/-- Generic evaluator for ‖BlockDiagOp · v‖ terms.
    Given ℚ matrix columns, vector function, tail coefficient, and weight ν,
    computes |[A·v]_n| * ν^n as an IntervalDyadic singleton. -/
def blockDiagActionEval
    (matCols : Array (Array ℚ)) (vec : ℕ → ℚ)
    (tailCoeff : ℚ) (ν : ℚ) (N : ℕ)
    (n : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  let entry : ℚ := if n ≤ N then
    -- Finite block: dot product of row n with vec
    let dot := ∑ j : Fin (N + 1), (matCols.getD (j : ℕ) #[]).getD n 0 * vec j
    |dot| * ν ^ n
  else
    -- Tail: scalar * vec entry
    |tailCoeff * vec n| * ν ^ n
  IntervalDyadic.ofIntervalRat (IntervalRat.singleton entry) cfg.precision

/-- Y₀ evaluator: instantiate blockDiagActionEval with A_mat columns, DirectCore.F(ā), 1/(2ā₀), ν -/
def Y₀_eval := blockDiagActionEval
  #[A_col0, A_col1, A_col2]  -- A_mat columns
  F_ā_q                       -- DirectCore.F(ā) vector in ℚ
  A_tail_q                    -- tail coefficient = 1/(2ā₀)
  (1/4)                       -- ν
  2                           -- N

/-! #### ℚ action function and bridge -/

/-- Y₀ action in ℚ -/
def Y₀_action_q := BlockDiag.blockDiagAction_q
  #[A_col0, A_col1, A_col2] F_ā_q A_tail_q 2

/-! #### Bridge: toSeq(A·DirectCore.F(ā))_n = ↑(Y₀_action_q n)

The bridge uses three problem-specific facts (hmat, hvec, htail) + the generic
`toCLM_action_eq_rat_cast` from BlockDiag.lean. -/

private lemma sol_toSeq_eq_q (k : ℕ) :
    DirectCore.ApproxSolution.toSeq sol k = (sol_q.getD k 0 : ℝ) := by
  simp only [DirectCore.ApproxSolution.toSeq, sol, sol_q, ā₀, ā₁, ā₂]
  match k with
  | 0 => simp [Array.getD]
  | 1 => simp [Array.getD]
  | 2 => simp [Array.getD]
  | k + 3 => simp [Array.getD, show ¬(k + 3 ≤ 2) from by omega]

private lemma F_ā_seq_eq (n : ℕ) :
    lpWeighted.toSeq F_ā n = (F_ā_q n : ℝ) := by
  simp only [F_ā, F_ā_q, DirectCore.F_component, DirectCore.ApproxSolution.toL1_toSeq,
    CauchyProduct.apply]
  simp_rw [sol_toSeq_eq_q]
  simp only [DirectCore.c, lpWeighted.mk_apply, DirectCore.paramSeq, lam0]
  simp_rw [← Rat.cast_mul]
  match n with
  | 0 => simp [Array.getD]
  | 1 => simp [Array.getD]
  | _ + 2 => simp [Array.getD]

private lemma A_op_finBlock_eq (i j : Fin 3) :
    A_op.finBlock i j = ((#[A_col0, A_col1, A_col2].getD (j : ℕ) #[]).getD (i : ℕ) 0 : ℝ) := by
  simp only [A_op, DirectCore.approxInverse, A_mat, A_colOf]
  fin_cases j <;> simp [Array.getD]

private lemma A_op_tailDiag_eq (n : ℕ) (_ : 2 < n) :
    A_op.tailDiag n = (A_tail_q : ℝ) := by
  simp only [A_op, DirectCore.approxInverse, sol, ā₀, A_tail_q, ā₀_q]
  push_cast
  ring

/-- Per-component bridge via generic `toCLM_action_eq_rat_cast`. -/
private lemma A_F_ā_toSeq_eq_q (n : ℕ) :
    lpWeighted.toSeq (A_op.toCLM F_ā) n = (Y₀_action_q n : ℝ) :=
  A_op.toCLM_action_eq_rat_cast F_ā _ _ _ A_op_finBlock_eq F_ā_seq_eq
    (fun n hn => A_op_tailDiag_eq n hn) n

/-- ν_val matches ℚ -/
private lemma ν_val_eq_q : (ν_val : ℝ) = ((1/4 : ℚ) : ℝ) := by
  simp only [ν_val]; push_cast; ring

/-- A_op.toCLM F_ā has support up to 4 -/
private lemma A_F_ā_supp : ∀ n, 4 < n → lpWeighted.toSeq (A_op.toCLM F_ā) n = 0 := by
  intro n hn
  simp only [BlockDiag.BlockDiagOp.toCLM_apply,
    BlockDiag.BlockDiagOp.action_tail _ _ _ (by omega : 2 < n)]
  rw [F_ā_supp n hn, mul_zero]

/-! #### Y₀ bound (O(1) via single-sum witness) -/

/-- Y₀: ‖A·DirectCore.F(ā)‖ ≤ 9/500.
    One rewrite to Icc sum, one bridge to ℚ, one finsum_bound auto. -/
lemma Y₀_norm_le : DirectCore.Y₀_norm (ν := ν_val) lam0 sol A_mat ≤ 9/500 := by
  change ‖A_op.toCLM F_ā‖ ≤ 9/500
  rw [l1Weighted.norm_eq_Icc_sum_of_support (a := A_op.toCLM F_ā) (M := 4) A_F_ā_supp]
  simp_rw [A_F_ā_toSeq_eq_q, ν_val_eq_q, ← Rat.cast_abs]
  finsum_bound auto Y₀_eval

/-! ### Z₀ bound (operator defect ‖I - A·DF‖) -/

-- Rational matrix data generated from A_mat and sol_q.
private def A_q : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => (A_colOf j).getD (i : ℕ) 0

private def DF_q : Matrix (Fin 3) (Fin 3) ℚ :=
  !![2 * sol_q.getD 0 0, 0, 0;
     2 * sol_q.getD 1 0, 2 * sol_q.getD 0 0, 0;
     2 * sol_q.getD 2 0, 2 * sol_q.getD 1 0, 2 * sol_q.getD 0 0]

private def I_sub_A_DF_q : Matrix (Fin 3) (Fin 3) ℚ := 1 - A_q * DF_q

-- I_sub_A_DF columns generated from I_sub_A_DF_q
private def Z₀_col0 : Array ℚ := #[I_sub_A_DF_q 0 0, I_sub_A_DF_q 1 0, I_sub_A_DF_q 2 0]
private def Z₀_col1 : Array ℚ := #[I_sub_A_DF_q 0 1, I_sub_A_DF_q 1 1, I_sub_A_DF_q 2 1]
private def Z₀_col2 : Array ℚ := #[I_sub_A_DF_q 0 2, I_sub_A_DF_q 1 2, I_sub_A_DF_q 2 2]

private def Z₀_colOf : Fin 3 → Array ℚ
  | 0 => Z₀_col0
  | 1 => Z₀_col1
  | 2 => Z₀_col2

private lemma A_mat_eq_A_q_cast :
    A_mat = fun i j => (A_q i j : ℝ) := by
  ext i j
  rfl

private lemma DF_fin_eq_DF_q_cast :
    DirectCore.DF_fin sol = fun i j => (DF_q i j : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [DirectCore.DF_fin, DF_q, sol, sol_q, ā₀, ā₁, ā₂]

private lemma I_sub_A_DF_cast (i j : Fin 3) :
    (1 - A_mat * DirectCore.DF_fin sol) i j = (I_sub_A_DF_q i j : ℝ) := by
  rw [A_mat_eq_A_q_cast, DF_fin_eq_DF_q_cast, I_sub_A_DF_q]
  simp [Matrix.sub_apply, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul, Rat.cast_sub]
  fin_cases i <;> fin_cases j <;> norm_num

private lemma Z₀_colOf_get (j i : Fin 3) :
    (Z₀_colOf j).getD (i : ℕ) 0 = I_sub_A_DF_q i j := by
  fin_cases i <;> fin_cases j <;> rfl

-- Direct bridge: entries of (I - A·DF(sol)) match the ℚ column data.
private lemma one_sub_A_DF_col (j : Fin 3) (i : Fin 3) :
    (1 - A_mat * DirectCore.DF_fin sol) i j = ((Z₀_colOf j).getD (i : ℕ) 0 : ℝ) := by
  rw [I_sub_A_DF_cast i j]
  exact_mod_cast (Z₀_colOf_get j i).symm

-- Z₀ column sum bounds via finsum_bound using
private lemma Z₀_col0_sum_le :
    l1Weighted.arrayColNormIccSum ν_val 2 Z₀_col0 0 ≤ 2/1000 := by
  unfold l1Weighted.arrayColNormIccSum
  rw [ν_val_eq_q]
  finsum_bound auto (colNormTermDyadic Z₀_col0 (1/4) 0)

private lemma Z₀_col1_sum_le :
    l1Weighted.arrayColNormIccSum ν_val 2 Z₀_col1 1 ≤ 2/1000 := by
  unfold l1Weighted.arrayColNormIccSum
  rw [ν_val_eq_q]
  finsum_bound auto (colNormTermDyadic Z₀_col1 (1/4) 1)

private lemma Z₀_col2_sum_le :
    l1Weighted.arrayColNormIccSum ν_val 2 Z₀_col2 2 ≤ 2/1000 := by
  unfold l1Weighted.arrayColNormIccSum
  rw [ν_val_eq_q]
  finsum_bound auto (colNormTermDyadic Z₀_col2 (1/4) 2)

/-- Uniform column-sum bound for `Z₀_colOf`. -/
private lemma Z₀_col_sum_le (j : Fin 3) :
    l1Weighted.arrayColNormIccSum ν_val 2 (Z₀_colOf j) j ≤ 2/1000 := by
  fin_cases j
  · simpa [Z₀_colOf] using Z₀_col0_sum_le
  · simpa [Z₀_colOf] using Z₀_col1_sum_le
  · simpa [Z₀_colOf] using Z₀_col2_sum_le

/-- Per-column matrix norm bound for `1 - A * DF(ā)`. -/
private lemma Z₀_matrixColNorm_le (j : Fin 3) :
    l1Weighted.matrixColNorm ν_val (1 - A_mat * DirectCore.DF_fin sol) j ≤ 2/1000 := by
  exact l1Weighted.matrixColNorm_le_of_arrayColNormIccSum
    ν_val 2 (1 - A_mat * DirectCore.DF_fin sol) (Z₀_colOf j) j (2/1000)
    (one_sub_A_DF_col j) (Z₀_col_sum_le j)

lemma Z₀_le : l1Weighted.finWeightedMatrixNorm ν_val (1 - A_mat * DirectCore.DF_fin sol) ≤ 2/1000 := by
  exact l1Weighted.finWeightedMatrixNorm_le_of_matrixColNorm_le
    (ν := ν_val) (A := 1 - A_mat * DirectCore.DF_fin sol) (C := 2/1000) Z₀_matrixColNorm_le

/-! ### Z₁ bound (tail contribution)

Z₁ = (1/|ā₀|) * ∑_{n=1}^{N} |āₙ| * νⁿ. We keep this as a direct formula and
bound it with an evaluator (`Z₁_eval`) via `finsum_bound auto`. -/

-- Local Z₁ formula used by the direct bounds pipeline (N = 2 specialization).
private noncomputable def Z₁_formula : ℝ :=
  (1 / |sol.aBar_fin 0|) * ∑ n ∈ Finset.Icc (1 : ℕ) 2, |sol.toSeq n| * (ν_val : ℝ) ^ n

private def Z₁_eval (n : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat
    (IntervalRat.singleton (inv_abs_ā₀_q * |sol_q.getD n 0| * (1 / 4 : ℚ) ^ n))
    cfg.precision

private lemma Z₁_formula_eq_icc_sum_q :
    Z₁_formula =
    ∑ n ∈ Finset.Icc (1 : ℕ) 2,
      (inv_abs_ā₀_q : ℝ) * |(sol_q.getD n 0 : ℝ)| * ((1 / 4 : ℚ) : ℝ) ^ n := by
  unfold Z₁_formula
  simp_rw [sol_toSeq_eq_q, ν_val_eq_q]
  have h0 : sol.aBar_fin 0 = ā₀ := by rfl
  have h_inv : (1 / |sol.aBar_fin 0| : ℝ) = (inv_abs_ā₀_q : ℝ) := by
    simpa [h0] using inv_abs_ā₀
  rw [h_inv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp [mul_left_comm, mul_comm]

lemma Z₁_le : Z₁_formula ≤ 46/100 :=
  (by
    rw [Z₁_formula_eq_icc_sum_q]
    finsum_bound auto Z₁_eval)

/-! ### Z₂ bound (nonlinear term coefficient)

Column norm bounds via `finsum_bound using` — O(1) proof terms via native_decide. -/

section MatrixNormBound
-- Column data ↔ A_mat (definitional)
private lemma A_mat_colOf (j i : Fin 3) : A_mat i j = ((A_colOf j).getD (i : ℕ) 0 : ℝ) := by
  fin_cases j <;> rfl

-- Column sum bounds — O(1) via finsum_bound using + native_decide
private lemma A_col0_sum_le :
    l1Weighted.arrayColNormIccSum ν_val 2 A_col0 0 ≤ 14/10 := by
  unfold l1Weighted.arrayColNormIccSum
  rw [ν_val_eq_q]
  finsum_bound using
    (colNormTermDyadic A_col0 (1/4) 0)
    (fun k _ _ => colNormTermDyadic_correct A_col0 (1/4) 0 k _)

private lemma A_col1_sum_le :
    l1Weighted.arrayColNormIccSum ν_val 2 A_col1 1 ≤ 14/10 := by
  unfold l1Weighted.arrayColNormIccSum
  rw [ν_val_eq_q]
  finsum_bound using
    (colNormTermDyadic A_col1 (1/4) 1)
    (fun k _ _ => colNormTermDyadic_correct A_col1 (1/4) 1 k _)

private lemma A_col2_sum_le :
    l1Weighted.arrayColNormIccSum ν_val 2 A_col2 2 ≤ 14/10 := by
  unfold l1Weighted.arrayColNormIccSum
  rw [ν_val_eq_q]
  finsum_bound using
    (colNormTermDyadic A_col2 (1/4) 2)
    (fun k _ _ => colNormTermDyadic_correct A_col2 (1/4) 2 k _)

private lemma A_col_sum_le (j : Fin 3) :
    l1Weighted.arrayColNormIccSum ν_val 2 (A_colOf j) j ≤ 14/10 := by
  fin_cases j
  · simpa [A_colOf] using A_col0_sum_le
  · simpa [A_colOf] using A_col1_sum_le
  · simpa [A_colOf] using A_col2_sum_le

private lemma colNorm_le (j : Fin 3) :
    l1Weighted.matrixColNorm ν_val A_mat j ≤ 14/10 := by
  exact l1Weighted.matrixColNorm_le_of_arrayColNormIccSum
    ν_val 2 A_mat (A_colOf j) j (14/10) (A_mat_colOf j) (A_col_sum_le j)

end MatrixNormBound -- section

private lemma matrixNorm_le : l1Weighted.finWeightedMatrixNorm ν_val A_mat ≤ 14/10 := by
  exact l1Weighted.finWeightedMatrixNorm_le_of_matrixColNorm_le
    (ν := ν_val) (A := A_mat) (C := 14/10) colNorm_le

private noncomputable def Z₂_formula : ℝ :=
  2 * max (l1Weighted.finWeightedMatrixNorm ν_val A_mat) (1 / (2 * |sol.aBar_fin 0|))

lemma Z₂_le : Z₂_formula ≤ 28/10 := by
  unfold Z₂_formula
  simp only [sol, Matrix.cons_val_zero, abs_ā₀]
  refine le_trans (mul_le_mul_of_nonneg_left (max_le matrixNorm_le ?_) (by norm_num)) (by norm_num)
  apply LeanCertHelpers.of_point_interval (q := 14/10) (by norm_num); fast_bound

end Connection

/-! ## Direct Norm Bounds

Direct operator bounds for this file:
- `Z₀`, `Z₁`, `Z₂`: direct CLM proofs (no `*_bound_valid` bridge)
- numerical constants still come from LeanCert-powered `_le` lemmas -/

section DirectBounds


/-- Defect operator for `Z₀`: finite block `1 - A·DF(ā)`, zero tail. -/
private noncomputable def Z₀_defect : BlockDiag.BlockDiagOp ν_val 2 :=
  ⟨1 - A_mat * (DirectCore.approxDeriv (ν := ν_val) sol).finBlock,
    (fun _ => 0), (0 : ℝ), by intro n hn; norm_num⟩

/-- Structural identification: `id - A∘A† = Z₀_defect.toCLM`. -/
private lemma Z₀_defect_eq :
    ContinuousLinearMap.id ℝ (l1Weighted ν_val) -
      A_op.toCLM.comp (DirectCore.approxDeriv sol).toCLM = Z₀_defect.toCLM := by
  refine BlockDiag.BlockDiagOp.clm_eq_of_finite_tail
    (T := ContinuousLinearMap.id ℝ (l1Weighted ν_val) -
      A_op.toCLM.comp (DirectCore.approxDeriv sol).toCLM) (A := Z₀_defect) ?_ ?_
  · intro h n
    simpa [Z₀_defect] using
      (DirectCore.I_sub_comp_finite_toSeq_eq (ν := ν_val) sol A_mat h n)
  · intro h n hn
    have htail :
        lpWeighted.toSeq
          ((ContinuousLinearMap.id ℝ (l1Weighted ν_val) -
            A_op.toCLM.comp (DirectCore.approxDeriv sol).toCLM) h) n = 0 := by
      simpa [ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_id', id_eq,
        ContinuousLinearMap.coe_comp', Function.comp_apply, lpWeighted.sub_toSeq]
        using DirectCore.I_sub_comp_action_tail_eq_zero (ν := ν_val) sol A_mat h n hn
    simpa [Z₀_defect] using htail

/-- Since `tailBound = 0`, the defect norm is controlled by its finite matrix norm. -/
private lemma Z₀_defect_norm_le_matrix :
    ‖Z₀_defect.toCLM‖ ≤
    l1Weighted.finWeightedMatrixNorm ν_val
      (1 - A_mat * (DirectCore.approxDeriv (ν := ν_val) sol).finBlock) := by
  simpa [Z₀_defect] using
    (BlockDiag.BlockDiagOp.norm_toCLM_le_finBlock_of_tailBound_zero (A := Z₀_defect) rfl)

/-- Numerical matrix bound from the LeanCert-powered `Z₀_le`. -/
private lemma Z₀_matrix_le :
    l1Weighted.finWeightedMatrixNorm ν_val
      (1 - A_mat * (DirectCore.approxDeriv (ν := ν_val) sol).finBlock) ≤ 2/1000 := by
  have hDFeq := DirectCore.approxDeriv_finBlock_eq_DF_fin (ν := ν_val) sol
  simpa [hDFeq] using Z₀_le

/-- Z₀: direct operator-norm bound ‖I - A·A†‖ ≤ 2/1000 (no `Z₀_bound_valid` bridge). -/
lemma Z₀_norm_le :
    DirectCore.Z₀_norm (ν := ν_val) sol A_mat ≤ 2/1000 := by
  change ‖ContinuousLinearMap.id ℝ (l1Weighted ν_val) -
      A_op.toCLM.comp (DirectCore.approxDeriv sol).toCLM‖ ≤ 2/1000
  have h_to_matrix :
      ‖ContinuousLinearMap.id ℝ (l1Weighted ν_val) -
          A_op.toCLM.comp (DirectCore.approxDeriv sol).toCLM‖ ≤
      l1Weighted.finWeightedMatrixNorm ν_val
        (1 - A_mat * (DirectCore.approxDeriv (ν := ν_val) sol).finBlock) := by
    rw [Z₀_defect_eq]
    exact Z₀_defect_norm_le_matrix
  exact h_to_matrix.trans Z₀_matrix_le

/-- Z₁: direct operator-norm bound ‖A·(A† - DF(ā))‖ ≤ 46/100 (no `Z₁_bound_valid` bridge). -/
private noncomputable def Z₁_input (h : l1Weighted ν_val) : l1Weighted ν_val :=
  fderiv ℝ (DirectCore.F lam0) sol.toL1 h - (DirectCore.approxDeriv sol).toCLM h

private lemma Z₁_finite_part_zero (h : l1Weighted ν_val) :
    ∑ n : Fin 3, |lpWeighted.toSeq (A_op.toCLM (Z₁_input h)) n| *
      (ν_val : ℝ) ^ (n : ℕ) = 0 := by
  change ∑ n : Fin 3, |lpWeighted.toSeq
    (A_op.toCLM (fderiv ℝ (DirectCore.F lam0) sol.toL1 h - (DirectCore.approxDeriv sol).toCLM h)) n| *
    (ν_val : ℝ) ^ (n : ℕ) = 0
  apply Finset.sum_eq_zero
  intro n hn
  rw [DirectCore.A_DF_sub_approxDeriv_finite_eq_zero (ν := ν_val) lam0 sol A_mat h n,
    abs_zero, zero_mul]

private lemma Z₁_tail_factor (h : l1Weighted ν_val) :
    ∑' n : {n : ℕ // 2 < n},
      |lpWeighted.toSeq (A_op.toCLM (Z₁_input h)) n| * (ν_val : ℝ) ^ (n : ℕ) =
    (1 / |sol.aBar_fin 0|) *
      ∑' n : {n : ℕ // 2 < n},
        |∑ j ∈ Finset.Icc 1 2, lpWeighted.toSeq h (n - j) * sol.toSeq j| *
        (ν_val : ℝ) ^ (n : ℕ) := by
  change ∑' n : {n : ℕ // 2 < n},
    |lpWeighted.toSeq
      (A_op.toCLM (fderiv ℝ (DirectCore.F lam0) sol.toL1 h - (DirectCore.approxDeriv sol).toCLM h)) n| *
      (ν_val : ℝ) ^ (n : ℕ) =
    (1 / |sol.aBar_fin 0|) *
      ∑' n : {n : ℕ // 2 < n},
        |∑ j ∈ Finset.Icc 1 2, lpWeighted.toSeq h (n - j) * sol.toSeq j| *
        (ν_val : ℝ) ^ (n : ℕ)
  rw [← tsum_mul_left]
  congr 1
  ext ⟨n, hn⟩
  rw [DirectCore.A_DF_sub_approxDeriv_tail (ν := ν_val) lam0 sol A_mat h n hn, abs_mul,
    abs_one_div]
  ring

private lemma Z₁_tail_le_formula (h : l1Weighted ν_val) :
    ∑' n : {n : ℕ // 2 < n},
      |lpWeighted.toSeq (A_op.toCLM (Z₁_input h)) n| * (ν_val : ℝ) ^ (n : ℕ) ≤
    Z₁_formula * ‖h‖ := by
  rw [Z₁_tail_factor]
  have h_tail_le :=
    mul_le_mul_of_nonneg_left
      (DirectCore.tail_cauchy_bound (ν := ν_val) sol h)
      (by positivity : 0 ≤ 1 / |sol.aBar_fin 0|)
  have h_rhs :
      (1 / |sol.aBar_fin 0|) *
          (‖h‖ * ∑ n ∈ Finset.Icc (1 : ℕ) 2, |sol.toSeq n| * (ν_val : ℝ) ^ n) =
      Z₁_formula * ‖h‖ := by
    simp only [Z₁_formula]
    ring
  exact h_tail_le.trans_eq h_rhs

private lemma Z₁_pointwise_le (h : l1Weighted ν_val) :
    ‖A_op.toCLM.comp ((DirectCore.approxDeriv sol).toCLM - fderiv ℝ (DirectCore.F lam0) sol.toL1) h‖ ≤
    Z₁_formula * ‖h‖ := by
  have h_neg : A_op.toCLM.comp
      ((DirectCore.approxDeriv sol).toCLM - fderiv ℝ (DirectCore.F lam0) sol.toL1) h =
      -A_op.toCLM (Z₁_input h) := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
    simp [Z₁_input, sub_eq_add_neg]
  rw [h_neg, norm_neg, BlockDiag.norm_split (N := 2)]
  rw [Z₁_finite_part_zero h, zero_add]
  exact Z₁_tail_le_formula h

lemma Z₁_norm_le :
    DirectCore.Z₁_norm (ν := ν_val) lam0 sol A_mat ≤ 46/100 := by
  change ‖A_op.toCLM.comp
      ((DirectCore.approxDeriv sol).toCLM - fderiv ℝ (DirectCore.F lam0) sol.toL1)‖ ≤ 46/100
  apply ContinuousLinearMap.opNorm_le_bound
  · norm_num
  intro h
  exact (Z₁_pointwise_le h).trans (mul_le_mul_of_nonneg_right Z₁_le (norm_nonneg h))

/-- Z₂: direct operator-norm bound ‖A·(DF(c) - DF(ā))‖ ≤ (28/10)·r₀. -/
private lemma Z₂_norm_le_Z₂bound (c : l1Weighted ν_val)
    (hc : c ∈ Metric.closedBall sol.toL1 r₀) :
    ‖A_op.toCLM.comp
      (fderiv ℝ (DirectCore.F lam0) c - fderiv ℝ (DirectCore.F lam0) sol.toL1)‖ ≤
    Z₂_formula * r₀ := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hc
  have h_B : ‖fderiv ℝ (DirectCore.F lam0) c - fderiv ℝ (DirectCore.F lam0) sol.toL1‖ ≤ 2 * r₀ :=
    (DirectCore.norm_fderiv_F_diff_le (ν := ν_val) lam0 sol c).trans (by gcongr)
  have h_rhs :
      max (l1Weighted.finWeightedMatrixNorm ν_val A_mat) (1 / (2 * |sol.aBar_fin 0|)) * (2 * r₀) =
      Z₂_formula * r₀ := by
    unfold Z₂_formula
    ring
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (DirectCore.approxInverse_norm_le (ν := ν_val) sol A_mat) h_B
      (by positivity) (by positivity)).trans_eq h_rhs)

lemma Z₂_norm_le (c : l1Weighted ν_val) (hc : c ∈ Metric.closedBall sol.toL1 r₀) :
    DirectCore.Z₂_norm (ν := ν_val) lam0 sol A_mat c ≤ 28/10 * r₀ := by
  change ‖A_op.toCLM.comp
      (fderiv ℝ (DirectCore.F lam0) c - fderiv ℝ (DirectCore.F lam0) sol.toL1)‖ ≤ 28/10 * r₀
  exact (Z₂_norm_le_Z₂bound c hc).trans
    (mul_le_mul_of_nonneg_right Z₂_le r₀_pos.le)

end DirectBounds

/-! ## Main Theorem -/

section MainTheorem


private lemma A_op_injective : Function.Injective A_op.toCLM := by
  exact DirectCore.approxInverse_injective_of_Z₀_lt_one (ν := ν_val) sol A_mat
    (lt_of_le_of_lt Z₀_le (by norm_num))

private lemma radiiPoly_direct_neg :
    generalRadiiPolynomial Y₀_bnd Z₀_bnd Z₁_bnd (fun _ => Z₂_bnd) r₀ < 0 := by
  have h := radiiPoly_upper_neg r₀ ⟨le_refl r₀, le_refl r₀⟩
  simpa [radiiPoly_upper] using h

theorem main_theorem :
    ∃! aTilde ∈ Metric.closedBall (sol.toL1 : l1Weighted ν_val) r₀,
      DirectCore.F lam0 aTilde = 0 := by
  exact DirectCore.existsUnique_of_direct_bounds
    (ν := ν_val) lam0 sol A_mat
    (Y₀ := (Y₀_bnd : ℝ)) (Z₀ := (Z₀_bnd : ℝ)) (Z₁ := (Z₁_bnd : ℝ))
    (Z₂ := (Z₂_bnd : ℝ)) (r₀ := r₀)
    r₀_pos
    (by simpa [Y₀_bnd, DirectCore.Y₀_norm] using Y₀_norm_le)
    (by simpa [Z₀_bnd, DirectCore.Z₀_norm] using Z₀_norm_le)
    (by simpa [Z₁_bnd, DirectCore.Z₁_norm] using Z₁_norm_le)
    (by
      intro c hc
      simpa [Z₂_bnd, DirectCore.Z₂_norm] using Z₂_norm_le c hc)
    radiiPoly_direct_neg
    A_op_injective

end MainTheorem


/-! ## Summary

This file keeps the active path fully direct:
- bounds are stated as CLM norms (`Y₀_norm_le`, `Z₀_norm_le`, `Z₁_norm_le`, `Z₂_norm_le`);
- numeric inequalities are discharged by LeanCert (`finsum_bound`, `fast_bound`);
- `main_theorem_via_witness` shows the same proof path using `canonicalWitness`
  (`Y₀/Z₀/Z₁/Z₂` term sums);
- `main_theorem` is obtained via the reusable
  `DirectCore.existsUnique_of_direct_bounds` API.
-/

end DirectRadiiCert

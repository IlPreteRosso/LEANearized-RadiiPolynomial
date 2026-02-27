import RadiiPolynomial.SystemTaylorODE.SystemTaylorODE

/-!
# Example 7.7 Numerical Verification (SystemTaylorODE)

This module encodes the scalar equation from Section 7.7,
`x(λ)^2 - λ = 0`, in the `SystemTaylorODE` API and assembles
the numerical witness layer for the fixed Example 7.7 caps.

Scope of this file:
- ODE-side objects (`c`, `F`, approximate center `xBar`)
- fixed rational caps (`Y₀`, `Z₀`, `Z₁`, `Z₂`, `r₀`)
- existence theorem via `ScalarBlockDiagData.existsUnique_of_scalar_bounds`

It does not import `TaylorODE_Direct` certificate files.
-/

noncomputable section

namespace SystemTaylorODE
namespace Examples
namespace Example77

/-- Weight used in the Example 7.7 certificate (`ν = 1/4`). -/
def ν_val : PosReal := ⟨1 / 4, by norm_num⟩

/-- Expansion parameter center (`λ₀ = 1/3`). -/
def lam0 : ℝ := 1 / 3

/-- Rational approximate coefficients from Example 7.7 (`N = 2`). -/
def ā₀_q : ℚ := 5774 / 10000
def ā₁_q : ℚ := 8660 / 10000
def ā₂_q : ℚ := -6495 / 10000

/-- Real casts of the approximate coefficients. -/
def ā₀ : ℝ := (ā₀_q : ℝ)
def ā₁ : ℝ := (ā₁_q : ℝ)
def ā₂ : ℝ := (ā₂_q : ℝ)

/-- Zero-padded approximate Taylor coefficients. -/
def aBarSeq (n : ℕ) : ℝ :=
  match n with
  | 0 => (ā₀_q : ℝ)
  | 1 => (ā₁_q : ℝ)
  | 2 => (ā₂_q : ℝ)
  | _ => 0

lemma aBarSeq_mem : lpWeighted.Mem ν_val 1 aBarSeq := by
  rw [l1Weighted.mem_iff]
  refine summable_of_ne_finset_zero (s := ({0, 1, 2} : Finset ℕ)) ?_
  intro n hn
  have hn0 : n ≠ 0 := by
    intro h
    exact hn (by simp [h])
  have hn1 : n ≠ 1 := by
    intro h
    exact hn (by simp [h])
  have hn2 : n ≠ 2 := by
    intro h
    exact hn (by simp [h])
  have hseq : aBarSeq n = 0 := by
    cases n with
    | zero => exact (hn0 rfl).elim
    | succ n =>
        cases n with
        | zero => exact (hn1 rfl).elim
        | succ n =>
            cases n with
            | zero => exact (hn2 rfl).elim
            | succ n => rfl
  simp [hseq]

/-- Approximate center `x̄ ∈ ℓ¹_ν` (Section 7.7, step 2). -/
def xBar : l1Weighted ν_val := lpWeighted.mk aBarSeq aBarSeq_mem

/-- Constant sequence `c = (λ₀, 1, 0, 0, ...)` from (7.44). -/
def paramSeq (lam0 : ℝ) : ℕ → ℝ := fun n =>
  match n with
  | 0 => lam0
  | 1 => 1
  | _ => 0

lemma paramSeq_mem (lam0 : ℝ) : lpWeighted.Mem ν_val 1 (paramSeq lam0) := by
  rw [l1Weighted.mem_iff]
  refine summable_of_ne_finset_zero (s := ({0, 1} : Finset ℕ)) ?_
  intro n hn
  have hn0 : n ≠ 0 := by
    intro h
    exact hn (by simp [h])
  have hn1 : n ≠ 1 := by
    intro h
    exact hn (by simp [h])
  have hseq : paramSeq lam0 n = 0 := by
    cases n with
    | zero => exact (hn0 rfl).elim
    | succ n =>
        cases n with
        | zero => exact (hn1 rfl).elim
        | succ n => rfl
  simp [hseq]

/-- `c` as an element of `ℓ¹_ν`. -/
def c (lam0 : ℝ) : l1Weighted ν_val := lpWeighted.mk (paramSeq lam0) (paramSeq_mem lam0)

/-- Zero-finding map from (7.43): `F(a) = a*a - c`. -/
def F (lam0 : ℝ) (a : l1Weighted ν_val) : l1Weighted ν_val := a * a - c lam0

/-! ## Approximate Operators (Concrete 7.7 Data)

We fix the block-diagonal operators from the 7.7 numerical setup:
- `A`: approximate inverse
- `A†`: approximate derivative surrogate
-/

/-- Finite block `A^(N)` (`N=2`) from the Example 7.7 numerics. -/
def A_fin : Matrix (Fin 3) (Fin 3) ℝ :=
  !![ā₁, 0, 0;
     -12990 / 10000, ā₁, 0;
      29240 / 10000, -12990 / 10000, ā₁]

/-- Finite derivative block `DF^(N)(x̄)` (`N=2`). -/
def A_dagger_fin : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2 * ā₀, 0, 0;
     2 * ā₁, 2 * ā₀, 0;
     2 * ā₂, 2 * ā₁, 2 * ā₀]

/-- Tail scalar for `A`: `1/(2ā₀)`. -/
def A_tail : ℝ := 1 / (2 * ā₀)

/-- Tail scalar for `A†`: `2ā₀`. -/
def A_dagger_tail : ℝ := 2 * ā₀

/-- Scalar block-diagonal data for the approximate inverse `A`. -/
def A_data : ScalarBlockDiagData 2 :=
  ScalarBlockDiagData.ofParts (N := 2)
    A_fin
    (fun _ => A_tail)
    |A_tail|
    (by intro n hn; exact le_rfl)

/-- Scalar block-diagonal data for the approximate derivative surrogate `A†`. -/
def A_dagger_data : ScalarBlockDiagData 2 :=
  ScalarBlockDiagData.ofParts (N := 2)
    A_dagger_fin
    (fun _ => A_dagger_tail)
    |A_dagger_tail|
    (by intro n hn; exact le_rfl)

/-- Concrete CLM `A : ℓ¹_ν →L ℓ¹_ν` used in the numerical certificate. -/
noncomputable def Aop : l1Weighted ν_val →L[ℝ] l1Weighted ν_val :=
  A_data.toScalarCLM (ν := ν_val)

/-- Concrete CLM `A† : ℓ¹_ν →L ℓ¹_ν` used in the numerical certificate. -/
noncomputable def AopDagger : l1Weighted ν_val →L[ℝ] l1Weighted ν_val :=
  A_dagger_data.toScalarCLM (ν := ν_val)

/-- Example 7.7 numeric cap for `Y₀`. -/
def Y₀_bnd : ℚ := 9 / 500

/-- Example 7.7 numeric cap for `Z₀`. -/
def Z₀_bnd : ℚ := 2 / 1000

/-- Example 7.7 numeric cap for `Z₁`. -/
def Z₁_bnd : ℚ := 46 / 100

/-- Example 7.7 numeric cap for `Z₂`. -/
def Z₂_bnd : ℚ := 28 / 10

/-- Example 7.7 radius candidate. -/
noncomputable def r₀ : ℝ := 996 / 10000

/-- Upper radii polynomial built from fixed Example 7.7 caps. -/
noncomputable def radiiPoly_upper (r : ℝ) : ℝ :=
  generalRadiiPolynomial Y₀_bnd Z₀_bnd Z₁_bnd (fun _ => Z₂_bnd) r

/-- Certified negativity of the fixed upper polynomial at `r₀`. -/
theorem radiiPoly_upper_neg_at_r₀ :
    generalRadiiPolynomial (Y₀_bnd : ℝ) (Z₀_bnd : ℝ) (Z₁_bnd : ℝ)
      (fun _ => (Z₂_bnd : ℝ)) r₀ < 0 := by
  unfold generalRadiiPolynomial r₀ Y₀_bnd Z₀_bnd Z₁_bnd Z₂_bnd
  norm_num

/-- Canonical scalar `Y₀` for this Example 7.7 setup: `‖A(F(x̄))‖`. -/
noncomputable def Y₀_exact : ℝ := ‖Aop (F lam0 xBar)‖

/-- Canonical scalar `Z₀` for this Example 7.7 setup: `‖I - A∘A†‖`. -/
noncomputable def Z₀_exact : ℝ :=
  ‖ContinuousLinearMap.id ℝ (l1Weighted ν_val) - Aop.comp AopDagger‖

/-- Canonical scalar `Z₁` for this Example 7.7 setup: `‖A∘(A† - DF(x̄))‖`. -/
noncomputable def Z₁_exact : ℝ :=
  ‖Aop.comp (AopDagger - fderiv ℝ (F lam0) xBar)‖

/-- Canonical scalar `Z₂(c)` for this Example 7.7 setup: `‖A∘(DF(c) - DF(x̄))‖`. -/
noncomputable def Z₂_exact (c : l1Weighted ν_val) : ℝ :=
  ‖Aop.comp (fderiv ℝ (F lam0) c - fderiv ℝ (F lam0) xBar)‖

section ExistenceTheorem

/-- Differentiability of the scalar Example 7.7 map `F(a) = a*a - c`. -/
theorem differentiable_F : Differentiable ℝ (F lam0) := by
  change Differentiable ℝ (fun a : l1Weighted ν_val => a * a - c lam0)
  exact (differentiable_id.mul differentiable_id).sub_const (c lam0)

/-- Tail diagonal of `A_data` is nonzero on the tail (in fact constant nonzero). -/
lemma A_data_tail_nonzero : ∀ n, 2 < n → A_data.tailDiag0 n ≠ 0 := by
  intro n _
  have htail_eval : A_data.tailDiag0 n = A_tail := by
    simp [A_data, ScalarBlockDiagData.tailDiag0, ScalarBlockDiagData.ofParts]
  rw [htail_eval]
  unfold A_tail
  have hā₀ : ā₀ ≠ 0 := by
    norm_num [ā₀, ā₀_q]
  have hden : 2 * ā₀ ≠ 0 := by
    exact mul_ne_zero (by norm_num) hā₀
  simpa [one_div] using inv_ne_zero hden

private def A_q : Matrix (Fin 3) (Fin 3) ℚ :=
  !![ā₁_q, 0, 0;
     -12990 / 10000, ā₁_q, 0;
      29240 / 10000, -12990 / 10000, ā₁_q]

private def A_dagger_q : Matrix (Fin 3) (Fin 3) ℚ :=
  !![2 * ā₀_q, 0, 0;
     2 * ā₁_q, 2 * ā₀_q, 0;
     2 * ā₂_q, 2 * ā₁_q, 2 * ā₀_q]

private def I_sub_A_DF_q : Matrix (Fin 3) (Fin 3) ℚ := 1 - A_q * A_dagger_q

private def Z₀_col0 : Array ℚ := #[I_sub_A_DF_q 0 0, I_sub_A_DF_q 1 0, I_sub_A_DF_q 2 0]
private def Z₀_col1 : Array ℚ := #[I_sub_A_DF_q 0 1, I_sub_A_DF_q 1 1, I_sub_A_DF_q 2 1]
private def Z₀_col2 : Array ℚ := #[I_sub_A_DF_q 0 2, I_sub_A_DF_q 1 2, I_sub_A_DF_q 2 2]

private def Z₀_colOf : Fin 3 → Array ℚ
  | 0 => Z₀_col0
  | 1 => Z₀_col1
  | 2 => Z₀_col2

private lemma A_fin_eq_A_q_cast :
    A_fin = fun i j => (A_q i j : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A_fin, A_q, ā₁, ā₁_q]

private lemma A_dagger_fin_eq_A_dagger_q_cast :
    A_dagger_fin = fun i j => (A_dagger_q i j : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A_dagger_fin, A_dagger_q, ā₀, ā₀_q, ā₁, ā₁_q, ā₂, ā₂_q]

private lemma I_sub_A_DF_cast (i j : Fin 3) :
    (1 - A_fin * A_dagger_fin) i j = (I_sub_A_DF_q i j : ℝ) := by
  rw [A_fin_eq_A_q_cast, A_dagger_fin_eq_A_dagger_q_cast, I_sub_A_DF_q]
  simp [Matrix.sub_apply, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul, Rat.cast_sub]
  fin_cases i <;> fin_cases j <;> norm_num [ā₀, ā₀_q, ā₁, ā₁_q, ā₂, ā₂_q]

private lemma Z₀_colOf_get (j i : Fin 3) :
    (Z₀_colOf j).getD (i : ℕ) 0 = I_sub_A_DF_q i j := by
  fin_cases i <;> fin_cases j <;> rfl

private lemma one_sub_A_DF_col (j : Fin 3) (i : Fin 3) :
    (1 - A_fin * A_dagger_fin) i j = ((Z₀_colOf j).getD (i : ℕ) 0 : ℝ) := by
  rw [I_sub_A_DF_cast i j]
  exact_mod_cast (Z₀_colOf_get j i).symm

private lemma Z₀_col0_sum_le :
    l1Weighted.arrayColNormIccSum ν_val 2 Z₀_col0 0 ≤ 2/1000 := by
  unfold l1Weighted.arrayColNormIccSum Z₀_col0 I_sub_A_DF_q A_q A_dagger_q
  norm_num [ν_val, ā₀_q, ā₁_q, ā₂_q]

private lemma Z₀_col1_sum_le :
    l1Weighted.arrayColNormIccSum ν_val 2 Z₀_col1 1 ≤ 2/1000 := by
  unfold l1Weighted.arrayColNormIccSum Z₀_col1 I_sub_A_DF_q A_q A_dagger_q
  norm_num [ν_val, ā₀_q, ā₁_q, ā₂_q]

private lemma Z₀_col2_sum_le :
    l1Weighted.arrayColNormIccSum ν_val 2 Z₀_col2 2 ≤ 2/1000 := by
  unfold l1Weighted.arrayColNormIccSum Z₀_col2 I_sub_A_DF_q A_q A_dagger_q
  norm_num [ν_val, ā₀_q, ā₁_q, ā₂_q]

private lemma Z₀_col_sum_le (j : Fin 3) :
    l1Weighted.arrayColNormIccSum ν_val 2 (Z₀_colOf j) j ≤ 2/1000 := by
  fin_cases j
  · simpa [Z₀_colOf] using Z₀_col0_sum_le
  · simpa [Z₀_colOf] using Z₀_col1_sum_le
  · simpa [Z₀_colOf] using Z₀_col2_sum_le

private lemma Z₀_matrixColNorm_le (j : Fin 3) :
    l1Weighted.matrixColNorm ν_val (1 - A_fin * A_dagger_fin) j ≤ 2/1000 := by
  exact l1Weighted.matrixColNorm_le_of_arrayColNormIccSum
    ν_val 2 (1 - A_fin * A_dagger_fin) (Z₀_colOf j) j (2/1000)
    (one_sub_A_DF_col j) (Z₀_col_sum_le j)

theorem Z₀_fin_le :
    l1Weighted.finWeightedMatrixNorm ν_val (1 - A_fin * A_dagger_fin) ≤ 2/1000 := by
  exact l1Weighted.finWeightedMatrixNorm_le_of_matrixColNorm_le
    (ν := ν_val) (A := 1 - A_fin * A_dagger_fin) (C := 2/1000) Z₀_matrixColNorm_le

theorem Z₀_fin_lt_one :
    l1Weighted.finWeightedMatrixNorm ν_val (1 - A_fin * A_dagger_fin) < 1 := by
  exact (lt_of_le_of_lt Z₀_fin_le (by norm_num))

/-- Injectivity of `Aop` from the structural finite-block criterion
`‖I - A_fin * A_dagger_fin‖_{1,ν} < 1` (Neumann-style, as in DirectCore). -/
theorem Aop_injective_of_Z₀_fin_lt_one
    (hZ₀_fin_lt_one :
      l1Weighted.finWeightedMatrixNorm ν_val (1 - A_fin * A_dagger_fin) < 1) :
    Function.Injective Aop := by
  unfold Aop
  exact ScalarBlockDiagData.injective_toScalarCLM_of_finBlock_mul_close_to_one
    (ν := ν_val) (N := 2) (A := A_data) (B := A_dagger_fin)
    (by simpa [A_data, ScalarBlockDiagData.finBlock0] using hZ₀_fin_lt_one)
    A_data_tail_nonzero

theorem Aop_injective : Function.Injective Aop :=
  Aop_injective_of_Z₀_fin_lt_one Z₀_fin_lt_one

/-- Main endpoint: provide the four bound lemmas directly and conclude
local existence/uniqueness via `ScalarBlockDiagData.existsUnique_of_scalar_bounds`. -/
theorem main_theorem_of_bounds
    (hY₀ : Y₀_exact ≤ (Y₀_bnd : ℝ))
    (hZ₀ : Z₀_exact ≤ (Z₀_bnd : ℝ))
    (hZ₁ : Z₁_exact ≤ (Z₁_bnd : ℝ))
    (hZ₂ : ∀ c ∈ Metric.closedBall xBar r₀, Z₂_exact c ≤ (Z₂_bnd : ℝ) * r₀) :
    ∃! aTilde ∈ Metric.closedBall xBar r₀, F lam0 aTilde = 0 :=
  ScalarBlockDiagData.existsUnique_of_scalar_bounds A_data A_dagger_data
    (hr₀ := by norm_num [r₀])
    (hY₀ := hY₀)
    (hZ₀ := hZ₀)
    (hZ₁ := hZ₁)
    (hZ₂ := hZ₂)
    (hf_diff := differentiable_F)
    (h_radii := by simpa using radiiPoly_upper_neg_at_r₀)
    (h_inj := Aop_injective)

end ExistenceTheorem

end Example77
end Examples
end SystemTaylorODE

import RadiiPolynomial.TaylorODE_Direct.BlockDiag
import RadiiPolynomial.RadiiPolyGeneral
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Operator Norms for Weighted Sequence Spaces

This file establishes the connection between explicit matrix norm formulas and
abstract operator norms on weighted ℓ¹ spaces.

## Mathematical Background

### Finite-Dimensional Case (Exercise 2.7.2)

For matrices A : ℝ^{N+1} → ℝ^{N+1} acting on the weighted ℓ¹_ν space, the
**induced operator norm** equals the **weighted column-sum formula**:

  ‖A‖_{op} = max_{0≤j≤N} (1/νʲ) Σᵢ |Aᵢⱼ| νⁱ

This is the content of `finWeightedMatrixNorm_eq_opNorm`.

### Infinite-Dimensional Case (Propositions 7.3.13-7.3.14)

For bounded linear operators A : ℓ¹_ω → ℓ¹_ω:

**Proposition 7.3.13**: ‖A‖ ≤ sup_n (1/ωₙ) Σₘ |Aₘₙ| ωₘ

**Proposition 7.3.14 (direct-file model)**: For block-diagonal operators with
finite block `A_N` and tail diagonal `tailDiag : ℕ → ℝ` satisfying
`|tailDiag n| ≤ C` on `n > N`, we have:

  ‖A‖ ≤ max(K, C)

where K = `finWeightedMatrixNorm(A_N)`.

## Main Definitions

- `WeightedPiLp`: Finite-dimensional weighted ℓ¹ space on `Fin (N+1) → ℝ`
- `FinWeightedMatrix.toWeightedCLM`: Matrix as continuous linear map on weighted space
- `BlockDiagOp`: Block-diagonal operator structure for Chapter 7.7

## Main Results

- `finWeightedMatrixNorm_eq_opNorm`: Matrix norm = operator norm (Exercise 2.7.2)
- Block-diagonal operator norm bound is now in `BlockDiag.BlockDiagOp.norm_toCLM_le`

## References

- Exercise 2.7.2: Finite-dimensional weighted norms
- Proposition 7.3.13: General column-norm bound
- Proposition 7.3.14: Block-diagonal operator bound
- Theorem 7.7.1: Application to Taylor series ODE
-/

open scoped BigOperators Topology NNReal ENNReal Matrix
open Metric Set Filter ContinuousLinearMap

noncomputable section

variable {ν : PosReal}

/-! ## Finite-Dimensional Weighted ℓ¹ Space

We construct the finite-dimensional weighted ℓ¹_ν space on `Fin (N+1) → ℝ`.
The norm is: ‖x‖_{1,ν} = Σₙ |xₙ| νⁿ

This can be realized as `PiLp 1 (fun n : Fin (N+1) => ScaledReal ν n)`,
but we also need direct definitions for computing with explicit formulas.
-/

namespace FinWeighted

variable {N : ℕ}

/-- The finite-dimensional weighted ℓ¹ space as PiLp.

    Elements are functions `Fin (N+1) → ℝ` with norm Σₙ |xₙ| νⁿ.

    We use `ScaledReal ν n` as the fiber at index n, which has norm |x| · νⁿ.
    Then PiLp 1 computes the ℓ¹ sum automatically. -/
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

/-- Standard basis vector eⱼ with 1 at position j and 0 elsewhere -/
def stdBasis {ν : PosReal} {N : ℕ} (j : Fin (N + 1)) : Space ν N :=
  WithLp.toLp 1 (fun n => if n = j then (1 : ScaledReal ν n) else 0)

@[simp]
lemma stdBasis_apply_self {ν : PosReal} {N : ℕ} (j : Fin (N + 1)) : stdBasis (ν := ν) j j = 1 := by
  simp [stdBasis]

@[simp]
lemma stdBasis_apply_ne {ν : PosReal} {N : ℕ} (i j : Fin (N + 1)) (h : i ≠ j) : stdBasis (ν := ν) j i = 0 := by
  simp [stdBasis, h]

/-- The norm of a basis vector: ‖eⱼ‖ = νʲ -/
lemma norm_stdBasis {ν : PosReal} {N : ℕ} (j : Fin (N + 1)) : ‖stdBasis (ν := ν) j‖ = (ν : ℝ) ^ (j : ℕ) := by
  rw [norm_eq_sum]
  simp only [stdBasis]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ j) h

end FinWeighted


/-! ## Matrix as Continuous Linear Map on Weighted Space

We define how a matrix A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ acts as a
continuous linear map on the weighted ℓ¹ space.
-/

namespace FinWeightedMatrix

variable {N : ℕ}

/-- Matrix action as a linear map on the weighted space.
    This is the standard matrix action (Ax)ᵢ = Σⱼ Aᵢⱼ xⱼ -/
def mulVecWeightedLinear {ν : PosReal} {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    FinWeighted.Space ν N →ₗ[ℝ] FinWeighted.Space ν N where
  toFun x := WithLp.toLp 1 (fun i => ScaledReal.ofReal (∑ j, A i j * ScaledReal.toReal (x j)))
  map_add' x y := by
    ext i
    simp only [PiLp.add_apply, ScaledReal.toReal_apply, ScaledReal.ofReal_apply]
    rw [← Finset.sum_add_distrib]
    congr 1; ext k; ring
  map_smul' c x := by
    ext i
    simp only [PiLp.smul_apply, ScaledReal.toReal_apply, ScaledReal.ofReal_apply,
               RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1; ext k; ring

/-- Bound on ‖Ax‖ in terms of column norms and ‖x‖.
    This is the key estimate: ‖Ax‖ ≤ (max_j colNorm_j) · ‖x‖
    **Proof outline** (following Proposition 7.3.13):
    ‖Ax‖ = Σᵢ |(Ax)ᵢ| νⁱ
         = Σᵢ |Σⱼ Aᵢⱼ xⱼ| νⁱ
         ≤ Σᵢ Σⱼ |Aᵢⱼ| |xⱼ| νⁱ           [triangle ineq]
         = Σⱼ (Σᵢ |Aᵢⱼ| νⁱ) |xⱼ|         [swap sums]
         = Σⱼ (colNorm_j · νʲ) |xⱼ|       [def of colNorm]
         ≤ (max_j colNorm_j) · Σⱼ |xⱼ| νʲ [factor out max]
         = (max_j colNorm_j) · ‖x‖ -/
lemma mulVecWeightedLinear_norm_le {ν : PosReal} {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (x : FinWeighted.Space ν N) :
    ‖mulVecWeightedLinear A x‖ ≤ l1Weighted.finWeightedMatrixNorm ν A * ‖x‖ := by
  rw [FinWeighted.norm_eq_sum, FinWeighted.norm_eq_sum]
  -- ‖Ax‖ = Σᵢ |(Ax)ᵢ| νⁱ
  calc ∑ i, |ScaledReal.toReal (mulVecWeightedLinear A x i)| * (ν : ℝ) ^ (i : ℕ)
      -- Step 1: Triangle inequality on inner sum
      ≤ ∑ i, (∑ j, |A i j| * |ScaledReal.toReal (x j)|) * (ν : ℝ) ^ (i : ℕ) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (PosReal.coe_nonneg ν) _)
        simp only [mulVecWeightedLinear, LinearMap.coe_mk, AddHom.coe_mk,
                   ScaledReal.toReal, ScaledReal.ofReal]
        calc |∑ j, A i j * ScaledReal.toReal (x j)|
            ≤ ∑ j, |A i j * ScaledReal.toReal (x j)| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j, |A i j| * |ScaledReal.toReal (x j)| := by simp_rw [abs_mul]
    -- Step 2: Distribute νⁱ and swap sums
    _ = ∑ i, ∑ j, |A i j| * |ScaledReal.toReal (x j)| * (ν : ℝ) ^ (i : ℕ) := by
        congr 1; ext i; rw [Finset.sum_mul]
    _ = ∑ j, ∑ i, |A i j| * |ScaledReal.toReal (x j)| * (ν : ℝ) ^ (i : ℕ) := Finset.sum_comm
    _ = ∑ j, |ScaledReal.toReal (x j)| * ∑ i, |A i j| * (ν : ℝ) ^ (i : ℕ) := by
        congr 1; ext j
        rw [Finset.mul_sum]
        congr 1; ext i; ring
    -- Step 3: Express in terms of column norm (via matrixColNorm_mul_pow simp lemma)
    _ = ∑ j, |ScaledReal.toReal (x j)| * (l1Weighted.matrixColNorm ν A j * (ν : ℝ) ^ (j : ℕ)) := by
        simp only [l1Weighted.matrixColNorm_mul_pow]
    -- Step 4: Factor out the maximum column norm
    _ ≤ ∑ j, |ScaledReal.toReal (x j)| * (l1Weighted.finWeightedMatrixNorm ν A * (ν : ℝ) ^ (j : ℕ)) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (PosReal.coe_nonneg ν) _)
        exact Finset.le_sup' _ (Finset.mem_univ j)
    _ = l1Weighted.finWeightedMatrixNorm ν A * ∑ j, |ScaledReal.toReal (x j)| * (ν : ℝ) ^ (j : ℕ) := by
        rw [Finset.mul_sum]
        congr 1; ext j; ring

/-- The matrix as a continuous linear map on the weighted space -/
def toWeightedCLM {ν : PosReal} {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    FinWeighted.Space ν N →L[ℝ] FinWeighted.Space ν N :=
  LinearMap.mkContinuous
    (mulVecWeightedLinear A)
    (l1Weighted.finWeightedMatrixNorm ν A)
    (mulVecWeightedLinear_norm_le A)

/-- Operator norm is bounded by the weighted matrix norm -/
lemma opNorm_toWeightedCLM_le {ν : PosReal} {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ‖toWeightedCLM (ν := ν) A‖ ≤ l1Weighted.finWeightedMatrixNorm ν A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    apply Finset.le_sup'_of_le _ (Finset.mem_univ 0)
    simp [l1Weighted.matrixColNorm]
    apply Finset.sum_nonneg
    intro i _
    apply l1Weighted.weighted_term_nonneg _ _)
  intro x
  exact mulVecWeightedLinear_norm_le A x

/-- **Lemma 7.3.11 application**: The column norm is achieved on basis vectors.
    For the j-th basis vector eⱼ with ‖eⱼ‖ = νʲ:
      ‖A eⱼ‖ / ‖eⱼ‖ = colNorm_j
    This shows the matrix norm is achieved, not just bounded. -/
lemma opNorm_achieved_on_basis {ν : PosReal} {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (j : Fin (N + 1)) :
    ‖toWeightedCLM (ν := ν) A (FinWeighted.stdBasis j)‖ =
    l1Weighted.matrixColNorm ν A j * (ν : ℝ) ^ (j : ℕ) := by
  simp only [toWeightedCLM]
  rw [FinWeighted.norm_eq_sum]
  have h_apply : ∀ i, ScaledReal.toReal ((mulVecWeightedLinear (ν := ν) A (FinWeighted.stdBasis j)).ofLp i) = A i j := by
    intro i
    simp only [mulVecWeightedLinear, LinearMap.coe_mk, AddHom.coe_mk,
               ScaledReal.toReal, ScaledReal.ofReal, FinWeighted.stdBasis]
    rw [Finset.sum_eq_single j]
    · simp only [↓reduceIte, mul_one]; rfl
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ j) h
  simp only [LinearMap.mkContinuous, coe_mk']
  have h' : ∀ i, |((mulVecWeightedLinear A (FinWeighted.stdBasis (ν := ν) j)).ofLp i)| = |A i j| := by
    intro i; rw [← h_apply]; rfl
  simp only [ScaledReal.toReal_apply, h', l1Weighted.matrixColNorm_mul_pow]

/-- **Exercise 2.7.2**: The weighted matrix norm equals the operator norm.
    ‖A‖_{1,ν} = max_j (1/νʲ) Σᵢ |Aᵢⱼ| νⁱ = ‖A‖_{op}
    **Proof**:
    - (≥): The sup over column norms is achieved on basis vectors (opNorm_achieved_on_basis)
    - (≤): Every vector gives at most the max column norm (mulVecWeightedLinear_norm_le) -/
theorem finWeightedMatrixNorm_eq_opNorm {ν : PosReal} {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    l1Weighted.finWeightedMatrixNorm ν A = ‖toWeightedCLM (ν := ν) A‖ := by
  apply le_antisymm
  -- Direction (≤): finWeightedMatrixNorm ≤ opNorm
  · -- The max column norm is achieved by some basis vector
    rw [l1Weighted.finWeightedMatrixNorm]
    apply Finset.sup'_le
    intro j _
    -- colNorm_j = ‖A eⱼ‖ / νʲ ≤ ‖A‖_op · ‖eⱼ‖ / νʲ = ‖A‖_op
    rw [l1Weighted.matrixColNorm]
    have h_basis_norm : ‖FinWeighted.stdBasis (ν := ν) j‖ = (ν : ℝ) ^ (j : ℕ) :=
      FinWeighted.norm_stdBasis j
    have h_pos : (0 : ℝ) < (ν : ℝ) ^ (j : ℕ) := pow_pos (PosReal.coe_pos ν) _
    calc (1 / (ν : ℝ) ^ (j : ℕ)) * ∑ i, |A i j| * (ν : ℝ) ^ (i : ℕ)
        = ‖toWeightedCLM (ν := ν) A (FinWeighted.stdBasis j)‖ / (ν : ℝ) ^ (j : ℕ) := by
          rw [opNorm_achieved_on_basis, l1Weighted.matrixColNorm]; field_simp [h_pos]
      _ = ‖toWeightedCLM (ν := ν) A (FinWeighted.stdBasis j)‖ / ‖FinWeighted.stdBasis (ν := ν) j‖ := by
          rw [h_basis_norm]
      _ ≤ ‖toWeightedCLM (ν := ν) A‖ := by
          rw [div_le_iff₀ (h_basis_norm ▸ h_pos)]
          exact ContinuousLinearMap.le_opNorm _ _
  -- Direction (≥): opNorm ≤ finWeightedMatrixNorm
  · exact opNorm_toWeightedCLM_le A

/-- toWeightedCLM preserves matrix multiplication.

    This shows that the embedding of matrices into weighted CLMs is a ring homomorphism.
    The proof swaps the order of summation and uses associativity of multiplication. -/
lemma toWeightedCLM_mul {ν : PosReal} {N : ℕ}
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    toWeightedCLM (ν := ν) (A * B) =
    (toWeightedCLM (ν := ν) A).comp (toWeightedCLM (ν := ν) B) := by
  ext x i
  simp only [toWeightedCLM, mulVecWeightedLinear, ScaledReal.ofReal,
    ScaledReal.toReal, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk, coe_comp',
    Function.comp_apply, Matrix.mul_apply]
  simp only [map_sum]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  conv_lhs =>
    arg 2; ext k
    simp only [map_sum]
  rw [Finset.sum_comm]
  simp [mul_assoc]
  rfl

/-- toWeightedCLM preserves subtraction from identity.

    This shows that applying the matrix (I - M) via toWeightedCLM equals
    the identity CLM minus toWeightedCLM of M. The proof reduces to showing
    that the Kronecker delta sum ∑ₖ δᵢₖ · xₖ = xᵢ. -/
lemma toWeightedCLM_one_sub {ν : PosReal} {N : ℕ}
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    toWeightedCLM (ν := ν) (1 - M) =
    ContinuousLinearMap.id ℝ (FinWeighted.Space ν N) - toWeightedCLM (ν := ν) M := by
  ext x i
  simp only [toWeightedCLM, mulVecWeightedLinear, ContinuousLinearMap.coe_sub',
             ContinuousLinearMap.coe_id', Pi.sub_apply, id_eq, LinearMap.coe_mk, AddHom.coe_mk,
             LinearMap.mkContinuous_apply, ScaledReal.ofReal, ScaledReal.toReal,
             Matrix.sub_apply, Matrix.one_apply, WithLp.ofLp_sub, map_sum, sub_mul]
  simp only [ite_mul, one_mul, zero_mul, map_sub, Finset.sum_sub_distrib, sub_left_inj]
  rw [Finset.sum_eq_single i]
  · simp only [↓reduceIte]; rfl
  · intro j _ hj; simp only [EmbeddingLike.map_eq_zero_iff, ite_eq_right_iff]; omega
  · intro h; exact absurd (Finset.mem_univ i) h

/-- If the CLM corresponding to a matrix is a unit, so is the matrix.

    The proof uses the fact that toWeightedCLM M is essentially M.mulVec
    transported to the weighted space via an isomorphism. If the CLM is
    invertible (a unit), then M.mulVec must be injective, which for
    square matrices over a field means det M ≠ 0.

    Key insight: FinWeighted.Space ν N ≅ Fin (N+1) → ℝ as vector spaces
    (the norms differ but the underlying spaces are the same).
    So IsUnit (toWeightedCLM M) ↔ IsUnit (toLin' M) ↔ IsUnit M. -/
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
      have := congrFun (congrArg DFunLike.coe u.inv_mul) x
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
      exact this
    exact h_left_inv.injective
  have h_det_lin : LinearMap.det (Matrix.toLin' M) = 0 := by
    rw [LinearMap.det_toLin']; exact h_det
  have h_ker_nontrivial := LinearMap.bot_lt_ker_of_det_eq_zero h_det_lin
  rw [bot_lt_iff_ne_bot, ne_eq, Submodule.eq_bot_iff] at h_ker_nontrivial
  push_neg at h_ker_nontrivial
  obtain ⟨v, hv_ker, hv_ne⟩ := h_ker_nontrivial
  rw [LinearMap.mem_ker] at hv_ker
  have hv_mulVec : M *ᵥ v = 0 := by
    simp only [Matrix.toLin'_apply] at hv_ker
    exact hv_ker
  let x : FinWeighted.Space ν N := WithLp.toLp 1 (fun i => v i)
  have hx_ne : x ≠ 0 := by
    simp only [ne_eq]
    intro hx; apply hv_ne; ext i
    exact congrFun (congrArg WithLp.ofLp hx) i
  have hx_zero : toWeightedCLM (ν := ν) M x = 0 := by
    ext i
    simp only [toWeightedCLM, mulVecWeightedLinear, LinearMap.coe_mk,
               AddHom.coe_mk, LinearMap.mkContinuous_apply, ScaledReal.ofReal]
    exact congrFun hv_mulVec i
  rw [← map_zero (toWeightedCLM (ν := ν) M)] at hx_zero
  exact hx_ne (h_inj hx_zero)

/-- If ‖I - M‖ < 1 for a square matrix M, then M is invertible.

    This is the matrix version of the Neumann series invertibility criterion. -/
lemma matrix_invertible_of_norm_lt_one {ν : PosReal} {N : ℕ}
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (h : l1Weighted.finWeightedMatrixNorm ν (1 - M) < 1) :
    IsUnit M := by
  rw [finWeightedMatrixNorm_eq_opNorm, toWeightedCLM_one_sub] at h
  have h_unit := isUnit_of_norm_sub_id_lt_one (E := FinWeighted.Space ν N) h
  exact matrix_isUnit_of_toWeightedCLM_isUnit M h_unit

end FinWeightedMatrix

/-- Structural injectivity criterion for block-diagonal operators:
    if the finite product `A.finBlock * B` is within distance `< 1` from identity
    in weighted matrix norm, then `A.finBlock` is invertible; combined with a
    nonvanishing tail diagonal this implies injectivity of `A.toCLM`. -/
lemma BlockDiag.BlockDiagOp.injective_of_finBlock_mul_close_to_one
    {ν : PosReal} {N : ℕ}
    (A : BlockDiag.BlockDiagOp ν N)
    (B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (h_norm : l1Weighted.finWeightedMatrixNorm ν (1 - A.finBlock * B) < 1)
    (h_tail : ∀ n, N < n → A.tailDiag n ≠ 0) :
    Function.Injective A.toCLM := by
  have h_prod_unit : IsUnit (A.finBlock * B) :=
    FinWeightedMatrix.matrix_invertible_of_norm_lt_one _ h_norm
  have h_fin_unit : IsUnit A.finBlock := by
    rw [Matrix.isUnit_iff_isUnit_det] at h_prod_unit ⊢
    have h_det_prod : IsUnit (A.finBlock * B).det := h_prod_unit
    rw [Matrix.det_mul] at h_det_prod
    exact isUnit_of_mul_isUnit_left h_det_prod
  exact BlockDiag.BlockDiagOp.injective_of_parts A h_fin_unit h_tail


/-! ## Block-Diagonal Operators

For Chapter 7.7 and Chapter 8.x, operators have block-diagonal structure:

- finite block `A_N` on coordinates `0..N`
- tail diagonal `tailDiag n` on coordinates `n > N`

With a uniform tail bound `|tailDiag n| ≤ C`, Proposition 7.3.14 is used as:
`‖A‖ ≤ max(‖A_N‖_{1,ν}, C)`.

The block-diagonal operator infrastructure is in `BlockDiag.lean`.
-/


-- Note: Proposition 7.3.14 (opNorm_blockDiag_le) has been removed.
-- It was subsumed by BlockDiag.BlockDiagOp.norm_toCLM_le and was unused downstream.

end

import RadiiPolynomial.TaylorODE.lpWeighted
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

**Proposition 7.3.14**: For block-diagonal operators of the form

  A = [ A_N    0   ]
      [  0    c·I  ]

where A_N is an (N+1)×(N+1) matrix and c is a scalar on the tail,
we have: ‖A‖ ≤ max(K, |c|)

where K = finWeightedMatrixNorm(A_N).

## Main Definitions

- `WeightedPiLp`: Finite-dimensional weighted ℓ¹ space on `Fin (N+1) → ℝ`
- `Matrix.toWeightedCLM`: Matrix as continuous linear map on weighted space
- `BlockDiagOp`: Block-diagonal operator structure for Chapter 7.7

## Main Results

- `finWeightedMatrixNorm_eq_opNorm`: Matrix norm = operator norm (Exercise 2.7.2)
- `Proposition_7_3_14`: Operator norm bound for block-diagonal operators

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

lemma norm_eq_sum (x : Space ν N) :
    ‖x‖ = ∑ n : Fin (N + 1), |ScaledReal.toReal (x n)| * (ν : ℝ) ^ (n : ℕ) := by
  rw [PiLp.norm_eq_sum (p := 1) (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one]
  rfl

lemma norm_eq_finl1WeightedNorm (x : Space ν N) :
    ‖x‖ = l1Weighted.finl1WeightedNorm ν.toNNReal (fun n => x n) := by
  rw [norm_eq_sum, l1Weighted.finl1WeightedNorm]
  rfl

/-- Standard basis vector eⱼ with 1 at position j and 0 elsewhere -/
def stdBasis (j : Fin (N + 1)) : Space ν N :=
  WithLp.toLp 1 (fun n => if n = j then (1 : ScaledReal ν n) else 0)

@[simp]
lemma stdBasis_apply_self (j : Fin (N + 1)) : stdBasis (ν := ν) j j = 1 := by
  simp [stdBasis]

@[simp]
lemma stdBasis_apply_ne (i j : Fin (N + 1)) (h : i ≠ j) : stdBasis (ν := ν) j i = 0 := by
  simp [stdBasis, h]

/-- The norm of a basis vector: ‖eⱼ‖ = νʲ -/
lemma norm_stdBasis (j : Fin (N + 1)) : ‖stdBasis (ν := ν) j‖ = (ν : ℝ) ^ (j : ℕ) := by
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

namespace Matrix

variable {N : ℕ}

/-- Matrix action as a linear map on the weighted space.
    This is the standard matrix action (Ax)ᵢ = Σⱼ Aᵢⱼ xⱼ -/
def mulVecWeightedLinear (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
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
         ≤ Σᵢ Σⱼ |Aᵢⱼ| |xⱼ| νⁱ            [triangle ineq]
         = Σⱼ (Σᵢ |Aᵢⱼ| νⁱ) |xⱼ|          [swap sums]
         = Σⱼ (colNorm_j · νʲ) |xⱼ|       [def of colNorm]
         ≤ (max_j colNorm_j) · Σⱼ |xⱼ| νʲ [factor out max]
         = (max_j colNorm_j) · ‖x‖ -/
lemma mulVecWeightedLinear_norm_le (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
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
    -- Step 3: Express in terms of column norm
    _ = ∑ j, |ScaledReal.toReal (x j)| * (l1Weighted.matrixColNorm ν A j * (ν : ℝ) ^ (j : ℕ)) := by
        congr 1; ext j
        rw [l1Weighted.matrixColNorm]
        have hν : (ν : ℝ) ^ (j : ℕ) ≠ 0 := pow_ne_zero _ (PosReal.coe_ne_zero ν)
        field_simp [hν]
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
def toWeightedCLM (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    FinWeighted.Space ν N →L[ℝ] FinWeighted.Space ν N :=
  LinearMap.mkContinuous
    (mulVecWeightedLinear A)
    (l1Weighted.finWeightedMatrixNorm ν A)
    (mulVecWeightedLinear_norm_le A)

/-- Operator norm is bounded by the weighted matrix norm -/
lemma opNorm_toWeightedCLM_le (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ‖toWeightedCLM (ν := ν) A‖ ≤ l1Weighted.finWeightedMatrixNorm ν A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    apply Finset.le_sup'_of_le _ (Finset.mem_univ 0)
    simp [l1Weighted.matrixColNorm]
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) _))
  intro x
  exact mulVecWeightedLinear_norm_le A x

/-- **Lemma 7.3.11 application**: The column norm is achieved on basis vectors.
    For the j-th basis vector eⱼ with ‖eⱼ‖ = νʲ:
      ‖A eⱼ‖ / ‖eⱼ‖ = colNorm_j
    This shows the matrix norm is achieved, not just bounded. -/
lemma opNorm_achieved_on_basis (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (j : Fin (N + 1)) :
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
  have h' : ∀ i, |((A.mulVecWeightedLinear (FinWeighted.stdBasis (ν := ν) j)).ofLp i)| = |A i j| := by
    intro i; rw [← h_apply]; rfl
  simp only [ScaledReal.toReal_apply, h']
  rw [l1Weighted.matrixColNorm]
  have hν : (ν : ℝ) ^ (j : ℕ) ≠ 0 := pow_ne_zero _ (PosReal.coe_ne_zero ν)
  field_simp [hν]

/-- **Exercise 2.7.2**: The weighted matrix norm equals the operator norm.
    ‖A‖_{1,ν} = max_j (1/νʲ) Σᵢ |Aᵢⱼ| νⁱ = ‖A‖_{op}
    **Proof**:
    - (≥): The sup over column norms is achieved on basis vectors (opNorm_achieved_on_basis)
    - (≤): Every vector gives at most the max column norm (mulVecWeightedLinear_norm_le) -/
theorem finWeightedMatrixNorm_eq_opNorm (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
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

end Matrix


/-! ## Block-Diagonal Operators

For Chapter 7.7, operators have block-diagonal structure:

  A = [ A_N    0   ]
      [  0    c·I  ]

where A_N is an (N+1)×(N+1) finite matrix and c is a scalar acting
diagonally on the infinite tail.

Proposition 7.3.14 gives: ‖A‖ ≤ max(‖A_N‖_{1,ν}, |c|)
-/

namespace BlockDiag

variable {N : ℕ}

/-- A block-diagonal operator on ℓ¹_ν.

    The operator acts as:
    - A finite matrix `finBlock` on coordinates 0, 1, ..., N
    - A scalar `tailScalar` times identity on coordinates N+1, N+2, ...

    See equations (7.47) and (7.48) for the operators A† and A in Chapter 7.7. -/
structure BlockDiagOp (ν : PosReal) (N : ℕ) where
  /-- The (N+1)×(N+1) matrix acting on the finite part -/
  finBlock : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  /-- The scalar multiplying the identity on the tail -/
  tailScalar : ℝ

/-- The action of a block-diagonal operator on a sequence.

    (A·a)ₙ = (finBlock · a_{[0,N]})ₙ  for n ≤ N
    (A·a)ₙ = tailScalar · aₙ          for n > N -/
def BlockDiagOp.action (A : BlockDiagOp ν N) (a : ℕ → ℝ) : ℕ → ℝ := fun n =>
  if h : n ≤ N then
    ∑ j : Fin (N + 1), A.finBlock ⟨n, Nat.lt_succ_of_le h⟩ j * a j
  else
    A.tailScalar * a n

/-- The projection of a sequence onto its first N+1 coordinates -/
def projFin (a : l1Weighted ν) : Fin (N + 1) → ℝ :=
  fun n => lpWeighted.toSeq a n

/-- Embedding a finite vector as a sequence with zero tail -/
def embedFin (x : Fin (N + 1) → ℝ) : ℕ → ℝ :=
  fun n => if h : n ≤ N then x ⟨n, Nat.lt_succ_of_le h⟩ else 0

/-- The tail projection: coordinates N+1, N+2, ... -/
def projTail (a : l1Weighted ν) : ℕ → ℝ :=
  fun n => if n ≤ N then 0 else lpWeighted.toSeq a n

/-- Direct sum decomposition: a = embedFin(projFin a) + projTail a -/
lemma direct_sum_decomp (a : l1Weighted ν) (n : ℕ) :
    lpWeighted.toSeq a n = embedFin (N := N) (projFin (N := N) a) n + projTail (N := N) a n := by
  simp only [embedFin, projFin, projTail]
  split_ifs with h
  · simp only [lpWeighted.toSeq_apply, add_zero]
  · simp only [lpWeighted.toSeq_apply, zero_add]

/-- Bound on the finite block contribution.

    For the finite part, we use the weighted matrix norm. -/
lemma finBlock_norm_bound (A : BlockDiagOp ν N) (a : l1Weighted ν) :
    ∑ n : Fin (N + 1), |∑ j : Fin (N + 1), A.finBlock n j * lpWeighted.toSeq a j| * (ν : ℝ) ^ (n : ℕ) ≤
    l1Weighted.finWeightedMatrixNorm ν A.finBlock *
    ∑ j : Fin (N + 1), |lpWeighted.toSeq a j| * (ν : ℝ) ^ (j : ℕ) := by
  -- This follows the same pattern as Matrix.mulVecWeightedLinear_norm_le
  calc ∑ n : Fin (N + 1), |∑ j, A.finBlock n j * lpWeighted.toSeq a j| * (ν : ℝ) ^ (n : ℕ)
      ≤ ∑ n : Fin (N + 1), (∑ j, |A.finBlock n j| * |lpWeighted.toSeq a j|) * (ν : ℝ) ^ (n : ℕ) := by
        apply Finset.sum_le_sum
        intro n _
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (PosReal.coe_nonneg ν) _)
        calc |∑ j, A.finBlock n j * lpWeighted.toSeq a j|
            ≤ ∑ j, |A.finBlock n j * lpWeighted.toSeq a j| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j, |A.finBlock n j| * |lpWeighted.toSeq a j| := by simp_rw [abs_mul]
    _ = ∑ n, ∑ j, |A.finBlock n j| * |lpWeighted.toSeq a j| * (ν : ℝ) ^ (n : ℕ) := by
        congr 1; ext n; rw [Finset.sum_mul]
    _ = ∑ j, ∑ n, |A.finBlock n j| * |lpWeighted.toSeq a j| * (ν : ℝ) ^ (n : ℕ) := Finset.sum_comm
    _ = ∑ j : Fin (N + 1), |lpWeighted.toSeq a j| * ∑ n, |A.finBlock n j| * (ν : ℝ) ^ (n : ℕ) := by
        congr 1; ext j; rw [Finset.mul_sum]; congr 1; ext n; ring
    _ = ∑ j : Fin (N + 1), |lpWeighted.toSeq a j| * (l1Weighted.matrixColNorm ν A.finBlock j * (ν : ℝ) ^ (j : ℕ)) := by
        congr 1; ext j; rw [l1Weighted.matrixColNorm]
        simp only [lpWeighted.toSeq_apply, one_div, mul_eq_mul_left_iff, abs_eq_zero]
        field_simp [PosReal.coe_ne_zero ν]
        simp only [true_or]
    _ ≤ ∑ j : Fin (N + 1), |lpWeighted.toSeq a j| * (l1Weighted.finWeightedMatrixNorm ν A.finBlock * (ν : ℝ) ^ (j : ℕ)) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (PosReal.coe_nonneg ν) _)
        exact Finset.le_sup' _ (Finset.mem_univ j)
    _ = l1Weighted.finWeightedMatrixNorm ν A.finBlock * ∑ j : Fin (N + 1), |lpWeighted.toSeq a j| * (ν : ℝ) ^ (j : ℕ) := by
        rw [Finset.mul_sum]; congr 1; ext j; ring

/-- Equality version: factoring out the scalar from tail -/
lemma tailScalar_norm_eq (A : BlockDiagOp ν N) (a : l1Weighted ν) :
    ∑' n : {n : ℕ // N < n}, |A.tailScalar * lpWeighted.toSeq a n| * (ν : ℝ) ^ (n : ℕ) =
    |A.tailScalar| * ∑' n : {n : ℕ // N < n}, |lpWeighted.toSeq a n| * (ν : ℝ) ^ (n : ℕ) := by
  calc ∑' n : {n : ℕ // N < n}, |A.tailScalar * lpWeighted.toSeq a n| * (ν : ℝ) ^ (n : ℕ)
      = ∑' n : {n : ℕ // N < n}, |A.tailScalar| * |lpWeighted.toSeq a n| * (ν : ℝ) ^ (n : ℕ) := by
        congr 1; ext n; rw [abs_mul]
    _ = |A.tailScalar| * ∑' n : {n : ℕ // N < n}, |lpWeighted.toSeq a n| * (ν : ℝ) ^ (n : ℕ) := by
        rw [← tsum_mul_left]; congr 1; ext n; ring

/-- Split the ℓ¹ norm into finite and tail parts -/
lemma norm_split (a : l1Weighted ν) :
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

end BlockDiag


/-! ## Proposition 7.3.14: Block-Diagonal Operator Norm Bound

For a block-diagonal operator A with finite block A_N and tail scalar c,
we have: ‖A‖ ≤ max(‖A_N‖_{1,ν}, |c|)

This is the key result connecting the computable matrix norm to the abstract
operator norm for the Chapter 7.7 formalization.
-/

namespace Proposition_7_3_14

variable {N : ℕ}

/-- **Proposition 7.3.14**: Operator norm bound for block-diagonal operators.

    Given a block-diagonal operator A = [A_N, 0; 0, c·I] on ℓ¹_ν, we have:

      ‖A‖ ≤ max(K, |c|)

    where K = ‖A_N‖_{1,ν} is the weighted matrix norm of the finite block.

    **Proof outline** (following the textbook):
    1. Split ‖Aa‖ into finite and tail contributions
    2. Bound finite part using matrix norm: ≤ K · ‖a_{fin}‖
    3. Bound tail part using scalar: ≤ |c| · ‖a_{tail}‖
    4. Combine using ‖a‖ = ‖a_{fin}‖ + ‖a_{tail}‖ and max bound -/
theorem opNorm_blockDiag_le (A : BlockDiag.BlockDiagOp ν N)
    (A_CLM : l1Weighted ν →L[ℝ] l1Weighted ν)
    (h_action : ∀ a n, lpWeighted.toSeq (A_CLM a) n = BlockDiag.BlockDiagOp.action A (lpWeighted.toSeq a) n) :
    ‖A_CLM‖ ≤ max (l1Weighted.finWeightedMatrixNorm ν A.finBlock) |A.tailScalar| := by
  let K := l1Weighted.finWeightedMatrixNorm ν A.finBlock
  let c := A.tailScalar
  apply ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left (l1Weighted.finWeightedMatrixNorm_nonneg A.finBlock))
  intro a
  -- Split ‖A_CLM a‖ using norm_split
  rw [BlockDiag.norm_split (N := N) (A_CLM a)]
  -- Rewrite finite part using h_action
  have h_fin : ∑ n : Fin (N + 1), |lpWeighted.toSeq (A_CLM a) n| * (ν : ℝ) ^ (n : ℕ) =
      ∑ n : Fin (N + 1), |∑ j : Fin (N + 1), A.finBlock n j * lpWeighted.toSeq a j| * (ν : ℝ) ^ (n : ℕ) := by
    congr 1; ext n
    congr 1
    rw [h_action]
    simp only [BlockDiag.BlockDiagOp.action, Fin.is_le, ↓reduceDIte]
  -- Rewrite tail part using h_action
  have h_tail : ∑' n : {n : ℕ // N < n}, |lpWeighted.toSeq (A_CLM a) n| * (ν : ℝ) ^ (n : ℕ) =
      ∑' n : {n : ℕ // N < n}, |A.tailScalar * lpWeighted.toSeq a n| * (ν : ℝ) ^ (n : ℕ) := by
    congr 1; ext ⟨n, hn⟩
    congr 1
    rw [h_action]
    simp only [BlockDiag.BlockDiagOp.action, not_le.mpr hn, ↓reduceDIte]
  rw [h_fin, h_tail, BlockDiag.tailScalar_norm_eq]
  -- Apply bounds and combine
  have hK := BlockDiag.finBlock_norm_bound A a
  have ha_split := BlockDiag.norm_split (N := N) a
  calc (∑ n : Fin (N + 1), |∑ j, A.finBlock n j * lpWeighted.toSeq a j| * (ν : ℝ) ^ (n : ℕ)) +
       |c| * ∑' n : {n : ℕ // N < n}, |lpWeighted.toSeq a n| * (ν : ℝ) ^ (n : ℕ)
      ≤ K * (∑ j : Fin (N + 1), |lpWeighted.toSeq a j| * (ν : ℝ) ^ (j : ℕ)) +
        |c| * ∑' n : {n : ℕ // N < n}, |lpWeighted.toSeq a n| * (ν : ℝ) ^ (n : ℕ) := by
          apply add_le_add_left hK
    _ ≤ max K |c| * (∑ j : Fin (N + 1), |lpWeighted.toSeq a j| * (ν : ℝ) ^ (j : ℕ)) +
        max K |c| * ∑' n : {n : ℕ // N < n}, |lpWeighted.toSeq a n| * (ν : ℝ) ^ (n : ℕ) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_right (le_max_left _ _)
            apply Finset.sum_nonneg; intro j _
            apply mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) _)
          · apply mul_le_mul_of_nonneg_right (le_max_right _ _)
            apply tsum_nonneg; intro n
            apply mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) _)
    _ = max K |c| * ‖a‖ := by rw [← mul_add, ← ha_split]

end Proposition_7_3_14

end

import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix -- For L2Operator norm

/-!
# Matrix Norms
This file provides the formal definition of a matrix norm
-/

/- Variables -/
variable {l m n p : Type*}
/- Typeclasses -/
/-
  `Fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list.
-/
variable [Fintype l] [Fintype m] [Fintype n] [Fintype p]


-- Import notations for matrices, big operators, and nonnegative reals.
open scoped Matrix BigOperators NNReal ENNReal


-- Top level namespace for this file
namespace MatrixNorm



/-
### General Norm Axioms
The following four axioms establish the fundamental properties that a function must satisfy to be considered a norm on a space of matrices.
-/
section GeneralNormAxioms

/--
This class defines the four axioms a function `norm_fun` must satisfy
to be considered a valid norm on a space of finite matrices over `ℝ`.
-/
class IsMatrixNorm {m n : Type*} [Fintype m] [Fintype n] (norm_fun : Matrix m n ℝ → ℝ) : Prop where
  /-- ‖A‖ ≥ 0 -/
  non_neg (A : Matrix m n ℝ) : 0 ≤ norm_fun A

  /-- ‖A‖ = 0 ↔ A = 0  -/
  zero_iff_matrix_zero (A : Matrix m n ℝ) : norm_fun A = 0 ↔ A = 0

  /-- ‖rA‖ = |r|·‖A‖ -/
  scalar_multiple (r : ℝ) (A : Matrix m n ℝ) : norm_fun (r • A) = |r| * norm_fun A

  /-- ‖A + B‖ ≤ ‖A‖ + ‖B‖ -/
  sum_le_sum_of_norms (A B : Matrix m n ℝ) : norm_fun (A + B) ≤ norm_fun A + norm_fun B

end GeneralNormAxioms



-- /-!
-- ### Equivalence with `mathlib`'s `NormedSpace`
instance : True :=
-- This section proves that our explicit `IsMatrixNorm` class is logically equivalent
-- to `mathlib`'s `NormedSpace` class. This allows us to use `mathlib`'s powerful
-- typeclass system directly.
-- -/
-- section MathlibEquivalence

-- open scoped Matrix.Norms.Operator
-- open Matrix

-- set_option diagnostics true
-- /-
-- A theorem proving that if a matrix type is a `NormedSpace` according to `mathlib`,
-- then it satisfies our `IsMatrixNorm` axioms.

-- 1. [NormedAddCommGroup (Matrix m n ℝ)]
-- This constraint requires that Matrix m n ℝ is a Normed Additive Commutative Group. This is a standard mathlib structure that guarantees the following properties for matrices:

--   It has addition (+) and a zero (0).
--   It has a norm function ‖·‖

-- The norm satisfies the core "group-related" axioms:
--   ‖A‖ = 0 ↔ A = 0 (Definiteness)
--   ‖A + B‖ ≤ ‖A‖ + ‖B‖ (Triangle Inequality)
--   ‖A‖ ≥ 0 (Non-negativity)
-- This single constraint provides the structure for three of the four axioms in your original IsMatrixNorm class.

-- 2. [NormedSpace ℝ (Matrix m n ℝ)]
-- This constraint requires that Matrix m n ℝ is a Normed Space over the real numbers ℝ. This builds on the previous structure and adds the concept of scalar multiplication. It guarantees:

-- It has scalar multiplication (r • A)
-- The norm is compatible with scalar multiplication:
--   ‖r • A‖ = |r| * ‖A‖ (Absolute Homogeneity)
-- -/
-- -- theorem isMatrixNorm_of_normedSpace
-- --     -- Assume we have the mathlib structures for a given norm.
-- --     [NormedAddCommGroup (Matrix m n ℝ)] [NormedSpace ℝ (Matrix m n ℝ)] :
-- --     -- Then we can prove our class holds for that norm.
-- --     IsMatrixNorm (norm : Matrix m n ℝ → ℝ) where
-- --   non_neg _ := norm_nonneg _
-- --   zero_iff_matrix_zero _ := norm_eq_zero
-- --   scalar_multiple r A := by rw [norm_smul r A, Real.norm_eq_abs]
-- --   sum_le_sum_of_norms _ _ := norm_add_le _ _

-- end MathlibEquivalence
by trivial


/-
A brief section to show that the element-wise norm satisfies the `IsMatrixNorm` axioms.
-/
namespace ElementwiseMatrixNorm
/-
Tells LEAN to interpret `‖·‖` and `norm` as the elementwise norm
Just to show the schematic norm axioms holds for this norm.
-/
open scoped Matrix.Norms.Elementwise

-- Set the option to show more detailed error messages.
-- set_option diagnostics true

-- This instance proves that the element-wise norm satisfies the `IsMatrixNorm` axioms.
theorem elementwiseNorm_is_matrixNorm : IsMatrixNorm (norm : Matrix m n ℝ → ℝ) where
  non_neg _ := by exact norm_nonneg _
  zero_iff_matrix_zero _ := by exact norm_eq_zero
  scalar_multiple r A := by rw [norm_smul r A, Real.norm_eq_abs]
  sum_le_sum_of_norms _ _ := by exact norm_add_le _ _

-- Legacy norm axioms checks for the elementwise norm
instance : true :=
-- -- A norm must be non-negative.
-- theorem norm_non_neg (A : Matrix n n ℝ) : 0 ≤ ‖A‖ :=
--   norm_nonneg _

-- -- A norm is zero if and only if the matrix is the zero matrix.
-- theorem norm_zero_iff_matrix_zero (A : Matrix n n ℝ) : ‖A‖ = 0 ↔ A = 0 :=
--   norm_eq_zero

-- -- Scaling a matrix by a scalar `r` scales its norm by `|r|`.
-- theorem norm_of_scalar_multiple (r : ℝ) (A : Matrix n n ℝ) : ‖r • A‖ = |r| * ‖A‖ := by
--   rw [norm_smul r A, Real.norm_eq_abs]

-- -- The triangle inequality: the norm of a sum is at most the sum of the norms.
-- theorem norm_of_sum_le_sum_of_norms (A B : Matrix n n ℝ) : ‖A + B‖ ≤ ‖A‖ + ‖B‖ :=
--   norm_add_le _ _

rfl

end ElementwiseMatrixNorm



/-!
### The Induced Norm (Operator Norm) Axioms

An induced norm is a matrix norm that is "induced" by a vector norm.
It must satisfy the standard matrix norm axioms, plus three additional properties
related to matrix-vector and matrix-matrix multiplication.
-/
section InducedNormAxioms

/--
This class defines the axioms for an induced matrix norm. It extends `IsMatrixNorm`
with properties for sub-multiplicativity and the norm of the identity matrix.
-/
class IsInducedMatrixNorm {m n : Type*} [Fintype m] [Fintype n] (norm_fun : Matrix m n ℝ → ℝ) : Prop extends IsMatrixNorm norm_fun where
  /-- The norm of a matrix-vector product is at most the product of their norms. (Consistency) -/
  norm_mul_vec_le (A : Matrix m n ℝ) (x : n → ℝ) : ‖A.mulVec x‖ ≤ norm_fun A * ‖x‖
  /-- The norm of a matrix product is at most the product of their norms. (Sub-multiplicativity) -/
  norm_mul_le {p : Type*} [Fintype p] (A : Matrix m n ℝ) (B : Matrix n p ℝ) : norm_fun (A * B) ≤ norm_fun A * norm_fun B
  /-- The norm of the identity matrix is 1. Requires a square matrix. -/
  norm_one [DecidableEq n] [Nonempty n] : norm_fun (1 : Matrix n n ℝ) = 1

end InducedNormAxioms


/-!
### The Operator Norm (Induced Norm)
-/
section LInftyMatrixNorm
-- Set the option to show more detailed error messages.
-- set_option diagnostics true

/-
Propositional equality is `Decidable` for all elements of a type.
In other words, an instance of `DecidableEq α` is a means of deciding the proposition `a = b` is
for all `a b : α`.

`DecidableEq n` is used in `norm_one` as a proof for ‖id.‖ = 1, which
equips `Matrix n n ℝ` with a `NormedRing` structure.
-/
variable [DecidableEq n]


/-
Activate the operator norm scope, defined in `Matrix.lean` source file.
LEAN recognizes `Matrix n n ℝ` as a full normed algebra,
which includes the ring and space structures.
Makes `‖·‖` and `norm` refer to the **L-infinity** operator norm.
-/
open scoped Matrix.Norms.Operator

-- Use the Matrix namespace
open Matrix

-- This Lemma proves the l-infty norm in linftyOpNormedSpace is exactly
-- the supremum of `‖A * x‖` over all vectors `x` with `‖x‖ = 1`.
omit [DecidableEq n] in
lemma operator_sup_norm_definition (A : Matrix m n ℝ) : ‖A‖ = sSup { ‖A.mulVec x‖ | (x) (_ : ‖x‖ = 1)} := by
  -- This proof restates the definition in terms of mathlib's `Metric.sphere`
  suffices ‖A‖ = sSup ((‖A.mulVec ·‖) '' Metric.sphere 0 1) by
    simpa [Set.image, mem_sphere_zero_iff_norm] using this
  -- It then connects the matrix operator norm to the ContinuousLinearMap operator norm.
  rw [linfty_opNorm_eq_opNorm, ← ContinuousLinearMap.sSup_sphere_eq_norm]
  simp


-- The operator norm of the identity matrix is 1.
theorem norm_of_identity_matrix [Nonempty n] : ‖(1 : Matrix n n ℝ)‖ = 1 :=
  norm_one

omit [DecidableEq n] in
-- The operator norm is consistent with the vector norm.
theorem norm_of_matrix_times_vector_le (A : Matrix m n ℝ) (x : n → ℝ) : ‖A.mulVec x‖ ≤ ‖A‖ * ‖x‖ :=
  linfty_opNorm_mulVec _ _

omit [DecidableEq n] in
-- The operator norm is submultiplicative.
theorem norm_of_matrix_product_le (A : Matrix m n ℝ) (B : Matrix n p ℝ) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  linfty_opNorm_mul _ _

end LInftyMatrixNorm



/-! #### 1. The L-infinity Norm (Operator Norm) -/
section LInfinityNorm
  -- Activate the operator norm scope for this section.
  open scoped Matrix.Norms.Operator
  open Matrix

  /--
  The L-infinity norm is the maximum absolute row sum.
  Essentially I just refactored the existing `linfty_opNorm_def` theorem in Matrix.lean
  -/
  theorem l_infinity_norm_def (A : Matrix m n ℝ) :
      ‖A‖ = ↑(Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) := by
    rw [linfty_opNorm_def]

  /-- Proof that the L-infinity operator norm satisfies the `IsMatrixNorm` axioms. -/
  theorem operatorNorm_is_matrixNorm_proof : IsMatrixNorm (norm : Matrix m n ℝ → ℝ) where
    non_neg _ := norm_nonneg _
    zero_iff_matrix_zero _ := norm_eq_zero
    scalar_multiple r A := by rw [norm_smul r A, Real.norm_eq_abs]
    sum_le_sum_of_norms _ _ := norm_add_le _ _

  -- Register the proof as a typeclass instance.
  instance operatorNorm_is_matrixNorm : IsMatrixNorm (norm : Matrix m n ℝ → ℝ) :=
    operatorNorm_is_matrixNorm_proof
end LInfinityNorm


-- /-! #### 2. The L1 Norm -/
-- section L1Norm
--   -- The L1 norm is not a built-in scoped norm in mathlib, so we define it directly.
--   noncomputable def l1Norm (A : Matrix m n ℝ) : ℝ := Finset.univ.sup fun j => ∑ i, |A i j|

--   /-- The L1 norm is the maximum absolute column sum. -/
--   theorem l1_norm_def (A : Matrix m n ℝ) :
--       l1Norm A = Finset.univ.sup fun j => ∑ i, |A i j| := rfl

--   /-- Proof that the L1 norm satisfies the `IsMatrixNorm` axioms. -/
--   theorem l1Norm_is_matrixNorm_proof : IsMatrixNorm (l1Norm : Matrix m n ℝ → ℝ) where
--     non_neg A := Finset.sup_nonneg fun j _ => Finset.sum_nonneg fun i _ => abs_nonneg _
--     zero_iff_matrix_zero A := by
--       simp [l1Norm, ← Finset.sup_eq_zero_iff, ← Finset.sum_eq_zero_iff_of_nonneg, abs_nonneg,
--         abs_eq_zero, funext_iff]
--     scalar_multiple r A := by
--       simp [l1Norm, Finset.mul_sup, Finset.sum_mul, abs_mul]
--     sum_le_sum_of_norms A B := by
--       simp_rw [l1Norm]
--       refine Finset.sup_le_sup_of_le fun j => ?_
--       calc
--         ∑ i, |A i j + B i j| ≤ ∑ i, (|A i j| + |B i j|) := Finset.sum_le_sum fun i _ => abs_add _ _
--         _ = (∑ i, |A i j|) + ∑ i, |B i j| := by rw [Finset.sum_add_distrib]
--         _ ≤ (Finset.univ.sup fun j' => ∑ i', |A i' j'|) + (Finset.univ.sup fun j' => ∑ i', |B i' j'|) :=
--           add_le_add (Finset.le_sup (Finset.mem_univ j)) (Finset.le_sup (Finset.mem_univ j))

--   -- Register the proof as a typeclass instance.
--   instance l1Norm_is_matrixNorm : IsMatrixNorm l1Norm :=
--     l1Norm_is_matrixNorm_proof
-- end L1Norm




-- /-! #### 3. The L2 Norm (Spectral Norm) -/
-- section L2Norm
--   -- The L2 norm requires the spectral theorem and is more complex.
--   -- We state its definition and assert it satisfies the axioms.
--   open Matrix


--   /-- The L2/spectral norm is the square root of the largest eigenvalue of `Aᵀ * A`.
--   Proving this requires the spectral theorem, which is a deep result in linear algebra. -/
--   theorem l2_norm_def (A : Matrix m n ℝ) :
--       (open scoped Matrix.Norms.L2Operator in ‖A‖) =
--         Real.sqrt (A.transpose * A).maxEigenvalue := by
--     sorry -- This proof requires the spectral theorem (`maxEigenvalue_eq_sup_quadForm`).

--   /-- Proof that the L2 operator norm satisfies the `IsMatrixNorm` axioms. -/
--   theorem l2Norm_is_matrixNorm_proof : IsMatrixNorm (fun A => open scoped Matrix.Norms.L2Operator in ‖A‖) where
--     non_neg _ := norm_nonneg _
--     zero_iff_matrix_zero _ := norm_eq_zero
--     scalar_multiple r A := by rw [norm_smul r A, Real.norm_eq_abs]
--     sum_le_sum_of_norms _ _ := norm_add_le _ _

--   -- Register the proof as a typeclass instance.
--   instance l2Norm_is_matrixNorm : IsMatrixNorm (fun A => open scoped Matrix.Norms.L2Operator in ‖A‖) :=
--     l2Norm_is_matrixNorm_proof
-- end L2Norm




/-! #### 4. The Max Norm (Element-wise L-infinity Norm) -/
section MaxNorm
  -- Activate the element-wise norm scope and open the Matrix namespace.
  open scoped Matrix.Norms.Elementwise
  open Matrix

  /-- The max norm is the largest absolute value of any single element. -/
  theorem max_norm_def (A : Matrix m n ℝ) :
      ‖A‖ = ↑(Finset.univ.sup fun i => Finset.univ.sup fun j => ‖A i j‖₊) :=
    norm_eq_sup_sup_nnnorm A

  /-- Proof that the max norm satisfies the `IsMatrixNorm` axioms. -/
  theorem maxNorm_is_matrixNorm_proof : IsMatrixNorm (norm : Matrix m n ℝ → ℝ) where
    non_neg _ := norm_nonneg _
    zero_iff_matrix_zero _ := norm_eq_zero
    scalar_multiple r A := by rw [norm_smul r A, Real.norm_eq_abs]
    sum_le_sum_of_norms _ _ := norm_add_le _ _

  -- Register the proof as a typeclass instance.
  instance maxNorm_is_matrixNorm : IsMatrixNorm (norm : Matrix m n ℝ → ℝ) :=
    maxNorm_is_matrixNorm_proof
end MaxNorm


/-! #### 5. The Frobenius Norm (Euclidean Norm) -/
section FrobeniusNorm
  -- Activate the Frobenius norm scope and open the Matrix namespace.
  open scoped Matrix.Norms.Frobenius

  /-- The Frobenius norm is the square root of the sum of squares of all elements. -/
  theorem frobenius_norm_def (A : Matrix m n ℝ) :
      ‖A‖ = Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) := by
    rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]

  /-- Proof that the Frobenius norm satisfies the `IsMatrixNorm` axioms. -/
  theorem frobeniusNorm_is_matrixNorm_proof : IsMatrixNorm (norm : Matrix m n ℝ → ℝ) where
    non_neg _ := norm_nonneg _
    zero_iff_matrix_zero _ := norm_eq_zero
    scalar_multiple r A := by rw [norm_smul r A, Real.norm_eq_abs]
    sum_le_sum_of_norms _ _ := norm_add_le _ _

  -- Register the proof as a typeclass instance.
  instance frobeniusNorm_is_matrixNorm : IsMatrixNorm (norm : Matrix m n ℝ → ℝ) :=
    frobeniusNorm_is_matrixNorm_proof
end FrobeniusNorm


instance : True :=
-- /-!
-- ### Examples of Common Matrix Norms
-- -/
-- section NormExamples

-- -- The L1-Norm: Maximum absolute column sum.
-- theorem l1_norm_def (A : Matrix m n ℝ) :
--     (Finset.univ.sup fun j => ∑ i, ‖A i j‖) = ‖A.toLin'‖ := by
--   sorry -- This requires connecting the definition to the `l1OpNorm` in mathlib.

-- -- The L2-Operator Norm (Spectral Norm): Square root of the largest eigenvalue of Aᵀ * A.
-- lemma spectral_norm_def (A : Matrix m n ℝ) :
--     (open scoped Matrix.Norms.L2Operator in ‖A‖) =
--       NNReal.sqrt (Finset.univ.sup fun i => ⟨_, A.eigenvalues_conjTranspose_mul_self_nonneg i⟩) := by
--   sorry -- This proof requires the spectral theorem for symmetric matrices.

-- -- The L-infinity Norm: Maximum absolute row sum.
-- theorem l_infinity_norm_def (A : Matrix m n ℝ) :
--     (open scoped Matrix.Norms.Operator in ‖A‖) =
--       ↑(Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) := by
--   rw [linfty_opNorm_def]

-- -- The Frobenius Norm (or Euclidean norm): Square root of the sum of squares of all elements.
-- theorem frobenius_norm_def (A : Matrix m n ℝ) :
--     (open scoped Matrix.Norms.Frobenius in ‖A‖) =
--       Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) := by
--   rw [frobenius_norm_def, Real.sqrt_eq_rpow]

-- -- The Max Norm (or Element-wise L-infinity norm): The largest absolute value of any element.
-- theorem max_norm_def (A : Matrix m n ℝ) :
--     (open scoped Matrix.Norms.Elementwise in ‖A‖) =
--       ↑(Finset.univ.sup fun ij : _ × _ => ‖A ij.1 ij.2‖₊) := by
--   -- This proof simplifies the definition by combining the row/column indices into a product set.
--   simp_rw [← Finset.univ_product_univ, Finset.sup_product_left, ← Pi.nnnorm_def, coe_nnnorm]

-- end NormExamples

-- end MatrixNorm
by trivial

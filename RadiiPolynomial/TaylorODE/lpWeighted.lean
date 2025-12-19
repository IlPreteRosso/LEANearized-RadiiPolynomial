import RadiiPolynomial.TaylorODE.ScaledReal
import RadiiPolynomial.TaylorODE.CauchyProduct
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Weighted ℓᵖ_ν Sequence Spaces

This file defines the weighted ℓᵖ space with weight ν > 0:

  ℓᵖ_ν = { a : ℕ → ℝ | ‖a‖_{p,ν} := (Σₙ |aₙ|^p · ν^{pn})^{1/p} < ∞ }

## Architecture Overview

The formalization separates **algebraic** and **analytic** concerns:

```
┌─────────────────────────────────────────────────────────────┐
│                     CauchyProduct.lean                      │
│  Pure algebra: ring axioms transported from PowerSeries     │
│  - assoc, comm, left_distrib, right_distrib                 │
│  - one, one_mul, mul_one                                    │
│  - smul_mul, mul_smul (scalar compatibility)                │
└─────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────┐
│                      lpWeighted.lean                        │
│  Analysis: norms, membership, submultiplicativity           │
│  - Weighted ℓᵖ space as lp (ScaledReal ν) p                 │
│  - Closure under Cauchy product (mem)                       │
│  - Submultiplicativity: ‖a ⋆ b‖ ≤ ‖a‖ · ‖b‖                 │
│  - Typeclass instances: Ring, CommRing, NormedRing          │
└─────────────────────────────────────────────────────────────┘
```

### Design Philosophy: "Transport from PowerSeries"

Ring axioms (associativity, distributivity, etc.) are **not** reproven manually.
Instead, `CauchyProduct.lean` establishes that the Cauchy product equals
`PowerSeries` multiplication via `toPowerSeries_mul`, then transports the
axioms. This file only proves the **analytic** properties:

1. **Membership closure**: `a, b ∈ ℓ¹_ν ⟹ a ⋆ b ∈ ℓ¹_ν`
2. **Submultiplicativity**: `‖a ⋆ b‖ ≤ ‖a‖ · ‖b‖` (Mertens + weight factorization)
3. **Norm of identity**: `‖1‖ = 1`

The ring axiom lemmas in this file are **thin wrappers** that lift the
`CauchyProduct` lemmas to `l1Weighted` via `lpWeighted.ext` and `congrFun`.

## Main Definitions

- `lpWeighted ν p`: The Banach space ℓᵖ_ν, defined as `lp (ScaledReal ν) p`
- `l1Weighted ν`: Specialization to p = 1
- `l1Weighted.mul`: Cauchy product multiplication on ℓ¹_ν
- `l1Weighted.one`: Identity element for the Banach algebra
- `l1Weighted.single`: Standard basis vectors

## Main Results

### Banach Space Structure
- `lpWeighted.instCompleteSpace`: ℓᵖ_ν is complete (inherited from Mathlib)

### Banach Algebra Structure (ℓ¹_ν only)
- `l1Weighted.mem`: Cauchy product preserves membership
- `l1Weighted.norm_mul_le`: Submultiplicativity `‖a ⋆ b‖ ≤ ‖a‖ · ‖b‖`
- `l1Weighted.instCommRing`: ℓ¹_ν is a commutative ring
- `l1Weighted.instNormedRing`: ℓ¹_ν is a normed ring
- `l1Weighted.instNormOneClass`: ‖1‖ = 1
- `l1Weighted.instSMulCommClass`: Scalar-ring multiplication compatibility
- `l1Weighted.instIsScalarTower`: Scalar tower compatibility
- `l1Weighted.instAlgebra`: ℓ¹_ν is an ℝ-algebra
- `l1Weighted.instNormedAlgebra`: ℓ¹_ν is a normed ℝ-algebra
- `l1Weighted.norm_pow_le`: ‖a^n‖ ≤ ‖a‖^n

## Dependencies

- `ScaledReal.lean`: Provides the scaled fiber type `ScaledReal ν n`
- `CauchyProduct.lean`: Provides algebraic properties (ring axioms)

## References

- Section 7.4 of the radii polynomial textbook
- Definition 7.4.1: Banach algebra axioms
- Theorem 7.4.4: Submultiplicativity proof
- Corollary 7.4.5: ℓ¹_ν is a commutative Banach algebra
-/

open scoped BigOperators Topology NNReal ENNReal Matrix

noncomputable section

/-! ## Part 1: Weighted ℓᵖ Space (General p)

`lpWeighted ν p` is the Banach space of sequences with finite weighted ℓᵖ norm.
Defined as `lp (ScaledReal ν) p`, inheriting completeness from Mathlib.

The norm is: ‖a‖_{p,ν} = (Σₙ |aₙ|^p · ν^{pn})^{1/p}
-/

/-- The weighted ℓᵖ_ν space, realized as lp with scaled fibers.

    **Key insight**: By using `ScaledReal ν n` (which has norm `|x| · νⁿ`) as the
    fiber at index n, the standard `lp` machinery gives us the weighted norm
    automatically. -/
abbrev lpWeighted (ν : PosReal) (p : ℝ≥0∞) := lp (ScaledReal ν) p

/-- Specialization to weighted ℓ¹.

    This is the main space of interest for the Banach algebra structure.
    See Section 7.4: ℓ¹_ν = { a : ℕ → ℝ | ‖a‖₁,ν := Σₙ |aₙ| νⁿ < ∞ } -/
abbrev l1Weighted (ν : PosReal) := lpWeighted ν 1

namespace lpWeighted

variable {ν : PosReal} {p : ℝ≥0∞}

/-! ### Inherited Topological Structure -/

instance instUniformSpace [Fact (1 ≤ p)] : UniformSpace (lpWeighted ν p) := by
  change UniformSpace (lp (ScaledReal ν) p)
  infer_instance

/-- ℓᵖ_ν is complete (a Banach space) for p ≥ 1.

    This is inherited from Mathlib's completeness of `lp`. -/
instance instCompleteSpace [Fact (1 ≤ p)] : CompleteSpace (lpWeighted ν p) := by
  change CompleteSpace (lp (ScaledReal ν) p)
  infer_instance

/-! ### Sequence Extraction -/

/-- Extract the underlying ℝ-valued sequence from a weighted ℓᵖ element.

    This "forgets" the weighted norm structure and gives a plain function ℕ → ℝ. -/
def toSeq {ν : PosReal} (a : lpWeighted ν p) : ℕ → ℝ := fun n => ScaledReal.toReal (a n)

/-- Extensionality: two weighted sequences are equal iff their underlying
    real sequences are equal. -/
lemma ext {a b : lpWeighted ν p} (h : ∀ n, toSeq a n = toSeq b n) : a = b :=
  lp.ext (funext h)

/-! ### Membership and Construction -/

/-- Membership predicate: a sequence has finite weighted ℓᵖ norm. -/
def Mem (ν : PosReal) (p : ℝ≥0∞) (a : ℕ → ℝ) : Prop :=
  Memℓp (fun n => ScaledReal.ofReal (a n) : ∀ n, ScaledReal ν n) p

/-- Construct a weighted ℓᵖ element from a sequence with finite weighted norm. -/
def mk (a : ℕ → ℝ) (ha : Mem ν p a) : lpWeighted ν p :=
  ⟨fun n => ScaledReal.ofReal (a n), ha⟩

/-! ### Simp Lemmas for Sequence Operations -/

@[simp] lemma toSeq_apply (a : lpWeighted ν p) (n : ℕ) : toSeq a n = a n := rfl
@[simp] lemma mk_apply (a : ℕ → ℝ) (ha : Mem ν p a) (n : ℕ) : toSeq (mk a ha) n = a n := rfl
@[simp] lemma zero_toSeq (n : ℕ) : toSeq (0 : lpWeighted ν p) n = 0 := rfl
@[simp] lemma neg_toSeq (a : lpWeighted ν p) (n : ℕ) : toSeq (-a) n = -toSeq a n := rfl
@[simp] lemma add_toSeq (a b : lpWeighted ν p) (n : ℕ) : toSeq (a + b) n = toSeq a n + toSeq b n := rfl
@[simp] lemma sub_toSeq (a b : lpWeighted ν p) (n : ℕ) : toSeq (a - b) n = toSeq a n - toSeq b n := rfl
@[simp] lemma smul_toSeq (c : ℝ) (a : lpWeighted ν p) (n : ℕ) : toSeq (c • a) n = c * toSeq a n := rfl

/-! ### Norm Characterization -/

/-- The norm for lpWeighted expressed as a weighted sum. -/
lemma norm_eq_tsum_rpow (hp : 0 < p.toReal) (a : lpWeighted ν p) :
    ‖a‖ = (∑' n, (|toSeq a n| * (ν : ℝ) ^ n) ^ p.toReal) ^ (1 / p.toReal) := by
  rw [lp.norm_eq_tsum_rpow hp]
  simp only [one_div, toSeq_apply]
  rfl

/-- Membership in ℓᵖ_ν ↔ weighted p-th power sum is summable. -/
lemma mem_iff_summable (hp : 0 < p.toReal) (a : ℕ → ℝ) (hp' : p ≠ ⊤) :
    Mem ν p a ↔ Summable fun n => (|a n| * (ν : ℝ) ^ n) ^ p.toReal := by
  simp only [Mem, Memℓp, ScaledReal.ofReal_apply, ne_eq]
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp
  simp only [hp0, hp', ↓reduceIte, ScaledReal.norm_def, ScaledReal.toReal_apply]

end lpWeighted


/-! ## Part 2: Weighted ℓ¹ Specialization

This section provides the API specific to `l1Weighted ν`, the weighted ℓ¹ space.
The key simplification is that the norm becomes a simple weighted sum (no p-th powers).
-/

namespace l1Weighted

variable {ν : PosReal}

instance : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_refl 1⟩

/-- Alias for `lpWeighted.toSeq` in the ℓ¹ setting. -/
abbrev toSeq (a : l1Weighted ν) := lpWeighted.toSeq a

/-- The ℓ¹_ν norm is a simple weighted sum: ‖a‖ = Σₙ |aₙ| νⁿ -/
lemma norm_eq_tsum (a : l1Weighted ν) : ‖a‖ = ∑' n, |toSeq a n| * (ν : ℝ) ^ n := by
  have h := lpWeighted.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) a
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one, Real.rpow_one] at h
  exact h

/-- Membership in ℓ¹_ν ↔ weighted sum is summable. -/
lemma mem_iff (a : ℕ → ℝ) :
    lpWeighted.Mem ν 1 a ↔ Summable fun n => |a n| * (ν : ℝ) ^ n := by
  have h := @lpWeighted.mem_iff_summable ν 1 (by norm_num : 0 < (1 : ℝ≥0∞).toReal) a ENNReal.one_ne_top
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  exact h

/-! ### Standard Basis Vectors

The single element `single n x` represents the sequence that is `x` at position `n`
and `0` elsewhere. These are the standard basis vectors of ℓ¹_ν scaled by `x`.
-/

/-- The single element in ℓ¹_ν: value `x` at position `n`, zero elsewhere.

    This is the standard basis vector eₙ scaled by x. See Theorem 7.3.8. -/
def single (n : ℕ) (x : ℝ) : l1Weighted ν :=
  lpWeighted.mk (fun k => if k = n then x else 0) (by
    rw [mem_iff]
    have h : (fun k => |if k = n then x else 0| * (ν : ℝ) ^ k) =
             fun k => if k = n then |x| * (ν : ℝ) ^ n else 0 := by
      ext k
      split_ifs with hk <;> simp [hk]
    rw [h]
    exact summable_of_ne_finset_zero (s := {n}) (fun k hk => by simp at hk; simp [hk]))

@[simp]
lemma single_toSeq_self (n : ℕ) (x : ℝ) : toSeq (single n x : l1Weighted ν) n = x := by
  simp only [lpWeighted.toSeq_apply, single, lpWeighted.mk]
  rfl

@[simp]
lemma single_toSeq_ne (n k : ℕ) (x : ℝ) (h : k ≠ n) : toSeq (single n x : l1Weighted ν) k = 0 := by
  simp [single, lpWeighted.mk, h]

/-- Norm of single element: ‖δₙ(x)‖ = |x| · νⁿ. See Theorem 7.3.8. -/
lemma norm_single (n : ℕ) (x : ℝ) : ‖(single n x : l1Weighted ν)‖ = |x| * (ν : ℝ) ^ n := by
  rw [norm_eq_tsum]
  have h : (fun k => |toSeq (single n x : l1Weighted ν) k| * (ν : ℝ) ^ k) =
           fun k => if k = n then |x| * (ν : ℝ) ^ n else 0 := by
    ext k
    split_ifs with hk <;> simp [hk, single, lpWeighted.mk]
  rw [h, tsum_ite_eq]

/-! ### Finite-Dimensional Weighted Norms

These definitions support the finite-dimensional truncation used in Example 7.7.
See Exercise 2.7.2 for the theory of finite-dimensional weighted norms.
-/

variable {N : ℕ}

/-- Finite weighted ℓ¹ norm: ‖x‖₁,ν = Σₙ |xₙ| νⁿ -/
def finl1WeightedNorm (ν : ℝ≥0) (x : Fin (N + 1) → ℝ) : ℝ :=
  ∑ n : Fin (N + 1), |x n| * (ν : ℝ) ^ (n : ℕ)

/-- Column norm for matrix: (1/νʲ) Σᵢ |Aᵢⱼ| νⁱ.

    This appears in the weighted operator norm formula. See equation (7.9). -/
def matrixColNorm (ν : PosReal) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (j : Fin (N + 1)) : ℝ :=
  (1 / (ν : ℝ) ^ (j : ℕ)) * ∑ i : Fin (N + 1), |A i j| * (ν : ℝ) ^ (i : ℕ)

/-- Induced matrix norm: ‖A‖_{ν,N} = max_j (1/νʲ) Σᵢ |Aᵢⱼ| νⁱ.

    This is the operator norm on finite-dimensional weighted ℓ¹. See Exercise 2.7.2. -/
def finWeightedMatrixNorm (ν : PosReal) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun j => matrixColNorm ν A j)

/-- **Key weight factorization**: νᵏ · νˡ = νⁿ when k + l = n.

    This is the crucial property enabling submultiplicativity (Theorem 7.4.4).
    The proof of `norm_mul_le` relies on this to factor νⁿ across antidiagonal pairs. -/
lemma antidiagonal_weight (n : ℕ) (k l : ℕ) (h : k + l = n) :
    (ν : ℝ) ^ k * (ν : ℝ) ^ l = (ν : ℝ) ^ n := by
  rw [← pow_add, h]

/-! ### Finite Weighted Matrix Norm Properties -/

lemma matrixColNorm_nonneg (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (j : Fin (N + 1)) :
    0 ≤ matrixColNorm ν A j := by
  unfold matrixColNorm
  apply mul_nonneg
  · apply div_nonneg zero_le_one (pow_nonneg (PosReal.coe_nonneg ν) _)
  · apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) _)

lemma finWeightedMatrixNorm_nonneg (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    0 ≤ finWeightedMatrixNorm ν A := by
  apply Finset.le_sup'_of_le _ (Finset.mem_univ 0)
  exact matrixColNorm_nonneg A 0

lemma matrixColNorm_one (j : Fin (N + 1)) :
    matrixColNorm ν (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) j = 1 := by
  unfold matrixColNorm
  simp only [Matrix.one_apply]
  rw [Finset.sum_eq_single j]
  · simp only [↓reduceIte, abs_one, one_mul, one_div]
    have : (ν : ℝ) ^ (j : ℕ) ≠ 0 := pow_ne_zero _ (PosReal.coe_ne_zero ν)
    field_simp [this]
  · intro i _ hi; simp [hi]
  · intro h; exact absurd (Finset.mem_univ j) h

lemma finWeightedMatrixNorm_one :
    finWeightedMatrixNorm ν (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) = 1 := by
  unfold finWeightedMatrixNorm
  apply le_antisymm
  · apply Finset.sup'_le; intro j _; rw [matrixColNorm_one]
  · apply Finset.le_sup'_of_le _ (Finset.mem_univ 0); rw [matrixColNorm_one]

lemma matrixColNorm_eq (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (j : Fin (N + 1)) :
    matrixColNorm ν A j = (∑ i : Fin (N + 1), |A i j| * (ν : ℝ) ^ (i : ℕ)) / (ν : ℝ) ^ (j : ℕ) := by
  unfold matrixColNorm; ring

end l1Weighted


/-! ## Part 3: Banach Algebra Structure

This section establishes that ℓ¹_ν is a commutative Banach algebra (Corollary 7.4.5).

### What is a Banach Algebra? (Definition 7.4.1)

A **Banach algebra** is a Banach space X with multiplication `·: X × X → X` satisfying:

1. **Associativity** (7.11): `x · (y · z) = (x · y) · z`
2. **Distributivity** (7.12): `(x + y) · z = x · z + y · z` and `x · (y + z) = x · y + x · z`
3. **Scalar compatibility** (7.13): `α(x · y) = (αx) · y = x · (αy)`
4. **Submultiplicativity** (7.14): `‖x · y‖ ≤ ‖x‖ · ‖y‖`

The algebra is **commutative** if `x · y = y · x` for all x, y.

### Correspondence: Textbook ↔ Lean

| Textbook                | Equation | Lean Instance/Lemma                      |
|-------------------------|----------|------------------------------------------|
| Banach space            |          | `CompleteSpace`, `NormedAddCommGroup`    |
| Associativity           | (7.11)   | `instRing.mul_assoc`                     |
| Left distributivity     | (7.12)   | `instRing.left_distrib`                  |
| Right distributivity    | (7.12)   | `instRing.right_distrib`                 |
| Scalar compatibility    | (7.13)   | `instIsScalarTower`, `instSMulCommClass` |
| Submultiplicativity     | (7.14)   | `instNormedRing.norm_mul_le`             |
| Commutativity           |          | `instCommRing.mul_comm`                  |
| Unit element            |          | `instRing.one_mul`, `instRing.mul_one`   |
| ‖1‖ = 1                 |          | `instNormOneClass`                       |
| ℝ-algebra structure     |          | `instAlgebra`, `instNormedAlgebra`       |

### Why This Architecture?

**Axioms (1)-(3)** are **pure algebra** — they don't involve norms.
These are proven in `CauchyProduct.lean` by connecting to `PowerSeries R`,
where Mathlib has already established the ring structure.

**Axiom (4)** is **analysis** — it requires norm estimates.
This is proven here using Mertens' theorem and weight factorization.

### Structure of This Section

1. **Membership closure** (`mem`): Proves `a, b ∈ ℓ¹_ν ⟹ a ⋆ b ∈ ℓ¹_ν`
2. **Multiplication** (`mul`): Defines the ring multiplication
3. **Submultiplicativity** (`norm_mul_le`): The key analytic result (7.14)
4. **Ring axioms**: Thin wrappers lifting `CauchyProduct` lemmas (7.11-7.13)
5. **Identity element** (`one`): The Kronecker delta sequence
6. **Typeclass instances**: `Ring`, `CommRing`, `NormedRing`, `NormOneClass`
7. **Algebra structure**: `SMulCommClass`, `IsScalarTower`, `Algebra`, `NormedAlgebra`
-/

section CauchyProductBanachAlgebra

namespace l1Weighted

/-! ### Closure Under Multiplication

This is the first analytic result: the Cauchy product of two ℓ¹_ν sequences
is again in ℓ¹_ν. The proof uses Mertens' theorem and weight factorization.
-/

/-- Cauchy product preserves membership in ℓ¹_ν.

    **Proof sketch** (Theorem 7.4.4):
    1. Apply Mertens' theorem to reorder the double sum
    2. Use weight factorization νⁿ = νᵏ · νˡ for k + l = n
    3. Bound by ‖a‖ · ‖b‖ -/
lemma mem {ν : PosReal} {a b : ℕ → ℝ}
    (ha : lpWeighted.Mem ν 1 a) (hb : lpWeighted.Mem ν 1 b) :
    lpWeighted.Mem ν 1 (a ⋆ b) := by
  rw [l1Weighted.mem_iff] at ha hb ⊢
  let f := fun k => |a k| * (ν : ℝ) ^ k
  let g := fun l => |b l| * (ν : ℝ) ^ l
  have hf_nn : ∀ k, 0 ≤ f k := fun k => mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) k)
  have hg_nn : ∀ l, 0 ≤ g l := fun l => mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) l)
  have hprod : Summable (fun x : ℕ × ℕ => f x.1 * g x.2) :=
    Summable.mul_of_nonneg ha hb hf_nn hg_nn
  have hsum := summable_sum_mul_antidiagonal_of_summable_mul hprod
  apply Summable.of_nonneg_of_le
  · intro n; exact mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) n)
  · intro n
    calc |CauchyProduct a b n| * (ν : ℝ) ^ n
        ≤ (∑ kl ∈ Finset.antidiagonal n, |a kl.1| * |b kl.2|) * (ν : ℝ) ^ n := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (PosReal.coe_nonneg ν) n)
          calc |CauchyProduct a b n|
              = |∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2| := rfl
            _ ≤ ∑ kl ∈ Finset.antidiagonal n, |a kl.1 * b kl.2| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ kl ∈ Finset.antidiagonal n, |a kl.1| * |b kl.2| := by simp_rw [abs_mul]
      _ = ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro kl hkl
          simp only [f, g, ← l1Weighted.antidiagonal_weight n kl.1 kl.2 (Finset.mem_antidiagonal.mp hkl)]
          ring
  · exact hsum

/-! ### Multiplication Definition -/

/-- Multiplication via Cauchy product.

    This defines the Banach algebra multiplication on ℓ¹_ν.
    The @[simp] attribute ensures that `mul a b` unfolds in simp calls. -/
@[simp]
def mul {ν : PosReal} (a b : l1Weighted ν) : l1Weighted ν :=
  lpWeighted.mk (lpWeighted.toSeq a ⋆ lpWeighted.toSeq b) (mem a.2 b.2)

/-! ### Submultiplicativity (Key Analytic Property)

This is **axiom (4)** of Definition 7.4.1, the defining property of a Banach algebra.
-/

/-- **Submultiplicativity** (Theorem 7.4.4, Equation 7.17):
    `‖a ⋆ b‖₁,ν ≤ ‖a‖₁,ν · ‖b‖₁,ν`

    This makes ℓ¹_ν a Banach algebra. The proof uses:
    1. Mertens' theorem to exchange sum order
    2. Weight factorization: νⁿ = νᵏ · νˡ for k + l = n -/
lemma norm_mul_le {ν : PosReal} (a b : l1Weighted ν) : ‖mul a b‖ ≤ ‖a‖ * ‖b‖ := by
  simp only [mul]
  rw [l1Weighted.norm_eq_tsum, l1Weighted.norm_eq_tsum, l1Weighted.norm_eq_tsum]
  let f := fun k => |lpWeighted.toSeq a k| * (ν : ℝ) ^ k
  let g := fun l => |lpWeighted.toSeq b l| * (ν : ℝ) ^ l
  have hf_nn : ∀ k, 0 ≤ f k := fun k => mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) k)
  have hg_nn : ∀ l, 0 ≤ g l := fun l => mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) l)
  have hf : Summable f := (l1Weighted.mem_iff _).mp a.2
  have hg : Summable g := (l1Weighted.mem_iff _).mp b.2
  have hprod : Summable (fun x : ℕ × ℕ => f x.1 * g x.2) :=
    Summable.mul_of_nonneg hf hg hf_nn hg_nn
  rw [hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hprod]
  refine Summable.tsum_le_tsum ?_ ((l1Weighted.mem_iff _).mp (mem a.2 b.2))
    (summable_sum_mul_antidiagonal_of_summable_mul hprod)
  intro n
  simp only [lpWeighted.mk_apply]
  calc |CauchyProduct (lpWeighted.toSeq a) (lpWeighted.toSeq b) n| * (ν : ℝ) ^ n
      ≤ (∑ kl ∈ Finset.antidiagonal n, |lpWeighted.toSeq a kl.1| * |lpWeighted.toSeq b kl.2|) * (ν : ℝ) ^ n := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (PosReal.coe_nonneg ν) n)
        calc |CauchyProduct (lpWeighted.toSeq a) (lpWeighted.toSeq b) n|
            = |∑ kl ∈ Finset.antidiagonal n, lpWeighted.toSeq a kl.1 * lpWeighted.toSeq b kl.2| := rfl
          _ ≤ ∑ kl ∈ Finset.antidiagonal n, |lpWeighted.toSeq a kl.1 * lpWeighted.toSeq b kl.2| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ kl ∈ Finset.antidiagonal n, |lpWeighted.toSeq a kl.1| * |lpWeighted.toSeq b kl.2| := by
              simp_rw [abs_mul]
    _ = ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro kl hkl
        simp only [f, g, ← l1Weighted.antidiagonal_weight n kl.1 kl.2 (Finset.mem_antidiagonal.mp hkl)]
        ring

/-! ### Ring Axioms (Lifted from CauchyProduct)

These lemmas are **thin wrappers** that lift the algebraic properties from
`CauchyProduct` to `l1Weighted`. Each follows the same pattern:

1. Apply `lpWeighted.ext` to reduce to pointwise equality
2. Unfold `mul` to expose the Cauchy product
3. Apply the corresponding `CauchyProduct` lemma via `congrFun`

This architecture avoids re-proving ring axioms and ensures consistency
with the `PowerSeries` multiplication structure.
-/

lemma mul_comm {ν : PosReal} (a b : l1Weighted ν) : mul a b = mul b a := by
  apply lpWeighted.ext; intro n
  simp only [mul, lpWeighted.mk_apply]
  rw [CauchyProduct.comm]

lemma mul_assoc {ν : PosReal} (a b c : l1Weighted ν) : mul (mul a b) c = mul a (mul b c) := by
  apply lpWeighted.ext; intro n
  simp only [mul, lpWeighted.mk_apply]
  exact congrFun (CauchyProduct.assoc _ _ _) n

lemma left_distrib {ν : PosReal} (a b c : l1Weighted ν) : mul a (b + c) = mul a b + mul a c := by
  apply lpWeighted.ext; intro n
  simp only [mul, lpWeighted.mk_apply, lpWeighted.add_toSeq]
  exact congrFun (CauchyProduct.left_distrib _ _ _) n

lemma right_distrib {ν : PosReal} (a b c : l1Weighted ν) : mul (a + b) c = mul a c + mul b c := by
  apply lpWeighted.ext; intro n
  simp only [mul, lpWeighted.mk_apply, lpWeighted.add_toSeq]
  exact congrFun (CauchyProduct.right_distrib _ _ _) n

lemma zero_mul {ν : PosReal} (a : l1Weighted ν) : mul 0 a = 0 := by
  apply lpWeighted.ext; intro n
  simp only [mul, lpWeighted.mk_apply, lpWeighted.zero_toSeq]
  exact congrFun (CauchyProduct.zero_mul _) n

lemma mul_zero {ν : PosReal} (a : l1Weighted ν) : mul a 0 = 0 := by
  apply lpWeighted.ext; intro n
  simp only [mul, lpWeighted.mk_apply, lpWeighted.zero_toSeq]
  exact congrFun (CauchyProduct.mul_zero _) n

/-! ### Identity Element

The multiplicative identity is `CauchyProduct.one`: the Kronecker delta sequence
with e₀ = 1 and eₙ = 0 for n ≥ 1. See Theorem 7.4.6.
-/

lemma one_mem (ν : PosReal) : lpWeighted.Mem ν 1 CauchyProduct.one := by
  rw [l1Weighted.mem_iff]
  have h : (fun n => |CauchyProduct.one n| * (ν : ℝ) ^ n) = fun n => if n = 0 then 1 else 0 := by
    ext n
    cases n with
    | zero => simp [CauchyProduct.one]
    | succ n => simp [CauchyProduct.one]
  rw [h]
  exact summable_of_ne_finset_zero (s := {0}) (fun n hn => by simp at hn; simp [hn])

/-- The multiplicative identity element of ℓ¹_ν (Kronecker delta). -/
def one (ν : PosReal) : l1Weighted ν := lpWeighted.mk CauchyProduct.one (one_mem ν)

@[simp] lemma one_toSeq_zero {ν : PosReal} : lpWeighted.toSeq (one ν) 0 = 1 := rfl
@[simp] lemma one_toSeq_succ {ν : PosReal} (n : ℕ) : lpWeighted.toSeq (one ν) (n + 1) = 0 := rfl
@[simp] lemma one_toSeq {ν : PosReal} : lpWeighted.toSeq (one ν) = CauchyProduct.one := rfl

lemma mul_one {ν : PosReal} (a : l1Weighted ν) : mul a (one ν) = a := by
  apply lpWeighted.ext; intro n
  simp only [mul, lpWeighted.mk_apply, one_toSeq]
  rw [CauchyProduct.mul_one]

lemma one_mul {ν : PosReal} (a : l1Weighted ν) : mul (one ν) a = a := by
  apply lpWeighted.ext; intro n
  simp only [mul, lpWeighted.mk_apply, one_toSeq]
  rw [CauchyProduct.one_mul]

lemma norm_one (ν : PosReal) : ‖one ν‖ = 1 := by
  rw [l1Weighted.norm_eq_tsum]
  have h : (fun n => |lpWeighted.toSeq (one ν) n| * (ν : ℝ) ^ n) =
           fun n => if n = 0 then 1 else 0 := by
    ext n
    cases n with
    | zero => simp [one, CauchyProduct.one, lpWeighted.mk]
    | succ n => simp [one, CauchyProduct.one, lpWeighted.mk]
  rw [h, tsum_ite_eq]

/-! ### Typeclass Instances

These instances register ℓ¹_ν as a commutative Banach algebra with Lean's
typeclass system, enabling generic lemmas and tactics like `ring`.
-/

instance instRing {ν : PosReal} : Ring (l1Weighted ν) where
  mul := mul
  mul_assoc := mul_assoc
  one := one ν
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero

instance instCommRing {ν : PosReal} : CommRing (l1Weighted ν) where
  mul_comm := mul_comm

instance instNormedRing {ν : PosReal} : NormedRing (l1Weighted ν) where
  dist_eq := fun _ _ => rfl
  norm_mul_le := norm_mul_le

instance instNormOneClass {ν : PosReal} : NormOneClass (l1Weighted ν) where
  norm_one := norm_one ν

/-! ### Algebra Structure (Scalar-Ring Compatibility)

These instances establish that scalar multiplication (by ℝ) is compatible with
ring multiplication, making ℓ¹_ν an ℝ-algebra. This enables:

- `smul_mul_assoc`: `(c • a) * b = c • (a * b)`
- `smul_comm`: `c • (a * b) = a * (c • b)`

These are used in `FrechetCauchyProduct.lean` for the derivative formula.
-/

/-- Scalar multiplication commutes with ring multiplication.

    Says: `c • (a * b) = a * (c • b)` for scalars c ∈ ℝ.
    Uses `CauchyProduct.mul_smul` from the algebra layer. -/
instance instSMulCommClass {ν : PosReal} : SMulCommClass ℝ (l1Weighted ν) (l1Weighted ν) where
  smul_comm c a b := by
    change c • (a * b) = a * (c • b)
    apply lpWeighted.ext; intro n
    simp only [lpWeighted.toSeq_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    exact congrFun (CauchyProduct.mul_smul c a.val b.val).symm n

/-- Scalar multiplication is associative with ring multiplication.

    Says: `(c • a) * b = c • (a * b)` for scalars c ∈ ℝ.
    Uses `CauchyProduct.smul_mul` from the algebra layer. -/
instance instIsScalarTower {ν : PosReal} : IsScalarTower ℝ (l1Weighted ν) (l1Weighted ν) where
  smul_assoc c a b := by
    change (c • a) * b = c • (a * b)
    apply lpWeighted.ext; intro n
    simp only [lpWeighted.toSeq_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    exact congrFun (CauchyProduct.smul_mul c a.val b.val) n

/-! ### Full Algebra Structure

These instances complete the Banach algebra structure by registering ℓ¹_ν as an
ℝ-algebra. The `Algebra ℝ` instance bundles the ring homomorphism `algebraMap`
that embeds ℝ into ℓ¹_ν via `r ↦ r • 1 = (r, 0, 0, ...)`.
-/

/-- ℓ¹_ν is an ℝ-algebra.

    The `algebraMap : ℝ →+* l1Weighted ν` sends `r ↦ r • 1 = (r, 0, 0, ...)`.
    This is synthesized from `SMulCommClass` and `IsScalarTower` via `Algebra.ofModule`. -/
instance instAlgebra {ν : PosReal} : Algebra ℝ (l1Weighted ν) := Algebra.ofModule
  (fun r a b => smul_mul_assoc r a b)
  (fun r a b => mul_smul_comm r a b)

@[simp]
lemma algebraMap_apply {ν : PosReal} (r : ℝ) : algebraMap ℝ (l1Weighted ν) r = r • 1 := rfl

/-- The algebraMap sends r to the scaled identity: r · 𝟙 = (r, 0, 0, ...). -/
lemma algebraMap_toSeq {ν : PosReal} (r : ℝ) (n : ℕ) :
    lpWeighted.toSeq (algebraMap ℝ (l1Weighted ν) r) n = r * CauchyProduct.one n := by
  rw [algebraMap_apply, lpWeighted.smul_toSeq, ←one_toSeq, lpWeighted.toSeq_apply, mul_eq_mul_left_iff]
  apply Or.inl
  rfl

/-- The norm of `algebraMap r` equals `|r|`. -/
lemma norm_algebraMap {ν : PosReal} (r : ℝ) : ‖algebraMap ℝ (l1Weighted ν) r‖ = ‖r‖ := by
  simp only [algebraMap_apply, norm_smul, Real.norm_eq_abs, NormOneClass.norm_one, _root_.mul_one]

/-- ℓ¹_ν is a normed ℝ-algebra.

    Requires `‖c • a‖ ≤ ‖c‖ * ‖a‖`, which holds with equality by `norm_smul`. -/
instance instNormedAlgebra {ν : PosReal} : NormedAlgebra ℝ (l1Weighted ν) where
  norm_smul_le := fun r a => by rw [norm_smul]

/-! ### Power Bounds

Note: Mathlib provides `norm_pow_le` for `NormedRing` + `NormOneClass`, but we
include it explicitly for completeness and documentation. -/

/-- Norm bound for powers: ‖a^n‖ ≤ ‖a‖^n.

    Follows from submultiplicativity by induction. -/
lemma norm_pow_le {ν : PosReal} (a : l1Weighted ν) (n : ℕ) : ‖a ^ n‖ ≤ ‖a‖ ^ n := by
  induction n with
  | zero => simp only [pow_zero, NormOneClass.norm_one, le_refl]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    have h : ‖a ^ n * a‖ ≤ ‖a‖ ^ n * ‖a‖ :=
      calc ‖a ^ n * a‖ ≤ ‖a ^ n‖ * ‖a‖ := norm_mul_le _ _
        _ ≤ ‖a‖ ^ n * ‖a‖ := mul_le_mul_of_nonneg_right ih (norm_nonneg _)
    simpa [pow_succ] using h


end l1Weighted

end CauchyProductBanachAlgebra

end

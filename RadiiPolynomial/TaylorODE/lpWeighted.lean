import RadiiPolynomial.TaylorODE.ScaledReal
import RadiiPolynomial.TaylorODE.CauchyProduct

/-!
# Weighted ℓᵖ_ν Sequence Spaces

This file defines the weighted ℓᵖ space with weight ν > 0:
  ℓᵖ_ν = { a : ℕ → ℝ | ‖a‖_{p,ν} := (Σₙ |aₙ|^p · ν^{pn})^{1/p} < ∞ }

## Implementation

We realize ℓᵖ_ν as `lp (ScaledReal ν) p` where `ScaledReal ν n` is ℝ equipped with
the scaled norm `‖x‖ₙ = |x| · νⁿ`. This gives us:
- `NormedAddCommGroup` and `NormedSpace ℝ` for free
- `CompleteSpace` (Banach) from Mathlib's lp theory

The Cauchy product (convolution) is defined for ℓ¹_ν specifically.

## Main definitions

- `ScaledReal ν n`: ℝ with norm `|x| · νⁿ`
- `lpWeighted ν p`: The Banach space ℓᵖ_ν, defined as `lp (ScaledReal ν) p`
- `l1Weighted ν`: Specialization to p = 1
- `CauchyProduct`: Convolution `(a ⋆ b)ₙ = Σⱼ₌₀ⁿ aₙ₋ⱼ bⱼ` (for ℓ¹)

## References

- Section 7.4 of the radii polynomial textbook
- Exercise 2.7.2 for finite-dimensional weighted norms
-/

open scoped BigOperators Topology NNReal ENNReal Matrix

noncomputable section nonComp

/-! ## Weighted ℓᵖ Space

`lpWeighted ν p` is the Banach space of sequences with finite weighted ℓᵖ norm.
Defined as `lp (ScaledReal ν) p`, inheriting completeness from Mathlib.

The norm is: ‖a‖_{p,ν} = (Σₙ |aₙ|^p · ν^{pn})^{1/p}

See Section 7.4 for the definition of ℓ¹_ν and its Banach algebra structure.
-/

/-- The weighted ℓᵖ_ν space, realized as lp with scaled fibers -/
abbrev lpWeighted (ν : PosReal) (p : ℝ≥0∞) := lp (ScaledReal ν) p

/-- Specialization to weighted ℓ¹.
    See Section 7.4: ℓ¹_ν = { a : ℕ → ℂ | ‖a‖₁,ν := Σₙ |aₙ| νⁿ < ∞ } -/
abbrev l1Weighted (ν : PosReal) := lpWeighted ν 1

namespace lpWeighted

variable {ν : PosReal} {p : ℝ≥0∞}

/-- Extract the underlying ℝ sequence -/
def toSeq (a : lpWeighted ν p) : ℕ → ℝ := fun n => ScaledReal.toReal (a n)

lemma ext {a b : lpWeighted ν p} (h : ∀ n, toSeq a n = toSeq b n) : a = b :=
  lp.ext (funext h)

/-- Membership predicate: sequence has finite weighted ℓᵖ norm -/
def Mem (ν : PosReal) (p : ℝ≥0∞) (a : ℕ → ℝ) : Prop :=
  Memℓp (fun n => ScaledReal.ofReal (a n) : ∀ n, ScaledReal ν n) p

/-- Construct an element from a sequence with finite weighted norm -/
def mk (a : ℕ → ℝ) (ha : Mem ν p a) : lpWeighted ν p :=
  ⟨fun n => ScaledReal.ofReal (a n), ha⟩

@[simp] lemma toSeq_apply (a : lpWeighted ν p) (n : ℕ) : toSeq a n = a n := rfl
@[simp] lemma mk_apply (a : ℕ → ℝ) (ha : Mem ν p a) (n : ℕ) : toSeq (mk a ha) n = a n := rfl
@[simp] lemma zero_toSeq (n : ℕ) : toSeq (0 : lpWeighted ν p) n = 0 := rfl
@[simp] lemma neg_toSeq (a : lpWeighted ν p) (n : ℕ) : toSeq (-a) n = -toSeq a n := rfl
@[simp] lemma add_toSeq (a b : lpWeighted ν p) (n : ℕ) : toSeq (a + b) n = toSeq a n + toSeq b n := rfl
@[simp] lemma sub_toSeq (a b : lpWeighted ν p) (n : ℕ) : toSeq (a - b) n = toSeq a n - toSeq b n := rfl
@[simp] lemma smul_toSeq (c : ℝ) (a : lpWeighted ν p) (n : ℕ) : toSeq (c • a) n = c * toSeq a n := rfl



section NormCharacterization

/-- The norm for lpWeighted: ‖a‖ = ( Σₙ |aₙ|^p · ν^{pn} )^{1/p} -/
lemma norm_eq_tsum_rpow (hp : 0 < p.toReal) (a : lpWeighted ν p) :
    ‖a‖ = (∑' n, (|toSeq a n| * (ν : ℝ) ^ n) ^ p.toReal) ^ (1 / p.toReal) := by
  rw [lp.norm_eq_tsum_rpow hp]
  simp only [one_div, toSeq_apply]
  rfl

/-- Membership in ℓᵖ_ν ↔ weighted p-th power sum is summable -/
lemma mem_iff_summable (hp : 0 < p.toReal) (a : ℕ → ℝ) (hp' : p ≠ ⊤) :
    Mem ν p a ↔ Summable fun n => (|a n| * (ν : ℝ) ^ n) ^ p.toReal := by
  simp only [Mem, Memℓp, ScaledReal.ofReal_apply, ne_eq]
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp
  simp only [hp0, hp', ↓reduceIte, ScaledReal.norm_def, ScaledReal.toReal_apply]

end NormCharacterization

end lpWeighted


/-! ## Weighted ℓ¹ Specialization -/

namespace l1Weighted

variable {ν : PosReal}

instance : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_refl 1⟩

/-- Alias for lpWeighted.toSeq -/
abbrev toSeq (a : l1Weighted ν) := lpWeighted.toSeq a

/-- The norm is the weighted sum: ‖a‖ = Σₙ |aₙ| νⁿ -/
lemma norm_eq_tsum (a : l1Weighted ν) : ‖a‖ = ∑' n, |toSeq a n| * (ν : ℝ) ^ n := by
  have h := lpWeighted.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) a
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one, Real.rpow_one] at h
  exact h

/-- Membership in ℓ¹_ν ↔ weighted sum is summable -/
lemma mem_iff (a : ℕ → ℝ) :
    lpWeighted.Mem ν 1 a ↔ Summable fun n => |a n| * (ν : ℝ) ^ n := by
  have h := @lpWeighted.mem_iff_summable ν 1 (by norm_num : 0 < (1 : ℝ≥0∞).toReal) a ENNReal.one_ne_top
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  exact h



/-! ### Finite-Dimensional Weighted Norms

See Exercise 2.7.2 for finite-dimensional weighted norms.
-/

variable {N : ℕ}

/-- Finite weighted ℓ¹ norm: ‖x‖₁,ν = Σₙ |xₙ| νⁿ -/
def finl1WeightedNorm (ν : ℝ≥0) (x : Fin (N + 1) → ℝ) : ℝ :=
  ∑ n : Fin (N + 1), |x n| * (ν : ℝ) ^ (n : ℕ)

/-- Column norm for matrix: (1/νʲ) Σᵢ |Aᵢⱼ| νⁱ. See equation (7.9). -/
def matrixColNorm (ν : PosReal) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (j : Fin (N + 1)) : ℝ :=
  (1 / (ν : ℝ) ^ (j : ℕ)) * ∑ i : Fin (N + 1), |A i j| * (ν : ℝ) ^ (i : ℕ)

/-- Induced matrix norm: ‖A‖_{ν,N} = max_j (1/νʲ) Σᵢ |Aᵢⱼ| νⁱ. See Exercise 2.7.2. -/
def finWeightedMatrixNorm (ν : PosReal) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun j => matrixColNorm ν A j)

/-- Key weight factorization: νᵏ · νˡ = νⁿ when k + l = n.
    This is the crucial property used in Theorem 7.4.4:
    "Since ν^n = ν^{n-k} · ν^k we have the following corollary" (Corollary 7.4.5) -/
lemma antidiagonal_weight (n : ℕ) (k l : ℕ) (h : k + l = n) :
    (ν : ℝ) ^ k * (ν : ℝ) ^ l = (ν : ℝ) ^ n := by
  rw [← pow_add, h]

/-! ### Finite Weighted Matrix Norm Properties

The weighted matrix norm ‖A‖_{1,ν} = max_j colNorm_j satisfies important properties
needed for Theorem 7.7.1 and the operator norm identification (Exercise 2.7.2).
-/

/-- Column norm is nonnegative. See equation (7.9). -/
lemma matrixColNorm_nonneg (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (j : Fin (N + 1)) :
    0 ≤ matrixColNorm ν A j := by
  unfold matrixColNorm
  apply mul_nonneg
  · apply div_nonneg zero_le_one (pow_nonneg (PosReal.coe_nonneg ν) _)
  · apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (abs_nonneg _) (pow_nonneg (PosReal.coe_nonneg ν) _)

/-- Matrix norm is nonnegative -/
lemma finWeightedMatrixNorm_nonneg (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    0 ≤ finWeightedMatrixNorm ν A := by
  apply Finset.le_sup'_of_le _ (Finset.mem_univ 0)
  exact matrixColNorm_nonneg A 0

/-- Column norm of identity matrix at diagonal entry -/
lemma matrixColNorm_one (j : Fin (N + 1)) :
    matrixColNorm ν (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) j = 1 := by
  unfold matrixColNorm
  simp only [Matrix.one_apply]
  rw [Finset.sum_eq_single j]
  · simp only [↓reduceIte, abs_one, one_mul, one_div]
    have : (ν : ℝ) ^ (j : ℕ) ≠ 0 := pow_ne_zero _ (PosReal.coe_ne_zero ν)
    field_simp [this]
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Matrix norm of identity is 1 -/
lemma finWeightedMatrixNorm_one :
    finWeightedMatrixNorm ν (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) = 1 := by
  unfold finWeightedMatrixNorm
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    rw [matrixColNorm_one]
  · apply Finset.le_sup'_of_le _ (Finset.mem_univ 0)
    rw [matrixColNorm_one]

/-- Column norm formula rewritten -/
lemma matrixColNorm_eq (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (j : Fin (N + 1)) :
    matrixColNorm ν A j = (∑ i : Fin (N + 1), |A i j| * (ν : ℝ) ^ (i : ℕ)) / (ν : ℝ) ^ (j : ℕ) := by
  unfold matrixColNorm
  ring

/-- The single element in ℓ¹_ν at position n with value x.
    This is the standard basis vector eₙ scaled by x. See Theorem 7.3.8. -/
def single (n : ℕ) (x : ℝ) : l1Weighted ν :=
  lpWeighted.mk (fun k => if k = n then x else 0) (by
    rw [mem_iff]
    have h : (fun k => |if k = n then x else 0| * (ν : ℝ) ^ k) =
             fun k => if k = n then |x| * (ν : ℝ) ^ n else 0 := by
      ext k
      split_ifs with hk
      · simp [hk]
      · simp
    rw [h]
    exact summable_of_ne_finset_zero (s := {n}) (fun k hk => by simp at hk; simp [hk]))

@[simp]
lemma single_toSeq_self (n : ℕ) (x : ℝ) : toSeq (single n x : l1Weighted ν) n = x := by
  simp only [lpWeighted.toSeq_apply, single, lpWeighted.mk]
  rfl

@[simp]
lemma single_toSeq_ne (n k : ℕ) (x : ℝ) (h : k ≠ n) : toSeq (single n x : l1Weighted ν) k = 0 := by
  simp only [lpWeighted.toSeq_apply, single, lpWeighted.mk, h]
  rfl

/-- Norm of single element: ‖δₙ(x)‖ = |x| · νⁿ. See Theorem 7.3.8: ‖eₖ‖ = ωₖ. -/
lemma norm_single (n : ℕ) (x : ℝ) : ‖(single n x : l1Weighted ν)‖ = |x| * (ν : ℝ) ^ n := by
  rw [norm_eq_tsum]
  have h : (fun k => |toSeq (single n x : l1Weighted ν) k| * (ν : ℝ) ^ k) =
           fun k => if k = n then |x| * (ν : ℝ) ^ n else 0 := by
    ext k
    split_ifs with hk
    · simp [hk, single, lpWeighted.mk]
    · simp [hk, single, lpWeighted.mk]
  rw [h, tsum_ite_eq]

end l1Weighted



/-! ### Banach Algebra Structure

The Cauchy product makes ℓ¹_ν a commutative Banach algebra.

## What is a Banach Algebra? (Definition 7.4.1)

A **Banach algebra** is a Banach space X equipped with a multiplication `·: X × X → X`
satisfying the following axioms:

1. **Associativity** (eq. 7.11):
   `x · (y · z) = (x · y) · z`

2. **Distributivity** (eq. 7.12):
   `(x + y) · z = x · z + y · z`  and  `x · (y + z) = x · y + x · z`

3. **Scalar compatibility** (eq. 7.13):
   `α(x · y) = (αx) · y = x · (αy)`

4. **Submultiplicativity** (eq. 7.14):
   `‖x · y‖ ≤ ‖x‖ · ‖y‖`

The algebra is **commutative** if `x · y = y · x` for all x, y ∈ X.

## Why ℓ¹_ν is a Banach Algebra (Theorem 7.4.4 & Corollary 7.4.5)

For ℓ¹_ν with the Cauchy product `⋆`:
- Axioms (1)-(3) follow from properties of finite sums
- Axiom (4), **submultiplicativity**, is the key analytic condition

The proof of submultiplicativity uses:
- **Mertens' Theorem** (Theorem 7.4.3): Product of summable series is summable
- **Weight factorization**: For geometric weights ωₙ = νⁿ, we have ωₙ = ωₙ₋ₖ · ωₖ

This weight factorization is what makes geometric weights special - it gives equality
in the submultiplicative estimate, not just an inequality.

## References

- Definition 7.4.1: Banach algebra axioms
- Theorem 7.4.3 (Mertens): Product of convergent series
- Theorem 7.4.4: Weighted ℓ¹ is a Banach algebra under Cauchy product
- Corollary 7.4.5: ℓ¹_ν specifically is a commutative Banach algebra
-/
namespace CauchyProductBanachAlgebra

/-- Cauchy product preserves membership in ℓ¹_ν.

    This is a prerequisite for showing ℓ¹_ν is closed under `⋆`.

    **Proof sketch** (following Theorem 7.4.4):
    Given a, b ∈ ℓ¹_ν, we need ‖a ⋆ b‖₁,ν < ∞. The key steps are:

    1. By Mertens' Theorem (Theorem 7.4.3), if Σ|aₙ|νⁿ and Σ|bₙ|νⁿ converge
       (with at least one absolutely), then the Cauchy product of the weighted
       sequences is summable.

    2. The triangle inequality gives:
       |(a ⋆ b)ₙ| · νⁿ ≤ Σₖ |aₙ₋ₖ| · |bₖ| · νⁿ

    3. Using νⁿ = νⁿ⁻ᵏ · νᵏ (the weight factorization from `antidiagonal_weight`):
       Σₖ |aₙ₋ₖ| · |bₖ| · νⁿ = Σₖ (|aₙ₋ₖ| · νⁿ⁻ᵏ) · (|bₖ| · νᵏ)

    4. Summing over n gives the product of the two norms. -/
lemma mem {ν a b} (ha : lpWeighted.Mem ν 1 a) (hb : lpWeighted.Mem ν 1 b) :
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
          -- Here we use the key weight factorization: νⁿ = νⁿ⁻ᵏ · νᵏ
          simp only [f, g, ← l1Weighted.antidiagonal_weight n kl.1 kl.2 (Finset.mem_antidiagonal.mp hkl)]; ring
  · exact hsum

/-- Multiplication via Cauchy product.

    This defines the Banach algebra multiplication on ℓ¹_ν.
    See Corollary 7.4.5: ℓ¹_ν is a commutative Banach algebra. -/
@[simp]
def mul {ν} (a b : l1Weighted ν) : l1Weighted ν :=
  lpWeighted.mk (lpWeighted.toSeq a ⋆ lpWeighted.toSeq b) (mem a.2 b.2)

/-- **Submultiplicativity** (Equation 7.17 from Theorem 7.4.4):
    `‖a ⋆ b‖₁,ν ≤ ‖a‖₁,ν · ‖b‖₁,ν`

    This is **axiom (4)** of Definition 7.4.1, the key analytic property that
    makes ℓ¹_ν a Banach algebra.

    **Proof outline** (following Equations 7.18-7.19):

    The right-hand side expands via Mertens' Theorem (Theorem 7.4.3, eq. 7.18):
      ‖a‖ · ‖b‖ = (Σₙ |aₙ|ωₙ)(Σₘ |bₘ|ωₘ) = Σₙ Σₖ (|aₙ₋ₖ|ωₙ₋ₖ)(|bₖ|ωₖ)

    In Mathlib, Mertens' theorem is realized as `tsum_mul_tsum_eq_tsum_sum_antidiagonal`:
      (∑' n, f n) * (∑' n, g n) = ∑' n, ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2

    The left-hand side is bounded (eq. 7.19):
      ‖a ⋆ b‖ = Σₙ |(a⋆b)ₙ|ωₙ
              ≤ Σₙ (Σₖ |aₙ₋ₖ||bₖ|) · ωₙ           [triangle ineq]
              = Σₙ Σₖ |aₙ₋ₖ| · (ωₙ/ωₖ) · |bₖ|ωₖ   [rearrange]

    For geometric weights ωₙ = νⁿ, we have ωₙ/ωₖ = ωₙ₋ₖ, giving equality
    in the final step (not just ≤). This is the special property of geometric
    weights mentioned after Corollary 7.4.5. -/
lemma norm_mul_le {ν} (a b : l1Weighted ν) : ‖mul a b‖ ≤ ‖a‖ * ‖b‖ := by
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
  -- Apply Mertens' theorem: (Σfₙ)(Σgₘ) = Σₙ Σₖ fₙ₋ₖ gₖ
  rw [hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hprod]
  refine Summable.tsum_le_tsum ?_ ((l1Weighted.mem_iff _).mp (mem a.2 b.2)) (summable_sum_mul_antidiagonal_of_summable_mul hprod)
  intro n
  simp only [lpWeighted.mk_apply]
  calc |CauchyProduct (lpWeighted.toSeq a) (lpWeighted.toSeq b) n| * (ν : ℝ) ^ n
      -- Step 1: Triangle inequality on the Cauchy product sum
      ≤ (∑ kl ∈ Finset.antidiagonal n, |lpWeighted.toSeq a kl.1| * |lpWeighted.toSeq b kl.2|) * (ν : ℝ) ^ n := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (PosReal.coe_nonneg ν) n)
        calc |CauchyProduct (lpWeighted.toSeq a) (lpWeighted.toSeq b) n|
            = |∑ kl ∈ Finset.antidiagonal n, lpWeighted.toSeq a kl.1 * lpWeighted.toSeq b kl.2| := rfl
          _ ≤ ∑ kl ∈ Finset.antidiagonal n, |lpWeighted.toSeq a kl.1 * lpWeighted.toSeq b kl.2| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ kl ∈ Finset.antidiagonal n, |lpWeighted.toSeq a kl.1| * |lpWeighted.toSeq b kl.2| := by simp_rw [abs_mul]
    -- Step 2: Use weight factorization νⁿ = νⁿ⁻ᵏ · νᵏ to match RHS
    _ = ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro kl hkl
        -- Key step: apply antidiagonal_weight to factor νⁿ
        simp only [f, g, ← l1Weighted.antidiagonal_weight n kl.1 kl.2 (Finset.mem_antidiagonal.mp hkl)]; ring

/-- **Commutativity**: `a ⋆ b = b ⋆ a`

    This makes ℓ¹_ν a **commutative** Banach algebra (Corollary 7.4.5).

    The proof lifts `CauchyProduct.comm` from raw sequences to `l1Weighted`.
    This is used in Remark 7.4.8 to simplify D(a·a)h = a·h + h·a to 2(a·h). -/
lemma mul_comm {ν} (a b : l1Weighted ν) : mul a b = mul b a := by
  apply lpWeighted.ext
  intro n
  simp only [mul, lpWeighted.mk_apply]
  rw [CauchyProduct.comm]

/-! ### Identity Element

The identity element e ∈ ℓ¹_ν is the Kronecker delta sequence:
  e₀ = 1,  eₙ = 0 for n ≥ 1

This satisfies a ⋆ e = e ⋆ a = a for all a ∈ ℓ¹_ν.

See Theorem 7.4.6: "the sequence e defined by eₙ := δₙ,₀ is the identity element"

The identity is used to define powers: a⁰ := e, aᵐ := a ⋆ aᵐ⁻¹
-/

/-- The Kronecker delta sequence: e₀ = 1, eₙ = 0 for n ≥ 1 -/
def oneSeq : ℕ → ℝ := fun n => if n = 0 then 1 else 0

@[simp]
lemma oneSeq_zero : oneSeq 0 = 1 := rfl

@[simp]
lemma oneSeq_succ (n : ℕ) : oneSeq (n + 1) = 0 := rfl

/-- The identity sequence has finite weighted norm: ‖e‖₁,ν = 1 -/
lemma oneSeq_mem (ν : PosReal) : lpWeighted.Mem ν 1 oneSeq := by
  rw [l1Weighted.mem_iff]
  -- The sum is just |1| · ν⁰ = 1 (all other terms are 0)
  have h : (fun n => |oneSeq n| * (ν : ℝ) ^ n) = fun n => if n = 0 then 1 else 0 := by
    ext n
    cases n with
    | zero => simp [oneSeq]
    | succ n => simp [oneSeq]
  rw [h]
  exact summable_of_ne_finset_zero (s := {0}) (fun n hn => by simp at hn; simp [hn])

/-- The identity element of ℓ¹_ν.

    See Theorem 7.4.6: e with eₙ = δₙ,₀ is the identity. -/
def one (ν : PosReal) : l1Weighted ν := lpWeighted.mk oneSeq (oneSeq_mem ν)

@[simp]
lemma one_toSeq_zero : lpWeighted.toSeq (one ν) 0 = 1 := rfl

@[simp]
lemma one_toSeq_succ (n : ℕ) : lpWeighted.toSeq (one ν) (n + 1) = 0 := rfl

/-- Cauchy product with identity on the right: (a ⋆ e)ₙ = aₙ

    Proof: (a ⋆ e)ₙ = Σₖ aₙ₋ₖ eₖ = aₙ₋₀ e₀ = aₙ · 1 = aₙ
    since eₖ = 0 for k ≥ 1. -/
lemma CauchyProduct_oneSeq_right (a : ℕ → ℝ) (n : ℕ) :
    (a ⋆ oneSeq) n = a n := by
  simp only [CauchyProduct.apply]
  -- Only the term with kl.2 = 0 survives
  rw [Finset.sum_eq_single (n, 0)]
  · simp only [oneSeq, ↓reduceIte, mul_one]
  · intro kl hkl hne
    simp only [Finset.mem_antidiagonal] at hkl
    cases kl with | mk k l =>
    simp only [ne_eq, Prod.mk.injEq, not_and] at hne
    cases l with
    | zero => simp only [not_true_eq_false, imp_false] at hne; omega
    | succ l => simp only [oneSeq, Nat.add_eq_zero_iff,
                  one_ne_zero, and_false, ↓reduceIte, mul_zero]
  · intro h; simp [Finset.mem_antidiagonal] at h

/-- Cauchy product with identity on the left: (e ⋆ a)ₙ = aₙ -/
lemma CauchyProduct_oneSeq_left (a : ℕ → ℝ) (n : ℕ) :
    (oneSeq ⋆ a) n = a n := by
  rw [CauchyProduct.comm, CauchyProduct_oneSeq_right]

/-- **Right identity law**: `a ⋆ e = a`

    This is one half of the identity axiom for the Banach algebra. -/
lemma mul_one {ν} (a : l1Weighted ν) : mul a (one ν) = a := by
  apply lpWeighted.ext
  intro n
  simp only [mul, one, lpWeighted.mk_apply]
  apply CauchyProduct_oneSeq_right

/-- **Left identity law**: `e ⋆ a = a`

    Together with `mul_one`, this establishes e as a two-sided identity. -/
lemma one_mul {ν} (a : l1Weighted ν) : mul (one ν) a = a := by
  rw [mul_comm, mul_one]

/-- The norm of the identity element: ‖e‖₁,ν = 1 -/
lemma norm_one (ν : PosReal) : ‖one ν‖ = 1 := by
  rw [l1Weighted.norm_eq_tsum]
  have h : (fun n => |lpWeighted.toSeq (one ν) n| * (ν : ℝ) ^ n) =
           fun n => if n = 0 then 1 else 0 := by
    ext n
    cases n with
    | zero =>
      have : lpWeighted.toSeq (one ν) 0 = 1 := one_toSeq_zero
      simp only [this, pow_zero, _root_.mul_one, ↓reduceIte, abs_one]
    | succ n =>
      have : lpWeighted.toSeq (one ν) (n + 1) = 0 := one_toSeq_succ n
      simp only [this, abs_zero, zero_mul,
        Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
  rw [h, tsum_ite_eq]

end CauchyProductBanachAlgebra

end nonComp

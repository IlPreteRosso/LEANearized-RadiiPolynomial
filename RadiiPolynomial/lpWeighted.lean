import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Data.Matrix.Basic

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
- `cauchyProduct`: Convolution `(a ⋆ b)ₙ = Σⱼ₌₀ⁿ aₙ₋ⱼ bⱼ` (for ℓ¹)

## References

- Section 7.4 of the radii polynomial textbook
- Exercise 2.7.2 for finite-dimensional weighted norms
-/

open scoped BigOperators Topology NNReal ENNReal Matrix
open Finset Filter

noncomputable section

/-! ## Positive Reals -/

/-- Positive real numbers as a subtype -/
abbrev PosReal := {x : ℝ // 0 < x}

namespace PosReal

instance : Coe PosReal ℝ := ⟨Subtype.val⟩

lemma coe_pos (ν : PosReal) : (0 : ℝ) < ν := ν.2
lemma coe_nonneg (ν : PosReal) : (0 : ℝ) ≤ ν := le_of_lt ν.2
lemma coe_ne_zero (ν : PosReal) : (ν : ℝ) ≠ 0 := ne_of_gt ν.2

def toNNReal (ν : PosReal) : ℝ≥0 := ⟨ν.1, le_of_lt ν.2⟩

end PosReal


/-! ## Scaled Real Numbers

`ScaledReal ν n` is ℝ with norm `‖x‖ = |x| · νⁿ`.

The parameters `ν` and `n` are not used in the definition (which is just ℝ), but they
create distinct types with different `Norm` instances via `inferInstanceAs`.
This allows `lp (ScaledReal ν) 1` to compute the weighted norm Σₙ |aₙ| νⁿ automatically.
-/

/-- ℝ with scaled norm at index n: ‖x‖ = |x| · νⁿ -/
def ScaledReal (_ν : PosReal) (_n : ℕ) := ℝ

namespace ScaledReal

variable {ν : PosReal} {n : ℕ}

/-- Borrow algebraic instances from ℝ -/
instance : AddCommGroup (ScaledReal ν n) := inferInstanceAs (AddCommGroup ℝ)
instance : Module ℝ (ScaledReal ν n) := inferInstanceAs (Module ℝ ℝ)
instance : Ring (ScaledReal ν n) := inferInstanceAs (Ring ℝ)
instance : Lattice (ScaledReal ν n) := inferInstanceAs (Lattice ℝ)
instance : LinearOrder (ScaledReal ν n) := inferInstanceAs (LinearOrder ℝ)
instance : AddLeftMono (ScaledReal ν n) := inferInstanceAs (AddLeftMono ℝ)

/-- Cast to ℝ (identity map) -/
@[coe] def toReal (x : ScaledReal ν n) : ℝ := x

/-- The scaled norm: ‖x‖ = |x| · νⁿ -/
instance instNorm : Norm (ScaledReal ν n) where
  norm x := |toReal x| * (ν : ℝ) ^ n

lemma norm_def (x : ScaledReal ν n) : ‖x‖ = |toReal x| * (ν : ℝ) ^ n := rfl

lemma norm_nonneg' (x : ScaledReal ν n) : 0 ≤ ‖x‖ :=
  mul_nonneg (abs_nonneg (toReal x)) (pow_nonneg (PosReal.coe_nonneg ν) n)

@[simp] lemma norm_zero' : ‖(0 : ScaledReal ν n)‖ = 0 := by simp [norm_def, toReal]

@[simp] lemma norm_neg' (x : ScaledReal ν n) : ‖-x‖ = ‖x‖ := by simp [norm_def, toReal, abs_neg]

lemma norm_add_le' (x y : ScaledReal ν n) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  simp only [norm_def]
  have h : toReal (x + y) = toReal x + toReal y := rfl
  calc |toReal (x + y)| * (ν : ℝ) ^ n
      ≤ (|toReal x| + |toReal y|) * (ν : ℝ) ^ n := by
        rw [h]
        exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (pow_nonneg (PosReal.coe_nonneg ν) n)
    _ = |toReal x| * (ν : ℝ) ^ n + |toReal y| * (ν : ℝ) ^ n := by ring

lemma norm_smul' (c : ℝ) (x : ScaledReal ν n) : ‖c • x‖ = |c| * ‖x‖ := by
  simp only [norm_def]
  have h : toReal (c • x) = c * toReal x := rfl
  rw [h, abs_mul]; ring

lemma norm_eq_zero' (x : ScaledReal ν n) : ‖x‖ = 0 ↔ x = 0 := by
  simp only [norm_def, mul_eq_zero, pow_eq_zero_iff', ne_eq]
  constructor
  · intro h; cases h with
    | inl h => exact abs_eq_zero.mp h
    | inr h => exact absurd h.1 (PosReal.coe_ne_zero ν)
  · intro h; left; simp [h, toReal]

instance instNormedAddCommGroup : NormedAddCommGroup (ScaledReal ν n) where
  dist x y := ‖x - y‖
  dist_self x := by simp [norm_zero']
  dist_comm x y := by
    simp only [norm_def]
    rw [show toReal (x - y) = toReal x - toReal y from rfl,
        show toReal (y - x) = toReal y - toReal x from rfl,
        abs_sub_comm]
  dist_triangle x y z := by
    have h : x - z = (x - y) + (y - z) := by abel_nf
    calc ‖x - z‖ = ‖(x - y) + (y - z)‖ := by rw [h]
      _ ≤ ‖x - y‖ + ‖y - z‖ := norm_add_le' _ _
  edist_dist x y := by simp only [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg' _)]
  eq_of_dist_eq_zero h := by rwa [norm_eq_zero', sub_eq_zero] at h
  norm := (‖·‖)
  dist_eq _ _ := rfl

instance instNormedSpace : NormedSpace ℝ (ScaledReal ν n) where
  norm_smul_le c x := by rw [norm_smul']; rfl

/-- Additive isomorphism from ℝ to ScaledReal -/
def ofReal : ℝ ≃+ ScaledReal ν n := AddEquiv.refl ℝ

@[simp] lemma toReal_apply (x : ScaledReal ν n) : toReal x = x := rfl
@[simp] lemma ofReal_apply (x : ℝ) : (ofReal x : ScaledReal ν n) = x := rfl

end ScaledReal


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

@[simp] lemma toSeq_apply (a : lpWeighted ν p) (n : ℕ) : toSeq a n = a n := rfl

lemma ext {a b : lpWeighted ν p} (h : ∀ n, toSeq a n = toSeq b n) : a = b :=
  lp.ext (funext h)

/-- Membership predicate: sequence has finite weighted ℓᵖ norm -/
def Mem (ν : PosReal) (p : ℝ≥0∞) (a : ℕ → ℝ) : Prop :=
  Memℓp (fun n => ScaledReal.ofReal (a n) : ∀ n, ScaledReal ν n) p

/-- Construct an element from a sequence with finite weighted norm -/
def mk (a : ℕ → ℝ) (ha : Mem ν p a) : lpWeighted ν p :=
  ⟨fun n => ScaledReal.ofReal (a n), ha⟩

@[simp] lemma mk_apply (a : ℕ → ℝ) (ha : Mem ν p a) (n : ℕ) : toSeq (mk a ha) n = a n := rfl
@[simp] lemma zero_toSeq (n : ℕ) : toSeq (0 : lpWeighted ν p) n = 0 := rfl
@[simp] lemma neg_toSeq (a : lpWeighted ν p) (n : ℕ) : toSeq (-a) n = -toSeq a n := rfl
@[simp] lemma add_toSeq (a b : lpWeighted ν p) (n : ℕ) : toSeq (a + b) n = toSeq a n + toSeq b n := rfl
@[simp] lemma sub_toSeq (a b : lpWeighted ν p) (n : ℕ) : toSeq (a - b) n = toSeq a n - toSeq b n := rfl
@[simp] lemma smul_toSeq (c : ℝ) (a : lpWeighted ν p) (n : ℕ) : toSeq (c • a) n = c * toSeq a n := rfl

section NormCharacterization

/-- The norm for lpWeighted: ‖a‖ = (Σₙ |aₙ|^p · ν^{pn})^{1/p} -/
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

end l1Weighted


/-! ## Finite-Dimensional Weighted Norms

See Exercise 2.7.2 for finite-dimensional weighted norms.
-/

variable {N : ℕ}

/-- Finite weighted ℓ¹ norm: ‖x‖₁,ν = Σₙ |xₙ| νⁿ -/
def finl1WeightedNorm (ν : ℝ≥0) (x : Fin (N + 1) → ℝ) : ℝ :=
  ∑ n : Fin (N + 1), |x n| * (ν : ℝ) ^ (n : ℕ)

/-- Column norm for matrix: (1/νʲ) Σᵢ |Aᵢⱼ| νⁱ -/
def matrixColNorm (ν : PosReal) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (j : Fin (N + 1)) : ℝ :=
  (1 / (ν : ℝ) ^ (j : ℕ)) * ∑ i : Fin (N + 1), |A i j| * (ν : ℝ) ^ (i : ℕ)

/-- Induced matrix norm: ‖A‖_{ν,N} = max_j (1/νʲ) Σᵢ |Aᵢⱼ| νⁱ -/
def finWeightedMatrixNorm (ν : PosReal) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun j => matrixColNorm ν A j)


/-! ## Cauchy Product

The Cauchy product (convolution) of sequences: `(a ⋆ b)ₙ = Σ_{k+l=n} aₖ bₗ`

Using `Finset.antidiagonal`, the Cauchy product is submultiplicative: ‖a ⋆ b‖₁,ν ≤ ‖a‖₁,ν · ‖b‖₁,ν

## References

- Definition 7.4.2: Cauchy product definition
- Theorem 7.4.3 (Mertens' Theorem): Product of summable series
- Theorem 7.4.4: Banach algebra estimate for weighted ℓ¹ spaces
- Corollary 7.4.5: ℓ¹_ν is a commutative Banach algebra
-/

/-- Cauchy product (convolution) of sequences.
    See Definition 7.4.2: `(a ⋆ b)ₙ = Σₖ₌₀ⁿ aₙ₋ₖ bₖ` -/
def cauchyProduct (a b : ℕ → ℝ) : ℕ → ℝ :=
  fun n => ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2

notation:70 a " ⋆ " b => cauchyProduct a b

namespace cauchyProduct

variable {ν : PosReal}

lemma apply (a b : ℕ → ℝ) (n : ℕ) :
    (a ⋆ b) n = ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2 := rfl

/-- Alternative form using range, matching Definition 7.4.2 exactly -/
lemma apply_range (a b : ℕ → ℝ) (n : ℕ) :
    (a ⋆ b) n = ∑ j ∈ Finset.range (n + 1), a (n - j) * b j := by
  simp only [apply]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * b j)]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
  rw [Nat.sub_sub_self (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]

/-- Commutativity of Cauchy product.
    See proof of Theorem 7.4.4: `Σₖ aₙ₋ₖ bₖ = Σₖ bₙ₋ₖ aₖ` -/
lemma comm (a b : ℕ → ℝ) : (a ⋆ b) = (b ⋆ a) := by
  ext n; simp only [apply]
  apply Finset.sum_nbij (fun kl => (kl.2, kl.1))
  · intro kl hkl; simp only [Finset.mem_antidiagonal] at hkl ⊢; omega
  · intro kl _ kl' _ h; ext <;> simp_all
  · intro kl hkl
    refine ⟨(kl.2, kl.1), ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_antidiagonal] at hkl ⊢; omega
    · simp only [Prod.mk.eta]
  · intro kl _; ring

/-- Key weight factorization: νᵏ · νˡ = νⁿ when k + l = n.
    This is the crucial property used in Theorem 7.4.4:
    "Since ν^n = ν^{n-k} · ν^k we have the following corollary" (Corollary 7.4.5) -/
lemma antidiagonal_weight (n : ℕ) (k l : ℕ) (h : k + l = n) :
    (ν : ℝ) ^ k * (ν : ℝ) ^ l = (ν : ℝ) ^ n := by
  rw [← pow_add, h]

/-- Cauchy product preserves membership in ℓ¹_ν.
    Follows from Mertens' Theorem (Theorem 7.4.3) applied to absolutely summable sequences. -/
lemma mem (ha : lpWeighted.Mem ν 1 a) (hb : lpWeighted.Mem ν 1 b) :
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
    calc |cauchyProduct a b n| * (ν : ℝ) ^ n
        ≤ (∑ kl ∈ Finset.antidiagonal n, |a kl.1| * |b kl.2|) * (ν : ℝ) ^ n := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (PosReal.coe_nonneg ν) n)
          calc |cauchyProduct a b n|
              = |∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2| := rfl
            _ ≤ ∑ kl ∈ Finset.antidiagonal n, |a kl.1 * b kl.2| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ kl ∈ Finset.antidiagonal n, |a kl.1| * |b kl.2| := by simp_rw [abs_mul]
      _ = ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro kl hkl
          simp only [f, g, ← antidiagonal_weight n kl.1 kl.2 (Finset.mem_antidiagonal.mp hkl)]; ring
  · exact hsum

/-- Submultiplicativity: ‖a ⋆ b‖₁,ν ≤ ‖a‖₁,ν · ‖b‖₁,ν
    This is Equation (7.17) from Theorem 7.4.4.

    The proof follows Equations (7.18)-(7.19):
    - (7.18): ‖a‖ · ‖b‖ = Σₙ Σₖ (|aₙ₋ₖ| ωₙ₋ₖ)(|bₖ| ωₖ) by Mertens
    - (7.19): ‖a ⋆ b‖ ≤ Σₙ Σₖ |aₙ₋ₖ| · (ωₙ/ωₖ) · |bₖ| ωₖ ≤ RHS of (7.18)

    For geometric weights ωₙ = νⁿ, we have ωₙ = ωₙ₋ₖ · ωₖ (equality, not just ≤). -/
lemma norm_mul_le (a b : l1Weighted ν) :
    ‖lpWeighted.mk (lpWeighted.toSeq a ⋆ lpWeighted.toSeq b) (mem a.2 b.2)‖ ≤ ‖a‖ * ‖b‖ := by
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
  apply tsum_le_tsum
  · intro n
    simp only [lpWeighted.mk_apply]
    calc |cauchyProduct (lpWeighted.toSeq a) (lpWeighted.toSeq b) n| * (ν : ℝ) ^ n
        ≤ (∑ kl ∈ Finset.antidiagonal n, |lpWeighted.toSeq a kl.1| * |lpWeighted.toSeq b kl.2|) * (ν : ℝ) ^ n := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (PosReal.coe_nonneg ν) n)
          calc |cauchyProduct (lpWeighted.toSeq a) (lpWeighted.toSeq b) n|
              = |∑ kl ∈ Finset.antidiagonal n, lpWeighted.toSeq a kl.1 * lpWeighted.toSeq b kl.2| := rfl
            _ ≤ ∑ kl ∈ Finset.antidiagonal n, |lpWeighted.toSeq a kl.1 * lpWeighted.toSeq b kl.2| :=
                Finset.abs_sum_le_sum_abs _ _
            _ = ∑ kl ∈ Finset.antidiagonal n, |lpWeighted.toSeq a kl.1| * |lpWeighted.toSeq b kl.2| := by simp_rw [abs_mul]
      _ = ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro kl hkl
          simp only [f, g, ← antidiagonal_weight n kl.1 kl.2 (Finset.mem_antidiagonal.mp hkl)]; ring
  · exact (l1Weighted.mem_iff _).mp (mem a.2 b.2)
  · exact summable_sum_mul_antidiagonal_of_summable_mul hprod

end cauchyProduct


/-! ## Banach Algebra Structure

The Cauchy product makes ℓ¹_ν a commutative Banach algebra.

See Definition 7.4.1 for Banach algebra axioms and Corollary 7.4.5 for ℓ¹_ν specifically.
-/

namespace l1Weighted

variable {ν : PosReal}

/-- Multiplication via Cauchy product.
    See Corollary 7.4.5: ℓ¹_ν is a commutative Banach algebra. -/
def mul (a b : l1Weighted ν) : l1Weighted ν :=
  lpWeighted.mk (lpWeighted.toSeq a ⋆ lpWeighted.toSeq b) (cauchyProduct.mem a.2 b.2)

/-- Norm submultiplicativity for Cauchy product.
    This is Equation (7.14) from Definition 7.4.1: ‖x · y‖ ≤ ‖x‖ ‖y‖ -/
lemma norm_mul_le (a b : l1Weighted ν) :
    ‖mul a b‖ ≤ ‖a‖ * ‖b‖ := cauchyProduct.norm_mul_le a b

end l1Weighted

end

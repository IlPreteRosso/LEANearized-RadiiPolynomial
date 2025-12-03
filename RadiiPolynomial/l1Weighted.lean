import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Data.Matrix.Basic

/-!
# Weighted ℓ¹_ν Sequence Spaces

This file defines the weighted ℓ¹ space with weight ν > 0:
  ℓ¹_ν = { a : ℕ → ℝ | ‖a‖₁,ν := Σₙ |aₙ| νⁿ < ∞ }

## Implementation

We realize ℓ¹_ν as `lp (ScaledReal ν) 1` where `ScaledReal ν n` is ℝ equipped with
the scaled norm `‖x‖ₙ = |x| · νⁿ`. This gives us:
- `NormedAddCommGroup` and `NormedSpace ℝ` for free
- `CompleteSpace` (Banach) from Mathlib's lp theory

The Cauchy product (convolution) structure is defined separately.

## Main definitions

- `ScaledReal ν n`: ℝ with norm `|x| · νⁿ`
- `l1Weighted ν`: The Banach space ℓ¹_ν, defined as `lp (ScaledReal ν) 1`
- `cauchyProduct`: Convolution `(a ⋆ b)ₙ = Σⱼ₌₀ⁿ aₙ₋ⱼ bⱼ`

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


/-! ## Weighted ℓ¹ Space

`l1Weighted ν` is the Banach space of sequences with finite weighted ℓ¹ norm.
Defined as `lp (ScaledReal ν) 1`, inheriting completeness from Mathlib.
-/

/-- The weighted ℓ¹_ν space, realized as lp with scaled fibers -/
abbrev l1Weighted (ν : PosReal) := lp (ScaledReal ν) 1

namespace l1Weighted

variable {ν : PosReal}

instance : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_refl 1⟩

/-- Extract the underlying ℝ sequence -/
def toSeq (a : l1Weighted ν) : ℕ → ℝ := fun n => ScaledReal.toReal (a n)

@[simp] lemma toSeq_apply (a : l1Weighted ν) (n : ℕ) : toSeq a n = a n := rfl

lemma ext {a b : l1Weighted ν} (h : ∀ n, toSeq a n = toSeq b n) : a = b :=
  lp.ext (funext h)

/-- The norm is the weighted sum: ‖a‖ = Σₙ |aₙ| νⁿ -/
lemma norm_eq_tsum (a : l1Weighted ν) : ‖a‖ = ∑' n, |toSeq a n| * (ν : ℝ) ^ n := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, ne_eq, one_ne_zero, not_false_eq_true, div_self,
    toSeq_apply]
  rfl

/-- Membership predicate: sequence has finite weighted norm -/
def Mem (ν : PosReal) (a : ℕ → ℝ) : Prop :=
  Summable fun n => |a n| * (ν : ℝ) ^ n

/-- Membership in ℓ¹_ν is equivalent to Memℓp with scaled fibers -/
lemma mem_iff_memℓp (a : ℕ → ℝ) :
    Mem ν a ↔ Memℓp (fun n => ScaledReal.ofReal (a n) : ∀ n, ScaledReal ν n) 1 := by
  simp only [Mem, Memℓp, one_ne_zero, ENNReal.one_ne_top,
             ENNReal.toReal_one, Real.rpow_one, ScaledReal.ofReal_apply]
  rfl

/-- Construct an element from a sequence with finite weighted norm -/
def mk (a : ℕ → ℝ) (ha : Mem ν a) : l1Weighted ν :=
  ⟨fun n => ScaledReal.ofReal (a n), (mem_iff_memℓp a).mp ha⟩

@[simp] lemma mk_apply (a : ℕ → ℝ) (ha : Mem ν a) (n : ℕ) : toSeq (mk a ha) n = a n := rfl
@[simp] lemma zero_toSeq (n : ℕ) : toSeq (0 : l1Weighted ν) n = 0 := rfl
@[simp] lemma neg_toSeq (a : l1Weighted ν) (n : ℕ) : toSeq (-a) n = -toSeq a n := rfl
@[simp] lemma add_toSeq (a b : l1Weighted ν) (n : ℕ) : toSeq (a + b) n = toSeq a n + toSeq b n := rfl
@[simp] lemma sub_toSeq (a b : l1Weighted ν) (n : ℕ) : toSeq (a - b) n = toSeq a n - toSeq b n := rfl
@[simp] lemma smul_toSeq (c : ℝ) (a : l1Weighted ν) (n : ℕ) : toSeq (c • a) n = c * toSeq a n := rfl

end l1Weighted

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

namespace SystemTaylorODE

/-- Positive real numbers. -/
abbrev PosReal := {x : ℝ // 0 < x}

namespace PosReal

instance : Coe PosReal ℝ := ⟨Subtype.val⟩

@[simp] lemma coe_pos (ν : PosReal) : (0 : ℝ) < ν := ν.2
@[simp] lemma coe_nonneg (ν : PosReal) : (0 : ℝ) ≤ ν := le_of_lt ν.2
@[simp] lemma coe_ne_zero (ν : PosReal) : (ν : ℝ) ≠ 0 := ne_of_gt ν.2

/-- Coercion to nonnegative reals. -/
@[coe] def toNNReal (ν : PosReal) : ℝ≥0 := ⟨ν.1, le_of_lt ν.2⟩

instance : Coe PosReal ℝ≥0 := ⟨PosReal.toNNReal⟩

@[simp, norm_cast] lemma coe_toNNReal (ν : PosReal) : ((ν : ℝ≥0) : ℝ) = (ν : ℝ) := rfl

end PosReal

/-- `ScaledReal ν n` is `ℝ` equipped with norm `|x| * ν^n`. -/
def ScaledReal (_ν : PosReal) (_n : ℕ) := ℝ

namespace ScaledReal

variable {ν : PosReal} {n : ℕ}

instance : AddCommGroup (ScaledReal ν n) := inferInstanceAs (AddCommGroup ℝ)
instance : Module ℝ (ScaledReal ν n) := inferInstanceAs (Module ℝ ℝ)
instance : Ring (ScaledReal ν n) := inferInstanceAs (Ring ℝ)
instance : Lattice (ScaledReal ν n) := inferInstanceAs (Lattice ℝ)
instance : LinearOrder (ScaledReal ν n) := inferInstanceAs (LinearOrder ℝ)
instance : AddLeftMono (ScaledReal ν n) := inferInstanceAs (AddLeftMono ℝ)

/-- Identity map to `ℝ`. -/
@[coe] def toReal (x : ScaledReal ν n) : ℝ := x

instance : CoeOut (ScaledReal ν n) ℝ := ⟨toReal⟩

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
  rw [h, abs_mul]
  ring

lemma norm_eq_zero' (x : ScaledReal ν n) : ‖x‖ = 0 ↔ x = 0 := by
  simp only [norm_def, mul_eq_zero, pow_eq_zero_iff', ne_eq]
  constructor
  · intro h
    cases h with
    | inl h => exact abs_eq_zero.mp h
    | inr h => exact absurd h.1 (PosReal.coe_ne_zero ν)
  · intro h
    left
    simp [h, toReal]

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
    rw [h]
    exact norm_add_le' _ _
  edist_dist x y := by simp only [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg' _)]
  eq_of_dist_eq_zero h := by rwa [norm_eq_zero', sub_eq_zero] at h
  norm := (‖·‖)
  dist_eq _ _ := rfl

instance instNormedSpace : NormedSpace ℝ (ScaledReal ν n) where
  norm_smul_le c x := by rw [norm_smul']; rfl

instance instFiniteDimensional : FiniteDimensional ℝ (ScaledReal ν n) :=
  inferInstanceAs (FiniteDimensional ℝ ℝ)

instance instCompleteSpace : CompleteSpace (ScaledReal ν n) := by
  simpa using (FiniteDimensional.complete (𝕜 := ℝ) (E := ScaledReal ν n))

/-- Additive equivalence from `ℝ`. -/
def ofReal : ℝ ≃+ ScaledReal ν n := AddEquiv.refl ℝ

@[simp] lemma toReal_apply (x : ScaledReal ν n) : toReal x = x := rfl
@[simp] lemma ofReal_apply (x : ℝ) : (ofReal x : ScaledReal ν n) = x := rfl

@[simp] lemma coe_zero : ((0 : ScaledReal ν n) : ℝ) = 0 := rfl
@[simp] lemma coe_one : ((1 : ScaledReal ν n) : ℝ) = 1 := rfl
@[simp] lemma coe_add (x y : ScaledReal ν n) : ((x + y : ScaledReal ν n) : ℝ) = x + y := rfl
@[simp] lemma coe_sub (x y : ScaledReal ν n) : ((x - y : ScaledReal ν n) : ℝ) = x - y := rfl
@[simp] lemma coe_neg (x : ScaledReal ν n) : ((-x : ScaledReal ν n) : ℝ) = -x := rfl
@[simp] lemma coe_mul (x y : ScaledReal ν n) : ((x * y : ScaledReal ν n) : ℝ) = x * y := rfl

end ScaledReal

end SystemTaylorODE

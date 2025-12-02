import Mathlib.Analysis.Calculus.Deriv.Mul


open scoped Topology BigOperators
open Metric Set Filter ContinuousLinearMap


/-
NormedAddCommGroup: A *normed* group is an additive group endowed with a norm for which `dist x y = ‖x - y‖` defines a *metric space structure*.

NormedSpace ℝ E: A normed space over the reals is a *vector space over the real numbers* equipped with a norm that satisfies the properties of a norm (non-negativity, definiteness, homogeneity, and triangle inequality).

CompleteSpace E: A *complete* space is a metric space in which every Cauchy sequence converges to a limit within the space.

⇒ E is a Banach space over ℝ.
-/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

abbrev I := ContinuousLinearMap.id ℝ E

section NeumannSeries
theorem isUnit_of_norm_sub_id_lt_one_LEAN_built_in {B : E →L[ℝ] E}
  (h : ‖I - B‖ < 1) :
  IsUnit B := by
  have : B = I - (I - B) := by
    simp only [sub_sub_cancel]
  rw [this]
  /-
  lemma isUnit_one_sub_of_norm_lt_one {x : R} (h : ‖x‖ < 1) : IsUnit (1 - x) :=
  ⟨Units.oneSub x h, rfl⟩
  -/
  exact isUnit_one_sub_of_norm_lt_one h


/--
Alternative version with explicit inverse construction
-/
theorem invertible_of_norm_sub_id_lt_one {B : E →L[ℝ] E}
  (h : ‖(1 : E →L[ℝ] E) - B‖ < 1) :
  ∃ (B_inv : E →L[ℝ] E),
    B * B_inv = 1 ∧ B_inv * B = 1 := by
  have hu := isUnit_of_norm_sub_id_lt_one_LEAN_built_in h
  obtain ⟨u, rfl⟩ := hu
  exact ⟨u.inv, u.val_inv, u.inv_val⟩
end NeumannSeries

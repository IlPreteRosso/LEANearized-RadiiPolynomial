import RadiiPolynomial.Example245.Algebra
import RadiiPolynomial.SystemTaylorODE.LeanCertEval

/-!
# Example 2.4.5 — Certificate

Numerical verification of f(x) = x² - 2 near x̄ = 13/10.
All bound proofs use `fast_bound` (dyadic interval arithmetic)
via `of_point_interval` / `abs_le` wrappers.

Bound lemma statements use canonical norms (`Y₀_norm`, `Z₀_norm`, `Z₁_norm`, `Z₂_norm`)
from `SystemTaylorODE.Core`.
-/

open scoped Topology BigOperators
open Metric Set Filter ContinuousLinearMap
open SystemTaylorODE

namespace Example245.Cert

/-! ## Parameter definitions -/

noncomputable abbrev ex_f     : ℝ → ℝ := fun x => x ^ 2 - 2
noncomputable abbrev ex_xBar  : ℝ := 13 / 10
noncomputable abbrev ex_A     : ℝ →L[ℝ] ℝ := smulCLM (19 / 50)
noncomputable abbrev ex_A_dag : ℝ →L[ℝ] ℝ := smulCLM (13 / 5)
noncomputable abbrev ex_Y₀    : ℝ := 1 / 8
noncomputable abbrev ex_Z₀    : ℝ := 1 / 80
noncomputable abbrev ex_Z₂    : ℝ → ℝ := fun _ => 19 / 25
noncomputable abbrev ex_r₀    : ℝ := 3 / 20

/-! ## Bridge -/

private lemma ex_A_dag_eq : ex_A_dag = fderiv ℝ ex_f ex_xBar := by
  simp [ex_A_dag, fderiv_sq_sub_const, ex_xBar]; ring_nf

/-! ## Bound proofs — all via fast_bound -/

private lemma Y₀_le : Y₀_norm ex_f ex_xBar ex_A ≤ ex_Y₀ := by
  unfold Y₀_norm
  simp only [ex_A, ex_f, ex_xBar, ex_Y₀, smulCLM_apply, Real.norm_eq_abs]
  rw [abs_le]
  exact ⟨of_point_interval (by fast_bound),
         of_point_interval (by fast_bound)⟩

private lemma Z₀_le : Z₀_norm ex_A ex_A_dag ≤ ex_Z₀ := by
  unfold Z₀_norm
  rw [smulCLM_comp, id_sub_smulCLM, norm_smulCLM]
  simp only [ex_Z₀]
  rw [abs_le]
  exact ⟨of_point_interval (by fast_bound),
         of_point_interval (by fast_bound)⟩

private lemma Z₁_le : Z₁_norm ex_f ex_xBar ex_A ex_A_dag ≤ 0 := by
  unfold Z₁_norm
  rw [fderiv_sq_sub_const, smulCLM_sub, smulCLM_comp, norm_smulCLM, ex_xBar]
  rw [abs_le]
  exact ⟨of_point_interval (by fast_bound),
         of_point_interval (by fast_bound)⟩

private lemma Z₂_le (c : ℝ) (hc : c ∈ closedBall ex_xBar ex_r₀) :
    Z₂_norm ex_f ex_xBar ex_A c ≤ ex_Z₂ ex_r₀ * ex_r₀ :=
  (Z₂_bound_sq_sub_const _ ex_xBar 2 hc).trans
    (by simp only [ex_Z₂, ex_r₀]
        exact of_point_interval (by fast_bound))

private lemma radii_neg : generalRadiiPolynomial ex_Y₀ ex_Z₀ 0 ex_Z₂ ex_r₀ < 0 := by
  unfold generalRadiiPolynomial ex_Y₀ ex_Z₀ ex_Z₂ ex_r₀
  exact of_point_interval_lt (by fast_bound)

private lemma r₀_pos : 0 < ex_r₀ := by
  unfold ex_r₀; exact of_point_interval_lt (by fast_bound)

private lemma A_inj : Function.Injective ex_A :=
  smulCLM_injective (ne_of_gt (of_point_interval_lt (by fast_bound)))

/-! ## Main Theorem -/

theorem main_theorem :
    ∃! xTilde ∈ closedBall ex_xBar ex_r₀, ex_f xTilde = 0 :=
  Example245.existsUnique ex_f ex_xBar ex_A ex_A_dag
    r₀_pos Y₀_le Z₀_le Z₁_le (fun c hc => Z₂_le c hc)
    (differentiable_sq_sub_const 2) radii_neg A_inj

theorem sqrt2 :
    ∃! xTilde ∈ closedBall (ex_xBar : ℝ) ex_r₀, xTilde ^ 2 = 2 := by
  obtain ⟨xTilde, ⟨hMem, hZero⟩, hUniq⟩ := main_theorem
  refine ⟨xTilde, ⟨hMem, ?_⟩, ?_⟩
  · simp only [ex_f] at hZero; linarith
  · intro y ⟨hyMem, hySq⟩
    exact hUniq y ⟨hyMem, by simp only [ex_f]; linarith⟩

end Example245.Cert

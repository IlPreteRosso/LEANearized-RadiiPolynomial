import LeanCert

/-!
# LeanCert Helper Lemmas (TaylorODE_Direct)

Small reusable helpers for LeanCert-based scalar and interval bounds.

Current API:
- `rat_mem_singleton`: bridge from rational singleton intervals to ℝ membership
- `of_point_interval`: convert interval-style point bounds (`Icc 0 0`) to scalar inequalities

These helpers are reused by direct certified bound files (for example,
`DirectRadiiCertificate.lean`) to keep local proof scripts focused on structure.
-/

open LeanCert.Core

namespace LeanCertHelpers

/-- A rational singleton interval contains its real cast. -/
lemma rat_mem_singleton (q : ℚ) (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    (q : ℝ) ∈ IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) prec :=
  IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton q) prec hprec

/-- Transform a pointwise interval bound into a scalar inequality. -/
lemma of_point_interval {e c : ℝ} {q : ℚ} (hqc : (q : ℝ) = c)
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 0, e ≤ q) : e ≤ c := by
  rw [← hqc]
  exact h 0 ⟨le_refl _, le_refl _⟩

end LeanCertHelpers

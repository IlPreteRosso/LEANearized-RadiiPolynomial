import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-!
# Finite Norm Inequality Helpers for `SystemTaylorODE`

Reusable finite-sum inequalities used across system-level norm proofs.
-/

open scoped BigOperators

noncomputable section

namespace SystemTaylorODE

/-- Weighted triangle inequality with a finite component index:
`∑ₙ |∑ⱼ fⱼₙ| wₙ ≤ ∑ⱼ ∑ₙ |fⱼₙ| wₙ` for nonnegative weights. -/
lemma weighted_sum_abs_sum_le
    {L N : ℕ}
    (w : Fin (N + 1) → ℝ)
    (hw : ∀ n : Fin (N + 1), 0 ≤ w n)
    (f : Fin L → Fin (N + 1) → ℝ) :
    ∑ n : Fin (N + 1), |∑ j : Fin L, f j n| * w n ≤
      ∑ j : Fin L, ∑ n : Fin (N + 1), |f j n| * w n := by
  have htriangle :
      ∑ n : Fin (N + 1), |∑ j : Fin L, f j n| * w n ≤
        ∑ n : Fin (N + 1), (∑ j : Fin L, |f j n|) * w n := by
    refine Finset.sum_le_sum ?_
    intro n _
    refine mul_le_mul_of_nonneg_right ?_ (hw n)
    exact (Finset.abs_sum_le_sum_abs _ _)
  have hswap :
      ∑ n : Fin (N + 1), (∑ j : Fin L, |f j n|) * w n =
        ∑ j : Fin L, ∑ n : Fin (N + 1), |f j n| * w n := by
    simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  exact htriangle.trans_eq hswap

/-- Pull out a uniform right factor from a weighted finite sum:
if `b j ≤ C` and `a j ≥ 0`, then `∑ a j * b j ≤ (∑ a j) * C`. -/
lemma sum_mul_le_sum_mul_const
    {L : ℕ}
    (a b : Fin L → ℝ) (C : ℝ)
    (ha : ∀ j : Fin L, 0 ≤ a j)
    (hb : ∀ j : Fin L, b j ≤ C) :
    ∑ j : Fin L, a j * b j ≤ (∑ j : Fin L, a j) * C := by
  have hpoint :
      ∀ j : Fin L, a j * b j ≤ a j * C := by
    intro j
    exact mul_le_mul_of_nonneg_left (hb j) (ha j)
  have hsum :
      ∑ j : Fin L, a j * b j ≤ ∑ j : Fin L, a j * C := by
    exact Finset.sum_le_sum (fun j _ => hpoint j)
  exact hsum.trans_eq (by rw [Finset.sum_mul])

/-- Reindex a 4-fold finite sum by swapping the first pair of indices with the second pair:
`(a,b,c,d) ↦ (c,d,a,b)`. -/
lemma sum4_swap_pairs
    {α β R : Type*}
    [Fintype α] [Fintype β]
    [AddCommMonoid R]
    (f : α → β → α → β → R) :
    (∑ a : α, ∑ b : β, ∑ c : α, ∑ d : β, f a b c d) =
      ∑ a : α, ∑ b : β, ∑ c : α, ∑ d : β, f c d a b := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let assoc : (((α × β) × α) × β) ≃ ((α × β) × (α × β)) :=
    Equiv.prodAssoc (α := α × β) (β := α) (γ := β)
  let e : (((α × β) × α) × β) ≃ (((α × β) × α) × β) :=
    (assoc.trans (Equiv.prodComm (α × β) (α × β))).trans assoc.symm
  simpa [e] using
    (Equiv.sum_comp e (fun t : (((α × β) × α) × β) =>
      f t.1.1.1 t.1.1.2 t.1.2 t.2)).symm

end SystemTaylorODE

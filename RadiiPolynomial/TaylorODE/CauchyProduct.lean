import Mathlib.Analysis.Normed.Lp.lpSpace

open scoped BigOperators NNReal ENNReal

/-! ### Cauchy Product

The Cauchy product (convolution) of sequences: `(a ⋆ b)ₙ = Σ_{k+l=n} aₖ bₗ`

Using `Finset.antidiagonal`, the Cauchy product is submultiplicative: ‖a ⋆ b‖₁,ν ≤ ‖a‖₁,ν · ‖b‖₁,ν

## References

- Definition 7.4.2: Cauchy product definition
-/

noncomputable section nonComp

/-- Cauchy product (convolution) of sequences.
    See Definition 7.4.2: `(a ⋆ b)ₙ = Σₖ₌₀ⁿ aₙ₋ₖ bₖ` -/
def CauchyProduct (a b : ℕ → ℝ) : ℕ → ℝ :=
  fun n => ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2

notation:70 a " ⋆ " b => CauchyProduct a b

namespace CauchyProduct

variable {ν : PosReal}

lemma apply (a b : ℕ → ℝ) (n : ℕ) :
    (a ⋆ b) n = ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2 := rfl

/-- Alternative form using range, matching Definition 7.4.2 exactly -/
lemma apply_range (a b : ℕ → ℝ) (n : ℕ) :
    (a ⋆ b) n = ∑ j ∈ Finset.range (n + 1), a (n - j) * b j := by
  simp only [CauchyProduct.apply]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * b j)]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
  rw [Nat.sub_sub_self (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]

/-- Commutativity of Cauchy product.
    See proof of Theorem 7.4.4: `Σₖ aₙ₋ₖ bₖ = Σₖ bₙ₋ₖ aₖ` -/
lemma comm (a b : ℕ → ℝ) : (a ⋆ b) = (b ⋆ a) := by
  ext n; simp only [CauchyProduct.apply]
  apply Finset.sum_nbij (fun kl => (kl.2, kl.1))
  · intro kl hkl; simp only [Finset.mem_antidiagonal] at hkl ⊢; omega
  · intro kl _ kl' _ h; ext <;> simp_all
  · intro kl hkl
    refine ⟨(kl.2, kl.1), ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_antidiagonal] at hkl ⊢; omega
    · simp only [Prod.mk.eta]
  · intro kl _; ring

end CauchyProduct

end nonComp

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

/-- If both sequences vanish beyond M, their Cauchy product vanishes beyond 2M -/
lemma zero_of_support {a b : ℕ → ℝ} {M : ℕ}
    (ha : ∀ n, M < n → a n = 0) (hb : ∀ n, M < n → b n = 0)
    (n : ℕ) (hn : 2 * M < n) :
    (a ⋆ b) n = 0 := by
  rw [apply]
  apply Finset.sum_eq_zero
  intro ⟨k, l⟩ hkl
  simp only [Finset.mem_antidiagonal] at hkl
  by_cases hk : M < k
  · simp [ha k hk]
  · push_neg at hk
    have hl : M < l := by omega
    simp [hb l hl]

/-- Cauchy product split when first sequence has support in [0,N] and n > N:
    (a⋆h)_n = a_0 h_n + ∑_{k=1}^N a_k h_{n-k} -/
lemma apply_of_support_le_split {a h : ℕ → ℝ} {N n : ℕ}
    (ha : ∀ k, N < k → a k = 0) (hn : N < n) :
    (a ⋆ h) n = a 0 * h n + ∑ k ∈ Finset.Icc 1 N, a k * h (n - k) := by
  rw [apply]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => a k * h l)]
  -- Restrict to range(N+1) since a_k = 0 for k > N
  have h_restrict : ∑ k ∈ Finset.range (n + 1), a k * h (n - k) =
      ∑ k ∈ Finset.range (N + 1), a k * h (n - k) := by
    symm
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    · intro k hk hk'
      simp only [Finset.mem_range] at hk hk'
      push_neg at hk'
      rw [ha k hk', zero_mul]
  rw [h_restrict]
  -- Split off k=0 term: range(N+1) = {0} ∪ Icc 1 N
  have h_range_eq : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [h_range_eq, Finset.sum_insert]
  · simp only [Nat.sub_zero]
  · simp only [Finset.mem_Icc]; omega

end CauchyProduct

end nonComp

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Algebra.Order.Antidiag.Prod

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

/-- Commutativity of Cauchy product: `a ⋆ b = b ⋆ a`.

    Uses `Finset.sum_equiv` with the swap equivalence `Equiv.prodComm`:
    - The antidiagonal is symmetric under `(i, j) ↦ (j, i)`
    - `Finset.swap_mem_antidiagonal` witnesses membership preservation
    - Summands match after applying `mul_comm` -/
lemma comm (a b : ℕ → ℝ) : (a ⋆ b) = (b ⋆ a) := by
  ext n
  -- After unfolding, need to show Σ a_i b_j = Σ b_i a_j over antidiagonal
  simp only [apply, mul_comm]
  -- Apply the equivalence (i,j) ↔ (j,i) via Equiv.prodComm
  exact Finset.sum_equiv (Equiv.prodComm ℕ ℕ)
    (fun _ => Finset.swap_mem_antidiagonal.symm) (by simp)

/-- Associativity of Cauchy product: `(a ⋆ b) ⋆ c = a ⋆ (b ⋆ c)`.

    Both sides equal the triple convolution `Σ_{i+j+k=n} aᵢ bⱼ cₖ`.

    Uses `Finset.sum_nbij'` with explicit forward/backward maps on sigma types:
    - Forward:  `((i, j), (k, l)) ↦ ((k, l + j), (l, j))` where `i + j = n`, `k + l = i`
    - Backward: `((i, j), (k, l)) ↦ ((i + k, l), (i, k))` where `i + j = n`, `k + l = j`

    The `aesop` tactic with `add_assoc` and `mul_assoc` hints automatically verifies:
    - Both maps are well-defined (indices land in correct antidiagonals)
    - Maps are mutual inverses
    - Summands are equal after reindexing -/
lemma assoc (a b c : ℕ → ℝ) : ((a ⋆ b) ⋆ c) = (a ⋆ (b ⋆ c)) := by
  ext n
  -- Expand nested Cauchy products into sigma-type sums over antidiagonals
  simp only [apply, Finset.sum_mul, Finset.mul_sum, Finset.sum_sigma']
  -- Establish bijection between the two nested sigma types
  apply Finset.sum_nbij'
    (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)   -- forward map
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;> -- backward map
  -- aesop verifies: membership, inverses, and summand equality
  aesop (add simp [add_assoc, mul_assoc])

/-!
### Alternative explicit proof of associativity

The following is a more explicit proof that constructs the bijection manually
using `Finset.sum_bij`. Preserved for reference.

```lean
lemma assoc_explicit (a b c : ℕ → ℝ) : ((a ⋆ b) ⋆ c) = (a ⋆ (b ⋆ c)) := by
  rw [funext_iff]
  unfold CauchyProduct
  -- Rewrite antidiagonal sums as range sums: Σ_{(i,j) ∈ antidiag n} f(i,j) = Σ_{i=0}^n f(i, n-i)
  simp (config := { decide := Bool.true }) [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  intro n
  -- Distribute multiplication through sums: (Σᵢ aᵢ) · c = Σᵢ (aᵢ · c)
  simp (config := { decide := Bool.true }) only [mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul]
  -- Convert nested range sums to sigma types for reindexing
  rw [Finset.range_eq_Ico, Finset.sum_sigma', Finset.sum_sigma']
  -- Bijection: (i, j) with 0 ≤ j ≤ i ≤ n  ↔  (j, i-j) with 0 ≤ j ≤ n, 0 ≤ i-j ≤ n-j
  refine Finset.sum_bij (fun x _ => ⟨x.2, x.1 - x.2⟩)
      ?h_mem ?h_inj ?h_surj ?h_comp
  -- h_mem: The map sends indices to valid indices in the target sigma set
  · intro a ha
    rcases a with ⟨fst, snd⟩
    simp [Nat.Ico_zero_eq_range, Finset.mem_sigma, Finset.mem_range] at ha ⊢
    rcases ha with ⟨left, right⟩
    refine ⟨?_, ?_⟩
    · exact lt_of_le_of_lt (Nat.lt_succ_iff.mp right) left
    · have hfst_le : fst ≤ n := Nat.lt_succ_iff.mp left
      exact lt_of_le_of_lt (Nat.sub_le_sub_right hfst_le snd) (Nat.lt_succ_self _)
  -- h_inj: The reindexing map is injective
  · intro a₁ ha₁ a₂ ha₂ h
    rcases a₁ with ⟨i1, j1⟩
    rcases a₂ with ⟨i2, j2⟩
    simp [Nat.Ico_zero_eq_range, Finset.mem_sigma, Finset.mem_range] at ha₁ ha₂
    have hfst  : j1 = j2 := by simpa using congrArg Sigma.fst h
    have hdiff : i1 - j1 = i2 - j2 := by simpa using congrArg Sigma.snd h
    have hj1 : j1 ≤ i1 := Nat.lt_succ_iff.mp ha₁.2
    have hj2 : j2 ≤ i2 := Nat.lt_succ_iff.mp ha₂.2
    have hdiff' : i1 - j1 = i2 - j1 := by simpa [hfst] using hdiff
    have hi : i1 = i2 := by
      have hsum := congrArg (fun t => t + j1) hdiff'
      simpa [Nat.sub_add_cancel hj1, Nat.sub_add_cancel (hfst ▸ hj2)] using hsum
    subst hi; subst hfst; rfl
  -- h_surj: The map is surjective; preimage of (j, k) is (j + k, j)
  · intro b hb
    rcases b with ⟨fst, snd⟩
    simp [Nat.Ico_zero_eq_range, Finset.mem_sigma, Finset.mem_range] at hb
    rcases hb with ⟨left, right⟩
    have hle : snd ≤ n - fst := Nat.lt_succ_iff.mp right
    refine ⟨⟨fst + snd, fst⟩, ?_, ?_⟩
    · simp [Nat.Ico_zero_eq_range, Finset.mem_sigma, Finset.mem_range]
      constructor
      · have hfst_le : fst ≤ n := Nat.lt_succ_iff.mp left
        have : fst + snd ≤ fst + (n - fst) := Nat.add_le_add_left hle _
        have : fst + snd ≤ n := by
          have hf : fst + (n - fst) = n := Nat.add_sub_of_le hfst_le
          simpa [hf] using this
        exact lt_of_le_of_lt this (Nat.lt_succ_self _)
      · exact Nat.lt_succ_of_le (Nat.le_add_right _ _)
    · simp only [add_tsub_cancel_left]
  -- h_comp: Summands agree after reindexing: a_j · b_{i-j} · c_{n-i} = a_j · b_{i-j} · c_{n-j-(i-j)}
  · intro a ha
    rcases a with ⟨fst, snd⟩
    simp [Nat.Ico_zero_eq_range, Finset.mem_sigma, Finset.mem_range] at ha
    have hle : snd ≤ fst := Nat.lt_succ_iff.mp ha.2
    -- Key calculation: n - snd - (fst - snd) = n - fst
    have hcalc : n - snd - (fst - snd) = n - fst := by
      calc
        n - snd - (fst - snd) = n - (snd + (fst - snd)) := Nat.sub_sub _ _ _
        _ = n - fst := by
          have : snd + (fst - snd) = fst := by
            have := Nat.sub_add_cancel hle
            simpa [Nat.add_comm] using this
          simp [this]
    simp [hcalc]
```
-/

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

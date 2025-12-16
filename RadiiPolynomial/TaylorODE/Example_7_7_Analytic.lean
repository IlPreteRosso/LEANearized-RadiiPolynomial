import RadiiPolynomial.TaylorODE.lpWeighted
import RadiiPolynomial.TaylorODE.CauchyProduct
import RadiiPolynomial.TaylorODE.Example_7_7
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# From Coefficient Space to Analytic Functions

This file bridges the gap between:
- **Coefficient space:** ã ∈ ℓ¹_ν with F(ã) = ã ⋆ ã - c = 0
- **Function space:** x̃(z) = Σ ãₙ zⁿ satisfies x̃(z)² - (λ₀ + z) = 0

## Main Results

* `l1Weighted.summable_powerSeries`: If ã ∈ ℓ¹_ν and |z| ≤ ν, then Σ ãₙ zⁿ converges absolutely
* `l1Weighted.tsum_sq_eq_tsum_cauchyProduct`: (Σ ãₙ zⁿ)² = Σ (ã ⋆ ã)ₙ zⁿ
* `powerSeries_sq_eq_param`: If F(ã) = 0, then x̃(z)² = λ₀ + z

## References

This completes the formalization of Example 7.7 from the radii polynomial textbook,
connecting the abstract Banach space fixed-point theorem to concrete analytic functions.
-/

open scoped BigOperators NNReal ENNReal

noncomputable section

namespace l1Weighted

/-! ## Absolute Convergence of Power Series -/

/-- The power series Σ aₙ zⁿ for a sequence a and complex number z -/
def powerSeries (a : ℕ → ℝ) (z : ℝ) : ℕ → ℝ := fun n => a n * z ^ n

/-- If a ∈ ℓ¹_ν and |z| ≤ ν, then the terms |aₙ zⁿ| are bounded by |aₙ| νⁿ -/
lemma norm_powerSeries_le {a : ℕ → ℝ} {z : ℝ} (hz : |z| ≤ ν) (n : ℕ) :
    |a n * z ^ n| ≤ |a n| * (ν : ℝ) ^ n := by
  rw [abs_mul, abs_pow]
  gcongr

/-- If a ∈ ℓ¹_ν and |z| ≤ ν, then Σ aₙ zⁿ converges absolutely -/
theorem summable_powerSeries (a : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    Summable (powerSeries (lpWeighted.toSeq a) z) := by
  apply Summable.of_norm_bounded (g := fun n => |lpWeighted.toSeq a n| * (ν : ℝ) ^ n)
  · exact (l1Weighted.mem_iff _).mp a.2
  · intro n
    simp only [powerSeries, Real.norm_eq_abs]
    exact norm_powerSeries_le hz n

/-- Absolute summability of the power series -/
theorem summable_abs_powerSeries (a : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    Summable (fun n => |lpWeighted.toSeq a n * z ^ n|) := by
  apply Summable.of_norm_bounded (g := fun n => |lpWeighted.toSeq a n| * (ν : ℝ) ^ n)
  · exact (l1Weighted.mem_iff _).mp a.2
  · intro n
    rw [Real.norm_eq_abs, abs_abs]
    exact norm_powerSeries_le hz n

/-! ## Cauchy Product and Pointwise Multiplication -/

/-- Key lemma: For absolutely convergent series, product = Cauchy product sum.
    (Σ aₙ zⁿ) * (Σ bₙ zⁿ) = Σₙ (Σₖ aₖ bₙ₋ₖ) zⁿ = Σₙ (a ⋆ b)ₙ zⁿ

    Proof outline:
    1. Since a, b ∈ ℓ¹_ν and |z| ≤ ν, both power series converge absolutely
    2. Apply Mertens' theorem (tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm):
       (Σ fₙ)(Σ gₙ) = Σₙ Σₖ₌₀ⁿ fₖ gₙ₋ₖ
    3. Convert range sum to antidiagonal sum via sum_antidiagonal_eq_sum_range_succ
    4. Factor out zⁿ: aₖ zᵏ · bₗ zˡ = aₖ bₗ · zᵏ⁺ˡ = aₖ bₗ · zⁿ (when k+l=n)
    5. Recognize the inner sum as the Cauchy product (a ⋆ b)ₙ -/
theorem tsum_mul_eq_tsum_cauchyProduct (a b : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    (∑' n, lpWeighted.toSeq a n * z ^ n) * (∑' n, lpWeighted.toSeq b n * z ^ n) =
    ∑' n, (lpWeighted.toSeq a ⋆ lpWeighted.toSeq b) n * z ^ n := by
  -- Step 1: Establish absolute convergence (using ‖·‖ not |·| to match Mathlib)
  have ha : Summable fun n => ‖lpWeighted.toSeq a n * z ^ n‖ := by
    simp only [Real.norm_eq_abs]
    exact summable_abs_powerSeries a hz
  have hb : Summable fun n => ‖lpWeighted.toSeq b n * z ^ n‖ := by
    simp only [Real.norm_eq_abs]
    exact summable_abs_powerSeries b hz
  -- Step 2: Apply Mertens' theorem
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm ha hb]
  congr 1
  ext n
  simp only [CauchyProduct.apply]
  -- Step 3: Convert Finset.range to Finset.antidiagonal
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => lpWeighted.toSeq a k * z ^ k * (lpWeighted.toSeq b l * z ^ l))]
  -- Step 4: Factor out z^n from each term
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ⟨k, l⟩ hkl
  simp only [Finset.mem_antidiagonal] at hkl
  -- aₖ zᵏ · bₗ zˡ = aₖ bₗ · zᵏ⁺ˡ = aₖ bₗ · zⁿ
  rw [mul_mul_mul_comm, ← pow_add]
  congr 1
  rw [hkl]

/-- Special case: (Σ aₙ zⁿ)² = Σ (a ⋆ a)ₙ zⁿ -/
theorem tsum_sq_eq_tsum_cauchyProduct (a : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    (∑' n, lpWeighted.toSeq a n * z ^ n) ^ 2 =
    ∑' n, (lpWeighted.toSeq a ⋆ lpWeighted.toSeq a) n * z ^ n := by
  rw [pow_two]
  exact tsum_mul_eq_tsum_cauchyProduct a a hz

/-! ## The Parameter Sequence c = (λ₀, 1, 0, 0, ...) -/

/-- Σ cₙ zⁿ = λ₀ + z -/
theorem tsum_paramSeq (lam0 : ℝ) (z : ℝ) :
    ∑' n, Example_7_7.paramSeq lam0 n * z ^ n = lam0 + z := by
  have h : ∀ n ≥ 2, Example_7_7.paramSeq lam0 n * z ^ n = 0 := by
    intro n hn
    simp only [Example_7_7.paramSeq]
    match n with
    | 0 => omega
    | 1 => omega
    | n + 2 => simp
  rw [tsum_eq_sum (s := {0, 1})]
  · simp [Example_7_7.paramSeq, pow_zero, pow_one]
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    exact h n (by omega)

/-! ## Main Theorem: Analytic Solution -/

/-- The analytic function defined by the power series -/
def analyticSolution (a : l1Weighted ν) (x : ℝ) : ℝ :=
  ∑' n, lpWeighted.toSeq a n * x ^ n

/-- If F(ã) = ã ⋆ ã - c = 0 coefficient-wise, then x̃(z)² = λ₀ + z pointwise -/
theorem analyticSolution_sq_eq (a : l1Weighted ν) (lam0 : ℝ) {z : ℝ} (hz : |z| ≤ ν)
    (hF : ∀ n, (lpWeighted.toSeq a ⋆ lpWeighted.toSeq a) n = Example_7_7.paramSeq lam0 n) :
    (analyticSolution a z) ^ 2 = lam0 + z := by
  unfold analyticSolution
  rw [tsum_sq_eq_tsum_cauchyProduct a hz]
  -- Now: Σ (a ⋆ a)ₙ zⁿ = Σ cₙ zⁿ = λ₀ + z
  conv_lhs =>
    congr
    ext n
    rw [hF n]
  exact tsum_paramSeq lam0 z

/-- Corollary: The analytic solution satisfies x̃(z)² - (λ₀ + z) = 0 -/
theorem analyticSolution_satisfies_eq (a : l1Weighted ν) (lam0 : ℝ) {z : ℝ} (hz : |z| ≤ ν)
    (hF : ∀ n, (lpWeighted.toSeq a ⋆ lpWeighted.toSeq a) n = Example_7_7.paramSeq lam0 n) :
    (analyticSolution a z) ^ 2 - (lam0 + z) = 0 := by
  rw [analyticSolution_sq_eq a lam0 hz hF]
  ring

end l1Weighted

/-! ## Connection to Example 7.7 -/

namespace Example_7_7

open l1Weighted

/-- The final semantic theorem for Example 7.7:
    Given the validated coefficient sequence ã from the radii polynomial method,
    the analytic function x̃(λ) = Σ ãₙ (λ - λ₀)ⁿ satisfies x̃(λ)² = λ
    for all λ in the disk |λ - λ₀| ≤ ν. -/
theorem analyticSolution_is_sqrt {ν : PosReal} (aTilde : l1Weighted ν) (lam0 : ℝ)
    (hF : ∀ n, (lpWeighted.toSeq aTilde ⋆ lpWeighted.toSeq aTilde) n = Example_7_7.paramSeq lam0 n)
    {lam : ℝ} (hlam : |lam - lam0| ≤ ν) :
    (analyticSolution aTilde (lam - lam0)) ^ 2 = lam := by
  rw [analyticSolution_sq_eq aTilde lam0 hlam hF]
  ring

/-- The function x̃ defines a branch of √λ near λ₀ -/
theorem analyticSolution_eq_sqrt {ν : PosReal} (aTilde : l1Weighted ν) (lam0 : ℝ)
    (hF : ∀ n, (lpWeighted.toSeq aTilde ⋆ lpWeighted.toSeq aTilde) n = Example_7_7.paramSeq lam0 n)
    (hlam0_pos : 0 < lam0)
    {lam : ℝ} (hlam : |lam - lam0| ≤ ν) (hlam_pos : 0 < lam)
    (ha0_pos : 0 < lpWeighted.toSeq aTilde 0) :
    analyticSolution aTilde (lam - lam0) = Real.sqrt lam := by
  have hsq := analyticSolution_is_sqrt aTilde lam0 hF hlam
  -- x̃² = λ and x̃(0) = ã₀ > 0 implies x̃ = √λ (positive branch)

  -- Step 1: Evaluate at z = 0: x̃(0) = a₀
  have h_at_zero : analyticSolution aTilde 0 = lpWeighted.toSeq aTilde 0 := by
    unfold analyticSolution
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [hn]

  -- Step 2: x̃(0)² = lam0 (from the equation at z=0)
  have hsq_at_zero : (analyticSolution aTilde 0) ^ 2 = lam0 := by
    have h0 : |(0 : ℝ) - 0| ≤ (ν : ℝ) := by
      simp only [sub_self, abs_zero, PosReal.coe_nonneg]
    have := analyticSolution_is_sqrt aTilde lam0 hF (by simp : |(lam0 : ℝ) - lam0| ≤ (ν : ℝ))
    simp only [sub_self] at this
    convert this using 2

  -- Step 3: Since a₀ > 0 and a₀² = lam0, we have a₀ = √lam0
  have ha0_eq : lpWeighted.toSeq aTilde 0 = Real.sqrt lam0 := by
    have h := Real.sqrt_sq ha0_pos.le
    -- h : √(lpWeighted.toSeq aTilde 0 ^ 2) = lpWeighted.toSeq aTilde 0
    -- Need to show lpWeighted.toSeq aTilde 0 ^ 2 = lam0
    have hsq' : lpWeighted.toSeq aTilde 0 ^ 2 = lam0 := by
      rw [← h_at_zero]
      exact hsq_at_zero
    rw [hsq'] at h
    exact h.symm

  -- Step 4: x̃ is continuous (power series with |z| ≤ ν is continuous)
  have hcont : ContinuousAt (analyticSolution aTilde) 0 := by
    unfold analyticSolution
    -- Use continuousOn_tsum on the ball {z : |z| ≤ ν}
    have hsum := (l1Weighted.mem_iff _).mp aTilde.2
    have hcontOn : ContinuousOn (fun z => ∑' n, lpWeighted.toSeq aTilde n * z ^ n)
        {z : ℝ | |z| ≤ ν} := by
      apply continuousOn_tsum (u := fun n => |lpWeighted.toSeq aTilde n| * (ν : ℝ) ^ n)
      · intro n
        exact (continuous_const.mul (continuous_pow n)).continuousOn
      · exact hsum
      · intro n z hz
        simp only [Set.mem_setOf_eq] at hz
        simp only [Real.norm_eq_abs, abs_mul, abs_pow]
        gcongr
    apply hcontOn.continuousAt
    rw [mem_nhds_iff]
    use Metric.ball 0 ν
    refine ⟨?_, Metric.isOpen_ball, Metric.mem_ball_self ν.2⟩
    intro z hz
    simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right] at hz ⊢
    exact hz.le

  -- Step 5: By continuity, x̃ stays positive (since x̃(0) > 0 and x̃² > 0 everywhere)
  -- If x̃(z) ≤ 0 for some z, then by IVT x̃ = 0 somewhere, but x̃² = lam > 0, contradiction
  have hpos : 0 < analyticSolution aTilde (lam - lam0) := by
    -- x̃² = lam > 0, so x̃ ≠ 0
    have hne : analyticSolution aTilde (lam - lam0) ≠ 0 := by
      intro heq
      rw [heq, pow_two, mul_zero] at hsq
      exact hlam_pos.ne' hsq.symm
    -- x̃(0) = a₀ > 0
    have hpos0 : 0 < analyticSolution aTilde 0 := by
      rw [h_at_zero]; exact ha0_pos
    -- By contrapositive of IVT: if x̃ continuous, x̃(0) > 0, x̃(z) ≠ 0, then x̃(z) > 0
    -- (otherwise x̃ would cross 0)
    by_contra hle
    push_neg at hle
    have hneg : analyticSolution aTilde (lam - lam0) < 0 := lt_of_le_of_ne hle hne
    -- Use IVT: continuous function going from positive to negative must cross 0
    -- We show this leads to a contradiction
    -- By IVT, there exists c between 0 and (lam - lam0) with analyticSolution aTilde c = 0
    -- But then c must satisfy 0² = lam0 + c, i.e., c = -lam0 < 0
    -- This is not in the interval [min 0 (lam-lam0), max 0 (lam-lam0)] when lam > 0
    have hcontOn : ContinuousOn (analyticSolution aTilde) (Set.uIcc 0 (lam - lam0)) := by
      -- analyticSolution is continuous on {z : |z| ≤ ν}
      have hcontBall : ContinuousOn (fun z => ∑' n, lpWeighted.toSeq aTilde n * z ^ n) {z : ℝ | |z| ≤ ν} := by
        apply continuousOn_tsum (u := fun n => |lpWeighted.toSeq aTilde n| * (ν : ℝ) ^ n)
        · intro n; exact (continuous_const.mul (continuous_pow n)).continuousOn
        · exact (l1Weighted.mem_iff _).mp aTilde.2
        · intro n z hz
          simp only [Set.mem_setOf_eq] at hz
          simp only [Real.norm_eq_abs, abs_mul, abs_pow]
          gcongr
      apply hcontBall.mono
      -- uIcc 0 (lam - lam0) ⊆ {z : |z| ≤ ν}
      intro z hz
      simp only [Set.mem_setOf_eq]
      simp only [Set.uIcc, Set.mem_Icc] at hz
      have h1 : |lam - lam0| ≤ ν := hlam
      rw [abs_le]
      constructor
      · calc -(ν : ℝ) ≤ -|lam - lam0| := by linarith
           _ ≤ min 0 (lam - lam0) := by
               simp only [le_min_iff]
               exact ⟨neg_nonpos.mpr (abs_nonneg _), neg_abs_le _⟩
           _ ≤ z := hz.1
      · calc z ≤ max 0 (lam - lam0) := hz.2
           _ ≤ max 0 |lam - lam0| := max_le_max_left 0 (le_abs_self _)
           _ = |lam - lam0| := by simp [abs_nonneg]
           _ ≤ ν := h1
    -- Apply IVT: 0 is between f(0) > 0 and f(lam - lam0) < 0
    -- intermediate_value_uIcc says: uIcc (f a) (f b) ⊆ f '' uIcc a b
    -- So 0 ∈ uIcc (f 0) (f (lam-lam0)) implies 0 ∈ f '' uIcc 0 (lam-lam0)
    have hIVT := intermediate_value_uIcc hcontOn
    -- 0 ∈ [f(lam-lam0), f(0)] since f(lam-lam0) < 0 < f(0)
    have h0_in : (0 : ℝ) ∈ Set.uIcc (analyticSolution aTilde 0) (analyticSolution aTilde (lam - lam0)) := by
      rw [Set.mem_uIcc]
      exact Or.inr ⟨hneg.le, hpos0.le⟩
    obtain ⟨c, hc_mem, hc_eq⟩ := hIVT h0_in
    -- At c, we have 0² = lam0 + c, so c = -lam0
    have hc_bound : |c| ≤ ν := by
      simp only [Set.uIcc, Set.mem_Icc] at hc_mem
      rw [abs_le]
      constructor
      · calc -(ν : ℝ) ≤ -|lam - lam0| := by linarith [hlam]
           _ ≤ min 0 (lam - lam0) := by
               simp only [le_min_iff]
               exact ⟨neg_nonpos.mpr (abs_nonneg _), neg_abs_le _⟩
           _ ≤ c := hc_mem.1
      · calc c ≤ max 0 (lam - lam0) := hc_mem.2
           _ ≤ max 0 |lam - lam0| := max_le_max_left 0 (le_abs_self _)
           _ = |lam - lam0| := by simp [abs_nonneg]
           _ ≤ ν := hlam
    -- Use analyticSolution_is_sqrt with lam := lam0 + c, so lam - lam0 = c
    have hc_bound' : |(lam0 + c) - lam0| ≤ ν := by simp [hc_bound]
    have hsq_c := analyticSolution_is_sqrt aTilde lam0 hF hc_bound'
    simp only [add_sub_cancel_left] at hsq_c
    rw [hc_eq, pow_two, mul_zero] at hsq_c
    -- So 0 = lam0 + c, i.e., c = -lam0
    have hc_val : c = -lam0 := by linarith
    -- But c ∈ uIcc 0 (lam - lam0), so min 0 (lam-lam0) ≤ c ≤ max 0 (lam-lam0)
    -- Since c = -lam0 < 0 and lam > 0, we have lam - lam0 > -lam0, so c < min 0 (lam-lam0) if lam-lam0 ≥ 0
    -- or c is not in range otherwise
    simp only [Set.uIcc, Set.mem_Icc] at hc_mem
    have hneg_lam0 : -lam0 < 0 := neg_neg_of_pos hlam0_pos
    rw [hc_val] at hc_mem
    -- Case split on lam - lam0 ≥ 0 or < 0
    by_cases h : lam - lam0 ≥ 0
    · -- If lam - lam0 ≥ 0, then min 0 (lam - lam0) = 0
      simp only [min_eq_left h.le, max_eq_right h.le] at hc_mem
      -- hc_mem.1 : 0 ≤ -lam0, but -lam0 < 0
      linarith [hc_mem.1]
    · -- If lam - lam0 < 0, then min 0 (lam - lam0) = lam - lam0
      push_neg at h
      simp only [min_eq_right h.le, max_eq_left h.le] at hc_mem
      -- hc_mem.1 : lam - lam0 ≤ -lam0, i.e., lam ≤ 0, but lam > 0
      linarith [hc_mem.1]

  -- sqrt(x²) = x when x ≥ 0, so sqrt((analyticSolution ...)²) = analyticSolution ...
  -- Since (analyticSolution ...)² = lam, we get sqrt(lam) = analyticSolution ...
  have h := Real.sqrt_sq hpos.le
  rw [hsq] at h
  exact h.symm

end Example_7_7

end

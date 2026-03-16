import RadiiPolynomial.TaylorODE.lpWeighted
import RadiiPolynomial.TaylorODE.CauchyProduct
import RadiiPolynomial.TaylorODE.Example_7_7
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.RingTheory.PowerSeries.Basic


/-!
# From Coefficient Space to Analytic Functions

This file bridges the gap between:
- **Coefficient space:** ã ∈ ℓ¹_ν with F(ã) = ã ⋆ ã - c = 0
- **Function space:** x̃(z) = Σ ãₙ zⁿ satisfies x̃(z)² - (λ₀ + z) = 0

## Main Results

* `l1Weighted.toPowerSeries`: Embedding of ℓ¹_ν into formal power series ℝ⟦X⟧
* `l1Weighted.eval`: Evaluation of power series at points in the disk of convergence
* `l1Weighted.eval_mul`: Evaluation commutes with multiplication (Mertens' theorem)
* `l1Weighted.eval_sq_eq`: If F(ã) = 0, then eval(ã, z)² = λ₀ + z
* `Example_7_7.analyticSolution_eq_sqrt`: Branch selection via IVT shows x̃(λ - λ₀) = √λ

## Architecture

We separate the formal and analytic levels:
1. **Formal level:** `l1Weighted.toPowerSeries` embeds sequences into `PowerSeries ℝ`
   - Multiplication in `PowerSeries` is the Cauchy product by definition
   - No convergence issues at this level
2. **Analytic level:** `l1Weighted.eval` evaluates the series at |z| ≤ ν
   - Uses absolute convergence from ℓ¹_ν membership
   - Mertens' theorem shows evaluation commutes with multiplication

## References

This completes the formalization of Example 7.7 from the radii polynomial textbook.
-/

open scoped BigOperators NNReal ENNReal

open PowerSeries (coeff)

noncomputable section

variable {ν : PosReal}

namespace l1Weighted

/-! ## Formal Power Series Embedding -/

/-- Embed an ℓ¹_ν sequence as a formal power series in ℝ⟦X⟧ -/
def toPowerSeries (a : l1Weighted ν) : PowerSeries ℝ :=
  PowerSeries.mk (lpWeighted.toSeq a)

/-- Coefficient extraction agrees with the underlying sequence -/
@[simp]
theorem coeff_toPowerSeries (a : l1Weighted ν) (n : ℕ) :
    coeff n (toPowerSeries a) = lpWeighted.toSeq a n :=
  PowerSeries.coeff_mk n _

/-- The formal power series for the parameter sequence c = (λ₀, 1, 0, 0, ...) -/
def paramPowerSeries (lam0 : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (Example_7_7.paramSeq lam0)

@[simp]
theorem coeff_paramPowerSeries (lam0 : ℝ) (n : ℕ) :
    coeff n (paramPowerSeries lam0) = Example_7_7.paramSeq lam0 n :=
  PowerSeries.coeff_mk n _

/-- The parameter series equals C(λ₀) + X in the ring of power series -/
theorem paramPowerSeries_eq (lam0 : ℝ) :
    paramPowerSeries lam0 = PowerSeries.C lam0 + PowerSeries.X := by
  ext n
  simp only [coeff_paramPowerSeries, map_add, PowerSeries.coeff_C, PowerSeries.coeff_X]
  match n with
  | 0 => simp [Example_7_7.paramSeq]
  | 1 => simp [Example_7_7.paramSeq]
  | n + 2 => simp [Example_7_7.paramSeq]

/-! ## Cauchy Product is PowerSeries Multiplication

The key insight: multiplication in `PowerSeries ℝ` is defined as the Cauchy product.
This is purely algebraic—no convergence needed at the formal level. -/

/-- PowerSeries multiplication agrees with Cauchy product coefficient-wise -/
theorem coeff_mul_eq_cauchyProduct (a b : l1Weighted ν) (n : ℕ) :
    coeff n (toPowerSeries a * toPowerSeries b) =
    (lpWeighted.toSeq a ⋆ lpWeighted.toSeq b) n := by
  rw [PowerSeries.coeff_mul]
  simp only [coeff_toPowerSeries, CauchyProduct.apply]

/-- Squaring in PowerSeries equals self-convolution -/
theorem coeff_sq_eq_cauchyProduct (a : l1Weighted ν) (n : ℕ) :
    coeff n (toPowerSeries a ^ 2) =
    (lpWeighted.toSeq a ⋆ lpWeighted.toSeq a) n := by
  rw [pow_two, coeff_mul_eq_cauchyProduct]

/-- The fixed-point equation F(a) = 0 means a² = c in PowerSeries -/
theorem toPowerSeries_sq_eq_param (a : l1Weighted ν) (lam0 : ℝ)
    (hF : ∀ n, (lpWeighted.toSeq a ⋆ lpWeighted.toSeq a) n = Example_7_7.paramSeq lam0 n) :
    toPowerSeries a ^ 2 = paramPowerSeries lam0 := by
  ext n
  rw [coeff_sq_eq_cauchyProduct, coeff_paramPowerSeries, hF]

/-! ## Analytic Evaluation -/

/-- If a ∈ ℓ¹_ν and |z| ≤ ν, then the terms |aₙ zⁿ| are bounded by |aₙ| νⁿ -/
lemma norm_term_le {a : ℕ → ℝ} {z : ℝ} (hz : |z| ≤ ν) (n : ℕ) :
    |a n * z ^ n| ≤ |a n| * (ν : ℝ) ^ n := by
  rw [abs_mul, abs_pow]
  gcongr

/-- If a ∈ ℓ¹_ν and |z| ≤ ν, then Σ aₙ zⁿ converges absolutely -/
theorem summable_eval (a : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    Summable fun n => lpWeighted.toSeq a n * z ^ n := by
  apply Summable.of_norm_bounded (g := fun n => |lpWeighted.toSeq a n| * (ν : ℝ) ^ n)
  · exact (l1Weighted.mem_iff _).mp a.2
  · intro n
    simp only [Real.norm_eq_abs]
    exact norm_term_le hz n

/-- Absolute summability -/
theorem summable_abs_eval (a : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    Summable fun n => |lpWeighted.toSeq a n * z ^ n| := by
  apply Summable.of_norm_bounded (g := fun n => |lpWeighted.toSeq a n| * (ν : ℝ) ^ n)
  · exact (l1Weighted.mem_iff _).mp a.2
  · intro n
    rw [Real.norm_eq_abs, abs_abs]
    exact norm_term_le hz n

/-- Evaluate a power series at z ∈ ℝ with |z| ≤ ν -/
def eval (a : l1Weighted ν) (z : ℝ) : ℝ :=
  ∑' n, lpWeighted.toSeq a n * z ^ n

/-- eval agrees with summing coefficients times powers -/
theorem eval_eq_tsum (a : l1Weighted ν) (z : ℝ) :
    eval a z = ∑' n, coeff n (toPowerSeries a) * z ^ n := by
  simp only [eval, coeff_toPowerSeries]

/-! ## Mertens' Theorem: Evaluation Commutes with Multiplication -/

/-- Key lemma: (Σ aₙ zⁿ) * (Σ bₙ zⁿ) = Σ (a ⋆ b)ₙ zⁿ -/
theorem eval_mul (a b : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    eval a z * eval b z = ∑' n, (lpWeighted.toSeq a ⋆ lpWeighted.toSeq b) n * z ^ n := by
  unfold eval
  -- Summability conditions for Mertens' theorem
  have ha_norm : Summable fun n => ‖lpWeighted.toSeq a n * z ^ n‖ := by
    simp only [Real.norm_eq_abs]; exact summable_abs_eval a hz
  have hb_norm : Summable fun n => ‖lpWeighted.toSeq b n * z ^ n‖ := by
    simp only [Real.norm_eq_abs]; exact summable_abs_eval b hz
  have ha : Summable fun n => lpWeighted.toSeq a n * z ^ n := ha_norm.of_norm
  have hb : Summable fun n => lpWeighted.toSeq b n * z ^ n := hb_norm.of_norm
  -- Apply Mertens' theorem (antidiagonal form)
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm' ha_norm ha hb_norm hb]
  congr 1
  ext n
  simp only [CauchyProduct.apply]
  -- Factor out z^n: aₖ zᵏ · bₗ zˡ = aₖ bₗ · zⁿ (when k+l=n)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ⟨k, l⟩ hkl
  simp only [Finset.mem_antidiagonal] at hkl
  rw [mul_mul_mul_comm, ← pow_add, hkl]

/-- Squaring: (Σ aₙ zⁿ)² = Σ (a ⋆ a)ₙ zⁿ -/
theorem eval_sq (a : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν) :
    eval a z ^ 2 = ∑' n, (lpWeighted.toSeq a ⋆ lpWeighted.toSeq a) n * z ^ n := by
  rw [pow_two, eval_mul a a hz]

/-! ## Evaluation of the Parameter Series -/

/-- Σ cₙ zⁿ = λ₀ + z -/
theorem eval_paramSeq (lam0 z : ℝ) :
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

/-! ## Main Semantic Theorems -/

/-- If F(a) = 0, then eval(a, z)² = λ₀ + z -/
theorem eval_sq_eq (a : l1Weighted ν) (lam0 : ℝ) {z : ℝ} (hz : |z| ≤ ν)
    (hF : ∀ n, (lpWeighted.toSeq a ⋆ lpWeighted.toSeq a) n = Example_7_7.paramSeq lam0 n) :
    eval a z ^ 2 = lam0 + z := by
  rw [eval_sq a hz]
  conv_lhs => congr; ext n; rw [hF n]
  exact eval_paramSeq lam0 z

/-- eval(a, 0) = a₀ -/
theorem eval_zero (a : l1Weighted ν) : eval a 0 = lpWeighted.toSeq a 0 := by
  unfold eval
  rw [tsum_eq_single 0]
  · simp
  · intro n hn; simp [hn]

end l1Weighted

/-! ## Connection to Example 7.7 -/

namespace Example_7_7

open l1Weighted

/-- Alias for backward compatibility -/
abbrev analyticSolution (a : l1Weighted ν) (z : ℝ) : ℝ := l1Weighted.eval a z

/-- The analytic function x̃(λ) = Σ ãₙ (λ - λ₀)ⁿ satisfies x̃(λ)² = λ -/
theorem analyticSolution_is_sqrt {ν : PosReal} (aTilde : l1Weighted ν) (lam0 : ℝ)
    (hF : ∀ n, (lpWeighted.toSeq aTilde ⋆ lpWeighted.toSeq aTilde) n = Example_7_7.paramSeq lam0 n)
    {lam : ℝ} (hlam : |lam - lam0| ≤ ν) :
    (analyticSolution aTilde (lam - lam0)) ^ 2 = lam := by
  rw [analyticSolution, eval_sq_eq aTilde lam0 hlam hF]
  ring

/-- The function x̃ defines a branch of √λ near λ₀ -/
theorem analyticSolution_eq_sqrt {ν : PosReal} (aTilde : l1Weighted ν) (lam0 : ℝ)
    (hF : ∀ n, (lpWeighted.toSeq aTilde ⋆ lpWeighted.toSeq aTilde) n = Example_7_7.paramSeq lam0 n)
    (hlam0_pos : 0 < lam0)
    {lam : ℝ} (hlam : |lam - lam0| ≤ ν) (hlam_pos : 0 < lam)
    (ha0_pos : 0 < lpWeighted.toSeq aTilde 0) :
    analyticSolution aTilde (lam - lam0) = Real.sqrt lam := by
  have hsq := analyticSolution_is_sqrt aTilde lam0 hF hlam

  -- Step 1: Evaluate at z = 0: x̃(0) = a₀
  have h_at_zero : analyticSolution aTilde 0 = lpWeighted.toSeq aTilde 0 :=
    eval_zero aTilde

  -- Step 2: x̃(0)² = lam0 (from the equation at z=0)
  have hsq_at_zero : (analyticSolution aTilde 0) ^ 2 = lam0 := by
    have := analyticSolution_is_sqrt aTilde lam0 hF (by simp : |(lam0 : ℝ) - lam0| ≤ (ν : ℝ))
    simp only [sub_self] at this
    convert this using 2

  -- Step 3: Since a₀ > 0 and a₀² = lam0, we have a₀ = √lam0
  have ha0_eq : lpWeighted.toSeq aTilde 0 = Real.sqrt lam0 := by
    have h := Real.sqrt_sq ha0_pos.le
    have hsq' : lpWeighted.toSeq aTilde 0 ^ 2 = lam0 := by
      rw [← h_at_zero]; exact hsq_at_zero
    rw [hsq'] at h
    exact h.symm

  -- Step 4: By continuity, x̃ stays positive (IVT argument)
  have hpos : 0 < analyticSolution aTilde (lam - lam0) := by
    -- Since $x̃$ is continuous and $x̃(0) = \sqrt{lam0} > 0$, $x̃(\lambda)$ cannot be negative for $\lambda > 0$.
    have h_cont : ContinuousOn (fun z => Example_7_7.analyticSolution aTilde z) (Set.Icc (-ν) (ν)) := by
      refine' continuousOn_tsum _ _ _;
      use fun n => |lpWeighted.toSeq aTilde n| * ( ν : ℝ ) ^ n;
      · fun_prop;
      · simpa [abs_mul] using aTilde.2.summable;
      · exact fun n x hx => by simpa [abs_mul] using mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( abs_nonneg _ ) ( abs_le.mpr hx ) _ ) ( abs_nonneg _ ) ;
    contrapose! hlam_pos;
    -- By the Intermediate Value Theorem, since $x̃$ is continuous and $x̃(0) = \sqrt{lam0} > 0$, $x̃(\lambda)$ cannot be negative for $\lambda > 0$.
    have h_ivt : ∃ z ∈ Set.Icc (lam - lam0) 0, Example_7_7.analyticSolution aTilde z = 0 := by
      apply_rules [intermediate_value_Icc];
      · -- Since $lam - lam0 \leq 0$, we have $lam - lam0 \leq 0$.
        apply le_of_not_gt; intro h_neg;
        have h_ivt : ∃ z ∈ Set.Ioo 0 (lam - lam0), Example_7_7.analyticSolution aTilde z = 0 := by
          apply_rules [intermediate_value_Ioo'];
          · linarith;
          · exact h_cont.mono ( Set.Icc_subset_Icc ( by linarith [abs_le.mp hlam] ) ( by linarith [abs_le.mp hlam] ) );
          · exact ⟨ lt_of_le_of_ne hlam_pos ( by rintro h; rw [h] at hsq; nlinarith ), by linarith ⟩;
        obtain ⟨ z, ⟨ hz₁, hz₂ ⟩, hz₃ ⟩ := h_ivt;
        have h_ivt : Example_7_7.analyticSolution aTilde z ^ 2 = lam0 + z := by
          apply eval_sq_eq;
          · exact abs_le.mpr ⟨ by linarith [abs_le.mp hlam], by linarith [abs_le.mp hlam] ⟩;
          · assumption;
        nlinarith;
      · exact h_cont.mono ( Set.Icc_subset_Icc ( by linarith [abs_le.mp hlam] ) ( by linarith [abs_le.mp hlam] ) );
      · constructor <;> linarith;
    obtain ⟨ z, ⟨ hz₁, hz₂ ⟩, hz₃ ⟩ := h_ivt;
    have h_ivt : (Example_7_7.analyticSolution aTilde z) ^ 2 = lam0 + z := by
      apply_rules [l1Weighted.eval_sq_eq];
      exact abs_le.mpr ⟨ by linarith [abs_le.mp hlam], by linarith [abs_le.mp hlam] ⟩;
    nlinarith

  -- Step 5: sqrt(x²) = x when x > 0
  have h := Real.sqrt_sq hpos.le
  rw [hsq] at h
  exact h.symm

end Example_7_7

end

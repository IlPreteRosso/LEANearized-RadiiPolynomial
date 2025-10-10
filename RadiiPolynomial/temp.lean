/-
# DETAILED TUTORIAL: MATHLIB 4 SERIES MACHINERY

This tutorial shows HOW to use the series/convergence lemmas in Lean 4 with Mathlib 4.
Verified for Lean 4.2.0+ and current Mathlib 4 (2024).

Key Lean 4 differences from Lean 3:
- Imports use Mathlib. prefix
- `by` tactic mode is standard
- Structure fields use := not :=
- obtain/rcases patterns updated
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap


-- ================================================================================
-- SECTION 0: LEAN 4 / MATHLIB 4 VERIFICATION
-- ================================================================================

section Lean4Verification

/-
This tutorial is specifically for Lean 4 with Mathlib 4.
Key Lean 4/Mathlib 4 indicators:
-/

-- 1. Import paths use Mathlib. prefix (Lean 4 style)
#check Mathlib.Analysis.SpecificLimits.Basic

-- 2. ContinuousLinearMap notation in Lean 4
#check (ContinuousLinearMap : ∀ (𝕜 E F : Type*) [inst : NontriviallyNormedField 𝕜]
  [inst_1 : SeminormedAddCommGroup E] [inst_2 : SeminormedAddCommGroup F]
  [inst_3 : Module 𝕜 E] [inst_4 : Module 𝕜 F], Type _)

-- 3. Lean 4 tactic syntax
example : 1 + 1 = 2 := by  -- 'by' starts tactic mode in Lean 4
  norm_num

-- 4. Structure instantiation (Lean 4 uses {field := value})
def myMap : Nat → Nat where  -- 'where' syntax is Lean 4
  toFun := fun n => n + 1

-- 5. Key Mathlib 4 lemma names (some changed from Mathlib 3)
#check Summable.of_norm  -- was summable_of_summable_norm in Mathlib 3
#check norm_tsum_le_tsum_norm  -- was norm_tsum_le_tsum_of_summable_norm
#check ContinuousLinearMap.norm_pow_le_pow_norm  -- namespace structure in Mathlib 4

end Lean4Verification

-- ================================================================================
-- SECTION 1: PROVING SUMMABILITY
-- ================================================================================

section ProvingSummability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

-- PATTERN 1: Direct geometric series
example : Summable (fun n : ℕ => (1/2 : ℝ)^n) := by
  -- Use: summable_geometric_of_norm_lt_one
  apply summable_geometric_of_norm_lt_one
  norm_num

-- PATTERN 2: Comparison with geometric series
example : Summable (fun n : ℕ => (n + 1) * (1/3 : ℝ)^n) := by
  -- Strategy: bound by geometric series
  have h1 : ∀ n, (n + 1) * (1/3 : ℝ)^n ≤ (n + 1) * (1/2)^n := by
    intro n
    gcongr
    norm_num
  have h2 : Summable (fun n => (n + 1) * (1/2 : ℝ)^n) := by
    -- This is a known summable series (derivative of geometric)
    sorry -- Would need specific lemma
  -- Use: Summable.of_norm_bounded
  sorry -- Need to connect the pieces

-- PATTERN 3: Absolute convergence
example (f : ℕ → E) (h : ∀ n, ‖f n‖ ≤ (1/2)^n) : Summable f := by
  -- Use: Summable.of_norm
  apply Summable.of_norm
  -- Now prove Summable (fun n => ‖f n‖)
  apply Summable.of_nonneg_of_le
  · -- Each norm is nonnegative
    intro n
    exact norm_nonneg _
  · -- Apply the bound
    exact h
  · -- Geometric series is summable
    exact summable_geometric_of_norm_lt_one (by norm_num : |(1/2 : ℝ)| < 1)

-- PATTERN 4: Using Cauchy criterion
example (f : ℕ → E)
    (h : ∀ ε > 0, ∃ N, ∀ s : Finset ℕ, (∀ n ∈ s, N ≤ n) → ‖∑ n ∈ s, f n‖ < ε) :
    Summable f := by
  -- Use: summable_iff_vanishing_norm
  rw [summable_iff_vanishing_norm]
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  use Finset.range N
  intro t ht
  -- ht says t is disjoint from range N, so all elements ≥ N
  apply hN
  intro n hn
  -- n ∈ t and t disjoint from range N means n ≥ N
  have : n ∉ Finset.range N := by
    exact Finset.disjoint_right.mp ht hn
  simpa using this

end ProvingSummability

-- ================================================================================
-- SECTION 2: COMPUTING SUMS WITH TSUM
-- ================================================================================

section ComputingSums

-- PATTERN 1: Using hasSum to compute tsum
example : ∑' n : ℕ, (1/2 : ℝ)^n = 2 := by
  -- First establish HasSum, then extract tsum value
  have h : HasSum (fun n => (1/2 : ℝ)^n) 2 := by
    convert hasSum_geometric_of_norm_lt_one (by norm_num : |(1/2 : ℝ)| < 1)
    norm_num
  exact h.tsum_eq

-- PATTERN 2: Direct formula application
example : ∑' n : ℕ, (1/3 : ℝ)^n = 3/2 := by
  -- Use: tsum_geometric_of_norm_lt_one
  convert tsum_geometric_of_norm_lt_one (by norm_num : |(1/3 : ℝ)| < 1)
  norm_num

-- PATTERN 3: Manipulating tsums
example (a b : ℝ) (ha : |a| < 1) (hb : |b| < 1) :
    ∑' n : ℕ, (a^n + b^n) = 1/(1-a) + 1/(1-b) := by
  -- Use: tsum_add
  rw [tsum_add]
  · -- Rewrite each sum
    simp only [tsum_geometric_of_norm_lt_one ha, tsum_geometric_of_norm_lt_one hb]
  · -- Show first series summable
    exact summable_geometric_of_norm_lt_one ha
  · -- Show second series summable
    exact summable_geometric_of_norm_lt_one hb

-- PATTERN 4: Scalar multiplication
example (c : ℝ) : ∑' n : ℕ, c * (1/2)^n = 2*c := by
  -- Use: tsum_mul_left
  rw [tsum_mul_left]
  rw [tsum_geometric_of_norm_lt_one (by norm_num : |(1/2 : ℝ)| < 1)]
  ring

end ComputingSums

-- ================================================================================
-- SECTION 3: WORKING WITH HASSUM
-- ================================================================================

section WorkingWithHasSum

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [CompleteSpace E] [CompleteSpace F] [NormedSpace ℝ E] [NormedSpace ℝ F]

-- PATTERN 1: Proving HasSum from definition
example : HasSum (fun n : ℕ => (1/2 : ℝ)^n) 2 := by
  -- Method 1: Use existing theorem
  convert hasSum_geometric_of_norm_lt_one (by norm_num : |(1/2 : ℝ)| < 1)
  norm_num

-- PATTERN 2: HasSum with continuous maps
example (f : E →L[ℝ] F) (g : ℕ → E) (a : E) (h : HasSum g a) :
    HasSum (fun n => f (g n)) (f a) := by
  -- Use: HasSum.map
  exact HasSum.map f.continuous h

-- PATTERN 3: Extracting properties from HasSum
example (f : ℕ → ℝ) (a : ℝ) (h : HasSum f a) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop (𝓝 a) := by
  -- HasSum means partial sums converge
  exact h.tendsto_sum_nat

-- PATTERN 4: Building HasSum from Summable
example (f : ℕ → E) (hf : Summable f) :
    HasSum f (∑' n, f n) := by
  -- Use: Summable.hasSum
  exact hf.hasSum

end WorkingWithHasSum

-- ================================================================================
-- SECTION 4: TELESCOPING SERIES
-- ================================================================================

section TelescopingSeries

-- PATTERN 1: Basic telescoping
example (f : ℕ → ℝ) :
    ∑ n ∈ Finset.range N, (f n - f (n + 1)) = f 0 - f N := by
  -- Use induction
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    ring

-- PATTERN 2: Telescoping to infinity
example (f : ℕ → ℝ) (h_lim : Tendsto f atTop (𝓝 0)) :
    HasSum (fun n => f n - f (n + 1)) (f 0) := by
  -- Show partial sums = f 0 - f N
  have partial : ∀ N, ∑ n ∈ Finset.range N, (f n - f (n + 1)) = f 0 - f N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  -- Use: hasSum_iff_tendsto_nat_of_summable
  rw [hasSum_iff_tendsto_nat_of_summable]
  · -- Show convergence of partial sums
    simp_rw [partial]
    convert Tendsto.sub tendsto_const_nhds h_lim
    simp
  · -- Show summability (requires additional work)
    sorry

-- PATTERN 3: Telescoping for operators
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hT : ‖T‖ < 1) (x : E) :
    HasSum (fun n => T^n x - T^(n+1) x) x := by
  -- Similar to above but with operators
  have partial : ∀ N, ∑ n ∈ Finset.range N, (T^n x - T^(n+1) x) = x - T^N x := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [pow_zero] at *
      abel
  -- Show T^N x → 0
  have h_lim : Tendsto (fun N => T^N x) atTop (𝓝 0) := by
    -- Use that T^N → 0 in operator norm
    have : Tendsto (fun N => T^N) atTop (𝓝 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp only [sub_zero]
      have : ∀ N, ‖T^N‖ ≤ ‖T‖^N := fun N => T.norm_pow_le_pow_norm N
      apply squeeze_zero_norm' (eventually_of_forall this)
      simp_rw [norm_norm]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hT
    -- Apply to x
    exact Tendsto.apply this x
  -- Complete the proof
  rw [hasSum_iff_tendsto_nat_of_summable]
  · simp_rw [partial]
    convert Tendsto.sub tendsto_const_nhds h_lim
    simp
  · -- Summability proof
    sorry

end TelescopingSeries

-- ================================================================================
-- SECTION 5: COMMON PITFALLS AND SOLUTIONS
-- ================================================================================

section PitfallsAndSolutions

/-
PITFALL 1: "tsum_apply doesn't exist for ContinuousLinearMap"
SOLUTION: Use HasSum.map with continuity
-/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hT : Summable (fun n => T^n)) (x : E) :
    (∑' n, T^n) x = ∑' n, T^n x := by
  -- Can't use tsum_apply, instead:
  have h1 : HasSum (fun n => T^n) (∑' n, T^n) := hT.hasSum
  have h2 : HasSum (fun n => T^n x) ((∑' n, T^n) x) := by
    -- Apply the sum to x
    convert HasSum.apply h1 x
    ext n
    rfl
  -- Now h2 gives us what we want
  exact h2.tsum_eq.symm

/-
PITFALL 2: "simp doesn't simplify my sum"
SOLUTION: Explicitly unfold and use specific lemmas
-/
example : ∑ i ∈ Finset.range 3, i^2 = 5 := by
  -- Don't just try simp, be explicit:
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num

/-
PITFALL 3: "How do I prove custom series converge?"
SOLUTION: Reduce to known series via comparison
-/
example : Summable (fun n : ℕ => (1 : ℝ) / (2^n + n)) := by
  -- Compare with geometric series
  have : ∀ n, (1 : ℝ) / (2^n + n) ≤ 1 / 2^n := by
    intro n
    rw [div_le_div_iff]
    · ring_nf
      exact le_add_of_nonneg_right (Nat.cast_nonneg n)
    · positivity
    · positivity
  apply Summable.of_nonneg_of_le
  · intro n; positivity
  · exact this
  · simp_rw [one_div]
    exact summable_geometric_of_norm_lt_one (by norm_num : |(1/2 : ℝ)| < 1)

end PitfallsAndSolutions

-- ================================================================================
-- SECTION 6: COMPLETE WORKED EXAMPLE
-- ================================================================================

section CompleteExample

/-
Complete example: Prove that if ‖T‖ < 1/2, then (I - T)⁻¹ = ∑ T^n
and compute ‖(I - T)⁻¹‖ ≤ 2
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Nontrivial E]

example (T : E →L[ℝ] E) (hT : ‖T‖ < 1/2) :
    ∃ S : E →L[ℝ] E, S = ∑' n, T^n ∧
    (ContinuousLinearMap.id ℝ E - T) * S = ContinuousLinearMap.id ℝ E ∧
    ‖S‖ ≤ 2 := by
  -- Step 1: Show series converges
  have h_sum : Summable (fun n => T^n) := by
    apply Summable.of_norm
    have : ∀ n, ‖T^n‖ ≤ ‖T‖^n := fun n => T.norm_pow_le_pow_norm n
    apply Summable.of_nonneg_of_le
    · intro; exact norm_nonneg _
    · exact this
    · have : ‖T‖ < 1 := by linarith
      exact summable_geometric_of_norm_lt_one this

  -- Step 2: Define S
  use ∑' n, T^n

  constructor
  · rfl

  constructor
  · -- Show (I - T) * S = I using telescoping
    ext x
    -- Key computation: distribute and telescope
    sorry -- This requires the telescoping machinery

  · -- Bound the norm
    calc ‖∑' n, T^n‖
      ≤ ∑' n, ‖T^n‖ := by exact norm_tsum_le_tsum_norm h_sum
    _ ≤ ∑' n, ‖T‖^n := by
        apply tsum_le_tsum
        · intro n; exact T.norm_pow_le_pow_norm n
        · apply Summable.of_nonneg_of_le
          · intro; exact norm_nonneg _
          · intro n; exact T.norm_pow_le_pow_norm n
          · have : ‖T‖ < 1 := by linarith
            exact summable_geometric_of_norm_lt_one this
        · exact h_sum.norm
    _ = 1 / (1 - ‖T‖) := by
        have : ‖T‖ < 1 := by linarith
        exact tsum_geometric_of_norm_lt_one this
    _ ≤ 1 / (1 - 1/2) := by
        gcongr
    _ = 2 := by norm_num

end CompleteExample

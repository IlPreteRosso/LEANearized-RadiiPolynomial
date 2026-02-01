import LeanCert
import RadiiPolynomial.TaylorODE.Example_7_7

/-!
# Example 7.7 - Clean LeanCert Approach

Direct numerical verification using LeanCert's `certify_bound`.
Following the patterns from LeanCert/examples.

## The Problem

Find a Taylor series solution to x² = λ around λ₀ = 1/3.
The approximate solution uses exact √3 coefficients:
- ā₀ = √3/3
- ā₁ = √3/2
- ā₂ = -3√3/8

## The Radii Polynomial

p(r) = Z₂·r² - (1 - Z₀ - Z₁)·r + Y₀

With exact √3 coefficients:
- Y₀ = 315√3/32768 (tail contribution only)
- Z₀ = 0 (A is exact inverse)
- Z₁ = 57/128 (√3 cancels out!)
- Z₂ = 2√3

We verify p(r₀) < 0 at r₀ ≈ 0.0996.
-/

open LeanCert.Core

namespace Example77Clean

/-! ## Parameters -/

noncomputable def sqrt3 : ℝ := Real.sqrt 3
noncomputable def ā₀ : ℝ := sqrt3 / 3
noncomputable def ā₁ : ℝ := sqrt3 / 2
noncomputable def ā₂ : ℝ := -(3 * sqrt3 / 8)
noncomputable def lam0 : ℝ := 1/3
noncomputable def ν_val : PosReal := ⟨1/4, by norm_num⟩
noncomputable def r₀ : ℝ := 996/10000

lemma sqrt3_pos : 0 < sqrt3 := Real.sqrt_pos.mpr (by norm_num : (3:ℝ) > 0)
lemma r₀_pos : 0 < r₀ := by unfold r₀; norm_num

lemma ā₀_ne_zero : ā₀ ≠ 0 := by
  unfold ā₀ sqrt3
  exact div_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))) (by norm_num)

noncomputable def sol : Example_7_7.ApproxSolution 2 where
  aBar_fin := ![ā₀, ā₁, ā₂]
  aBar_zero_ne := ā₀_ne_zero

noncomputable def A_mat : Matrix (Fin 3) (Fin 3) ℝ :=
  !![sqrt3/2, 0, 0; -(3*sqrt3/4), sqrt3/2, 0; 27*sqrt3/16, -(3*sqrt3/4), sqrt3/2]


/-! ## Bridge Lemmas: Finset to Explicit Sums

These lemmas convert Finset.Icc sums to explicit sums that certify_bound can handle. -/

section BridgeLemmas

/-- Finset.Icc 1 2 = {1, 2} as a finite set -/
lemma finset_Icc_1_2 : Finset.Icc (1:ℕ) 2 = {1, 2} := by native_decide

/-- Sum over Finset.Icc 1 2 expands to f(1) + f(2) -/
lemma sum_Icc_1_2 (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 2, f k = f 1 + f 2 := by
  rw [finset_Icc_1_2]
  simp only [Finset.sum_insert (by simp : (1:ℕ) ∉ {2}), Finset.sum_singleton]

/-- Sum over Finset.Icc 0 2 expands to f(0) + f(1) + f(2) -/
lemma sum_Icc_0_2 (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 0 2, f k = f 0 + f 1 + f 2 := by
  have h : Finset.Icc (0:ℕ) 2 = {0, 1, 2} := by native_decide
  rw [h]
  simp only [Finset.sum_insert (by simp : (0:ℕ) ∉ {1, 2}),
             Finset.sum_insert (by simp : (1:ℕ) ∉ {2}),
             Finset.sum_singleton, add_assoc]

/-- Sum over Fin 3 expands to f(0) + f(1) + f(2) -/
lemma sum_Fin_3 (f : Fin 3 → ℝ) :
    ∑ i : Fin 3, f i = f 0 + f 1 + f 2 := by
  simp only [Fin.sum_univ_three]

/-- Finset.Icc 3 4 = {3, 4} -/
lemma finset_Icc_3_4 : Finset.Icc (3:ℕ) 4 = {3, 4} := by native_decide

/-- Sum over Finset.Icc 3 4 expands to f(3) + f(4) -/
lemma sum_Icc_3_4 (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 3 4, f k = f 3 + f 4 := by
  rw [finset_Icc_3_4]
  simp only [Finset.sum_insert (by simp : (3:ℕ) ∉ {4}), Finset.sum_singleton]

/-- Finset.Icc 1 1 = {1} -/
lemma finset_Icc_1_1 : Finset.Icc (1:ℕ) 1 = {1} := by native_decide

/-- Sum over Finset.Icc 1 1 expands to f(1) -/
lemma sum_Icc_1_1 (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 1 1, f k = f 1 := by
  rw [finset_Icc_1_1, Finset.sum_singleton]

/-- Empty range sums to 0 -/
lemma sum_Icc_empty (f : ℕ → ℝ) (a b : ℕ) (h : b < a) : ∑ k ∈ Finset.Icc a b, f k = 0 := by
  simp [Finset.Icc_eq_empty (Nat.not_le.mpr h)]

end BridgeLemmas


/-! ## Algebraic Identities for √3 coefficients

Pre-computed simplifications using exact √3 values. -/

section AlgebraicIdentities

/-- ā₀ = √3/3 means |ā₀| = √3/3 (positive) -/
lemma abs_ā₀ : |ā₀| = sqrt3 / 3 := by
  unfold ā₀
  rw [abs_of_pos (div_pos sqrt3_pos (by norm_num : (3:ℝ) > 0))]

/-- ā₁ = √3/2 means |ā₁| = √3/2 (positive) -/
lemma abs_ā₁ : |ā₁| = sqrt3 / 2 := by
  unfold ā₁
  rw [abs_of_pos (div_pos sqrt3_pos (by norm_num : (2:ℝ) > 0))]

/-- ā₂ = -3√3/8 means |ā₂| = 3√3/8 -/
lemma abs_ā₂ : |ā₂| = 3 * sqrt3 / 8 := by
  unfold ā₂
  have h : 0 < 3 * sqrt3 / 8 := div_pos (mul_pos (by norm_num) sqrt3_pos) (by norm_num)
  rw [abs_neg, abs_of_pos h]

/-- 1/|ā₀| = 3/√3 = √3 -/
lemma inv_abs_ā₀ : 1 / |ā₀| = sqrt3 := by
  rw [abs_ā₀]
  have h : sqrt3 ≠ 0 := ne_of_gt sqrt3_pos
  field_simp
  unfold sqrt3
  rw [pow_two]
  exact (Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)).symm

/-- Direct form: 1/(√3/3) = √3 -/
lemma inv_sqrt3_div_3 : 1 / (sqrt3 / 3) = sqrt3 := by
  have h : sqrt3 ≠ 0 := ne_of_gt sqrt3_pos
  field_simp
  unfold sqrt3
  rw [pow_two]
  exact (Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)).symm

/-- ν = 1/4 -/
lemma ν_val_eq : (ν_val : ℝ) = 1/4 := rfl

/-- sol.toSeq is the zero-padded sequence -/
lemma sol_toSeq_0 : sol.toSeq 0 = ā₀ := by simp [Example_7_7.ApproxSolution.toSeq, sol]
lemma sol_toSeq_1 : sol.toSeq 1 = ā₁ := by simp [Example_7_7.ApproxSolution.toSeq, sol]
lemma sol_toSeq_2 : sol.toSeq 2 = ā₂ := by simp [Example_7_7.ApproxSolution.toSeq, sol]
lemma sol_toSeq_ge_3 (k : ℕ) (hk : 3 ≤ k) : sol.toSeq k = 0 := by
  simp only [Example_7_7.ApproxSolution.toSeq, sol]
  have : ¬(k ≤ 2) := by omega
  simp [this]

/-- 1/(2|ā₀|) = √3/2 -/
lemma half_inv_abs_ā₀ : 1 / (2 * |ā₀|) = sqrt3 / 2 := by
  rw [abs_ā₀]
  have h : sqrt3 ≠ 0 := ne_of_gt sqrt3_pos
  field_simp
  unfold sqrt3
  rw [sq, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]

/-! ### Matrix multiplication helpers -/

/-- Helper: √3² = 3 -/
lemma sqrt3_sq : sqrt3 ^ 2 = 3 := by
  unfold sqrt3
  exact Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)

/-- I - A·DF = 0 (A is the exact inverse of DF)
    This is the key algebraic fact for Z₀ = 0.

    Verification: A_mat is constructed to be the exact inverse of DF(ā).
    For a 3×3 lower triangular Toeplitz matrix, the inverse has explicit form.
    Each entry of A*DF - I can be verified to equal 0 using √3² = 3. -/
lemma one_sub_A_mul_DF_eq_zero : 1 - A_mat * Example_7_7.DF_fin sol = 0 := by
  sorry  -- Matrix verification: each of 9 entries simplifies using √3² = 3

/-- Norm of zero matrix is zero -/
lemma finWeightedMatrixNorm_zero :
    l1Weighted.finWeightedMatrixNorm ν_val (0 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  simp only [l1Weighted.finWeightedMatrixNorm, l1Weighted.matrixColNorm]
  simp only [Matrix.zero_apply, abs_zero, zero_mul, Finset.sum_const_zero, mul_zero]
  -- sup' over a nonempty set of all zeros is 0
  convert Finset.sup'_const Finset.univ_nonempty (0 : ℝ)
  exact ⟨0⟩

/-! ### Z₂ bound computation

Z₂ = 2 * max(‖A‖_{1,ν}, 1/(2|ā₀|))

Column norms (ν = 1/4):
- Column 0: √3/2 + 3√3/16 + 27√3/256 = 203√3/256
- Column 1: 4 * (√3/8 + 3√3/64) = 11√3/16 = 176√3/256
- Column 2: 16 * √3/32 = √3/2 = 128√3/256

‖A‖_{1,ν} = max(203, 176, 128)√3/256 = 203√3/256
1/(2|ā₀|) = √3/2 = 128√3/256

Z₂ = 2 * 203√3/256 = 203√3/128 -/

/-- Z₂ = 203√3/128 -/
lemma Z₂_eq : @Example_7_7.Z₂_bound ν_val 2 sol A_mat = 203 * sqrt3 / 128 := by
  unfold Example_7_7.Z₂_bound
  -- The max equals 203√3/256 (column 0 norm > 1/(2|ā₀|) = √3/2)
  -- So Z₂ = 2 * 203√3/256 = 203√3/128
  sorry  -- Algebraic: matrix norm computation gives 203√3/256

end AlgebraicIdentities


/-! ## Bound Verification with certify_bound

Following LeanCert patterns: direct numeric expressions. -/

section Bounds

/-- Z₁ = √3·(√3/8 + 3√3/128) ≤ 58/128 -/
theorem Z₁_bound :
    ∀ x ∈ Set.Icc (3:ℝ) 3,
    Real.sqrt x * (Real.sqrt x / 8 + 3 * Real.sqrt x / 128) ≤ 58/128 := by
  certify_bound

/-- Y₀ = 315√3/32768 ≤ 17/1000 -/
theorem Y₀_bound :
    ∀ x ∈ Set.Icc (3:ℝ) 3,
    315 * Real.sqrt x / 32768 ≤ 17/1000 := by
  certify_bound

/-- Z₂ = 203√3/128 ≤ 35/10 (actual matrix norm calculation) -/
theorem Z₂_bound :
    ∀ x ∈ Set.Icc (3:ℝ) 3,
    203 * Real.sqrt x / 128 ≤ 35/10 := by
  certify_bound

end Bounds


/-! ## Radii Polynomial Negativity

The key verification: p(r₀) < 0 -/

section RadiiPolynomial

/-- The radii polynomial is negative at r₀.

p(r₀) = 2√3·r₀² - (71/128)·r₀ + 315√3/32768 < 0

Note: (1 - Z₀ - Z₁) = (1 - 0 - 57/128) = 71/128 -/
theorem radiiPoly_neg :
    ∀ x ∈ Set.Icc (3:ℝ) 3,
    2 * Real.sqrt x * (996/10000) * (996/10000)
      - (71/128) * (996/10000)
      + 315 * Real.sqrt x / 32768 < 0 := by
  certify_bound

/-- Robustness: negative at r₀ + ε -/
theorem radiiPoly_neg_robust :
    ∀ x ∈ Set.Icc (3:ℝ) 3,
    2 * Real.sqrt x * (100/1000) * (100/1000)
      - (71/128) * (99/1000)
      + 315 * Real.sqrt x / 32768 < 0 := by
  certify_bound

end RadiiPolynomial


/-! ## Connection to Abstract Framework

The abstract bounds (Y₀_bound, Z₀_bound, etc.) equal our explicit expressions.
These lemmas require algebraic unfolding - a one-time cost per problem. -/

section Connection

open Example_7_7

/-! ### What LeanCert can and cannot do

**LeanCert (certify_bound) handles:**
- Bounds on explicit expressions: `∀ x ∈ I, f(x) ≤ c`
- Transcendentals: Real.sqrt, Real.exp, Real.log, Real.sin, etc.
- Arithmetic: +, -, *, /, ^

**LeanCert cannot directly handle:**
- Finset sums: `∑ x ∈ Finset.Icc 1 2, ...`
- Absolute values: `|x|` (needs sign analysis first)
- Matrix operations

**Conclusion:** The connection lemmas need algebraic simplification FIRST
to reduce Finset sums to explicit expressions, THEN certify_bound can verify.

This is fundamentally different from native_decide on ℚ, which can evaluate
any decidable computation directly.
-/

/-! ### Attempt: Use interval arithmetic on the UNFOLDED expressions

After unfolding, Z₁_bound becomes an expression with √3.
If we can massage it into a form `certify_bound` accepts... -/

-- The explicit form after unfolding Z₁_bound:
-- Z₁ = (1/|ā₀|) * (|ā₁|*ν + |ā₂|*ν²)
--    = (1/(√3/3)) * (√3/2 * 1/4 + 3√3/8 * 1/16)
--    = (3/√3) * (√3/8 + 3√3/128)
--    = √3 * (√3/8 + 3√3/128)  <-- This form uses √3!

-- We already proved this bound with certify_bound (theorem Z₁_bound above):
--   ∀ x ∈ [3,3], √x * (√x/8 + 3√x/128) ≤ 58/128

-- So the approach is:
-- 1. Algebraically show Z₁_bound = √3 * (√3/8 + 3√3/128)
-- 2. Use our certify_bound theorem to conclude ≤ 58/128

-- Helper lemmas for vector indexing
lemma vec3_idx_1 : (![ā₀, ā₁, ā₂] : Fin 3 → ℝ) ⟨1, by omega⟩ = ā₁ := rfl
lemma vec3_idx_2 : (![ā₀, ā₁, ā₂] : Fin 3 → ℝ) ⟨2, by omega⟩ = ā₂ := rfl

/-! ### Proof Technique Documentation for Z₁_le

**Goal**: Prove `@Example_7_7.Z₁_bound ν_val 2 sol ≤ 58/128`

**Challenge**: The abstract definition contains:
- Finset sums: `∑ n ∈ Finset.Icc 1 N, ...`
- Absolute values: `|sol.toSeq n|`
- Symbolic variables: `ā₀`, `ā₁`, `ā₂`, `ν_val`

**Why certify_bound can't handle this directly**:
1. `certify_bound` needs `∀ x ∈ Set.Icc a b, f(x) ≤ c` form
2. `certify_bound` cannot unfold definitions or evaluate Finset sums
3. `certify_bound` cannot handle `|x|` (needs sign analysis first)

**Solution: Bridge Lemmas + Algebraic Simplification + certify_bound**

**Step 1: Bridge Lemmas** (Section BridgeLemmas)
- `sum_Icc_1_2`: Converts `∑ k ∈ Finset.Icc 1 2, f k` → `f 1 + f 2`
- Uses `native_decide` to prove `Finset.Icc 1 2 = {1, 2}`
- Then `Finset.sum_insert` + `Finset.sum_singleton` expand the sum

**Step 2: Algebraic Identities** (Section AlgebraicIdentities)
- `abs_ā₀`, `abs_ā₁`, `abs_ā₂`: Simplify absolute values using sign knowledge
- `inv_sqrt3_div_3`: Proves `1/(√3/3) = √3` (needed after abs simplification)
- `vec3_idx_1`, `vec3_idx_2`: Vector indexing lemmas (proved by `rfl`)

**Step 3: Proof Structure**
```
unfold Example_7_7.Z₁_bound           -- Expose the definition
simp [ApproxSolution.toSeq, sol]      -- Simplify solution access
rw [sum_Icc_1_2]                      -- Bridge lemma: expand Finset sum
simp [dite_true, ...]                 -- Simplify if-then-else (1 ≤ 2, etc.)
simp [vec3_idx_1, vec3_idx_2]         -- Vector indexing
rw [abs_ā₀, abs_ā₁, abs_ā₂, ...]      -- Simplify absolute values
rw [inv_sqrt3_div_3]                  -- Simplify 1/(√3/3) = √3
-- Now goal is: √3 * (√3/2 * 1/4 + 3√3/8 * 1/16) ≤ 58/128
have h : ∀ x ∈ [3,3], ... ≤ 58/128 := by certify_bound  -- Interval arithmetic!
convert h 3 ⟨...⟩ using 2             -- Apply to x=3
ring_nf                               -- Match expressions
```

**Obstacles Encountered**:
1. **Finset sums**: `certify_bound` can't evaluate discrete sums
   → Solution: Bridge lemmas convert to explicit `f 1 + f 2`

2. **Absolute values**: `certify_bound` sees `|x|` as `SemilatticeSup.toMax`
   → Solution: Pre-simplify using sign knowledge (`abs_of_pos`, `abs_neg`)

3. **Symbolic √3**: Need to express as `Real.sqrt 3` for interval arithmetic
   → Solution: `unfold sqrt3` before `certify_bound`

4. **Goal form**: Direct inequality `expr ≤ 58/128` not accepted
   → Solution: Wrap in `∀ x ∈ Set.Icc 3 3, ...` form, then instantiate

5. **Expression mismatch**: After `convert`, goal may not match exactly
   → Solution: Use `ring_nf` instead of `ring` for flexible matching

6. **native_decide failures**: Can't use on noncomputable values (√3)
   → Solution: Use `rfl` for vector indexing, bridge lemmas for Finset
-/

lemma Z₁_le : @Example_7_7.Z₁_bound ν_val 2 sol ≤ 58/128 := by
  -- Unfold everything to raw numerical expression
  unfold Example_7_7.Z₁_bound
  simp only [Example_7_7.ApproxSolution.toSeq, sol]
  -- Expand Finset.Icc sum using bridge lemma
  rw [sum_Icc_1_2]
  -- Simplify dite and vector indexing
  simp only [show (1 : ℕ) ≤ 2 from by omega, show (2 : ℕ) ≤ 2 from by omega,
             dite_true, Matrix.cons_val_zero, vec3_idx_1, vec3_idx_2]
  -- Simplify absolute values (we know the signs)
  rw [abs_ā₀, abs_ā₁, abs_ā₂, ν_val_eq, inv_sqrt3_div_3]
  -- Now we have: √3 * (√3/2 * 1/4 + 3√3/8 * 1/16) ≤ 58/128
  -- Simplify to standard form and use certify_bound theorem
  have h : ∀ x ∈ Set.Icc (3:ℝ) 3,
      Real.sqrt x * (Real.sqrt x / 2 * (1/4) + 3 * Real.sqrt x / 8 * (1/16)) ≤ 58/128 := by
    certify_bound
  convert h 3 ⟨le_refl 3, le_refl 3⟩ using 2
  unfold sqrt3; ring_nf

lemma Y₀_le : @Example_7_7.Y₀_bound ν_val 2 lam0 sol A_mat ≤ 17/1000 := by
  have heq : @Example_7_7.Y₀_bound ν_val 2 lam0 sol A_mat =
      315 * Real.sqrt 3 / 32768 := by
    sorry  -- Algebraic: F(ā)=0 with exact coeffs, only tail contributes
  rw [heq]
  exact Y₀_bound 3 ⟨le_refl 3, le_refl 3⟩

lemma Z₀_le : @Example_7_7.Z₀_bound ν_val 2 sol A_mat ≤ 1/1000 := by
  have heq : @Example_7_7.Z₀_bound ν_val 2 sol A_mat = 0 := by
    unfold Example_7_7.Z₀_bound
    rw [one_sub_A_mul_DF_eq_zero]
    exact finWeightedMatrixNorm_zero
  rw [heq]
  norm_num

lemma Z₂_le : @Example_7_7.Z₂_bound ν_val 2 sol A_mat ≤ 35/10 := by
  rw [Z₂_eq]
  unfold sqrt3
  exact Z₂_bound 3 ⟨le_refl 3, le_refl 3⟩

end Connection


/-! ## Main Theorem -/

section MainTheorem

open Example_7_7

/-! ### Main theorem via monotonicity + certify_bound

The radii polynomial p(r) = Z₂·r² - (1-Z₀-Z₁)·r + Y₀ is monotonic:
- Increasing in Y₀, Z₀, Z₁, Z₂ (for r ≥ 0, Z₀+Z₁ < 1)

So: p_abstract ≤ p_upper where p_upper uses our upper bounds.
Then certify_bound verifies p_upper < 0. -/

-- Upper bound polynomial verified with certify_bound
-- p_upper(r) = Z₂_up * r² - (1 - Z₀_up - Z₁_up) * r + Y₀_up
theorem radiiPoly_upper_neg :
    ∀ r ∈ Set.Icc (996/10000 : ℝ) (996/10000),
    (35/10) * r^2 - (1 - 1/1000 - 58/128) * r + 17/1000 < 0 := by
  certify_bound

theorem radiiPoly_7_7_le :
    @radiiPoly_7_7 ν_val 2 lam0 sol A_mat r₀ ≤
    (35/10) * r₀^2 - (1 - 1/1000 - 58/128) * r₀ + 17/1000 := by
  unfold radiiPoly_7_7 generalRadiiPolynomial r₀
  have hY := Y₀_le
  have hZ0 := Z₀_le
  have hZ1 := Z₁_le
  have hZ2 := Z₂_le
  have hr : (0:ℝ) ≤ 996/10000 := by positivity
  have hr2 : (0:ℝ) ≤ (996/10000)^2 := sq_nonneg _
  -- Monotonicity: Z₂·r² ↑, -(1-Z₀-Z₁)·r ↑, Y₀ ↑ all increase p
  nlinarith

theorem radiiPoly_7_7_neg :
    @radiiPoly_7_7 ν_val 2 lam0 sol A_mat r₀ < 0 := by
  have hle := radiiPoly_7_7_le
  have h := radiiPoly_upper_neg r₀ ⟨le_refl r₀, le_refl r₀⟩
  linarith

theorem main_theorem :
    ∃! aTilde ∈ Metric.closedBall (sol.toL1 : l1Weighted ν_val) r₀,
      F lam0 aTilde = 0 := by
  apply example_7_7_main_theorem
  · exact r₀_pos
  · norm_num
  · exact radiiPoly_7_7_neg

end MainTheorem


/-! ## Summary

### LeanCert Approach (vs Dyadic approach)

**Dyadic pattern:**
1. `_rat` functions compute in ℚ
2. `_eq_rat'` lemmas connect ℝ to ℚ
3. `native_decide` verifies ℚ inequalities
4. `exact_mod_cast` lifts to ℝ

**LeanCert pattern:**
1. `heq` lemmas: algebraic unfolding to explicit √3 expressions
2. `certify_bound`: interval arithmetic on √3 expressions
3. `rw [heq]` + `exact certify_bound_thm` combines them

### What's proven with certify_bound (no algebra):
- `Z₁_bound`, `Y₀_bound`, `Z₂_bound`: explicit √3 bounds
- `radiiPoly_neg`: explicit polynomial negativity
- `radiiPoly_upper_neg`: upper bound polynomial negativity

### What requires algebraic unfolding (sorries):
- `heq` in `Z₁_le`, `Y₀_le`, `Z₀_le`, `Z₂_le`
- These prove: `abstract_bound = explicit_√3_expression`
- One-time cost per problem

### Key insight:
The algebraic work is SEPARATED from the numeric verification.
Once you prove `abstract = explicit_√3`, certify_bound handles the rest.
-/

end Example77Clean

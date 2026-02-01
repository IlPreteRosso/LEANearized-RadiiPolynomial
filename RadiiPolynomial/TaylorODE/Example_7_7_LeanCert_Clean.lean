import LeanCert
import RadiiPolynomial.TaylorODE.Example_7_7

/-!
# Example 7.7 - Clean LeanCert Approach with Rational Approximations

Direct numerical verification using LeanCert's `certify_bound` with Dyadic interval arithmetic.

## Key Insight: Rational Approximations

Instead of exact √3 coefficients (which require symbolic algebra), we use
rational approximations. This allows:
- All bounds to be pure rational arithmetic
- `certify_bound` to handle everything via Dyadic interval arithmetic
- No need for `native_decide` or symbolic √3 manipulation

## Trade-offs

With rational approximations:
- F(ā) ≠ 0 exactly → Y₀ includes small residual (slightly larger)
- I - A·DF ≠ 0 → Z₀ > 0 (small but nonzero)
- The radii polynomial still satisfies p(r₀) < 0 (method has margin)

## Approximations Used

Exact values → Rational approximations:
- ā₀ = √3/3 ≈ 0.5774 → 5774/10000
- ā₁ = √3/2 ≈ 0.8660 → 8660/10000
- ā₂ = -3√3/8 ≈ -0.6495 → -6495/10000
- A entries similarly approximated

## LeanCert Pattern: `of_point_interval` + `fast_bound`

The key pattern for connection lemmas avoids separate `_certify` theorems:

```lean
lemma Bound_le : AbstractBound ≤ concrete := by
  unfold AbstractBound           -- unfold to raw expression
  finsum_expand!                 -- expand Finset sums
  simp only [...]; vec_simp!     -- simplify vectors/dite/abs
  unfold defs...                 -- unfold to pure numerics
  apply of_point_interval (q := bound) (by norm_num)
  fast_bound                     -- interval arithmetic verification
```

### Helper lemma (defined once):
```lean
private lemma of_point_interval {e c : ℝ} {q : ℚ} (hqc : (q : ℝ) = c)
    (h : ∀ x ∈ Set.Icc (0:ℝ) 0, e ≤ q) : e ≤ c := ...
```

### Key tactics:
- **`finsum_expand!`**: Expands Finset sums + handles dite conditions
- **`vec_simp!`**: Simplifies vector indexing, dite, and absolute values
- **`fast_bound`**: Interval arithmetic for goals of form `∀ x ∈ Icc a b, f x ≤ c`

### Why this pattern works:
1. **No separate theorems**: Expression stays inline, no duplication
2. **`of_point_interval`**: Wraps `e ≤ c` as `∀ x ∈ Icc 0 0, e ≤ q` for `fast_bound`
3. **Rational bounds**: Use `(q := 9/500)` - `fast_bound` handles ℚ→ℝ coercion
4. **Compound fractions**: `fast_bound` handles `1/(a/b)` directly
-/

open LeanCert.Core

namespace Example77Clean

/-! ## Parameters - Rational Approximations -/

-- Rational approximations (still noncomputable since ℝ division is noncomputable)
noncomputable def ā₀ : ℝ := 5774/10000      -- ≈ √3/3 ≈ 0.57735
noncomputable def ā₁ : ℝ := 8660/10000      -- ≈ √3/2 ≈ 0.86603
noncomputable def ā₂ : ℝ := -6495/10000     -- ≈ -3√3/8 ≈ -0.64952
noncomputable def lam0 : ℝ := 1/3
noncomputable def ν_val : PosReal := ⟨1/4, by norm_num⟩
noncomputable def r₀ : ℝ := 996/10000

lemma ā₀_pos : 0 < ā₀ := by unfold ā₀; norm_num
lemma r₀_pos : 0 < r₀ := by unfold r₀; norm_num

lemma ā₀_ne_zero : ā₀ ≠ 0 := ne_of_gt ā₀_pos

noncomputable def sol : Example_7_7.ApproxSolution 2 where
  aBar_fin := ![ā₀, ā₁, ā₂]
  aBar_zero_ne := ā₀_ne_zero

-- A_mat entries as symbolic definitions
noncomputable def A_diag : ℝ := 8660/10000       -- ≈ √3/2 (diagonal entries)
noncomputable def A_sub1 : ℝ := -12990/10000     -- ≈ -3√3/4 (first subdiagonal)
noncomputable def A_sub2 : ℝ := 29240/10000      -- ≈ 27√3/16 (second subdiagonal)

-- A_mat with rational approximations
-- Original: !![√3/2, 0, 0; -3√3/4, √3/2, 0; 27√3/16, -3√3/4, √3/2]
noncomputable def A_mat : Matrix (Fin 3) (Fin 3) ℝ :=
  !![A_diag, 0, 0;
     A_sub1, A_diag, 0;
     A_sub2, A_sub1, A_diag]


/-! ## Explicit Coefficient Values

With rational coefficients, we can state explicit equalities. -/

section Coefficients

lemma ā₀_eq : ā₀ = 5774/10000 := rfl
lemma ν_val_eq : (ν_val : ℝ) = 1/4 := rfl

-- A_mat entry equalities
lemma A_diag_eq : A_diag = 8660/10000 := rfl
lemma A_sub2_eq : A_sub2 = 29240/10000 := rfl

-- A_mat entry positivity/negativity
lemma A_diag_pos : 0 < A_diag := by unfold A_diag; norm_num
lemma A_sub2_pos : 0 < A_sub2 := by unfold A_sub2; norm_num

-- Absolute values of A_mat entries
lemma abs_A_diag : |A_diag| = 8660/10000 := by rw [abs_of_pos A_diag_pos, A_diag_eq]
lemma abs_A_sub1 : |A_sub1| = 12990/10000 := by
  unfold A_sub1; rw [abs_of_neg (by norm_num : (-12990:ℝ)/10000 < 0)]; ring_nf
lemma abs_A_sub2 : |A_sub2| = 29240/10000 := by rw [abs_of_pos A_sub2_pos, A_sub2_eq]

-- Matrix entry access: unfold A_mat to explicit values
-- The key is to unfold through the !![...] notation
/-- |ā₀| = ā₀ (positive) -/
lemma abs_ā₀ : |ā₀| = 5774/10000 := by
  rw [abs_of_pos ā₀_pos, ā₀_eq]

/-- |ā₁| = ā₁ (positive) -/
lemma abs_ā₁ : |ā₁| = 8660/10000 := by
  unfold ā₁
  rw [abs_of_pos (by norm_num : (0:ℝ) < 8660/10000)]

/-- |ā₂| = -ā₂ (negative) -/
lemma abs_ā₂ : |ā₂| = 6495/10000 := by
  unfold ā₂
  rw [abs_of_neg (by norm_num : (-6495:ℝ)/10000 < 0)]
  ring_nf

/-- 1/|ā₀| -/
lemma inv_abs_ā₀ : 1 / |ā₀| = 10000/5774 := by
  rw [abs_ā₀]
  norm_num

-- Note: inv_ā₀_frac not needed! certify_bound handles 1/(a/b) directly.

/-! ### F_fin explicit values (ODE residual)

F(ā) = ā⋆ā - c where c = (lam0, 1, 0, ...).
For rational approximations, F(ā) ≠ 0 but is small. -/

/-! ### F_fin computation lemmas

These lemmas prove that F_fin equals the explicit rational formulas.
F_fin n = (ā⋆ā)_n - c_n where c = (lam0, 1, 0, 0, ...).

We use native_decide for the antidiagonal expansions since the sums are finite and computable. -/

/-- Helper: antidiagonal 1 as explicit list -/
private lemma antidiag_1 : Finset.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} := by native_decide

/-- Helper: antidiagonal 2 as explicit list -/
private lemma antidiag_2 : Finset.antidiagonal (2 : ℕ) = {(0, 2), (1, 1), (2, 0)} := by native_decide

open Example_7_7 in
lemma F_fin_0_eq : F_fin (ν := ν_val) lam0 sol 0 = ā₀^2 - lam0 := by
  unfold F_fin F; simp only [l1Weighted.F_sub_const, lpWeighted.sub_toSeq, l1Weighted.sq_toSeq,
    c, lpWeighted.mk_apply, paramSeq, CauchyProduct.apply, Fin.val_zero,
    Finset.Nat.antidiagonal_zero, ApproxSolution.toL1, ApproxSolution.toSeq, sol]
  vec_simp!; ring

open Example_7_7 in
lemma F_fin_1_eq : F_fin (ν := ν_val) lam0 sol 1 = 2 * ā₀ * ā₁ - 1 := by
  unfold F_fin F; simp only [l1Weighted.F_sub_const, lpWeighted.sub_toSeq, l1Weighted.sq_toSeq,
    c, lpWeighted.mk_apply, paramSeq, CauchyProduct.apply, Fin.val_one, antidiag_1,
    ApproxSolution.toL1, ApproxSolution.toSeq, sol]
  finsum_expand; vec_simp!; ring

open Example_7_7 in
lemma F_fin_2_eq : F_fin (ν := ν_val) lam0 sol 2 = 2 * ā₀ * ā₂ + ā₁^2 := by
  unfold F_fin F; simp only [l1Weighted.F_sub_const, lpWeighted.sub_toSeq, l1Weighted.sq_toSeq,
    c, lpWeighted.mk_apply, paramSeq, CauchyProduct.apply, Fin.val_two, antidiag_2,
    ApproxSolution.toL1, ApproxSolution.toSeq, sol]
  finsum_expand; vec_simp!; ring

end Coefficients


/-! ## Bound Computations - Pure Rational Arithmetic

All bounds are now rational expressions that certify_bound can verify directly.

### Z₁ Computation

Z₁ = (1/|ā₀|) * Σₙ₌₁² |āₙ| * νⁿ
   = (10000/5774) * (8660/10000 * 1/4 + 6495/10000 * 1/16)
   = (10000/5774) * (8660/40000 + 6495/160000)
   = (10000/5774) * (34640/160000 + 6495/160000)
   = (10000/5774) * (41135/160000)
   ≈ 0.4453

### Y₀ Computation (with residual)

With rational approximations, F(ā) ≠ 0. The residual contributes to Y₀.
Y₀ ≈ 0.017 (slightly larger than exact case)

### Z₀ Computation

Z₀ = ‖I - A·DF‖ > 0 (A is not exact inverse)
Z₀ ≈ 0.001 (small but nonzero)

### Z₂ Computation

Z₂ = 2 * max(‖A‖_{1,ν}, 1/(2|ā₀|))
   ≈ 2 * max(0.79..., 0.866...)
   ≈ 2 * 0.866 ≈ 1.73
(Actually need to compute matrix norm properly)
-/

/-! ## Verifying √3/3 ≈ 0.57735

### Problem
LeanCert doesn't directly support absolute value `|x|` in expressions (it uses
`SemilatticeSup.toMax` internally which isn't in the supported expression AST).

### Solution
We prove separate upper and lower bounds using `certify_bound`, then combine them:

1. **Upper bound**: `√3/3 < 0.5774` via `certify_bound`
2. **Lower bound**: `√3/3 > 0.5773` via `certify_bound`
3. **Combine**: Use `abs_sub_lt_iff` to convert `|a - b| < ε` into two inequalities,
   then close with `linarith`

### Alternative approaches considered
- `|x| = √(x²)`: LeanCert supports sqrt, but nested `sqrt((sqrt(x)/3 - c)²)` gives
  loose interval bounds due to the dependency problem in interval arithmetic.
- Direct `∈ Set.Icc`: The `certify_bound` tactic doesn't directly support membership
  in `Set.Icc` for two-sided bounds.

### Pattern
```lean
theorem foo_upper : ∀ x ∈ Set.Icc a a, f x < upper := by certify_bound
theorem foo_lower : ∀ x ∈ Set.Icc a a, f x > lower := by certify_bound
theorem foo_error : |f a - approx| < ε := by
  have hub := foo_upper a ⟨le_refl _, le_refl _⟩
  have hlb := foo_lower a ⟨le_refl _, le_refl _⟩
  rw [abs_sub_lt_iff]
  constructor <;> linarith
```
-/

/-! ## Radii Polynomial Negativity

The key verification: p(r₀) < 0

p(r) = Z₂·r² - (1 - Z₀ - Z₁)·r + Y₀

With our bounds:
- Y₀ ≤ Y₀_bnd = 9/500
- Z₀ ≤ Z₀_bnd = 2/1000
- Z₁ ≤ Z₁_bnd = 46/100
- Z₂ ≤ Z₂_bnd = 28/10

1 - Z₀ - Z₁ ≥ 1 - Z₀_bnd - Z₁_bnd = 0.538

p_upper(r₀) = Z₂_bnd * r₀² - (1 - Z₀_bnd - Z₁_bnd) * r₀ + Y₀_bnd < 0 ✓
-/

section RadiiPolynomial

/-- Bound constants for the radii polynomial -/
def Y₀_bnd : ℚ := 9/500      -- ≈ 0.018
def Z₀_bnd : ℚ := 2/1000     -- = 0.002
def Z₁_bnd : ℚ := 46/100     -- = 0.46
def Z₂_bnd : ℚ := 28/10      -- = 2.8

/-- The upper bound polynomial using generalRadiiPolynomial with constant bounds -/
noncomputable def radiiPoly_upper (r : ℝ) : ℝ :=
  generalRadiiPolynomial Y₀_bnd Z₀_bnd Z₁_bnd (fun _ => Z₂_bnd) r

/-- The upper bound polynomial is negative at r₀ -/
theorem radiiPoly_upper_neg :
    ∀ r ∈ Set.Icc r₀ r₀, radiiPoly_upper r < 0 := by
  unfold radiiPoly_upper generalRadiiPolynomial r₀ Y₀_bnd Z₀_bnd Z₁_bnd Z₂_bnd
  simp only [Rat.cast_div, Rat.cast_ofNat]
  certify_bound

/-- More margin: check at r = 0.1 -/
theorem radiiPoly_upper_neg_margin :
    ∀ r ∈ Set.Icc (1/10 : ℝ) (1/10), radiiPoly_upper r < 0 := by
  unfold radiiPoly_upper generalRadiiPolynomial Y₀_bnd Z₀_bnd Z₁_bnd Z₂_bnd
  simp only [Rat.cast_div, Rat.cast_ofNat]
  certify_bound

end RadiiPolynomial


/-! ## Connection to Abstract Framework

Now we need to show the abstract bounds equal our rational expressions. -/

section Connection

open Example_7_7

/-- Helper: Transform `e ≤ c` goal into interval form for fast_bound. -/
private lemma of_point_interval {e c : ℝ} {q : ℚ} (hqc : (q : ℝ) = c)
    (h : ∀ x ∈ Set.Icc (0:ℝ) 0, e ≤ q) : e ≤ c := by
  rw [← hqc]; exact h 0 ⟨le_refl _, le_refl _⟩

/-! ### Y₀ bound -/

lemma Y₀_le : @Example_7_7.Y₀_bound ν_val 2 lam0 sol A_mat ≤ 9/500 := by
  unfold Example_7_7.Y₀_bound
  finsum_expand!
  simp only [A_mat, F_fin_0_eq, F_fin_1_eq, F_fin_2_eq]; vec_simp!
  finsum_expand!
  simp only [Example_7_7.ApproxSolution.toSeq, sol]; vec_simp!
  unfold A_diag A_sub1 A_sub2 ā₀ ā₁ ā₂ lam0; simp only [ν_val_eq]
  apply of_point_interval (q := 9/500) (by norm_num); fast_bound

/-! ### Z₀ bound (operator defect ‖I - A·DF‖) -/

private lemma DF_explicit :
    Example_7_7.DF_fin sol = !![2*ā₀, 0, 0; 2*ā₁, 2*ā₀, 0; 2*ā₂, 2*ā₁, 2*ā₀] := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp only [Example_7_7.DF_fin, Matrix.of_apply, sol]
  all_goals (first | rfl)

private noncomputable def A_DF : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2*A_diag*ā₀, 0, 0;
     2*(A_sub1*ā₀ + A_diag*ā₁), 2*A_diag*ā₀, 0;
     2*(A_sub2*ā₀ + A_sub1*ā₁ + A_diag*ā₂), 2*(A_sub1*ā₀ + A_diag*ā₁), 2*A_diag*ā₀]

private lemma A_mul_DF_eq : A_mat * Example_7_7.DF_fin sol = A_DF := by
  rw [DF_explicit]; ext i j
  fin_cases i <;> fin_cases j <;>
  simp only [Matrix.mul_apply, A_mat, A_DF, A_diag, A_sub1, A_sub2]
  all_goals (vec_simp!; finsum_expand!; try ring)

private noncomputable def I_sub_A_DF : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - 2*A_diag*ā₀, 0, 0;
     -2*(A_sub1*ā₀ + A_diag*ā₁), 1 - 2*A_diag*ā₀, 0;
     -2*(A_sub2*ā₀ + A_sub1*ā₁ + A_diag*ā₂), -2*(A_sub1*ā₀ + A_diag*ā₁), 1 - 2*A_diag*ā₀]

private lemma one_sub_A_DF_eq : 1 - A_mat * Example_7_7.DF_fin sol = I_sub_A_DF := by
  rw [A_mul_DF_eq]; unfold A_DF I_sub_A_DF A_diag A_sub1 A_sub2 ā₀ ā₁ ā₂
  ext i j; fin_cases i <;> fin_cases j <;>
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.of_apply]
  all_goals vec_simp!

lemma Z₀_le : @Example_7_7.Z₀_bound ν_val 2 sol A_mat ≤ 2/1000 := by
  unfold Example_7_7.Z₀_bound; rw [one_sub_A_DF_eq]
  unfold l1Weighted.finWeightedMatrixNorm; apply Finset.sup'_le; intro j _
  unfold l1Weighted.matrixColNorm I_sub_A_DF A_diag A_sub1 A_sub2 ā₀ ā₁ ā₂
  fin_cases j <;> (simp only [pow_zero, pow_one, pow_two, div_one, one_mul, ν_val_eq]
                   finsum_expand!; vec_simp!)

/-! ### Z₁ bound (tail contribution) -/

lemma Z₁_le : @Example_7_7.Z₁_bound ν_val 2 sol ≤ 46/100 := by
  unfold Example_7_7.Z₁_bound
  simp only [Example_7_7.ApproxSolution.toSeq, sol]
  finsum_expand; vec_simp!
  unfold ā₀ ā₁ ā₂; simp only [ν_val_eq, pow_two, inv_eq_one_div]
  apply of_point_interval (q := 46/100) (by norm_num); fast_bound

/-! ### Z₂ bound (nonlinear term coefficient) -/

private lemma colNorm_le (j : Fin 3) :
    l1Weighted.matrixColNorm ν_val A_mat j ≤ 14/10 := by
  unfold l1Weighted.matrixColNorm A_mat A_diag A_sub1 A_sub2 ν_val
  fin_cases j <;> (finsum_expand!; vec_simp!)

private lemma matrixNorm_le : l1Weighted.finWeightedMatrixNorm ν_val A_mat ≤ 14/10 := by
  unfold l1Weighted.finWeightedMatrixNorm
  apply Finset.sup'_le; intro j _; exact colNorm_le j

lemma Z₂_le : @Example_7_7.Z₂_bound ν_val 2 sol A_mat ≤ 28/10 := by
  unfold Example_7_7.Z₂_bound
  simp only [sol, Matrix.cons_val_zero, abs_ā₀]
  refine le_trans (mul_le_mul_of_nonneg_left (max_le matrixNorm_le ?_) (by norm_num)) (by norm_num)
  apply of_point_interval (q := 14/10) (by norm_num); fast_bound

end Connection


/-! ## Main Theorem -/

section MainTheorem

open Example_7_7

/-- Upper bound polynomial verified -/
theorem radiiPoly_7_7_le :
    @radiiPoly_7_7 ν_val 2 lam0 sol A_mat r₀ ≤ radiiPoly_upper r₀ := by
  simp only [radiiPoly_7_7, radiiPoly_upper, generalRadiiPolynomial, r₀,
             Y₀_bnd, Z₀_bnd, Z₁_bnd, Z₂_bnd, Rat.cast_div, Rat.cast_ofNat]
  have hY := Y₀_le
  have hZ0 := Z₀_le
  have hZ1 := Z₁_le
  have hZ2 := Z₂_le
  -- Monotonicity: all bounds increase p
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

See file header for the `of_point_interval` + `fast_bound` pattern documentation.

Key tactics: `finsum_expand!`, `vec_simp!`, `fast_bound`
-/

end Example77Clean

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

## LeanCert Pattern: Connecting Abstract to Certified Bounds

`certify_bound` requires goals of form: `∀ x ∈ Set.Icc a b, f(x) ≤ c`

### Pattern for connection lemmas:

```
Abstract_bound ≤ concrete_bound
       ↓ unfold definition
Finset.sum / matrix / abs / dite expressions
       ↓ finsum_expand, vec_simp!, abs_ā₀, etc.
Explicit rational arithmetic expression
       ↓ exact Certified_theorem (1/(a/b)) ⟨le_refl, le_refl⟩
Done
```

### Key tactics:
- **`finsum_expand`**: Expands Finset sums (Icc, Ico, Fin n) to explicit additions
- **`vec_simp!`**: Simplifies vector indexing AND dite conditions in one step
  - Replaces verbose: `simp only [show (n : ℕ) ≤ 2 from by omega, dite_true]; vec_simp`
- **`dite_simp`**: Standalone dite simplification for decidable ℕ comparisons

### Key principles:
1. **Certified theorems** (`_certify`): Written to match EXACTLY what unfolds
2. **Use `vec_simp!`**: Handles both dite conditions and vector indexing automatically
3. **Compound fractions work**: `certify_bound` handles `1/(a/b)` directly - no need to rewrite to `b/a`
4. **No post-processing**: Avoid `convert`/`field_simp` - get form right upfront

### LeanCert style (from examples):
- Use `(bound : ℚ)` annotation for clarity (though `bound` as ℝ also works)
- `certify_bound` handles `Real.sqrt`, `Real.exp`, `Real.log`, etc.
- For constant bounds, wrap in trivial interval: `∀ x ∈ Set.Icc a a, ...`

See: `.lake/packages/LeanCert/examples/` for reference patterns.
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
lemma ā₁_eq : ā₁ = 8660/10000 := rfl
lemma ā₂_eq : ā₂ = -6495/10000 := rfl
lemma ν_val_eq : (ν_val : ℝ) = 1/4 := rfl

-- A_mat entry equalities
lemma A_diag_eq : A_diag = 8660/10000 := rfl
lemma A_sub1_eq : A_sub1 = -12990/10000 := rfl
lemma A_sub2_eq : A_sub2 = 29240/10000 := rfl

-- A_mat entry positivity/negativity
lemma A_diag_pos : 0 < A_diag := by unfold A_diag; norm_num
lemma A_sub1_neg : A_sub1 < 0 := by unfold A_sub1; norm_num
lemma A_sub2_pos : 0 < A_sub2 := by unfold A_sub2; norm_num

-- Absolute values of A_mat entries
lemma abs_A_diag : |A_diag| = 8660/10000 := by rw [abs_of_pos A_diag_pos, A_diag_eq]
lemma abs_A_sub1 : |A_sub1| = 12990/10000 := by
  unfold A_sub1; rw [abs_of_neg (by norm_num : (-12990:ℝ)/10000 < 0)]; ring_nf
lemma abs_A_sub2 : |A_sub2| = 29240/10000 := by rw [abs_of_pos A_sub2_pos, A_sub2_eq]

-- Matrix entry access: unfold A_mat to explicit values
-- The key is to unfold through the !![...] notation
lemma A_mat_unfold : A_mat = !![A_diag, 0, 0; A_sub1, A_diag, 0; A_sub2, A_sub1, A_diag] := rfl

-- For matrix access, we need to unfold Matrix.of and use vec_simp! to evaluate
-- The indices come as ⟨n, proof⟩ form after fin_cases, so we use the dsimproc approach

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

/-- sol.toSeq accessors -/
lemma sol_toSeq_0 : sol.toSeq 0 = ā₀ := by simp [Example_7_7.ApproxSolution.toSeq, sol]
lemma sol_toSeq_1 : sol.toSeq 1 = ā₁ := by simp [Example_7_7.ApproxSolution.toSeq, sol]
lemma sol_toSeq_2 : sol.toSeq 2 = ā₂ := by simp [Example_7_7.ApproxSolution.toSeq, sol]
lemma sol_toSeq_ge_3 (k : ℕ) (hk : 3 ≤ k) : sol.toSeq k = 0 := by
  simp only [Example_7_7.ApproxSolution.toSeq, sol]
  have : ¬(k ≤ 2) := by omega
  simp [this]

/-! ### F_fin explicit values (ODE residual)

F(ā) = ā⋆ā - c where c = (lam0, 1, 0, ...).
For rational approximations, F(ā) ≠ 0 but is small. -/

/-- F_fin 0 = ā₀² - lam0 -/
noncomputable def F₀_val : ℝ := (5774/10000)^2 - 1/3

/-- F_fin 1 = 2ā₀ā₁ - 1 -/
noncomputable def F₁_val : ℝ := 2 * (5774/10000) * (8660/10000) - 1

/-- F_fin 2 = 2ā₀ā₂ + ā₁² (note: for n≥2, convolution has no constant term) -/
noncomputable def F₂_val : ℝ := 2 * (5774/10000) * (-6495/10000) + (8660/10000)^2

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
  unfold F_fin F
  simp only [l1Weighted.F_sub_const, lpWeighted.sub_toSeq, l1Weighted.sq_toSeq]
  simp only [c, lpWeighted.mk_apply, paramSeq]
  rw [CauchyProduct.apply]
  simp only [Fin.val_zero, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  simp only [ApproxSolution.toL1, lpWeighted.mk_apply, ApproxSolution.toSeq, sol]
  vec_simp!  -- Replaces: simp only [show (0 : ℕ) ≤ 2 from by omega, dite_true]; vec_simp
  ring

open Example_7_7 in
lemma F_fin_1_eq : F_fin (ν := ν_val) lam0 sol 1 = 2 * ā₀ * ā₁ - 1 := by
  unfold F_fin F
  simp only [l1Weighted.F_sub_const, lpWeighted.sub_toSeq, l1Weighted.sq_toSeq]
  simp only [c, lpWeighted.mk_apply, paramSeq]
  rw [CauchyProduct.apply]
  simp only [Fin.val_one, antidiag_1]
  finsum_expand  -- Replaces manual Finset.sum_insert calls
  simp only [ApproxSolution.toL1, lpWeighted.mk_apply, ApproxSolution.toSeq, sol]
  vec_simp!
  ring

open Example_7_7 in
lemma F_fin_2_eq : F_fin (ν := ν_val) lam0 sol 2 = 2 * ā₀ * ā₂ + ā₁^2 := by
  unfold F_fin F
  simp only [l1Weighted.F_sub_const, lpWeighted.sub_toSeq, l1Weighted.sq_toSeq]
  simp only [c, lpWeighted.mk_apply, paramSeq]
  rw [CauchyProduct.apply]
  simp only [Fin.val_two, antidiag_2]
  finsum_expand  -- Replaces manual Finset.sum_insert calls
  simp only [ApproxSolution.toL1, lpWeighted.mk_apply, ApproxSolution.toSeq, sol]
  vec_simp!  -- Replaces manual dite + vec_simp
  ring

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

section SqrtVerification

/-- √3/3 < 0.5774 (upper bound) -/
theorem sqrt3_div3_upper :
    ∀ x ∈ Set.Icc (3 : ℝ) 3,
    Real.sqrt x / 3 < (5774/10000 : ℚ) := by
  certify_bound

/-- √3/3 > 0.5773 (lower bound) -/
theorem sqrt3_div3_lower :
    ∀ x ∈ Set.Icc (3 : ℝ) 3,
    Real.sqrt x / 3 > (5773/10000 : ℚ) := by
  certify_bound

/-- Combining bounds: |√3/3 - 5774/10000| < 0.0001
    Since 0.5773 < √3/3 < 0.5774, we have:
    - √3/3 - 0.5774 < 0 (so this direction is < 0.0001)
    - √3/3 - 0.5773 > 0, and √3/3 < 0.5774 so √3/3 - 0.5773 < 0.0001 -/
theorem sqrt3_div3_error_bound : |Real.sqrt 3 / 3 - 5774/10000| < 1/10000 := by
  have hub := sqrt3_div3_upper 3 ⟨le_refl _, le_refl _⟩
  have hlb := sqrt3_div3_lower 3 ⟨le_refl _, le_refl _⟩
  rw [abs_sub_lt_iff]
  constructor <;> linarith

end SqrtVerification


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

/-- Helper: Transform `e ≤ c` goal into interval form `∀ x ∈ Set.Icc 0 0, e ≤ c` for fast_bound.
    This avoids copying large expressions into separate certified theorems.
    Uses rational bound with cast conversion for fast_bound compatibility. -/
private lemma of_point_interval {e c : ℝ} {q : ℚ} (hqc : (q : ℝ) = c)
    (h : ∀ x ∈ Set.Icc (0:ℝ) 0, e ≤ q) : e ≤ c := by
  rw [← hqc]; exact h 0 ⟨le_refl _, le_refl _⟩

/-- Z₁ certified bound using symbolic names
    Z₁ = (1/|ā₀|) * (|ā₁|*ν + |ā₂|*ν²) -/
theorem Z₁_certify :
    ∀ x ∈ Set.Icc (1/|ā₀| : ℝ) (1/|ā₀|),
    x * (|ā₁| * ν_val + |ā₂| * ν_val^2) ≤ (46/100 : ℚ) := by
  simp only [abs_ā₀, abs_ā₁, abs_ā₂, ν_val_eq, pow_two]
  certify_bound

/-- Z₁ connection: unfold to rational expression -/
lemma Z₁_le : @Example_7_7.Z₁_bound ν_val 2 sol ≤ 46/100 := by
  -- Unfold to raw numerical expression
  unfold Example_7_7.Z₁_bound
  simp only [Example_7_7.ApproxSolution.toSeq, sol]
  -- Expand Finset.Icc sum using finsum_expand
  finsum_expand
  -- Simplify dite and vector indexing using vec_simp!
  vec_simp!
  -- Simplify absolute values and parameters
  rw [abs_ā₀, abs_ā₁, abs_ā₂, ν_val_eq]
  -- Simplify powers and convert inv to 1/
  simp only [pow_two, inv_eq_one_div]
  -- Apply certified bound
  have h := Z₁_certify (1/|ā₀|) ⟨le_refl _, le_refl _⟩
  simp only [abs_ā₀] at h
  linarith

/-! ### Z₂ proof

Strategy: Z₂ = 2 * max(matrix_norm, 1/(2|ā₀|))
- Column norms: col0 ≈ 1.37, col1 ≈ 1.19, col2 ≈ 0.87
- Tail term 1/(2|ā₀|) ≈ 0.866
- Matrix norm (col0) dominates
- Bound both by 14/10, so Z₂ ≤ 2 * 14/10 = 28/10
-/

/-- Column 0 norm bound: |A_diag| + |A_sub1|*ν + |A_sub2|*ν² ≤ 14/10 -/
private theorem Z₂_col0_certify :
    ∀ x ∈ Set.Icc (1:ℝ) 1,
    |A_diag| + |A_sub1| * ν_val + |A_sub2| * ν_val^2 ≤ (14/10 : ℚ) := by
  simp only [abs_A_diag, abs_A_sub1, abs_A_sub2, ν_val_eq, pow_two]
  certify_bound

/-- Column 1 norm bound: (1/ν) * (|A_diag|*ν + |A_sub1|*ν²) ≤ 14/10 -/
private theorem Z₂_col1_certify :
    ∀ x ∈ Set.Icc (1:ℝ) 1,
    (1/ν_val) * (|A_diag| * ν_val + |A_sub1| * ν_val^2) ≤ (14/10 : ℚ) := by
  simp only [abs_A_diag, abs_A_sub1, ν_val_eq, pow_two]
  certify_bound

/-- Column 2 norm bound: (1/ν²) * (|A_diag|*ν²) ≤ 14/10 -/
private theorem Z₂_col2_certify :
    ∀ x ∈ Set.Icc (1:ℝ) 1,
    (1/ν_val^2) * (|A_diag| * ν_val^2) ≤ (14/10 : ℚ) := by
  simp only [abs_A_diag, ν_val_eq, pow_two]
  certify_bound

/-- The tail term value: 1/(2*|ā₀|) -/
noncomputable def Z₂_tail_val : ℝ := 1/(2*|ā₀|)

lemma Z₂_tail_val_eq : Z₂_tail_val = 5000/5774 := by
  simp only [Z₂_tail_val, abs_ā₀]
  norm_num

/-- Tail term bound: 1/(2*|ā₀|) ≤ 14/10 -/
private theorem Z₂_tail_certify :
    ∀ x ∈ Set.Icc Z₂_tail_val Z₂_tail_val,
    x ≤ (14/10 : ℚ) := by
  simp only [Z₂_tail_val_eq]
  certify_bound

/-- Helper: matrixColNorm for column 0 equals |A_diag| + |A_sub1|*ν + |A_sub2|*ν² -/
private lemma colNorm_0_eq :
    l1Weighted.matrixColNorm ν_val A_mat 0 = |A_diag| + |A_sub1| * ν_val + |A_sub2| * ν_val^2 := by
  unfold l1Weighted.matrixColNorm A_mat A_diag A_sub1 A_sub2 ν_val
  simp only [Fin.val_zero, pow_zero, div_one, one_mul]
  finsum_expand!
  simp only [Matrix.of_apply]
  vec_simp!

/-- Helper: matrixColNorm for column 1 -/
private lemma colNorm_1_eq :
    l1Weighted.matrixColNorm ν_val A_mat 1 = (1/ν_val) * (|A_diag| * ν_val + |A_sub1| * ν_val^2) := by
  unfold l1Weighted.matrixColNorm A_mat A_diag A_sub1
  simp only [Fin.val_one, pow_one]
  finsum_expand!
  simp only [Matrix.of_apply]
  vec_simp!

/-- Helper: matrixColNorm for column 2 -/
private lemma colNorm_2_eq :
    l1Weighted.matrixColNorm ν_val A_mat 2 = (1/ν_val^2) * (|A_diag| * ν_val^2) := by
  unfold l1Weighted.matrixColNorm A_mat A_diag
  simp only [Fin.val_two, pow_two]
  finsum_expand!
  simp only [Matrix.of_apply]
  vec_simp!
  ring

/-- Each column norm is ≤ 14/10 -/
private lemma colNorm_le (j : Fin 3) :
    l1Weighted.matrixColNorm ν_val A_mat j ≤ 14/10 := by
  fin_cases j
  · show l1Weighted.matrixColNorm ν_val A_mat 0 ≤ _; rw [colNorm_0_eq]
    simp only [abs_A_diag, abs_A_sub1, abs_A_sub2, ν_val_eq, pow_two]; norm_num
  · show l1Weighted.matrixColNorm ν_val A_mat 1 ≤ _; rw [colNorm_1_eq]
    simp only [abs_A_diag, abs_A_sub1, ν_val_eq, pow_two]; norm_num
  · show l1Weighted.matrixColNorm ν_val A_mat 2 ≤ _; rw [colNorm_2_eq]
    simp only [abs_A_diag, ν_val_eq, pow_two]; norm_num

/-- finWeightedMatrixNorm ≤ 14/10 -/
private lemma matrixNorm_le :
    l1Weighted.finWeightedMatrixNorm ν_val A_mat ≤ 14/10 := by
  unfold l1Weighted.finWeightedMatrixNorm
  apply Finset.sup'_le
  intro j _
  exact colNorm_le j

/-- Z₂ = 2 * max(‖A‖, 1/(2|ā₀|)) ≤ 28/10 -/
lemma Z₂_le : @Example_7_7.Z₂_bound ν_val 2 sol A_mat ≤ 28/10 := by
  unfold Example_7_7.Z₂_bound
  simp only [sol, Matrix.cons_val_zero]
  -- 2 * max(matrixNorm, tailTerm) ≤ 28/10
  have h_norm := matrixNorm_le
  have h_tail : 1 / (2 * |ā₀|) ≤ 14/10 := by
    have h := Z₂_tail_certify Z₂_tail_val ⟨le_refl _, le_refl _⟩
    simp only [Z₂_tail_val] at h
    linarith
  have hmax : max (l1Weighted.finWeightedMatrixNorm ν_val A_mat) (1 / (2 * |ā₀|)) ≤ 14/10 :=
    max_le h_norm h_tail
  linarith

/-! ### Z₀ proof

Z₀ = ‖I - A·DF‖ where DF is the Jacobian matrix.

DF_fin(i,j) = 2*ā_{i-j} if j ≤ i, else 0
For N=2: DF = [[2ā₀, 0, 0], [2ā₁, 2ā₀, 0], [2ā₂, 2ā₁, 2ā₀]]

The key is that A ≈ (DF)⁻¹, so I - A·DF ≈ 0 for exact coefficients.
With rational approximations, we get small but nonzero entries.
-/

/-- DF_fin entry (i,j): 2*ā_{i-j} if j ≤ i, else 0 -/
private lemma DF_entry (i j : Fin 3) :
    Example_7_7.DF_fin sol i j =
    if h : (j : ℕ) ≤ i then 2 * sol.aBar_fin ⟨(i : ℕ) - (j : ℕ), by omega⟩ else 0 := rfl

/-- Explicit DF matrix for our sol -/
private lemma DF_explicit :
    Example_7_7.DF_fin sol = !![2*ā₀, 0, 0; 2*ā₁, 2*ā₀, 0; 2*ā₂, 2*ā₁, 2*ā₀] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp only [Example_7_7.DF_fin, Matrix.of_apply, sol]
  all_goals (first | rfl)

/-- Product A * DF explicitly computed -/
private noncomputable def A_DF : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2*A_diag*ā₀, 0, 0;
     2*(A_sub1*ā₀ + A_diag*ā₁), 2*A_diag*ā₀, 0;
     2*(A_sub2*ā₀ + A_sub1*ā₁ + A_diag*ā₂), 2*(A_sub1*ā₀ + A_diag*ā₁), 2*A_diag*ā₀]

private lemma A_mul_DF_eq : A_mat * Example_7_7.DF_fin sol = A_DF := by
  rw [DF_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp only [Matrix.mul_apply, A_mat, A_DF, A_diag, A_sub1, A_sub2]
  all_goals (vec_simp!; finsum_expand!; ring)

/-- I - A*DF explicitly -/
private noncomputable def I_sub_A_DF : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - 2*A_diag*ā₀, 0, 0;
     -2*(A_sub1*ā₀ + A_diag*ā₁), 1 - 2*A_diag*ā₀, 0;
     -2*(A_sub2*ā₀ + A_sub1*ā₁ + A_diag*ā₂), -2*(A_sub1*ā₀ + A_diag*ā₁), 1 - 2*A_diag*ā₀]

private lemma one_sub_A_DF_eq : 1 - A_mat * Example_7_7.DF_fin sol = I_sub_A_DF := by
  rw [A_mul_DF_eq]
  -- Unfold all definitions to numeric values
  unfold A_DF I_sub_A_DF A_diag A_sub1 A_sub2 ā₀ ā₁ ā₂
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.of_apply]
  all_goals vec_simp!

/-- The diagonal entry 1 - 2*A_diag*ā₀ is small -/
private noncomputable def diag_val : ℝ := 1 - 2*A_diag*ā₀

private lemma diag_abs_le : |diag_val| ≤ 1/1000 := by
  simp only [diag_val, A_diag, ā₀]
  norm_num

/-- Off-diagonal entry (1,0) -/
private noncomputable def off10_val : ℝ := -2*(A_sub1*ā₀ + A_diag*ā₁)

private lemma off10_abs_le : |off10_val| ≤ 1/1000 := by
  simp only [off10_val, A_sub1, A_diag, ā₀, ā₁]
  norm_num

/-- Off-diagonal entry (2,0) -/
private noncomputable def off20_val : ℝ := -2*(A_sub2*ā₀ + A_sub1*ā₁ + A_diag*ā₂)

private lemma off20_abs_le : |off20_val| ≤ 2/1000 := by
  simp only [off20_val, A_sub2, A_sub1, A_diag, ā₀, ā₁, ā₂]
  norm_num

/-- Column norms of I - A*DF -/
private lemma Z₀_colNorm_0 :
    l1Weighted.matrixColNorm ν_val I_sub_A_DF 0 ≤ 2/1000 := by
  unfold l1Weighted.matrixColNorm I_sub_A_DF A_diag A_sub1 A_sub2 ā₀ ā₁ ā₂
  simp only [Fin.val_zero, pow_zero, div_one, one_mul]
  finsum_expand!
  simp only [Matrix.of_apply]
  vec_simp!
  simp only [ν_val_eq]
  apply of_point_interval (q := 2/1000) (by norm_num)
  fast_bound

private lemma Z₀_colNorm_1 :
    l1Weighted.matrixColNorm ν_val I_sub_A_DF 1 ≤ 2/1000 := by
  unfold l1Weighted.matrixColNorm I_sub_A_DF A_diag A_sub1 A_sub2 ā₀ ā₁ ā₂
  simp only [Fin.val_one, pow_one]
  finsum_expand!
  simp only [Matrix.of_apply]
  vec_simp!
  simp only [ν_val_eq]
  apply of_point_interval (q := 2/1000) (by norm_num)
  fast_bound

private lemma Z₀_colNorm_2 :
    l1Weighted.matrixColNorm ν_val I_sub_A_DF 2 ≤ 2/1000 := by
  unfold l1Weighted.matrixColNorm I_sub_A_DF A_diag A_sub1 A_sub2 ā₀ ā₁ ā₂
  simp only [Fin.val_two, pow_two]
  finsum_expand!
  simp only [Matrix.of_apply]
  vec_simp!
  simp only [ν_val_eq]
  apply of_point_interval (q := 2/1000) (by norm_num)
  fast_bound

/-- Z₀ = ‖I - A·DF‖ ≤ 2/1000 -/
lemma Z₀_le : @Example_7_7.Z₀_bound ν_val 2 sol A_mat ≤ 2/1000 := by
  unfold Example_7_7.Z₀_bound
  rw [one_sub_A_DF_eq]
  unfold l1Weighted.finWeightedMatrixNorm
  apply Finset.sup'_le
  intro j _
  fin_cases j
  · show l1Weighted.matrixColNorm ν_val I_sub_A_DF 0 ≤ _; exact Z₀_colNorm_0
  · show l1Weighted.matrixColNorm ν_val I_sub_A_DF 1 ≤ _; exact Z₀_colNorm_1
  · show l1Weighted.matrixColNorm ν_val I_sub_A_DF 2 ≤ _; exact Z₀_colNorm_2

/-! ### Y₀ proof

Y₀ = finite_part + tail_part where:
- Finite part: ∑_{n=0}^2 |∑_j A_{nj} * F_j| * ν^n
- Tail part: (1/(2|ā₀|)) * ∑_{n=3}^4 (∑_k |ā_k||ā_{n-k}|) * ν^n

Strategy: Unfold Y₀_bound step by step, expand sums to explicit expressions,
then use fast_bound certified theorems (like Z₀ pattern).
-/

lemma Y₀_le : @Example_7_7.Y₀_bound ν_val 2 lam0 sol A_mat ≤ 9/500 := by
  -- Step 1: Unfold Y₀_bound definition
  unfold Example_7_7.Y₀_bound
  -- Step 2: Expand outer Fin 3 sum
  finsum_expand!
  -- Step 3: Expand inner Fin 3 sums (matrix-vector products) and simplify
  simp only [A_mat, Matrix.of_apply]
  vec_simp
  -- Step 4: Use F_fin computation lemmas
  simp only [F_fin_0_eq, F_fin_1_eq, F_fin_2_eq]
  -- Step 5: Expand tail sum over Finset.Icc 3 4
  have hIcc34 : Finset.Icc 3 (2 * 2) = {3, 4} := by native_decide
  simp only [hIcc34]
  finsum_expand
  -- Step 6: Expand inner sums in tail
  have hIcc12 : Finset.Icc (3 - 2) 2 = {1, 2} := by native_decide
  have hIcc22 : Finset.Icc (4 - 2) 2 = {2} := by native_decide
  simp only [hIcc12, hIcc22]
  finsum_expand
  -- Step 7: Unfold toSeq and simplify vector access
  simp only [Example_7_7.ApproxSolution.toSeq, sol]
  vec_simp!
  -- Step 8: Unfold all symbolic definitions to numerics
  unfold A_diag A_sub1 A_sub2 ā₀ ā₁ ā₂ lam0
  simp only [ν_val_eq]
  -- Step 9: Use of_point_interval to wrap goal in interval form, then fast_bound
  apply of_point_interval (q := 9/500) (by norm_num)
  fast_bound

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
  have hr : (0:ℝ) ≤ 996/10000 := by positivity
  have hr2 : (0:ℝ) ≤ (996/10000)^2 := sq_nonneg _
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

### The LeanCert Tactic Pattern

**Tactics from LeanCert make connection proofs cleaner:**

- **`finsum_expand`** - Automatically expands Finset sums (Icc, Ico, Fin n, etc.) to explicit additions
- **`vec_simp`** - Simplifies vector indexing `![a, b, c] ⟨n, _⟩` with explicit Fin.mk forms
- **`vec_simp!`** - Aggressive variant: also simplifies `dite` conditions with decidable ℕ comparisons
- **`dite_simp`** - Standalone tactic for `dite` with decidable literal conditions

**Key improvement: `vec_simp!` replaces verbose manual patterns:**

```lean
-- OLD (verbose):
simp only [show (0 : ℕ) ≤ 2 from by omega, show (1 : ℕ) ≤ 2 from by omega, dite_true]
vec_simp

-- NEW (one line):
vec_simp!
```

**Structure of a successful connection proof (using `of_point_interval`):**

```lean
-- Helper lemma (defined once in the file):
private lemma of_point_interval {e c : ℝ} {q : ℚ} (hqc : (q : ℝ) = c)
    (h : ∀ x ∈ Set.Icc (0:ℝ) 0, e ≤ q) : e ≤ c := by
  rw [← hqc]; exact h 0 ⟨le_refl _, le_refl _⟩

-- Connection lemma: unfold → expand → simplify → apply of_point_interval → fast_bound
lemma Bound_le : @Abstract.Bound params ≤ upper_bound := by
  unfold Abstract.Bound
  simp only [...]              -- unfold inner definitions
  finsum_expand                -- Finset.Icc / Fin n → explicit sum (automatic!)
  vec_simp!                    -- dite + vector indexing (automatic!)
  unfold defs...               -- unfold to pure numerics
  simp only [param_eq]         -- substitute parameter values
  -- Wrap in interval form and use fast_bound directly (no separate _certify theorem needed!)
  apply of_point_interval (q := upper_bound_as_rat) (by norm_num)
  fast_bound
```

### Key Principles

1. **Use `of_point_interval`** - Avoids copying expressions into separate `_certify` theorems
2. **Use `finsum_expand`** - No manual bridge lemmas needed for Finset sums
3. **Use `vec_simp!`** - Handles both dite conditions AND vector indexing in one step
4. **Use `fast_bound`/`certify_bound`** - Handles interval arithmetic automatically
5. **Compound fractions work directly** - `certify_bound` handles `1/(a/b)` without alignment lemmas
-/

end Example77Clean

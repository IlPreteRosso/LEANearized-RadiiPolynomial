# Development Log

## Legacy notes (TaylorODE / TaylorODE_Direct — now in Legacy/)

Early development used `TaylorODE/` and `TaylorODE_Direct/` folders, now moved to `Legacy/`.
Patterns documented there (tsum_subtype, calc→.trans, BlockDiagOp generalization) are
incorporated into the current `SystemTaylorODE` API. See git history for details.

---

## SystemTaylorODE scaffolding (2026-02-25, condensed)

Built `SystemTaylorODE/` as self-contained infrastructure for Section 8.2 systems:
- `Core.lean`: canonical norms `Y₀_norm/Z₀_norm/Z₁_norm/Z₂_norm` over general Banach spaces + `general_radii_polynomial_theorem`
- `BlockDiagSystem/{Base,Concrete,Scalar}.lean`: `SystemBlockDiagData` (coupled L×L finite block + componentwise tail diagonal), CLM lift, Z₀/Z₁ pipeline (general L), scalar L=1 wrappers
- Concrete backend: `ScaledReal.lean`, `CauchyProduct.lean`, `lpWeighted.lean`, `LpOneBanachAlgebra.lean`
- Evaluators/pipeline: `LeanCertEval.lean`, `WitnessSpec.lean`, `Setup82.lean`
- Reference alignment: pages 185-201 (Eq. 8.15-8.24, Theorem 8.2.2)

---

## Current State (SystemTaylorODE Example77, 2026-02-26)

### Bound architecture

**Working pipeline for column norm bounds (Z₀, ‖A‖):**
1. `Z₀_le_via_colNorm` / `norm_toScalarCLM_le_via_colNorm` (LeanCertEval.lean)
   chains structural reduction → `matrixColNorm` per column
2. `matrixColNorm_le_of_arrayColNormIccSum` bridges to ℚ Array columns
3. `finsum_bound using (colNormTermEval col ν j) (... colNormTermEval_correct ...)`
   closes via LeanCert interval arithmetic
4. Defect columns computed via `defectMatQ` (I-AB in ℚ) from A/B column arrays
5. `defectMatQ_correct` bridges real defect matrix to ℚ computation

**Key design decisions:**
- Per-term evaluator `colNormTermEval` in general API (LeanCertEval.lean)
- `defectMatQ` computes I-AB automatically from input columns — no hand computation
- `fast_bound` needs `∀ r ∈ Icc r₀ r₀` wrapper for scalar bounds
- `arrayColNormIccSum` is the bridge layer between `matrixColNorm` and `finsum_bound`

### Scalar-specific APIs for later generalization (2026-02-26)

APIs currently L=1 only, need general-L for Section 8.2:
- `norm_toScalarCLM_le` → need per-component `norm_toCLM_le`
- `injective_toScalarCLM_of_finBlock_mul_close_to_one` → per-component Neumann
- `toScalarCLM_support`, `norm_toScalarCLM_action_eq_Icc_sum` → per-component
- `norm_toScalarCLM_le_via_colNorm` (LeanCertEval) → system version with block norms

### New scalar-specific APIs (2026-02-26)

- `tailTsum_toScalarCLM_le` — tail action bound
- `finRangeSum_toScalarCLM_le` — finite action bound
- `norm_toScalarCLM_le_max` — tight max bound (Exercise 2.7.2)
- `norm_eq_finRangeSum_add_tailTsum` (lpWeighted.lean) — norm splitting

### Certificate progress (2026-02-27)

**All bounds completed (zero sorry):** `radii_neg`, `Z₀_le`, `A_injective`, `A_norm_le`, `Y₀_le`, `Z₁_le`

**Key lessons:**
- `finsum_bound` reifier can't handle complex Lean (antidiagonal, dite, match) — bridge norm body to `↑(ℚ_function n)` form
- LeanCertEval.lean = general evaluators only; equation-specific pipelines go in Algebra.lean

### Z₁ general-L porting + API cleanup (2026-02-27)

**Ported 3 scalar Z₁ APIs to general L in Concrete.lean:**
- `SystemBlockDiagData.norm_comp_of_fin_kill`
- `XL1.opNorm_le_of_fin_kill_tail_eq`
- `SystemBlockDiagData.Z₁_le_of_fin_kill_tail_dom`

**Extracted helpers to lpWeighted.lean:**
- `l1Weighted.norm_eq_tailTsum_of_fin_zero`, `tailTsum_le_norm_of_eq`, `norm_mk_le_of_pointwise`

**Extracted to Base.lean:**
- `SystemBlockDiagData.actionFinite_eq_zero_of_coeff_fin_zero`

### Canonical names generalized to Banach spaces (2026-02-27)

`Y₀_norm`, `Z₀_norm`, `Z₁_norm`, `Z₂_norm` in `Core.lean` now over general Banach spaces
(`E F : Type*`). Both `l1Weighted ν` and `XL1 ν L` unify under the same definitions.

---

### `auto_poly_fderiv` tactic (2026-02-28)

**File: `RadiiPolynomial/Tactic/AutoPolyFDeriv.lean`**

Unified tactic for polynomial differentiation. Handles both `fderiv` (CLM-valued, any
`NormedCommRing`) and `iteratedDeriv` (scalar-valued, univariate) goals.

**Architecture:**
1. Main simp (`fun_prop` discharger — handles both `DifferentiableAt` and `ContDiffAt`):
   - Mathlib `fderiv_*` rules (identity, add/sub/neg, mul, pow, const, composition)
   - Mathlib `iteratedDeriv_*` rules (same operations + Leibniz product rule)
   - `ContinuousLinearMap.fderiv` (projections from Pi types)
   - Banach algebra bridge: `smul_id_eq_leftMul`, `leftMul_nsmul` (type-safe, only fires on `l1Weighted`)
2. Cleanup (`first` with backtracking):
   - `ring_nf; try simp` — fderiv scalar normalization
   - `repeat unfold Nat.descFactorial; push_cast; ring` — iteratedDeriv cleanup

**Key design decisions:**
- Combined lemma set is safe: unmatched lemmas don't fire (e.g., `iteratedDeriv_*` ignored for `fderiv` goals)
- `fun_prop` is universal: discharges both `DifferentiableAt` and `ContDiffAt`
- Bridge lemmas (`smul_id_eq_leftMul`, `leftMul_nsmul`) in main simp, not cleanup — prevents `ring_nf` from rearranging before bridge can fire
- `leftMul_nsmul` handles arbitrary degree: `leftMul (n • a) → (↑n : ℝ) • leftMul a`

**Key discovery:** `l1Weighted ν` has `NormedCommRing` + `NormedAlgebra ℝ` (added `instNormedCommRing`).
Mathlib's `fderiv_pow_ring`/`hasFDerivAt_pow` fire directly — manual remainder proofs redundant.

**`leftMul` generalized:** moved from Example77 to `LpOneBanachAlgebra.lean` as
`ContinuousLinearMap.mul ℝ (l1Weighted ν)`. Helpers delegate to Mathlib.

**Usage:**
```lean
auto_poly_fderiv                      -- scalar fderiv or iteratedDeriv
rw [sq_eq_fun]; auto_poly_fderiv     -- Banach algebra (unfold named def first)
auto_poly_fderiv [extra₁, ...]       -- with additional simp lemmas
```

**Pi projection support (system-level):**
- `fderiv_pi_apply`: `fderiv 𝕜 (· i) x = ContinuousLinearMap.proj i` (`@[simp]`)
- `differentiable_pi_apply`: `Differentiable 𝕜 (· i)` (`@[fun_prop]`)
- The `@[fun_prop]` registration is critical: without it, `simp (discharger := fun_prop)`
  gets stuck on dependent Pi typeclass resolution for compound expressions.
  Key trick: `(ContinuousLinearMap.proj i : (ι → F) →L[𝕜] F).differentiable` with
  explicit type ascription forces non-dependent Pi unification.

**Files:**
- `Tactic/AutoPolyFDeriv.lean` — unified tactic + tests
- `LpOneBanachAlgebra.lean` — `instNormedCommRing`, `leftMul` + `leftMul_nsmul`
- `Example245/Algebra.lean` — `auto_poly_fderiv` one-liners
- `Example77/Algebra.lean` — `rw [sq_eq_fun]; auto_poly_fderiv`

---

### General-L API preparation (2026-02-28)

Generalized LeanCert evaluator and pipeline infrastructure from L=1 to arbitrary L,
preparing for Section 9.2 Lorenz manifold (L=3) certificate.

**New APIs in LeanCertEval.lean (system-level):**
- `systemComponentAction` — per-component ℝ action formula (sums over all L blocks)
- `toCoeff_toCLM_eq_componentAction` — bridge from `A.applyX` to evaluator formula
- `systemComponentActionEval` + `_correct` — ℚ evaluator for `finsum_bound using`
- `Z₀_le_via_block_colNorm` — system Z₀ via `finiteBlockMatrixNorm` + per-block bounds
- `norm_toCLM_le_via_block_colNorm` — system ‖A‖ via `finiteBlockMatrixNorm + tailBound`

**Already general-L (no changes needed):**
- `Z₁_le_of_fin_kill_tail_dom` (Concrete.lean) — Z₁ pipeline
- `injective_toCLM_of_finite_part_injective` (Concrete.lean) — injectivity
- `defectMatQ` + `colNormTermEval` — work per-block for any matrix size

---

### Proof refactoring: `finWeightedMatrixNorm_mulVec_le` (2026-02-28)

Refactored the weighted ℓ¹ submultiplicativity proof from ~50 lines (7 inline `have` blocks
with hand-typed summation formulas) to ~15 lines using existing helpers.

**Before:** 7 `have` blocks (h₁–h₅, h₃₄, h₂₃₄) each restating full `∑ n, ∑ k, |...| * ν^n` sums.

**After:** 3 concise steps:
1. `weighted_sum_abs_sum_le` (NormHelpers) — triangle + sum swap in one call
2. `simp_rw [abs_mul, show ... from by ring, ← Finset.mul_sum, ← matrixColNorm_mul_pow]` — factor + recognize colNorm
3. `Finset.sum_le_sum` + `mul_le_mul_of_nonneg` + `.trans_eq (mul_left_comm)` — sup bound

**Key fix:** `← Finset.mul_sum` (reverse direction to collapse `∑ a * f` → `a * ∑ f`),
and `mul_left_comm` instead of `ring` (since `finWeightedMatrixNorm = Finset.sup'` is a lattice op, not a ring op).

**Import added:** `lpWeighted.lean` now imports `NormHelpers.lean` (no circular dependency).

---

### Symbolize + flatten weighted norm API (2026-03-01)

Restated `finWeightedMatrixNorm_mulVec_le` symbolically using `finl1WeightedNorm` and `Matrix.mulVec`,
and deleted thin wrappers so callers use the general version directly.

**lpWeighted.lean:**
- Added `matrixColNorm_eq_finl1WeightedNorm_div` — symbolic bridge: `matrixColNorm ν A j = finl1WeightedNorm (col j) / ν^j`
- Restated `finWeightedMatrixNorm_mulVec_le`: `finl1WeightedNorm (A *ᵥ v) ≤ finWeightedMatrixNorm ν A * finl1WeightedNorm v`
  (proof via `show` to the definitionally-equal expanded form)
- Kept `matrixColNorm_mul_pow` `@[simp]` unchanged (OperatorNorm.lean needs expanded RHS)

**API flattening (Concrete.lean / Scalar.lean):**
- Deleted `finiteMatrix_weighted_l1_bound` — pure alias of `finWeightedMatrixNorm_mulVec_le`
- Deleted `finiteCoeffNorm_le_component_norm` — thin wrapper of `finSum_weighted_toSeq_le_norm` (1 caller)
- `actionFinite_component_norm_le_row`: calls `finWeightedMatrixNorm_mulVec_le` directly
  (`simpa [blockEntryNorm, finl1WeightedNorm, Matrix.mulVec, dotProduct]`)
- `finRangeSum_toScalarCLM_le` (Scalar.lean): calls `finWeightedMatrixNorm_mulVec_le` directly

**MatrixCLM.lean:** `mulVecWeightedLinear_norm_le` bridges via `norm_eq_finl1WeightedNorm` instead of `norm_eq_sum`.

**Key fix:** `dotProduct` lives at module level, not `Matrix.dotProduct` — use unqualified name in `simpa`.

**Definition-level symbolization:**
- `matrixColNorm` definition changed from `(1/ν^j) * ∑ |A i j| * ν^i` to `finl1WeightedNorm (ν : ℝ≥0) (col j) / ν^j`
- `matrixColNorm_eq_finl1WeightedNorm_div` is now `rfl`

**`PosReal` coercion infrastructure (ScaledReal.lean):**
- Added `@[coe] def toNNReal` + `instance : Coe PosReal ℝ≥0`
- Added `@[simp, norm_cast] lemma coe_toNNReal : ((ν : ℝ≥0) : ℝ) = (ν : ℝ)`
- Eliminates manual `simp [PosReal.toNNReal]` — `norm_cast`/`push_cast` handles coercion chain automatically

**Proof refactoring: `actionFinite_component_norm_le_row` (Concrete.lean):**
- Extracted `norm_mk_actionFinite_eq` helper (bridges `‖mk actionFinite ...‖` to expanded double-sum)
- Compressed 100-line proof to ~35 lines via `.trans` chain

**Deleted `Setup82.lean`** — dead code (`SeqModel` typeclass superseded by `BlockDiagSystem`). `shiftCoeff`/`lambdaNCoeff` unused, can be re-added when needed.

---

### Section 9.2 Lorenz manifold — Julia pipeline + gap analysis (2026-03-01)

Julia pipeline (`julia/lorenz_manifold.ipynb`) validated for Lorenz 1D unstable manifold at origin:
- Taylor recursion works (N=20, coefficients decay ~100×/mode)
- λ = (-11+√1201)/2 ≈ 11.83, ξ = (-0.4165, -0.9091, 0)
- Bounds: Y₀ < 1e-39, Z₀ < 1e-15, Z₁ < 0.008, Z₂ < 0.009 — validates

**Gap for Lean formalization:**
- ā involves irrational λ → rationalized ā_ℚ gives F(ā_ℚ) ≠ 0
- Y₀ = ‖A·F(ā_ℚ)‖ involves `√1201` → needs `fast_bound` to handle `Real.sqrt` (untested)
- Float64 precision insufficient for modes ≥ 9 → need BigFloat or lower N

**Decision:** Pivot to Example 8.3 (Lorenz IVP) first — fully rational pipeline, exercises general-L API with zero new obstacles. Return to 9.2 after.

---

### Example 8.3 Lorenz IVP — Julia pipeline (2026-03-01, in progress)

**Setup:** ẋ = f(x), x(0) = (1,1,1), σ=10, ρ=28, β=8/3, tail diagonal = n (rational).

**Taylor recursion:** works in exact ℚ (BigInt), F(ā)=0 exactly. Also works in Float64.

**Issue:** DF^(N) is terribly conditioned (cond ≈ 4e27 at ν=0.05, N=20) because unweighted matrix mixes mode-0 (O(1)) with mode-N (O(N·ν^{-N})) scales. Float64 inverse gives Z₀ ≈ 8.

**Next steps:**
1. Weight DF by ν^n (scale row n by ν^n, col m by ν^{-m}) to improve conditioning
2. Or use `RadiiPolynomial.jl` which handles this internally
3. Use floats + interval arithmetic for bounds, rationalize only final upper bounds for Lean export
